//! dregg-tui — the face of the Robigalia v0 demo.
//!
//! A terminal light client over a running dregg node's HTTP API
//! (`node/src/api.rs`). It is the operator's window: a tab for the node
//! identity, a tab listing cells (id / balance / nonce / capability count), and
//! a tab of recent receipts. Arrow keys / Tab switch panes; `r` refreshes; `q`
//! quits. Point it at a node with `dregg-tui <BASE_URL>` (default
//! http://127.0.0.1:8080).
//!
//! It is a *light client* in the dregg sense: it does not run the node, hold
//! the ledger, or trust the node blindly — it reads the node's published API
//! and (in the verify-extended form) checks the attested history against the
//! finality certs (`lightclient/`). M4 of the seL4 boot ladder: once the M3 net
//! stack carries the node onto seL4, this same TUI is the face of the seL4
//! deployment.

use std::io::{self, Stdout};
use std::time::Duration;

use anyhow::Result;
use crossterm::event::{self, Event, KeyCode};
use crossterm::execute;
use crossterm::terminal::{
    disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen,
};
use ratatui::backend::CrosstermBackend;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, List, ListItem, Paragraph, Row, Table, Tabs};
use ratatui::{Frame, Terminal};
use serde::Deserialize;

// ── The node API response shapes we consume (subset of node/src/api.rs). ────

#[derive(Deserialize, Default, Clone)]
struct NodeIdentity {
    #[serde(default)]
    cell_id: String,
    #[serde(default)]
    public_key: String,
    #[serde(default)]
    federation: String,
}

#[derive(Deserialize, Clone)]
struct CellListEntry {
    id: String,
    #[serde(default)]
    balance: i64,
    #[serde(default)]
    nonce: u64,
    #[serde(default)]
    capability_count: usize,
    #[serde(default)]
    has_program: bool,
}

#[derive(Deserialize, Clone)]
struct ReceiptInfo {
    #[serde(default)]
    hash: String,
    #[serde(default)]
    kind: String,
    #[serde(default)]
    cell_id: String,
}

// ── The light-client HTTP layer. ────────────────────────────────────────────

struct Client {
    base: String,
}

impl Client {
    fn new(base: String) -> Self {
        Client { base }
    }

    fn get<T: serde::de::DeserializeOwned>(&self, path: &str) -> Result<T> {
        let url = format!("{}{}", self.base, path);
        let v: T = ureq::get(&url).timeout(Duration::from_secs(3)).call()?.into_json()?;
        Ok(v)
    }

    fn identity(&self) -> NodeIdentity {
        self.get("/api/node/identity").unwrap_or_default()
    }
    fn cells(&self) -> Vec<CellListEntry> {
        self.get("/api/cells").unwrap_or_default()
    }
    fn receipts(&self) -> Vec<ReceiptInfo> {
        self.get("/api/receipts").unwrap_or_default()
    }
}

// ── App state. ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq)]
enum Tab {
    Identity,
    Cells,
    Receipts,
}

impl Tab {
    fn titles() -> [&'static str; 3] {
        ["Identity", "Cells", "Receipts"]
    }
    fn index(self) -> usize {
        match self {
            Tab::Identity => 0,
            Tab::Cells => 1,
            Tab::Receipts => 2,
        }
    }
    fn next(self) -> Tab {
        match self {
            Tab::Identity => Tab::Cells,
            Tab::Cells => Tab::Receipts,
            Tab::Receipts => Tab::Identity,
        }
    }
}

struct App {
    client: Client,
    tab: Tab,
    identity: NodeIdentity,
    cells: Vec<CellListEntry>,
    receipts: Vec<ReceiptInfo>,
    status: String,
    online: bool,
}

impl App {
    fn new(base: String) -> Self {
        let client = Client::new(base);
        let mut app = App {
            client,
            tab: Tab::Identity,
            identity: NodeIdentity::default(),
            cells: Vec::new(),
            receipts: Vec::new(),
            status: String::new(),
            online: false,
        };
        app.refresh();
        app
    }

    fn refresh(&mut self) {
        // Probe with the identity call; if it succeeds we're online.
        let id: Result<NodeIdentity> = self.client.get("/api/node/identity");
        self.online = id.is_ok();
        self.identity = self.client.identity();
        self.cells = self.client.cells();
        self.receipts = self.client.receipts();
        self.status = if self.online {
            format!(
                "online · {} · {} cells · {} receipts",
                self.client.base,
                self.cells.len(),
                self.receipts.len()
            )
        } else {
            format!("offline · could not reach {} (is a dregg node running?)", self.client.base)
        };
    }
}

// ── Rendering. ───────────────────────────────────────────────────────────────

fn draw(f: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Length(3), Constraint::Min(0), Constraint::Length(1)])
        .split(f.area());

    // Tab bar.
    let titles: Vec<Line> = Tab::titles().iter().map(|t| Line::from(*t)).collect();
    let tabs = Tabs::new(titles)
        .block(Block::default().borders(Borders::ALL).title(" dregg robigalia v0 — light client "))
        .select(app.tab.index())
        .highlight_style(Style::default().fg(Color::Black).bg(Color::Cyan).add_modifier(Modifier::BOLD));
    f.render_widget(tabs, chunks[0]);

    match app.tab {
        Tab::Identity => draw_identity(f, app, chunks[1]),
        Tab::Cells => draw_cells(f, app, chunks[1]),
        Tab::Receipts => draw_receipts(f, app, chunks[1]),
    }

    // Status / help line.
    let dot = if app.online { Span::styled("●", Style::default().fg(Color::Green)) } else {
        Span::styled("●", Style::default().fg(Color::Red))
    };
    let status = Line::from(vec![
        dot,
        Span::raw(" "),
        Span::raw(app.status.clone()),
        Span::styled("   [Tab] pane  [r] refresh  [q] quit", Style::default().fg(Color::DarkGray)),
    ]);
    f.render_widget(Paragraph::new(status), chunks[2]);
}

fn draw_identity(f: &mut Frame, app: &App, area: Rect) {
    let id = &app.identity;
    let lines = vec![
        Line::from(vec![Span::styled("node cell id  ", Style::default().fg(Color::Cyan)), Span::raw(blank_dash(&id.cell_id))]),
        Line::from(vec![Span::styled("public key    ", Style::default().fg(Color::Cyan)), Span::raw(blank_dash(&id.public_key))]),
        Line::from(vec![Span::styled("federation    ", Style::default().fg(Color::Cyan)), Span::raw(blank_dash(&id.federation))]),
        Line::from(""),
        Line::from(Span::styled(
            "this is a light client: it reads the node's published API and",
            Style::default().fg(Color::DarkGray),
        )),
        Line::from(Span::styled(
            "(in verify mode) checks attested history against finality certs.",
            Style::default().fg(Color::DarkGray),
        )),
    ];
    f.render_widget(
        Paragraph::new(lines).block(Block::default().borders(Borders::ALL).title(" node identity ")),
        area,
    );
}

fn draw_cells(f: &mut Frame, app: &App, area: Rect) {
    let rows: Vec<Row> = app
        .cells
        .iter()
        .map(|c| {
            Row::new(vec![
                short(&c.id),
                c.balance.to_string(),
                c.nonce.to_string(),
                c.capability_count.to_string(),
                if c.has_program { "yes".into() } else { "—".into() },
            ])
        })
        .collect();
    let widths = [
        Constraint::Length(20),
        Constraint::Length(14),
        Constraint::Length(8),
        Constraint::Length(6),
        Constraint::Length(8),
    ];
    let table = Table::new(rows, widths)
        .header(
            Row::new(vec!["cell id", "balance", "nonce", "caps", "program"])
                .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)),
        )
        .block(Block::default().borders(Borders::ALL).title(format!(" cells ({}) ", app.cells.len())));
    f.render_widget(table, area);
}

fn draw_receipts(f: &mut Frame, app: &App, area: Rect) {
    let items: Vec<ListItem> = app
        .receipts
        .iter()
        .map(|r| {
            ListItem::new(Line::from(vec![
                Span::styled(format!("{:<14}", blank_dash(&r.kind)), Style::default().fg(Color::Yellow)),
                Span::raw(short(&r.hash)),
                Span::raw("  "),
                Span::styled(short(&r.cell_id), Style::default().fg(Color::DarkGray)),
            ]))
        })
        .collect();
    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title(format!(" receipts ({}) ", app.receipts.len())));
    f.render_widget(list, area);
}

fn short(s: &str) -> String {
    if s.len() > 18 {
        format!("{}…{}", &s[..8], &s[s.len() - 6..])
    } else if s.is_empty() {
        "—".into()
    } else {
        s.to_string()
    }
}

fn blank_dash(s: &str) -> String {
    if s.is_empty() {
        "—".into()
    } else {
        s.to_string()
    }
}

// ── Event loop. ──────────────────────────────────────────────────────────────

fn run(terminal: &mut Terminal<CrosstermBackend<Stdout>>, mut app: App) -> Result<()> {
    loop {
        terminal.draw(|f| draw(f, &app))?;
        if event::poll(Duration::from_millis(250))? {
            if let Event::Key(key) = event::read()? {
                match key.code {
                    KeyCode::Char('q') | KeyCode::Esc => break,
                    KeyCode::Tab | KeyCode::Right => app.tab = app.tab.next(),
                    KeyCode::Char('r') => app.refresh(),
                    KeyCode::Char('1') => app.tab = Tab::Identity,
                    KeyCode::Char('2') => app.tab = Tab::Cells,
                    KeyCode::Char('3') => app.tab = Tab::Receipts,
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let base = std::env::args().nth(1).unwrap_or_else(|| "http://127.0.0.1:8080".to_string());

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let app = App::new(base);
    let res = run(&mut terminal, app);

    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    terminal.show_cursor()?;
    res
}
