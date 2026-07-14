//! `/buy-credits` and `/balance` — the `$DREGG` earning surface.
//!
//! * **`/buy-credits`** issues the caller's deterministic per-user Solana deposit address
//!   (`dregg_pay::HdDeposit::deposit_address(discord_user_id)` — same user ⇒ same address), shows
//!   the price per run and the network, and explains how paying credits a run. It polls first so a
//!   payment that already landed is reflected immediately.
//! * **`/balance`** polls the watcher for the caller's deposit address (crediting any new payment,
//!   idempotently) then shows their persisted run-credit balance.
//!
//! A run-credit is spent by a paid `/dungeon` room narration (real Bedrock under a per-run budget);
//! an empty balance falls back to the free ollama/scripted tier. See [`crate::pay`].

use serenity::all::{
    CommandInteraction, Context, CreateCommand, CreateEmbed, CreateEmbedFooter,
    CreateInteractionResponse, CreateInteractionResponseMessage,
};

use crate::BotState;
use dregg_pay::{ChainId, CreditOutcome, Network};

/// The bot-branded purple (matches the dungeon surface).
const PAY_COLOR: u32 = 0x7B2CBF;

/// Register `/buy-credits`.
pub fn register() -> CreateCommand {
    register_buy()
}

/// Register `/buy-credits`.
pub fn register_buy() -> CreateCommand {
    CreateCommand::new("buy-credits").description(
        "Get your $DREGG deposit address to buy real-AI dungeon run-credits (devnet/mock by default)",
    )
}

/// Register `/balance`.
pub fn register_balance() -> CreateCommand {
    CreateCommand::new("balance")
        .description("Show your $DREGG run-credit balance for real-AI dungeon runs")
}

/// Register `/treasury`.
pub fn register_treasury() -> CreateCommand {
    CreateCommand::new("treasury").description(
        "Report the game treasury: the two-balance fuel/pile + its proven cross-chain holdings",
    )
}

/// A human name for a declared position's chain.
fn chain_label(chain: ChainId) -> String {
    match chain {
        ChainId::Solana => "Solana".to_string(),
        ChainId::ETHEREUM => "Ethereum".to_string(),
        ChainId::BASE => "Base".to_string(),
        ChainId::Evm(id) => format!("EVM chain {id}"),
        ChainId::Cosmos(_) => "Cosmos".to_string(),
    }
}

async fn respond_ephemeral(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn network_label(n: Network) -> &'static str {
    match n {
        Network::Devnet => "devnet (safe · mock)",
        Network::Mainnet => "mainnet (real funds)",
    }
}

/// `/buy-credits` — issue the caller's deposit address, price, and pay instructions.
pub async fn handle_buy(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let pay = &state.pay;

    // Persist the user→deposit-index map (stable address), then reflect any payment already landed.
    let _ = pay.record_deposit_assignment(&discord_id).await;
    let credited: u64 = match pay.poll_and_credit(&discord_id) {
        Ok(outs) => outs
            .iter()
            .map(|o| match o {
                CreditOutcome::Credited { runs, .. } => *runs,
                _ => 0,
            })
            .sum(),
        Err(_) => 0,
    };

    let address = pay.deposit_address_base58(&discord_id);
    let price = pay.price_per_run();
    let balance = pay.balance(&discord_id);

    let mut desc = format!(
        "Send **$DREGG** to your personal deposit address below. Each **{price}** atomic $DREGG buys **one** real-AI dungeon run. Your address is deterministic — it is always the same for you.\n\n**Your deposit address**\n```\n{address}\n```\nNetwork: **{}**\n\nAfter you pay, run `/balance` (or `/buy-credits` again) to credit it. A paid `/dungeon` room is narrated by real Bedrock; with no credits you get the free (ollama/scripted) narrator.",
        network_label(pay.network()),
    );
    if credited > 0 {
        desc.push_str(&format!(
            "\n\n✅ Just credited **{credited}** run(s) from a payment."
        ));
    }

    let embed = CreateEmbed::new()
        .title("Buy real-AI dungeon credits")
        .description(desc)
        .color(PAY_COLOR)
        .field("Price per run", format!("{price} atomic $DREGG"), true)
        .field("Your balance", format!("{balance} run(s)"), true)
        .footer(CreateEmbedFooter::new(
            "custodial HD-deposit (\"B\") model · devnet/mock by default · mainnet is an operator flip",
        ));
    respond_ephemeral(ctx, command, embed).await;
}

/// `/balance` — poll for new payments, then show the caller's run-credit balance.
pub async fn handle_balance(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let pay = &state.pay;

    let credited: u64 = match pay.poll_and_credit(&discord_id) {
        Ok(outs) => outs
            .iter()
            .map(|o| match o {
                CreditOutcome::Credited { runs, .. } => *runs,
                _ => 0,
            })
            .sum(),
        Err(_) => 0,
    };
    let balance = pay.balance(&discord_id);
    let price = pay.price_per_run();

    let mut desc = format!(
        "You have **{balance}** run-credit(s). Each paid `/dungeon` room narration by real Bedrock spends one; with none you get the free (ollama/scripted) narrator.\n\nBuy more with `/buy-credits` — send **{price}** atomic $DREGG per run to your deposit address."
    );
    if credited > 0 {
        desc.push_str(&format!(
            "\n\n✅ Just credited **{credited}** run(s) from a new payment."
        ));
    }

    let embed = CreateEmbed::new()
        .title("Your $DREGG run-credits")
        .description(desc)
        .color(PAY_COLOR)
        .footer(CreateEmbedFooter::new(
            "credits persist across restarts (sqlite) · devnet/mock by default",
        ));
    respond_ephemeral(ctx, command, embed).await;
}

/// `/treasury` — report the two-balance treasury (the revenue that landed) and the
/// treasury's declared cross-chain positions + proven cross-chain holdings.
///
/// The fuel/pile are the LIVE revenue-landing accounting: a detected USDC payment fuels the
/// tank (burned per real-AI run), a `$DREGG` payment grows the pile (see [`crate::pay`]). The
/// multichain view is the non-custodial cross-chain report: it counts only proof-of-holdings
/// facts that bind to the treasury's own declared addresses and carry a real consensus proof.
/// A live proof-of-holdings relayer feed is a named residual — until one is wired the proven
/// total reflects the facts currently available (none in the interim), while the DECLARED
/// positions are always shown.
pub async fn handle_treasury(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let pay = &state.pay;

    let fuel = pay.treasury_fuel();
    let pile = pay.treasury_pile();

    let mut desc = format!(
        "**The two-balance treasury** — where detected game revenue lands.\n\n• **Fuel (USDC):** `{fuel}` atomic — burned per real-AI run; fails closed (must-refuel) on empty.\n• **Pile ($DREGG):** `{pile}` atomic — the accumulating illiquid holding.\n\nA USDC payment fuels the tank; a $DREGG payment grows the pile. Every run burns USD fuel regardless of how it was paid.\n\n**Declared cross-chain positions** (non-custodial — proven, not held):"
    );

    let slots = pay.treasury_slots();
    if slots.is_empty() {
        desc.push_str("\n_(none declared)_");
    } else {
        for s in slots {
            desc.push_str(&format!("\n• `{}` — {}", chain_label(s.chain), s.label));
        }
    }

    // Report proven cross-chain holdings over whatever facts are currently available. With
    // no live proof-of-holdings relayer wired yet (a named residual), this is the empty set
    // in the interim; the accessor is the exposed surface a relayer feeds.
    let held = pay.treasury_holdings(&[]);
    desc.push_str(&format!(
        "\n\n**Proven cross-chain holdings:** {} position(s) proven across {} chain(s), total `{}` atomic.\n_Proven holdings require a proof-of-holdings relayer pointed at these addresses (a named residual); the declared positions above are the treasury's non-custodial claim._",
        held.holdings.len(),
        held.chains_proven(),
        held.total_amount(),
    ));

    let embed = CreateEmbed::new()
        .title("Game treasury")
        .description(desc)
        .color(PAY_COLOR)
        .field("Fuel (USDC atomic)", format!("{fuel}"), true)
        .field("Pile ($DREGG atomic)", format!("{pile}"), true)
        .footer(CreateEmbedFooter::new(
            "revenue-landing accounting persists across restart (sqlite) · non-custodial cross-chain view · devnet/mock by default",
        ));
    respond_ephemeral(ctx, command, embed).await;
}
