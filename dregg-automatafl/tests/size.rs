use dregg_automatafl::build_d1_honest;
use dregg_automatafl::reference::{ATT, AUTO, Board, VAC};

fn mk(n: usize, placed: &[((i32, i32), u8)], auto: (i32, i32)) -> Board {
    let mut cells = vec![VAC; n * n];
    for &(c, p) in placed {
        cells[(c.1 as usize) * n + (c.0 as usize)] = p;
    }
    cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
    Board {
        n,
        cells,
        auto,
        col_rule: true,
    }
}

#[test]
fn d1_size_report() {
    let old = mk(5, &[((2, 4), ATT)], (2, 2));
    let b = build_d1_honest(&old);
    let d = b.descriptor();
    eprintln!(
        "D1 width={} constraints={} max_degree={} pis={}",
        d.trace_width,
        d.constraints.len(),
        d.max_degree,
        d.public_input_count
    );
    assert!(b.air_accepts());
}
