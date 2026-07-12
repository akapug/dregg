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
use dregg_pay::{CreditOutcome, Network};

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
