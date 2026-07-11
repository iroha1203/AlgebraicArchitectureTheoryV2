use crate::app::{AppError, CheckoutCommand, CheckoutLineCommand, CheckoutService};
use crate::domain::{
    Address, CatalogItem, Currency, CustomerId, CustomerProfile, InventoryPosition, Money,
    Quantity, ServiceLevel, Sku, WarehouseId,
};
use crate::policy::{PolicyEngine, PolicyVerdict};
use crate::store::InMemoryCommercePlatform;
use crate::telemetry::PresentationSnapshot;

pub fn build_demo_platform() -> Result<InMemoryCommercePlatform, AppError> {
    let mut platform = InMemoryCommercePlatform::new();
    let kit = CatalogItem::new(
        Sku::new("KIT-RED")?,
        "Red field repair kit",
        Money::new(12_490, Currency::Usd)?,
        1_800,
        true,
    )?;
    let cable = CatalogItem::new(
        Sku::new("CBL-2M")?,
        "Two meter shielded cable",
        Money::new(4_505, Currency::Usd)?,
        400,
        false,
    )?;
    platform.add_catalog_item(kit);
    platform.add_catalog_item(cable);
    platform.add_customer(CustomerProfile::new(
        CustomerId::new("customer-1")?,
        "ops@example.com",
        Address::new("1 Market", "San Francisco", "CA", "94105", "US")?,
        true,
        400,
    )?);
    platform.add_inventory(InventoryPosition::new(
        Sku::new("KIT-RED")?,
        WarehouseId::new("west-1")?,
        Quantity::new(12)?,
    ));
    platform.add_inventory(InventoryPosition::new(
        Sku::new("CBL-2M")?,
        WarehouseId::new("west-1")?,
        Quantity::new(40)?,
    ));
    Ok(platform)
}

pub fn demo_command() -> CheckoutCommand {
    CheckoutCommand {
        order_id: "order-demo-100".to_string(),
        customer_id: "customer-1".to_string(),
        lines: vec![
            CheckoutLineCommand {
                sku: "KIT-RED".to_string(),
                quantity: 2,
            },
            CheckoutLineCommand {
                sku: "CBL-2M".to_string(),
                quantity: 2,
            },
        ],
        service_level: ServiceLevel::Expedited,
        ship_to: None,
    }
}

pub fn run_demo() -> Result<PresentationSnapshot, AppError> {
    let platform = build_demo_platform()?;
    let mut service = CheckoutService::new(platform, PolicyEngine::standard());
    let outcome = service.execute(demo_command())?;
    let mut snapshot = PresentationSnapshot::new("ArchSig practical Rust service demo");
    snapshot.push(format!(
        "order {} released",
        outcome.decision.order.id().as_str()
    ));
    snapshot.push(format!(
        "{} reservation lines",
        outcome.decision.reservation.lines().len()
    ));
    snapshot.push(format!(
        "displayed total {} cents ({} minus {} loyalty discount)",
        outcome.pricing.total_due().cents(),
        outcome.pricing.subtotal().cents(),
        outcome.pricing.discount().cents()
    ));
    snapshot.push(format!(
        "payment {} authorized for {} cents",
        outcome.decision.payment.id().as_str(),
        outcome.decision.payment.amount().cents()
    ));
    snapshot.push(format!(
        "shipment {} planned",
        outcome.decision.shipment.id().as_str()
    ));
    snapshot.push(format!("risk score {}", outcome.decision.risk.score));
    snapshot.push(format!("{} trace events", outcome.trace_events.len()));
    let satisfied = outcome
        .policy_evaluations
        .iter()
        .filter(|evaluation| evaluation.verdict == PolicyVerdict::Satisfied)
        .count();
    snapshot.push(format!("{} policy rules satisfied", satisfied));
    snapshot.push(format!(
        "insight tags: {}",
        outcome.decision.insight_tags().join(", ")
    ));
    #[cfg(feature = "psp-compliance")]
    {
        use crate::domain::VIP_LOYALTY_DISCOUNT_BPS;
        use crate::ledger::SettlementLedger;

        let mut ledger = SettlementLedger::new();
        let report = ledger.book_order(&outcome, VIP_LOYALTY_DISCOUNT_BPS)?;
        for line in report.render_lines() {
            snapshot.push(line);
        }
    }
    Ok(snapshot)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demo_snapshot_contains_archsig_presentation_lines() -> Result<(), AppError> {
        let snapshot = run_demo()?;
        let rendered = snapshot.render();
        assert!(rendered.contains("ArchSig practical Rust service demo"));
        assert!(rendered.contains("policy rules satisfied"));
        Ok(())
    }
}
