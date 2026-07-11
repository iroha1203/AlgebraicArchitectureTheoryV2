//! Settlement ledger: the finance book of record for captured orders.
//!
//! Ledger convention: monetary values are kept exact in ten-thousandths of a
//! cent ("tenk-cents"); the ledger itself never rounds. Rounded presentation
//! amounts coming from other modules are booked as-is and compared against
//! the exact value during reconciliation.

use crate::app::{AppError, CheckoutOutcome};

const TENK: i128 = 10_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerEntryKind {
    DisplayTotal,
    PspCapture,
    ExactTotal,
    RoundingResidual,
}

#[derive(Debug, Clone)]
pub struct LedgerEntry {
    pub order_id: String,
    pub kind: LedgerEntryKind,
    pub amount_tenk_cents: i128,
}

#[derive(Debug, Clone)]
pub struct SettlementReport {
    pub order_id: String,
    pub display_total_cents: i64,
    pub captured_cents: i64,
    pub exact_total_tenk_cents: i128,
    pub residual_booked: bool,
}

impl SettlementReport {
    pub fn capture_drift_cents(&self) -> i64 {
        self.captured_cents - self.display_total_cents
    }

    pub fn rounding_residual_tenk_cents(&self) -> i128 {
        i128::from(self.display_total_cents) * TENK - self.exact_total_tenk_cents
    }

    pub fn is_reconciled(&self) -> bool {
        self.capture_drift_cents() == 0
            && (self.rounding_residual_tenk_cents() == 0 || self.residual_booked)
    }

    pub fn render_lines(&self) -> Vec<String> {
        let exact_whole = self.exact_total_tenk_cents / TENK;
        let exact_frac = (self.exact_total_tenk_cents % TENK).unsigned_abs();
        let mut lines = vec![
            format!("settlement reconciliation for {}", self.order_id),
            format!(
                "display total {} cents / psp captured {} cents / exact {}.{:04} cents",
                self.display_total_cents, self.captured_cents, exact_whole, exact_frac
            ),
        ];
        if self.is_reconciled() {
            lines.push(format!(
                "reconciled: capture matches display; rounding residual {:+} tenk-cents booked explicitly",
                -self.rounding_residual_tenk_cents()
            ));
        } else {
            lines.push(format!(
                "RECONCILIATION MISMATCH: psp captured {:+} cents against the displayed total",
                self.capture_drift_cents()
            ));
        }
        lines
    }
}

#[derive(Debug, Clone, Default)]
pub struct SettlementLedger {
    entries: Vec<LedgerEntry>,
}

impl SettlementLedger {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn entries(&self) -> &[LedgerEntry] {
        &self.entries
    }

    /// Books one captured order. The exact total is recomputed from the order
    /// lines under the ledger's own no-rounding convention.
    pub fn book_order(
        &mut self,
        outcome: &CheckoutOutcome,
        discount_bps: i64,
    ) -> Result<SettlementReport, AppError> {
        let order = &outcome.decision.order;
        let order_id = order.id().as_str().to_string();
        let subtotal_cents = i128::from(order.subtotal()?.cents());
        let exact_discount_tenk = subtotal_cents * i128::from(discount_bps);
        let exact_total_tenk = subtotal_cents * TENK - exact_discount_tenk;
        let display_total_cents = outcome.pricing.total_due().cents();
        let captured_cents = outcome.decision.payment.amount().cents();

        self.entries.push(LedgerEntry {
            order_id: order_id.clone(),
            kind: LedgerEntryKind::DisplayTotal,
            amount_tenk_cents: i128::from(display_total_cents) * TENK,
        });
        self.entries.push(LedgerEntry {
            order_id: order_id.clone(),
            kind: LedgerEntryKind::PspCapture,
            amount_tenk_cents: i128::from(captured_cents) * TENK,
        });
        self.entries.push(LedgerEntry {
            order_id: order_id.clone(),
            kind: LedgerEntryKind::ExactTotal,
            amount_tenk_cents: exact_total_tenk,
        });

        let residual_tenk = i128::from(display_total_cents) * TENK - exact_total_tenk;
        let residual_booked = cfg!(feature = "settlement-authority") && residual_tenk != 0;
        if residual_booked {
            self.entries.push(LedgerEntry {
                order_id: order_id.clone(),
                kind: LedgerEntryKind::RoundingResidual,
                amount_tenk_cents: -residual_tenk,
            });
        }

        Ok(SettlementReport {
            order_id,
            display_total_cents,
            captured_cents,
            exact_total_tenk_cents: exact_total_tenk,
            residual_booked,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::app::{CheckoutService, CheckoutCommand, CheckoutLineCommand};
    use crate::domain::{
        Address, CatalogItem, Currency, CustomerId, CustomerProfile, InventoryPosition, Money,
        Quantity, ServiceLevel, Sku, WarehouseId, VIP_LOYALTY_DISCOUNT_BPS,
    };
    use crate::policy::PolicyEngine;
    use crate::store::InMemoryCommercePlatform;

    fn vip_checkout_outcome() -> Result<CheckoutOutcome, AppError> {
        let mut platform = InMemoryCommercePlatform::new();
        platform.add_catalog_item(CatalogItem::new(
            Sku::new("KIT-RED")?,
            "Red field repair kit",
            Money::new(12_490, Currency::Usd)?,
            1_800,
            true,
        )?);
        platform.add_catalog_item(CatalogItem::new(
            Sku::new("CBL-2M")?,
            "Two meter shielded cable",
            Money::new(4_505, Currency::Usd)?,
            400,
            false,
        )?);
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
        let mut service = CheckoutService::new(platform, PolicyEngine::standard());
        service.execute(CheckoutCommand {
            order_id: "order-ledger-test".to_string(),
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
            service_level: ServiceLevel::Standard,
            ship_to: None,
        })
    }

    #[test]
    fn ledger_keeps_exact_totals_without_rounding() -> Result<(), AppError> {
        let outcome = vip_checkout_outcome()?;
        let mut ledger = SettlementLedger::new();

        let report = ledger.book_order(&outcome, VIP_LOYALTY_DISCOUNT_BPS)?;

        // subtotal 33,990 cents at 250 bps: exact total is 33,140.25 cents
        assert_eq!(report.exact_total_tenk_cents, 331_402_500);
        assert_eq!(report.display_total_cents, 33_140);
        Ok(())
    }

    #[cfg(not(feature = "settlement-authority"))]
    #[test]
    fn head_state_reports_one_cent_capture_drift() -> Result<(), AppError> {
        let outcome = vip_checkout_outcome()?;
        let mut ledger = SettlementLedger::new();

        let report = ledger.book_order(&outcome, VIP_LOYALTY_DISCOUNT_BPS)?;

        assert_eq!(report.capture_drift_cents(), 1);
        assert!(!report.is_reconciled());
        Ok(())
    }

    #[cfg(feature = "settlement-authority")]
    #[test]
    fn settlement_authority_books_residual_and_reconciles() -> Result<(), AppError> {
        let outcome = vip_checkout_outcome()?;
        let mut ledger = SettlementLedger::new();

        let report = ledger.book_order(&outcome, VIP_LOYALTY_DISCOUNT_BPS)?;

        assert_eq!(report.capture_drift_cents(), 0);
        assert_eq!(report.rounding_residual_tenk_cents(), -2_500);
        assert!(report.is_reconciled());
        assert!(ledger
            .entries()
            .iter()
            .any(|entry| entry.kind == LedgerEntryKind::RoundingResidual));
        Ok(())
    }
}
