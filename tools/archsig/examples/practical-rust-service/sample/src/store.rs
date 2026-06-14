use std::collections::BTreeMap;

use crate::app::{
    AppError, CatalogPort, CustomerPort, InventoryPort, OutboxPort, PaymentPort,
    ReservationAllocator, RiskPort, ShippingPort,
};
use crate::domain::{
    Address, CatalogItem, CustomerId, CustomerProfile, DomainEvent, InventoryPosition,
    InventoryReservation, Money, Order, OrderId, PaymentAuthorization, PaymentId, PaymentStatus,
    Quantity, RiskAssessment, ServiceLevel, ShipmentId, ShipmentLeg, ShipmentPlan, Sku,
    WarehouseId,
};

#[derive(Debug, Clone)]
pub struct InMemoryCommercePlatform {
    catalog: BTreeMap<Sku, CatalogItem>,
    customers: BTreeMap<CustomerId, CustomerProfile>,
    inventory: BTreeMap<(Sku, WarehouseId), InventoryPosition>,
    payment_authorizations: BTreeMap<OrderId, PaymentAuthorization>,
    outbox: Vec<DomainEvent>,
    next_payment: u64,
}

impl InMemoryCommercePlatform {
    pub fn new() -> Self {
        Self {
            catalog: BTreeMap::new(),
            customers: BTreeMap::new(),
            inventory: BTreeMap::new(),
            payment_authorizations: BTreeMap::new(),
            outbox: Vec::new(),
            next_payment: 1,
        }
    }

    pub fn add_catalog_item(&mut self, item: CatalogItem) {
        self.catalog.insert(item.sku().clone(), item);
    }

    pub fn add_customer(&mut self, profile: CustomerProfile) {
        self.customers.insert(profile.id().clone(), profile);
    }

    pub fn add_inventory(&mut self, position: InventoryPosition) {
        self.inventory.insert(
            (position.sku().clone(), position.warehouse_id().clone()),
            position,
        );
    }

    pub fn outbox(&self) -> &[DomainEvent] {
        &self.outbox
    }

    pub fn inventory_snapshot(&self) -> BTreeMap<String, u32> {
        self.inventory
            .iter()
            .map(|((sku, warehouse), position)| {
                (
                    format!("{}@{}", sku.as_str(), warehouse.as_str()),
                    position.available().units(),
                )
            })
            .collect()
    }

    fn payment_id(&mut self) -> Result<PaymentId, AppError> {
        let id = PaymentId::new(format!("pay-{}", self.next_payment))?;
        self.next_payment += 1;
        Ok(id)
    }
}

impl Default for InMemoryCommercePlatform {
    fn default() -> Self {
        Self::new()
    }
}

impl CatalogPort for InMemoryCommercePlatform {
    fn find_item(&self, sku: &Sku) -> Result<CatalogItem, AppError> {
        self.catalog
            .get(sku)
            .cloned()
            .ok_or_else(|| AppError::NotFound {
                entity: "catalog item",
                key: sku.as_str().to_string(),
            })
    }
}

impl CustomerPort for InMemoryCommercePlatform {
    fn find_customer(&self, customer_id: &CustomerId) -> Result<CustomerProfile, AppError> {
        self.customers
            .get(customer_id)
            .cloned()
            .ok_or_else(|| AppError::NotFound {
                entity: "customer",
                key: customer_id.as_str().to_string(),
            })
    }
}

impl InventoryPort for InMemoryCommercePlatform {
    fn choose_warehouse(&self, sku: &Sku, quantity: Quantity) -> Result<WarehouseId, AppError> {
        self.inventory
            .iter()
            .find(|((candidate_sku, _warehouse), position)| {
                candidate_sku == sku && position.available().units() >= quantity.units()
            })
            .map(|((_sku, warehouse), _position)| warehouse.clone())
            .ok_or_else(|| AppError::InventoryUnavailable {
                sku: sku.as_str().to_string(),
                requested: quantity.units(),
            })
    }

    fn reserve(
        &mut self,
        order_id: &OrderId,
        lines: &[crate::domain::OrderLine],
    ) -> Result<InventoryReservation, AppError> {
        let reservation = ReservationAllocator::allocate(order_id, lines, |sku, quantity| {
            self.choose_warehouse(sku, quantity)
        })?;
        for line in reservation.lines() {
            let key = (line.sku().clone(), line.warehouse_id().clone());
            let position =
                self.inventory
                    .get_mut(&key)
                    .ok_or_else(|| AppError::InventoryUnavailable {
                        sku: line.sku().as_str().to_string(),
                        requested: line.quantity().units(),
                    })?;
            position.reserve(line.quantity())?;
        }
        Ok(reservation)
    }
}

impl PaymentPort for InMemoryCommercePlatform {
    fn authorize(
        &mut self,
        order: &Order,
        amount: Money,
        risk: &RiskAssessment,
    ) -> Result<PaymentAuthorization, AppError> {
        if let Some(existing) = self.payment_authorizations.get(order.id()) {
            return Ok(existing.clone());
        }
        let status = if risk.score > 85 {
            PaymentStatus::RequiresReview
        } else {
            PaymentStatus::Authorized
        };
        let payment = PaymentAuthorization::new(
            self.payment_id()?,
            order.id().clone(),
            amount,
            status,
            if status == PaymentStatus::Authorized {
                "authorized"
            } else {
                "manual review"
            },
        );
        self.payment_authorizations
            .insert(order.id().clone(), payment.clone());
        Ok(payment)
    }
}

impl ShippingPort for InMemoryCommercePlatform {
    fn plan_shipment(
        &self,
        order: &Order,
        reservation: &InventoryReservation,
    ) -> Result<ShipmentPlan, AppError> {
        let mut legs = Vec::new();
        for line in reservation.lines() {
            let carrier = if order.contains_hazardous_material() {
                "hazmat-ground"
            } else if order.service_level() == ServiceLevel::Overnight {
                "air-priority"
            } else {
                "ground-economy"
            };
            let days = match order.service_level() {
                ServiceLevel::Standard => 5,
                ServiceLevel::Expedited => 2,
                ServiceLevel::Overnight => 1,
            };
            legs.push(ShipmentLeg::new(
                line.warehouse_id().clone(),
                order.service_level(),
                carrier,
                days,
            )?);
        }
        let id = ShipmentId::new(format!("ship-for-{}", order.id().as_str()))?;
        ShipmentPlan::new(id, order.id().clone(), legs).map_err(AppError::from)
    }
}

impl RiskPort for InMemoryCommercePlatform {
    fn assess(
        &self,
        customer: &CustomerProfile,
        order: &Order,
    ) -> Result<RiskAssessment, AppError> {
        let mut score = order.service_level().risk_weight() * 5;
        let mut reasons = Vec::new();
        if customer.account_age_days() < 30 {
            score += 35;
            reasons.push("new-account".to_string());
        }
        if order.contains_hazardous_material() {
            score += 15;
            reasons.push("hazmat".to_string());
        }
        if order.ship_to().is_cross_border_from("US") {
            score += 20;
            reasons.push("cross-border".to_string());
        }
        if customer.is_vip() && score > 10 {
            score -= 10;
        }
        if score >= 90 {
            Ok(RiskAssessment::reject(score, reasons))
        } else if score >= 45 {
            Ok(RiskAssessment::review(score, reasons))
        } else {
            Ok(RiskAssessment::accept(score))
        }
    }
}

impl OutboxPort for InMemoryCommercePlatform {
    fn publish(&mut self, event: DomainEvent) -> Result<(), AppError> {
        self.outbox.push(event);
        Ok(())
    }
}

pub fn sample_address() -> Result<Address, AppError> {
    Ok(Address::new(
        "1 Market",
        "San Francisco",
        "CA",
        "94105",
        "US",
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Currency, Money};

    #[test]
    fn inventory_snapshot_shows_warehouse_locality() -> Result<(), AppError> {
        let mut platform = InMemoryCommercePlatform::new();
        platform.add_inventory(InventoryPosition::new(
            Sku::new("KIT-RED")?,
            WarehouseId::new("west-1")?,
            Quantity::new(10)?,
        ));

        let snapshot = platform.inventory_snapshot();

        assert_eq!(snapshot.get("KIT-RED@west-1"), Some(&10));
        Ok(())
    }

    #[test]
    fn catalog_adapter_returns_not_found_for_unknown_sku() -> Result<(), AppError> {
        let platform = InMemoryCommercePlatform::new();
        let result = platform.find_item(&Sku::new("missing")?);

        assert!(matches!(
            result,
            Err(AppError::NotFound {
                entity: "catalog item",
                ..
            })
        ));
        Ok(())
    }

    #[test]
    fn platform_can_hold_catalog_item() -> Result<(), AppError> {
        let mut platform = InMemoryCommercePlatform::new();
        let item = CatalogItem::new(
            Sku::new("KIT")?,
            "Kit",
            Money::new(1000, Currency::Usd)?,
            300,
            false,
        )?;
        platform.add_catalog_item(item.clone());
        assert_eq!(platform.find_item(item.sku())?.title(), "Kit");
        Ok(())
    }
}
