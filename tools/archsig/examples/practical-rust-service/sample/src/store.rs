use std::collections::BTreeMap;

use crate::app::{InventoryStore, StorePortError};
use crate::domain::{InventoryReservation, ProductId};

#[derive(Debug, Default, Clone)]
pub struct InMemoryInventoryStore {
    stock: BTreeMap<ProductId, u32>,
    reservation_log: Vec<InventoryReservation>,
}

impl InMemoryInventoryStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_stock(&mut self, product_id: ProductId, quantity: u32) {
        let stock = self.stock.entry(product_id).or_insert(0);
        *stock += quantity;
    }

    pub fn reservation_count(&self) -> usize {
        self.reservation_log.len()
    }

    pub fn stock_snapshot(&self) -> BTreeMap<String, u32> {
        self.stock
            .iter()
            .map(|(product_id, quantity)| (product_id.as_str().to_string(), *quantity))
            .collect()
    }
}

impl InventoryStore for InMemoryInventoryStore {
    fn available_units(&self, product_id: &ProductId) -> Result<u32, StorePortError> {
        self.stock
            .get(product_id)
            .copied()
            .ok_or_else(|| StorePortError::ProductNotFound {
                product_id: product_id.as_str().to_string(),
            })
    }

    fn reserve(&mut self, reservation: &InventoryReservation) -> Result<(), StorePortError> {
        for line in reservation.lines() {
            let product_id = line.product_id();
            let available = self.available_units(product_id)?;
            if available < line.quantity() {
                return Err(StorePortError::ReservationConflict {
                    product_id: product_id.as_str().to_string(),
                });
            }
        }

        for line in reservation.lines() {
            let product_id = line.product_id();
            let available = self.available_units(product_id)?;
            self.stock
                .insert(product_id.clone(), available - line.quantity());
        }
        self.reservation_log.push(reservation.clone());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{InventoryReservation, Order, OrderId, OrderLine};

    #[test]
    fn reserve_decrements_stock() -> Result<(), Box<dyn std::error::Error>> {
        let product_id = ProductId::new("sku-1")?;
        let mut store = InMemoryInventoryStore::new();
        store.add_stock(product_id.clone(), 5);
        let order = Order::new(
            OrderId::new("order-1")?,
            vec![OrderLine::new(product_id.clone(), 2)?],
        )?;
        let reservation = InventoryReservation::for_order(&order)?;

        store.reserve(&reservation)?;

        assert_eq!(store.available_units(&product_id)?, 3);
        assert_eq!(store.reservation_count(), 1);
        Ok(())
    }

    #[test]
    fn reserve_rejects_stale_reservation_after_stock_changes()
    -> Result<(), Box<dyn std::error::Error>> {
        let product_id = ProductId::new("sku-1")?;
        let mut store = InMemoryInventoryStore::new();
        store.add_stock(product_id.clone(), 1);
        let first_order = Order::new(
            OrderId::new("order-1")?,
            vec![OrderLine::new(product_id.clone(), 1)?],
        )?;
        let second_order = Order::new(
            OrderId::new("order-2")?,
            vec![OrderLine::new(product_id.clone(), 1)?],
        )?;
        let first_reservation = InventoryReservation::for_order(&first_order)?;
        let stale_reservation = InventoryReservation::for_order(&second_order)?;

        store.reserve(&first_reservation)?;
        let result = store.reserve(&stale_reservation);

        assert!(matches!(
            result,
            Err(StorePortError::ReservationConflict { .. })
        ));
        assert_eq!(store.available_units(&product_id)?, 0);
        assert_eq!(store.reservation_count(), 1);
        Ok(())
    }
}
