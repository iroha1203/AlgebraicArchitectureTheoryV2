use std::error::Error;
use std::fmt;

use crate::domain::{DomainError, InventoryReservation, Order, ProductId};

pub trait InventoryStore {
    fn available_units(&self, product_id: &ProductId) -> Result<u32, StorePortError>;
    fn reserve(&mut self, reservation: &InventoryReservation) -> Result<(), StorePortError>;
}

pub struct OrderService<S> {
    store: S,
}

impl<S> OrderService<S>
where
    S: InventoryStore,
{
    pub fn new(store: S) -> Self {
        Self { store }
    }

    pub fn place_order(&mut self, order: Order) -> Result<OrderReceipt, AppError> {
        let reservation = InventoryReservation::for_order(&order)?;

        for line in reservation.lines() {
            let available = self.store.available_units(line.product_id())?;
            if available < line.quantity() {
                return Err(AppError::InsufficientInventory {
                    product_id: line.product_id().as_str().to_string(),
                    requested: line.quantity(),
                    available,
                });
            }
        }

        self.store.reserve(&reservation)?;
        Ok(OrderReceipt {
            order_id: order.id().as_str().to_string(),
            reserved_line_count: reservation.lines().len(),
            reserved_unit_count: order.total_quantity(),
        })
    }

    pub fn into_store(self) -> S {
        self.store
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderReceipt {
    pub order_id: String,
    pub reserved_line_count: usize,
    pub reserved_unit_count: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorePortError {
    ProductNotFound { product_id: String },
    ReservationConflict { product_id: String },
}

impl fmt::Display for StorePortError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ProductNotFound { product_id } => {
                write!(f, "product {product_id} was not found")
            }
            Self::ReservationConflict { product_id } => {
                write!(
                    f,
                    "inventory for product {product_id} changed before reservation"
                )
            }
        }
    }
}

impl Error for StorePortError {}

#[derive(Debug)]
pub enum AppError {
    Domain(DomainError),
    Store(StorePortError),
    InsufficientInventory {
        product_id: String,
        requested: u32,
        available: u32,
    },
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Domain(error) => write!(f, "{error}"),
            Self::Store(error) => write!(f, "{error}"),
            Self::InsufficientInventory {
                product_id,
                requested,
                available,
            } => write!(
                f,
                "product {product_id} has {available} units available, requested {requested}"
            ),
        }
    }
}

impl Error for AppError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Domain(error) => Some(error),
            Self::Store(error) => Some(error),
            Self::InsufficientInventory { .. } => None,
        }
    }
}

impl From<DomainError> for AppError {
    fn from(error: DomainError) -> Self {
        Self::Domain(error)
    }
}

impl From<StorePortError> for AppError {
    fn from(error: StorePortError) -> Self {
        Self::Store(error)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::domain::{OrderId, OrderLine};

    struct FakeStore {
        stock: BTreeMap<ProductId, u32>,
        reserved: Vec<InventoryReservation>,
    }

    impl FakeStore {
        fn with_stock(stock: BTreeMap<ProductId, u32>) -> Self {
            Self {
                stock,
                reserved: Vec::new(),
            }
        }
    }

    impl InventoryStore for FakeStore {
        fn available_units(&self, product_id: &ProductId) -> Result<u32, StorePortError> {
            self.stock
                .get(product_id)
                .copied()
                .ok_or_else(|| StorePortError::ProductNotFound {
                    product_id: product_id.as_str().to_string(),
                })
        }

        fn reserve(&mut self, reservation: &InventoryReservation) -> Result<(), StorePortError> {
            self.reserved.push(reservation.clone());
            Ok(())
        }
    }

    #[test]
    fn place_order_reserves_inventory() -> Result<(), AppError> {
        let product_id = ProductId::new("sku-1")?;
        let mut stock = BTreeMap::new();
        stock.insert(product_id.clone(), 3);
        let store = FakeStore::with_stock(stock);
        let mut service = OrderService::new(store);
        let order = Order::new(
            OrderId::new("order-1")?,
            vec![OrderLine::new(product_id, 2)?],
        )?;

        let receipt = service.place_order(order)?;
        let store = service.into_store();

        assert_eq!(receipt.order_id, "order-1");
        assert_eq!(receipt.reserved_line_count, 1);
        assert_eq!(receipt.reserved_unit_count, 2);
        assert_eq!(store.reserved.len(), 1);
        Ok(())
    }

    #[test]
    fn place_order_rejects_unavailable_inventory() -> Result<(), AppError> {
        let product_id = ProductId::new("sku-1")?;
        let mut stock = BTreeMap::new();
        stock.insert(product_id.clone(), 1);
        let store = FakeStore::with_stock(stock);
        let mut service = OrderService::new(store);
        let order = Order::new(
            OrderId::new("order-1")?,
            vec![OrderLine::new(product_id, 2)?],
        )?;

        let result = service.place_order(order);

        assert!(matches!(
            result,
            Err(AppError::InsufficientInventory { .. })
        ));
        Ok(())
    }
}
