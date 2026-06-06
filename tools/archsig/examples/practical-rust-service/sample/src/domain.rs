use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProductId(String);

impl ProductId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyProductId);
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderId(String);

impl OrderId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyOrderId);
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderLine {
    product_id: ProductId,
    quantity: u32,
}

impl OrderLine {
    pub fn new(product_id: ProductId, quantity: u32) -> Result<Self, DomainError> {
        if quantity == 0 {
            return Err(DomainError::ZeroQuantity {
                product_id: product_id.as_str().to_string(),
            });
        }
        Ok(Self {
            product_id,
            quantity,
        })
    }

    pub fn product_id(&self) -> &ProductId {
        &self.product_id
    }

    pub fn quantity(&self) -> u32 {
        self.quantity
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Order {
    id: OrderId,
    lines: Vec<OrderLine>,
}

impl Order {
    pub fn new(id: OrderId, lines: Vec<OrderLine>) -> Result<Self, DomainError> {
        if lines.is_empty() {
            return Err(DomainError::EmptyOrder {
                order_id: id.as_str().to_string(),
            });
        }
        Ok(Self { id, lines })
    }

    pub fn id(&self) -> &OrderId {
        &self.id
    }

    pub fn lines(&self) -> &[OrderLine] {
        &self.lines
    }

    pub fn total_quantity(&self) -> u32 {
        self.lines.iter().map(OrderLine::quantity).sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReservationLine {
    product_id: ProductId,
    quantity: u32,
}

impl ReservationLine {
    pub fn new(product_id: ProductId, quantity: u32) -> Result<Self, DomainError> {
        if quantity == 0 {
            return Err(DomainError::ZeroQuantity {
                product_id: product_id.as_str().to_string(),
            });
        }
        Ok(Self {
            product_id,
            quantity,
        })
    }

    pub fn product_id(&self) -> &ProductId {
        &self.product_id
    }

    pub fn quantity(&self) -> u32 {
        self.quantity
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InventoryReservation {
    order_id: OrderId,
    lines: Vec<ReservationLine>,
}

impl InventoryReservation {
    pub fn for_order(order: &Order) -> Result<Self, DomainError> {
        let mut lines = Vec::with_capacity(order.lines().len());
        for line in order.lines() {
            lines.push(ReservationLine::new(
                line.product_id().clone(),
                line.quantity(),
            )?);
        }
        Ok(Self {
            order_id: order.id().clone(),
            lines,
        })
    }

    pub fn order_id(&self) -> &OrderId {
        &self.order_id
    }

    pub fn lines(&self) -> &[ReservationLine] {
        &self.lines
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainError {
    EmptyProductId,
    EmptyOrderId,
    EmptyOrder { order_id: String },
    ZeroQuantity { product_id: String },
}

impl fmt::Display for DomainError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyProductId => write!(f, "product id must not be empty"),
            Self::EmptyOrderId => write!(f, "order id must not be empty"),
            Self::EmptyOrder { order_id } => {
                write!(f, "order {order_id} must contain at least one line")
            }
            Self::ZeroQuantity { product_id } => {
                write!(
                    f,
                    "order line for product {product_id} must have positive quantity"
                )
            }
        }
    }
}

impl Error for DomainError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_requires_at_least_one_line() -> Result<(), DomainError> {
        let order_id = OrderId::new("order-1")?;
        let result = Order::new(order_id, Vec::new());
        assert!(matches!(result, Err(DomainError::EmptyOrder { .. })));
        Ok(())
    }

    #[test]
    fn reservation_preserves_order_lines() -> Result<(), DomainError> {
        let sku = ProductId::new("sku-1")?;
        let order = Order::new(
            OrderId::new("order-1")?,
            vec![OrderLine::new(sku.clone(), 2)?],
        )?;

        let reservation = InventoryReservation::for_order(&order)?;

        assert_eq!(reservation.order_id().as_str(), "order-1");
        assert_eq!(reservation.lines().len(), 1);
        assert_eq!(reservation.lines()[0].product_id(), &sku);
        assert_eq!(reservation.lines()[0].quantity(), 2);
        Ok(())
    }
}
