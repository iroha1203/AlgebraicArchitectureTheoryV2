use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CustomerId(String);

impl CustomerId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "customer_id",
            });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrderId(String);

impl OrderId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField { field: "order_id" });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sku(String);

impl Sku {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField { field: "sku" });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WarehouseId(String);

impl WarehouseId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "warehouse_id",
            });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PaymentId(String);

impl PaymentId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "payment_id",
            });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShipmentId(String);

impl ShipmentId {
    pub fn new(value: impl Into<String>) -> Result<Self, DomainError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "shipment_id",
            });
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Currency {
    Usd,
    Eur,
    Jpy,
}

impl Currency {
    pub fn code(self) -> &'static str {
        match self {
            Self::Usd => "USD",
            Self::Eur => "EUR",
            Self::Jpy => "JPY",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Money {
    cents: i64,
    currency: Currency,
}

impl Money {
    pub fn new(cents: i64, currency: Currency) -> Result<Self, DomainError> {
        if cents < 0 {
            return Err(DomainError::NegativeMoney { cents });
        }
        Ok(Self { cents, currency })
    }

    pub fn zero(currency: Currency) -> Self {
        Self { cents: 0, currency }
    }

    pub fn cents(self) -> i64 {
        self.cents
    }

    pub fn currency(self) -> Currency {
        self.currency
    }

    pub fn checked_add(self, other: Money) -> Result<Money, DomainError> {
        if self.currency != other.currency {
            return Err(DomainError::CurrencyMismatch {
                left: self.currency.code(),
                right: other.currency.code(),
            });
        }
        Ok(Money {
            cents: self.cents + other.cents,
            currency: self.currency,
        })
    }

    pub fn multiply(self, quantity: Quantity) -> Result<Money, DomainError> {
        Ok(Money {
            cents: self.cents * quantity.units() as i64,
            currency: self.currency,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quantity(u32);

impl Quantity {
    pub fn new(units: u32) -> Result<Self, DomainError> {
        if units == 0 {
            return Err(DomainError::ZeroQuantity);
        }
        Ok(Self(units))
    }

    pub fn zero() -> Self {
        Self(0)
    }

    pub fn units(self) -> u32 {
        self.0
    }

    pub fn checked_sub(self, other: Quantity) -> Result<Quantity, DomainError> {
        if self.0 < other.0 {
            return Err(DomainError::QuantityUnderflow {
                available: self.0,
                requested: other.0,
            });
        }
        let remaining = self.0 - other.0;
        if remaining == 0 {
            Ok(Quantity::zero())
        } else {
            Quantity::new(remaining)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServiceLevel {
    Standard,
    Expedited,
    Overnight,
}

impl ServiceLevel {
    pub fn risk_weight(self) -> u32 {
        match self {
            Self::Standard => 1,
            Self::Expedited => 2,
            Self::Overnight => 4,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
    pub line1: String,
    pub city: String,
    pub region: String,
    pub postal_code: String,
    pub country: String,
}

impl Address {
    pub fn new(
        line1: impl Into<String>,
        city: impl Into<String>,
        region: impl Into<String>,
        postal_code: impl Into<String>,
        country: impl Into<String>,
    ) -> Result<Self, DomainError> {
        let address = Self {
            line1: line1.into(),
            city: city.into(),
            region: region.into(),
            postal_code: postal_code.into(),
            country: country.into(),
        };
        if address.line1.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "address.line1",
            });
        }
        if address.city.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "address.city",
            });
        }
        if address.country.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "address.country",
            });
        }
        Ok(address)
    }

    pub fn is_cross_border_from(&self, origin_country: &str) -> bool {
        self.country != origin_country
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustomerProfile {
    id: CustomerId,
    email: String,
    default_address: Address,
    vip: bool,
    account_age_days: u32,
}

impl CustomerProfile {
    pub fn new(
        id: CustomerId,
        email: impl Into<String>,
        default_address: Address,
        vip: bool,
        account_age_days: u32,
    ) -> Result<Self, DomainError> {
        let email = email.into();
        if !email.contains('@') {
            return Err(DomainError::InvalidEmail);
        }
        Ok(Self {
            id,
            email,
            default_address,
            vip,
            account_age_days,
        })
    }

    pub fn id(&self) -> &CustomerId {
        &self.id
    }

    pub fn default_address(&self) -> &Address {
        &self.default_address
    }

    pub fn is_vip(&self) -> bool {
        self.vip
    }

    pub fn account_age_days(&self) -> u32 {
        self.account_age_days
    }

    pub fn email_domain(&self) -> &str {
        self.email.split('@').nth(1).unwrap_or("")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CatalogItem {
    sku: Sku,
    title: String,
    price: Money,
    weight_grams: u32,
    hazardous: bool,
}

impl CatalogItem {
    pub fn new(
        sku: Sku,
        title: impl Into<String>,
        price: Money,
        weight_grams: u32,
        hazardous: bool,
    ) -> Result<Self, DomainError> {
        let title = title.into();
        if title.trim().is_empty() {
            return Err(DomainError::EmptyField {
                field: "catalog.title",
            });
        }
        if weight_grams == 0 {
            return Err(DomainError::InvalidWeight);
        }
        Ok(Self {
            sku,
            title,
            price,
            weight_grams,
            hazardous,
        })
    }

    pub fn sku(&self) -> &Sku {
        &self.sku
    }

    pub fn title(&self) -> &str {
        &self.title
    }

    pub fn price(&self) -> Money {
        self.price
    }

    pub fn weight_grams(&self) -> u32 {
        self.weight_grams
    }

    pub fn hazardous(&self) -> bool {
        self.hazardous
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderLine {
    sku: Sku,
    quantity: Quantity,
    unit_price: Money,
    weight_grams: u32,
    hazardous: bool,
}

impl OrderLine {
    pub fn from_catalog(item: &CatalogItem, quantity: Quantity) -> Self {
        Self {
            sku: item.sku().clone(),
            quantity,
            unit_price: item.price(),
            weight_grams: item.weight_grams(),
            hazardous: item.hazardous(),
        }
    }

    pub fn sku(&self) -> &Sku {
        &self.sku
    }

    pub fn quantity(&self) -> Quantity {
        self.quantity
    }

    pub fn line_total(&self) -> Result<Money, DomainError> {
        self.unit_price.multiply(self.quantity)
    }

    pub fn total_weight_grams(&self) -> u32 {
        self.weight_grams * self.quantity.units()
    }

    pub fn hazardous(&self) -> bool {
        self.hazardous
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderStatus {
    Draft,
    Priced,
    Reserved,
    Authorized,
    Planned,
    Released,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    lines: Vec<OrderLine>,
    service_level: ServiceLevel,
    ship_to: Address,
    status: OrderStatus,
}

impl Order {
    pub fn new(
        id: OrderId,
        customer_id: CustomerId,
        lines: Vec<OrderLine>,
        service_level: ServiceLevel,
        ship_to: Address,
    ) -> Result<Self, DomainError> {
        if lines.is_empty() {
            return Err(DomainError::EmptyOrder);
        }
        Ok(Self {
            id,
            customer_id,
            lines,
            service_level,
            ship_to,
            status: OrderStatus::Priced,
        })
    }

    pub fn id(&self) -> &OrderId {
        &self.id
    }

    pub fn customer_id(&self) -> &CustomerId {
        &self.customer_id
    }

    pub fn lines(&self) -> &[OrderLine] {
        &self.lines
    }

    pub fn service_level(&self) -> ServiceLevel {
        self.service_level
    }

    pub fn ship_to(&self) -> &Address {
        &self.ship_to
    }

    pub fn status(&self) -> OrderStatus {
        self.status
    }

    pub fn mark_reserved(&mut self) {
        self.status = OrderStatus::Reserved;
    }

    pub fn mark_authorized(&mut self) {
        self.status = OrderStatus::Authorized;
    }

    pub fn mark_planned(&mut self) {
        self.status = OrderStatus::Planned;
    }

    pub fn mark_released(&mut self) {
        self.status = OrderStatus::Released;
    }

    pub fn subtotal(&self) -> Result<Money, DomainError> {
        let currency = self.lines[0].unit_price.currency();
        self.lines
            .iter()
            .try_fold(Money::zero(currency), |acc, line| {
                acc.checked_add(line.line_total()?)
            })
    }

    pub fn total_weight_grams(&self) -> u32 {
        self.lines.iter().map(OrderLine::total_weight_grams).sum()
    }

    pub fn contains_hazardous_material(&self) -> bool {
        self.lines.iter().any(OrderLine::hazardous)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InventoryPosition {
    sku: Sku,
    warehouse_id: WarehouseId,
    available: Quantity,
    reserved_units: u32,
}

impl InventoryPosition {
    pub fn new(sku: Sku, warehouse_id: WarehouseId, available: Quantity) -> Self {
        Self {
            sku,
            warehouse_id,
            available,
            reserved_units: 0,
        }
    }

    pub fn sku(&self) -> &Sku {
        &self.sku
    }

    pub fn warehouse_id(&self) -> &WarehouseId {
        &self.warehouse_id
    }

    pub fn available(&self) -> Quantity {
        self.available
    }

    pub fn reserve(&mut self, quantity: Quantity) -> Result<(), DomainError> {
        if self.available.units() < quantity.units() {
            return Err(DomainError::QuantityUnderflow {
                available: self.available.units(),
                requested: quantity.units(),
            });
        }
        self.available = self.available.checked_sub(quantity)?;
        self.reserved_units += quantity.units();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReservationLine {
    sku: Sku,
    warehouse_id: WarehouseId,
    quantity: Quantity,
}

impl ReservationLine {
    pub fn new(sku: Sku, warehouse_id: WarehouseId, quantity: Quantity) -> Self {
        Self {
            sku,
            warehouse_id,
            quantity,
        }
    }

    pub fn sku(&self) -> &Sku {
        &self.sku
    }

    pub fn warehouse_id(&self) -> &WarehouseId {
        &self.warehouse_id
    }

    pub fn quantity(&self) -> Quantity {
        self.quantity
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReservationStatus {
    Held,
    Released,
    Cancelled,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InventoryReservation {
    order_id: OrderId,
    lines: Vec<ReservationLine>,
    status: ReservationStatus,
}

impl InventoryReservation {
    pub fn new(order_id: OrderId, lines: Vec<ReservationLine>) -> Result<Self, DomainError> {
        if lines.is_empty() {
            return Err(DomainError::EmptyReservation);
        }
        Ok(Self {
            order_id,
            lines,
            status: ReservationStatus::Held,
        })
    }

    pub fn order_id(&self) -> &OrderId {
        &self.order_id
    }

    pub fn lines(&self) -> &[ReservationLine] {
        &self.lines
    }

    pub fn status(&self) -> ReservationStatus {
        self.status
    }

    pub fn mark_released(&mut self) {
        self.status = ReservationStatus::Released;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PaymentStatus {
    Authorized,
    Declined,
    RequiresReview,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PaymentAuthorization {
    id: PaymentId,
    order_id: OrderId,
    amount: Money,
    status: PaymentStatus,
    processor_message: String,
}

impl PaymentAuthorization {
    pub fn new(
        id: PaymentId,
        order_id: OrderId,
        amount: Money,
        status: PaymentStatus,
        processor_message: impl Into<String>,
    ) -> Self {
        Self {
            id,
            order_id,
            amount,
            status,
            processor_message: processor_message.into(),
        }
    }

    pub fn id(&self) -> &PaymentId {
        &self.id
    }

    pub fn order_id(&self) -> &OrderId {
        &self.order_id
    }

    pub fn amount(&self) -> Money {
        self.amount
    }

    pub fn status(&self) -> PaymentStatus {
        self.status
    }

    pub fn processor_message(&self) -> &str {
        &self.processor_message
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShipmentLeg {
    warehouse_id: WarehouseId,
    service_level: ServiceLevel,
    carrier: String,
    estimated_days: u32,
}

impl ShipmentLeg {
    pub fn new(
        warehouse_id: WarehouseId,
        service_level: ServiceLevel,
        carrier: impl Into<String>,
        estimated_days: u32,
    ) -> Result<Self, DomainError> {
        let carrier = carrier.into();
        if carrier.trim().is_empty() {
            return Err(DomainError::EmptyField { field: "carrier" });
        }
        if estimated_days == 0 {
            return Err(DomainError::InvalidShipmentPlan);
        }
        Ok(Self {
            warehouse_id,
            service_level,
            carrier,
            estimated_days,
        })
    }

    pub fn warehouse_id(&self) -> &WarehouseId {
        &self.warehouse_id
    }

    pub fn estimated_days(&self) -> u32 {
        self.estimated_days
    }

    pub fn carrier(&self) -> &str {
        &self.carrier
    }

    pub fn service_level(&self) -> ServiceLevel {
        self.service_level
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShipmentStatus {
    Planned,
    Released,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShipmentPlan {
    id: ShipmentId,
    order_id: OrderId,
    legs: Vec<ShipmentLeg>,
    status: ShipmentStatus,
}

impl ShipmentPlan {
    pub fn new(
        id: ShipmentId,
        order_id: OrderId,
        legs: Vec<ShipmentLeg>,
    ) -> Result<Self, DomainError> {
        if legs.is_empty() {
            return Err(DomainError::InvalidShipmentPlan);
        }
        Ok(Self {
            id,
            order_id,
            legs,
            status: ShipmentStatus::Planned,
        })
    }

    pub fn id(&self) -> &ShipmentId {
        &self.id
    }

    pub fn order_id(&self) -> &OrderId {
        &self.order_id
    }

    pub fn legs(&self) -> &[ShipmentLeg] {
        &self.legs
    }

    pub fn status(&self) -> ShipmentStatus {
        self.status
    }

    pub fn mark_released(&mut self) {
        self.status = ShipmentStatus::Released;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RiskDecision {
    Accept,
    Review,
    Reject,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RiskAssessment {
    pub score: u32,
    pub decision: RiskDecision,
    pub reasons: Vec<String>,
}

impl RiskAssessment {
    pub fn accept(score: u32) -> Self {
        Self {
            score,
            decision: RiskDecision::Accept,
            reasons: Vec::new(),
        }
    }

    pub fn review(score: u32, reasons: Vec<String>) -> Self {
        Self {
            score,
            decision: RiskDecision::Review,
            reasons,
        }
    }

    pub fn reject(score: u32, reasons: Vec<String>) -> Self {
        Self {
            score,
            decision: RiskDecision::Reject,
            reasons,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FulfillmentDecision {
    pub order: Order,
    pub reservation: InventoryReservation,
    pub payment: PaymentAuthorization,
    pub shipment: ShipmentPlan,
    pub risk: RiskAssessment,
}

impl FulfillmentDecision {
    pub fn insight_tags(&self) -> Vec<&'static str> {
        let mut tags = vec![
            "order-priced",
            "inventory-held",
            "payment-authorized",
            "shipment-planned",
        ];
        if self.order.contains_hazardous_material() {
            tags.push("hazmat-policy-applied");
        }
        if self.risk.decision == RiskDecision::Review {
            tags.push("manual-review-required");
        }
        tags
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainEvent {
    OrderPriced {
        order_id: String,
        amount_cents: i64,
    },
    InventoryReserved {
        order_id: String,
        line_count: usize,
    },
    PaymentAuthorized {
        order_id: String,
        payment_id: String,
    },
    ShipmentPlanned {
        order_id: String,
        shipment_id: String,
    },
    FulfillmentReleased {
        order_id: String,
    },
}

#[derive(Debug, Clone, Default)]
pub struct OrderBook {
    orders: BTreeMap<OrderId, Order>,
}

impl OrderBook {
    pub fn insert(&mut self, order: Order) {
        self.orders.insert(order.id().clone(), order);
    }

    pub fn get(&self, order_id: &OrderId) -> Option<&Order> {
        self.orders.get(order_id)
    }

    pub fn len(&self) -> usize {
        self.orders.len()
    }

    pub fn is_empty(&self) -> bool {
        self.orders.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainError {
    EmptyField {
        field: &'static str,
    },
    EmptyOrder,
    EmptyReservation,
    InvalidEmail,
    InvalidWeight,
    InvalidShipmentPlan,
    NegativeMoney {
        cents: i64,
    },
    CurrencyMismatch {
        left: &'static str,
        right: &'static str,
    },
    ZeroQuantity,
    QuantityUnderflow {
        available: u32,
        requested: u32,
    },
}

impl fmt::Display for DomainError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyField { field } => write!(f, "{field} must not be empty"),
            Self::EmptyOrder => write!(f, "order must contain at least one line"),
            Self::EmptyReservation => write!(f, "reservation must contain at least one line"),
            Self::InvalidEmail => write!(f, "customer email must contain a domain"),
            Self::InvalidWeight => write!(f, "catalog item weight must be positive"),
            Self::InvalidShipmentPlan => {
                write!(f, "shipment plan must contain at least one valid leg")
            }
            Self::NegativeMoney { cents } => {
                write!(f, "money amount must be non-negative: {cents}")
            }
            Self::CurrencyMismatch { left, right } => {
                write!(f, "currency mismatch: {left} vs {right}")
            }
            Self::ZeroQuantity => write!(f, "quantity must be greater than zero"),
            Self::QuantityUnderflow {
                available,
                requested,
            } => write!(
                f,
                "requested {requested} units but only {available} units are available"
            ),
        }
    }
}

impl Error for DomainError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn address() -> Address {
        Address::new("1 Market", "San Francisco", "CA", "94105", "US").unwrap()
    }

    #[test]
    fn order_subtotal_preserves_money_currency() -> Result<(), DomainError> {
        let sku = Sku::new("KIT-1")?;
        let item = CatalogItem::new(
            sku,
            "starter kit",
            Money::new(2_500, Currency::Usd)?,
            1200,
            false,
        )?;
        let line = OrderLine::from_catalog(&item, Quantity::new(2)?);
        let order = Order::new(
            OrderId::new("order-1")?,
            CustomerId::new("customer-1")?,
            vec![line],
            ServiceLevel::Standard,
            address(),
        )?;

        assert_eq!(order.subtotal()?.cents(), 5_000);
        assert_eq!(order.total_weight_grams(), 2_400);
        Ok(())
    }

    #[test]
    fn reservation_rejects_empty_lines() -> Result<(), DomainError> {
        let result = InventoryReservation::new(OrderId::new("order-1")?, Vec::new());
        assert!(matches!(result, Err(DomainError::EmptyReservation)));
        Ok(())
    }
}
