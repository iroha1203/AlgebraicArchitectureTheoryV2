use std::error::Error;
use std::fmt;

use crate::domain::{
    Address, CatalogItem, CustomerId, CustomerProfile, DomainError, DomainEvent,
    FulfillmentDecision, InventoryReservation, Money, Order, OrderId, OrderLine, OrderPricing,
    PaymentAuthorization, PaymentStatus, Quantity, ReservationLine, RiskAssessment, RiskDecision,
    ServiceLevel, ShipmentPlan, Sku, WarehouseId, VIP_LOYALTY_DISCOUNT_BPS,
};
use crate::policy::{PolicyContext, PolicyEngine, PolicyEvaluation, PolicyVerdict};
use crate::telemetry::{TraceEvent, TraceRecorder};

pub trait CatalogPort {
    fn find_item(&self, sku: &Sku) -> Result<CatalogItem, AppError>;
}

pub trait CustomerPort {
    fn find_customer(&self, customer_id: &CustomerId) -> Result<CustomerProfile, AppError>;
}

pub trait InventoryPort {
    fn choose_warehouse(&self, sku: &Sku, quantity: Quantity) -> Result<WarehouseId, AppError>;
    fn reserve(
        &mut self,
        order_id: &OrderId,
        lines: &[OrderLine],
    ) -> Result<InventoryReservation, AppError>;
}

pub trait PaymentPort {
    fn authorize(
        &mut self,
        order: &Order,
        amount: Money,
        risk: &RiskAssessment,
    ) -> Result<PaymentAuthorization, AppError>;
}

pub trait ShippingPort {
    fn plan_shipment(
        &self,
        order: &Order,
        reservation: &InventoryReservation,
    ) -> Result<ShipmentPlan, AppError>;
}

pub trait RiskPort {
    fn assess(&self, customer: &CustomerProfile, order: &Order)
    -> Result<RiskAssessment, AppError>;
}

pub trait OutboxPort {
    fn publish(&mut self, event: DomainEvent) -> Result<(), AppError>;
}

pub trait Platform:
    CatalogPort + CustomerPort + InventoryPort + PaymentPort + ShippingPort + RiskPort + OutboxPort
{
}

impl<T> Platform for T where
    T: CatalogPort
        + CustomerPort
        + InventoryPort
        + PaymentPort
        + ShippingPort
        + RiskPort
        + OutboxPort
{
}

#[derive(Debug, Clone)]
pub struct CheckoutLineCommand {
    pub sku: String,
    pub quantity: u32,
}

#[derive(Debug, Clone)]
pub struct CheckoutCommand {
    pub order_id: String,
    pub customer_id: String,
    pub lines: Vec<CheckoutLineCommand>,
    pub service_level: ServiceLevel,
    pub ship_to: Option<Address>,
}

#[derive(Debug, Clone)]
pub struct CheckoutOutcome {
    pub decision: FulfillmentDecision,
    pub pricing: OrderPricing,
    pub policy_evaluations: Vec<PolicyEvaluation>,
    pub trace_events: Vec<TraceEvent>,
}

pub struct CheckoutService<P> {
    platform: P,
    policy_engine: PolicyEngine,
    trace: TraceRecorder,
}

impl<P> CheckoutService<P>
where
    P: Platform,
{
    pub fn new(platform: P, policy_engine: PolicyEngine) -> Self {
        Self {
            platform,
            policy_engine,
            trace: TraceRecorder::new("checkout-service"),
        }
    }

    pub fn execute(&mut self, command: CheckoutCommand) -> Result<CheckoutOutcome, AppError> {
        self.trace.record(
            "command.accepted",
            "checkout command accepted by application service",
        );
        let customer_id = CustomerId::new(command.customer_id)?;
        let order_id = OrderId::new(command.order_id)?;
        let customer = self.platform.find_customer(&customer_id)?;
        self.trace
            .record("customer.loaded", customer.email_domain());
        let ship_to = command
            .ship_to
            .unwrap_or_else(|| customer.default_address().clone());
        let mut order_lines = Vec::with_capacity(command.lines.len());
        for line in command.lines {
            let sku = Sku::new(line.sku)?;
            let quantity = Quantity::new(line.quantity)?;
            let item = self.platform.find_item(&sku)?;
            order_lines.push(OrderLine::from_catalog(&item, quantity));
        }
        let mut order = Order::new(
            order_id,
            customer_id,
            order_lines,
            command.service_level,
            ship_to,
        )?;
        let discount_bps = if customer.is_vip() {
            VIP_LOYALTY_DISCOUNT_BPS
        } else {
            0
        };
        let pricing = order.pricing(discount_bps)?;
        self.trace.record(
            "order.priced",
            format!(
                "{} {}",
                pricing.total_due().cents(),
                pricing.total_due().currency().code()
            ),
        );
        self.platform.publish(DomainEvent::OrderPriced {
            order_id: order.id().as_str().to_string(),
            amount_cents: pricing.total_due().cents(),
        })?;

        let risk = self.platform.assess(&customer, &order)?;
        self.trace.record(
            "risk.assessed",
            format!("score={} decision={:?}", risk.score, risk.decision),
        );
        if risk.decision == RiskDecision::Reject {
            return Err(AppError::RiskRejected { score: risk.score });
        }

        let context = PolicyContext::new(&order, &risk);
        let policy_evaluations = self.policy_engine.evaluate(&context);
        if self.policy_engine.blocking_count(&policy_evaluations) > 0 {
            return Err(AppError::PolicyBlocked {
                blocked_rules: policy_evaluations
                    .iter()
                    .filter(|evaluation| evaluation.verdict == PolicyVerdict::Blocked)
                    .map(|evaluation| evaluation.rule_id.to_string())
                    .collect(),
            });
        }
        self.trace.record(
            "policy.evaluated",
            format!("{} rules", policy_evaluations.len()),
        );

        let reservation = self.platform.reserve(order.id(), order.lines())?;
        order.mark_reserved();
        self.platform.publish(DomainEvent::InventoryReserved {
            order_id: order.id().as_str().to_string(),
            line_count: reservation.lines().len(),
        })?;
        self.trace.record(
            "inventory.reserved",
            format!("{} lines", reservation.lines().len()),
        );

        let payment = self.platform.authorize(&order, pricing.total_due(), &risk)?;
        if payment.status() != PaymentStatus::Authorized {
            return Err(AppError::PaymentDeclined {
                order_id: order.id().as_str().to_string(),
                message: payment.processor_message().to_string(),
            });
        }
        order.mark_authorized();
        self.platform.publish(DomainEvent::PaymentAuthorized {
            order_id: order.id().as_str().to_string(),
            payment_id: payment.id().as_str().to_string(),
        })?;
        self.trace
            .record("payment.authorized", payment.id().as_str());

        let shipment = self.platform.plan_shipment(&order, &reservation)?;
        order.mark_planned();
        self.platform.publish(DomainEvent::ShipmentPlanned {
            order_id: order.id().as_str().to_string(),
            shipment_id: shipment.id().as_str().to_string(),
        })?;
        self.trace
            .record("shipment.planned", shipment.id().as_str());

        order.mark_released();
        self.platform.publish(DomainEvent::FulfillmentReleased {
            order_id: order.id().as_str().to_string(),
        })?;
        self.trace
            .record("fulfillment.released", order.id().as_str());

        let decision = FulfillmentDecision {
            order,
            reservation,
            payment,
            shipment,
            risk,
        };
        Ok(CheckoutOutcome {
            decision,
            pricing,
            policy_evaluations,
            trace_events: self.trace.events().to_vec(),
        })
    }

    pub fn into_platform(self) -> P {
        self.platform
    }
}

pub struct ReservationAllocator;

impl ReservationAllocator {
    pub fn allocate(
        order_id: &OrderId,
        lines: &[OrderLine],
        warehouse_for_line: impl Fn(&Sku, Quantity) -> Result<WarehouseId, AppError>,
    ) -> Result<InventoryReservation, AppError> {
        let mut reservation_lines = Vec::with_capacity(lines.len());
        for line in lines {
            let warehouse_id = warehouse_for_line(line.sku(), line.quantity())?;
            reservation_lines.push(ReservationLine::new(
                line.sku().clone(),
                warehouse_id,
                line.quantity(),
            ));
        }
        Ok(InventoryReservation::new(
            order_id.clone(),
            reservation_lines,
        )?)
    }
}

#[derive(Debug)]
pub enum AppError {
    Domain(DomainError),
    NotFound {
        entity: &'static str,
        key: String,
    },
    InventoryUnavailable {
        sku: String,
        requested: u32,
    },
    PaymentDeclined {
        order_id: String,
        message: String,
    },
    RiskRejected {
        score: u32,
    },
    PolicyBlocked {
        blocked_rules: Vec<String>,
    },
    Integration {
        adapter: &'static str,
        message: String,
    },
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Domain(error) => write!(f, "{error}"),
            Self::NotFound { entity, key } => write!(f, "{entity} {key} was not found"),
            Self::InventoryUnavailable { sku, requested } => {
                write!(f, "sku {sku} does not have {requested} units available")
            }
            Self::PaymentDeclined { order_id, message } => {
                write!(f, "payment for order {order_id} was declined: {message}")
            }
            Self::RiskRejected { score } => write!(f, "risk score {score} rejected the order"),
            Self::PolicyBlocked { blocked_rules } => {
                write!(f, "policy blocked checkout: {}", blocked_rules.join(","))
            }
            Self::Integration { adapter, message } => {
                write!(f, "{adapter} integration failed: {message}")
            }
        }
    }
}

impl Error for AppError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Domain(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DomainError> for AppError {
    fn from(error: DomainError) -> Self {
        Self::Domain(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scenario::build_demo_platform;

    #[test]
    fn checkout_service_completes_happy_path() -> Result<(), AppError> {
        let platform = build_demo_platform()?;
        let mut service = CheckoutService::new(platform, PolicyEngine::standard());
        let outcome = service.execute(CheckoutCommand {
            order_id: "order-100".to_string(),
            customer_id: "customer-1".to_string(),
            lines: vec![CheckoutLineCommand {
                sku: "KIT-RED".to_string(),
                quantity: 2,
            }],
            service_level: ServiceLevel::Expedited,
            ship_to: None,
        })?;

        assert_eq!(outcome.decision.reservation.lines().len(), 1);
        assert!(
            outcome
                .policy_evaluations
                .iter()
                .any(|evaluation| evaluation.verdict == PolicyVerdict::Satisfied)
        );
        assert!(outcome.trace_events.len() >= 6);
        Ok(())
    }
}
