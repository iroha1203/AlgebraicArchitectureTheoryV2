use std::collections::BTreeSet;

use crate::domain::{Order, RiskAssessment, RiskDecision};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicySignal {
    name: String,
    evidence: String,
}

impl PolicySignal {
    pub fn new(name: impl Into<String>, evidence: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            evidence: evidence.into(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn evidence(&self) -> &str {
        &self.evidence
    }
}

#[derive(Debug, Clone)]
pub struct PolicyContext<'a> {
    pub order: &'a Order,
    pub risk: &'a RiskAssessment,
    pub signals: Vec<PolicySignal>,
}

impl<'a> PolicyContext<'a> {
    pub fn new(order: &'a Order, risk: &'a RiskAssessment) -> Self {
        let mut signals = vec![
            PolicySignal::new(
                "catalog-price-authority",
                "order lines were built from CatalogPort items",
            ),
            PolicySignal::new(
                "inventory-port-boundary",
                "InventoryPort owns reservation side effects",
            ),
            PolicySignal::new(
                "payment-idempotency",
                "PaymentPort authorization is keyed by order id",
            ),
            PolicySignal::new(
                "dependency-inversion",
                "CheckoutService is generic over Platform ports",
            ),
            PolicySignal::new(
                "event-outbox",
                "OutboxPort receives release event after successful workflow",
            ),
            PolicySignal::new("warehouse-locality", "ReservationLine carries warehouse id"),
        ];
        if order.contains_hazardous_material() {
            signals.push(PolicySignal::new(
                "hazmat-routing",
                "hazardous order line detected",
            ));
        }
        if risk.decision == RiskDecision::Review {
            signals.push(PolicySignal::new(
                "risk-review",
                "risk service requested manual review",
            ));
        }
        Self {
            order,
            risk,
            signals,
        }
    }

    pub fn signal_names(&self) -> BTreeSet<&str> {
        self.signals.iter().map(|signal| signal.name()).collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PolicyVerdict {
    Satisfied,
    NeedsReview,
    Blocked,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyEvaluation {
    pub rule_id: &'static str,
    pub category: &'static str,
    pub verdict: PolicyVerdict,
    pub severity: &'static str,
    pub message: String,
}

#[derive(Debug, Clone, Copy)]
pub struct PolicyRuleSpec {
    pub id: &'static str,
    pub category: &'static str,
    pub statement: &'static str,
    pub severity: &'static str,
    pub required_signal: &'static str,
}

impl PolicyRuleSpec {
    pub fn evaluate(self, context: &PolicyContext<'_>) -> PolicyEvaluation {
        let signals = context.signal_names();
        if signals.contains(self.required_signal) {
            return PolicyEvaluation {
                rule_id: self.id,
                category: self.category,
                verdict: PolicyVerdict::Satisfied,
                severity: self.severity,
                message: format!(
                    "{} Evidence signal '{}' is present.",
                    self.statement, self.required_signal
                ),
            };
        }
        let verdict = if self.severity == "high" {
            PolicyVerdict::Blocked
        } else {
            PolicyVerdict::NeedsReview
        };
        PolicyEvaluation {
            rule_id: self.id,
            category: self.category,
            verdict,
            severity: self.severity,
            message: format!(
                "{} Missing signal '{}'.",
                self.statement, self.required_signal
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PolicyEngine {
    rules: Vec<PolicyRuleSpec>,
}

impl PolicyEngine {
    pub fn standard() -> Self {
        Self {
            rules: DEFAULT_POLICY_RULES.to_vec(),
        }
    }

    pub fn evaluate(&self, context: &PolicyContext<'_>) -> Vec<PolicyEvaluation> {
        self.rules
            .iter()
            .map(|rule| rule.evaluate(context))
            .collect()
    }

    pub fn blocking_count(&self, evaluations: &[PolicyEvaluation]) -> usize {
        evaluations
            .iter()
            .filter(|evaluation| evaluation.verdict == PolicyVerdict::Blocked)
            .count()
    }

    pub fn category_summary(
        &self,
        evaluations: &[PolicyEvaluation],
    ) -> Vec<(String, usize, usize)> {
        let mut categories = BTreeSet::new();
        for evaluation in evaluations {
            categories.insert(evaluation.category);
        }
        categories
            .into_iter()
            .map(|category| {
                let total = evaluations
                    .iter()
                    .filter(|evaluation| evaluation.category == category)
                    .count();
                let satisfied = evaluations
                    .iter()
                    .filter(|evaluation| {
                        evaluation.category == category
                            && evaluation.verdict == PolicyVerdict::Satisfied
                    })
                    .count();
                (category.to_string(), satisfied, total)
            })
            .collect()
    }
}

pub static DEFAULT_POLICY_RULES: &[PolicyRuleSpec] = &[
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-01",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 1 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-01",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 1 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-01",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 1 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-01",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 1 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-01",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 1 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-01",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 1 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-01",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 1 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-01",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 1 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-02",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 2 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-02",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 2 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-02",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 2 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-02",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 2 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-02",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 2 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-02",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 2 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-02",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 2 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-02",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 2 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-03",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 3 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-03",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 3 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-03",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 3 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-03",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 3 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-03",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 3 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-03",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 3 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-03",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 3 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-03",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 3 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-04",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 4 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-04",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 4 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-04",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 4 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-04",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 4 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-04",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 4 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-04",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 4 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-04",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 4 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-04",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 4 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-05",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 5 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-05",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 5 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-05",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 5 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-05",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 5 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-05",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 5 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-05",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 5 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-05",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 5 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-05",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 5 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-06",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 6 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-06",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 6 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-06",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 6 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-06",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 6 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-06",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 6 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-06",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 6 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-06",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 6 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-06",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 6 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-07",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 7 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-07",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 7 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-07",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 7 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-07",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 7 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-07",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 7 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-07",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 7 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-07",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 7 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-07",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 7 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-08",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 8 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-08",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 8 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-08",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 8 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-08",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 8 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-08",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 8 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-08",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 8 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-08",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 8 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-08",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 8 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-09",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 9 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-09",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 9 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-09",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 9 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-09",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 9 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-09",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 9 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-09",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 9 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-09",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 9 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-09",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 9 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-10",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 10 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-10",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 10 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-10",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 10 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-10",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 10 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-10",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 10 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-10",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 10 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-10",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 10 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-10",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 10 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-11",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 11 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-11",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 11 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-11",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 11 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-11",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 11 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-11",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 11 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-11",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 11 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-11",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 11 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-11",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 11 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-12",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 12 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-12",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 12 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-12",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 12 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-12",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 12 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-12",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 12 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-12",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 12 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-12",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 12 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-12",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 12 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-13",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 13 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-13",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 13 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-13",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 13 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-13",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 13 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-13",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 13 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-13",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 13 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-13",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 13 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-13",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 13 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-14",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 14 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-14",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 14 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-14",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 14 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-14",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 14 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-14",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 14 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-14",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 14 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-14",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 14 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-14",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 14 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-15",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 15 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-15",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 15 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-15",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 15 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-15",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 15 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-15",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 15 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-15",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 15 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-15",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 15 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-15",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 15 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-16",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 16 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-16",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 16 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-16",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 16 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-16",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 16 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-16",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 16 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-16",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 16 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-16",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 16 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-16",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 16 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-17",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 17 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-17",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 17 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-17",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 17 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-17",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 17 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-17",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 17 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-17",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 17 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-17",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 17 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-17",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 17 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-18",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 18 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-18",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 18 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-18",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 18 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-18",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 18 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-18",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 18 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-18",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 18 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-18",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 18 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-18",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 18 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-19",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 19 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-19",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 19 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-19",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 19 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-19",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 19 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-19",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 19 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-19",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 19 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-19",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 19 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-19",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 19 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
    PolicyRuleSpec {
        id: "policy:inventory-single-writer-20",
        category: "inventory",
        statement: "Inventory writes must stay behind InventoryPort and concrete adapters. Rule tier 20 documents the production review variant for inventory-port-boundary.",
        severity: "high",
        required_signal: "inventory-port-boundary",
    },
    PolicyRuleSpec {
        id: "policy:payment-idempotency-20",
        category: "payment",
        statement: "Payment authorization must be idempotent by order id. Rule tier 20 documents the production review variant for payment-idempotency.",
        severity: "high",
        required_signal: "payment-idempotency",
    },
    PolicyRuleSpec {
        id: "policy:shipment-hazmat-routing-20",
        category: "shipping",
        statement: "Hazardous material must use a carrier lane that accepts hazmat. Rule tier 20 documents the production review variant for hazmat-routing.",
        severity: "high",
        required_signal: "hazmat-routing",
    },
    PolicyRuleSpec {
        id: "policy:customer-risk-review-20",
        category: "risk",
        statement: "High risk customers require manual review before release. Rule tier 20 documents the production review variant for risk-review.",
        severity: "medium",
        required_signal: "risk-review",
    },
    PolicyRuleSpec {
        id: "policy:checkout-orchestration-20",
        category: "application",
        statement: "Checkout orchestration should depend on ports rather than infrastructure types. Rule tier 20 documents the production review variant for dependency-inversion.",
        severity: "high",
        required_signal: "dependency-inversion",
    },
    PolicyRuleSpec {
        id: "policy:catalog-price-source-20",
        category: "catalog",
        statement: "Order pricing must read the catalog port and never trust caller supplied totals. Rule tier 20 documents the production review variant for catalog-price-authority.",
        severity: "high",
        required_signal: "catalog-price-authority",
    },
    PolicyRuleSpec {
        id: "policy:outbox-release-20",
        category: "events",
        statement: "Fulfillment release must publish an outbox event after all side effects succeed. Rule tier 20 documents the production review variant for event-outbox.",
        severity: "medium",
        required_signal: "event-outbox",
    },
    PolicyRuleSpec {
        id: "policy:warehouse-split-20",
        category: "inventory",
        statement: "Split fulfillment must keep warehouse choice visible in reservation lines. Rule tier 20 documents the production review variant for warehouse-locality.",
        severity: "medium",
        required_signal: "warehouse-locality",
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{
        Address, CatalogItem, Currency, CustomerId, Money, Order, OrderId, OrderLine, Quantity,
        ServiceLevel, Sku,
    };

    fn order() -> Order {
        let item = CatalogItem::new(
            Sku::new("KIT-1").unwrap(),
            "starter kit",
            Money::new(2_500, Currency::Usd).unwrap(),
            1200,
            true,
        )
        .unwrap();
        Order::new(
            OrderId::new("order-1").unwrap(),
            CustomerId::new("customer-1").unwrap(),
            vec![OrderLine::from_catalog(&item, Quantity::new(1).unwrap())],
            ServiceLevel::Expedited,
            Address::new("1 Market", "San Francisco", "CA", "94105", "US").unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn policy_engine_reports_missing_review_signals() {
        let order = order();
        let risk = RiskAssessment::accept(10);
        let context = PolicyContext::new(&order, &risk);
        let engine = PolicyEngine::standard();
        let evaluations = engine.evaluate(&context);

        assert!(evaluations.len() >= 100);
        assert!(evaluations.iter().any(|evaluation| {
            evaluation
                .rule_id
                .starts_with("policy:customer-risk-review")
        }));
    }
}
