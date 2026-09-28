from dataclasses import dataclass


@dataclass
class OrderPayment:
    order_id: str
    ref: str | None
