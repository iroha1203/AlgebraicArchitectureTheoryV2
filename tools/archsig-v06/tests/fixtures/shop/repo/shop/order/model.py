from dataclasses import dataclass

from shop.shipping.address import Address


@dataclass
class Order:
    order_id: str
    shipping_address: Address
    payment_ref: str | None
