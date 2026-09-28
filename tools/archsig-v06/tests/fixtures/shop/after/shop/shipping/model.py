from dataclasses import dataclass

from shop.shipping.address import Address


@dataclass
class OrderShipping:
    order_id: str
    address: Address
