from shop.order.model import Order
from shop.payment import gateway


def charge(order: Order, amount: int) -> None:
    gateway.charge(order.payment_ref, amount)
