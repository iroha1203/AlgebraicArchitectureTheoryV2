from shop.payment import gateway
from shop.payment.model import OrderPayment


def charge(payment: OrderPayment, amount: int) -> None:
    gateway.charge(payment.ref, amount)
