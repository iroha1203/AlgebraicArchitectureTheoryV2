from shop.payment import repository


def reset_authorization(order_id: str) -> None:
    payment = repository.load(order_id)
    payment.ref = None
