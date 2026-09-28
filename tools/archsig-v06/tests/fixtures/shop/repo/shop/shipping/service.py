from shop.order.model import Order
from shop.shipping.address import Address, normalize_address


def update_shipping(order: Order, new: Address) -> None:
    if new.country != order.shipping_address.country:
        order.payment_ref = None          # 国をまたぐと与信をやり直す
    order.shipping_address = normalize_address(new)
