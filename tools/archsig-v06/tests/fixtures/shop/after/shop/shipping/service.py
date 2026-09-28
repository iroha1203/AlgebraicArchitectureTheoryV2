from shop.payment.service import reset_authorization
from shop.shipping.address import Address, normalize_address
from shop.shipping.model import OrderShipping


def update_shipping(shipping: OrderShipping, new: Address) -> None:
    if new.country != shipping.address.country:
        reset_authorization(shipping.order_id)   # 国をまたぐと与信をやり直す
    shipping.address = normalize_address(new)
