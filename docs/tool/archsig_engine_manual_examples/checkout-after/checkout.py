"""注文確認画面と見積画面の金額計算。金額の単位は円。"""


def with_packaging(subtotal_yen: int) -> int:
    return subtotal_yen + 100


def with_delivery(packed_yen: int) -> int:
    return packed_yen + 200


def checkout_total(subtotal_yen: int) -> int:
    return with_delivery(with_packaging(subtotal_yen))


def quote_total(subtotal_yen: int) -> int:
    return subtotal_yen + 300


def order_totals(subtotal_yen: int) -> dict[str, int]:
    return {
        "checkout": checkout_total(subtotal_yen),
        "quote": quote_total(subtotal_yen),
    }
