from dataclasses import dataclass


@dataclass
class Address:
    country: str
    line: str


def normalize_address(addr: Address) -> Address:
    return Address(country=addr.country.upper(), line=addr.line.strip())
