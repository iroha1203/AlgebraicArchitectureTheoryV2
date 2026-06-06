use std::error::Error;

use archsig_practical_rust_service_sample::app::OrderService;
use archsig_practical_rust_service_sample::domain::{Order, OrderId, OrderLine, ProductId};
use archsig_practical_rust_service_sample::store::InMemoryInventoryStore;

fn main() -> Result<(), Box<dyn Error>> {
    let sku_rust_book = ProductId::new("sku-rust-book")?;
    let sku_archsig_notes = ProductId::new("sku-archsig-notes")?;

    let mut store = InMemoryInventoryStore::new();
    store.add_stock(sku_rust_book.clone(), 4);
    store.add_stock(sku_archsig_notes.clone(), 2);

    let order = Order::new(
        OrderId::new("order-demo-1")?,
        vec![
            OrderLine::new(sku_rust_book, 1)?,
            OrderLine::new(sku_archsig_notes, 2)?,
        ],
    )?;

    let mut service = OrderService::new(store);
    let receipt = service.place_order(order)?;
    let store = service.into_store();

    println!(
        "reserved order={} lines={} units={} reservations={}",
        receipt.order_id,
        receipt.reserved_line_count,
        receipt.reserved_unit_count,
        store.reservation_count()
    );
    println!("remaining stock={:?}", store.stock_snapshot());

    Ok(())
}
