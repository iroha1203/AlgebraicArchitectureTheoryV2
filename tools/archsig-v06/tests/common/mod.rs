//! マニュアル第2章の `shop` の題材と、コマンドを実行する補助。

#![allow(dead_code)]

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

pub struct Repo {
    pub dir: PathBuf,
}

impl Repo {
    pub fn new(name: &str) -> Repo {
        let dir = std::env::temp_dir().join(format!("archsig-plan-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join(".archsig/law")).unwrap();
        Repo { dir }
    }

    pub fn write(&self, path: &str, text: &str) {
        let p = self.dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    pub fn map(&self, source: &str, text: &str) {
        self.write(&format!(".archsig/map/{source}.jsonl"), text);
    }

    pub fn run(&self, args: &[&str]) -> Value {
        let out = Command::new(env!("CARGO_BIN_EXE_archsig")).current_dir(&self.dir).args(args).output().unwrap();
        assert!(out.status.success(), "archsig {args:?}: {}", String::from_utf8_lossy(&out.stderr));
        serde_json::from_slice(&out.stdout).unwrap()
    }

    pub fn fail(&self, args: &[&str]) -> String {
        let out = Command::new(env!("CARGO_BIN_EXE_archsig")).current_dir(&self.dir).args(args).output().unwrap();
        assert!(!out.status.success(), "archsig {args:?} は失敗するはず");
        String::from_utf8_lossy(&out.stderr).to_string()
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

pub const LAW: &str = r#"sources "shop/**"
  except "**/tests/**"

reading module = dir(depth: 2)

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations
"#;

pub const SERVICE: &str = r#"{"kind": "observed", "subject": "shop/shipping/service.py", "scope": "structure", "at": "shop/shipping/service.py@blob:3f2a9c1"}
{"kind": "observed", "subject": "shop/shipping/service.py", "scope": "meaning:payment-info", "at": "shop/shipping/service.py@blob:3f2a9c1"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"order": "shop.order.model.Order", "new": "shop.shipping.model.Address"}, "at": "shop/shipping/service.py:2@blob:3f2a9c1"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.order.model.Order.payment_ref", "value": "None", "when": "$new.country != $order.shipping_address.country", "at": "shop/shipping/service.py:4@blob:3f2a9c1"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.normalize_address", "object": "shop.shipping.address.normalize_address.$addr", "value": "$new", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.order.model.Order.shipping_address", "value": "shop.shipping.address.normalize_address($new)", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:3f2a9c1"}
{"kind": "defines", "subject": "shop.shipping.service.fix_address", "value": "operation", "params": {"order": "shop.order.model.Order"}, "at": "shop/shipping/service.py:8@blob:3f2a9c1"}
{"kind": "calls", "subject": "shop.shipping.service.fix_address", "object": "shop.shipping.address.normalize_address", "at": "shop/shipping/service.py:9@blob:3f2a9c1"}
"#;

pub const ORDER: &str = r#"{"kind": "observed", "subject": "shop/order/model.py", "scope": "structure", "at": "shop/order/model.py@blob:1d9e3b4"}
{"kind": "observed", "subject": "shop/order/model.py", "scope": "meaning:payment-info", "at": "shop/order/model.py@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order", "value": "type", "at": "shop/order/model.py:7@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.order_id", "value": "field", "type": "str", "at": "shop/order/model.py:8@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.shipping_address", "value": "field", "type": "shop.shipping.model.Address", "at": "shop/order/model.py:9@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.payment_ref", "value": "field", "type": "str", "at": "shop/order/model.py:10@blob:1d9e3b4"}
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/order/model.py:10@blob:1d9e3b4"}
"#;

pub const ADDRESS_MODEL: &str = r#"{"kind": "observed", "subject": "shop/shipping/model.py", "scope": "structure", "at": "shop/shipping/model.py@blob:6a1b2c3"}
{"kind": "observed", "subject": "shop/shipping/model.py", "scope": "meaning:payment-info", "at": "shop/shipping/model.py@blob:6a1b2c3"}
{"kind": "defines", "subject": "shop.shipping.model.Address", "value": "type", "at": "shop/shipping/model.py:3@blob:6a1b2c3"}
{"kind": "defines", "subject": "shop.shipping.model.Address.country", "value": "field", "type": "str", "at": "shop/shipping/model.py:4@blob:6a1b2c3"}
"#;

pub const ADDRESS: &str = r#"{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure", "at": "shop/shipping/address.py@blob:9f2c4e7"}
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "meaning:payment-info", "at": "shop/shipping/address.py@blob:9f2c4e7"}
{"kind": "defines", "subject": "shop.shipping.address.normalize_address", "value": "operation", "params": {"addr": "shop.shipping.model.Address"}, "at": "shop/shipping/address.py:5@blob:9f2c4e7"}
{"kind": "returns", "subject": "shop.shipping.address.normalize_address", "value": "$addr", "at": "shop/shipping/address.py:6@blob:9f2c4e7"}
"#;

/// マニュアル第2章の候補(一つ目)。
pub const SPLIT: &str = r#"{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping", "value": "type", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment", "value": "type", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.address", "value": "field", "type": "shop.shipping.model.Address", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.order_id", "value": "field", "type": "str", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment.ref", "value": "field", "type": "str", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.shipping_address", "object": "shop.shipping.model.OrderShipping.address", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref", "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.shipping.service.update_shipping.$order", "object": "shop.shipping.service.update_shipping.$shipping", "at": "plan:split-order"}
{"kind": "removes", "subject": "shop.order.model.Order", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"shipping": "shop.shipping.model.OrderShipping", "new": "shop.shipping.model.Address"}, "file": "shop/shipping/service.py", "at": "plan:split-order"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.normalize_address", "object": "shop.shipping.address.normalize_address.$addr", "value": "$new", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.model.OrderShipping.address", "value": "shop.shipping.address.normalize_address($new)", "at": "plan:split-order"}
"#;

/// 第2章 5. の直した候補。国が変わるとき決済側の reset_authorization を呼ぶ。
pub const RESET: &str = r#"{"kind": "defines", "subject": "shop.payment.service.reset_authorization", "value": "operation", "params": {"order_id": "str"}, "file": "shop/payment/service.py", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.payment.service.reset_authorization", "object": "shop.payment.model.OrderPayment.ref", "value": "None", "at": "plan:split-order"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.payment.service.reset_authorization", "when": "$new.country != $shipping.address.country", "at": "plan:split-order"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.payment.service.reset_authorization", "object": "shop.payment.service.reset_authorization.$order_id", "value": "$shipping.order_id", "at": "plan:split-order"}
"#;

pub fn shop(name: &str) -> Repo {
    let repo = Repo::new(name);
    repo.write(".archsig/law/shop.law", LAW);
    repo.map("shop/shipping/service.py", SERVICE);
    repo.map("shop/order/model.py", ORDER);
    repo.map("shop/shipping/model.py", ADDRESS_MODEL);
    repo
}

pub fn result<'a>(summary: &'a Value, subject: &str) -> &'a Value {
    summary["results"].as_array().unwrap().iter().find(|r| r["subject"] == subject).unwrap_or_else(|| panic!("{subject} がない: {summary}"))
}
