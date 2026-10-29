use archsig::canonical::Json;

// 元のspanを保った期待値へ、公開結果で必須の1始まり位置を補う。
pub fn law_positions(mut expected: Json, law: &[u8]) -> Json {
    fn visit(value: &mut Json, law: &str) {
        match value {
            Json::Obj(fields) => {
                if fields.get("input") == Some(&Json::str("law")) {
                    if let Some(Json::Arr(span)) = fields.get("span") {
                        let Json::Nat(start) = span[0] else { panic!("span start") };
                        let prefix = &law[..start as usize];
                        let lines: Vec<_> = prefix.split('\n').collect();
                        let line = lines.len() as u64;
                        let column = lines.last().unwrap().chars().count() as u64 + 1;
                        fields.insert("line".into(), Json::Nat(line));
                        fields.insert("column".into(), Json::Nat(column));
                    }
                }
                for value in fields.values_mut() { visit(value, law); }
            }
            Json::Arr(values) => for value in values { visit(value, law); },
            _ => (),
        }
    }
    visit(&mut expected, std::str::from_utf8(law).unwrap());
    expected
}
