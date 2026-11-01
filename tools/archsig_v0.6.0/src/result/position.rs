//! 表示時にだけ、保持した元入力から Location の開始行・列を補う。
use crate::canonical::Json;

pub fn add_location_positions<'a>(
    document: &mut Json,
    sources: impl IntoIterator<Item = (&'a str, &'a [u8])>,
) {
    let sources: Vec<_> = sources
        .into_iter()
        .map(|(id, bytes)| {
            // UTF-8 エラーも、その直前までの有効な prefix の位置を持つ。
            let text = std::str::from_utf8(bytes).unwrap_or_else(|e| {
                std::str::from_utf8(&bytes[..e.valid_up_to()]).expect("valid UTF-8 prefix")
            });
            let mut lines = vec![0];
            lines.extend(
                text.bytes()
                    .enumerate()
                    .filter_map(|(i, b)| (b == b'\n').then_some(i + 1)),
            );
            (id, text, lines)
        })
        .collect();
    let mut pending = vec![document];
    while let Some(value) = pending.pop() {
        match value {
            Json::Obj(fields) => {
                // Location の閉じた形だけを扱う。source location やユーザー文字列は対象外。
                if fields
                    .keys()
                    .all(|k| matches!(k.as_str(), "input" | "pointer" | "span" | "line" | "column"))
                    && let (Some(Json::Str(id)), Some(Json::Arr(span))) =
                        (fields.get("input"), fields.get("span"))
                    && let [Json::Nat(start), Json::Nat(_)] = span.as_slice()
                    && let Ok(start) = usize::try_from(*start)
                    && let Some((_, text, lines)) =
                        sources.iter().find(|(source, _, _)| source == id)
                    && text.is_char_boundary(start)
                {
                    let line = lines.partition_point(|offset| *offset <= start);
                    let column = text[lines[line - 1]..start].chars().count() + 1;
                    fields.insert("line".into(), Json::Nat(line as u64));
                    fields.insert("column".into(), Json::Nat(column as u64));
                }
                pending.extend(fields.values_mut());
            }
            Json::Arr(values) => pending.extend(values),
            _ => {}
        }
    }
}
