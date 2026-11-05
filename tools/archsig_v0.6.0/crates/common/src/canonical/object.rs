//! canonical key順を持つ小さいJSON object。可変参照は値だけに限る。
use super::Json;
use std::{borrow::Borrow, collections::BTreeMap, ops::Index};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct JsonObject {
    entries: Vec<(String, Json)>,
}
impl std::fmt::Debug for JsonObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl JsonObject {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    fn find<Q: Ord + ?Sized>(&self, key: &Q) -> Result<usize, usize>
    where
        String: Borrow<Q>,
    {
        self.entries
            .binary_search_by(|(name, _)| name.borrow().cmp(key))
    }
    pub fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&Json>
    where
        String: Borrow<Q>,
    {
        self.find(key).ok().map(|i| &self.entries[i].1)
    }
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<&mut Json>
    where
        String: Borrow<Q>,
    {
        self.find(key).ok().map(|i| &mut self.entries[i].1)
    }
    pub fn contains_key<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        String: Borrow<Q>,
    {
        self.find(key).is_ok()
    }
    pub fn insert(&mut self, key: String, value: Json) -> Option<Json> {
        match self.find(&key) {
            Ok(i) => Some(std::mem::replace(&mut self.entries[i].1, value)),
            Err(i) => {
                if self.entries.is_empty() {
                    self.entries = vec![(key, value)];
                } else {
                    self.entries.insert(i, (key, value));
                }
                None
            }
        }
    }
    pub fn remove<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<Json>
    where
        String: Borrow<Q>,
    {
        self.find(key).ok().map(|i| self.entries.remove(i).1)
    }
    pub fn retain(&mut self, mut keep: impl FnMut(&String, &mut Json) -> bool) {
        self.entries.retain_mut(|(key, value)| keep(key, value));
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&String, &Json)> + ExactSizeIterator {
        self.entries.iter().map(|(key, value)| (key, value))
    }
    pub fn keys(
        &self,
    ) -> impl DoubleEndedIterator<Item = &String> + ExactSizeIterator + std::fmt::Debug {
        self.entries.iter().map(|(key, _)| key)
    }
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &Json> + ExactSizeIterator {
        self.entries.iter().map(|(_, value)| value)
    }
    pub fn values_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Json> + ExactSizeIterator {
        self.entries.iter_mut().map(|(_, value)| value)
    }
    pub fn into_values(self) -> impl DoubleEndedIterator<Item = Json> + ExactSizeIterator {
        self.entries.into_iter().map(|(_, value)| value)
    }
    fn sorted(mut entries: Vec<(String, Json)>) -> Self {
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        // stable sort後の最後の値を残す。keyは外へ可変借用しない。
        entries.dedup_by(|later, earlier| {
            if later.0 == earlier.0 {
                std::mem::swap(later, earlier);
                true
            } else {
                false
            }
        });
        Self { entries }
    }
}
impl FromIterator<(String, Json)> for JsonObject {
    fn from_iter<T: IntoIterator<Item = (String, Json)>>(iter: T) -> Self {
        Self::sorted(iter.into_iter().collect())
    }
}
impl<const N: usize> From<[(String, Json); N]> for JsonObject {
    fn from(entries: [(String, Json); N]) -> Self {
        Self::sorted(Vec::from(entries))
    }
}
impl From<BTreeMap<String, Json>> for JsonObject {
    fn from(entries: BTreeMap<String, Json>) -> Self {
        Self {
            entries: entries.into_iter().collect(),
        }
    }
}
impl Extend<(String, Json)> for JsonObject {
    fn extend<T: IntoIterator<Item = (String, Json)>>(&mut self, iter: T) {
        let mut entries = std::mem::take(&mut self.entries);
        entries.extend(iter);
        *self = Self::sorted(entries);
    }
}
impl<Q: Ord + ?Sized> Index<&Q> for JsonObject
where
    String: Borrow<Q>,
{
    type Output = Json;
    fn index(&self, key: &Q) -> &Json {
        self.get(key).expect("no entry found for key")
    }
}
impl IntoIterator for JsonObject {
    type Item = (String, Json);
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}
fn pair_ref(pair: &(String, Json)) -> (&String, &Json) {
    (&pair.0, &pair.1)
}
fn pair_mut(pair: &mut (String, Json)) -> (&String, &mut Json) {
    (&pair.0, &mut pair.1)
}
impl<'a> IntoIterator for &'a JsonObject {
    type Item = (&'a String, &'a Json);
    type IntoIter =
        std::iter::Map<std::slice::Iter<'a, (String, Json)>, fn(&'a (String, Json)) -> Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter().map(pair_ref)
    }
}
impl<'a> IntoIterator for &'a mut JsonObject {
    type Item = (&'a String, &'a mut Json);
    type IntoIter = std::iter::Map<
        std::slice::IterMut<'a, (String, Json)>,
        fn(&'a mut (String, Json)) -> Self::Item,
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter_mut().map(pair_mut)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn layout_and_singleton_allocation_do_not_add_a_larger_json_header() {
        assert_eq!(
            std::mem::size_of::<JsonObject>(),
            std::mem::size_of::<Vec<(String, Json)>>()
        );
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(std::mem::size_of::<JsonObject>(), 24);
            assert_eq!(std::mem::size_of::<Json>(), 32);
            println!(
                "JsonObject={} Json={} String={} pair={}",
                std::mem::size_of::<JsonObject>(),
                std::mem::size_of::<Json>(),
                std::mem::size_of::<String>(),
                std::mem::size_of::<(String, Json)>()
            );
        }
        let Json::Obj(ref object) = Json::obj([("node", Json::str("n1"))]) else {
            panic!()
        };
        assert_eq!(object.entries.capacity(), 1);
        let mut inserted = JsonObject::new();
        assert!(inserted.is_empty());
        inserted.insert("node".into(), Json::str("n1"));
        assert_eq!(inserted.entries.capacity(), 1);
    }
    #[test]
    fn canonical_order_escape_and_duplicate_last_wins_match_the_map() {
        let pairs = vec![
            ("é".into(), Json::str("line\n\"")),
            ("a".into(), Json::Nat(1)),
            ("z".into(), Json::Bool(true)),
            ("a".into(), Json::Nat(2)),
            ("a".into(), Json::Nat(3)),
        ];
        let expected: BTreeMap<String, Json> = pairs.clone().into_iter().collect();
        let object: JsonObject = pairs.into_iter().collect();
        assert_eq!(
            object.iter().collect::<Vec<_>>(),
            expected.iter().collect::<Vec<_>>()
        );
        assert_eq!(
            Json::Obj(object).canonical(),
            "{\"a\":3,\"z\":true,\"é\":\"line\\u000a\\\"\"}"
        );
        assert_eq!(Json::obj([]).canonical(), "{}");
    }
    #[test]
    fn updates_removals_retention_and_iteration_change_values_only() {
        let mut object = JsonObject::from([("b".into(), Json::Nat(2)), ("a".into(), Json::Nat(1))]);
        assert_eq!(object.insert("b".into(), Json::Nat(3)), Some(Json::Nat(2)));
        *object.get_mut("a").unwrap() = Json::Nat(4);
        *object.get_mut("b").unwrap() = Json::Nat(5);
        for (_key, value) in &mut object {
            *value = Json::Bool(true);
        }
        object.extend([("c".into(), Json::Nat(6)), ("b".into(), Json::Nat(7))]);
        object.retain(|key, value| {
            if key == "b" {
                *value = Json::Nat(8);
            }
            key != "a"
        });
        assert_eq!(
            object.keys().map(String::as_str).collect::<Vec<_>>(),
            ["b", "c"]
        );
        assert_eq!(object.remove("b"), Some(Json::Nat(8)));
        assert_eq!(object.remove("absent"), None);
        assert!(object.contains_key("c"));
        for value in object.values_mut() {
            *value = Json::Nat(9);
        }
        assert_eq!(
            object.clone().into_values().collect::<Vec<_>>(),
            [Json::Nat(9)]
        );
        assert_eq!(object.values().collect::<Vec<_>>(), [&Json::Nat(9)]);
        assert_eq!(
            object.into_iter().collect::<Vec<_>>(),
            [("c".into(), Json::Nat(9))]
        );
    }
    #[test]
    fn large_bulk_build_sorts_once_and_preserves_the_last_duplicate() {
        let pairs = (0..20_000).rev().flat_map(|n| {
            [
                (format!("k{n:05}"), Json::Nat(n)),
                (format!("k{n:05}"), Json::Nat(n + 1)),
            ]
        });
        let object: JsonObject = pairs.collect();
        assert_eq!(object.len(), 20_000);
        assert_eq!(object["k00000"], Json::Nat(1));
        assert_eq!(object["k19999"], Json::Nat(20_000));
        assert!(
            object
                .iter()
                .zip(object.iter().skip(1))
                .all(|((a, _), (b, _))| a < b)
        );
    }
    #[test]
    fn deeply_nested_objects_drop_without_recursive_container_drop() {
        let mut value = Json::Bool(true);
        for _ in 0..20_000 {
            value = Json::obj([("next", value)]);
        }
        drop(value);
    }
}
