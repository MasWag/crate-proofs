use fxhash::{FxHashMap, FxHashSet};
fn main() {
    let mut map = FxHashMap::default();
    map.insert("black", 0);
    map.insert("white", 255);
    assert_eq!(map.get("black"), Some(&0));
    let mut set = FxHashSet::default();
    set.insert("black");
    set.insert("white");
    assert!(set.contains("white"));
}
