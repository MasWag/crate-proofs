extern crate option_ext;
use option_ext::OptionExt;

struct Stored(u32);
struct Query(u32);
impl PartialEq<Stored> for Query {
    fn eq(&self, other: &Stored) -> bool { self.0 + 1 == other.0 }
}

#[test]
fn contains_uses_cross_type_query_direction() {
    assert!(OptionExt::contains(&Some(Stored(8)), &Query(7)));
    assert!(!OptionExt::contains(&Some(Stored(7)), &Query(7)));
    assert!(!OptionExt::contains(&None::<Stored>, &Query(7)));
}

#[test]
fn map_or_consumes_only_selected_callback() {
    let owned = String::from("value");
    assert_eq!(Some(5).map_or2(move |x| (x, owned), (0, String::new())),
               (5, String::from("value")));
    assert_eq!(None::<u32>.map_or2(|_| panic!("unselected"), 17), 17);
}

#[test]
fn map_or_else_selects_one_owned_callback() {
    let owned = String::from("some");
    assert_eq!(Some(5).map_or_else2(move |_| owned, || panic!("unselected")), "some");
    let owned = String::from("none");
    assert_eq!(None::<u32>.map_or_else2(|_| panic!("unselected"), move || owned), "none");
}
