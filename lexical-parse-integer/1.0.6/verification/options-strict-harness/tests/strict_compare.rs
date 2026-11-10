use lexical_parse_integer_options_strict_adapted as adapted;

#[test]
fn both_builder_states_match_release() {
    for flag in [false, true] {
        let adapted = adapted::Options::builder().no_multi_digit(flag).build_strict();
        let release = release::Options::builder().no_multi_digit(flag).build_strict();
        assert_eq!(adapted.get_no_multi_digit(), release.get_no_multi_digit());
        assert_eq!(adapted.get_no_multi_digit(), flag);
    }
}

#[test]
fn predefined_constants_match_release() {
    assert_eq!(adapted::options::SMALL_NUMBERS.get_no_multi_digit(),
               release::options::SMALL_NUMBERS.get_no_multi_digit());
    assert_eq!(adapted::options::LARGE_NUMBERS.get_no_multi_digit(),
               release::options::LARGE_NUMBERS.get_no_multi_digit());
    assert!(adapted::options::SMALL_NUMBERS.get_no_multi_digit());
    assert!(!adapted::options::LARGE_NUMBERS.get_no_multi_digit());
}
