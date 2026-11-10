use lexical_parse_integer_options_harness::{Options, OptionsBuilder};

#[test]
fn builder_and_options_preserve_the_flag() {
    for flag in [false, true] {
        let builder = OptionsBuilder::new().no_multi_digit(flag);
        assert_eq!(builder.get_no_multi_digit(), flag);
        assert!(builder.is_valid());
        let unchecked = builder.build_unchecked();
        let strict = builder.build_strict();
        let fallible = builder.build().unwrap();
        assert_eq!(unchecked, strict);
        assert_eq!(strict, fallible);
        assert_eq!(fallible.get_no_multi_digit(), flag);
        assert!(fallible.is_valid());
        assert_eq!(fallible.rebuild().get_no_multi_digit(), flag);
        let mut changed = fallible;
        #[allow(deprecated)]
        changed.set_no_multi_digit(!flag);
        assert_eq!(changed.get_no_multi_digit(), !flag);
    }
}

#[test]
fn default_and_radix_constructors_use_default_state() {
    assert!(Options::new().get_no_multi_digit());
    assert!(Options::default().get_no_multi_digit());
    assert!(OptionsBuilder::default().get_no_multi_digit());
    for radix in u8::MIN..=u8::MAX {
        assert!(Options::from_radix(radix).get_no_multi_digit());
    }
}
