use toml_write::{TomlStringBuilder, ToTomlValue};

fn main() {
    let expect_panics = std::env::args().any(|arg| arg == "--expect-overflow");
    for quote in ['\'', '"'] {
        for len in [0, 1, 254, 255, 256, 257, 512] {
            let input = quote.to_string().repeat(len);
            let constructor = std::panic::catch_unwind(|| {
                let _ = TomlStringBuilder::new(&input);
            });
            let serialization = std::panic::catch_unwind(|| input.to_toml_value());
            let expected_panic = expect_panics && len >= 256;
            println!("quote={quote:?} len={len} constructor_panics={} serialization_panics={}",
                constructor.is_err(), serialization.is_err());
            assert_eq!(constructor.is_err(), expected_panic);
            assert_eq!(serialization.is_err(), expected_panic);
        }
        let input = format!("{}x{}", quote.to_string().repeat(255), quote.to_string().repeat(255));
        let _ = TomlStringBuilder::new(&input);
        let _ = input.to_toml_value();
        println!("quote={quote:?} separated 255-quote runs succeed");
    }
}
