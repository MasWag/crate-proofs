// This native check compares the two Rust source bodies over all raw metric states.
#![allow(dead_code)]

trait TomlWrite: core::fmt::Write {
    fn newline(&mut self) -> core::fmt::Result;
}

trait WriteTomlValue {
    fn write_toml_value<W: TomlWrite + ?Sized>(&self, writer: &mut W) -> core::fmt::Result;
}

trait WriteTomlKey {
    fn write_toml_key<W: TomlWrite + ?Sized>(&self, writer: &mut W) -> core::fmt::Result;
}

fn flag(bits: u8, index: u32) -> bool {
    bits & (1 << index) != 0
}

macro_rules! source {
    ($module:ident, $path:expr) => {
        mod $module {
            include!($path);

            pub fn key(decoded: &str, bits: u8) -> (&str, Option<u8>) {
                let selected = TomlKeyBuilder {
                    decoded,
                    metrics: KeyMetrics {
                        unquoted: super::flag(bits, 0),
                        single_quotes: super::flag(bits, 1),
                        double_quotes: super::flag(bits, 2),
                        escape_codes: super::flag(bits, 3),
                        escape: super::flag(bits, 4),
                    },
                }
                .as_default();
                (selected.decoded, selected.encoding.map(|encoding| encoding as u8))
            }

            pub fn string(decoded: &str, single: u8, double: u8, bits: u8) -> (&str, u8, bool) {
                let selected = TomlStringBuilder {
                    decoded,
                    metrics: ValueMetrics {
                        max_seq_single_quotes: single,
                        max_seq_double_quotes: double,
                        escape_codes: super::flag(bits, 0),
                        escape: super::flag(bits, 1),
                        newline: super::flag(bits, 2),
                    },
                }
                .as_default();
                (selected.decoded, selected.encoding as u8, selected.newline)
            }
        }
    };
}

source!(release, env!("TOML_WRITE_RELEASE_STRING"));
source!(adapted, env!("TOML_WRITE_ADAPTED_STRING"));

fn main() {
    let decoded = "example ‘text’ with\nnewline";
    for bits in 0..32 {
        assert_eq!(release::key(decoded, bits), adapted::key(decoded, bits));
    }
    for single in u8::MIN..=u8::MAX {
        for double in u8::MIN..=u8::MAX {
            for bits in 0..8 {
                assert_eq!(
                    release::string(decoded, single, double, bits),
                    adapted::string(decoded, single, double, bits)
                );
            }
        }
    }
    println!("Matched release and adapted defaults in 32 key and 524288 string metric states.");
}
