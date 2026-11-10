# Native behavior probe

`probe.rs` exercises the checksum-pinned lexical-parse-integer 1.0.6 release through its public API. The source archive SHA-256 is `9a7a039f8fb9c19c996cd7b2fcce303c1b2874fe1aca544edc85c4a5f8489b34`; `src/algorithm.rs` SHA-256 is `c98d417dc2e8969d82150a8b80dcd285b9ea692a647c049fa7ae13edc477c7cf`. The probe file SHA-256 is `5a6a66c1654021f05ed935c30074e6317089ad21362dcda747f4f0d9cb1a014a`.

Run from `/private/tmp` on Darwin arm64 with Rust 1.94.1. The isolated `CARGO_HOME` and this working directory avoid the inherited Cargo patch in `~/.cargo/config.toml`.

```sh
CARGO_HOME=/Users/mwaga/crate-proofs/lexical-parse-integer/1.0.6/.work/cargo-home rustup run 1.94.1 cargo test --locked --offline --manifest-path /Users/mwaga/crate-proofs/lexical-parse-integer/1.0.6/Cargo.toml --test behavior_probe --features format,power-of-two -- --nocapture
CARGO_HOME=/Users/mwaga/crate-proofs/lexical-parse-integer/1.0.6/.work/cargo-home rustup run 1.94.1 cargo test --locked --offline --manifest-path /Users/mwaga/crate-proofs/lexical-parse-integer/1.0.6/Cargo.toml --test behavior_probe --features format,power-of-two -- --ignored --nocapture
```

The first command exits 0: five controls pass, four regression reproductions are ignored. The second exits 101: all four expected-correct assertions fail, in two behavior groups.

| API and input | Expected | Actual |
| --- | --- | --- |
| `u8::from_lexical_partial_with_options`, no leading zeros, `b"0"` | `Ok((0, 1))` | `Ok((0, 0))` |
| `i8::from_lexical_partial_with_options`, no leading zeros, `b"-0"` | `Ok((0, 2))` | `Ok((0, 1))` |
| `u8::from_lexical_partial_with_options`, suffix `h`, `b"12?x"` | `Ok((12, 2))` | `Ok((12, 3))` |
| `u8::from_lexical_with_options`, suffix `h`, `b"12?x"` | `Err(InvalidDigit(2))` | `Err(InvalidDigit(3))` |

The default feature run exits 0 with three passing tests. `format,power-of-two,compact` gives five passing controls and the same four failed regression assertions. The controls compare all decimal strings for unsigned values 0–300 and signed values −140–140, plus i128/u128 boundaries, against Rust integer parsing with both `no_multi_digit` settings. They also cover suffix and leading-zero nearby inputs. These executions are native tests, not formal proofs.

The zero-length-prefix observation `b"?" -> Ok((0, 0))` and `b"+?" -> Ok((0, 1))` occurs in both default and format profiles. It is recorded as a specification question, not a confirmed bug.

Raw logs are retained locally in ignored `.work/`: `default.log` SHA-256 `224fcdafa05d2ac538c7e56d631214357cf18c33d29590004ce1b8251fc4949a`, `format.log` `eeb12cce5239af126cfc44a24e935ae3e068c2894e4629eb9b65207fa1226fcd`, `format_repro.log` `1dd1d21b459762ea907dfcd471e9d4562bb55196c98b7e6b6d2d42df915aaac9`, `compact.log` `8484e1cb0c5951f819fa9bdc164abcc408264c9455c7c4d5018d60e1e1cf4238`, and `compact_repro.log` `22bbc46a99a8ac8cf35ef73684dc5a0537163b928dc011d63885e90cd9ee33d6`.
