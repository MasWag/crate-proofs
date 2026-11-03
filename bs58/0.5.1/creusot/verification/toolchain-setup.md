# Toolchain setup and reuse

This trial uses unmodified Creusot 0.13.0 at commit
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1` with its own 0.13 standard library
and prelude. Do not substitute the user's separately installed 0.15 development
compiler. The user's existing local opam switch supplies Why3 and why3find
read-only; its package revisions and executable hashes belong in tool identity
evidence. No opam switch update or installation is required to reuse it.

## Reuse the prepared installation

The local ignored `.work/tools` is a link to the isolated tool installation used
for this trial. It contains `env.sh`, `sources/creusot`, isolated Cargo/Rustup
homes, Creusot data/configuration, and the prover binaries. The proof crate's
relative dependency resolves to that exact checkout's `creusot-std`.

From the Creusot workspace:

```bash
source scripts/env.sh
CARGO_NET_OFFLINE=true cargo creusot version
why3 --version
why3find --version
why3 config list-provers -C "$WHY3CONFIG"
```

The four configured provers are Alt-Ergo 2.6.2, Z3 4.15.3, CVC4 1.8 and
CVC5 1.3.1. `WHY3CONFIG` selects Creusot's supplied prover configuration, while
`DUNE_DIR_LOCATIONS` selects its 0.13 prelude. Keep both explicit for direct
Why3find runs. `cargo creusot` selects its own configuration internally.

## Restore on another checkout

Install into that workspace's `.work/tools`, or link an already prepared matching
installation there. Preserve its unmodified source revision and record executable
hashes. Prerequisites are Rustup/Cargo, Git, a native linker, and an existing
Why3/why3find installation supporting the generated Coma. First inspect
`opam switch list` for local switches outside `~/.opam`; executables need not
already be on PATH. Read installed switch metadata directly if an opam query
would try to write logs to a read-only user home.

Use isolated `CARGO_HOME`, `RUSTUP_HOME`, `XDG_DATA_HOME`, `XDG_CONFIG_HOME`,
`XDG_CACHE_HOME`, `CARGO_TARGET_DIR` and a sufficiently large `TMPDIR` under the
installation root. Leave the caller's home configuration unchanged. Fetch the
official Creusot repository and check out the full commit above. Install
nightly-2026-06-22 with `rustc-dev`, `llvm-tools`, `rustfmt` and `rust-src`.
The upstream build commands, executed against the pinned source, are:

```bash
cargo +nightly-2026-06-22 install --locked --path cargo-creusot
cargo +nightly-2026-06-22 install --locked --path creusot-rustc \
  --root "$XDG_DATA_HOME/creusot/toolchains/nightly-2026-06-22"
cargo +nightly-2026-06-22 run --locked --bin creusot-install -- prelude provers
```

Use the upstream installer/configuration procedure for prover discovery. Reuse
the existing Why3/why3find binaries through private links; do not modify their
user switch. If direct Why3find reports missing provers, inspect the selected
configuration and use the standard `why3 config detect -C PRIVATE_CONFIG` command
on a private configuration. Do not rewrite a user configuration or driver.

Confirm the source tree remains clean and save the exact versions and hashes.
Run a fresh standard example with `cargo creusot --no-cache` and require a positive
closed goal before accepting the tool environment. A successful smoke proof is
evidence that the tools run together; the bs58 contracts require their own fresh
complete run. The prepared installation passed the upstream generated `add_one`
example using the existing user switch. Setup is not a proof of bs58.
