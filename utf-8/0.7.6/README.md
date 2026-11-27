# utf-8 0.7.6 verification

The default profile investigates the unchanged crates.io `utf-8` 0.7.6
release with Aeneas and Lean. Seven public storage, constructor and clone operations
and one private helper are covered; UTF-8 decoding and streaming are not verified.
See the [results and coverage ledger](aeneas/profiles/default/results.md).

The separate [adapted-core profile](aeneas/profiles/core_adapted/results.md)
checks conditional private helper transitions in modified source; it does not
prove a public decoder API. Its [correspondence record](aeneas/profiles/core_adapted/correspondence.md)
describes the source adaptation and the unproved relationship to the release.

Two native observations are recorded as specification questions:
[manually constructed incomplete states](verification/findings/UTF8-001.md)
and [retry after a buffer-fill error](verification/findings/UTF8-002.md).
Neither has been reported upstream.

From the repository root on the tested macOS host, use Python 3.11 or later
and prepared tool caches:

```sh
export PATH=/opt/homebrew/bin:$PATH
bash utf-8/0.7.6/scripts/setup.sh --offline
bash utf-8/0.7.6/scripts/verify.sh --offline
bash utf-8/0.7.6/scripts/verify.sh --profile core_adapted --offline
python3 utf-8/0.7.6/scripts/probe-boundaries.py
```

The accepted setup used an already prepared local Lake package cache, supplied
from the repository root as
`AENEAS_LAKE_CACHE="$PWD/utf-8/0.7.6/.work/proof-dev/.lake/packages"`.
The prepared cache now exists; a fresh clone without caches is not established
to work offline.
