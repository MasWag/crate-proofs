# Independent specification: option-ext 0.2.0

## Responsibility and source

This specification was designed independently by the Astra specification agent;
the Sol implementation agent is responsible for extraction and checked proofs.
The primary agent reviews the contracts, generated bodies, commands, evidence,
and coverage claims. This file states obligations, not proof completion.

The release public surface is `src/lib.rs`, with its implementation in
`src/impl.rs`, restored from the pinned crates.io archive. The fresh registry
query on 2026-11-03 identifies 0.2.0 as the latest release. The only public trait
is `OptionExt<T>`, and its sole release implementation is for `Option<T>`.
The three operations below constitute the complete release API and algorithm
ledger. There is no feature-specific alternate implementation.

## Mathematical observables

An optional value is either `none` or `some t`, for an arbitrary type `T`.
The mathematical specification quantifies over every such value. There are no
private representation invariants, integer bounds, collection lengths, or
constructor restrictions to assume.

Let `R : U -> T -> Prop` describe the intended heterogeneous comparison relation,
`F : T -> V` describe a mapping, and `D : V` describe a lazy default result.
The independent successful-result functions are:

```
member R none     x = false
member R (some t) x = the Boolean reflecting R x t

mapDefault F d none     = d
mapDefault F d (some t) = F t

mapLazyDefault F D none     = D
mapLazyDefault F D (some t) = F t
```

These equations express membership and option elimination; their meaning does
not depend on generated code. A proof may state Boolean reflection as
`b = true <-> R x t`, avoiding any need for a global decidability assumption.

The translated Rust computation has an outer Aeneas `Result`. Write `ok v` for
successful execution. This outer result is distinct from any Rust `Result`
chosen as the generic output type `V`: returning `Err e` as a value is still
successful execution, represented by `ok (Err e)`.

## API contracts and coverage ledger

| Public operation | Core obligation | Necessary selected-callback premise |
| --- | --- | --- |
| `contains(&self, x: &U)` | Boolean membership using `U: PartialEq<T>` in the direction `x == contained` | On `some t`, the actual `U::eq(x,t)` succeeds and reflects `R x t`; none on `none` |
| `map_or2(self, f, default)` | Map the contained value or return the supplied value | On `some t`, the actual `f(t)` succeeds with the specified output; none on `none` |
| `map_or_else2(self, f, default)` | Invoke and return exactly the selected branch's callback result | On `some t`, only `f(t)` must succeed; on `none`, only `default()` must succeed |

### `contains`

For every `x`, `contains none x = ok false`, without any assumption on the
comparison implementation. For `some t`, assume only
`actualEq x t = ok b` and `(b = true <-> R x t)`. Then prove

```
exists out, contains (some t) x = ok out
         and (out = true <-> R x t).
```

Also prove the exact branch equations `contains none x = ok false` and
`contains (some t) x = actualEq x t`, with the actual generated trait dictionary.
They capture failure propagation and independence from an unused comparator.

No symmetry, reflexivity, transitivity, or equality with Lean's propositional
equality is required for this dispatch contract. In particular, Rust permits
heterogeneous comparison in this direction, and floating-point NaN is not
reflexively equal. A stronger mathematical-equality corollary requires a
separate comparator-refinement hypothesis; it must not be silently substituted
for the generic API contract. These hypotheses describe the callback only, not
the correctness of `contains` itself.

### `map_or2`

For every supplied `d` and callback `f`, prove the unconditional none case:

```
exists out, map_or2 none f d = ok out and out = d.
```

For `some t`, assume only `actualCall f t = ok (F t)` and prove

```
exists out, map_or2 (some t) f d = ok out and out = F t.
```

A relational postcondition is also valid: if `actualCall f t = ok u` and
`P t u`, the returned value satisfies `P t`. Global callback totality is
unnecessary. The exact branch equations must relate the generated body to
`ok d` on none and `actualCall f t` on some, including callback failures.

The default is already a value at method entry. Rust evaluates the expression
used to construct that argument before the method is called, even for some.
This eager caller-side evaluation is a language-level observation, not a claim
that the method invokes a default callback. Likewise, constructing the mapping
closure is distinct from invoking its body.

### `map_or_else2`

For none, assume only `actualCall default () = ok D` and prove

```
exists out, map_or_else2 none f default = ok out and out = D.
```

For `some t`, assume only `actualCall f t = ok (F t)` and prove

```
exists out, map_or_else2 (some t) f default = ok out and out = F t.
```

The exact branch equations are equality to the actual default callback
computation on none and equality to the actual mapping callback computation on
some. The unselected callback needs no success, termination, or refinement
hypothesis. Conditional theorems must be branchwise rather than require both
callbacks to succeed. This preserves the advertised lazy selection even when
an unused callback would panic.

## Callback selection, borrowing, and effects

At the source level, `contains` selects zero comparisons on none and one on
some; `map_or2` selects zero mapping invocations on none and one on some;
`map_or_else2` selects exactly one of its two closures. Exact branch equations
establish the selected translated computation and independence from an unused
callback. A pure result equation by itself is not an execution-trace or
arbitrary-side-effect call-count theorem. Claims about effects or exact runtime
call counts require an explicitly supported state/trace model or separate native
observations, which must be labeled accordingly.

`contains` borrows its receiver and candidate through shared references. The
other methods consume their receiver and accept `FnOnce` callbacks. There is no
mutable-receiver API and no crate-defined mutation algorithm. Inputs and outputs
may themselves contain references, including mutable references; that fact does
not grant this profile a separate aliasing, interior-mutability, or borrow-back
theorem. A shared reference does not rule out effects through interior mutability
inside user comparison code.

Closure captures and unused generic values may have user-defined destruction
behavior. The success contracts concern the supported Aeneas translation and
its documented destruction/effect model; do not infer that arbitrary panicking
destructors or unmodeled external effects are proven safe. The crate defines no
new error type or unconditional panic path. Failure of a selected callback is
not a crate bug, and its success cannot be proved without a premise.

## Proof and trust requirements

1. Extract and prove the actual three release bodies, retaining their generic
   types, comparison dictionary, and closure dictionaries. Concrete integer
   examples or replacement wrapper algorithms do not establish this coverage.
2. For the delegated standard-library `Option::map_or` and `Option::map_or_else`
   bodies, record whether extraction includes the bodies or uses Aeneas library
   models. Identify that trust boundary explicitly; a model-only theorem is not
   verification of arbitrary upstream standard-library code.
3. Do not strengthen selected-callback premises to assume the desired outer
   method result. Prove total success with an existential output and its
   independent property, together with branch equations for failure propagation.
4. Audit theorem dependencies. No admitted theorem, custom axiom, native-decision
   axiom, or hand-edited generated implementation may discharge these obligations.
5. Preserve release correspondence and report any adaptation. Report native
   tests separately from formal proofs. This ledger includes all three core
   operations even if extraction or proof leaves one blocked.

## Independent defect hypotheses

Check reversed heterogeneous comparison arguments, accidental comparison on
none, wrong default selection, evaluating the unused closure, lost mapping
input, or substituted callback output. A failing or non-lawful user comparator,
a selected closure that panics, caller-side eager default construction, and
destructor behavior outside the translation are not by themselves defects in
these three operations. Inspection of the release implementation reveals no
violation of the specified branch behavior; final proof evidence must determine
which obligations have actually been discharged.
