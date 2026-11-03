# Independent Creusot specification for the original lazy option operation

## Purpose, source, and responsibilities

The target is the released `OptionExt::map_or_else2` implementation for
`Option<T>` in option-ext 0.2.0. Its executable body must remain exactly the
delegation `self.map_or_else(default, f)`. This Creusot effort does not reuse the
direct-match adaptation proved in the separate Aeneas profile, and must not
modify that profile or either verifier to obtain a proof.

The Astra agent owns this independent specification and the later mathematical
review. The Sol agent owns annotations, environment preparation, verification,
and reproducible evidence. The primary agent checks source correspondence,
commands, proof coverage, evidence, and publication claims.

The release source is the separately locked archive restored under
`../.work/source` relative to this specification directory. Annotation-only derived sources must have an explicit
correspondence check. Proof-only imports, logical observations, and contracts
are allowed when separately identified; no executable replacement of the
delegated method, strengthened runtime type bounds, or application-level trust
declarations are allowed. Native compilation and tests are separate evidence.

## Independent mathematical behavior

For arbitrary input and output types `T` and `U`, write `o : Option<T>`,
`f : FnOnce(T) -> U`, and `d : FnOnce() -> U`. Let `F : T -> U` and `D : U`
specify desired callback outputs. The mathematical operation is

```
lazyMap(F, D, None)    = D
lazyMap(F, D, Some(t)) = F(t).
```

All optional values are valid. No integer, size, equality-law, or representation
restriction is needed. On `Some(t)`, only the invocation of `f` on that exact
payload is selected; on `None`, only the invocation of `d` with no arguments is
selected. The unused callback has no invocation precondition, termination, or
output-refinement requirement. Constructing either closure before calling the
method is different from invoking it.

The desired total-success statement is that, if the selected callback succeeds
with its specified output, the option operation also succeeds with
`lazyMap(F,D,o)`, subject to the applicable destructor and execution model.
The Creusot obligations below separate what is actually checked from this
stronger goal. Default `requires`/`ensures` verification must not be reported as
a termination theorem.

## Creusot call and return contract

The selected-call precondition must have precisely this branching shape:

```rust
match o {
    None => d.precondition(()),
    Some(t) => f.precondition((t,)),
}
```

The useful relational postcondition on the actual returned value `result` is:

```rust
match o {
    None => resolve(f) && d.postcondition_once((), result),
    Some(t) => resolve(d) && f.postcondition_once((t,), result),
}
```

`precondition` and `postcondition_once` refer to the initial closure values and
their exact argument tuples. These are the existing Creusot closure model
predicates, not new application axioms. `resolve` records resolution of the
unused consumed closure in Creusot's borrowing/prophecy model. It is a
postcondition, not permission to require the unused closure's invocation to
succeed. Its presence is needed for composition involving borrowed captures;
do not silently remove it to obtain only a return-value theorem.

For a mathematical output corollary, require refinement of the selected
callback postcondition only:

* `None`: for every `u`, `d.postcondition_once((),u)` implies `u = D`.
* `Some(t)`: for every `u`, `f.postcondition_once((t,),u)` implies `u = F(t)`.

Together with the selected-call precondition and checked return contract, this
entails `result = lazyMap(F,D,o)` when the call returns. The relational contract
may instead carry any output property established by the selected callback.
It does not independently establish callback correctness. A callback whose
postcondition is false does not establish actual successful execution merely
because an implication from that postcondition is true.

## Trait refinement and observation of the receiver

The public `OptionExt<T>` trait has an abstract `Self`, whereas its release
implementation has `Self = Option<T>`. The trait contract must express the same
branch distinction as the implementation contract. Adding an implementation
precondition beneath an unconditional trait declaration is not an acceptable
substitute for proving refinement.

If a proof-only logical observation `option_model(self) : Option<T>` is needed
to state the trait contract, its implementation for `Option<T>` must be the
identity and must be checked. The observation must introduce no runtime bound,
algorithm change, or assumption about an unproved application function. Its
addition to the verification interface and its erasure/correspondence to the
release must be documented. Trait contracts can branch on this observation;
the identity bridge must connect them to the actual receiver.

All generated body, trait-refinement, logical-observation, and associated law
obligations needed by this method belong to the accepted coverage ledger.
Unresolved or missing refinement goals prohibit a claim that the public method
has been verified for trait callers. If only a concrete body is proved, report
that restricted result explicitly.

## Existing standard-library boundary

At the selected official Creusot 0.13 revision
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`, restored under
`../.work/tools/creusot` relative to this directory,
`creusot-std/src/std/option.rs` supplies `Option::map_or_else` with exactly the
selected precondition and resolution-bearing postcondition above. The same
file shows a direct-match model body. `creusot-std/src/std/ops.rs` supplies
`FnOnce::call_once` with its receiver's `precondition(args)` and
`postcondition_once(args,result)`.

The product proof must identify the actual selected external contract in its
generated Coma and VCs. This is proof of the unchanged option-ext delegation
relative to the existing standard-library and closure specifications. It is
not verification of the original Rust standard-library implementation unless
that implementation is separately selected, translated, and proved with its
own evidence. A direct-match body appearing inside `extern_spec!` is not enough
to claim that Rust's standard-library body has been verified in this run.

No additional trusted external contract is anticipated. If one is proposed,
review its necessity, exact domain, and observation limits before relying on
it. Application functions may not be marked `trusted` or supplied with an
assumed successful result.

## Termination, panic, and callback effects

Creusot 0.13's ordinary `requires`/`ensures` contracts establish postconditions on
return, not termination. Its pinned `guide/src/termination.md` requires
`#[check(terminates)]` for total
correctness. The inspected standard `map_or_else` and `FnOnce::call_once`
contracts are not marked as terminating. Therefore keep the following claims
separate:

1. The original wrapper satisfies the selected-call precondition obligations
   and has the specified return relation under the external specifications.
2. Its body and trait refinement have all relevant modeled panic VCs closed.
3. It terminates under stated assumptions about the selected callback.

The third claim remains open unless a checked termination mechanism actually
supports it. Do not add `trusted(terminates)` to the wrapper, assert global
termination of arbitrary callbacks, or describe callback precondition validity
as a termination guarantee. Report only the properties actually recorded by the
pinned proofs.rs adapter, separately from functional properties established by
the raw VCs; do not infer a panic-contract metadata classification from a
different adapter version.

The closure postcondition and `resolve` relation may express modeled borrowed
capture state, but they are not a universal external-effect trace. This scope
does not prove arbitrary IO effects, exact runtime call counts, general aliasing
properties, allocation behavior, or arbitrary destructor panics. If a consumer
proof demonstrates one captured mutable-state example, distinguish that
concrete checked composition from the generic method contract.

## Acceptance evidence and exclusions

* Preserve the exact original delegated executable statement and public generic
  runtime signature; record source/annotation correspondence and hashes.
* Generate fresh Coma and every target/root/leaf VC for the selected method,
  required observations, and trait refinement. Require a positive goal count,
  complete target inventory, all selected goals closed, and successful exits.
* Inspect actual preconditions for impossible or unconditional-false assumptions.
  A successful body VC with a missing callee contract is not sufficient.
* Exercise useful concrete callers or native checks with each branch selected
  and an unused callback that would panic if invoked. These support
  nonvacuity/branch interpretation within their separate evidence category;
  they do not replace generic proof.
* Pin source, annotations, configuration, external models, compiler, verifier,
  and provers before execution and verify unchanged inputs afterward.
* Keep `contains`, `map_or2`, arbitrary third-party implementations of
  `OptionExt`, and any unused inherited/standard-library methods out of this
  report unless they receive their own explicit contracts and complete proof.

This document states obligations and interpretation boundaries. Run outcomes,
goal counts, blockers, and publication status belong in the separate results
record and must not be inferred from the existence of annotations or models.
