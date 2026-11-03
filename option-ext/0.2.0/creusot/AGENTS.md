# Creusot workspace for original map_or_else2

This nested independent workspace uses Creusot, not the parent Aeneas activation.
Read the repository Creusot verification and proof-composition skills. Runtime
source is the option-ext0.2.0 release, changed only by imports, verification
annotations and a cfg(creusot) proof-only trait observation. The delegated body
`self.map_or_else(default, f)` must remain unchanged. The two previously checked
Aeneas methods are excluded with cfg(not(creusot)) annotations solely from this
formal scope; native builds retain all methods.

The primary reviews specifications, commands, all positive root/leaf evidence,
trait refinements and coverage. Independent specification and review are separate
from implementation. Never trust application logic or assume false/unselected
callback preconditions. Standard-library closure models do not establish callback
termination. Do not alter the existing Aeneas report or tools. Source publication
and proofs.rs submission require user authorization; the primary handles them.
