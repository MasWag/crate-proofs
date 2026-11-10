# Sign helper contract

The independently authored `SignSpecs.lean` models `parse_sign!` over the byte
at the current cursor, signedness, forbidden positive sign, and required sign.
Accepted `+` or signed `-` advances the cursor once. All other accepted inputs
leave it unchanged. Forbidden `+` returns `InvalidPositiveSign` at the unchanged
cursor; a missing required sign returns `MissingSign` there. A sign alone is
accepted by this helper; nonempty digit checks belong to the caller.

`LexicalParseIntegerSignProofs.sign_spec` proves total success for the actual
generated `parse_sign_state` body and compares both its `Result` and returned
cursor to the independent model. Only a branch that advances the cursor needs
room for one `usize` step. The source checker reconstructs the release macro
branch tree with explicit byte, cursor, and computed flag arguments. Flag
calculation by `NumberFormat` and `Integer`, and the surrounding parser call,
remain separate release-correspondence obligations.
