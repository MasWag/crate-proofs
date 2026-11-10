import Init

/-! Independent state contracts for integer parsing options, authored by Astra.
The observable state is whether multi-digit optimization is disabled. Both
Boolean states are valid; validity is not a restriction on construction.
These definitions do not refer to generated functions, Rust representations,
or parser outputs. They establish no equivalence of parsing with different
option settings, and no performance guarantee.
-/
namespace LexicalParseIntegerOptionsSpec

abbrev State := Bool

/-- New/default builders, new/default options and the STANDARD constant disable
multi-digit optimization. Options::builder has this same initial state. -/
def defaultState : State := true

def get (state : State) : Bool := state

/-- Builder assignment and both deprecated Options mutators replace the flag
with the supplied value, independently of its previous state. -/
def set (_previous : State) (requested : Bool) : State := requested

/-- Every builder and options state is valid, including false. The trait-level
ParseOptions validity query has the same observable result. -/
def valid (_state : State) : Bool := true

/-- Building preserves the state. The fallible Rust build must return Ok with
this state; unchecked/strict construction must return normally with this state.
The implementation theorem must prove total Aeneas success in every case. -/
def buildState (state : State) : State := state

def rebuild (state : State) : State := state

/-- With the power-of-two feature, from_radix returns the default options for
every u8 argument, even outside 2..36: it does not validate or store the radix.
This is an options-constructor contract, not a parser radix-domain promise. -/
def fromRadix (_radix : Nat) : State := defaultState

def standard : State := defaultState
def smallNumbers : State := true
def largeNumbers : State := false

end LexicalParseIntegerOptionsSpec
