import Proofs.Common
import Proofs.Model
import Proofs.Split
import Proofs.Token
import Proofs.Validate
import Proofs.Index
import Proofs.Codec
import Proofs.Resolve

/-!
# Proofs of the adapted jsonptr contracts

Each target has its own module so that further modules can be added without
editing these:

* `Proofs.Validate`: target 1 (`validateAdapted`)
* `Proofs.Codec`: targets 2 and 3 (`newAdapted`, `decodedAdapted`)
* `Proofs.Token`: target 4 (`fromEncodedAdapted`)
* `Proofs.Index`: target 5 (`fromStrAdapted`)
* `Proofs.Split`: target 6 (`splitFrontAdapted`)
* `Proofs.Resolve`: target 7 (`resolveAdapted`) and its single-step support
  theorem `resolveStepAdapted`
* `Proofs.Model`: lemmas about the specification model only
* `Proofs.Common`: shared helpers
-/
