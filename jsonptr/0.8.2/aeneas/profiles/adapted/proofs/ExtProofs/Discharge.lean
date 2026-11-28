import ExtProofs.Tier3
import Proofs

/-! # Tier 3 wrappers discharged against targets 1 and 5 (implementation agent 1's theorems) -/

open JsonptrExtSpec

namespace JsonptrExtProofs

theorem pointerParseAdaptedDischarged : PointerParseContract := pointerParseAdapted JsonptrAdaptedProofs.validateAdapted
theorem bufTryFromStrAdaptedDischarged : BufTryFromStrContract := bufTryFromStrAdapted JsonptrAdaptedProofs.validateAdapted
theorem bufTryFromStringAdaptedDischarged : BufTryFromStringContract :=
  bufTryFromStringAdapted JsonptrAdaptedProofs.validateAdapted
theorem bufParseAdaptedDischarged : BufParseContract := bufParseAdapted JsonptrAdaptedProofs.validateAdapted
theorem fromStaticAdaptedDischarged : FromStaticContract := fromStaticAdapted JsonptrAdaptedProofs.validateAdapted
theorem isNextAdaptedDischarged : IsNextContract := isNextAdapted JsonptrAdaptedProofs.fromStrAdapted

end JsonptrExtProofs
