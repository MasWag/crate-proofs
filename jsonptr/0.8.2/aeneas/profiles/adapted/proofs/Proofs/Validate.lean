import Proofs.Token

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

/-! ## Target 1: `pointer::validate`

The release `validate_bytes` (generated body identical to the default profile's)
is proved to compute the model's executable scan `ptrScan`, which is the
contract's `pointerError` on slash-led input. -/

/-- Outcome of the byte validator in the model, matching `ptrOutcome`. -/
def bytesOutcome : core.result.Result Unit jsonptr.pointer.ParseError → Option (Option PtrError)
  | .Ok _ => some none
  | .Err .NoLeadingSlash => some (some .noLeadingSlash)
  | .Err (.InvalidEncoding d ⟨t, .Tilde⟩) => some (some (.invalidEncoding d.val t.val))
  | .Err (.InvalidEncoding _ ⟨_, .Slash⟩) => none

def ScanInv (L : List Nat) (T : Option PtrError) : Usize × Usize × Usize → Prop
  | (sep, tok, pos) => pos.val ≤ L.length ∧ sep.val + tok.val = pos.val ∧
      ptrScan pos.val sep.val (L.drop pos.val) = T

theorem scanLoop_spec (bytes' : Slice U8) (sep tok pos : Usize)
    (hinv : ScanInv (bytes bytes') (ptrScan 0 0 (bytes bytes')) (sep, tok, pos)) :
    jsonptr.pointer.validate_bytes_loop1 bytes' sep tok pos
      ⦃ r => bytesOutcome r = some (ptrScan 0 0 (bytes bytes')) ⦄ := by
  have hlen : (bytes bytes').length = bytes'.length := bytes_length bytes'
  unfold jsonptr.pointer.validate_bytes_loop1
  apply loop.spec_decr_nat (fun st : Usize × Usize × Usize => bytes'.length - st.2.2.val)
    (ScanInv (bytes bytes') (ptrScan 0 0 (bytes bytes')))
  · rintro ⟨sep, tok, pos⟩ ⟨hle, hsum, hT⟩
    simp only [jsonptr.pointer.validate_bytes_loop1.body]
    split
    next hlt =>
      have hi : pos.val < bytes'.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec bytes' pos hi)
      intro x hx
      have hL := bytes_getElem? bytes' hi hx
      split
      · step as ⟨p', hp'⟩
        step as ⟨t', ht'⟩
        refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [show p'.val = pos.val + 1 by scalar_tac, ← Model.ps_slash sep.val (by simpa using hL)]
        exact hT
      · step as ⟨i3, hi3⟩
        split
        next hend =>
          apply (spec_ok _).mpr
          simp only [bytesOutcome]
          rw [← hT, Model.ps_tilde_end sep.val (by simpa using hL) (by rw [hlen]; scalar_tac)]
          congr 3; omega
        next hcont =>
          have hi3' : i3.val < bytes'.length := by scalar_tac
          apply spec_bind (Slice.index_usize_spec bytes' i3 hi3')
          intro y hy
          have hc : (bytes bytes')[pos.val + 1]? = some y.val := by
            rw [show pos.val + 1 = i3.val by scalar_tac]; exact bytes_getElem? bytes' hi3' hy
          have htl := Model.ps_tilde sep.val (by simpa using hL) hc
          split
          next h48 =>
            apply spec_bind (Slice.index_usize_spec bytes' i3 hi3')
            intro z hz
            have hzy : z = y := hz.trans hy.symm
            subst hzy
            split
            next h49 =>
              apply (spec_ok _).mpr
              simp only [bytesOutcome]
              have n48 : z.val ≠ 48 := by simpa using bne_val h48
              have n49 : z.val ≠ 49 := by simpa using bne_val h49
              rw [← hT, htl]; simp [n48, n49]; omega
            next h49 =>
              have e49 : z.val = 49 := by simpa using not_bne_val h49
              step as ⟨a1, ha1⟩
              step as ⟨p2, hp2⟩
              step as ⟨a2, ha2⟩
              refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
              rw [show p2.val = pos.val + 2 by scalar_tac, ← hT, htl]; simp [e49]
          next h48 =>
            have e48 : y.val = 48 := by simpa using not_bne_val h48
            step as ⟨a1, ha1⟩
            step as ⟨p2, hp2⟩
            step as ⟨a2, ha2⟩
            refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
            rw [show p2.val = pos.val + 2 by scalar_tac, ← hT, htl]; simp [e48]
      · rename_i h47 h126
        step as ⟨p', hp'⟩
        step as ⟨t', ht'⟩
        refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [show p'.val = pos.val + 1 by scalar_tac, ← Model.ps_other sep.val hL
          (by simpa using val_ne_of_ne h47) (by simpa using val_ne_of_ne h126)]
        exact hT
    next hge =>
      apply (spec_ok _).mpr
      simp only [bytesOutcome]
      have : pos.val = (bytes bytes').length := by scalar_tac
      rw [← hT, this, Model.ps_end]
  · exact hinv

theorem validateBytes_spec (xs : Slice U8) (h : 0 < xs.length) :
    jsonptr.pointer.validate_bytes xs 0#usize ⦃ r => bytesOutcome r = some (pointerError (bytes xs)) ⦄ := by
  obtain ⟨a, rest, hxs⟩ : ∃ a rest, xs.val = a :: rest := by
    cases hv : xs.val with
    | nil => simp [Slice.length, hv] at h
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hb : bytes xs = a.val :: rest.map (fun b => b.val) := by simp [bytes, hxs]
  unfold jsonptr.pointer.validate_bytes
  have h0 : (0#usize : Usize).val < xs.length := by scalar_tac
  apply spec_bind (Slice.index_usize_spec xs 0#usize h0)
  intro x hx
  have hxa : x = a := by simp [hx, hxs]
  subst hxa
  split
  next hne =>
    simp only [↓reduceIte]
    apply (spec_ok _).mpr
    have : x.val ≠ 47 := by simpa using bne_val hne
    simp [bytesOutcome, pointerError, hb, this]
  next heq =>
    have e47 : x.val = 47 := by simpa using not_bne_val heq
    have hpe : pointerError (bytes xs) = ptrScan 0 0 (bytes xs) := by
      simp [pointerError, hb, e47]
    rw [hpe]
    exact scanLoop_spec xs _ _ _ ⟨by simp, by simp, by simp⟩

/-- Target 1, `pointer::validate`. -/
theorem validateAdapted : ValidateContract := by
  intro xs
  by_cases hlen : xs.length = 0
  · have hnil : xs.val = [] := List.length_eq_zero_iff.mp hlen
    refine ⟨.Ok xs, ?_, ?_, ?_⟩
    · simp [jsonptr.pointer.validate_adapted, core.slice.Slice.is_empty, hlen]
    · simp [ptrOutcome, pointerError, bytes, hnil]
    · intro v hv; cases hv; rfl
  · obtain ⟨r, hr, hpost⟩ := ok_of_spec (validateBytes_spec xs (by omega))
    cases r with
    | Ok u =>
      refine ⟨.Ok xs, ?_, ?_, ?_⟩
      · simp [jsonptr.pointer.validate_adapted, core.slice.Slice.is_empty, hlen, hr]
      · simpa [bytesOutcome, ptrOutcome] using hpost
      · intro v hv; cases hv; rfl
    | Err pe =>
      refine ⟨.Err pe, ?_, ?_, ?_⟩
      · simp [jsonptr.pointer.validate_adapted, core.slice.Slice.is_empty, hlen, hr]
      · rw [← hpost]; rcases pe with _ | ⟨d, ⟨t, src⟩⟩ <;> try cases src
        all_goals rfl
      · intro v hv; cases hv

end JsonptrAdaptedProofs
