import ExtProofs.Ranges

/-!
# Tier 2: bounds record and checked refutations (implementation agent)

`GetBoundsContract` (JSONPTR-002) and `StripPrefixContract` (JSONPTR-001) are
refuted on the extracted adapted bodies, which keep the release arithmetic and
the release string-prefix test.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem usize_add_one_ok (n : Usize) (h : n.val < Usize.max) :
    ∃ m : Usize, (n + 1#usize : Result Usize) = .ok m ∧ m.val = n.val + 1 := by
  obtain ⟨m, hm, hv⟩ := ok_of_spec (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
  exact ⟨m, hm, by simpa using hv⟩

theorem getBoundsExceptMax : GetBoundsExceptMaxRecord := by
  intro xs s e hv hs
  cases s with
  | Included a =>
    cases e with
    | Included b => exact getRangeInclusiveAdapted xs a b hv
    | Excluded b => exact getRangeAdapted xs a b hv
    | Unbounded => exact getRangeFromAdapted xs a hv
  | Excluded a =>
    obtain ⟨m, hm, hmv⟩ := usize_add_one_ok a (hs a rfl)
    cases e with
    | Included b =>
      obtain ⟨r, hr, hres⟩ := getRangeInclusiveAdapted xs m b hv
      refine ⟨r, by simp [jsonptr.adapted_api.get_bounds_adapted, hm, hr], ?_⟩
      simpa [bound, getBounds, hmv] using hres
    | Excluded b =>
      obtain ⟨r, hr, hres⟩ := getRangeAdapted xs m b hv
      refine ⟨r, by simp [jsonptr.adapted_api.get_bounds_adapted, hm, hr], ?_⟩
      simpa [bound, getBounds, hmv] using hres
    | Unbounded =>
      obtain ⟨r, hr, hres⟩ := getRangeFromAdapted xs m hv
      refine ⟨r, by simp [jsonptr.adapted_api.get_bounds_adapted, hm, hr], ?_⟩
      simpa [bound, getBounds, hmv] using hres
  | Unbounded =>
    cases e with
    | Included b => exact getRangeToInclusiveAdapted xs b hv
    | Excluded b => exact getRangeToAdapted xs b hv
    | Unbounded => exact getRangeFullAdapted xs hv

theorem usize_max_add_one : (core.num.Usize.MAX + 1#usize : Result Usize) = .fail .integerOverflow := by
  have hv : core.num.Usize.MAX.val = Usize.max := by simp [core.num.Usize.MAX]
  show UScalar.add core.num.Usize.MAX 1#usize = _
  simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, Result.ofOption]
  rw [dif_neg]
  simp only [UScalar.check_bounds, decide_eq_true_eq, not_lt]
  rw [hv, Usize.max_def]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp [Usize.numBits] at *

def emptySlice : Slice U8 := Slice.from [] (by simp)

theorem emptySlice_valid : ValidPtr emptySlice := by
  have : bytes emptySlice = [] := by simp [bytes, emptySlice]
  rw [ValidPtr, this]; exact (validPointer_iff []).mpr ⟨Or.inl rfl, noBad_nil⟩

/-- JSONPTR-002, checked: the intended `(Bound, Bound)` contract is false for
the extracted body at `Excluded(usize::MAX)`; the machine `start + 1` fails. -/
theorem getBounds_refuted : ¬ GetBoundsContract := by
  intro h
  obtain ⟨r, hr, _⟩ := h emptySlice (.Excluded core.num.Usize.MAX) .Unbounded emptySlice_valid
  simp [jsonptr.adapted_api.get_bounds_adapted, usize_max_add_one] at hr

def slAb : Slice U8 := Slice.from [47#u8, 97#u8, 98#u8] (by simp; scalar_tac)
def slA : Slice U8 := Slice.from [47#u8, 97#u8] (by simp; scalar_tac)

theorem slAb_bytes : bytes slAb = [47, 97, 98] := by simp [bytes, slAb]
theorem slA_bytes : bytes slA = [47, 97] := by simp [bytes, slA]

theorem valid_47 (l : List Nat) (h : NoBad l) : ValidPointer (47 :: l) :=
  (validPointer_iff _).mpr ⟨Or.inr rfl, (noBad_cons 47 l).mpr ⟨fun h' => absurd h' (by decide), h⟩⟩

/-- JSONPTR-001, checked: `"/ab"` minus `"/a"` is `Some("b")` for the extracted
body, which is not a valid pointer; the intended contract gives `None`. -/
theorem stripPrefix_refuted : ¬ StripPrefixContract := by
  intro h
  have hvAb : ValidPtr slAb := by
    rw [ValidPtr, slAb_bytes]; apply valid_47
    simp [noBad_cons, noBad_nil]
  have hvA : ValidPtr slA := by
    rw [ValidPtr, slA_bytes]; apply valid_47
    simp [noBad_cons, noBad_nil]
  obtain ⟨r, hr, hm, _⟩ := h slAb slA hvAb hvA
  obtain ⟨r', hr', hm'⟩ := ok_of_spec (stripPrefix_spec slAb slA)
  rw [hr] at hr'; simp only [Result.ok.injEq] at hr'; subst hr'
  rw [slAb_bytes, slA_bytes] at hm hm'
  have hpre : [47, 97] <+: [47, 97, 98] := ⟨[98], rfl⟩
  rw [if_pos hpre] at hm'
  have hmodel : stripPrefix [47, 97, 98] [47, 97] = none := by decide
  rw [hmodel] at hm
  rw [hm] at hm'
  simp at hm'

/-- The release behaviour behind JSONPTR-001, as a record: the adapted body
returns the raw byte remainder `"b"`. -/
theorem stripPrefix_release_record :
    ∃ r, jsonptr.adapted_api.strip_prefix_adapted slAb slA = .ok (some r) ∧ bytes r = [98] := by
  obtain ⟨r, hr, hm⟩ := ok_of_spec (stripPrefix_spec slAb slA)
  rw [slAb_bytes, slA_bytes, if_pos ⟨[98], rfl⟩] at hm
  cases r with
  | none => simp [obytes] at hm
  | some v => exact ⟨v, hr, by simpa [obytes] using hm⟩

end JsonptrExtProofs
