import Aeneas
import Specs
open Aeneas Aeneas.Std
namespace NumConvProof
@[simp] theorem unsignedCastSelf {t : UScalarTy} (x : UScalar t) : UScalar.cast t x = x :=
  UScalar.eq_of_val_eq (UScalar.cast_val_mod_pow_greater_numBits_eq t x (by omega))
@[simp] theorem signedCastSelf {t : IScalarTy} (x : IScalar t) : IScalar.cast t x = x :=
  IScalar.eq_of_val_eq (IScalar.val_mod_pow_greater_numBits t x (by omega))

def unsignedSat {s t : UScalarTy} (x : UScalar s) (lo hi : UScalar t) : Result (UScalar t) :=
  if x > UScalar.cast s hi then .ok hi
  else if x < UScalar.cast s lo then .ok lo else .ok (UScalar.cast t x)

def unsignedChecked {s t : UScalarTy} (x : UScalar s) (lo hi : UScalar t) : Result (Option (UScalar t)) :=
  if x > UScalar.cast s hi then .ok none
  else if x < UScalar.cast s lo then .ok none else .ok (some (UScalar.cast t x))

theorem unsignedSat_spec {s t : UScalarTy} (x : UScalar s) (lo hi : UScalar t)
    (hw : t.numBits ≤ s.numBits) (hlh : lo.val ≤ hi.val) :
    ∃ out, unsignedSat x lo hi = .ok out ∧ (out.val : Int) =
      NumConvSpec.saturate lo.val hi.val x.val := by
  have hcl := UScalar.cast_val_mod_pow_greater_numBits_eq s lo hw
  have hch := UScalar.cast_val_mod_pow_greater_numBits_eq s hi hw
  unfold unsignedSat
  simp only [UScalar.lt_equiv, hcl, hch]
  split
  · rename_i h
    refine ⟨hi, rfl, ?_⟩
    simp [NumConvSpec.saturate, min_eq_left (show (hi.val : Int) ≤ x.val by omega), max_eq_right (show (lo.val : Int) ≤ hi.val by omega)]
  · split
    · rename_i hupper hlower
      refine ⟨lo, rfl, ?_⟩
      simp [NumConvSpec.saturate, min_eq_right (show (x.val : Int) ≤ hi.val by omega), max_eq_left (show (x.val : Int) ≤ lo.val by omega)]
    · rename_i hupper hlower
      have hc : (UScalar.cast t x).val = x.val := by
        apply UScalar.cast_val_mod_pow_of_inBounds_eq
        have hb := hi.hBounds
        omega
      refine ⟨UScalar.cast t x, rfl, ?_⟩
      rw [hc]
      simp [NumConvSpec.saturate, min_eq_right (show (x.val : Int) ≤ hi.val by omega), max_eq_right (show (lo.val : Int) ≤ x.val by omega)]

theorem unsignedChecked_spec {s t : UScalarTy} (x : UScalar s) (lo hi : UScalar t)
    (hw : t.numBits ≤ s.numBits) :
    ∃ out, unsignedChecked x lo hi = .ok out ∧ out.map (fun v => (v.val : Int)) =
      NumConvSpec.checked lo.val hi.val x.val := by
  have hcl := UScalar.cast_val_mod_pow_greater_numBits_eq s lo hw
  have hch := UScalar.cast_val_mod_pow_greater_numBits_eq s hi hw
  unfold unsignedChecked
  simp only [UScalar.lt_equiv, hcl, hch]
  split
  · rename_i h
    refine ⟨none, rfl, ?_⟩
    simp [NumConvSpec.checked]; omega
  · split
    · rename_i hupper hlower
      refine ⟨none, rfl, ?_⟩
      simp [NumConvSpec.checked]; omega
    · rename_i hupper hlower
      have hc : (UScalar.cast t x).val = x.val := by
        apply UScalar.cast_val_mod_pow_of_inBounds_eq
        have hb := hi.hBounds
        omega
      refine ⟨some (UScalar.cast t x), rfl, ?_⟩
      simp [NumConvSpec.checked, hc]; omega

def signedSat {s t : IScalarTy} (x : IScalar s) (lo hi : IScalar t) : Result (IScalar t) :=
  if x > IScalar.cast s hi then .ok hi
  else if x < IScalar.cast s lo then .ok lo else .ok (IScalar.cast t x)

def signedChecked {s t : IScalarTy} (x : IScalar s) (lo hi : IScalar t) : Result (Option (IScalar t)) :=
  if x > IScalar.cast s hi then .ok none
  else if x < IScalar.cast s lo then .ok none else .ok (some (IScalar.cast t x))

theorem signedSat_spec {s t : IScalarTy} (x : IScalar s) (lo hi : IScalar t)
    (hw : t.numBits ≤ s.numBits) (hlh : lo.val ≤ hi.val) :
    ∃ out, signedSat x lo hi = .ok out ∧ (out.val : Int) =
      NumConvSpec.saturate lo.val hi.val x.val := by
  have hcl := IScalar.val_mod_pow_greater_numBits s lo hw
  have hch := IScalar.val_mod_pow_greater_numBits s hi hw
  unfold signedSat
  simp only [IScalar.lt_equiv, hcl, hch]
  split
  · rename_i h
    refine ⟨hi, rfl, ?_⟩
    simp [NumConvSpec.saturate, min_eq_left (show (hi.val : Int) ≤ x.val by omega), max_eq_right (show (lo.val : Int) ≤ hi.val by omega)]
  · split
    · rename_i hupper hlower
      refine ⟨lo, rfl, ?_⟩
      simp [NumConvSpec.saturate, min_eq_right (show (x.val : Int) ≤ hi.val by omega), max_eq_left (show (x.val : Int) ≤ lo.val by omega)]
    · rename_i hupper hlower
      have hc : (IScalar.cast t x).val = x.val := by
        apply IScalar.val_mod_pow_inBounds
        · have hb := lo.hBounds
          omega
        · have hb := hi.hBounds
          omega
      refine ⟨IScalar.cast t x, rfl, ?_⟩
      rw [hc]
      simp [NumConvSpec.saturate, min_eq_right (show (x.val : Int) ≤ hi.val by omega), max_eq_right (show (lo.val : Int) ≤ x.val by omega)]

theorem signedChecked_spec {s t : IScalarTy} (x : IScalar s) (lo hi : IScalar t)
    (hw : t.numBits ≤ s.numBits) :
    ∃ out, signedChecked x lo hi = .ok out ∧ out.map (fun v => (v.val : Int)) =
      NumConvSpec.checked lo.val hi.val x.val := by
  have hcl := IScalar.val_mod_pow_greater_numBits s lo hw
  have hch := IScalar.val_mod_pow_greater_numBits s hi hw
  unfold signedChecked
  simp only [IScalar.lt_equiv, hcl, hch]
  split
  · rename_i h
    refine ⟨none, rfl, ?_⟩
    simp [NumConvSpec.checked]; omega
  · split
    · rename_i hupper hlower
      refine ⟨none, rfl, ?_⟩
      simp [NumConvSpec.checked]; omega
    · rename_i hupper hlower
      have hc : (IScalar.cast t x).val = x.val := by
        apply IScalar.val_mod_pow_inBounds
        · have hb := lo.hBounds
          omega
        · have hb := hi.hBounds
          omega
      refine ⟨some (IScalar.cast t x), rfl, ?_⟩
      simp [NumConvSpec.checked, hc]; omega
end NumConvProof
