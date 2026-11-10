import GenericScalarSpecs
import Aeneas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Aeneas Aeneas.Std Result
open LexicalParseIntegerGenericSpec
namespace LexicalGenericComposition
set_option maxHeartbeats 2000000

theorem scan_append (radix bound : Nat) (negative isPartial : Bool)
 (a b : List Nat) (value index : Nat) :
 scan radix bound negative isPartial (a++b) value index =
 match scan radix bound negative isPartial a value index with
 | .value next j => if j < index+a.length then .value next j else scan radix bound negative isPartial b next j
 | other => other := by
 induction a generalizing value index with
 | nil => simp [scan]
 | cons c a ih =>
   cases hc : LexicalParseIntegerDigitSpec.digit radix c with
   | none => cases isPartial <;> simp [scan,hc]
   | some d =>
     simp only [List.cons_append,scan,hc,List.length_cons]
     split
     · rw [ih]; simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
     · cases negative <;> rfl

theorem scan_le (radix bound : Nat) (negative isPartial : Bool)
 (a : List Nat) (value index next j : Nat)
 (h : scan radix bound negative isPartial a value index = .value next j) : j ≤ index+a.length := by
 induction a generalizing value index with
 | nil => simp only [scan,ScanResult.value.injEq] at h; simp only [List.length_nil]; omega
 | cons c a ih =>
   simp only [scan] at h
   cases hc : LexicalParseIntegerDigitSpec.digit radix c with
   | none => cases isPartial <;> simp_all [ScanResult.value.injEq]
   | some d =>
     simp only [hc] at h
     split at h
     · have hh := ih _ _ h; simp only [List.length_cons]; omega
     · cases negative <;> contradiction
theorem selected_prefix_safe (byteWidth radix : Nat) (signed : Bool)
 (hw : byteWidth∈[1,2,4,8,16]) (hr : 2≤radix ∧ radix≤36) :
 selectedPrefixSafe byteWidth signed radix := by
 rcases hr with ⟨hrlo,hrhi⟩
 simp at hw
 rcases hw with rfl|rfl|rfl|rfl|rfl <;> cases signed <;>
 interval_cases radix <;>
 norm_num [selectedPrefixSafe,uncheckedBound,overflowDigits,magnitudeBound,unsignedBound,positiveBound]
#print axioms selected_prefix_safe
theorem unchecked_bound_step (radix bound value count digit : Nat)
 (hr : 2≤radix) (hd : digit<radix)
 (h : uncheckedBound radix bound value (count+1)) :
 uncheckedBound radix bound (radix*value+digit) count := by
 unfold uncheckedBound at *
 have hp : 1≤radix^count := by
   have hpos : 0<radix^count := Nat.pow_pos (by omega)
   omega
 have hm : radix^count*(digit+1)≤radix^count*radix := Nat.mul_le_mul_left _ (by omega)
 have he : radix^count*(radix*value+digit) = radix^(count+1)*value+radix^count*digit := by rw [Nat.pow_succ]; ring
 rw [he]
 simp only [Nat.mul_add,Nat.mul_one] at hm
 simp only [Nat.pow_succ] at *
 omega
theorem unchecked_bound_value (radix bound value count : Nat) (hr : 2≤radix)
 (h : uncheckedBound radix bound value count) : value≤bound := by
 unfold uncheckedBound at h
 have hp : 1≤radix^count := by
   have hpos : 0<radix^count := Nat.pow_pos (by omega)
   omega
 have hm : value≤radix^count*value := by
   calc value=1*value := by omega
        _≤radix^count*value := Nat.mul_le_mul_right _ hp
 omega
unseal Result in
theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun v _ hp => ⟨v, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)


theorem unchecked_zero_shorter (radix bound a b : Nat) (hr : 2≤radix) (hab : a≤b)
 (h : uncheckedBound radix bound 0 b) : uncheckedBound radix bound 0 a := by
 unfold uncheckedBound at *
 simp only [Nat.mul_zero,Nat.zero_add] at *
 have hp := Nat.pow_le_pow_right (by omega : 0<radix) hab
 omega
theorem scan_complete_consumed (radix bound : Nat) (neg : Bool) (a : List Nat) (value index next j : Nat)
 (h : scan radix bound neg false a value index=.value next j) : j=index+a.length := by
 induction a generalizing value index with
 | nil => simp only [scan,ScanResult.value.injEq] at h; simp only [List.length_nil]; omega
 | cons c a ih =>
   simp only [scan] at h
   cases hc : LexicalParseIntegerDigitSpec.digit radix c with
   | none => simp [hc] at h
   | some d =>
     simp only [hc] at h
     split at h
     · have hh := ih _ _ h; simp only [List.length_cons]; omega
     · cases neg <;> contradiction
end LexicalGenericComposition
