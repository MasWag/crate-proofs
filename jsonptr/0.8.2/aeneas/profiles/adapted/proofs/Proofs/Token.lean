import Proofs.Common
import Proofs.Model

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

theorem bytes_getElem? (s : Slice U8) {i : Usize} (hi : i.val < s.length) {x : U8}
    (hx : x = s.val[i.val]) : (bytes s)[i.val]? = some x.val := by
  simp [bytes, List.getElem?_eq_getElem hi, hx]

@[simp] theorem lit47 : (47#8#uscalar : U8) = 47#u8 := by decide
@[simp] theorem lit126 : (126#8#uscalar : U8) = 126#u8 := by decide
@[simp] theorem lit48 : (48#8#uscalar : U8) = 48#u8 := by decide
@[simp] theorem lit49 : (49#8#uscalar : U8) = 49#u8 := by decide

theorem val_ne_of_ne {x y : U8} (h : ¬ x = y) : x.val ≠ y.val :=
  fun hv => h (UScalar.eq_of_val_eq hv)

theorem bne_val {z c : U8} (h : (z != c) = true) : z.val ≠ c.val := by
  intro hv; have := UScalar.eq_of_val_eq hv; simp [this] at h

theorem not_bne_val {z c : U8} (h : ¬ (z != c) = true) : z.val = c.val := by
  simp at h; rw [h]

/-! ## Target 4: `Token::from_encoded` -/

def EncPost (L : List Nat) : core.result.Result Unit jsonptr.token.EncodingError → Prop
  | .Ok _ => firstEncError L = none
  | .Err err => firstEncError L = some (encError err)

def EncInv (L : List Nat) : Bool × Usize → Prop
  | (false, i) => i.val ≤ L.length ∧ firstEncErrorFrom i.val (L.drop i.val) = firstEncError L
  | (true, i) => i.val ≤ L.length ∧ 0 < i.val ∧ L[i.val - 1]? = some 126 ∧
      firstEncErrorFrom (i.val - 1) (L.drop (i.val - 1)) = firstEncError L

theorem fromEncodedScan_spec (e : Slice U8) :
    jsonptr.token.from_encoded_scan_adapted e ⦃ EncPost (bytes e) ⦄ := by
  unfold jsonptr.token.from_encoded_scan_adapted jsonptr.token.from_encoded_scan_adapted_loop
  have hlen : (bytes e).length = e.length := bytes_length e
  apply loop.spec_decr_nat (fun st : Bool × Usize => e.length - st.2.val) (EncInv (bytes e))
  · rintro ⟨b, i⟩ hinv
    simp only [jsonptr.token.from_encoded_scan_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < e.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec e i hi)
      intro x hx
      have hL := bytes_getElem? e hi hx
      cases b
      · obtain ⟨hle, hT⟩ := hinv
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · apply (spec_ok _).mpr
          simp only [EncPost, encError, encSource]
          rw [← hT, Model.fe_slash (by simpa using hL)]
        · step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
          · rw [show i'.val - 1 = i.val by scalar_tac]; simpa using hL
          · rw [show i'.val - 1 = i.val by scalar_tac]; exact hT
        · step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [show i'.val = i.val + 1 by scalar_tac, ← Model.fe_other hL (by simp) (by simp)]; exact hT
        · step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [show i'.val = i.val + 1 by scalar_tac, ← Model.fe_other hL (by simp) (by simp)]; exact hT
        · rename_i h47 h126 h48 h49
          step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [show i'.val = i.val + 1 by scalar_tac, ← Model.fe_other hL
            (by simpa using val_ne_of_ne h47) (by simpa using val_ne_of_ne h126)]; exact hT
      · obtain ⟨hle, hpos, hprev, hT⟩ := hinv
        simp only [↓reduceIte]
        have hj : i.val - 1 + 1 = i.val := by omega
        have hc : (bytes e)[i.val - 1 + 1]? = some x.val := by rw [hj]; exact hL
        have hesc := Model.fe_esc hprev hc
        rw [hT, hj] at hesc
        split
        · apply (spec_ok _).mpr
          simp only [EncPost, encError, encSource]
          rw [hesc]; simp
        · apply (spec_ok _).mpr
          simp only [EncPost, encError, encSource]
          rw [hesc]; simp
        · step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [show i'.val = i.val - 1 + 2 by scalar_tac, hesc]; simp
        · step as ⟨i', hi'⟩
          refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [show i'.val = i.val - 1 + 2 by scalar_tac, hesc]; simp
        · rename_i h47 h126 h48 h49
          have n47 := val_ne_of_ne h47
          have n48 := val_ne_of_ne h48
          have n49 := val_ne_of_ne h49
          simp at n47 n48 n49
          apply (spec_ok _).mpr
          simp only [EncPost, encError, encSource]
          rw [hesc]; simp [n47, n48, n49]
    next hge =>
      have hi : i.val = e.length := by
        cases b <;> (simp only [EncInv] at hinv; scalar_tac)
      cases b
      · obtain ⟨hle, hT⟩ := hinv
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply (spec_ok _).mpr
        simp only [EncPost]
        rw [← hT, hi, ← hlen, Model.fe_end]
      · obtain ⟨hle, hpos, hprev, hT⟩ := hinv
        simp only [↓reduceIte]
        apply (spec_ok _).mpr
        simp only [EncPost, encError, encSource]
        rw [← hT, Model.fe_esc_end hprev (by rw [hlen]; omega)]
        have : (↑e.len : Nat) = e.length := by simp
        rw [this, ← hi]
        congr 2; omega
  · exact ⟨by scalar_tac, by simp [firstEncError]⟩

/-- Target 4, `Token::from_encoded`. -/
theorem fromEncodedAdapted : FromEncodedContract := by
  intro e
  obtain ⟨r, hr, hpost⟩ := ok_of_spec (fromEncodedScan_spec e)
  cases r with
  | Ok u =>
    refine ⟨.Ok e, ?_, rfl, hpost⟩
    simp [jsonptr.token.from_encoded_adapted, hr]
  | Err err =>
    refine ⟨.Err err, ?_, hpost⟩
    simp [jsonptr.token.from_encoded_adapted, hr]

end JsonptrAdaptedProofs
