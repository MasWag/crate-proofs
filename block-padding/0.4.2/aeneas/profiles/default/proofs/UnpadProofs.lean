import BlockPaddingVerificationApi
import BlockPadding.Specs
open Aeneas Aeneas.Std Aeneas.Std.WP Result
open block_padding_verification_api
namespace BlockPadding.UnpadProof
set_option maxHeartbeats 4000000

def bytes (s : Slice Std.U8) := s.val.map UScalar.val

abbrev RevRange := core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)

theorem rev_next (it : RevRange) (h : it.iter.start.val < it.iter.«end».val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it =
    .ok (some (UScalar.ofNatCore (it.iter.«end».val - 1) (by have := it.iter.«end».hBounds; omega)),
      ⟨{it.iter with «end» := (UScalar.ofNatCore (it.iter.«end».val - 1)
        (by have := it.iter.«end».hBounds; omega))}⟩) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked, core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    show 1 ≤ it.iter.«end».val by omega, h]

 theorem rev_next_empty (it : RevRange) (h : it.iter.«end».val ≤ it.iter.start.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it =
    .ok (none, it) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep, core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    show ¬it.iter.start.val < it.iter.«end».val by omega]

def ZeroCut (b : Slice Std.U8) (p : Nat) : Prop :=
  p ≤ b.length ∧ (∀ j, p ≤ j → (hj : j < b.length) → b.val[j] = 0#u8) ∧
    (p = 0 ∨ 0 < p ∧ ∃ (h : p - 1 < b.length), b.val[p-1] ≠ 0#u8)

theorem zero_loop (b : Slice Std.U8) (it : RevRange)
    (hstart : it.iter.start = 0#usize) (hend : it.iter.«end».val ≤ b.length)
    (hz : ∀ j, it.iter.«end».val ≤ j → (hj : j < b.length) → b.val[j] = 0#u8) :
    ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad_loop it b
      ⦃ out => ∃ p, out.val = b.val.take p ∧ ZeroCut b p ⦄ := by
  unfold ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad_loop
  apply loop.spec_decr_nat (fun i : RevRange => i.iter.«end».val)
    (fun i => i.iter.start = 0#usize ∧ i.iter.«end».val ≤ b.length ∧
      ∀ j, i.iter.«end».val ≤ j → (hj : j < b.length) → b.val[j] = 0#u8)
  · intro i ⟨hs, he, hz⟩
    simp only [Slice.length] at he hz
    unfold ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad_loop.body
    by_cases hp : 0 < i.iter.«end».val
    · rw [rev_next i (by simpa [hs] using hp)]
      simp only [bind_ok]
      step as ⟨v, hv⟩
      split
      · rename_i hne
        step as ⟨p, hpval⟩
        step as ⟨out, hout, hlen⟩
        simp only [ZeroCut, Slice.length]
        refine ⟨p.val, by simpa [List.slice] using hout, ?_, ?_, ?_⟩
        · omega
        · intro j hj hjlen
          apply hz j (by omega) hjlen
        · right
          have hj : p.val - 1 < b.val.length := by omega
          refine ⟨by omega, hj, ?_⟩
          simp_all
      · rename_i hzero
        simp only [spec_ok]
        simp only [UScalar.ofNatCore_val_eq, Slice.length]
        refine ⟨hs, by omega, ?_, ?_⟩
        · intro j hj hjlen
          by_cases hold : i.iter.«end».val ≤ j
          · exact hz j hold hjlen
          · have heq : j = i.iter.«end».val - 1 := by omega
            subst j
            apply UScalar.eq_of_val_eq
            simpa using (by simpa [hv] using hzero : b.val[i.iter.«end».val - 1].val = 0)
        · omega
    · rw [rev_next_empty i (by simp [hs]; omega)]
      simp only [bind_ok]
      step as ⟨out, hout, hlen⟩
      refine ⟨0, by simpa [List.slice] using hout, Nat.zero_le _, ?_, Or.inl rfl⟩
      intro j hj hjlen
      exact hz j (by omega) hjlen
  · exact ⟨hstart, hend, hz⟩

theorem zero_cut_spec (b : Slice Std.U8) (p : Nat) (h : ZeroCut b p) :
    Spec.Accepted .zero (bytes b) p := by
  rcases h with ⟨hp, hz, hlast⟩
  simp only [Spec.Accepted, Spec.ZeroPrefix, bytes, List.length_map]
  refine ⟨hp, ?_, ?_⟩
  · apply List.ext_getElem
    · simp
    · intro j hj hk
      simp only [List.getElem_drop, List.getElem_map, List.getElem_replicate]
      rw [hz (p+j) (by omega) (by simp only [List.length_drop, List.length_map] at hj; simpa [Slice.length] using (show p+j < b.val.length by omega))]
      rfl
  · rcases hlast with hzero | ⟨hpos, hl, hn⟩
    · exact Or.inl hzero
    · right
      refine ⟨(bytes b).take (p-1), b.val[p-1].val, ?_, ?_⟩
      · have heq : p = (p-1)+1 := by omega
        conv_lhs => rw [heq, List.take_add_one]
        simp [bytes, hl]
      · intro heq
        apply hn
        apply UScalar.eq_of_val_eq
        simpa using heq

theorem zero_unpad (b : Slice Std.U8) :
    ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad b
      ⦃ r => ∃ out p, r = .Ok out ∧ bytes out = (bytes b).take p ∧
          Spec.Accepted .zero (bytes b) p ⦄ := by
  unfold ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad
  step as ⟨it, hit⟩
  step with zero_loop as ⟨out, p, hout, hcut⟩
  · refine ⟨out, p, rfl, ?_, zero_cut_spec b p hcut⟩
    simp [bytes, hout, List.map_take]

def IsoCut (b : Slice Std.U8) (p : Nat) : Prop :=
  ∃ hp : p < b.length, b.val[p] = 128#u8 ∧
    ∀ j, p < j → (hj : j < b.length) → b.val[j] = 0#u8

theorem iso_cut_spec (b : Slice Std.U8) (p : Nat) :
    IsoCut b p ↔ Spec.Accepted .iso7816 (bytes b) p := by
  simp only [IsoCut, Spec.Accepted, bytes, List.length_map, Slice.length]
  constructor
  · rintro ⟨hp, hmark, hz⟩
    refine ⟨hp, ?_⟩
    apply List.ext_getElem
    · simp; omega
    · intro j hj hk
      by_cases hzero : j = 0
      · subst j
        simpa using congrArg UScalar.val hmark
      · have hpos : 0 < j := by omega
        simp only [List.getElem_drop, List.getElem_map]
        rw [hz (p+j) (by omega) (by simp only [List.length_drop, List.length_map] at hj; omega)]
        cases j with
        | zero => omega
        | succ j => simp
  · rintro ⟨hp, hsuffix⟩
    refine ⟨hp, ?_, ?_⟩
    · have he := congrArg (fun xs : List Nat => xs[0]?) hsuffix
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_map] at he
      simp only [List.getElem?_eq_getElem hp, Option.map_some] at he
      apply UScalar.eq_of_val_eq
      simpa using he
    · intro j hj hjlen
      have he := congrArg (fun xs : List Nat => xs[j-p]?) hsuffix
      have hsub : p+(j-p) = j := by omega
      have hpos : 0 < j-p := by omega
      simp only [List.getElem?_drop, hsub, List.getElem?_map] at he
      simp only [List.getElem?_eq_getElem hjlen, Option.map_some] at he
      cases hdiff : j-p with
      | zero => omega
      | succ k =>
        simp only [List.cons_append, List.nil_append, hdiff, List.getElem?_cons_succ, List.getElem?_replicate] at he
        split at he
        · simp only [Option.some.injEq] at he
          apply UScalar.eq_of_val_eq
          simpa using he
        · contradiction

theorem iso_match {α : Type} (v : Std.U8) (a b c : α) :
    Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad_loop.body.match_1
      (fun _ => α) v (fun _ => a) (fun _ => b) (fun _ => c) =
      if v = (⟨BitVec.ofNat 8 128⟩ : Std.U8) then a else
      if v = (⟨BitVec.ofNat 8 0⟩ : Std.U8) then b else c := by
  cases v
  unfold Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad_loop.body.match_1
  split <;> simp_all

theorem iso_loop (b : Slice Std.U8) (it : RevRange)
    (hstart : it.iter.start = 0#usize) (hend : it.iter.«end».val ≤ b.length)
    (hz : ∀ j, it.iter.«end».val ≤ j → (hj : j < b.length) → b.val[j] = 0#u8) :
    Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad_loop it b
      ⦃ r => match r with
        | .Ok out => ∃ p, out.val = b.val.take p ∧ IsoCut b p
        | .Err _ => ¬ ∃ p, IsoCut b p ⦄ := by
  unfold Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad_loop
  apply loop.spec_decr_nat (fun i : RevRange => i.iter.«end».val)
    (fun i => i.iter.start = 0#usize ∧ i.iter.«end».val ≤ b.length ∧
      ∀ j, i.iter.«end».val ≤ j → (hj : j < b.length) → b.val[j] = 0#u8)
  · intro i ⟨hs, he, hz⟩
    simp only [Slice.length] at he hz
    unfold Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad_loop.body
    unfold Aeneas.Std.uncurry
    by_cases hp : 0 < i.iter.«end».val
    · rw [rev_next i (by simpa [hs] using hp)]
      simp only [bind_ok]
      step as ⟨v, hv⟩
      rw [iso_match]
      by_cases hm : v = (⟨BitVec.ofNat 8 128⟩ : Std.U8)
      · simp only [hm, ↓reduceIte]
        step as ⟨out, hout, hlen⟩
        simp only [IsoCut, Slice.length]
        refine ⟨i.iter.«end».val-1, by simpa [List.slice] using hout, by omega, ?_, ?_⟩
        · exact hv.symm.trans (hm.trans (by apply UScalar.eq_of_val_eq; decide))
        · intro j hj hjlen
          exact hz j (by omega) hjlen
      · simp only [hm, ↓reduceIte]
        by_cases hzv : v = (⟨BitVec.ofNat 8 0⟩ : Std.U8)
        · simp only [hzv, ↓reduceIte, spec_ok, UScalar.ofNatCore_val_eq, Slice.length]
          refine ⟨hs, by omega, ?_, by omega⟩
          intro j hj hjlen
          by_cases hold : i.iter.«end».val ≤ j
          · exact hz j hold hjlen
          · have heq : j = i.iter.«end».val - 1 := by omega
            subst j
            exact hv.symm.trans (hzv.trans (by apply UScalar.eq_of_val_eq; decide))
        · simp only [hzv, ↓reduceIte, spec_ok]
          rintro ⟨q, hq, hmark, hqz⟩
          by_cases hbefore : q < i.iter.«end».val - 1
          · have hh := hqz (i.iter.«end».val-1) hbefore (by simp [Slice.length]; omega)
            exact hzv (hv.trans hh)
          · by_cases hequal : q = i.iter.«end».val - 1
            · subst q
              exact hm (hv.trans hmark)
            · have hh := hz q (by omega) hq
              have : (128#u8) = 0#u8 := hmark.symm.trans hh
              contradiction
    · rw [rev_next_empty i (by simp [hs]; omega)]
      simp only [bind_ok]
      apply (spec_ok _).mpr
      rintro ⟨q, hqcut⟩
      rcases hqcut with ⟨hq, hm, hqz⟩
      have hh := hz q (by omega) hq
      simp_all
  · exact ⟨hstart, hend, hz⟩

theorem iso_unpad (b : Slice Std.U8) :
    Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad b
      ⦃ r => match r with
        | .Ok out => ∃ p, bytes out = (bytes b).take p ∧
            Spec.Accepted .iso7816 (bytes b) p
        | .Err _ => Spec.Rejected .iso7816 (bytes b) ⦄ := by
  unfold Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad
  step as ⟨it, hit⟩
  step with iso_loop as ⟨r, hr⟩
  cases r with
  | Ok out =>
    rcases hr with ⟨p, hout, hcut⟩
    refine ⟨p, ?_, (iso_cut_spec b p).mp hcut⟩
    simp [bytes, hout, List.map_take]
  | Err e =>
    rintro ⟨p, hp⟩
    exact hr ⟨p, (iso_cut_spec b p).mpr hp⟩

theorem spec_result_ok {α : Type _} {m : Result α} {post : α → Prop}
    (h : WP.spec m post) : ∃ value, m = Result.ok value ∧ post value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, (WP.spec_ok value).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem zero_unpad_total (b : Slice Std.U8) :
    ∃ out p, ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_unpad b =
      .ok (.Ok out) ∧ bytes out = (bytes b).take p ∧
        Spec.Accepted .zero (bytes b) p := by
  obtain ⟨r, hr, out, p, heq, hout, hp⟩ := spec_result_ok (zero_unpad b)
  exact ⟨out, p, heq ▸ hr, hout, hp⟩

theorem iso_unpad_total (b : Slice Std.U8) :
    ∃ r, Iso7816.Insts.Block_padding_verification_apiPadding.raw_unpad b = .ok r ∧
      match r with
      | .Ok out => ∃ p, bytes out = (bytes b).take p ∧
          Spec.Accepted .iso7816 (bytes b) p
      | .Err _ => Spec.Rejected .iso7816 (bytes b) :=
  spec_result_ok (iso_unpad b)
end BlockPadding.UnpadProof
