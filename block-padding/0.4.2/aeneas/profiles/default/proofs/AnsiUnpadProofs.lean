import Proofs
open Aeneas Aeneas.Std Aeneas.Std.WP Result
open block_padding_verification_api
namespace BlockPadding.AnsiUnpadProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def Zeros (b : Slice Std.U8) (s e : Nat) : Prop :=
  ∀ j, s ≤ j → j < e → (hj : j < b.length) → b.val[j] = 0#u8

theorem ansi_loop (b : Slice Std.U8) (bs s i : Std.Usize)
    (hbs : bs.val = b.length) (hpos : 0 < bs.val)
    (hsi : s.val ≤ i.val) (hib : i.val ≤ bs.val-1)
    (hprefix : Zeros b s.val i.val) :
    AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad_loop b bs s i
      ⦃ r => match r with
        | .Ok out => out.val = b.val.take s.val ∧ Zeros b s.val (bs.val-1)
        | .Err _ => ¬Zeros b s.val (bs.val-1) ⦄ := by
  unfold AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad_loop
  apply loop.spec_decr_nat (fun i : Std.Usize => bs.val-1-i.val)
    (fun i => s.val ≤ i.val ∧ i.val ≤ bs.val-1 ∧ Zeros b s.val i.val)
  · intro i ⟨hsi, hib, hprefix⟩
    unfold AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad_loop.body
    step as ⟨last, hlast⟩
    split
    · rename_i hlt
      step as ⟨v, hv⟩
      split
      · rename_i hne
        simp only [spec_ok]
        intro hall
        have hi : i.val < b.length := by omega
        have he := hall i.val hsi (by scalar_tac) hi
        simp_all
      · rename_i heq
        step as ⟨next, hn⟩
        refine ⟨by omega, by scalar_tac, ?_, by scalar_tac⟩
        intro j hjs hjnext hj
        by_cases hold : j < i.val
        · exact hprefix j hjs hold hj
        · have hjEq : j = i.val := by omega
          subst j
          rw [← hv]
          apply UScalar.eq_of_val_eq
          simpa using heq
    · rename_i hge
      step as ⟨out, hout, hlen⟩
      refine ⟨by simpa [List.slice] using hout, ?_⟩
      intro j hjs hje hj
      apply hprefix j hjs (by scalar_tac) hj
  · exact ⟨hsi, hib, hprefix⟩

def AnsiCut (b : Slice Std.U8) (p : Nat) : Prop :=
  ∃ n : Std.U8, 0 < n.val ∧ n.val ≤ b.length ∧ p = b.length-n.val ∧
    ∃ hl : b.length-1 < b.length, b.val[b.length-1] = n ∧ Zeros b p (b.length-1)

theorem ansi_unpad_cut (b : Slice Std.U8)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad b
      ⦃ r => match r with
        | .Ok out => ∃ p, out.val = b.val.take p ∧ AnsiCut b p
        | .Err _ => ¬∃ p, AnsiCut b p ⦄ := by
  unfold AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad
  step
  step as ⟨last, hlast⟩
  step as ⟨n, hn⟩
  step as ⟨count, hcount⟩
  have hc : count.val = n.val := by rw [hcount]; simp
  have hl : b.length-1 < b.val.length := by change b.length-1 < b.length; omega
  have hlastN : b.val[b.length-1]'hl = n := by simpa [hlast] using hn.symm
  split
  · rename_i hzero
    simp only [spec_ok]
    rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hz⟩
    have he : nc = n := hlastn.symm.trans hlastN
    have hzval : count.val = 0 := by rw [hzero]; rfl
    have hnzero : n.val = 0 := by omega
    rw [he] at hnc
    omega
  · rename_i hnzero
    split
    · rename_i hbig
      simp only [spec_ok]
      rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hz⟩
      have he : nc = n := hlastn.symm.trans hlastN
      rw [he] at hnb
      simp only [UScalar.lt_equiv, Slice.len_val] at hbig
      omega
    · rename_i hsmall
      simp only [UScalar.lt_equiv, Slice.len_val] at hsmall
      have hnle : n.val ≤ b.length := by omega
      have hnpos : 0 < n.val := by
        have he : count.val ≠ 0 := by simpa using hnzero
        omega
      step as ⟨s, hs⟩
      simp only [Slice.len_val] at hs
      have hsval : s.val = b.length - n.val := by omega
      step with ansi_loop as ⟨r, hr⟩
      · intro j hjs hje hj; omega
      · cases r with
        | Ok out =>
          rcases hr with ⟨hout, hall⟩
          exact ⟨s.val, hout, n, hnpos, hnle, hsval, hl, hlastN, hall⟩
        | Err e =>
          rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hz⟩
          have he : nc = n := hlastn.symm.trans hlastN
          rw [he] at hp
          apply hr
          have hpEq : p = s.val := by omega
          subst p
          simpa only [Slice.len_val, ← hsval] using hz

 theorem cut_accepted (b : Slice Std.U8) (p : Nat) (h : AnsiCut b p) :
    Spec.Accepted .ansiX923 (Proof.bytes b) p := by
  rcases h with ⟨n, hnpos, hnle, hp, hl, hlast, hall⟩
  have hnmax : n.val ≤ 255 := by scalar_tac
  simp only [Spec.Accepted, Proof.bytes, List.length_map]
  refine ⟨n.val, hnpos, hnle, hnmax, hp, ?_⟩
  apply List.ext_getElem
  · simp; change b.length-p=(n.val-1)+1; omega
  · intro j hj hk
    simp only [List.getElem_drop, List.getElem_map]
    have hidx : p+j < b.length := by simp only [List.length_drop, List.length_map] at hj; change p+j < b.val.length; omega
    by_cases hjlast : j < n.val-1
    · rw [List.getElem_append_left (by simpa using hjlast)]
      simp only [List.getElem_replicate]
      exact congrArg UScalar.val (hall (p+j) (by omega) (by omega) hidx)
    · have hjEq : j = n.val-1 := by simp at hk; omega
      have hlastidx : p+j = b.length-1 := by omega
      rw [List.getElem_append_right (by simp; omega)]
      have hjlen : j - (n.val - 1) = 0 := by omega
      simp only [List.length_replicate, hjlen, List.getElem_cons_zero]
      simpa only [hlastidx] using congrArg UScalar.val hlast

theorem accepted_cut (b : Slice Std.U8) (p : Nat)
    (hpos : 0 < b.length) (h : Spec.Accepted .ansiX923 (Proof.bytes b) p) :
    AnsiCut b p := by
  have hl : b.length-1 < b.val.length := by change b.length-1 < b.length; omega
  let n : Std.U8 := b.val[b.length-1]'hl
  simp only [Spec.Accepted, Proof.bytes, List.length_map] at h
  rcases h with ⟨count, hcpos, hcle, hcmax, hp, htail⟩
  simp only [Slice.length] at *
  have hsum : p+(b.length-1-p) = b.length-1 := by change p+(b.val.length-1-p)=b.val.length-1; omega
  have hcount : n.val = count := by
    have he := congrArg (fun xs : List Nat => xs[b.length-1-p]?) htail
    simp only [List.getElem?_drop, hsum, List.getElem?_map,
      List.getElem?_eq_getElem hl, Option.map_some] at he
    have hidx : b.length-1-p = count-1 := by change b.val.length-1-p=count-1; omega
    simpa [hidx, List.getElem?_append] using he
  refine ⟨n, by omega, by simp only [Slice.length]; omega, by simp only [Slice.length]; omega, hl, rfl, ?_⟩
  intro j hjs hje hj
  have hidx : j-p < count-1 := by omega
  have hsum : p+(j-p)=j := by omega
  have he := congrArg (fun xs : List Nat => xs[j-p]?) htail
  simp only [List.getElem?_drop, hsum, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some] at he
  have hv : b.val[j].val = 0 := by
    simpa [List.getElem?_append, List.getElem?_replicate, hidx] using he
  apply UScalar.eq_of_val_eq
  exact hv

theorem ansi_unpad_spec (b : Slice Std.U8)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad b
      ⦃ r => match r with
        | .Ok out => ∃ p, Proof.bytes out = (Proof.bytes b).take p ∧
            Spec.Accepted .ansiX923 (Proof.bytes b) p
        | .Err _ => Spec.Rejected .ansiX923 (Proof.bytes b) ⦄ := by
  apply spec_mono (ansi_unpad_cut b hpos hb)
  intro r hr
  cases r with
  | Ok out =>
    rcases hr with ⟨p, hout, hcut⟩
    refine ⟨p, ?_, cut_accepted b p hcut⟩
    simp [Proof.bytes, hout, List.map_take]
  | Err e =>
    rintro ⟨p, hp⟩
    exact hr ⟨p, accepted_cut b p hpos hp⟩

theorem ansi_unpad_total (b : Slice Std.U8)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    ∃ r, AnsiX923.Insts.Block_padding_verification_apiPadding.raw_unpad b = .ok r ∧
      match r with
      | .Ok out => ∃ p, Proof.bytes out = (Proof.bytes b).take p ∧
          Spec.Accepted .ansiX923 (Proof.bytes b) p
      | .Err _ => Spec.Rejected .ansiX923 (Proof.bytes b) :=
  Proof.spec_result_ok (ansi_unpad_spec b hpos hb)
end BlockPadding.AnsiUnpadProof
