import Proofs
open Aeneas Aeneas.Std Aeneas.Std.WP Result
open block_padding_verification_api
namespace BlockPadding.CountUnpadProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def Uniform (b : Slice Std.U8) (n : Std.U8) (s e : Nat) : Prop :=
  ∀ j, s ≤ j → j < e → (hj : j < b.length) → b.val[j] = n

theorem pkcs_loop (b : Slice Std.U8) (bs : Std.Usize) (n : Std.U8)
    (s i : Std.Usize) (hbs : bs.val = b.length) (hpos : 0 < bs.val)
    (hsi : s.val ≤ i.val) (hib : i.val ≤ bs.val-1)
    (hprefix : Uniform b n s.val i.val) :
    Pkcs7.unpad_loop b bs n s i
      ⦃ r => match r with
        | .Ok out => out.val = b.val.take s.val ∧ Uniform b n s.val (bs.val-1)
        | .Err _ => ¬Uniform b n s.val (bs.val-1) ⦄ := by
  unfold Pkcs7.unpad_loop
  apply loop.spec_decr_nat (fun i : Std.Usize => bs.val-1-i.val)
    (fun i => s.val ≤ i.val ∧ i.val ≤ bs.val-1 ∧ Uniform b n s.val i.val)
  · intro i ⟨hsi, hib, hprefix⟩
    unfold Pkcs7.unpad_loop.body
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
def CountCut (b : Slice Std.U8) (strict : Bool) (p : Nat) : Prop :=
  ∃ (n : Std.U8), 0 < n.val ∧ n.val ≤ b.length ∧ p = b.length-n.val ∧
    ∃ (hl : b.length-1 < b.length), b.val[b.length-1] = n ∧
      (strict = true → Uniform b n p (b.length-1))

theorem pkcs_unpad_cut (b : Slice Std.U8) (strict : Bool)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    Pkcs7.unpad b strict ⦃ r => match r with
      | .Ok out => ∃ p, out.val = b.val.take p ∧ CountCut b strict p
      | .Err _ => ¬∃ p, CountCut b strict p ⦄ := by
  unfold Pkcs7.unpad
  step
  step as ⟨last, hlast⟩
  step as ⟨n, hn⟩
  have hlastBound : b.length-1 < b.val.length := by change b.length-1 < b.length; omega
  have hlastN : b.val[b.length-1]'hlastBound = n := by simpa [hlast] using hn.symm
  split
  · rename_i hzero
    simp only [spec_ok]
    rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hstrict⟩
    have he : nc = n := hlastn.symm.trans hlastN
    have hz : n = 0#u8 := by simpa using hzero
    rw [he, hz] at hnc
    norm_num at hnc
  · rename_i hnzero
    step as ⟨count, hcount⟩
    have hc : count.val = n.val := by rw [hcount]; simp
    split
    · rename_i hbig
      simp only [spec_ok]
      rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hstrict⟩
      have he : nc = n := hlastn.symm.trans hlastN
      rw [he] at hnb
      simp only [UScalar.lt_equiv, Slice.len_val] at hbig
      omega
    · rename_i hsmall
      simp only [UScalar.lt_equiv, Slice.len_val] at hsmall
      have hnle : n.val ≤ b.length := by omega
      step as ⟨count2, hcount2⟩
      have hc2 : count2.val = n.val := by rw [hcount2]; simp
      step as ⟨s, hs⟩
      simp only [Slice.len_val] at hs
      have hsval : s.val = b.length - n.val := by omega
      split
      · rename_i htrue
        step with pkcs_loop as ⟨r, hr⟩
        · intro j hjs hje hj; omega
        · cases r with
          | Ok out =>
            rcases hr with ⟨hout, hall⟩
            refine ⟨s.val, hout, n, ?_, ?_, ?_, by omega, ?_, ?_⟩
            · have hne : n.val ≠ 0 := by simpa using hnzero
              omega
            · omega
            · omega
            · simpa [hlast] using hn.symm
            · intro _; simpa using hall
          | Err e =>
            rintro ⟨p, nc, hnc, hnb, hp, hl, hlastn, hstrict⟩
            have he : nc = n := hlastn.symm.trans hlastN
            rw [he] at hstrict hp
            apply hr
            have hpEq : p = s.val := by omega
            subst p
            simpa only [Slice.len_val, hsval] using hstrict htrue
      · rename_i hfalse
        step as ⟨out, hout, hlen⟩
        refine ⟨s.val, by simpa [List.slice] using hout, n, ?_, ?_, ?_, by omega, ?_, ?_⟩
        · have hne : n.val ≠ 0 := by simpa using hnzero
          omega
        · omega
        · omega
        · simpa [hlast] using hn.symm
        · intro ht; contradiction
theorem cut_accepted (b : Slice Std.U8) (strict : Bool) (p : Nat)
    (h : CountCut b strict p) :
    Spec.Accepted (if strict then .pkcs7 else .iso10126) (Proof.bytes b) p := by
  rcases h with ⟨n, hnpos, hnle, hp, hl, hlast, hall⟩
  have hnmax : n.val ≤ 255 := by scalar_tac
  cases strict with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Spec.Accepted, Proof.bytes, List.length_map]
    refine ⟨n.val, (Proof.bytes b).take (b.length-1), hnpos, hnle, hnmax, hp, ?_⟩
    have he : b.val.take (b.length-1) ++ [n] = b.val := by
      rw [← hlast, ← List.take_succ_eq_append_getElem (by simpa using hl)]
      have hlen : b.length-1+1 = b.length := by omega
      simp [hlen]
    simpa [Proof.bytes, List.map_append] using congrArg (List.map UScalar.val) he.symm
  | true =>
    simp only [↓reduceIte, Spec.Accepted, Proof.bytes, List.length_map]
    refine ⟨n.val, hnpos, hnle, hnmax, hp, ?_⟩
    apply List.ext_getElem
    · simp; change b.length-p=n.val; omega
    · intro j hj hk
      simp only [List.getElem_drop, List.getElem_map, List.getElem_replicate]
      have hidx : p+j < b.length := by simp only [List.length_drop, List.length_map] at hj; change p+j < b.val.length; omega
      by_cases hlastidx : p+j = b.length-1
      · simpa [hlastidx] using congrArg UScalar.val hlast
      · exact congrArg UScalar.val (hall rfl (p+j) (by omega) (by omega) hidx)
theorem accepted_cut (b : Slice Std.U8) (strict : Bool) (p : Nat)
    (hpos : 0 < b.length)
    (h : Spec.Accepted (if strict then .pkcs7 else .iso10126) (Proof.bytes b) p) :
    CountCut b strict p := by
  have hl : b.length-1 < b.val.length := by change b.length-1 < b.length; omega
  let n : Std.U8 := b.val[b.length-1]'hl
  cases strict with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Spec.Accepted, Proof.bytes, List.length_map] at h
    rcases h with ⟨count, head, hcpos, hcle, hcmax, hp, hbytes⟩
    simp only [Slice.length] at *
    have hhead : head.length = b.length-1 := by
      have he := congrArg List.length hbytes
      simp at he
      change head.length = b.val.length-1
      omega
    have hcount : n.val = count := by
      have he := congrArg (fun xs : List Nat => xs[b.length-1]?) hbytes
      simp only [List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some] at he
      simp [List.getElem?_append, hhead] at he
      exact he
    refine ⟨n, by omega, by simp only [Slice.length]; omega, by simp only [Slice.length]; omega, hl, rfl, ?_⟩
    intro ht; contradiction
  | true =>
    simp only [↓reduceIte, Spec.Accepted, Proof.bytes, List.length_map] at h
    rcases h with ⟨count, hcpos, hcle, hcmax, hp, htail⟩
    simp only [Slice.length] at *
    have hidx : b.length-1-p < count := by change b.val.length-1-p < count; omega
    have hsum : p+(b.length-1-p) = b.length-1 := by change p+(b.val.length-1-p)=b.val.length-1; omega
    have hcount : n.val = count := by
      have he := congrArg (fun xs : List Nat => xs[b.length-1-p]?) htail
      simp only [List.getElem?_drop, hsum, List.getElem?_map,
        List.getElem?_eq_getElem hl, Option.map_some] at he
      simpa [List.getElem?_replicate, hidx] using he
    refine ⟨n, by omega, by simp only [Slice.length]; omega, by simp only [Slice.length]; omega, hl, rfl, ?_⟩
    intro _ j hjs hje hj
    have hidx : j-p < count := by omega
    have hsum : p+(j-p)=j := by omega
    have he := congrArg (fun xs : List Nat => xs[j-p]?) htail
    simp only [List.getElem?_drop, hsum, List.getElem?_map,
      List.getElem?_eq_getElem hj, Option.map_some] at he
    have hv : b.val[j].val = count := by simpa [List.getElem?_replicate, hidx] using he
    apply UScalar.eq_of_val_eq
    omega
theorem pkcs_unpad_spec (b : Slice Std.U8) (strict : Bool)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    Pkcs7.unpad b strict ⦃ r => match r with
      | .Ok out => ∃ p, Proof.bytes out = (Proof.bytes b).take p ∧
          Spec.Accepted (if strict then .pkcs7 else .iso10126) (Proof.bytes b) p
      | .Err _ => Spec.Rejected (if strict then .pkcs7 else .iso10126) (Proof.bytes b) ⦄ := by
  apply spec_mono (pkcs_unpad_cut b strict hpos hb)
  intro r hr
  cases r with
  | Ok out =>
    rcases hr with ⟨p, hout, hcut⟩
    refine ⟨p, ?_, cut_accepted b strict p hcut⟩
    simp [Proof.bytes, hout, List.map_take]
  | Err e =>
    rintro ⟨p, hp⟩
    exact hr ⟨p, accepted_cut b strict p hpos hp⟩

theorem pkcs_unpad_total (b : Slice Std.U8)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    ∃ r, Pkcs7.Insts.Block_padding_verification_apiPadding.raw_unpad b = .ok r ∧
      match r with
      | .Ok out => ∃ p, Proof.bytes out = (Proof.bytes b).take p ∧
          Spec.Accepted .pkcs7 (Proof.bytes b) p
      | .Err _ => Spec.Rejected .pkcs7 (Proof.bytes b) :=
  Proof.spec_result_ok (pkcs_unpad_spec b true hpos hb)

theorem iso10126_unpad_total (b : Slice Std.U8)
    (hpos : 0 < b.length) (hb : b.length ≤ 255) :
    ∃ r, Iso10126.Insts.Block_padding_verification_apiPadding.raw_unpad b = .ok r ∧
      match r with
      | .Ok out => ∃ p, Proof.bytes out = (Proof.bytes b).take p ∧
          Spec.Accepted .iso10126 (Proof.bytes b) p
      | .Err _ => Spec.Rejected .iso10126 (Proof.bytes b) :=
  Proof.spec_result_ok (pkcs_unpad_spec b false hpos hb)
end BlockPadding.CountUnpadProof
