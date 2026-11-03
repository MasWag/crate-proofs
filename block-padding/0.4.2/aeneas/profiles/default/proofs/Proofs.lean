import BlockPaddingVerificationApi
import BlockPadding.Specs
open Aeneas Aeneas.Std Aeneas.Std.WP Result
open block_padding_verification_api
namespace BlockPadding.Proof
set_option maxHeartbeats 2000000

def bytes (s : Slice Std.U8) := s.val.map UScalar.val

theorem spec_result_ok {α : Type _} {m : Result α} {post : α → Prop}
    (h : WP.spec m post) : ∃ value, m = Result.ok value ∧ post value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, (WP.spec_ok value).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem no_pad (b : Slice Std.U8) (p : Std.Usize) (h : p.val ≤ b.length) :
    ∃ out, NoPadding.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .none (bytes b) p.val := by
  refine ⟨b, ?_, rfl⟩
  simp [NoPadding.Insts.Block_padding_verification_apiPadding.raw_pad, Slice.len,
    massert, UScalar.lt_equiv, UScalar.le_equiv, h]

theorem no_unpad (b : Slice Std.U8) :
    ∃ out, NoPadding.Insts.Block_padding_verification_apiPadding.raw_unpad b =
      .ok (.Ok out) ∧ bytes out = (bytes b).take (bytes b).length ∧
      Spec.Accepted .none (bytes b) (bytes b).length := by
  exact ⟨b, rfl, by simp, rfl⟩

theorem zero_pad (b : Slice Std.U8) (p : Std.Usize) (h : p.val ≤ b.length) :
    ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_pad b p
      ⦃ out => bytes out = Spec.Padded .zero (bytes b) p.val ⦄ := by
  unfold ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_pad
  step
  step as ⟨s, back, hs, hlen, hb⟩
  step as ⟨s', hlen', hs'⟩
  all_goals simp [bytes, Spec.Padded, hb, hs', hlen, List.setSlice!] <;> omega
theorem pkcs_pad (b : Slice Std.U8) (p : Std.Usize)
    (h : p.val < b.length) (hb : b.length ≤ 255) :
    Pkcs7.Insts.Block_padding_verification_apiPadding.raw_pad b p
      ⦃ out => bytes out = Spec.Padded .pkcs7 (bytes b) p.val ⦄ := by
  unfold Pkcs7.Insts.Block_padding_verification_apiPadding.raw_pad
  step
  step
  step as ⟨d, hd⟩
  step as ⟨n, hn⟩
  step as ⟨s, back, hs, hlen, hback⟩
  step as ⟨s', hlen', hs'⟩
  all_goals simp [bytes, Spec.Padded, hback, hs', hlen, List.setSlice!, hn, hd]
  all_goals
    have hsmall : b.val.length - p.val < 256 := by change b.length - p.val < 256; omega
    have hdrop : p.val + (b.val.length - p.val) ≥ (b.val.map UScalar.val).length := by simp; change b.length ≤ p.val + (b.length - p.val); omega
    simp [Nat.mod_eq_of_lt hsmall, List.drop_eq_nil_iff.mpr hdrop]

theorem iso10126_pad (b : Slice Std.U8) (p : Std.Usize)
    (h : p.val < b.length) (hb : b.length ≤ 255) :
    Iso10126.Insts.Block_padding_verification_apiPadding.raw_pad b p
      ⦃ out => bytes out = Spec.Padded .iso10126 (bytes b) p.val ⦄ := by
  exact pkcs_pad b p h hb
theorem ansi_pad (b : Slice Std.U8) (p : Std.Usize)
    (h : p.val < b.length) (hb : b.length ≤ 255) :
    AnsiX923.Insts.Block_padding_verification_apiPadding.raw_pad b p
      ⦃ out => bytes out = Spec.Padded .ansiX923 (bytes b) p.val ⦄ := by
  unfold AnsiX923.Insts.Block_padding_verification_apiPadding.raw_pad
  step
  step
  step as ⟨last, hlast⟩
  step as ⟨s, back, hs, hlen, hback⟩
  step as ⟨s', hlen', hs'⟩
  step as ⟨d, hd⟩
  step as ⟨n, hn⟩
  step as ⟨out, hout⟩
  have hmin : min (b.val.length - 1 - p.val) (b.val.length - p.val) = b.val.length - p.val - 1 := by omega
  have hp : min p.val b.val.length = p.val := by change min p.val b.length = p.val; omega
  have hsum : p.val + (b.val.length - p.val - 1) = b.val.length - 1 := by change p.val + (b.length - p.val - 1) = b.length - 1; omega
  have hsmall : b.val.length - p.val < 256 := by change b.length - p.val < 256; omega
  simp [bytes, Spec.Padded, hout, hback, Slice.set, Slice.setAtNat, Slice.setSlice!, hs', hlen, hlast, hn, hd, List.setSlice!, hmin, hp, List.set_append, hsum, Nat.mod_eq_of_lt hsmall]
  have hdiff : b.val.length - 1 - p.val = b.val.length - p.val - 1 := by omega
  have hnot : ¬ b.val.length - 1 < p.val := by change ¬b.length-1 < p.val; omega
  have htail : ∃ x, b.val.drop (b.val.length - 1) = [x] := by
    have hlenTail : (b.val.drop (b.val.length - 1)).length = 1 := by simp; change b.length-(b.length-1)=1; omega
    cases he : b.val.drop (b.val.length - 1) with
    | nil => simp [he] at hlenTail
    | cons x xs =>
      cases xs with
      | nil => exact ⟨x, rfl⟩
      | cons y ys => simp [he] at hlenTail
  rcases htail with ⟨x, hx⟩
  simp [hdiff, hnot, hx, hd, Nat.mod_eq_of_lt hsmall]
theorem iso7816_pad (b : Slice Std.U8) (p : Std.Usize)
    (h : p.val < b.length) :
    Iso7816.Insts.Block_padding_verification_apiPadding.raw_pad b p
      ⦃ out => bytes out = Spec.Padded .iso7816 (bytes b) p.val ⦄ := by
  unfold Iso7816.Insts.Block_padding_verification_apiPadding.raw_pad
  step
  step as ⟨b', hb'⟩
  step as ⟨next, hn⟩
  step as ⟨s, back, hs, hlen, hback⟩
  step as ⟨s', hlen', hs'⟩
  have htake : (b.val.set p.val (128#u8)).take (p.val+1) = b.val.take p.val ++ [128#u8] := by
    rw [List.take_succ_eq_append_getElem (by simpa using h)]
    simp only [List.take_set, List.getElem_set_self, List.append_cancel_right_eq]
    exact List.set_eq_of_length_le (by simp)
  simp [bytes, Spec.Padded, hback, hs', hlen, hn, hb', Slice.set, Slice.setAtNat, List.setSlice!, htake]
  have hdrop : (p.val+1) + (b.val.length-(p.val+1)) ≥ ((b.val.map UScalar.val).set p.val 128).length := by
    simp; change b.length ≤ p.val+1+(b.length-(p.val+1)); omega
  simp [List.drop_eq_nil_iff.mpr hdrop, Nat.sub_sub]
theorem zero_pad_total (b : Slice Std.U8) (p : Std.Usize) (h : p.val ≤ b.length) :
    ∃ out, ZeroPadding.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .zero (bytes b) p.val :=
  spec_result_ok (zero_pad b p h)

theorem pkcs_pad_total (b : Slice Std.U8) (p : Std.Usize) (h : p.val < b.length) (hb : b.length ≤ 255) :
    ∃ out, Pkcs7.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .pkcs7 (bytes b) p.val :=
  spec_result_ok (pkcs_pad b p h hb)

theorem iso10126_pad_total (b : Slice Std.U8) (p : Std.Usize) (h : p.val < b.length) (hb : b.length ≤ 255) :
    ∃ out, Iso10126.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .iso10126 (bytes b) p.val :=
  spec_result_ok (iso10126_pad b p h hb)

theorem ansi_pad_total (b : Slice Std.U8) (p : Std.Usize) (h : p.val < b.length) (hb : b.length ≤ 255) :
    ∃ out, AnsiX923.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .ansiX923 (bytes b) p.val :=
  spec_result_ok (ansi_pad b p h hb)

theorem iso7816_pad_total (b : Slice Std.U8) (p : Std.Usize) (h : p.val < b.length) :
    ∃ out, Iso7816.Insts.Block_padding_verification_apiPadding.raw_pad b p = .ok out ∧
      bytes out = Spec.Padded .iso7816 (bytes b) p.val :=
  spec_result_ok (iso7816_pad b p h)

end BlockPadding.Proof
