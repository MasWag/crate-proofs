import Specs
namespace FxHash.Spec

theorem words_cons_block (e : Endian) (k : Nat) (ks : List Nat) (bs : List Nat)
    (hk : 0 < k) (hlen : k ≤ bs.length) :
    words e k ks bs = decode e (bs.take k) :: words e k ks (bs.drop k) := by
  have hq : bs.length / k = (bs.drop k).length / k + 1 := by
    rw [List.length_drop]
    exact Nat.div_eq_sub_div hk hlen
  have hd : ∀ i, bs.drop (i.succ * k) = (bs.drop k).drop (i * k) := by
    intro i
    rw [List.drop_drop]
    congr 1
    simp [Nat.succ_mul, Nat.add_comm]
  unfold words
  rw [hq, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero, List.cons_append]
  congr 1
  · congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply]
      rw [hd]
    · congr 1
      rw [List.drop_drop]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

theorem words32_little_short (bs : List Nat) (hlen : bs.length < 4) :
    words32 .little bs = bs := by
  cases bs with
  | nil => rfl
  | cons a bs =>
    cases bs with
    | nil => simp [words32, words, tailWords, decode, decodeLittle]
    | cons b bs =>
      cases bs with
      | nil => simp [words32, words, tailWords, decode, decodeLittle]
      | cons c bs =>
        cases bs with
        | nil => simp [words32, words, tailWords, decode, decodeLittle]
        | cons d bs => simp at hlen; omega

theorem words64_little_short (bs : List Nat) (hlen : bs.length < 8) :
    words64 .little bs =
      if 4 ≤ bs.length then decodeLittle (bs.take 4) :: bs.drop 4 else bs := by
  cases bs with
  | nil => simp [words64, words, tailWords, decode, decodeLittle]
  | cons a bs =>
    cases bs with
    | nil => simp [words64, words, tailWords, decode, decodeLittle]
    | cons a bs =>
      cases bs with
      | nil => simp [words64, words, tailWords, decode, decodeLittle]
      | cons a bs =>
        cases bs with
        | nil => simp [words64, words, tailWords, decode, decodeLittle]
        | cons a bs =>
          cases bs with
          | nil => simp [words64, words, tailWords, decode, decodeLittle]
          | cons a bs =>
            cases bs with
            | nil => simp [words64, words, tailWords, decode, decodeLittle]
            | cons a bs =>
              cases bs with
              | nil => simp [words64, words, tailWords, decode, decodeLittle]
              | cons a bs =>
                cases bs with
                | nil => simp [words64, words, tailWords, decode, decodeLittle]
                | cons a bs =>
                  cases bs with
                  | nil => simp at hlen
                  | cons a bs => simp at hlen; omega

theorem words32_little_cons_block (bs : List Nat) (hlen : 4 ≤ bs.length) :
    words32 .little bs = decodeLittle (bs.take 4) :: words32 .little (bs.drop 4) := by
  exact words_cons_block .little 4 [1, 1, 1] bs (by decide) hlen

theorem words64_little_cons_block (bs : List Nat) (hlen : 8 ≤ bs.length) :
    words64 .little bs = decodeLittle (bs.take 8) :: words64 .little (bs.drop 8) := by
  exact words_cons_block .little 8 [4, 1, 1, 1] bs (by decide) hlen

theorem write32_little_cons_block (h : BitVec 32) (bs : List Nat)
    (hlen : 4 ≤ bs.length) :
    write32 .little h bs =
      write32 .little (mix32 h (BitVec.ofNat 32 (decodeLittle (bs.take 4)))) (bs.drop 4) := by
  simp [write32, words32_little_cons_block bs hlen]

theorem write64_little_cons_block (h : BitVec 64) (bs : List Nat)
    (hlen : 8 ≤ bs.length) :
    write64 .little h bs =
      write64 .little (mix64 h (BitVec.ofNat 64 (decodeLittle (bs.take 8)))) (bs.drop 8) := by
  simp [write64, words64_little_cons_block bs hlen]

theorem write32_little_short (h : BitVec 32) (bs : List Nat)
    (hlen : bs.length < 4) :
    write32 .little h bs = bs.foldl (fun s x => mix32 s (BitVec.ofNat 32 x)) h := by
  simp [write32, words32_little_short bs hlen]

theorem write64_little_short (h : BitVec 64) (bs : List Nat)
    (hlen : bs.length < 8) :
    write64 .little h bs =
      if 4 ≤ bs.length then
        (bs.drop 4).foldl (fun s x => mix64 s (BitVec.ofNat 64 x))
          (mix64 h (BitVec.ofNat 64 (decodeLittle (bs.take 4))))
      else bs.foldl (fun s x => mix64 s (BitVec.ofNat 64 x)) h := by
  rw [write64, words64_little_short bs hlen]
  by_cases h4 : 4 ≤ bs.length <;> simp [h4]

theorem take_four_eq_getElems {α : Type} (bs : List α) (hlen : 4 ≤ bs.length) :
    bs.take 4 = [bs[0], bs[1], bs[2], bs[3]] := by
  cases bs with
  | nil => simp at hlen
  | cons a bs =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      cases bs with
      | nil => simp at hlen
      | cons c bs =>
        cases bs with
        | nil => simp at hlen
        | cons d bs => simp



theorem take_eight_eq_getElems {α : Type} (bs : List α) (hlen : 8 ≤ bs.length) :
    bs.take 8 = [bs[0], bs[1], bs[2], bs[3], bs[4], bs[5], bs[6], bs[7]] := by
  cases bs with
  | nil => simp at hlen
  | cons a bs =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      cases bs with
      | nil => simp at hlen
      | cons c bs =>
        cases bs with
        | nil => simp at hlen
        | cons d bs =>
          cases bs with
          | nil => simp at hlen
          | cons e bs =>
            cases bs with
            | nil => simp at hlen
            | cons f bs =>
              cases bs with
              | nil => simp at hlen
              | cons g bs =>
                cases bs with
                | nil => simp at hlen
                | cons h bs => simp

end FxHash.Spec
