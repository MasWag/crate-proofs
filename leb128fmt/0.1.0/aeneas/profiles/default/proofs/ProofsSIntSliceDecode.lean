import SliceConcrete
import SignedDecodeMath

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open leb128fmt.signedMath

attribute [local step] IScalar.ShiftLeft_spec
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace leb128fmt_slice_probe

inductive SignedRead where
  | value (value : Int) (cursor : Nat)
  | needMore (cursor : Nat)
  | invalid (cursor : Nat)

def signedSliceByte (input : Slice U8) (i : Nat) : Nat :=
  (input.val[i]?.getD 0#u8).val

def signedSliceSum (sum byte index : Nat) : Int :=
  let raw := sum + byte % 128 * 128^index
  if 64 ≤ byte then (raw : Int) - (128^(index+1) : Nat) else raw

def effectiveSignedWidth (width : Nat) : Nat :=
  if width % 7 = 0 then width + 1 else width

abbrev signedFieldFits (width : Nat) (value : Int) : Prop :=
  -(2^(width-1) : Int) ≤ value ∧ value < 2^(width-1)

def signedReadDigits (input : Slice U8) (start width index sum : Nat) : Nat → SignedRead
  | 0 => .invalid start
  | fuel + 1 =>
    if input.val.length ≤ start + index then .needMore start
    else
      let byte := signedSliceByte input (start + index)
      if byte < 128 then
        let value := signedSliceSum sum byte index
        if signedFieldFits width value then .value value (start + index + 1) else .invalid start
      else signedReadDigits input start width (index+1)
        (sum + byte % 128 * 128^index) fuel

def signedSliceMeaning (input : Slice U8) (start width : Nat) : SignedRead :=
  signedReadDigits input start (effectiveSignedWidth width) 0 0 (width/7+1)

def observeSignedRead {ty : IScalarTy} :
    core.result.Result (IScalar ty) leb128fmt.Error × Usize → SignedRead
  | (.Ok value, pos) => .value value.val pos.val
  | (.Err .NeedMoreBytes, pos) => .needMore pos.val
  | (.Err .InvalidEncoding, pos) => .invalid pos.val

private theorem scalar_eq_of_val {ty : UScalarTy} {x y : UScalar ty} (h : x.val = y.val) : x = y := by
  cases x with
  | mk xv =>
    cases y with
    | mk yv => congr 1; exact BitVec.eq_of_toNat_eq h

private theorem ucast_bv {ty : IScalarTy} (h : 8 ≤ ty.numBits) (byte : U8) :
    (UScalar.hcast ty byte).bv.toNat = byte.val := by
  rw [UScalar.hcast_bv_eq, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le byte.bv.isLt (Nat.pow_le_pow_right (by decide) h))

private theorem continuation_iff (n : U8) : ((n &&& 128#u8) != 0#u8) = true ↔ ¬n.val < 128 := by
  have hbyte : n.val < 256 := by scalar_tac
  have hdiv := @Nat.and_div_two_pow n.val 128 7
  have hmod := @Nat.and_mod_two_pow n.val 128 7
  change (n.val &&& 128) / 128 = (n.val / 128) &&& 1 at hdiv
  change (n.val &&& 128) % 128 = (n.val % 128) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  simp
  omega

private theorem width_shift (w : Nat) : w - w % 7 = 7 * (w / 7) := by omega

private theorem signedReadDigits_outside (input : Slice U8) (start width index sum fuel : Nat)
    (hfuel : index ≤ fuel) (h : input.val.length ≤ start + index) :
    signedReadDigits input start width index sum (fuel + 1 - index) = .needMore start := by
  rw [show fuel + 1 - index = (fuel - index) + 1 by omega]
  simp [signedReadDigits, h]

private theorem signed_shifted_range {sum byte j field : Nat}
    (hsum : sum < 128^j) (hbyte : byte < 128) (hwidth : 7*j < field) :
    signedFieldFits field (signedSliceSum sum byte j) ↔
      byte < 2^(field-1-7*j) ∨ 128 - 2^(field-1-7*j) ≤ byte := by
  let radix := 128^j
  let bound := 2^(field-1-7*j)
  have hradix : (0 : Int) < radix := by dsimp [radix]; positivity
  have hbound : 0 < bound := by dsimp [bound]; positivity
  have hscale : (2^(field-1) : Int) = (bound : Int) * radix := by
    have he : field-1 = (field-1-7*j) + 7*j := by omega
    have hradix' : (radix : Int) = 2^(7*j) := by
      have h := congrArg Int.ofNat (pow_radix j).symm
      simpa [radix] using h
    have hbound' : (bound : Int) = 2^(field-1-7*j) := by
      simp [bound]
    rw [hradix', hbound', ← pow_add]
    exact congrArg (fun k => (2 : Int)^k) he
  have hfactor (x : Int) :
      -(bound : Int) * radix ≤ (sum : Int) + x*radix ∧
        (sum : Int) + x*radix < (bound : Int)*radix ↔
        -(bound : Int) ≤ x ∧ x < bound := by
    have hsI : (sum : Int) < (radix : Int) := by exact_mod_cast hsum
    constructor
    · rintro ⟨hlow, hhigh⟩
      constructor
      · by_contra! hbad
        have h := mul_le_mul_of_nonneg_right (show x + 1 ≤ -(bound : Int) by omega) (le_of_lt hradix)
        nlinarith
      · by_contra! hbad
        have h := mul_le_mul_of_nonneg_right hbad (le_of_lt hradix)
        nlinarith
    · rintro ⟨hlow, hhigh⟩
      have hl := mul_le_mul_of_nonneg_right hlow (le_of_lt hradix)
      have hh := mul_le_mul_of_nonneg_right (show x + 1 ≤ (bound : Int) by omega) (le_of_lt hradix)
      constructor <;> nlinarith
  simp only [signedFieldFits, signedSliceSum, Nat.mod_eq_of_lt hbyte, hscale, ← neg_mul]
  by_cases hnegative : 64 ≤ byte
  · rw [ite_eq_left hnegative]
    rw [show (↑(sum + byte * 128^j) : Int) - (↑(128^(j+1) : Nat) : Int) =
        (sum : Int) + (byte - 128 : Int)*radix by
      simp [radix, pow_succ]
      ring]
    rw [hfactor]
    change _ ↔ byte < bound ∨ 128-bound ≤ byte
    omega
  · rw [ite_eq_right hnegative]
    rw [show (↑(sum + byte * 128^j) : Int) = (sum : Int) + (byte : Int)*radix by
      simp [radix]]
    rw [hfactor]
    change _ ↔ byte < bound ∨ 128-bound ≤ byte
    omega

private theorem sign_flag_iff (n : U8) (hn : n.val < 128) :
    ((n &&& 64#u8) != 0#u8) = true ↔ 64 ≤ n.val := by
  have hdiv := @Nat.and_div_two_pow n.val 64 6
  have hmod := @Nat.and_mod_two_pow n.val 64 6
  change (n.val &&& 64) / 64 = (n.val / 64) &&& 1 at hdiv
  change (n.val &&& 64) % 64 = (n.val % 64) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  simp
  omega

private theorem append_bits {ty : IScalarTy} (hN : 8 ≤ ty.numBits)
    (acc part : IScalar ty) (n : U8) (j : Nat)
    (hacc : acc.bv.toNat < 128^j)
    (hpart : part.bv = (UScalar.hcast ty (n &&& 127#u8)).bv <<< (7*j)) :
    (acc ||| part).bv = BitVec.ofNat ty.numBits
      (acc.bv.toNat + n.val % 128 * 128^j) := by
  rw [IScalar.bv_or, hpart, bv_or_chunk _ _ (by rwa [pow_radix]), pow_radix,
    ucast_bv hN, UScalar.val_and]
  have hmask : n.val &&& (127#u8).val = n.val % 128 := Nat.and_two_pow_sub_one_eq_mod n.val 7
  rw [hmask]

private theorem append_small {ty : IScalarTy}
    (acc part : IScalar ty) (n : U8) (j : Nat)
    (hacc : acc.bv.toNat < 128^j) (hshort : 7*(j+1) ≤ ty.numBits)
    (hpart : (acc ||| part).bv = BitVec.ofNat ty.numBits
      (acc.bv.toNat + n.val % 128 * 128^j)) :
    (acc ||| part).bv.toNat = acc.bv.toNat + n.val % 128 * 128^j := by
  rw [hpart, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  apply lt_of_lt_of_le (decode_append hacc (Nat.mod_lt _ (by decide)))
  rw [← pow_radix]
  exact Nat.pow_le_pow_right (by decide) hshort

private theorem terminal_value {ty : IScalarTy} (hN : 8 ≤ ty.numBits)
    (x : IScalar ty) (value : Int) (hfield : field ≤ ty.numBits)
    (hrange : signedFieldFits field value)
    (hx : x.bv = BitVec.ofInt ty.numBits value) :
    x.val = value := by
  rw [IScalar.val, hx]
  have hle : (2^(field-1) : Int) ≤ 2^(ty.numBits-1) := by gcongr; omega
  exact BitVec.toInt_ofInt_eq_self (by omega) (by omega) (by omega)

private theorem extend_terminal {ty : IScalarTy} (acc part extension : IScalar ty) (n : U8)
    (j : Nat) (hraw : (acc ||| part).bv.toNat = acc.bv.toNat + n.val % 128 * 128^j)
    (hacc : acc.bv.toNat < 128^j) (hsign : 64 ≤ n.val)
    (hext : extension.bv = BitVec.allOnes ty.numBits <<< (7*(j+1))) :
    (acc ||| part ||| extension).bv = BitVec.ofInt ty.numBits (signedSliceSum acc.bv.toNat n.val j) := by
  rw [IScalar.bv_or, hext, bv_sign_extend _ (by
    rw [pow_radix, hraw]
    exact decode_append hacc (Nat.mod_lt _ (by decide))),
    pow_radix, hraw, signedSliceSum, ite_eq_left hsign]

private theorem unextended_terminal {ty : IScalarTy} (acc part : IScalar ty) (n : U8) (j : Nat)
    (hpart : (acc ||| part).bv = BitVec.ofNat ty.numBits
      (acc.bv.toNat + n.val % 128 * 128^j))
    (hnoextend : n.val < 64 ∨ ty.numBits ≤ 7*(j+1)) :
    (acc ||| part).bv = BitVec.ofInt ty.numBits (signedSliceSum acc.bv.toNat n.val j) := by
  rw [hpart, signedSliceSum]
  split
  · rename_i h
    apply bv_sign_wrap
    rcases hnoextend with h | h <;> omega
  · rfl

private theorem signedReadDigits_unroll (input : Slice U8) (start field j groups sum : Nat)
    (hj : j ≤ groups) (hbound : start+j < input.val.length) :
    signedReadDigits input start field j sum (groups+1-j) =
      if signedSliceByte input (start+j) < 128 then
        let value := signedSliceSum sum (signedSliceByte input (start+j)) j
        if signedFieldFits field value then .value value (start+j+1) else .invalid start
      else signedReadDigits input start field (j+1)
        (sum + signedSliceByte input (start+j) % 128 * 128^j) (groups+1-(j+1)) := by
  rw [show groups+1-j = (groups+1-(j+1))+1 by omega]
  simp [signedReadDigits, show ¬input.val.length ≤ start+j by omega]

private theorem maskValue (r : U32) (part : I8) (hr : r.val < 7)
    (hpart : part.bv = ((-1)#i8).bv <<< (core.num.U32.saturating_sub r 1#u32).val) :
    (IScalar.hcast .U8 (part &&& 127#i8)).val = 128 - 2^(r.val-1) := by
  have hcases : r = 0#u32 ∨ r = 1#u32 ∨ r = 2#u32 ∨ r = 3#u32 ∨
      r = 4#u32 ∨ r = 5#u32 ∨ r = 6#u32 := by
    have hr' : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨
        r.val = 4 ∨ r.val = 5 ∨ r.val = 6 := by omega
    rcases hr' with h | h | h | h | h | h | h
    · exact Or.inl (scalar_eq_of_val h)
    · exact Or.inr (Or.inl (scalar_eq_of_val h))
    · exact Or.inr (Or.inr (Or.inl (scalar_eq_of_val h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (scalar_eq_of_val h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (scalar_eq_of_val h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (scalar_eq_of_val h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (scalar_eq_of_val h))))))
  have hpart' : part = ⟨((-1)#i8).bv <<< (core.num.U32.saturating_sub r 1#u32).val⟩ := by
    cases part
    congr 1
  rw [hpart']
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem finalMaskZero (n mask : U8) (shift : Nat) (hn : n.val < 128)
    (hshift : shift ≤ 6) (hmask : mask.val = 128 - 2^shift) :
    (n &&& mask) = 0#u8 ↔ n.val < 2^shift := by
  let d := 2^shift
  let k := 7-shift
  have hd : 0 < d := by dsimp [d]; positivity
  have hprod : 2^k * d = 128 := by
    dsimp [d,k]
    rw [← pow_add, show 7-shift+shift = 7 by omega]
    rfl
  have hk : 0 < 2^k := by positivity
  have hmask' : mask.val = (2^k-1) * d := by
    rw [Nat.sub_mul, Nat.one_mul, hprod]
    exact hmask
  have hmdiv : mask.val / d = 2^k-1 := by rw [hmask', Nat.mul_div_cancel _ hd]
  have hmmod : mask.val % d = 0 := by rw [hmask', Nat.mul_mod_left]
  have hnsmall : n.val / d < 2^k := by
    rw [Nat.div_lt_iff_lt_mul hd, hprod]
    exact hn
  have hdiv := @Nat.and_div_two_pow n.val mask.val shift
  have hmod := @Nat.and_mod_two_pow n.val mask.val shift
  change (n.val &&& mask.val) / d = _ at hdiv
  change (n.val &&& mask.val) % d = _ at hmod
  rw [hmdiv, Nat.and_two_pow_sub_one_of_lt_two_pow hnsmall] at hdiv
  rw [hmmod, Nat.and_zero] at hmod
  constructor
  · intro h
    have he : n.val &&& mask.val = 0 := by simpa using congrArg UScalar.val h
    rw [he, Nat.zero_div] at hdiv
    exact (Nat.div_eq_zero_iff_lt hd).mp hdiv.symm
  · intro h
    apply scalar_eq_of_val
    change n.val &&& mask.val = 0
    have hi := Nat.mod_add_div (n.val &&& mask.val) d
    rw [hdiv, hmod, (Nat.div_eq_zero_iff_lt hd).mpr h, Nat.mul_zero, Nat.zero_add] at hi
    exact hi.symm

private theorem slice_loop {ty : IScalarTy} (hN : 8 ≤ ty.numBits)
    (hNmod : ty.numBits % 7 ≠ 0) (hNbound : ty.numBits ≤ 128)
    (width : U32) (hwidth : width.val ≤ ty.numBits)
    (shl : core.ops.bit.Shl (IScalar ty) U32 (IScalar ty))
    (bor : core.ops.bit.BitOrAssign (IScalar ty) (IScalar ty))
    (fi : core.convert.From (IScalar ty) I8) (fu : core.convert.From (IScalar ty) U8)
    (hshl : ∀ v s, shl.shl v s = (v <<< s))
    (hbor : ∀ v x, bor.bitor_assign v x = ok (v ||| x))
    (hfu : ∀ n, fu.«from» n = ok (UScalar.hcast ty n))
    (hfi : fi.«from» (-1)#i8 = ok ⟨BitVec.allOnes ty.numBits⟩)
    (nBits : U32) (hbits : nBits.val = ty.numBits)
    (input : Slice U8) (pos : Usize) (zero : IScalar ty) (hzero : zero.bv.toNat = 0) :
    WP.spec (leb128fmt.decode_sint_slice_loop width shl bor fi fu nBits input pos zero 0#u32 pos)
      (fun out => observeSignedRead out = signedSliceMeaning input pos.val width.val) := by
  let groups := width.val / 7
  let field := effectiveSignedWidth width.val
  have hmaxshift : 7 * groups < ty.numBits := by dsimp [groups]; omega
  have hfield : field ≤ ty.numBits := by
    simp only [field, effectiveSignedWidth]
    split <;> omega
  have hfieldlo : 7 * groups + 1 ≤ field := by
    simp only [field, groups, effectiveSignedWidth]
    split <;> omega
  unfold leb128fmt.decode_sint_slice_loop
  apply loop.spec_decr_nat (measure := fun state => groups + 1 - (state.2.2.val - pos.val))
    (inv := fun state =>
      ∃ j, state.2.2.val = pos.val + j ∧ state.2.1.val = 7*j ∧ j ≤ groups ∧
        state.1.bv.toNat < 128^j ∧
        signedReadDigits input pos.val field j state.1.bv.toNat (groups+1-j) =
          signedSliceMeaning input pos.val width.val)
  · rintro ⟨acc, shift, idx⟩ ⟨j, hidx, hshift, hj, hacc, hspec⟩
    dsimp at hidx hshift hacc hspec ⊢
    have hshiftrange : shift.val < ty.numBits := by omega
    unfold leb128fmt.decode_sint_slice_loop.body
    simp only [hshl, hbor, hfu, hfi]
    split
    · rename_i h
      rw [WP.spec_ok]
      have hout : input.val.length ≤ pos.val + j := by
        rw [← hidx]
        exact h
      rw [← hspec, signedReadDigits_outside _ _ _ _ _ _ hj hout]
      rfl
    · rename_i h
      have hbound : idx.val < input.val.length := Nat.lt_of_not_ge h
      have hposj : pos.val + j < input.val.length := by omega
      step*
      all_goals
        have hbyte : signedSliceByte input (pos.val+j) = n.val := by
          rw [n_post, ← hidx]
          simp [signedSliceByte, List.getElem?_eq_getElem hbound]
        have hflag : (i2 != 0#u8) = true ↔ ¬n.val < 128 := by
          rw [scalar_eq_of_val i2_post]
          exact continuation_iff n
        rw [signedReadDigits_unroll _ _ _ _ _ _ hj hposj, hbyte] at hspec
      · have hfinal : j = groups := by
          have he : shift = i4 := by assumption
          have he' := congrArg UScalar.val he
          dsimp [groups]
          omega
        have hfinalShift : i4.val = 7*j := by omega
        have hi5val : (core.num.U32.saturating_sub i3 1#u32).val = i3.val - 1 := by
          rw [core.num.U32.saturating_sub, UScalar.saturating_sub]
          change (i3.val-1) % 2^32 = _
          apply Nat.mod_eq_of_lt
          omega
        have hi5small : (core.num.U32.saturating_sub i3 1#u32).val < 8 := by omega
        have hfieldRem : field - 1 - 7*j = i3.val - 1 := by
          simp only [field, effectiveSignedWidth]
          split <;> omega
        simp only [lift]
        step*
        · have hmore : (i2 != 0#u8) = true := by assumption
          rw [← hspec, ite_eq_right (hflag.mp hmore), hfinal]
          simp [signedReadDigits, observeSignedRead]
        all_goals
          have hmore : ¬(i2 != 0#u8) = true := by assumption
          have hterminal : n.val < 128 := by
            by_contra! hh
            exact hmore (hflag.mpr (by omega))
          have hm := maskValue i3 i6 (by omega) i6_post1
          let mask := IScalar.hcast .U8 (i6 &&& 127#i8)
          have hmask := finalMaskZero n mask (i3.val-1) hterminal (by omega) hm
          have hfit := signed_shifted_range hacc hterminal (by omega : 7*j < field)
          rw [hfieldRem, ← hm] at hfit
        · have hband : (n &&& mask != 0#u8) = true := by assumption
          have hlt : n < mask := by assumption
          have hlow : ¬n.val < 2^(i3.val-1) := by
            intro hl
            have hz := hmask.mpr hl
            simp [hz] at hband
          have hbad : ¬signedFieldFits field (signedSliceSum acc.bv.toNat n.val j) :=
            fun hp => (hfit.mp hp).elim hlow (fun hge => (Nat.not_le_of_gt hlt) hge)
          simp [← hspec, hterminal, hbad, observeSignedRead]
        all_goals
          have hrange : signedFieldFits field (signedSliceSum acc.bv.toNat n.val j) := by
            apply hfit.mpr
            first
            | have hge : ¬n < mask := by assumption
              exact Or.inr (Nat.le_of_not_gt hge)
            | have hband : ¬(n &&& mask != 0#u8) = true := by assumption
              have hz : (n &&& mask) = 0#u8 := by apply scalar_eq_of_val; simpa using hband
              exact Or.inl (hmask.mp hz)
          have hpart := append_bits hN acc t1 n j hacc (by rw [t1_post1, hfinalShift])
          have hshiftNext : shift1.val = 7*(j+1) := by omega
          have hvalue :
              signedSliceMeaning input pos.val width.val =
                SignedRead.value (signedSliceSum acc.bv.toNat n.val j) (idx1.val) := by
            rw [← hspec]
            simp [hterminal, hrange, hidx, idx1_post]
          rw [hvalue]
          simp only [observeSignedRead, SignedRead.value.injEq, and_true]
          apply terminal_value hN _ _ hfield hrange
          first
          | have hsign : ((n &&& 64#u8) != 0#u8) = true := by assumption
            have hlt : shift1 < nBits := by assumption
            have hs : shift1.val < nBits.val := hlt
            have hraw := append_small acc t1 n j hacc (by omega) hpart
            exact extend_terminal acc t1 t3 n j hraw hacc ((sign_flag_iff n hterminal).mp hsign)
              (by rw [t3_post1, hshiftNext])
          | apply unextended_terminal acc t1 n j hpart
            first
            | have hnosign : ¬((n &&& 64#u8) != 0#u8) = true := by assumption
              exact Or.inl (Nat.lt_of_not_ge (fun hge => hnosign ((sign_flag_iff n hterminal).mpr hge)))
            | have hcut : ¬shift1 < nBits := by assumption
              have hs : ¬shift1.val < nBits.val := hcut
              exact Or.inr (by omega)
      all_goals
        have hnotFinal : j < groups := by
          have he : ¬shift = i4 := by assumption
          by_contra! hh
          exact he (scalar_eq_of_val (by dsimp [groups] at *; omega))
        have hshiftNext : shift1.val = 7*(j+1) := by omega
        have hpart := append_bits hN acc t1 n j hacc (by
          have hdigit : i9 = (n &&& 127#u8) := scalar_eq_of_val i9_post
          rw [t1_post1, hdigit, hshift])
        have hraw := append_small acc t1 n j hacc (by omega) hpart
      · have hmore : (i2 != 0#u8) = true := by assumption
        rw [ite_eq_right (hflag.mp hmore)] at hspec
        refine ⟨⟨j+1, by omega, hshiftNext, by omega, ?_, ?_⟩, by omega⟩
        · rw [hraw]
          exact decode_append hacc (Nat.mod_lt _ (by decide))
        · simpa only [hraw] using hspec
      all_goals
        have hmore : ¬(i2 != 0#u8) = true := by assumption
        have hterminal : n.val < 128 := by
          by_contra! hh
          exact hmore (hflag.mpr (by omega))
        have hrange : signedFieldFits field (signedSliceSum acc.bv.toNat n.val j) := by
          apply (signed_shifted_range hacc hterminal (by omega)).mpr
          have hlarge : (64 : Nat) ≤ 2^(field-1-7*j) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 6 ≤ field-1-7*j)
          omega
        have hvalue :
            signedSliceMeaning input pos.val width.val =
              SignedRead.value (signedSliceSum acc.bv.toNat n.val j) (idx1.val) := by
          rw [← hspec]
          simp [hterminal, hrange, hidx, idx1_post]
        rw [hvalue]
        simp only [observeSignedRead, SignedRead.value.injEq, and_true]
        apply terminal_value hN _ _ hfield hrange
        first
        | have hsign : ((n &&& 64#u8) != 0#u8) = true := by
            have hsign : (i10 != 0#u8) = true := by assumption
            have he : i10 = n &&& 64#u8 := scalar_eq_of_val i10_post
            rw [← he]
            exact hsign
          exact extend_terminal acc t1 _ n j hraw hacc ((sign_flag_iff n hterminal).mp hsign)
            (by rw [t3_post1, hshiftNext])
        | apply unextended_terminal acc t1 n j hpart
          have hnosign : ¬((n &&& 64#u8) != 0#u8) = true := by
            have hsign : ¬(i10 != 0#u8) = true := by assumption
            have he : i10 = n &&& 64#u8 := scalar_eq_of_val i10_post
            rw [← he]
            exact hsign
          exact Or.inl (Nat.lt_of_not_ge (fun hge => hnosign ((sign_flag_iff n hterminal).mpr hge)))
  · exact ⟨0, by simp, by simp, by omega, by simp [hzero], by simp [hzero, groups, field, signedSliceMeaning]⟩

private theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

private theorem signed_decoder {ty : IScalarTy}
    (hN : 8 ≤ ty.numBits) (hNmod : ty.numBits % 7 ≠ 0) (hNbound : ty.numBits ≤ 128)
    (width : U32) (hwidth : width.val ≤ ty.numBits)
    (shl : core.ops.bit.Shl (IScalar ty) U32 (IScalar ty))
    (bor : core.ops.bit.BitOrAssign (IScalar ty) (IScalar ty))
    (fi : core.convert.From (IScalar ty) I8) (fu : core.convert.From (IScalar ty) U8)
    (hshl : ∀ v s, shl.shl v s = (v <<< s))
    (hbor : ∀ v x, bor.bitor_assign v x = ok (v ||| x))
    (hfu : ∀ n, fu.«from» n = ok (UScalar.hcast ty n))
    (hfi : fi.«from» (-1)#i8 = ok ⟨BitVec.allOnes ty.numBits⟩)
    (st : leb128fmt.SInt (IScalar ty)) (nBits : U32) (hbits : nBits.val = ty.numBits)
    (hst : st.BITS = ok nBits)
    (zero : IScalar ty) (hzero : zero.bv.toNat = 0) (hfiZero : fi.«from» 0#i8 = ok zero)
    (input : Slice U8) (pos : Usize) :
    ∃ out, leb128fmt.decode_sint_slice width shl bor fi fu st input pos = ok out ∧
      observeSignedRead out = signedSliceMeaning input pos.val width.val := by
  have hguard : width ≤ nBits := by
    change width.val ≤ nBits.val
    omega
  unfold leb128fmt.decode_sint_slice
  simp only [hst, hfiZero, massert, Aeneas.Std.bind_ok, ite_eq_left hguard]
  exact total_result (slice_loop hN hNmod hNbound width hwidth shl bor fi fu
    hshl hbor hfu hfi nBits hbits input pos zero hzero)

theorem i16_reader_spec (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : width.val ≤ 16) :
    ∃ out, i16_reader width input pos = ok out ∧
      observeSignedRead out = signedSliceMeaning input pos.val width.val := by
  unfold i16_reader
  exact signed_decoder (ty := .I16) (by decide) (by decide) (by decide) width hwidth
    _ _ _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl) (by rfl)
    _ 16#u32 rfl (by rw [show (16#u32) = core.num.I16.BITS from rfl]; simp [I16.Insts.Leb128fmtSInt.BITS])
    0#i16 rfl (by rfl) input pos

theorem i32_reader_spec (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : width.val ≤ 32) :
    ∃ out, i32_reader width input pos = ok out ∧
      observeSignedRead out = signedSliceMeaning input pos.val width.val := by
  unfold i32_reader
  exact signed_decoder (ty := .I32) (by decide) (by decide) (by decide) width hwidth
    _ _ _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl) (by rfl)
    _ 32#u32 rfl (by rw [show (32#u32) = core.num.I32.BITS from rfl]; simp [I32.Insts.Leb128fmtSInt.BITS])
    0#i32 rfl (by rfl) input pos

theorem i64_reader_spec (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : width.val ≤ 64) :
    ∃ out, i64_reader width input pos = ok out ∧
      observeSignedRead out = signedSliceMeaning input pos.val width.val := by
  unfold i64_reader
  exact signed_decoder (ty := .I64) (by decide) (by decide) (by decide) width hwidth
    _ _ _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl) (by rfl)
    _ 64#u32 rfl (by rw [show (64#u32) = core.num.I64.BITS from rfl]; simp [I64.Insts.Leb128fmtSInt.BITS])
    0#i64 rfl (by rfl) input pos

theorem i128_reader_spec (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : width.val ≤ 128) :
    ∃ out, i128_reader width input pos = ok out ∧
      observeSignedRead out = signedSliceMeaning input pos.val width.val := by
  unfold i128_reader
  exact signed_decoder (ty := .I128) (by decide) (by decide) (by decide) width hwidth
    _ _ _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl) (by rfl)
    _ 128#u32 rfl (by rw [show (128#u32) = core.num.I128.BITS from rfl]; simp [I128.Insts.Leb128fmtSInt.BITS])
    0#i128 rfl (by rfl) input pos

theorem i16_reader_oversize (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : 16 < width.val) :
    i16_reader width input pos = fail .assertionFailure := by
  have hnot : ¬width ≤ core.num.I16.BITS := by
    change ¬width.val ≤ 16
    omega
  simp only [i16_reader, leb128fmt.decode_sint_slice,
    I16.Insts.Leb128fmtSInt.BITS, massert, Aeneas.Std.bind_ok, ite_eq_right hnot,
    Aeneas.Std.bind_fail]

theorem i32_reader_oversize (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : 32 < width.val) :
    i32_reader width input pos = fail .assertionFailure := by
  have hnot : ¬width ≤ core.num.I32.BITS := by
    change ¬width.val ≤ 32
    omega
  simp only [i32_reader, leb128fmt.decode_sint_slice,
    I32.Insts.Leb128fmtSInt.BITS, massert, Aeneas.Std.bind_ok, ite_eq_right hnot,
    Aeneas.Std.bind_fail]

theorem i64_reader_oversize (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : 64 < width.val) :
    i64_reader width input pos = fail .assertionFailure := by
  have hnot : ¬width ≤ core.num.I64.BITS := by
    change ¬width.val ≤ 64
    omega
  simp only [i64_reader, leb128fmt.decode_sint_slice,
    I64.Insts.Leb128fmtSInt.BITS, massert, Aeneas.Std.bind_ok, ite_eq_right hnot,
    Aeneas.Std.bind_fail]

theorem i128_reader_oversize (width : U32) (input : Slice U8) (pos : Usize)
    (hwidth : 128 < width.val) :
    i128_reader width input pos = fail .assertionFailure := by
  have hnot : ¬width ≤ core.num.I128.BITS := by
    change ¬width.val ≤ 128
    omega
  simp only [i128_reader, leb128fmt.decode_sint_slice,
    I128.Insts.Leb128fmtSInt.BITS, massert, Aeneas.Std.bind_ok, ite_eq_right hnot,
    Aeneas.Std.bind_fail]

end leb128fmt_slice_probe
