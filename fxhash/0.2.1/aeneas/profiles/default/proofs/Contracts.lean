import FxhashAdapted
import Specs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 4096
namespace FxHashContracts

open fxhash_adapted

theorem hashWord32_correct (h x : Std.U32) :
    ∃ out : Std.U32,
      fxhash_adapted.U32.Insts.Fxhash_adaptedHashWord.hash_word h x = .ok out ∧
      out.bv = FxHash.Spec.mix32 h.bv x.bv := by
  refine ⟨core.num.U32.wrapping_mul
    ((core.num.U32.rotate_left h 5#u32) ^^^ x) 0x27220a95#u32, ?_, ?_⟩
  · simp [fxhash_adapted.U32.Insts.Fxhash_adaptedHashWord.hash_word, fxhash_adapted.SEED32, fxhash_adapted.SEED64, fxhash_adapted.ROTATE, lift, UScalar.cast]; rfl
  · rfl

theorem hashWord64_correct (h x : Std.U64) :
    ∃ out : Std.U64,
      fxhash_adapted.U64.Insts.Fxhash_adaptedHashWord.hash_word h x = .ok out ∧
      out.bv = FxHash.Spec.mix64 h.bv x.bv := by
  refine ⟨core.num.U64.wrapping_mul
    ((core.num.U64.rotate_left h 5#u32) ^^^ x) 0x517cc1b727220a95#u64, ?_, ?_⟩
  · simp [fxhash_adapted.U64.Insts.Fxhash_adaptedHashWord.hash_word,
      fxhash_adapted.SEED64, fxhash_adapted.ROTATE, lift]
  · rfl

theorem hashWordUsize_correct (h x : Std.Usize) :
    ∃ out : Std.Usize,
      fxhash_adapted.Usize.Insts.Fxhash_adaptedHashWord.hash_word h x = .ok out ∧
      out.bv = FxHash.Spec.mixNative h.bv x.bv := by
  refine ⟨core.num.Usize.wrapping_mul
    ((core.num.Usize.rotate_left h 5#u32) ^^^ x)
    (UScalar.cast .Usize fxhash_adapted.SEED64), ?_, ?_⟩
  · simp [fxhash_adapted.Usize.Insts.Fxhash_adaptedHashWord.hash_word,
      fxhash_adapted.SEED, fxhash_adapted.ROTATE, lift]
  · simp only [core.num.Usize.wrapping_mul_bv_eq, UScalar.bv_xor, UScalar.cast_bv_eq]
    simp only [FxHash.Spec.mixNative, FxHash.Spec.mix, FxHash.Spec.seed64,
      core.num.Usize.rotate_left, UScalar.rotate_left, fxhash_adapted.SEED64]
    rfl

theorem fxHasher32_default :
    fxhash_adapted.FxHasher32.Insts.CoreDefaultDefault.default =
      .ok { hash := (0#u32 : Std.U32) } := by rfl

theorem fxHasher64_default :
    fxhash_adapted.FxHasher64.Insts.CoreDefaultDefault.default =
      .ok { hash := (0#u64 : Std.U64) } := by rfl

theorem fxHasher_default :
    fxhash_adapted.FxHasher.Insts.CoreDefaultDefault.default =
      .ok { hash := (0#usize : Std.Usize) } := by rfl

theorem fxHasher32_finish (self : fxhash_adapted.FxHasher32) :
    fxhash_adapted.FxHasher32.Insts.CoreHashHasher.finish self =
      .ok (UScalar.cast .U64 self.hash) := by rfl

theorem fxHasher64_finish (self : fxhash_adapted.FxHasher64) :
    fxhash_adapted.FxHasher64.Insts.CoreHashHasher.finish self =
      .ok self.hash := by rfl

theorem fxHasher_finish (self : fxhash_adapted.FxHasher) :
    fxhash_adapted.FxHasher.Insts.CoreHashHasher.finish self =
      .ok (UScalar.cast .U64 self.hash) := by rfl

theorem fxHasher32_write_u32 (self : fxhash_adapted.FxHasher32) (i : Std.U32) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u32 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix32 self.hash.bv i.bv := by
  rcases hashWord32_correct self.hash i with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, hs⟩
  simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u32, hh]

theorem fxHasher64_write_u64 (self : fxhash_adapted.FxHasher64) (i : Std.U64) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u64 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix64 self.hash.bv i.bv := by
  rcases hashWord64_correct self.hash i with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, hs⟩
  simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u64, hh]

theorem fxHasher32_write_u8 (self : fxhash_adapted.FxHasher32) (i : Std.U8) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u8 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix32 self.hash.bv (BitVec.setWidth 32 i.bv) := by
  let x := UScalar.cast .U32 i
  rcases hashWord32_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u8, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher32_write_u16 (self : fxhash_adapted.FxHasher32) (i : Std.U16) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u16 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix32 self.hash.bv (BitVec.setWidth 32 i.bv) := by
  let x := UScalar.cast .U32 i
  rcases hashWord32_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u16, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher64_write_u8 (self : fxhash_adapted.FxHasher64) (i : Std.U8) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u8 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix64 self.hash.bv (BitVec.setWidth 64 i.bv) := by
  let x := UScalar.cast .U64 i
  rcases hashWord64_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u8, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher64_write_u16 (self : fxhash_adapted.FxHasher64) (i : Std.U16) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u16 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix64 self.hash.bv (BitVec.setWidth 64 i.bv) := by
  let x := UScalar.cast .U64 i
  rcases hashWord64_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u16, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher64_write_u32 (self : fxhash_adapted.FxHasher64) (i : Std.U32) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u32 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix64 self.hash.bv (BitVec.setWidth 64 i.bv) := by
  let x := UScalar.cast .U64 i
  rcases hashWord64_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_u32, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher64_write_usize (self : fxhash_adapted.FxHasher64) (i : Std.Usize) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_usize self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mix64 self.hash.bv (BitVec.setWidth 64 i.bv) := by
  let x := UScalar.cast .U64 i
  rcases hashWord64_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write_usize, lift, x, hh]
  · simpa [x] using hs

private theorem high32_of_u64 (i : Std.U64) :
    BitVec.setWidth 32 (i.bv >>> 32) = BitVec.ofNat 32 (i.bv.toNat / 2^32) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem fxHasher32_write_u64 (self : fxhash_adapted.FxHasher32) (i : Std.U64) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u64 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.writeU64To32 self.hash.bv i.bv := by
  have hshift : i >>> (32#i32) = .ok ⟨i.bv.ushiftRight 32⟩ := by rfl
  simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_u64, hshift,
    fxhash_adapted.U32.Insts.Fxhash_adaptedHashWord.hash_word,
    fxhash_adapted.SEED32, fxhash_adapted.SEED64, fxhash_adapted.ROTATE,
    FxHash.Spec.writeU64To32, FxHash.Spec.mix32, FxHash.Spec.mix, FxHash.Spec.seed32,
    lift, UScalar.cast]
  rw [high32_of_u64]
  rfl

theorem fxHasher32_write_usize (self : fxhash_adapted.FxHasher32) (i : Std.Usize) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_usize self i = .ok out ∧
      out.hash.bv = FxHash.Spec.writeU64To32 self.hash.bv (BitVec.setWidth 64 i.bv) := by
  obtain ⟨out, hout, hspec⟩ := fxHasher32_write_u64 self (UScalar.cast .U64 i)
  refine ⟨out, ?_, ?_⟩
  · simpa [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write_usize, lift] using hout
  · simpa using hspec

theorem fxHasher_write_u8 (self : fxhash_adapted.FxHasher) (i : Std.U8) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u8 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mixNative self.hash.bv
        (BitVec.setWidth System.Platform.numBits i.bv) := by
  let x := UScalar.cast .Usize i
  rcases hashWordUsize_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u8, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher_write_u16 (self : fxhash_adapted.FxHasher) (i : Std.U16) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u16 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mixNative self.hash.bv
        (BitVec.setWidth System.Platform.numBits i.bv) := by
  let x := UScalar.cast .Usize i
  rcases hashWordUsize_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u16, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher_write_u32 (self : fxhash_adapted.FxHasher) (i : Std.U32) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u32 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mixNative self.hash.bv
        (BitVec.setWidth System.Platform.numBits i.bv) := by
  let x := UScalar.cast .Usize i
  rcases hashWordUsize_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u32, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher_write_u64 (self : fxhash_adapted.FxHasher) (i : Std.U64) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u64 self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mixNative self.hash.bv
        (BitVec.setWidth System.Platform.numBits i.bv) := by
  let x := UScalar.cast .Usize i
  rcases hashWordUsize_correct self.hash x with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_u64, lift, x, hh]
  · simpa [x] using hs

theorem fxHasher_write_usize (self : fxhash_adapted.FxHasher) (i : Std.Usize) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_usize self i = .ok out ∧
      out.hash.bv = FxHash.Spec.mixNative self.hash.bv i.bv := by
  rcases hashWordUsize_correct self.hash i with ⟨h, hh, hs⟩
  refine ⟨{ hash := h }, ?_, hs⟩
  simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write_usize, hh]

end FxHashContracts
