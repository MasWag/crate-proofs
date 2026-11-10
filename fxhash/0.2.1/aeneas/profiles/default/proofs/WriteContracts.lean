import ByteFunctional

open Aeneas Aeneas.Std Result ControlFlow Error
namespace FxHashWriteContracts

theorem fxHasher32_write_succeeds (self : fxhash_adapted.FxHasher32)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write self bytes = .ok out := by
  obtain ⟨h, hh⟩ := FxHash.ByteProofs.write32_succeeds self.hash bytes
  exact ⟨{ hash := h }, by simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write, hh]⟩

theorem fxHasher64_write_succeeds (self : fxhash_adapted.FxHasher64)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write self bytes = .ok out := by
  obtain ⟨h, hh⟩ := FxHash.ByteProofs.write64_succeeds self.hash bytes
  exact ⟨{ hash := h }, by simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write, hh]⟩

theorem fxHasher_write_succeeds (self : fxhash_adapted.FxHasher)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write self bytes = .ok out := by
  obtain ⟨h, hh⟩ := FxHash.ByteProofs.write64_succeeds (UScalar.cast .U64 self.hash) bytes
  refine ⟨{ hash := UScalar.cast .Usize h }, ?_⟩
  simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write,
    fxhash_adapted.write_native, lift, hh]

theorem fxHasher32_write_exact (self : fxhash_adapted.FxHasher32)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher32,
      fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write self bytes = .ok out ∧
      out.hash.bv = FxHash.Spec.write32 .little self.hash.bv
        (bytes.val.map UScalar.val) := by
  obtain ⟨h, hh, hs⟩ := FxHash.ByteFunctional.write32_exact self.hash bytes
  exact ⟨{ hash := h }, by
    simp [fxhash_adapted.FxHasher32.Insts.CoreHashHasher.write, hh], hs⟩

theorem fxHasher64_write_exact (self : fxhash_adapted.FxHasher64)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher64,
      fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write self bytes = .ok out ∧
      out.hash.bv = FxHash.Spec.write64 .little self.hash.bv
        (bytes.val.map UScalar.val) := by
  obtain ⟨h, hh, hs⟩ := FxHash.ByteFunctional.write64_exact self.hash bytes
  exact ⟨{ hash := h }, by
    simp [fxhash_adapted.FxHasher64.Insts.CoreHashHasher.write, hh], hs⟩

/-- The generated native method casts the input state to 64 bits, executes the
64-bit byte algorithm, then casts the result back to native width. -/
theorem fxHasher_write_exact (self : fxhash_adapted.FxHasher)
    (bytes : Slice Std.U8) :
    ∃ out : fxhash_adapted.FxHasher,
      fxhash_adapted.FxHasher.Insts.CoreHashHasher.write self bytes = .ok out ∧
      out.hash.bv = BitVec.setWidth System.Platform.numBits
        (FxHash.Spec.write64 .little (BitVec.setWidth 64 self.hash.bv)
          (bytes.val.map UScalar.val)) := by
  obtain ⟨h, hh, hs⟩ := FxHash.ByteFunctional.write64_exact
    (UScalar.cast .U64 self.hash) bytes
  refine ⟨{ hash := UScalar.cast .Usize h }, ?_, ?_⟩
  · simp [fxhash_adapted.FxHasher.Insts.CoreHashHasher.write,
      fxhash_adapted.write_native, lift, hh]
  · simpa [UScalar.cast_bv_eq, UScalarTy.numBits] using congrArg
      (BitVec.setWidth System.Platform.numBits) hs

end FxHashWriteContracts
