import LebErrors

open Aeneas Aeneas.Std Result

namespace leb128fmt

theorem Error.is_more_bytes_needed_spec (error : leb128fmt.Error) :
    ∃ out, Error.is_more_bytes_needed error = ok out ∧
      (out = true ↔ error = InnerError.NeedMoreBytes) := by
  cases error <;> simp [Error.is_more_bytes_needed]

theorem Error.is_invalid_encoding_spec (error : leb128fmt.Error) :
    ∃ out, Error.is_invalid_encoding error = ok out ∧
      (out = true ↔ error = InnerError.InvalidEncoding) := by
  cases error <;> simp [Error.is_invalid_encoding]

theorem Error.clone_spec (error : Error) :
    Error.Insts.CoreCloneClone.clone error = ok error := by
  cases error <;> simp [Error.Insts.CoreCloneClone.clone, InnerError.Insts.CoreCloneClone.clone]

theorem Error.eq_spec (left right : Error) :
    ∃ equal, Error.Insts.CoreCmpPartialEqError.eq left right = ok equal ∧
      (equal = true ↔ left = right) := by
  rcases left with _ | _ <;> rcases right with _ | _
  · exact ⟨true, by simp [Error.Insts.CoreCmpPartialEqError.eq,
      InnerError.Insts.CoreCmpPartialEqInnerError.eq], by simp⟩
  · refine ⟨false, ?_, by simp⟩
    simp [Error.Insts.CoreCmpPartialEqError.eq,
      InnerError.Insts.CoreCmpPartialEqInnerError.eq, InnerError.read_discriminant]
  · refine ⟨false, ?_, by simp⟩
    simp [Error.Insts.CoreCmpPartialEqError.eq,
      InnerError.Insts.CoreCmpPartialEqInnerError.eq, InnerError.read_discriminant]
  · exact ⟨true, by simp [Error.Insts.CoreCmpPartialEqError.eq,
      InnerError.Insts.CoreCmpPartialEqInnerError.eq], by simp⟩

theorem U8.uint_bits_spec : U8.Insts.Leb128fmtUInt.BITS = 8#u32 := by
  rw [U8.Insts.Leb128fmtUInt.BITS]
  rfl

theorem U16.uint_bits_spec : U16.Insts.Leb128fmtUInt.BITS = 16#u32 := by
  rw [U16.Insts.Leb128fmtUInt.BITS]
  rfl

theorem U32.uint_bits_spec : U32.Insts.Leb128fmtUInt.BITS = 32#u32 := by
  rw [U32.Insts.Leb128fmtUInt.BITS]
  rfl

theorem U64.uint_bits_spec : U64.Insts.Leb128fmtUInt.BITS = 64#u32 := by
  rw [U64.Insts.Leb128fmtUInt.BITS]
  rfl

theorem U128.uint_bits_spec : U128.Insts.Leb128fmtUInt.BITS = 128#u32 := by
  rw [U128.Insts.Leb128fmtUInt.BITS]
  rfl

theorem I8.sint_bits_spec : I8.Insts.Leb128fmtSInt.BITS = 8#u32 := by
  rw [I8.Insts.Leb128fmtSInt.BITS]
  rfl

theorem I16.sint_bits_spec : I16.Insts.Leb128fmtSInt.BITS = 16#u32 := by
  rw [I16.Insts.Leb128fmtSInt.BITS]
  rfl

theorem I32.sint_bits_spec : I32.Insts.Leb128fmtSInt.BITS = 32#u32 := by
  rw [I32.Insts.Leb128fmtSInt.BITS]
  rfl

theorem I64.sint_bits_spec : I64.Insts.Leb128fmtSInt.BITS = 64#u32 := by
  rw [I64.Insts.Leb128fmtSInt.BITS]
  rfl

theorem I128.sint_bits_spec : I128.Insts.Leb128fmtSInt.BITS = 128#u32 := by
  rw [I128.Insts.Leb128fmtSInt.BITS]
  rfl

end leb128fmt
