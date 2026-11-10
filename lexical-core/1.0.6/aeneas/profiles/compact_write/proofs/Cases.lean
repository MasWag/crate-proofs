import CompactWrite
open Aeneas Aeneas.Std Result ControlFlow Error
open lexical_core_compact_write
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option maxRecDepth 10000
namespace CompactWriteProofs

theorem loop_stop (digits : Array U8 128#usize) (index : Usize) (value : U8)
    (h : value.val < 10) :
    decimal_u8_loop digits index value = .ok (digits, index, value) := by
  unfold decimal_u8_loop
  rw [loop.eq_def]
  have hv : ¬ value ≥ 10#u8 := by scalar_tac
  simp [decimal_u8_loop.body, hv]

theorem loop_step (digits : Array U8 128#usize) (index : Usize) (value : U8)
    (h : 10 ≤ value.val) :
    decimal_u8_loop digits index value = (do
      let r ← value % 10#u8
      let value1 ← value / 10#u8
      let index1 ← index - 1#usize
      let i ← lift (UScalar.cast .U32 r)
      let i1 ← digit_to_char i
      let a ← Array.update digits index1 i1
      decimal_u8_loop a index1 value1) := by
  unfold decimal_u8_loop
  rw [loop.eq_def]
  have hv : value ≥ 10#u8 := by scalar_tac
  simp [decimal_u8_loop.body, hv]



theorem case_000 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 0#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [48#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_001 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 1#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [49#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_002 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 2#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [50#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_003 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 3#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [51#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_004 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 4#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [52#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_005 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 5#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [53#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_006 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 6#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [54#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_007 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 7#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [55#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_008 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 8#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [56#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_009 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 9#u8 buffer ⦃ out => out.1.val = 1 ∧
      out.2.val = [57#u8] ++ buffer.val.drop 1 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_010 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 10#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_011 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 11#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_012 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 12#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_013 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 13#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_014 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 14#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_015 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 15#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_016 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 16#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_017 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 17#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_018 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 18#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_019 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 19#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [49#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_020 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 20#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_021 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 21#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_022 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 22#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_023 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 23#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_024 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 24#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_025 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 25#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_026 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 26#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_027 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 27#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_028 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 28#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_029 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 29#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [50#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_030 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 30#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_031 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 31#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_032 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 32#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_033 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 33#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_034 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 34#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_035 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 35#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_036 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 36#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_037 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 37#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_038 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 38#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_039 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 39#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [51#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_040 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 40#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_041 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 41#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_042 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 42#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_043 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 43#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_044 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 44#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_045 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 45#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_046 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 46#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_047 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 47#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_048 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 48#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_049 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 49#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [52#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_050 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 50#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_051 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 51#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_052 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 52#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_053 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 53#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_054 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 54#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_055 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 55#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_056 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 56#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_057 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 57#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_058 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 58#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_059 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 59#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [53#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_060 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 60#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_061 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 61#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_062 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 62#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_063 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 63#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_064 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 64#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_065 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 65#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_066 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 66#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_067 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 67#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_068 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 68#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_069 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 69#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [54#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_070 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 70#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_071 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 71#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_072 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 72#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_073 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 73#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_074 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 74#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_075 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 75#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_076 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 76#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_077 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 77#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_078 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 78#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_079 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 79#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [55#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_080 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 80#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_081 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 81#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_082 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 82#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_083 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 83#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_084 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 84#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_085 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 85#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_086 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 86#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_087 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 87#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_088 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 88#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_089 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 89#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [56#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_090 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 90#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,48#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_091 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 91#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,49#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_092 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 92#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,50#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_093 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 93#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,51#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_094 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 94#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,52#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_095 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 95#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,53#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_096 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 96#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,54#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_097 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 97#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,55#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_098 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 98#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,56#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_099 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 99#u8 buffer ⦃ out => out.1.val = 2 ∧
      out.2.val = [57#u8,57#u8] ++ buffer.val.drop 2 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_100 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 100#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_101 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 101#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_102 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 102#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_103 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 103#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_104 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 104#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_105 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 105#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_106 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 106#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_107 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 107#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_108 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 108#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_109 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 109#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,48#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_110 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 110#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_111 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 111#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_112 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 112#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_113 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 113#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_114 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 114#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_115 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 115#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_116 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 116#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_117 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 117#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_118 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 118#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_119 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 119#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,49#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_120 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 120#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_121 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 121#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_122 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 122#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_123 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 123#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_124 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 124#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_125 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 125#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_126 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 126#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_127 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 127#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_128 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 128#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_129 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 129#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,50#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_130 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 130#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_131 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 131#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_132 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 132#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_133 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 133#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_134 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 134#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_135 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 135#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_136 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 136#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_137 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 137#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_138 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 138#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_139 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 139#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,51#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_140 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 140#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_141 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 141#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_142 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 142#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_143 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 143#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_144 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 144#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_145 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 145#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_146 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 146#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_147 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 147#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_148 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 148#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_149 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 149#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,52#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_150 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 150#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_151 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 151#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_152 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 152#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_153 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 153#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_154 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 154#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_155 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 155#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_156 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 156#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_157 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 157#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_158 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 158#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_159 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 159#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,53#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_160 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 160#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_161 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 161#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_162 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 162#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_163 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 163#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_164 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 164#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_165 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 165#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_166 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 166#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_167 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 167#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_168 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 168#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_169 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 169#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,54#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_170 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 170#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_171 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 171#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_172 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 172#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_173 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 173#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_174 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 174#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_175 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 175#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_176 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 176#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_177 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 177#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_178 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 178#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_179 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 179#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,55#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_180 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 180#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_181 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 181#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_182 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 182#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_183 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 183#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_184 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 184#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_185 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 185#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_186 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 186#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_187 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 187#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_188 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 188#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_189 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 189#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,56#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_190 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 190#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_191 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 191#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_192 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 192#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_193 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 193#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_194 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 194#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_195 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 195#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_196 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 196#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_197 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 197#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_198 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 198#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_199 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 199#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [49#u8,57#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_200 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 200#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_201 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 201#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_202 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 202#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_203 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 203#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_204 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 204#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_205 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 205#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_206 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 206#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_207 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 207#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_208 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 208#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_209 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 209#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,48#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_210 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 210#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_211 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 211#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_212 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 212#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_213 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 213#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_214 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 214#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_215 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 215#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_216 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 216#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_217 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 217#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_218 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 218#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_219 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 219#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,49#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_220 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 220#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_221 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 221#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_222 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 222#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_223 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 223#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_224 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 224#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_225 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 225#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_226 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 226#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_227 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 227#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_228 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 228#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_229 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 229#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,50#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_230 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 230#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_231 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 231#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_232 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 232#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_233 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 233#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_234 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 234#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_235 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 235#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_236 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 236#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_237 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 237#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_238 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 238#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_239 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 239#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,51#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_240 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 240#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_241 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 241#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_242 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 242#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_243 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 243#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_244 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 244#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_245 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 245#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_246 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 246#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,54#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_247 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 247#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,55#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_248 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 248#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,56#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_249 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 249#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,52#u8,57#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_250 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 250#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,48#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_251 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 251#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,49#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_252 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 252#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,50#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_253 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 253#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,51#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_254 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 254#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,52#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

theorem case_255 (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 255#u8 buffer ⦃ out => out.1.val = 3 ∧
      out.2.val = [50#u8,53#u8,53#u8] ++ buffer.val.drop 3 ⦄ := by
  unfold decimal_u8
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_step _ _ _ (by scalar_tac)]
  step
  step
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  rw [loop_stop _ _ _ (by scalar_tac)]
  step
  step
  try unfold digit_to_char
  step
  step
  step
  step
  step
  step
  step
  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]

end CompactWriteProofs
