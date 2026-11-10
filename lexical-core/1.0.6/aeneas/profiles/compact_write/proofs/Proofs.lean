import Cases
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result ControlFlow Error
open lexical_core_compact_write
namespace CompactWriteProofs
set_option maxHeartbeats 8000000

/-- Independent arithmetic ASCII specification for the entire u8 domain. -/
def decimalAscii (n : Nat) : List Nat :=
  if n < 10 then [48 + n]
  else if n < 100 then [48 + n / 10, 48 + n % 10]
  else [48 + n / 100, 48 + (n / 10) % 10, 48 + n % 10]

def asciiByte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩
def decimalBytes (n : Nat) : List U8 := (decimalAscii n).map asciiByte

private theorem total_ok {α : Type _} {m : Result α} {P : α → Prop}
    (h : WP.spec m P) : ∃ out, m = .ok out ∧ P out := by
  cases m using Result.cases with
  | ret out => exact ⟨out, rfl, (WP.spec_ok out).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

/-- Kernel-checked finite exhaustion covers all representable u8 values;
    the caller buffer and its contents remain arbitrary. -/
theorem decimal_u8_wp (value : U8) (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 value buffer ⦃ out =>
      out.1.val = (decimalBytes value.val).length ∧
      out.2.val = decimalBytes value.val ++ buffer.val.drop out.1.val ⦄ := by
  have hv : value.val ≤ 255 := by scalar_tac
  interval_cases hval : value.val
  · have heq : value = 0#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_000 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 1#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_001 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 2#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_002 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 3#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_003 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 4#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_004 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 5#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_005 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 6#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_006 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 7#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_007 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 8#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_008 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 9#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_009 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 10#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_010 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 11#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_011 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 12#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_012 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 13#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_013 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 14#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_014 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 15#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_015 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 16#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_016 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 17#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_017 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 18#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_018 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 19#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_019 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 20#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_020 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 21#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_021 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 22#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_022 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 23#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_023 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 24#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_024 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 25#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_025 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 26#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_026 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 27#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_027 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 28#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_028 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 29#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_029 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 30#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_030 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 31#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_031 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 32#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_032 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 33#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_033 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 34#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_034 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 35#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_035 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 36#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_036 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 37#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_037 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 38#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_038 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 39#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_039 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 40#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_040 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 41#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_041 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 42#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_042 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 43#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_043 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 44#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_044 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 45#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_045 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 46#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_046 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 47#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_047 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 48#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_048 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 49#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_049 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 50#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_050 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 51#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_051 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 52#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_052 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 53#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_053 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 54#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_054 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 55#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_055 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 56#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_056 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 57#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_057 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 58#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_058 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 59#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_059 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 60#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_060 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 61#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_061 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 62#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_062 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 63#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_063 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 64#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_064 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 65#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_065 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 66#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_066 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 67#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_067 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 68#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_068 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 69#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_069 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 70#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_070 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 71#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_071 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 72#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_072 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 73#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_073 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 74#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_074 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 75#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_075 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 76#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_076 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 77#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_077 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 78#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_078 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 79#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_079 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 80#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_080 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 81#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_081 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 82#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_082 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 83#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_083 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 84#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_084 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 85#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_085 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 86#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_086 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 87#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_087 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 88#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_088 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 89#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_089 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 90#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_090 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 91#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_091 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 92#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_092 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 93#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_093 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 94#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_094 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 95#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_095 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 96#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_096 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 97#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_097 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 98#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_098 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 99#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_099 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 100#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_100 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 101#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_101 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 102#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_102 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 103#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_103 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 104#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_104 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 105#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_105 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 106#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_106 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 107#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_107 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 108#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_108 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 109#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_109 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 110#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_110 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 111#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_111 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 112#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_112 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 113#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_113 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 114#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_114 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 115#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_115 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 116#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_116 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 117#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_117 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 118#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_118 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 119#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_119 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 120#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_120 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 121#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_121 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 122#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_122 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 123#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_123 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 124#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_124 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 125#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_125 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 126#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_126 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 127#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_127 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 128#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_128 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 129#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_129 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 130#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_130 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 131#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_131 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 132#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_132 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 133#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_133 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 134#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_134 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 135#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_135 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 136#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_136 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 137#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_137 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 138#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_138 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 139#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_139 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 140#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_140 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 141#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_141 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 142#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_142 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 143#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_143 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 144#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_144 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 145#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_145 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 146#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_146 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 147#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_147 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 148#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_148 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 149#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_149 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 150#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_150 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 151#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_151 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 152#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_152 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 153#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_153 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 154#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_154 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 155#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_155 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 156#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_156 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 157#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_157 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 158#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_158 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 159#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_159 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 160#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_160 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 161#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_161 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 162#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_162 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 163#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_163 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 164#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_164 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 165#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_165 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 166#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_166 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 167#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_167 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 168#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_168 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 169#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_169 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 170#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_170 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 171#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_171 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 172#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_172 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 173#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_173 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 174#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_174 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 175#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_175 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 176#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_176 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 177#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_177 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 178#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_178 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 179#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_179 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 180#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_180 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 181#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_181 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 182#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_182 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 183#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_183 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 184#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_184 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 185#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_185 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 186#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_186 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 187#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_187 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 188#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_188 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 189#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_189 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 190#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_190 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 191#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_191 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 192#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_192 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 193#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_193 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 194#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_194 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 195#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_195 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 196#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_196 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 197#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_197 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 198#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_198 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 199#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_199 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 200#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_200 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 201#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_201 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 202#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_202 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 203#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_203 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 204#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_204 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 205#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_205 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 206#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_206 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 207#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_207 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 208#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_208 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 209#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_209 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 210#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_210 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 211#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_211 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 212#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_212 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 213#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_213 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 214#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_214 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 215#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_215 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 216#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_216 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 217#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_217 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 218#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_218 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 219#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_219 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 220#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_220 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 221#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_221 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 222#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_222 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 223#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_223 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 224#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_224 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 225#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_225 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 226#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_226 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 227#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_227 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 228#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_228 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 229#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_229 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 230#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_230 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 231#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_231 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 232#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_232 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 233#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_233 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 234#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_234 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 235#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_235 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 236#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_236 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 237#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_237 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 238#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_238 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 239#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_239 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 240#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_240 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 241#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_241 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 242#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_242 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 243#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_243 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 244#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_244 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 245#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_245 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 246#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_246 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 247#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_247 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 248#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_248 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 249#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_249 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 250#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_250 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 251#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_251 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 252#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_252 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 253#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_253 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 254#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_254 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]
  · have heq : value = 255#u8 := UScalar.eq_of_val_eq (by simpa using hval)
    subst value
    apply WP.spec_mono (case_255 buffer h)
    intro out ⟨hk, hb⟩
    simp_all [decimalBytes, decimalAscii, asciiByte, UScalar.ofNatCore]

def decodeAscii (digits : List Nat) : Nat :=
  digits.foldl (fun value c => 10 * value + (c - 48)) 0

/-- The independent arithmetic specification is canonical throughout u8's domain. -/
theorem decimalAscii_canonical (n : Nat) (h : n ≤ 255) :
    1 ≤ (decimalAscii n).length ∧ (decimalAscii n).length ≤ 3 ∧
    decodeAscii (decimalAscii n) = n ∧
    (n = 0 ∨ (decimalAscii n).head? ≠ some 48) ∧
    (decimalAscii n).all (fun c => decide (48 ≤ c ∧ c ≤ 57)) = true := by
  interval_cases n <;> decide

/-- Total successful canonical decimal output, exact length and caller-buffer frame. -/
theorem decimal_u8_spec (value : U8) (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    ∃ out, decimal_u8 value buffer = .ok out ∧
      out.1.val = (decimalBytes value.val).length ∧
      out.2.val = decimalBytes value.val ++ buffer.val.drop out.1.val :=
  total_ok (decimal_u8_wp value buffer h)

end CompactWriteProofs
