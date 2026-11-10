import Proofs.Recognition

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result
namespace LexicalParseIntegerRadixProofs

private def swar4 (r : Nat) (v : Std.U32) : Bool :=
  decide (((v.bv + BitVec.ofNat 32 (repeated (80-r) 4) ||| v.bv - 808464432#32)
    &&& 2155905152#32) = 0#32)

private def swar8 (r : Nat) (v : Std.U64) : Bool :=
  decide (((v.bv + BitVec.ofNat 64 (repeated (80-r) 8) ||| v.bv - 3472328296227680304#64)
    &&& 9259542123273814144#64) = 0#64)

theorem is4_eq_swar_radix2 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 2#u32 v = .ok (swar4 2 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 2#u32 : Result Std.U32) = .ok 78#u32 := by rfl
  have h2 : (78#u32 <<< 8#i32 : Result Std.U32) = .ok 19968#u32 := by rfl
  have h3 : (78#u32 + 19968#u32 : Result Std.U32) = .ok 20046#u32 := by rfl
  have h4 : (78#u32 <<< 16#i32 : Result Std.U32) = .ok 5111808#u32 := by rfl
  have h5 : (20046#u32 + 5111808#u32 : Result Std.U32) = .ok 5131854#u32 := by rfl
  have h6 : (78#u32 <<< 24#i32 : Result Std.U32) = .ok 1308622848#u32 := by rfl
  have h7 : (5131854#u32 + 1308622848#u32 : Result Std.U32) = .ok 1313754702#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix3 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 3#u32 v = .ok (swar4 3 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 3#u32 : Result Std.U32) = .ok 77#u32 := by rfl
  have h2 : (77#u32 <<< 8#i32 : Result Std.U32) = .ok 19712#u32 := by rfl
  have h3 : (77#u32 + 19712#u32 : Result Std.U32) = .ok 19789#u32 := by rfl
  have h4 : (77#u32 <<< 16#i32 : Result Std.U32) = .ok 5046272#u32 := by rfl
  have h5 : (19789#u32 + 5046272#u32 : Result Std.U32) = .ok 5066061#u32 := by rfl
  have h6 : (77#u32 <<< 24#i32 : Result Std.U32) = .ok 1291845632#u32 := by rfl
  have h7 : (5066061#u32 + 1291845632#u32 : Result Std.U32) = .ok 1296911693#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix4 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 4#u32 v = .ok (swar4 4 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 4#u32 : Result Std.U32) = .ok 76#u32 := by rfl
  have h2 : (76#u32 <<< 8#i32 : Result Std.U32) = .ok 19456#u32 := by rfl
  have h3 : (76#u32 + 19456#u32 : Result Std.U32) = .ok 19532#u32 := by rfl
  have h4 : (76#u32 <<< 16#i32 : Result Std.U32) = .ok 4980736#u32 := by rfl
  have h5 : (19532#u32 + 4980736#u32 : Result Std.U32) = .ok 5000268#u32 := by rfl
  have h6 : (76#u32 <<< 24#i32 : Result Std.U32) = .ok 1275068416#u32 := by rfl
  have h7 : (5000268#u32 + 1275068416#u32 : Result Std.U32) = .ok 1280068684#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix5 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 5#u32 v = .ok (swar4 5 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 5#u32 : Result Std.U32) = .ok 75#u32 := by rfl
  have h2 : (75#u32 <<< 8#i32 : Result Std.U32) = .ok 19200#u32 := by rfl
  have h3 : (75#u32 + 19200#u32 : Result Std.U32) = .ok 19275#u32 := by rfl
  have h4 : (75#u32 <<< 16#i32 : Result Std.U32) = .ok 4915200#u32 := by rfl
  have h5 : (19275#u32 + 4915200#u32 : Result Std.U32) = .ok 4934475#u32 := by rfl
  have h6 : (75#u32 <<< 24#i32 : Result Std.U32) = .ok 1258291200#u32 := by rfl
  have h7 : (4934475#u32 + 1258291200#u32 : Result Std.U32) = .ok 1263225675#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix6 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 6#u32 v = .ok (swar4 6 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 6#u32 : Result Std.U32) = .ok 74#u32 := by rfl
  have h2 : (74#u32 <<< 8#i32 : Result Std.U32) = .ok 18944#u32 := by rfl
  have h3 : (74#u32 + 18944#u32 : Result Std.U32) = .ok 19018#u32 := by rfl
  have h4 : (74#u32 <<< 16#i32 : Result Std.U32) = .ok 4849664#u32 := by rfl
  have h5 : (19018#u32 + 4849664#u32 : Result Std.U32) = .ok 4868682#u32 := by rfl
  have h6 : (74#u32 <<< 24#i32 : Result Std.U32) = .ok 1241513984#u32 := by rfl
  have h7 : (4868682#u32 + 1241513984#u32 : Result Std.U32) = .ok 1246382666#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix7 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 7#u32 v = .ok (swar4 7 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 7#u32 : Result Std.U32) = .ok 73#u32 := by rfl
  have h2 : (73#u32 <<< 8#i32 : Result Std.U32) = .ok 18688#u32 := by rfl
  have h3 : (73#u32 + 18688#u32 : Result Std.U32) = .ok 18761#u32 := by rfl
  have h4 : (73#u32 <<< 16#i32 : Result Std.U32) = .ok 4784128#u32 := by rfl
  have h5 : (18761#u32 + 4784128#u32 : Result Std.U32) = .ok 4802889#u32 := by rfl
  have h6 : (73#u32 <<< 24#i32 : Result Std.U32) = .ok 1224736768#u32 := by rfl
  have h7 : (4802889#u32 + 1224736768#u32 : Result Std.U32) = .ok 1229539657#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix8 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 8#u32 v = .ok (swar4 8 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 8#u32 : Result Std.U32) = .ok 72#u32 := by rfl
  have h2 : (72#u32 <<< 8#i32 : Result Std.U32) = .ok 18432#u32 := by rfl
  have h3 : (72#u32 + 18432#u32 : Result Std.U32) = .ok 18504#u32 := by rfl
  have h4 : (72#u32 <<< 16#i32 : Result Std.U32) = .ok 4718592#u32 := by rfl
  have h5 : (18504#u32 + 4718592#u32 : Result Std.U32) = .ok 4737096#u32 := by rfl
  have h6 : (72#u32 <<< 24#i32 : Result Std.U32) = .ok 1207959552#u32 := by rfl
  have h7 : (4737096#u32 + 1207959552#u32 : Result Std.U32) = .ok 1212696648#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix9 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 9#u32 v = .ok (swar4 9 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 9#u32 : Result Std.U32) = .ok 71#u32 := by rfl
  have h2 : (71#u32 <<< 8#i32 : Result Std.U32) = .ok 18176#u32 := by rfl
  have h3 : (71#u32 + 18176#u32 : Result Std.U32) = .ok 18247#u32 := by rfl
  have h4 : (71#u32 <<< 16#i32 : Result Std.U32) = .ok 4653056#u32 := by rfl
  have h5 : (18247#u32 + 4653056#u32 : Result Std.U32) = .ok 4671303#u32 := by rfl
  have h6 : (71#u32 <<< 24#i32 : Result Std.U32) = .ok 1191182336#u32 := by rfl
  have h7 : (4671303#u32 + 1191182336#u32 : Result Std.U32) = .ok 1195853639#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar_radix10 (v : Std.U32) :
    lexical_parse_integer_radix_harness.is_4digits 10#u32 v = .ok (swar4 10 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 10#u32 : Result Std.U32) = .ok 70#u32 := by rfl
  have h2 : (70#u32 <<< 8#i32 : Result Std.U32) = .ok 17920#u32 := by rfl
  have h3 : (70#u32 + 17920#u32 : Result Std.U32) = .ok 17990#u32 := by rfl
  have h4 : (70#u32 <<< 16#i32 : Result Std.U32) = .ok 4587520#u32 := by rfl
  have h5 : (17990#u32 + 4587520#u32 : Result Std.U32) = .ok 4605510#u32 := by rfl
  have h6 : (70#u32 <<< 24#i32 : Result Std.U32) = .ok 1174405120#u32 := by rfl
  have h7 : (4605510#u32 + 1174405120#u32 : Result Std.U32) = .ok 1179010630#u32 := by rfl
  simp [swar4, repeated, lexical_parse_integer_radix_harness.is_4digits,
    h0,h1,h2,h3,h4,h5,h6,h7, core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix2 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 2#u32 v = .ok (swar8 2 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 2#u32 : Result Std.U32) = .ok 78#u32 := by rfl
  have h2 : (78#u32 <<< 8#i32 : Result Std.U32) = .ok 19968#u32 := by rfl
  have h3 : (78#u32 + 19968#u32 : Result Std.U32) = .ok 20046#u32 := by rfl
  have h4 : (78#u32 <<< 16#i32 : Result Std.U32) = .ok 5111808#u32 := by rfl
  have h5 : (20046#u32 + 5111808#u32 : Result Std.U32) = .ok 5131854#u32 := by rfl
  have h6 : (78#u32 <<< 24#i32 : Result Std.U32) = .ok 1308622848#u32 := by rfl
  have h7 : (5131854#u32 + 1308622848#u32 : Result Std.U32) = .ok 1313754702#u32 := by rfl
  have hc : UScalar.cast .U64 1313754702#u32 = (1313754702#u64 : Std.U64) := by rfl
  have h8 : (1313754702#u64 <<< 32#i32 : Result Std.U64) = .ok 5642533480056225792#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix3 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 3#u32 v = .ok (swar8 3 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 3#u32 : Result Std.U32) = .ok 77#u32 := by rfl
  have h2 : (77#u32 <<< 8#i32 : Result Std.U32) = .ok 19712#u32 := by rfl
  have h3 : (77#u32 + 19712#u32 : Result Std.U32) = .ok 19789#u32 := by rfl
  have h4 : (77#u32 <<< 16#i32 : Result Std.U32) = .ok 5046272#u32 := by rfl
  have h5 : (19789#u32 + 5046272#u32 : Result Std.U32) = .ok 5066061#u32 := by rfl
  have h6 : (77#u32 <<< 24#i32 : Result Std.U32) = .ok 1291845632#u32 := by rfl
  have h7 : (5066061#u32 + 1291845632#u32 : Result Std.U32) = .ok 1296911693#u32 := by rfl
  have hc : UScalar.cast .U64 1296911693#u32 = (1296911693#u64 : Std.U64) := by rfl
  have h8 : (1296911693#u64 <<< 32#i32 : Result Std.U64) = .ok 5570193307234992128#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix4 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 4#u32 v = .ok (swar8 4 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 4#u32 : Result Std.U32) = .ok 76#u32 := by rfl
  have h2 : (76#u32 <<< 8#i32 : Result Std.U32) = .ok 19456#u32 := by rfl
  have h3 : (76#u32 + 19456#u32 : Result Std.U32) = .ok 19532#u32 := by rfl
  have h4 : (76#u32 <<< 16#i32 : Result Std.U32) = .ok 4980736#u32 := by rfl
  have h5 : (19532#u32 + 4980736#u32 : Result Std.U32) = .ok 5000268#u32 := by rfl
  have h6 : (76#u32 <<< 24#i32 : Result Std.U32) = .ok 1275068416#u32 := by rfl
  have h7 : (5000268#u32 + 1275068416#u32 : Result Std.U32) = .ok 1280068684#u32 := by rfl
  have hc : UScalar.cast .U64 1280068684#u32 = (1280068684#u64 : Std.U64) := by rfl
  have h8 : (1280068684#u64 <<< 32#i32 : Result Std.U64) = .ok 5497853134413758464#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix5 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 5#u32 v = .ok (swar8 5 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 5#u32 : Result Std.U32) = .ok 75#u32 := by rfl
  have h2 : (75#u32 <<< 8#i32 : Result Std.U32) = .ok 19200#u32 := by rfl
  have h3 : (75#u32 + 19200#u32 : Result Std.U32) = .ok 19275#u32 := by rfl
  have h4 : (75#u32 <<< 16#i32 : Result Std.U32) = .ok 4915200#u32 := by rfl
  have h5 : (19275#u32 + 4915200#u32 : Result Std.U32) = .ok 4934475#u32 := by rfl
  have h6 : (75#u32 <<< 24#i32 : Result Std.U32) = .ok 1258291200#u32 := by rfl
  have h7 : (4934475#u32 + 1258291200#u32 : Result Std.U32) = .ok 1263225675#u32 := by rfl
  have hc : UScalar.cast .U64 1263225675#u32 = (1263225675#u64 : Std.U64) := by rfl
  have h8 : (1263225675#u64 <<< 32#i32 : Result Std.U64) = .ok 5425512961592524800#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix6 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 6#u32 v = .ok (swar8 6 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 6#u32 : Result Std.U32) = .ok 74#u32 := by rfl
  have h2 : (74#u32 <<< 8#i32 : Result Std.U32) = .ok 18944#u32 := by rfl
  have h3 : (74#u32 + 18944#u32 : Result Std.U32) = .ok 19018#u32 := by rfl
  have h4 : (74#u32 <<< 16#i32 : Result Std.U32) = .ok 4849664#u32 := by rfl
  have h5 : (19018#u32 + 4849664#u32 : Result Std.U32) = .ok 4868682#u32 := by rfl
  have h6 : (74#u32 <<< 24#i32 : Result Std.U32) = .ok 1241513984#u32 := by rfl
  have h7 : (4868682#u32 + 1241513984#u32 : Result Std.U32) = .ok 1246382666#u32 := by rfl
  have hc : UScalar.cast .U64 1246382666#u32 = (1246382666#u64 : Std.U64) := by rfl
  have h8 : (1246382666#u64 <<< 32#i32 : Result Std.U64) = .ok 5353172788771291136#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix7 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 7#u32 v = .ok (swar8 7 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 7#u32 : Result Std.U32) = .ok 73#u32 := by rfl
  have h2 : (73#u32 <<< 8#i32 : Result Std.U32) = .ok 18688#u32 := by rfl
  have h3 : (73#u32 + 18688#u32 : Result Std.U32) = .ok 18761#u32 := by rfl
  have h4 : (73#u32 <<< 16#i32 : Result Std.U32) = .ok 4784128#u32 := by rfl
  have h5 : (18761#u32 + 4784128#u32 : Result Std.U32) = .ok 4802889#u32 := by rfl
  have h6 : (73#u32 <<< 24#i32 : Result Std.U32) = .ok 1224736768#u32 := by rfl
  have h7 : (4802889#u32 + 1224736768#u32 : Result Std.U32) = .ok 1229539657#u32 := by rfl
  have hc : UScalar.cast .U64 1229539657#u32 = (1229539657#u64 : Std.U64) := by rfl
  have h8 : (1229539657#u64 <<< 32#i32 : Result Std.U64) = .ok 5280832615950057472#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix8 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 8#u32 v = .ok (swar8 8 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 8#u32 : Result Std.U32) = .ok 72#u32 := by rfl
  have h2 : (72#u32 <<< 8#i32 : Result Std.U32) = .ok 18432#u32 := by rfl
  have h3 : (72#u32 + 18432#u32 : Result Std.U32) = .ok 18504#u32 := by rfl
  have h4 : (72#u32 <<< 16#i32 : Result Std.U32) = .ok 4718592#u32 := by rfl
  have h5 : (18504#u32 + 4718592#u32 : Result Std.U32) = .ok 4737096#u32 := by rfl
  have h6 : (72#u32 <<< 24#i32 : Result Std.U32) = .ok 1207959552#u32 := by rfl
  have h7 : (4737096#u32 + 1207959552#u32 : Result Std.U32) = .ok 1212696648#u32 := by rfl
  have hc : UScalar.cast .U64 1212696648#u32 = (1212696648#u64 : Std.U64) := by rfl
  have h8 : (1212696648#u64 <<< 32#i32 : Result Std.U64) = .ok 5208492443128823808#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix9 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 9#u32 v = .ok (swar8 9 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 9#u32 : Result Std.U32) = .ok 71#u32 := by rfl
  have h2 : (71#u32 <<< 8#i32 : Result Std.U32) = .ok 18176#u32 := by rfl
  have h3 : (71#u32 + 18176#u32 : Result Std.U32) = .ok 18247#u32 := by rfl
  have h4 : (71#u32 <<< 16#i32 : Result Std.U32) = .ok 4653056#u32 := by rfl
  have h5 : (18247#u32 + 4653056#u32 : Result Std.U32) = .ok 4671303#u32 := by rfl
  have h6 : (71#u32 <<< 24#i32 : Result Std.U32) = .ok 1191182336#u32 := by rfl
  have h7 : (4671303#u32 + 1191182336#u32 : Result Std.U32) = .ok 1195853639#u32 := by rfl
  have hc : UScalar.cast .U64 1195853639#u32 = (1195853639#u64 : Std.U64) := by rfl
  have h8 : (1195853639#u64 <<< 32#i32 : Result Std.U64) = .ok 5136152270307590144#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_eq_swar_radix10 (v : Std.U64) :
    lexical_parse_integer_radix_harness.is_8digits 10#u32 v = .ok (swar8 10 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 10#u32 : Result Std.U32) = .ok 70#u32 := by rfl
  have h2 : (70#u32 <<< 8#i32 : Result Std.U32) = .ok 17920#u32 := by rfl
  have h3 : (70#u32 + 17920#u32 : Result Std.U32) = .ok 17990#u32 := by rfl
  have h4 : (70#u32 <<< 16#i32 : Result Std.U32) = .ok 4587520#u32 := by rfl
  have h5 : (17990#u32 + 4587520#u32 : Result Std.U32) = .ok 4605510#u32 := by rfl
  have h6 : (70#u32 <<< 24#i32 : Result Std.U32) = .ok 1174405120#u32 := by rfl
  have h7 : (4605510#u32 + 1174405120#u32 : Result Std.U32) = .ok 1179010630#u32 := by rfl
  have hc : UScalar.cast .U64 1179010630#u32 = (1179010630#u64 : Std.U64) := by rfl
  have h8 : (1179010630#u64 <<< 32#i32 : Result Std.U64) = .ok 5063812097486356480#u64 := by rfl
  simp [swar8, repeated, lexical_parse_integer_radix_harness.is_8digits,
    h0,h1,h2,h3,h4,h5,h6,h7,hc,h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_eq_swar (r : Std.U32) (v : Std.U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
    lexical_parse_integer_radix_harness.is_4digits r v = .ok (swar4 r.val v) := by
  have hcases : r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · have heq : r = 2#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h2)
    rw [heq]
    simpa using is4_eq_swar_radix2 v
  · have heq : r = 3#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h3)
    rw [heq]
    simpa using is4_eq_swar_radix3 v
  · have heq : r = 4#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h4)
    rw [heq]
    simpa using is4_eq_swar_radix4 v
  · have heq : r = 5#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h5)
    rw [heq]
    simpa using is4_eq_swar_radix5 v
  · have heq : r = 6#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h6)
    rw [heq]
    simpa using is4_eq_swar_radix6 v
  · have heq : r = 7#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h7)
    rw [heq]
    simpa using is4_eq_swar_radix7 v
  · have heq : r = 8#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h8)
    rw [heq]
    simpa using is4_eq_swar_radix8 v
  · have heq : r = 9#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h9)
    rw [heq]
    simpa using is4_eq_swar_radix9 v
  · have heq : r = 10#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h10)
    rw [heq]
    simpa using is4_eq_swar_radix10 v

theorem is8_eq_swar (r : Std.U32) (v : Std.U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
    lexical_parse_integer_radix_harness.is_8digits r v = .ok (swar8 r.val v) := by
  have hcases : r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · have heq : r = 2#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h2)
    rw [heq]
    simpa using is8_eq_swar_radix2 v
  · have heq : r = 3#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h3)
    rw [heq]
    simpa using is8_eq_swar_radix3 v
  · have heq : r = 4#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h4)
    rw [heq]
    simpa using is8_eq_swar_radix4 v
  · have heq : r = 5#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h5)
    rw [heq]
    simpa using is8_eq_swar_radix5 v
  · have heq : r = 6#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h6)
    rw [heq]
    simpa using is8_eq_swar_radix6 v
  · have heq : r = 7#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h7)
    rw [heq]
    simpa using is8_eq_swar_radix7 v
  · have heq : r = 8#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h8)
    rw [heq]
    simpa using is8_eq_swar_radix8 v
  · have heq : r = 9#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h9)
    rw [heq]
    simpa using is8_eq_swar_radix9 v
  · have heq : r = 10#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h10)
    rw [heq]
    simpa using is8_eq_swar_radix10 v

theorem bitvec_mask_nat {w : Nat} (v a b m : BitVec w) :
 (((v+a ||| v-b)&&&m)=0#w) ↔
 (((v.toNat+a.toNat)%2^w ||| ((2^w-b.toNat)+v.toNat)%2^w)&&&m.toNat=0) := by
 rw [←BitVec.toNat_inj]
 simp only [BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_add,BitVec.toNat_sub,
   BitVec.toNat_ofNat, Nat.zero_mod]

theorem swar4_correct (r : Std.U32) (v : Std.U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
 swar4 r.val v = true ↔ LexicalParseIntegerRadixSpec.digits4 r.val v.val := by
 have h := recognition_mask r.val 4 v.val hr
 have hc0 : repeated 48 4 = 808464432 := by norm_num [repeated]
 have hc1 : repeated 128 4 = 2155905152 := by norm_num [repeated]
 have hp : 256^4 = 4294967296 := by norm_num
 simp only [hc0,hc1,hp] at h
 have hsub : v.val+4294967296-808464432=v.val+3486502864 := by omega
 rw [hsub] at h
 simp only [swar4,decide_eq_true_eq,bitvec_mask_nat,BitVec.toNat_ofNat]
 norm_num only
 have hrep : repeated (80-r.val) 4 < 4294967296 := by
   have hb := repeated_bound 4 (80-r.val) (by omega)
   norm_num at hb
   exact hb
 simp only [Nat.mod_eq_of_lt hrep]
 rw [UScalar.bv_toNat]
 conv_lhs => lhs; lhs; rhs; lhs; rw [Nat.add_comm]
 unfold LexicalParseIntegerRadixSpec.digits4
 exact h

theorem swar8_correct (r : Std.U32) (v : Std.U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
 swar8 r.val v = true ↔ LexicalParseIntegerRadixSpec.digits8 r.val v.val := by
 have h := recognition_mask r.val 8 v.val hr
 have hc0 : repeated 48 8 = 3472328296227680304 := by norm_num [repeated]
 have hc1 : repeated 128 8 = 9259542123273814144 := by norm_num [repeated]
 have hp : 256^8 = 18446744073709551616 := by norm_num
 simp only [hc0,hc1,hp] at h
 have hsub : v.val+18446744073709551616-3472328296227680304=v.val+14974415777481871312 := by omega
 rw [hsub] at h
 simp only [swar8,decide_eq_true_eq,bitvec_mask_nat,BitVec.toNat_ofNat]
 norm_num only
 have hrep : repeated (80-r.val) 8 < 18446744073709551616 := by
   have hb := repeated_bound 8 (80-r.val) (by omega)
   norm_num at hb
   exact hb
 simp only [Nat.mod_eq_of_lt hrep]
 rw [UScalar.bv_toNat]
 conv_lhs => lhs; lhs; rhs; lhs; rw [Nat.add_comm]
 unfold LexicalParseIntegerRadixSpec.digits8
 exact h

theorem is4_digits (r : Std.U32) (v : Std.U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
    ∃ out, lexical_parse_integer_radix_harness.is_4digits r v = .ok out ∧
      (out = true ↔ LexicalParseIntegerRadixSpec.digits4 r.val v.val) :=
  ⟨swar4 r.val v, is4_eq_swar r v hr, swar4_correct r v hr⟩

theorem is8_digits (r : Std.U32) (v : Std.U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10) :
    ∃ out, lexical_parse_integer_radix_harness.is_8digits r v = .ok out ∧
      (out = true ↔ LexicalParseIntegerRadixSpec.digits8 r.val v.val) :=
  ⟨swar8 r.val v, is8_eq_swar r v hr, swar8_correct r v hr⟩

end LexicalParseIntegerRadixProofs
