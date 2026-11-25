import MetricsProofs

open Aeneas Aeneas.Std Result ControlFlow
open toml_write.string

namespace TomlWriteVerification

private theorem valMk (b : BitVec 8) : (UScalar.mk b : U8).val = b.toNat := rfl

private theorem checkedIncrement (n : U8) (h : n.val + 1 < 256) :
    (n + 1#u8 : Result U8) = .ok (UScalar.ofNatCore (n.val + 1) h) := by
  change UScalar.tryMk .U8 (n.val + 1) = _
  simp [UScalar.tryMk, UScalar.tryMkOpt, h, Result.ofOption]

private theorem scalarMax (x y : U8) :
    (core.cmp.impls.OrdU8.max x y).val = max x.val y.val := by
  unfold core.cmp.impls.OrdU8.max
  simp only [UScalar.lt_equiv]
  split
  · exact (Nat.max_eq_left (by omega)).symm
  · exact (Nat.max_eq_right (by omega)).symm

private def nextQuote (q byte : U8) (previous : U8) : U8 :=
  if byte = q then UScalar.ofNatCore ((previous.val + 1) % 256) (Nat.mod_lt _ (by decide))
  else 0#u8

private def quoteMax (q byte high previous : U8) : U8 :=
  if byte = q then core.cmp.impls.OrdU8.max high (nextQuote q byte previous) else high

def isValueControl (b : U8) : Bool :=
  decide ((b.val ≤ 31 ∧ b.val ≠ 9 ∧ b.val ≠ 10) ∨ b.val = 127)

private def valueStep (m : ValueMetrics) (single double b : U8) : ValueMetrics :=
  ⟨quoteMax 39#u8 b m.max_seq_single_quotes single,
    quoteMax 34#u8 b m.max_seq_double_quotes double,
    m.escape_codes || isValueControl b, m.escape || (decide (b.val = 92)), m.newline || (decide (b.val = 10))⟩

set_option maxHeartbeats 1000000 in
private theorem valueBody (it : core.slice.iter.Iter U8) (m : ValueMetrics) (single double : U8)
    (hi : it.i < it.slice.len)
    (hs : it.slice[it.i] = 39#u8 → single.val + 1 < 256)
    (hd : it.slice[it.i] = 34#u8 → double.val + 1 < 256) :
    ValueMetrics.calculate_loop.body it m single double =
      .ok (.cont ({ it with i := it.i + 1 }, valueStep m single double it.slice[it.i],
        nextQuote 39#u8 it.slice[it.i] single, nextQuote 34#u8 it.slice[it.i] double)) := by
  simp only [ValueMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next,
    hi, ↓reduceDIte, bind_ok]
  generalize hb : it.slice[it.i] = byte at hs hd ⊢
  by_cases hsingle : byte = 39#u8 <;> by_cases hdouble : byte = 34#u8
  all_goals
    simp [hsingle, hdouble, checkedIncrement, hs, hd, valueStep, quoteMax, nextQuote,
      Nat.mod_eq_of_lt, lift, isValueControl, UScalar.le_equiv]
    repeat' (split <;> simp_all)
    all_goals simp_all [UScalar.eq_equiv, valMk]
  all_goals cases m; simp_all

/-- Length of the initial block consisting of copies of the given byte. -/
def leadingQuotes (quote : U8) : List U8 → Nat
  | [] => 0
  | byte :: rest => if byte = quote then leadingQuotes quote rest + 1 else 0

/-- Maximum initial block length over all suffixes. -/
def longestQuoteRun (quote : U8) : List U8 → Nat
  | [] => 0
  | byte :: rest => max (leadingQuotes quote (byte :: rest)) (longestQuoteRun quote rest)

private abbrev ValueView := Nat × Nat × Bool × Bool × Bool

private def view (m : ValueMetrics) : ValueView :=
  (m.max_seq_single_quotes.val, m.max_seq_double_quotes.val, m.escape_codes, m.escape, m.newline)

private def runFrom (quote : U8) (remaining : List U8) (previous high : Nat) : Nat :=
  max high (max (previous + leadingQuotes quote remaining) (longestQuoteRun quote remaining))

private theorem leading_le_longest (q : U8) (bytes : List U8) :
    leadingQuotes q bytes ≤ longestQuoteRun q bytes := by
  cases bytes <;> simp [leadingQuotes, longestQuoteRun]

private theorem increment_fits (q b : U8) (rest : List U8) (previous high : Nat)
    (h : runFrom q (b :: rest) previous high ≤ 255) (matchQuote : b = q) :
    previous + 1 < 256 := by
  simp only [runFrom, max_le_iff, leadingQuotes, matchQuote, ↓reduceIte] at h
  omega

private theorem runFrom_step (q b previous high : U8) (rest : List U8)
    (h : b = q → previous.val + 1 < 256) (hp : previous.val ≤ high.val) :
    runFrom q (b :: rest) previous.val high.val =
      runFrom q rest (nextQuote q b previous).val (quoteMax q b high previous).val := by
  by_cases hq : b = q
  · have hi := h hq
    simp only [runFrom, longestQuoteRun, leadingQuotes, hq, ↓reduceIte, quoteMax, nextQuote,
      Nat.mod_eq_of_lt hi, UScalar.ofNatCore_val_eq, scalarMax]
    omega
  · simp only [runFrom, longestQuoteRun, leadingQuotes, hq, ↓reduceIte, quoteMax, nextQuote,
      show (0#u8 : U8).val = 0 by rfl, Nat.add_zero, Nat.zero_add, Nat.zero_max]
    have hl := leading_le_longest q rest
    omega

private def expected (remaining : List U8) (m : ValueMetrics) (single double : U8) : ValueView :=
  (runFrom 39#u8 remaining single.val m.max_seq_single_quotes.val,
    runFrom 34#u8 remaining double.val m.max_seq_double_quotes.val,
    m.escape_codes || remaining.any isValueControl,
    m.escape || remaining.any (fun byte => decide (byte.val = 92)),
    m.newline || remaining.any (fun byte => decide (byte.val = 10)))

private theorem expected_step (byte : U8) (rest : List U8) (m : ValueMetrics) (s d : U8)
    (hs : byte = 39#u8 → s.val + 1 < 256) (hd : byte = 34#u8 → d.val + 1 < 256)
    (hsp : s.val ≤ m.max_seq_single_quotes.val) (hdp : d.val ≤ m.max_seq_double_quotes.val) :
    expected (byte :: rest) m s d =
      expected rest (valueStep m s d byte) (nextQuote 39#u8 byte s) (nextQuote 34#u8 byte d) := by
  unfold expected valueStep
  simp only [List.any_cons, Bool.or_assoc]
  rw [runFrom_step _ _ _ _ _ hs hsp, runFrom_step _ _ _ _ _ hd hdp]

private theorem nextQuote_le_max (q byte previous high : U8) :
    (nextQuote q byte previous).val ≤ (quoteMax q byte high previous).val := by
  unfold quoteMax
  split
  · simp only [scalarMax]
    exact Nat.le_max_right _ _
  · simp [nextQuote, *]

private theorem view_empty (m : ValueMetrics) (single double : U8)
    (hs : single.val ≤ m.max_seq_single_quotes.val) (hd : double.val ≤ m.max_seq_double_quotes.val) :
    expected [] m single double = view m := by
  simp [expected, view, runFrom, leadingQuotes, longestQuoteRun, Nat.max_eq_left hs,
    Nat.max_eq_left hd]

private theorem valueLoop (it : core.slice.iter.Iter U8) (m : ValueMetrics) (single double : U8)
    (hs : single.val ≤ m.max_seq_single_quotes.val) (hd : double.val ≤ m.max_seq_double_quotes.val)
    (hb1 : (expected (it.slice.val.drop it.i) m single double).1 ≤ 255)
    (hb2 : (expected (it.slice.val.drop it.i) m single double).2.1 ≤ 255) :
    WP.spec (ValueMetrics.calculate_loop it m single double)
      (fun out => view out = expected (it.slice.val.drop it.i) m single double) := by
  unfold ValueMetrics.calculate_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.1.slice.len - x.1.i)
    (inv := fun x => expected (x.1.slice.val.drop x.1.i) x.2.1 x.2.2.1 x.2.2.2 =
      expected (it.slice.val.drop it.i) m single double ∧
      x.2.2.1.val ≤ x.2.1.max_seq_single_quotes.val ∧
      x.2.2.2.val ≤ x.2.1.max_seq_double_quotes.val)
  · intro x hx
    rcases x with ⟨iter, metrics, previousSingle, previousDouble⟩
    rcases hx with ⟨he, hsp, hdp⟩
    simp only at he hsp hdp ⊢
    by_cases hi : iter.i < iter.slice.len
    · have hl : iter.i < iter.slice.val.length := hi
      rw [List.drop_eq_getElem_cons hl] at he
      let byte := iter.slice[iter.i]
      let rest := iter.slice.val.drop (iter.i + 1)
      change expected (byte :: rest) metrics previousSingle previousDouble = _ at he
      have h1 : (expected (byte :: rest) metrics previousSingle previousDouble).1 ≤ 255 := he ▸ hb1
      have h2 : (expected (byte :: rest) metrics previousSingle previousDouble).2.1 ≤ 255 := he ▸ hb2
      have hsingle := increment_fits 39#u8 byte rest previousSingle.val
        metrics.max_seq_single_quotes.val h1
      have hdouble := increment_fits 34#u8 byte rest previousDouble.val
        metrics.max_seq_double_quotes.val h2
      rw [valueBody iter metrics previousSingle previousDouble hi hsingle hdouble, WP.spec_ok]
      refine ⟨⟨?_, nextQuote_le_max _ _ _ _, nextQuote_le_max _ _ _ _⟩, ?_⟩
      · exact (expected_step byte rest metrics previousSingle previousDouble
          hsingle hdouble hsp hdp).symm.trans he
      · change iter.slice.len - (iter.i + 1) < iter.slice.len - iter.i
        omega
    · have hn : ¬ iter.i < iter.slice.val.length := hi
      have hl : iter.slice.val.length ≤ iter.i := by omega
      simp [ValueMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next, hn, WP.spec_ok]
      rw [List.drop_eq_nil_iff.mpr hl, view_empty _ _ _ hsp hdp] at he
      exact he
  · exact ⟨rfl, hs, hd⟩

def valueMetricsSpec (bytes : List U8) : Nat × Nat × Bool × Bool × Bool :=
  (longestQuoteRun 39#u8 bytes, longestQuoteRun 34#u8 bytes, bytes.any isValueControl,
    bytes.any (fun byte => decide (byte.val = 92)), bytes.any (fun byte => decide (byte.val = 10)))

private def emptyValueMetrics : ValueMetrics := ⟨0#u8, 0#u8, false, false, false⟩

private theorem expected_initial (bytes : List U8) :
    expected bytes emptyValueMetrics 0#u8 0#u8 = valueMetricsSpec bytes := by
  simp [expected, emptyValueMetrics, runFrom, valueMetricsSpec,
    Nat.max_eq_right (leading_le_longest _ _)]

private theorem valueTotal (value : Result ValueMetrics) (post : ValueMetrics → Prop)
    (h : WP.spec value post) : ∃ metrics, value = .ok metrics ∧ post metrics := by
  cases value with
  | ret metrics => exact ⟨metrics, rfl, (WP.spec_ok _).mp h⟩
  | vis effect resume => exact False.elim ((WP.spec_vis effect resume).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem value_metrics (s : Str)
    (singleFits : longestQuoteRun 39#u8 s.val ≤ 255)
    (doubleFits : longestQuoteRun 34#u8 s.val ≤ 255) :
    ∃ metrics, ValueMetrics.calculate s = .ok metrics ∧
      (metrics.max_seq_single_quotes.val, metrics.max_seq_double_quotes.val,
        metrics.escape_codes, metrics.escape, metrics.newline) = valueMetricsSpec s.val := by
  have h1 : (expected s.val emptyValueMetrics 0#u8 0#u8).1 ≤ 255 := by
    simpa only [expected_initial, valueMetricsSpec] using singleFits
  have h2 : (expected s.val emptyValueMetrics 0#u8 0#u8).2.1 ≤ 255 := by
    simpa only [expected_initial, valueMetricsSpec] using doubleFits
  have result := valueLoop ⟨s, 0⟩ emptyValueMetrics 0#u8 0#u8
    (by decide) (by decide) (by simpa only [List.drop_zero] using h1)
    (by simpa only [List.drop_zero] using h2)
  let computation := ValueMetrics.calculate_loop ⟨s, 0⟩ emptyValueMetrics 0#u8 0#u8
  have calculated : ValueMetrics.calculate s = computation := by
    simp only [ValueMetrics.calculate, ValueMetrics.new, core.str.Str.as_bytes,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
    erw [bind_ok]
    rfl
  obtain ⟨metrics, hm, hspec⟩ := valueTotal _ _ result
  exact ⟨metrics, calculated.trans hm, by simpa only [List.drop_zero, expected_initial, view] using hspec⟩

theorem string_constructor (s : Str)
    (singleFits : longestQuoteRun 39#u8 s.val ≤ 255)
    (doubleFits : longestQuoteRun 34#u8 s.val ≤ 255) :
    ∃ metrics, TomlStringBuilder.new s = .ok ⟨s, metrics⟩ ∧
      (metrics.max_seq_single_quotes.val, metrics.max_seq_double_quotes.val,
        metrics.escape_codes, metrics.escape, metrics.newline) = valueMetricsSpec s.val := by
  obtain ⟨metrics, hm, hspec⟩ := value_metrics s singleFits doubleFits
  exact ⟨metrics, by simp [TomlStringBuilder.new, hm], hspec⟩

private theorem valueLoop_unfold (it : core.slice.iter.Iter U8) (m : ValueMetrics)
    (single double : U8) :
    ValueMetrics.calculate_loop it m single double = (do
      let r ← ValueMetrics.calculate_loop.body it m single double
      match r with
      | .cont (it', m', single', double') => ValueMetrics.calculate_loop it' m' single' double'
      | .done m' => .ok m') := by
  unfold ValueMetrics.calculate_loop
  conv_lhs => rw [loop.eq_1]
  congr 1
  funext result
  cases result with
  | cont tuple => rcases tuple with ⟨_, _, _, _⟩; rfl
  | done output => rfl

private theorem counter_full (previous : U8) (h : ¬ previous.val + 1 < 256) :
    previous = 255#u8 := by
  apply UScalar.val_eq_imp
  have hb : previous.val < 256 := previous.hmax
  change previous.val = 255
  omega

private theorem valueLoop_overflow (it : core.slice.iter.Iter U8) (m : ValueMetrics)
    (single double : U8)
    (hs : single.val ≤ m.max_seq_single_quotes.val) (hd : double.val ≤ m.max_seq_double_quotes.val)
    (overflow : 255 < (expected (it.slice.val.drop it.i) m single double).1 ∨
      255 < (expected (it.slice.val.drop it.i) m single double).2.1) :
    ValueMetrics.calculate_loop it m single double = .fail .integerOverflow := by
  by_cases hi : it.i < it.slice.len
  · let byte := it.slice[it.i]
    by_cases hsingle : byte = 39#u8 → single.val + 1 < 256
    · by_cases hdouble : byte = 34#u8 → double.val + 1 < 256
      · let rest := it.slice.val.drop (it.i + 1)
        have hEq : expected (it.slice.val.drop it.i) m single double =
            expected rest (valueStep m single double byte)
              (nextQuote 39#u8 byte single) (nextQuote 34#u8 byte double) := by
          have hl : it.i < it.slice.val.length := hi
          rw [List.drop_eq_getElem_cons hl]
          exact expected_step byte rest m single double hsingle hdouble hs hd
        rw [hEq] at overflow
        rw [valueLoop_unfold, valueBody it m single double hi hsingle hdouble, bind_ok]
        exact valueLoop_overflow ({ it with i := it.i + 1 }) (valueStep m single double byte)
          (nextQuote 39#u8 byte single) (nextQuote 34#u8 byte double)
          (nextQuote_le_max _ _ _ _) (nextQuote_le_max _ _ _ _) overflow
      · have ⟨hbyte, hcount⟩ := not_imp.mp hdouble
        rw [valueLoop_unfold, counter_full double hcount,
          double_quote_overflow_step it m single hi hbyte, bind_fail]
    · have ⟨hbyte, hcount⟩ := not_imp.mp hsingle
      rw [valueLoop_unfold, counter_full single hcount,
        single_quote_overflow_step it m double hi hbyte, bind_fail]
  · exfalso
    have hn : ¬ it.i < it.slice.val.length := hi
    have hl : it.slice.val.length ≤ it.i := by omega
    rw [List.drop_eq_nil_iff.mpr hl, view_empty _ _ _ hs hd] at overflow
    have hS : m.max_seq_single_quotes.val < 256 := m.max_seq_single_quotes.hmax
    have hD : m.max_seq_double_quotes.val < 256 := m.max_seq_double_quotes.hmax
    change 255 < m.max_seq_single_quotes.val ∨ 255 < m.max_seq_double_quotes.val at overflow
    omega
termination_by it.slice.val.length - it.i
decreasing_by
  have hl : it.i < it.slice.val.length := hi
  omega

theorem string_constructor_overflow (s : Str)
    (overflow : 255 < longestQuoteRun 39#u8 s.val ∨ 255 < longestQuoteRun 34#u8 s.val) :
    TomlStringBuilder.new s = .fail .integerOverflow := by
  have he : 255 < (expected s.val emptyValueMetrics 0#u8 0#u8).1 ∨
      255 < (expected s.val emptyValueMetrics 0#u8 0#u8).2.1 := by
    simpa only [expected_initial, valueMetricsSpec] using overflow
  have failure := valueLoop_overflow ⟨s, 0⟩ emptyValueMetrics 0#u8 0#u8
    (by decide) (by decide) (by simpa only [List.drop_zero] using he)
  simp only [TomlStringBuilder.new, ValueMetrics.calculate, ValueMetrics.new,
    core.str.Str.as_bytes, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_ok]
  erw [bind_ok]
  erw [failure]
  simp

end TomlWriteVerification
