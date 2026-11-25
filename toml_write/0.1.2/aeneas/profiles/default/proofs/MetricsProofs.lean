import TomlWrite.Funs

open Aeneas Aeneas.Std Result ControlFlow
open toml_write.string

namespace TomlWriteVerification

private def bareByte (byte : U8) : Bool :=
  decide ((65 ≤ byte.val ∧ byte.val ≤ 90) ∨ (97 ≤ byte.val ∧ byte.val ≤ 122) ∨
    (48 ≤ byte.val ∧ byte.val ≤ 57) ∨ byte.val = 45 ∨ byte.val = 95)

private def keyControl (byte : U8) : Bool :=
  decide ((byte.val ≤ 31 ∧ byte.val ≠ 9) ∨ byte.val = 127)

private abbrev KeyFlags := Bool × Bool × Bool × Bool × Bool

private def keyStep (flags : KeyFlags) (byte : U8) : KeyFlags :=
  let (bare, single, double, controls, backslash) := flags
  (bare && bareByte byte, single || byte == 39#u8, double || byte == 34#u8,
    controls || keyControl byte, backslash || byte == 92#u8)

private theorem mkVal (b : BitVec 8) : (UScalar.mk b : U8).val = b.toNat := rfl

set_option maxHeartbeats 5000000 in
private theorem keyBody_cons (iter : core.slice.iter.Iter U8)
    (bare single double controls backslash : Bool) (h : iter.i < iter.slice.len) :
    KeyMetrics.calculate_loop.body iter bare single double controls backslash =
      .ok (.cont ({ iter with i := iter.i + 1 },
        keyStep (bare, single, double, controls, backslash) iter.slice[iter.i])) := by
  simp only [KeyMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next, h, ↓reduceDIte]
  generalize iter.slice[iter.i] = byte
  simp [keyStep, bareByte, keyControl, UScalar.le_equiv]
  repeat' (split <;> simp_all)
  all_goals simp_all [UScalar.eq_equiv, mkVal]

private theorem keyLoop (iter : core.slice.iter.Iter U8) (flags : KeyFlags) :
    WP.spec (KeyMetrics.calculate_loop iter flags.1 flags.2.1 flags.2.2.1
      flags.2.2.2.1 flags.2.2.2.2)
      (fun out => out = (iter.slice.val.drop iter.i).foldl keyStep flags) := by
  unfold KeyMetrics.calculate_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.1.slice.len - x.1.i)
    (inv := fun x => (x.1.slice.val.drop x.1.i).foldl keyStep x.2 =
      (iter.slice.val.drop iter.i).foldl keyStep flags)
  · intro x hx
    rcases x with ⟨it, b, b1, b2, b3, b4⟩
    simp only at hx ⊢
    by_cases hi : it.i < it.slice.len
    · rw [keyBody_cons it b b1 b2 b3 b4 hi, WP.spec_ok]
      constructor
      · change (it.slice.val.drop (it.i + 1)).foldl keyStep
          (keyStep (b, b1, b2, b3, b4) it.slice[it.i]) = _
        have hl : it.i < it.slice.val.length := hi
        rw [List.drop_eq_getElem_cons hl, List.foldl_cons] at hx
        exact hx
      · change it.slice.len - (it.i + 1) < it.slice.len - it.i
        omega
    · have hn : ¬ it.i < it.slice.val.length := hi
      have hl : it.slice.val.length ≤ it.i := by omega
      simp [KeyMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next, hn,
        WP.spec_ok]
      simpa [List.drop_eq_nil_iff.mpr hl] using hx
  · cases flags with
    | mk a tail =>
      rcases tail with ⟨b, c, d, e⟩
      rfl

private theorem eq_ok_of_spec_eq {T : Type} (value : Result T) (expected : T)
    (h : WP.spec value (fun out => out = expected)) :
    value = .ok expected := by
  cases value with
  | ret result => rw [WP.spec_ok] at h; subst result; rfl
  | vis effect resume => exact False.elim ((WP.spec_vis effect resume).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

private theorem keyFold (bytes : List U8) (bare single double controls backslash : Bool) :
    bytes.foldl keyStep (bare, single, double, controls, backslash) =
      (bare && bytes.all bareByte, single || bytes.any (· == 39#u8),
        double || bytes.any (· == 34#u8), controls || bytes.any keyControl,
        backslash || bytes.any (· == 92#u8)) := by
  induction bytes generalizing bare single double controls backslash with
  | nil => simp
  | cons byte rest ih =>
    simp [List.foldl_cons, keyStep, ih, Bool.and_assoc, Bool.or_assoc]

def keyMetricsSpec (s : Str) : KeyMetrics :=
  ⟨!s.val.isEmpty && s.val.all bareByte, s.val.any (· == 39#u8),
    s.val.any (· == 34#u8), s.val.any keyControl, s.val.any (· == 92#u8)⟩

private theorem decideNot (b : Bool) : decide (¬ b = true) = !b := by
  cases b <;> rfl

theorem key_metrics (s : Str) :
    KeyMetrics.calculate s = .ok (keyMetricsSpec s) := by
  unfold KeyMetrics.calculate keyMetricsSpec
  simp only [KeyMetrics.new, core.str.Str.is_empty, core.str.Str.as_bytes,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok,
    decideNot]
  erw [bind_ok]
  change (do
    let (bare, single, double, controls, backslash) ←
      KeyMetrics.calculate_loop ⟨s, 0⟩ (!s.val.isEmpty) false false false false
    ok (⟨bare, single, double, controls, backslash⟩ : KeyMetrics)) = _
  rw [eq_ok_of_spec_eq _ _ (keyLoop ⟨s, 0⟩ (!s.val.isEmpty, false, false, false, false))]
  simp [keyFold]

theorem key_constructor (s : Str) :
    TomlKeyBuilder.new s = .ok ⟨s, keyMetricsSpec s⟩ := by
  unfold TomlKeyBuilder.new
  simp [key_metrics]

theorem key_unquoted_after_new (s : Str) :
    (do let builder ← TomlKeyBuilder.new s; builder.as_unquoted) =
      .ok (if !s.val.isEmpty && s.val.all bareByte
        then some (⟨s, none⟩ : TomlKey) else none) := by
  simp [key_constructor, keyMetricsSpec, TomlKeyBuilder.as_unquoted]
  split <;> simp_all

private theorem addQuoteOverflow : (255#u8 + 1#u8 : Result U8) =
    .fail .integerOverflow := rfl

theorem single_quote_overflow_step (iter : core.slice.iter.Iter U8)
    (metrics : ValueMetrics) (double : U8) (h : iter.i < iter.slice.len)
    (byte : iter.slice[iter.i] = 39#u8) :
    ValueMetrics.calculate_loop.body iter metrics 255#u8 double =
      .fail .integerOverflow := by
  simp [ValueMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next,
    show iter.i < iter.slice.val.length from h, byte, addQuoteOverflow]

theorem double_quote_overflow_step (iter : core.slice.iter.Iter U8)
    (metrics : ValueMetrics) (single : U8) (h : iter.i < iter.slice.len)
    (byte : iter.slice[iter.i] = 34#u8) :
    ValueMetrics.calculate_loop.body iter metrics single 255#u8 =
      .fail .integerOverflow := by
  simp [ValueMetrics.calculate_loop.body, core.slice.iter.IteratorSliceIter.next,
    show iter.i < iter.slice.val.length from h, byte, addQuoteOverflow]

end TomlWriteVerification

