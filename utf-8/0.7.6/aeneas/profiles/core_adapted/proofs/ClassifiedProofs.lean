import CoreProofs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace ClassifiedProofs
@[step] theorem sub_spec (a b : Usize) (h : b.val ≤ a.val) :
 lift (a.checked_sub b) ⦃ out => ∃ z, out = some z ∧ z.val = a.val-b.val ⦄ := by
 have hh := Usize.checked_sub_bv_spec a b
 cases he : a.checked_sub b with
 | none => simp only [he] at hh; scalar_tac
 | some z =>
   simp only [he] at hh
   simp only [lift, spec_ok]
   exact ⟨z,rfl,hh.2.1⟩

def endpoint (n k : Nat) (c : core.result.Result Unit (Usize × Option Usize)) : Nat :=
 match c with
 | .Ok _ => n+k
 | .Err (p,e) => if p.val > 0 then p.val else match e with | none => n+k | some j => j.val
def tag (c : core.result.Result Unit (Usize × Option Usize)) : Option (core.result.Result Unit Unit) :=
 match c with
 | .Ok _ => some (.Ok ())
 | .Err (p,e) => if p.val > 0 then some (.Ok ()) else match e with | none => none | some _ => some (.Err ())
theorem classified_spec (s : utf8.Incomplete) (x : Slice U8)
 (c : core.result.Result Unit (Usize × Option Usize))
 (bound : s.buffer_len.val ≤ 4)
 (lo : s.buffer_len.val ≤ endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c)
 (hi : endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c ≤ s.buffer_len.val + min (4-s.buffer_len.val) x.val.length) :
 s.classified_offsets x c ⦃ out =>
 out.1.1.val = endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c - s.buffer_len.val ∧
 out.1.2 = tag c ∧
 out.2.buffer.val = CoreProofs.overwritten s.buffer.val x.val s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) ∧
 out.2.buffer_len.val = endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c ⦄ := by
 unfold utf8.Incomplete.classified_offsets
 step with CoreProofs.splice_prefix_spec s x bound as ⟨n,k,state,hn,hk,hlen,hbytes⟩
 step as ⟨sum,hsum⟩
 step as ⟨spliced,hspliced,hslength⟩
 have sumBound : s.buffer_len.val + min (4-s.buffer_len.val) x.val.length ≤ 4 := by omega
 cases c with
 | Ok u =>
   simp only [endpoint,tag] at *
   step with UScalar.cast_inBounds_spec .U8 spliced.len (by scalar_tac) as ⟨size,hsize⟩
   simp_all
 | Err e =>
   rcases e with ⟨p,e⟩
   simp only [endpoint,tag] at *
   by_cases hp : p > 0#usize
   · have hpv : p.val > 0 := by scalar_tac
     simp_all only [hp, hpv, ite_true]
     simp_all
     step with sub_spec p n (by scalar_tac) as ⟨o,z,ho,hz⟩
     simp only [ho]
     step
     step with UScalar.cast_inBounds_spec .U8 p (by scalar_tac) as ⟨size,hsize⟩
     simp_all
   · have hpv : ¬ p.val > 0 := by scalar_tac
     simp_all only [hp, hpv, ite_false]
     simp_all
     cases e with
     | none =>
       step with UScalar.cast_inBounds_spec .U8 spliced.len (by scalar_tac) as ⟨size,hsize⟩
       simp_all
     | some j =>
       step with sub_spec j n (by scalar_tac) as ⟨o,z,ho,hz⟩
       simp only [ho]
       step
       step with UScalar.cast_inBounds_spec .U8 j (by scalar_tac) as ⟨size,hsize⟩
       simp_all
theorem classified_total (s : utf8.Incomplete) (x : Slice U8)
 (c : core.result.Result Unit (Usize × Option Usize))
 (bound : s.buffer_len.val ≤ 4)
 (lo : s.buffer_len.val ≤ endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c)
 (hi : endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c ≤ s.buffer_len.val + min (4-s.buffer_len.val) x.val.length) :
 ∃ out, s.classified_offsets x c = .ok out ∧
 out.1.1.val = endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c - s.buffer_len.val ∧
 out.1.2 = tag c ∧
 out.2.buffer.val = s.buffer.val.take s.buffer_len.val ++ x.val.take (min (4-s.buffer_len.val) x.val.length) ++ s.buffer.val.drop (s.buffer_len.val + min (4-s.buffer_len.val) x.val.length) ∧
 out.2.buffer_len.val = endpoint s.buffer_len.val (min (4-s.buffer_len.val) x.val.length) c := by
 exact CoreProofs.total_of_spec _ _ (classified_spec s x c bound lo hi)
end ClassifiedProofs
#print axioms ClassifiedProofs.classified_total
