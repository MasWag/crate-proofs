import Aeneas
import Specs
open Aeneas Aeneas.Std
namespace NumConvProof

theorem unsigned_cast_contract {s : UScalarTy} (t : UScalarTy) (x : UScalar s) :
  NumConvSpec.boundedCongruent t.numBits 0 (NumConvSpec.unsignedMax t.numBits)
    (x.val : Int) ((UScalar.cast t x).val : Int) := by
  unfold NumConvSpec.boundedCongruent NumConvSpec.inRange NumConvSpec.unsignedMax NumConvSpec.modulus
  constructor
  · have h := (UScalar.cast t x).hBounds
    constructor
    · omega
    · have hp : ((2 ^ t.numBits : Nat) : Int) = (2 : Int) ^ t.numBits := by simp
      omega
  · simp only [UScalar.cast_val_eq]
    norm_cast
    simp

theorem signed_cast_contract {s : IScalarTy} (t : IScalarTy) (x : IScalar s)
    (h : t.numBits ≤ s.numBits) :
  NumConvSpec.boundedCongruent t.numBits (NumConvSpec.signedMin t.numBits) (NumConvSpec.signedMax t.numBits)
    x.val (IScalar.cast t x).val := by
  unfold NumConvSpec.boundedCongruent NumConvSpec.inRange NumConvSpec.signedMin NumConvSpec.signedMax NumConvSpec.modulus
  constructor
  · have hb := (IScalar.cast t x).hBounds
    omega
  · simp only [IScalar.cast_val_eq, Nat.min_eq_left h]
    simpa using (Int.bmod_emod (x := x.val) (m := 2 ^ t.numBits))
end NumConvProof
