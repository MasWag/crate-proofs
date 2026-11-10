import Std

/-! Independent mathematical specification of fxhash 0.2.1.
No generated function, Rust scalar operation, or execution-success assumption is
used here. Implementation bridges must additionally establish total success.
Byte arguments represent natural values below 256; states are fixed-width words.
-/
namespace FxHash.Spec

inductive Endian where
  | little | big
  deriving DecidableEq, Repr

def Bytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

def seed32 : BitVec 32 := BitVec.ofNat 32 0x27220a95
def seed64 : BitVec 64 := BitVec.ofNat 64 0x517cc1b727220a95

/-- Rotation, exclusive-or, then multiplication in the width-w word ring. -/
def mix {w : Nat} (seed h x : BitVec w) : BitVec w :=
  (h.rotateLeft 5 ^^^ x) * seed

def mix32 (h x : BitVec 32) : BitVec 32 := mix seed32 h x
def mix64 (h x : BitVec 64) : BitVec 64 := mix seed64 h x

/-- Positional value of a byte string, independent of machine reads. -/
def decodeLittle : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * decodeLittle bs

def decode (e : Endian) (bs : List Nat) : Nat :=
  match e with
  | .little => decodeLittle bs
  | .big => decodeLittle bs.reverse

/-- Tail segmentation: consume at most one block of each supplied size. -/
def tailWords (e : Endian) : List Nat → List Nat → List Nat
  | [], _ => []
  | k :: ks, bs =>
      if k ≤ bs.length then decode e (bs.take k) :: tailWords e ks (bs.drop k)
      else tailWords e ks bs

/-- All full blocks followed by the decreasing-size suffix partition. -/
def words (e : Endian) (blockSize : Nat) (tailSizes : List Nat)
    (bs : List Nat) : List Nat :=
  (List.range (bs.length / blockSize)).map
    (fun i => decode e ((bs.drop (i * blockSize)).take blockSize)) ++
  tailWords e tailSizes (bs.drop (bs.length / blockSize * blockSize))

/-- Release 0.2.1 mixes the final zero to three bytes individually. -/
def words32 (e : Endian) (bs : List Nat) : List Nat := words e 4 [1, 1, 1] bs
def words64 (e : Endian) (bs : List Nat) : List Nat := words e 8 [4, 1, 1, 1] bs

def write32 (e : Endian) (h : BitVec 32) (bs : List Nat) : BitVec 32 :=
  (words32 e bs).foldl (fun s x => mix32 s (BitVec.ofNat 32 x)) h

def write64 (e : Endian) (h : BitVec 64) (bs : List Nat) : BitVec 64 :=
  (words64 e bs).foldl (fun s x => mix64 s (BitVec.ofNat 64 x)) h

/-- A 64-bit integer write to a 32-bit state has low-word-first order. -/
def writeU64To32 (h : BitVec 32) (x : BitVec 64) : BitVec 32 :=
  mix32 (mix32 h (BitVec.ofNat 32 x.toNat))
    (BitVec.ofNat 32 (x.toNat / 2 ^ 32))

/-- A sequence of distinct calls; boundaries deliberately remain observable. -/
def writeCalls32 (e : Endian) (h : BitVec 32) (calls : List (List Nat)) : BitVec 32 :=
  calls.foldl (write32 e) h

def writeCalls64 (e : Endian) (h : BitVec 64) (calls : List (List Nat)) : BitVec 64 :=
  calls.foldl (write64 e) h

/-- Native-width mathematical scalar mix, independently reviewed against the
release constants: reducing seed64 to 32 bits gives seed32, and at 64 bits it is
unchanged. `System.Platform.numBits` is the Lean platform width used by Aeneas's
Usize representation. Relating this operation to Rust requires matching that width
to the extracted target (64 bits in this profile). This definition alone does not
specify the number of rounds for a wide integer write on a 32-bit Rust target. -/
def mixNative (h x : BitVec System.Platform.numBits) : BitVec System.Platform.numBits :=
  mix (BitVec.setWidth System.Platform.numBits seed64) h x

end FxHash.Spec
