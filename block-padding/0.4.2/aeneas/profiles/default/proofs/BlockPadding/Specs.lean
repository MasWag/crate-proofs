import Std

/- Independent, byte-sequence specifications for block-padding 0.4.2.
   These definitions do not import or invoke extracted implementation functions.
   The implementation bridge maps each Rust u8 to its natural-number value. -/
namespace BlockPadding.Spec

inductive Algorithm where
  | zero | pkcs7 | iso10126 | ansiX923 | iso7816 | none
  deriving DecidableEq, Repr

def Bytes (b : List Nat) : Prop := ∀ x ∈ b, x < 256

def PadDomain (a : Algorithm) (b : List Nat) (p : Nat) : Prop :=
  match a with
  | .zero | .none => p ≤ b.length
  | .pkcs7 | .iso10126 | .ansiX923 => p < b.length ∧ b.length ≤ 255
  | .iso7816 => p < b.length

def Padded (a : Algorithm) (b : List Nat) (p : Nat) : List Nat :=
  match a with
  | .zero => b.take p ++ List.replicate (b.length - p) 0
  | .pkcs7 | .iso10126 =>
      b.take p ++ List.replicate (b.length - p) (b.length - p)
  | .ansiX923 =>
      b.take p ++ List.replicate (b.length - p - 1) 0 ++ [b.length - p]
  | .iso7816 => b.take p ++ [128] ++ List.replicate (b.length - p - 1) 0
  | .none => b

/-- Exact nonpanicking domain of the release's raw decoder, including errors. -/
def UnpadDomain (a : Algorithm) (b : List Nat) : Prop :=
  match a with
  | .pkcs7 | .iso10126 | .ansiX923 => 0 < b.length ∧ b.length ≤ 255
  | _ => True

/-- The maximal prefix remaining after removal of trailing zeros. -/
def ZeroPrefix (b : List Nat) (p : Nat) : Prop :=
  p ≤ b.length ∧ b.drop p = List.replicate (b.length - p) 0 ∧
  (p = 0 ∨ ∃ head x, b.take p = head ++ [x] ∧ x ≠ 0)

/-- Semantic acceptance and exact returned prefix length; includes every byte.
    A false predicate for every p means the API must return its ordinary Error,
    provided UnpadDomain holds. -/
def Accepted (a : Algorithm) (b : List Nat) (p : Nat) : Prop :=
  match a with
  | .zero => ZeroPrefix b p
  | .none => p = b.length
  | .pkcs7 =>
      ∃ n, 1 ≤ n ∧ n ≤ b.length ∧ n ≤ 255 ∧ p = b.length - n ∧
        b.drop p = List.replicate n n
  | .iso10126 =>
      ∃ n head, 1 ≤ n ∧ n ≤ b.length ∧ n ≤ 255 ∧
        p = b.length - n ∧ b = head ++ [n]
  | .ansiX923 =>
      ∃ n, 1 ≤ n ∧ n ≤ b.length ∧ n ≤ 255 ∧ p = b.length - n ∧
        b.drop p = List.replicate (n - 1) 0 ++ [n]
  | .iso7816 =>
      p < b.length ∧ b.drop p = [128] ++ List.replicate (b.length - p - 1) 0

def Rejected (a : Algorithm) (b : List Nat) : Prop := ¬ ∃ p, Accepted a b p

/-- Empty-input behavior of block-list decoding differs from raw decoding. -/
def BlocksAccepted (a : Algorithm) (blocks : List (List Nat)) (p : Nat) : Prop :=
  match a with
  | .zero => ZeroPrefix blocks.flatten p
  | .none => p = blocks.flatten.length
  | _ => ∃ initial last q, blocks = initial ++ [last] ∧
      Accepted a last q ∧ p = initial.flatten.length + q

inductive Detached where
  | pad (blocks : List (List Nat)) (tail : List Nat)
  | noPad (blocks : List (List Nat))
  | error
  deriving DecidableEq, Repr

/-- Positive block width and valid full-block split are separate premises.
    The relation specifies result variants, unchanged full blocks, and exact tail. -/
def DetachedResult (a : Algorithm) (width : Nat) (data : List Nat)
    (result : Detached) : Prop :=
  ∃ blocks tail, (∀ b ∈ blocks, b.length = width) ∧ tail.length < width ∧
    data = blocks.flatten ++ tail ∧
    match a with
    | .none => if tail = [] then result = .noPad blocks else result = .error
    | .zero => if tail = [] then result = .noPad blocks else
        result = .pad blocks (tail ++ List.replicate (width - tail.length) 0)
    | _ => result = .pad blocks
        (Padded a (tail ++ List.replicate (width - tail.length) 0) tail.length)

end BlockPadding.Spec
