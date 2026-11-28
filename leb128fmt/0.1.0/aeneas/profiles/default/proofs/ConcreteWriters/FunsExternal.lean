module
public import ConcreteWriters.Types
public import WriterMaxLen
@[expose] public section
open Aeneas Aeneas.Std

namespace leb128fmt_writer_model

/-- The fixed writers call the release's max_len body, extracted separately
    to provide the generated external function. -/
def leb128fmt.max_len (width : U32) : Result Usize :=
  leb128fmt_writer_max_len.max_len width

/-- The pinned backend represents TryFromIntError as Unit. Erase exactly
    the generated IntErrorKind payload to that representation. The writer
    proofs discharge the successful conversion of every masked payload. -/
scoped instance : Coe core.num.error.IntErrorKind Aeneas.Std.core.num.error.TryFromIntError where
  coe _ := ()

end leb128fmt_writer_model
