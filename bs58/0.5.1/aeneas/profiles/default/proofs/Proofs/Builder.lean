import Bs58

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bs58

/-- Constructing an encoder stores the supplied input and alphabet and disables checks. -/
theorem encode_builder_new_spec {I : Type _}
    (asRef : core.convert.AsRef I (Slice Std.U8)) (input : I) (alpha : alphabet.Alphabet) :
    encode.EncodeBuilder.new asRef input alpha =
      Result.ok { input := input, alpha := alpha, check := Check.Disabled } := by
  rfl

/-- Replacing the encoder alphabet preserves its input and checksum setting. -/
theorem encode_builder_with_alphabet_spec {I : Type _}
    (asRef : core.convert.AsRef I (Slice Std.U8)) (builder : encode.EncodeBuilder I)
    (alpha : alphabet.Alphabet) :
    encode.EncodeBuilder.with_alphabet asRef builder alpha =
      Result.ok { builder with alpha := alpha } := by
  rfl

/-- Constructing a decoder stores the supplied input and alphabet and disables checks. -/
theorem decode_builder_new_spec {I : Type _}
    (asRef : core.convert.AsRef I (Slice Std.U8)) (input : I) (alpha : alphabet.Alphabet) :
    decode.DecodeBuilder.new asRef input alpha =
      Result.ok { input := input, alpha := alpha, check := Check.Disabled } := by
  rfl

/-- Replacing the decoder alphabet preserves its input and checksum setting. -/
theorem decode_builder_with_alphabet_spec {I : Type _}
    (asRef : core.convert.AsRef I (Slice Std.U8)) (builder : decode.DecodeBuilder I)
    (alpha : alphabet.Alphabet) :
    decode.DecodeBuilder.with_alphabet asRef builder alpha =
      Result.ok { builder with alpha := alpha } := by
  rfl

end bs58
