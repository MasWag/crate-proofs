module
public import Aeneas

@[expose] public section

open Aeneas Aeneas.Std

def core.str.Str.as_bytes (s : Str) : Result (Slice U8) := .ok s

def core.str.Str.is_empty (s : Str) : Result Bool := .ok (s.val.isEmpty)
