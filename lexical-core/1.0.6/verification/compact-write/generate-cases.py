#!/usr/bin/env python3.11
"""Generate kernel-checked literal proof scripts; no evaluation result is trusted."""
from pathlib import Path
import argparse
import sys

HERE = Path(__file__).resolve().parent
DEFAULT = HERE.parent.parent / "aeneas/profiles/compact_write/proofs/Cases.lean"


def generated():
    result = (HERE / "cases-prelude.lean.in").read_text()
    prefix = '  unfold decimal_u8\n  step\n'
    round_ = '  rw [loop_step _ _ _ (by scalar_tac)]\n  step\n  step\n  step\n  step\n  try unfold digit_to_char\n  step\n  step\n  step\n  step\n'
    finish = '  rw [loop_stop _ _ _ (by scalar_tac)]\n  step\n  step\n  try unfold digit_to_char\n  step\n  step\n  step\n  step\n  step\n  step\n  step\n  simp_all [digit_to_char.TABLE, List.setSlice!, List.slice]\n\n'
    for value in range(256):
        digits = [ord(c) for c in str(value)]
        size = len(digits)
        literal = "[" + ",".join(f"{c}#u8" for c in digits) + "]"
        result += f"""theorem case_{value:03d} (buffer : Slice U8) (h : 3 ≤ buffer.length) :
    decimal_u8 {value}#u8 buffer ⦃ out => out.1.val = {size} ∧
      out.2.val = {literal} ++ buffer.val.drop {size} ⦄ := by
"""
        result += prefix + round_ * (size - 1) + finish
    return result + "end CompactWriteProofs\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    content = generated()
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content)
    elif args.output.read_text() != content:
        sys.exit("case proof file does not match its reproducible generator")
    print("All 256 authored literal proof scripts match the generator.")


if __name__ == "__main__":
    main()
