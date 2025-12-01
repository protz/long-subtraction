import Aeneas
import LongSubtraction.Funs
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

def BigInt := Array U64 4#usize

@[simp, coe]
def toNat (x: BigInt) :=
  let x0: Nat := x.val[0]
  let x1: Nat := x.val[1]
  let x2: Nat := x.val[2]
  let x3: Nat := x.val[3]
  x0 + x1 * 2^64 + x2 * 2^(64*2) + x3 * 2^(64*3)

@[progress]
theorem sub_borrow_spec (b0: U8) (src1 src2 dst: U64) (h: b0.val = 0 ∨ b0.val = 1):
  ∃ b1 r, sub_borrow b0 src1 src2 dst = ok (b1, r) ∧
  r.val - b1 * (2 ^ 64) = src1.val - src2.val - b0.val ∧
  (b1.val = 0 ∨ b1.val = 1)
:= by
  unfold sub_borrow
  progress* 
  <;> simp_all
  <;> simp_scalar
  scalar_tac

theorem sub_spec
  (b0 : U8) (src1 : Array U64 4#usize) (src2 : Array U64 4#usize)
  (dst : Array U64 4#usize) (h: b0.val = 0 ∨ b0.val = 1):
  ∃ b1 r, sub b0 src1 src2 dst = ok (b1, r) ∧
  toNat r - 2 ^ (64 * 4) * b1.val = toNat src1 - toNat src2 - b0.val
:= by
  unfold sub
  progress*
  simp_all
  simp_scalar
