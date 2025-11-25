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

theorem sub_borrow_spec (b0: U8) (src1 src2 dst: U64) (h: b0.val = 0 ∨ b0.val = 1):
  ∃ b1 r, sub_borrow b0 src1 src2 dst = ok (b1, r) ∧
  r.val - b1 * (2 ^ 64) = src1.val - src2.val - b0.val
:= by
  unfold sub_borrow
  progress* 
  <;> exists i1, tmp2
  <;> simp
  -- how do I know what to simp here?
  <;> simp only [core.num.U64.wrapping_sub] at *
  -- shouldn't this be automatic?
  <;> rewrite [tmp2_post, tmp1_post, i1_post, i_post]
  -- why is this not working? ;-)
  scalar_tac
