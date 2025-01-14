/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.field.opposite from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Field structure on the multiplicative/additive opposite
-/

variable {α : Type*}

namespace MulOpposite

@[to_additive]
instance ratCast [RatCast α] : RatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

@[to_additive (attr := simp, norm_cast)]
theorem op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast

@[to_additive (attr := simp, norm_cast)]
theorem unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q :=
  rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero

instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  ratCast_mk a b hb h := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]
  qsmul := qsmulRec _

instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵐᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero

instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  ratCast_mk a b hb h := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv,
    unop_natCast, unop_intCast, div_eq_mul_inv]
  qsmul := _

instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵃᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end AddOpposite
