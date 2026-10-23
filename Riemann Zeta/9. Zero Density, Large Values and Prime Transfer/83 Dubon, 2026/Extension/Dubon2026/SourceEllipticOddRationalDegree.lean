import Dubon2026.SourceEllipticOddKernelCoprime
import Dubon2026.SourceEllipticOddGenericCoordinate
import Dubon2026.SourceEllipticRationalDegree

/-! The explicit odd quotient has the required rational-coordinate degree.
Actual half-orbit geometry supplies distinct abscissae and nonzero tangent
terms, hence no numerator cancellation. The native rational-function degree
theorem then gives degree 2n+1. This is a necessary degree computation for the
odd quotient field map and cyclic modular-polynomial roots (DUB-17/18). -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped IntermediateField

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The literal polynomial quotient defining the Velu x-coordinate as a rational function. -/
noncomputable def ratFuncVeluX : RatFunc F :=
  algebraMap F[X] (RatFunc F)
    (AP S Prod.fst (fun P => veluT W P.1 P.2) (fun P => veluU W P.1 P.2)) /
      algebraMap F[X] (RatFunc F) (hP S Prod.fst ^ 2)

variable {W S} {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd half-orbit makes the quotient numerator and denominator coprime. -/
theorem isCoprime_odd_generic (hQ : addOrderOf Q = 2 * n + 1) :
    IsCoprime (AP (oddOrderSummingSet W Q n) Prod.fst (fun P => veluT W P.1 P.2)
      (fun P => veluU W P.1 P.2)) (hP (oddOrderSummingSet W Q n) Prod.fst ^ 2) := by
  have hS := isOddVeluSet_oddOrderSummingSet hQ
  apply isCoprime_AP_hP_sq
  · intro A hA B hB hab
    exact hS.x_injOn A hA B hB hab
  · intro A hA
    exact pow_ne_zero 2 (hS.gy_ne_zero A hA)

/-- The rational x-coordinate of the actual odd quotient defines an extension of the odd order. -/
theorem finrank_odd_ratFuncVeluX (hQ : addOrderOf Q = 2 * n + 1) :
    Module.finrank F⟮ratFuncVeluX W (oddOrderSummingSet W Q n)⟯ (RatFunc F) = 2 * n + 1 := by
  rw [ratFuncVeluX, finrank_ratFunc_div_of_coprime_monic (isCoprime_odd_generic hQ)
    ((hP_monic _ _).pow 2)]
  · exact odd_generic_numerator_degree hQ
  · rw [odd_generic_denominator_degree hQ, odd_generic_numerator_degree hQ]
    omega

/-- Finite dimensionality of that actual rational-coordinate extension is derived from its degree. -/
theorem finiteDimensional_odd_ratFuncVeluX (hQ : addOrderOf Q = 2 * n + 1) :
    FiniteDimensional F⟮ratFuncVeluX W (oddOrderSummingSet W Q n)⟯ (RatFunc F) :=
  .of_finrank_pos (by rw [finrank_odd_ratFuncVeluX hQ]; omega)

end Dubon2026.SourceEllipticVelu
