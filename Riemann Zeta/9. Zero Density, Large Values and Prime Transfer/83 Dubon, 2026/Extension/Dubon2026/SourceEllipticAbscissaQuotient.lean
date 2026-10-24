import Dubon2026.SourceEllipticVeluQuotient
import Dubon2026.SourceEllipticOddSummingStructure

/-! DUB-17/18 -> good reduction -> all-level exceptional-fiber census ->
successive cyclic quotients. Express the existing odd quotient coefficients
using only the distinct abscissae of its kernel. These are the same literal
Velu coefficients; the curve equation removes the ordinate dependence.
The finite-set formulation avoids irrelevant behavior on infinite subgroups.
Adapted from Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The ordinate-free T coefficient of the original Velu quotient. -/
def abscissaVeluT (x : R) : R := 6 * x ^ 2 + W.b₂ * x + W.b₄

/-- The ordinate-free W coefficient, using the original division polynomial. -/
def abscissaVeluW (x : R) : R := W.Ψ₂Sq.eval x + x * abscissaVeluT W x

theorem abscissaVeluT_eq (x y : R) : abscissaVeluT W x = veluT W x y :=
  (veluT_eq W x y).symm

theorem abscissaVeluW_eq {x y : R} (h : W.toAffine.Equation x y) :
    abscissaVeluW W x = veluW W x y := by
  rw [abscissaVeluW, veluW, ← veluU_eq_Ψ₂Sq_eval W h, abscissaVeluT_eq W x y]

/-- The actual odd Velu quotient written as sums over its distinct kernel abscissae. -/
def abscissaQuotient (S : Finset R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * ∑ x ∈ S, abscissaVeluT W x
  a₆ := W.a₆ - W.b₂ * (∑ x ∈ S, abscissaVeluT W x) -
    7 * ∑ x ∈ S, abscissaVeluW W x

/-- Removing ordinates preserves the literal quotient when the original abscissae are distinct. -/
theorem abscissaQuotient_image [DecidableEq R] (S : Finset (R × R))
    (heq : ∀ P ∈ S, W.toAffine.Equation P.1 P.2)
    (hinj : Set.InjOn Prod.fst (S : Set (R × R))) :
    abscissaQuotient W (S.image Prod.fst) = veluQuotient W S := by
  have hT : ∑ x ∈ S.image Prod.fst, abscissaVeluT W x = veluTSum W S := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun P _ => abscissaVeluT_eq W P.1 P.2
  have hW : ∑ x ∈ S.image Prod.fst, abscissaVeluW W x = veluWSum W S := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun P hP => abscissaVeluW_eq W (heq P hP)
  ext <;> simp only [abscissaQuotient, veluQuotient, hT, hW]

/-- The actual odd-order half-orbit quotient is already the abscissa quotient. -/
theorem abscissaQuotient_oddOrderSummingSet
    {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F)
    {P : V.toAffine.Point} {n : ℕ} (hP : addOrderOf P = 2 * n + 1) :
    abscissaQuotient V ((oddOrderSummingSet V P n).image Prod.fst) =
      veluQuotient V (oddOrderSummingSet V P n) := by
  have hs := isOddVeluSet_oddOrderSummingSet hP
  exact abscissaQuotient_image V _ hs.equation hs.x_injOn

end
end Dubon2026.SourceEllipticVelu
