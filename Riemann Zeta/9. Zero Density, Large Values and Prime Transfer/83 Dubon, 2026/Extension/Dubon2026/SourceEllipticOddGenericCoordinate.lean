import Dubon2026.SourceEllipticOddGenericPolynomials
import Dubon2026.SourceEllipticOddSummingStructure
import Dubon2026.SourceEllipticFunctionGeneric

/-! The actual odd quotient x-coordinate in the elliptic function field.
The existing cleared numerator, kernel denominator and actual half-orbit count
derive transcendence and their exact degrees in every characteristic. This
discharges the nonconstancy input to the odd quotient pullback (DUB-17/18);
the quotient equation, separability and exact cyclic kernel remain required. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The original finite Velu x-coordinate sum at the actual generic point. -/
noncomputable def genericVeluX : W.toAffine.FunctionField :=
  Xv S (fun P => algebraMap F W.toAffine.FunctionField P.1)
    (fun P => algebraMap F W.toAffine.FunctionField (veluT W P.1 P.2))
    (fun P => algebraMap F W.toAffine.FunctionField (veluU W P.1 P.2))
    (genericX W.toAffine)

/-- The generic coordinate sum equals the existing cleared polynomial quotient. -/
theorem genericVeluX_eq_ratio : genericVeluX W S =
    aeval (genericX W.toAffine) (AP S Prod.fst (fun P => veluT W P.1 P.2)
      (fun P => veluU W P.1 P.2)) /
      aeval (genericX W.toAffine) (hP S Prod.fst) ^ 2 :=
  (aeval_AP_div_eq_Xv S Prod.fst _ _ (transcendental_genericX W.toAffine)).symm

/-- No transcendence assumption is needed for the actual quotient coordinate. -/
theorem transcendental_genericVeluX : Transcendental F (genericVeluX W S) := by
  rw [genericVeluX_eq_ratio]
  exact transcendental_AP_div S Prod.fst _ _ (transcendental_genericX W.toAffine)

omit [DecidableEq F] in
/-- The actual generic kernel denominator is nonzero. -/
theorem generic_kernel_denominator_ne_zero :
    aeval (genericX W.toAffine) (hP S Prod.fst) ≠ 0 := by
  simpa using (transcendental_iff_injective.mp (transcendental_genericX W.toAffine)).ne
    (hP_monic S Prod.fst).ne_zero

variable {W S} {Q : W.toAffine.Point} {n : ℕ}

/-- The cleared numerator for an actual cyclic half-orbit has degree equal to the odd order. -/
theorem odd_generic_numerator_degree (hQ : addOrderOf Q = 2 * n + 1) :
    (AP (oddOrderSummingSet W Q n) Prod.fst (fun P => veluT W P.1 P.2)
      (fun P => veluU W P.1 P.2)).natDegree = 2 * n + 1 := by
  rw [natDegree_AP, card_oddOrderSummingSet hQ]

/-- The squared denominator for an actual cyclic half-orbit has degree twice its half size. -/
theorem odd_generic_denominator_degree (hQ : addOrderOf Q = 2 * n + 1) :
    (hP (oddOrderSummingSet W Q n) Prod.fst ^ 2).natDegree = 2 * n := by
  rw [(hP_monic _ _).natDegree_pow, natDegree_hP, card_oddOrderSummingSet hQ]

end Dubon2026.SourceEllipticVelu
