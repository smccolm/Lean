import Dubon2026.SourceEllipticAbscissaBaseChange
import Dubon2026.SourceEllipticCyclicAbscissae
import Dubon2026.SourceEllipticOddPointNormFormula
import Dubon2026.SourceEllipticVeluTwoPointMap

/-! Intrinsic x-coordinate formulas for the original prime quotient maps.
These are finite sums over the actual kernel abscissae and specialize under
field embeddings. They serve image-subgroup compatibility for composite
cyclic quotients in the DUB-17/18 all-level inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceEllipticFunctionField
open OddDiscriminant.Algebra
noncomputable section
variable {F K : Type*} [Field F] [Field K]

/-- The original odd quotient x-coordinate, expressed using kernel abscissae. -/
def abscissaQuotientX (W : WeierstrassCurve F) (S : Finset F) (x : F) : F :=
  x + ∑ r ∈ S, (abscissaVeluT W r / (x - r) + W.Ψ₂Sq.eval r / (x - r) ^ 2)

/-- The original degree-two quotient x-coordinate on its singleton abscissa set. -/
def twoAbscissaQuotientX (W : WeierstrassCurve F) (S : Finset F) (x : F) : F :=
  x + ∑ r ∈ S, twoAbscissaG W r / (x - r)

/-- Removing kernel ordinates preserves the actual odd quotient x-coordinate. -/
theorem abscissaQuotientX_image [DecidableEq F]
    (W : WeierstrassCurve F) (S : Finset (F × F))
    (heq : ∀ P ∈ S, W.toAffine.Equation P.1 P.2)
    (hinj : Set.InjOn Prod.fst (S : Set (F × F))) (x : F) :
    abscissaQuotientX W (S.image Prod.fst) x = veluAffineX W S x := by
  simp only [abscissaQuotientX, veluAffineX, Xv, Finset.sum_image hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [abscissaVeluT_eq W P.1 P.2, ← veluU_eq_Ψ₂Sq_eval W (heq P hP)]

/-- The actual odd generator formula is the intrinsic subgroup formula. -/
theorem abscissaQuotientX_oddOrderSummingSet [DecidableEq F]
    (W : WeierstrassCurve F) (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} {n : ℕ} (hP : addOrderOf P = 2 * n + 1)
    (hPH : AddSubgroup.zmultiples P = H) (x : F) :
    abscissaQuotientX W (cyclicAbscissae W H) x =
      veluAffineX W (oddOrderSummingSet W P n) x := by
  rw [cyclicAbscissae_eq_oddOrderSummingSet W H hP hPH]
  have hs := isOddVeluSet_oddOrderSummingSet hP
  exact abscissaQuotientX_image W _ hs.equation hs.x_injOn x

/-- The intrinsic odd x-coordinate commutes with the original field embedding. -/
theorem abscissaQuotientX_map [DecidableEq K] (f : F →+* K)
    (W : WeierstrassCurve F) (S : Finset F) (x : F) :
    abscissaQuotientX (W.map f) (S.image f) (f x) = f (abscissaQuotientX W S x) := by
  simp only [abscissaQuotientX, Finset.sum_image f.injective.injOn, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  simp [map_abscissaVeluT, Ψ₂Sq, map_ofNat]

/-- The degree-two subgroup formula is the original quotient x-coordinate. -/
theorem twoAbscissaQuotientX_eq [DecidableEq F]
    (W : WeierstrassCurve F) (h2 : (2 : F) ≠ 0)
    (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} (hP : addOrderOf P = 2)
    (hPH : AddSubgroup.zmultiples P = H) (x : F) :
    twoAbscissaQuotientX W (cyclicAbscissae W H) x =
      velu2X W (coordsOrZero P).1 (coordsOrZero P).2 x := by
  rw [cyclicAbscissae_two_singleton W H hP hPH]
  simp only [twoAbscissaQuotientX, Finset.sum_singleton, velu2X, twoAbscissaG]
  rw [← two_torsion_y_eq W h2 hP]

/-- The intrinsic degree-two x-coordinate commutes with the original field embedding. -/
theorem twoAbscissaQuotientX_map [DecidableEq F] [DecidableEq K] (f : F →+* K)
    (W : WeierstrassCurve F) (S : Finset F) (x : F) :
    twoAbscissaQuotientX (W.map f) (S.image f) (f x) =
      f (twoAbscissaQuotientX W S x) := by
  simp only [twoAbscissaQuotientX, Finset.sum_image f.injective.injOn, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [map_div₀, map_sub, map_twoAbscissaG]

end
end Dubon2026.SourceEllipticVelu
