import Dubon2026.SourceEllipticComplexUniformization
import Dubon2026.SourceEllipticVeluAnalytic
import Dubon2026.SourceEllipticOddKernelNorm
import Dubon2026.SourceEllipticOddPointSurjective

/-! Actual odd norm maps in period coordinates. Native equality transport
and the already proved variable changes are used literally. These formulas
discharge the affine-germ hypothesis in SourceEllipticPeriodQuotientGerm,
needed for the odd-prime product identity on the DUB-17/18 dependency chain. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve WeierstrassCurve.Affine
open SourceEllipticVariableChange SourceEllipticFunctionField SourceEllipticVelu
open SourceEllipticVelu.OddDiscriminant.Algebra
open scoped PeriodPair
noncomputable section

theorem point_cast_some {W V : WeierstrassCurve ℂ} (h : W = V)
    {x y : ℂ} (hxy : W.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) h
      (Point.some x y hxy) = Point.some x y (h ▸ hxy) := by
  subst V
  rfl

variable (L M : PeriodPair) [(periodCurve L).IsElliptic]
variable (C D : VariableChange ℂ)
variable {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
variable (hQ : addOrderOf Q = 2 * n + 1)
variable (hD : veluQuotient (C • periodCurve L)
  (oddOrderSummingSet (C • periodCurve L) Q n) = D • periodCurve M)

/-- The actual odd ideal norm conjugated by actual period-model coordinate changes. -/
def periodOddNorm : (periodCurve L).toAffine.Point →+ (periodCurve M).toAffine.Point :=
  (variableChangeAddEquiv D (periodCurve M).toAffine).toAddMonoidHom.comp
    ((AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD).toAddMonoidHom.comp
      ((oddPointNorm (C • periodCurve L) hQ).comp
        (variableChangeAddEquiv C (periodCurve L).toAffine).symm.toAddMonoidHom))

theorem periodOddNorm_surjective : Function.Surjective (periodOddNorm L M C D hQ hD) :=
  (variableChangeAddEquiv D (periodCurve M).toAffine).surjective.comp
    ((AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD).surjective.comp
      ((oddPointNorm_surjective (C • periodCurve L) hQ).comp
        (variableChangeAddEquiv C (periodCurve L).toAffine).symm.surjective))

theorem periodOddNorm_affine {z : ℂ} (hz : z ∉ L.lattice)
    (hd : (hP (oddOrderSummingSet (C • periodCurve L) Q n) Prod.fst).eval
      (vcXInv C (℘[L] z)) ≠ 0) :
    ∃ h, periodOddNorm L M C D hQ hD (periodHom L z) =
      Point.some
        (vcX D (veluAffineX (C • periodCurve L)
          (oddOrderSummingSet (C • periodCurve L) Q n) (vcXInv C (℘[L] z))))
        (vcY D (veluAffineX (C • periodCurve L)
          (oddOrderSummingSet (C • periodCurve L) Q n) (vcXInv C (℘[L] z)))
          (veluAffineY (C • periodCurve L)
            (oddOrderSummingSet (C • periodCurve L) Q n)
              (vcXInv C (℘[L] z)) (vcYInv C (℘[L] z) (℘'[L] z / 2)))) h := by
  have hs : (C • periodCurve L).toAffine.Equation
      (vcXInv C (℘[L] z)) (vcYInv C (℘[L] z) (℘'[L] z / 2)) :=
    (equation_variableChange_iff _ _).mpr (by
      rw [vcX_vcXInv, vcY_vcYInv]
      exact periodCurve_equation L hz)
  change ∃ h, vcFun D (periodCurve M).toAffine
    (AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD
      (oddPointNorm (C • periodCurve L) hQ
        (vcInvFun C (periodCurve L).toAffine (periodPoint L z)))) = _
  rw [periodPoint_of_notMem L hz]
  simp only [vcInvFun]
  rw [oddPointNorm_some _ _ hQ hd, point_cast_some]
  exact ⟨(nonsingular_variableChange_iff _ _).mp
    (hD ▸ odd_veluAffine_nonsingular (C • periodCurve L) hs hQ hd), rfl⟩

theorem periodOddNorm_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    periodOddNorm L M C D hQ hD (periodHom L z) = 0 ↔
      (hP (oddOrderSummingSet (C • periodCurve L) Q n) Prod.fst).eval
        (vcXInv C (℘[L] z)) = 0 := by
  change (variableChangeAddEquiv D (periodCurve M).toAffine)
    (AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD
      (oddPointNorm (C • periodCurve L) hQ
        (vcInvFun C (periodCurve L).toAffine (periodPoint L z)))) = 0 ↔ _
  rw [map_eq_zero_iff _ (variableChangeAddEquiv D (periodCurve M).toAffine).injective,
    map_eq_zero_iff _ (AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD).injective,
    periodPoint_of_notMem L hz]
  exact oddPointNorm_some_eq_zero_iff _ _ hQ

end
end Dubon2026.SourceEllipticPeriod
