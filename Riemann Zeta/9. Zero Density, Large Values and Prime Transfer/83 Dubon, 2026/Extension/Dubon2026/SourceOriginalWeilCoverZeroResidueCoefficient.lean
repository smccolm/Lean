import Dubon2026.SourceOriginalWeilCoverRegularizedCoefficient
import Dubon2026.SourceOriginalWeilCoverSimplePoleSpaceFinite
import Dubon2026.SourceComplexZeroResidueCoefficient

/-! DUB-17/18 -> cover Abel converse -> pole-avoiding local primitive atlas.
Zero actual residue removes a possible simple pole. The already proved
analytic coefficient and removable-limit identity show that its regularized
coefficient equals the literal coefficient, including the cell center. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders



theorem cover_regCoeff_eq_coeff_of_zero {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      RadialMeromorphicPeriods.PolePos D S →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      ∀ (r : R) (C : D.ιC), RadialMeromorphicPeriods.ρ D S residue C r = 0 →
        ∀ {w : ℂ}, w ∈ RadialMeromorphicPeriods.goodSet (S := S) C →
          coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ r C w = CF (D.cell C).ζ (θ r) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS
  dsimp only
  intro r C hρ w hw
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  change RadialMeromorphicPeriods.ρ D S residue C r = 0 at hρ
  have hreg : 0 ≤ ((D.cell C).ζ.symm w).ordDifferential (θ r) := by
    by_cases hwS : (D.cell C).ζ.symm w ∈ S
    · have hint := (RadialMeromorphicPeriods.goodSet_pole hS hw hwS).1
      have hρv := congrFun (RadialMeromorphicPeriods.ρ_eq_of_mem residue hS hwS hint) r
      rw [hρ] at hρv
      apply cover_simple_pole_regular_of_residue_zero N n radicand _ _ (hθ r _).1
      rw [coverDifferentialResidue_simplePole N n radicand _ _ (hθ r _).1]
      exact hρv.symm
    · exact (hθ r _).2 hwS
  have ha := cover_analyticAt_coeff_of_regular N n radicand baseDivisor hRadicand hOrders
    (D.cell C).ζ (hD C) (θ r) hw.1 hreg
  change residueSubtractedCoefficient (D.cell C).R.q (RadialMeromorphicPeriods.ρ D S residue C r)
    (CF (D.cell C).ζ (θ r)) w = _
  rw [hρ]
  exact residueSubtractedCoefficient_zero _ _ ha.continuousAt

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
