import Dubon2026.SourceOriginalWeilCoverCellResidues
import Dubon2026.SourceOriginalWeilCoverCellRegularCoefficient
import Dubon2026.SourceRadialMeromorphicPoleNeighborhoods
import Dubon2026.SourceComplexResidueSubtractedCoefficient

/-! DUB-17/18 -> actual auxiliary point division -> cover Abel converse -> meromorphic
loop generation. Reuse the actual simple-pole expansion and radial pole geometry
to prove that subtracting the literal rational residue gives an analytic
coefficient throughout a common pole-excluded neighborhood. -/
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

/-- The literal actual cover coefficient with its cell residue subtracted. -/
def coverRegCoeff {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) →
      (R → Ω[EE⁄ℂ]) → R → D.ιC → ℂ → ℂ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ r C
  exact residueSubtractedCoefficient (D.cell C).R.q
    (RadialMeromorphicPeriods.ρ D S (fun v r =>
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
        (v.uniformizer * v.differentialCoeff (θ r))) C r)
    (CF (D.cell C).ζ (θ r))

theorem cover_analyticAt_coeff_of_regular :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ P ∈ ζ.source, AnalyticAt ℂ (ζ ∘ PF P) 0 ∧ deriv (ζ ∘ PF P) 0 ≠ 0) →
      ∀ (θ : Ω[EE⁄ℂ]) {w : ℂ}, w ∈ ζ.target →
        0 ≤ (ζ.symm w).ordDifferential θ → AnalyticAt ℂ (CF ζ θ) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ hζ θ w hw hθ
  have hQ := ζ.map_target hw
  have h := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders ζ hQ
    (hζ _ hQ).1 (hζ _ hQ).2 θ ((ζ.symm w).mem_of_ord_nonneg hθ)).2
  rwa [ζ.right_inv hw] at h

theorem cover_analyticAt_regCoeff {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
        (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
        RadialMeromorphicPeriods.PolePos D S →
        ∀ (r : R) (C : D.ιC) {w : ℂ}, w ∈ RadialMeromorphicPeriods.goodSet (S := S) C →
          AnalyticAt ℂ (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ r C) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS r C w hw
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  change AnalyticAt ℂ (residueSubtractedCoefficient (D.cell C).R.q
    (RadialMeromorphicPeriods.ρ D S residue C r) (CF (D.cell C).ζ (θ r))) w
  by_cases hwq : w = (D.cell C).R.q
  · subst w
    by_cases hpole : ∃ v ∈ S, v ∈ (D.cell C).interior'
    · obtain ⟨v, hv, hvC⟩ := hpole
      have hvq := (hS.center hv (RadialCell.interior_subset_carrier _ hvC)).2
      have hvs : v ∈ (D.cell C).ζ.source := by
        obtain ⟨z, hz, rfl⟩ := RadialCell.interior_subset_carrier _ hvC
        exact (D.cell C).ζ.map_target ((D.cell C).hKt hz)
      obtain ⟨G, hGa, hG⟩ := cover_coeff_simple_pole N n radicand baseDivisor hRadicand hOrders
        (D.cell C).ζ hvs (hD C v hvs).1 (hD C v hvs).2 (θ r) (hθ r v).1
      rw [hvq] at hGa hG
      have hρ : RadialMeromorphicPeriods.ρ D S residue C r = residue v r := by
        rw [RadialMeromorphicPeriods.ρ_eq_of_mem residue hS hv hvC]
      apply analyticAt_residueSubtractedCoefficient_center _ _ _ G hGa
      simpa only [hρ, residue] using hG
    · have hpole' : ∀ v ∈ S, v ∉ (D.cell C).interior' :=
        fun v hv hvC => hpole ⟨v, hv, hvC⟩
      have hρ : RadialMeromorphicPeriods.ρ D S residue C = 0 :=
        RadialMeromorphicPeriods.ρ_eq_zero residue hpole'
      have hreg : 0 ≤ ((D.cell C).ζ.symm (D.cell C).R.q).ordDifferential (θ r) := by
        refine (hθ r _).2 fun hv => hpole' _ hv ?_
        exact (RadialMeromorphicPeriods.goodSet_pole hS hw hv).1
      have ha := cover_analyticAt_coeff_of_regular N n radicand baseDivisor hRadicand hOrders
        (D.cell C).ζ (hD C) (θ r) hw.1 hreg
      apply analyticAt_residueSubtractedCoefficient_center _ _ _ _ ha
      exact Filter.Eventually.of_forall (fun _ => by simp only [hρ, Pi.zero_apply, zero_div, zero_add])
  · apply analyticAt_residueSubtractedCoefficient_of_ne _ _ _ hwq
    apply cover_analyticAt_coeff_of_regular N n radicand baseDivisor hRadicand hOrders
      (D.cell C).ζ (hD C) (θ r) hw.1
    refine (hθ r _).2 fun hv => hwq ?_
    exact (RadialMeromorphicPeriods.goodSet_pole hS hw hv).2

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
