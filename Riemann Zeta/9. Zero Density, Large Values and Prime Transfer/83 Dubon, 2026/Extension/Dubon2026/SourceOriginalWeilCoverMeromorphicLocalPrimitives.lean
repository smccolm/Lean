import Dubon2026.SourceOriginalWeilCoverZeroResidueCoefficient
import Dubon2026.SourceOriginalWeilCoverMeromorphicCellPrimitives
import Dubon2026.SourceMeromorphicLocalLog

/-! DUB-17/18 -> cover Abel converse -> pole-avoiding local primitive atlas.
Restore a local logarithm using the existing native logarithm derivative.
The zero-residue case uses actual pole removal. Both cases give a primitive
of the literal cover coefficient on a constructed neighborhood. -/
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



open Metric
open MeromorphicPeriods (Lg hasDerivAt_Lg)

theorem cover_exists_logPrimitive {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      RadialMeromorphicPeriods.PolePos D S →
      ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      ∀ (r : R) (C : D.ιC) {c : ℂ}, c ∈ V C →
        (RadialMeromorphicPeriods.ρ D S residue C r ≠ 0 → c ≠ (D.cell C).R.q) →
        ∃ W : Set ℂ, IsOpen W ∧ c ∈ W ∧ ∀ w ∈ W,
          HasDerivAt (fun w => Ψ r C w + RadialMeromorphicPeriods.ρ D S residue C r * Lg (D.cell C).R.q c w)
            (CF (D.cell C).ζ (θ r) w) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP
  dsimp only
  intro r C c hc hcq
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  let ρr := RadialMeromorphicPeriods.ρ D S residue C r
  change (ρr ≠ 0 → c ≠ (D.cell C).R.q) at hcq
  change ∃ W : Set ℂ, IsOpen W ∧ c ∈ W ∧ ∀ w ∈ W,
    HasDerivAt (fun w => Ψ r C w + ρr * Lg (D.cell C).R.q c w) (CF (D.cell C).ζ (θ r) w) w
  by_cases hρ : ρr = 0
  · refine ⟨V C, hP.hVo C, hc, fun w hw => ?_⟩
    have h1 := hP.hΨ r C w hw
    rw [cover_regCoeff_eq_coeff_of_zero N n radicand baseDivisor hRadicand hOrders
      D hD S θ hθ hS r C hρ (hP.hVgood C hw)] at h1
    simpa only [hρ, zero_mul, add_zero] using h1
  · have hcq' := hcq hρ
    refine ⟨V C ∩ ball c ‖c - (D.cell C).R.q‖, (hP.hVo C).inter isOpen_ball,
      ⟨hc, mem_ball_self (norm_pos_iff.2 (sub_ne_zero.2 hcq'))⟩, fun w hw => ?_⟩
    have hwq : w ≠ (D.cell C).R.q := by
      intro he
      have h := hw.2
      rw [he, mem_ball, dist_comm, dist_eq_norm] at h
      exact lt_irrefl _ h
    have h1 := hP.hΨ r C w hw.1
    change HasDerivAt (Ψ r C)
      (residueSubtractedCoefficient (D.cell C).R.q ρr (CF (D.cell C).ζ (θ r)) w) w at h1
    rw [residueSubtractedCoefficient_of_ne _ _ _ hwq] at h1
    have h2 := (hasDerivAt_Lg (q := (D.cell C).R.q) hw.2).const_mul ρr
    convert h1.add h2 using 1
    field_simp
    ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
