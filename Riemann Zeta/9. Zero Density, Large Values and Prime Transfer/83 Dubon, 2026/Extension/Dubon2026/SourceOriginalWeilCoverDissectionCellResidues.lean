import Dubon2026.SourceOriginalWeilCoverCellCenteredResidue
import Dubon2026.SourceRadialCellInteriors

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
weighted residue reciprocity. Reuse the centered planar residue theorem,
finite interval partition and exact constructed primitive jumps. These prove
the global identity with the actual algebraic residues and cell coordinates. -/
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open scoped Real

open scoped Classical in
theorem cover_weighted_cell_residue :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE))
    (_ : ∀ C P, P ∈ (D.cell C).ζ.source →
      AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0)
    (S : Finset (Place ℂ EE))
    (_ : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton)
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (θ : Ω[EE⁄ℂ]) (_ : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (_ : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ)
    (C : D.ιC) (Ψ : ℂ → ℂ) (_ : ∀ z ∈ (D.cell C).R.K, AnalyticAt ℂ Ψ z),
    IntervalIntegrable
      (fun φ => (CF (D.cell C).ζ θ ((D.cell C).R.loop φ) * Ψ ((D.cell C).R.loop φ)) *
        (D.cell C).R.loop' φ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π),
        (CF (D.cell C).ζ θ ((D.cell C).R.loop φ) * Ψ ((D.cell C).R.loop φ)) *
          (D.cell C).R.loop' φ) =
        2 * π * Complex.I * ∑ v ∈ S.filter (fun v => v ∈ (D.cell C).carrier),
          v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) * Ψ ((D.cell C).ζ v) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S hsep hcent θ hθpol hθreg C Ψ hΨ
  classical
  let T := S.filter (fun v => v ∈ (D.cell C).carrier)
  by_cases hT : T.Nonempty
  · obtain ⟨v, hvT⟩ := hT
    have hv := Finset.mem_filter.mp hvT
    obtain ⟨hvs, hvc⟩ := D.pole_center_on_carrier S hcent C v hv.1 hv.2
    have hreg : ∀ Q ∈ (D.cell C).carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ := by
      intro Q hQC hQv
      apply hθreg Q
      intro hQS
      exact hQv (hsep C ⟨hQC, hQS⟩ ⟨hv.2, hv.1⟩)
    have hsingle : T = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hvT, ?_⟩
      intro Q hQT
      have hQ := Finset.mem_filter.mp hQT
      exact hsep C ⟨hQ.2, hQ.1⟩ ⟨hv.2, hv.1⟩
    have hcalc := cover_cell_centered_weighted_residue N n radicand baseDivisor hRadicand hOrders (D.cell C) (hD C) v hvs hvc θ (hθpol v hv.1) hreg Ψ hΨ
    change _ ∧ _ = 2 * π * Complex.I * ∑ v ∈ T, _
    simpa only [hsingle, Finset.sum_singleton, hvc] using hcalc
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hreg : ∀ Q ∈ (D.cell C).carrier, 0 ≤ Q.ordDifferential θ := by
      intro Q hQC
      apply hθreg Q
      intro hQS
      have hQT : Q ∈ T := Finset.mem_filter.mpr ⟨hQS, hQC⟩
      rw [hTempty] at hQT
      exact Finset.notMem_empty Q hQT
    have ha : ∀ z ∈ (D.cell C).R.K,
        AnalyticAt ℂ (fun z => CF (D.cell C).ζ θ z * Ψ z) z := by
      intro z hz
      have hQ := (D.cell C).ζ.map_target ((D.cell C).hKt hz)
      have h := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders
        (D.cell C).ζ hQ (hD C _ hQ).1 (hD C _ hQ).2 θ
        (((D.cell C).ζ.symm z).mem_of_ord_nonneg (hreg _ ⟨z, hz, rfl⟩))).2
      rw [(D.cell C).ζ.right_inv ((D.cell C).hKt hz)] at h
      exact h.mul (hΨ z hz)
    have hcalc := (D.cell C).R.integral_eq_zero_of_analyticOnNhd _ ha
    change _ ∧ _ = 2 * π * Complex.I * ∑ v ∈ T, _
    simpa only [hTempty, Finset.sum_empty, mul_zero] using hcalc

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
