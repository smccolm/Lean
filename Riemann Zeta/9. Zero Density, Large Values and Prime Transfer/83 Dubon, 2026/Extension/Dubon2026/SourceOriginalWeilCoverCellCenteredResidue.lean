import Dubon2026.SourceOriginalWeilCoverCellResidues
import Dubon2026.SourceOriginalWeilCoverWeightedArcIntegral
import Dubon2026.SourceCellCenteredResidue

/-! DUB-17/18 -> cover Abel converse -> global weighted residue reciprocity.
Apply the existing planar centered residue theorem to the literal cover
coefficient and the proved actual rational-residue expansion. -/
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

theorem cover_cell_analyticAt_coeff_off_center :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (v : Place ℂ EE) (θ : Ω[EE⁄ℂ]), C.ζ v = C.R.q →
      (∀ Q ∈ C.carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ) →
      ∀ {z : ℂ}, z ∈ C.R.K → z ≠ C.R.q → AnalyticAt ℂ (CF C.ζ θ) z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC v θ hcenter hθreg z hz hn
  have hQ := C.ζ.map_target (C.hKt hz)
  have hreg : 0 ≤ (C.ζ.symm z).ordDifferential θ := by
    apply hθreg _ ⟨z, hz, rfl⟩
    intro he
    apply hn
    rw [← C.ζ.right_inv (C.hKt hz), he, hcenter]
  have h := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders C.ζ hQ
    (hC _ hQ).1 (hC _ hQ).2 θ ((C.ζ.symm z).mem_of_ord_nonneg hreg)).2
  rw [C.ζ.right_inv (C.hKt hz)] at h
  exact h

theorem cover_cell_centered_weighted_residue :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (v : Place ℂ EE), v ∈ C.ζ.source → C.ζ v = C.R.q →
      ∀ (θ : Ω[EE⁄ℂ]), -1 ≤ v.ordDifferential θ →
      (∀ Q ∈ C.carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ) →
      ∀ (Ψ : ℂ → ℂ), (∀ z ∈ C.R.K, AnalyticAt ℂ Ψ z) →
      IntervalIntegrable (fun φ => (CF C.ζ θ (C.R.loop φ) * Ψ (C.R.loop φ)) * C.R.loop' φ)
        volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), (CF C.ζ θ (C.R.loop φ) * Ψ (C.R.loop φ)) * C.R.loop' φ) =
        2 * π * Complex.I *
          (v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
            (v.uniformizer * v.differentialCoeff θ) * Ψ C.R.q) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC v hv hcenter θ hθ hθreg Ψ hΨ
  let r := v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ)
  apply C.R.centered_residue (fun z => CF C.ζ θ z * Ψ z) (r * Ψ C.R.q)
  · exact fun z hz hn => (cover_cell_analyticAt_coeff_off_center N n radicand baseDivisor hRadicand hOrders C hC v θ hcenter hθreg hz hn).mul (hΨ z hz)
  · obtain ⟨g, hga, hge⟩ := cover_coeff_simple_pole N n radicand baseDivisor hRadicand hOrders C.ζ hv (hC v hv).1 (hC v hv).2 θ hθ
    rw [hcenter] at hga hge
    have hΨ0 := hΨ C.R.q C.R.center_mem_K
    refine ⟨fun z => r * dslope Ψ C.R.q z + g z * Ψ z,
      (analyticAt_const.mul (analyticAt_dslope hΨ0)).add (hga.mul hΨ0), ?_⟩
    filter_upwards [hge, self_mem_nhdsWithin] with z hz hne
    have hn : z - C.R.q ≠ 0 := sub_ne_zero.mpr hne
    have hs := sub_smul_dslope Ψ C.R.q z
    rw [smul_eq_mul] at hs
    have he : Ψ z = Ψ C.R.q + (z - C.R.q) * dslope Ψ C.R.q z := by
      rw [hs]
      ring
    rw [hz]
    change (r / (z - C.R.q) + g z) * Ψ z = _
    rw [he]
    field_simp
    ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
