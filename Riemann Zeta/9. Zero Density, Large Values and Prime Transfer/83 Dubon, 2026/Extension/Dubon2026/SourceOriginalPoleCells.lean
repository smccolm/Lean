import Dubon2026.SourceOriginalPoleCellGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> actual exterior pole cells.
A sufficiently large radial window has a reciprocal region within the proved
inverse-j chart scale. Its exact power pullbacks construct all original pole
cells, with full source arc geometry and exact exterior coverage.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The full source reciprocal geometry, including reversed arc intervals and images. -/
def RadialRecip.ReciprocalGeometry (W U : RadialRegion) : Prop :=
      U.q = 0 ∧ U.N = W.N ∧ (0 : ℂ) ∈ U.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ U.K ↔ w⁻¹ ∉ W.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ U.Kint ↔ w⁻¹ ∉ W.K)) ∧
      (∀ θ : ℝ, U.loop θ = (W.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin W.N ≃ Fin U.N,
        (∀ k : Fin W.N, U.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' W.arcIcc k) ∧
        (∀ k : Fin W.N, (fun w : ℂ => w⁻¹) '' U.arcSet (σ k) = W.arcSet k)

theorem exists_original_j_pole_cells :
    ∃ B > 0, ∀ W : RadialRegion, W.q = 0 → 2 ≤ W.N → closedBall 0 B ⊆ W.Kint →
      ∃ (R : RadialRegion) (C : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → Cell N),
        RadialRecip.ReciprocalGeometry W R ∧
        (∀ v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0,
          (v : Place ℂ F) ∈ (C v).interior' ∧ (C v).ζ v = 0 ∧
          PowPullback.PowerGeometry R ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat (C v).R ∧
          ∀ P ∈ (C v).ζ.source, (jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
            originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = (C v).ζ P ^
              ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat) ∧
        (Pairwise fun v w => Disjoint (C v).carrier (C w).carrier) ∧
        ∀ P : Place ℂ F,
          (jOver N ℂ ∉ P.toValuationSubring ∨
            (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∉ W.Kint)) ↔
          ∃ v, P ∈ (C v).carrier := by
  obtain ⟨ε, hε, hcells⟩ := exists_original_j_inverse_cells N
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro W hW hN hlarge
  obtain ⟨R, hR⟩ := RadialRecip.exists_recip W hW
  have hsmall : R.K ⊆ ball 0 ε := reciprocal_region_small hε hR.2.2.2.1 hlarge
  have hNR : 2 ≤ R.N := by rw [hR.2.1]; exact hN
  obtain ⟨C, hC, hd, hx⟩ := hcells R hR.1 hNR hsmall
  refine ⟨R, C, hR, hC, hd, ?_⟩
  intro P
  exact (original_inverse_j_mem_reciprocal_iff N W R hW hR.1 hR.2.2.2.1 P).symm.trans (hx P)

end
end Dubon2026.SourceFunctionField.CellGeometry
