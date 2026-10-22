import Dubon2026.SourceOriginalChartPathIntegrals

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The actual Abel-Jacobi vector differs locally from the vector of analytic
chart primitives by a loop period. This supplies the local analytic input
for the full real span of the period lattice and Jacobi inversion. All
paths, integral laws and primitive existence are proved for the original
curve; only regularity of the given original differentials is required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem abelJacobiVec_chart_primitive {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ v : Place ℂ (modularFunctionFieldOver N ℂ)) (Φ : Fin n → ℂ → ℂ)
    (hΦ : ∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
      HasDerivAt (Φ i) (readDifferential N v (b i) z) z)
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    abelJacobiVec N b P₀ (placeFamily N v z) - abelJacobiVec N b P₀ v -
      (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N b := by
  obtain ⟨γ, hγ⟩ := exists_original_chart_path_integrals N b hb v Φ hΦ hz
  have hm := abelJacobiVec_sub_mem N b hb ((originalPath N P₀ v).trans γ)
  convert hm using 1
  funext i
  simp only [Pi.sub_apply, pathIntegral_trans N (hb i), hγ i, abelJacobiVec]
  ring

theorem exists_abelJacobiVec_chart_primitive {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ Φ : Fin n → ℂ → ℂ,
      (∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
        HasDerivAt (Φ i) (readDifferential N v (b i) z) z) ∧
      ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
        abelJacobiVec N b P₀ (placeFamily N v z) - abelJacobiVec N b P₀ v -
          (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N b := by
  choose Φ hΦ using fun i => exists_readDifferential_primitive_on_chart N v (b i) (hb i)
  exact ⟨Φ, hΦ, fun z hz => abelJacobiVec_chart_primitive N b hb P₀ v Φ hΦ hz⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
