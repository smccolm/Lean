import Dubon2026.SourceAnalyticPowerCoordinate
import Dubon2026.SourceOriginalChartDifferentials

/-! DUB-17/18 -> actual Jacobian torsion -> Abel-Jacobi -> geometric dissection.
The original field's proved chart readings and exact orders give the source
normal coordinate around each zero. Regularity on the entire chart is obtained
from the existing regular-neighborhood theorem, rather than assumed.
Adapted from S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Manifold Topology
attribute [local instance] placeTopology placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_power_coordinate (v : Place ℂ F) {g : F}
    (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : originalPlaceEval N ℂ v g = 0) :
    ∃ (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ), 0 < ρ ∧
      v ∈ ζ.source ∧ ζ v = 0 ∧ ζ.target = ball 0 ρ ∧
      ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
        (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source) ∧
      (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
        deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) ∧
      ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧
        originalPlaceEval N ℂ P g = (ζ P) ^ (v.ord g).toNat := by
  have ho : 0 < v.ord g := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v hg hne).mp hg0
  have he : 0 < (v.ord g).toNat := by omega
  have hGe : meromorphicOrderAt (chartRead N v g) 0 = ((v.ord g).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg ho.le]
    exact meromorphicOrderAt_place_reading N v hne
  obtain ⟨H, hH0, hHzero, hHa, hHd, hHG⟩ :=
    AnalyticFiber.exists_power_coordinate (analyticAt_place_reading N v hg) he hGe
  obtain ⟨δ, hδ, hreg⟩ := exists_place_reading_regular_disk N v hg
  let ψ := (chartAt ℂ v).trans (H.restrOpen (ball 0 δ) isOpen_ball)
  have hψv : v ∈ ψ.source := by
    refine ⟨?_, ?_⟩
    · simpa only [extChartAt_source] using (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v)
    change extChartAt 𝓘(ℂ, ℂ) v v ∈ H.source ∩ ball 0 δ
    rw [extPlaceChart_self]
    exact ⟨hH0, mem_ball_self hδ⟩
  have hψ0 : ψ v = 0 := by
    change H (extChartAt 𝓘(ℂ, ℂ) v v) = 0
    rw [extPlaceChart_self, hHzero]
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    (ψ.open_target.mem_nhds (hψ0 ▸ ψ.map_source hψv))
  let ζ := ψ.trans (OpenPartialHomeomorph.ofSet (ball (0 : ℂ) ρ) isOpen_ball)
  have hkey : ∀ P ∈ ζ.source, P ∈ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      extChartAt 𝓘(ℂ, ℂ) v P ∈ H.source ∧ extChartAt 𝓘(ℂ, ℂ) v P ∈ ball 0 δ := by
    intro P hP
    rw [extChartAt_source]
    exact hP.1
  have hcoe : ∀ P, ζ P = H (extChartAt 𝓘(ℂ, ℂ) v P) := fun _ => rfl
  have hloc : ∀ z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target,
      (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) =ᶠ[𝓝 z] H := by
    intro z hz
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) v).mem_nhds hz] with u hu
    change ζ ((extChartAt 𝓘(ℂ, ℂ) v).symm u) = H u
    rw [hcoe, (extChartAt 𝓘(ℂ, ℂ) v).right_inv hu]
  refine ⟨ζ, ρ, hρ, ⟨hψv, ?_⟩, hψ0, ?_, ?_, ?_, ?_, ?_⟩
  · change ψ v ∈ ball 0 ρ
    rw [hψ0]
    exact mem_ball_self hρ
  · change ball (0 : ℂ) ρ ∩ (OpenPartialHomeomorph.ofSet (ball (0 : ℂ) ρ)
      isOpen_ball).symm ⁻¹' ψ.target = ball 0 ρ
    rw [OpenPartialHomeomorph.ofSet_symm]
    exact inter_eq_left.mpr hρsub
  · intro P hP
    exact (hkey P hP).1
  · rintro z ⟨P, hP, rfl⟩
    exact (hHa _ (hkey P hP).2.1).congr
      (hloc _ ((extChartAt 𝓘(ℂ, ℂ) v).map_source (hkey P hP).1)).symm
  · rintro z ⟨P, hP, rfl⟩
    rw [(hloc _ ((extChartAt 𝓘(ℂ, ℂ) v).map_source (hkey P hP).1)).deriv_eq]
    exact hHd _ (hkey P hP).2.1
  · intro P hP
    have hPs := (hkey P hP).1
    have hread : chartRead N v g (extChartAt 𝓘(ℂ, ℂ) v P) = originalPlaceEval N ℂ P g := by
      rw [← chartRead_eq_extChartAt, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hPs]
    refine ⟨?_, ?_⟩
    · have hr := hreg _ (mem_ball_zero_iff.mp (hkey P hP).2.2)
      rw [← extPlaceChart_symm_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hPs] at hr
      exact hr
    · rw [hcoe, ← hread]
      exact hHG _ (hkey P hP).2.1

end
end Dubon2026.SourceFunctionField.OriginalChart
