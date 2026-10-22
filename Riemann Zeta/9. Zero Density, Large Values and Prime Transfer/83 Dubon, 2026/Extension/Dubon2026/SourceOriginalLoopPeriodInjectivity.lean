import Dubon2026.SourceOriginalDiscretePeriodsOfLoops
import Dubon2026.SourcePeriodIntegerCorrection

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
Actual generating loops already form a real basis. Native dot-product duality
then proves injectivity of their regular-differential period matrix, discharging
the analytic injectivity premise of the raw reciprocity kernel calculation.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_loop_period_matrix_injective {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
      ∀ i, pathIntegral N (b i : Ω[F⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)) :
    Function.Injective (Matrix.mulVecLin
      (fun k i => pathIntegral N (b i : Ω[F⁄ℂ]) (Z k))) := by
  obtain ⟨B, hB, _⟩ := original_period_basis_of_generating_loops N b Pz Z hgen
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro c hc
  let ℓ : (Fin n → ℂ) →ₗ[ℝ] ℂ := (dotProductBilin ℂ ℂ c).restrictScalars ℝ
  have hℓ : ℓ = 0 := by
    apply B.ext
    intro k
    change ∑ i, c i * B k i = 0
    simp only [hB]
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using congrFun hc k
  funext i
  have h := LinearMap.congr_fun hℓ (Pi.single i 1)
  simpa [ℓ, dotProduct, Pi.single_apply] using h

end
end Dubon2026.SourceFunctionField.OriginalChart
