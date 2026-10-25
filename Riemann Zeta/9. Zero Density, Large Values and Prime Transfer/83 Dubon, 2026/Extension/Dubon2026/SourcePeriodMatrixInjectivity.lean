import Dubon2026.SourcePeriodIntegerCorrection

/-! DUB-17/18 -> cover Abel converse -> period correction. Integer coordinates
and vanishing real annihilators of the actual period subgroup imply injectivity
of the regular period matrix. This is exactly the finite linear calculation
needed by the cover; no real basis or lattice discreteness is constructed. -/
namespace Dubon2026.SourceFunctionField.PeriodCorrection
noncomputable section
open Matrix

theorem matrix_mulVecLin_injective_of_period_annihilator {kDim : ℕ}
    (M : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim) ℂ)
    (Λ : Submodule ℤ (Fin kDim → ℂ))
    (hcoord : ∀ u ∈ Λ, ∃ κ : Fin kDim ⊕ Fin kDim → ℤ,
      u = fun i => ∑ k, (κ k : ℂ) * M k i)
    (hann : ∀ ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ, (∀ u ∈ Λ, ℓ u = 0) → ℓ = 0) :
    Function.Injective M.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro c hc
  let L : (Fin kDim → ℂ) →ₗ[ℝ] ℂ := (dotProductBilin ℂ ℂ c).restrictScalars ℝ
  have hL : ∀ u ∈ Λ, L u = 0 := by
    intro u hu
    obtain ⟨κ, rfl⟩ := hcoord u hu
    change (∑ i, c i * (∑ k, (κ k : ℂ) * M k i)) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    have hk : (∑ i, M k i * c i) = 0 := congrFun hc k
    calc
      _ = (κ k : ℂ) * (∑ i, M k i * c i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hk, mul_zero]
  have hR : Complex.reCLM.toLinearMap.comp L = 0 := by
    apply hann
    intro u hu
    change (L u).re = 0
    rw [hL u hu, Complex.zero_re]
  have hI : Complex.imCLM.toLinearMap.comp L = 0 := by
    apply hann
    intro u hu
    change (L u).im = 0
    rw [hL u hu, Complex.zero_im]
  have hL0 : L = 0 := by
    apply LinearMap.ext
    intro u
    exact Complex.ext (LinearMap.congr_fun hR u) (LinearMap.congr_fun hI u)
  funext i
  have hi := LinearMap.congr_fun hL0 (Pi.single i 1)
  simpa [L, dotProduct, Pi.single_apply] using hi

end
end Dubon2026.SourceFunctionField.PeriodCorrection
