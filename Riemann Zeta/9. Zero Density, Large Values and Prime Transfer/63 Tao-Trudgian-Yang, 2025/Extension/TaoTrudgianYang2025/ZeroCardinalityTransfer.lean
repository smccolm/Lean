import TaoTrudgianYang2025.ClassicalSlabCardinalityTransfer
import TaoTrudgianYang2025.ZeroCardinalityAssembly
import TaoTrudgianYang2025.ZeroDensityExponent

/-!
# Actual endpoint-one zero-density transfer

The two uniform large-value predicates imply the paper's multiplicity-weighted
symmetric-rectangle zero-density bound. The zeta input here starts at one;
the separate printed endpoint-two theorem is not asserted by this module.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem isZeroDensityBound_of_uniform_largeValue_bounds
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueBound σ τ (B * τ))
    (hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueBound σ τ (B * τ)) :
    IsZeroDensityBound σ (B / (1 - σ)) := by
  intro ε hε
  obtain ⟨δ, hδ, _hσδ, C, _hC, hslab⟩ :=
    classicalSlabZeroCount_bound_of_uniform_largeValue_bounds σ B τ₀ hσ hσUpper.le
      hB hτ₀ hZeta hGeneral (ε / 2) (by linarith)
  obtain ⟨K, hK, hglobal⟩ := paperZeroCount_bound_of_eventual_slab_bound
    (σ - δ) (B + ε / 2) C (by linarith) hslab (ε / 2) (by linarith)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hglobal
  let Cfinal := max K T₀
  have hCfinal : 1 ≤ Cfinal := hK.trans (le_max_left _ _)
  refine ⟨Cfinal, hCfinal, δ, hδ, ?_⟩
  intro T hT
  have hp := hT₀ T ((le_max_right _ _).trans hT)
  have hTpos : 0 < T := zero_lt_one.trans_le (hCfinal.trans hT)
  have hexponent : B / (1 - σ) * (1 - σ) + ε = (B + ε / 2) + ε / 2 := by
    rw [div_mul_cancel₀ B (by linarith : 1 - σ ≠ 0)]
    ring
  rw [hexponent]
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg hTpos.le _))


end TaoTrudgianYang2025
