import TaoTrudgianYang2025.SargosQuarticPrefixBlocks
import TaoTrudgianYang2025.SargosSlowPrefix

/-! Exact conjugation to the positive-quadratic phase, retaining its sextic correction. -/

noncomputable section

open Set GafniTao
open scoped BigOperators FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosQuarticDualPolynomial_neg_eq (α γ y : ℝ) :
    -sargosQuarticDualPolynomial α γ y =
      y^2*(1/(4*α))+y^4*(-γ/(16*α^4))+γ^2*y^6/(16*α^7) := by
  unfold sargosQuarticDualPolynomial
  ring

theorem sargosQuarticDualCharacter_eq_conj (α γ y : ℝ) :
    (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ) =
      conj (fordAdditiveCharacter
        (y^2*(1/(4*α))+y^4*(-γ/(16*α^4))+γ^2*y^6/(16*α^7))) := by
  rw [sargos_ford_character_eq_fourier,← sargosQuarticDualPolynomial_neg_eq,sargos_fourier_conj]

theorem sargosQuarticDualPrefix_eq_conj_slow (m H : ℕ) (α γ : ℝ) :
    sargosIntegerPrefix ((m:ℤ)+1) H (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ)) =
      conj (sargosSlowQuarticPrefix m H (fun _ => 1) (1/(4*α)) (-γ/(16*α^4))
        (fun y => γ^2*y^6/(16*α^7))) := by
  rw [sargosSlowQuarticPrefix,sargos_sum_Ioc_eq_integerPrefix]
  simp only [sargosIntegerPrefix,map_sum,one_mul,sargosQuarticDualCharacter_eq_conj]

theorem sargosQuarticDualBlockMaximum_eq_slow (m : ℕ) (α γ : ℝ) :
    sargosQuarticDualBlockMaximum m α γ =
      sargosSlowQuarticMaximum m (fun _ => 1) (1/(4*α)) (-γ/(16*α^4))
        (fun y => γ^2*y^6/(16*α^7)) := by
  unfold sargosQuarticDualBlockMaximum sargosIntegerPrefixMaximum sargosSlowQuarticMaximum
  apply Finset.sup'_congr _ rfl
  intro H hH
  rw [sargosQuarticDualPrefix_eq_conj_slow,Complex.norm_conj]

theorem sargosQuartic_source_le_two_slow_blocks :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (Δ α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ Δ → Δ ≤ 1/2 →
      α ∈ Icc Δ (2*Δ) → |γ| ≤ 1/(N : ℝ)^3 →
      let m := sargosQuarticRoundedDualScale N Δ
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤
        C*((1/Real.sqrt Δ)*
          (sargosSlowQuarticMaximum m (fun _ => 1) (1/(4*α)) (-γ/(16*α^4))
            (fun y => γ^2*y^6/(16*α^7))+
           sargosSlowQuarticMaximum (2*m) (fun _ => 1) (1/(4*α)) (-γ/(16*α^4))
            (fun y => γ^2*y^6/(16*α^7)))+(N : ℝ)^((1:ℝ)/4)) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_source_le_two_dual_blocks
  refine ⟨C,hC,?_⟩
  intro N Δ α γ hN hΔ hΔ₁ hα hγ m
  have hh := hsource N Δ α γ hN hΔ hΔ₁ hα hγ
  simpa only [sargosQuarticDualBlockMaximum_eq_slow] using hh

end TaoTrudgianYang2025

