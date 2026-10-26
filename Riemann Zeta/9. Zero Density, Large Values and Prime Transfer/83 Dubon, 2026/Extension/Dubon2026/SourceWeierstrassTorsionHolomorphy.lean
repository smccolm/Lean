import Dubon2026.SourceWeierstrassTorsionTail

/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

/-- The actual Weierstrass function at the indicated torsion-point representative. -/
def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

/-- The explicit convergent Fourier expression for the actual torsion Weierstrass value. -/
def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

lemma wpTorsion_eq_wpTorsionSeries {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    wpTorsion N a₁ a₂ τ = wpTorsionSeries N a₁ a₂ τ :=
  weierstrassP_torsionPt_eq_tsum_prod τ ha₁ ha₂ h0

lemma one_sub_zetaN_pow_mul_qN_pow_ne_zero {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) {τ : ℂ} (hτ : 0 < τ.im) :
    1 - zetaN N ^ a₂ * qN N τ ^ a₁ ≠ 0 := by
  obtain ⟨-, -, hz⟩ := torsionPt_hyps ⟨τ, hτ⟩ ha₁ ha₂ h0
  rw [← cexp_two_pi_I_mul_torsionPt (by omega), sub_ne_zero]
  exact (cexp_two_pi_I_mul_ne_one hz).symm

lemma differentiable_qN (N : ℕ) : Differentiable ℂ (qN N) := by
  unfold qN; fun_prop

lemma differentiable_wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) :
    Differentiable ℂ (wpTail N a₁ a₂ p) := by
  unfold wpTail
  have := differentiable_qN N
  fun_prop

open Complex in

theorem differentiableOn_wpTorsionSeries {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    DifferentiableOn ℂ (wpTorsionSeries N a₁ a₂) {τ : ℂ | 0 < τ.im} := by
  intro τ₀ hτ₀

  set B : ℝ := τ₀.im / 2 with hB
  have hB0 : 0 < B := by simp only [Set.mem_setOf_eq] at hτ₀; positivity
  set U : Set ℂ := {τ : ℂ | B < τ.im} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτ₀U : τ₀ ∈ U := by
    simp only [hU, Set.mem_setOf_eq, hB]; simp only [Set.mem_setOf_eq] at hτ₀; linarith
  have hUsub : U ⊆ {τ : ℂ | 0 < τ.im} := fun τ hτ ↦ lt_trans hB0 hτ
  set ρ : ℝ := Real.exp (-(2 * π * B / N)) with hρ
  have hN : 0 < N := by omega
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff, neg_lt_zero]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have htail : DifferentiableOn ℂ (fun τ ↦ ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) U := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_wpTail_majorant (Real.exp_pos _).le hρ1)
      (fun p ↦ (differentiable_wpTail N a₁ a₂ p).differentiableOn) hUopen ?_
    intro p τ hτ
    refine (norm_wpTail_le ha₁ a₂ p (lt_trans hB0 hτ).le).trans ?_
    gcongr
    exact norm_qN_le_of_le_im N (le_of_lt hτ)
  have hhead : DifferentiableOn ℂ
      (fun τ ↦ zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2) U := by
    have := differentiable_qN N
    refine DifferentiableOn.div (by fun_prop) (by fun_prop) fun τ hτ ↦ pow_ne_zero _ ?_
    exact one_sub_zetaN_pow_mul_qN_pow_ne_zero ha₁ ha₂ h0 (hUsub hτ)
  have hall : DifferentiableOn ℂ (wpTorsionSeries N a₁ a₂) U := by
    unfold wpTorsionSeries
    exact DifferentiableOn.mul (differentiableOn_const _)
      ((hhead.add (differentiableOn_const _)).add htail)
  exact ((hall τ₀ hτ₀U).differentiableAt (hUopen.mem_nhds hτ₀U)).differentiableWithinAt

theorem mdifferentiable_wpTorsion {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpTorsion N a₁ a₂) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_wpTorsionSeries ha₁ ha₂ h0).congr fun τ hτ ↦ ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hτ]
  exact wpTorsion_eq_wpTorsionSeries ha₁ ha₂ h0 ⟨τ, hτ⟩


end
end Dubon2026.SourceFricke
