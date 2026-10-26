import Dubon2026.SourceWeierstrassLatticeRows

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

/-- The standard complex root of unity for the positive level. -/
def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

/-- The actual complex Fourier parameter of width N. -/
def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _
lemma qN_ne_zero (N : ℕ) (τ : ℂ) : qN N τ ≠ 0 := Complex.exp_ne_zero _

lemma qN_pow_self {N : ℕ} (hN : N ≠ 0) (τ : ℂ) : qN N τ ^ N = cexp (2 * π * I * τ) := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [qN, ← Complex.exp_nat_mul]
  congr 1
  field_simp

lemma cexp_two_pi_I_mul_torsionPt {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (τ : ℂ) :
    cexp (2 * π * I * ((a₁ * τ + a₂) / N)) = zetaN N ^ a₂ * qN N τ ^ a₁ := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [zetaN, qN, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

lemma norm_qN (N : ℕ) (τ : ℂ) : ‖qN N τ‖ = Real.exp (-(2 * π * τ.im / N)) := by
  rw [qN, Complex.norm_exp]
  congr 1
  rw [show 2 * (π : ℂ) * I * τ / N = (2 * π * I * τ) / (N : ℕ) from rfl, Complex.div_natCast_re]
  simp [mul_comm]
  ring

private lemma torsion_term_aux (ζ q : ℂ) (hq : q ≠ 0) (a₁ a₂ k m : ℕ) :
    ((ζ ^ a₂ * q ^ a₁) ^ m + (ζ ^ a₂ * q ^ a₁)⁻¹ ^ m - 2) * q ^ ((a₁ + k) * m) =
      ζ ^ (a₂ * m) * q ^ ((a₁ + k + a₁) * m) + ζ⁻¹ ^ (a₂ * m) * q ^ (k * m) -
        2 * q ^ ((a₁ + k) * m) := by
  have h2 : (ζ ^ a₂ * q ^ a₁)⁻¹ ^ m * q ^ ((a₁ + k) * m) = ζ⁻¹ ^ (a₂ * m) * q ^ (k * m) := by
    rw [mul_inv, mul_pow, ← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, add_mul, pow_add,
      mul_assoc]
    congr 1
    rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  linear_combination h2

open scoped UpperHalfPlane in

lemma torsionPt_hyps (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    -τ.im < (((a₁ : ℂ) * τ + a₂) / N).im ∧ (((a₁ : ℂ) * τ + a₂) / N).im < τ.im ∧
      ((a₁ : ℂ) * τ + a₂) / N ∈ Complex.integerComplement := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) ha₁
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ : 0 < τ.im := τ.im_pos
  have him : (((a₁ : ℂ) * τ + a₂) / N).im = a₁ * τ.im / N := by
    rw [Complex.div_natCast_im]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [him]
    have : (0 : ℝ) ≤ a₁ * τ.im / N := by positivity
    linarith
  · rw [him, div_lt_iff₀ hNr]
    have : (a₁ : ℝ) < N := by exact_mod_cast ha₁
    nlinarith
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have him' := congrArg Complex.im hn
    rw [him] at him'
    simp only [Complex.intCast_im] at him'
    have ha₁0 : a₁ = 0 := by
      rcases mul_eq_zero.mp ((div_eq_zero_iff.mp him'.symm).resolve_right hNr.ne') with h | h
      · exact_mod_cast h
      · exact absurd h hτ.ne'
    have ha₂0 : a₂ ≠ 0 := h0.resolve_left (not_not.mpr ha₁0)
    subst ha₁0
    rw [Complex.div_natCast_re] at hre
    simp only [Complex.intCast_re, Nat.cast_zero, zero_mul, zero_add, Complex.natCast_re] at hre
    rw [eq_div_iff hNr.ne'] at hre
    have h1 : (0 : ℝ) < n := by
      have : (0 : ℝ) < a₂ := by exact_mod_cast Nat.pos_of_ne_zero ha₂0
      nlinarith
    have h2 : (n : ℝ) < 1 := by
      have : (a₂ : ℝ) < N := by exact_mod_cast ha₂
      nlinarith
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega

open scoped UpperHalfPlane in

theorem weierstrassP_torsionPt_qExpansion (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N) =
      (2 * π * I) ^ 2 *
        (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (zetaN N ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N + a₁) * m) +
              (zetaN N)⁻¹ ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N - a₁) * m) -
                2 * qN N τ ^ ((c : ℕ) * N * m))) := by
  have hN : N ≠ 0 := by omega
  obtain ⟨hz₁, hz₂, hz⟩ := torsionPt_hyps τ ha₁ ha₂ h0
  rw [weierstrassP_periodPairOfTau_qExpansion τ hz₁ hz₂ hz, cexp_two_pi_I_mul_torsionPt hN,
    ← qN_pow_self hN]
  congr 2
  refine tsum_congr fun c ↦ tsum_congr fun m ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (c : ℕ) * N = a₁ + k :=
    ⟨(c : ℕ) * N - a₁, (Nat.add_sub_cancel' (le_trans ha₁.le (Nat.le_mul_of_pos_left N c.pos))).symm⟩
  rw [← pow_mul (qN N τ) N, show N * ((c : ℕ) * m) = ((c : ℕ) * N) * m by ring, hk,
    Nat.add_sub_cancel_left, mul_assoc, torsion_term_aux _ _ (qN_ne_zero N τ)]


end
end Dubon2026.SourceFricke
