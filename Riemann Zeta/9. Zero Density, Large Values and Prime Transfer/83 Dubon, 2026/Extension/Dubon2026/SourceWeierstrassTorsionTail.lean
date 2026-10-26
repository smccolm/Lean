import Dubon2026.SourceWeierstrassTorsionExpansion

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

lemma norm_zetaN (N : ℕ) : ‖zetaN N‖ = 1 := by
  rw [zetaN, Complex.norm_exp, show 2 * (π : ℂ) * I / N = (2 * π * I) / (N : ℕ) from rfl,
    Complex.div_natCast_re]
  simp

lemma norm_qN_le_one (N : ℕ) {τ : ℂ} (hτ : 0 ≤ τ.im) : ‖qN N τ‖ ≤ 1 := by
  rw [norm_qN, Real.exp_le_one_iff, neg_nonpos]
  positivity

lemma norm_qN_lt_one {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) : ‖qN N τ‖ < 1 := by
  rw [norm_qN, Real.exp_lt_one_iff, neg_lt_zero]
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

lemma norm_qN_le_of_le_im (N : ℕ) {B : ℝ} {τ : ℂ} (hτ : B ≤ τ.im) :
    ‖qN N τ‖ ≤ Real.exp (-(2 * π * B / N)) := by
  rw [norm_qN, Real.exp_le_exp, neg_le_neg_iff]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have : (0 : ℝ) < N := by exact_mod_cast hN
    gcongr

/-- The explicit paired-row Fourier summand at a torsion point. -/
def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

lemma norm_wpTail_le {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) (p : ℕ+ × ℕ+) {τ : ℂ} (hτ : 0 ≤ τ.im) :
    ‖wpTail N a₁ a₂ p τ‖ ≤ 4 * ((p.2 : ℕ) * ‖qN N τ‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  obtain ⟨c, m⟩ := p
  have hq1 := norm_qN_le_one N hτ
  have hcN : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
    have h1 : (c : ℕ) * (a₁ + 1) ≤ (c : ℕ) * N := Nat.mul_le_mul_left _ ha₁
    have h2 : a₁ ≤ (c : ℕ) * a₁ := Nat.le_mul_of_pos_left _ c.pos
    rw [mul_add, mul_one] at h1
    omega
  have e1 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N + a₁) * (m : ℕ) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have e2 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N - a₁) * (m : ℕ) := Nat.mul_le_mul_right _ hcN
  have e3 : (c : ℕ) * (m : ℕ) ≤ (c : ℕ) * N * (m : ℕ) := Nat.mul_le_mul_right _ (by nlinarith)
  have b1 : ‖qN N τ‖ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e1
  have b2 : ‖qN N τ‖ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e2
  have b3 : ‖qN N τ‖ ^ ((c : ℕ) * N * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e3
  have hz : ‖zetaN N‖ = 1 := norm_zetaN N
  set ρ : ℝ := ‖qN N τ‖ with hρ
  set A : ℂ := zetaN N ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) with hAdef
  set B : ℂ := (zetaN N)⁻¹ ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) with hBdef
  set C : ℂ := qN N τ ^ ((c : ℕ) * N * (m : ℕ)) with hCdef
  have hA : ‖A‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hAdef, norm_mul, norm_pow, hz, one_pow, one_mul, norm_pow]; exact b1
  have hB : ‖B‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hBdef, norm_mul, norm_pow, norm_inv, hz, inv_one, one_pow, one_mul, norm_pow]; exact b2
  have hC : ‖(2 : ℂ) * C‖ ≤ 2 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [norm_mul, Complex.norm_ofNat, hCdef, norm_pow]; linarith
  have hst : ‖A + B - 2 * C‖ ≤ 4 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    linarith [norm_sub_le (A + B) (2 * C), norm_add_le A B]
  change ‖((m : ℕ) : ℂ) * (A + B - 2 * C)‖ ≤ 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ)))
  rw [norm_mul, Complex.norm_natCast]
  calc ((m : ℕ) : ℝ) * ‖A + B - 2 * C‖ ≤ (m : ℕ) * (4 * ρ ^ ((c : ℕ) * (m : ℕ))) := by gcongr
    _ = 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ))) := by ring

lemma summable_wpTail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ 4 * ((p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have h := summable_prod_mul_pow 1 (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  refine (h.mul_left 4).congr fun p ↦ ?_
  simp

lemma summable_wpTail {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun p ↦ wpTail N a₁ a₂ p τ :=
  Summable.of_norm_bounded
    (summable_wpTail_majorant (norm_nonneg _) (norm_qN_lt_one (by omega) hτ))
    fun p ↦ norm_wpTail_le ha₁ a₂ p hτ.le

theorem weierstrassP_torsionPt_eq_tsum_prod (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N) =
      (2 * π * I) ^ 2 *
        (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
          ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) := by
  have hS := summable_wpTail ha₁ a₂ (τ := (τ : ℂ)) τ.im_pos
  rw [weierstrassP_torsionPt_qExpansion τ ha₁ ha₂ h0, hS.tsum_prod]
  congr 2
  refine tsum_congr fun c ↦ ?_
  set F : ℕ → ℂ := fun m ↦ (m : ℂ) *
    (zetaN N ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N + a₁) * m) +
      (zetaN N)⁻¹ ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N - a₁) * m) -
        2 * qN N τ ^ ((c : ℕ) * N * m)) with hF
  have hs : Summable F := summable_pnat_iff_summable_nat.mp (hS.prod_factor c)
  change ∑' m : ℕ, F m = ∑' m : ℕ+, F m
  rw [← tsum_zero_pnat_eq_tsum_nat hs]
  simp [hF]


end
end Dubon2026.SourceFricke
