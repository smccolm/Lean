import TaoTrudgianYang2025.SargosLemmaOne

/-! Ordinary measurable-integral form of both source inequalities, with integrability derived. -/

noncomputable section

open MeasureTheory Set Filter

namespace TaoTrudgianYang2025

theorem sargosSlowQuartic_even_window_le_count {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K δ lambda : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hlambda : 0 < lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      (sargosSlowQuarticMaximum N z α γ (φ α γ))^(2*p)) ≤
      sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p)*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) := by
  have hi := integrable_sargosSlowQuarticPower (by omega : 1 ≤ N) (2*p) z hK
    c (c+δ) d (d+lambda) φ φ' hφ hφ' hm
  have hu := sargosSlowQuartic_upper_even_window_le_count hN hp z hz hK hδ hlambda
    c d φ φ' hφ hφ'
  rw [sargosUpperIntegral_ofReal_eq_integral hi
    (Eventually.of_forall (fun t => pow_nonneg
      (sargosSlowQuarticMaximum_nonneg N z t.1 t.2 (φ t.1 t.2)) (2*p))),
    integral_prod _ hi] at hu
  have hC := sargosWindowConstant_nonneg p hK
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu

theorem sargos_lemma_one {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ δ μ lambda : ℝ} (hK : 0 ≤ K) (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))) :
    ((∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      (sargosSlowQuarticMaximum N z α γ (φ α γ))^(2*p))/
      ((Real.log N)^(2*p)*δ*lambda) ≤
      sargosWindowConstant p K*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ)) ∧
    ((sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p))) := by
  have hδp := hΔ.trans_le hδ
  have hlambdap := hμ.trans_le hlambda
  constructor
  · have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    apply (div_le_iff₀ (by positivity : 0 < (Real.log N)^(2*p)*δ*lambda)).mpr
    convert sargosSlowQuartic_even_window_le_count hN hp z hz hK hδp hlambdap
      c d φ φ' hφ hφ' hm using 1
    ring
  · exact sargosMomentNearCount_window_le_central (by omega) p hΔ hμ hδ hlambda

theorem sargosSlowQuartic_even_window_transfer {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ δ μ lambda : ℝ} (hK : 0 ≤ K) (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      (sargosSlowQuarticMaximum N z α γ (φ α γ))^(2*p)) ≤
      (64*sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p)/(Δ*μ))*
        (∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
          ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p)) := by
  have hi := integrable_sargosSlowQuarticPower (by omega : 1 ≤ N) (2*p) z hK
    c (c+δ) d (d+lambda) φ φ' hφ hφ' hm
  have hu := sargosSlowQuartic_upper_even_window_transfer hN hp z hz hK hΔ hμ hδ hlambda
    c d φ φ' hφ hφ'
  rw [sargosUpperIntegral_ofReal_eq_integral hi
    (Eventually.of_forall (fun t => pow_nonneg
      (sargosSlowQuarticMaximum_nonneg N z t.1 t.2 (φ t.1 t.2)) (2*p))),
    integral_prod _ hi] at hu
  have hδp := hΔ.trans_le hδ
  have hlambdap := hμ.trans_le hlambda
  have hC := sargosWindowConstant_nonneg p hK
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hI : 0 ≤ ∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
      ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p) :=
    integral_nonneg (fun α => integral_nonneg (fun γ => pow_nonneg (norm_nonneg _) _))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu

end TaoTrudgianYang2025
