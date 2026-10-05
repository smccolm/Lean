import DhimanKadiriQuesadaHerrera2026.ZetaTruncation

/-! # The first approximate functional equation with the exact source constant

The source's omitted unit term is repaired as documented in E01. The proof covers every
positive half-integer cutoff, including 1/2, and derives the approved Part-I weight hypotheses.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The exact m(c) of Theorem 9, with t₀ exposed as a parameter. -/
noncomputable def afeFirstConstant (c t₀ : ℝ) : ℝ :=
  c + (1 / Real.pi) * (1 / t₀ + 1) * afePartIFactor (1 / (2 * Real.pi * c))

/-- Theorem 9 with its source-intended positive-integer sum, including n=1.
All regularity and the accepted additional Part-I hypotheses are discharged for the actual weights. -/
theorem afe_first_kind {sigma t t₀ c : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hc : 1 / (2 * Real.pi) < c)
    (hhalf : ∃ k : ℤ, c * t = (k : ℝ) + 1 / 2) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) (c * t)‖ ≤
      afeFirstConstant c t₀ * (c * t) ^ (-sigma) := by
  have htpos : 0 < t := ht₀.trans_le ht
  have hπ : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := (one_div_pos.mpr hπ).trans hc
  have hx : 0 < c * t := mul_pos hcpos htpos
  have hcut : t / (2 * Real.pi) < c * t := by
    have he := mul_lt_mul_of_pos_right hc htpos
    convert he using 1
    ring
  have hu : 0 < 1 / (2 * Real.pi * c) := by positivity
  have hu1 : 1 / (2 * Real.pi * c) < 1 := by
    apply (div_lt_one (mul_pos hπ hcpos)).mpr
    have he := (div_lt_iff₀ hπ).mp hc
    nlinarith
  have hfactor := afePartIFactor_nonneg hu hu1
  have hratio : t / (2 * Real.pi) / (c * t) = 1 / (2 * Real.pi * c) := by
    field_simp
  have he := afe_zeta_sub_sum_sub_pole_bound hsigma.1 htpos hx hcut hhalf
  rw [hratio] at he
  have hp := norm_afe_pole_le (sigma := sigma) htpos hx
  rw [mul_div_cancel_right₀ c htpos.ne'] at hp
  have hst : sigma / t ≤ 1 / t₀ :=
    (div_le_div_of_nonneg_right hsigma.2 htpos.le).trans
      (div_le_div_of_nonneg_left zero_le_one ht₀ ht)
  have herr : (c * t) ^ (-sigma) / Real.pi * (1 + sigma / t) *
      afePartIFactor (1 / (2 * Real.pi * c)) ≤
      (c * t) ^ (-sigma) / Real.pi * (1 / t₀ + 1) *
        afePartIFactor (1 / (2 * Real.pi * c)) := by
    apply mul_le_mul_of_nonneg_right _ hfactor
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  calc
    _ ≤ ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
          sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) (c * t) -
          ((c * t : ℝ) : ℂ) ^ (1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) /
            (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)‖ +
        ‖((c * t : ℝ) : ℂ) ^ (1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) /
            (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)‖ := norm_le_norm_sub_add _ _
    _ ≤ (c * t) ^ (-sigma) / Real.pi * (1 / t₀ + 1) *
        afePartIFactor (1 / (2 * Real.pi * c)) + c * (c * t) ^ (-sigma) :=
      add_le_add (he.trans herr) hp
    _ = _ := by unfold afeFirstConstant; ring

/-- The digamma convention in m(c) is exactly the source's real Gamma logarithmic derivative. -/
theorem afeFirstConstant_eq_source {c : ℝ} (hc : 1 / (2 * Real.pi) < c) (t₀ : ℝ) :
    afeFirstConstant c t₀ = c + (1 / Real.pi) * (1 / t₀ + 1) *
      (Real.log (1 + 1 / (2 * Real.pi * c)) + Real.eulerMascheroniConstant -
        deriv Real.Gamma (1 - 1 / (2 * Real.pi * c)) /
          Real.Gamma (1 - 1 / (2 * Real.pi * c)) -
        1 / (2 * (1 + 1 / (2 * Real.pi * c))) - 1 / 2) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := (one_div_pos.mpr hπ).trans hc
  have hu : 1 / (2 * Real.pi * c) < 1 := by
    apply (div_lt_one (mul_pos hπ hcpos)).mpr
    have he := (div_lt_iff₀ hπ).mp hc
    nlinarith
  rw [afeFirstConstant, afePartIFactor, real_digamma_eq_deriv_Gamma_div (by linarith)]

/-- The smallest positive half-integer cutoff is included; its sharp positive sum is empty. -/
theorem afe_first_kind_small_cutoff {sigma t t₀ c : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hc : 1 / (2 * Real.pi) < c) (hcut : c * t = 1 / 2) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      afeFirstConstant c t₀ * (1 / 2 : ℝ) ^ (-sigma) := by
  have hh : ∃ k : ℤ, c * t = (k : ℝ) + 1 / 2 := ⟨0, by simpa using hcut⟩
  have he := afe_first_kind hsigma ht₀ ht hc hh
  rw [hcut] at he
  have hfloor : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  simpa only [sharpZetaSum, hfloor, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1),
    Finset.sum_empty, sub_zero] using he

end DhimanKadiriQuesadaHerrera2026
