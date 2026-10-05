import DhimanKadiriQuesadaHerrera2026.SecondHalfErrors
import DhimanKadiriQuesadaHerrera2026.ChiBound

/-! # The source A/B error formulas for the actual AFE

All terms of the proof's A and B formulas are retained. The quantitative direct and
reflected estimates include both height signs and σ endpoints. Uniform A₀/B₀ estimates
and the source's equation-(5.2) branch discrepancy remain separate obligations.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The literal A expression in the proof of Theorem 10, before uniform parameter bounds. -/
noncomputable def afeSourceA (σ t x y : ℝ) : ℝ :=
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    (115 / (54 * Real.pi ^ 3)) * (t / x ^ 2) +
    7 / (4 * Real.pi * y) + 3 / (4 * Real.pi * (y + 1)) + 7 / (8 * Real.pi * y ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x) + (115 * σ) / (54 * Real.pi ^ 3 * x ^ 2) +
    σ / (4 * t) + σ / (2 * Real.pi * y ^ 2 * t) +
    (σ * Real.log 2) / (2 * Real.pi * t) + (3 * σ) / (4 * Real.pi * (y + 1) * t) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x * t)

/-- The literal exponentially small B expression uses the positive height magnitude. -/
noncomputable def afeSourceB (σ t y t₀ : ℝ) : ℝ :=
  (y * Real.log y + y ^ (1 - σ)) * Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))

/-- The actual left Poisson error has the complete elementary 46/9 and 230/27 majorant. -/
theorem afeSecondLeftExplicit_le {σ t x y : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hx : 0 < x) (hy : 3 / 2 ≤ y) (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = t) :
    afeSecondLeftExplicit σ (t / (2 * Real.pi)) x ≤
      x ^ (-σ) * (Real.log 2 / (2 * Real.pi) + 1 / (2 * Real.pi * y) +
        ((σ + t) / (2 * Real.pi * t)) * (Real.pi / 2 + Real.log 2) +
        (23 / (9 * Real.pi ^ 2)) * ((σ + t) * (σ + 1) / (x * t)) +
        (115 / (54 * Real.pi ^ 3)) * ((σ + t) / x ^ 2)) := by
  have hypos : 0 < y := by linarith
  have hc : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hcy : (t / (2 * Real.pi)) / x = y := by rw [← hscale]; field_simp
  have hs := mul_le_mul_of_nonneg_left (squareBounds_half_le (by linarith : 1 ≤ y) hyhalf)
    (show 0 ≤ ((σ + 1) * (σ + 2 * Real.pi * (t / (2 * Real.pi))) * x ^ (-σ - 2)) /
      (4 * Real.pi ^ 3) by positivity)
  have hk := mul_le_mul_of_nonneg_left (cubeBounds_half_le hy hyhalf)
    (show 0 ≤ (((σ + 2 * Real.pi * (t / (2 * Real.pi))) * x ^ (-σ - 1)) *
      ((t / (2 * Real.pi)) / x ^ 2) / (4 * Real.pi ^ 3)) by positivity)
  dsimp only [afeSecondLeftExplicit]
  rw [hcy]
  apply (add_le_add (add_le_add (le_refl _) hs) hk).trans_eq
  rw [Real.rpow_sub_one hx.ne']
  have he : x ^ (-σ - 2) = x ^ (-σ) / x ^ 2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hx.ne' (-σ) 2
  rw [he]
  rw [← hscale]
  field_simp
  ring_nf


/-- The elementary Poisson, pole and lower-integral coefficients are bounded by the source's A formula. -/
theorem afeSourceA_dominates {σ t x y : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hx : 0 < x) (hy : 0 < y) (hscale : 2 * Real.pi * x * y = t) :
    (Real.log 2 / (2 * Real.pi) + 1 / (2 * Real.pi * y) +
        ((σ + t) / (2 * Real.pi * t)) * (Real.pi / 2 + Real.log 2) +
        (23 / (9 * Real.pi ^ 2)) * ((σ + t) * (σ + 1) / (x * t)) +
        (115 / (54 * Real.pi ^ 3)) * ((σ + t) / x ^ 2)) + x / t +
      (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) ≤
      Real.log y / Real.pi + afeSourceA σ t x y := by
  have he : (Real.log y / Real.pi + afeSourceA σ t x y) -
      ((Real.log 2 / (2 * Real.pi) + 1 / (2 * Real.pi * y) +
        ((σ + t) / (2 * Real.pi * t)) * (Real.pi / 2 + Real.log 2) +
        (23 / (9 * Real.pi ^ 2)) * ((σ + t) * (σ + 1) / (x * t)) +
        (115 / (54 * Real.pi ^ 3)) * ((σ + t) / x ^ 2)) + x / t +
      (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2))) =
      Real.log 2 / (2 * Real.pi) + 3 / (4 * Real.pi * (y + 1)) +
        1 / (2 * Real.pi * y ^ 2) + σ / (2 * Real.pi * y ^ 2 * t) +
        3 * σ / (4 * Real.pi * (y + 1) * t) := by
    unfold afeSourceA
    rw [← hscale]
    have h1 : y + 1 ≠ 0 := by positivity
    field_simp
    ring_nf
  have hn : 0 ≤ Real.log 2 / (2 * Real.pi) + 3 / (4 * Real.pi * (y + 1)) +
        1 / (2 * Real.pi * y ^ 2) + σ / (2 * Real.pi * y ^ 2 * t) +
        3 * σ / (4 * Real.pi * (y + 1) * t) := by positivity
  linarith only [he, hn]

/-- The Gamma error factors exactly into the source B expression and the dual real power. -/
theorem afeSourceB_factor (σ t t₀ : ℝ) {y : ℝ} (hy : 0 < y) :
    (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
      (y ^ σ * Real.log y + 1) = afeSourceB σ t y t₀ * y ^ (σ - 1) := by
  have hp : y ^ (1 - σ) * y ^ (σ - 1) = 1 := by
    rw [← Real.rpow_add hy, show 1 - σ + (σ - 1) = 0 by ring, Real.rpow_zero]
  have hq : y * y ^ (σ - 1) = y ^ σ := by
    conv_lhs => lhs; rw [← Real.rpow_one y]
    rw [← Real.rpow_add hy, show 1 + (σ - 1) = σ by ring]
  have he : y ^ σ * Real.log y + 1 = (y * Real.log y + y ^ (1 - σ)) * y ^ (σ - 1) := by
    rw [add_mul, hp, mul_right_comm y (Real.log y), hq]
  rw [he]
  unfold afeSourceB
  ring

/-- The actual closed-strip error is bounded by the literal A and B formulas in the proof of Theorem 10. -/
theorem afeSecondError_le_source {σ t x y t₀ : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hx : 0 < x) (hy : 3 / 2 ≤ y) (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = t) :
    afeSecondError σ t x y t₀ ≤
      (Real.log y / Real.pi + afeSourceA σ t x y) * x ^ (-σ) +
        ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSourceB σ t y t₀ * y ^ (σ - 1) := by
  have hypos : 0 < y := by linarith
  have hL := afeSecondLeftExplicit_le hσ ht hx hy hyhalf hscale
  have hA := mul_le_mul_of_nonneg_right (afeSourceA_dominates hσ ht hx hypos hscale)
    (Real.rpow_nonneg hx.le (-σ))
  have hB := afeSourceB_factor σ t t₀ hypos
  have hB' := congrArg (fun q : ℝ => ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * q) hB
  dsimp only [afeSecondError]
  simp only [div_eq_mul_inv, mul_inv_rev] at hL hA hB' ⊢
  nlinarith only [hL, hA, hB']

/-- The actual two-polynomial AFE consumes the complete A/B estimate for positive height, including σ=0 and σ=1. -/
theorem afe_second_source_AB_positive {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = t)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + afeSourceA σ t x y) * x ^ (-σ) +
        ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSourceB σ t y t₀ * y ^ (σ - 1) :=
  (afe_closed_strip_bound hσ (by linarith) (by linarith) hxhalf hyhalf hscale ht₀ ht).trans
    (afeSecondError_le_source hσ.1 (ht₀.trans_le ht) (by linarith) hy hyhalf hscale)


/-- The literal chi modulus at the positive magnitude equals its modulus at either signed height. -/
theorem norm_chi_abs_height (σ t : ℝ) :
    ‖chi ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ = ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), norm_chi_neg_height]

/-- The actual AFE satisfies the complete A/B estimate at both height signs and both σ endpoints. -/
theorem afe_second_source_AB {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + afeSourceA σ |t| x y) * x ^ (-σ) +
        ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSourceB σ |t| y t₀ * y ^ (σ - 1) := by
  have hb := (afe_closed_strip_abs_bound hσ (by linarith) (by linarith) hxhalf hyhalf hscale ht₀ ht).trans
    (afeSecondError_le_source hσ.1 (ht₀.trans_le ht) (by linarith) hy hyhalf hscale)
  rwa [norm_chi_abs_height] at hb

/-- The reflected actual AFE has log(x) and the dual A/B coefficients after cancellation of the reciprocal chi factors. -/
theorem afe_second_source_AB_reflected {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.log x / Real.pi + afeSourceA (1 - σ) |t| y x) * y ^ (σ - 1) +
          afeSourceB (1 - σ) |t| x t₀ * x ^ (-σ) := by
  have htne : t ≠ 0 := abs_pos.mp (ht₀.trans_le ht)
  have hs : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hσ.1, hσ.2]
  have ht' : t₀ ≤ |-t| := by simpa only [abs_neg] using ht
  have hscale' : 2 * Real.pi * y * x = |-t| := by rw [abs_neg, ← hscale]; ring
  have hb := afe_second_source_AB hs hy hx hyhalf hxhalf hscale' ht₀ ht'
  rw [abs_neg, show -(1 - σ) = σ - 1 by ring, show 1 - σ - 1 = -σ by ring] at hb
  have he : 1 - ((σ : ℂ) + (t : ℂ) * Complex.I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hr := norm_afeRemainder_reflection (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using htne) x y
  rw [he] at hr
  have hχ := congrArg norm (chi_mul_chi_one_sub (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using htne))
  rw [norm_mul, norm_one, he] at hχ
  have hb' := mul_le_mul_of_nonneg_left hb (norm_nonneg (chi ((σ : ℂ) + (t : ℂ) * Complex.I)))
  rw [← hr] at hb'
  have heχ := congrArg (fun q : ℝ => q * afeSourceB (1 - σ) |t| x t₀ * x ^ (-σ)) hχ
  nlinarith only [hb', heχ]

end DhimanKadiriQuesadaHerrera2026
