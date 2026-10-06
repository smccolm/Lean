import DhimanKadiriQuesadaHerrera2026.PoissonHalfDelta

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual logarithmic phase has the third derivative needed by the B-process. -/
theorem afePhase_second_hasDerivAt (c : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (deriv (deriv (afePhase c))) (2 * c / u ^ 3) u := by
  have hd : HasDerivAt (fun v : ℝ => -c / v ^ 2) (2 * c / u ^ 3) u := by
    convert (hasDerivAt_const u (-c)).div ((hasDerivAt_id u).pow 2) (by positivity : u ^ 2 ≠ 0) using 1
    dsimp
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact (afePhase_deriv_hasDerivAt c hv).deriv

/-- Every extra second-order condition is discharged for the actual unweighted logarithmic phase. -/
theorem afePhase_constant_secondOrderRegularity {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b) :
    SecondOrderRegularity (afePhase c) (fun _ => 1) a b := by
  have h := afe_secondOrderRegularity (σ := 0) (by norm_num) hc ha hab
  have he : afeWeight 0 = (fun _ => 1) := by funext u; simp [afeWeight]
  rw [he] at h
  exact h

/-- The explicit curvature scales and third-derivative bound hold throughout the actual interval. -/
theorem afePhase_b_process_scales {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    (∀ u ∈ Set.Icc a b, c / b ^ 2 ≤ |deriv (deriv (afePhase c)) u|) ∧
    (∀ u ∈ Set.Icc a b, |deriv (deriv (afePhase c)) u| ≤ (b ^ 2 / a ^ 2) * (c / b ^ 2)) ∧
    (∀ u ∈ Set.Icc a b, |deriv (deriv (deriv (afePhase c))) u| ≤ 2 * c / a ^ 3) := by
  have hb := ha.trans_le hab
  have hcurv (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |deriv (deriv (afePhase c)) u| = c / u ^ 2 := by
    rw [(afePhase_deriv_hasDerivAt c (ha.trans_le hu.1)).deriv, abs_div, abs_neg,
      abs_of_pos hc, abs_of_nonneg (sq_nonneg u)]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hup := ha.trans_le hu.1
    rw [hcurv u hu]
    exact div_le_div_of_nonneg_left hc.le (by positivity : 0 < u ^ 2)
      (pow_le_pow_left₀ (ha.trans_le hu.1).le hu.2 2)
  · intro u hu
    rw [hcurv u hu]
    have he : (b ^ 2 / a ^ 2) * (c / b ^ 2) = c / a ^ 2 := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_left hc.le (by positivity : 0 < a ^ 2)
      (pow_le_pow_left₀ ha.le hu.1 2)
  · intro u hu
    have hup := ha.trans_le hu.1
    rw [(afePhase_second_hasDerivAt c hup).deriv, abs_of_pos (by positivity : 0 < 2 * c / u ^ 3)]
    exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * c) (by positivity : 0 < a ^ 3)
      (pow_le_pow_left₀ ha.le hu.1 3)

/-- The source derivative is strictly decreasing for the actual logarithmic phase. -/
theorem afePhase_strictAnti {c : ℝ} (hc : 0 < c) : StrictAntiOn (deriv (afePhase c)) (Set.Ioi 0) := by
  intro u hu v _ huv
  rw [(afePhase_hasDerivAt c hu).deriv, (afePhase_hasDerivAt c (hu.trans huv)).deriv]
  exact div_lt_div_of_pos_left hc hu huv

/-- The actual logarithmic stationary term has its explicit point, phase and amplitude. -/
theorem afePhase_stationary_term {c u ν : ℝ} (hc : 0 < c) (hu : 0 < u) (hν : 0 < ν)
    (hstat : deriv (afePhase c) u = ν) :
    Complex.exp (2 * Real.pi * Complex.I * ((afePhase c u - ν * u - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv (afePhase c)) u| : ℂ) =
    ((Real.sqrt c / ν : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / ν) - c - 1 / 8 : ℝ) : ℂ)) := by
  rw [(afePhase_hasDerivAt c hu).deriv] at hstat
  have hνu : ν * u = c := ((div_eq_iff hu.ne').mp hstat).symm
  have hpoint : c / ν = u := (div_eq_iff hν.ne').mpr (by linarith)
  have hamp : (Real.sqrt |deriv (deriv (afePhase c)) u|)⁻¹ = Real.sqrt c / ν := by
    rw [(afePhase_deriv_hasDerivAt c hu).deriv, abs_div, abs_neg, abs_of_pos hc,
      abs_of_nonneg (sq_nonneg u), Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hu]
    have hsq := Real.sq_sqrt hc.le
    have hs := Real.sqrt_pos.mpr hc
    field_simp
    nlinarith
  rw [hpoint, afePhase, hνu, div_eq_mul_inv]
  have he : (Real.sqrt |deriv (deriv (afePhase c)) u| : ℂ)⁻¹ = ((Real.sqrt c / ν : ℝ) : ℂ) := by
    exact_mod_cast hamp
  rw [he]
  ring

/-- The actual logarithmic exponential sum has an explicit stationary dual sum and the proved all-δ Poisson error, with every extra analytic condition discharged. -/
theorem logarithmic_b_process {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) + 1.251 +
      ((Real.log 2 + 1 / (c / a)) / Real.pi +
        ((c / b) * halfSecondEndpointDelta ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointDelta ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) / (2 * Real.pi ^ 2) * (minusSquareBound ⌊c / a⌋₊ (c / a) + plusSquareBound (c / a)) +
        ((c / a) * (c / a ^ 2) / (2 * Real.pi ^ 2)) *
          (minusCubeBound ⌊c / a⌋₊ (c / a) + plusCubeBound (c / a))) := by
  have hb := ha.trans hab
  have hup (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hβ := (afePhase_hasDerivAt c ha).deriv
  have hγ := (afePhase_hasDerivAt c hb).deriv
  obtain ⟨ξ, hξ, hs⟩ := exists_b_process_delta (ℓ₂ := c / b ^ 2) (ℓ₃ := 2 * c / a ^ 3)
    (h₂ := b ^ 2 / a ^ 2) (h₃ := 1) hr (by positivity) (by positivity) (by norm_num)
    (by rw [hγ]; exact hα) hah hbh
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).differentiableAt)
    ((afePhase_strictAnti hc).mono (fun u hu => hup u hu)) hscl.1 hscl.2.1
    (fun u hu => by simpa only [one_mul] using hscl.2.2 u hu)
  rw [hβ] at hξ hs
  rw [hγ] at hs
  have hmain : (∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊,
      Complex.exp (2 * Real.pi * Complex.I * ((afePhase c (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv (afePhase c)) (ξ ν)| : ℂ)) =
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro ν hν
    have hxp := hξ ν hν
    exact afePhase_stationary_term hc (hup (ξ ν) hxp.1)
      (by exact_mod_cast (show 0 < ν by have h := (Finset.mem_Icc.mp hν).1; omega)) hxp.2
  rw [hmain, (afePhase_deriv_hasDerivAt c ha).deriv, abs_div, abs_neg, abs_of_pos hc,
    abs_of_nonneg (sq_nonneg a)] at hs
  simp only [Real.one_rpow, mul_one, afePhase] at hs
  exact hs.trans_eq (by ring)

end DhimanKadiriQuesadaHerrera2026
