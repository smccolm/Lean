import DhimanKadiriQuesadaHerrera2026.BProcessPoisson

namespace DhimanKadiriQuesadaHerrera2026.PoissonHalfReview

/-- A near-integer cubic phase on a five-unit half-integer interval. -/
noncomputable def phase (u : ℝ) : ℝ := u - (u - 1 / 2) / 1000 - (u - 1 / 2) ^ 2 / 2000000000 + (u - 1 / 2) ^ 3 / 60000000000

/-- Exact first derivative of the review phase. -/
theorem phase_hasDerivAt (u : ℝ) :
    HasDerivAt phase (999 / 1000 - (u - 1 / 2) / 1000000000 + (u - 1 / 2) ^ 2 / 20000000000) u := by
  unfold phase
  have hd := (hasDerivAt_id u).sub_const (1 / 2)
  convert (((hasDerivAt_id u).sub (hd.div_const 1000)).sub ((hd.pow 2).div_const 2000000000)).add
    ((hd.pow 3).div_const 60000000000) using 1
  dsimp
  ring

/-- Exact derivative of the review phase. -/
theorem phase_deriv (u : ℝ) :
    deriv phase u = 999 / 1000 - (u - 1 / 2) / 1000000000 + (u - 1 / 2) ^ 2 / 20000000000 :=
  (phase_hasDerivAt u).deriv

/-- The signed curvature increases strictly while remaining negative. -/
theorem phase_second_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv phase) (-1 / 1000000000 + (u - 1 / 2) / 10000000000) u := by
  rw [show deriv phase = fun v => 999 / 1000 - (v - 1 / 2) / 1000000000 +
    (v - 1 / 2) ^ 2 / 20000000000 by funext v; exact phase_deriv v]
  have hd := (hasDerivAt_id u).sub_const (1 / 2)
  convert ((hasDerivAt_const u (999 / 1000 : ℝ)).sub (hd.div_const 1000000000)).add
    ((hd.pow 2).div_const 20000000000) using 1
  dsimp
  ring

/-- The exact second derivative. -/
theorem phase_second (u : ℝ) :
    deriv (deriv phase) u = -1 / 1000000000 + (u - 1 / 2) / 10000000000 :=
  (phase_second_hasDerivAt u).deriv

/-- The signed curvature stays strictly negative on the entire interval. -/
theorem phase_second_neg {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2)) :
    deriv (deriv phase) u < 0 := by
  rw [phase_second]
  linarith [hu.2]

/-- The first derivative strictly decreases and remains positive on the entire source interval. -/
theorem phase_range : StrictAntiOn (deriv phase) (Set.Icc (1 / 2 : ℝ) (11 / 2)) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2), 0 < deriv phase u) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun u _ => (phase_second_hasDerivAt u).continuousAt.continuousWithinAt)
    intro u hu
    exact phase_second_neg (interior_subset hu)
  · intro u hu
    rw [phase_deriv]
    nlinarith [hu.2, sq_nonneg (u - 1 / 2)]

/-- The printed hypotheses hold even with strictly decreasing positive absolute curvature. -/
theorem phase_source_hypotheses :
    ContDiff ℝ 3 phase ∧ ContinuousOn (deriv phase) (Set.Icc (1 / 2 : ℝ) (11 / 2)) ∧
    StrictAntiOn (deriv phase) (Set.Icc (1 / 2 : ℝ) (11 / 2)) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2), 0 < deriv phase u) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2), 0 < |deriv (deriv phase) u|) ∧
    StrictAntiOn (fun u => |deriv (deriv phase) u|) (Set.Icc (1 / 2 : ℝ) (11 / 2)) := by
  refine ⟨?_, fun u _ => (phase_second_hasDerivAt u).continuousAt.continuousWithinAt,
    phase_range.1, phase_range.2, ?_, ?_⟩
  · unfold phase
    fun_prop
  · intro u hu
    exact abs_pos.mpr (phase_second_neg hu).ne
  · intro u hu v hv huv
    dsimp only
    rw [abs_of_neg (phase_second_neg hu), abs_of_neg (phase_second_neg hv), phase_second, phase_second]
    linarith

/-- The review uses half-integer endpoints and an allowed printed δ=1/1000. -/
theorem phase_endpoint_data :
    (∃ k : ℤ, (1 / 2 : ℝ) = k + 1 / 2) ∧ (∃ k : ℤ, (11 / 2 : ℝ) = k + 1 / 2) ∧
    deriv phase (1 / 2) = 999 / 1000 ∧ deriv phase (11 / 2) = 799199997 / 800000000 ∧
    1 - Int.fract (deriv phase (1 / 2)) = 1 / 1000 := by
  refine ⟨⟨0, by norm_num⟩, ⟨5, by norm_num⟩, ?_, ?_, ?_⟩
  · norm_num [phase_deriv]
  · norm_num [phase_deriv]
  · norm_num [phase_deriv, Int.fract]

/-- Every actual integer sample is close to one by periodicity and the exponential Lipschitz bound. -/
theorem sample_close_one (n : ℤ) (hn : n ∈ Finset.Ioc 0 5) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ)) - 1‖ ≤ 1 / 20 := by
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ n by have h := (Finset.mem_Ioc.mp hn).1; omega)
  have hn5 : (n : ℝ) ≤ 5 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  let x : ℝ := (n : ℝ) - 1 / 2
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx5 : x ≤ 5 := by dsimp [x]; linarith
  have hx2 : x ^ 2 ≤ 25 := by nlinarith [mul_self_le_mul_self hx0 hx5]
  have hx3 : x ^ 3 ≤ 125 := by
    calc
      _ = x ^ 2 * x := by ring
      _ ≤ 25 * 5 := mul_le_mul hx2 hx5 hx0 (by norm_num)
      _ = _ := by norm_num
  have habs : |phase (n : ℝ) - (n : ℝ)| ≤ 1 / 160 := by
    have he : phase (n : ℝ) - (n : ℝ) = -x / 1000 - x ^ 2 / 2000000000 + x ^ 3 / 60000000000 := by
      dsimp [phase, x]
      ring
    rw [he, abs_le]
    constructor <;> nlinarith [pow_nonneg hx0 3, sq_nonneg x]
  have he := weightedWave_phaseShift_int phase (fun _ => 1) 1 n
  simp only [weightedWave, phaseShift, Nat.cast_one, Complex.ofReal_one, one_mul] at he
  rw [← he]
  apply (norm_exp_two_pi_sub_one_le _).trans
  have hm := mul_le_mul_of_nonneg_left habs Real.two_pi_pos.le
  nlinarith [Real.pi_lt_four]

/-- The actual five-term exponential sum is within one quarter of five. -/
theorem sum_close_five :
    ‖(∑ n ∈ Finset.Ioc (0 : ℤ) 5, Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ))) - 5‖ ≤ 1 / 4 := by
  have h := (norm_sum_le (Finset.Ioc (0 : ℤ) 5)
    (fun n => Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ)) - 1)).trans
      (Finset.sum_le_sum (fun n hn => sample_close_one n hn))
  norm_num [Finset.sum_sub_distrib, Finset.sum_const] at h
  norm_num [show Int.toNat 5 = 5 by rfl] at h
  exact h

/-- The zero-frequency Fourier integral has norm at most one half. -/
theorem integral_small :
    ‖∫ u in (1 / 2 : ℝ)..(11 / 2), Complex.exp (2 * Real.pi * Complex.I * (phase u : ℂ))‖ ≤ 1 / 2 := by
  have h := norm_shifted_integral_positive (ν := 0) (by norm_num : (1 / 2 : ℝ) ≤ 11 / 2)
    (fun u _ => (phase_hasDerivAt u).differentiableAt)
    (fun u _ => (phase_second_hasDerivAt u).continuousAt.continuousWithinAt) phase_range.1.antitoneOn
    (by norm_num [phase_deriv] : 0 < deriv phase (11 / 2))
  simp only [zero_mul, sub_zero] at h
  apply h.trans
  rw [div_le_iff₀ (mul_pos Real.pi_pos (by norm_num [phase_deriv] : 0 < deriv phase (11 / 2)))]
  norm_num [phase_deriv]
  nlinarith [Real.pi_gt_three]

/-- The actual remainder is larger than four, including the source floor conventions. -/
theorem remainder_gt_four : 4 <
    ‖(∑ n ∈ Finset.Ioc ⌊(1 / 2 : ℝ)⌋ ⌊(11 / 2 : ℝ)⌋,
      Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv phase (1 / 2)⌋₊, ∫ u in (1 / 2 : ℝ)..(11 / 2),
        Complex.exp (2 * Real.pi * Complex.I * ((phase u - (ν : ℝ) * u : ℝ) : ℂ))‖ := by
  rw [show deriv phase (1 / 2) = 999 / 1000 by norm_num [phase_deriv]]
  norm_num only [
    show ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) by norm_num, show ⌊(11 / 2 : ℝ)⌋ = (5 : ℤ) by norm_num,
    show ⌊(999 / 1000 : ℝ)⌋₊ = 0 by norm_num, Finset.Icc_self, Finset.sum_singleton,
    Nat.cast_zero, zero_mul, sub_zero]
  let S := ∑ n ∈ Finset.Ioc (0 : ℤ) 5, Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ))
  let I := ∫ u in (1 / 2 : ℝ)..(11 / 2), Complex.exp (2 * Real.pi * Complex.I * (phase u : ℂ))
  have h1 := norm_sub_norm_le (5 : ℂ) S
  rw [norm_sub_rev] at h1
  norm_num only [Complex.norm_ofNat] at h1
  have h2 := norm_sub_norm_le S I
  have hs : ‖S - 5‖ ≤ 1 / 4 := sum_close_five
  have hi : ‖I‖ ≤ 1 / 2 := integral_small
  change 4 < ‖S - I‖
  linarith

/-- In constant weight the two printed coefficients simplify exactly, without estimates for digamma. -/
theorem printed_coefficient_small :
    printedPartIIE1 (999 / 1000) / (999 / 1000) + partIICubeCoefficient (999 / 1000) ≤ 1000000010 := by
  have he : printedPartIIE1 (999 / 1000) / (999 / 1000) + partIICubeCoefficient (999 / 1000) =
      1000000000 + 1 / (1001 / 1000 : ℝ) ^ 3 + 1 / (2 * (1001 / 1000 : ℝ) ^ 2) +
        1 / ((999 / 1000 : ℝ) * (1001 / 1000 : ℝ) ^ 2) +
          1 / (2 * (999 / 1000 : ℝ) ^ 2) - 1 / (2 * (1999 / 1000 : ℝ) ^ 2) := by
    norm_num [printedPartIIE1, partIICubeCoefficient]
    ring
  rw [he]
  norm_num

/-- The literal Corollary 0.1 Part-II bound, using its cited half-integer B formula. -/
noncomputable def printedBound : ℝ :=
  let β := deriv phase (1 / 2)
  let α := deriv phase (11 / 2)
  Real.log 2 / (2 * Real.pi) +
    (β * halfSecondEndpointBound ⌊β⌋₊ β + α * halfSecondEndpointBound ⌊β⌋₊ α) / (2 * Real.pi) +
      1 / (2 * Real.pi * β) + |deriv (deriv phase) (1 / 2)| / (2 * Real.pi ^ 2) *
        (printedPartIIE1 β / β + partIICubeCoefficient β)

/-- The full printed bound for this phase is smaller than three. -/
theorem printedBound_lt_three : printedBound < 3 := by
  have hp := Real.pi_gt_three
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hcoef := printed_coefficient_small
  have hcoefmul := mul_le_mul_of_nonneg_left hcoef
    (by positivity : 0 ≤ (1 / 1000000000 : ℝ) / (2 * Real.pi ^ 2))
  have he : printedBound =
      1 / 2 + (2 + 3 * Real.log 2 + 3 / (2 * (1999 / 1000 : ℝ)) +
        3 / (2 * (1599199997 / 800000000 : ℝ)) + 1 / (999 / 1000 : ℝ)) / (2 * Real.pi) +
      (1 / 1000000000 : ℝ) / (2 * Real.pi ^ 2) *
        (printedPartIIE1 (999 / 1000) / (999 / 1000) + partIICubeCoefficient (999 / 1000)) := by
    norm_num [printedBound, phase_deriv, phase_second, halfSecondEndpointBound]
    field_simp
    ring
  rw [he]
  have hnum : 2 + 3 * Real.log 2 + 3 / (2 * (1999 / 1000 : ℝ)) +
      3 / (2 * (1599199997 / 800000000 : ℝ)) + 1 / (999 / 1000 : ℝ) ≤ 9 := by
    linarith
  have hhead : (2 + 3 * Real.log 2 + 3 / (2 * (1999 / 1000 : ℝ)) +
      3 / (2 * (1599199997 / 800000000 : ℝ)) + 1 / (999 / 1000 : ℝ)) / (2 * Real.pi) < 3 / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith
  have htail : (1 / 1000000000 : ℝ) / (2 * Real.pi ^ 2) * 1000000010 < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by positivity : 0 < 2 * Real.pi ^ 2)]
    nlinarith
  linarith

/-- The entire literal Corollary 0.1 Part-II inequality fails for this smooth example with positive absolute curvature. -/
theorem printed_poisson_bound_false :
    ¬ ‖(∑ n ∈ Finset.Ioc ⌊(1 / 2 : ℝ)⌋ ⌊(11 / 2 : ℝ)⌋,
      Complex.exp (2 * Real.pi * Complex.I * (phase (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv phase (1 / 2)⌋₊, ∫ u in (1 / 2 : ℝ)..(11 / 2),
        Complex.exp (2 * Real.pi * Complex.I * ((phase u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤ printedBound := by
  have h := remainder_gt_four
  have hb := printedBound_lt_three
  linarith

end DhimanKadiriQuesadaHerrera2026.PoissonHalfReview
