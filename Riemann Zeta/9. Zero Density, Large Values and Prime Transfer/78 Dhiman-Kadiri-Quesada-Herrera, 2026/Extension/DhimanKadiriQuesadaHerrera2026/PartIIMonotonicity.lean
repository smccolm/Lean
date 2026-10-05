import DhimanKadiriQuesadaHerrera2026.PoissonShift

/-! # Concrete diagnostic of the Part-II quotient inference

This refutes one intermediate inference, not the full Poisson inequality.
-/

namespace DhimanKadiriQuesadaHerrera2026.PartIIMonotonicity

/-- An actual cubic phase with strictly decreasing positive derivative on [0,1]. -/
noncomputable def phase (x : ℝ) : ℝ := 2 * x - x ^ 2 / 20 + x ^ 3 / 300
/-- An actual cubic weight with positive strictly decreasing second derivative on [0,1]. -/
noncomputable def weight (x : ℝ) : ℝ := 10 - x + x ^ 2 / 20 - x ^ 3 / 6000

/-- Derivative of the concrete cubic phase. -/
lemma phase_hasDerivAt (x : ℝ) :
    HasDerivAt phase (2 - x / 10 + x ^ 2 / 100) x := by
  unfold phase
  convert (((hasDerivAt_id x).const_mul 2).sub (((hasDerivAt_id x).pow 2).div_const 20)).add
    (((hasDerivAt_id x).pow 3).div_const 300) using 1
  dsimp
  ring

/-- Derivative of the concrete cubic weight. -/
lemma weight_hasDerivAt (x : ℝ) :
    HasDerivAt weight (-1 + x / 10 - x ^ 2 / 2000) x := by
  unfold weight
  convert (((hasDerivAt_const x (10 : ℝ)).sub (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 2).div_const 20)).sub
      (((hasDerivAt_id x).pow 3).div_const 6000) using 1
  dsimp
  ring

/-- Explicit first derivative of the phase. -/
lemma phase_deriv (x : ℝ) : deriv phase x = 2 - x / 10 + x ^ 2 / 100 :=
  (phase_hasDerivAt x).deriv
/-- Explicit first derivative of the weight. -/
lemma weight_deriv (x : ℝ) : deriv weight x = -1 + x / 10 - x ^ 2 / 2000 :=
  (weight_hasDerivAt x).deriv

/-- Second derivative of the concrete phase. -/
lemma phase_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv phase) (-1 / 10 + x / 50) x := by
  have he : deriv phase = fun x => 2 - x / 10 + x ^ 2 / 100 := funext phase_deriv
  rw [he]
  convert ((hasDerivAt_const x (2 : ℝ)).sub ((hasDerivAt_id x).div_const 10)).add
    (((hasDerivAt_id x).pow 2).div_const 100) using 1
  dsimp
  ring

/-- Second derivative of the concrete weight. -/
lemma weight_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv weight) (1 / 10 - x / 1000) x := by
  have he : deriv weight = fun x => -1 + x / 10 - x ^ 2 / 2000 := funext weight_deriv
  rw [he]
  convert ((hasDerivAt_const x (-1 : ℝ)).add ((hasDerivAt_id x).div_const 10)).sub
    (((hasDerivAt_id x).pow 2).div_const 2000) using 1
  dsimp
  ring

/-- Explicit second derivative of the phase. -/
lemma phase_second (x : ℝ) : deriv (deriv phase) x = -1 / 10 + x / 50 :=
  (phase_second_hasDerivAt x).deriv
/-- Explicit second derivative of the weight. -/
lemma weight_second (x : ℝ) : deriv (deriv weight) x = 1 / 10 - x / 1000 :=
  (weight_second_hasDerivAt x).deriv

/-- The first disputed quotient increases between the two endpoints. -/
theorem second_quotient_not_antitone :
    ¬ AntitoneOn (fun x => |deriv (deriv weight) x| / (1 + deriv phase x) ^ 2) (Set.Icc 0 1) := by
  intro hm
  have h := hm (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num [phase_deriv, weight_second] at h

/-- The phase derivative is positive throughout the source interval. -/
lemma phase_deriv_pos {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 0 < deriv phase x := by
  rw [phase_deriv]
  nlinarith [hx.2, sq_nonneg x]

/-- The weight derivative is negative throughout the source interval. -/
lemma weight_deriv_neg {x : ℝ} (hx : x ∈ Set.Icc 0 1) : deriv weight x < 0 := by
  rw [weight_deriv]
  nlinarith [hx.2, sq_nonneg x]

/-- The phase has negative curvature throughout the source interval. -/
lemma phase_second_neg {x : ℝ} (hx : x ∈ Set.Icc 0 1) : deriv (deriv phase) x < 0 := by
  rw [phase_second]
  linarith [hx.2]

/-- The weight has positive curvature throughout the source interval. -/
lemma weight_second_pos {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 0 < deriv (deriv weight) x := by
  rw [weight_second]
  linarith [hx.2]

/-- The source phase derivative is strictly decreasing. -/
lemma phase_deriv_strictAnti : StrictAntiOn (deriv phase) (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun x _ => (phase_second_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  exact phase_second_neg (interior_subset hx)

/-- The source weight is strictly decreasing. -/
lemma weight_strictAnti : StrictAntiOn weight (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun x _ => (weight_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  exact weight_deriv_neg (interior_subset hx)

/-- The source weight stays strictly positive. -/
lemma weight_pos {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 0 < weight x := by
  have h := weight_strictAnti.antitoneOn hx (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hx.2
  norm_num [weight] at h
  unfold weight
  linarith

/-- The absolute weight derivative is strictly decreasing. -/
lemma abs_weight_deriv_strictAnti : StrictAntiOn (fun x => |deriv weight x|) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  dsimp only
  rw [abs_of_neg (weight_deriv_neg hx), abs_of_neg (weight_deriv_neg hy), weight_deriv, weight_deriv]
  have hp : 0 < (y - x) * (1 / 10 - (x + y) / 2000) :=
    mul_pos (sub_pos.mpr hxy) (by linarith [hx.2, hy.2])
  nlinarith

/-- The absolute phase curvature is strictly decreasing. -/
lemma abs_phase_second_strictAnti : StrictAntiOn (fun x => |deriv (deriv phase) x|) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  dsimp only
  rw [abs_of_neg (phase_second_neg hx), abs_of_neg (phase_second_neg hy), phase_second, phase_second]
  linarith

/-- The weight curvature is strictly decreasing. -/
lemma weight_second_strictAnti : StrictAntiOn (deriv (deriv weight)) (Set.Icc 0 1) := by
  intro x _ y _ hxy
  rw [weight_second, weight_second]
  linarith

/-- The absolute product derivative has two positive summands. -/
lemma abs_product_derivative (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    |deriv weight x * deriv phase x + weight x * deriv (deriv phase) x| =
      |deriv weight x| * deriv phase x + weight x * |deriv (deriv phase) x| := by
  have hn1 := mul_neg_of_neg_of_pos (weight_deriv_neg hx) (phase_deriv_pos hx)
  have hn2 := mul_neg_of_pos_of_neg (weight_pos hx) (phase_second_neg hx)
  rw [abs_of_neg (add_neg hn1 hn2), abs_of_neg (weight_deriv_neg hx), abs_of_neg (phase_second_neg hx)]
  ring

/-- The absolute product derivative is strictly positive. -/
lemma product_derivative_pos {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 < |deriv weight x * deriv phase x + weight x * deriv (deriv phase) x| := by
  rw [abs_product_derivative x hx]
  exact add_pos (mul_pos (abs_pos.mpr (weight_deriv_neg hx).ne) (phase_deriv_pos hx))
    (mul_pos (weight_pos hx) (abs_pos.mpr (phase_second_neg hx).ne))

/-- The absolute product derivative is strictly decreasing. -/
lemma abs_product_derivative_strictAnti :
    StrictAntiOn (fun x => |deriv weight x * deriv phase x + weight x * deriv (deriv phase) x|)
      (Set.Icc 0 1) := by
  intro x hx y hy hxy
  dsimp only
  rw [abs_product_derivative x hx, abs_product_derivative y hy]
  apply add_lt_add_of_lt_of_le
  · apply (mul_lt_mul_of_pos_right (abs_weight_deriv_strictAnti hx hy hxy) (phase_deriv_pos hy)).trans_le
    exact mul_le_mul_of_nonneg_left (phase_deriv_strictAnti.antitoneOn hx hy hxy.le) (abs_nonneg _)
  · exact mul_le_mul (weight_strictAnti.antitoneOn hx hy hxy.le)
      (abs_phase_second_strictAnti.antitoneOn hx hy hxy.le) (abs_nonneg _) (weight_pos hx).le

/-- The already accepted Part-I quotient is nonincreasing. -/
lemma accepted_quotient_antitone :
    AntitoneOn (fun x => |deriv weight x| / (1 + deriv phase x)) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  dsimp only
  have hxp : 0 < 1 + deriv phase x := by linarith [phase_deriv_pos hx]
  have hyp : 0 < 1 + deriv phase y := by linarith [phase_deriv_pos hy]
  apply (div_le_div_iff₀ hyp hxp).mpr
  rw [abs_of_neg (weight_deriv_neg hx), abs_of_neg (weight_deriv_neg hy),
    phase_deriv, phase_deriv, weight_deriv, weight_deriv]
  have hprod : x * y ≤ 1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]
  have hfac : 0 ≤ 1 / 5 + (17 / 2000) * (x + y) - (19 / 20000) * x * y := by
    nlinarith [hx.1, hy.1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hfac]

/-- The cubic example satisfies the already accepted Part-I hypotheses as well. -/
theorem accepted_partI_regular : PartIRegularityAt phase weight 0 1 0 := by
  apply partIRegularityAt_of_source_hypotheses (by norm_num)
    (fun x _ => (phase_hasDerivAt x).differentiableAt)
    (fun x _ => (phase_second_hasDerivAt x).continuousAt.continuousWithinAt)
    (by simpa using phase_deriv_pos (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1))
    phase_deriv_strictAnti
    (fun x _ => (weight_hasDerivAt x).differentiableAt)
    (fun x _ => (weight_second_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun _ hx => weight_pos hx) weight_strictAnti.antitoneOn abs_weight_deriv_strictAnti.antitoneOn
  simpa only [Nat.cast_zero, sub_zero] using accepted_quotient_antitone

/-- Both concrete functions are smooth, so the obstruction is not a regularity defect. -/
theorem smooth_functions : ContDiff ℝ ⊤ phase ∧ ContDiff ℝ ⊤ weight := by
  constructor
  · unfold phase
    fun_prop
  · unfold weight
    fun_prop

/-- All four strictly decreasing positive Part-II quantities hold, but the asserted quotient inference fails. -/
theorem source_conditions_and_failed_quotient :
    PartIRegularityAt phase weight 0 1 0 ∧
    ContDiff ℝ ⊤ phase ∧ ContDiff ℝ ⊤ weight ∧
    StrictAntiOn (deriv phase) (Set.Icc 0 1) ∧
    (∀ x ∈ Set.Icc 0 1, 0 < weight x ∧ 0 < deriv phase x ∧
      0 < |deriv weight x| ∧ 0 < |deriv (deriv phase) x| ∧
      0 < deriv (deriv weight) x ∧
      0 < |deriv weight x * deriv phase x + weight x * deriv (deriv phase) x|) ∧
    StrictAntiOn (fun x => |deriv weight x|) (Set.Icc 0 1) ∧
    StrictAntiOn (fun x => |deriv (deriv phase) x|) (Set.Icc 0 1) ∧
    StrictAntiOn (deriv (deriv weight)) (Set.Icc 0 1) ∧
    StrictAntiOn (fun x => |deriv weight x * deriv phase x + weight x * deriv (deriv phase) x|)
      (Set.Icc 0 1) ∧
    ¬ AntitoneOn (fun x => |deriv (deriv weight) x| / (1 + deriv phase x) ^ 2) (Set.Icc 0 1) := by
  refine ⟨accepted_partI_regular, smooth_functions.1, smooth_functions.2, phase_deriv_strictAnti,
    ?_, abs_weight_deriv_strictAnti, abs_phase_second_strictAnti, weight_second_strictAnti,
    abs_product_derivative_strictAnti, second_quotient_not_antitone⟩
  intro x hx
  exact ⟨weight_pos hx, phase_deriv_pos hx, abs_pos.mpr (weight_deriv_neg hx).ne,
    abs_pos.mpr (phase_second_neg hx).ne, weight_second_pos hx, product_derivative_pos hx⟩

end DhimanKadiriQuesadaHerrera2026.PartIIMonotonicity
