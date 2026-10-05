import DhimanKadiriQuesadaHerrera2026.StationaryPoints
import Mathlib.Analysis.Calculus.Taylor

namespace DhimanKadiriQuesadaHerrera2026
open Set

/-- On a set with unique derivatives, ordinary differentiability identifies every lower derivative. -/
theorem iteratedDerivWithin_eq_of_differentiable {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hs : UniqueDiffOn ℝ s)
    (hd : ∀ k < n, ∀ u ∈ s, DifferentiableAt ℝ (iteratedDeriv k f) u) :
    EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    have he := ih (fun k hk => hd k (by omega))
    intro u hu
    rw [iteratedDerivWithin_succ, iteratedDeriv_succ,
      derivWithin_congr he (he hu), (hd n (by omega) u hu).derivWithin (hs u hu)]

/-- Existence of the next derivative supplies exactly the finite smoothness required for Taylor's theorem. -/
theorem contDiffOn_of_iterated_differentiable {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hs : UniqueDiffOn ℝ s)
    (hd : ∀ k ≤ n, ∀ u ∈ s, DifferentiableAt ℝ (iteratedDeriv k f) u) :
    ContDiffOn ℝ n f s := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs).mpr
  constructor
  · intro k hk
    have he := iteratedDerivWithin_eq_of_differentiable hs (n := k) (fun j hj => hd j (by omega : j ≤ n))
    have hh : ContinuousOn (iteratedDeriv k f) s := fun u hu => (hd k hk u hu).continuousAt.continuousWithinAt
    exact hh.congr (fun u hu => he hu)
  · intro k hk
    have he := iteratedDerivWithin_eq_of_differentiable hs (n := k) (fun j hj => hd j (by omega : j ≤ n))
    have hh : DifferentiableOn ℝ (iteratedDeriv k f) s := fun u hu => (hd k hk.le u hu).differentiableWithinAt
    exact hh.congr (fun u hu => he hu)

/-- The sharp factorial Taylor bound needs only existence and boundedness of the highest derivative. -/
theorem taylor_remainder_of_differentiable {f : ℝ → ℝ} {a x D : ℝ} (n : ℕ)
    (hd : ∀ k ≤ n, ∀ u ∈ uIcc a x, DifferentiableAt ℝ (iteratedDeriv k f) u)
    (hD : ∀ u ∈ uIcc a x, |iteratedDeriv (n + 1) f u| ≤ D) :
    |f x - taylorWithinEval f n univ a x| ≤ D * |x - a| ^ (n + 1) / (n + 1).factorial := by
  by_cases hax : a = x
  · subst x
    simp
  have hs : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hax with h | h
    · simpa only [min_eq_left h.le, max_eq_right h.le] using h
    · simpa only [min_eq_right h.le, max_eq_left h.le] using h)
  have he (k : ℕ) (hk : k ≤ n + 1) := iteratedDerivWithin_eq_of_differentiable hs
    (n := k) (fun j hj => hd j (by omega : j ≤ n))
  have hfd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIoo a x) := by
    have hh : DifferentiableOn ℝ (iteratedDeriv n f) (uIoo a x) :=
      fun u hu => (hd n le_rfl u (Ioo_subset_Icc_self hu)).differentiableWithinAt
    apply hh.congr
    intro u hu
    exact he n (by omega) (Ioo_subset_Icc_self hu)
  obtain ⟨u, hu, ht⟩ := taylor_mean_remainder_lagrange hax (contDiffOn_of_iterated_differentiable hs hd) hfd
  have hp : taylorWithinEval f n (uIcc a x) a x = taylorWithinEval f n univ a x := by
    simp only [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [he k (by have hh := Finset.mem_range.mp hk; omega) left_mem_uIcc, iteratedDerivWithin_univ]
  rw [hp, he (n + 1) le_rfl (Ioo_subset_Icc_self hu)] at ht
  rw [ht, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hD u (Ioo_subset_Icc_self hu)) (pow_nonneg (abs_nonneg _) _))
    (Nat.cast_nonneg _)

/-- The actual phase differs from its quadratic Taylor polynomial by the sharp cubic bound. -/
theorem quadratic_taylor_remainder_bound {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ uIcc c x, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ uIcc c x, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ uIcc c x, |deriv (deriv (deriv f)) u| ≤ D) :
    |f x - f c - (x - c) * deriv f c - (x - c) ^ 2 * deriv (deriv f) c / 2| ≤
      D * |x - c| ^ 3 / 6 := by
  have hd : ∀ k ≤ 2, ∀ u ∈ uIcc c x, DifferentiableAt ℝ (iteratedDeriv k f) u := by
    intro k hk
    interval_cases k <;> simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (by assumption)
  have ht := taylor_remainder_of_differentiable 2 hd
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hD)
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    iteratedDeriv_succ, iteratedDeriv_zero] at ht
  convert ht using 1
  congr 1
  ring

/-- The actual first derivative has the sharp quadratic Taylor remainder. -/
theorem derivative_taylor_remainder_bound {f : ℝ → ℝ} {c x D : ℝ}
    (hf' : ∀ u ∈ uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ uIcc c x, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ uIcc c x, |deriv (deriv (deriv f)) u| ≤ D) :
    |deriv f x - deriv f c - (x - c) * deriv (deriv f) c| ≤ D * |x - c| ^ 2 / 2 := by
  have hd : ∀ k ≤ 1, ∀ u ∈ uIcc c x, DifferentiableAt ℝ (iteratedDeriv k (deriv f)) u := by
    intro k hk
    interval_cases k <;> simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (by assumption)
  have ht := taylor_remainder_of_differentiable 1 hd
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hD)
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    iteratedDeriv_succ, iteratedDeriv_zero] at ht
  rw [sq_abs]
  convert ht using 1
  congr 1
  ring

/-- The actual centered error after subtracting the full quadratic phase. -/
noncomputable def stationaryTaylorError (f : ℝ → ℝ) (c x : ℝ) : ℝ :=
  f (c + x) - f c - x * deriv f c - x ^ 2 * deriv (deriv f) c / 2

/-- The centered cubic error bound uses only three derivatives on its genuine segment. -/
theorem stationaryTaylorError_bound {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ uIcc c (c + x), |deriv (deriv (deriv f)) u| ≤ D) :
    |stationaryTaylorError f c x| ≤ D * |x| ^ 3 / 6 := by
  simpa only [stationaryTaylorError, add_sub_cancel_left] using quadratic_taylor_remainder_bound hf hf' hf'' hD

/-- The derivative of the centered error is the actual first-derivative remainder. -/
theorem stationaryTaylorError_hasDerivAt {f : ℝ → ℝ} {c x : ℝ}
    (hf : DifferentiableAt ℝ f (c + x)) :
    HasDerivAt (stationaryTaylorError f c)
      (deriv f (c + x) - deriv f c - x * deriv (deriv f) c) x := by
  have h := (((hf.hasDerivAt.comp x ((hasDerivAt_id x).const_add c)).sub_const (f c)).sub
    ((hasDerivAt_id x).mul_const (deriv f c))).sub
      ((((hasDerivAt_id x).pow 2).mul_const (deriv (deriv f) c)).div_const 2)
  convert h using 1
  simp only [id_eq]
  ring

/-- The centered derivative error has the sharp quadratic constant 1/2. -/
theorem stationaryTaylorError_deriv_bound {f : ℝ → ℝ} {c x D : ℝ}
    (hf : DifferentiableAt ℝ f (c + x))
    (hf' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ uIcc c (c + x), |deriv (deriv (deriv f)) u| ≤ D) :
    |deriv (stationaryTaylorError f c) x| ≤ D * |x| ^ 2 / 2 := by
  rw [(stationaryTaylorError_hasDerivAt hf).deriv]
  simpa only [add_sub_cancel_left] using derivative_taylor_remainder_bound hf' hf'' hD

/-- The source exponential normalization preserves the linear phase-perturbation bound. -/
theorem norm_exp_two_pi_sub_one_le (u : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) - 1‖ ≤ 2 * Real.pi * |u| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * u)
  have he : Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) = 2 * Real.pi * Complex.I * (u : ℂ) := by
    push_cast
    ring
  simpa only [he, Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos] using h

/-- The actual nonlinear phase perturbation satisfies the cubic source bound at both orientations. -/
theorem stationaryTaylorError_exp_bound {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ uIcc c (c + x), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ uIcc c (c + x), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1‖ ≤
      Real.pi * D * |x| ^ 3 / 3 := by
  exact (norm_exp_two_pi_sub_one_le _).trans
    ((mul_le_mul_of_nonneg_left (stationaryTaylorError_bound hf hf' hf'' hD) Real.two_pi_pos.le).trans_eq (by ring))

/-- The centered nonlinear phase factors exactly into its quadratic part and Taylor perturbation. -/
theorem stationary_phase_factorization {f : ℝ → ℝ} {c ν : ℝ} (hc : deriv f c = ν) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold stationaryTaylorError
  rw [hc]
  push_cast
  ring

end DhimanKadiriQuesadaHerrera2026
