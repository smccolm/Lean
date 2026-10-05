import DhimanKadiriQuesadaHerrera2026.FresnelEvaluation
import DhimanKadiriQuesadaHerrera2026.WeightedIntegralPhase

/-! # Actual stationary points and the negative-curvature branch

The derivative range determines the unique stationary point of f(x)−νx.
The evaluated quadratic integral supplies the source phase −1/8; the separate
B-process gate must still control replacement of the original phase by its
quadratic expansion and prove the advertised numerical error constants.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped Topology

/-- Each frequency in the decreasing derivative range has a unique actual stationary point. -/
theorem existsUnique_stationaryPoint {f : ℝ → ℝ} {a b ν : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : StrictAntiOn (deriv f) (Set.Icc a b))
    (hν : ν ∈ Set.Icc (deriv f b) (deriv f a)) :
    ∃! x : ℝ, x ∈ Set.Icc a b ∧ deriv f x = ν := by
  obtain ⟨x, hx, hv⟩ := intermediate_value_Icc' hab hc hν
  exact ⟨x, ⟨hx, hv⟩, fun y hy => hm.injOn hy.1 hx (hy.2.trans hv.symm)⟩

/-- At that point the actual shifted phase has derivative zero. -/
theorem stationary_shift_hasDerivAt {f : ℝ → ℝ} {x ν : ℝ}
    (hd : DifferentiableAt ℝ f x) (hv : deriv f x = ν) :
    HasDerivAt (fun u => f u - ν * u) 0 x := by
  simpa only [id_eq, mul_one, hv, sub_self] using
    hd.hasDerivAt.sub ((hasDerivAt_id x).const_mul ν)

/-- The logarithmic J-phase has precisely the positive critical point used in its physical scale. -/
theorem weightedIntegralPhase_stationary_iff {t m u : ℝ}
    (hm : 0 < m) (hu : 0 < u) :
    deriv (weightedIntegralPhase t m) u = 0 ↔ u = t / (2 * Real.pi * m) := by
  rw [(weightedIntegralPhase_hasDerivAt t m hu).deriv, sub_eq_zero]
  constructor
  · intro h
    apply (eq_div_iff (by positivity : 2 * Real.pi * m ≠ 0)).mpr
    have ht := (eq_div_iff hu.ne').mp h
    nlinarith
  · intro h
    apply (eq_div_iff hu.ne').mpr
    have ht := (eq_div_iff (by positivity : 2 * Real.pi * m ≠ 0)).mp h
    nlinarith

/-- Positive heights give an actual positive stationary point; negative heights give none. -/
theorem weightedIntegralPhase_stationary_exists_iff {t m : ℝ} (hm : 0 < m) :
    (∃ u : ℝ, 0 < u ∧ deriv (weightedIntegralPhase t m) u = 0) ↔ 0 < t := by
  constructor
  · rintro ⟨u, hu, hd⟩
    have he := (weightedIntegralPhase_stationary_iff hm hu).mp hd
    have ht := (eq_div_iff (by positivity : 2 * Real.pi * m ≠ 0)).mp he
    rw [← ht]
    positivity
  · intro ht
    have hp : 0 < t / (2 * Real.pi * m) := by positivity
    exact ⟨_, hp, (weightedIntegralPhase_stationary_iff hm hp).mpr rfl⟩

/-- The evaluated negative-curvature quadratic integral has exactly the source's −1/8 phase.
This is a limit of finite oscillatory integrals, not an absolute whole-line integral. -/
theorem quadratic_stationary_phase_limit (A : ℝ) {κ : ℝ} (hκ : κ < 0) :
    Filter.Tendsto (fun H : ℝ => ∫ v in (-H)..H,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A + κ * v ^ 2 / 2 : ℝ) : ℂ)))
        Filter.atTop (𝓝 (Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |κ| : ℂ))) := by
  have hc : 0 < -κ / 2 := by linarith
  have he (v : ℝ) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A + κ * v ^ 2 / 2 : ℝ) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ)) *
        Complex.exp (((-2 * Real.pi * (-κ / 2) * v ^ 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  have h := (tendsto_quadraticWindow hc).const_mul
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ)))
  have hv : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ)) *
      (Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) / (Real.sqrt (2 * (-κ / 2)) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ) := by
    rw [← mul_div_assoc, ← Complex.exp_add,
      show 2 * (-κ / 2) = |κ| by rw [abs_of_neg hκ]; ring]
    congr 2
    push_cast
    ring
  simpa only [quadraticWindow, hv] using h

end DhimanKadiriQuesadaHerrera2026
