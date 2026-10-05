import DongWangWangZhang2026.ZetaSum
import Mathlib.Topology.Order.Compact

/-!
# The actual maximizing twist

This proves existence at the source's shifted zeta function, not at an
abstract supplied maximizer. Quantitative displacement, distance and comparison
are proved downstream in `TwistBounds`; uniform Lipschitz remains open.
-/

namespace DongWangWangZhang2026

open Complex Set

noncomputable section

/-- The zeta argument in equation (2.4), for the twist variable `u`. -/
def twistZetaPoint (x t u : ℝ) : ℂ :=
  ((1 + 1 / Real.log x : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * I

theorem twistZetaPoint_re (x t u : ℝ) :
    (twistZetaPoint x t u).re = 1 + 1 / Real.log x := by
  simp [twistZetaPoint]

theorem twistZetaPoint_ne_one {x : ℝ} (hx : 1 < x) (t u : ℝ) :
    twistZetaPoint x t u ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [twistZetaPoint_re] at hre
  have hpos := one_div_pos.mpr (Real.log_pos hx)
  simp only [Complex.one_re] at hre
  linarith

theorem continuous_twistZetaNorm {x : ℝ} (hx : 1 < x) (t : ℝ) :
    Continuous (fun u : ℝ => ‖riemannZeta (twistZetaPoint x t u)‖) := by
  have hp : Continuous (twistZetaPoint x t) := by
    unfold twistZetaPoint
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro u
  exact ((differentiableAt_riemannZeta (twistZetaPoint_ne_one hx t u)).continuousAt.comp
    hp.continuousAt).norm

/-- Source-faithful maximum attainment on `[-log x,log x]`. -/
theorem exists_maximizingTwist {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      ∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤
          ‖riemannZeta (twistZetaPoint x t t₀)‖ := by
  have hlog := (Real.log_pos hx).le
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Set.Icc (-Real.log x) (Real.log x))
    ⟨0, by constructor <;> linarith⟩ (continuous_twistZetaNorm hx t).continuousOn
  refine ⟨u, abs_le.mpr hu, fun v hv => hmax (abs_le.mp hv)⟩

/-- The squared pretentious distance in equation (2.5), at spectral difference `τ`. -/
def primePhaseDistance (x τ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (zetaTerm τ p).re) / p

theorem primePhaseDistance_nonneg (x τ : ℝ) : 0 ≤ primePhaseDistance x τ := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hre := Complex.re_le_norm (zetaTerm τ p)
  rw [norm_zetaTerm τ hprime.pos] at hre
  exact div_nonneg (sub_nonneg.mpr hre) (Nat.cast_nonneg p)

/-- The exact unit-circle identity behind the source's Cauchy--Schwarz step. -/
theorem norm_one_sub_zetaTerm_sq (τ : ℝ) {p : ℕ} (hp : 0 < p) :
    ‖1 - zetaTerm τ p‖ ^ 2 = 2 * (1 - (zetaTerm τ p).re) := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, norm_zetaTerm τ hp,
    norm_one, one_pow, one_mul, Complex.conj_re]
  ring

/-- Weighted prime Cauchy--Schwarz for the actual phase, with no assumed distance bound. -/
theorem prime_phase_deviation_sq_le (x τ : ℝ) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) ^ 2 ≤
      2 * primePhaseDistance x τ *
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
  let primes := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  have hsq : (∑ p ∈ primes, ‖1 - zetaTerm τ p‖ ^ 2 / p) =
      2 * primePhaseDistance x τ := by
    rw [primePhaseDistance, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [norm_one_sub_zetaTerm_sq τ (Finset.mem_filter.mp hp).2.pos]
    ring
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul primes
    (f := fun p => (1 : ℝ) / p)
    (g := fun p => ‖1 - zetaTerm τ p‖ ^ 2 / p)
    (r := fun p => ‖1 - zetaTerm τ p‖ / p)
    (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    (fun p _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
    (fun p _ => by dsimp; apply le_of_eq; ring)
  rw [hsq] at h
  change _ ≤ _ * _
  nlinarith [h]

theorem prime_phase_deviation_le (x τ : ℝ) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) ≤
      Real.sqrt (2 * primePhaseDistance x τ *
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) :=
  Real.le_sqrt_of_sq_le (prime_phase_deviation_sq_le x τ)

/-- The spectral difference is exactly the source's pretentious twist, not a new phase. -/
theorem primePhaseDistance_eq_twisted (x t t₀ : ℝ) :
    primePhaseDistance x (t - t₀) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        (1 - (zetaTerm t p * star (zetaTerm t₀ p)).re) / p := by
  simp only [primePhaseDistance, zetaTerm_sub]

end
end DongWangWangZhang2026
