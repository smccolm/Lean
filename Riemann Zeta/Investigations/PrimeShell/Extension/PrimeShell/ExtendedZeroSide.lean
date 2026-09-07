import PrimeShell.Admissible
import Zeta23.Tail.Package
import Zeta23.ZeroSide.Final
import Zeta23.Assembly.SeamMult
import Zeta23.Hypotheses.GzGp

noncomputable section

open Filter Complex RHLinalg

namespace PrimeShell
namespace PrimeShellAdmissible

open Zeta23

/-- The ramp width is positive in the extended parameter class. -/
theorem w_pos (A : PrimeShellAdmissible) : 0 < A.P.w :=
  zero_lt_one.trans_le A.one_le_w

/-- `L(T) = lambda * log(T/(2*pi))` still tends to infinity when the
support-one cap is removed.  Only positivity of `lambda` is used. -/
theorem tendsto_L_atTop (A : PrimeShellAdmissible) :
    Tendsto (fun T => A.P.L T) atTop atTop := by
  unfold Params.L Zeta23.l
  apply Tendsto.const_mul_atTop A.lambda_pos
  exact Real.tendsto_log_atTop.comp
    (tendsto_id.atTop_div_const (by positivity))

/-- The source taper only needs `2w <= L`; the stronger `8w <= L` is the
eventual convention used by the released assembly. -/
theorem two_w_le (A : PrimeShellAdmissible) {T : ℝ}
    (hwL : 8 * A.P.w ≤ A.P.L T) :
    2 * A.P.w ≤ A.P.L T := by
  nlinarith [A.one_le_w]

/-- The normalization constant remains bounded below beyond support one.
This is the released taper argument with no use of `lambda <= 1`. -/
theorem half_le_a (A : PrimeShellAdmissible) {T : ℝ}
    (hwL : 8 * A.P.w ≤ A.P.L T) :
    1 / 2 ≤ A.P.a T := by
  have h2 := A.two_w_le hwL
  have hb_le_a := Taper.bConst_le_aConst A.taper A.w_pos h2
  have hone_sub := Taper.one_sub_le_bConst A.taper A.w_pos h2
  have hL : 0 < A.P.L T := by nlinarith [A.one_le_w]
  have hquarter : 2 * A.P.w / A.P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]
    linarith
  change 1 / 2 ≤ Taper.aConst A.P.ϱ (A.P.L T) A.P.w
  change Taper.bConst A.P.ϱ (A.P.L T) A.P.w ≤
    Taper.aConst A.P.ϱ (A.P.L T) A.P.w at hb_le_a
  change 1 - 2 * A.P.w / A.P.L T ≤
    Taper.bConst A.P.ϱ (A.P.L T) A.P.w at hone_sub
  linarith

/-- The second-derivative norm bound required by the tail estimate. -/
theorem C1_le (A : PrimeShellAdmissible) {T : ℝ}
    (hwL : 8 * A.P.w ≤ A.P.L T) :
    A.P.C1 T ≤ 2 * Taper.l1Deriv2 A.P.ϱ := by
  exact Taper.C1_le A.taper A.one_le_w (A.two_w_le hwL)

/-- The exact strip-decay estimate for the released taper, valid throughout
the enlarged analytic range. -/
theorem norm_phiHat_sub_I_mul_le (A : PrimeShellAdmissible) {T : ℝ}
    (hwL : 8 * A.P.w ≤ A.P.L T) (r y : ℝ)
    (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖A.P.phiHat T (r - I * y)‖ ≤
      Real.exp (A.P.L T / 4) * A.P.C1 T /
        ‖(r : ℂ) - I * y‖ ^ 2 := by
  exact Taper.norm_phiHat_sub_I_mul_le A.taper A.w_pos
    (A.two_w_le hwL) r y hy hz

/-- The exact Poisson square identity needed by the multiplicity seam. -/
theorem poissonSq (A : PrimeShellAdmissible) {T : ℝ}
    (hwL : 8 * A.P.w ≤ A.P.L T) :
    Zeta23.ZeroSide.PoissonSq T A.P := by
  intro γ
  exact Taper.hasSum_phiHatR_sq A.taper A.w_pos
    (A.two_w_le hwL) T γ

/-- The quantitative tail majorant does not use the support-one cap. -/
theorem theta0_le (A : PrimeShellAdmissible) {T A₀ C₁ R : ℝ}
    (hT : Zeta23.Tail.T₀ ≤ T) (hA₀ : 0 ≤ A₀)
    (hC₁ : 0 ≤ C₁) (hC₁R : C₁ ≤ 2 * R) :
    Zeta23.Tail.theta0 A₀ (Real.exp (A.P.L T / 4) * C₁) T ≤
      32 * A₀ * R ^ 2 * Zeta23.l T * T ^ (A.P.lam / 2 - 1) := by
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : 0 < T := by linarith
  have hexp : Real.exp (A.P.L T / 4) ^ 2 ≤ T ^ (A.P.lam / 2) := by
    rw [← Real.exp_nat_mul]
    push_cast
    have heq : (2 : ℝ) * (A.P.L T / 4) =
        (A.P.lam / 2) * Real.log (T / (2 * Real.pi)) := by
      unfold Params.L Zeta23.l
      ring
    rw [heq, ← Real.log_rpow (by positivity), Real.exp_log (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith [A.lambda_pos])
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  have hlog := Zeta23.Tail.log_four_mul_le_two_mul_l hT
  have hl0 : 0 ≤ Zeta23.l T := by
    have := Zeta23.Tail.one_le_log_four_mul hT
    linarith
  have hK2 : (Real.exp (A.P.L T / 4) * C₁) ^ 2 ≤
      T ^ (A.P.lam / 2) * (4 * R ^ 2) := by
    rw [mul_pow]
    apply mul_le_mul hexp _ (by positivity) (by positivity)
    nlinarith
  unfold Zeta23.Tail.theta0
  rw [div_le_iff₀ hT0]
  have hTpow : T ^ (A.P.lam / 2 - 1) * T = T ^ (A.P.lam / 2) := by
    rw [Real.rpow_sub hT0, Real.rpow_one, div_mul_cancel₀ _ hT0.ne']
  calc
    4 * A₀ * (Real.exp (A.P.L T / 4) * C₁) ^ 2 * Real.log (4 * T)
        ≤ 4 * A₀ * (T ^ (A.P.lam / 2) * (4 * R ^ 2)) *
            (2 * Zeta23.l T) := by
          apply mul_le_mul _ hlog
            (by linarith [Zeta23.Tail.one_le_log_four_mul hT]) (by positivity)
          exact mul_le_mul_of_nonneg_left hK2 (by positivity)
    _ = 32 * A₀ * R ^ 2 * Zeta23.l T *
          T ^ (A.P.lam / 2 - 1) * T := by
          rw [mul_assoc _ _ T, hTpow]
          ring

/-- The complete released tail-input construction, generalized only by
replacing `lambda <= 1` with the hypotheses actually used by its proof. -/
theorem eventually_tailPackage (A : PrimeShellAdmissible)
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∃ θ₀ : ℝ → ℝ,
      (∀ᶠ T in atTop, Zeta23.Assembly.TailInputs Z A.P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop,
        θ₀ T ≤ C * Zeta23.l T * T ^ (A.P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  have hwL : ∀ᶠ T in atTop, 8 * A.P.w ≤ A.P.L T :=
    A.tendsto_L_atTop.eventually_ge_atTop _
  let θ₀ : ℝ → ℝ := fun T =>
    Zeta23.Tail.theta0 A₀
      (Real.exp (A.P.L T / 4) * A.P.C1 T) T
  refine ⟨θ₀, ?_, 32 * A₀ * (Taper.l1Deriv2 A.P.ϱ) ^ 2, ?_⟩
  · have hL2 : ∀ᶠ T in atTop, 2 ≤ A.P.L T :=
      A.tendsto_L_atTop.eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop Zeta23.Tail.T₀, hL2, hwL]
      with T hT hL hw
    have hdecay := fun r y hy hz => A.norm_phiHat_sub_I_mul_le hw r y hy hz
    have hTail : Zeta23.Tail.TailHyp Z A.P T A₀ (A.P.C1 T) :=
      { hT := hT
        hL := hL
        hA₀ := hA₀
        hloc := hloc
        hC₁ := Zeta23.Tail.C1_nonneg A.P T
        hdecay := hdecay }
    exact hTail.tailInputs (by linarith [A.half_le_a hw])
      (Zeta23.GzGp.phiHat_conj A.P T)
  · filter_upwards [eventually_ge_atTop Zeta23.Tail.T₀, hwL] with T hT hw
    exact A.theta0_le hT (by linarith) (Zeta23.Tail.C1_nonneg A.P T)
      (A.C1_le hw)

end PrimeShellAdmissible
end PrimeShell
