import PrimeShell.ExtendedZeroSide
import Zeta23.Assembly.Certificate
import Zeta23.XiPrime.Statement

noncomputable section

open Filter Asymptotics Topology RHLinalg

namespace PrimeShell

open Zeta23 Zeta23.Assembly

namespace PrimeShellAdmissible

/-- The exact decay rate needed by the zero-side tail is available on the
whole analytic range `lambda < 2`. -/
theorem tendsto_tail_rpow (A : PrimeShellAdmissible) :
    Tendsto (fun T : ℝ => T ^ (A.P.lam / 2 - 1)) atTop (𝓝 0) := by
  have heq : A.P.lam / 2 - 1 = -(1 - A.P.lam / 2) := by ring
  rw [heq]
  exact tendsto_rpow_neg_atTop (by linarith [A.lam_lt_two])

/-- The complete multiplicity-aware Zeta23 count certificate after removing
only the artificial support-one cap from the zero side.  Its sole new
mathematical input is the actual pair of trace/frobenius estimates on the
source matrix `Gz`; the theorem does not assume a zero-count conclusion. -/
theorem simple_bound_of_gzMoments (A : PrimeShellAdmissible)
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {κ : ℝ}
    (hM : Zeta23.XiPrime.GzMoments Z (fun _ => A.P) κ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := A.eventually_tailPackage Z hR
  obtain ⟨htrace, hfrob⟩ := hM
  have hLtop := A.tendsto_L_atTop
  have hwL : ∀ᶠ T in atTop, 8 * A.P.w ≤ A.P.L T :=
    hLtop.eventually_ge_atTop _
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ A.P.a T := by
    filter_upwards [hwL] with T hw
    exact A.half_le_a hw
  have h0 : ∀ᶠ T in atTop,
      4 * rtrace (A.P.hat T (Z.Gz A.P T)) -
          frobSq (A.P.hat T (Z.Gz A.P T)) -
          2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ) -
          θ₀ T / (A.P.a T * A.P.L T) *
            (4 + 2 * Real.sqrt (frobSq (A.P.hat T (Z.Gz A.P T))) +
              θ₀ T / (A.P.a T * A.P.L T))
        ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hwL, hapos, eventually_ge_atTop (0 : ℝ),
      eventually_l_pos] with T hTl hw ha2 hT0 hl
    have hLpos : 0 < A.P.L T := by
      rw [Params.L]
      exact mul_pos A.lambda_pos hl
    exact seamA_mult2 hT0 Zeta23.ZeroSide.phiHatConj
      Zeta23.ZeroSide.phiHatReal (A.poissonSq hw) hTl
      (by linarith) hLpos
  have hB0 : ∀ᶠ T in atTop,
      0 ≤ θ₀ T / (A.P.a T * A.P.L T) := by
    filter_upwards [hTail, hapos, eventually_l_pos]
      with T hTl ha2 hl
    have hLpos : 0 < A.P.L T := by
      rw [Params.L]
      exact mul_pos A.lambda_pos hl
    exact div_nonneg hTl.theta_nonneg (mul_pos (by linarith) hLpos).le
  have hBto : Tendsto
      (fun T => θ₀ T / (A.P.a T * A.P.L T)) atTop (𝓝 0) := by
    let K : ℝ := 2 * |Cθ| / A.P.lam
    have hK0 : 0 ≤ K := by
      dsimp [K]
      exact div_nonneg (mul_nonneg (by norm_num) (abs_nonneg Cθ)) A.lambda_pos.le
    have hup : Tendsto
        (fun T : ℝ => K * T ^ (A.P.lam / 2 - 1)) atTop (𝓝 0) := by
      simpa using A.tendsto_tail_rpow.const_mul K
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup hB0 ?_
    filter_upwards [hTail, hapos, eventually_l_pos, hθ,
      eventually_gt_atTop (0 : ℝ)] with T hTl ha2 hl hθT hT0
    have hLpos : 0 < A.P.L T := by
      rw [Params.L]
      exact mul_pos A.lambda_pos hl
    have hapos' : 0 < A.P.a T := by linarith
    have hr0 : 0 ≤ T ^ (A.P.lam / 2 - 1) := by positivity
    rw [div_le_iff₀ (mul_pos hapos' hLpos)]
    calc
      θ₀ T ≤ Cθ * Zeta23.l T * T ^ (A.P.lam / 2 - 1) := hθT
      _ ≤ |Cθ| * Zeta23.l T * T ^ (A.P.lam / 2 - 1) := by
        gcongr
        exact le_abs_self Cθ
      _ = (2 * |Cθ| / A.P.lam * T ^ (A.P.lam / 2 - 1)) *
          ((1 / 2) * A.P.L T) := by
        simp only [Params.L]
        field_simp [A.lambda_pos.ne']
      _ ≤ K * T ^ (A.P.lam / 2 - 1) *
          (A.P.a T * A.P.L T) := by
        dsimp [K]
        gcongr
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
    obtain ⟨CII, hII⟩ := Zeta23.Tail.eventually_NII_le Z hA₀ hloc
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop]
        (fun T => Real.sqrt T * Zeta23.l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos, eventually_ge_atTop (0 : ℝ)]
        with T h hl hT0
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hR
        Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)
  have hNtop := Zeta23.Assembly.tendsto_N_atTop Z hR
  exact count_certificate Z A.P κ (fun T => (Z.N0s T (2 * T) : ℝ))
    θ₀ h0 hB0 hBto hNII_o hNtop htrace hfrob

end PrimeShellAdmissible
end PrimeShell
