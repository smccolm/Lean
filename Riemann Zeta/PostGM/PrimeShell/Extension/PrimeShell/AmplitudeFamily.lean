import PrimeShell.ExtendedFamilyHyps
import Zeta23.XiPrime.FamilyHypsV

namespace PrimeShell

noncomputable section

open Filter Function MeasureTheory Set
open Zeta23

/-- A directly specified amplitude for a multi-band test function.

Unlike `XiPrime.WindowProfile`, this structure does not require strict
positivity.  Zeros of `q` are allowed because the test function is formed
from `q` itself, rather than by asking Lean to construct a smooth square
root of a merely nonnegative profile. -/
structure AmplitudeProfile (q : ℝ → ℝ) : Prop where
  even : ∀ s : ℝ, q (-s) = q s
  contDiff : ContDiff ℝ 3 q
  nonneg : ∀ s : ℝ, 0 ≤ q s
  le_one : ∀ s : ℝ, q s ≤ 1
  deriv_bound : ∃ H : ℝ, 1 ≤ H ∧
    ∀ i : ℕ, i ≤ 3 → ∀ s : ℝ, |iteratedDeriv i q s| ≤ H

/-- The nonnegative profile associated to an amplitude. -/
def amplitudeSq (q : ℝ → ℝ) (s : ℝ) : ℝ := q s ^ 2

theorem amplitudeSq_even {q : ℝ → ℝ} (hq : AmplitudeProfile q) :
    ∀ s : ℝ, amplitudeSq q (-s) = amplitudeSq q s := by
  intro s
  simp only [amplitudeSq, hq.even]

/-- At the active height, `atV (q²)` is literally the amplitude-modulated
test function `q(u/L) * phi(u)`.  This is the source-entry identity that
prevents a zero of `q` from being confused with a nonsmooth square root. -/
theorem atAmplitude_phi
    {P : Params} {q : ℝ → ℝ} (hq : AmplitudeProfile q)
    (T : ℝ) (hw : P.w ≠ 0) :
    (P.atV (amplitudeSq q) T).phi T =
      fun u => q (u / P.L T) * P.phi T u := by
  rw [Params.atV_phi T hw (amplitudeSq_even hq)]
  funext u
  rw [Params.phiV_eq]
  have hq0 : 0 ≤ q (u / P.L T) := hq.nonneg _
  simp only [amplitudeSq]
  rw [max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hq0]
  rfl

/-- Every bounded `C³` even amplitude, including a genuinely disconnected
one, gives a valid extended explicit-formula family throughout `3λ < 4`.
This proves the analytic entry bridge directly and does not use the released
strictly-positive `WindowProfile` interface. -/
theorem extendedFamilyHyps_atAmplitude
    (A : PrimeShellFullChainAdmissible) {q : ℝ → ℝ}
    (hq : AmplitudeProfile q) :
    ExtendedFamilyHyps
      (A.toPrimeShellAdmissible.P.atV (amplitudeSq q)) := by
  let P := A.toPrimeShellAdmissible.P
  have hTaper : TaperProfile P.ϱ := A.toPrimeShellAdmissible.taper
  have hLamPos : 0 < P.lam := A.toPrimeShellAdmissible.lambda_pos
  have hThree : 3 * P.lam < 4 := A.three_mul_lam_lt_four
  have hWOne : 1 ≤ P.w := A.toPrimeShellAdmissible.one_le_w
  have hWPos : 0 < P.w := one_pos.trans_le hWOne
  obtain ⟨B, hB0, hB⟩ :=
    Zeta23.XiPrime.FamilyHypsC3.exists_deriv_bound hTaper
  obtain ⟨H, hHOne, hH⟩ := hq.deriv_bound
  refine ⟨⟨P.lam, hLamPos, hThree, fun _ => rfl⟩, ?_⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((Zeta23.Assembly.tendsto_L_atTop P hLamPos).eventually_ge_atTop (8 * P.w))
  refine ⟨8 * (2 * B + 1) * H, T₀, fun T hT => ?_⟩
  have hEight : 8 * P.w ≤ P.L T := hT₀ T hT
  have hTwo : 2 * P.w ≤ P.L T := by linarith
  have hLOne : 1 ≤ P.L T := by linarith
  have hLPos : 0 < P.L T := by linarith
  have hPhi : (P.atV (amplitudeSq q) T).phi T =
      fun u => Zeta23.XiPrime.FamilyHypsV.gfac q (P.L T) u *
        Taper.phi P.ϱ (P.L T) P.w u := by
    rw [atAmplitude_phi hq T hWPos.ne']
    funext u
    simp only [Zeta23.XiPrime.FamilyHypsV.gfac, Params.phi,
      Taper.phi, div_eq_inv_mul]
  rw [hPhi]
  refine ⟨?_, ?_, ?_, ?_, fun j hjOne hjThree => ?_⟩
  · exact (Zeta23.XiPrime.FamilyHypsV.gfac_contDiff hq.contDiff).mul
      (Taper.phi_contDiff hTaper hWPos hTwo)
  · refine closure_minimal ?_ isClosed_Icc
    intro u hu
    have hBase : Taper.phi P.ϱ (P.L T) P.w u ≠ 0 := by
      intro hzero
      apply hu
      simp [hzero]
    exact Taper.phi_support_subset hTaper hWPos hBase
  · intro u
    simp only [Zeta23.XiPrime.FamilyHypsV.gfac, Taper.phi_even]
    rw [show (P.L T)⁻¹ * -u = -((P.L T)⁻¹ * u) by ring, hq.even]
  · intro u
    unfold Zeta23.XiPrime.FamilyHypsV.gfac
    rw [abs_mul, abs_of_nonneg (hq.nonneg _),
      abs_of_nonneg (Taper.phi_nonneg hTaper u)]
    simpa using mul_le_mul (hq.le_one _) (Taper.phi_le_one hTaper u)
      (Taper.phi_nonneg hTaper u) zero_le_one
  · exact Zeta23.XiPrime.FamilyHypsV.integral_abs_iteratedDeriv_mul_le
      hTaper hB0 hB hWOne hTwo hLOne hq.contDiff hHOne hH hjOne hjThree

end

end PrimeShell
