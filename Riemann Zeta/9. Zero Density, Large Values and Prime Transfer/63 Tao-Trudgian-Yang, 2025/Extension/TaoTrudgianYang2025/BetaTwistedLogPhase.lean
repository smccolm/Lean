import TaoTrudgianYang2025.BetaPhaseNormalization
import TaoTrudgianYang2025.BetaLogCoherence

/-!
# Genuine logarithmic model phases with a small resonant linear correction

The correction affects only the first derivative. Its higher jets vanish,
including under the source's closed-interval within-derivative convention.
Rounding T/N upwards makes the linear coefficient at the integer source
endpoint integral, with correction smaller than N/T.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def twistedLogPhase (c u : ℝ) : ℝ := Real.log u+c*(u-1)

theorem twistedLogPhase_approximate (P : ℕ) {c δ : ℝ} (hc : |c| ≤ δ) :
    IsApproximateModelPhaseFunction (twistedLogPhase c) 1 P δ := by
  have hcorrection : ContDiff ℝ ∞ (fun u : ℝ => c*(u-1)) := by fun_prop
  have hderiv : deriv (fun u : ℝ => c*(u-1)) = fun _ => c := by
    ext u
    convert (((hasDerivAt_id u).sub_const 1).const_mul c).deriv using 1
    ring
  have hmodel := referencePlusCorrection_approximate hcorrection 1 P (ε := δ) (by
    intro u _ n _
    rw [iteratedDeriv_succ',hderiv,iteratedDeriv_const]
    split_ifs
    · exact hc
    · simpa only [abs_zero] using (abs_nonneg c).trans hc)
  simpa only [twistedLogPhase,referenceModelPrimitive,if_pos rfl] using hmodel

def betaResonantCorrection (T N : ℝ) : ℝ :=
  (N/T)*((⌈T/N⌉₊ : ℝ)-T/N)

theorem betaResonantCorrection_bounds {T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    0 ≤ betaResonantCorrection T N ∧ betaResonantCorrection T N < N/T := by
  have hlower := Nat.le_ceil (T/N)
  have hupper := Nat.ceil_lt_add_one (div_nonneg hT.le hN.le)
  unfold betaResonantCorrection
  constructor
  · exact mul_nonneg (div_nonneg hN.le hT.le) (sub_nonneg.mpr hlower)
  · calc
      (N/T)*((⌈T/N⌉₊ : ℝ)-T/N) < (N/T)*1 :=
        mul_lt_mul_of_pos_left (by linarith) (div_pos hN hT)
      _ = N/T := mul_one _

theorem betaResonantCorrection_integer_slope {T N : ℝ}
    (hT : T ≠ 0) (hN : N ≠ 0) :
    T*(1+betaResonantCorrection T N) = (⌈T/N⌉₊ : ℝ)*N := by
  unfold betaResonantCorrection
  field_simp
  ring

theorem betaResonantCorrection_model {T N δ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hsmall : N/T ≤ δ) (P : ℕ) :
    IsApproximateModelPhaseFunction (twistedLogPhase (betaResonantCorrection T N)) 1 P δ := by
  have hc := betaResonantCorrection_bounds hT hN
  apply twistedLogPhase_approximate P
  rw [abs_of_nonneg hc.1]
  exact hc.2.le.trans hsmall

end TaoTrudgianYang2025
