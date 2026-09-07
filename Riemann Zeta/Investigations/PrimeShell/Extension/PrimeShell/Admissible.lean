import PrimeShell.ShellDensity
import Zeta23.Taper

namespace PrimeShell

noncomputable section

open Zeta23 Zeta23.PrimeSide

/-- The analytic parameter class for the root-Zeta23 test family after the
bandwidth-one cap is removed.  This retains the released taper and ramp
conditions, and replaces only `Params.Valid.lam_le_one` by the exact
zero-side decay range `lambda < 2`.

It deliberately contains no arithmetic theorem and no conclusion about
zeros.  In particular, an MRT or Guth--Maynard range condition belongs to a
separate arithmetic subclass. -/
structure PrimeShellAdmissible : Type where
  P : Params
  taper : TaperProfile P.ϱ
  one_lt_lam : 1 < P.lam
  lam_lt_two : P.lam < 2
  one_le_w : 1 ≤ P.w

namespace PrimeShellAdmissible

/-- The released support-one cutoff `exp(l(T)) = T/(2*pi)`. -/
def supportOneCutoff (_A : PrimeShellAdmissible) (T : ℝ) : ℝ :=
  Real.exp (Zeta23.l T)

/-- The exact root-Zeta23 prime density in the support-one block. -/
def lowDensity (A : PrimeShellAdmissible) (T : ℝ) : ℝ → ℝ :=
  primeLowDensity (A.supportOneCutoff T)

/-- The actual additive prime shell between support one and the complete
cutoff `X = exp(lambda*l(T))`.  This is a decomposition of the source
density, not a zero gap in the positive test window. -/
def highDensity (A : PrimeShellAdmissible) (T : ℝ) : ℝ → ℝ :=
  primeHighShellDensity (A.supportOneCutoff T) (A.P.X T)

theorem lambda_pos (A : PrimeShellAdmissible) : 0 < A.P.lam :=
  zero_lt_one.trans A.one_lt_lam

/-- The literal support-one cutoff agrees with the usual physical scale. -/
theorem supportOneCutoff_eq (A : PrimeShellAdmissible) {T : ℝ}
    (hT : 0 < T) :
    A.supportOneCutoff T = T / (2 * Real.pi) := by
  unfold supportOneCutoff Zeta23.l
  rw [Real.exp_log]
  exact div_pos hT (mul_pos (by norm_num) Real.pi_pos)

/-- Exact source entry for the extended family. -/
theorem fullDensity_eq_low_add_high (A : PrimeShellAdmissible) (T : ℝ) :
    Zeta23.PX (A.P.X T) = A.lowDensity T + A.highDensity T :=
  PX_eq_primeLowDensity_add_primeHighShellDensity
    (A.supportOneCutoff T) (A.P.X T)

/-- The complete four-term prime-prime trace identity attached to the
actual root-Zeta23 source object. -/
theorem primePrime_eq_four_terms (A : PrimeShellAdmissible)
    (hΦ : Continuous Φ) (T : ℝ) :
    Mform Φ T (Zeta23.PX (A.P.X T)) (Zeta23.PX (A.P.X T)) =
      (primeShellTraceTerms Φ T (A.supportOneCutoff T) (A.P.X T)).lowLow +
      (primeShellTraceTerms Φ T (A.supportOneCutoff T) (A.P.X T)).lowHigh +
      (primeShellTraceTerms Φ T (A.supportOneCutoff T) (A.P.X T)).highLow +
      (primeShellTraceTerms Φ T (A.supportOneCutoff T) (A.P.X T)).highHigh :=
  primePrime_eq_four_additive_shell_terms hΦ T
    (A.supportOneCutoff T) (A.P.X T)

end PrimeShellAdmissible

/-- The subclass whose upper cutoff actually reaches the strict MRT
long-shift threshold.  The inequality is an arithmetic range condition,
not part of analytic admissibility. -/
structure PrimeShellMRTAdmissible : Type extends PrimeShellAdmissible where
  mrt_overlap : (33 / 25 : ℝ) < toPrimeShellAdmissible.P.lam

/-- The analytic subrange in which the released explicit-formula contour
still has a positive displacement.  The source proof chooses
`δ = (1 - 3 * λ / 4) / 2`; hence `λ < 4/3`, rather than merely `λ < 2`, is
the faithful upper endpoint for the complete prime/zero chain. -/
structure PrimeShellFullChainAdmissible : Type extends PrimeShellAdmissible where
  three_mul_lam_lt_four : 3 * toPrimeShellAdmissible.P.lam < 4

namespace PrimeShellFullChainAdmissible

theorem lambda_lt_four_thirds (A : PrimeShellFullChainAdmissible) :
    A.toPrimeShellAdmissible.P.lam < (4 / 3 : ℝ) := by
  linarith [A.three_mul_lam_lt_four]

theorem explicitFormulaDelta_pos (A : PrimeShellFullChainAdmissible) :
    0 < (1 - 3 * A.toPrimeShellAdmissible.P.lam / 4) / 2 := by
  linarith [A.three_mul_lam_lt_four]

end PrimeShellFullChainAdmissible

/-- The nonempty overlap in which both the released explicit-formula
displacement and the long-shift range of MRT Theorem 1.3(i) are available. -/
structure PrimeShellMRTFullChainAdmissible : Type extends
    PrimeShellFullChainAdmissible where
  mrt_overlap : (33 / 25 : ℝ) <
    toPrimeShellFullChainAdmissible.toPrimeShellAdmissible.P.lam

/-- A concrete nonempty extended analytic class.  This proves that the old
`IsEmpty` result was an artefact of imposing a zero gap on the window
profile, rather than a no-go for the additive prime-density shell. -/
def concretePrimeShellParams : Params :=
  ⟨Taper.smoothstep, 199 / 150, 1⟩

def concretePrimeShellAdmissible : PrimeShellAdmissible where
  P := concretePrimeShellParams
  taper := Taper.taperProfile_smoothstep
  one_lt_lam := by norm_num [concretePrimeShellParams]
  lam_lt_two := by norm_num [concretePrimeShellParams]
  one_le_w := by norm_num [concretePrimeShellParams]

def concretePrimeShellMRTAdmissible : PrimeShellMRTAdmissible where
  toPrimeShellAdmissible := concretePrimeShellAdmissible
  mrt_overlap := by norm_num [concretePrimeShellAdmissible, concretePrimeShellParams]

def concretePrimeShellFullChainAdmissible : PrimeShellFullChainAdmissible where
  toPrimeShellAdmissible := concretePrimeShellAdmissible
  three_mul_lam_lt_four := by
    norm_num [concretePrimeShellAdmissible, concretePrimeShellParams]

def concretePrimeShellMRTFullChainAdmissible : PrimeShellMRTFullChainAdmissible where
  toPrimeShellFullChainAdmissible := concretePrimeShellFullChainAdmissible
  mrt_overlap := by
    norm_num [concretePrimeShellFullChainAdmissible, concretePrimeShellAdmissible,
      concretePrimeShellParams]

theorem primeShellAdmissible_nonempty : Nonempty PrimeShellAdmissible :=
  ⟨concretePrimeShellAdmissible⟩

theorem primeShellMRTAdmissible_nonempty : Nonempty PrimeShellMRTAdmissible :=
  ⟨concretePrimeShellMRTAdmissible⟩

theorem primeShellFullChainAdmissible_nonempty :
    Nonempty PrimeShellFullChainAdmissible :=
  ⟨concretePrimeShellFullChainAdmissible⟩

theorem primeShellMRTFullChainAdmissible_nonempty :
    Nonempty PrimeShellMRTFullChainAdmissible :=
  ⟨concretePrimeShellMRTFullChainAdmissible⟩

end

end PrimeShell
