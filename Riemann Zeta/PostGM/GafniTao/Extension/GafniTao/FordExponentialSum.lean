import GafniTao.FordSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ford's shifted logarithmic exponential sum

This is the finite source object in Ford's Theorem 2.  The endpoint
convention is `N < n ≤ R`, represented by `Finset.Ioc N R`; the shift is the
literal real parameter `0 < u ≤ 1`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordShiftedLogPhase (n : ℕ) (u t : ℝ) : ℂ :=
  Complex.exp (-I * (t * Real.log (n + u) : ℝ))

def fordShiftedExponentialSum
    (N R : ℕ) (u t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N R, fordShiftedLogPhase n u t

def fordLambda (N : ℕ) (t : ℝ) : ℝ :=
  Real.log t / Real.log N

/-- Pointwise form of Ford's Theorem 2.  Since the integer endpoint set is
finite and the shift interval is compact, this is equivalent to the two
maxima in the paper, while being the useful consumer interface in Lean. -/
def FordExponentialSumEstimate (C D : ℝ) : Prop :=
  ∀ ⦃N R : ℕ⦄ ⦃u t : ℝ⦄,
    0 < N → (N : ℝ) ≤ t → 0 < u → u ≤ 1 →
    N < R → R ≤ 2 * N →
    ‖fordShiftedExponentialSum N R u t‖ ≤
      C * (N : ℝ) ^ (1 - 1 / (D * fordLambda N t ^ 2))

def FordTheorem2 : Prop :=
  FordExponentialSumEstimate 9.463 133.66

theorem norm_fordShiftedLogPhase (n : ℕ) (u t : ℝ) :
    ‖fordShiftedLogPhase n u t‖ = 1 := by
  unfold fordShiftedLogPhase
  rw [Complex.norm_exp]
  simp

theorem norm_fordShiftedExponentialSum_le_card
    (N R : ℕ) (u t : ℝ) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (Finset.Ioc N R).card := by
  unfold fordShiftedExponentialSum
  calc
    ‖∑ n ∈ Finset.Ioc N R, fordShiftedLogPhase n u t‖ ≤
        ∑ n ∈ Finset.Ioc N R, ‖fordShiftedLogPhase n u t‖ :=
      norm_sum_le _ _
    _ = (Finset.Ioc N R).card := by
      simp only [norm_fordShiftedLogPhase, sum_const, nsmul_eq_mul,
        mul_one]

theorem norm_fordShiftedExponentialSum_le_N
    {N R : ℕ} (hR : R ≤ 2 * N) (u t : ℝ) :
    ‖fordShiftedExponentialSum N R u t‖ ≤ N := by
  refine (norm_fordShiftedExponentialSum_le_card N R u t).trans ?_
  rw [Nat.card_Ioc]
  norm_cast
  omega

theorem fordLambda_sq_eq
    {N : ℕ} {t : ℝ} (hN : 1 < N) :
    fordLambda N t ^ 2 = Real.log t ^ 2 / Real.log N ^ 2 := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  unfold fordLambda
  field_simp [hlogN]

theorem fordTheorem2_exponent_eq
    {N : ℕ} {t D : ℝ} (hN : 1 < N) (htN : (N : ℝ) ≤ t)
    (hD : D ≠ 0) :
    1 - 1 / (D * fordLambda N t ^ 2) =
      1 - Real.log N ^ 2 / (D * Real.log t ^ 2) := by
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  have hlogt : Real.log t ≠ 0 := by
    have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
    have htOne : 1 < t := hNreal.trans_le htN
    exact ne_of_gt (Real.log_pos htOne)
  unfold fordLambda
  field_simp [hlogN, hlogt, hD]

#print axioms norm_fordShiftedExponentialSum_le_N
#print axioms fordTheorem2_exponent_eq

end

end GafniTao
