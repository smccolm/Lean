import Mathlib
import Theorems.Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one
import P2M.Util
namespace P2MW.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat

theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by
  rw [Ring.krullDimLE_iff]
  have h := ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one A
  rw [trdeg_eq_zero, map_zero] at h
  simpa using h
