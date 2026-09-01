import GafniTao.FordPositiveIntegralFormula

open GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

structure PositiveEqualityBundle where
  source : Polynomial ℚ
  explicit : Polynomial ℚ
  source_eq : source = fordPositiveIntegralFormula fordPositiveTaylorPower11
  explicit_eq : explicit = fordPositiveAtThreeHalvesExplicit

opaque positiveEqualityBundle : PositiveEqualityBundle :=
  ⟨fordPositiveIntegralFormula fordPositiveTaylorPower11,
    fordPositiveAtThreeHalvesExplicit, rfl, rfl⟩

def positiveEval (p : Polynomial ℚ) (x : ℚ) : ℚ := Polynomial.eval x p
theorem positiveEval_eq (p : Polynomial ℚ) (x : ℚ) :
    positiveEval p x = Polynomial.eval x p := rfl
attribute [irreducible] positiveEval

example : positiveEqualityBundle.source = positiveEqualityBundle.explicit := by
  apply Polynomial.funext
  intro y
  rw [← positiveEval_eq, ← positiveEval_eq]
  rw [positiveEqualityBundle.source_eq, positiveEqualityBundle.explicit_eq]
  rw [positiveEval_eq, positiveEval_eq]
  rw [fordPositiveIntegralFormula_eval]
  norm_num [fordPositivePrimitiveCandidateValue,
    fordPositiveTaylorPower11, fordPositiveAtThreeHalvesExplicit,
    Finset.sum_range_succ]
  ring
