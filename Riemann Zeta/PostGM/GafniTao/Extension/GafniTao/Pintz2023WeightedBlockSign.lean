import GafniTao.Pintz2023CorollaryThree

/-!
# Sign symmetry for Pintz's weighted blocks

The source zero family uses both signs of the ordinate, whereas the
derivative estimate is stated at positive height.  Since the weight in
`pintz2023WeightedBlock` is real, changing the sign of the height complex
conjugates the complete block and therefore preserves its norm.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

theorem pintz2023WeightedBlock_neg_eq_conj
    (xi : ℝ) (N R : ℕ) (t : ℝ) :
    pintz2023WeightedBlock xi N R (-t) =
      conj (pintz2023WeightedBlock xi N R t) := by
  classical
  unfold pintz2023WeightedBlock
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
    change ((((n : ℝ) : ℂ)).arg ≠ Real.pi)
    rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
    exact Real.pi_ne_zero.symm
  have hphase :=
    Complex.cpow_conj (n : ℂ) (-(t : ℂ) * I) hnArg
  have hphase' :
      conj ((n : ℂ) ^ (-(t : ℂ) * I)) =
        (n : ℂ) ^ ((t : ℂ) * I) := by
    simpa using hphase.symm
  have hexp : -(((-t : ℝ) : ℂ)) * I = (t : ℂ) * I := by
    push_cast
    ring
  rw [Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal, hphase', hexp]

theorem norm_pintz2023WeightedBlock_neg
    (xi : ℝ) (N R : ℕ) (t : ℝ) :
    ‖pintz2023WeightedBlock xi N R (-t)‖ =
      ‖pintz2023WeightedBlock xi N R t‖ := by
  rw [pintz2023WeightedBlock_neg_eq_conj, RCLike.norm_conj]

theorem norm_pintz2023WeightedBlock_abs
    (xi : ℝ) (N R : ℕ) (t : ℝ) :
    ‖pintz2023WeightedBlock xi N R |t|‖ =
      ‖pintz2023WeightedBlock xi N R t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), ← norm_pintz2023WeightedBlock_neg]
    congr 2
    linarith

#print axioms pintz2023WeightedBlock_neg_eq_conj
#print axioms norm_pintz2023WeightedBlock_neg
#print axioms norm_pintz2023WeightedBlock_abs

end

end GafniTao
