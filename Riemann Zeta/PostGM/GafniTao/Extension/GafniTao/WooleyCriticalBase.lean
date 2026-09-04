import GafniTao.VinogradovCriticalReduction

/-!
# The degree-one base of the critical Vinogradov mean value theorem

This is the `k = 1` base case of Wooley, Section 5.  For one variable and
one equation, equality of the first power sums is literal equality of the
two entries.  Consequently the critical mean value `J_{1,1}(Q)` is exactly
`Q`, with no asymptotic loss.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordVinogradovPowerVector_one_one_injective (Q : ℕ) :
    Function.Injective (fordVinogradovPowerVector 1 1 Q) := by
  intro x y hxy
  funext i
  have h0 := congrFun hxy (0 : Fin 1)
  unfold fordVinogradovPowerVector at h0
  simp only [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one] at h0
  have hz : ((x (0 : Fin 1) : ℕ) : ℤ) =
      ((y (0 : Fin 1) : ℕ) : ℤ) := by omega
  have hval : (x (0 : Fin 1) : ℕ) = (y (0 : Fin 1) : ℕ) := by
    exact_mod_cast hz
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  exact Fin.ext (by simpa only [hi] using hval)

theorem fordVinogradovMomentNat_one_one (Q : ℕ) :
    fordVinogradovMomentNat 1 1 Q = Q := by
  classical
  unfold fordVinogradovMomentNat fordVinogradovShiftedCountNat
    fordRepresentationCount
  rw [show ((Finset.univ : Finset (FordVinogradovTuple 1 Q)) ×ˢ
      Finset.univ).filter
        (fun xy => fordVinogradovPowerVector 1 1 Q xy.1 -
          fordVinogradovPowerVector 1 1 Q xy.2 = 0) =
      (Finset.univ : Finset (FordVinogradovTuple 1 Q)).diag by
    ext xy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, sub_eq_zero, Finset.mem_diag]
    exact (fordVinogradovPowerVector_one_one_injective Q).eq_iff]
  simp [FordVinogradovTuple]

theorem fordVinogradovKappa_one : fordVinogradovKappa 1 = 1 := by
  norm_num [fordVinogradovKappa]

theorem fordLambda34_one_one (epsilon : ℝ) :
    fordLambda34 1 1 epsilon = 1 + epsilon := by
  unfold fordLambda34
  norm_num

theorem fordVinogradovMomentBound_critical_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    FordVinogradovMomentBound 1 1 1 epsilon := by
  intro Q hQ
  rw [fordVinogradovMomentNat_one_one, fordLambda34_one_one]
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQrpow : (Q : ℝ) ≤ (Q : ℝ) ^ (1 + epsilon) := by
    have h := Real.rpow_le_rpow_of_exponent_le hQone
      (show (1 : ℝ) ≤ 1 + epsilon by linarith)
    simpa only [Real.rpow_one] using h
  simpa using hQrpow

/-- The exact `l = 1` member of the critical endpoint family. -/
theorem vinogradovCriticalEndpoint_degree_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      FordVinogradovMomentBound (fordVinogradovKappa 1) 1 C epsilon := by
  refine ⟨1, by norm_num, ?_⟩
  simpa [fordVinogradovKappa] using
    fordVinogradovMomentBound_critical_one hepsilon

#print axioms fordVinogradovPowerVector_one_one_injective
#print axioms fordVinogradovMomentNat_one_one
#print axioms fordVinogradovMomentBound_critical_one
#print axioms vinogradovCriticalEndpoint_degree_one

end

end GafniTao
