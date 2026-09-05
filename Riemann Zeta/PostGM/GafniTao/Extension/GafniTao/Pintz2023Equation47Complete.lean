import GafniTao.Pintz2023Equation47Shift

/-!
# Pintz (2023), equation (4.7): complete-line finite source form

This assembles the residue-producing `n = 1` term, the shifted finite
source polynomial, and the quantitatively controlled infinite tail.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023SmallLineTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (pintz2023Coeff X) rho n *
    pintz2023BareWeight lambda (lambda - Real.log n) (1 / lambda)

theorem pintz2023WeightedTerm_eq_smallLineTerm
    {X n : ℕ} {rho : ℂ} {lambda : ℝ}
    (hlambda : 1 ≤ lambda) (hn : 0 < n) :
    pintz2023WeightedTerm X rho lambda n =
      pintz2023SmallLineTerm X rho lambda n := by
  unfold pintz2023WeightedTerm pintz2023SmallLineTerm
  rw [pintz2023GaussianWeight_eq_smallLine hlambda hn]

theorem pintz2023_middle_sum_eq_smallLine
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
      pintz2023WeightedTerm X rho lambda n) =
    ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
      pintz2023SmallLineTerm X rho lambda n := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [pintz2023WeightedTerm_eq_smallLineTerm hlambda]
  have := (Finset.mem_Ioc.mp hn).1
  omega

noncomputable def pintz2023Equation47Remainder
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ :=
  (VerticalIntegral' (pintzGaussianKernel lambda) 3 - 1) +
    ∑' n : ℕ, pintz2023TailTerm X rho lambda n

/-- Exact complete-line form underlying Pintz equation (4.7). -/
theorem pintz2023_equation_4_7_completeLine
    {X : ℕ} {rho : ℂ} {lambda eta : ℝ}
    (hrho : 1 - eta ≤ rho.re) (hlambda : 8 ≤ lambda)
    (heta : eta ≤ 1 / 32) (hX : 1 ≤ X)
    (hXC : X ≤ pintz2023Cutoff lambda) :
    pintz2023Equation42Integral X rho lambda =
      1 +
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023SmallLineTerm X rho lambda n +
        pintz2023Equation47Remainder X rho lambda := by
  have hrhoHalf : 1 / 2 ≤ rho.re := by linarith
  rw [pintz2023_equation_4_2_source_split
    hrhoHalf (by linarith) hX hXC]
  rw [pintz2023_middle_sum_eq_smallLine (by linarith)]
  unfold pintz2023Equation47Remainder
  ring

/-- Uniform `O(Y⁻²)` remainder in the complete-line equation (4.7), with
the implicit constant exposed existentially and independent of all source
parameters. -/
theorem norm_pintz2023Equation47Remainder_le_exp_neg_two :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 8 ≤ lambda → eta ≤ 1 / 32 →
        ‖pintz2023Equation47Remainder X rho lambda‖ ≤
          K * Real.exp (-2 * lambda) := by
  obtain ⟨Ktail, hKtail, htail⟩ :=
    norm_tsum_pintz2023TailTerm_le_exp_neg_two
  refine ⟨Ktail + 1, by positivity, ?_⟩
  intro X rho eta lambda hrho hlambda heta
  have hbare := pintz_equation_4_1 hlambda
  have htail' := htail (X := X) (rho := rho)
    (eta := eta) (lambda := lambda) hrho hlambda heta
  unfold pintz2023Equation47Remainder
  calc
    ‖(VerticalIntegral' (pintzGaussianKernel lambda) 3 - 1) +
        ∑' n : ℕ, pintz2023TailTerm X rho lambda n‖ ≤
      ‖VerticalIntegral' (pintzGaussianKernel lambda) 3 - 1‖ +
        ‖∑' n : ℕ, pintz2023TailTerm X rho lambda n‖ := norm_add_le _ _
    _ ≤ Real.exp (-2 * lambda) +
        Ktail * Real.exp (-2 * lambda) := add_le_add hbare htail'
    _ = (Ktail + 1) * Real.exp (-2 * lambda) := by ring

#print axioms pintz2023_equation_4_7_completeLine
#print axioms norm_pintz2023Equation47Remainder_le_exp_neg_two

end

end GafniTao
