import Dubon2026.BoundedL2Differentiation

/-! # Actual L2 convergence of original uniformly summable pointwise series -/

namespace Dubon2026

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

/-- The genuine L2 realization commutes with each original finite pointwise sum. -/
theorem toLp_finsetSum {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (q : ℕ → X → ℂ) (hq : ∀ n, MemLp (q n) 2 μ) (s : Finset ℕ) :
    (memLp_finsetSum s (fun n _ => hq n)).toLp (fun x => ∑ n ∈ s, q n x) =
      ∑ n ∈ s, (hq n).toLp (q n) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.toLp_zero _
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    change ((hq n).add (memLp_finsetSum s (fun j _ => hq j))).toLp
      (q n + (fun x => ∑ j ∈ s, q j x)) = _
    rw [MemLp.toLp_add (hq n) (memLp_finsetSum s (fun j _ => hq j))]
    exact congrArg (fun v => (hq n).toLp (q n) + v) ih

/-- A uniformly summable original pointwise series converges to its actual pointwise sum in the genuine L2 norm. -/
theorem toLp_partialSums_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] (q : ℕ → X → ℂ) (G : X → ℂ)
    (hq : ∀ n, MemLp (q n) 2 μ) (hG : MemLp G 2 μ)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Summable u)
    (hbound : ∀ n x, ‖q n x‖ ≤ u n)
    (hpoint : ∀ x, Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, q j x) atTop (𝓝 (G x))) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, (hq j).toLp (q j)) atTop (𝓝 (hG.toLp G)) := by
  let F : ℕ → X → ℂ := fun n x => ∑ j ∈ Finset.range n, q j x
  have hF (n : ℕ) : MemLp (F n) 2 μ := memLp_finsetSum _ (fun j _ => hq j)
  have hsum (n : ℕ) (x : X) : ‖F n x‖ ≤ ∑' j : ℕ, u j := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hbound j x)).trans
      (hu.sum_le_tsum (Finset.range n) (fun j _ => hu0 j)))
  have hlimit (x : X) : ‖G x‖ ≤ ∑' j : ℕ, u j :=
    le_of_tendsto (hpoint x).norm (Eventually.of_forall (fun n => hsum n x))
  have hh := toLp_tendsto_of_uniform_difference_bound F G hF hG
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (tsum_nonneg hu0))
    (fun n x => (norm_sub_le _ _).trans (by linarith [hsum n x, hlimit x])) hpoint
  have he (n : ℕ) : (hF n).toLp (F n) = ∑ j ∈ Finset.range n, (hq j).toLp (q j) :=
    toLp_finsetSum q hq (Finset.range n)
  simpa only [he] using hh

end
end Dubon2026
