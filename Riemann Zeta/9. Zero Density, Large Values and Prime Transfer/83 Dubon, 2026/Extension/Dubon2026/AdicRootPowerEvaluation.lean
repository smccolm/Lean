import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # Convergence from a power in the actual adic ideal

The actual cyclotomic root has a positive power in the original prime
ideal. This elementary adic estimate converts that proved algebraic fact
into the convergence hypothesis for evaluating DUB-17's constructed series.
-/
namespace Dubon2026
open Filter
open scoped Topology

/-- An element with a power in the defining adic ideal is an actual convergent power-series evaluation point. -/
theorem adic_hasEval_of_pow_mem {R : Type*} [CommRing R] [WithIdeal R]
    (x : R) (d : ℕ) (hx : x ^ d ∈ (WithIdeal.i : Ideal R)) :
    PowerSeries.HasEval x := by
  suffices ∀ m : ℕ, ∃ N, ∀ n, N ≤ n → x ^ n ∈ (WithIdeal.i : Ideal R) ^ m by
    simpa [PowerSeries.hasEval_def, IsTopologicallyNilpotent,
      (WithIdeal.i : Ideal R).hasBasis_nhds_zero_adic.tendsto_right_iff]
  intro m
  refine ⟨d * m, fun n hn => ?_⟩
  rw [← Nat.add_sub_of_le hn, pow_add]
  apply Ideal.mul_mem_right
  simpa only [pow_mul] using Ideal.pow_mem_pow hx m

end Dubon2026
