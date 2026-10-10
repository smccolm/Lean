import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Instances.Matrix

/-! # Actual limits of original coefficient and matrix sequences with increasing adic differences -/

namespace Dubon2026
noncomputable section
open Filter Topology

variable {R : Type*} [CommRing R] [WithIdeal R]
  [IsPrecomplete (WithIdeal.i : Ideal R) R]

/-- Original coefficient sequences whose successive differences lie in the actual nth ideal power converge in the original adic topology, by the given original precompleteness. -/
theorem adicSequence_exists_limit_of_steps (f : ℕ → R)
    (hf : ∀ n, f (n + 1) - f n ∈ (WithIdeal.i : Ideal R) ^ n) :
    ∃ a : R, Tendsto f atTop (𝓝 a) := by
  let I : Ideal R := WithIdeal.i
  have hc : AdicCompletion.IsAdicCauchy I R f := by
    apply (AdicCompletion.isAdicCauchy_iff (I := I) (M := R) f).mpr
    intro n
    rw [SModEq.sub_mem]
    simpa only [smul_eq_mul, Ideal.mul_top, neg_sub] using (I ^ n).neg_mem (hf n)
  obtain ⟨a, ha⟩ := (inferInstance : IsPrecomplete I R).prec hc
  refine ⟨a, ?_⟩
  have hdiff : Tendsto (fun n => f n - a) atTop (𝓝 (0 : R)) := by
    rw [(show IsAdic I from rfl).hasBasis_nhds_zero.tendsto_right_iff]
    intro N _
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn => ?_⟩
    apply Ideal.pow_le_pow_right hn
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using ha n
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const a

/-- The actual original matrix sequence converges in its genuine product coefficient topology when every original entry has these increasing adic differences. -/
theorem adicMatrixSequence_exists_limit_of_steps {ι : Type*} (u : ℕ → Matrix ι ι R)
    (hu : ∀ n i j, (u (n + 1) - u n) i j ∈ (WithIdeal.i : Ideal R) ^ n) :
    ∃ X : Matrix ι ι R, Tendsto u atTop (𝓝 X) := by
  choose X hX using fun i j => adicSequence_exists_limit_of_steps
    (fun n => u n i j) (fun n => hu n i j)
  refine ⟨Matrix.of X, ?_⟩
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hX i j

end
end Dubon2026
