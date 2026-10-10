import Dubon2026.MatrixIdempotentNewtonBounds
import Dubon2026.AdicMatrixSequenceConvergence
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Actual idempotent lifting inside an original closed matrix subalgebra -/

namespace Dubon2026
noncomputable section
open Matrix Filter Topology

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [WithIdeal R]

/-- The actual matrix idempotency errors tend to zero in the original product coefficient topology. -/
theorem matrixIdempotentNewtonSequence_error_tendsto_zero (X : Matrix ι ι R)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ (WithIdeal.i : Ideal R)) :
    Tendsto (fun n => (matrixIdempotentNewtonSequence X n) ^ 2 -
      matrixIdempotentNewtonSequence X n) atTop (𝓝 (0 : Matrix ι ι R)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [Matrix.zero_apply]
  rw [(show IsAdic (WithIdeal.i : Ideal R) from rfl).hasBasis_nhds_zero.tendsto_right_iff]
  intro N _
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  exact Ideal.pow_le_pow_right (hn.trans (Nat.le_of_lt n.lt_two_pow_self))
    (matrixIdempotentNewtonSequence_error WithIdeal.i X hX n i j)

omit [WithIdeal R] in
/-- All genuine polynomial iterates retain the original matrix reduction modulo the actual coefficient ideal. -/
theorem matrixIdempotentNewtonSequence_sub_initial (I : Ideal R) (X : Matrix ι ι R)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ I) (n : ℕ) :
    ∀ i j, (matrixIdempotentNewtonSequence X n - X) i j ∈ I := by
  induction n with
  | zero =>
    intro i j
    simpa only [matrixIdempotentNewtonSequence, sub_self, Matrix.zero_apply] using I.zero_mem
  | succ n hn =>
    intro i j
    have hd : (matrixIdempotentNewtonSequence X (n + 1) -
        matrixIdempotentNewtonSequence X n) i j ∈ I :=
      Ideal.pow_le_self (pow_ne_zero n (by decide))
        (matrixIdempotentNewtonSequence_sub I X hX n i j)
    have ha := I.add_mem hd (hn i j)
    simpa only [Matrix.sub_apply, sub_add_sub_cancel] using ha

/-- An actual original approximate matrix idempotent in a closed coefficient subalgebra lifts to a genuine idempotent in that same subalgebra, with exactly the same original reduction. -/
theorem adicMatrixIdempotent_exists_mem_closedSubalgebra
    [IsAdicComplete (WithIdeal.i : Ideal R) R]
    {O : Type*} [CommRing O] [Algebra O (Matrix ι ι R)]
    (S : Subalgebra O (Matrix ι ι R)) (hS : IsClosed (S : Set (Matrix ι ι R)))
    (X : Matrix ι ι R) (hXS : X ∈ S)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ (WithIdeal.i : Ideal R)) :
    ∃ E : Matrix ι ι R, E ∈ S ∧ E ^ 2 = E ∧
      ∀ i j, (E - X) i j ∈ (WithIdeal.i : Ideal R) := by
  let I : Ideal R := WithIdeal.i
  letI : T2Space R := (show IsAdic I from rfl).isHausdorff_iff.mp inferInstance
  obtain ⟨E, hE⟩ := adicMatrixSequence_exists_limit_of_steps
    (matrixIdempotentNewtonSequence X) (fun n i j =>
      Ideal.pow_le_pow_right (Nat.le_of_lt n.lt_two_pow_self)
        (matrixIdempotentNewtonSequence_sub I X hX n i j))
  have hES : E ∈ S := hS.mem_of_tendsto hE
    (Eventually.of_forall (matrixIdempotentNewtonSequence_mem S X hXS))
  have heq : E ^ 2 = E := sub_eq_zero.mp (tendsto_nhds_unique
    ((hE.pow 2).sub hE) (matrixIdempotentNewtonSequence_error_tendsto_zero X hX))
  have hI : IsClosed (I : Set R) := by
    have hi := (I.openAddSubgroup 1).isClosed
    change IsClosed ((I ^ 1 : Ideal R) : Set R) at hi
    simpa only [pow_one] using hi
  refine ⟨E, hES, heq, ?_⟩
  intro i j
  have hcoord : Tendsto (fun n => (matrixIdempotentNewtonSequence X n - X) i j)
      atTop (𝓝 ((E - X) i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hE.sub_const X) i) j
  exact hI.mem_of_tendsto hcoord (Eventually.of_forall
    (fun n => matrixIdempotentNewtonSequence_sub_initial I X hX n i j))

end
end Dubon2026
