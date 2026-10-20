import Dubon2026.SourceSquareZeroDifferentialStability
import Dubon2026.SourceSpecialLinearMatrices

/-! Extending actual off-diagonal differential stability to trace-zero matrices.
The already proved original matrix-unit spanning theorem and actual Lie
bracket discharge the diagonal directions. This is the remaining algebraic
step from the original group action to the original source Lie action.
-/

namespace Dubon2026
noncomputable section
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

/-- Stability under every actual off-diagonal source differential implies stability under every original trace-zero differential. -/
theorem sourceRegular_traceZero_stable_of_offDiagonal (W : Submodule K S)
    (hW : ∀ (i j : Fin n), i ≠ j → ∀ p ∈ W,
      sourceRegularDifferential (Matrix.single i j (1 : K)) p ∈ W)
    (X : Matrix (Fin n) (Fin n) K) (hX : X.trace = 0)
    (p : S) (hp : p ∈ W) : sourceRegularDifferential X p ∈ W := by
  let N : Submodule K (Matrix (Fin n) (Fin n) K) :=
    { carrier := {Y | ∀ q ∈ W, sourceRegularDifferential Y q ∈ W}
      zero_mem' := by
        intro q _
        have hz : sourceRegularDifferential (0 : Matrix (Fin n) (Fin n) K) = 0 :=
          (sourceRegularDifferentialLieHom (R := K) (n := n)).map_zero
        rw [hz, Derivation.zero_apply]
        exact W.zero_mem
      add_mem' := by
        intro Y Z hY hZ q hq
        rw [sourceRegularDifferential_add, Derivation.add_apply]
        exact W.add_mem (hY q hq) (hZ q hq)
      smul_mem' := by
        intro c Y hY q hq
        rw [sourceRegularDifferential_smul, Derivation.smul_apply]
        exact W.smul_mem c (hY q hq) }
  have hoff {i j : Fin n} (hij : i ≠ j) (c : K) : Matrix.single i j c ∈ N := by
    intro q hq
    have hm : Matrix.single i j c = c • Matrix.single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hm, sourceRegularDifferential_smul, Derivation.smul_apply]
    exact W.smul_mem c (hW i j hij q hq)
  have hdiag (i j : Fin n) (c : K) :
      Matrix.single i i c - Matrix.single j j c ∈ N := by
    by_cases hij : i = j
    · subst j
      rw [sub_self]
      exact N.zero_mem
    · rw [← lie_single_single_eq_sub]
      intro q hq
      rw [sourceRegularDifferential_lie, Derivation.commutator_apply]
      exact W.sub_mem (hoff hij c _ (hoff (fun h => hij h.symm) 1 q hq))
        (hoff (fun h => hij h.symm) 1 _ (hoff hij c q hq))
  have hmem : X ∈ N := mem_of_trace_eq_zero_of_single_mem hoff hdiag hX
  exact hmem p hp

end
end Dubon2026
