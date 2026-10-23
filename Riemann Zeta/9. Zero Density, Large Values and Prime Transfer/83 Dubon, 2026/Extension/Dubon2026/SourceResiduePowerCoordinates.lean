import Dubon2026.SourceResidueAllLevelDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> coefficient
specialization. The exact all-level minimal-polynomial degree gives independence
of the first psi(N) powers of j_N over K(j). Actual field generation gives a
finite expression in those same powers for every member. This replaces an
arbitrary divisor-monomial basis in the specialization argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem residue_power_polynomial_independent (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (C : Fin (dedekindPsi N) → Polynomial K)
    (hC : ∑ i, Polynomial.aeval (jqModC K) (C i) *
      (qExpand K N (jqModC K)) ^ (i : ℕ) = 0) : ∀ i, C i = 0 := by
  have hv := linearIndependent_pow (K := K⟮jqModC K⟯) (qExpand K N (jqModC K))
  rw [residue_j_minpoly_natDegree_eq_psi N hNK] at hv
  let g : Fin (dedekindPsi N) → K⟮jqModC K⟯ := fun i =>
    ⟨Polynomial.aeval (jqModC K) (C i),
      IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)⟩
  have hsum : ∑ i, g i • (qExpand K N (jqModC K)) ^ (i : ℕ) = 0 := hC
  intro i
  have hi := Fintype.linearIndependent_iff.mp hv g hsum i
  have he : Polynomial.aeval (jqModC K) (C i) = 0 := congrArg Subtype.val hi
  by_contra hn
  exact transcendental_jqModC K ⟨C i, hn, he⟩

theorem residue_member_power_coordinates (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldCoeff N K) :
    ∃ c : Fin (dedekindPsi N) → K⟮jqModC K⟯,
      ∑ i, (c i : LaurentSeries K) * (qExpand K N (jqModC K)) ^ (i : ℕ) = x := by
  obtain ⟨g, _, hg⟩ := residue_member_reduced_polynomial N
    (residue_full_generation_and_degree N hNK).1 x hx
  have hm := (residue_j_substitution_isIntegral K N).mem_span_pow ⟨g, hg.symm⟩
  rw [residue_j_minpoly_natDegree_eq_psi N hNK] at hm
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
  exact ⟨c, hc⟩

end
end Dubon2026.SourceFunctionField
