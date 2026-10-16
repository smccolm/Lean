import Dubon2026.OriginalCyclicCompositumDegree
import Mathlib.Data.Nat.Prime.Basic

/-! # Prescribed lower prime-power degree after a compositum

The actual absolute degree bounds the loss on adjoining a cyclic field.
This discharges the nontriviality and divisibility conditions for DUB-17's
auxiliary class-generator tower, without linear-disjointness assumptions.
-/
namespace Dubon2026
noncomputable section
open IntermediateField
attribute [-instance] SubfieldClass.instSMulRat

/-- A sufficiently large cyclic rational prime-power field retains a prescribed positive prime-power degree after adjoining it to the actual finite base. -/
theorem originalCyclicCompositum_exists_large_primePower_degree
    (U : Type) [Field U] [Algebra ℚ U]
    (K D : IntermediateField ℚ U) [FiniteDimensional ℚ K] [FiniteDimensional ℚ D]
    [IsGalois ℚ D] [IsCyclic Gal(D/ℚ)]
    (q n t : ℕ) (hq : q.Prime) (hD : Module.finrank ℚ D = q ^ n)
    (hn : Module.finrank ℚ K + t ≤ n) :
    let N := K ⊔ D
    letI : Algebra K N := (IntermediateField.inclusion (show K ≤ N from le_sup_left)).toAlgebra
    letI : Module K N := Algebra.toModule
    IsGalois K N ∧ IsCyclic Gal(N/K) ∧
      ∃ r : ℕ, t ≤ r ∧ Module.finrank K N = q ^ (r + 1) := by
  let N := K ⊔ D
  letI : Algebra K N := (IntermediateField.inclusion (show K ≤ N from le_sup_left)).toAlgebra
  letI : Module K N := Algebra.toModule
  letI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K N := FiniteDimensional.right ℚ K N
  obtain ⟨hg, hc, hd⟩ := originalCyclicCompositum_galois_cyclic_degree_dvd U K D
  rw [hD] at hd
  obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow hq).mp hd
  have hbound : q ^ n ≤ Module.finrank ℚ K * q ^ s := by
    rw [← hD, ← hs, Module.finrank_mul_finrank]
    exact IntermediateField.finrank_le_of_le_right (show D ≤ N from le_sup_right)
  have hstrict : Module.finrank ℚ K * q ^ s < q ^ (Module.finrank ℚ K + s) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_pow_self hq.one_lt) (pow_pos hq.pos s)
  have hexp : n < Module.finrank ℚ K + s :=
    (Nat.pow_lt_pow_iff_right hq.one_lt).mp (hbound.trans_lt hstrict)
  have hts : t < s := by omega
  refine ⟨hg, hc, s - 1, by omega, ?_⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using hs

end
end Dubon2026
