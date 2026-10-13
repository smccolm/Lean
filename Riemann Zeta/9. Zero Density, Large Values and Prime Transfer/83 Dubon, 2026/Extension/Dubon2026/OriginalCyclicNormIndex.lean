import Dubon2026.OriginalPrimeNormIndex
import Dubon2026.OriginalNormQuotientTower
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # The exact literal original cyclic class norm index

Strong induction on the original field degree uses the fixed field of an
actual prime-order automorphism. The prime upper extension has the proved
unconditional original norm index; the lower extension inherits cyclicity.
The original tower quotient bound and existing degree lower bound give
equality. This closes the cyclic norm-index dependency for DUB-17's global
class-field-theory route; reciprocity, invariant sum-zero and global duality
remain further required obligations.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- The literal original class norm quotient has order equal to the degree
of every original finite cyclic Galois number-field extension. -/
theorem original_cyclic_normQuotient_card :
    Nat.card (OriginalIdeleClassNormQuotient K L) = Module.finrank K L := by
  induction hDegree : Module.finrank K L using Nat.strong_induction_on generalizing K L with
  | h d ih =>
    apply Eq.trans ?_ hDegree
    by_cases hOne : Module.finrank K L = 1
    · have hRange : (originalIdeleClassNormLinear K L).range = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        intro c
        refine ⟨Additive.ofMul (originalIdeleClassBaseChangeMap K L c.toMul), ?_⟩
        change Additive.ofMul (originalIdeleClassNorm K L
          (originalIdeleClassBaseChangeMap K L c.toMul)) = c
        rw [originalIdeleClassNorm_baseChange, hOne, pow_one]
        rfl
      rw [hOne]
      change Nat.card (Additive (OriginalNumberFieldIdeleClassGroup K) ⧸
        (originalIdeleClassNormLinear K L).range) = 1
      rw [hRange]
      exact Nat.card_unique
    · obtain ⟨p, hp, hDiv⟩ := Nat.exists_prime_and_dvd hOne
      letI : Fact p.Prime := ⟨hp⟩
      have hDivGal : p ∣ Nat.card Gal(L/K) := by
        rw [IsGalois.card_aut_eq_finrank]
        exact hDiv
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hDivGal
      letI : CommGroup Gal(L/K) := IsCyclic.commGroup
      let H := Subgroup.zpowers g
      let F := IntermediateField.fixedField H
      letI : NumberField F := NumberField.of_module_finite K F
      letI : IsCyclic Gal(F/K) := isCyclic_of_surjective
        (AlgEquiv.restrictNormalHom F) (AlgEquiv.restrictNormalHom_surjective L)
      have hTop : Module.finrank F L = p := by
        rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hg]
      have hBaseLt : Module.finrank K F < d := by
        have hMul := Module.finrank_mul_finrank K F L
        rw [hTop, hDegree] at hMul
        have hTwo := Nat.mul_le_mul_left (Module.finrank K F) hp.two_le
        have hPos : 0 < Module.finrank K F := Module.finrank_pos
        omega
      have hBase := ih (Module.finrank K F) hBaseLt K F rfl
      have hUpper := original_primeDegree_normQuotient_card F L p hTop
      letI : Finite (OriginalIdeleClassNormQuotient F L) :=
        Nat.finite_of_card_ne_zero (hUpper.symm ▸ hp.ne_zero)
      apply Nat.le_antisymm
      · calc
          Nat.card (OriginalIdeleClassNormQuotient K L) ≤
              Nat.card (OriginalIdeleClassNormQuotient F L) *
                Nat.card (OriginalIdeleClassNormQuotient K F) :=
            originalIdeleClassNormQuotient_card_le_tower K F L
          _ = p * Module.finrank K F := by rw [hUpper, hBase]
          _ = Module.finrank K L := by
            rw [← hTop, mul_comm, Module.finrank_mul_finrank K F L]
      · exact (originalIdeleClassNormQuotient_degree_lower K L).2

end
end Dubon2026
