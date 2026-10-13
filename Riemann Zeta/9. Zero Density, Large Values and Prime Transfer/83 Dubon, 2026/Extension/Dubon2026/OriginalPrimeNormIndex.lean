import Dubon2026.OriginalPrimeNormIndexActual
import Dubon2026.OriginalNormCoprimeBaseChange
import Dubon2026.OriginalCyclotomicPrimeStage
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The exact original norm index for every prime-degree Galois extension

The existing cyclotomic stage has degree coprime to p. Its actual
compositum with the image of the original upper field has degree p over
that stage by pinned linear disjointness. The original upper field itself
embeds into the compositum and is retained in the norm comparison.
Coprime norm-quotient injection descends the proved primitive-root case.
This removes the primitive-root assumption from DUB-17's prime norm-index
dependency. Cyclic induction and the subsequent reciprocity and global
duality obligations remain separate.
-/
namespace Dubon2026
noncomputable section
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every literal original finite prime-degree Galois class norm quotient
has order equal to the extension degree, without a base primitive-root assumption. -/
theorem original_primeDegree_normQuotient_card
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p) :
    Nat.card (OriginalIdeleClassNormQuotient K L) = p := by
  have hp : p.Prime := Fact.out
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hGal : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hDegree
  letI : IsCyclic Gal(L/K) := isCyclic_of_prime_card hGal
  let Ω := AlgebraicClosure L
  let i : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let F := i.fieldRange
  let e : L ≃ₐ[K] F := AlgEquiv.ofInjectiveField i
  letI : FiniteDimensional K F := i.toLinearMap.finiteDimensional_range
  letI : IsGalois K F := IsGalois.of_algEquiv e
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  let M := originalPrimitiveRootStage K Ω hμ
  let N := F ⊔ M.toIntermediateField
  letI : NumberField M := NumberField.of_module_finite K M
  letI : NumberField N := NumberField.of_module_finite K N
  let j : L →ₐ[K] N :=
    (IntermediateField.inclusion (show F ≤ N from le_sup_left)).comp e.toAlgHom
  letI : Algebra L N := j.toAlgebra
  letI : IsScalarTower K L N := IsScalarTower.of_algHom j
  let jM : M →ₐ[K] N :=
    IntermediateField.inclusion (show M.toIntermediateField ≤ N from le_sup_right)
  letI : Algebra M N := jM.toAlgebra
  letI : IsScalarTower K M N := IsScalarTower.of_algHom jM
  letI : FiniteDimensional L N := FiniteDimensional.right K L N
  letI : FiniteDimensional M N := FiniteDimensional.right K M N
  letI : IsGalois L N := IsGalois.tower_top_of_isGalois K L N
  letI : IsGalois M N := IsGalois.tower_top_of_isGalois K M N
  have hF : Module.finrank K F = p := e.toLinearEquiv.finrank_eq.symm.trans hDegree
  have hCoprime : (Module.finrank K M).Coprime p :=
    (originalPrimitiveRootStage_finrank_coprime K Ω hμ).symm
  have hDisjoint : F.LinearDisjoint M.toIntermediateField :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (by rw [hF]; exact hCoprime.symm)
  have hN : Module.finrank K N = p * Module.finrank K M := by
    simpa only [hF] using hDisjoint.finrank_sup
  have hMN : Module.finrank M N = p := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := M))
    rw [Module.finrank_mul_finrank K M N, hN, mul_comm]
  have hUpper := original_primeDegree_normQuotient_card_roots M N p hMN
    (originalPrimitiveRootStageRoot K Ω hμ) (originalPrimitiveRootStageRoot_isPrimitive K Ω hμ)
  letI : Finite (OriginalIdeleClassNormQuotient M N) :=
    Nat.finite_of_card_ne_zero (hUpper.symm ▸ hp.ne_zero)
  have hBound := originalIdeleClassNormQuotient_card_le_coprime_baseChange K L M N
    (hDegree ▸ hCoprime)
  exact Nat.le_antisymm (hBound.trans_eq hUpper)
    (hDegree ▸ (originalIdeleClassNormQuotient_degree_lower K L).2)

end
end Dubon2026
