import Dubon2026.SourceModularCoefficientSlotRange
import Dubon2026.SourceModularCoefficientSeparability

/-! DUB-17/18 -> good reduction -> finite exceptional-fiber census ->
actual modular embeddings and elliptic cyclic-subgroup orbits. The literal
coefficient field is a simple extension of its j-coordinate field. This
reuses the proved two-generator equality and all-level degree; no new
modular-polynomial or field-generation hypothesis is introduced. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (K : Type*) [Field K]

/-- Cache the existing scalar action on the literal coefficient field. -/
scoped instance fieldConstantsAlgebra : Algebra K (modularFunctionFieldCoeff N K) := inferInstance

/-- Cache the existing scalar action on the actual internal j-coordinate field. -/
scoped instance coordinateConstantsAlgebra : Algebra K K⟮jCoeff N K⟯ := inferInstance

/-- The existing coordinate inclusion is a tower over the original constants. -/
scoped instance coordinateConstantsTower :
    IsScalarTower K K⟮jCoeff N K⟯ (modularFunctionFieldCoeff N K) := inferInstance

/-- The second actual modular coordinate, with its original Laurent series. -/
abbrev jN : modularFunctionFieldCoeff N K :=
  ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩

variable [IsAlgClosed K]

theorem adjoin_level_eq_top (hNK : (N : K) ≠ 0) :
    K⟮jCoeff N K⟯⟮jN N K⟯ = ⊤ := by
  letI : Algebra K (modularFunctionFieldCoeff N K) := inferInstance
  letI : Algebra K K⟮jCoeff N K⟯ := inferInstance
  letI : IsScalarTower K K⟮jCoeff N K⟯ (modularFunctionFieldCoeff N K) := inferInstance
  apply restrictScalars_injective K
  exact (adjoin_simple_adjoin_simple K (jCoeff N K) (jN N K)).trans
    ((coeff_internal_pair_adjoin_top N K hNK).trans restrictScalars_top.symm)

/-- The actual simple presentation; its generator is the original j_N. -/
def adjoinLevelEquiv (hNK : (N : K) ≠ 0) :
    K⟮jCoeff N K⟯⟮jN N K⟯ ≃ₐ[K⟮jCoeff N K⟯] modularFunctionFieldCoeff N K :=
  (equivOfEq (adjoin_level_eq_top N K hNK)).trans topEquiv

theorem adjoinLevelEquiv_gen (hNK : (N : K) ≠ 0) :
    adjoinLevelEquiv N K hNK (AdjoinSimple.gen K⟮jCoeff N K⟯ (jN N K)) = jN N K := rfl

omit [IsAlgClosed K] in
theorem level_isIntegral : IsIntegral K⟮jCoeff N K⟯ (jN N K) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := Algebra.IsIntegral.of_finite K⟮jCoeff N K⟯ (modularFunctionFieldCoeff N K)
  exact Algebra.IsIntegral.isIntegral _

theorem level_minpoly_natDegree (hNK : (N : K) ≠ 0) :
    (minpoly K⟮jCoeff N K⟯ (jN N K)).natDegree = SourceLevelProjective.dedekindPsi N := by
  rw [← adjoin.finrank (level_isIntegral N K),
    (adjoinLevelEquiv N K hNK).toLinearEquiv.finrank_eq,
    finrank_coeff_over_j_eq_psi N hNK]

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
