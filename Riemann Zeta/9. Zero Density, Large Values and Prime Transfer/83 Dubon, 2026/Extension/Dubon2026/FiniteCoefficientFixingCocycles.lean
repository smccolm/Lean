import Dubon2026.ContinuousH1GroupReindex
import Dubon2026.ContinuousCohomologyCoefficientCongr
import Dubon2026.GaloisFixingSubgroupTopology
import Dubon2026.ContinuousTrivialCocycleCoordinates

/-! # Original split coefficient cocycles on their actual fixing field

The actual group reindexing and proved equality of coefficient actions identify
restricted cocycles with the constant cocycles whose local finiteness is proved.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] continuousTrivialCoordinateSMul

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(Ω/K))
  [TopologicalSpace A] [DiscreteTopology A] (E : IntermediateField K Ω)
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)

include hE in
omit [IsGalois K Ω] [TopologicalSpace A] [DiscreteTopology A] in
/-- Reindexing the actual restricted coefficient action gives the original
trivial action precisely when the genuine fixing subgroup fixes the coefficients. -/
theorem fixingCoefficientAction_eq_one :
    (A.ρ.comp E.fixingSubgroup.subtype).comp E.fixingSubgroupEquiv.symm.toMonoidHom =
      (1 : Representation (ZMod q) Gal(Ω/E) A) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro a
  exact hE (E.fixingSubgroupEquiv.symm g) a

/-- Identify original restricted continuous cocycles with the genuine constant
cocycles over the same actual field, using the proved group and action identities. -/
def finiteCoefficientFixingCocycleEquiv :
    continuousRepresentationCocyclesOne (restrictedCoefficientRep A E.fixingSubgroup.subtype) ≃+
      continuousRepresentationCocyclesOne (Rep.of (1 : Representation (ZMod q) Gal(Ω/E) A)) :=
  (continuousCocycleOneGroupEquiv (restrictedCoefficientRep A E.fixingSubgroup.subtype)
    E.fixingSubgroupEquiv.symm (fixingSubgroupEquiv_symm_continuous K Ω E)
    (fixingSubgroupEquiv_continuous K Ω E)).trans
      (continuousCocycleOneCoefficientCongr (fixingCoefficientAction_eq_one K Ω q A E hE)).toAddEquiv

/-- The actual coefficient and fixing-group identification retains the literal
original cocycle values under the original Galois equivalence. -/
theorem finiteCoefficientFixingCocycleEquiv_apply
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep A E.fixingSubgroup.subtype))
    (g : Gal(Ω/E)) :
    (finiteCoefficientFixingCocycleEquiv K Ω q A E hE c).val g =
      c.val (E.fixingSubgroupEquiv.symm g) := by
  exact continuousCocycleOneCoefficientCongr_apply (fixingCoefficientAction_eq_one K Ω q A E hE)
    (continuousCocycleOneGroupEquiv (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      E.fixingSubgroupEquiv.symm (fixingSubgroupEquiv_symm_continuous K Ω E)
      (fixingSubgroupEquiv_continuous K Ω E) c) g

end
end Dubon2026
