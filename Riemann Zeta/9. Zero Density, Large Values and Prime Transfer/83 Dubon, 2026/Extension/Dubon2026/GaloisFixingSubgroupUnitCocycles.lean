import Dubon2026.GaloisFixingSubgroupTopology
import Dubon2026.ContinuousGaloisUnitBaseChange

/-! # Original continuous Galois unit cocycles on the actual fixing subgroup -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [tK : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [tE : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Reindex the original unit cocycle by the genuine fixing-subgroup
equivalence, retaining exactly the same original field-unit values. -/
def galoisFixingUnitCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E Ω) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) E.fixingSubgroup.subtype) where
  toFun c := ⟨⟨fun z => c.val (E.fixingSubgroupEquiv z.1, E.fixingSubgroupEquiv z.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h j
    have hc := (groupCohomology.mem_cocycles₂_iff _).mp c.val.property
      (E.fixingSubgroupEquiv g) (E.fixingSubgroupEquiv h) (E.fixingSubgroupEquiv j)
    simpa only [map_mul] using hc⟩, by
      have hi : @Continuous (Rep.ofAlgebraAutOnUnits E Ω) (Rep.ofAlgebraAutOnUnits K Ω)
          tE tK (fun a => a) := continuous_of_discreteTopology
      exact hi.comp (c.property.comp
        (((fixingSubgroupEquiv_continuous K Ω E).comp continuous_fst).prodMk
          ((fixingSubgroupEquiv_continuous K Ω E).comp continuous_snd)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The same actual reindexing on original continuous one-cochains. -/
def galoisFixingUnitCochain (f : C(Gal(Ω/E), Rep.ofAlgebraAutOnUnits E Ω)) :
    C(E.fixingSubgroup, Rep.ofAlgebraAutOnUnits K Ω) :=
  ⟨fun g => f (E.fixingSubgroupEquiv g), by
    have hi : @Continuous (Rep.ofAlgebraAutOnUnits E Ω) (Rep.ofAlgebraAutOnUnits K Ω)
        tE tK (fun a => a) := continuous_of_discreteTopology
    exact hi.comp (f.continuous.comp (fixingSubgroupEquiv_continuous K Ω E))⟩

omit [IsGalois E Ω] in
/-- Reindexing preserves the literal original differential and its
continuous one-cochain witness. -/
theorem galoisFixingUnitCocycle_coboundary
    (f : C(Gal(Ω/E), Rep.ofAlgebraAutOnUnits E Ω)) :
    galoisFixingUnitCocycle K Ω E
      (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits E Ω)
        (discreteGaloisUnitAction_continuous (K := E) (Ω := Ω)) f) =
      continuousRepresentationCoboundaryTwo
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) E.fixingSubgroup.subtype)
        (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K Ω)
          E.fixingSubgroup.subtype continuous_subtype_val
          (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)))
        (galoisFixingUnitCochain K Ω E f) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

end
end Dubon2026
