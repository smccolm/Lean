import Dubon2026.ContinuousH1GroupReindex
import Dubon2026.ContinuousH2GroupReindex
import Dubon2026.GaloisFixingSubgroupTopology
import Dubon2026.ContinuousKummerH1Map
import Dubon2026.ContinuousKummerH2Maps

/-! # Actual root cohomology on the genuine Galois fixing subgroup

The equivalences identify the original field's continuous root cohomology with
the restriction of the original base action to its actual fixing subgroup.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance fixingRootStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))

/-- The unchanged original root coefficient topology remains discrete. -/
local instance fixingRootStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))

/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance fixingRootUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))

/-- The unchanged original unit coefficient topology remains discrete. -/
local instance fixingRootUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- The actual field H1 is the original root H1 on the fixing subgroup;
continuity in both directions follows from its genuine Krull topology. -/
def galoisFixingRootH1Equiv :
    GaloisRootContinuousH1 (K := E) (Ω := Ω) n ≃+
      ContinuousRepresentationH1
        (restrictedCoefficientRep (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
          E.fixingSubgroup.subtype)
        (restrictedCoefficientAction_continuous _ E.fixingSubgroup.subtype continuous_subtype_val
          (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) :=
  continuousH1GroupEquiv (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)
    E.fixingSubgroupEquiv (fixingSubgroupEquiv_continuous K Ω E)
    (fixingSubgroupEquiv_symm_continuous K Ω E)
    (discreteGaloisRootAction_continuous (K := E) (Ω := Ω) n)

/-- The same actual fixing-subgroup identification preserves the original
continuous two-cocycles and their original continuous boundaries. -/
def galoisFixingRootH2Equiv :
    GaloisRootContinuousH2 (K := E) (Ω := Ω) n ≃+
      ContinuousRepresentationH2
        (restrictedCoefficientRep (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
          E.fixingSubgroup.subtype)
        (restrictedCoefficientAction_continuous _ E.fixingSubgroup.subtype continuous_subtype_val
          (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) :=
  continuousH2GroupEquiv (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)
    E.fixingSubgroupEquiv (fixingSubgroupEquiv_continuous K Ω E)
    (fixingSubgroupEquiv_symm_continuous K Ω E)
    (discreteGaloisRootAction_continuous (K := E) (Ω := Ω) n)

/-- The genuine fixing-subgroup H1 map retains exactly the original root values. -/
theorem galoisFixingRootH1Equiv_mk
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)) :
    galoisFixingRootH1Equiv K Ω E n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleOneRestriction
        (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)
        E.fixingSubgroupEquiv.toMonoidHom (fixingSubgroupEquiv_continuous K Ω E) c) := rfl

/-- The genuine fixing-subgroup H2 map retains exactly the original root values. -/
theorem galoisFixingRootH2Equiv_mk
    (c : continuousRepresentationCocyclesTwo
      (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)) :
    galoisFixingRootH2Equiv K Ω E n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction
        (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)
        E.fixingSubgroupEquiv.toMonoidHom (fixingSubgroupEquiv_continuous K Ω E) c) := rfl

end
end Dubon2026
