import Dubon2026.GaloisFixingSubgroupUnitCocycles

/-! # Original continuous H2 on the genuine Galois fixing subgroup -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Reindex original continuous unit H2 along the actual fixing-subgroup
isomorphism, preserving original continuous coboundaries. -/
def galoisFixingUnitH2 : GaloisUnitContinuousH2 (K := E) (Ω := Ω) →ₗ[ℤ]
    ContinuousRepresentationH2
      (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) E.fixingSubgroup.subtype)
      (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K Ω)
        E.fixingSubgroup.subtype continuous_subtype_val
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) := by
  let A := Rep.ofAlgebraAutOnUnits K Ω
  let B := Rep.ofAlgebraAutOnUnits E Ω
  let hA := discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)
  let hB := discreteGaloisUnitAction_continuous (K := E) (Ω := Ω)
  let hS := restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA
  have hb : continuousRepresentationCoboundariesTwo B hB ≤
      (continuousRepresentationCoboundariesTwo
        (restrictedCoefficientRep A E.fixingSubgroup.subtype) hS).comap (galoisFixingUnitCocycle K Ω E) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨galoisFixingUnitCochain K Ω E f, (galoisFixingUnitCocycle_coboundary K Ω E f).symm⟩
  exact Submodule.mapQ (R := ℤ) (R₂ := ℤ)
    (M := continuousRepresentationCocyclesTwo B)
    (M₂ := continuousRepresentationCocyclesTwo (restrictedCoefficientRep A E.fixingSubgroup.subtype))
    (τ₁₂ := RingHom.id ℤ) (continuousRepresentationCoboundariesTwo B hB)
    (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A E.fixingSubgroup.subtype) hS)
    (galoisFixingUnitCocycle K Ω E) hb

/-- The actual H2 identification keeps the original cocycle values. -/
theorem galoisFixingUnitH2_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E Ω)) :
    galoisFixingUnitH2 K Ω E (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (galoisFixingUnitCocycle K Ω E c) := rfl

/-- Original field restriction, followed by the genuine fixing-subgroup
identification, is exactly literal subgroup restriction on original classes. -/
theorem galoisFixingUnitH2_baseChange (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisFixingUnitH2 K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
        E.fixingSubgroup.subtype continuous_subtype_val x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change c.val (galoisBaseChangeRestriction K E Ω Ω (E.fixingSubgroupEquiv z.1),
        galoisBaseChangeRestriction K E Ω Ω (E.fixingSubgroupEquiv z.2)) = c.val (z.1, z.2)
    rw [galoisBaseChangeRestriction_eq_fixingSubgroup, galoisBaseChangeRestriction_eq_fixingSubgroup,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end
end Dubon2026
