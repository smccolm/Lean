import Dubon2026.ArithmeticSourceHomContinuity

/-! # Continuity of actual finite-stage arithmetic coefficient actions

Literal restriction to the original arithmetic Galois group supplies
continuous actions for all three terms of the finite relation sequence.
This discharges their action premises in DUB-17's S-unit cup comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (A : Rep.{0} ℤ Gal(F/K))
  [TopologicalSpace (Rep.res (AlgEquiv.restrictNormalHom F :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)) A)]
  [DiscreteTopology (Rep.res (AlgEquiv.restrictNormalHom F :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)) A)]

omit [NumberField K] in
/-- The actual finite-stage coefficient action is continuous after the
original arithmetic Galois restriction. No action-continuity input remains. -/
theorem arithmeticFiniteStageRepresentationAction_continuous :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
      Rep.res (AlgEquiv.restrictNormalHom F :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)) A =>
      (Rep.res (AlgEquiv.restrictNormalHom F :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)) A).ρ z.1 z.2) := by
  exact restrictedCoefficientAction_continuous A (AlgEquiv.restrictNormalHom F)
    (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField)
    continuous_of_discreteTopology

end
end Dubon2026
