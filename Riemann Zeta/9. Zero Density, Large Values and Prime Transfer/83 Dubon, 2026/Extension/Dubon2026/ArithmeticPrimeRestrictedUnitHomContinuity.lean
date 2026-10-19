import Dubon2026.ArithmeticFiniteSUnitLocalDualDiagram
import Dubon2026.OriginalInternalHomActionContinuity

/-! Derive action continuity for the actual local dual terms of the
restricted arithmetic finite presentation. The finite-generator theorem
serves both its finite trace coefficient and its finite free cover in
DUB-17's constructed-class localization comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) (p : ℕ) (hp : p.Prime)

/-- The original local units dual to the arithmetic finite coefficient
under the actual global-to-prime restriction. -/
abbrev arithmeticPrimeRestrictedUnitHom :
    Rep ℤ Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) :=
  (Rep.ihom (Rep.res
    ((AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) B)).obj
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))

/-- The actual local Hom action is continuous for the finitely generated
original coefficient, using the proved arithmetic restriction continuity
and original local unit action. -/
theorem arithmeticPrimeRestrictedUnitHomAction_continuous
    [Module.Finite ℤ B]
    [TopologicalSpace (arithmeticPrimeRestrictedUnitHom a F B p hp)]
    [DiscreteTopology (arithmeticPrimeRestrictedUnitHom a F B p hp)] :
    Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ×
      arithmeticPrimeRestrictedUnitHom a F B p hp =>
        (arithmeticPrimeRestrictedUnitHom a F B p hp).ρ z.1 z.2) := by
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let j := rationalPrimeArithmeticRestriction a p hp
  let C := Rep.res (π.comp j.toMonoidHom) B
  let D := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : Module.Finite ℤ C := inferInstanceAs (Module.Finite ℤ B)
  have hπ : Continuous π := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  have hB : Continuous (fun z : Gal(F/ℚ) × B => B.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  exact originalInternalHomAction_continuous_of_finiteGenerated C D
    (restrictedCoefficientAction_continuous B (π.comp j.toMonoidHom)
      (hπ.comp j.continuous) hB)
    (discreteGaloisUnitAction_continuous (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp))

end
end Dubon2026
