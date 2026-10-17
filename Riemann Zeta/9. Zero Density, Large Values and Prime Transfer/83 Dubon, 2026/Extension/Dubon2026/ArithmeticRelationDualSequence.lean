import Dubon2026.OriginalContravariantHomExtExact
import Dubon2026.OriginalRelationGroupChange
import Dubon2026.ArithmeticSUnitIntegerExt

/-! # Exact dual relation sequence for the actual arithmetic S-units

Pull the finite-stage relation presentation back along the literal Galois
restriction. The previously proved arithmetic root construction kills its
integer Ext obstruction. This gives the actual dual coefficient sequence
required by the continuous cup/connecting comparison for DUB-17, without
assuming exactness or equivariant Ext vanishing.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

private theorem sUnitIntegerExt_with_module
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (A : Type) [hA : AddCommGroup A] [Module (ZMod q) A] [hM : Module ℤ A]
    (x : CategoryTheory.Abelian.Ext (ModuleCat.of ℤ A)
      (ModuleCat.of ℤ (originalArithmeticSUnitRepresentation K Ω a ha)) 1) : x = 0 := by
  have h : hM = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  cases h
  exact originalArithmeticSUnit_integerExt_eq_zero K Ω a ha q hqa A 0 x

/-- The literal finite-stage relation presentation, restricted to the
original arithmetic Galois group, has a short exact S-unit dual sequence. -/
theorem arithmeticRelationSUnitDualSequence_shortExact
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (B : Rep.{0} ℤ Gal(F/K)) (hB : ∀ b : B, q • b = 0) :
    (originalContravariantHomShortComplex
      ((originalRelationShortComplex B).map
        (Rep.resFunctor (AlgEquiv.restrictNormalHom F :
          Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))))
      (originalArithmeticSUnitRepresentation K Ω a ha)).ShortExact := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom F
  apply originalContravariantHom_shortExact_of_integerExt _ _
    (originalRelationGroupChange_shortExact π B)
  intro x
  letI : Module (ZMod q) (Rep.res π B) := AddCommGroup.zmodModule hB
  exact sUnitIntegerExt_with_module K Ω a ha q hqa (Rep.res π B)
    (hA := (Rep.res π B).hV1) (hM := (Rep.res π B).hV2) x

end
end Dubon2026
