import Dubon2026.OriginalContravariantHomExtExact
import Dubon2026.OriginalRelationGroupChange
import Dubon2026.PrimeDivisibleIntegerExt
import Dubon2026.GaloisUnitCartierHom

/-! The original local unit dual relation sequence is exact. The existing
algebraically closed unit root theorem and integer Ext vanishing supply
the lifting step. This discharges the target exactness needed when mapping
DUB-17's global S-unit connecting class to the original local units. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Abelian
attribute [local instance 1100] Rep.hV1 Rep.hV2

private theorem unitIntegerExt_with_module
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (q : ℕ) [Fact q.Prime]
    (A : Type) [hA : AddCommGroup A] [Module (ZMod q) A] [hM : Module ℤ A]
    (x : Ext (ModuleCat.of ℤ A) (ModuleCat.of ℤ (Rep.ofAlgebraAutOnUnits K Ω)) 1) :
    x = 0 := by
  have h : hM = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  cases h
  apply primeDivisible_primeField_ext_eq_zero q (Rep.ofAlgebraAutOnUnits K Ω) ?_ A 0 x
  intro u
  obtain ⟨v, hv⟩ := galoisKummerPower_surjective (K := K) (Ω := Ω) q
    (Fact.out : q.Prime).pos u
  exact ⟨v, (galoisUnitPower_eq_zsmul K Ω q v).symm.trans hv⟩

/-- The actual relation presentation restricted to a local Galois group
has a short exact dual sequence with the original extension-field units.
No unit divisibility or dual exactness premise is supplied. -/
theorem galoisUnitRelationDualSequence_shortExact
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (H : Type) [Group H] (π : Gal(Ω/K) →* H)
    (q : ℕ) [Fact q.Prime] (B : Rep.{0} ℤ H) (hB : ∀ b : B, q • b = 0) :
    (originalContravariantHomShortComplex
      ((originalRelationShortComplex B).map (Rep.resFunctor π))
      (Rep.ofAlgebraAutOnUnits K Ω)).ShortExact := by
  apply originalContravariantHom_shortExact_of_integerExt _ _
    (originalRelationGroupChange_shortExact π B)
  intro x
  letI : Module (ZMod q) (Rep.res π B) := AddCommGroup.zmodModule hB
  exact unitIntegerExt_with_module K Ω q (Rep.res π B)
    (hA := (Rep.res π B).hV1) (hM := (Rep.res π B).hV2) x

end
end Dubon2026
