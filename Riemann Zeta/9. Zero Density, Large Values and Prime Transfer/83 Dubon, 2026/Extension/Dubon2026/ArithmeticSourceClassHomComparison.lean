import Dubon2026.ArithmeticTorsionClassColimitLifting
import Dubon2026.ArithmeticSourceHomContinuity

/-! # Actual prime-field Hom comparison for source and full classes

The original arithmetic source comparison is injective and every q-torsion
full-class coefficient lifts by the proved finite-stage Kummer correction.
Thus postcomposition is an isomorphism on integer-linear Hom from the actual
prime-field module. No full principalization theorem is assumed. This is the
coefficient comparison needed by the DUB-17 continuous duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))

/-- Integer-linear Hom to the actual full-class quotient colimit with its original conjugate action. -/
abbrev arithmeticFullClassHomRep :=
  (CategoryTheory.ihom A).obj (arithmeticClassesModOutsideColimitRep K Ω a ha)

/-- Literal postcomposition by the original arithmetic source-class comparison. -/
def arithmeticSourceClassHomComparison :
    arithmeticSourceClassHomRep K Ω a ha A ⟶ arithmeticFullClassHomRep K Ω a ha A :=
  (CategoryTheory.ihom A).map (arithmeticSourceClassColimitComparison K Ω a ha)

omit [IsAlgClosure K Ω] in
/-- The Hom comparison preserves each literal original coefficient value. -/
theorem arithmeticSourceClassHomComparison_apply
    (f : arithmeticSourceClassHomRep K Ω a ha A) (x : A) :
    (show A →ₗ[ℤ] arithmeticClassesModOutsideColimitRep K Ω a ha from
      (arithmeticSourceClassHomComparison K Ω a ha A).hom f) x =
      (arithmeticSourceClassColimitComparison K Ω a ha).hom
        ((show A →ₗ[ℤ] arithmeticSPlaceClassColimitRep K Ω a ha from f) x) := rfl

omit [IsAlgClosure K Ω] in
/-- Postcomposition by the actual source comparison is injective on the original Hom coefficients. -/
theorem arithmeticSourceClassHomComparison_injective :
    Function.Injective (arithmeticSourceClassHomComparison K Ω a ha A).hom := by
  intro f g h
  apply LinearMap.ext
  intro x
  apply arithmeticSourceClassColimitComparison_injective K Ω a ha
  exact congrArg (fun φ : arithmeticFullClassHomRep K Ω a ha A =>
    (show A →ₗ[ℤ] arithmeticClassesModOutsideColimitRep K Ω a ha from φ) x) h

variable (q : ℕ) [Fact q.Prime] [Module (ZMod q) A] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- Actual prime-field Hom coefficients lift to the original source classes without a principalization premise. -/
theorem arithmeticSourceClassHomComparison_surjective :
    Function.Surjective (arithmeticSourceClassHomComparison K Ω a ha A).hom := by
  intro f
  let i := (arithmeticSourceClassColimitComparison K Ω a ha).hom.toLinearMap
  let e := LinearEquiv.ofInjective i (arithmeticSourceClassColimitComparison_injective K Ω a ha)
  have hf (x : A) : (show A →ₗ[ℤ] arithmeticClassesModOutsideColimitRep K Ω a ha from f) x ∈ i.range := by
    apply arithmeticTorsionClassColimit_exists_source K Ω a ha q hqa
    have hx : q • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
    rw [← map_nsmul, hx, map_zero]
  let f' := (show A →ₗ[ℤ] arithmeticClassesModOutsideColimitRep K Ω a ha from f).codRestrict i.range hf
  let g := e.symm.toLinearMap.comp f'
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (f' x))

/-- The original prime-field class Hom comparison is an actual equivariant isomorphism. -/
def arithmeticSourceClassHomComparisonIso :
    arithmeticSourceClassHomRep K Ω a ha A ≅ arithmeticFullClassHomRep K Ω a ha A := by
  let f := arithmeticSourceClassHomComparison K Ω a ha A
  haveI : Mono f := (Rep.mono_iff_injective f).mpr (arithmeticSourceClassHomComparison_injective K Ω a ha A)
  haveI : Epi f := (Rep.epi_iff_surjective f).mpr (arithmeticSourceClassHomComparison_surjective K Ω a ha A q hqa)
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

/-- The equivariant isomorphism uses precisely the original source comparison on Hom. -/
theorem arithmeticSourceClassHomComparisonIso_hom :
    (arithmeticSourceClassHomComparisonIso K Ω a ha A q hqa).hom =
      arithmeticSourceClassHomComparison K Ω a ha A := rfl

end
end Dubon2026
