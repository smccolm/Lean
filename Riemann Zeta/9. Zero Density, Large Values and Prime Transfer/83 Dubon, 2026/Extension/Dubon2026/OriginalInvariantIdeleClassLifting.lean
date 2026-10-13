import Dubon2026.OriginalFullIdeleCohomologySequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Every actual invariant idele class has an actual invariant idele representative

The original H0 surjection is transported through the pinned natural H0
identification with invariants. The conclusion is stated using the
original idele/class Galois maps and original quotient map themselves.
This removes the class-lifting obstruction in DUB-17's base-field norm
comparison; identifying fixed ideles with original base-field ideles
remains a separate required comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- Every original Galois-fixed idele class has a representative fixed by the actual original idele action. -/
theorem original_ideleClass_fixed_has_fixed_representative
    (c : OriginalNumberFieldIdeleClassGroup L)
    (hc : ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c) :
    ∃ a : (AdeleRing (𝓞 L) L)ˣ,
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range a = c ∧
        ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a := by
  let A := originalFullIdeleRep K L
  let B := originalIdeleClassRep K L
  let f := originalFullClassRepHom K L
  let x : B.ρ.invariants := ⟨Additive.ofMul c, fun σ => congrArg Additive.ofMul (hc σ)⟩
  obtain ⟨y, hy⟩ := originalFullClassH0_surjective K L ((groupCohomology.H0Iso B).inv x)
  let aInv : A.ρ.invariants := (groupCohomology.H0Iso A).hom y
  have hmap : (groupCohomology.H0Iso B).hom
      ((groupCohomology.functor ℤ Gal(L/K) 0).map f y) =
      ((Rep.invariantsFunctor ℤ Gal(L/K)).map f) aInv := by
    exact congrArg
      (fun t : groupCohomology A 0 ⟶ ModuleCat.of ℤ B.ρ.invariants => t y)
      (groupCohomology.map_id_comp_H0Iso_hom f)
  have hleft : (groupCohomology.H0Iso B).hom ((groupCohomology.H0Iso B).inv x) = x :=
    (groupCohomology.H0Iso B).toLinearEquiv.apply_symm_apply x
  rw [hy, hleft] at hmap
  let a : (AdeleRing (𝓞 L) L)ˣ := Additive.toMul aInv.val
  refine ⟨a, ?_, ?_⟩
  · exact congrArg (fun z : B.ρ.invariants =>
      (z.val : Additive (OriginalNumberFieldIdeleClassGroup L)).toMul) hmap.symm
  · intro σ
    apply Additive.ofMul.injective
    exact aInv.property σ

end
end Dubon2026
