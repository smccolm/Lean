import Dubon2026.OriginalIdeleClassBaseInvariants
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The original base class norm quotient and its degree lower bound

The literal quotient C_K/N(C_L), with the norm induced from the descended
original idele product, is identified with the proved original invariant
norm quotient. Thus its finiteness, degree lower bound and degree exponent
require no assumed base-field comparison. This is a necessary step in
DUB-17's norm-index, reciprocity, global duality and automorphy chain.
The matching local field-norm formulas and index upper bound remain separate.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

/-- The actual original base class group modulo the actual descended extension class norms. -/
abbrev OriginalIdeleClassNormQuotient :=
  Additive (OriginalNumberFieldIdeleClassGroup K) ⧸ (originalIdeleClassNormLinear K L).range

/-- The actual original base class mapped to the proved original invariant norm quotient. -/
def originalIdeleClassBaseNormQuotientMap (g : Gal(L/K)) :
    Additive (OriginalNumberFieldIdeleClassGroup K) →ₗ[ℤ] OriginalIdeleClassInvariantNormQuotient K L g :=
  (finiteCyclicInvariantNormRange (originalIdeleClassRep K L) g).mkQ.comp
    (originalIdeleClassBaseInvariant K L g)

/-- The kernel of the actual base class map is exactly the actual descended class norm range. -/
theorem originalIdeleClassBaseNormQuotientMap_ker (g : Gal(L/K)) :
    LinearMap.ker (originalIdeleClassBaseNormQuotientMap K L g) =
      (originalIdeleClassNormLinear K L).range := by
  ext c
  change (finiteCyclicInvariantNormRange (originalIdeleClassRep K L) g).mkQ
    (originalIdeleClassBaseInvariant K L g c) = 0 ↔ _
  rw [originalIdeleClassInvariantNormQuotient_mk_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    apply originalIdeleClassBaseChangeMap_injective K L
    exact (originalIdeleClassBaseChangeMap_norm K L y).trans hy
  · rintro ⟨y, hy⟩
    refine ⟨y.toMul, ?_⟩
    rw [← originalIdeleClassBaseChangeMap_norm]
    exact congrArg (fun z => originalIdeleClassBaseChangeMap K L (Additive.toMul z)) hy

/-- Every original invariant norm class is represented by an actual original base class. -/
theorem originalIdeleClassBaseNormQuotientMap_surjective
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Function.Surjective (originalIdeleClassBaseNormQuotientMap K L g) :=
  (finiteCyclicInvariantNormRange (originalIdeleClassRep K L) g).mkQ_surjective.comp
    (originalIdeleClassBaseInvariantEquiv K L g hg).surjective

/-- The actual original base class norm quotient is the proved original invariant norm quotient. -/
def originalIdeleClassNormQuotientEquiv
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    OriginalIdeleClassNormQuotient K L ≃ₗ[ℤ] OriginalIdeleClassInvariantNormQuotient K L g :=
  (Submodule.quotEquivOfEq _ _ (originalIdeleClassBaseNormQuotientMap_ker K L g).symm).trans
    ((originalIdeleClassBaseNormQuotientMap K L g).quotKerEquivOfSurjective
      (originalIdeleClassBaseNormQuotientMap_surjective K L g hg))

/-- The actual original base class norm quotient is finite and its order is at least the extension degree. -/
theorem originalIdeleClassNormQuotient_degree_lower :
    Finite (OriginalIdeleClassNormQuotient K L) ∧
      Module.finrank K L ≤ Nat.card (OriginalIdeleClassNormQuotient K L) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨hfinite, hcard⟩ := originalIdeleClassInvariantNormQuotient_degree_lower K L g hg
  letI := hfinite
  let e := originalIdeleClassNormQuotientEquiv K L g hg
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, (Nat.card_congr e.toEquiv).symm ▸ hcard⟩

/-- The actual extension degree annihilates the actual original base class norm quotient. -/
theorem originalIdeleClassNormQuotient_degree_nsmul_zero (x : OriginalIdeleClassNormQuotient K L) :
    Module.finrank K L • x = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e := originalIdeleClassNormQuotientEquiv K L g hg
  apply e.injective
  change e.toAddEquiv.toAddMonoidHom (Module.finrank K L • x) = e.toAddEquiv.toAddMonoidHom 0
  rw [map_nsmul e.toAddEquiv.toAddMonoidHom, map_zero e.toAddEquiv.toAddMonoidHom]
  exact originalIdeleClassInvariantNormQuotient_degree_nsmul_zero K L g hg (e x)

end
end Dubon2026
