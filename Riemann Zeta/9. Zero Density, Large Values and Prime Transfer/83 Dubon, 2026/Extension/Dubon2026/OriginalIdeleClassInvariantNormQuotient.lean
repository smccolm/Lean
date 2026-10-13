import Dubon2026.OriginalIdeleClassHerbrand
import Dubon2026.FiniteCyclicPeriodQuotient

/-! # The actual invariant idele classes modulo their original group norms

The existing periodic projection identifies the original cyclic H2 with
the quotient of the actual generator-fixed idele classes by the actual
representation norm. Its product formula uses the original Galois maps.
This is the cohomological norm quotient needed for DUB-17's norm-index
lower bound. Descent to a base-field idele-class norm quotient remains
a separate original-object comparison.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

/-- The actual norm quotient inside the original generator-fixed idele classes. -/
abbrev OriginalIdeleClassInvariantNormQuotient (g : Gal(L/K)) :=
  LinearMap.ker (Rep.applyAsHom (originalIdeleClassRep K L) g - 𝟙 _).hom.toLinearMap ⧸
    finiteCyclicInvariantNormRange (originalIdeleClassRep K L) g

omit [IsCyclic Gal(L/K)] in
/-- The actual original coefficient norm is the product of the original Galois class maps. -/
theorem originalIdeleClass_representation_norm (x : OriginalNumberFieldIdeleClassGroup L) :
    Additive.toMul ((originalIdeleClassRep K L).norm.hom (Additive.ofMul x)) =
      ∏ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ x := by
  letI := numberFieldIdeleClassGaloisAction K L
  exact Representation.norm_ofMulDistribMulAction_eq (G := Gal(L/K)) (Additive.ofMul x)

/-- The original cyclic H2 projection has exactly the original invariant norm range as kernel. -/
theorem originalIdeleClass_cyclicPi_ker (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    LinearMap.ker (Rep.FiniteCyclicGroup.groupCohomologyπEven
      (originalIdeleClassRep K L) g hg 2 (by decide)).hom =
        finiteCyclicInvariantNormRange (originalIdeleClassRep K L) g := by
  ext x
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (originalIdeleClassRep K L) g hg 2 (by decide) x

/-- An actual invariant class is zero in this quotient exactly when it is a product of the original Galois conjugates of one original idele class. -/
theorem originalIdeleClassInvariantNormQuotient_mk_eq_zero_iff
    (g : Gal(L/K)) :
    let A := originalIdeleClassRep K L
    ∀ x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap,
    (finiteCyclicInvariantNormRange A g).mkQ x = 0 ↔
      ∃ y : OriginalNumberFieldIdeleClassGroup L,
        (∏ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ y) = Additive.toMul x.val := by
  intro A x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (∃ y : originalIdeleClassRep K L,
    (originalIdeleClassRep K L).norm.hom y = x.val) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    rw [← originalIdeleClass_representation_norm K L (Additive.toMul y)]
    exact congrArg Additive.toMul hy
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    rw [originalIdeleClass_representation_norm]
    exact hy

/-- The literal original invariant norm quotient is the original cyclic idele-class H2. -/
def originalIdeleClassInvariantNormQuotientEquiv
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    OriginalIdeleClassInvariantNormQuotient K L g ≃ₗ[ℤ]
      groupCohomology (originalIdeleClassRep K L) 2 :=
  (Submodule.quotEquivOfEq _ _ (originalIdeleClass_cyclicPi_ker K L g hg).symm).trans
    ((Rep.FiniteCyclicGroup.groupCohomologyπEven
      (originalIdeleClassRep K L) g hg 2 (by decide)).hom.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The original invariant norm quotient is finite and has order at least the original cyclic group order. -/
theorem originalIdeleClassInvariantNormQuotient_order_lower
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Finite (OriginalIdeleClassInvariantNormQuotient K L g) ∧
      Nat.card Gal(L/K) ≤ Nat.card (OriginalIdeleClassInvariantNormQuotient K L g) := by
  obtain ⟨h1, h2, hcard⟩ := original_ideleClass_herbrand K L
  haveI := h1
  haveI := h2
  let e := originalIdeleClassInvariantNormQuotientEquiv K L g hg
  refine ⟨Finite.of_equiv (groupCohomology (originalIdeleClassRep K L) 2) e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, hcard]
  exact Nat.le_mul_of_pos_left _ (Nat.card_pos (α := groupCohomology (originalIdeleClassRep K L) 1))

end
end Dubon2026
