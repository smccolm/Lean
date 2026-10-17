import Dubon2026.OriginalNormCoinvariantTransfer

/-! # The literal norm map out of original coinvariants

The pinned coinvariant universal property supplies the actual norm map.
Its injectivity criterion makes an original coefficient inclusion
injective on coinvariants, as required for the homology sequence on
DUB-17's integral duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- The actual finite group norm factors through the original coinvariant quotient. -/
def originalCoinvariantNorm (A : Rep k G) : A.ρ.Coinvariants →ₗ[k] A :=
  Representation.Coinvariants.lift A.ρ A.ρ.norm A.ρ.norm_comp_self

/-- The factored original norm is the literal norm on every representative. -/
theorem originalCoinvariantNorm_mk (A : Rep k G) (x : A) :
    originalCoinvariantNorm A (Representation.Coinvariants.mk A.ρ x) = A.ρ.norm x := rfl

/-- An original coefficient inclusion is injective on coinvariants when its source has injective coinvariant norm. -/
theorem originalCoinvariantMap_injective_of_norm
    {A B : Rep k G} (f : A ⟶ B) (hf : Function.Injective f.hom)
    (hA : OriginalNormCoinvariantInjective A) :
    Function.Injective (Representation.Coinvariants.map A.ρ B.ρ f.hom) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ x
  have hn := congrArg (originalCoinvariantNorm B) hx
  rw [Representation.Coinvariants.map_mk, originalCoinvariantNorm_mk, map_zero] at hn
  apply hA a
  apply hf
  rw [originalCoefficientMorphism_norm, hn, map_zero]

end
end Dubon2026
