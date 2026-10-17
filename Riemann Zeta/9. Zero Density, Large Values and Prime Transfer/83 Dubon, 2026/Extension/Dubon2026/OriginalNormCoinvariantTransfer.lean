import Dubon2026.OriginalCoinducedNormKernel
import Dubon2026.OriginalArbitraryFreeCoinduced

/-! # Actual norm injectivity on coinvariants and coefficient retracts

The literal condition below says exactly that zero norm implies zero
coinvariant. It is proved for the arbitrary free cover via the actual
coinduced isomorphism, supplying DUB-17's required presentation input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- Literal injectivity of the norm on the original coinvariant quotient, expressed on representatives. This definition alone asserts no instance. -/
def OriginalNormCoinvariantInjective (A : Rep k G) : Prop :=
  ∀ x : A, A.ρ.norm x = 0 → Representation.Coinvariants.mk A.ρ x = 0

/-- Actual norm injectivity on coinvariants descends through an original coefficient retraction. -/
theorem originalNormCoinvariantInjective_of_retract {A B : Rep k G}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (hB : OriginalNormCoinvariantInjective B) : OriginalNormCoinvariantInjective A := by
  intro x hx
  have hi : B.ρ.norm (i.hom x) = 0 := by
    rw [← originalCoefficientMorphism_norm, hx, map_zero]
  have hz := congrArg (Representation.Coinvariants.map B.ρ A.ρ r.hom) (hB _ hi)
  rw [Representation.Coinvariants.map_mk, map_zero] at hz
  have he : r.hom (i.hom x) = x := congrArg (fun f : A ⟶ A => f.hom x) hir
  rwa [he] at hz

/-- The literal arbitrary-index free representation has injective norm on its actual coinvariants. -/
theorem originalArbitraryFree_normCoinvariantInjective (α : Type) :
    OriginalNormCoinvariantInjective (Rep.free k G α) :=
  originalNormCoinvariantInjective_of_retract
    (originalArbitraryFreeCoinducedIso α).hom (originalArbitraryFreeCoinducedIso α).inv
    (originalArbitraryFreeCoinducedIso α).hom_inv_id
    (originalCoinduced_coinvariant_zero_of_norm_zero (Rep.trivial k G (α →₀ k)))

end
end Dubon2026
