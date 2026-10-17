import Dubon2026.OriginalFullClassNormQuotientComparison
import Dubon2026.OriginalFiniteNormalizedClassSystem
import Dubon2026.OriginalFundamentalPGroupVanishing

/-! # The actual full class norm index from the normalized class system

The proved full normalized class system constructs the same fundamental
coefficient. The literal norm quotient is then the abelianization, and
every group-exponent power of a base class is an actual field norm.
These are the exact arithmetic inputs to DUB-17's Kummer norm-field step.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual full normalized class system gives the literal field norm quotient's abelianization, exact order and group-exponent norm preimages. -/
theorem originalFullClass_abelian_norm_index (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p Gal(L/K)) (hsys : OriginalFiniteNormalizedClassSystem K L) :
    Nonempty (OriginalIdeleClassNormQuotient K L ≃+ Additive (Abelianization Gal(L/K))) ∧
    Nat.card (OriginalIdeleClassNormQuotient K L) = Nat.card (Abelianization Gal(L/K)) ∧
    ∀ (n : ℕ), (∀ g : Gal(L/K), g ^ n = 1) →
      ∀ c : OriginalNumberFieldIdeleClassGroup K,
        ∃ b : OriginalNumberFieldIdeleClassGroup L, originalIdeleClassNorm K L b = c ^ n := by
  obtain ⟨u, _, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassRep K L
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  obtain ⟨hv, _, _⟩ := originalFundamentalPGroup_positive_and_norm p hG C φ h1 hc hg
  let e := (originalFullClassNormQuotientEquiv K L).toAddEquiv.trans
    (originalInvariantNormAbelianEquiv C φ p hG hv)
  refine ⟨⟨e⟩, Nat.card_congr e.toEquiv, ?_⟩
  intro n hn c
  let β := originalFullClassBaseInvariantEquiv K L
  obtain ⟨b, hb⟩ := originalInvariant_multiple_is_norm C φ p hG hv n hn (β (Additive.ofMul c))
  refine ⟨b.toMul, ?_⟩
  have he : β (originalIdeleClassNormLinear K L b) = β (n • Additive.ofMul c) :=
    (originalFullClassBaseInvariant_norm K L b).trans
      (hb.trans (map_nsmul β n (Additive.ofMul c)).symm)
  exact congrArg Additive.toMul (β.injective he)

end
end Dubon2026
