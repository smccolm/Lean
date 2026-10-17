import Dubon2026.OriginalFiniteClassRelationExtension
import Dubon2026.OriginalQuotientH2SubgroupGenerators

/-! # Arithmetic relation extension needs only one full-order class

The existing original full-class/quotient isomorphism, subgroup H1
vanishing and restriction-generator theorem discharge all finite class
data from a single full-order original idele-class H2 element. DUB-17's
relation step therefore needs no completion-normalized class-system
premise. OriginalRationalFullOrderClass now constructs that element for
every rational finite Galois field, including the actual enlarged stage.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- An original full-idele-class element of full order suffices for the
actual outside-unit quotient relation criterion. All subgroup class
data and the quotient generator are derived from the existing arithmetic
theorems; completion-normalization is not a hypothesis. -/
theorem originalClassQuotient_relation_extension_of_full_order
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hunram : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L)
    (p : ℕ) [Fact p.Prime] (N : Subgroup Gal(L/K)) [Fintype N]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) χ = 0 ↔
      ∃ a : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
        originalRelationInclusion B ≫ a = χ := by
  let e := (originalClassesModOutsideH2Iso K L S hS hunram).toLinearEquiv
  have he : addOrderOf (e u) = Module.finrank K L :=
    (e.toAddEquiv.addOrderOf_eq u).trans hu
  obtain ⟨hc, hg⟩ :=
    originalClassQuotient_full_order_restricts_to_generators K L S hS hunram (e u) he
  exact originalFiniteClass_relation_extension_iff
    (originalIdeleClassesModOutsideRep K L S hS) (e u)
    (he.trans (IsGalois.card_aut_eq_finrank K L).symm)
    (fun H => originalClassQuotientSubgroup_first_zero K L S hS H hunram)
    hc hg p N hnorm B hB hNB χ

end
end Dubon2026
