import Dubon2026.OriginalClassPowerOutsideComparison
import Dubon2026.OriginalFullSupportPowerIndex
import Dubon2026.OriginalOutsideUnitNormContainment
import Dubon2026.OriginalFullClassAbelianNormIndex

/-! # Exact original norm subgroup from the S-unit Kummer degree

The actual abelian norm index and exponent-power norm preimages, original
outside-unit norm containment and exact local-power quotient order imply
equality of the literal class subgroups. The remaining field-construction
inputs are explicit: its degree, exponent, unramifiedness and normalized
class system. This is the large-support Kummer step serving DUB-17's
prescribed-support norm field and enlarged-stage invariant norm roots.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
  Submodule.module Submodule.Quotient.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]

/-- An actual abelian prime-exponent field with the S-unit Kummer degree
has exactly the original power-plus-outside-unit class norm subgroup. -/
theorem originalFullSupport_normRange_eq_power_sup_outside
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L)
    (hexp : ∀ g : Gal(L/K), g ^ p = 1)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal)
    (hUpper : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (hDegree : Module.finrank K L = p ^ (Fintype.card (InfinitePlace K) + S.card)) :
    LinearMap.range (originalIdeleClassNormLinear K L) =
      LinearMap.range ((p : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  have hp : p.Prime := Fact.out
  obtain ⟨_, hcard, hpower⟩ := originalFullClass_abelian_norm_index K L p hG hsys
  let B := originalIdeleClassPowerLocalUnitSubmodule K p S ∅
  let N := LinearMap.range (originalIdeleClassNormLinear K L)
  have hB := originalClassPowerLocalUnitSubmodule_eq_power_sup_outside K S hS p hClasses
  have hBN : B ≤ N := by
    rw [show B = originalIdeleClassPowerLocalUnitSubmodule K p S ∅ from rfl, hB]
    apply sup_le
    · rintro x ⟨c, rfl⟩
      obtain ⟨b, hb⟩ := hpower p hexp c.toMul
      refine ⟨Additive.ofMul b, ?_⟩
      change Additive.ofMul (originalIdeleClassNorm K L b) = (p : ℤ) • c
      rw [hb, natCast_zsmul]
      rfl
    · exact originalOutsideIdeleClass_range_le_norm K L S hS hUpper
  have hNcard : Nat.card (originalIdeleClassRep K K ⧸ N) =
      p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    calc
      _ = Nat.card (Abelianization Gal(L/K)) := hcard
      _ = Nat.card Gal(L/K) := (Nat.card_congr (Abelianization.equivOfComm (H := Gal(L/K))).toEquiv).symm
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      _ = _ := hDegree
  have hBcard : Nat.card (originalIdeleClassRep K K ⧸ B) =
      p ^ (Fintype.card (InfinitePlace K) + S.card) :=
    originalClassPowerQuotient_card_full_support K p hp ζ hζ S hClasses hBase hAway
  letI : Finite (originalIdeleClassRep K K ⧸ B) :=
    Nat.finite_of_card_ne_zero (hBcard.trans_ne (pow_ne_zero _ hp.ne_zero))
  let f : (originalIdeleClassRep K K ⧸ B) →ₗ[ℤ] (originalIdeleClassRep K K ⧸ N) :=
    B.mapQ N LinearMap.id hBN
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := N.mkQ_surjective y
    exact ⟨B.mkQ c, rfl⟩
  have hinj := ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hsurj, hBcard.trans hNcard.symm⟩).1
  have hNB : N ≤ B := by
    intro c hc
    have hz : f (B.mkQ c) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hc
    have hc0 : B.mkQ c = 0 := hinj (hz.trans f.map_zero.symm)
    exact (Submodule.Quotient.mk_eq_zero B).mp hc0
  exact (le_antisymm hNB hBN).trans hB

end
end Dubon2026
