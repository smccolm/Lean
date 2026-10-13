import Dubon2026.OriginalSupportedPowerIndex
import Dubon2026.OriginalPrincipalPowerExactSequence
import Dubon2026.NumberFieldSUnitPowerCardinality

/-! # Original principal/class numerical index calculation

The actual exact sequence now consumes all proved local numerical factors.
For the prime-degree route to DUB-17's global norm-index bound, only the
selected-prime cardinality and localization equality of the actual S-unit
kernel remain explicit. These are narrower Kummer prime-selection inputs,
not an assumed class-index or norm-index conclusion.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]

/-- The actual original principal/class exact sequence has the fully
evaluated middle-term cardinality. -/
theorem originalPrincipalPowerIndex_product
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hLarge : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalSUnitPowerLocalQuotient K n S T) *
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) =
        n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) := by
  rw [originalSUnitPowerLocalQuotient_card_mul_class K n S T hLarge,
    originalSupportedPowerLocalUnitQuotient_card_exact K n hn ζ hζ S T hS]

/-- For a selected split-prime support of the prime-degree size, the
actual localization equality of the principal S-unit kernel gives class
power-quotient order n. The selected-prime inputs remain explicit. -/
theorem originalClassPowerQuotient_card_of_selected_kernel
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hLarge : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))))
    (hDisjoint : Disjoint S T)
    (hCount : T.card + 1 = Fintype.card (InfinitePlace K) + S.card)
    (hKernel : originalSUnitPowerLocalSubgroup K n S T =
      (powMonoidHom n : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range) :
    Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) = n := by
  have hsu : Nat.card (OriginalSUnitPowerLocalQuotient K n S T) =
      n ^ (Fintype.card (InfinitePlace K) + (S ∪ T).card) := by
    unfold OriginalSUnitPowerLocalQuotient
    rw [hKernel]
    simpa only [Finset.coe_sort_coe, Set.ncard_coe_finset] using
      numberField_sUnit_powerQuotient_card K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))
        (S ∪ T).finite_toSet n hn.ne' ζ hζ
  have h := originalPrincipalPowerIndex_product K n hn ζ hζ S T hS hLarge
  rw [hsu] at h
  have he : 2 * (Fintype.card (InfinitePlace K) + S.card) =
      (Fintype.card (InfinitePlace K) + (S ∪ T).card) + 1 := by
    rw [Finset.card_union_of_disjoint hDisjoint]
    omega
  rw [he, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hn _) h

end
end Dubon2026
