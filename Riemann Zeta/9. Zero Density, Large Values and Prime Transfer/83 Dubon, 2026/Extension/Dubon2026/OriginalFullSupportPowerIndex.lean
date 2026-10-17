import Dubon2026.OriginalPrincipalSUnitLocalization
import Dubon2026.OriginalPrincipalPowerIndex

/-! # The original class power quotient for full supported classes

The existing principal localization theorem is applied with no auxiliary
selected primes. Its correction map is surjective because its target is
the empty product. The existing exact sequence and S-unit power cardinality
then compute the literal class quotient. This is the index input to the
S-unit Kummer norm-field construction in DUB-17's invariant norm-root chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]

/-- With no selected auxiliary primes, principal localization follows
from the already proved original Kummer norm-descent theorem. -/
theorem originalSUnitPowerLocalSubgroup_empty_eq_powers
    (p : ℕ) (hp : p.Prime) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) :
    originalSUnitPowerLocalSubgroup K p S ∅ =
      (powMonoidHom p : ((↑(S ∪ ∅) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ ∅) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range := by
  apply originalSUnitPowerLocalSubgroup_eq_powers K p hp ζ hζ S ∅
    (by simp) hClasses _ hBase hAway
  intro x
  refine ⟨1, ?_⟩
  funext v
  exact False.elim (Finset.notMem_empty v.val v.property)

/-- The original class quotient by local powers and outside units has
exactly the S-unit Kummer degree when the supported classes are all classes. -/
theorem originalClassPowerQuotient_card_full_support
    (p : ℕ) (hp : p.Prime) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) :
    Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K p S ∅) =
      p ^ (Fintype.card (InfinitePlace K) + S.card) := by
  have hKernel := originalSUnitPowerLocalSubgroup_empty_eq_powers K p hp ζ hζ S
    hClasses hBase hAway
  have hsu : Nat.card (OriginalSUnitPowerLocalQuotient K p S ∅) =
      p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    unfold OriginalSUnitPowerLocalQuotient
    rw [hKernel]
    simpa only [Finset.union_empty, Finset.coe_sort_coe, Set.ncard_coe_finset] using
      numberField_sUnit_powerQuotient_card K (↑(S ∪ ∅) : Set (HeightOneSpectrum (𝓞 K)))
        (S ∪ ∅).finite_toSet p hp.ne_zero ζ hζ
  have hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    by_contra hnot
    exact hAway v hnot hv
  have h := originalPrincipalPowerIndex_product K p hp.pos ζ hζ S ∅ hS
    (by
      intro c
      obtain ⟨a, ha⟩ := hClasses c
      refine ⟨⟨a.val, ?_⟩, ha⟩
      simpa only [Finset.union_empty] using a.property)
  have hPow : p ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) =
      p ^ (Fintype.card (InfinitePlace K) + S.card) *
        p ^ (Fintype.card (InfinitePlace K) + S.card) := by rw [two_mul, pow_add]
  rw [hsu, hPow] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h

end
end Dubon2026
