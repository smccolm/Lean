import Dubon2026.OriginalPrimeSelectedSupportActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Dubon2026.OriginalPrincipalSUnitLocalization
import Dubon2026.OriginalPrincipalPowerIndex

/-! # Constructed original class power quotient of prime order

The finite seed now also contains the original base ramification support.
The actual selected support therefore satisfies the proved principal
S-union-T localization equality. The existing numerical principal/class
exact sequence evaluates the actual class power quotient as the extension
prime degree. This removes its last selected-kernel assumption in DUB-17's
prime-degree norm-index chain, with original splitting and outside
unramifiedness retained for the already proved norm containment.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
include Ω

/-- A constructed original selected support has the proved principal kernel,
class quotient of order p, splitting and outside unramifiedness. -/
theorem original_exists_prime_class_power_quotient_actual
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S T : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      originalSUnitPowerLocalSubgroup K p S T =
        (powMonoidHom p : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
          ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range ∧
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K p S T) = p ∧
      (∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
        OriginalFiniteDecompositionGroup K L w = ⊥) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
        Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  have hp : p.Prime := Fact.out
  let B := (original_finite_absolutely_ramified_places K).toFinset
  obtain ⟨S, T, hST, hS, hCount, hSurj, hClasses, hAway, hUnram, hSplit⟩ :=
    original_exists_sUnit_selected_support_actual K L Ω p hDegree ζ hζ (S₀ ∪ B)
  have hBase (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)))
  have hKernel := originalSUnitPowerLocalSubgroup_eq_powers K p hp ζ hζ S T hST
    hClasses hSurj hBase hAway
  refine ⟨S, T, Finset.subset_union_left.trans hS, hKernel, ?_, hSplit, ?_⟩
  · apply originalClassPowerQuotient_card_of_selected_kernel K p hp.pos ζ hζ S T
      _ _ hST hCount hKernel
    · intro v hv
      by_contra h
      exact hAway v h hv
    · exact numberFieldSupportedIdeleClassMap_surjective_mono K
        (show (S : Set (HeightOneSpectrum (𝓞 K))) ⊆ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))
          from Finset.subset_union_left) hClasses
  · intro w hw
    exact hUnram w (fun h => hw (Finset.mem_union_left _ h))

end
end Dubon2026

/-! # Exact original prime-degree norm index with base roots of unity

The constructed class power quotient has order equal to the actual prime
degree. Proved original local norm containment gives a surjection onto
the literal original class norm quotient; the existing degree lower bound
gives the reverse inequality. This closes the root-of-unity prime step of
DUB-17's norm-index chain. Coprime cyclotomic descent, cyclic induction and
the subsequent global reciprocity/duality and automorphy obligations remain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
include Ω

/-- The literal original norm quotient has exactly the prime extension
degree when the base contains the corresponding primitive root. -/
theorem original_primeDegree_normQuotient_card_of_primitiveRoot_actual
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
      Nat.card (OriginalIdeleClassNormQuotient K L) = p := by
  have hp : p.Prime := Fact.out
  have hCard : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hDegree
  letI : IsCyclic Gal(L/K) := isCyclic_of_prime_card hCard
  obtain ⟨S, T, _, _, hPowerCard, hSplit, hAway⟩ :=
    original_exists_prime_class_power_quotient_actual K L Ω p hDegree ζ hζ ∅
  letI : Finite (OriginalIdeleClassPowerLocalUnitQuotient K p S T) :=
    Nat.finite_of_card_ne_zero (hPowerCard.symm ▸ hp.ne_zero)
  have hContain : originalIdeleClassPowerLocalUnitSubmodule K p S T ≤
      (originalIdeleClassNormLinear K L).range := by
    intro x hx
    have hC := originalIdeleClassPowerLocalUnitSubgroup_le_norm K L S T hSplit hAway
    rw [hDegree] at hC
    obtain ⟨y, hy⟩ := hC hx
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  let f : OriginalIdeleClassPowerLocalUnitQuotient K p S T →ₗ[ℤ]
      OriginalIdeleClassNormQuotient K L :=
    (originalIdeleClassPowerLocalUnitSubmodule K p S T).mapQ
      (originalIdeleClassNormLinear K L).range LinearMap.id hContain
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := (originalIdeleClassNormLinear K L).range.mkQ_surjective c
    exact ⟨(originalIdeleClassPowerLocalUnitSubmodule K p S T).mkQ x, rfl⟩
  apply Nat.le_antisymm
  · exact hPowerCard ▸ Nat.card_le_card_of_surjective f hf
  · exact hDegree ▸ (originalIdeleClassNormQuotient_degree_lower K L).2

end
end Dubon2026

namespace Dubon2026
noncomputable section
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The original prime-degree class norm quotient has order p with a base
primitive root. The ambient closure is constructed, not assumed. -/
theorem original_primeDegree_normQuotient_card_roots
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    Nat.card (OriginalIdeleClassNormQuotient K L) = p := by
  exact original_primeDegree_normQuotient_card_of_primitiveRoot_actual
    K L (AlgebraicClosure L) p hDegree ζ hζ

end
end Dubon2026
