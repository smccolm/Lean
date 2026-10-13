import Dubon2026.OriginalPrimeSUnitKummerTower
import Dubon2026.NumberFieldGaloisStableIdeleSupport
import Dubon2026.SUnitFiniteSupport
import Dubon2026.OriginalCoordinatePrimeSet
import Dubon2026.OriginalDecompositionAlgebraTower
import Dubon2026.OriginalSUnitSelectedImageCardinality

/-! # Selected primes with the original S-unit correction map

The proved Kummer enlargement and coordinate prime selection are assembled
on the same actual field. The original restriction kernel forces splitting
in the prescribed extension, and the proved image cardinality makes the
original S-unit local-power map surjective. Only the finite seed support of
the exponent is assumed; disjointness, the precise count and the local
correction map are constructed. This supplies DUB-17's remaining principal
S-union-T localization argument, then the class norm-index upper bound.
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

/-- For the original prime-degree extension, the actual selected primes
split, have the required count, and provide all local unit-power corrections
by original S-units. All coordinate and image hypotheses are discharged. -/
theorem original_exists_sUnit_selected_primes_actual
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSeed : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T),
      S₀ ⊆ S ∧
      T.card + 1 = Fintype.card (InfinitePlace K) + S.card ∧
      Function.Surjective (originalSUnitLocalPowerMap K p S T hST) ∧
      ∀ v : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L v ∈ T →
        OriginalFiniteDecompositionGroup K L v = ⊥ := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  obtain ⟨S, j, hS, hf, hCount, ⟨e⟩⟩ :=
    original_primeDegree_sUnit_kummer_tower_coordinates K L Ω p hDegree ζ hζ S₀
  let N := OriginalSUnitKummerField K Ω S p
  letI : Algebra L N := j.toAlgebra
  letI : IsScalarTower K L N := IsScalarTower.of_algHom j
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp.pos hroot
  letI : NumberField N := NumberField.of_module_finite K N
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  let f : Gal(N/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let r := Fintype.card (InfinitePlace K) + S.card - 1
  have hPower (σ : Gal(N/K)) : σ ^ p = 1 :=
    originalKummerRadicalField_galois_pow_eq_one p hroot _ σ
  obtain ⟨w, hInjective, hw⟩ := original_primeCoordinate_primes_decomposition
    K N p hp hPower r f.ker e S
  let T := Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i))
  have hTCount : T.card = r := by
    rw [Finset.card_image_of_injective _ hInjective, Finset.card_univ, Fintype.card_fin]
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hvT
    exact (hw i).1 (hi.symm ▸ hvS)
  refine ⟨S, T, hST, hS, ?_, ?_, ?_⟩
  · dsimp [r] at hTCount
    omega
  · apply originalSUnitSelectedPowerMap_surjective K Ω S p hp.pos hroot
      f.ker r e w T rfl hST hTCount _ (fun i => (hw i).2.2)
    intro v hv
    exact (Finset.disjoint_left.mp hST) (hS (hSeed v.val hv)) v.property
  · intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have hBot : OriginalFiniteDecompositionGroup K L (originalFinitePrimeBelow L N (w i)) = ⊥ := by
      apply originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower K L N (w i)
      rw [(hw i).2.2]
      exact Subgroup.zpowers_le.mpr (primeCoordinateGenerator e i).property
    apply originalFiniteDecomposition_eq_bot_of_same_base K L
      (originalFinitePrimeBelow L N (w i)) v _ hBot
    rw [originalFinitePrimeBelow_tower]
    exact hi

end
end Dubon2026

/-! # Joint original support for the prime norm-index calculation

The existing finite class-surjective support and actual ramification
support are combined with the finite support of the exponent. Enlarging
by the proved S-unit prime-selection theorem preserves all three. Thus
the same constructed S and T provide the count, splitting, local-power
correction surjectivity, global class representatives, and unramified
outside places required by DUB-17's norm-index upper-bound argument.
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

/-- All support and selected-prime data are constructed together for the
original prime-degree extension, including the actual local correction map. -/
theorem original_exists_sUnit_selected_support_actual
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T),
      S₀ ⊆ S ∧
      T.card + 1 = Fintype.card (InfinitePlace K) + S.card ∧
      Function.Surjective (originalSUnitLocalPowerMap K p S T hST) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap K S) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
        Algebra.IsUnramifiedAt ℤ w.asIdeal) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
        OriginalFiniteDecompositionGroup K L w = ⊥ := by
  have hp : p.Prime := Fact.out
  let a : Kˣ := Units.mk0 (p : K) (Nat.cast_ne_zero.mpr hp.ne_zero)
  let U := (unit_valuation_support_finite (R := 𝓞 K) a).toFinset
  have hExp (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) : v ∈ U := by
    apply (Set.Finite.mem_toFinset _).mpr
    have hlt := (v.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).mpr hv
    simpa only [map_natCast] using hlt.ne
  let B := (S₀ ∪ originalNormRamificationSupport K L) ∪ U
  obtain ⟨C, hC, hClasses⟩ := numberField_exists_supportedIdeleClassMap_surjective K B
  obtain ⟨S, T, hST, hS, hCount, hSurj, hSplit⟩ :=
    original_exists_sUnit_selected_primes_actual K L Ω p hDegree ζ hζ C
      (fun v hv => hC (Finset.mem_union_right _ (hExp v hv)))
  have hBS : B ⊆ S := hC.trans hS
  refine ⟨S, T, hST, ?_, hCount, hSurj,
    numberFieldSupportedIdeleClassMap_surjective_mono K hS hClasses, ?_, ?_, hSplit⟩
  · exact (Finset.subset_union_left.trans Finset.subset_union_left).trans hBS
  · intro v hv hpv
    exact hv (hBS (Finset.mem_union_right _ (hExp v hpv)))
  · intro w hw
    apply originalNormRamificationSupport_unramified K L w
    intro h
    exact hw (hBS (Finset.mem_union_left _ (Finset.mem_union_right _ h)))

end
end Dubon2026
