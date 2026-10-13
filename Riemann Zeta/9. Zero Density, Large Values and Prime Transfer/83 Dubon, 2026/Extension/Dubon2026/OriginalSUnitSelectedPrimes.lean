import Dubon2026.OriginalSUnitKummerPrimeCoordinates
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
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- For the original prime-degree extension, the actual selected primes
split, have the required count, and provide all local unit-power corrections
by original S-units. All coordinate and image hypotheses are discharged. -/
theorem original_exists_sUnit_selected_primes
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K E = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSeed : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T),
      S₀ ⊆ S ∧
      T.card + 1 = Fintype.card (InfinitePlace K) + S.card ∧
      Function.Surjective (originalSUnitLocalPowerMap K p S T hST) ∧
      ∀ v : HeightOneSpectrum (𝓞 E), originalFinitePrimeBelow K E v ∈ T →
        OriginalFiniteDecompositionGroup K E v = ⊥ := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  obtain ⟨S, hE, hS, hf, hCount, ⟨e⟩⟩ :=
    numberField_exists_prime_sUnit_kummer_coordinates E p hDegree ζ hζ S₀
  let N := OriginalSUnitKummerField K Ω S p
  letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
  letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp.pos hroot
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField N := NumberField.of_module_finite K N
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
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
    have hBot : OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E N (w i)) = ⊥ := by
      apply originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower K E N (w i)
      rw [(hw i).2.2]
      exact Subgroup.zpowers_le.mpr (primeCoordinateGenerator e i).property
    apply originalFiniteDecomposition_eq_bot_of_same_base K E
      (originalFinitePrimeBelow E N (w i)) v _ hBot
    rw [originalFinitePrimeBelow_tower]
    exact hi

end
end Dubon2026
