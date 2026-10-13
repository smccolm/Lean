import Dubon2026.OriginalSUnitSelectedPrimes
import Dubon2026.NumberFieldGaloisStableIdeleSupport
import Dubon2026.SUnitFiniteSupport

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
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- All support and selected-prime data are constructed together for the
original prime-degree extension, including the actual local correction map. -/
theorem original_exists_sUnit_selected_support
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K E = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T),
      S₀ ⊆ S ∧
      T.card + 1 = Fintype.card (InfinitePlace K) + S.card ∧
      Function.Surjective (originalSUnitLocalPowerMap K p S T hST) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap K S) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), originalFinitePrimeBelow K E w ∉ S →
        Algebra.IsUnramifiedAt ℤ w.asIdeal) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), originalFinitePrimeBelow K E w ∈ T →
        OriginalFiniteDecompositionGroup K E w = ⊥ := by
  have hp : p.Prime := Fact.out
  letI : NumberField E := NumberField.of_module_finite K E
  let a : Kˣ := Units.mk0 (p : K) (Nat.cast_ne_zero.mpr hp.ne_zero)
  let U := (unit_valuation_support_finite (R := 𝓞 K) a).toFinset
  have hExp (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) : v ∈ U := by
    apply (Set.Finite.mem_toFinset _).mpr
    have hlt := (v.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).mpr hv
    simpa only [map_natCast] using hlt.ne
  let B := (S₀ ∪ originalNormRamificationSupport K E) ∪ U
  obtain ⟨C, hC, hClasses⟩ := numberField_exists_supportedIdeleClassMap_surjective K B
  obtain ⟨S, T, hST, hS, hCount, hSurj, hSplit⟩ :=
    original_exists_sUnit_selected_primes K Ω E p hDegree ζ hζ C
      (fun v hv => hC (Finset.mem_union_right _ (hExp v hv)))
  have hBS : B ⊆ S := hC.trans hS
  refine ⟨S, T, hST, ?_, hCount, hSurj,
    numberFieldSupportedIdeleClassMap_surjective_mono K hS hClasses, ?_, ?_, hSplit⟩
  · exact (Finset.subset_union_left.trans Finset.subset_union_left).trans hBS
  · intro v hv hpv
    exact hv (hBS (Finset.mem_union_right _ (hExp v hpv)))
  · intro w hw
    apply originalNormRamificationSupport_unramified K E w
    intro h
    exact hw (hBS (Finset.mem_union_left _ (Finset.mem_union_right _ h)))

end
end Dubon2026
