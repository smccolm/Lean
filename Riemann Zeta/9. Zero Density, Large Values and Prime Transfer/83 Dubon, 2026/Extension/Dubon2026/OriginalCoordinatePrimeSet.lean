import Dubon2026.OriginalDecompositionRestriction
import Dubon2026.OriginalDistinctCoordinatePrimes
import Dubon2026.OriginalNormRamificationSupport

/-! # Original coordinate primes with proved splitting

The coordinate prime selection now avoids the actual ramification support.
Its original stabilizers are precisely the prescribed cyclic generators.
For coordinates on a restriction kernel, the resulting finite base-prime
set has the exact cardinality and splits throughout the subextension.
These are the disjointness, count and splitting premises in DUB-17's
principal/class index and local-norm containment chain. The S-unit
localization kernel must still be identified separately.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- Trivial original decomposition at one upper prime implies trivial
decomposition at every upper prime above the same original base prime. -/
theorem originalFiniteDecomposition_eq_bot_of_same_base
    (w₁ w₂ : HeightOneSpectrum (𝓞 L))
    (hBelow : originalFinitePrimeBelow K L w₁ = originalFinitePrimeBelow K L w₂)
    (hBot : OriginalFiniteDecompositionGroup K L w₁ = ⊥) :
    OriginalFiniteDecompositionGroup K L w₂ = ⊥ := by
  obtain ⟨σ, hσ⟩ := (originalFinitePrimeBelow_eq_iff_orbit K L w₁ w₂).mp hBelow
  letI := numberFieldGaloisPlaceAction K L
  change MulAction.stabilizer Gal(L/K) w₁ = ⊥ at hBot
  rw [← hσ]
  change MulAction.stabilizer Gal(L/K) (σ • w₁) = ⊥
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hBot, Subgroup.map_bot]

/-- The distinct coordinate primes can be chosen unramified, with their
entire original decomposition groups equal to the coordinate cyclic subgroups. -/
theorem original_primeCoordinate_primes_decomposition
    (p : ℕ) (hp : p.Prime) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (r : ℕ) (H : Subgroup Gal(L/K))
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : Fin r → HeightOneSpectrum (𝓞 L),
      Function.Injective (fun i => originalFinitePrimeBelow K L (w i)) ∧
      ∀ i, originalFinitePrimeBelow K L (w i) ∉ S ∧
        Algebra.IsUnramifiedAt ℤ (w i).asIdeal ∧
        OriginalFiniteDecompositionGroup K L (w i) =
          Subgroup.zpowers (primeCoordinateGenerator e i).val := by
  obtain ⟨w, hInjective, hw⟩ := original_primeCoordinate_primes_distinct
    K L p hp r H e (S ∪ originalNormRamificationSupport K L)
  refine ⟨w, hInjective, ?_⟩
  intro i
  have hUnram := originalNormRamificationSupport_unramified K L (w i)
    (fun h => (hw i).1 (Finset.mem_union_right _ h))
  refine ⟨fun h => (hw i).1 (Finset.mem_union_left _ h), hUnram, ?_⟩
  apply originalFiniteDecomposition_eq_zpowers_of_relative_top K L p hp.pos hPower
    (primeCoordinateGenerator e i).val _ (w i) hUnram (hw i).2
  rw [Subgroup.orderOf_coe, primeCoordinateGenerator_order]

/-- Coordinates on the actual restriction kernel give a disjoint set of
exactly r original base primes, all split in the prescribed subextension;
the chosen upper primes retain their exact coordinate decomposition groups. -/
theorem original_primeCoordinate_split_primeSet
    (E : IntermediateField K L) [IsGalois K E]
    (p : ℕ) (hp : p.Prime) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (r : ℕ) (e : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃*
      (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (w : Fin r → HeightOneSpectrum (𝓞 L)),
      T = Finset.univ.image (fun i => originalFinitePrimeBelow K L (w i)) ∧
      T.card = r ∧ Disjoint S T ∧
      (∀ i, OriginalFiniteDecompositionGroup K L (w i) =
        Subgroup.zpowers (primeCoordinateGenerator e i).val) ∧
      ∀ v : HeightOneSpectrum (𝓞 E), originalFinitePrimeBelow K E v ∈ T →
        OriginalFiniteDecompositionGroup K E v = ⊥ := by
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨w, hInjective, hw⟩ := original_primeCoordinate_primes_decomposition
    K L p hp hPower r _ e S
  let T := Finset.univ.image (fun i => originalFinitePrimeBelow K L (w i))
  refine ⟨T, w, rfl, ?_, ?_, fun i => (hw i).2.2, ?_⟩
  · rw [Finset.card_image_of_injective _ hInjective, Finset.card_univ, Fintype.card_fin]
  · apply Finset.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hvT
    exact (hw i).1 (hi.symm ▸ hvS)
  · intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have hBot : OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L (w i)) = ⊥ := by
      apply originalFiniteDecomposition_below_eq_bot_of_le_ker K L E (w i)
      rw [(hw i).2.2]
      exact Subgroup.zpowers_le.mpr (primeCoordinateGenerator e i).property
    apply originalFiniteDecomposition_eq_bot_of_same_base K E
      (originalFinitePrimeBelow E L (w i)) v _ hBot
    rw [originalFinitePrimeBelow_tower]
    exact hi

end
end Dubon2026
