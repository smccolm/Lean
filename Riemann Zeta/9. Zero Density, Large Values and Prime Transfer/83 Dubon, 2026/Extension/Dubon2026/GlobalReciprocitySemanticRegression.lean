import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
section

variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L] [IsGalois K E]





/-- Exact original-object consumer of `originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower`. -/
theorem actual_original_sunit_localization_originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower_source
    (w : HeightOneSpectrum (𝓞 L))
    (hD : OriginalFiniteDecompositionGroup K L w ≤ (AlgEquiv.restrictNormalHom E).ker) :
    OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w) = ⊥ :=
  originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower K E L w hD

end

section

variable {K : Type} [Field K] (A : ValuationSubring K)





/-- Exact original-object consumer of `valuationSubring_unit_mem_power_range_iff`. -/
theorem actual_original_sunit_localization_valuationSubring_unit_mem_power_range_iff_source
    (n : ℕ) (hn : n ≠ 0) (x : Aˣ) :
    x ∈ (powMonoidHom n : Aˣ →* Aˣ).range ↔
      Units.map A.subtype.toMonoidHom x ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
  valuationSubring_unit_mem_power_range_iff A n hn x

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalSUnitLocalPowerMap_mem_ker_iff`. -/
theorem actual_original_sunit_localization_originalSUnitLocalPowerMap_mem_ker_iff_source
    (n : ℕ) (hn : n ≠ 0) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    x ∈ (originalSUnitLocalPowerMap K n S T hST).ker ↔
      ∀ v : T, Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom x.val ∈
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range :=
  originalSUnitLocalPowerMap_mem_ker_iff K n hn S T hST x

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]





/-- Exact original-object consumer of `originalKummerClassPairing_restrict_surjective`. -/
theorem actual_original_sunit_localization_originalKummerClassPairing_restrict_surjective_source
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)]
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) :
    Function.Surjective ((MonoidHom.restrictHom H
      (originalKummerRadicalField (Ω := Ω) n Δ)ˣ).comp
        (originalKummerClassPairing (Ω := Ω) n hn hζ Δ)) :=
  originalKummerClassPairing_restrict_surjective (Ω := Ω) n hn hζ Δ H

end

section

variable (K : Type) [Field K] [NumberField K]



variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]





/-- Exact original-object consumer of `originalSUnitKummerCharacterMap_surjective`. -/
theorem actual_original_sunit_localization_originalSUnitKummerCharacterMap_surjective_source
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)/K)) :
    Function.Surjective (originalSUnitKummerCharacterMap K Ω S n hn hζ H) :=
  originalSUnitKummerCharacterMap_surjective K Ω S n hn hζ H

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) (hp : 0 < p)
  (hroot : (primitiveRoots p K).Nonempty)



local notation "N" => OriginalSUnitKummerField K Ω S p

/-- Exact original-object consumer of `originalSUnitSelectedPowerMap_ker_eq`. -/
theorem actual_original_sunit_localization_originalSUnitSelectedPowerMap_ker_eq_source
    (H : Subgroup Gal(N/K)) (r : ℕ)
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 N))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T = Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)))
    (hST : Disjoint S T)
    (hD : ∀ i, OriginalFiniteDecompositionGroup K N (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val) :
    (originalSUnitLocalPowerMap K p S T hST).ker =
      (originalSUnitKummerCharacterMap K Ω S p hp hroot H).ker :=
  originalSUnitSelectedPowerMap_ker_eq K Ω S p hp hroot H r e w T hT hST hD

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalAdicIntegerPowerQuotient_card_away`. -/
theorem actual_original_sunit_localization_originalAdicIntegerPowerQuotient_card_away_source
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (hv : (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range) = n :=
  originalAdicIntegerPowerQuotient_card_away K v n hn ζ hζ hv

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) (hp : 0 < p)
  (hroot : (primitiveRoots p K).Nonempty)



local notation "N" => OriginalSUnitKummerField K Ω S p

include hp hroot in
/-- Exact original-object consumer of `originalSUnitSelectedPowerMap_surjective`. -/
theorem actual_original_sunit_localization_originalSUnitSelectedPowerMap_surjective_source
    (H : Subgroup Gal(N/K)) (r : ℕ)
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 N))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T = Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)))
    (hST : Disjoint S T) (hCount : T.card = r)
    (hAway : ∀ v : T, (p : 𝓞 K) ∉ v.val.asIdeal)
    (hD : ∀ i, OriginalFiniteDecompositionGroup K N (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val) :
    Function.Surjective (originalSUnitLocalPowerMap K p S T hST) :=
  originalSUnitSelectedPowerMap_surjective K Ω S p hp hroot H r e w T hT hST hCount hAway hD

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]





/-- Exact original-object consumer of `original_exists_sUnit_selected_primes`. -/
theorem actual_original_sunit_localization_original_exists_sUnit_selected_primes_source
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
        OriginalFiniteDecompositionGroup K E v = ⊥ :=
  original_exists_sUnit_selected_primes K Ω E p hDegree ζ hζ S₀ hSeed

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]





/-- Exact original-object consumer of `original_exists_sUnit_selected_support`. -/
theorem actual_original_sunit_localization_original_exists_sUnit_selected_support_source
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
        OriginalFiniteDecompositionGroup K E w = ⊥ :=
  original_exists_sUnit_selected_support K Ω E p hDegree ζ hζ S₀

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `originalSupportedIdele_sUnit_power_correction`. -/
theorem actual_original_principal_localization_originalSupportedIdele_sUnit_power_correction_source
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K n S T hST))
    (u : numberFieldSupportedIdeles K S) :
    ∃ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∀ v : T, numberFieldIdeleFiniteComponent K v.val
        (u.val / numberFieldPrincipalIdele K x.val) ∈
          (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range :=
  originalSupportedIdele_sUnit_power_correction K n S T hST hSurj u

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `originalIdeleClassNorm_surjective_of_selected_corrections`. -/
theorem actual_original_principal_localization_originalIdeleClassNorm_surjective_of_selected_corrections_source
    (n : ℕ) (hDegree : Module.finrank K L ∣ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K n S T hST))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ S →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hInf : ∀ w : InfinitePlace L, Function.Surjective (originalInfiniteLocalNorm K L w))
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Surjective (originalIdeleClassNorm K L) :=
  originalIdeleClassNorm_surjective_of_selected_corrections K L n hDegree S T hST hClasses hSurj hSplit hInf hAway

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `originalCyclicNormSurjective_power_descent`. -/
theorem actual_original_principal_localization_originalCyclicNormSurjective_power_descent_source
    (hSurj : Function.Surjective (originalIdeleClassNorm K L))
    (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K)) :
    a ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
  originalCyclicNormSurjective_power_descent K L hSurj n a β hβ

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalGeneratedKummer_finite_split`. -/
theorem actual_original_principal_localization_originalGeneratedKummer_finite_split_source
    (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hGen : IntermediateField.adjoin K {(β : L)} = ⊤)
    (hLocal : Units.map (algebraMap K ((originalFinitePrimeBelow K L w).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n).range) :
    OriginalFiniteDecompositionGroup K L w = ⊥ :=
  originalGeneratedKummer_finite_split K L w n hn ζ hζ a β hβ hGen hLocal

end

section



/-- Exact original-object consumer of `valuation_unitExponent_root_eq_one`. -/
theorem actual_original_principal_localization_valuation_unitExponent_root_eq_one_source
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (n : ℕ) (hn : v (n : K) = 1) (z : K)
    (hz : v z = 1) (hClose : v (z - 1) < 1) (hPow : z ^ n = 1) : z = 1 :=
  valuation_unitExponent_root_eq_one v n hn z hz hClose hPow

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalInertia_valuation_sub_lt_one`. -/
theorem actual_original_principal_localization_originalInertia_valuation_sub_lt_one_source
    (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K))
    (hσ : σ ∈ w.asIdeal.inertia Gal(L/K))
    (x : L) (hx : w.valuation L x ≤ 1) :
    w.valuation L (σ x - x) < 1 :=
  originalInertia_valuation_sub_lt_one K L w σ hσ x hx

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalGeneratedKummer_unramified_of_base_units`. -/
theorem actual_original_principal_localization_originalGeneratedKummer_unramified_of_base_units_source
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (hBase : Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (n : ℕ) (hn : 0 < n) (hAway : (n : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    (β : Lˣ) (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hGen : IntermediateField.adjoin K {(β : L)} = ⊤) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal :=
  originalGeneratedKummer_unramified_of_base_units K L v w hBase n hn hAway a ha β hβ hGen

end

section

variable (K : Type) [Field K]



/-- Exact original-object consumer of `originalPrimeKummerField_data`. -/
theorem actual_original_principal_localization_originalPrimeKummerField_data_source
    (p : ℕ) (hp : p.Prime) (hroot : (primitiveRoots p K).Nonempty)
    (a : Kˣ) (ha : a ∉ (powMonoidHom p : Kˣ →* Kˣ).range) :
    let L := OriginalSimpleKummerField K p a
    FiniteDimensional K L ∧ IsGalois K L ∧ IsCyclic Gal(L/K) ∧
      Module.finrank K L = p ∧
      ∃ β : Lˣ, (β : L) ^ p = algebraMap K L (a : K) ∧
        IntermediateField.adjoin K {(β : L)} = ⊤ :=
  originalPrimeKummerField_data K p hp hroot a ha

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `originalSUnitPowerLocalSubgroup_eq_powers`. -/
theorem actual_original_principal_localization_originalSUnitPowerLocalSubgroup_eq_powers_source
    (p : ℕ) (hp : p.Prime) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K p S T hST))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) :
    originalSUnitPowerLocalSubgroup K p S T =
      (powMonoidHom p : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range :=
  originalSUnitPowerLocalSubgroup_eq_powers K p hp ζ hζ S T hST hClasses hSurj hBase hAway

end

section

variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]



/-- Exact original-object consumer of `original_primeDegree_sUnit_kummer_embedding`. -/
theorem actual_original_principal_localization_original_primeDegree_sUnit_kummer_embedding_source
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Nonempty (L →ₐ[K] OriginalSUnitKummerField K Ω S p) :=
  original_primeDegree_sUnit_kummer_embedding K L Ω p hDegree ζ hζ S₀

end

section

variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `original_primeDegree_sUnit_kummer_tower_coordinates`. -/
theorem actual_original_principal_localization_original_primeDegree_sUnit_kummer_tower_coordinates_source
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (j : L →ₐ[K] OriginalSUnitKummerField K Ω S p), S₀ ⊆ S ∧
      let N := OriginalSUnitKummerField K Ω S p
      letI : Algebra L N := j.toAlgebra
      letI : IsScalarTower K L N := IsScalarTower.of_algHom j
      let f : Gal(N/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
      Function.Surjective f ∧
        1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nonempty (f.ker ≃* (Fin (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) →
          Multiplicative (ZMod p))) :=
  original_primeDegree_sUnit_kummer_tower_coordinates K L Ω p hDegree ζ hζ S₀

end

section

variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

include Ω


/-- Exact original-object consumer of `original_exists_sUnit_selected_support_actual`. -/
theorem actual_original_principal_localization_original_exists_sUnit_selected_support_actual_source
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
        OriginalFiniteDecompositionGroup K L w = ⊥ :=
  original_exists_sUnit_selected_support_actual K L Ω p hDegree ζ hζ S₀

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeDegree_normQuotient_card_roots`. -/
theorem actual_original_principal_localization_original_primeDegree_normQuotient_card_roots_source
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    Nat.card (OriginalIdeleClassNormQuotient K L) = p :=
  original_primeDegree_normQuotient_card_roots K L p hDegree ζ hζ

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_tower`. -/
theorem actual_original_cyclic_norm_originalIdeleClassBaseChangeMap_tower_source (a : OriginalNumberFieldIdeleClassGroup K) :
    originalIdeleClassBaseChangeMap E L (originalIdeleClassBaseChangeMap K E a) =
      originalIdeleClassBaseChangeMap K L a :=
  originalIdeleClassBaseChangeMap_tower K E L a

end

section

variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_restrictNormal`. -/
theorem actual_original_cyclic_norm_originalIdeleClassBaseChangeMap_restrictNormal_source
    (σ : Gal(L/K)) (a : OriginalNumberFieldIdeleClassGroup E) :
    numberFieldIdeleClassGaloisMap K L σ (originalIdeleClassBaseChangeMap E L a) =
      originalIdeleClassBaseChangeMap E L
        (numberFieldIdeleClassGaloisMap K E (AlgEquiv.restrictNormalHom E σ) a) :=
  originalIdeleClassBaseChangeMap_restrictNormal K E L σ a

end

section

variable (K E L : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]



/-- Exact original-object consumer of `numberFieldIdeleClassGaloisMap_restrictScalars`. -/
theorem actual_original_cyclic_norm_numberFieldIdeleClassGaloisMap_restrictScalars_source (σ : Gal(L/E))
    (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L (σ.restrictScalars K) a =
      numberFieldIdeleClassGaloisMap E L σ a :=
  numberFieldIdeleClassGaloisMap_restrictScalars K E L σ a

end

section

variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois E L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassNorm_tower`. -/
theorem actual_original_cyclic_norm_originalIdeleClassNorm_tower_source (a : OriginalNumberFieldIdeleClassGroup L) :
    originalIdeleClassNorm K E (originalIdeleClassNorm E L a) =
      originalIdeleClassNorm K L a :=
  originalIdeleClassNorm_tower K E L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `originalIdeleClassNorm_mem_of_coprime_pow`. -/
theorem actual_original_cyclic_norm_originalIdeleClassNorm_mem_of_coprime_pow_source
    (d : ℕ) (hd : d.Coprime (Module.finrank K L))
    (c : OriginalNumberFieldIdeleClassGroup K)
    (hc : c ^ d ∈ (originalIdeleClassNorm K L).range) :
    c ∈ (originalIdeleClassNorm K L).range :=
  originalIdeleClassNorm_mem_of_coprime_pow K L d hd c hc

end

section

variable (K L M N : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Field N] [NumberField N]
  [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L N] [Algebra M N]
  [IsScalarTower K L N] [IsScalarTower K M N]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
  [FiniteDimensional L N] [FiniteDimensional M N]
  [IsGalois K L] [IsGalois K M] [IsGalois K N] [IsGalois L N] [IsGalois M N]
  [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_coprime_baseChange`. -/
theorem actual_original_cyclic_norm_originalIdeleClassNormQuotient_card_le_coprime_baseChange_source
    [Finite (OriginalIdeleClassNormQuotient M N)]
    (hd : (Module.finrank K M).Coprime (Module.finrank K L)) :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤ Nat.card (OriginalIdeleClassNormQuotient M N) :=
  originalIdeleClassNormQuotient_card_le_coprime_baseChange K L M N hd

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeDegree_normQuotient_card`. -/
theorem actual_original_cyclic_norm_original_primeDegree_normQuotient_card_source
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p) :
    Nat.card (OriginalIdeleClassNormQuotient K L) = p :=
  original_primeDegree_normQuotient_card K L p hDegree

end

section

variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois E L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_tower`. -/
theorem actual_original_cyclic_norm_originalIdeleClassNormQuotient_card_le_tower_source
    [Finite (OriginalIdeleClassNormQuotient E L)] :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassNormQuotient E L) *
        Nat.card (OriginalIdeleClassNormQuotient K E) :=
  originalIdeleClassNormQuotient_card_le_tower K E L

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `original_cyclic_normQuotient_card`. -/
theorem actual_original_cyclic_norm_original_cyclic_normQuotient_card_source :
    Nat.card (OriginalIdeleClassNormQuotient K L) = Module.finrank K L :=
  original_cyclic_normQuotient_card K L

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `original_ideleClass_first_zero`. -/
theorem actual_original_finite_class_original_ideleClass_first_zero_source :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) :=
  original_ideleClass_first_zero K L

end

section

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (S : Subgroup Gal(L/K))



/-- Exact original-object consumer of `originalIdeleClassSubgroup_second_card`. -/
theorem actual_original_finite_class_originalIdeleClassSubgroup_second_card_source :
    Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) =
      Nat.card (groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L) 2) :=
  originalIdeleClassSubgroup_second_card S

end

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]



/-- Exact original-object consumer of `originalIdeleClassNormalInvariantInclusion_bijective`. -/
theorem actual_original_finite_class_originalIdeleClassNormalInvariantInclusion_bijective_source :
    Function.Bijective (originalIdeleClassNormalInvariantInclusion S).hom :=
  originalIdeleClassNormalInvariantInclusion_bijective S

end

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]



/-- Exact original-object consumer of `originalIdeleClass_first_zero_of_fixedField`. -/
theorem actual_original_finite_class_originalIdeleClass_first_zero_of_fixedField_source
    (hQ : Limits.IsZero (groupCohomology
      (originalIdeleClassRep K (IntermediateField.fixedField S)) 1))
    (hS : Limits.IsZero (groupCohomology
      (originalIdeleClassRep (IntermediateField.fixedField S) L) 1)) :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) :=
  originalIdeleClass_first_zero_of_fixedField S hQ hS

end

section

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)



/-- Exact original-object consumer of `finiteFirstCohomology_card_nsmul_eq_zero`. -/
theorem actual_original_finite_class_finiteFirstCohomology_card_nsmul_eq_zero_source
    (x : groupCohomology A 1) : Fintype.card G • x = 0 :=
  finiteFirstCohomology_card_nsmul_eq_zero A x

end

section



/-- Exact original-object consumer of `originalIdeleClass_pGroup_cohomology`. -/
theorem actual_original_finite_class_originalIdeleClass_pGroup_cohomology_source
    (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hG : IsPGroup p Gal(L/K)) :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
        Nat.card (groupCohomology (originalIdeleClassRep K L) 2) ∣ Nat.card Gal(L/K) :=
  originalIdeleClass_pGroup_cohomology p K L hG

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClass_finiteGalois_first_zero`. -/
theorem actual_original_finite_class_originalIdeleClass_finiteGalois_first_zero_source :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) :=
  originalIdeleClass_finiteGalois_first_zero K L

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFullPrincipalH2_injective`. -/
theorem actual_original_finite_class_originalFullPrincipalH2_injective_source :
    Function.Injective ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullPrincipalRepHom K L)) :=
  originalFullPrincipalH2_injective K L

end

section

variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassTowerQuotientInclusion_bijective`. -/
theorem actual_original_finite_class_originalIdeleClassTowerQuotientInclusion_bijective_source :
    Function.Bijective (originalIdeleClassTowerQuotientInclusion K E L).hom :=
  originalIdeleClassTowerQuotientInclusion_bijective K E L

end

section

variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassH2Inflation_injective`. -/
theorem actual_original_finite_class_originalIdeleClassH2Inflation_injective_source :
    Function.Injective (groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (originalIdeleClassTowerInclusion K E L) 2) :=
  originalIdeleClassH2Inflation_injective K E L

end

section

variable (K E L : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]



/-- Exact original-object consumer of `originalIdeleClassTowerH2Restriction_kernel_composition`. -/
theorem actual_original_finite_class_originalIdeleClassTowerH2Restriction_kernel_composition_source [IsGalois K E] :
    originalIdeleClassTowerH2Restriction K E L ≫
      groupCohomology.map (galoisTowerKernelEquiv K E L).toMonoidHom
        (originalIdeleClassTowerKernelCoefficientIso K E L).hom 2 =
      groupCohomology.map (A := originalIdeleClassRep K L)
        (B := Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype
          (originalIdeleClassRep K L))
        (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype (𝟙 _) 2 :=
  originalIdeleClassTowerH2Restriction_kernel_composition K E L

end

section

variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassH2_inflation_exists_iff_restriction_zero`. -/
theorem actual_original_finite_class_originalIdeleClassH2_inflation_exists_iff_restriction_zero_source
    (x : groupCohomology (originalIdeleClassRep K L) 2) :
    (∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E L) 2 y = x) ↔
      originalIdeleClassTowerH2Restriction K E L x = 0 :=
  originalIdeleClassH2_inflation_exists_iff_restriction_zero K E L x

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)



/-- Exact original-object consumer of `originalPi_second_cohomology_zero`. -/
theorem actual_original_local_detection_originalPi_second_cohomology_zero_source
    (hz : ∀ i, Limits.IsZero (groupCohomology (A i) 2)) :
    Limits.IsZero (groupCohomology (originalPiRep A) 2) :=
  originalPi_second_cohomology_zero A hz

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `originalTransported_second_zero_of_stabilizers`. -/
theorem actual_original_local_detection_originalTransported_second_zero_of_stabilizers_source
    (hz : ∀ ω : MulAction.orbitRel.Quotient G ι,
      Limits.IsZero (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω)) 2)) :
    Limits.IsZero (groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2) :=
  originalTransported_second_zero_of_stabilizers R G ι M T T_one T_mul hz

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalOutsideOrbitField_faithful`. -/
theorem actual_original_local_detection_originalOutsideOrbitField_faithful_source :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := originalOutsideOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K)
          (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (ω.out.val.adicCompletion L) :=
  originalOutsideOrbitField_faithful K L S hS

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalOutsideUnit_second_zero_of_unramified`. -/
theorem actual_original_local_detection_originalOutsideUnit_second_zero_of_unramified_source
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) 2) :=
  originalOutsideUnit_second_zero_of_unramified K L S hS hu

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalIdeleH2_exists_supported_lift`. -/
theorem actual_original_local_detection_originalIdeleH2_exists_supported_lift_source [FiniteDimensional K L]
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) ∧
      ∃ y : groupCohomology (originalSupportedIdeleRep K L S hS) 2,
        (groupCohomology.functor ℤ Gal(L/K) 2).map
          (originalSupportedFullIdeleInclusion K L S hS) y = x :=
  originalIdeleH2_exists_supported_lift K L x

end

section

variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (B : Rep R S)



/-- Exact original-object consumer of `originalCoinducedH2Evaluation_injective`. -/
theorem actual_original_local_detection_originalCoinducedH2Evaluation_injective_source :
    Function.Injective (groupCohomology.map S.subtype (originalCoinducedEvaluationRepHom S B) 2) :=
  originalCoinducedH2Evaluation_injective S B

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))
  [MulAction.IsPretransitive G ι] (i : ι)



/-- Exact original-object consumer of `originalTransportedStabilizerH2_injective`. -/
theorem actual_original_local_detection_originalTransportedStabilizerH2_injective_source :
    Function.Injective (groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2) :=
  originalTransportedStabilizerH2_injective R G ι M T T_one T_mul i

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `originalTransportedH2_zero_of_local`. -/
theorem actual_original_local_detection_originalTransportedH2_zero_of_local_source
    (x : groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2)
    (hx : ∀ ω : MulAction.orbitRel.Quotient G ι,
      groupCohomology.map (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype
        (originalTransportedOrbitEvaluation R G ι M T T_one T_mul ω) 2 x = 0) : x = 0 :=
  originalTransportedH2_zero_of_local R G ι M T T_one T_mul x hx

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedUnrestrictedH2_injective`. -/
theorem actual_original_local_detection_originalSupportedUnrestrictedH2_injective_source
    [NumberField K] [FiniteDimensional K L] [IsGalois K L]
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Injective ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalSupportedUnrestrictedProjection K L S hS)) :=
  originalSupportedUnrestrictedH2_injective K L S hS hu

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedFull_unrestricted_composition`. -/
theorem actual_original_local_detection_originalSupportedFull_unrestricted_composition_source :
    originalSupportedFullIdeleInclusion K L S hS ≫ originalFullUnrestrictedRepHom K L S hS =
      originalSupportedUnrestrictedProjection K L S hS :=
  originalSupportedFull_unrestricted_composition K L S hS

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalGlobalUnitH2_zero_of_local`. -/
theorem actual_original_local_detection_originalGlobalUnitH2_zero_of_local_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        originalIdeleLocalH2Map K L S hS ω
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0) :
    x = 0 :=
  originalGlobalUnitH2_zero_of_local K L x hx

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical Pointwise WithZero
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalIdeleLocalH2Map_principal_cocycle`. -/
theorem actual_original_cyclotomic_local_originalIdeleLocalH2Map_principal_cocycle_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S))
      (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)),
      originalIdeleLocalH2Map K L S hS ω
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)
          (groupCohomology.H2π _ c)) =
        groupCohomology.H2π _ (originalGlobalLocalTwoCocycle K L S hS ω c) :=
  originalIdeleLocalH2Map_principal_cocycle K L S hS

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicBaseChange_finite_galois`. -/
theorem actual_original_cyclotomic_local_originalAdicBaseChange_finite_galois_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) ∧
      IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  originalAdicBaseChange_finite_galois K L v w

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



variable [NumberField K] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicUnitCoefficientIso_hom_apply`. -/
theorem actual_original_cyclotomic_local_originalAdicUnitCoefficientIso_hom_apply_source (x : Additive (w.adicCompletion L)ˣ) :
    (originalAdicUnitCoefficientIso K L v w).hom.hom x = x :=
  originalAdicUnitCoefficientIso_hom_apply K L v w x

end

section



/-- Exact original-object consumer of `originalAdicNormValuation_hasExtension`. -/
theorem actual_original_cyclotomic_local_originalAdicNormValuation_hasExtension_source
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    letI : ValuativeRel (v.adicCompletion K) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    (ValuativeRel.valuation (v.adicCompletion K)).HasExtension
      (ValuativeRel.valuation (w.adicCompletion L)) :=
  originalAdicNormValuation_hasExtension K L v w

end

section



/-- Exact original-object consumer of `cyclotomicPrimePower_exists_residue_orders`. -/
theorem actual_original_cyclotomic_local_cyclotomicPrimePower_exists_residue_orders_source
    (q : ℕ) (hq : q.Prime) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 1 < p ∧ ¬ q ∣ p) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ p ∈ S, q ∣ orderOf (p : ZMod (q ^ (k + 1))) :=
  cyclotomicPrimePower_exists_residue_orders q hq S hS

end

section

variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω]



/-- Exact original-object consumer of `originalQUnramifiedUnion_exists_powerRoot`. -/
theorem actual_original_cyclotomic_local_originalQUnramifiedUnion_exists_powerRoot_source [IsSepClosed Ω]
    (a : 𝓞 ℚ) (q r : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ ζ : originalUnramifiedGaloisUnion (Ω := Ω) a, IsPrimitiveRoot ζ (q ^ r) :=
  originalQUnramifiedUnion_exists_powerRoot a q r hqa

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



variable [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicBaseChange_finrank_eq_decomposition_card`. -/
theorem actual_original_cyclotomic_local_originalAdicBaseChange_finrank_eq_decomposition_card_source
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (OriginalFiniteDecompositionGroup K L w) :=
  originalAdicBaseChange_finrank_eq_decomposition_card K L v w

end

section

variable (q k : ℕ) [hq : Fact q.Prime]
  (L : Type) [Field L] [NumberField L] [hL : IsCyclotomicExtension {q ^ (k + 1)} ℚ L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `cyclotomicPrimePower_original_completion_degree_dvd`. -/
theorem actual_original_cyclotomic_local_cyclotomicPrimePower_original_completion_degree_dvd_source
    (hk : 1 ≤ k) (p : ℕ) [Fact p.Prime]
    (hlarge : p ≠ q → p ^ (q - 1) - 1 < q ^ (k + 1))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let v := originalFinitePrimeBelow ℚ L w
    letI := originalFinitePrimeBelow_liesOver ℚ L w
    letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap ℚ L v w).toAlgebra
    q ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L) :=
  cyclotomicPrimePower_original_completion_degree_dvd q k L hk p hlarge w

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalCyclotomic_exists_localDegree_stage`. -/
theorem actual_original_cyclotomic_local_originalCyclotomic_exists_localDegree_stage_source
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∀ (p : ℕ), p ∈ S → ∀ (w : HeightOneSpectrum (𝓞 F)),
        w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        let v := originalFinitePrimeBelow ℚ F w
        letI := originalFinitePrimeBelow_liesOver ℚ F w
        letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion F) :=
          (originalAdicBaseChangeMap ℚ F v w).toAlgebra
        q ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion F) :=
  originalCyclotomic_exists_localDegree_stage a q hq hq2 hqa S hS

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical Pointwise WithZero
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))



/-- Exact original-object consumer of `originalGlobalAdicTwoCocycle_apply`. -/
theorem actual_original_cyclic_killing_originalGlobalAdicTwoCocycle_apply_source
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (g h : OriginalFiniteDecompositionGroup K L w) :
    originalGlobalAdicTwoCocycle K L w c (g, h) =
      Additive.ofMul (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
        (c (g.val, h.val)).toMul) :=
  originalGlobalAdicTwoCocycle_apply K L w c g h

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `originalTransportedH2_zero_of_points`. -/
theorem actual_original_cyclic_killing_originalTransportedH2_zero_of_points_source
    (x : groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2)
    (hx : ∀ i : ι, groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2 x = 0) : x = 0 :=
  originalTransportedH2_zero_of_points R G ι M T T_one T_mul x hx

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalGlobalUnitH2_zero_of_points`. -/
theorem actual_original_cyclic_killing_originalGlobalUnitH2_zero_of_points_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ p : SUnitLogPlace L S,
        originalIdelePointH2Map K L S hS p
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0) :
    x = 0 :=
  originalGlobalUnitH2_zero_of_points K L x hx

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedAdicH2_comparison`. -/
theorem actual_original_cyclic_killing_originalSupportedAdicH2_comparison_source
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∈ S})
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    letI := sUnitLogPlaceAction K L S hS
    groupCohomology.map (originalSupportedFiniteStabilizerHom K L S hS w)
      (originalSupportedAdicCoefficientHom K L S hS w) 2 (originalGlobalAdicH2 K L w.val x) =
        originalIdelePointH2Map K L S hS (Sum.inr w)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) :=
  originalSupportedAdicH2_comparison K L S hS w x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (w : InfinitePlace L)



/-- Exact original-object consumer of `originalGlobalInfiniteTwoCocycle_apply`. -/
theorem actual_original_cyclic_killing_originalGlobalInfiniteTwoCocycle_apply_source
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (g h : OriginalInfiniteDecompositionGroup K L w) :
    originalGlobalInfiniteTwoCocycle K L w c (g, h) =
      Additive.ofMul (Units.map (algebraMap L (w.Completion)).toMonoidHom
        (c (g.val, h.val)).toMul) :=
  originalGlobalInfiniteTwoCocycle_apply K L w c g h

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (w : InfinitePlace L)



variable [FiniteDimensional K L]



/-- Exact original-object consumer of `originalGlobalInfiniteH2_eq_zero_of_odd_torsion`. -/
theorem actual_original_cyclic_killing_originalGlobalInfiniteH2_eq_zero_of_odd_torsion_source
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0) :
    originalGlobalInfiniteH2 K L w x = 0 :=
  originalGlobalInfiniteH2_eq_zero_of_odd_torsion K L w q hq hq2 x hx

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedInfiniteH2_comparison`. -/
theorem actual_original_cyclic_killing_originalSupportedInfiniteH2_comparison_source
    (w : InfinitePlace L)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    letI := sUnitLogPlaceAction K L S hS
    groupCohomology.map (originalSupportedInfiniteStabilizerHom K L S hS w)
      (originalSupportedInfiniteCoefficientHom K L S hS w) 2 (originalGlobalInfiniteH2 K L w x) =
        originalIdelePointH2Map K L S hS (Sum.inl w)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) :=
  originalSupportedInfiniteH2_comparison K L S hS w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalGlobalUnitH2_zero_of_finite_at_odd_prime`. -/
theorem actual_original_cyclic_killing_originalGlobalUnitH2_zero_of_finite_at_odd_prime_source
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hxq : q • x = 0)
    (hx : ∀ w : HeightOneSpectrum (𝓞 L), originalGlobalAdicH2 K L w x = 0) : x = 0 :=
  originalGlobalUnitH2_zero_of_finite_at_odd_prime K L q hq hq2 x hxq hx

end

section



/-- Exact original-object consumer of `localFieldContinuousH2_baseChange_zero_of_degree_dvd`. -/
theorem actual_original_cyclic_killing_localFieldContinuousH2_baseChange_zero_of_degree_dvd_source
    (K E Ω : Type) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [FiniteDimensional K E] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) (hx : q • x = 0) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    continuousGaloisUnitBaseChangeH2 K E Ω Ω x = 0 :=
  localFieldContinuousH2_baseChange_zero_of_degree_dvd K E Ω q hq x hx

end

section



/-- Exact original-object consumer of `originalFiniteGalois_continuousH2Inflation_injective`. -/
theorem actual_original_cyclic_killing_originalFiniteGalois_continuousH2Inflation_injective_source
    (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] :
    Function.Injective (continuousGaloisUnitBaseChangeH2 K K L Ω) :=
  originalFiniteGalois_continuousH2Inflation_injective K L Ω

end

section



/-- Exact original-object consumer of `localFieldFiniteH2_baseChange_zero_of_degree_dvd`. -/
theorem actual_original_cyclic_killing_localFieldFiniteH2_baseChange_zero_of_degree_dvd_source
    (K E L M : Type) [Field K] [CharZero K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K L] [IsGalois E M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) (hx : q • x = 0) :
    finiteGaloisUnitBaseChangeH2 K E L M x = 0 :=
  localFieldFiniteH2_baseChange_zero_of_degree_dvd K E L M q hq x hx

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalGlobalCompletionH2_decomposition`. -/
theorem actual_original_cyclic_killing_originalGlobalCompletionH2_decomposition_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    (originalAdicUnitCohomologyIso K L v w 2).hom
      (originalGlobalCompletionH2 K L v w x) = originalGlobalAdicH2 K L w x :=
  originalGlobalCompletionH2_decomposition K L v w x

end

section



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalAdicBaseChange_isScalarTower`. -/
theorem actual_original_cyclic_killing_originalAdicBaseChange_isScalarTower_source
    (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
      (originalAdicBaseChangeMap K E v u).toAlgebra
    letI : Algebra (u.adicCompletion E) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap E L u w).toAlgebra
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    IsScalarTower (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) :=
  originalAdicBaseChange_isScalarTower K E L v u w

end

section

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalCompletionGaloisRestriction_baseChange`. -/
theorem actual_original_cyclic_killing_originalCompletionGaloisRestriction_baseChange_source :
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  ∀ σ : Gal(t.adicCompletion M/u.adicCompletion E),
    originalCompletionGaloisRestriction K L v w
      (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M) σ) =
      galoisBaseChangeRestriction K E L M (originalCompletionGaloisRestriction E M u t σ) :=
  originalCompletionGaloisRestriction_baseChange K E L M v u w t

end

section

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalGlobalCompletionH2_baseChange`. -/
theorem actual_original_cyclic_killing_originalGlobalCompletionH2_baseChange_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  groupCohomology.map
      (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M))
      (galoisUnitBaseChangeInclusion (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M)) 2
      (originalGlobalCompletionH2 K L v w x) =
    originalGlobalCompletionH2 E M u t
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) :=
  originalGlobalCompletionH2_baseChange K E L M v u w t x

end

section



/-- Exact original-object consumer of `localFieldAlgebraicH2_baseChange_zero_of_degree_dvd`. -/
theorem actual_original_cyclic_killing_localFieldAlgebraicH2_baseChange_zero_of_degree_dvd_source
    (K E L M : Type) [Field K] [CharZero K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K L] [IsGalois E M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 :=
  localFieldAlgebraicH2_baseChange_zero_of_degree_dvd K E L M q hq x hx

end

section

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
include w in
/-- Exact original-object consumer of `originalGlobalAdicH2_baseChange_zero_of_degree_dvd`. -/
theorem actual_original_cyclic_killing_originalGlobalAdicH2_baseChange_zero_of_degree_dvd_source
    (q : ℕ) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (hq : letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
      (originalAdicBaseChangeMap K E v u).toAlgebra
      q ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    originalGlobalAdicH2 E M t
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) = 0 :=
  originalGlobalAdicH2_baseChange_zero_of_degree_dvd K E L M v u w t q x hx hq

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



variable (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalFullIdeleAdicH2_supported_outside_zero`. -/
theorem actual_original_cyclic_killing_originalFullIdeleAdicH2_supported_outside_zero_source
    [NumberField K] [FiniteDimensional K L] [IsGalois K L]
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
    (x : groupCohomology (originalSupportedIdeleRep K L S hS) 2) :
    originalFullIdeleAdicH2 K L w.val
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSupportedFullIdeleInclusion K L S hS) x) = 0 :=
  originalFullIdeleAdicH2_supported_outside_zero K L S hS hu w x

end

section



/-- Exact original-object consumer of `originalGlobalAdicH2_exists_finite_support`. -/
theorem actual_original_cyclic_killing_originalGlobalAdicH2_exists_finite_support_source
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0 :=
  originalGlobalAdicH2_exists_finite_support K L x

end

section

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
include v u in
/-- Exact original-object consumer of `originalGlobalAdicH2_baseChange_zero_of_local_zero`. -/
theorem actual_original_cyclic_killing_originalGlobalAdicH2_baseChange_zero_of_local_zero_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalAdicH2 K L w x = 0) :
    originalGlobalAdicH2 E M t
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) = 0 :=
  originalGlobalAdicH2_baseChange_zero_of_local_zero K E L M v u w t x hx

end

section



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalGlobalUnitH2_baseChange_zero_of_finite_degrees`. -/
theorem actual_original_cyclic_killing_originalGlobalUnitH2_baseChange_zero_of_finite_degrees_source
    (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois E M]
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0)
    (hdegree : ∀ t : HeightOneSpectrum (𝓞 M), originalFinitePrimeBelow L M t ∈ S →
      let u := originalFinitePrimeBelow E M t
      let v := originalFinitePrimeBelow K E u
      letI := originalFinitePrimeBelow_liesOver K E u
      letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
        (originalAdicBaseChangeMap K E v u).toAlgebra
      q ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 :=
  originalGlobalUnitH2_baseChange_zero_of_finite_degrees K E L M q hq hq2 x hx S hS hdegree

end

section



/-- Exact original-object consumer of `originalIntegerPrimeBelow_tower`. -/
theorem actual_original_cyclic_killing_originalIntegerPrimeBelow_tower_source
    (L M : Type) [Field L] [NumberField L] [Field M] [NumberField M] [Algebra L M]
    (t : HeightOneSpectrum (𝓞 M)) :
    originalIntegerPrimeBelow L (originalFinitePrimeBelow L M t) = originalIntegerPrimeBelow M t :=
  originalIntegerPrimeBelow_tower L M t

end

section



attribute [-instance] UniformSpace.Completion.instSMul
attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
/-- Exact original-object consumer of `originalCyclotomic_exists_globalH2_killing_stage`. -/
theorem actual_original_cyclic_killing_originalCyclotomic_exists_globalH2_killing_stage_source
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra F M := iF.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
      groupCohomology.map (galoisBaseChangeRestriction ℚ F L M)
        (galoisUnitBaseChangeInclusion ℚ F L M) 2 x = 0 :=
  originalCyclotomic_exists_globalH2_killing_stage L a q hq hq2 hqa x hx

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical BigOperators
section



/-- Exact original-object consumer of `originalFiniteH2_exists_torsion_descent_of_baseChange_zero`. -/
theorem actual_original_cyclic_descent_originalFiniteH2_exists_torsion_descent_of_baseChange_zero_source
    (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K M] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois K M]
    (q : ℕ) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (hkill : groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0) :
    ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2, q • y = 0 ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E) (finiteGaloisUnitTowerInclusion K E M) 2 y =
        groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion K L M) 2 x :=
  originalFiniteH2_exists_torsion_descent_of_baseChange_zero K E L M q x hx hkill

end
section



attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
/-- Exact original-object consumer of `originalCyclotomic_exists_globalH2_descent_stage`. -/
theorem actual_original_cyclic_descent_originalCyclotomic_exists_globalH2_descent_stage_source
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra F M := iF.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
      M ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
        groupCohomology.map (AlgEquiv.restrictNormalHom F) (finiteGaloisUnitTowerInclusion ℚ F M) 2 y =
          groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion ℚ L M) 2 x :=
  originalCyclotomic_exists_globalH2_descent_stage L a q hq hq2 hqa hL x hx

end
section



/-- Exact original-object consumer of `cyclicTwoCocycle_eq_of_generator_column`. -/
theorem actual_original_cyclic_descent_cyclicTwoCocycle_eq_of_generator_column_source
    {R G : Type} [CommRing R] [Group G] [Finite G] (A : Rep R G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (c d : groupCohomology.cocycles₂ A) (h : ∀ x, c (x, g) = d (x, g)) : c = d :=
  cyclicTwoCocycle_eq_of_generator_column A g hg c d h

end
section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n))
  (g : G) (hχ : χ g = Multiplicative.ofAdd 1)



include hχ in
/-- Exact original-object consumer of `cyclicCarryPartialCochain_column`. -/
theorem actual_original_cyclic_descent_cyclicCarryPartialCochain_column_source (hn : 1 < n)
    (c : groupCohomology.cocycles₂ A) (x : G) :
    c (x, g) + groupCohomology.d₁₂ A (cyclicCarryPartialCochain A χ g c) (x, g) =
      zmodAdditionCarry (χ x).toAdd (χ g).toAdd •
        representationCyclicTwoCochainPeriodSum A g n c :=
  cyclicCarryPartialCochain_column A χ g hχ hn c x

end
section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n))
  (g : G) (hχ : χ g = Multiplicative.ofAdd 1)



include hχ in
/-- Exact original-object consumer of `cyclicTwoCocycleH2_eq_carry_of_period`. -/
theorem actual_original_cyclic_descent_cyclicTwoCocycleH2_eq_carry_of_period_source (hn : 1 < n)
    (c : groupCohomology.cocycles₂ A) :
    groupCohomology.H2π A c =
      groupCohomology.H2π A
        (representationCarryCocycle A χ.toMonoidHom
          (representationCyclicTwoCochainPeriodSum A g n c)
          (cyclicCarryPeriod_invariant A χ g hχ c)) :=
  cyclicTwoCocycleH2_eq_carry_of_period A χ g hχ hn c

end
section



/-- Exact original-object consumer of `originalCyclicGaloisH2_exists_characterCarry`. -/
theorem actual_original_cyclic_descent_originalCyclicGaloisH2_exists_characterCarry_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {n : ℕ} [NeZero n] (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (hn : 1 < n)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ u : Kˣ, groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
      (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ.toMonoidHom
        (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u)) = x :=
  originalCyclicGaloisH2_exists_characterCarry K L χ hn x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul
/-- Exact original-object consumer of `originalGlobalCompletionH2_characterCarry`. -/
theorem actual_original_cyclic_descent_originalGlobalCompletionH2_characterCarry_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalGlobalCompletionH2 K L v w
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
          (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u))) =
      groupCohomology.H2π
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (representationCarryCocycle
          (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
          (χ.comp (originalCompletionGaloisRestriction K L v w))
          (galoisUnitsBaseCoefficient
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))
          (galoisUnitsBaseCoefficient_fixed
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))) :=
  originalGlobalCompletionH2_characterCarry K L v w χ u

end

section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (F : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(F/K)]
  [Algebra L F] [IsScalarTower K L F] [IsScalarTower L F Ω]



/-- Exact original-object consumer of `localFieldOriginalCarryInvariant`. -/
theorem actual_original_cyclic_descent_localFieldOriginalCarryInvariant_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldContinuousH2InvariantEquiv K Ω
      (continuousGaloisUnitBaseChangeH2 K K L Ω
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
      rationalCyclicInvariant n
        (χ (galoisBaseChangeRestriction K K L F
          (localFieldFiniteCyclicReciprocity K Ω F (Additive.ofMul u)).toMul)).toAdd :=
  localFieldOriginalCarryInvariant K L Ω F χ u

end

section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteGaloisImage_isCyclic`. -/
theorem actual_original_cyclic_descent_originalFiniteGaloisImage_isCyclic_source [IsCyclic Gal(L/K)] :
    IsCyclic Gal(originalFiniteGaloisImage K L Ω/K) :=
  originalFiniteGaloisImage_isCyclic K L Ω

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField



variable (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]



/-- Exact original-object consumer of `originalGlobalCompletionInvariant_characterCarry`. -/
theorem actual_original_cyclic_descent_originalGlobalCompletionInvariant_characterCarry_source [IsCyclic Gal(L/K)]
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    let F := originalFiniteGaloisImage (v.adicCompletion K) (w.adicCompletion L) Ω
    letI : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
      originalCompletionGalois_isCyclic K L v w
    letI : IsCyclic Gal(F/v.adicCompletion K) :=
      originalFiniteGaloisImage_isCyclic (v.adicCompletion K) (w.adicCompletion L) Ω
    letI := originalFiniteGaloisImageAlgebra (v.adicCompletion K) (w.adicCompletion L) Ω
    letI := originalFiniteGaloisImage_baseTower (v.adicCompletion K) (w.adicCompletion L) Ω
    originalGlobalCompletionInvariant K L v w Ω
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
          (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u))) =
      rationalCyclicInvariant n
        (χ (originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
            (w.adicCompletion L) F
            (localFieldFiniteCyclicReciprocity (v.adicCompletion K) Ω F
              (Additive.ofMul (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))).toMul))).toAdd :=
  originalGlobalCompletionInvariant_characterCarry K L v w Ω χ u

end

end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical BigOperators
section


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitH2_exists_torsion_finite_stage`. -/
theorem actual_arithmetic_cyclic_stage_continuousGaloisUnitH2_exists_torsion_finite_stage_source
    (q : ℕ) (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) (hx : q • x = 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F), q • y = 0 ∧
        galoisUnitFiniteStageH2Inflation F y = x :=
  continuousGaloisUnitH2_exists_torsion_finite_stage q x hx

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology arithmeticKummerStageDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



/-- Exact original-object consumer of `rationalArithmeticKummerUnitH2_exists_torsion_finite_stage`. -/
theorem actual_arithmetic_cyclic_stage_rationalArithmeticKummerUnitH2_exists_torsion_finite_stage_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := ℚ) (Ω := F), q • y = 0 ∧
        galoisUnitFiniteStageH2Inflation (K := ℚ) (Ω := rationalUnramifiedExtension a) F y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) :=
  rationalArithmeticKummerUnitH2_exists_torsion_finite_stage a q hqa x

end

section

attribute [local instance] originalFiniteGaloisStageLiftAlgebra originalFiniteGaloisStageLiftUpperAlgebra originalStageLiftFiniteTopology originalStageLiftFiniteDiscrete

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (U : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K U)



variable [IsGalois K U]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)]



/-- Exact original-object consumer of `originalFiniteGaloisStageLift_inflation`. -/
theorem actual_arithmetic_cyclic_stage_originalFiniteGaloisStageLift_inflation_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := F)) :
    let E := originalFiniteGaloisStageLift U F
    letI := originalFiniteGaloisStageLift_baseTower U F
    letI := originalFiniteGaloisStageLift_upperBaseTower U F
    letI := originalFiniteGaloisStageLift_upperTower U F
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K K E U
      (finiteGaloisUnitBaseChangeH2 K K F E x) = galoisUnitFiniteStageH2Inflation F x :=
  originalFiniteGaloisStageLift_inflation U F x

end

section


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]



/-- Exact original-object consumer of `originalFiniteH2_continuousInflation_comparison`. -/
theorem actual_arithmetic_cyclic_stage_originalFiniteH2_continuousInflation_comparison_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := M))
      (finiteGaloisUnitBaseChangeH2 K K L M x) =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2
        (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) :=
  originalFiniteH2_continuousInflation_comparison K L M x

end

section




/-- Exact original-object consumer of `originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq`. -/
theorem actual_arithmetic_cyclic_stage_originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq_source
    (K E L M U : Type) [Field K] [Field E] [Field L] [Field M] [Field U]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra K U]
    [Algebra E M] [Algebra L M] [Algebra M U] [Algebra E U] [Algebra L U]
    [IsScalarTower K E M] [IsScalarTower K L M] [IsScalarTower K M U]
    [IsScalarTower K E U] [IsScalarTower K L U]
    [IsScalarTower E M U] [IsScalarTower L M U]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois K U]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2)
    (y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (h : groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (finiteGaloisUnitTowerInclusion K E M) 2 x =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y) :
    continuousGaloisUnitBaseChangeH2 K K E U
      ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K E)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := E))).symm x) =
      continuousGaloisUnitBaseChangeH2 K K L U
        ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).symm y) :=
  originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq K E L M U x y h

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)



variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]



/-- Exact original-object consumer of `originalCyclotomic_exists_continuousH2_descent_stage`. -/
theorem actual_arithmetic_cyclic_stage_originalCyclotomic_exists_continuousH2_descent_stage_source
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
    letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ L) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ L) := ⟨rfl⟩
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            continuousGaloisUnitBaseChangeH2 ℚ ℚ L U
              ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ L)
                (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := L))).symm x) :=
  originalCyclotomic_exists_continuousH2_descent_stage a L q hq hq2 hqa hL x hx

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]



/-- Exact original-object consumer of `originalUnramifiedUnitH2_exists_cyclic_stage`. -/
theorem actual_arithmetic_cyclic_stage_originalUnramifiedUnitH2_exists_cyclic_stage_source
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hx : q • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) = x :=
  originalUnramifiedUnitH2_exists_cyclic_stage a q hq hq2 hqa x hx

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology arithmeticKummerStageDiscrete
attribute [local instance] arithmeticCyclicAmbientAlgebra

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



/-- Exact original-object consumer of `rationalArithmeticKummerUnitH2_exists_cyclic_stage`. -/
theorem actual_arithmetic_cyclic_stage_rationalArithmeticKummerUnitH2_exists_cyclic_stage_source (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    let U := rationalUnramifiedExtension a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            rationalArithmeticKummerH2Inclusion a q
              (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) :=
  rationalArithmeticKummerUnitH2_exists_cyclic_stage a q hqa hq2 x

end


section

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra
  AlgebraicClosure.instSMulOfIsScalarTower

attribute [local instance] rationalPrimeLocalField_charZero

attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul


attribute [local instance] arithmeticUnitBaseChangePrimeModule arithmeticUnitBaseChangeAlgebra arithmeticUnitBaseChangeSMul arithmeticUnitBaseChangeTower

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



/-- Exact original-object consumer of `rationalArithmeticUnitH2Restriction_eq_baseChange`. -/
theorem actual_arithmetic_carry_rationalArithmeticUnitH2Restriction_eq_baseChange_source
    (x : ContinuousRepresentationH2 (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitAction_continuous a)) :
    rationalArithmeticUnitH2Restriction a p hp x =
      continuousGaloisUnitBaseChangeH2 ℚ (rationalPrimeLocalField p hp)
        (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) x :=
  rationalArithmeticUnitH2Restriction_eq_baseChange a p hp x

end

section

attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat


attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra




/-- Exact original-object consumer of `rationalArithmeticFiniteLocalStage_isCyclic`. -/
theorem actual_arithmetic_carry_rationalArithmeticFiniteLocalStage_isCyclic_source
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime) :
    IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) :=
  rationalArithmeticFiniteLocalStage_isCyclic a F p hp

end

section


variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `originalFiniteGaloisImage_inflation`. -/
theorem actual_arithmetic_carry_originalFiniteGaloisImage_inflation_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    let E := originalFiniteGaloisImage K L Ω
    letI := originalFiniteGaloisImageAlgebra K L Ω
    letI := originalFiniteGaloisImage_baseTower K L Ω
    letI := originalFiniteGaloisImage_ambientTower K L Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
    galoisUnitFiniteStageH2Inflation E (finiteGaloisUnitBaseChangeH2 K K L E x) =
      continuousGaloisUnitBaseChangeH2 K K L Ω x :=
  originalFiniteGaloisImage_inflation K L Ω x

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete arithmeticCyclicAmbientAlgebra


variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



/-- Exact original-object consumer of `rationalArithmeticKummerUnitH2_exists_cyclic_finite_stage`. -/
theorem actual_arithmetic_carry_rationalArithmeticKummerUnitH2_exists_cyclic_finite_stage_source (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) :=
  rationalArithmeticKummerUnitH2_exists_cyclic_finite_stage a q hqa hq2 x

end

section


variable (K E L Ω : Type) [Field K] [Field E] [Field L] [Field Ω]
  [Algebra K E] [Algebra K L] [Algebra E Ω] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K E Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois E Ω] [IsSepClosed Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (F : FiniteGaloisIntermediateField E Ω) [IsCyclic Gal(F/E)]
  [Algebra K F] [IsScalarTower K E F]
  [Algebra L F] [IsScalarTower K L F] [IsScalarTower L F Ω]



/-- Exact original-object consumer of `localFieldBaseChangedCarryInvariant`. -/
theorem actual_arithmetic_carry_localFieldBaseChangedCarryInvariant_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldContinuousH2InvariantEquiv E Ω
      (continuousGaloisUnitBaseChangeH2 K E L Ω
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
      rationalCyclicInvariant n
        (χ (galoisBaseChangeRestriction K E L F
          (localFieldFiniteCyclicReciprocity E Ω F
            (Additive.ofMul (Units.map (algebraMap K E).toMonoidHom u))).toMul)).toAdd :=
  localFieldBaseChangedCarryInvariant K E L Ω F χ u

end

section

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower

attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  arithmeticUnitBaseChangePrimeModule arithmeticUnitBaseChangeAlgebra
  arithmeticUnitBaseChangeSMul arithmeticUnitBaseChangeTower
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


attribute [local instance] arithmeticFiniteCarryGlobalAlgebra arithmeticFiniteCarryClosureAlgebra arithmeticFiniteCarryStageAlgebra arithmeticFiniteCarryUnionSMul arithmeticFiniteCarryClosureSMul arithmeticFiniteCarryStageSMul arithmeticFiniteCarryLocalBaseTower arithmeticFiniteCarryClosureTower arithmeticFiniteCarryStageTower arithmeticFiniteCarryUnionTower arithmeticFiniteCarryLocalTower arithmeticFiniteCarryLocalCyclic arithmeticFiniteCarryTopology arithmeticFiniteCarryDiscrete

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))



variable [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



/-- Exact original-object consumer of `rationalArithmeticFiniteCarryInvariant`. -/
theorem actual_arithmetic_carry_rationalArithmeticFiniteCarryInvariant_source
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (u : ℚˣ) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (rationalArithmeticUnitH2Restriction a p hp
        (galoisUnitFiniteStageH2Inflation F
          (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)))) =
      rationalCyclicInvariant n
        (χ (rationalArithmeticFiniteLocalRestriction a F p hp
          (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
            (rationalArithmeticFiniteLocalStage a F p hp)
            (Additive.ofMul (Units.map (algebraMap ℚ (rationalPrimeLocalField p hp)).toMonoidHom u))).toMul)).toAdd :=
  rationalArithmeticFiniteCarryInvariant a F p hp χ u

end

section


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]



/-- Exact original-object consumer of `originalCyclicContinuousH2_exists_characterCarry`. -/
theorem actual_arithmetic_carry_originalCyclicContinuousH2_exists_characterCarry_source
    (hn : 1 < Nat.card Gal(L/K)) (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    let n := Nat.card Gal(L/K)
    letI : NeZero n := ⟨by omega⟩
    ∃ χ : Gal(L/K) ≃* Multiplicative (ZMod n), ∃ u : Kˣ,
      Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = x :=
  originalCyclicContinuousH2_exists_characterCarry K L hn x

end

section




/-- Exact original-object consumer of `oddPrimeCyclotomic_galois_card_gt_one`. -/
theorem actual_arithmetic_carry_oddPrimeCyclotomic_galois_card_gt_one_source
    (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (q k : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    [IsCyclotomicExtension {q ^ (k + 1)} ℚ L] : 1 < Nat.card Gal(L/ℚ) :=
  oddPrimeCyclotomic_galois_card_gt_one L q k hq hq2

end

section

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete arithmeticCyclicAmbientAlgebra


variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



/-- Exact original-object consumer of `rationalArithmeticKummerUnitH2_exists_cyclic_carry`. -/
theorem actual_arithmetic_carry_rationalArithmeticKummerUnitH2_exists_cyclic_carry_source (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      letI : Algebra ℚ E := E.toIntermediateField.algebra'
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) ∧
        ∃ (n : ℕ) (hn : 1 < n),
          letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
          ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod n), ∃ u : ℚˣ,
            Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = y :=
  rationalArithmeticKummerUnitH2_exists_cyclic_carry a q hqa hq2 x

end


end
noncomputable section
open scoped BigOperators
section


variable {G : Type} [Group G] (S : Subgroup G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))



/-- Exact original-object consumer of `cosetCarryCorrection_identity`. -/
theorem actual_carry_norm_cosetCarryCorrection_identity_source (g h : G) (q : G ⧸ S) :
    (zmodAdditionCarry (χ g).toAdd (χ h).toAdd : ℤ) -
      zmodAdditionCarry (χ (cosetTransition S g (h • q))).toAdd
        (χ (cosetTransition S h q)).toAdd =
      cosetCarryCorrection S χ h q - cosetCarryCorrection S χ (g * h) q +
        cosetCarryCorrection S χ g (h • q) :=
  cosetCarryCorrection_identity S χ g h q

end

section


variable {G : Type} [Group G] (S : Subgroup G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (A : Rep ℤ G) (a : A) (ha : ∀ s : S, A.ρ s a = a)



variable [Fintype (G ⧸ S)]



include ha in
/-- Exact original-object consumer of `cosetCarryProjectionHomotopy_differential`. -/
theorem actual_carry_norm_cosetCarryProjectionHomotopy_differential_source :
    groupCohomology.d₁₂ A (cosetCarryProjectionHomotopy S χ A a) =
      (fun z => zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd •
        (∑ q : G ⧸ S, A.ρ q.out a)) -
      cosetTraceTwo A S (fun z => zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd • a) :=
  cosetCarryProjectionHomotopy_differential S χ A a ha

end

section

attribute [local instance 1100] Rep.hV2

attribute [-instance] AddCommGroup.toIntModule


attribute [local instance] carryCoefficientContinuousSMul

variable {G : Type} [Group G] [TopologicalSpace G]
  {n : ℕ} [NeZero n]



variable [IsTopologicalGroup G] (S : Subgroup G) (hS : IsOpen (S : Set G))
  (χ : G →ₜ* Multiplicative (ZMod n))



variable (A : Rep ℤ G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (a : A) [Fintype (G ⧸ S)]



/-- Exact original-object consumer of `continuousRepresentationCarryCocycle_corestriction`. -/
theorem actual_carry_norm_continuousRepresentationCarryCocycle_corestriction_source
    (ha : ∀ s : S, A.ρ s a = a) :
    continuousRepresentationH2Corestriction A hA S hS
      (Submodule.Quotient.mk (continuousRepresentationCarryCocycle
        (restrictedCoefficientRep A S.subtype)
        ⟨χ.toMonoidHom.comp S.subtype, χ.continuous.comp continuous_subtype_val⟩ a ha)) =
      (Submodule.Quotient.mk (continuousRepresentationCarryCocycle A χ
        (∑ q : G ⧸ S, A.ρ q.out a) (cosetInvariantCoefficient_sum_fixed S A a ha)) :
        ContinuousRepresentationH2 A hA) :=
  continuousRepresentationCarryCocycle_corestriction S hS χ A hA a ha

end

section


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω)



variable [FiniteDimensional K E] [IsAlgClosed Ω]
  [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)]



/-- Exact original-object consumer of `originalGaloisCosetProduct_eq_norm`. -/
theorem actual_carry_norm_originalGaloisCosetProduct_eq_norm_source (x : E) :
    (∏ q : Gal(Ω/K) ⧸ E.fixingSubgroup, q.out (x : Ω)) =
      algebraMap K Ω (Algebra.norm K x) :=
  originalGaloisCosetProduct_eq_norm K Ω E x

end

section


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (E : IntermediateField K Ω)



variable [IsGalois K Ω] [FiniteDimensional K E] [IsAlgClosed Ω]
  [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)]



/-- Exact original-object consumer of `galoisIntermediateUnitCoefficient_coset_norm`. -/
theorem actual_carry_norm_galoisIntermediateUnitCoefficient_coset_norm_source (u : Eˣ) :
    (∑ q : Gal(Ω/K) ⧸ E.fixingSubgroup,
      (Rep.ofAlgebraAutOnUnits K Ω).ρ q.out (galoisIntermediateUnitCoefficient K Ω E u)) =
      galoisUnitsBaseCoefficient (L := Ω) (Units.map (Algebra.norm K (S := E)) u) :=
  galoisIntermediateUnitCoefficient_coset_norm K Ω E u

end

section

attribute [local instance] carryCoefficientContinuousSMul


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] {n : ℕ} [NeZero n]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))



variable [FiniteDimensional K E] [IsAlgClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `continuousGaloisCharacterCarryCocycle_corestriction_norm`. -/
theorem actual_carry_norm_continuousGaloisCharacterCarryCocycle_corestriction_norm_source (u : Eˣ) :
    galoisUnitContinuousCorestriction K Ω E
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n
        (galoisFiniteBaseCharacterRestriction K Ω E χ) u)) =
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ
        (Units.map (Algebra.norm K (S := E)) u)) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :=
  continuousGaloisCharacterCarryCocycle_corestriction_norm K Ω E χ u

end

section


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `localFieldContinuousCarryInvariant_norm`. -/
theorem actual_carry_norm_localFieldContinuousCarryInvariant_norm_source
    {n : ℕ} [NeZero n] (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) (u : Eˣ) :
    localFieldContinuousH2InvariantEquiv K Ω
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ
        (Units.map (Algebra.norm K (S := E)) u))) =
      localFieldContinuousH2InvariantEquiv E Ω
        (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n
          (galoisFiniteBaseCharacterRestriction K Ω E χ) u)) :=
  localFieldContinuousCarryInvariant_norm K Ω E χ u

end

section


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]



omit [IsGalois E Ω] in
/-- Exact original-object consumer of `finiteGaloisCharacterInflation_baseRestriction`. -/
theorem actual_carry_norm_finiteGaloisCharacterInflation_baseRestriction_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) :
    galoisFiniteBaseCharacterRestriction K Ω E (finiteGaloisCharacterInflation L χ) =
      finiteGaloisCharacterInflation M (χ.comp (galoisBaseChangeRestriction K E L M)) :=
  finiteGaloisCharacterInflation_baseRestriction K Ω E L M χ

end

section

attribute [local instance] IsCyclic.commGroup


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [IsCyclic Gal(L/K)] [IsCyclic Gal(M/E)]
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]



/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_norm`. -/
theorem actual_carry_norm_localFieldFiniteCyclicReciprocity_norm_source (u : Eˣ) :
    galoisBaseChangeRestriction K E L M
      (localFieldFiniteCyclicReciprocity E Ω M (Additive.ofMul u)).toMul =
      (localFieldFiniteCyclicReciprocity K Ω L
        (Additive.ofMul (Units.map (Algebra.norm K (S := E)) u))).toMul :=
  localFieldFiniteCyclicReciprocity_norm K Ω E L M u

end


end

noncomputable section
open scoped BigOperators NumberField ValuativeRel
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
section


variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]



/-- Exact original-object consumer of `primeToResidue_unit_roots_eq`. -/
theorem actual_cyclotomic_unramified_primeToResidue_unit_roots_eq_source {n : ℕ}
    (hn : (n : IsLocalRing.ResidueField R) ≠ 0) (x y : Rˣ)
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : IsLocalRing.residue R (x : R) = IsLocalRing.residue R (y : R)) : x = y :=
  primeToResidue_unit_roots_eq hn x y hx hy hxy

end

section


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_unit_root`. -/
theorem actual_cyclotomic_unramified_localFieldArithmeticFrobenius_unit_root_source {n : ℕ}
    (hn : (n : 𝓀[L]) ≠ 0) (u : 𝒪[L]ˣ) (hu : u ^ n = 1) :
    localFieldArithmeticFrobenius K L (algebraMap 𝒪[L] L (u : 𝒪[L])) =
      algebraMap 𝒪[L] L (u : 𝒪[L]) ^ Nat.card 𝓀[K] :=
  localFieldArithmeticFrobenius_unit_root K L hn u hu

end

section


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]



/-- Exact original-object consumer of `localFieldRoot_exists_integer_unit`. -/
theorem actual_cyclotomic_unramified_localFieldRoot_exists_integer_unit_source {n : ℕ} [NeZero n] (ζ : K) (hζ : ζ ^ n = 1) :
    ∃ u : 𝒪[K]ˣ, u ^ n = 1 ∧ algebraMap 𝒪[K] K (u : 𝒪[K]) = ζ :=
  localFieldRoot_exists_integer_unit K ζ hζ

end

section


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_field_root`. -/
theorem actual_cyclotomic_unramified_localFieldArithmeticFrobenius_field_root_source {n : ℕ}
    (hn : (n : 𝓀[L]) ≠ 0) (ζ : L) (hζ : ζ ^ n = 1) :
    localFieldArithmeticFrobenius K L ζ = ζ ^ Nat.card 𝓀[K] :=
  localFieldArithmeticFrobenius_field_root K L hn ζ hζ

end

section

attribute [local instance 1100] Ring.toIntAlgebra




/-- Exact original-object consumer of `rationalPrimeLocalField_residue_card`. -/
theorem actual_cyclotomic_unramified_rationalPrimeLocalField_residue_card_source (p : ℕ) (hp : p.Prime) :
    Nat.card 𝓀[rationalPrimeLocalField p hp] = p :=
  rationalPrimeLocalField_residue_card p hp

end

section


variable (p : ℕ) (hp : p.Prime) (L : Type) [Field L]
  [Algebra (rationalPrimeLocalField p hp) L] [IsGalois (rationalPrimeLocalField p hp) L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp] 𝒪[L]]



/-- Exact original-object consumer of `rationalPrimeArithmeticFrobenius_field_root`. -/
theorem actual_cyclotomic_unramified_rationalPrimeArithmeticFrobenius_field_root_source {n : ℕ}
    (hpn : ¬p ∣ n) (ζ : L) (hζ : ζ ^ n = 1) :
    localFieldArithmeticFrobenius (rationalPrimeLocalField p hp) L ζ = ζ ^ p :=
  rationalPrimeArithmeticFrobenius_field_root p hp L hpn ζ hζ

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]



/-- Exact original-object consumer of `arithmeticCyclotomicFiniteLocalStage_integer_unramified`. -/
theorem actual_cyclotomic_unramified_arithmeticCyclotomicFiniteLocalStage_integer_unramified_source
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n) :
    Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
      𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
  arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]



/-- Exact original-object consumer of `arithmeticCyclotomicFiniteLocal_frobenius_root`. -/
theorem actual_cyclotomic_unramified_arithmeticCyclotomicFiniteLocal_frobenius_root_source
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    (ζ : F) (hζ : ζ ^ n = 1) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldArithmeticFrobenius (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp)) ζ = ζ ^ p :=
  arithmeticCyclotomicFiniteLocal_frobenius_root a F p hp n hpn ζ hζ

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]



/-- Exact original-object consumer of `arithmeticCyclotomicFiniteLocal_frobenius_character`. -/
theorem actual_cyclotomic_unramified_arithmeticCyclotomicFiniteLocal_frobenius_character_source
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldArithmeticFrobenius (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp))) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) :=
  arithmeticCyclotomicFiniteLocal_frobenius_character a F p hp n hpn hζ

end

section

attribute [local instance] IsCyclic.commGroup


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]



/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_frobenius_image`. -/
theorem actual_cyclotomic_unramified_localFieldFiniteCyclicReciprocity_frobenius_image_source
    {H : Type*} [Group H] (χ : Gal(E/K) →* H) (u : Kˣ) :
    letI : IsCyclic Gal(E/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
    χ (localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u)).toMul =
      χ (localFieldArithmeticFrobenius K E) ^ localFieldUnitOrder K (Additive.ofMul u) :=
  localFieldFiniteCyclicReciprocity_frobenius_image K Ω E χ u

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]




variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



/-- Exact original-object consumer of `arithmeticCyclotomicFiniteLocal_reciprocity_character`. -/
theorem actual_cyclotomic_unramified_arithmeticCyclotomicFiniteLocal_reciprocity_character_source
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (u : (rationalPrimeLocalField p hp)ˣ) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    letI : IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp /
        rationalPrimeLocalField p hp) :=
      (unramifiedLocalFieldResidueGaloisEquiv (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp)).isCyclic.mpr inferInstance
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) (rationalArithmeticFiniteLocalStage a F p hp)
        (Additive.ofMul u)).toMul) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u) :=
  arithmeticCyclotomicFiniteLocal_reciprocity_character a F p hp n hpn hζ u

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra


attribute [local instance] arithmeticCyclotomicLocalCyclic

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



/-- Exact original-object consumer of `arithmeticCyclotomic_reciprocity_away_conductor`. -/
theorem actual_cyclotomic_unramified_arithmeticCyclotomic_reciprocity_away_conductor_source
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (u : (rationalPrimeLocalField p hp)ˣ) :
    letI := arithmeticCyclotomicLocalCyclic a F p hp
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) (rationalArithmeticFiniteLocalStage a F p hp)
        (Additive.ofMul u)).toMul) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u) :=
  arithmeticCyclotomic_reciprocity_away_conductor a F p hp n hpn hζ u

end

section

attribute [local instance 1100] Ring.toIntAlgebra




/-- Exact original-object consumer of `rationalPrimeLocalField_prime_order`. -/
theorem actual_cyclotomic_unramified_rationalPrimeLocalField_prime_order_source (p : ℕ) (hp : p.Prime) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (Units.mk0 (p : rationalPrimeLocalField p hp)
        (by
          intro h
          exact (rationalPrimeValuationInteger_irreducible_prime p hp).ne_zero
            (Subtype.ext h)))) = 1 :=
  rationalPrimeLocalField_prime_order p hp

end

section




/-- Exact original-object consumer of `rationalPrimeLocalField_rational_order`. -/
theorem actual_cyclotomic_unramified_rationalPrimeLocalField_rational_order_source (p : ℕ) (hp : p.Prime) (u : ℚˣ) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (Units.map (algebraMap ℚ (rationalPrimeLocalField p hp)).toMonoidHom u)) =
        -WithZero.log ((rationalPrimePlace p hp).valuation ℚ u.val) :=
  rationalPrimeLocalField_rational_order p hp u

end

section




/-- Exact original-object consumer of `rational_abs_eq_of_finite_valuations`. -/
theorem actual_cyclotomic_unramified_rational_abs_eq_of_finite_valuations_source (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ x = v.valuation ℚ y) : |x| = |y| :=
  rational_abs_eq_of_finite_valuations x y hx hy hv

end

section




/-- Exact original-object consumer of `rationalPositivePrimeProduct_eq_abs`. -/
theorem actual_cyclotomic_unramified_rationalPositivePrimeProduct_eq_abs_source (S : Finset (HeightOneSpectrum ℤ))
    (x : ℚ) (hx : x ≠ 0) (hS : ∀ v ∉ S, v.valuation ℚ x = 1) :
    (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
      (-log (v.valuation ℚ x))) = |x| :=
  rationalPositivePrimeProduct_eq_abs S x hx hS

end

section




/-- Exact original-object consumer of `rationalPositivePrimeProduct_exists_support`. -/
theorem actual_cyclotomic_unramified_rationalPositivePrimeProduct_exists_support_source (u : ℚˣ) :
    ∃ S : Finset (HeightOneSpectrum ℤ),
      (∀ v ∉ S, v.valuation ℚ u.val = 1) ∧
      (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))
          (Additive.ofMul (Units.map (algebraMap ℚ
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom u))) = |u.val| :=
  rationalPositivePrimeProduct_exists_support u

end


end
noncomputable section
open scoped BigOperators NumberField ValuativeRel
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
section

attribute [local instance] IsCyclic.commGroup


attribute [local instance] normedUniformizerRelativeCyclic

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [IsCyclic Gal(L/K)]
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]



variable [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]



/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_norm_uniformizer`. -/
theorem actual_semilinear_uniformizer_localFieldFiniteCyclicReciprocity_norm_uniformizer_source
    (θ : 𝒪[E]) (hθ : Irreducible θ) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (Units.map (Algebra.norm K (S := E))
        (Units.mk0 (algebraMap 𝒪[E] E θ) (by intro h; exact hθ.ne_zero (Subtype.ext h)))))).toMul =
      galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) :=
  localFieldFiniteCyclicReciprocity_norm_uniformizer K Ω E L M θ hθ

end

section




/-- Exact original-object consumer of `primeWitt_exists_frobenius_unit_rotation`. -/
theorem actual_semilinear_uniformizer_primeWitt_exists_frobenius_unit_rotation_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    ∃ ε : (WittVector p (AlgebraicClosure (ZMod p)))ˣ,
      WittVector.frobenius (ε : WittVector p (AlgebraicClosure (ZMod p))) =
        (ε : WittVector p (AlgebraicClosure (ZMod p))) * u :=
  primeWitt_exists_frobenius_unit_rotation p u

end

section

attribute [local instance 1100] Ring.toIntAlgebra


attribute [local instance] rationalPrimeWittPrime



/-- Exact original-object consumer of `rationalPrimeIntegerWittMap_exists_rotation`. -/
theorem actual_semilinear_uniformizer_rationalPrimeIntegerWittMap_exists_rotation_source (p : ℕ) (hp : p.Prime)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    ∃ ε : (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))ˣ,
      WittVector.frobenius ε.val = ε.val * rationalPrimeIntegerWittMap p hp u.val :=
  rationalPrimeIntegerWittMap_exists_rotation p hp u

end

section


variable {R : Type*} [CommRing R]



/-- Exact original-object consumer of `adicComplete_existsUnique_affine_fixedPoint`. -/
theorem actual_semilinear_uniformizer_adicComplete_existsUnique_affine_fixedPoint_source
    (I : Ideal R) [IsAdicComplete I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) :
    ∃! x : R, x = b + T x :=
  adicComplete_existsUnique_affine_fixedPoint I T hT b

end

section




/-- Exact original-object consumer of `primeWitt_existsUnique_higher_coefficient`. -/
theorem actual_semilinear_uniformizer_primeWitt_existsUnique_higher_coefficient_source
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (m : ℕ) (hm : 2 ≤ m)
    (b : WittVector p (AlgebraicClosure (ZMod p))) :
    ∃! a : WittVector p (AlgebraicClosure (ZMod p)),
      a =
        b +
          (↑(u⁻¹) :
              WittVector p (AlgebraicClosure (ZMod p))) *
            (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
            WittVector.frobenius a :=
  primeWitt_existsUnique_higher_coefficient p u m hm b

end

section

attribute [local instance] rationalPrimeWittPrime




/-- Exact original-object consumer of `rationalPrimeIntegerWittMap_existsUnique_higher_coefficient`. -/
theorem actual_semilinear_uniformizer_rationalPrimeIntegerWittMap_existsUnique_higher_coefficient_source
    (p : ℕ) (hp : p.Prime) (u : 𝒪[rationalPrimeLocalField p hp]ˣ)
    (m : ℕ) (hm : 2 ≤ m)
    (b : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) :
    ∃! a : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))),
      a = b + rationalPrimeIntegerWittMap p hp u.inv *
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp) :
          WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
            (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) ^
          (m - 1) * WittVector.frobenius a :=
  rationalPrimeIntegerWittMap_existsUnique_higher_coefficient p hp u m hm b

end

section


variable (p : ℕ) [Fact p.Prime]



/-- Exact original-object consumer of `primeWittChangedSeries_residue`. -/
theorem actual_semilinear_uniformizer_primeWittChangedSeries_residue_source (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.map WittVector.constantCoeff (primeWittChangedSeries p u) =
      (PowerSeries.X : PowerSeries (AlgebraicClosure (ZMod p))) ^ p :=
  primeWittChangedSeries_residue p u

end

section




/-- Exact original-object consumer of `primeWittSemilinearDefect_coeff_mem_span_p`. -/
theorem actual_semilinear_uniformizer_primeWittSemilinearDefect_coeff_mem_span_p_source
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    PowerSeries.coeff m (primeWittSemilinearDefect p u H) ∈
      Ideal.span ({(p : WittVector p (AlgebraicClosure (ZMod p)))} : Set _) :=
  primeWittSemilinearDefect_coeff_mem_span_p p u H hH m

end

section




/-- Exact original-object consumer of `powerSeries_coeff_subst_eq_of_coeff_eq_le`. -/
theorem actual_semilinear_uniformizer_powerSeries_coeff_subst_eq_of_coeff_eq_le_source
    {R : Type*} [CommRing R] {f g b c : PowerSeries R}
    (hb : PowerSeries.constantCoeff b = 0) (hc : PowerSeries.constantCoeff c = 0)
    (m : ℕ) (hfg : ∀ d ≤ m, PowerSeries.coeff d f = PowerSeries.coeff d g)
    (hbc : ∀ d ≤ m, PowerSeries.coeff d b = PowerSeries.coeff d c) :
    PowerSeries.coeff m (PowerSeries.subst b f) =
      PowerSeries.coeff m (PowerSeries.subst c g) :=
  powerSeries_coeff_subst_eq_of_coeff_eq_le hb hc m hfg hbc

end

section




/-- Exact original-object consumer of `primeWittCorrectionCoefficient_kills_defect`. -/
theorem actual_semilinear_uniformizer_primeWittCorrectionCoefficient_kills_defect_source
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    PowerSeries.coeff m
        (primeWittSemilinearDefect p u
          (H + PowerSeries.monomial m
            (primeWittCorrectionCoefficient
              p u H hH m hm))) = 0 :=
  primeWittCorrectionCoefficient_kills_defect p u H hH m hm

end

section




/-- Exact original-object consumer of `primeWittIntertwiner_functionalEquation`. -/
theorem actual_semilinear_uniformizer_primeWittIntertwiner_functionalEquation_source
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.subst (primeWittIntertwiner p u) (primeWittChangedSeries p u) =
      PowerSeries.subst (primeWittMultiplicativeSeries p)
        (PowerSeries.map WittVector.frobenius (primeWittIntertwiner p u)) :=
  primeWittIntertwiner_functionalEquation p u

end

section


variable (p : ℕ) [Fact p.Prime]
  (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)



/-- Exact original-object consumer of `primeWittIntertwiner_linear_isUnit`. -/
theorem actual_semilinear_uniformizer_primeWittIntertwiner_linear_isUnit_source :
    IsUnit (PowerSeries.coeff 1 (primeWittIntertwiner p u)) :=
  primeWittIntertwiner_linear_isUnit p u

end

section




/-- Exact original-object consumer of `powerSeries_coeff_one_subst`. -/
theorem actual_semilinear_uniformizer_powerSeries_coeff_one_subst_source {R : Type*} [CommRing R]
    {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g :=
  powerSeries_coeff_one_subst hf hg

end

section


variable (p : ℕ) [Fact p.Prime]



/-- Exact original-object consumer of `primeWittNaturalSeries_commutes`. -/
theorem actual_semilinear_uniformizer_primeWittNaturalSeries_commutes_source (a : ℕ) :
    PowerSeries.subst (primeWittNaturalSeries p a) (primeWittMultiplicativeSeries p) =
      PowerSeries.subst (primeWittMultiplicativeSeries p) (primeWittNaturalSeries p a) :=
  primeWittNaturalSeries_commutes p a

end

section




/-- Exact original-object consumer of `primeWittIntertwiner_frobenius_nat`. -/
theorem actual_semilinear_uniformizer_primeWittIntertwiner_frobenius_nat_source
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    PowerSeries.map WittVector.frobenius
        (primeWittIntertwiner p u) =
      PowerSeries.subst
        (primeWittNaturalSeries p a)
        (primeWittIntertwiner p u) :=
  primeWittIntertwiner_frobenius_nat p u a hu

end

section

attribute [local instance] rationalPrimeWittPrime




/-- Exact original-object consumer of `rationalPrimeNaturalWittIntertwiner_exists`. -/
theorem actual_semilinear_uniformizer_rationalPrimeNaturalWittIntertwiner_exists_source
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let W := WittVector q (AlgebraicClosure (ZMod q))
    ∃ u : 𝒪[rationalPrimeLocalField p hp]ˣ,
      u.val = a ∧ ∃ H : PowerSeries W,
        PowerSeries.constantCoeff H = 0 ∧ IsUnit (PowerSeries.coeff 1 H) ∧
        PowerSeries.subst H
            (primeWittChangedSeries q (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u)) =
          PowerSeries.subst (primeWittMultiplicativeSeries q) (PowerSeries.map WittVector.frobenius H) ∧
        PowerSeries.map WittVector.frobenius H = PowerSeries.subst (primeWittNaturalSeries q a) H ∧
        ∃ J : PowerSeries W, PowerSeries.constantCoeff J = 0 ∧
          PowerSeries.subst J H = PowerSeries.X ∧ PowerSeries.subst H J = PowerSeries.X :=
  rationalPrimeNaturalWittIntertwiner_exists p hp a ha

end

section

attribute [local instance 1100] Ring.toIntAlgebra

attribute [local instance] rationalPrimeWittPrime




/-- Exact original-object consumer of `rationalPrimeIntegerWittMap_frobenius_fixed_iff`. -/
theorem actual_semilinear_uniformizer_rationalPrimeIntegerWittMap_frobenius_fixed_iff_source
    (p : ℕ) (hp : p.Prime)
    (x : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) :
    WittVector.frobenius x = x ↔
      ∃ z : 𝒪[rationalPrimeLocalField p hp], rationalPrimeIntegerWittMap p hp z = x :=
  rationalPrimeIntegerWittMap_frobenius_fixed_iff p hp x

end

section

attribute [local instance] rationalPrimeWittPrime




/-- Exact original-object consumer of `rationalPrimeWittFieldFrobenius_base`. -/
theorem actual_semilinear_uniformizer_rationalPrimeWittFieldFrobenius_base_source (p : ℕ) (hp : p.Prime)
    (x : rationalPrimeLocalField p hp) :
    rationalPrimeWittFieldFrobenius p hp (rationalPrimeWittFieldMap p hp x) =
      rationalPrimeWittFieldMap p hp x :=
  rationalPrimeWittFieldFrobenius_base p hp x

end

section

attribute [local instance] rationalPrimeWittPrime




/-- Exact original-object consumer of `rationalPrimeWittFieldFrobenius_fixed_iff`. -/
theorem actual_semilinear_uniformizer_rationalPrimeWittFieldFrobenius_fixed_iff_source
    (p : ℕ) (hp : p.Prime) (x : rationalPrimeWittField p hp) :
    rationalPrimeWittFieldFrobenius p hp x = x ↔
      ∃ z : rationalPrimeLocalField p hp, rationalPrimeWittFieldMap p hp z = x :=
  rationalPrimeWittFieldFrobenius_fixed_iff p hp x

end


end
noncomputable section
open Polynomial
open scoped BigOperators NumberField ValuativeRel PowerSeries.WithPiTopology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
section




/-- Exact original-object consumer of `primePowerShiftedCyclotomic_isEisensteinAt`. -/
theorem actual_cyclotomic_changed_norm_primePowerShiftedCyclotomic_isEisensteinAt_source
    (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime]
    (hpR : Prime (p : R)) (n : ℕ) :
    (primePowerShiftedCyclotomic R p n).IsEisensteinAt (Ideal.span {(p : R)}) :=
  primePowerShiftedCyclotomic_isEisensteinAt R p hpR n

end

section


attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFinite

variable (p : ℕ) [Fact p.Prime] (n : ℕ)



/-- Exact original-object consumer of `wittCyclotomicRoot_pow_mem_prime`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicRoot_pow_mem_prime_source :
    (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) ^
        ((p - 1) * p ^ n) ∈
      (Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
        (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n)) :=
  wittCyclotomicRoot_pow_mem_prime p n

end

section




/-- Exact original-object consumer of `adic_hasEval_of_pow_mem`. -/
theorem actual_cyclotomic_changed_norm_adic_hasEval_of_pow_mem_source {R : Type*} [CommRing R] [WithIdeal R]
    (x : R) (d : ℕ) (hx : x ^ d ∈ (WithIdeal.i : Ideal R)) :
    PowerSeries.HasEval x :=
  adic_hasEval_of_pow_mem x d hx

end

section


attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space



/-- Exact original-object consumer of `wittCyclotomicPowerSeriesEval_subst`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicPowerSeriesEval_subst_source (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x)
    (a f : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (ha : PowerSeries.HasSubst a) :
    wittCyclotomicPowerSeriesEval p n x hx (PowerSeries.subst a f) =
      wittCyclotomicPowerSeriesEval p n (wittCyclotomicPowerSeriesEval p n x hx a)
        (wittCyclotomicPowerSeriesEval_hasEval p n x hx a ha) f :=
  wittCyclotomicPowerSeriesEval_subst p n x hx a f ha

end

section

attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space




/-- Exact original-object consumer of `wittCyclotomicIntertwiner_eval_injective`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicIntertwiner_eval_injective_source
    (p : ℕ) [Fact p.Prime] (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) (x y : wittCyclotomicRootAlgebra p n)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u) =
      wittCyclotomicPowerSeriesEval p n y hy (primeWittIntertwiner p u)) : x = y :=
  wittCyclotomicIntertwiner_eval_injective p u n x y hx hy hxy

end

section

attribute [local instance] wittCyclotomicRootDomain




/-- Exact original-object consumer of `wittCyclotomicPrimitiveRoot_isPrimitive`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicPrimitiveRoot_isPrimitive_source (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsPrimitiveRoot (wittCyclotomicPrimitiveRoot p n) (p ^ (n + 1)) :=
  wittCyclotomicPrimitiveRoot_isPrimitive p n

end

section




/-- Exact original-object consumer of `primeWittIntertwiner_natural_functional`. -/
theorem actual_cyclotomic_changed_norm_primeWittIntertwiner_natural_functional_source
    (p : ℕ) [Fact p.Prime] (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (a : ℕ) (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    PowerSeries.subst (primeWittIntertwiner p u) (primeWittChangedSeries p u) =
      PowerSeries.subst (primeWittNaturalSeries p (p * a)) (primeWittIntertwiner p u) :=
  primeWittIntertwiner_natural_functional p u a hu

end

section


variable {R : Type*} [CommRing R]



/-- Exact original-object consumer of `primeChangedPolynomialIterate_succ_factor`. -/
theorem actual_cyclotomic_changed_norm_primeChangedPolynomialIterate_succ_factor_source
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    primeChangedPolynomialIterate p π (n + 1) =
      primeChangedPolynomialIterate p π n *
        primeChangedPrimitivePolynomial p π n :=
  primeChangedPolynomialIterate_succ_factor p π n

end

section

attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space




/-- Exact original-object consumer of `wittCyclotomicIntertwiner_eval_natural_step`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicIntertwiner_eval_natural_step_source (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    let y := wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u)
    algebraMap _ (wittCyclotomicRootAlgebra p n) (u.val * p) * y + y ^ p =
      wittCyclotomicPowerSeriesEval p n ((1 + x) ^ (p * a) - 1)
        (wittCyclotomicNaturalPoint_hasEval p n (p * a) x hx) (primeWittIntertwiner p u) :=
  wittCyclotomicIntertwiner_eval_natural_step p n u a hu x hx

end

section


variable {R : Type*} [CommRing R]



/-- Exact original-object consumer of `primeChangedPrimitivePolynomial_irreducible`. -/
theorem actual_cyclotomic_changed_norm_primeChangedPrimitivePolynomial_irreducible_source [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (hπ : Prime π) (n : ℕ) :
    Irreducible (primeChangedPrimitivePolynomial p π n) :=
  primeChangedPrimitivePolynomial_irreducible p π hπ n

end

section

attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space wittCyclotomicRootDomain




/-- Exact original-object consumer of `wittCyclotomicChangedPoint_iterate_zero`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicChangedPoint_iterate_zero_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    (primeChangedPolynomialIterate p (u.val * p) (n + 1)).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n) = 0 :=
  wittCyclotomicChangedPoint_iterate_zero p u n a hu

end

section

attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space wittCyclotomicRootDomain




/-- Exact original-object consumer of `wittCyclotomicChangedPoint_primitivePolynomial`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicChangedPoint_primitivePolynomial_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    (primeChangedPrimitivePolynomial p (u.val * p) n).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n) = 0 :=
  wittCyclotomicChangedPoint_primitivePolynomial p u n a hu ha

end

section

attribute [local instance] wittCyclotomicRootDomain


attribute [local instance] wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower



/-- Exact original-object consumer of `wittCyclotomicField_finrank_and_finite`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicField_finrank_and_finite_source (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicField p n) = (p - 1) * p ^ n ∧
    FiniteDimensional (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicField p n) :=
  wittCyclotomicField_finrank_and_finite p n

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite




/-- Exact original-object consumer of `wittCyclotomicChangedFieldPoint_adjoin`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicChangedFieldPoint_adjoin_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    IntermediateField.adjoin (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      ({wittCyclotomicChangedFieldPoint p u n} : Set (wittCyclotomicField p n)) = ⊤ :=
  wittCyclotomicChangedFieldPoint_adjoin p u n a hu ha

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite




/-- Exact original-object consumer of `wittCyclotomicChangedFieldPoint_norm_neg`. -/
theorem actual_cyclotomic_changed_norm_wittCyclotomicChangedFieldPoint_norm_neg_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    Algebra.norm (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (-wittCyclotomicChangedFieldPoint p u n) =
      algebraMap _ (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (u.val * p) :=
  wittCyclotomicChangedFieldPoint_norm_neg p u n a hu ha

end

section

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  wittCyclotomicFieldFinite




/-- Exact original-object consumer of `rationalPrimeNaturalWittNorm_exists`. -/
theorem actual_cyclotomic_changed_norm_rationalPrimeNaturalWittNorm_exists_source (p : ℕ) (hp : p.Prime) (n a : ℕ) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∃ u : 𝒪[rationalPrimeLocalField p hp]ˣ, u.val = a ∧
      let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
      IntermediateField.adjoin (rationalPrimeWittField p hp)
        ({wittCyclotomicChangedFieldPoint q v n} : Set (wittCyclotomicField q n)) = ⊤ ∧
      Algebra.norm (rationalPrimeWittField p hp) (-wittCyclotomicChangedFieldPoint q v n) =
        algebraMap _ (rationalPrimeWittField p hp)
          (rationalPrimeIntegerWittMap p hp (u.val * p)) :=
  rationalPrimeNaturalWittNorm_exists p hp n a ha

end


end
noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators NumberField ValuativeRel PowerSeries.WithPiTopology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
section

attribute [local instance] wittCyclotomicRootDomain




/-- Exact original-object consumer of `wittCyclotomicPowerHom_comp_eq_id`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicPowerHom_comp_eq_id_source (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    (wittCyclotomicPowerHom p n a ha).comp (wittCyclotomicPowerHom p n b hb) = AlgHom.id _ _ :=
  wittCyclotomicPowerHom_comp_eq_id p n a b ha hb hab

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space




/-- Exact original-object consumer of `wittCyclotomicRootHom_continuous`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicRootHom_continuous_source (p : ℕ) [Fact p.Prime] (n : ℕ)
    (f : wittCyclotomicRootAlgebra p n →+* wittCyclotomicRootAlgebra p n) : Continuous f :=
  wittCyclotomicRootHom_continuous p n f

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicCoefficientUniformSpace
  wittCyclotomicRootWithIdeal wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space




/-- Exact original-object consumer of `wittCyclotomicDiagonalFrobenius_changedPoint`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicDiagonalFrobenius_changedPoint_source (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    wittCyclotomicDiagonalFrobenius p n a b ha hb hab (wittCyclotomicChangedPoint p u n) =
      wittCyclotomicChangedPoint p u n :=
  wittCyclotomicDiagonalFrobenius_changedPoint p n a b ha hb hab u hu

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite




/-- Exact original-object consumer of `wittCyclotomicDiagonalFieldFrobenius_changedPoint`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicDiagonalFieldFrobenius_changedPoint_source (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab (wittCyclotomicChangedFieldPoint p u n) =
      wittCyclotomicChangedFieldPoint p u n :=
  wittCyclotomicDiagonalFieldFrobenius_changedPoint p n a b ha hb hab u hu

end

section


variable {R S : Type*} [CommRing R] [CommRing S]



/-- Exact original-object consumer of `primeChangedPrimitivePolynomial_map`. -/
theorem actual_diagonal_auxiliary_dvr_primeChangedPrimitivePolynomial_map_source (f : R →+* S) (p : ℕ) (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).map f = primeChangedPrimitivePolynomial p (f π) n :=
  primeChangedPrimitivePolynomial_map f p π n

end

section

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower


attribute [local instance] rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower



/-- Exact original-object consumer of `rationalPrimeWittCyclotomicMap_injective`. -/
theorem actual_diagonal_auxiliary_dvr_rationalPrimeWittCyclotomicMap_injective_source (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Function.Injective (algebraMap (rationalPrimeLocalField p hp)
      (wittCyclotomicField (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)) :=
  rationalPrimeWittCyclotomicMap_injective p hp n

end

section

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower




/-- Exact original-object consumer of `rationalPrimeChangedFieldPoint_minpoly`. -/
theorem actual_diagonal_auxiliary_dvr_rationalPrimeChangedFieldPoint_minpoly_source (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
    minpoly (rationalPrimeLocalField p hp) (wittCyclotomicChangedFieldPoint q v n) =
      primeChangedPrimitivePolynomial q ((a : rationalPrimeLocalField p hp) * q) n :=
  rationalPrimeChangedFieldPoint_minpoly p hp n a u hu ha

end

section




/-- Exact original-object consumer of `powerBasis_norm_neg_gen`. -/
theorem actual_diagonal_auxiliary_dvr_powerBasis_norm_neg_gen_source {K E : Type*} [Field K] [Field E] [Algebra K E]
    (b : PowerBasis K E) :
    Algebra.norm K (-b.gen) = (minpoly K b.gen).coeff 0 :=
  powerBasis_norm_neg_gen b

end

section

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower


attribute [local instance] rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction



/-- Exact original-object consumer of `rationalPrimeChangedAuxiliaryPoint_norm_neg`. -/
theorem actual_diagonal_auxiliary_dvr_rationalPrimeChangedAuxiliaryPoint_norm_neg_source (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    Algebra.norm (rationalPrimeLocalField p hp) (-rationalPrimeChangedAuxiliaryPoint p hp n u) =
      (a : rationalPrimeLocalField p hp) * p :=
  rationalPrimeChangedAuxiliaryPoint_norm_neg p hp n a u hu ha

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower




/-- Exact original-object consumer of `wittCyclotomicDiagonalFieldFrobenius_coefficient`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicDiagonalFieldFrobenius_coefficient_source (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (x : FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) :
    wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab
      (algebraMap _ (wittCyclotomicField p n) x) =
    algebraMap _ (wittCyclotomicField p n)
      ((IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p))) :
        FractionRing (WittVector p (AlgebraicClosure (ZMod p))) ≃+*
          FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) x) :=
  wittCyclotomicDiagonalFieldFrobenius_coefficient p n a b ha hb hab x

end

section

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction




/-- Exact original-object consumer of `rationalPrimeDiagonalFrobenius_auxiliary`. -/
theorem actual_diagonal_auxiliary_dvr_rationalPrimeDiagonalFrobenius_auxiliary_source (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∀ (ha : a.Coprime (q ^ (n + 1))) (hb : b.Coprime (q ^ (n + 1)))
      (hab : a * b ≡ 1 [MOD q ^ (n + 1)]) (x : rationalPrimeChangedAuxiliaryField p hp n u),
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab x.val = x.val :=
  rationalPrimeDiagonalFrobenius_auxiliary p hp n a b u hu

end

section




/-- Exact original-object consumer of `prime_constant_adjoinRoot_root_maximal`. -/
theorem actual_diagonal_auxiliary_dvr_prime_constant_adjoinRoot_root_maximal_source {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R[X]) (π : R) (hπ : Prime π) (h0 : f.coeff 0 = π) :
    (Ideal.span {AdjoinRoot.root f} : Ideal (AdjoinRoot f)).IsMaximal :=
  prime_constant_adjoinRoot_root_maximal f π hπ h0

end

section




/-- Exact original-object consumer of `monic_eisenstein_adjoinRoot_dvr`. -/
theorem actual_diagonal_auxiliary_dvr_monic_eisenstein_adjoinRoot_dvr_source {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R[X]) [IsDomain (AdjoinRoot f)]
    (hf : f.Monic) (hd : 0 < f.natDegree) (π : R) (hπ : Prime π)
    (h0 : f.coeff 0 = π) (he : f.IsEisensteinAt (Ideal.span {π})) :
    IsDiscreteValuationRing (AdjoinRoot f) :=
  monic_eisenstein_adjoinRoot_dvr f hf hd π hπ h0 he

end

section

attribute [local instance] wittCyclotomicRootDomain


attribute [local instance] wittCyclotomicRootDVR



/-- Exact original-object consumer of `wittCyclotomicRoot_irreducible`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicRoot_irreducible_source (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) :=
  wittCyclotomicRoot_irreducible p n

end

section

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootDVR
  wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space




/-- Exact original-object consumer of `wittCyclotomicChangedPoint_irreducible`. -/
theorem actual_diagonal_auxiliary_dvr_wittCyclotomicChangedPoint_irreducible_source (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    Irreducible (wittCyclotomicChangedPoint p u n) :=
  wittCyclotomicChangedPoint_irreducible p u n

end

section


attribute [local instance] rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR



/-- Exact original-object consumer of `rationalPrimeChangedIntegralRoot_irreducible`. -/
theorem actual_diagonal_auxiliary_dvr_rationalPrimeChangedIntegralRoot_irreducible_source (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    Irreducible (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u)) :=
  rationalPrimeChangedIntegralRoot_irreducible p hp n u

end


end
noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators NumberField ValuativeRel PowerSeries.WithPiTopology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
section

attribute [local instance] rationalPrimeChangedIntegralRootDomain
  rationalPrimeChangedIntegralRootDVR rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction


attribute [local instance] rationalPrimeChangedAuxiliaryIntegerAlgebra rationalPrimeChangedAuxiliaryIntegerTower



/-- Exact original-object consumer of `rationalPrimeChangedAuxiliaryField_isFractionRing`. -/
theorem actual_changed_auxiliary_local_rationalPrimeChangedAuxiliaryField_isFractionRing_source
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    letI : Algebra (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u))
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
        (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
    IsFractionRing (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u))
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
  rationalPrimeChangedAuxiliaryField_isFractionRing p hp n a u hu ha

end

section

attribute [local instance] rationalPrimeChangedIntegralRootDomain
  rationalPrimeChangedIntegralRootDVR rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction




/-- Exact original-object consumer of `rationalPrimeChangedAuxiliary_exists_local_structure`. -/
theorem actual_changed_auxiliary_local_rationalPrimeChangedAuxiliary_exists_local_structure_source
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    ∃ (_ : FiniteDimensional K E) (_ : ValuativeRel E)
      (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)),
      True :=
  rationalPrimeChangedAuxiliary_exists_local_structure p hp n a u hu ha

end

section

attribute [local instance] rationalPrimeChangedIntegralRootDomain
  rationalPrimeChangedIntegralRootDVR rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction




/-- Exact original-object consumer of `rationalPrimeChangedAuxiliary_exists_integer_uniformizer`. -/
theorem actual_changed_auxiliary_local_rationalPrimeChangedAuxiliary_exists_integer_uniformizer_source
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))] :
    ∃ θE : 𝒪[rationalPrimeChangedAuxiliaryField p hp n u],
      Irreducible θE ∧
      algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
          (rationalPrimeChangedAuxiliaryField p hp n u) θE =
        rationalPrimeChangedAuxiliaryPoint p hp n u ∧
      Algebra.norm (rationalPrimeLocalField p hp)
          (-algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
            (rationalPrimeChangedAuxiliaryField p hp n u) θE) =
        (a : rationalPrimeLocalField p hp) * p :=
  rationalPrimeChangedAuxiliary_exists_integer_uniformizer p hp n a u hu ha

end


end
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Exact original-object consumer of the primitive root in the actual Witt
cyclotomic fraction field. -/
theorem actual_changed_cyclotomic_compositum_primitiveRoot_source
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    IsPrimitiveRoot (rationalPrimeWittCyclotomicFieldPrimitiveRoot p hp n)
      (q ^ (n + 1)) :=
  rationalPrimeWittCyclotomicFieldPrimitiveRoot_isPrimitive p hp n

/-- Exact original-object consumer of the actual changed/cyclotomic
compositum carrier. -/
theorem actual_changed_cyclotomic_compositum_coe_source
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    ((rationalPrimeChangedCyclotomicCompositum p hp n u).toIntermediateField :
      Set (wittCyclotomicField
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)) =
      (rationalPrimeChangedAuxiliaryField p hp n u ⊔
        (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField :
          IntermediateField (rationalPrimeLocalField p hp)
            (wittCyclotomicField
              (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)) :=
  rationalPrimeChangedCyclotomicCompositum_coe p hp n u

/-- Exact original-object consumer of the ambient inverse-unit root action. -/
theorem actual_changed_cyclotomic_compositum_diagonal_root_source
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (ha : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hb : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)]) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab
        (rationalPrimeWittCyclotomicFieldPrimitiveRoot p hp n) =
      (rationalPrimeWittCyclotomicFieldPrimitiveRoot p hp n) ^ b :=
  rationalPrimeDiagonalFrobenius_primitiveRoot p hp n a b ha hb hab

/-- Exact original-object consumer of preservation of the actual original
cyclotomic stage. -/
theorem actual_changed_cyclotomic_compositum_originalStage_source
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (ha : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hb : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    (x : rationalPrimeOriginalCyclotomicStage p hp n) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab x.val ∈
      (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField :=
  rationalPrimeDiagonalFrobenius_originalCyclotomicStage p hp n a b ha hb hab x

/-- Exact original-object consumer of preservation of the actual compositum. -/
theorem actual_changed_cyclotomic_compositum_preserved_source
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a)
    (ha : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hb : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    (x : rationalPrimeChangedCyclotomicCompositum p hp n u) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab x.val ∈
      (rationalPrimeChangedCyclotomicCompositum p hp n u).toIntermediateField :=
  rationalPrimeDiagonalFrobenius_changedCyclotomicCompositum
    p hp n a b u hu ha hb hab x

/-- Exact original-object consumer of the restricted actual automorphism and
its literal inverse-unit action. -/
theorem actual_changed_cyclotomic_compositum_algEquiv_root_source
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a)
    (ha : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hb : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)]) :
    rationalPrimeChangedCyclotomicDiagonalAlgEquiv p hp n a b u hu ha hb hab
        (rationalPrimeChangedCyclotomicCompositumRoot p hp n u) =
      (rationalPrimeChangedCyclotomicCompositumRoot p hp n u) ^ b :=
  rationalPrimeChangedCyclotomicDiagonalAlgEquiv_root
    p hp n a b u hu ha hb hab


open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Exact original-object consumer of the spectral local structure on the
actual changed/cyclotomic compositum. -/
theorem actual_changed_cyclotomic_local_structure_source
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)] :
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    ∃ (_ : ValuativeRel M) (_ : TopologicalSpace M)
      (_ : IsNonarchimedeanLocalField M)
      (_ : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)),
      True :=
  rationalPrimeChangedCyclotomicCompositum_exists_local_structure p hp n u

/-- Exact original-object consumer of the local uniformizer criterion that
will discharge formal unramifiedness of the actual compositum. -/
theorem actual_changed_cyclotomic_unramified_criterion_source
    (E M : Type) [Field E] [Field M] [Algebra E M]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [Module.Finite 𝒪[E] 𝒪[M]]
    (π : 𝒪[E]) (hπ : Irreducible π)
    (hmap : Irreducible (algebraMap 𝒪[E] 𝒪[M] π)) :
    Algebra.FormallyUnramified 𝒪[E] 𝒪[M] :=
  localField_integer_formallyUnramified_of_irreducible_algebraMap E M π hπ hmap

attribute [local instance] wittCyclotomicRootDVR
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

/-- Exact original-object consumer of the connected DUB-17 local chain:
the transported auxiliary uniformizer remains irreducible upstairs, the
actual compositum is formally unramified, its auxiliary residue cardinality
is the original prime, and the restricted diagonal automorphism is the
positive arithmetic Frobenius. -/
theorem actual_changed_cyclotomic_frobenius_chain_source
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))] :
    (∃ θE : 𝒪[rationalPrimeChangedAuxiliaryField p hp n u],
      Irreducible θE ∧
      algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
          (rationalPrimeChangedAuxiliaryField p hp n u) θE =
        rationalPrimeChangedAuxiliaryPoint p hp n u ∧
      Algebra.norm (rationalPrimeLocalField p hp)
          (-algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
            (rationalPrimeChangedAuxiliaryField p hp n u) θE) =
        (a : rationalPrimeLocalField p hp) * p ∧
      Irreducible (algebraMap
        𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
        𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] θE)) ∧
    Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
      𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] ∧
    Nat.card 𝓀[rationalPrimeChangedAuxiliaryField p hp n u] = p ∧
    rationalPrimeChangedCyclotomicDiagonalAlgEquiv
        p hp n a b u hu hcoprimeA hcoprimeB hab =
      letI : Algebra.FormallyUnramified
          𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
          𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] :=
        rationalPrimeChangedCyclotomicCompositum_formallyUnramified
          p hp n a u hu ha
      localFieldArithmeticFrobenius
          (rationalPrimeChangedAuxiliaryField p hp n u)
          (rationalPrimeChangedCyclotomicCompositum p hp n u) := by
  letI : Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
      𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] :=
    rationalPrimeChangedCyclotomicCompositum_formallyUnramified
      p hp n a u hu ha
  exact ⟨rationalPrimeChangedAuxiliary_exists_compositum_integer_uniformizer
      p hp n a u hu ha,
    rationalPrimeChangedCyclotomicCompositum_formallyUnramified
      p hp n a u hu ha,
    rationalPrimeChangedAuxiliary_residue_card p hp n a u hu ha,
    rationalPrimeChangedCyclotomicDiagonalAlgEquiv_eq_arithmeticFrobenius
      p hp n a b u hu ha hcoprimeA hcoprimeB hab⟩

end
end Dubon2026.SemanticRegression
