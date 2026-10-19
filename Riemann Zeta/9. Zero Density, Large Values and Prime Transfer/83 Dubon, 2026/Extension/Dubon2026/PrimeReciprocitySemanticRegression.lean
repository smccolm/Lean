import Dubon2026

/-! Exact original-prime reciprocity and full-idele completion consumers.

Retain these source consumers in their own mandatory verification module
so Lean's default-limit library-suggestion export indexes smaller scopes.
The theorem statements and proofs are unchanged; no check is disabled.
-/
namespace Dubon2026.SemanticRegression
noncomputable section FiniteGlobalLocalizationConsumerOriginalScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The actual finite Galois arithmetic stage constructs every scalar and prime comparison needed for the original finite-global localization invariant. -/
theorem regression_original_finite_stage_localization_invariant :
    letI : Algebra F H.toIntermediateField := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H.toIntermediateField := Algebra.toModule
    letI : SMul F H.toIntermediateField := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H.toIntermediateField := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H.toIntermediateField := FiniteDimensional.right ℚ F H.toIntermediateField
    letI : IsGalois F H.toIntermediateField := IsGalois.tower_top_of_isGalois ℚ F H.toIntermediateField
    letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
    letI : Algebra H.toIntermediateField (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitBaseClosureAlgebra a p hp H.toIntermediateField (QuotientGroup.mk c.out)
    letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H.toIntermediateField hFH c
    letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
    letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H.toIntermediateField (QuotientGroup.mk c.out)
    letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H.toIntermediateField hFH c
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalArithmeticOrbitPrimeCompletion a p hp H.toIntermediateField (QuotientGroup.mk c.out)) :=
      (originalAdicBaseChangeMap F H.toIntermediateField (rationalArithmeticOrbitPrime a p hp F c)
        (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))).toAlgebra
    letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H.toIntermediateField hFH c
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H.toIntermediateField) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H.toIntermediateField) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
    letI : IsScalarTower F H.toIntermediateField (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
    ∀ y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H.toIntermediateField),
    localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)
      (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c
        (continuousGaloisUnitBaseChangeCocycle F F H.toIntermediateField (rationalUnramifiedExtension a) y))) =
      originalGlobalCompletionInvariant F H.toIntermediateField (rationalArithmeticOrbitPrime a p hp F c)
        (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out)) (rationalPrimeLocalClosure p hp)
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H.toIntermediateField) y.val) := by
  exact rationalArithmeticOrbitFiniteStage_localization_invariant a p hp F H.toIntermediateField hFH c

end FiniteGlobalLocalizationConsumerOriginalScope

noncomputable section OriginalPrimeInvariantSumConsumerOriginalScope
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The actual finite arithmetic field and its original unit cocycle give one invariant term at every genuine prime above p, with all local fields and indexing premises derived. -/
theorem regression_original_prime_indexed_corestriction_invariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    letI : Fintype {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp} :=
      Fintype.ofEquiv (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F)) (rationalArithmeticOrbitPrimeEquiv a p hp F)
    rationalArithmeticUnitPrimeInvariant a p hp
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp},
        rationalArithmeticOrbitCompletionUnitInvariant a p hp F
          ((rationalArithmeticOrbitPrimeEquiv a p hp F).symm w).out y := by
  exact rationalArithmeticUnitCorestriction_primeInvariant_originalPrimes a p hp F y

end OriginalPrimeInvariantSumConsumerOriginalScope

noncomputable section OriginalCompletionSupportConsumerOriginalScope
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every actual finite-global number-field unit class has finite support in the genuine original completion Galois cohomology, without a support premise. -/
theorem regression_original_global_completion_finite_support
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)),
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w ∉ S →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (h : w.asIdeal.LiesOver v.asIdeal),
      letI := h
      letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
        (originalAdicBaseChangeMap K L v w).toAlgebra
      originalGlobalCompletionH2 K L v w x = 0 := by
  exact originalGlobalCompletionH2_exists_finite_support K L x

end OriginalCompletionSupportConsumerOriginalScope

noncomputable section OriginalOddPrimaryInvariantSumConsumerOriginalScope
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The original rational unit coefficients retain their actual discrete topology. -/
local instance arithmeticOrbitSumRationalTopology : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
/-- The specified rational unit topology is discrete. -/
local instance arithmeticOrbitSumRationalDiscrete : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
/-- The original relative unit coefficients retain their actual discrete topology. -/
local instance arithmeticOrbitSumUpperTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The specified original relative unit topology is discrete. -/
local instance arithmeticOrbitSumUpperDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩

/-- The actual odd-primary original arithmetic class has zero total of the genuine completion-invariant blocks by proved rational reciprocity, with its original coefficient and field structures. -/
theorem regression_original_odd_primary_completion_invariant_sum
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (hy : q ^ (r + 1) • (Submodule.Quotient.mk y : GaloisUnitContinuousH2
      (K := F) (Ω := rationalUnramifiedExtension a)) = 0) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∉ S, (∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F ω.out y) = 0) ∧
      (∑ p ∈ S, (∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F ω.out y)) = 0 := by
  exact rationalArithmeticOrbit_invariants_exists_support_sum_zero a F q r hq hq2 hqa y hy

end OriginalOddPrimaryInvariantSumConsumerOriginalScope

noncomputable section FiniteStageReciprocityConsumerOriginalScope
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete

private theorem finiteGaloisDegree_annihilates
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    (n : ℕ) (hn : Module.finrank K L = n)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) : n • x = 0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hz := continuousFiniteH2_card_nsmul_eq_zero (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x
  have he : Fintype.card Gal(L/K) = n :=
    Nat.card_eq_fintype_card.symm.trans ((IsGalois.card_aut_eq_finrank K L).trans hn)
  exact he ▸ hz

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- At an actual prime-power-degree original Galois stage, finite-group cohomology derives the annihilator and reciprocity constructs the individual-prime support and proves its total is zero. -/
theorem regression_original_finite_stage_prime_reciprocity
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : rationalArithmeticFiniteStageCocycles a F H hFH)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      (∀ w ∉ T, rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w = 0) ∧
      (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  have hz := finiteGaloisDegree_annihilates F H (q ^ (r + 1)) hdegree (Submodule.Quotient.mk z)
  exact rationalArithmeticFiniteStage_invariants_exists_support_sum_zero a F H hFH q r hq hq2 hqa y
    hz

end FiniteStageReciprocityConsumerOriginalScope

noncomputable section FullIdeleInvariantConsumerOriginalScope
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]


/-- The actual full-idele local invariant on the literal principal image equals the existing original finite-global normalized invariant. -/
theorem regression_original_full_idele_principal_invariant
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ω
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
      originalGlobalCompletionInvariant K L v w Ω x :=
  originalFullIdeleCompletionInvariant_principal K L v w Ω x

/-- Every actual full-idele H2 class has a constructed finite support for its original decomposition localizations. -/
theorem regression_original_full_idele_completion_support
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)), ∀ w ∉ S,
      originalFullIdeleAdicH2 K L w x = 0 :=
  originalFullIdeleAdicH2_exists_finite_support K L x

end FullIdeleInvariantConsumerOriginalScope

noncomputable section FullDecompositionIdeleLiftConsumerCyclicClassScope
open scoped NumberField

/-- The native cyclic prime-power prime selection supplies an original prime where every original local H2 class lifts with no other finite localization. -/
theorem regression_original_prime_power_idele_lift
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (q n : ℕ) (hq : q.Prime) (hn : 0 < n) (hdegree : Module.finrank K L = q ^ n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      ∀ y : groupCohomology (originalAdicUnitRep K L w) 2,
      ∃ x : groupCohomology (originalFullIdeleRep K L) 2,
        originalFullIdeleAdicH2 K L w x = y ∧
        ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 L), t ≠ w → originalFullIdeleAdicH2 K L t x = 0 := by
  obtain ⟨w, hwS, hw⟩ := original_cyclicPrimePower_exists_fullDecomposition_outside K L q n hq hn hdegree S
  refine ⟨w, hwS, fun y => ⟨originalFullDecompositionIdeleH2Lift K L w hw y, ?_, ?_⟩⟩
  · exact originalFullDecompositionIdeleH2Lift_section K L w hw y
  · exact fun t ht => originalFullDecompositionIdeleH2Lift_other K L w hw t ht y

end FullDecompositionIdeleLiftConsumerCyclicClassScope

noncomputable section NormalizedClassInvariantConsumerCyclicClassScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The constructed class invariant and the original principal H2 injection produce a unique genuine global class from an actual zero-total full-idele class. -/
theorem regression_original_cyclic_stage_zero_total_global_lift
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH)
    (hx : rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x = 0) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃! y : groupCohomology (Rep.ofAlgebraAutOnUnits F H) 2,
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H) y = x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  obtain ⟨y, hy⟩ := (rationalArithmeticFiniteStage_total_zero_iff_principal
    a F H hFH q r hq hq2 hqa hcyclic hdegree x).mp hx
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact originalFullPrincipalH2_injective F H (hz.trans hy.symm)

end NormalizedClassInvariantConsumerCyclicClassScope

noncomputable section ClassInvariantSubgroupConsumerCyclicClassScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

private theorem subgroup_vanishing_of_actual_system
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (h : ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective f ∧ (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) ∧
      (∀ x : groupCohomology (originalFullIdeleRep K L) 2,
        f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x) ∧
      ∀ S : Subgroup Gal(L/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom x) =
              S.index • f x)
    (S : Subgroup Gal(L/K)) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = 0 ↔
        S.index • total x = 0 := by
  obtain ⟨f, _, _, ht, hS⟩ := h
  obtain ⟨invS, hi, _, hs⟩ := hS S
  let y := (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x
  have he := (hs y).trans (congrArg (fun z => S.index • z) (ht x))
  exact (map_eq_zero_iff invS hi).symm.trans (Iff.of_eq (congrArg (fun z => z = 0) he))

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- Actual subgroup restriction of the actual idele-class image vanishes exactly when the subgroup index annihilates the same original-prime total. -/
theorem regression_original_cyclic_stage_subgroup_vanishing
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (S : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      Subgroup Gal(H/F))
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep F H))) 2).hom
      ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) = 0 ↔
        S.index • rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact subgroup_vanishing_of_actual_system F H (q ^ (r + 1))
    (rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticFiniteStage_exists_normalized_class_system a F H hFH q r hq hq2 hqa hcyclic hdegree) S x

end ClassInvariantSubgroupConsumerCyclicClassScope

noncomputable section FullIdeleBaseChangeConsumerRelativeComparisonScope
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K L]
  [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (u.adicCompletion E) Ω]
  [Algebra (w.adicCompletion L) Ω] [Algebra (t.adicCompletion M) Ω]
  [IsScalarTower (v.adicCompletion K) (u.adicCompletion E) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (t.adicCompletion M) Ω]
  [IsScalarTower (u.adicCompletion E) (t.adicCompletion M) Ω]
  [IsScalarTower (w.adicCompletion L) (t.adicCompletion M) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) Ω)]

/-- The constructed normalized single-prime class, without an assumed invariant value, has the exact local-degree value after genuine field base change. -/
theorem regression_original_normalized_idele_class_baseChange
    (hw : OriginalFiniteDecompositionGroup K L w = ⊤) :
    letI : IsGalois (u.adicCompletion E) Ω :=
      IsGalois.tower_top_of_isGalois (v.adicCompletion K) (u.adicCompletion E) Ω
    ∃ x : groupCohomology (originalFullIdeleRep K L) 2,
      originalFullIdeleCompletionInvariant K L v w Ω x =
        (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) ∧
      originalFullIdeleCompletionInvariant E M u t Ω
        (originalFullIdeleBaseChangeH2 K E L M x) =
        Module.finrank (v.adicCompletion K) (u.adicCompletion E) •
          (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) ∧
      ∀ z : HeightOneSpectrum (𝓞 L), z ≠ w → originalFullIdeleAdicH2 K L z x = 0 := by
  letI : IsGalois (u.adicCompletion E) Ω :=
    IsGalois.tower_top_of_isGalois (v.adicCompletion K) (u.adicCompletion E) Ω
  obtain ⟨x, hx, hzero⟩ := originalFullDecomposition_exists_normalized_idele_class K L v w Ω hw
  refine ⟨x, hx, ?_, hzero⟩
  exact (originalFullIdeleCompletionInvariant_baseChange K E L M v u w t Ω x).trans
    (congrArg (fun z : AddCircle (1 : ℚ) =>
      Module.finrank (v.adicCompletion K) (u.adicCompletion E) • z) hx)

end FullIdeleBaseChangeConsumerRelativeComparisonScope

noncomputable section FullIdeleClosureConsumerRelativeComparisonScope
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω Ξ : Type) [Field Ω] [Field Ξ]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [Algebra (v.adicCompletion K) Ξ] [Algebra (w.adicCompletion L) Ξ]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ξ]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [IsGalois (v.adicCompletion K) Ξ] [IsSepClosed Ξ]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]

/-- The actual normalized single-prime idele class constructed in one closure retains its normalization in a separately chosen compatible closure, with no supplied closure map. -/
theorem regression_original_normalized_idele_class_closure_independent
    (hw : OriginalFiniteDecompositionGroup K L w = ⊤) :
    ∃ x : groupCohomology (originalFullIdeleRep K L) 2,
      originalFullIdeleCompletionInvariant K L v w Ω x =
        (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) ∧
      originalFullIdeleCompletionInvariant K L v w Ξ x =
        (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) ∧
      ∀ z : IsDedekindDomain.HeightOneSpectrum (𝓞 L), z ≠ w →
        originalFullIdeleAdicH2 K L z x = 0 := by
  obtain ⟨x, hx, hzero⟩ := originalFullDecomposition_exists_normalized_idele_class K L v w Ω hw
  exact ⟨x, hx,
    (originalFullIdeleCompletionInvariant_closure_independent K L v w Ω Ξ x).trans hx, hzero⟩

end FullIdeleClosureConsumerRelativeComparisonScope

noncomputable section RelativeNormalizedClassInvariantConsumerRelativeComparisonScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The constructed class invariant and the original principal H2 injection produce a unique genuine global class from an actual zero-total full-idele class. -/
theorem regression_original_relative_cyclic_stage_zero_total_global_lift
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (hx : rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃! y : groupCohomology (Rep.ofAlgebraAutOnUnits F H) 2,
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H) y = x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  obtain ⟨y, hy⟩ := (rationalArithmeticRelativeStage_total_zero_iff_principal
    a F H hFH q r hq hq2 hqa hcyclic hdegree x).mp hx
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact originalFullPrincipalH2_injective F H (hz.trans hy.symm)

end RelativeNormalizedClassInvariantConsumerRelativeComparisonScope

noncomputable section RelativeClassInvariantSubgroupConsumerRelativeComparisonScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

private theorem relative_subgroup_vanishing_of_actual_system
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (h : ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective f ∧ (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) ∧
      (∀ x : groupCohomology (originalFullIdeleRep K L) 2,
        f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x) ∧
      ∀ S : Subgroup Gal(L/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom x) =
              S.index • f x)
    (S : Subgroup Gal(L/K)) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = 0 ↔
        S.index • total x = 0 := by
  obtain ⟨f, _, _, ht, hS⟩ := h
  obtain ⟨invS, hi, _, hs⟩ := hS S
  let y := (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x
  have he := (hs y).trans (congrArg (fun z => S.index • z) (ht x))
  exact (map_eq_zero_iff invS hi).symm.trans (Iff.of_eq (congrArg (fun z => z = 0) he))

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Actual subgroup restriction of the actual idele-class image vanishes exactly when the subgroup index annihilates the same original-prime total. -/
theorem regression_original_relative_cyclic_stage_subgroup_vanishing
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (S : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      Subgroup Gal(H/F))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep F H))) 2).hom
      ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) = 0 ↔
        S.index • rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact relative_subgroup_vanishing_of_actual_system F H (q ^ (r + 1))
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativeStage_exists_normalized_class_system a F H hFH q r hq hq2 hqa hcyclic hdegree) S x

end RelativeClassInvariantSubgroupConsumerRelativeComparisonScope

noncomputable section ArithmeticIdeleBaseChangeConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra

attribute [local instance] arithmeticRelativeStageIdeleAddCommGroup
  originalCompletionCarryFinite originalCompletionCarryGalois

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]
  (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a)

/-- The original constructed normalized single-prime arithmetic class has the proved local-degree value after actual relative-stage base change; no normalization or map-comparison certificate is assumed. -/
theorem regression_original_arithmetic_normalized_idele_baseChange
    (n : ℕ)
    (hdegree : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      letI : Module K L := Algebra.toModule
      Module.finrank K L = n)
    (hw : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      OriginalFiniteDecompositionGroup K L
        (rationalArithmeticOrbitPrime a p hp L (QuotientGroup.mk σ)) = ⊤) :
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a K L hKL,
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x =
        (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) ∧
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp E M hEM σ
        (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) =
        rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ •
          (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) ∧
      (letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
        ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
          t ≠ rationalArithmeticOrbitPrime a p hp L (QuotientGroup.mk σ) →
            originalFullIdeleAdicH2 K L t x = 0) := by
  obtain ⟨x, hx, hs⟩ := rationalArithmeticRelativeStageIdeleRepresentativeInvariant_exists_normalized
    a p hp K L hKL σ n hdegree hw
  refine ⟨x, hx, ?_, hs⟩
  exact (rationalArithmeticRelativeStageIdeleBaseChange_commonInvariant
    a K E L M hKE hKL hEM hLM p hp σ x).trans
      (congrArg (fun z : AddCircle (1 : ℚ) =>
        rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ • z) hx)

end ArithmeticIdeleBaseChangeConsumerAuxiliaryScope

noncomputable section ArithmeticAuxiliaryGeneratorConsumerAuxiliaryScope
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- Construct the actual auxiliary witness, compute its normalized total and full original class order, and prove that its prescribed scaled base change has zero class image. -/
theorem regression_original_arithmetic_auxiliary_generator_and_vanishing
    (q r s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclicKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      IsCyclic Gal(L/K))
    (hdegreeKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      letI : Module K L := Algebra.toModule
      Module.finrank K L = q ^ (r + 1))
    (hcyclicEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsCyclic Gal(M/E))
    (hdegreeEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ (s + 1))
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ q ^ (r + 1)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a K L hKL,
      rationalArithmeticRelativeStageIdeleTotalInvariant a K L hKL x =
        (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      addOrderOf (rationalArithmeticRelativeStageClassProjection a K L hKL x) = q ^ (r + 1) ∧
      rationalArithmeticRelativeStageClassProjection a E M hEM
        ((q ^ (r + 1) / Module.finrank K E) •
          rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨p, hp, σ, x, _, hx, _⟩ :=
    rationalArithmeticRelativeStage_exists_single_prime_invariant_class
      a K L hKL q r hq hcyclicKL hdegreeKL
  have ht := rationalArithmeticRelativeStageIdeleTotalInvariant_of_representative_values
    a K L hKL x (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ)) _ hx
  refine ⟨x, ht, ?_, ?_⟩
  · exact rationalArithmeticRelativeStage_class_order_of_normalized_total
      a K L hKL q r hq hq2 hqa hcyclicKL hdegreeKL x ht
  · exact rationalArithmeticRelativeStageIdeleBaseChange_scaled_class_zero
      a K E L M hKE hKL hEM hLM q s hq hq2 hqa hcyclicEM hdegreeEM x
      (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
      (q ^ (r + 1)) (pow_pos hq.pos (r + 1)) hd hx

end ArithmeticAuxiliaryGeneratorConsumerAuxiliaryScope

noncomputable section ArithmeticStageGeneratorConsumerAuxiliaryScope
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]

include hLM in
/-- The constructed actual target generator reaches every original idele-class H2 element by an integer multiple, and the original H2 group has exactly the extension degree. -/
theorem regression_original_arithmetic_class_generator_reaches_every_class
    (q r s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclicKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      IsCyclic Gal(L/K))
    (hdegreeKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      letI : Module K L := Algebra.toModule
      Module.finrank K L = q ^ (r + 1))
    (hcyclicEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsCyclic Gal(M/E))
    (hdegreeEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ (s + 1))
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ q ^ (r + 1)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      ∀ z : groupCohomology (originalIdeleClassRep K E) 2, ∃ m : ℤ, m • y = z := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨y, hc, hs⟩ := rationalArithmeticRelativeStage_exists_class_generator
    a K E L M hKE hKL hEM hLM q r s hq hq2 hqa
    hcyclicKL hdegreeKL hcyclicEM hdegreeEM hd
  refine ⟨y, hc, ?_⟩
  intro z
  obtain ⟨m, hm⟩ := (Submodule.span_singleton_eq_top_iff ℤ y).mp hs z
  refine ⟨m, ?_⟩
  simpa only [Int.cast_id] using (Int.cast_smul_eq_zsmul ℤ m y).symm.trans hm

end ArithmeticStageGeneratorConsumerAuxiliaryScope

noncomputable section ArithmeticPrimePowerInvariantConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- The constructed arithmetic invariant detects vanishing under every actual subgroup restriction through precisely the subgroup-index factor, with its exact global image retained. -/
theorem regression_original_arithmetic_primePower_restriction_kernel
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
      ∀ (S : Subgroup Gal(E/K)) (x : groupCohomology (originalIdeleClassRep K E) 2),
        (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x = 0 ↔
          S.index • invG x = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact originalIdeleClass_restriction_kernel_of_invariant_system K E
    (rationalArithmeticRelativePrimePower_exists_class_invariant_system
      (hGalKE := hGalKE) a K E hKE q t hq hq2 hqa hdegreeKE)

end ArithmeticPrimePowerInvariantConsumerAuxiliaryScope

noncomputable section ArithmeticPrimePowerCanonicalConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The constructed odd-primary canonical invariant detects the actual class-projection kernel, without cyclicity, auxiliary fields, class witnesses or an assumed invariant. -/
theorem regression_original_arithmetic_primePower_canonical_total_detects_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t)
    (x : rationalArithmeticRelativeStageIdeleH2 a K E hKE) :
    rationalArithmeticRelativeStageClassProjection a K E hKE x = 0 ↔
      rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE x = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact originalIdeleClass_canonical_system_zero_iff K E
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE)
    (rationalArithmeticRelativePrimePower_exists_canonical_class_system
      (hGalKE := hGalKE) a K E hKE q t hq hq2 hqa hdegreeKE) x

end ArithmeticPrimePowerCanonicalConsumerAuxiliaryScope

noncomputable section ArithmeticPrimePowerTraceConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The constructed canonical invariants make every actual subgroup trace on original class H2 injective in the odd-primary arithmetic scope. -/
theorem regression_original_arithmetic_primePower_class_trace_injective
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
    letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
    letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
    OriginalClassTraceInjective K E := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  exact originalIdeleClass_canonical_trace_injective K E
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE)
    (rationalArithmeticRelativePrimePower_exists_canonical_trace_system
      (hGalKE := hGalKE) a K E hKE q t hq hq2 hqa hdegreeKE)

end ArithmeticPrimePowerTraceConsumerAuxiliaryScope

noncomputable section SinglePrimeIdeleLiftConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- Every original local class has a genuine trace lift recovering that class and vanishing outside its original Galois prime orbit. -/
theorem regression_original_single_prime_local_class_lift
    (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] (w : HeightOneSpectrum (𝓞 E))
    (x : groupCohomology (originalAdicUnitRep K E w) 2) :
    letI : Fintype (Gal(E/K) ⧸ OriginalFiniteDecompositionGroup K E w) := Fintype.ofFinite _
    ∃ y : groupCohomology (originalFullIdeleRep K E) 2,
      originalFullIdeleAdicH2 K E w y = x ∧
      (∀ v : HeightOneSpectrum (𝓞 E),
        (∀ σ : Gal(E/K), numberFieldGaloisPlaceEquiv K E σ w ≠ v) →
        originalFullIdeleAdicH2 K E v y = 0) ∧
      y = subgroupCohomologyTrace (originalFullIdeleRep K E)
        (OriginalFiniteDecompositionGroup K E w) 2
          ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K E w) 2).map
            (originalIdeleSingleFiniteRepHom K E w) x) := by
  letI : Fintype (Gal(E/K) ⧸ OriginalFiniteDecompositionGroup K E w) := Fintype.ofFinite _
  refine ⟨originalSinglePrimeIdeleH2Lift K E w x, ?_, ?_, ?_⟩
  · exact congrArg (fun f => f.hom x) (originalSinglePrimeIdeleH2Lift_section K E w)
  · exact fun v hv => originalSinglePrimeIdeleH2Lift_outside_orbit K E w v hv x
  · exact congrArg (fun f => f.hom x) (originalSinglePrimeIdeleH2Lift_eq_trace K E w)

end SinglePrimeIdeleLiftConsumerAuxiliaryScope

noncomputable section ArithmeticCanonicalLocalClassConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The constructed normalized original local class has full-order image in the actual canonical decomposition-subgroup idele-class H2. -/
theorem regression_original_arithmetic_canonical_prime_full_order_local_image
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    let p := rationalArithmeticOriginalPrimeBase a F v
    let c := ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩).out
    OriginalLocalClassFullOrderImage F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  let p := rationalArithmeticOriginalPrimeBase a F v
  let c := ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
    ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩).out
  exact originalIdeleClass_local_full_order_of_canonical_normalization F H
    (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out))
    (rationalArithmeticRelativeStageIdeleOrbitInvariant a p.val p.property F H hFH c)
    (rationalArithmeticRelativePrimePower_exists_canonical_local_class
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree v)

end ArithmeticCanonicalLocalClassConsumerAuxiliaryScope

noncomputable section ArithmeticAnyPrimeLocalClassConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- At every original upper prime, the constructed original local class has full-order image in the actual decomposition-subgroup idele-class H2. -/
theorem regression_original_arithmetic_every_prime_full_order_local_image
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalClassFullOrderImage F H w := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  exact originalIdeleClass_local_full_order_of_canonical_normalization F H w
    (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH (originalFinitePrimeBelow F H w))
    (rationalArithmeticRelativePrimePower_exists_any_prime_local_class
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree w)

end ArithmeticAnyPrimeLocalClassConsumerAuxiliaryScope

noncomputable section ArithmeticLocalClassSurjectiveConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The constructed common original global class makes every original local-to-class H2 map of an actual odd-primary stage surjective. -/
theorem regression_original_arithmetic_all_local_class_maps_surjective
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalToClassSurjective F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_local_to_class_surjective_of_normalized_restrictions F H _
    (rationalArithmeticRelativePrimePower_exists_normalized_local_restrictions
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)

end ArithmeticLocalClassSurjectiveConsumerAuxiliaryScope

noncomputable section ArithmeticFiniteNormalizedClassConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual odd-primary arithmetic constructor supplies one global class with all original subgroup H1/H2 clauses and every source-normalized finite-completion restriction; no class or normalization certificate is assumed. -/
theorem regression_original_arithmetic_source_normalized_finite_class_system
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalFiniteNormalizedClassSystem F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
    (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)

end ArithmeticFiniteNormalizedClassConsumerAuxiliaryScope

noncomputable section ArithmeticNormalizedQuotientConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual arithmetic quotient constructor gives one class whose restriction writes every subgroup H2 class as an integer multiple, while retaining exact orders, H1 vanishing and all normalized completion restrictions. -/
theorem regression_original_arithmetic_quotient_explicit_generators
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalFiniteNormalizedQuotientGenerators F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalClassQuotient_normalized_system_explicit_generators F H _ _
    (rationalArithmeticRelativePrimePower_normalized_quotient_system
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree)

end ArithmeticNormalizedQuotientConsumerAuxiliaryScope

noncomputable section OriginalQuotientRelationConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField

/-- At an actual finite arithmetic coefficient and original outside-unit class quotient, the literal relation sequence and its connecting map need no exactness, projectivity, lattice or acyclicity certificates. The converse extension criterion remains separate. -/
theorem regression_original_quotient_relation_obstruction
    (K L : Type) [Field K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (B : Rep ℤ Gal(L/K)) [Finite B] :
    (originalRelationShortComplex B).ShortExact ∧
    Projective (originalRelationShortComplex B).X₂ ∧
    Module.Finite ℤ (originalRelationModule B) ∧
    Module.Free ℤ (originalRelationModule B) ∧
    IsIso (groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl) ∧
    (∀ φ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS,
      originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) φ = 0 ↔
        (groupCohomology.functor ℤ Gal(L/K) 2).map φ = 0) ∧
    (∀ (φ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS)
      (χ : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS),
      originalRelationInclusion B ≫ χ = φ →
        originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) φ = 0) := by
  exact ⟨originalRelationShortComplex_shortExact B,
    originalRelationFreeCover_projective B, originalRelationModule_finite B,
    originalRelationModule_free B, originalRelationConnecting_isIso B,
    fun φ => originalRelationExtensionObstruction_zero_iff B _ φ,
    fun φ χ hχ => originalRelationExtensionObstruction_zero_of_extension B _ φ χ hχ⟩

end OriginalQuotientRelationConsumerAuxiliaryScope

noncomputable section OriginalQuotientNormExtensionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField BigOperators

variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The original finite Galois group has its actual finite enumeration. -/
local instance quotientNormGaloisFintype : Fintype (Gal(L/K)) := Fintype.ofFinite _

/-- In the literal outside-unit quotient, prime torsion, trivial action, invariant norm divisibility and an actual additive norm witness construct an extension and kill the connecting obstruction. Arithmetic divisibility and the converse norm criterion are not assumed proved. -/
theorem regression_original_quotient_norm_extension
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep ℤ Gal(L/K)) (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : Gal(L/K)) (b : B), B.ρ g b = b)
    (φ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS)
    (ψ : originalRelationModule B →+ originalIdeleClassesModOutsideRep K L S hS)
    (hφ : ∀ x : originalRelationModule B,
      φ.hom x = ∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g
        (ψ ((originalRelationModule B).ρ g⁻¹ x))) :
    (∃ χ : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
      originalRelationInclusion B ≫ χ = φ) ∧
    originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) φ = 0 := by
  obtain ⟨χ, hχ⟩ := originalRelation_exists_extension_of_norm
    (originalIdeleClassesModOutsideRep K L S hS) p hnorm B hB htriv φ ψ hφ
  exact ⟨⟨χ, hχ⟩, originalRelationExtensionObstruction_zero_of_extension B _ φ χ hχ⟩

end OriginalQuotientNormExtensionConsumerAuxiliaryScope

noncomputable section OriginalQuotientNormMapConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField BigOperators

variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- Enumerate the actual finite Galois group for the literal norm. -/
local instance quotientNormMapGaloisFintype : Fintype (Gal(L/K)) := Fintype.ofFinite _

/-- For the original outside-unit quotient, the genuine obstruction is exactly the degree-two image of the norm class, and that class vanishes precisely when a genuine norm witness exists. Injectivity of the displayed map remains the substantive converse obligation. -/
theorem regression_original_quotient_norm_map
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (B : Rep ℤ Gal(L/K)) [Finite B]
    (φ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    (originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) φ = 0 ↔
      originalNormQuotientCohomologyMap (originalRelationModule B)
        (originalIdeleClassesModOutsideRep K L S hS) 1 (Submodule.Quotient.mk φ) = 0) ∧
    ((Submodule.Quotient.mk φ : OriginalCoefficientNormQuotient
      (originalRelationModule B) (originalIdeleClassesModOutsideRep K L S hS)) = 0 ↔
      ∃ η : originalRelationModule B →ₗ[ℤ] originalIdeleClassesModOutsideRep K L S hS,
        ∀ x : originalRelationModule B,
          φ.hom x = ∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g
            (η ((originalRelationModule B).ρ g⁻¹ x))) := by
  exact ⟨originalRelationObstruction_zero_iff_norm_quotient_image_zero B _ φ,
    originalCoefficientNormQuotient_mk_eq_zero_iff (originalRelationModule B) _ φ⟩

end OriginalQuotientNormMapConsumerAuxiliaryScope

noncomputable section OriginalQuotientPositiveConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField

/-- Apply the two-degree criterion and the literal normal-quotient inflation comparison to coinduction of the actual outside-unit quotient. All subgroup vanishing inputs come from the original explicit coboundaries; this does not construct the separate fundamental-class splitting module. -/
theorem regression_original_quotient_positive_inflation
    (K L : Type) [Field K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (N : Subgroup Gal(L/K)) [N.Normal] (n : ℕ) :
    let A := originalCoinducedFunctionRep (originalIdeleClassesModOutsideRep K L S hS)
    Limits.IsZero (groupCohomology A (n + 1)) ∧
      IsIso (groupCohomology.map (A := A.quotientToInvariants N) (B := A)
        (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) (n + 1)) := by
  let C := originalIdeleClassesModOutsideRep K L S hS
  exact ⟨originalPGroup_positive_zero_of_subgroup_first_second p hG
    (originalCoinducedFunctionRep C)
    (fun T => ⟨originalCoinducedSubgroup_first_zero C T,
      originalCoinducedSubgroup_second_zero C T⟩) n,
    originalPositiveInflation_isIso_of_subgroup_zero (originalCoinducedFunctionRep C) N
      (originalCoinducedSubgroup_positive_zero C N) n⟩

end OriginalQuotientPositiveConsumerAuxiliaryScope

noncomputable section OriginalQuotientInvariantNormConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The actual finite Galois group is enumerated for the literal norm. -/
local instance quotientInvariantNormGaloisFintype : Fintype (Gal(L/K)) := Fintype.ofFinite _

/-- The two-degree criterion constructs a norm preimage for every invariant in coinduction of the actual outside-unit quotient. Subgroup H1/H2 vanish by the existing explicit coboundaries; the separate fundamental-class extension is not assumed constructed. -/
theorem regression_original_quotient_invariant_norm_preimages
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K)) :
    let A := originalCoinducedFunctionRep (originalIdeleClassesModOutsideRep K L S hS)
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.ρ.norm y = x := by
  let C := originalIdeleClassesModOutsideRep K L S hS
  exact originalPGroup_norm_preimages_of_subgroup_first_second p hG
    (originalCoinducedFunctionRep C)
    (fun T => ⟨originalCoinducedSubgroup_first_zero C T,
      originalCoinducedSubgroup_second_zero C T⟩)

end OriginalQuotientInvariantNormConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalSplittingConsumerAuxiliaryScope
open CategoryTheory
attribute [local instance 1100] Rep.hV2
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- An actual normalized outside-unit quotient cocycle whose literal fundamental extension kills the whole original H2 group and has invariant norm preimages. This proposition alone asserts no existence. -/
def ActualNormalizedFundamentalConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    (originalFundamentalSplittingShortComplex C φ).ShortExact ∧
    (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFundamentalSplittingInclusion C φ) = 0 ∧
    OriginalInvariantNormSurjective (originalFundamentalSplittingModule C φ)

/-- The actual arithmetic constructor gives a normalized original cocycle whose literal extension kills every original quotient H2 class, with an actual short exact sequence and invariant norm preimages. No class-system, splitting or acyclicity input is supplied. -/
theorem regression_arithmetic_fundamental_splitting_kills_second
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualNormalizedFundamentalConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  obtain ⟨φ, ho, hl, he, _, hp, hn⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  exact ⟨φ, ho, hl, he, (hp 1).eq_zero_of_tgt _, hn⟩

end ArithmeticFundamentalSplittingConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalKernelConsumerAuxiliaryScope
open CategoryTheory
attribute [local instance 1100] Rep.hV2
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized cocycle's literal fundamental free kernel, with integral freeness and derived subgroup vanishing. This proposition alone asserts no existence. -/
def ActualNormalizedFundamentalKernelConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    (originalRelationShortComplex (originalFundamentalSplittingModule C φ)).ShortExact ∧
    Module.Free ℤ (originalRelationModule (originalFundamentalSplittingModule C φ)) ∧
    (∀ U : Subgroup Gal(L/K),
      Limits.IsZero (groupCohomology
        (Rep.res U.subtype (originalRelationModule (originalFundamentalSplittingModule C φ))) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res U.subtype (originalRelationModule (originalFundamentalSplittingModule C φ))) 2)) ∧
    (∀ n : ℕ, Limits.IsZero
      (groupCohomology (originalRelationModule (originalFundamentalSplittingModule C φ)) (n + 1))) ∧
    OriginalInvariantNormSurjective (originalRelationModule (originalFundamentalSplittingModule C φ)) ∧
    OriginalNormCoinvariantInjective (originalRelationModule (originalFundamentalSplittingModule C φ)) ∧
    Limits.IsZero (groupHomology (originalRelationModule (originalFundamentalSplittingModule C φ)) 1)

/-- The actual arithmetic construction discharges integral freeness, subgroup H1/H2, positive vanishing, both norm properties and first homology vanishing for its literal fundamental free kernel, retaining all normalized class restrictions. -/
theorem regression_arithmetic_fundamental_kernel_prepared
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualNormalizedFundamentalKernelConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  obtain ⟨hf, hsub, hp, hn⟩ := originalPGroup_relationKernel_prepared
    (originalFundamentalSplittingModule _ φ) q hG hv
  exact ⟨φ, ho, hl, originalRelationShortComplex_shortExact _, hf, hsub, hp, hn,
    originalPGroup_normCoinvariantInjective _ q hG hsub,
    originalPGroup_first_homology_zero _ q hG hsub⟩

end ArithmeticFundamentalKernelConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalPrimeReductionConsumerAuxiliaryScope
open CategoryTheory
attribute [local instance 1100] Rep.hV2
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized cocycle and the literal mod-p reduction of its actual fundamental free kernel. This proposition alone asserts no existence. -/
def ActualNormalizedFundamentalPrimeReductionConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) (p : ℕ) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    Nonempty (originalScalarReduction (originalRelationModule (originalFundamentalSplittingModule C φ)) (p : ℤ) ≅
      originalCoinducedFunctionRep (originalCoinvariantTrivialRep
        (originalScalarReduction (originalRelationModule (originalFundamentalSplittingModule C φ)) (p : ℤ))))

/-- The actual arithmetic construction proves the literal mod-p reduction of its fundamental free kernel is coinduced from its own coinvariants. No section, classification, freeness, norm or homology certificate is supplied. -/
theorem regression_arithmetic_fundamental_kernel_prime_coinduced
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualNormalizedFundamentalPrimeReductionConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) q := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  exact ⟨φ, ho, hl, originalPGroup_relationKernel_prime_coinduced
    (originalFundamentalSplittingModule _ φ) q hG hv⟩

end ArithmeticFundamentalPrimeReductionConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalProjectiveKernelConsumerAuxiliaryScope
open CategoryTheory
attribute [local instance 1100] Rep.hV2
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized cocycle and the actual projective presentation of its fundamental coefficient. This proposition alone asserts no existence. -/
def ActualNormalizedFundamentalProjectiveKernelConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    (originalRelationShortComplex (originalFundamentalSplittingModule C φ)).ShortExact ∧
    Projective (originalRelationModule (originalFundamentalSplittingModule C φ)) ∧
    Projective (originalRelationShortComplex (originalFundamentalSplittingModule C φ)).X₂ ∧
    Nonempty (originalRelationShortComplex
      (originalRelationModule (originalFundamentalSplittingModule C φ))).Splitting

/-- The actual arithmetic construction proves its literal fundamental coefficient has an actual short exact projective presentation and constructs a splitting of the kernel's own free cover. No projectivity, splitting, freeness, norm, cohomology or homology certificate is supplied. -/
theorem regression_arithmetic_fundamental_kernel_projective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualNormalizedFundamentalProjectiveKernelConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  exact ⟨φ, ho, hl, originalRelationShortComplex_shortExact _,
    originalPGroup_relationKernel_projective (originalFundamentalSplittingModule _ φ) q hG hv,
    originalRelationFreeCover_projective _,
    originalPGroup_relationKernel_cover_splits (originalFundamentalSplittingModule _ φ) q hG hv⟩

end ArithmeticFundamentalProjectiveKernelConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalInternalHomConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized cocycle and the actual internal Hom into its fundamental coefficient, with subgroup acyclicity and literal norm witnesses. This proposition alone asserts no existence. -/
def ActualNormalizedFundamentalInternalHomConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    ∀ (M : Rep.{0} ℤ Gal(L/K)), Module.Projective ℤ M →
      (∀ (T : Subgroup Gal(L/K)) (n : ℕ), Limits.IsZero (groupCohomology
        (Rep.res T.subtype ((Rep.ihom M).obj (originalFundamentalSplittingModule C φ))) (n + 1))) ∧
      OriginalInvariantNormSurjective ((Rep.ihom M).obj (originalFundamentalSplittingModule C φ)) ∧
      (∀ χ : M ⟶ originalFundamentalSplittingModule C φ,
        ∃ η : M →ₗ[ℤ] originalFundamentalSplittingModule C φ, ∀ x : M,
          χ.hom x = ∑ g : Gal(L/K), (originalFundamentalSplittingModule C φ).ρ g (η (M.ρ g⁻¹ x)))

/-- The actual normalized arithmetic coefficient has vanishing lattice internal Hom on every subgroup and constructs the exact sum-of-conjugates witness for every original lattice map. Its coefficient acyclicity, projective presentation and norm conditions are all derived. -/
theorem regression_arithmetic_fundamental_internalHom_acyclic
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualNormalizedFundamentalInternalHomConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  refine ⟨φ, ho, hl, fun M hM => ?_⟩
  letI := hM
  exact ⟨originalPGroup_internalHom_subgroup_positive_zero M
      (originalFundamentalSplittingModule _ φ) q hG hv,
    originalPGroup_internalHom_norm_preimages M (originalFundamentalSplittingModule _ φ) q hG hv,
    originalPGroup_internalHom_map_norm_witness M (originalFundamentalSplittingModule _ φ) q hG hv⟩

end ArithmeticFundamentalInternalHomConsumerAuxiliaryScope

noncomputable section ArithmeticLatticeDualityConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized fundamental coefficient together with derived lattice duality and its literal norm witnesses. This proposition alone asserts no existence or comparison between the two pairings. -/
def ActualArithmeticLatticeDualityConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    ∀ (M : Rep.{0} ℤ Gal(L/K)) (hfinite : Module.Finite ℤ M)
        (hprojective : Module.Projective ℤ M),
      letI := hfinite
      letI := hprojective
      (∀ x : groupCohomology M 2,
        (∀ y, originalLatticeIntegralDuality M x y = 0) → x = 0) ∧
      (∀ y : groupHomology (originalLinearCharacterRep ℤ M) 1,
        (∀ x, originalLatticeIntegralDuality M x y = 0) → y = 0) ∧
      (∀ χ : M ⟶ originalFundamentalSplittingModule C φ,
        ∃ η : M →ₗ[ℤ] originalFundamentalSplittingModule C φ, ∀ x : M,
          χ.hom x = ∑ g : Gal(L/K), (originalFundamentalSplittingModule C φ).ρ g (η (M.ρ g⁻¹ x)))

/-- At the actual relative odd-primary arithmetic stage, both sides of lattice duality and the fundamental coefficient norm witnesses are derived, with the same original normalized class and completion restrictions retained. -/
theorem regression_arithmetic_lattice_duality_and_fundamental_norms
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticLatticeDualityConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  refine ⟨φ, ho, hl, fun M hfinite hprojective => ?_⟩
  letI := hfinite
  letI := hprojective
  exact ⟨originalLatticeIntegralDuality_left_nondegenerate M,
    originalLatticeIntegralDuality_right_nondegenerate M,
    originalPGroup_internalHom_map_norm_witness M (originalFundamentalSplittingModule _ φ) q hG hv⟩

end ArithmeticLatticeDualityConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalHomologyConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original full-order class and completion restrictions, with the exact homology witness and integral pairing criterion for every finite lattice morphism. This proposition alone asserts no existence or induced-H2-map comparison. -/
def ActualArithmeticFundamentalHomologyConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    ∀ (M : Rep.{0} ℤ Gal(L/K)) (hfinite : Module.Finite ℤ M)
        (hprojective : Module.Projective ℤ M),
      letI := hfinite
      letI := hprojective
      ∀ χ : M ⟶ C,
        ∃ y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ Gal(L/K) ℤ)) 1,
          OriginalFundamentalHomologyWitness M C φ χ y ∧
            ((Submodule.Quotient.mk χ : OriginalCoefficientNormQuotient M C) = 0 ↔
              ∀ x : groupCohomology M 2, originalLatticeIntegralDuality M x y = 0)

/-- The actual relative arithmetic construction represents every original lattice morphism norm class by its exact augmentation homology boundary and proves the integral pairing zero criterion, retaining the same full-order class and every normalized completion restriction. -/
theorem regression_arithmetic_fundamental_homology_norm_detection
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticFundamentalHomologyConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  refine ⟨φ, ho, hl, fun M hfinite hprojective => ?_⟩
  letI := hfinite
  letI := hprojective
  exact originalFundamentalHomology_pairing_criterion M _ φ q hG hv


end ArithmeticFundamentalHomologyConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalConverseNormConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The same original full-order class and completion restrictions, with actual norm-quotient H2 injectivity and the literal norm criterion for every finite projective lattice. This proposition alone asserts no witness. -/
def ActualArithmeticFundamentalConverseNormConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    ∀ (M : Rep.{0} ℤ Gal(L/K)) (hfinite : Module.Finite ℤ M)
        (hprojective : Module.Projective ℤ M),
      letI := hfinite
      letI := hprojective
      Function.Injective (originalNormQuotientCohomologyMap M C 1) ∧
        ∀ χ : M ⟶ C,
          (groupCohomology.functor ℤ Gal(L/K) 2).map χ = 0 ↔
            ∃ η : M →ₗ[ℤ] C, originalCoefficientNormMorphism M C η = χ

/-- The actual relative odd-primary arithmetic construction proves injectivity of the original norm-quotient H2 map and the converse literal norm criterion, retaining the same full-order class and every normalized completion restriction. -/
theorem regression_arithmetic_fundamental_converse_norm
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticFundamentalConverseNormConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  have ho' : addOrderOf (groupCohomology.H2π _ φ) = Fintype.card Gal(H/F) :=
    ho.trans ((IsGalois.card_aut_eq_finrank F H).symm.trans Fintype.card_eq_nat_card.symm)
  refine ⟨φ, ho, hl, fun M hfinite hprojective => ?_⟩
  letI := hfinite
  letI := hprojective
  exact ⟨originalFundamental_normQuotient_h2_injective M _ φ q hG ho' hv,
    originalFundamental_h2_zero_iff_norm M _ φ q hG ho' hv⟩

end ArithmeticFundamentalConverseNormConsumerAuxiliaryScope

noncomputable section ArithmeticFundamentalRelationConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original normalized class and completion restrictions with the actual finite relation norm criterion and extension equivalence conditional on invariant norm divisibility. This proposition alone asserts no witness. -/
def ActualArithmeticFundamentalRelationConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (p : ℕ) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    ∀ (B : Rep.{0} ℤ Gal(L/K)) (hfinite : Finite B),
      letI := hfinite
      (∀ χ : originalRelationModule B ⟶ C,
        originalRelationExtensionObstruction B C χ = 0 ↔
          ∃ η : originalRelationModule B →ₗ[ℤ] C,
            originalCoefficientNormMorphism (originalRelationModule B) C η = χ) ∧
      (∀ (_hnorm : ∀ c : C, ∃ d : C, (∀ g : Gal(L/K), C.ρ g d = d) ∧
          (∑ g : Gal(L/K), C.ρ g c) = p • d)
        (_hB : ∀ b : B, p • b = 0)
        (_htriv : ∀ (g : Gal(L/K)) (b : B), B.ρ g b = b)
        (χ : originalRelationModule B ⟶ C),
        originalRelationExtensionObstruction B C χ = 0 ↔
          ∃ a : Rep.free ℤ Gal(L/K) B ⟶ C, originalRelationInclusion B ≫ a = χ)

/-- The actual arithmetic construction supplies the finite relation converse norm criterion and the conditional extension equivalence for the same class coefficient, retaining every completion restriction and leaving invariant norm divisibility explicit. -/
theorem regression_arithmetic_fundamental_relation_criterion
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticFundamentalRelationConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) q := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  have ho' : addOrderOf (groupCohomology.H2π _ φ) = Fintype.card Gal(H/F) :=
    ho.trans ((IsGalois.card_aut_eq_finrank F H).symm.trans Fintype.card_eq_nat_card.symm)
  refine ⟨φ, ho, hl, fun B hfinite => ?_⟩
  letI := hfinite
  exact ⟨originalFundamental_relation_obstruction_zero_iff_norm _ φ q hG ho' hv B,
    fun hnorm hB htriv χ =>
      originalFundamental_relation_obstruction_zero_iff_extension _ φ q hG ho' hv hnorm B hB htriv χ⟩

end ArithmeticFundamentalRelationConsumerAuxiliaryScope

noncomputable section ArithmeticInvariantNormIndexConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual class quotient retains its full-order normalized class and completion restrictions, and its literal invariant norm quotient has the derived abelianization, order and exponent. This proposition alone supplies no witness. -/
def ActualArithmeticInvariantNormIndexConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    Nonempty (OriginalInvariantNormQuotient C ≃+ Additive (Abelianization Gal(L/K))) ∧
    Nat.card (OriginalInvariantNormQuotient C) = Nat.card (Abelianization Gal(L/K)) ∧
    ∀ (n : ℕ), (∀ g : Gal(L/K), g ^ n = 1) →
      ∀ c : C.ρ.invariants, ∃ b : C, originalInvariantNormLinear C b = n • c

/-- The actual odd-primary arithmetic stage has the original invariant norm quotient, its exact abelianization order and literal norm witnesses for group-exponent multiples of invariants, with the same full-order class and all completion restrictions. -/
theorem regression_arithmetic_invariant_norm_index
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticInvariantNormIndexConsumer F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  obtain ⟨φ, ho, hl, _, hv, _, _⟩ :=
    rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree
  exact ⟨φ, ho, hl, ⟨originalInvariantNormAbelianEquiv _ φ q hG hv⟩,
    originalInvariantNormQuotient_card _ φ q hG hv,
    originalInvariant_multiple_is_norm _ φ q hG hv⟩

end ArithmeticInvariantNormIndexConsumerAuxiliaryScope

noncomputable section ArithmeticFullNormIndexConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original full normalized class system and the literal field norm quotient retain their actual objects, abelianization order and power norm preimages. This proposition alone supplies no witness. -/
def ActualArithmeticFullNormIndexConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  OriginalFiniteNormalizedClassSystem K L ∧
  Nonempty (OriginalIdeleClassNormQuotient K L ≃+ Additive (Abelianization Gal(L/K))) ∧
  Nat.card (OriginalIdeleClassNormQuotient K L) = Nat.card (Abelianization Gal(L/K)) ∧
  ∀ (n : ℕ), (∀ g : Gal(L/K), g ^ n = 1) →
    ∀ c : OriginalNumberFieldIdeleClassGroup K,
      ∃ b : OriginalNumberFieldIdeleClassGroup L, originalIdeleClassNorm K L b = c ^ n

/-- The actual relative odd-primary arithmetic stage has the source-normalized full class system and the literal full class-norm quotient, with its exact abelianization order and group-exponent power norm preimages. -/
theorem regression_arithmetic_full_norm_index
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticFullNormIndexConsumer F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  exact ⟨hs, originalFullClass_abelian_norm_index F H q hG hs⟩

end ArithmeticFullNormIndexConsumerAuxiliaryScope

noncomputable section ArithmeticLargeSupportNormConsumerAuxiliaryScope
open CategoryTheory
open IsDedekindDomain
open scoped BigOperators NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The precise large-support norm-field deduction on the original field
objects. The field degree, exponent and support conditions are explicit;
no normalized class system or norm-index conclusion is an input. -/
def ActualArithmeticLargeSupportNormConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (q : ℕ) : Prop :=
  ∀ [IsMulCommutative Gal(L/K)] (_hexp : ∀ g : Gal(L/K), g ^ q = 1)
    (ζ : K) (_hζ : IsPrimitiveRoot ζ q)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S),
    Function.Surjective (numberFieldSupportedIdeleClassMap K S) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (q : 𝓞 K) ∉ v.asIdeal) →
    (∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) →
    Module.finrank K L = q ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) →
    (LinearMap.range (originalIdeleClassNormLinear K L) =
      LinearMap.range ((q : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 L)))
      (hT : ∀ (σ : Gal(L/K)) w, w ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ w ∈ T)
      (_hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)
      (x : originalIdeleClassesModOutsideRep K L T hT),
      ∃ d : originalIdeleClassesModOutsideRep K L T hT,
        (∀ g, (originalIdeleClassesModOutsideRep K L T hT).ρ g d = d) ∧
        (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L T hT).ρ g x) = q • d

/-- The actual relative odd-primary arithmetic stage constructs the
normalized class system and uses it to prove the large-support norm
subgroup equality from the specified Kummer field data. -/
theorem regression_arithmetic_large_support_norm
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticLargeSupportNormConsumer F H q := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  intro hcomm hexp ζ hζ S hS hClasses hBase hAway hUpper hDegree
  have hn := originalFullSupport_normRange_eq_power_sup_outside F H q hG hs
    hexp ζ hζ S hS hClasses hBase hAway hUpper hDegree
  refine ⟨hn, ?_⟩
  intro T hT hST x
  exact originalClassesModOutside_invariant_norm_divisibility F H S T hS hT hST q hn.le x

end ArithmeticLargeSupportNormConsumerAuxiliaryScope

noncomputable section ArithmeticSubgroupNormMapConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual normalized class system and an abelianized norm map with
its literal kernel and every normal fixed-field subgroup image. This
proposition alone constructs no witness. -/
def ActualArithmeticSubgroupNormMapConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  OriginalFiniteNormalizedClassSystem K L ∧
  ∃ r : Additive (OriginalNumberFieldIdeleClassGroup K) →+ Additive (Abelianization Gal(L/K)),
    Function.Surjective r ∧
    (∀ c, r c = 0 ↔ ∃ b, originalIdeleClassNormLinear K L b = c) ∧
    ∀ (S : Subgroup Gal(L/K)) (hS : S.Normal),
      letI : S.Normal := hS
      Set.range (fun c => r (originalIdeleClassNormLinear K (IntermediateField.fixedField S) c)) =
        Set.range (Abelianization.map S.subtype).toAdditive

/-- The actual relative odd-primary stage constructs its normalized
class system and a surjective norm map whose kernel and all normal
fixed-field norm images are the literal arithmetic ones. -/
theorem regression_arithmetic_subgroup_norm_map
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticSubgroupNormMapConsumer F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  exact ⟨hs, originalFullClass_abelian_norm_map F H q hG hs⟩

end ArithmeticSubgroupNormMapConsumerAuxiliaryScope

noncomputable section ArithmeticPrescribedNormSubfieldConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual class system constructs a normal fixed field realizing
every submodule above the original norm range. This proposition alone
does not construct a field or assert any ramification support. -/
def ActualArithmeticPrescribedNormSubfieldConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  OriginalFiniteNormalizedClassSystem K L ∧
  ∀ (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K))),
    (originalIdeleClassNormLinear K L).range ≤ U →
    ∃ (S : Subgroup Gal(L/K)) (hS : S.Normal),
      letI : S.Normal := hS
      (originalIdeleClassNormLinear K (IntermediateField.fixedField S)).range = U

/-- The actual relative odd-primary stage constructs a normal fixed
field with the specified literal class-norm range. The normalized class
system and the norm correspondence are derived from the original stage. -/
theorem regression_arithmetic_prescribed_norm_subfield
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticPrescribedNormSubfieldConsumer F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  refine ⟨hs, ?_⟩
  intro U hU
  exact originalFullClass_exists_prescribed_norm_subfield F H q hG hs U hU

end ArithmeticPrescribedNormSubfieldConsumerAuxiliaryScope

noncomputable section ArithmeticCompletionNormConsumerAuxiliaryScope
open CategoryTheory
open scoped BigOperators NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual global fundamental data and all completion norm squares.
This proposition alone constructs no witness. -/
def ActualArithmeticCompletionNormConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ hG : IsPGroup p Gal(L/K), OriginalNormalizedClassCompletionNormSystem K L p hG

/-- The actual relative odd-primary stage constructs one normalized
global cocycle, its acyclicity and every normal-decomposition completion
norm comparison, without those inputs being assumed. -/
theorem regression_arithmetic_completion_norm_system
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    letI : Fact q.Prime := ⟨hq⟩
    ActualArithmeticCompletionNormConsumer F H q := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  exact ⟨hG, originalNormalizedClass_completion_norm_system F H q hG hs⟩

end ArithmeticCompletionNormConsumerAuxiliaryScope

noncomputable section ArithmeticPrescribedSupportNormFieldConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped BigOperators NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual class system and the universal prescribed-support
norm-field conclusion for the original arithmetic stage. The abelian
stage condition and the two necessary submodule inclusions are explicit.
This proposition alone constructs no witness. -/
def ActualArithmeticPrescribedSupportNormFieldConsumer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  OriginalFiniteNormalizedClassSystem K L ∧
  (IsMulCommutative Gal(L/K) →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K))),
    (originalIdeleClassNormLinear K L).range ≤ U →
    (∀ z, (originalOutsideIdeleClassRepHom K K S hS).hom z ∈ U) →
    ∃ (H : Subgroup Gal(L/K)) (hH : H.Normal),
      letI : H.Normal := hH
      (originalIdeleClassNormLinear K (IntermediateField.fixedField H)).range = U ∧
      ∀ q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)),
        originalFinitePrimeBelow K (IntermediateField.fixedField H) q ∉ S →
        (q.asIdeal.under (𝓞 K)).ramificationIdx q.asIdeal = 1)

/-- The actual relative odd-primary stage constructs the normalized
class system and prescribed-support norm fields. No local comparison,
inertia image, norm correspondence or ramification certificate is supplied. -/
theorem regression_arithmetic_prescribed_support_norm_field
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticPrescribedSupportNormFieldConsumer F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  refine ⟨hs, ?_⟩
  intro hComm S hS U hU hOutside
  letI : IsMulCommutative Gal(H/F) := hComm
  exact originalFullClass_exists_prescribed_support_norm_field_of_base_support
    F H S hS q hG hs U hU hOutside

end ArithmeticPrescribedSupportNormFieldConsumerAuxiliaryScope

noncomputable section ArithmeticReducedSupportNormFieldConsumerAuxiliaryScope
open CategoryTheory
open IsDedekindDomain
open scoped BigOperators NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The precise large-support norm-field deduction on the original field
objects. The field degree, exponent and support conditions are explicit;
no normalized class system or norm-index conclusion is an input.
The number-field structure on `L` is already supplied by its finite
extension of `K`; it is not a separate argument to this specification. -/
def ActualArithmeticReducedSupportNormFieldConsumer
    (K L : Type) [Field K] [NumberField K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (q : ℕ) : Prop :=
  ∀ [IsMulCommutative Gal(L/K)] (_hexp : ∀ g : Gal(L/K), g ^ q = 1)
    (ζ : K) (_hζ : IsPrimitiveRoot ζ q)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (_hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S),
    Function.Surjective (numberFieldSupportedIdeleClassMap K S) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (q : 𝓞 K) ∉ v.asIdeal) →
    (∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) →
    Module.finrank K L = q ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) →
    ∀ (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
      (hS₀ : ∀ (σ : Gal(K/K)) v, v ∈ S₀ ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S₀),
      S₀ ⊆ S →
      ∃ (J : Subgroup Gal(L/K)) (hJ : J.Normal),
        letI : J.Normal := hJ
        LinearMap.range (originalIdeleClassNormLinear K (IntermediateField.fixedField J)) =
          LinearMap.range ((q : ℤ) • (LinearMap.id :
            originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
          LinearMap.range (originalOutsideIdeleClassRepHom K K S₀ hS₀).hom.toLinearMap ∧
        (∀ v : HeightOneSpectrum (𝓞 (IntermediateField.fixedField J)),
          originalFinitePrimeBelow K (IntermediateField.fixedField J) v ∉ S₀ →
          (v.asIdeal.under (𝓞 K)).ramificationIdx v.asIdeal = 1) ∧
        ∀ (T : Finset (HeightOneSpectrum (𝓞 (IntermediateField.fixedField J))))
          (hT : ∀ (σ : Gal(IntermediateField.fixedField J/K)) v,
            v ∈ T ↔ numberFieldGaloisPlaceEquiv K (IntermediateField.fixedField J) σ v ∈ T)
          (_hST : ∀ v, v ∈ T ↔ originalFinitePrimeBelow K (IntermediateField.fixedField J) v ∈ S₀)
          (x : originalIdeleClassesModOutsideRep K (IntermediateField.fixedField J) T hT),
          ∃ d : originalIdeleClassesModOutsideRep K (IntermediateField.fixedField J) T hT,
            (∀ g, (originalIdeleClassesModOutsideRep K (IntermediateField.fixedField J) T hT).ρ g d = d) ∧
            (∑ g : Gal(IntermediateField.fixedField J/K),
              (originalIdeleClassesModOutsideRep K (IntermediateField.fixedField J) T hT).ρ g x) = q • d

/-- The specified original class system and large-support field data
give the exact support-reduction consumer on abstract original fields. -/
theorem arithmeticReducedSupportNormFieldConsumer_of_normalized_system
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : ℕ) [Fact q.Prime] (hG : IsPGroup q Gal(L/K))
    (hs : OriginalFiniteNormalizedClassSystem K L) :
    ActualArithmeticReducedSupportNormFieldConsumer K L q := by
  intro hcomm hexp ζ hζ S hS hClasses hBase hAway hUpper hDegree
  have hn := originalFullSupport_normRange_eq_power_sup_outside K L q hG hs
    hexp ζ hζ S hS hClasses hBase hAway hUpper hDegree
  intro S₀ hS₀ hS₀S
  obtain ⟨J, hJ, hNorm, hUnram⟩ := originalFullClass_exists_reduced_support_norm_field
    K L S₀ S hS₀ hS q hG hs hS₀S hn
  letI : J.Normal := hJ
  letI : IsGalois K (IntermediateField.fixedField J) := IsGalois.of_fixedField_normal_subgroup J
  refine ⟨J, hJ, hNorm, hUnram, ?_⟩
  intro T hT hST x
  exact originalClassesModOutside_invariant_norm_divisibility
    K (IntermediateField.fixedField J) S₀ T hS₀ hT hST q hNorm.le x


/-- The actual odd-primary stage constructs a fixed field with the
prescribed smaller norm subgroup, index one outside that support and
invariant roots of all its actual quotient norms. The large-support
field data remain explicit; normalization and the norm field are derived. -/
theorem regression_arithmetic_reduced_support_norm_field
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ActualArithmeticReducedSupportNormFieldConsumer F H q := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) := IsPGroup.of_card
    ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  have hs : OriginalFiniteNormalizedClassSystem F H :=
    originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
      (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
        (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)
  intro hcomm
  exact @arithmeticReducedSupportNormFieldConsumer_of_normalized_system
    F H _ _ _ _ _ _ _ q _ hG hs hcomm

end ArithmeticReducedSupportNormFieldConsumerAuxiliaryScope

noncomputable section ArithmeticUnrestrictedKummerNormFieldConsumerAuxiliaryScope
open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField unrestrictedArithmeticUnionClosed
  unrestrictedArithmeticUnionRelativeGalois
variable (F : IntermediateField ℚ (rationalUnramifiedExtension 0)) [FiniteDimensional ℚ F]

/-- The actual arithmetic Kummer field constructs the prescribed norm
subfield without normalized-class or large-support field hypotheses. -/
theorem regression_arithmetic_unrestricted_kummer_norm_field
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ (σ : Gal(F/F)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv F F σ v ∈ S) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧
      let N := OriginalSUnitKummerField F (rationalUnramifiedExtension 0) T p
      letI : FiniteDimensional F N := numberField_sUnit_kummerField_finiteDimensional
        F (rationalUnramifiedExtension 0) T T.finite_toSet p (Fact.out : p.Prime).pos
        ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
      letI : NumberField N := NumberField.of_module_finite F N
      letI : IsGalois F N := originalKummerRadicalField_isGalois p _
      OriginalPrescribedSupportNormSubfield F N S hS p :=
  originalUnrestricted_exists_prescribed_support_norm_field F p hp2 ζ hζ S hS

end ArithmeticUnrestrictedKummerNormFieldConsumerAuxiliaryScope

noncomputable section ArithmeticEnlargedInvariantNormRootsConsumerAuxiliaryScope
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The constructed actual stage has prime-divisible relative degree
and invariant roots of its literal quotient norm, with the original base
embedding and prescribed lower stage retained. -/
theorem regression_arithmetic_enlarged_stage_invariant_norm_roots
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    (P : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ζ : F) (hζ : IsPrimitiveRoot ζ p) :
    let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)
    ∃ N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a,
      letI : Algebra ℚ N.val := N.val.algebra'
      ∃ j : F →ₐ[ℚ] N.val,
        (∀ x : F, (j x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ)) ∧
        P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
        letI : Algebra F N.val := j.toRingHom.toAlgebra
        letI : Module F N.val := Algebra.toModule
        letI : SMul F N.val := j.toRingHom.toAlgebra.toSMul
        letI : IsScalarTower ℚ F N.val := IsScalarTower.of_algHom j
        letI : FiniteDimensional F N.val := FiniteDimensional.right ℚ F N.val
        p ∣ Module.finrank F N.val ∧
          
          ∀ (T : Finset (HeightOneSpectrum (𝓞 N.val)))
            (hT : ∀ (σ : Gal(N.val/F)) v,
              v ∈ T ↔ numberFieldGaloisPlaceEquiv F N.val σ v ∈ T)
            (_hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow F N.val w ∈ S)
            (x : originalIdeleClassesModOutsideRep F N.val T hT),
            ∃ d : originalIdeleClassesModOutsideRep F N.val T hT,
              (∀ g, (originalIdeleClassesModOutsideRep F N.val T hT).ρ g d = d) ∧
              (∑ g : Gal(N.val/F),
                (originalIdeleClassesModOutsideRep F N.val T hT).ρ g x) = p • d :=
  rationalArithmetic_exists_enlarged_stage_invariant_norm_roots a ha F P p hp2 hpa ζ hζ

end ArithmeticEnlargedInvariantNormRootsConsumerAuxiliaryScope

noncomputable section OriginalFiniteQuotientRelationConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual finite quotient class system and invariant norm roots
give the literal relation-extension criterion. No fundamental cocycle,
subgroup acyclicity or p-group certificate is assumed. -/
theorem regression_original_finite_quotient_relation_criterion
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : Gal(L/K)) (b : B), B.ρ g b = b)
    (χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    (groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      (groupCohomology.functor ℤ Gal(L/K) 2).map χ) = 0 ↔
      ∃ a : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
        originalRelationInclusion B ≫ a = χ :=
  originalClassQuotient_relation_obstruction_zero_iff_extension K L S hS hsys
    p hnorm B hB htriv χ

end OriginalFiniteQuotientRelationConsumerAuxiliaryScope

noncomputable section ArithmeticKernelNormTowerConsumerAuxiliaryScope
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/-- A constructed literal arithmetic tower has a normal restriction
kernel of prime-divisible order and invariant roots of its quotient norms.
No primitive root, norm field, class normalization or degree is supplied. -/
theorem regression_original_arithmetic_kernel_norm_tower
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a) :
    ∃ E N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      P.val.toIntermediateField ≤ E.val.toIntermediateField ∧
      ∃ hEN : E.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra ℚ E.val := E.val.algebra'
        letI : Algebra ℚ N.val := N.val.algebra'
        letI : Algebra E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
        letI : Module E.val N.val := Algebra.toModule
        letI : SMul E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra.toSMul
        letI : IsScalarTower ℚ E.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
        letI : FiniteDimensional E.val N.val := FiniteDimensional.right ℚ E.val N.val
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        
        let H := (AlgEquiv.restrictNormalHom E.val : Gal(N.val/ℚ) →* Gal(E.val/ℚ)).ker
        letI : Fintype H := Fintype.ofFinite H
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        p ∣ Nat.card H ∧ ∀ c : C, ∃ d : C,
          (∀ g : H, C.ρ g.val d = d) ∧ (∑ g : H, C.ρ g.val c) = p • d :=
  originalUnramifiedStage_exists_kernel_norm_tower Ω a ha P p hp2 hpa

end ArithmeticKernelNormTowerConsumerAuxiliaryScope

noncomputable section OriginalClassQuotientTraceConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- Consume the actual source objects and the literal maps of the
kernel/trace comparison, with its stated upstream hypotheses retained. -/
theorem regression_original_class_quotient_trace_injective
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L T hT)
    (S : Subgroup Gal(L/K)) [Fintype S] [Fintype (Gal(L/K) ⧸ S)] :
    Function.Injective (subgroupCohomologyTrace
      (originalIdeleClassesModOutsideRep K L T hT) S 2).hom :=
  originalClassQuotient_subgroup_trace_injective K L T hT hsys S

end OriginalClassQuotientTraceConsumerAuxiliaryScope

noncomputable section OriginalStageKernelActionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- Consume the actual source objects and the literal maps of the
kernel/trace comparison, with its stated upstream hypotheses retained. -/
theorem regression_original_stage_kernel_coefficient_trivial
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (P E N : FiniteGaloisIntermediateField K Ω)
    (hPE : P.toIntermediateField ≤ E.toIntermediateField)
    (hEN : E.toIntermediateField ≤ N.toIntermediateField) :
    letI : Algebra P E := (IntermediateField.inclusion hPE).toRingHom.toAlgebra
    letI : Algebra E N := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
    letI : Algebra P N := (IntermediateField.inclusion (hPE.trans hEN)).toRingHom.toAlgebra
    letI : IsScalarTower K P E := IsScalarTower.of_algHom (IntermediateField.inclusion hPE)
    letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
    letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion (hPE.trans hEN))
    ∀ (B : Rep ℤ Gal(P/K))
      (g : (AlgEquiv.restrictNormalHom E : Gal(N/K) →* Gal(E/K)).ker)
      (b : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B),
      (Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B).ρ g.val b = b :=
  originalFiniteGaloisStages_kernel_coefficient_trivial P E N hPE hEN

end OriginalStageKernelActionConsumerAuxiliaryScope

noncomputable section OriginalFiniteQuotientNormHomologyConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual normalized outside-unit quotient system constructs the
norm-class/homology equivalence without supplied fundamental cocycles,
subgroup vanishing, norm lifts or a p-group degree hypothesis. -/
theorem regression_original_finite_quotient_norm_homology
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (M : Rep.{0} ℤ Gal(L/K)) [Module.Projective ℤ M] :
    Nonempty (((M ⟶ originalIdeleClassesModOutsideRep K L S hS) ⧸
      (originalCoefficientNormLinearMap M (originalIdeleClassesModOutsideRep K L S hS)).range) ≃ₗ[ℤ]
      groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ Gal(L/K) ℤ)) 1) :=
  originalClassQuotient_norm_homology_equiv K L S hS hsys M

end OriginalFiniteQuotientNormHomologyConsumerAuxiliaryScope

noncomputable section OriginalQuotientRelationSurjectivityConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- The actual normalized quotient realizes every literal H1-to-H2
functional by a morphism from the original relation lattice. -/
theorem regression_original_quotient_relation_obstruction_surjectivity
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B]
    (θ : groupCohomology B 1 ⟶
      groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) :
    ∃ χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS,
      groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
        (groupCohomology.functor ℤ Gal(L/K) 2).map χ = θ :=
  originalClassQuotient_relation_obstruction_surjective K L S hS hsys B θ

end OriginalQuotientRelationSurjectivityConsumerAuxiliaryScope

noncomputable section OriginalQuotientInducedDecompositionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- Every zero obstruction into the actual arithmetic quotient decomposes
through its constructed induced relation comparison. -/
theorem regression_original_quotient_induced_relation_decomposition
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (N : Subgroup Gal(L/K)) (B : Rep.{0} ℤ Gal(L/K)) [Finite B] :
    let C := originalIdeleClassesModOutsideRep K L S hS
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    ∃ (ιR : originalRelationModule B ⟶ TI.X₁)
      (ιP : Rep.free ℤ Gal(L/K) B ⟶ TI.X₂)
      (ρR : TI.X₁ ⟶ originalRelationModule SB.X₃)
      (ρP : TI.X₂ ⟶ Rep.free ℤ Gal(L/K) SB.X₃),
      originalRelationInclusion B ≫ ιP = ιR ≫ TI.f ∧
      originalRelationFreeCover B ≫ SB.f = ιP ≫ TI.g ∧
      TI.f ≫ ρP = ρR ≫ originalRelationInclusion SB.X₃ ∧
      TI.g ≫ SB.g = ρP ≫ originalRelationFreeCover SB.X₃ ∧
      ∀ χ : originalRelationModule B ⟶ C,
        groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
          (groupCohomology.functor ℤ Gal(L/K) 2).map χ = 0 →
        ∃ (ψ : TI.X₁ ⟶ C) (a : Rep.free ℤ Gal(L/K) B ⟶ C),
          χ = ιR ≫ ψ + originalRelationInclusion B ≫ a :=
  originalClassQuotient_induced_relation_decomposition K L S hS hsys N B

end OriginalQuotientInducedDecompositionConsumerAuxiliaryScope

noncomputable section OriginalQuotientInducedExtensionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- The actual arithmetic quotient has the induced extension criterion,
with all class-system and comparison inputs derived from its original
normalized quotient system. -/
theorem regression_original_quotient_induced_relation_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime] (N : Subgroup Gal(L/K)) [Fintype N]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (ψ : Rep.ind N.subtype (originalRelationModule (Rep.res N.subtype B)) ⟶
      originalIdeleClassesModOutsideRep K L S hS) :
    groupCohomology.δ (originalInducedRelationSequence_shortExact N B) 1 2 rfl ≫
        (groupCohomology.functor ℤ Gal(L/K) 2).map ψ = 0 ↔
      ∃ χ : Rep.ind N.subtype (Rep.free ℤ N (Rep.res N.subtype B)) ⟶
        originalIdeleClassesModOutsideRep K L S hS,
        (Rep.indFunctor ℤ N.subtype).map (originalRelationInclusion (Rep.res N.subtype B)) ≫ χ = ψ :=
  originalClassQuotient_induced_relation_extension K L S hS hsys p N hnorm B hB hNB ψ

end OriginalQuotientInducedExtensionConsumerAuxiliaryScope

noncomputable section OriginalQuotientNontrivialExtensionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- For the original arithmetic quotient and a finite prime coefficient,
zero of the actual obstruction is equivalent to extension through the
original free cover. Only the specified subgroup must fix the coefficient. -/
theorem regression_original_quotient_nontrivial_relation_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime] (N : Subgroup Gal(L/K)) [Fintype N]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      (groupCohomology.functor ℤ Gal(L/K) 2).map χ = 0 ↔
      ∃ a : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
        originalRelationInclusion B ≫ a = χ :=
  originalClassQuotient_nontrivial_relation_extension_iff K L S hS hsys p N hnorm B hB hNB χ

end OriginalQuotientNontrivialExtensionConsumerAuxiliaryScope

noncomputable section OriginalArithmeticStageRelationConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] stageRelationRationalAlgebra

/-- At a constructed stage above the original coefficient stage,
the actual zero-obstruction/extension equivalence follows from one
full-order original class. The norm roots, kernel action, support
unramifiedness and all comparison data are constructed. -/
theorem regression_original_constructed_stage_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ (u : groupCohomology (originalIdeleClassRep ℚ N.val) 2),
          addOrderOf u = Module.finrank ℚ N.val →
          ∀ χ : originalRelationModule BN ⟶ C,
            groupCohomology.δ (originalRelationShortComplex_shortExact BN) 1 2 rfl ≫
              (groupCohomology.functor ℤ Gal(N.val/ℚ) 2).map χ = 0 ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = χ :=
  originalUnramifiedStage_exists_relation_criterion Ω a ha P p hp2 hpa B hB

end OriginalArithmeticStageRelationConsumerAuxiliaryScope

noncomputable section OriginalTwoPrimaryLocalDegreeStageConsumerAuxiliaryScope
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Construct a cyclotomic stage in the original arithmetic union and a
totally complex cyclic subfield with the required local degrees on all
of the prescribed finite support. -/
theorem regression_original_two_primary_localDegree_subfield
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        Module.finrank E F ≤ 2 ∧
        ∀ p ∈ S, ∀ w : HeightOneSpectrum (𝓞 E),
          w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
          let v := originalFinitePrimeBelow ℚ E w
          letI := originalFinitePrimeBelow_liesOver ℚ E w
          letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion E) :=
            (originalAdicBaseChangeMap ℚ E v w).toAlgebra
          2 ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) :=
  originalUnramifiedUnion_exists_two_primary_localDegree_subfield a r h2a S hS

end OriginalTwoPrimaryLocalDegreeStageConsumerAuxiliaryScope

noncomputable section OriginalTotallyComplexGlobalH2KillingConsumerAuxiliaryScope
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Divisible actual completion degrees on the original finite localization support kill the actual globally base-changed class over the totally complex field. -/
theorem regression_original_totallyComplex_global_killing
    (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois E M]
    [IsTotallyComplex E] (n : ℕ)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : n • x = 0)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0)
    (hdegree : ∀ t : HeightOneSpectrum (𝓞 M), originalFinitePrimeBelow L M t ∈ S →
      let u := originalFinitePrimeBelow E M t
      let v := originalFinitePrimeBelow K E u
      letI := originalFinitePrimeBelow_liesOver K E u
      letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
        (originalAdicBaseChangeMap K E v u).toAlgebra
      n ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 :=
  originalGlobalUnitH2_baseChange_zero_of_totallyComplex_degrees K E L M n x hx S hS hdegree

end OriginalTotallyComplexGlobalH2KillingConsumerAuxiliaryScope

noncomputable section OriginalTwoPrimaryGlobalKillingConsumerAuxiliaryScope
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower

/-- An actual two-primary global unit class becomes zero over a constructed
totally complex cyclic subfield in the original arithmetic union. -/
theorem regression_original_constructed_two_primary_globalH2_killing
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω) (a : 𝓞 ℚ) (r : ℕ)
    (h2a : (2 : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        let M := L.toIntermediateField ⊔ F.toIntermediateField
        let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
        let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
        let iE : E →ₐ[ℚ] M := iF.comp E.val
        letI : Algebra L M := iL.toAlgebra
        letI : Algebra E M := iE.toAlgebra
        letI : Module E M := Algebra.toModule
        letI : SMul E M := iE.toAlgebra.toSMul
        letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
        letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
        groupCohomology.map (galoisBaseChangeRestriction ℚ E L M)
          (galoisUnitBaseChangeInclusion ℚ E L M) 2 x = 0 :=
  originalUnramifiedUnion_exists_two_primary_globalH2_killing L a r h2a x hx

end OriginalTwoPrimaryGlobalKillingConsumerAuxiliaryScope

noncomputable section OriginalTwoPrimaryCyclicDescentConsumerAuxiliaryScope
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower

/-- An original two-primary class descends to an actual cyclic class with
the same annihilator and identical inflation inside the original union. -/
theorem regression_original_two_primary_cyclic_descent
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω) (a : 𝓞 ℚ) (r : ℕ)
    (h2a : (2 : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        ∃ hgal : IsGalois ℚ E,
        letI := hgal
        IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        let M := L.toIntermediateField ⊔ F.toIntermediateField
        let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
        let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
        let iE : E →ₐ[ℚ] M := iF.comp E.val
        letI : Algebra L M := iL.toAlgebra
        letI : Algebra E M := iE.toAlgebra
        letI : Module E M := Algebra.toModule
        letI : SMul E M := iE.toAlgebra.toSMul
        letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
        letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
        M ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2,
          2 ^ (r + 1) • y = 0 ∧
          groupCohomology.map (AlgEquiv.restrictNormalHom E)
            (finiteGaloisUnitTowerInclusion ℚ E M) 2 y =
          groupCohomology.map (AlgEquiv.restrictNormalHom L)
            (finiteGaloisUnitTowerInclusion ℚ L M) 2 x :=
  originalUnramifiedUnion_exists_two_primary_cyclic_descent L a r h2a hL x hx

end OriginalTwoPrimaryCyclicDescentConsumerAuxiliaryScope

noncomputable section OriginalTwoPrimarySourceEntryConsumerAuxiliaryScope
open NumberField
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Every actual two-primary continuous class is the original inflation
of a constructed cyclic totally complex finite-field class in the same union. -/
theorem regression_original_two_primary_continuous_source_entry
    (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hx : 2 ^ (r + 1) • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      ∃ hF : F.toIntermediateField ≤ U,
      ∃ E : IntermediateField ℚ F, ∃ hgal : IsGalois ℚ E,
      letI := hgal
      IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      let iE := (IntermediateField.inclusion hF).comp E.val
      letI : Algebra E U := iE.toAlgebra
      letI : SMul E U := iE.toAlgebra.toSMul
      letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iE
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2,
        2 ^ (r + 1) • y = 0 ∧
        continuousGaloisUnitBaseChangeH2 ℚ ℚ E U
          ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ E)
            (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := E))).symm y) = x :=
  originalUnramifiedUnitH2_exists_two_primary_cyclic_subfield a r h2a x hx

end OriginalTwoPrimarySourceEntryConsumerAuxiliaryScope

noncomputable section RationalPrimeCyclicSubfieldNormConsumerAuxiliaryScope
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

variable
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (L₀ : FiniteGaloisIntermediateField (rationalPrimeLocalField p hp)
      (rationalPrimeLocalClosure p hp))
    (hL₀ : L₀.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L₀/rationalPrimeLocalField p hp)]
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]

/-- The constructed normed uniformizer has its literal restricted Frobenius
image on every cyclic subfield, including at the prime two. -/
theorem regression_original_cyclic_subfield_normed_reciprocity :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
    let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
    let i₀ : L₀ →ₐ[K] L := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
    (localFieldFiniteCyclicReciprocity K Ω L₀
      (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i₀
            (embeddedNormalGaloisRestriction (F := E) j
              (localFieldArithmeticFrobenius E M)) :=
  rationalPrimeChangedCyclotomicClosure_cyclicSubfield_reciprocity_natural_mul_prime p hp n a u hu ha L₀ hL₀

end RationalPrimeCyclicSubfieldNormConsumerAuxiliaryScope

noncomputable section RationalTwoCyclicSubfieldCancellationConsumerAuxiliaryScope
open scoped ValuativeRel

/-- On the same cyclic subfield, the original reciprocity of `a * 2`
equals the original reciprocity of the natural unit `a`. -/
theorem regression_original_two_cyclic_subfield_prime_cancellation
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)] :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit 2 Nat.prime_two a ha))).toMul =
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul :=
  rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_mul_prime_eq_natural n a hn u hu ha L hL

end RationalTwoCyclicSubfieldCancellationConsumerAuxiliaryScope

noncomputable section RationalTwoCyclicSubfieldNaturalActionConsumerAuxiliaryScope
open scoped ValuativeRel

variable
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a)
    (L₀ : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL₀ : L₀.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L₀/rationalPrimeLocalField 2 Nat.prime_two)]

include hn

/-- Exact consumer with derived auxiliary structures and inverse exponent. -/
theorem regression_original_two_cyclic_subfield_constructed_natural_action :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
    ∃ b : ℕ, b.Coprime (2 ^ (n + 1)) ∧ a * b ≡ 1 [MOD 2 ^ (n + 1)] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
        (localFieldFiniteCyclicReciprocity K Ω L₀
          (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i₀ σ :=
  rationalTwoOriginalCyclotomicClosure_cyclicSubfield_constructed_natural_action n a hn u hu ha L₀ hL₀

end RationalTwoCyclicSubfieldNaturalActionConsumerAuxiliaryScope

noncomputable section RationalTwoFixedNaturalActionConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators ValuativeRel

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]

include hn

/-- Exact consumer of the constructed original-object reciprocity result. -/
theorem regression_original_two_fixed_natural_action
    (a : ℕ) (ha : ¬2 ∣ a) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n c v hv hc
    ∃ b : ℕ, b.Coprime (2 ^ (n + 1)) ∧ a * b ≡ 1 [MOD 2 ^ (n + 1)] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ :=
  rationalTwoOriginalCyclotomicClosure_cyclicSubfield_fixed_natural_action n c hn v hv hc L hL a ha

end RationalTwoFixedNaturalActionConsumerAuxiliaryScope

noncomputable section RationalTwoPrincipalCharacterConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators ValuativeRel

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]
    (q : ℚˣ)

include hn

/-- Exact consumer of the constructed original-object reciprocity result. -/
theorem regression_original_two_cyclic_subfield_principal_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ σ : Gal(F/K),
          (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
            2 Nat.prime_two n c v hv hc).autToPow K σ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          (localFieldFiniteCyclicReciprocity K Ω L
            (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q))).toMul =
            embeddedNormalGaloisRestriction (F := K) i σ :=
  rationalTwoOriginalCyclotomicClosure_cyclicSubfield_principal_character n c hn v hv hc L hL q

end RationalTwoPrincipalCharacterConsumerAuxiliaryScope

noncomputable section RationalTwoArithmeticPrincipalCharacterConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    [IsCyclic Gal(E/ℚ)]
    (n : ℕ) (hn : 1 ≤ n) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    (q : ℚˣ)

include hn

/-- Exact arithmetic source consumer with derived local stage and reference unit. -/
theorem regression_original_two_arithmetic_principal_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let h1 : (1 : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ).val = (1 : ℕ) :=
      by simp only [Units.val_one, Nat.cast_one]
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 h1
      Nat.prime_two.not_dvd_one
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ σ : Gal(C/K),
          (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
            2 Nat.prime_two n 1 1 h1 Nat.prime_two.not_dvd_one).autToPow K σ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
            rationalTwoArithmeticSubfieldRestriction a E F hEF n σ :=
  rationalTwoArithmeticCyclicSubfield_exists_principal_character a E F hEF n hn q

end RationalTwoArithmeticPrincipalCharacterConsumerAuxiliaryScope

noncomputable section RationalTwoArithmeticContainingPrincipalConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (n + 1))) (q : ℚˣ)

variable (hn : 1 ≤ n)
include hn

/-- Exact original containing-field principal-character consumer. -/
theorem regression_original_two_containing_principal_character :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ τ : Gal(F/ℚ),
          hζ.autToPow ℚ τ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
            embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF) τ :=
  rationalTwoArithmeticContainingField_exists_principal_character a E F hEF n hζ q hn

end RationalTwoArithmeticContainingPrincipalConsumerAuxiliaryScope

noncomputable section RationalTwoOriginalPrincipalProductConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] (q : ℚˣ)

variable (hn : 1 ≤ n)
include hn

/-- Exact principal product on the original arithmetic cyclic subfield. -/
theorem regression_original_two_cyclic_principal_product :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ _hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        (letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
         let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
           embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
         rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
           (R (rationalCyclotomicRealSignAut (2 ^ (n + 1)) F q) *
             S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
               (Rat.HeightOneSpectrum.natGenerator w.1)
               (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :=
  rationalTwoArithmeticCyclicSubfield_exists_principal_product a E F hEF n q hn

end RationalTwoOriginalPrincipalProductConsumerAuxiliaryScope

noncomputable section ArithmeticContainingAwayRestrictionConsumerAuxiliaryScope
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
  [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n) (q : ℚˣ)

include hp hpn q

variable (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]

/-- Exact restriction of original away-prime reciprocity to the cyclic subfield. -/
theorem regression_original_containing_away_restriction :
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      (arithmeticCyclotomicContainingAwayAut a F p hp n hpn q) =
      rationalArithmeticFiniteLocalReciprocityAut a E p hp q :=
  arithmeticCyclotomicContainingAwayAut_restrict a F p hp n hpn q E hEF

end ArithmeticContainingAwayRestrictionConsumerAuxiliaryScope

noncomputable section RationalTwoActualPrincipalProductConsumerAuxiliaryScope
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] (q : ℚˣ)

variable (hn : 1 ≤ n)
include hn hEF

/-- Exact principal product with the actual original real and finite arithmetic maps. -/
theorem regression_original_two_actual_principal_product :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ _hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        (letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
         rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
           (rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) *
             S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
               (Rat.HeightOneSpectrum.natGenerator w.1)
               (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :=
  rationalTwoArithmeticCyclicSubfield_exists_actual_principal_product a E F hEF n q hn

end RationalTwoActualPrincipalProductConsumerAuxiliaryScope

noncomputable section ArithmeticFiniteRealCarryInvariantConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois originalRealPeriodQuadratic
  arithmeticFiniteRealRationalAlgebra
  arithmeticFiniteRealClosureAlgebra arithmeticFiniteRealClosureSMul arithmeticFiniteRealClosureTower

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

/-- Exact original arithmetic carry, actual real unit-H2 restriction and normalized real invariant. -/
theorem regression_original_arithmetic_real_carry_invariant
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (q : ℚˣ) :
    originalRealUnitH2Invariant (rationalArithmeticFiniteRealUnitH2 a F
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q))) =
      rationalCyclicInvariant n
        (χ (rationalRealArithmeticFiniteRestriction a F
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd :=
  rationalArithmeticFiniteRealCarryInvariant a F χ q

end ArithmeticFiniteRealCarryInvariantConsumerAuxiliaryScope

noncomputable section TwoPrimaryPrincipalPrimeSumConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- Exact principal sum on the original rational primes and actual real restriction. -/
theorem regression_original_two_primary_principal_prime_sum
    (a : 𝓞 ℚ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(E/ℚ)] (q : ℚˣ)
    {d : ℕ} [NeZero d] (χ : Gal(E/ℚ) →* Multiplicative (ZMod d))
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n : ℕ) (hn : 1 ≤ n) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q)).toAdd = 0) ∧
      (∑ p ∈ T, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q)).toAdd) +
        rationalCyclicInvariant d (χ (rationalRealArithmeticFiniteRestriction a E
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd = 0 :=
  rationalTwoArithmeticCyclicSubfield_exists_principal_prime_sum a E q χ F hEF n hn

end TwoPrimaryPrincipalPrimeSumConsumerAuxiliaryScope

noncomputable section ArithmeticRealInflationConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic

attribute [local instance] arithmeticFiniteCarryGlobalAlgebra arithmeticFiniteCarryTopology
  arithmeticFiniteCarryDiscrete
variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- Exact real invariant of the same original globally inflated carry. -/
theorem regression_original_real_inflated_carry_invariant
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (q : ℚˣ) :
    originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a
      (galoisUnitFiniteStageH2Inflation F
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q)))) =
      rationalCyclicInvariant n
        (χ (rationalRealArithmeticFiniteRestriction a F
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd :=
  rationalArithmeticRealInflatedCarryInvariant a F χ q

end ArithmeticRealInflationConsumerAuxiliaryScope

noncomputable section TwoPrimaryCyclicFiniteStageConsumerAuxiliaryScope
open scoped NumberField BigOperators
open NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
variable (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include h2a

/-- Exact original annihilator, containing cyclotomic field, subfield inclusion and inflation. -/
theorem regression_original_two_primary_retained_cyclic_stage
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      E.toIntermediateField ≤ F.toIntermediateField ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        2 ^ (r + 1) • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y = x :=
  rationalArithmeticUnitH2_exists_two_primary_cyclic_finite_stage a r h2a x hx

end TwoPrimaryCyclicFiniteStageConsumerAuxiliaryScope

noncomputable section TwoPrimaryUnitInvariantSumConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic
variable (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include h2a
variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

/-- Exact finite support and finite-plus-real sum for every original two-primary arithmetic unit class. -/
theorem regression_original_two_primary_unit_invariant_support_sum
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
        originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 :=
  rationalArithmeticUnitInvariant_exists_two_primary_support_sum_zero a r h2a x hx

/-- Exact sum on every finite support of the same original two-primary class. -/
theorem regression_original_two_primary_unit_invariant_sum
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) (T : Finset Nat.Primes)
    (hT : ∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) :
    (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 :=
  rationalArithmeticUnitInvariant_two_primary_sum_zero a r h2a x hx T hT

end TwoPrimaryUnitInvariantSumConsumerAuxiliaryScope

noncomputable section PrimePowerUnitInvariantSumConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic
variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
variable (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include hq hqa

/-- Exact finite-plus-real sum on the original prime-power arithmetic unit class, including two. -/
theorem regression_original_prime_power_unit_invariant_support_sum
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
        originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 :=
  rationalArithmeticUnitInvariant_exists_prime_power_support_sum_zero a q r hq hqa x hx

/-- Exact finite-plus-real sum on the original prime-power arithmetic unit class, including two. -/
theorem regression_original_prime_power_unit_invariant_sum
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) (T : Finset Nat.Primes)
    (hT : ∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) :
    (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 :=
  rationalArithmeticUnitInvariant_prime_power_sum_zero a q r hq hqa x hx T hT

end PrimePowerUnitInvariantSumConsumerAuxiliaryScope

noncomputable section RealInfiniteKernelConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic arithmeticRealGlobalClosureAlgebra arithmeticRealGlobalClosureSMul
  arithmeticRealGlobalClosureTower arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete
  arithmeticRealOrbitUpperGalois arithmeticRealOrbitGlobalFinite arithmeticRealOrbitGlobalFintype
  arithmeticRealOrbitIndexFinite arithmeticRealOrbitIndexFintype
  arithmeticRealOrbitStabilizerFintype arithmeticRealOrbitStabilizerFamily

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Exact consumer retaining the original objects, all parameters and the derived conclusion. -/
theorem regression_rationalArithmeticRealCorestriction_eq_zero_of_infinite
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      ∀ v : NumberField.InfinitePlace H,
        originalGlobalInfiniteH2 F H v (groupCohomology.H2π _ z.val) = 0) :
    rationalArithmeticRealUnitH2Restriction a
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
        (Submodule.Quotient.mk (@rationalArithmeticRelativeStageInflation a F H hFH hGal y))) = 0 :=
  rationalArithmeticRealCorestriction_eq_zero_of_infinite a F H hFH y hy

end RealInfiniteKernelConsumerAuxiliaryScope

noncomputable section PrimePowerOriginalSumConsumerAuxiliaryScope
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOriginalPrimeFiberFintype

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- Exact consumer retaining the original objects, all parameters and the derived conclusion. -/
theorem regression_rationalArithmeticOriginalPrimeInvariant_prime_power_sum_add_real_zero
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (hy : q ^ (r + 1) • (Submodule.Quotient.mk y : GaloisUnitContinuousH2
      (K := F) (Ω := rationalUnramifiedExtension a)) = 0)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : ∀ w ∉ T, rationalArithmeticOriginalPrimeInvariant a F y w = 0) :
    (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F y w) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a
        (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
          (Submodule.Quotient.mk y))) = 0 :=
  rationalArithmeticOriginalPrimeInvariant_prime_power_sum_add_real_zero a F q r hq hqa y hy T hT

end PrimePowerOriginalSumConsumerAuxiliaryScope

noncomputable section AllPrimeCyclicClassConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Exact consumer retaining the original objects, all parameters and the derived conclusion. -/
theorem regression_rationalArithmeticRelativeStage_exists_prime_power_full_order_idele
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
        (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      (∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) ∧
      addOrderOf ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
        q ^ (r + 1) :=
  rationalArithmeticRelativeStage_exists_prime_power_full_order_idele a F H hFH q r hq hqa hcyclic hdegree

end AllPrimeCyclicClassConsumerAuxiliaryScope

noncomputable section AllPrimeClassKernelConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Exact consumer retaining the original objects, all parameters and the derived conclusion. -/
theorem regression_rationalArithmeticRelativeStage_class_zero_iff_total_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      (∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) →
      ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x = 0 ↔
        rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0) :=
  rationalArithmeticRelativeStage_class_zero_iff_total_of_infinite a F H hFH q r hq hqa hcyclic hdegree

end AllPrimeClassKernelConsumerAuxiliaryScope

noncomputable section CyclicTwoPowerFieldConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- Exact consumer of the actual constructed fields and class maps, retaining every source parameter. -/
theorem regression_rationalArithmetic_exists_cyclic_twoPower_subfield
    (a : 𝓞 ℚ) (n : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a) :
    ∃ D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      IsCyclic Gal(D/ℚ) ∧ Module.finrank ℚ D = 2 ^ n :=
  rationalArithmetic_exists_cyclic_twoPower_subfield a n h2a

end CyclicTwoPowerFieldConsumerAuxiliaryScope

noncomputable section SinglePrimeBaseChangeInfiniteConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]

/-- Exact consumer of the actual constructed fields and class maps, retaining every source parameter. -/
theorem regression_rationalArithmeticRelativeStageIdeleBaseChange_lift_infinite_zero
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hw : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      OriginalFiniteDecompositionGroup K L w = ⊤)
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (hx : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
        x = originalFullDecompositionIdeleH2Lift K L w hw y) :
    letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    ∀ v : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 E M v
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 :=
  rationalArithmeticRelativeStageIdeleBaseChange_lift_infinite_zero a K E L M hKE hKL hEM hLM w hw x hx

end SinglePrimeBaseChangeInfiniteConsumerAuxiliaryScope

noncomputable section AllPrimePowerGeneratorConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Exact consumer of the actual constructed fields and class maps, retaining every source parameter. -/
theorem regression_rationalArithmeticRelativeAllPrimePower_exists_class_generator
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ :=
  rationalArithmeticRelativeAllPrimePower_exists_class_generator a K E hKE q t hq hqa hdegreeKE

end AllPrimePowerGeneratorConsumerAuxiliaryScope

noncomputable section AllPrimePowerInvariantSystemConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Exact consumer of the actual constructed fields and class maps, retaining every source parameter. -/
theorem regression_rationalArithmeticRelativeAllPrimePower_exists_class_invariant_system
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E ∧
      ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
        Function.Injective invG ∧
        (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
        invG u = ↑((1 : ℚ) / Module.finrank K E) ∧
        ∀ S : Subgroup Gal(E/K),
          ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
            Function.Injective invS ∧
            (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
            ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
              invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
                S.index • invG x :=
  rationalArithmeticRelativeAllPrimePower_exists_class_invariant_system a K E hKE q t hq hqa hdegreeKE

end AllPrimePowerInvariantSystemConsumerAuxiliaryScope

noncomputable section OriginalInfiniteBaseChangeConsumerAuxiliaryScope
open NumberField CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

/-- Exact original-object consumer of the constructed arithmetic class system and its source-normalized completion maps. -/
theorem regression_originalFullIdeleInfiniteH2_baseChange
    (v : InfinitePlace M) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleInfiniteH2 E M v (originalFullIdeleBaseChangeH2 K E L M x) =
      groupCohomology.map (originalInfiniteBaseChangeStabilizerHom K E L M v)
        (originalInfiniteBaseChangeRepHom K E L M v) 2
        (originalFullIdeleInfiniteH2 K L (v.comap (algebraMap L M)) x) :=
  originalFullIdeleInfiniteH2_baseChange K E L M v x

end OriginalInfiniteBaseChangeConsumerAuxiliaryScope

noncomputable section AllPrimeInfiniteKernelSystemConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup

/-- Exact original-object consumer of the constructed arithmetic class system and its source-normalized completion maps. -/
theorem regression_rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    OriginalInfiniteKernelClassInvariantSystem K E
      (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) :=
  rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system a K E hKE q t hq hqa hdegreeKE

end AllPrimeInfiniteKernelSystemConsumerAuxiliaryScope

noncomputable section AllPrimeCompletionRestrictionConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Exact original-object consumer of the constructed arithmetic class system and its source-normalized completion maps. -/
theorem regression_rationalArithmeticRelativeAllPrimePower_exists_completion_local_restrictions
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    ∃ u : groupCohomology (originalIdeleClassRep F H) 2,
      addOrderOf u = Module.finrank F H ∧ OriginalCompletionClassRestrictions F H u :=
  rationalArithmeticRelativeAllPrimePower_exists_completion_local_restrictions a F H hFH q t hq hqa hdegree

end AllPrimeCompletionRestrictionConsumerAuxiliaryScope

noncomputable section AllPrimeFiniteClassSystemConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Exact original-object consumer of the constructed arithmetic class system and its source-normalized completion maps. -/
theorem regression_rationalArithmeticRelativeAllPrimePower_finite_normalized_class_system
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalFiniteNormalizedClassSystem F H :=
  rationalArithmeticRelativeAllPrimePower_finite_normalized_class_system a F H hFH q t hq hqa hdegree

end AllPrimeFiniteClassSystemConsumerAuxiliaryScope

noncomputable section MixedPrimaryOrderConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Exact consumer retaining the original fields, coefficients, maps and quantifiers. -/
theorem regression_rationalArithmeticRelativeStage_exists_prime_power_order_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      q ^ t ∣ Module.finrank K E) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = q ^ t :=
  rationalArithmeticRelativeStage_exists_prime_power_order_class a K E hKE q t hq hqa hdegreeKE

end MixedPrimaryOrderConsumerAuxiliaryScope

noncomputable section MixedFullOrderConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Exact consumer retaining the original fields, coefficients, maps and quantifiers. -/
theorem regression_rationalArithmeticRelativeStage_exists_mixed_degree_full_order_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (hallowed : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      ∀ q : ℕ, q.Prime → q ∣ Module.finrank K E → (q : 𝓞 ℚ) ∣ a) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ x : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf x = Module.finrank K E :=
  rationalArithmeticRelativeStage_exists_mixed_degree_full_order_class a K E hKE hallowed

end MixedFullOrderConsumerAuxiliaryScope

noncomputable section RationalFullOrderConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- Exact consumer retaining the original fields, coefficients, maps and quantifiers. -/
theorem regression_originalRationalNumberField_exists_full_order_class_of_algebra
    (K : Type) [Field K] [NumberField K] [hAlg : Algebra ℚ K] [IsGalois ℚ K] :
    ∃ u : groupCohomology (originalIdeleClassRep ℚ K) 2,
      addOrderOf u = Module.finrank ℚ K :=
  originalRationalNumberField_exists_full_order_class_of_algebra K

end RationalFullOrderConsumerAuxiliaryScope

noncomputable section ConstructedRelationCriterionConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Use the actual stage inclusion as the rational algebra throughout
the assembled field towers and coefficient restrictions. -/
local instance consumerConstructedStageRelationRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- Exact consumer retaining the original fields, coefficients, maps and quantifiers. -/
theorem regression_originalUnramifiedStage_exists_constructed_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ χ : originalRelationModule BN ⟶ C,
            originalRelationExtensionObstruction BN C χ = 0 ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = χ :=
  originalUnramifiedStage_exists_constructed_relation_criterion Ω a ha P p hp2 hpa B hB

end ConstructedRelationCriterionConsumerAuxiliaryScope

noncomputable section RelationObstructionTransitionConsumerAuxiliaryScope
open CategoryTheory
variable {G H : Type} [Group G] [Group H] (f : G →* H)
  (B C : Rep ℤ H) (D : Rep ℤ G)

/-- Exact consumer of the original relation and arithmetic stage maps. -/
theorem regression_originalRelationExtensionObstruction_groupChange
    (φ : originalRelationModule B ⟶ C) (j : Rep.res f C ⟶ D) :
    groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫
      originalRelationExtensionObstruction (Rep.res f B) D
        (originalRelationGroupChange f B ≫ (Rep.resFunctor f).map φ ≫ j) =
      originalRelationExtensionObstruction B C φ ≫ groupCohomology.map f j 2 :=
  originalRelationExtensionObstruction_groupChange f B C D φ j

end RelationObstructionTransitionConsumerAuxiliaryScope

noncomputable section ConstructedRelationLevelConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Use the actual stage inclusion as the rational algebra throughout
the assembled field towers and coefficient restrictions. -/
local instance consumerLevelDichotomyRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- Exact consumer of the original relation and arithmetic stage maps. -/
theorem regression_originalUnramifiedStage_exists_relation_level_dichotomy
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    let S := originalExceptionalIntegerSupport P.val (algebraMap (𝓞 ℚ) (𝓞 P.val) a)
      (originalIntegerMap_ne_zero (L := P.val) a ha)
    let hS := originalExceptionalIntegerSupport_galoisStable P.val ℚ a ha
    let CP := originalIdeleClassesModOutsideRep ℚ P.val S hS
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ φ : originalRelationModule B ⟶ CP,
          let π : Gal(N.val/ℚ) →* Gal(P.val/ℚ) := AlgEquiv.restrictNormalHom P.val
          let ψ := originalRelationGroupChange π B ≫ (Rep.resFunctor π).map φ ≫
            originalRationalExceptionalClassTransition P.val N.val a ha
          (∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ) ∨
            ∃ y : groupCohomology BN 1, (originalRelationExtensionObstruction BN C ψ).hom y ≠ 0 :=
  originalUnramifiedStage_exists_relation_level_dichotomy Ω a ha P p hp2 hpa B hB

end ConstructedRelationLevelConsumerAuxiliaryScope

noncomputable section ArithmeticPrimeRelationPairingConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Retain the original stage's rational algebra in the scalar pairing. -/
local instance consumerRelationPrimePairingRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- Exact consumer of the constructed original scalar relation pairing. -/
theorem regression_originalUnramifiedStage_exists_prime_relation_pairing
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [NeZero p] (B : Rep.{0} ℤ Gal(N.val/ℚ)) (hB : ∀ b : B, p • b = 0) :
    let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
      (originalIntegerMap_ne_zero (L := N.val) a ha)
    let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
    let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
    ∃ inv : groupCohomology C 2 →+ AddCircle (1 : ℚ), Function.Injective inv ∧
      ∃ α : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p),
        (∀ φ y, rationalCyclicInvariant p (α φ y) =
          inv ((originalRelationExtensionObstruction B C φ).hom y)) ∧
        ∀ φ y, α φ y = 0 ↔ (originalRelationExtensionObstruction B C φ).hom y = 0 :=
  originalUnramifiedStage_exists_prime_relation_pairing a ha N p B hB

end ArithmeticPrimeRelationPairingConsumerAuxiliaryScope

noncomputable section ScalarRelationCriterionConsumerAuxiliaryScope
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Keep the actual stage's displayed rational algebra. -/
local instance consumerScalarCriterionRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- Exact consumer of the constructed original scalar relation pairing. -/
theorem regression_originalUnramifiedStage_exists_scalar_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∃ d : OriginalRelationPrimePairingData BN C p,
          ∀ ψ : originalRelationModule BN ⟶ C,
            (∀ y, d.readout ψ y = 0) ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ :=
  originalUnramifiedStage_exists_scalar_relation_criterion Ω a ha P p hp2 hpa B hB

end ScalarRelationCriterionConsumerAuxiliaryScope

noncomputable section ArithmeticRelationDualExactConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- Exact consumer of the original arithmetic S-unit dual relation comparison. -/
theorem regression_arithmeticRelationSUnitDualSequence_shortExact
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (B : Rep.{0} ℤ Gal(F/K)) (hB : ∀ b : B, q • b = 0) :
    (originalContravariantHomShortComplex
      ((originalRelationShortComplex B).map
        (Rep.resFunctor (AlgEquiv.restrictNormalHom F :
          Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))))
      (originalArithmeticSUnitRepresentation K Ω a ha)).ShortExact :=
  arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hB

end ArithmeticRelationDualExactConsumerAuxiliaryScope

noncomputable section ArithmeticRelationFreeContinuityConsumerAuxiliaryScope
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K))

/-- Exact consumer of the original arithmetic S-unit dual relation comparison. -/
theorem regression_arithmeticRelationFreeSUnitDualAction_continuous [Finite B]
    [TopologicalSpace (arithmeticRelationFreeSUnitDual K Ω a ha F B)]
    [DiscreteTopology (arithmeticRelationFreeSUnitDual K Ω a ha F B)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
      arithmeticRelationFreeSUnitDual K Ω a ha F B =>
        (arithmeticRelationFreeSUnitDual K Ω a ha F B).ρ z.1 z.2) :=
  arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B

end ArithmeticRelationFreeContinuityConsumerAuxiliaryScope

noncomputable section ArithmeticRelationCupConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K)) [Finite B] (hCoeff : ∀ b : B, q • b = 0)

/-- Exact consumer of the original arithmetic S-unit dual relation comparison. -/
theorem regression_arithmeticRelationSUnitCup_adjunction :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F;
    let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
      X₁ := Rep.res π (originalRelationModule B)
      X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
      X₃ := Rep.res π B
      f := (Rep.resFunctor π).map (originalRelationInclusion B)
      g := (Rep.resFunctor π).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero };
    let D := originalArithmeticSUnitRepresentation K Ω a ha;
    letI : TopologicalSpace X.X₁ := ⊥;
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₂ := ⊥;
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₃ := ⊥;
    letI : DiscreteTopology X.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace D := ⊥;
    letI : DiscreteTopology D := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hA := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (originalRelationModule B);
    let hB := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (Rep.free ℤ Gal(F/K) B);
    let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B;
    let hD := originalArithmeticSUnitAction_continuous K Ω a ha;
    let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD;
    let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B;
    let hX : X.ShortExact := originalRelationGroupChange_shortExact π B;
    let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff;
    ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      (continuousShortComplexInvariantConnectingMap
        (originalContravariantHomShortComplex X D) hY hU hV w) :=
  arithmeticRelationSUnitCup_adjunction K Ω a ha q hqa F B hCoeff

end ArithmeticRelationCupConsumerAuxiliaryScope

noncomputable section ArithmeticRelationCupAlgebraicConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K)) [Finite B] (hCoeff : ∀ b : B, q • b = 0)

/-- Exact consumer of the original arithmetic S-unit dual relation comparison. -/
theorem regression_arithmeticRelationSUnitCup_toAlgebraic :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F;
    let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
      X₁ := Rep.res π (originalRelationModule B)
      X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
      X₃ := Rep.res π B
      f := (Rep.resFunctor π).map (originalRelationInclusion B)
      g := (Rep.resFunctor π).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero };
    let D := originalArithmeticSUnitRepresentation K Ω a ha;
    letI : TopologicalSpace X.X₁ := ⊥;
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₂ := ⊥;
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₃ := ⊥;
    letI : DiscreteTopology X.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace D := ⊥;
    letI : DiscreteTopology D := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B;
    let hD := originalArithmeticSUnitAction_continuous K Ω a ha;
    let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD;
    let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B;
    let hX : X.ShortExact := originalRelationGroupChange_shortExact π B;
    let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff;
    ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousH2ToAlgebraic D hD
      (continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D)
        (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology hC hU hD x
        (continuousShortComplexInvariantConnectingMap
          (originalContravariantHomShortComplex X D) hY hU hV w)) =
    groupCohomology.map (MonoidHom.id Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (originalInvariantHomMorphism X.X₁ D w) 2
      (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x)) :=
  arithmeticRelationSUnitCup_toAlgebraic K Ω a ha q hqa F B hCoeff

end ArithmeticRelationCupAlgebraicConsumerAuxiliaryScope

noncomputable section ArithmeticClassHomDescentConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- Exact consumer preserving the original finite stage and source-class coefficient values. -/
theorem regression_arithmeticFiniteClassHom_exists_galois_descent
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B ⟶
        arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
        letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
        letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        ∃ η : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B ⟶
            arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ b : B, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom b) =
              φ.hom b :=
  arithmeticFiniteClassHom_exists_galois_descent K Ω a ha P B φ

end ArithmeticClassHomDescentConsumerAuxiliaryScope

noncomputable section ArithmeticSourceClassInvariantDescentConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- Exact consumer preserving the original finite stage and source-class coefficient values. -/
theorem regression_arithmeticSourceInvariantClass_exists_finite_descent
    (w : (arithmeticSourceClassHomRep K Ω a ha
      (Rep.res (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B)).ρ.invariants) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
        letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
        letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        ∃ η : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B ⟶
            arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ b : B, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom b) =
              (arithmeticSourceClassColimitComparison K Ω a ha).hom
                ((show B →ₗ[ℤ] arithmeticSPlaceClassColimitRep K Ω a ha from w.val) b) :=
  arithmeticSourceInvariantClass_exists_finite_descent K Ω a ha P B w

end ArithmeticSourceClassInvariantDescentConsumerAuxiliaryScope

noncomputable section ArithmeticRelationClassStageConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- Exact consumer of the original relation lattice and actual finite class stage. -/
theorem regression_arithmeticRelationClassHom_exists_stage
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) (originalRelationModule B) ⟶
        arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      P ≤ N ∧ ∃ ψ : Rep.res (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) (originalRelationModule B) ⟶
          arithmeticGlobalClassesModOutsideStageRep K Ω a ha N,
        ψ ≫ coefficientRepresentationColimitOf _
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N = φ :=
  arithmeticRelationClassHom_exists_stage K Ω a ha P B φ

end ArithmeticRelationClassStageConsumerAuxiliaryScope

noncomputable section ArithmeticRelationClassGaloisConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- Exact consumer of the original relation lattice and actual finite class stage. -/
theorem regression_arithmeticRelationClassHom_exists_finite_relation_descent
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K))
        (originalRelationModule B) ⟶ arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
        letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
        letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
        ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ r, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom r) =
              φ.hom ((originalRelationGroupChange τ B).hom r) :=
  arithmeticRelationClassHom_exists_finite_relation_descent K Ω a ha P B φ

end ArithmeticRelationClassGaloisConsumerAuxiliaryScope

noncomputable section ArithmeticFreeClassHomCocycleConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union's displayed rational inclusion. -/
local instance freeClassHomUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite stage's displayed rational inclusion. -/
local instance freeClassHomStageAlgebra : Algebra ℚ P := P.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticRelationFreeClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticRelationFreeClassHom Ω a ha P B)]

/-- The original discrete Hom coefficient has continuous integer scalar action. -/
local instance freeClassHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticRelationFreeClassHom Ω a ha P B)
      (arithmeticRelationFreeClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticRelationFreeClassHom Ω a ha P B)
    (arithmeticRelationFreeClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original discrete class coefficient has continuous integer scalar action. -/
local instance classHomTargetContinuousSMul :
    @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Exact consumer retaining the actual original cocycle, relation morphism and coefficient maps. -/
theorem regression_arithmeticRelationFreeClassHomCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesOne (arithmeticRelationFreeClassHom Ω a ha P B)) :
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B,
      ∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v = c.val g :=
  arithmeticRelationFreeClassHomCocycle_exists_coboundary Ω a ha P B c

end ArithmeticFreeClassHomCocycleConsumerAuxiliaryScope

noncomputable section ArithmeticClassCocycleFiniteRelationConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance finiteClassRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance finiteClassRelationStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance finiteClassRelationHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Exact consumer retaining the actual original cocycle, relation morphism and coefficient maps. -/
theorem regression_arithmeticClassHomCocycle_exists_finite_relation_representative
    [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      (∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom (c.val g)) ∧
      ∃ N : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          letI : Module P N := Algebra.toModule
          letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
          letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
          let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
          ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha N,
            ∀ r, (coefficientRepresentationColimitOf _
              (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) N).hom (η.hom r) =
                φ.hom ((originalRelationGroupChange τ B).hom r) :=
  arithmeticClassHomCocycle_exists_finite_relation_representative Ω a ha P B c

end ArithmeticClassCocycleFiniteRelationConsumerAuxiliaryScope

noncomputable section ArithmeticSourceClassCocycleFiniteRelationConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceFiniteRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceFiniteRelationStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceFiniteRelationHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Exact consumer retaining the actual original cocycle, relation morphism and coefficient maps. -/
theorem regression_arithmeticSourceClassHomCocycle_exists_finite_relation_representative
    [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      (∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom
          ((arithmeticSourceClassHomComparison ℚ Ω a ha (Rep.res π B)).hom (c.val g))) ∧
      ∃ N : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          letI : Module P N := Algebra.toModule
          letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
          letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
          let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
          ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha N,
            ∀ r, (coefficientRepresentationColimitOf _
              (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) N).hom (η.hom r) =
                φ.hom ((originalRelationGroupChange τ B).hom r) :=
  arithmeticSourceClassHomCocycle_exists_finite_relation_representative Ω a ha P B c

end ArithmeticSourceClassCocycleFiniteRelationConsumerAuxiliaryScope

noncomputable section ArithmeticEmbeddedRelationScalarConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Keep the original arithmetic union's rational inclusion. -/
local instance relationScalarPlacementUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Keep every original finite stage's displayed rational algebra. -/
local instance relationScalarPlacementStageAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Exact consumer of the actual field transport and constructed scalar relation criterion. -/
theorem regression_arithmeticClassRelation_exists_original_scalar_criterion
    (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : P →ₐ[ℚ] F.val,
      (∀ x : P, (i x : Ω) = (x.val : Ω)) ∧
      let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
      ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
        ∃ hFN : F.val.toIntermediateField ≤ N.val.toIntermediateField,
          letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
          letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
          let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
            (originalIntegerMap_ne_zero (L := N.val) a ha)
          let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
          let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
          let BN := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(N.val/ℚ) →* Gal(F.val/ℚ)) BF
          ∃ d : OriginalRelationPrimePairingData BN C p,
            ∀ φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha P F i B N hFN φ
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ :=
  arithmeticClassRelation_exists_original_scalar_criterion Ω a ha P p hp2 hpa B hB

end ArithmeticEmbeddedRelationScalarConsumerAuxiliaryScope

noncomputable section ArithmeticSourceClassScalarStageConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarStageUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarStageFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarStageHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Exact consumer of the actual field transport and constructed scalar relation criterion. -/
theorem regression_arithmeticSourceClassHomCocycle_exists_scalar_relation_stage
    [Finite B]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : r.stage →ₐ[ℚ] F.val,
        (∀ x : r.stage, (i x : Ω) = (x.val : Ω)) ∧
        let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
          (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
        ∃ L : OriginalUnramifiedGaloisStage (Ω := Ω) a,
          ∃ hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField,
            letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
            letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
            let T := originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
              (originalIntegerMap_ne_zero (L := L.val) a ha)
            let hT := originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha
            let C := originalIdeleClassesModOutsideRep ℚ L.val T hT
            let BL := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(L.val/ℚ) →* Gal(F.val/ℚ)) BF
            ∃ d : OriginalRelationPrimePairingData BL C p,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha r.stage F i
                (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) L hFL
                  (arithmeticSourceClassRelationStageHom Ω a ha P B c r)
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(L.val/ℚ) BL ⟶ C, originalRelationInclusion BL ≫ f = ψ :=
  arithmeticSourceClassHomCocycle_exists_scalar_relation_stage Ω a ha P B p hp2 hpa hB c

end ArithmeticSourceClassScalarStageConsumerAuxiliaryScope

noncomputable section ArithmeticSourceRelationDataValuesConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceDataRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceDataRegressionStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceDataRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Unfold the constructed data into the full original source-cocycle lift and finite-value contract. -/
theorem regression_arithmeticSourceClassRelationData_values
    [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      (∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom
          ((arithmeticSourceClassHomComparison ℚ Ω a ha (Rep.res π B)).hom (c.val g))) ∧
      ∃ N : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          letI : Module P N := Algebra.toModule
          letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
          letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
          let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
          ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha N,
            ∀ r, (coefficientRepresentationColimitOf _
              (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) N).hom (η.hom r) =
                φ.hom ((originalRelationGroupChange τ B).hom r) := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  refine ⟨r.lift, r.relation, r.relation_eq, r.lift_coboundary, r.stage, r.le_stage, ?_⟩
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := Algebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  exact ⟨r.finiteRelation, r.finiteRelation_values⟩

end ArithmeticSourceRelationDataValuesConsumerAuxiliaryScope

noncomputable section ArithmeticConstructedSourceCupConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceCupRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceCupRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceCupRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- An actual source cocycle constructs the relation data and the equality
of the literal cup and connecting maps; no relation witness is supplied. -/
theorem regression_arithmeticSourceClassCocycle_cup_relation [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∀ x : arithmeticSourceRelationContinuousH1 Ω a P B,
        arithmeticSourceRelationCupClass Ω a ha P B c x =
          arithmeticSourceRelationConnectingClass Ω a ha P B r.relation x := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  exact ⟨r, arithmeticSourceClassRelationData_cup_toAlgebraic Ω a ha P B c r⟩

end ArithmeticConstructedSourceCupConsumerAuxiliaryScope

noncomputable section ArithmeticSourceCupScalarStageConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceCupScalarRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceCupScalarRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceCupScalarRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The same constructed source relation gives the actual cup identity and the complete original scalar-stage criterion. -/
theorem regression_arithmeticSourceClassCocycle_cup_scalar_stage
    [Finite B]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      (∀ x : arithmeticSourceRelationContinuousH1 Ω a P B,
        arithmeticSourceRelationCupClass Ω a ha P B c x =
          arithmeticSourceRelationConnectingClass Ω a ha P B r.relation x) ∧
      ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : r.stage →ₐ[ℚ] F.val,
        (∀ x : r.stage, (i x : Ω) = (x.val : Ω)) ∧
        let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
          (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
        ∃ L : OriginalUnramifiedGaloisStage (Ω := Ω) a,
          ∃ hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField,
            letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
            letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
            let T := originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
              (originalIntegerMap_ne_zero (L := L.val) a ha)
            let hT := originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha
            let C := originalIdeleClassesModOutsideRep ℚ L.val T hT
            let BL := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(L.val/ℚ) →* Gal(F.val/ℚ)) BF
            ∃ d : OriginalRelationPrimePairingData BL C p,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha r.stage F i
                (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) L hFL
                  (arithmeticSourceClassRelationStageHom Ω a ha P B c r)
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(L.val/ℚ) BL ⟶ C, originalRelationInclusion BL ≫ f = ψ := by
  let h := arithmeticSourceClassHomCocycle_exists_scalar_relation_stage Ω a ha P B p hp2 hpa hB c
  let r := Classical.choose h
  exact ⟨r, arithmeticSourceClassRelationData_cup_toAlgebraic Ω a ha P B c r,
    Classical.choose_spec h⟩

end ArithmeticSourceCupScalarStageConsumerAuxiliaryScope

noncomputable section ArithmeticSourceFiniteObstructionConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceInflationRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceInflationRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceInflationRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original source cocycle constructs its own finite relation; the
finite obstruction has exactly the displayed global colimit image. -/
theorem regression_arithmeticSourceClassCocycle_finite_obstruction [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
      let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
      let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
        AlgEquiv.restrictNormalHom r.stage
      let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
      let j := coefficientRepresentationColimitOf _
        (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
      ∀ y : groupCohomology BN 1,
    groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y) =
      (groupCohomology.functor ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) 2).map
        ((Rep.resFunctor π).map η ≫ j)
        (groupCohomology.δ (originalRelationGroupChange_shortExact π BN) 1 2 rfl
          (groupCohomology.map π (𝟙 (Rep.res π BN)) 1 y)) := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  refine ⟨r, ?_⟩
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
  change ∀ y : groupCohomology BN 1,
    groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y) =
      (groupCohomology.functor ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) 2).map
        ((Rep.resFunctor π).map η ≫ j)
        (groupCohomology.δ (originalRelationGroupChange_shortExact π BN) 1 2 rfl
          (groupCohomology.map π (𝟙 (Rep.res π BN)) 1 y))
  intro y
  exact arithmeticFiniteRelationObstruction_inflation ℚ Ω a ha r.stage BN η y

end ArithmeticSourceFiniteObstructionConsumerAuxiliaryScope

noncomputable section ArithmeticConstructedSourceFiniteCupConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceFiniteCupRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceFiniteCupRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceFiniteCupRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source cocycle constructs the relation data used in the finite cup comparison. -/
theorem regression_arithmeticSourceClassCocycle_finite_obstruction_cup [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    : ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
    letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
    letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
    letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
    letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
    letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
      AlgEquiv.restrictNormalHom r.stage
    let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
    let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
    let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
    let j := coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
    ∀ y : groupCohomology BN 1,
      ∃ x : arithmeticSourceRelationContinuousH1 Ω a P B,
        arithmeticSourceRelationCupClass Ω a ha P B c x =
          groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y) := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  exact ⟨r, arithmeticSourceClassRelationData_finite_obstruction_cup Ω a ha P B c r⟩

end ArithmeticConstructedSourceFiniteCupConsumerAuxiliaryScope

noncomputable section ArithmeticSourceContinuousFiniteCupConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousFiniteRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousFiniteRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousFiniteRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original source cocycle constructs its relation and realizes every
finite algebraic H1 input with the same continuous cup and finite obstruction. -/
theorem regression_arithmeticSourceCocycle_every_finite_continuous_cup [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∀ y : groupCohomology (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) 1,
        ∃ v : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r,
          arithmeticSourceRelationStageH1ToAlgebraic Ω a ha P B c r v = y ∧
          arithmeticSourceRelationContinuousCupClass Ω a ha P B c
            (arithmeticSourceRelationFiniteContinuousH1Inflation Ω a ha P B c r v) =
            arithmeticSourceRelationFiniteContinuousObstruction Ω a ha P B c r v ∧
          arithmeticSourceRelationContinuousH2ToAlgebraic Ω a ha
            (arithmeticSourceRelationFiniteContinuousObstruction Ω a ha P B c r v) =
            arithmeticSourceRelationFiniteObstructionImage Ω a ha P B c r y := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  refine ⟨r, ?_⟩
  intro y
  obtain ⟨v, hv⟩ := arithmeticSourceRelationStageH1ToAlgebraic_surjective Ω a ha P B c r y
  refine ⟨v, hv, arithmeticSourceClassRelationData_finite_continuous_cup Ω a ha P B c r v, ?_⟩
  rw [arithmeticSourceRelationFiniteContinuousObstruction_toAlgebraic, hv]

end ArithmeticSourceContinuousFiniteCupConsumerAuxiliaryScope

noncomputable section ArithmeticSourceScalarContinuousCupConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarCupRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarCupRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarCupRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source cocycle constructs one enlarged scalar criterion
and realizes every one of its algebraic H1 inputs with the same original
continuous cup and literal algebraic obstruction image. -/
theorem regression_arithmeticSourceCocycle_scalar_criterion_continuous_cup
    [Finite B]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : r.stage →ₐ[ℚ] F.val,
        ∃ hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω),
        let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
          (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
        ∃ L : OriginalUnramifiedGaloisStage (Ω := Ω) a,
          ∃ hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField,
            r.stage ≤ originalUnramifiedStageInUnion a L ∧
            letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
            letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
            let T := originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
              (originalIntegerMap_ne_zero (L := L.val) a ha)
            let hT := originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha
            let C := originalIdeleClassesModOutsideRep ℚ L.val T hT
            let BL := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(L.val/ℚ) →* Gal(F.val/ℚ)) BF
            ∃ d : OriginalRelationPrimePairingData BL C p,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha r.stage F i
                (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) L hFL
                  (arithmeticSourceClassRelationStageHom Ω a ha P B c r)
              ((∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(L.val/ℚ) BL ⟶ C, originalRelationInclusion BL ≫ f = ψ) ∧
              ∀ y : groupCohomology BL 1,
                ∃ v : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL,
                  arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL v = y ∧
                  arithmeticSourceRelationContinuousCupClass Ω a ha P B c
                    (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi v) =
                    arithmeticSourceScalarContinuousObstruction Ω a ha P B c r F i L hFL v ∧
                  arithmeticSourceRelationContinuousH2ToAlgebraic Ω a ha
                    (arithmeticSourceScalarContinuousObstruction Ω a ha P B c r F i L hFL v) =
                    arithmeticSourceScalarObstructionImage Ω a ha P B c r F i L hFL y := by
  obtain ⟨r, F, i, hi, L, hFL, hle, d, hd⟩ :=
    arithmeticSourceClassHomCocycle_exists_scalar_stage_in_union Ω a ha P B p hp2 hpa hB c
  refine ⟨r, F, i, hi, L, hFL, hle, d, hd, ?_⟩
  intro y
  obtain ⟨v, hv⟩ := arithmeticSourceScalarStageH1ToAlgebraic_surjective Ω a ha P B c r F i L hFL y
  refine ⟨v, hv, arithmeticSourceClassRelationData_scalar_continuous_cup Ω a ha P B c r F i L hFL hi v, ?_⟩
  rw [arithmeticSourceScalarContinuousObstruction_toAlgebraic, hv]

end ArithmeticSourceScalarContinuousCupConsumerAuxiliaryScope

noncomputable section ArithmeticSourceScalarSylowClassConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceSylowClassRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceSylowClassRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceSylowClassRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source cocycle constructs its relation. At every
embedded and enlarged scalar stage, the same obstruction is detected by
a full-class element over an actual prime-power field
extension. No mixed-degree normalization premise is supplied. -/
theorem regression_arithmeticSourceCocycle_scalar_sylow_full_class [Finite B]
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∀ (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
        (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
        (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
        (S : Sylow p Gal(L.val/ℚ)),
          ∃ t : ℕ,
            Module.finrank (IntermediateField.fixedField (S : Subgroup Gal(L.val/ℚ))) L.val = p ^ t ∧
            ∀ y : groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1,
              let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
              let C := arithmeticOriginalStageClassRep Ω a ha L
              let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
              (originalRelationExtensionObstruction BL C ψ).hom y = 0 ↔
                arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S y = 0 := by
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  refine ⟨r, ?_⟩
  intro F i L hFL S
  obtain ⟨t, ht⟩ := originalScalarStage_sylow_fixedField_degree Ω a L p S
  refine ⟨t, ht, ?_⟩
  intro y
  exact arithmeticSourceScalarObstruction_eq_zero_iff_sylowClass Ω a ha P B c r F i L hFL p S hB y

end ArithmeticSourceScalarSylowClassConsumerAuxiliaryScope

noncomputable section ArithmeticSourceScalarNormalizedReadoutConsumerAuxiliaryScope
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceNormalizedReadoutRegressionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceNormalizedReadoutRegressionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceNormalizedReadoutRegressionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every actual source Hom cocycle constructs its relation; the original
scalar obstruction at every embedded enlarged stage is detected by the
proved canonical normalized class invariant of its realized Sylow class. -/
theorem regression_arithmeticSourceCocycle_scalar_normalized_readout [Finite B]
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne
      (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData (AlgebraicClosure ℚ) a ha P B c,
      ∀ (F : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a) (i : r.stage →ₐ[ℚ] F.val)
        (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
        (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
        (S : Sylow p Gal(L.val/ℚ))
        (y : groupCohomology
          (arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL) 1),
          let BL := arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL
          let C := arithmeticOriginalStageClassRep (AlgebraicClosure ℚ) a ha L
          let ψ := arithmeticSourceScalarStageRelationTransport (AlgebraicClosure ℚ) a ha P B c r F i L hFL
          (originalRelationExtensionObstruction BL C ψ).hom y = 0 ↔
            arithmeticSourceScalarNormalizedReadout a ha P B c r F i L hFL p hpa S y = 0 := by
  let r := Classical.choice
    (arithmeticSourceClassRelationData_nonempty (AlgebraicClosure ℚ) a ha P B c)
  refine ⟨r, ?_⟩
  intro F i L hFL S y
  exact arithmeticSourceScalarObstruction_eq_zero_iff_normalizedReadout
    a ha P B c r F i L hFL p hpa S hB y

end ArithmeticSourceScalarNormalizedReadoutConsumerAuxiliaryScope

noncomputable section ArithmeticNonNormalBaseChangeTotalConsumerAuxiliaryScope
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

/-- Inside the actual finite Galois upper field, every intermediate field
has the canonical total restriction formula. Its upper Galois structure is
derived, and its normality over the lower field is not a premise. -/
theorem regression_actual_arithmetic_intermediate_idele_total
    (a : 𝓞 ℚ) (K E M : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] [FiniteDimensional ℚ M]
    (hKE : K ≤ E) (hEM : E ≤ M)
    [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
      IsGalois K M] :
    ∃ hGalEM : (letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra; IsGalois E M),
      letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      ∀ x : rationalArithmeticRelativeStageIdeleH2 a K M (hKE.trans hEM),
        rationalArithmeticRelativeStageIdeleTotalInvariant (hGal := hGalEM) a E M hEM
          (rationalArithmeticRelativeStageIdeleBaseChange a K E M M hKE (hKE.trans hEM) hEM le_rfl x) =
        Module.finrank K E • rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM) x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois K M := hGalKM
  let hGalEM : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  exact ⟨hGalEM, fun x => rationalArithmeticRelativeStageIdeleBaseChange_total_in_galois_overfield
    (hGalKM := hGalKM) (hGalEM := hGalEM)
    a K E M hKE hEM x⟩

end ArithmeticNonNormalBaseChangeTotalConsumerAuxiliaryScope

end Dubon2026.SemanticRegression
