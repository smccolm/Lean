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

end Dubon2026.SemanticRegression
