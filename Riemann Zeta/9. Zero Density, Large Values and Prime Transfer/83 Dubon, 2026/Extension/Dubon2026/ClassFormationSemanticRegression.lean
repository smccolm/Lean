import Dubon2026
import Dubon2026.PrimeReciprocitySemanticRegression

/-! Exact original arithmetic source sequences and class-formation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology

section ExceptionalLocalization

open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)

/-- The actual exceptional local product has a perfect coherent trace pairing,
derived from local arithmetic duality rather than supplied as a premise. -/
theorem actual_exceptional_trace_pairing_perfect_source
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).IsPerfPair :=
  rationalArithmeticExceptionalTracePairing_isPerfPair a q hqa ha σ hσ hn

/-- The literal sum of original restricted trace cups is zero on the fixed prime set. -/
theorem actual_exceptional_restricted_trace_cup_sum_zero_source
    (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    (∑ p : ↥(rationalArithmeticExceptionalPrimes a ha),
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
          (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous y)) = 0 := by
  exact (rationalArithmeticExceptionalTracePairing_apply a q hqa ha σ hσ
    (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x)
    (rationalArithmeticTraceH1Localization a q ha σ hσ y)).symm.trans
    (rationalArithmeticExceptionalTracePairing_global_eq_zero a q hqa ha σ hσ hq2 x y)

/-- Reciprocity and actual perfectness give a dimension bound on the genuine global images. -/
theorem actual_exceptional_global_images_dimension_bound_source
    (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    Module.finrank (ZMod q) (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)) +
      Module.finrank (ZMod q)
        (LinearMap.range (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) ≤
      Module.finrank (ZMod q)
        ((p : ↥(rationalArithmeticExceptionalPrimes a ha)) →
          rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :=
  rationalArithmeticTraceLocalization_finrank_add_le a q hqa ha σ hσ hq2 hn

/-- The actual localization image lies in the kernel of evaluation against all global dual classes. -/
theorem actual_exceptional_global_localization_obstruction_source (hq2 : q ≠ 2) :
    LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ≤
      LinearMap.ker ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).flip.compl₂
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) :=
  rationalArithmeticTraceH1Localization_range_le_obstruction_ker a q hqa ha σ hσ hq2

end ExceptionalLocalization

section RealAndSUnitCoefficients

open scoped NumberField

/-- Actual odd-prime real restrictions vanish for both original trace coefficient systems. -/
theorem actual_real_trace_and_dual_H1_vanish_source
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (hσ : Continuous σ) (hq2 : q ≠ 2)
    (x : rationalArithmeticRealTraceH1Module a q σ hσ)
    (y : rationalArithmeticRealTraceDualH1Module a q hqa σ hσ) : x = 0 ∧ y = 0 :=
  ⟨rationalArithmeticRealTraceH1_eq_zero a q σ hσ hq2 x,
    rationalArithmeticRealTraceDualH1_eq_zero a q hqa σ hσ hq2 y⟩

/-- The actual all-place restriction becomes precisely the existing finite-prime map. -/
theorem actual_all_places_trace_localization_comparison_source
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (ha : a ≠ 0)
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (hσ : Continuous σ) (hq2 : q ≠ 2) (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticTraceAllPlacesEquiv a q σ hσ ha hq2
      (rationalArithmeticTraceAllPlacesLocalization a q σ hσ ha x) =
        rationalArithmeticTraceH1Localization a q ha σ hσ x :=
  rationalArithmeticTraceAllPlacesEquiv_localization a q σ hσ ha hq2 x

/-- Original localized-unit roots have literal original ramification indices one away from a. -/
theorem actual_localized_unit_root_original_prime_indices_source
    (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (u : (originalLocalizedIntegers K a ha)ˣ) (β : L)
    (hβ : β ^ q = algebraMap (originalLocalizedIntegers K a ha) L u.val)
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  originalLocalizedUnitKummer_unramifiedAway K a ha q L u β hβ hqa hgen

/-- Finite fields need no assumed normality to belong to the actual unramified Galois union. -/
theorem actual_finite_field_unramified_union_characterization_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω] [Normal K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (E : IntermediateField K Ω) [FiniteDimensional K E] :
    E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ↔
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
        algebraMap (𝓞 K) (𝓞 E) a ∉ w.asIdeal →
          (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  originalUnramifiedUnion_finite_le_iff a ha E

/-- Actual localized units have roots in the original arithmetic extension itself. -/
theorem actual_localized_unit_root_original_arithmetic_extension_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (u : (originalLocalizedIntegers K a ha)ˣ) :
    ∃ β : originalUnramifiedGaloisUnion (Ω := Ω) a,
      β ^ q = algebraMap K (originalUnramifiedGaloisUnion (Ω := Ω) a) u.val.val :=
  originalLocalizedUnit_exists_root_in_unramifiedUnion K Ω a ha q hqa u

/-- Original finite-stage roots stay in the original base arithmetic union. -/
theorem actual_finite_stage_unit_root_original_union_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
    (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (u : (originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha))ˣ)
    (β : Ω) (hβ : β ^ q = algebraMap E Ω u.val.val) :
    β ∈ originalUnramifiedGaloisUnion (Ω := Ω) a :=
  originalLocalizedFiniteStageUnit_root_mem_unramifiedUnion K Ω a ha q hqa E hE u β hβ

/-- The literal units of the original localized integral closure are q-divisible. -/
theorem actual_arithmetic_S_unit_power_surjective_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a) :
    Function.Surjective (fun u : (integralClosure (originalLocalizedIntegers K a ha)
      (originalUnramifiedGaloisUnion (Ω := Ω) a))ˣ => u ^ q) :=
  originalArithmeticSUnit_pow_surjective K Ω a ha q hqa

end RealAndSUnitCoefficients

section ActualSUnitHomAndExt

open scoped NumberField
open CategoryTheory CategoryTheory.Abelian
attribute [local instance 1100] Rep.hV2

/-- Actual arithmetic S-units carry the proved continuous discrete Galois action. -/
theorem actual_arithmetic_S_unit_action_continuous_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    (a : 𝓞 K) (ha : a ≠ 0)
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
      originalArithmeticSUnitRepresentation K Ω a ha =>
        (originalArithmeticSUnitRepresentation K Ω a ha).ρ z.1 z.2) :=
  originalArithmeticSUnitAction_continuous K Ω a ha

/-- Actual arithmetic roots and q-power on S-units form the proved short exact sequence. -/
theorem actual_arithmetic_S_unit_Kummer_shortExact_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a) :
    (originalArithmeticSUnitKummerShortComplex K Ω a ha q).ShortExact :=
  originalArithmeticSUnitKummerShortComplex_shortExact K Ω a ha q hqa

/-- The arithmetic root inclusion retains precisely the previously constructed field inclusion. -/
theorem actual_arithmetic_S_unit_root_inclusion_field_source
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] :
    (originalArithmeticSUnitInclusion K Ω a ha).hom.toLinearMap.comp
      (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap =
      (galoisKummerInclusion (K := K)
        (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q).hom.toLinearMap :=
  originalArithmeticSUnitKummerInclusion_field_comparison K Ω a ha q

/-- The actual trace dual evaluates to the original coherently normalized root inside S-units. -/
theorem actual_arithmetic_trace_S_unit_dual_evaluation_source
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (hqa : (q : 𝓞 ℚ) ∣ a) (hn : (Fintype.card ι : ZMod q) ≠ 0)
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X Y =
      (originalArithmeticSUnitKummerInclusion ℚ (AlgebraicClosure ℚ) a ha q).hom
        (rationalArithmeticRootCoefficientEquiv a q hqa (Matrix.trace (X.val * Y.val))) :=
  rationalArithmeticTraceSUnitDualEquiv_apply a ha q σ hqa hn X Y

/-- The actual twisted trace action agrees with the original conjugate action on S-unit Hom. -/
theorem actual_arithmetic_trace_S_unit_dual_action_source
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (hqa : (q : 𝓞 ℚ) ∣ a) (hn : (Fintype.card ι : ZMod q) ≠ 0)
    (g : rationalArithmeticGaloisGroup a) (X : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn
      (rationalArithmeticTraceZeroCyclotomicTwist a q hqa σ g X) =
      Representation.linHom (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
        (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha).ρ g
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X) :=
  rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn g X

/-- Every positive integer Ext from the original trace coefficients to the actual S-units vanishes. -/
theorem actual_arithmetic_trace_S_unit_positive_integer_Ext_source
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (n : ℕ)
    (x : Ext (ModuleCat.of ℤ (rationalArithmeticTraceZeroIntegerRep a q σ))
      (ModuleCat.of ℤ (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha))
      (n + 1)) : x = 0 :=
  rationalArithmeticTraceSUnit_integerExt_eq_zero a ha q hqa σ n x

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  [TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ)]

local instance arithmeticTraceSUnitConsumerContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticTraceSUnitHomRep a ha q σ)
      (rationalArithmeticTraceSUnitHomRep a ha q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Original global dual H1 cocycles map pointwise into the actual S-unit Hom cohomology. -/
theorem actual_arithmetic_trace_S_unit_H1_cocycle_source
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv _ _
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) c) :=
  rationalArithmeticTraceSUnitH1Equiv_mk a ha q σ hσ hqa hn c

/-- Original global dual H2 retains the same continuous cocycles and their actual coefficient images. -/
theorem actual_arithmetic_trace_S_unit_H2_cocycle_source
    (c : continuousRepresentationCocyclesTwo (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    rationalArithmeticTraceSUnitH2Equiv a ha q σ hσ hqa hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoAdditiveEquiv _ _
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) c) :=
  rationalArithmeticTraceSUnitH2Equiv_mk a ha q σ hσ hqa hn c

end ActualSUnitHomAndExt

section SUnitIdeleEntry
open IsDedekindDomain
open scoped NumberField

/-- The original localized ring is the valuation-defined ring at exactly the same exceptional integer. -/
theorem actual_localized_S_integer_ring_source
    (L : Type) [Field L] [NumberField L] (b : 𝓞 L) (hb : b ≠ 0) :
    originalLocalizedIntegers L b hb =
      ({w : HeightOneSpectrum (𝓞 L) | b ∈ w.asIdeal} : Set _).integer L :=
  originalLocalizedIntegers_eq_SIntegers L b hb

/-- The finite support is exactly the original exceptional prime set. -/
theorem actual_exceptional_S_unit_support_source
    (L : Type) [Field L] [NumberField L] (b : 𝓞 L) (hb : b ≠ 0)
    (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ originalExceptionalIntegerSupport L b hb ↔ b ∈ w.asIdeal :=
  mem_originalExceptionalIntegerSupport L b hb w

/-- The actual arithmetic units enter the actual source idele sequence at a finite Galois stage. -/
theorem actual_arithmetic_S_unit_source_idele_stage
    (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : NumberField F := NumberField.of_module_finite K F
      let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha)
      let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
      ∃ v : (S : Set (HeightOneSpectrum (𝓞 F))).unit F,
        F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
          algebraMap F Ω v.val.val = u.val.val.val ∧
          (originalSPlaceIdeleShortComplex K F S hS).ShortExact :=
  originalArithmeticSUnit_exists_sourceIdeleStage K Ω a ha u

/-- The original S-place diagonal has its actual finite completion value. -/
theorem actual_S_place_diagonal_finite_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    ((originalSPlacePrincipalRepHom K L S hS).hom x (Sum.inr v)).toMul.val =
      algebraMap L (v.val.adicCompletion L) x.toMul.val.val :=
  originalSPlacePrincipalRepHom_finite K L S hS x v

/-- The original S-place diagonal has its actual infinite completion value. -/
theorem actual_S_place_diagonal_infinite_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : NumberField.InfinitePlace L) :
    ((originalSPlacePrincipalRepHom K L S hS).hom x (Sum.inl v)).toMul.val =
      algebraMap L v.Completion x.toMul.val.val :=
  originalSPlacePrincipalRepHom_infinite K L S hS x v

/-- The original fixed-support source class sequence is short exact. -/
theorem actual_exceptional_S_place_shortExact_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (a : 𝓞 K) (ha : a ≠ 0) :
    (originalSPlaceIdeleShortComplex K L
      (originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha))
      (originalExceptionalIntegerSupport_galoisStable L K a ha)).ShortExact :=
  originalSPlaceIdeleShortComplex_shortExact K L _ _

/-- The original S-place class comparison preserves the literal idele representative. -/
theorem actual_S_place_class_comparison_representative_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (x : supportedUnrestrictedUnitRep K L S hS) :
    (originalSPlaceClassComparison K L S hS).hom
      ((originalSPlaceIdeleClassRepHom K L S hS).hom x) =
        (originalSPlaceToClassesModOutside K L S hS).hom x :=
  originalSPlaceClassComparison_mk K L S hS x

/-- The actual class comparison is injective at exactly the original exceptional support. -/
theorem actual_exceptional_S_place_class_comparison_injective_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (a : 𝓞 K) (ha : a ≠ 0) :
    Function.Injective (originalSPlaceClassComparison K L
      (originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha))
      (originalExceptionalIntegerSupport_galoisStable L K a ha)).hom :=
  originalSPlaceClassComparison_injective K L _ _

/-- The principal square commutes at the original exceptional supports without a supplied support condition. -/
theorem actual_exceptional_S_unit_idele_transition_source
    (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (a : 𝓞 K) (ha : a ≠ 0)
    (x : (↑(originalExceptionalIntegerSupport K a ha) : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    originalExceptionalSupportedIdeleBaseChange K L a ha
      (numberFieldSupportedPrincipalIdele K _ x) =
        numberFieldSupportedPrincipalIdele L _ (originalExceptionalSUnitBaseChange K L a ha x) :=
  originalExceptionalSupportedIdeleBaseChange_principal K L a ha x

/-- The original localized and valuation-defined transitions carry the same actual unit. -/
theorem actual_exceptional_localized_unit_transition_source
    (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (a : 𝓞 K) (ha : a ≠ 0) (u : (originalLocalizedIntegers K a ha)ˣ) :
    originalExceptionalSUnitBaseChange K L a ha
      (originalLocalizedUnitsEquivSupportedSUnits K a ha u) =
        originalLocalizedUnitsEquivSupportedSUnits L (algebraMap (𝓞 K) (𝓞 L) a)
          (originalIntegerMap_ne_zero (L := L) a ha)
          (Units.map (originalLocalizedIntegersMap (L := L) a ha).toMonoidHom u) :=
  originalExceptionalSUnitBaseChange_localized K L a ha u

end SUnitIdeleEntry

section ArithmeticSUnitH2Colimit
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

/-- Every original arithmetic H2 class has a representative in the same finite S-unit coefficient that enters the fixed-support source idele sequence. -/
theorem actual_arithmetic_S_unit_H2_finite_source_sequence
    (x : ArithmeticSUnitContinuousH2 K Ω a ha) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      letI : NumberField F := NumberField.of_module_finite K F
      ∃ y : ArithmeticSUnitH2Stage K Ω a ha F,
        arithmeticSUnitH2StageMap K Ω a ha F y = x ∧
          (originalSPlaceIdeleShortComplex K F (arithmeticSUnitFiniteStageSupport K Ω a ha F)
            (originalExceptionalIntegerSupport_galoisStable F K a ha)).ShortExact := by
  have h := arithmeticSUnitContinuousH2_exists_finiteStage K Ω a ha x
  let F := h.choose
  letI : NumberField F := NumberField.of_module_finite K F
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  exact ⟨F, h.choose_spec.choose, h.choose_spec.choose_spec,
    originalSPlaceIdeleShortComplex_shortExact K F _ _⟩

/-- A globally vanishing original S-unit class becomes an actual finite-stage coboundary after a genuine finite extension. -/
theorem actual_arithmetic_S_unit_H2_zero_stage_source
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSUnitH2Stage K Ω a ha E)
    (hx : arithmeticSUnitH2StageMap K Ω a ha E x = 0) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEF : E ≤ F, arithmeticSUnitH2Transition K Ω a ha E F hEF x = 0 := by
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E) := ⟨rfl⟩
  exact arithmeticSUnitContinuousH2_zero_detected_at_finiteStage K Ω a ha E x hx

/-- The actual continuous one-cochain witness retains all original S-unit values after descent above any prescribed field. -/
theorem actual_arithmetic_S_unit_cochain_descent_source
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (b : C(Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
      originalArithmeticSUnitRepresentation K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a), E ≤ F ∧
      ∃ f : Gal(F/K) → (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
        Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F,
        ∀ g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
          arithmeticSUnitFiniteStageUnitMap K Ω a ha F (f (AlgEquiv.restrictNormalHom F g)) =
            (b g).toMul :=
  arithmeticSUnitCochain_exists_finite_descent K Ω a ha E b

omit [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)] in
/-- The finite coefficient inclusion has exactly the original field value. -/
theorem actual_arithmetic_S_unit_finite_inclusion_source
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F) :
    (arithmeticSUnitFiniteStageUnitMap K Ω a ha F u).val.val =
      algebraMap F (originalUnramifiedGaloisUnion (Ω := Ω) a) u.val.val :=
  arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F u

omit [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)] in
/-- The coefficient transition uses precisely the inclusion of the same original finite fields. -/
theorem actual_arithmetic_S_unit_transition_value_source
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F)
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF u).val.val = algebraMap E F u.val.val :=
  arithmeticSUnitFiniteTransitionMap_coe K Ω a ha E F hEF u

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Every original continuous arithmetic S-unit H2 class has exactly one class in the actual finite-stage colimit. -/
theorem actual_arithmetic_S_unit_H2_colimit_source
    (x : ArithmeticSUnitContinuousH2 K Ω a ha) :
    ∃! y : ArithmeticSUnitH2FiniteColimit K Ω a ha,
      arithmeticSUnitH2FiniteColimitToH2 K Ω a ha y = x := by
  obtain ⟨y, hy⟩ := arithmeticSUnitH2FiniteColimitToH2_surjective K Ω a ha x
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact arithmeticSUnitH2FiniteColimitToH2_injective K Ω a ha (hz.trans hy.symm)

/-- The proved colimit equivalence sends a finite-stage class to its literal original inflation. -/
theorem actual_arithmetic_S_unit_H2_colimit_representative_source
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSUnitH2Stage K Ω a ha F) :
    arithmeticSUnitH2FiniteColimitEquiv K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (ArithmeticSUnitH2Stage K Ω a ha) (arithmeticSUnitH2Transition K Ω a ha) F x) =
      arithmeticSUnitH2StageMap K Ω a ha F x :=
  arithmeticSUnitH2FiniteColimitEquiv_of K Ω a ha F x

/-- The actual global comparison kills exactly zero in the proved arithmetic colimit. -/
theorem actual_arithmetic_S_unit_H2_colimit_zero_source
    (x : ArithmeticSUnitH2FiniteColimit K Ω a ha) :
    arithmeticSUnitH2FiniteColimitToH2 K Ω a ha x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact arithmeticSUnitH2FiniteColimitToH2_injective K Ω a ha
      (hx.trans (map_zero (arithmeticSUnitH2FiniteColimitToH2 K Ω a ha)).symm)
  · rintro rfl
    exact map_zero _

end ArithmeticSUnitH2Colimit

section ArithmeticSourceColimitSequence
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Actual arithmetic source coefficients have a short exact sequence and continuous actions on both original source colimits. -/
theorem actual_arithmetic_source_colimit_sequence
    [TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha)]
    [TopologicalSpace (arithmeticSPlaceClassColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticSPlaceClassColimitRep K Ω a ha)] :
    (arithmeticSourceIdeleShortComplex K Ω a ha).ShortExact ∧
      Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
          arithmeticSPlaceColimitRep K Ω a ha =>
        (arithmeticSPlaceColimitRep K Ω a ha).ρ z.1 z.2) ∧
      Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
          arithmeticSPlaceClassColimitRep K Ω a ha =>
        (arithmeticSPlaceClassColimitRep K Ω a ha).ρ z.1 z.2) :=
  ⟨arithmeticSourceIdeleShortComplex_shortExact K Ω a ha,
    arithmeticSPlaceColimitAction_continuous K Ω a ha,
    arithmeticSPlaceClassColimitAction_continuous K Ω a ha⟩

/-- Every original arithmetic S-unit has a finite representative whose original local diagonal is its global source diagonal. -/
theorem actual_arithmetic_source_diagonal_finite_representative
    (u : originalArithmeticSUnitRepresentation K Ω a ha) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ x : arithmeticSUnitFiniteStageRep K Ω a ha F,
        (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom x = u ∧
          (arithmeticSourcePrincipalRepHom K Ω a ha).hom u =
            Module.DirectLimit.of ℤ
              (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
              (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
              (arithmeticSPlaceTransitionMap K Ω a ha) F
                ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom x) := by
  obtain ⟨F, x, rfl⟩ := arithmeticSUnitCoefficient_exists_finiteStage K Ω a ha u
  exact ⟨F, x, rfl, arithmeticSourcePrincipal_finiteStage K Ω a ha F x⟩

/-- Vanishing in the original source class colimit supplies an actual arithmetic S-unit diagonal preimage. -/
theorem actual_arithmetic_source_class_kernel_original_S_unit
    (x : arithmeticSPlaceColimitRep K Ω a ha)
    (hx : (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom x = 0) :
    ∃ u : originalArithmeticSUnitRepresentation K Ω a ha,
      (arithmeticSourcePrincipalRepHom K Ω a ha).hom u = x := by
  have hx' : x ∈ LinearMap.ker (arithmeticSPlaceColimitQuotient K Ω a ha) := hx
  rw [← arithmeticSPlaceColimit_range_eq_ker K Ω a ha] at hx'
  obtain ⟨y, hy⟩ := hx'
  refine ⟨arithmeticSUnitCoefficientColimitToGlobal K Ω a ha y, ?_⟩
  have h := congrArg (fun v : arithmeticSUnitCoefficientColimitRep K Ω a ha ⟶
      arithmeticSPlaceColimitRep K Ω a ha => v.hom y)
    (arithmeticSourcePrincipal_from_colimit K Ω a ha)
  exact h.trans hy

/-- The literal source diagonal is injective for the original arithmetic coefficients. -/
theorem actual_arithmetic_source_original_diagonal_injective :
    Function.Injective (arithmeticSourcePrincipalRepHom K Ω a ha).hom := by
  haveI := (arithmeticSourceIdeleShortComplex_shortExact K Ω a ha).mono_f
  exact (Rep.mono_iff_injective (arithmeticSourceIdeleShortComplex K Ω a ha).f).mp inferInstance

/-- Original source class coefficients all have actual source idele representatives. -/
theorem actual_arithmetic_source_class_has_idele_representative
    (c : arithmeticSPlaceClassColimitRep K Ω a ha) :
    ∃ j : arithmeticSPlaceColimitRep K Ω a ha,
      (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom j = c :=
  arithmeticSPlaceColimitQuotient_surjective K Ω a ha c

/-- Actual arithmetic continuous S-unit H2 descends in the same ES coefficient that begins the original global source sequence. -/
theorem actual_arithmetic_H2_and_original_source_sequence
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]
    (x : ArithmeticSUnitContinuousH2 K Ω a ha) :
    (arithmeticSourceIdeleShortComplex K Ω a ha).ShortExact ∧
      ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ y : ArithmeticSUnitH2Stage K Ω a ha F, arithmeticSUnitH2StageMap K Ω a ha F y = x := by
  refine ⟨arithmeticSourceIdeleShortComplex_shortExact K Ω a ha, ?_⟩
  have h := arithmeticSUnitContinuousH2_exists_finiteStage K Ω a ha x
  let F := h.choose
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  exact ⟨F, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end ArithmeticSourceColimitSequence

section ArithmeticTraceSourceHom
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

include hqa in
/-- The actual trace-zero adjoint has the original arithmetic source Hom short exact sequence, with the integer Ext obstruction discharged. -/
theorem actual_rational_trace_source_Hom_shortExact :
    (arithmeticSourceHomShortComplex ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).ShortExact := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.instIsAlgClosure ℚ
    rw [hAlg] at h
    exact h
  letI : Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
    inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))
  exact arithmeticSourceHomShortComplex_shortExact ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) q hqa

include hqa in
/-- Every actual trace-zero source-class Hom has an original source-idele Hom preimage under the literal quotient. -/
theorem actual_rational_trace_source_class_Hom_lift
    (f : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      arithmeticSPlaceClassColimitRep ℚ (AlgebraicClosure ℚ) a ha) :
    ∃ g : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
        arithmeticSPlaceColimitRep ℚ (AlgebraicClosure ℚ) a ha,
      (arithmeticSPlaceColimitQuotientRepHom ℚ (AlgebraicClosure ℚ) a ha).hom.toLinearMap.comp g = f := by
  have hS := actual_rational_trace_source_Hom_shortExact a ha q hqa σ
  exact (Rep.epi_iff_surjective _).mp hS.epi_g f

end ArithmeticTraceSourceHom

section ArithmeticSourceHomContinuousSequence
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

local instance : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

/-- The exact consumer retains the original prime-field trace-module scalars. -/
local instance : Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))
local instance : Finite (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
/-- The exact consumer uses the original finite trace-module topology. -/
local instance : TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficientTopology a q σ
local instance : DiscreteTopology (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficient_discrete a q σ

variable [TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]

/-- The identified source coefficient uses the original S-unit Hom topology. -/
local instance : TopologicalSpace (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)) :=
  inferInstanceAs (TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ))
local instance : DiscreteTopology (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)) :=
  inferInstanceAs (DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ))

local instance : @ContinuousSMul ℤ (rationalArithmeticTraceSUnitHomRep a ha q σ)
    (rationalArithmeticTraceSUnitHomRep a ha q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

local instance : @ContinuousSMul ℤ
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual trace-dual class killed by the original source idele map has its original invariant source-class connecting representative. -/
theorem actual_trace_dual_source_idele_kernel
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ)
    (hx : rationalTraceSourceIdeleH1Map a ha q σ hσ hqa hn x = 0) :
    ∃ c : (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ)).ρ.invariants,
      arithmeticSourceHomInvariantConnectingMap ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c =
          rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn x :=
  (rationalTraceSourceIdeleH1Map_eq_zero_iff a ha q σ hσ hqa hn x).mp hx

/-- An original invariant source-class Hom coefficient gives an actual global trace-dual class killed by the same source idele map. -/
theorem actual_invariant_source_class_trace_dual_zero
    (c : (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).ρ.invariants) :
    rationalTraceSourceIdeleH1Map a ha q σ hσ hqa hn
      ((rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn).symm
        (arithmeticSourceHomInvariantConnectingMap ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ)
          (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c)) = 0 := by
  apply (rationalTraceSourceIdeleH1Map_eq_zero_iff a ha q σ hσ hqa hn _).mpr
  exact ⟨c, ((rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn).apply_symm_apply _).symm⟩

variable [TopologicalSpace (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]

local instance : @ContinuousSMul ℤ
    (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ
    (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

include hqa in
/-- A source-idele Hom H2 class with zero actual class image lifts to the original arithmetic S-unit Hom H2. -/
theorem actual_trace_source_idele_H2_kernel_lift
    (y : ContinuousRepresentationH2
      (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ))
      (arithmeticSourceIdeleHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)))
    (hy : arithmeticSourceHomH2Quotient ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) y = 0) :
    ∃ x : ContinuousRepresentationH2
        (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticSourceSUnitHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)),
      arithmeticSourceHomH2Inclusion ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) x = y := by
  have hy' : y ∈ LinearMap.ker (arithmeticSourceHomH2Quotient ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)) := hy
  rw [← arithmeticSourceHomH2_range_eq_ker ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa] at hy'
  exact hy'

/-- An actual S-unit Hom H2 class killed by the original source diagonal is the connecting image of an original source-class Hom H1 class. -/
theorem actual_trace_source_S_unit_H2_connecting_lift
    (x : ContinuousRepresentationH2
      (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ))
      (arithmeticSourceSUnitHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)))
    (hx : arithmeticSourceHomH2Inclusion ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) x = 0) :
    ∃ c : ContinuousRepresentationH1
        (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticSourceClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)),
      arithmeticSourceHomConnectingMap ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c = x := by
  have hx' : x ∈ LinearMap.ker (arithmeticSourceHomH2Inclusion ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)) := hx
  rw [← arithmeticSourceHomConnecting_H2_range_eq_ker ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa] at hx'
  exact hx'

end ArithmeticSourceHomContinuousSequence

section ArithmeticOriginalFullClassComparison
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- An original source idele vanishing in the actual full-class quotient colimit is an original arithmetic S-unit diagonal. -/
theorem actual_full_class_zero_has_original_S_unit
    (x : arithmeticSPlaceColimitRep K Ω a ha)
    (hx : (arithmeticSourceClassColimitComparison K Ω a ha).hom
      ((arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom x) = 0) :
    ∃ u : originalArithmeticSUnitRepresentation K Ω a ha,
      (arithmeticSourcePrincipalRepHom K Ω a ha).hom u = x := by
  apply actual_arithmetic_source_class_kernel_original_S_unit K Ω a ha x
  exact arithmeticSourceClassColimitComparison_injective K Ω a ha
    (hx.trans (map_zero (arithmeticSourceClassColimitComparison K Ω a ha).hom).symm)

/-- The original source class finite representative has its literal image in the continuous full-class quotient colimit. -/
theorem actual_full_class_comparison_original_representative
    [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceFiniteStageRep K Ω a ha F) :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticClassesModOutsideColimitRep K Ω a ha =>
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ z.1 z.2) ∧
    (arithmeticSourceClassColimitComparison K Ω a ha).hom
      ((coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) F).hom
        ((arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom x)) =
      (coefficientRepresentationColimitOf _ (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
        ((arithmeticSourceClassStageComparison K Ω a ha F).hom
          ((arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom x)) :=
  ⟨arithmeticClassesModOutsideColimitAction_continuous K Ω a ha,
    arithmeticSourceClassColimitComparison_of K Ω a ha F _⟩

end ArithmeticOriginalFullClassComparison

noncomputable section ArithmeticPrimeClassHom
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- An actual prime-torsion full-class colimit element has a unique original source class at the same support. -/
theorem actual_arithmetic_prime_torsion_full_class_lift
    (x : arithmeticClassesModOutsideColimitRep K Ω a ha) (hx : q • x = 0) :
    ∃! c : arithmeticSPlaceClassColimitRep K Ω a ha,
      (arithmeticSourceClassColimitComparison K Ω a ha).hom c = x := by
  obtain ⟨c, hc⟩ := arithmeticTorsionClassColimit_exists_source K Ω a ha q hqa x hx
  refine ⟨c, hc, fun y hy => ?_⟩
  exact arithmeticSourceClassColimitComparison_injective K Ω a ha (hy.trans hc.symm)

end ArithmeticPrimeClassHom

noncomputable section RationalTracePrimeClassHom
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance1 : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

/-- The trace coefficient retains its original prime-field scalar multiplication. -/
local instance originalClassConsumerGroup1Instance2 : Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))

include hqa in
/-- Every actual trace-zero Hom coefficient in the full-class quotient has exactly one original source-class Hom lift. -/
theorem actual_trace_full_class_Hom_unique_source
    (f : arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)) :
    ∃! g : arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ),
      (arithmeticSourceClassHomComparison ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ)).hom g = f := by
  obtain ⟨g, hg⟩ := arithmeticSourceClassHomComparison_surjective ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) q hqa f
  refine ⟨g, hg, fun k hk => ?_⟩
  exact arithmeticSourceClassHomComparison_injective ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (hk.trans hg.symm)

/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance3 : Finite (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
/-- The coefficient retains the topology of its original finite trace module. -/
local instance originalClassConsumerGroup1Instance4 : TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficientTopology a q σ
/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance5 : DiscreteTopology (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficient_discrete a q σ

variable (hσ : Continuous σ)
  [TopologicalSpace (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [TopologicalSpace (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]

/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance6 : @ContinuousSMul ℤ
    (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance7 : @ContinuousSMul ℤ
    (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original full-class trace Hom H1 class lifts through the proved continuous original source comparison. -/
theorem actual_trace_full_class_H1_source
    (x : ContinuousRepresentationH1
      (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
      (arithmeticFullClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ))) :
    ∃ c : ContinuousRepresentationH1
        (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticSourceClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)),
      arithmeticSourceClassHomH1Equiv ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c = x :=
  (arithmeticSourceClassHomH1Equiv ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa).surjective x

/-- The same actual trace Hom H2 class lifts through the original pointwise coefficient comparison. -/
theorem actual_trace_full_class_H2_source
    (x : ContinuousRepresentationH2
      (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
      (arithmeticFullClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ))) :
    ∃ c : ContinuousRepresentationH2
        (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticSourceClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)),
      arithmeticSourceClassHomH2Equiv ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c = x :=
  (arithmeticSourceClassHomH2Equiv ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa).surjective x

variable [TopologicalSpace (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [TopologicalSpace (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]

/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance8 : @ContinuousSMul ℤ
    (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup1Instance9 : @ContinuousSMul ℤ
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

include hqa in
/-- An actual trace S-unit Hom H2 class killed in source ideles comes from the original full-class quotient Hom connecting map. -/
theorem actual_trace_full_class_connecting_lift
    (x : ContinuousRepresentationH2
      (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
      (arithmeticSourceSUnitHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)))
    (hx : arithmeticSourceHomH2Inclusion ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) x = 0) :
    ∃ c : ContinuousRepresentationH1
        (arithmeticFullClassHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticFullClassHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)),
      arithmeticFullClassHomConnectingMap ℚ (AlgebraicClosure ℚ) a ha
        (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c = x := by
  have h : x ∈ (arithmeticSourceHomH2Inclusion ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalTraceIntegerAction_continuous a q σ hσ)).toAddMonoidHom.ker := hx
  rw [← arithmeticFullClassHomConnecting_H2_range_eq_ker ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ) q hqa] at h
  exact h

end RationalTracePrimeClassHom

noncomputable section OriginalArithmeticClassFormationInputs
open CategoryTheory
open scoped NumberField

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance originalClassConsumerGroup2Instance1 : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance originalClassConsumerGroup2Instance2 : Algebra ℚ F := F.algebra'
/-- The original finite arithmetic extension is a number field. -/
local instance originalClassConsumerGroup2Instance3 : NumberField F := NumberField.of_module_finite ℚ F

/-- An actual H1 class in the original arithmetic full-class quotient is zero. -/
theorem actual_arithmetic_class_quotient_H1_zero
    (x : groupCohomology
      (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F) 1) : x = 0 := by
  haveI := ModuleCat.isZero_iff_subsingleton.mp
    (rationalArithmeticClassesModOutsideStage_first_zero (AlgebraicClosure ℚ) a ha F)
  exact Subsingleton.elim _ _

/-- The actual cyclic arithmetic quotient H2 has the exact field-degree order and unique original full-class lifts. -/
theorem actual_arithmetic_class_quotient_cyclic_H2 [IsCyclic Gal(F/ℚ)]
    (x : groupCohomology
      (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F) 2) :
    Nat.card (groupCohomology
      (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F) 2) =
        Module.finrank ℚ F ∧
    ∃! y : groupCohomology (originalIdeleClassRep ℚ F) 2,
      (groupCohomology.functor ℤ Gal(F/ℚ) 2).map
        (originalIdeleClassesModOutsideRepHom ℚ F
          (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
          (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)) y = x :=
  ⟨(rationalArithmeticClassesModOutsideStage_cyclic_second_card
      (AlgebraicClosure ℚ) a ha F).2,
    rationalArithmeticClassesModOutsideStage_H2_unique_lift (AlgebraicClosure ℚ) a ha F x⟩

end OriginalArithmeticClassFormationInputs

noncomputable section OriginalArithmeticClassContinuousH1
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The consumer uses the original rational algebra structure on the arithmetic union. -/
local instance originalClassConsumerGroup3Instance1 : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]

/-- The exact arithmetic consumer uses the original coefficient structure. -/
local instance originalClassConsumerGroup3Instance2 : @ContinuousSMul ℤ
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).hV2.toSMul
    inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩

/-- An original arithmetic class-colimit cocycle has an actual coefficient witness for its coboundary. -/
theorem actual_arithmetic_class_colimit_cocycle_coboundary
    (c : continuousRepresentationCocyclesOne
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)) :
    ∃ v : arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha,
      ∀ g : Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ),
        (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).ρ g v - v = c.val g :=
  rationalArithmeticClassOneCocycle_exists_coboundary (AlgebraicClosure ℚ) a ha c

/-- Every actual continuous H1 class of the original arithmetic class quotient vanishes. -/
theorem actual_arithmetic_class_colimit_H1_zero
    (x : ContinuousRepresentationH1
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)
      (arithmeticClassesModOutsideColimitAction_continuous ℚ (AlgebraicClosure ℚ) a ha)) : x = 0 :=
  rationalArithmeticClassesModOutsideContinuousH1_eq_zero (AlgebraicClosure ℚ) a ha x

end OriginalArithmeticClassContinuousH1

noncomputable section OriginalArithmeticClassQuotientInvariants
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union carries its literal rational inclusion in these consumers. -/
local instance originalClassConsumerGroup4Instance1 : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

/-- An invariant original finite arithmetic class has a unique base-field quotient class, with the original exceptional support. -/
theorem actual_arithmetic_finite_class_invariant_unique_base
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))
    (x : (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F).ρ.invariants) :
    ∃! c : rationalArithmeticBaseClassQuotient a ha,
      rationalArithmeticClassQuotientInvariantEquiv a ha (AlgebraicClosure ℚ) F c = x :=
  rationalArithmeticClassQuotientInvariant_unique_base a ha (AlgebraicClosure ℚ) F x

/-- The original finite class quotient embeds injectively into the actual arithmetic colimit. -/
theorem actual_arithmetic_class_stage_embedding
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a)) :
    Function.Injective (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ (AlgebraicClosure ℚ) a ha) F).hom :=
  arithmeticClassesModOutsideColimitOf_injective ℚ (AlgebraicClosure ℚ) a ha F

/-- Every original arithmetic invariant class-colimit coefficient has a unique genuine rational base quotient preimage. -/
theorem actual_arithmetic_class_colimit_invariant_unique_base
    (x : (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).ρ.invariants) :
    ∃! c : rationalArithmeticBaseClassQuotient a ha,
      rationalArithmeticBaseClassToColimitInvariants a ha (AlgebraicClosure ℚ) c = x :=
  (rationalArithmeticBaseClassToColimitInvariants_bijective a ha
    (AlgebraicClosure ℚ)).existsUnique x

end OriginalArithmeticClassQuotientInvariants

noncomputable section OriginalArithmeticOpenSubgroupClassH1
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original rational arithmetic union has its literal rational algebra. -/
local instance openClassConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'
/-- The actual arithmetic class coefficient has its discrete topology. -/
local instance openClassConsumerTopology :
    TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) := ⊥
/-- The original class coefficient topology is discrete. -/
local instance openClassConsumerDiscrete :
    DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) := ⟨rfl⟩
/-- The original discrete arithmetic class coefficient has continuous scalar multiplication. -/
local instance openClassConsumerSMul : @ContinuousSMul ℤ
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).hV2.toSMul
    inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩
/-- Each actual open arithmetic subgroup has its induced topological group structure. -/
local instance openClassConsumerGroup
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ)) :
    IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- Every cocycle on every actual open arithmetic subgroup is an original class-coefficient coboundary. -/
theorem actual_arithmetic_open_class_cocycle_coboundary
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) H.toSubgroup.subtype)) :
    ∃ v : arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha,
      ∀ g : H, (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).ρ g.val v - v = c.val g :=
  rationalArithmeticOpenSubgroupClassOneCocycle_exists_coboundary (AlgebraicClosure ℚ) a ha H c

/-- The original continuous class-quotient H1 vanishes on every actual open arithmetic subgroup. -/
theorem actual_arithmetic_open_class_H1_zero
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) H.toSubgroup.subtype)
      (restrictedCoefficientAction_continuous _ H.toSubgroup.subtype continuous_subtype_val
        (arithmeticClassesModOutsideColimitAction_continuous ℚ (AlgebraicClosure ℚ) a ha))) : x = 0 :=
  rationalArithmeticOpenSubgroupClassesModOutsideH1_eq_zero (AlgebraicClosure ℚ) a ha H x

end OriginalArithmeticOpenSubgroupClassH1

noncomputable section OriginalArithmeticNormalClassInvariants
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The actual arithmetic union uses its literal rational inclusion. -/
local instance normalClassConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))

/-- The actual finite Galois stage uses its literal rational inclusion. -/
local instance normalClassConsumerStageAlgebra : Algebra ℚ F := F.algebra'

variable (H : Subgroup Gal(F/ℚ)) [H.Normal]

/-- Every original normal invariant class coefficient has a unique actual fixed-field quotient representative. -/
theorem actual_arithmetic_normal_class_unique_base
    (x : (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F).quotientToInvariants H) :
    ∃! y : rationalArithmeticNormalClassRep (AlgebraicClosure ℚ) a ha F H,
      (rationalArithmeticClassNormalInvariantCoefficientIso (AlgebraicClosure ℚ) a ha F H).hom.hom y = x :=
  (Representation.equivOfIso
    (rationalArithmeticClassNormalInvariantCoefficientIso (AlgebraicClosure ℚ) a ha F H)).toLinearEquiv.bijective.existsUnique x

/-- Every original normal invariant H2 class has a unique actual fixed-field class-quotient H2 preimage. -/
theorem actual_arithmetic_normal_class_H2_unique_base
    (x : groupCohomology
      ((arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F).quotientToInvariants H) 2) :
    ∃! y : groupCohomology (rationalArithmeticNormalClassRep (AlgebraicClosure ℚ) a ha F H) 2,
      (rationalArithmeticClassNormalInvariantH2Iso (AlgebraicClosure ℚ) a ha F H).hom y = x :=
  (rationalArithmeticClassNormalInvariantH2Iso (AlgebraicClosure ℚ) a ha F H).toLinearEquiv.bijective.existsUnique x

end OriginalArithmeticNormalClassInvariants

noncomputable section OriginalArithmeticPrimePowerDegrees
open scoped NumberField

/-- Every selected prime power occurs in the degree of an actual finite Galois stage at the unchanged support. -/
theorem actual_arithmetic_primePower_degree_dvd
    (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (n : ℕ) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a),
      q ^ n ∣ Module.finrank ℚ F :=
  rationalArithmetic_exists_primePower_degree_dvd (AlgebraicClosure ℚ) a q hqa n

end OriginalArithmeticPrimePowerDegrees

noncomputable section OriginalArithmeticOpenSubgroupClassH2
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union carries its literal rational algebra. -/
local instance openClassH2ConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'
/-- Each actual finite Galois stage carries its original rational algebra. -/
local instance openClassH2ConsumerStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a)) :
    Algebra ℚ F := F.algebra'

/-- The actual arithmetic class coefficient has the discrete topology. -/
local instance openClassH2ConsumerTopology :
    TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) := ⊥
/-- The original class coefficient topology is discrete. -/
local instance openClassH2ConsumerDiscrete :
    DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) := ⟨rfl⟩
/-- The actual discrete arithmetic class coefficient has continuous scalar multiplication. -/
local instance openClassH2ConsumerSMul : @ContinuousSMul ℤ
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).hV2.toSMul
    inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩

/-- Every actual continuous class two-cocycle on an original open arithmetic subgroup has a literal finite-image representative with the same coefficient values. -/
theorem actual_arithmetic_open_class_two_cocycle_finite_descent
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) H.toSubgroup.subtype)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a),
      let π : H →* Gal(F/ℚ) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : groupCohomology.cocycles₂
        (Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F)),
        ∀ g h : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha)
          (arithmeticGlobalClassesModOutsideStageTransition ℚ (AlgebraicClosure ℚ) a ha) F).hom
            (d (π.rangeRestrict g, π.rangeRestrict h)) = c.val (g, h) :=
  arithmeticOpenSubgroupClassTwoCocycle_exists_finite_descent ℚ (AlgebraicClosure ℚ) a ha H
    (fun z => c.val z) c.property ((groupCohomology.mem_cocycles₂_iff _).mp c.val.property)

/-- Every actual continuous class coboundary cochain descends above the prescribed original coefficient stage. -/
theorem actual_arithmetic_open_class_cochain_finite_descent
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))
    (c : C(H, arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a), E ≤ F ∧
      let π : H →* Gal(F/ℚ) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : π.range → arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F,
        ∀ g : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha)
          (arithmeticGlobalClassesModOutsideStageTransition ℚ (AlgebraicClosure ℚ) a ha) F).hom
            (d (π.rangeRestrict g)) = c g :=
  arithmeticOpenSubgroupClassCochain_exists_finite_descent ℚ (AlgebraicClosure ℚ) a ha H E c

/-- The original open arithmetic subgroup has its induced topological group structure. -/
local instance openClassH2ConsumerGroup
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ)) :
    IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- Zero in actual continuous class H2 yields a finite arithmetic coboundary witness for its original stage representative. -/
theorem actual_arithmetic_open_class_H2_zero_finite_witness
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))
    (u : H × H → arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha E)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) H.toSubgroup.subtype))
    (hu : ∀ z, (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha)
        (arithmeticGlobalClassesModOutsideStageTransition ℚ (AlgebraicClosure ℚ) a ha) E).hom (u z) = c.val z)
    (hz : (Submodule.Quotient.mk c : ContinuousRepresentationH2
      (restrictedCoefficientRep (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha) H.toSubgroup.subtype)
      (restrictedCoefficientAction_continuous _ H.toSubgroup.subtype continuous_subtype_val
        (arithmeticClassesModOutsideColimitAction_continuous ℚ (AlgebraicClosure ℚ) a ha))) = 0) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a), ∃ hEF : E ≤ F,
      let π : H →* Gal(F/ℚ) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : π.range → arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F,
        ∀ g h : H, (arithmeticGlobalClassesModOutsideStageTransition ℚ (AlgebraicClosure ℚ) a ha E F hEF).hom (u (g, h)) =
          (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F).ρ g.val (d (π.rangeRestrict h)) -
            d (π.rangeRestrict (g * h)) + d (π.rangeRestrict g) :=
  arithmeticOpenSubgroupClassH2_zero_exists_finite_witness ℚ (AlgebraicClosure ℚ) a ha H E u c hu hz

end OriginalArithmeticOpenSubgroupClassH2

noncomputable section OriginalArithmeticOpenClassInvariants
open scoped NumberField Classical

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- These consumers use the original rational inclusion in the actual arithmetic union. -/
local instance openInvariantConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))

/-- An actual open-subgroup invariant arithmetic class coefficient has exactly one original fixed-field class preimage. -/
theorem actual_arithmetic_open_class_invariant_unique_base
    (x : (Rep.res H.toSubgroup.subtype
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)).ρ.invariants) :
    ∃! c : rationalArithmeticOpenBaseClassQuotient (AlgebraicClosure ℚ) a ha H,
      rationalArithmeticOpenBaseClassToColimitInvariants (AlgebraicClosure ℚ) a ha H c = x :=
  (rationalArithmeticOpenBaseClassToColimitInvariants_bijective
    (AlgebraicClosure ℚ) a ha H).existsUnique x

/-- Actual finite-stage open-subgroup invariant classes have their unique genuine fixed-field preimages. -/
theorem actual_arithmetic_open_finite_class_invariant_unique_base
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))
    (hF : IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField)
    (x : (Rep.res H.toSubgroup.subtype
      (arithmeticGlobalClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F)).ρ.invariants) :
    letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField) := ⟨hF⟩
    ∃! c : rationalArithmeticOpenBaseClassQuotient (AlgebraicClosure ℚ) a ha H,
      rationalArithmeticOpenBaseClassToStageInvariants (AlgebraicClosure ℚ) a ha H F c = x := by
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField) := ⟨hF⟩
  exact (rationalArithmeticOpenBaseClassToStageInvariants_bijective
    (AlgebraicClosure ℚ) a ha H F).existsUnique x

end OriginalArithmeticOpenClassInvariants

noncomputable section OriginalArithmeticGeneralClassH2
open scoped NumberField

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The consumer uses the original rational inclusion in the actual arithmetic union. -/
local instance generalClassH2ConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))

/-- The consumer uses the original rational algebra on the finite arithmetic stage. -/
local instance generalClassH2ConsumerStageAlgebra : Algebra ℚ F := F.algebra'
/-- The actual finite arithmetic stage is a number field. -/
local instance generalClassH2ConsumerStageNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- The actual arithmetic class quotient H2 has order dividing the field degree and every class has its unique original full-class lift, for arbitrary finite stages. -/
theorem actual_arithmetic_general_class_H2_lift_and_degree
    (x : groupCohomology (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F) 2) :
    Nat.card (groupCohomology (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha F) 2) ∣
        Module.finrank ℚ F ∧
    ∃! y : groupCohomology (originalIdeleClassRep ℚ F) 2,
      (groupCohomology.functor ℤ Gal(F/ℚ) 2).map
        (originalIdeleClassesModOutsideRepHom ℚ F
          (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha F)
          (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)) y = x :=
  ⟨(rationalArithmeticClassesModOutsideStage_second_card_dvd (AlgebraicClosure ℚ) a ha F).2,
    rationalArithmeticClassesModOutsideStage_H2_unique_full_class (AlgebraicClosure ℚ) a ha F x⟩

end OriginalArithmeticGeneralClassH2

noncomputable section OriginalArithmeticRelativeOpenFields
open scoped NumberField

variable (a : 𝓞 ℚ)

/-- The consumer uses the actual arithmetic union's original rational algebra. -/
local instance relativeOpenConsumerUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'
/-- The consumer uses the proved Galois structure of the original arithmetic union. -/
local instance relativeOpenConsumerUnionGalois : IsGalois ℚ
    (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  originalUnramifiedGaloisUnion_isGalois a

/-- Actual normal open arithmetic subgroups have continuous literal relative restriction, the exact original kernel and the genuine fixed-field degree. -/
theorem actual_arithmetic_open_relative_restriction_kernel_degree
    (U V : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a / ℚ))
    (hVU : V.toSubgroup ≤ U.toSubgroup)
    [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] :
    Continuous (openGaloisSubgroupRelativeRestriction U V hVU) ∧
      (openGaloisSubgroupRelativeRestriction U V hVU).ker = V.toSubgroup.subgroupOf U.toSubgroup ∧
      Nat.card (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) =
        Module.finrank (IntermediateField.fixedField U.toSubgroup)
          (IntermediateField.extendScalars (IntermediateField.fixedField_le hVU)) :=
  ⟨openGaloisSubgroupRelativeRestriction_continuous U V hVU,
    openGaloisSubgroupRelativeRestriction_ker U V hVU,
    openGaloisSubgroupRelativeQuotient_degree U V hVU⟩

end OriginalArithmeticRelativeOpenFields

noncomputable section OriginalArithmeticOpenQuotientClasses
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union retains its rational inclusion. -/
local instance relativeQuotientConsumerUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := (AlgebraicClosure ℚ)) a) :=
  (originalUnramifiedGaloisUnion (Ω := (AlgebraicClosure ℚ)) a).algebra'
/-- The original arithmetic union is Galois. -/
local instance relativeQuotientConsumerUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := (AlgebraicClosure ℚ)) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (U V : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := (AlgebraicClosure ℚ)) a / ℚ))
  [hVU : Fact (V.toSubgroup ≤ U.toSubgroup)]
  [(V.toSubgroup.subgroupOf U.toSubgroup).Normal]

/-- The lower fixed field has its literal rational algebra. -/
local instance relativeQuotientConsumerLowerAlgebra : Algebra ℚ (IntermediateField.fixedField U.toSubgroup) :=
  (IntermediateField.fixedField U.toSubgroup).algebra'
/-- The upper fixed field has its literal rational algebra. -/
local instance relativeQuotientConsumerUpperAlgebra : Algebra ℚ (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.fixedField V.toSubgroup).algebra'
/-- The lower rational action is induced by the original algebra. -/
local instance relativeQuotientConsumerLowerRatSMul : SMul ℚ (IntermediateField.fixedField U.toSubgroup) :=
  Algebra.toSMul
/-- The upper rational action is induced by the original algebra. -/
local instance relativeQuotientConsumerUpperRatSMul : SMul ℚ (IntermediateField.fixedField V.toSubgroup) :=
  Algebra.toSMul
/-- The lower fixed field is finite over the rationals. -/
local instance relativeQuotientConsumerLowerFinite : FiniteDimensional ℚ (IntermediateField.fixedField U.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite U
/-- The upper fixed field is finite over the rationals. -/
local instance relativeQuotientConsumerUpperFinite : FiniteDimensional ℚ (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite V
/-- The lower fixed field is an actual number field. -/
local instance relativeQuotientConsumerLowerNumberField : NumberField (IntermediateField.fixedField U.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- The upper fixed field is an actual number field. -/
local instance relativeQuotientConsumerUpperNumberField : NumberField (IntermediateField.fixedField V.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- Containment gives the literal relative fixed-field algebra. -/
local instance relativeQuotientConsumerAlgebra : Algebra (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.inclusion (IntermediateField.fixedField_le hVU.out)).toAlgebra
/-- The relative module uses the original field inclusion. -/
local instance relativeQuotientConsumerModule : Module (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toModule
/-- The relative scalar action uses the original inclusion. -/
local instance relativeQuotientConsumerSMul : SMul (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toSMul
/-- The relative multiplicative action is induced by the original module. -/
local instance relativeQuotientConsumerMulAction : MulAction (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (relativeQuotientConsumerModule a U V).toDistribMulAction.toMulAction
/-- The relative fixed-field inclusion forms the original rational tower. -/
local instance relativeQuotientConsumerTower : IsScalarTower ℚ (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := .of_algebraMap_eq' rfl
/-- Normality gives the genuine relative fixed-field Galois extension. -/
local instance relativeQuotientConsumerGalois : IsGalois (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_relative_isGalois U V hVU.out

open scoped Classical

/-- The actual arithmetic fixed-field class map preserves literal relative Galois action. -/
theorem actual_arithmetic_open_quotient_class_action
    (g : U) (c : rationalArithmeticOpenBaseClassQuotient (AlgebraicClosure ℚ) a ha V) :
    rationalArithmeticOpenBaseClassToColimit (AlgebraicClosure ℚ) a ha V
      ((rationalArithmeticRelativeClassRep (AlgebraicClosure ℚ) a ha U V).ρ
        (openGaloisSubgroupRelativeRestriction U V hVU.out g) c) =
    (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha).ρ g.val
      (rationalArithmeticOpenBaseClassToColimit (AlgebraicClosure ℚ) a ha V c) :=
  rationalArithmeticOpenBaseClassToColimit_equivariant (AlgebraicClosure ℚ) a ha U V g c

/-- The original quotient invariant coefficient has precisely the actual fixed-field class preimages. -/
theorem actual_arithmetic_open_quotient_class_unique
    (x : ((Rep.res U.toSubgroup.subtype
      (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup))) :
    ∃! c : rationalArithmeticOpenBaseClassQuotient (AlgebraicClosure ℚ) a ha V,
      (rationalArithmeticOpenQuotientClassInclusion (AlgebraicClosure ℚ) a ha U V).hom c = x :=
  (rationalArithmeticOpenQuotientClassInclusion_bijective (AlgebraicClosure ℚ) a ha U V).existsUnique x

/-- Actual open-quotient H2 has unique genuine full-class preimages and finite order dividing the original subgroup index. -/
theorem actual_arithmetic_open_quotient_h2_unique_finite
    (x : groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) :
    (∃! y : groupCohomology (originalIdeleClassRep (IntermediateField.fixedField U.toSubgroup)
      (IntermediateField.fixedField V.toSubgroup)) 2,
      (rationalArithmeticFullClassToOpenQuotientH2Iso (AlgebraicClosure ℚ) a ha U V).hom y = x) ∧
    Finite (groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) ∧
    Nat.card (groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) ∣
      Nat.card (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) :=
  ⟨rationalArithmeticOpenQuotientH2_unique_full_class (AlgebraicClosure ℚ) a ha U V x,
    rationalArithmeticOpenQuotientH2_finite_card_dvd (AlgebraicClosure ℚ) a ha U V⟩

end OriginalArithmeticOpenQuotientClasses

noncomputable section OriginalClassGeneratorReuse
open CategoryTheory groupCohomology Rep
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ F] [IsGalois ℚ F]

/-- The actual finite rational intermediate field is a number field. -/
local instance originalClassGeneratorFieldNumberField : NumberField F :=
  NumberField.of_module_finite ℚ F

omit [IsGalois ℚ F] in
/-- The original finite rational class trace uses literal subgroup restriction. -/
theorem regression_originalClassH2_restriction_trace
    (S : Subgroup Gal(F/ℚ)) [Fintype (Gal(F/ℚ) ⧸ S)]
    (x : groupCohomology (originalIdeleClassRep ℚ F) 2) :
    (subgroupCohomologyTrace (originalIdeleClassRep ℚ F) S 2).hom
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep ℚ F))) 2).hom x) = S.index • x :=
  originalCohomology_trace_restriction_apply (originalIdeleClassRep ℚ F) S 2 x

/-- Consume the genuine original rational finite-stage class theorem with only its stated upstream arithmetic inputs. -/
theorem regression_originalClassH2_auxiliary_generator
    (S T : Subgroup Gal(F/ℚ)) [S.Normal] [T.Normal]
    [Fintype Gal(F/ℚ)] [Fintype (Gal(F/ℚ) ⧸ S)]
    (n' : ℕ) (hn : Fintype.card (Gal(F/ℚ) ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology ((originalIdeleClassRep ℚ F).quotientToInvariants T) 2)
    (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep ℚ F))) 2).hom
        ((n' / Fintype.card (Gal(F/ℚ) ⧸ S)) •
          (map (A := (originalIdeleClassRep ℚ F).quotientToInvariants T)
            (B := originalIdeleClassRep ℚ F) (QuotientGroup.mk' T)
            (ofHom ((originalIdeleClassRep ℚ F).ρ.quotientToInvariants_lift T)) 2).hom u') = 0) :
    ∃ y : groupCohomology ((originalIdeleClassRep ℚ F).quotientToInvariants S) 2,
      Nat.card (groupCohomology ((originalIdeleClassRep ℚ F).quotientToInvariants S) 2) =
        Fintype.card (Gal(F/ℚ) ⧸ S) ∧
      Submodule.span ℤ {y} = ⊤ ∧
      (map (A := (originalIdeleClassRep ℚ F).quotientToInvariants S)
        (B := originalIdeleClassRep ℚ F) (QuotientGroup.mk' S)
        (ofHom ((originalIdeleClassRep ℚ F).ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Gal(F/ℚ) ⧸ S)) •
          (map (A := (originalIdeleClassRep ℚ F).quotientToInvariants T)
            (B := originalIdeleClassRep ℚ F) (QuotientGroup.mk' T)
            (ofHom ((originalIdeleClassRep ℚ F).ρ.quotientToInvariants_lift T)) 2).hom u' :=
  originalIdeleClass_quotientH2_generator_from_auxiliary ℚ F S T n' hn hn'0 u' hu' hres

/-- Consume the genuine original rational finite-stage class theorem with only its stated upstream arithmetic inputs. -/
theorem regression_originalClassH2_invariant_from_full_order
    (u : groupCohomology (originalIdeleClassRep ℚ F) 2)
    (hu : addOrderOf u = Module.finrank ℚ F) :
    ∃ invG : groupCohomology (originalIdeleClassRep ℚ F) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Module.finrank ℚ F • t = 0) ∧
      invG u = ↑((1 : ℚ) / Module.finrank ℚ F) ∧
      ∀ S : Subgroup Gal(F/ℚ),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep ℚ F)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep ℚ F) 2,
            invS ((map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep ℚ F))) 2).hom x) =
              S.index • invG x :=
  originalIdeleClass_exists_invariants_of_full_order ℚ F u hu

end OriginalClassGeneratorReuse

noncomputable section OriginalAuxiliaryCyclicExtensionReuse

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]

/-- The actual finite rational intermediate field used by the cyclic extension consumer is a number field. -/
local instance auxiliaryCyclicConsumerNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- The auxiliary cyclic extension is constructed over the actual finite rational intermediate field. -/
theorem regression_original_auxiliary_cyclic_degree (n : ℕ) (hn : 0 < n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
      IsGalois F L ∧ IsCyclic Gal(L/F) ∧ Module.finrank F L = n :=
  originalNumberField_exists_cyclic_degree F n hn

end OriginalAuxiliaryCyclicExtensionReuse

noncomputable section MackeyOriginalConsumer1

/-- The canonical rational algebra on the original closure agrees with
the algebra used by the pinned closure construction. -/
local instance representativeConsumerClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]

/-- The original rational unit coefficient has its discrete topology. -/
local instance rationalUnitDiscreteTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) := ⊥
/-- The rational unit topology is discrete by construction. -/
local instance rationalUnitDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) := ⟨rfl⟩
/-- The original extension unit coefficient has its discrete topology. -/
local instance extensionUnitDiscreteTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (AlgebraicClosure ℚ)) := ⊥
/-- The extension unit topology is discrete by construction. -/
local instance extensionUnitDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (AlgebraicClosure ℚ)) := ⟨rfl⟩

/-- The actual finite rational field and algebraic closure consume the
changed-representative transfer theorem on their original unit cocycles. -/
theorem regression_original_arithmetic_corestriction_representatives
    (a : Gal(AlgebraicClosure ℚ/ℚ) ⧸ F.fixingSubgroup → F.fixingSubgroup)
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (AlgebraicClosure ℚ))) :
    letI : Fintype (Gal(AlgebraicClosure ℚ/ℚ) ⧸ F.fixingSubgroup) := Fintype.ofFinite _
    (Submodule.Quotient.mk
      (continuousChangedCosetTraceCocycle (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
        (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := AlgebraicClosure ℚ))
        F.fixingSubgroup F.fixingSubgroup_isOpen a
        (galoisFixingUnitCocycle ℚ (AlgebraicClosure ℚ) F c)) :
      GaloisUnitContinuousH2 (K := ℚ) (Ω := AlgebraicClosure ℚ)) =
        galoisUnitContinuousCorestriction ℚ (AlgebraicClosure ℚ) F (Submodule.Quotient.mk c) :=
  galoisUnitContinuousCorestriction_changed_representatives ℚ (AlgebraicClosure ℚ) F a c

end MackeyOriginalConsumer1

noncomputable section MackeyOriginalConsumer2
open scoped BigOperators NumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)

/-- Retain the rational algebra of the original arithmetic union. -/
local instance orbitConsumerAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- The original arithmetic union is Galois by its proved construction. -/
local instance orbitConsumerGalois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The actual finite field fixing subgroup, with the original arithmetic
group structure retained explicitly for its coset instances. -/
def orbitConsumerFixingSubgroup : Subgroup (rationalArithmeticGaloisGroup a) := F.fixingSubgroup

/-- The actual finite field fixes an open subgroup of the original compact arithmetic group. -/
local instance orbitConsumerFiniteCosets :
    Finite (rationalArithmeticGaloisGroup a ⧸ (orbitConsumerFixingSubgroup a F)) :=
  Subgroup.quotient_finite_of_isOpen (orbitConsumerFixingSubgroup a F) F.fixingSubgroup_isOpen

/-- Enumerate the actual finite fixing cosets. -/
local instance orbitConsumerCosetsFintype :
    Fintype (rationalArithmeticGaloisGroup a ⧸ (orbitConsumerFixingSubgroup a F)) := Fintype.ofFinite _

/-- The actual orbit set is finite as a quotient of the original finite cosets. -/
local instance orbitConsumerIndexFinite :
    Finite (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) :=
  Finite.of_surjective
    (fun q : rationalArithmeticGaloisGroup a ⧸ (orbitConsumerFixingSubgroup a F) =>
      (Quotient.mk'' q : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)))
    (fun q => Quotient.inductionOn' q (fun x => ⟨x, rfl⟩))

/-- Enumerate the actual local orbits. -/
local instance orbitConsumerIndexFintype :
    Fintype (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) := Fintype.ofFinite _

/-- The stabilizer cosets embed in the actual finite global coset space. -/
local instance orbitConsumerStabilizerFintype
    (ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) :
    Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out) := by
  letI := orbitConsumerCosetsFintype a F
  exact Fintype.ofInjective (cosetOrbitMap (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out)
    (cosetOrbitMap_injective (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out)

/-- The actual discrete arithmetic unit module retains its integer action. -/
local instance orbitConsumerContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitRepresentation a).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The actual finite arithmetic field, original prime restriction and
original unit embedding consume Mackey with every finite orbit instance derived. -/
theorem regression_actual_arithmetic_unit_corestriction_orbits
    (c : continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (rationalArithmeticUnitRepresentation a) (orbitConsumerFixingSubgroup a F).subtype)) :
  letI : Fintype (rationalArithmeticGaloisGroup a ⧸ (orbitConsumerFixingSubgroup a F)) := orbitConsumerCosetsFintype a F
  letI : Fintype (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) := orbitConsumerIndexFintype a p hp F
  letI (ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) :
      Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
        cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out) := orbitConsumerStabilizerFintype a p hp F ω
    let A := rationalArithmeticUnitRepresentation a
    let j := rationalPrimeArithmeticRestriction a p hp
    let B := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    let hB := discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp)
    rationalArithmeticUnitH2Restriction a p hp
        (continuousRepresentationH2Corestriction A (rationalArithmeticUnitAction_continuous a)
          (orbitConsumerFixingSubgroup a F) F.fixingSubgroup_isOpen (Submodule.Quotient.mk c)) =
      ∑ ω : cosetOrbitIndex j.toMonoidHom (orbitConsumerFixingSubgroup a F),
        continuousRepresentationH2Corestriction B hB
          (cosetOrbitStabilizer j.toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out)
          (cosetOrbitStabilizer_isOpen j.toMonoidHom j.continuous (orbitConsumerFixingSubgroup a F) F.fixingSubgroup_isOpen ω.out)
          (Submodule.Quotient.mk
            (continuousCoefficientCocycleTwoMap
              (restrictedCoefficientRep (restrictedCoefficientRep A j.toMonoidHom)
                (cosetOrbitStabilizer j.toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out).subtype)
              (restrictedCoefficientRep B (cosetOrbitStabilizer j.toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out).subtype)
              (rationalArithmeticUnitLocalMap a p hp) continuous_of_discreteTopology
              (fun g x => rationalArithmeticUnitLocalMap_equivariant a p hp g x)
              (continuousCosetOrbitCocycle A (rationalArithmeticUnitAction_continuous a)
                j.toMonoidHom j.continuous (orbitConsumerFixingSubgroup a F) ω.out c))) := by
  letI : Fintype (rationalArithmeticGaloisGroup a ⧸ (orbitConsumerFixingSubgroup a F)) := orbitConsumerCosetsFintype a F
  letI : Fintype (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) := orbitConsumerIndexFintype a p hp F
  letI (ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F)) :
      Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
        cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom (orbitConsumerFixingSubgroup a F) ω.out) := orbitConsumerStabilizerFintype a p hp F ω
  exact rationalArithmeticUnitH2_restriction_corestriction_orbits a p hp (orbitConsumerFixingSubgroup a F)
    F.fixingSubgroup_isOpen c

end MackeyOriginalConsumer2

noncomputable section OddPrimaryReciprocityConsumers
open NumberField IsDedekindDomain
open scoped NumberField BigOperators

section FullDecomposition

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ F] [IsGalois ℚ F] [IsCyclic Gal(F/ℚ)]

/-- The actual finite rational subfield has its derived number-field structure. -/
local instance oddPrimaryConsumerNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- The original finite rational field supplies a full-decomposition prime
outside the actual prescribed rational prime support. -/
theorem regression_original_cyclic_prime_power_full_decomposition
    (q n : ℕ) (hq : q.Prime) (hn : 0 < n) (hdegree : Module.finrank ℚ F = q ^ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ w : HeightOneSpectrum (𝓞 F), originalFinitePrimeBelow ℚ F w ∉ S ∧
      OriginalFiniteDecompositionGroup ℚ F w = ⊤ :=
  original_cyclicPrimePower_exists_fullDecomposition_outside ℚ F q n hq hn hdegree S

end FullDecomposition

section OriginalArithmeticCorestriction

attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

variable (a : 𝓞 ℚ)

/-- Retain the original rational algebra on the actual arithmetic union. -/
local instance oddPrimaryConsumerAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'
/-- The actual arithmetic union is Galois by its proved construction. -/
local instance oddPrimaryConsumerGalois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a
/-- The actual original global unit coefficients carry their discrete topology. -/
local instance oddPrimaryConsumerUnitTopology : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
/-- That original unit topology is discrete. -/
local instance oddPrimaryConsumerUnitDiscrete : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
/-- Retain the same discrete topology on the literal global unit representation. -/
local instance oddPrimaryConsumerRawUnitTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) := ⊥
/-- The literal original global unit representation is discrete. -/
local instance oddPrimaryConsumerRawUnitDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) := ⟨rfl⟩

variable (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The same arithmetic union is Galois over the actual finite subfield. -/
local instance oddPrimaryConsumerUpperGalois : IsGalois F (rationalUnramifiedExtension a) :=
  IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension a)
/-- Retain the discrete unit coefficients for the same upper field over the finite subfield. -/
local instance oddPrimaryConsumerUpperTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- Those original relative unit coefficients are discrete. -/
local instance oddPrimaryConsumerUpperDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩

/-- The original finite arithmetic subfield and actual coset corestriction
consume odd-primary rational reciprocity with derived Galois structures. -/
theorem regression_original_odd_primary_corestriction_invariant_sum
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : GaloisUnitContinuousH2 (K := F) (Ω := rationalUnramifiedExtension a))
    (hy : q ^ (r + 1) • y = 0) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∉ S, rationalArithmeticUnitPrimeInvariant a p.val p.property
        (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F y) = 0) ∧
      (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property
        (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F y)) = 0 :=
  rationalArithmeticUnitCorestriction_exists_support_sum_zero a q r hq hq2 hqa F y hy

end OriginalArithmeticCorestriction
end OddPrimaryReciprocityConsumers

noncomputable section ArithmeticOrbitOriginalConsumer1
open scoped NumberField
attribute [local instance] arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)

/-- Keep the original rational algebra of the actual arithmetic union. -/
local instance orbitFieldConsumerAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- Every actual finite arithmetic subfield and coset yields the actual
finite local field with exactly the Mackey stabilizer as its fixing subgroup. -/
theorem regression_original_arithmetic_orbit_local_field
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    (rationalArithmeticOrbitLocalField a p hp F c).fixingSubgroup =
        cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F) c ∧
      FiniteDimensional (rationalPrimeLocalField p hp) (rationalArithmeticOrbitLocalField a p hp F c) :=
  ⟨rationalArithmeticOrbitLocalField_fixingSubgroup a p hp F c,
    rationalArithmeticOrbitLocalField_finiteDimensional a p hp F c⟩

/-- The actual global field image and original prime completion generate
the same local field, with literal field-element values preserved. -/
theorem regression_original_arithmetic_orbit_field_embedding
    (F : IntermediateField ℚ (rationalUnramifiedExtension a))
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    (algebraMap (rationalPrimeLocalField p hp) (rationalArithmeticOrbitLocalField a p hp F c)).fieldRange ⊔
        (rationalArithmeticOrbitFieldInclusion a p hp F c).toRingHom.fieldRange = ⊤ ∧
      ∀ x : F, (rationalArithmeticOrbitFieldInclusion a p hp F c x : rationalPrimeLocalClosure p hp) =
        rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a) :=
  ⟨rationalArithmeticOrbitField_ranges a p hp F c,
    rationalArithmeticOrbitFieldInclusion_coe a p hp F c⟩

end ArithmeticOrbitOriginalConsumer1

noncomputable section ArithmeticOrbitOriginalConsumer2
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)

/-- The actual arithmetic unit coefficient has its discrete topology. -/
local instance orbitUnitConsumerGlobalTopology : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
/-- The actual arithmetic unit topology is discrete by construction. -/
local instance orbitUnitConsumerGlobalDiscrete : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
/-- The same original arithmetic union over the actual finite stage has discrete unit coefficients. -/
local instance orbitUnitConsumerRelativeTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The original relative unit topology is discrete by construction. -/
local instance orbitUnitConsumerRelativeDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
/-- The actual orbit local field uses discrete original algebraic-closure units. -/
local instance orbitUnitConsumerLocalTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c)
      (rationalPrimeLocalClosure p hp)) := ⊥
/-- Those original local unit coefficients are discrete. -/
local instance orbitUnitConsumerLocalDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩

/-- An actual finite Galois arithmetic stage consumes the same-cocycle
comparison between its Mackey orbit and genuine local field base change. -/
theorem regression_original_arithmetic_orbit_unit_base_change
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (d e : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField) c) :
    (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F.toIntermediateField c y).val
        (rationalArithmeticOrbitLocalAutomorphism a p hp F.toIntermediateField c d,
          rationalArithmeticOrbitLocalAutomorphism a p hp F.toIntermediateField c e) =
      rationalArithmeticOrbitUnitCocycleValue a p hp F.toIntermediateField c y (d, e) :=
  rationalArithmeticOrbitUnitCocycle_eq_baseChange a p hp F.toIntermediateField c y d e

/-- The actual finite Galois arithmetic stage supplies the extending
local valuation and topology without an assumed local-field certificate. -/
theorem regression_original_arithmetic_orbit_local_structure :
    let E := rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c
    ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E), IsNonarchimedeanLocalField E ∧
      (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E) :=
  rationalArithmeticOrbitLocalField_exists_structure a p hp F.toIntermediateField c

end ArithmeticOrbitOriginalConsumer2

noncomputable section ArithmeticOrbitOriginalConsumer3
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  orbitUnitConsumerGlobalTopology orbitUnitConsumerGlobalDiscrete
  orbitUnitConsumerRelativeTopology orbitUnitConsumerRelativeDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)

/-- The actual prime-completion unit coefficients have the discrete topology. -/
local instance orbitInvariantConsumerPrimeTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⊥
/-- The original prime-completion unit topology is discrete. -/
local instance orbitInvariantConsumerPrimeDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
/-- Finiteness of the actual stabilizer quotient follows from openness of the actual finite-field fixing subgroup. -/
local instance orbitInvariantConsumerCosets :
    Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField) c) := by
  let H := cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField) c
  haveI : Finite (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ H) :=
    Subgroup.quotient_finite_of_isOpen H
      (cosetOrbitStabilizer_isOpen (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous
        (rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)
        F.toIntermediateField.fixingSubgroup_isOpen c)
  exact Fintype.ofFinite _

/-- Choose the actual orbit valuation from the proved spectral construction. -/
local instance orbitInvariantConsumerValuation :
    ValuativeRel (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F.toIntermediateField c).choose
/-- Retain the local topology accompanying that constructed valuation. -/
local instance orbitInvariantConsumerTopology :
    TopologicalSpace (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F.toIntermediateField c).choose_spec.choose
/-- The chosen structures satisfy the proved local-field property. -/
local instance orbitInvariantConsumerLocalField :
    IsNonarchimedeanLocalField (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F.toIntermediateField c).choose_spec.choose_spec.1
/-- The constructed valuation extends the original prime-completion valuation. -/
local instance orbitInvariantConsumerExtension :
    (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c)) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F.toIntermediateField c).choose_spec.choose_spec.2

/-- The original arithmetic stage constructs every local-field premise
and consumes the exact invariant identity for its literal Mackey orbit trace. -/
theorem regression_original_arithmetic_orbit_trace_invariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
        (rationalArithmeticOrbitUnitTrace a p hp F.toIntermediateField c y) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F.toIntermediateField c y)) := by
  exact rationalArithmeticOrbitUnitTrace_invariant a p hp F.toIntermediateField c y

end ArithmeticOrbitOriginalConsumer3

noncomputable section CompletionInvariantOriginalConsumer1
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionGlobalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)

/-- The actual finite arithmetic stage constructs its original prime over the chosen rational prime. -/
theorem regression_original_arithmetic_orbit_prime :
    originalIntegerPrimeBelow F
      (rationalArithmeticOrbitPrime a p hp F.toIntermediateField c) = rationalPrimePlace p hp :=
  rationalArithmeticOrbitPrime_below a p hp F.toIntermediateField c

/-- The actual finite arithmetic stage has a completion equivalence retaining the literal global embedding. -/
theorem regression_original_arithmetic_orbit_completion (x : F) :
    (rationalArithmeticOrbitCompletionEquiv a p hp F.toIntermediateField c
      (algebraMap F ((rationalArithmeticOrbitPrime a p hp F.toIntermediateField c).adicCompletion F) x) :
        rationalPrimeLocalClosure p hp) =
      rationalArithmeticOrbitEmbedding a p hp F.toIntermediateField c (x : rationalUnramifiedExtension a) :=
  rationalArithmeticOrbitCompletionEquiv_coe a p hp F.toIntermediateField c x

/-- The actual stage's completion equivalence supplies the original valuation-extension premise. -/
theorem regression_original_arithmetic_orbit_completion_valuation :
    let W := (rationalArithmeticOrbitPrime a p hp F.toIntermediateField c).adicCompletion F
    letI : Algebra W (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c) :=
      (rationalArithmeticOrbitCompletionEquiv a p hp F.toIntermediateField c).toRingHom.toAlgebra
    letI : ValuativeRel W := ValuativeRel.ofValuation (NormedField.valuation (K := W))
    (ValuativeRel.valuation W).HasExtension
      (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField c)) :=
  rationalArithmeticOrbitCompletion_hasExtension a p hp F.toIntermediateField c

end CompletionInvariantOriginalConsumer1

noncomputable section CompletionInvariantOriginalConsumer2
open scoped NumberField
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

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)

/-- Retain discrete original arithmetic unit coefficients. -/
local instance orbitCompletionInvariantConsumerGlobalTopology :
    TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
/-- The original arithmetic coefficient topology is discrete. -/
local instance orbitCompletionInvariantConsumerGlobalDiscrete :
    DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
/-- Retain discrete unit coefficients over the original finite arithmetic stage. -/
local instance orbitCompletionInvariantConsumerRelativeTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The finite-stage coefficient topology is discrete. -/
local instance orbitCompletionInvariantConsumerRelativeDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
/-- Use the original prime-closure unit coefficients with their discrete topology. -/
local instance orbitCompletionInvariantConsumerPrimeTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⊥
/-- The actual prime coefficient topology is discrete. -/
local instance orbitCompletionInvariantConsumerPrimeDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩

/-- The original finite Galois arithmetic stage identifies its literal Mackey summand with its genuine number-field completion localization, constructing every field, valuation, tower and quotient-finiteness premise. -/
theorem regression_original_arithmetic_trace_completion_invariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (rationalArithmeticOrbitUnitTrace a p hp F.toIntermediateField c y) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F.toIntermediateField c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F.toIntermediateField c y)) :=
  rationalArithmeticOrbitUnitTrace_completion_invariant a p hp F.toIntermediateField c y

end CompletionInvariantOriginalConsumer2

noncomputable section PrimeBijectionOriginalConsumer
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F.toIntermediateField)

/-- The genuine finite arithmetic-stage primes identify exactly the actual local Galois coset orbits, with all local comparisons constructed. -/
theorem regression_original_arithmetic_prime_fibers :
    rationalArithmeticOrbitPrime a p hp F.toIntermediateField c =
      rationalArithmeticOrbitPrime a p hp F.toIntermediateField c' ↔
    ∃ d : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
      rationalPrimeArithmeticRestriction a p hp d • c = c' :=
  rationalArithmeticOrbitPrime_eq_iff a p hp F.toIntermediateField c c'

/-- The exact Mackey orbit quotient of an original finite arithmetic stage embeds into its genuine primes above the original rational prime. -/
theorem regression_original_arithmetic_prime_index_injective :
    Function.Injective (rationalArithmeticOrbitPrimeIndex a p hp F.toIntermediateField) :=
  rationalArithmeticOrbitPrimeIndex_injective a p hp F.toIntermediateField

/-- The exact original finite-stage Mackey index reaches every genuine prime above p and identifies no distinct orbits. -/
theorem regression_original_arithmetic_prime_index_bijective :
    Function.Bijective (rationalArithmeticOrbitPrimeIndex a p hp F.toIntermediateField) :=
  ⟨rationalArithmeticOrbitPrimeIndex_injective a p hp F.toIntermediateField,
    rationalArithmeticOrbitPrimeIndex_surjective a p hp F.toIntermediateField⟩

/-- The actual finite-stage orbit equivalence retains the literal original prime used in its completion-localization cocycle. -/
theorem regression_original_arithmetic_prime_equiv_literal :
    (rationalArithmeticOrbitPrimeEquiv a p hp F.toIntermediateField (Quotient.mk'' c)).val =
      rationalArithmeticOrbitPrime a p hp F.toIntermediateField c :=
  rationalArithmeticOrbitPrimeEquiv_mk a p hp F.toIntermediateField c

end PrimeBijectionOriginalConsumer







end Dubon2026.SemanticRegression
