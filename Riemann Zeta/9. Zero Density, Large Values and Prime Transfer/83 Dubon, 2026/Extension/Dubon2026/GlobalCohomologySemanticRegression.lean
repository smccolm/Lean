import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] Rep.hV2
attribute [local instance] Units.mulDistribMulActionRight
section

variable (G F : Type) [Group G] [Finite G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulFieldUnit_first_cohomology_zero`. -/
theorem actual_unrestricted_local_cohomology_faithfulFieldUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1) :=
  faithfulFieldUnit_first_cohomology_zero G F

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedFieldTransport_algebraMap`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedFieldTransport_algebraMap_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q) (x : L),
      supportedUnrestrictedFieldTransport K L S hS σ p q h
        (algebraMap L (supportedUnrestrictedCompletion L S p) x) =
      algebraMap L (supportedUnrestrictedCompletion L S q) (σ x) :=
  supportedUnrestrictedFieldTransport_algebraMap K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedOrbitField_faithful`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedOrbitField_faithful_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω))
        (supportedUnrestrictedCompletion L S ω.out) :=
  supportedUnrestrictedOrbitField_faithful K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnitFieldEquiv_transport`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedUnitFieldEquiv_transport_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q)
      (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitFieldEquiv L S q (supportedUnrestrictedUnitTransport K L S hS σ p q h x) =
        Additive.ofMul (Units.map (supportedUnrestrictedFieldTransport K L S hS σ p q h).toMonoidHom
          (supportedUnrestrictedUnitFieldEquiv L S p x).toMul) :=
  supportedUnrestrictedUnitFieldEquiv_transport K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnit_first_cohomology_zero`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 1) :=
  supportedUnrestrictedUnit_first_cohomology_zero K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_local_second`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_local_second_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hsecond : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_local_second K L S hS hsurj hsecond houtside

end

section

variable (K : Type*) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_exists_ringOfIntegers_approximation`. -/
theorem actual_unrestricted_local_cohomology_original_exists_ringOfIntegers_approximation_source
    (v : HeightOneSpectrum (𝓞 K)) (y : K)
    (hy : v.valuation K y ≤ 1) :
    ∃ r : 𝓞 K, v.valuation K (y - algebraMap (𝓞 K) K r) < 1 :=
  original_exists_ringOfIntegers_approximation K v y hy

end

section

variable (K : Type*) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_finite_adicCompletion_residueField`. -/
theorem actual_unrestricted_local_cohomology_original_finite_adicCompletion_residueField_source
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (Valued.ResidueField (v.adicCompletion K)) :=
  original_finite_adicCompletion_residueField K v

end

section

variable (G F : Type) [Group G] [Finite G] [NontriviallyNormedField F]
  [MulSemiringAction G F]
  (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖)



include hnorm in
/-- Exact original-object consumer of `normPreserving_fixedField_exists_norm_gt_one`. -/
theorem actual_unrestricted_local_cohomology_normPreserving_fixedField_exists_norm_gt_one_source :
    ∃ x : FixedPoints.subfield G F, 1 < ‖x‖ :=
  normPreserving_fixedField_exists_norm_gt_one G F hnorm

end

section

variable (G F : Type) [Group G] [Finite G] [IsCyclic G]
  [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
  [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulLocalField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulLocalField_second_cohomology_order_source
    (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulLocalField_second_cohomology_order G F hnorm

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `supportedFiniteCompletion_isUltrametric`. -/
theorem actual_unrestricted_local_cohomology_supportedFiniteCompletion_isUltrametric_source (p : SUnitLogPlace L S)
    (h : p.isRight) : IsUltrametricDist (supportedUnrestrictedCompletion L S p) :=
  supportedFiniteCompletion_isUltrametric L S p h

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `supportedFiniteOrbitPoint_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_supportedFiniteOrbitPoint_second_cohomology_order_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isRight →
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
      Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  supportedFiniteOrbitPoint_second_cohomology_order K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_archimedean_second`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_archimedean_second_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (harch : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        ω.out.isLeft →
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_archimedean_second K L S hS hsurj harch houtside

end

section



/-- Exact original-object consumer of `originalRealComplexNormQuotient_card`. -/
theorem actual_unrestricted_local_cohomology_originalRealComplexNormQuotient_card_source :
    Finite (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) ∧
    Nat.card (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) = 2 :=
  originalRealComplexNormQuotient_card 

end

section



/-- Exact original-object consumer of `originalRealComplex_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_originalRealComplex_second_cohomology_order_source :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) = 2 :=
  originalRealComplex_second_cohomology_order 

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulRealField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulRealField_second_cohomology_order_source (e : F ≃+* ℝ) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulRealField_second_cohomology_order G F e

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ)
  (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



variable [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulComplexActionHom_injective`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexActionHom_injective_source :
    Function.Injective (faithfulComplexActionHom G F e hc) :=
  faithfulComplexActionHom_injective G F e hc

end

section

variable (G F : Type) [Group G] [Finite G] [Nontrivial G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



/-- Exact original-object consumer of `faithfulComplexActionHom_bijective`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexActionHom_bijective_source :
    Function.Bijective (faithfulComplexActionHom G F e hc) :=
  faithfulComplexActionHom_bijective G F e hc

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



variable [Finite G] [FaithfulSMul G F]



include e hc in
/-- Exact original-object consumer of `faithfulComplexField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexField_second_cohomology_order_source :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulComplexField_second_cohomology_order G F e hc

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `supportedArchimedeanOrbitPoint_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_supportedArchimedeanOrbitPoint_second_cohomology_order_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isLeft →
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
      Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  supportedArchimedeanOrbitPoint_second_cohomology_order K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_outside`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_outside_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_outside K L S hS hsurj houtside

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)



/-- Exact original-object consumer of `localFieldFixedUniformizerSection_comp`. -/
theorem actual_original_idele_herbrand_localFieldFixedUniformizerSection_comp_source
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    localFieldFixedUniformizerSection K L π hfixed ≫
        (localFieldUnitValuationShortComplex K L).g = 𝟙 (Rep.trivial ℤ Gal(L/K) ℤ) :=
  localFieldFixedUniformizerSection_comp K L π hfixed hπ

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localIntegerUnit_first_second_zero_of_fixed_uniformizer`. -/
theorem actual_original_idele_herbrand_localIntegerUnit_first_second_zero_of_fixed_uniformizer_source
    [IsCyclic Gal(L/K)] (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 1) ∧
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 2) :=
  localIntegerUnit_first_second_zero_of_fixed_uniformizer K L π hfixed hπ

end

section



/-- Exact original-object consumer of `original_finite_absolutely_ramified_places`. -/
theorem actual_original_idele_herbrand_original_finite_absolutely_ramified_places_source
    (L : Type) [Field L] [NumberField L] :
    {w : HeightOneSpectrum (𝓞 L) | ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal}.Finite :=
  original_finite_absolutely_ramified_places L

end

section

variable (L : Type) [Field L] [NumberField L]



/-- Exact original-object consumer of `original_unramified_exists_completion_integer_uniformizer`. -/
theorem actual_original_idele_herbrand_original_unramified_exists_completion_integer_uniformizer_source
    (w : HeightOneSpectrum (𝓞 L)) [Algebra.IsUnramifiedAt ℤ w.asIdeal] :
    ∃ r : ℤ, Valued.v (r : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
  original_unramified_exists_completion_integer_uniformizer L w

end

section

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))



/-- Exact original-object consumer of `originalAdicIntegerNormEquiv_val`. -/
theorem actual_original_idele_herbrand_originalAdicIntegerNormEquiv_val_source (x : w.adicCompletionIntegers L) :
    (originalAdicIntegerNormEquiv L w x).val = x.val :=
  originalAdicIntegerNormEquiv_val L w x

end

section

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))



/-- Exact original-object consumer of `originalAdicUnitOrder_of_uniformizer`. -/
theorem actual_original_idele_herbrand_originalAdicUnitOrder_of_uniformizer_source
    (π : (w.adicCompletion L)ˣ) (hπ : Valued.v π.val = WithZero.exp (-1 : ℤ)) :
    letI : ProperSpace (w.adicCompletion L) := original_adicCompletion_properSpace L w
    letI : NontriviallyNormedField (w.adicCompletion L) :=
      Valued.toNontriviallyNormedField (w.adicCompletion L) ℤᵐ⁰
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    letI : IsNonarchimedeanLocalField (w.adicCompletion L) :=
      normValuation_isNonarchimedeanLocalField (w.adicCompletion L)
    localFieldUnitOrder (w.adicCompletion L) (Additive.ofMul π) = 1 :=
  originalAdicUnitOrder_of_uniformizer L w π hπ

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `supportedOutsideOrbitField_norm`. -/
theorem actual_original_idele_herbrand_supportedOutsideOrbitField_norm_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := supportedOutsideOrbitFieldAction K L S hS ω
      ∀ (σ : MulAction.stabilizer Gal(L/K)
          (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖ :=
  supportedOutsideOrbitField_norm K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `supportedOutsideOrbitPoint_first_second_zero_of_unramified`. -/
theorem actual_original_idele_herbrand_supportedOutsideOrbitPoint_first_second_zero_of_unramified_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2) :=
  supportedOutsideOrbitPoint_first_second_zero_of_unramified K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]



/-- Exact original-object consumer of `original_exists_unramified_galoisStable_idele_support`. -/
theorem actual_original_idele_herbrand_original_exists_unramified_galoisStable_idele_support_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
        Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal :=
  original_exists_unramified_galoisStable_idele_support K L S₀

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `original_ideleClass_herbrand`. -/
theorem actual_original_idele_herbrand_original_ideleClass_herbrand_source :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand K L

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassInvariantNormQuotient_order_lower`. -/
theorem actual_original_norm_descent_originalIdeleClassInvariantNormQuotient_order_lower_source
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Finite (OriginalIdeleClassInvariantNormQuotient K L g) ∧
      Nat.card Gal(L/K) ≤ Nat.card (OriginalIdeleClassInvariantNormQuotient K L g) :=
  originalIdeleClassInvariantNormQuotient_order_lower K L g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassInvariantNormQuotient_degree_nsmul_zero`. -/
theorem actual_original_norm_descent_originalIdeleClassInvariantNormQuotient_degree_nsmul_zero_source
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (x : OriginalIdeleClassInvariantNormQuotient K L g) :
    Module.finrank K L • x = 0 :=
  originalIdeleClassInvariantNormQuotient_degree_nsmul_zero K L g hg x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFullClassH0_surjective`. -/
theorem actual_original_norm_descent_originalFullClassH0_surjective_source [FiniteDimensional K L] :
    Function.Surjective ((groupCohomology.functor ℤ Gal(L/K) 0).map (originalFullClassRepHom K L)) :=
  originalFullClassH0_surjective K L

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]



/-- Exact original-object consumer of `original_ideleClass_fixed_has_fixed_representative`. -/
theorem actual_original_norm_descent_original_ideleClass_fixed_has_fixed_representative_source
    (c : OriginalNumberFieldIdeleClassGroup L)
    (hc : ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c) :
    ∃ a : (AdeleRing (𝓞 L) L)ˣ,
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range a = c ∧
        ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a :=
  original_ideleClass_fixed_has_fixed_representative K L c hc

end

section

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]



/-- Exact original-object consumer of `original_intValuation_algebraMap_pow`. -/
theorem actual_original_norm_descent_original_intValuation_algebraMap_pow_source
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (r : R) :
    w.intValuation (algebraMap R S r) =
      v.intValuation r ^ v.asIdeal.ramificationIdx w.asIdeal :=
  original_intValuation_algebraMap_pow v w r

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `original_adicFieldMap_uniformContinuous`. -/
theorem actual_original_norm_descent_original_adicFieldMap_uniformContinuous_source :
    UniformContinuous (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) :=
  original_adicFieldMap_uniformContinuous K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_mem_integers`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_mem_integers_source (x : v.adicCompletion K) :
    originalAdicBaseChangeMap K L v w x ∈ w.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K :=
  originalAdicBaseChangeMap_mem_integers K L v w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_fixed`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_fixed_source (σ : Gal(L/K))
    (hσ : numberFieldGaloisPlaceEquiv K L σ w = w) (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ w w hσ
      (originalAdicBaseChangeMap K L v w x) = originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseChangeMap_fixed K L v w σ hσ x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_adicAbv_not_isEquiv_of_ne`. -/
theorem actual_original_norm_descent_original_adicAbv_not_isEquiv_of_ne_source
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) :=
  original_adicAbv_not_isEquiv_of_ne K hvw

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_finiteCompletions_dense`. -/
theorem actual_original_norm_descent_original_finiteCompletions_dense_source (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun v : S => algebraMap K (v.1.adicCompletion K) x) :=
  original_finiteCompletions_dense K S

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]



/-- Exact original-object consumer of `originalCompletionOrbitTrace_mem_base`. -/
theorem actual_original_norm_descent_originalCompletionOrbitTrace_mem_base_source [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (z : ∀ u : originalGaloisCompletionOrbit K L w, u.1.adicCompletion L) :
    originalCompletionOrbitTrace K L w z ∈ Set.range (originalAdicBaseChangeMap K L v w) :=
  originalCompletionOrbitTrace_mem_base K L v w z

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_range_iff_fixed_source (x : w.adicCompletion L) :
    x ∈ Set.range (originalAdicBaseChangeMap K L v w) ↔
      ∀ (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w),
        numberFieldGaloisLocalTransport K L σ w w hσ x = x :=
  originalAdicBaseChangeMap_range_iff_fixed K L v w x

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2 AddCommGroup.toAddCommMonoid
attribute [local instance] IsCyclic.commGroup
section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFinitePrimeBelow_preimage_finite`. -/
theorem actual_original_base_norm_originalFinitePrimeBelow_preimage_finite_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L w ∈ S}.Finite :=
  originalFinitePrimeBelow_preimage_finite K L S hS

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_transport`. -/
theorem actual_original_base_norm_originalAdicBaseChangeMap_transport_source
    (v : HeightOneSpectrum (𝓞 K)) (u w : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ u w hσ (originalAdicBaseChangeMap K L v u x) =
      originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseChangeMap_transport K L v u w σ hσ x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFiniteAdeleBaseChangeMap_fixed`. -/
theorem actual_original_base_norm_originalFiniteAdeleBaseChangeMap_fixed_source (σ : Gal(L/K)) (a : FiniteAdeleRing (𝓞 K) K) :
    numberFieldFiniteAdeleGaloisMap K L σ (originalFiniteAdeleBaseChangeMap K L a) =
      originalFiniteAdeleBaseChangeMap K L a :=
  originalFiniteAdeleBaseChangeMap_fixed K L σ a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteAdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalFiniteAdeleBaseChangeMap_range_iff_fixed_source (a : FiniteAdeleRing (𝓞 L) L) :
    a ∈ Set.range (originalFiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldFiniteAdeleGaloisMap K L σ a = a :=
  originalFiniteAdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



variable [NumberField K] [NumberField L]



/-- Exact original-object consumer of `originalInfiniteAdeleBaseChangeMap_isClosedEmbedding`. -/
theorem actual_original_base_norm_originalInfiniteAdeleBaseChangeMap_isClosedEmbedding_source :
    IsClosedEmbedding (originalInfiniteAdeleBaseChangeMap K L) :=
  originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalInfiniteAdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalInfiniteAdeleBaseChangeMap_range_iff_fixed_source (a : InfiniteAdeleRing L) :
    a ∈ Set.range (originalInfiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ a = a :=
  originalInfiniteAdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalAdeleBaseChangeMap_surjective_fixed`. -/
theorem actual_original_base_norm_originalAdeleBaseChangeMap_surjective_fixed_source [FiniteDimensional K L] [IsGalois K L]
    (a : AdeleRing (𝓞 L) L) (ha : ∀ σ : Gal(L/K), numberFieldAdeleGaloisMap K L σ a = a) :
    ∃ b : AdeleRing (𝓞 K) K, originalAdeleBaseChangeMap K L b = a :=
  originalAdeleBaseChangeMap_surjective_fixed K L a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalIdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalIdeleBaseChangeMap_range_iff_fixed_source [FiniteDimensional K L] [IsGalois K L]
    (a : (AdeleRing (𝓞 L) L)ˣ) :
    a ∈ Set.range (originalIdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a :=
  originalIdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalIdeleClassBaseChangeMap_range_iff_fixed_source (c : OriginalNumberFieldIdeleClassGroup L) :
    c ∈ Set.range (originalIdeleClassBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c :=
  originalIdeleClassBaseChangeMap_range_iff_fixed K L c

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleNorm_principal`. -/
theorem actual_original_base_norm_originalIdeleNorm_principal_source (x : Lˣ) :
    originalIdeleNorm K L (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele K (Units.map (Algebra.norm K (S := L)) x) :=
  originalIdeleNorm_principal K L x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_norm`. -/
theorem actual_original_base_norm_originalIdeleClassBaseChangeMap_norm_source (c : OriginalNumberFieldIdeleClassGroup L) :
    originalIdeleClassBaseChangeMap K L (originalIdeleClassNorm K L c) =
      ∏ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c :=
  originalIdeleClassBaseChangeMap_norm K L c

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassBaseInvariant_norm`. -/
theorem actual_original_base_norm_originalIdeleClassBaseInvariant_norm_source (g : Gal(L/K))
    (x : Additive (OriginalNumberFieldIdeleClassGroup L)) :
    (originalIdeleClassBaseInvariant K L g (originalIdeleClassNormLinear K L x)).val =
      (originalIdeleClassRep K L).norm.hom x :=
  originalIdeleClassBaseInvariant_norm K L g x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassNormQuotient_degree_nsmul_zero`. -/
theorem actual_original_base_norm_originalIdeleClassNormQuotient_degree_nsmul_zero_source (x : OriginalIdeleClassNormQuotient K L) :
    Module.finrank K L • x = 0 :=
  originalIdeleClassNormQuotient_degree_nsmul_zero K L x

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
attribute [local instance] IsCyclic.commGroup
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



variable [NumberField K] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicBaseFixedEquiv_val`. -/
theorem actual_original_local_norm_originalAdicBaseFixedEquiv_val_source (x : v.adicCompletion K) :
    (originalAdicBaseFixedEquiv K L v w x).val = originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseFixedEquiv_val K L v w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicNorm_galois_product`. -/
theorem actual_original_local_norm_originalAdicNorm_galois_product_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ x : w.adicCompletion L,
      originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K) x) =
        ∏ σ : OriginalFiniteDecompositionGroup K L w,
          numberFieldGaloisLocalTransport K L σ.val w w σ.property x :=
  originalAdicNorm_galois_product K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



variable [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_product`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    Units.map (originalAdicBaseChangeMap K L v w).toMonoidHom
        (numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a)) =
      ∏ σ : Gal(L/K), Units.map
        (numberFieldGaloisLocalTransport K L σ ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
          ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)).toMonoidHom
        (numberFieldIdeleFiniteComponent L ((numberFieldGaloisPlaceEquiv K L σ).symm w) a) :=
  originalIdeleNorm_finiteComponent_product K L v w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : HeightOneSpectrum (𝓞 L))



omit [NumberField K] [IsGalois K L] in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleFiniteOrbitNormPreimage_product`. -/
theorem actual_original_local_norm_originalIdeleFiniteOrbitNormPreimage_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    (∏ σ : Gal(L/K), numberFieldIdeleFiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)) =
      ∏ τ : OriginalFiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleFiniteOrbitNormPreimage_product K L w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_eq_localNorm`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_eq_localNorm_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a) =
        Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L))
          (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_finiteComponent_eq_localNorm K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (w : InfinitePlace L)



variable [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteCompletionBaseChange_range_iff_fixed`. -/
theorem actual_original_local_norm_originalInfiniteCompletionBaseChange_range_iff_fixed_source (x : w.Completion) :
    x ∈ Set.range (originalInfiniteCompletionBaseChange K L w) ↔
      ∀ (σ : Gal(L/K)) (hσ : σ • w = w), numberFieldGaloisArchimedeanTransport K L σ w w hσ x = x :=
  originalInfiniteCompletionBaseChange_range_iff_fixed K L w x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



variable [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteCompletionBaseFixedEquiv_val`. -/
theorem actual_original_local_norm_originalInfiniteCompletionBaseFixedEquiv_val_source (x : (w.comap (algebraMap K L)).Completion) :
    (originalInfiniteCompletionBaseFixedEquiv K L w x).val = originalInfiniteCompletionBaseChange K L w x :=
  originalInfiniteCompletionBaseFixedEquiv_val K L w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteNorm_galois_product`. -/
theorem actual_original_local_norm_originalInfiniteNorm_galois_product_source :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ x : w.Completion,
      originalInfiniteCompletionBaseChange K L w (Algebra.norm ((w.comap (algebraMap K L)).Completion) x) =
        ∏ σ : OriginalInfiniteDecompositionGroup K L w,
          numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property x :=
  originalInfiniteNorm_galois_product K L w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : InfinitePlace L)



omit [NumberField K] [IsGalois K L] in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleInfiniteOrbitNormPreimage_product`. -/
theorem actual_original_local_norm_originalIdeleInfiniteOrbitNormPreimage_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    (∏ σ : Gal(L/K), numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleInfiniteOrbitNormPreimage K L w a) :=
  originalIdeleInfiniteOrbitNormPreimage_product K L w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_infiniteComponent_eq_localNorm`. -/
theorem actual_original_local_norm_originalIdeleNorm_infiniteComponent_eq_localNorm_source :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
        Units.map (Algebra.norm ((w.comap (algebraMap K L)).Completion) (S := w.Completion))
          (originalIdeleInfiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_infiniteComponent_eq_localNorm K L w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicNorm_preimage_integerUnit`. -/
theorem actual_original_local_norm_originalAdicNorm_preimage_integerUnit_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ u : (w.adicCompletion L)ˣ,
      Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L)) u ∈
        (v.adicCompletionIntegers K).units → u ∈ (w.adicCompletionIntegers L).units :=
  originalAdicNorm_preimage_integerUnit K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



variable [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteLocal`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteLocal_source (w : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_finiteLocal K L w a

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdele_eq_of_components`. -/
theorem actual_original_local_norm_originalIdele_eq_of_components_source (a b : (AdeleRing (𝓞 K) K)ˣ)
    (hFin : ∀ v, numberFieldIdeleFiniteComponent K v a = numberFieldIdeleFiniteComponent K v b)
    (hInf : ∀ v, numberFieldIdeleInfiniteComponent K v a = numberFieldIdeleInfiniteComponent K v b) : a = b :=
  originalIdele_eq_of_components K a b hFin hInf

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteLocalNorm_baseChange`. -/
theorem actual_original_local_norm_originalInfiniteLocalNorm_baseChange_source (w : InfinitePlace L) (u : w.Completionˣ) :
    Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom
        (originalInfiniteLocalNorm K L w u) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom u :=
  originalInfiniteLocalNorm_baseChange K L w u

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_of_onePrime`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_of_onePrime_source (w : HeightOneSpectrum (𝓞 L))
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w →
      u ≠ w → numberFieldIdeleFiniteComponent L u a = 1) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (numberFieldIdeleFiniteComponent L w a) :=
  originalIdeleNorm_finiteComponent_of_onePrime K L w a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_infiniteComponent_of_onePlace`. -/
theorem actual_original_local_norm_originalIdeleNorm_infiniteComponent_of_onePlace_source (w : InfinitePlace L)
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w.comap (algebraMap K L) →
      u ≠ w → numberFieldIdeleInfiniteComponent L u a = 1) :
    numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
      originalInfiniteLocalNorm K L w (numberFieldIdeleInfiniteComponent L w a) :=
  originalIdeleNorm_infiniteComponent_of_onePlace K L w a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



variable [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_range_iff_local`. -/
theorem actual_original_local_norm_originalIdeleNorm_range_iff_local_source (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ (originalIdeleNorm K L).range ↔
      (∀ w : HeightOneSpectrum (𝓞 L), numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) a ∈
        (originalFiniteLocalNorm K L w).range) ∧
      (∀ w : InfinitePlace L, numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a ∈
        (originalInfiniteLocalNorm K L w).range) :=
  originalIdeleNorm_range_iff_local K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_degreePower`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_degreePower_source (w : HeightOneSpectrum (𝓞 L))
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ) :
    u ^ Module.finrank K L ∈ (originalFiniteLocalNorm K L w).range :=
  originalFiniteLocalNorm_degreePower K L w u

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `localIntegerUnit_norm_preimages_of_fixed_uniformizer`. -/
theorem actual_original_local_norm_localIntegerUnit_norm_preimages_of_fixed_uniformizer_source
    (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x :=
  localIntegerUnit_norm_preimages_of_fixed_uniformizer K L π hfixed hπ

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_integerUnit_of_unramified`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_integerUnit_of_unramified_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ)
    (hu : u ∈ ((originalFinitePrimeBelow K L w).adicCompletionIntegers K).units) :
    u ∈ (originalFiniteLocalNorm K L w).range :=
  originalFiniteLocalNorm_integerUnit_of_unramified K L w hw u hu

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_surjective_of_split`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_surjective_of_split_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalFiniteLocalNorm K L w) :=
  originalFiniteLocalNorm_surjective_of_split K L w hw

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdelePowerLocalUnitSubgroup_mem_iff`. -/
theorem actual_original_local_norm_originalIdelePowerLocalUnitSubgroup_mem_iff_source (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ originalIdelePowerLocalUnitSubgroup K n S T ↔
      (∀ w : InfinitePlace K, numberFieldIdeleInfiniteComponent K w a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        numberFieldIdeleFiniteComponent K v a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        numberFieldIdeleFiniteComponent K v a ∈ (v.adicCompletionIntegers K).units) :=
  originalIdelePowerLocalUnitSubgroup_mem_iff K n S T a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassPowerLocalUnitSubgroup_le_norm`. -/
theorem actual_original_local_norm_originalIdeleClassPowerLocalUnitSubgroup_le_norm_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L) S T ≤ (originalIdeleClassNorm K L).range :=
  originalIdeleClassPowerLocalUnitSubgroup_le_norm K L S T hT hAway

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged`. -/
theorem actual_original_local_norm_originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T ≤ (originalIdeleClassNorm K L).range :=
  originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged K L S T hT

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [local instance] IsCyclic.commGroup
section

variable (K : Type) [Field K] [NumberField K]



variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (S T : Finset (HeightOneSpectrum (𝓞 K)))
  (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
    OriginalFiniteDecompositionGroup K L w = ⊥)



include hT in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient`. -/
theorem actual_original_power_quotient_originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_source
    [Finite (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T)] :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) :=
  originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient K L S T hT

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedPowerClassMap_ker`. -/
theorem actual_original_power_quotient_originalSupportedPowerClassMap_ker_source (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (originalSupportedPowerClassMap K n S T).ker = originalSupportedPowerLocalUnitSubgroup K n S T :=
  originalSupportedPowerClassMap_ker K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedPowerLocalUnitQuotient_card`. -/
theorem actual_original_power_quotient_originalSupportedPowerLocalUnitQuotient_card_source :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      (∏ w : InfinitePlace K, Nat.card
        (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
      ∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range) :=
  originalSupportedPowerLocalUnitQuotient_card K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSUnitPowerLocalQuotientMap_injective`. -/
theorem actual_original_power_quotient_originalSUnitPowerLocalQuotientMap_injective_source :
    Function.Injective (originalSUnitPowerLocalQuotientMap K n S T) :=
  originalSUnitPowerLocalQuotientMap_injective K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedClassPowerQuotientMap_surjective`. -/
theorem actual_original_power_quotient_originalSupportedClassPowerQuotientMap_surjective_source
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Function.Surjective (originalSupportedClassPowerQuotientMap K n S T) :=
  originalSupportedClassPowerQuotientMap_surjective K n S T hS

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSUnitPowerLocalQuotient_card_mul_class`. -/
theorem actual_original_power_quotient_originalSUnitPowerLocalQuotient_card_mul_class_source
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalSUnitPowerLocalQuotient K n S T) *
        Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) =
      Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) :=
  originalSUnitPowerLocalQuotient_card_mul_class K n S T hS

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFinitePowerQuotient_finite`. -/
theorem actual_original_power_quotient_originalFinitePowerQuotient_finite_source (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Finite ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) :=
  originalFinitePowerQuotient_finite K v n hn

end

section

variable (K : Type) [Field K] (w : InfinitePlace K)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalComplexCompletionUnit_power_surjective`. -/
theorem actual_original_power_quotient_originalComplexCompletionUnit_power_surjective_source (hw : w.IsComplex)
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : w.Completionˣ →* w.Completionˣ) :=
  originalComplexCompletionUnit_power_surjective K w hw n hn

end

section

variable (K : Type) [Field K] (w : InfinitePlace K)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfinitePowerQuotient_card`. -/
theorem actual_original_power_quotient_originalInfinitePowerQuotient_card_source (n : ℕ) (hn : 0 < n) :
    Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even n then 2 else 1 :=
  originalInfinitePowerQuotient_card K w n hn

end

section

variable (K : Type) [Field K] [NumberField K]



variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support`. -/
theorem actual_original_power_quotient_originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑((S ∪ originalNormRamificationSupport K L) ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) :=
  originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support K L S T hT hS

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Filter Topology Metric
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]





/-- Exact original-object consumer of `normedField_power_norm_sub_eventually`. -/
theorem actual_original_power_index_normedField_power_norm_sub_eventually_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∀ᶠ x : K in 𝓝 1, ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ :=
  normedField_power_norm_sub_eventually K n hn

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]





/-- Exact original-object consumer of `normedField_power_small_closedBall`. -/
theorem actual_original_power_index_normedField_power_small_closedBall_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ s : ℝ, 0 < s → s ≤ r →
      Set.BijOn (fun x : K => x ^ n) (closedBall 1 s)
        (closedBall 1 (‖(n : K)‖ * s)) :=
  normedField_power_small_closedBall K n hn

end

section

variable {G : Type} [CommGroup G]





/-- Exact original-object consumer of `endomorphism_index_of_small_subgroup`. -/
theorem actual_original_power_index_endomorphism_index_of_small_subgroup_source (f : G →* G) (U : Subgroup G)
    [U.FiniteIndex] (hstable : U.map f ≤ U) (hker : U ⊓ f.ker = ⊥) :
    f.range.index = Nat.card f.ker * (U.map f).relIndex U :=
  endomorphism_index_of_small_subgroup f U hstable hker

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]





/-- Exact original-object consumer of `normedFieldSmallUnitSubgroup_isOpen`. -/
theorem actual_original_power_index_normedFieldSmallUnitSubgroup_isOpen_source (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    IsOpen (normedFieldSmallUnitSubgroup K r hr0.le hr1 : Set Kˣ) :=
  normedFieldSmallUnitSubgroup_isOpen K r hr0 hr1

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]





/-- Exact original-object consumer of `normedField_exists_small_unit_power_image`. -/
theorem actual_original_power_index_normedField_exists_small_unit_power_image_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ (r : ℝ) (_hr0 : 0 < r) (hr1 : r < 1), ∀ (s : ℝ) (hs0 : 0 < s) (hsr : s ≤ r),
      let hs1 : s < 1 := hsr.trans_lt hr1
      let ht1 : ‖(n : K)‖ * s < 1 :=
        (mul_le_of_le_one_left hs0.le (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt hs1
      let U := normedFieldSmallUnitSubgroup K s hs0.le hs1
      let V := normedFieldSmallUnitSubgroup K (‖(n : K)‖ * s)
        (mul_nonneg (norm_nonneg _) hs0.le) ht1
      U.map (powMonoidHom n : Kˣ →* Kˣ) = V ∧
        U ⊓ (powMonoidHom n : Kˣ →* Kˣ).ker = ⊥ :=
  normedField_exists_small_unit_power_image K n hn

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]



variable (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hs1 : s < 1)
  (hmul : s * s ≤ t)





include hmul in
/-- Exact original-object consumer of `normedFieldSmallUnit_relativeIndex`. -/
theorem actual_original_power_index_normedFieldSmallUnit_relativeIndex_source (ht1 : t < 1) :
    (normedFieldSmallUnitSubgroup K t ht.le ht1).relIndex
      (normedFieldSmallUnitSubgroup K s hs.le hs1) =
      Nat.card (normedFieldBallModule K s hs ⧸
        (normedFieldBallModule K t ht).comap (normedFieldBallModule K s hs).subtype) :=
  normedFieldSmallUnit_relativeIndex K s t hs ht hs1 hmul ht1

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallIntegerCoordinatesNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallIntegerCoordinatesUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- Exact original-object consumer of `localFieldIntegerBallEquiv_apply`. -/
theorem actual_original_power_index_localFieldIntegerBallEquiv_apply_source (a : K) (ha : a ≠ 0) (x : 𝒪[K]) :
    (localFieldIntegerBallEquiv K a ha x : K) = a * (x : K) :=
  localFieldIntegerBallEquiv_apply K a ha x

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallScalarQuotientNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallScalarQuotientUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- Exact original-object consumer of `localFieldBallScalarQuotient_card`. -/
theorem actual_original_power_index_localFieldBallScalarQuotient_card_source (a : K) (ha : a ≠ 0)
    (r : 𝒪[K]) (hr : r ≠ 0) :
    Nat.card (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha) ⧸
      (normedFieldBallModule K ‖(r : K) * a‖
        (norm_pos_iff.mpr (mul_ne_zero (by exact_mod_cast hr) ha))).comap
          (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha)).subtype) =
      Nat.card (𝒪[K] ⧸ (Ideal.span {r} : Ideal 𝒪[K])) :=
  localFieldBallScalarQuotient_card K a ha r hr

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexComplete : CompleteSpace K := localFieldOriginalNorm_complete K

/-- Exact original-object consumer of `localField_integerUnit_power_index`. -/
theorem actual_original_power_index_localField_integerUnit_power_index_source (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker *
        Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K])) :=
  localField_integerUnit_power_index K n hn

end

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (q : 𝒪[K]) (hq : Irreducible q)





/-- Exact original-object consumer of `localField_unitPower_index_uniformizer_factor`. -/
theorem actual_original_power_index_localField_unitPower_index_uniformizer_factor_source (n : ℕ) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) :=
  localField_unitPower_index_uniformizer_factor K n

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]





/-- Exact original-object consumer of `localField_unitPower_index_scalar_of_primitiveRoot`. -/
theorem actual_original_power_index_localField_unitPower_index_scalar_of_primitiveRoot_source
    (n : ℕ) (hn : (n : K) ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (n * Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K]))) :=
  localField_unitPower_index_scalar_of_primitiveRoot K n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))




/-- The actual ideal semiring, fixed for this exact consumer. -/
local instance originalScalarIdealSemiring : IdemCommSemiring (Ideal (v.adicCompletionIntegers K)) := Ideal.instIdemCommSemiring


/-- Exact original-object consumer of `originalAdic_natCast_span_eq_maximalIdeal_pow`. -/
theorem actual_original_power_index_originalAdic_natCast_span_eq_maximalIdeal_pow_source (n : ℕ) (hn : n ≠ 0) :
    (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K)) =
      @Monoid.npow (Ideal (v.adicCompletionIntegers K)) inferInstance
        (multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)}))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  originalAdic_natCast_span_eq_maximalIdeal_pow K v n hn

end

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))





/-- Exact original-object consumer of `originalAdic_natCast_quotient_card`. -/
theorem actual_original_power_index_originalAdic_natCast_quotient_card_source (n : ℕ) (hn : n ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)})) :=
  originalAdic_natCast_quotient_card K v n hn

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalFinitePowerQuotient_card`. -/
theorem actual_original_power_index_originalFinitePowerQuotient_card_source (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) =
      n * (n * Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)}))) :=
  originalFinitePowerQuotient_card K v n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalFinitePowerQuotient_product`. -/
theorem actual_original_power_index_originalFinitePowerQuotient_product_source (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range)) =
      n ^ (2 * S.card) * n ^ Module.finrank ℚ K :=
  originalFinitePowerQuotient_product K n hn ζ hζ S hS

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalInfinitePowerQuotient_product_mul_degree`. -/
theorem actual_original_power_index_originalInfinitePowerQuotient_product_mul_degree_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
        n ^ Module.finrank ℚ K = n ^ (2 * Fintype.card (InfinitePlace K)) :=
  originalInfinitePowerQuotient_product_mul_degree K n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalSupportedPowerLocalUnitQuotient_card_exact`. -/
theorem actual_original_power_index_originalSupportedPowerLocalUnitQuotient_card_exact_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) :=
  originalSupportedPowerLocalUnitQuotient_card_exact K n hn ζ hζ S T hS

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalClassPowerQuotient_card_of_selected_kernel`. -/
theorem actual_original_power_index_originalClassPowerQuotient_card_of_selected_kernel_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hLarge : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))))
    (hDisjoint : Disjoint S T)
    (hCount : T.card + 1 = Fintype.card (InfinitePlace K) + S.card)
    (hKernel : originalSUnitPowerLocalSubgroup K n S T =
      (powMonoidHom n : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range) :
    Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) = n :=
  originalClassPowerQuotient_card_of_selected_kernel K n hn ζ hζ S T hS hLarge hDisjoint hCount hKernel

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Filter Topology Metric
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K : Type) [Field K] {ι : Type} [Fintype ι]



/-- Exact original-object consumer of `finite_independent_absoluteValues_dense`. -/
theorem actual_original_prime_selection_finite_independent_absoluteValues_dense_source (abv : ι → AbsoluteValue K ℝ)
    (hNontrivial : ∀ i, (abv i).IsNontrivial)
    (hIndependent : Pairwise fun i j => ¬ (abv i).IsEquiv (abv j)) :
    DenseRange (algebraMap K (∀ i, WithAbs (abv i))) :=
  finite_independent_absoluteValues_dense K abv hNontrivial hIndependent

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_mixedCompletions_dense`. -/
theorem actual_original_prime_selection_original_mixedCompletions_dense_source (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun i : OriginalApproximationPlace K S =>
      algebraMap K (OriginalApproximationCompletion K S i) x) :=
  original_mixedCompletions_dense K S

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_principalUnit_open_approximation`. -/
theorem actual_original_prime_selection_original_principalUnit_open_approximation_source
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ)
    (U : ∀ i, Subgroup (OriginalApproximationCompletion K S i)ˣ)
    (hU : ∀ i, IsOpen (U i : Set (OriginalApproximationCompletion K S i)ˣ)) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈ U i :=
  original_principalUnit_open_approximation K S a U hU

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_principalUnit_power_approximation`. -/
theorem actual_original_prime_selection_original_principalUnit_power_approximation_source
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 0 < n)
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈
        (powMonoidHom n : (OriginalApproximationCompletion K S i)ˣ →*
          (OriginalApproximationCompletion K S i)ˣ).range :=
  original_principalUnit_power_approximation K S n hn a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassNorm_surjective_of_split_outside`. -/
theorem actual_original_prime_selection_originalIdeleClassNorm_surjective_of_split_outside_source
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalIdeleClassNorm K L) :=
  originalIdeleClassNorm_surjective_of_split_outside K L S hSplit

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeDegree_fullDecomposition_infinite`. -/
theorem actual_original_prime_selection_original_primeDegree_fullDecomposition_infinite_source
    (hp : (Module.finrank K L).Prime) :
    Set.Infinite {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 L),
      originalFinitePrimeBelow K L w = v ∧ OriginalFiniteDecompositionGroup K L w = ⊤} :=
  original_primeDegree_fullDecomposition_infinite K L hp

end

section

variable (G : Type) [CommGroup G] (p : ℕ) [Fact p.Prime]



/-- Exact original-object consumer of `primeExponent_exists_coordinates`. -/
theorem actual_original_prime_selection_primeExponent_exists_coordinates_source (r : ℕ)
    (hPower : ∀ g : G, g ^ p = 1) (hCard : Nat.card G = p ^ r) :
    Nonempty (G ≃* (Fin r → Multiplicative (ZMod p))) :=
  primeExponent_exists_coordinates G p r hPower hCard

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_exists_prime_sUnit_kummer_coordinates`. -/
theorem actual_original_prime_selection_numberField_exists_prime_sUnit_kummer_coordinates_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K E = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nonempty (f.ker ≃* (Fin (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) →
          Multiplicative (ZMod p))) :=
  numberField_exists_prime_sUnit_kummer_coordinates E p hDegree ζ hζ S₀

end

section

variable {G : Type} [Group G] {p r : ℕ}
  (e : G ≃* (Fin r → Multiplicative (ZMod p)))



/-- Exact original-object consumer of `primeCoordinateGenerator_iSup`. -/
theorem actual_original_prime_selection_primeCoordinateGenerator_iSup_source [NeZero p] :
    (⨆ i : Fin r, Subgroup.zpowers (primeCoordinateGenerator e i)) = ⊤ :=
  primeCoordinateGenerator_iSup e

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeOrder_fixedField_exists_fullDecomposition`. -/
theorem actual_original_prime_selection_original_primeOrder_fixedField_exists_fullDecomposition_source
    (p : ℕ) (hp : p.Prime) (g : Gal(L/K)) (hg : orderOf g = p)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤ :=
  original_primeOrder_fixedField_exists_fullDecomposition K L p hp g hg S

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeCoordinate_primes_distinct`. -/
theorem actual_original_prime_selection_original_primeCoordinate_primes_distinct_source
    (p : ℕ) (hp : p.Prime) (r : ℕ) (H : Subgroup Gal(L/K))
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : Fin r → HeightOneSpectrum (𝓞 L),
      Function.Injective (fun i => originalFinitePrimeBelow K L (w i)) ∧
      ∀ i, originalFinitePrimeBelow K L (w i) ∉ S ∧
        OriginalFiniteDecompositionGroup
          (IntermediateField.fixedField (Subgroup.zpowers (primeCoordinateGenerator e i).val)) L (w i) = ⊤ :=
  original_primeCoordinate_primes_distinct K L p hp r H e S

end


section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteDecomposition_isCyclic_of_unramified`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_isCyclic_of_unramified_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    IsCyclic (OriginalFiniteDecompositionGroup K L w) :=
  originalFiniteDecomposition_isCyclic_of_unramified K L w hw

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteDecomposition_eq_zpowers_of_relative_top`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_eq_zpowers_of_relative_top_source
    (p : ℕ) (hp : 0 < p) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (g : Gal(L/K)) (hg : orderOf g = p) (w : HeightOneSpectrum (𝓞 L))
    (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (hFull : OriginalFiniteDecompositionGroup
      (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤) :
    OriginalFiniteDecompositionGroup K L w = Subgroup.zpowers g :=
  originalFiniteDecomposition_eq_zpowers_of_relative_top K L p hp hPower g hg w hw hFull

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]



omit [NumberField L] in
/-- Exact original-object consumer of `originalFiniteDecomposition_below_eq_bot_of_le_ker`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_below_eq_bot_of_le_ker_source
    (w : HeightOneSpectrum (𝓞 L))
    (hD : OriginalFiniteDecompositionGroup K L w ≤ (AlgEquiv.restrictNormalHom E).ker) :
    OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w) = ⊥ :=
  originalFiniteDecomposition_below_eq_bot_of_le_ker K L E w hD

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeCoordinate_split_primeSet`. -/
theorem actual_original_prime_selection_original_primeCoordinate_split_primeSet_source
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
        OriginalFiniteDecompositionGroup K E v = ⊥ :=
  original_primeCoordinate_split_primeSet K L E p hp hPower r e S

end


section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalLocalKummer_power_iff_fixed`. -/
theorem actual_original_prime_selection_originalLocalKummer_power_iff_fixed_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ n = algebraMap K L (a : K)) :
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range ↔
    (β : L) ∈ IntermediateField.fixedField (OriginalFiniteDecompositionGroup K L w) :=
  originalLocalKummer_power_iff_fixed K L v w n hn ζ hζ a β hβ

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalLocalKummer_coordinates_iff_mem_subextension`. -/
theorem actual_original_prime_selection_originalLocalKummer_coordinates_iff_mem_subextension_source
    (E : IntermediateField K L) [IsGalois K E]
    (p : ℕ) (hp : 0 < p) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (r : ℕ) (e : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃*
      (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 L))
    (hD : ∀ i, OriginalFiniteDecompositionGroup K L (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ p = algebraMap K L (a : K)) :
    (∀ i, Units.map (algebraMap K ((originalFinitePrimeBelow K L (w i)).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom p : ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ →*
        ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ).range) ↔ (β : L) ∈ E :=
  originalLocalKummer_coordinates_iff_mem_subextension K L E p hp ζ hζ r e w hD a β hβ

end


end

end Dubon2026.SemanticRegression
