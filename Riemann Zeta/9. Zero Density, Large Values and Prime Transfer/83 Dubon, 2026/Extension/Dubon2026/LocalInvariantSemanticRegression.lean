import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `invariantCoefficientSequence_shortExact_of_first_zero`. -/
theorem actual_invariant_coefficient_exactness_invariantCoefficientSequence_shortExact_of_first_zero_source
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep.{0} k G)) (hX : X.ShortExact)
    (hzero : Limits.IsZero (groupCohomology X.X₁ 1)) :
    (X.map (Rep.invariantsFunctor k G)).ShortExact :=
  invariantCoefficientSequence_shortExact_of_first_zero X hX hzero

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]
  (X : ShortComplex (Rep.{0} k G)) (S : Subgroup G) [S.Normal]

/-- Exact original-object consumer of `normalInvariantCoefficientSequence_shortExact`. -/
theorem actual_normal_invariant_coefficient_sequence_normalInvariantCoefficientSequence_shortExact_source
    (hX : (X.map (Rep.resFunctor S.subtype)).ShortExact)
    (hzero : Limits.IsZero (groupCohomology (Rep.res S.subtype X.X₁) 1)) :
    (normalInvariantCoefficientSequence X S).ShortExact :=
  normalInvariantCoefficientSequence_shortExact X S hX hzero

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/-- Exact original-object consumer of `originalCoinducedInvariantDimensionShift_isIso`. -/
theorem actual_original_coinduced_global_dimension_shift_originalCoinducedInvariantDimensionShift_isIso_source (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    IsIso (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl) :=
  originalCoinducedInvariantDimensionShift_isIso A S hfirst

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_exact_three_module_card_dvd`. -/
theorem actual_finite_exact_module_divisibility_finite_exact_three_module_card_dvd_source
    {R A B C : Type} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Finite A] [Finite C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : f.range = g.ker) :
    Finite B ∧ Nat.card B ∣ Nat.card A * Nat.card C :=
  finite_exact_three_module_card_dvd f g hf hfg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `secondCohomology_normal_subgroup_card_dvd`. -/
theorem actual_second_cohomology_normal_subgroup_cardinality_secondCohomology_normal_subgroup_card_dvd_source
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
    [Finite (groupCohomology (A.quotientToInvariants S) 2)]
    [Finite (groupCohomology (Rep.res S.subtype A) 2)] :
    Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) ∣
        Nat.card (groupCohomology (A.quotientToInvariants S) 2) *
          Nat.card (groupCohomology (Rep.res S.subtype A) 2) :=
  secondCohomology_normal_subgroup_card_dvd A S hfirst

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalCohomologyReindex_isIso`. -/
theorem actual_original_group_cohomology_reindex_originalCohomologyReindex_isIso_source
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (e : G ≃* H) (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n) :=
  originalCohomologyReindex_isIso A e n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (S : Subgroup Gal(L/K))

/-- Exact original-object consumer of `galoisSubgroupUnit_first_cohomology_zero`. -/
theorem actual_galois_subgroup_unit_cohomology_galoisSubgroupUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) :=
  galoisSubgroupUnit_first_cohomology_zero S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisNormalInvariantUnitInclusion_bijective`. -/
theorem actual_galois_normal_invariant_unit_coefficients_galoisNormalInvariantUnitInclusion_bijective_source :
    Function.Bijective (galoisNormalInvariantUnitInclusion S).hom :=
  galoisNormalInvariantUnitInclusion_bijective S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisUnit_second_cohomology_fixedField_card_dvd`. -/
theorem actual_galois_fixed_field_second_cohomology_galoisUnit_second_cohomology_fixedField_card_dvd_source
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2) *
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2) :=
  galoisUnit_second_cohomology_fixedField_card_dvd S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `pGroup_exists_central_cyclic_reduction`. -/
theorem actual_p_group_central_cyclic_reduction_pGroup_exists_central_cyclic_reduction_source
    {G : Type} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    ∃ S : Subgroup G, S.Normal ∧ IsCyclic S ∧
      1 < Nat.card S ∧ S.index < Nat.card G :=
  pGroup_exists_central_cyclic_reduction hG

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_cyclic_second_cohomology_order`. -/
theorem actual_normed_local_field_cyclic_cohomology_normedLocalField_cyclic_second_cohomology_order_source
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [IsGalois K L] [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) :=
  normedLocalField_cyclic_second_cohomology_order K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_pGroup_second_cohomology_card_dvd`. -/
theorem actual_normed_local_field_p_group_second_cohomology_normedLocalField_pGroup_second_cohomology_card_dvd_source
    (p : ℕ) [Fact p.Prime]
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K)) :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  normedLocalField_pGroup_second_cohomology_card_dvd p K L hG

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `secondCohomology_card_dvd_of_sylows`. -/
theorem actual_second_cohomology_sylow_cardinality_secondCohomology_card_dvd_of_sylows_source
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep.{0} k G)
    (hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∧
        Nat.card (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∣ Nat.card P) :
    Finite (groupCohomology A 2) ∧ Nat.card (groupCohomology A 2) ∣ Nat.card G :=
  secondCohomology_card_dvd_of_sylows A hSylow

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_second_cohomology_card_dvd`. -/
theorem actual_normed_local_field_second_cohomology_bound_normedLocalField_second_cohomology_card_dvd_source
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  normedLocalField_second_cohomology_card_dvd K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_finite_galois_second_cohomology_card_dvd`. -/
theorem actual_local_field_finite_galois_second_cohomology_bound_localField_finite_galois_second_cohomology_card_dvd_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  localField_finite_galois_second_cohomology_card_dvd K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_finite_continuous_h2_card_dvd`. -/
theorem actual_local_field_finite_continuous_h2_bound_localField_finite_continuous_h2_card_dvd_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)] :
    Finite (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∧
      Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∣ Module.finrank K L :=
  localField_finite_continuous_h2_card_dvd K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {X : ShortComplex (Rep.{0} k H)} {Y : ShortComplex (Rep.{0} k G)}
  (f : G →* H) (φ : X.map (Rep.resFunctor f) ⟶ Y)

/-- Exact original-object consumer of `originalCohomologyGroupChange_delta_naturality`. -/
theorem actual_original_cohomology_group_change_naturality_originalCohomologyGroupChange_delta_naturality_source
    (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map f φ.τ₁ j =
      groupCohomology.map f φ.τ₃ i ≫ groupCohomology.δ hY i j hij :=
  originalCohomologyGroupChange_delta_naturality f φ hX hY i j hij

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]

/-- Exact original-object consumer of `originalCoinduced_delta_inflation`. -/
theorem actual_original_normal_sequence_cohomology_maps_originalCoinduced_delta_inflation_source
    (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl ≫
        groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 =
      (groupCohomology.H1InfRes (originalCoinducedQuotient A) S).f ≫
        groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl :=
  originalCoinduced_delta_inflation A S hfirst

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]
  (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
  (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))

/-- Exact original-object consumer of `originalSecondCohomology_inflation_restriction_exact`. -/
theorem actual_original_second_cohomology_inflation_restriction_originalSecondCohomology_inflation_restriction_exact_source :
    (originalSecondCohomologyInfRes A S hfirst).Exact :=
  originalSecondCohomology_inflation_restriction_exact A S hfirst

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalGroupChangeCohomology_isIso`. -/
theorem actual_original_group_change_cohomology_isomorphism_originalGroupChangeCohomology_isIso_source
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (B : Rep.{0} k G) (e : G ≃* H)
    (φ : Rep.res e.toMonoidHom A ⟶ B) [IsIso φ] (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom φ n) :=
  originalGroupChangeCohomology_isIso A B e φ n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisFixedFieldH2Inflation_mono`. -/
theorem actual_galois_fixed_field_h2_inflation_injection_galoisFixedFieldH2Inflation_mono_source :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom (IntermediateField.fixedField S))
      (finiteGaloisUnitTowerInclusion K (IntermediateField.fixedField S) L) 2) :=
  galoisFixedFieldH2Inflation_mono S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `galoisIntermediateFieldH2Inflation_mono`. -/
theorem actual_galois_intermediate_field_h2_inflation_injection_galoisIntermediateFieldH2Inflation_mono_source
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F] :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom F)
      (finiteGaloisUnitTowerInclusion K F L) 2) :=
  galoisIntermediateFieldH2Inflation_mono F

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]



/-- Exact original-object consumer of `galoisTowerKernelUnit_first_zero`. -/
theorem actual_full_local_invariant_2229_galoisTowerKernelUnit_first_zero_source [FiniteDimensional L M] :
    Limits.IsZero (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (Rep.ofAlgebraAutOnUnits K M)) 1) :=
  galoisTowerKernelUnit_first_zero K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `galoisTowerQuotientUnitInclusion_bijective`. -/
theorem actual_full_local_invariant_2230_galoisTowerQuotientUnitInclusion_bijective_source :
    Function.Bijective (galoisTowerQuotientUnitInclusion K L M).hom :=
  galoisTowerQuotientUnitInclusion_bijective K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `finiteGaloisUnitH2Inflation_mono`. -/
theorem actual_full_local_invariant_2231_finiteGaloisUnitH2Inflation_mono_source :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (finiteGaloisUnitTowerInclusion K L M) 2) :=
  finiteGaloisUnitH2Inflation_mono K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]



/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_injective`. -/
theorem actual_full_local_invariant_2232_finiteGaloisUnitTowerH2Inflation_injective_source :
    Function.Injective (finiteGaloisUnitTowerH2Inflation K L M) :=
  finiteGaloisUnitTowerH2Inflation_injective K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_injective`. -/
theorem actual_full_local_invariant_2233_galoisUnitFiniteStageH2Inflation_injective_source :
    Function.Injective (galoisUnitFiniteStageH2Inflation E) :=
  galoisUnitFiniteStageH2Inflation_injective E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `zmodAdditionCarry_sum_period`. -/
theorem actual_full_local_invariant_2234_zmodAdditionCarry_sum_period_source {n : ℕ} [NeZero n] (a : ZMod n)
    (N : ℕ) (hN : N • a = 0) :
    n * (∑ i ∈ Finset.range N, zmodAdditionCarry (i • a) a) = N * a.val :=
  zmodAdditionCarry_sum_period a N hN

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)



/-- Exact original-object consumer of `representationCarryCocycle_period_mul`. -/
theorem actual_full_local_invariant_2235_representationCarryCocycle_period_mul_source (g : G) (N : ℕ) (hN : g ^ N = 1) :
    n • representationCyclicTwoCochainPeriodSum A g N
        (representationCarryCocycle A χ a ha) =
      (N * (χ g).toAdd.val) • a :=
  representationCarryCocycle_period_mul A χ a ha g N hN

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localField_ramification_mul_residue_degree`. -/
theorem actual_full_local_invariant_2236_localField_ramification_mul_residue_degree_source :
    (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx (IsLocalRing.maximalIdeal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  localField_ramification_mul_residue_degree K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localFieldUnitOrder_algebraMap`. -/
theorem actual_full_local_invariant_2237_localFieldUnitOrder_algebraMap_source (u : Kˣ) :
    localFieldUnitOrder L (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u)) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) * localFieldUnitOrder K (Additive.ofMul u) :=
  localFieldUnitOrder_algebraMap K L u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

variable [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisUnitBaseChangeH2_mk`. -/
theorem actual_full_local_invariant_2238_finiteGaloisUnitBaseChangeH2_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitBaseChangeCocycle K E L M c) :=
  finiteGaloisUnitBaseChangeH2_mk K E L M c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_eq_pow_of_residue`. -/
theorem actual_full_local_invariant_2239_localFieldArithmeticFrobenius_eq_pow_of_residue_source (g : Gal(L/K)) (n : ℕ)
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n)) :
    g = localFieldArithmeticFrobenius K L ^ n :=
  localFieldArithmeticFrobenius_eq_pow_of_residue K L g n hg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]

variable [IsGalois K L] [IsGalois E M]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_baseChange`. -/
theorem actual_full_local_invariant_2240_localFieldArithmeticFrobenius_baseChange_source :
    galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) =
      localFieldArithmeticFrobenius K L ^ Module.finrank 𝓀[K] 𝓀[E] :=
  localFieldArithmeticFrobenius_baseChange K E L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ)

variable [IsCyclic Gal(L/K)] (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
attribute [local instance] IsCyclic.commGroup

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `galoisUnitCharacterCarryCocycle_period_mul`. -/
theorem actual_full_local_invariant_2241_galoisUnitCharacterCarryCocycle_period_mul_source :
    n • galoisUnitCyclicPeriodBase g hg (galoisUnitCharacterCarryCocycle χ u) =
      (orderOf g * (χ g).toAdd.val) • Additive.ofMul u :=
  galoisUnitCharacterCarryCocycle_period_mul χ u g hg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_characterCarry_smul`. -/
theorem actual_full_local_invariant_2242_localFieldPeriodRationalInvariant_characterCarry_smul_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    localFieldPeriodRationalInvariant K L
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        localFieldUnitOrder K (Additive.ofMul u) •
          rationalCyclicInvariant n (χ (localFieldArithmeticFrobenius K L)).toAdd :=
  localFieldPeriodRationalInvariant_characterCarry_smul K L χ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisUnitBaseChangeH2_characterCarry`. -/
theorem actual_full_local_invariant_2243_finiteGaloisUnitBaseChangeH2_characterCarry_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    finiteGaloisUnitBaseChangeH2 K E L M
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle
          (χ.comp (galoisBaseChangeRestriction K E L M))
          (Units.map (algebraMap K E).toMonoidHom u)) :=
  finiteGaloisUnitBaseChangeH2_characterCarry K E L M χ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_baseChange_characterCarry`. -/
theorem actual_full_local_invariant_2244_localFieldPeriodRationalInvariant_baseChange_characterCarry_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M
      (finiteGaloisUnitBaseChangeH2 K E L M
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
          Module.finrank K E • localFieldPeriodRationalInvariant K L
            (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) :=
  localFieldPeriodRationalInvariant_baseChange_characterCarry K E L M χ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldH2_exists_carry_representative`. -/
theorem actual_full_local_invariant_2245_localFieldH2_exists_carry_representative_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    ∃ u : Kˣ, Submodule.Quotient.mk (galoisUnitCarryCocycle
      (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) u) = x :=
  localFieldH2_exists_carry_representative K L x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_baseChange`. -/
theorem actual_full_local_invariant_2246_localFieldPeriodRationalInvariant_baseChange_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M (finiteGaloisUnitBaseChangeH2 K E L M x) =
      Module.finrank K E • localFieldPeriodRationalInvariant K L x :=
  localFieldPeriodRationalInvariant_baseChange K E L M x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]



/-- Exact original-object consumer of `baseChangedTensorFractionEmbedding_compositum`. -/
theorem actual_full_local_invariant_2247_baseChangedTensorFractionEmbedding_compositum_source
    {E L : Type*} [Field E] [Field L]
    [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
    (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
    (hi : i.comp (algebraMap B E) = algebraMap B Ω)
    (hj : j.comp (algebraMap A L) = f.toRingHom) :
    (baseChangedTensorFractionEmbedding (B := B) f).toRingHom.fieldRange =
      i.fieldRange ⊔ j.fieldRange :=
  baseChangedTensorFractionEmbedding_compositum f i j hi hj

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]
  {E L : Type*} [Field E] [Field L]
  [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
  (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
  (hi : i.comp (algebraMap B E) = algebraMap B Ω)
  (hj : j.comp (algebraMap A L) = f.toRingHom)
  (htop : i.fieldRange ⊔ j.fieldRange = ⊤)

variable [IsDedekindDomain B] [Module.Finite R A] [Algebra.FormallyUnramified R A]


include hi hj htop

/-- Exact original-object consumer of `integralClosure_formallyUnramified_of_baseChange_compositum_top`. -/
theorem actual_full_local_invariant_2248_integralClosure_formallyUnramified_of_baseChange_compositum_top_source
    (C : Type*) [CommRing C] [Algebra B C] [Algebra C Ω]
    [IsScalarTower B C Ω] [IsIntegralClosure C B Ω] :
    Algebra.FormallyUnramified B C :=
  integralClosure_formallyUnramified_of_baseChange_compositum_top f i j hi hj htop C

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



include K in
omit [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)] in
/-- Exact original-object consumer of `localField_integer_unramified_of_compositum`. -/
theorem actual_full_local_invariant_2249_localField_integer_unramified_of_compositum_source
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤) :
    Algebra.FormallyUnramified 𝒪[E] 𝒪[M] :=
  localField_integer_unramified_of_compositum K E L M htop

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `spectralIntegerExtension_formallyUnramified`. -/
theorem actual_full_local_invariant_2250_spectralIntegerExtension_formallyUnramified_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      spectralValuation_hasExtension K L
    Algebra.FormallyUnramified 𝒪[K] 𝒪[L] :=
  spectralIntegerExtension_formallyUnramified K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_exists_spectral_original_unramified_stage`. -/
theorem actual_full_local_invariant_2251_localField_exists_spectral_original_unramified_stage_source
    (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    (n : ℕ) [NeZero n] :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = n ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] :=
  localField_exists_spectral_original_unramified_stage K Ω n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralFiniteGalois_sup_unramified`. -/
theorem actual_full_local_invariant_2252_spectralFiniteGalois_sup_unramified_source (E F : FiniteGaloisIntermediateField K Ω)
    (hF :
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F]) :
    let H := E ⊔ F
    letI : Algebra E H :=
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left)).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left))
    letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
    letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
    letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
    letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
      normedFieldValuation_hasExtension E H
    Algebra.FormallyUnramified 𝒪[E] 𝒪[H] :=
  spectralFiniteGalois_sup_unramified E F hF

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]



/-- Exact original-object consumer of `galoisUnitTowerH2Restriction_kernel_composition`. -/
theorem actual_full_local_invariant_2253_galoisUnitTowerH2Restriction_kernel_composition_source [Normal K L] :
    galoisUnitTowerH2Restriction K L M ≫
      groupCohomology.map (galoisTowerKernelEquiv K L M).toMonoidHom
        (galoisTowerKernelUnitCoefficientIso K L M).hom 2 =
      groupCohomology.map (A := Rep.ofAlgebraAutOnUnits K M)
        (B := Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
          (Rep.ofAlgebraAutOnUnits K M))
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (𝟙 _) 2 :=
  galoisUnitTowerH2Restriction_kernel_composition K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `finiteGaloisUnitH2_inflation_exists_iff_restriction_zero`. -/
theorem actual_full_local_invariant_2254_finiteGaloisUnitH2_inflation_exists_iff_restriction_zero_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2) :
    (∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y = x) ↔
      galoisUnitTowerH2Restriction K L M x = 0 :=
  finiteGaloisUnitH2_inflation_exists_iff_restriction_zero K L M x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

variable [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `continuousDiscreteH2Equiv_finiteGaloisBaseChange`. -/
theorem actual_full_local_invariant_2255_continuousDiscreteH2Equiv_finiteGaloisBaseChange_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
      (discreteGaloisUnitAction_continuous (K := E) (Ω := M))
      (finiteGaloisUnitBaseChangeH2 K E L M x) =
        groupCohomology.map (galoisBaseChangeRestriction K E L M)
          (galoisUnitBaseChangeInclusion K E L M) 2
          (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
            (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) :=
  continuousDiscreteH2Equiv_finiteGaloisBaseChange K E L M x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
  [FiniteDimensional E M] [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero`. -/
theorem actual_full_local_invariant_2256_finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    (∃ y : GaloisUnitContinuousH2 (K := K) (Ω := E),
      finiteGaloisUnitTowerH2Inflation K E M y = finiteGaloisUnitTowerH2Inflation K L M x) ↔
        finiteGaloisUnitBaseChangeH2 K E L M x = 0 :=
  finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero K E L M x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K E] [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `localFieldH2_exists_unramified_compositum_representative`. -/
theorem actual_full_local_invariant_2257_localFieldH2_exists_unramified_compositum_representative_source
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤)
    (hdegree : Module.finrank K L = Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : FiniteDimensional K M := localField_field_module_finite
    ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := L),
      finiteGaloisUnitTowerH2Inflation K E M x = finiteGaloisUnitTowerH2Inflation K L M y :=
  localFieldH2_exists_unramified_compositum_representative K E L M htop hdegree x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralFiniteStageH2_exists_unramified_representative`. -/
theorem actual_full_local_invariant_2258_spectralFiniteStageH2_exists_unramified_representative_source
    (E : FiniteGaloisIntermediateField K Ω)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = Module.finrank K E ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
        ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
          galoisUnitFiniteStageH2Inflation E x = galoisUnitFiniteStageH2Inflation F y :=
  spectralFiniteStageH2_exists_unramified_representative E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_continuousH2_exists_unramified_stage`. -/
theorem actual_full_local_invariant_2259_localField_continuousH2_exists_unramified_stage_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F)
        (_ : IsNonarchimedeanLocalField F)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
          letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
          letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
          ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
            galoisUnitFiniteStageH2Inflation F y = x :=
  localField_continuousH2_exists_unramified_stage K Ω x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_mem_range_iff`. -/
theorem actual_full_local_invariant_2260_spectralUnramifiedStageInvariant_mem_range_iff_source (F : FiniteGaloisIntermediateField K Ω)
    (hF : SpectralStageUnramified K Ω F) (q : AddCircle (1 : ℚ)) :
    q ∈ (spectralUnramifiedStageInvariant K Ω F hF).range ↔ Module.finrank K F • q = 0 :=
  spectralUnramifiedStageInvariant_mem_range_iff K Ω F hF q

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_eq_of_inflation_eq`. -/
theorem actual_full_local_invariant_2261_spectralUnramifiedStageInvariant_eq_of_inflation_eq_source
    (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (x : GaloisUnitH2FiniteStage K Ω E) (y : GaloisUnitH2FiniteStage K Ω F)
    (hxy : galoisUnitH2FiniteStageMap K Ω E x = galoisUnitH2FiniteStageMap K Ω F y) :
    spectralUnramifiedStageInvariant K Ω E hE x =
      spectralUnramifiedStageInvariant K Ω F hF y :=
  spectralUnramifiedStageInvariant_eq_of_inflation_eq K Ω E F hE hF x y hxy

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralContinuousH2Invariant_existsUnique`. -/
theorem actual_full_local_invariant_2262_spectralContinuousH2Invariant_existsUnique_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃! q : AddCircle (1 : ℚ),
      ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hF : SpectralStageUnramified K Ω F,
        ∃ y : GaloisUnitH2FiniteStage K Ω F,
          galoisUnitH2FiniteStageMap K Ω F y = x ∧ spectralUnramifiedStageInvariant K Ω F hF y = q :=
  spectralContinuousH2Invariant_existsUnique K Ω x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralContinuousH2InvariantEquiv_stage`. -/
theorem actual_full_local_invariant_2263_spectralContinuousH2InvariantEquiv_stage_source
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (y : GaloisUnitH2FiniteStage K Ω F) :
    spectralContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F y) =
      spectralUnramifiedStageInvariant K Ω F hF y :=
  spectralContinuousH2InvariantEquiv_stage K Ω F hF y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localField_continuousH2_equivalent_rationalCircle`. -/
theorem actual_full_local_invariant_2264_localField_continuousH2_equivalent_rationalCircle_source :
    Nonempty (GaloisUnitContinuousH2 (K := K) (Ω := Ω) ≃ₗ[ℤ] AddCircle (1 : ℚ)) :=
  localField_continuousH2_equivalent_rationalCircle K Ω

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_valuative_extension_unique`. -/
theorem actual_local_invariant_functoriality_2265_localField_valuative_extension_unique_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v w : ValuativeRel L) (t u : TopologicalSpace L)
    (hv : letI := v; letI := t; IsNonarchimedeanLocalField L)
    (hw : letI := w; letI := u; IsNonarchimedeanLocalField L)
    (hvext : letI := v;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L))
    (hwext : letI := w;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)) : v = w :=
  localField_valuative_extension_unique K L v w t u hv hw hvext hwext

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_local_structures_eq_spectral`. -/
theorem actual_local_invariant_functoriality_2266_localField_local_structures_eq_spectral_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [v : ValuativeRel L] [t : TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    v = ValuativeRel.ofValuation (NormedField.valuation (K := L)) ∧
      t = (spectralNorm.uniformSpace K L).toTopologicalSpace :=
  localField_local_structures_eq_spectral K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_eq_original_period`. -/
theorem actual_local_invariant_functoriality_2267_spectralUnramifiedStageInvariant_eq_original_period_source
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    [v : ValuativeRel F] [t : TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    spectralUnramifiedStageInvariant K Ω F hF x = localFieldPeriodRationalInvariant K F x :=
  spectralUnramifiedStageInvariant_eq_original_period K Ω F hF x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_stage`. -/
theorem actual_local_invariant_functoriality_2268_localFieldContinuousH2InvariantEquiv_stage_source
    (F : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    localFieldContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      localFieldPeriodRationalInvariant K F x :=
  localFieldContinuousH2InvariantEquiv_stage K Ω F x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]



/-- Exact original-object consumer of `galoisBaseChangeRestriction_continuous`. -/
theorem actual_local_invariant_functoriality_2269_galoisBaseChangeRestriction_continuous_source [Algebra.IsAlgebraic E M] :
    Continuous (galoisBaseChangeRestriction K E L M) :=
  galoisBaseChangeRestriction_continuous K E L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]

variable [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_mk`. -/
theorem actual_local_invariant_functoriality_2270_continuousGaloisUnitBaseChangeH2_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    continuousGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousGaloisUnitBaseChangeCocycle K E L M c) :=
  continuousGaloisUnitBaseChangeH2_mk K E L M c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E F L M N : Type) [Field K] [Field E] [Field F] [Field L] [Field M] [Field N]
  [Algebra K E] [Algebra E F] [Algebra K F]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra E M] [Algebra E N] [Algebra F N]
  [Algebra L M] [Algebra M N] [Algebra L N]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsScalarTower E F N] [IsScalarTower E M N]
  [IsScalarTower K F N] [IsScalarTower K L N] [IsScalarTower L M N]
  [Normal K L] [Normal E M]

variable [IsGalois K L] [IsGalois E M] [IsGalois F N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F N)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_comp`. -/
theorem actual_local_invariant_functoriality_2271_continuousGaloisUnitBaseChangeH2_comp_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousGaloisUnitBaseChangeH2 E F M N (continuousGaloisUnitBaseChangeH2 K E L M x) =
      continuousGaloisUnitBaseChangeH2 K F L N x :=
  continuousGaloisUnitBaseChangeH2_comp K E F L M N x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_eq_finiteStage`. -/
theorem actual_local_invariant_functoriality_2272_continuousGaloisUnitBaseChangeH2_eq_finiteStage_source
    (F : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K K F Ω x = galoisUnitH2FiniteStageMap K Ω F x :=
  continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `finiteGaloisStageExtendScalars_coe`. -/
theorem actual_local_invariant_functoriality_2273_finiteGaloisStageExtendScalars_coe_source
    (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) :
    ((finiteGaloisStageExtendScalars E H hEH).toIntermediateField : Set Ω) =
      (H.toIntermediateField : Set Ω) :=
  finiteGaloisStageExtendScalars_coe E H hEH

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_finite_compositum`. -/
theorem actual_local_invariant_functoriality_2274_continuousGaloisUnitRestriction_finite_compositum_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 E E H Ω
        (finiteGaloisUnitBaseChangeH2 K E F H x) :=
  continuousGaloisUnitRestriction_finite_compositum E F H hEH hFH x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)



/-- Exact original-object consumer of `finiteGaloisStageExtendScalars_algebra_eq`. -/
theorem actual_local_invariant_functoriality_2275_finiteGaloisStageExtendScalars_algebra_eq_source :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    (inferInstance : Algebra E H) =
      (inferInstance : Algebra E (finiteGaloisStageExtendScalars E H hEH)) :=
  finiteGaloisStageExtendScalars_algebra_eq E H hEH

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `galoisUnitH2AlgebraCongruence_bijective`. -/
theorem actual_local_invariant_functoriality_2276_galoisUnitH2AlgebraCongruence_bijective_source
    {K L : Type} [Field K] [Field L] (a b : Algebra K L) (hab : a = b)
    (ha : letI := a; IsGalois K L) (hb : letI := b; IsGalois K L) :
    Function.Bijective (galoisUnitH2AlgebraCongruence a b hab ha hb) :=
  galoisUnitH2AlgebraCongruence_bijective a b hab ha hb

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)



/-- Exact original-object consumer of `finiteGaloisStageRebasedH2Equiv_bijective`. -/
theorem actual_local_invariant_functoriality_2277_finiteGaloisStageRebasedH2Equiv_bijective_source :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    Function.Bijective (finiteGaloisStageRebasedH2Equiv E H hEH) :=
  finiteGaloisStageRebasedH2Equiv_bijective E H hEH

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_rebased_stage`. -/
theorem actual_local_invariant_functoriality_2278_continuousGaloisUnitRestriction_rebased_stage_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω (finiteGaloisStageExtendScalars E H hEH)
        (finiteGaloisUnitBaseChangeH2 K E F H x) :=
  continuousGaloisUnitRestriction_rebased_stage E F H hEH hFH x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralFiniteGalois_sup_rebased_unramified`. -/
theorem actual_local_invariant_functoriality_2279_spectralFiniteGalois_sup_rebased_unramified_source (E F : FiniteGaloisIntermediateField K Ω)
    (hF :
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F]) :
    let H := E ⊔ F
    letI : Algebra E H := inferInstanceAs
      (Algebra E (finiteGaloisStageExtendScalars E H le_sup_left))
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
    letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
    letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
    letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
      normedFieldValuation_hasExtension E H
    Algebra.FormallyUnramified 𝒪[E] 𝒪[H] :=
  spectralFiniteGalois_sup_rebased_unramified E F hF

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousInvariant_restriction_on_stage`. -/
theorem actual_local_invariant_functoriality_2280_localFieldContinuousInvariant_restriction_on_stage_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel H]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace H]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField H]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)] :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ [_hextEH : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H)]
      [_hextFH : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H)]
      [_hunram : Algebra.FormallyUnramified 𝒪[E] 𝒪[H]] (y : GaloisUnitH2FiniteStage K Ω F),
      localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) := by
  letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  haveI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E H := FiniteDimensional.right K E H
  haveI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  intro hextEH hextFH hunram y
  exact localFieldContinuousInvariant_restriction_on_stage K Ω E F H hEH hFH
    (_hextEH := hextEH) (_hextFH := hextFH) (_hunram := hunram) y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_restriction`. -/
theorem actual_local_invariant_functoriality_2281_localFieldContinuousH2InvariantEquiv_restriction_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x :=
  localFieldContinuousH2InvariantEquiv_restriction K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
  (G : FiniteGaloisIntermediateField E Ω)
  [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_general_stage`. -/
theorem actual_local_invariant_functoriality_2282_continuousGaloisUnitRestriction_general_stage_source
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω G (finiteGaloisUnitBaseChangeH2 K E F G x) :=
  continuousGaloisUnitRestriction_general_stage E F G x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `intermediateField_compositum_splitting_polynomial`. -/
theorem actual_local_invariant_functoriality_2283_intermediateField_compositum_splitting_polynomial_source
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    ∃ q : Polynomial E, q.Separable ∧
      q.IsSplittingField E (IntermediateField.adjoin E (F.toIntermediateField : Set Ω)) :=
  intermediateField_compositum_splitting_polynomial E F

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousInvariant_restriction_general_stage`. -/
theorem actual_local_invariant_functoriality_2284_localFieldContinuousInvariant_restriction_general_stage_source
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
    (G : FiniteGaloisIntermediateField E Ω)
    [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField G]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G)]
    [(ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [Algebra.FormallyUnramified 𝒪[E] 𝒪[G]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (y : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) :=
  localFieldContinuousInvariant_restriction_general_stage K Ω E F G y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_finite_restriction`. -/
theorem actual_local_invariant_functoriality_2285_localFieldContinuousH2InvariantEquiv_finite_restriction_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x :=
  localFieldContinuousH2InvariantEquiv_finite_restriction K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G : Type} [Group G] (S : Subgroup G)



/-- Exact original-object consumer of `cosetTransition_mul`. -/
theorem actual_local_invariant_functoriality_2286_cosetTransition_mul_source (g h : G) (q : G ⧸ S) :
    cosetTransition S (g * h) q = cosetTransition S g (h • q) * cosetTransition S h q :=
  cosetTransition_mul S g h q

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

variable [Fintype (G ⧸ S)]



/-- Exact original-object consumer of `cosetTraceTwo_mem_cocycles`. -/
theorem actual_local_invariant_functoriality_2287_cosetTraceTwo_mem_cocycles_source
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    cosetTraceTwo A S c ∈ groupCohomology.cocycles₂ A :=
  cosetTraceTwo_mem_cocycles A S c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)



/-- Exact original-object consumer of `cosetTraceTwo_differential`. -/
theorem actual_local_invariant_functoriality_2288_cosetTraceTwo_differential_source [Fintype (G ⧸ S)] (f : S → A) :
    cosetTraceTwo A S (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) =
      groupCohomology.d₁₂ A (cosetTraceOne A S f) :=
  cosetTraceTwo_differential A S f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

variable [TopologicalSpace R] [ContinuousSMul R A]


include hA hS

/-- Exact original-object consumer of `continuousCosetTraceTwo_coboundary`. -/
theorem actual_local_invariant_functoriality_2289_continuousCosetTraceTwo_coboundary_source (f : C(S, A)) :
    continuousCosetTraceTwo A hA S hS
      (continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) f) =
      continuousRepresentationCoboundaryTwo A hA (continuousCosetTraceOne A hA S hS f) :=
  continuousCosetTraceTwo_coboundary A hA S hS f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)



/-- Exact original-object consumer of `cosetRestrictionHomotopy_differential`. -/
theorem actual_local_invariant_functoriality_2290_cosetRestrictionHomotopy_differential_source [Fintype (G ⧸ S)]
    (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (cosetRestrictionHomotopy A S c) =
      Fintype.card (G ⧸ S) • c.val - cosetTraceTwo A S (fun z => c (z.1, z.2)) :=
  cosetRestrictionHomotopy_differential A S c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousRepresentationH2Corestriction_restriction`. -/
theorem actual_local_invariant_functoriality_2291_continuousRepresentationH2Corestriction_restriction_source
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Corestriction A hA S hS
      (continuousRepresentationH2Restriction A hA S.subtype continuous_subtype_val x) =
        Fintype.card (G ⧸ S) • x :=
  continuousRepresentationH2Corestriction_restriction A hA S hS x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω)

variable [FiniteDimensional K E]



omit [FiniteDimensional K E] in
/-- Exact original-object consumer of `galoisFixingCosets_card`. -/
theorem actual_local_invariant_functoriality_2292_galoisFixingCosets_card_source [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)] :
    Fintype.card (Gal(Ω/K) ⧸ E.fixingSubgroup) = Module.finrank K E :=
  galoisFixingCosets_card K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [tK : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [tE : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



omit [IsGalois E Ω] in
/-- Exact original-object consumer of `galoisFixingUnitCocycle_coboundary`. -/
theorem actual_local_invariant_functoriality_2293_galoisFixingUnitCocycle_coboundary_source
    (f : C(Gal(Ω/E), Rep.ofAlgebraAutOnUnits E Ω)) :
    galoisFixingUnitCocycle K Ω E
      (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits E Ω)
        (discreteGaloisUnitAction_continuous (K := E) (Ω := Ω)) f) =
      continuousRepresentationCoboundaryTwo
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) E.fixingSubgroup.subtype)
        (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K Ω)
          E.fixingSubgroup.subtype continuous_subtype_val
          (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)))
        (galoisFixingUnitCochain K Ω E f) :=
  galoisFixingUnitCocycle_coboundary K Ω E f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `galoisFixingUnitH2_baseChange`. -/
theorem actual_local_invariant_functoriality_2294_galoisFixingUnitH2_baseChange_source (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisFixingUnitH2 K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
        E.fixingSubgroup.subtype continuous_subtype_val x :=
  galoisFixingUnitH2_baseChange K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `galoisUnitContinuousCorestriction_restriction`. -/
theorem actual_local_invariant_functoriality_2295_galoisUnitContinuousCorestriction_restriction_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisUnitContinuousCorestriction K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • x :=
  galoisUnitContinuousCorestriction_restriction K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2_restriction_surjective`. -/
theorem actual_local_invariant_functoriality_2296_localFieldContinuousH2_restriction_surjective_source :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    Function.Surjective (continuousGaloisUnitBaseChangeH2 K E Ω Ω) :=
  localFieldContinuousH2_restriction_surjective K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_corestriction`. -/
theorem actual_local_invariant_functoriality_2297_localFieldContinuousH2InvariantEquiv_corestriction_source :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ y : GaloisUnitContinuousH2 (K := E) (Ω := Ω),
      localFieldContinuousH2InvariantEquiv K Ω (galoisUnitContinuousCorestriction K Ω E y) =
        localFieldContinuousH2InvariantEquiv E Ω y :=
  localFieldContinuousH2InvariantEquiv_corestriction K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K E] [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]


/-- Exact original-object consumer of `localFieldH2_unramified_descends_iff`. -/
theorem actual_relative_fundamental_2298_localFieldH2_unramified_descends_iff_source
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤)
    (y : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K M := localField_field_module_finite
    (∃ x : GaloisUnitContinuousH2 (K := K) (Ω := E),
      finiteGaloisUnitTowerH2Inflation K E M x = finiteGaloisUnitTowerH2Inflation K L M y) ↔
        Module.finrank K E • localFieldPeriodRationalInvariant K L y = 0 :=
  localFieldH2_unramified_descends_iff K E L M htop y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `spectralUnramifiedStageH2_descends_same_degree`. -/
theorem actual_relative_fundamental_2299_spectralUnramifiedStageH2_descends_same_degree_source
    (E F : FiniteGaloisIntermediateField K Ω)
    (hdegree : Module.finrank K F = Module.finrank K E)
    (hF : SpectralStageUnramified K Ω F) (y : GaloisUnitH2FiniteStage K Ω F) :
    ∃ x : GaloisUnitH2FiniteStage K Ω E,
      galoisUnitH2FiniteStageMap K Ω E x = galoisUnitH2FiniteStageMap K Ω F y :=
  spectralUnramifiedStageH2_descends_same_degree E F hdegree hF y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `spectralFiniteStageFullInvariant_mem_range_iff`. -/
theorem actual_relative_fundamental_2300_spectralFiniteStageFullInvariant_mem_range_iff_source
    (E : FiniteGaloisIntermediateField K Ω) (q : AddCircle (1 : ℚ)) :
    q ∈ (spectralFiniteStageFullInvariant K Ω E).range ↔ Module.finrank K E • q = 0 :=
  spectralFiniteStageFullInvariant_mem_range_iff K Ω E q

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `spectralFiniteStageH2_card`. -/
theorem actual_relative_fundamental_2301_spectralFiniteStageH2_card_source (E : FiniteGaloisIntermediateField K Ω) :
    Nat.card (GaloisUnitH2FiniteStage K Ω E) = Module.finrank K E :=
  spectralFiniteStageH2_card K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `spectralFiniteStageFundamentalClass_generates`. -/
theorem actual_relative_fundamental_2302_spectralFiniteStageFundamentalClass_generates_source
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    ∃ j : ℤ, j • spectralFiniteStageFundamentalClass K Ω E = x :=
  spectralFiniteStageFundamentalClass_generates K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `spectralFiniteStageFundamentalClass_transition`. -/
theorem actual_relative_fundamental_2303_spectralFiniteStageFundamentalClass_transition_source
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (spectralFiniteStageFundamentalClass K Ω E) =
      Module.finrank E F • spectralFiniteStageFundamentalClass K Ω F :=
  spectralFiniteStageFundamentalClass_transition K Ω E F hEF

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `localFieldFiniteStageInvariant_mem_range_iff`. -/
theorem actual_relative_fundamental_2304_localFieldFiniteStageInvariant_mem_range_iff_source
    (E : FiniteGaloisIntermediateField K Ω) (q : AddCircle (1 : ℚ)) :
    q ∈ (localFieldFiniteStageInvariant K Ω E).range ↔ Module.finrank K E • q = 0 :=
  localFieldFiniteStageInvariant_mem_range_iff K Ω E q

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `localFieldFiniteStageH2_card`. -/
theorem actual_relative_fundamental_2305_localFieldFiniteStageH2_card_source (E : FiniteGaloisIntermediateField K Ω) :
    Nat.card (GaloisUnitH2FiniteStage K Ω E) = Module.finrank K E :=
  localFieldFiniteStageH2_card K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `localFieldFiniteStageFundamentalClass_generates`. -/
theorem actual_relative_fundamental_2306_localFieldFiniteStageFundamentalClass_generates_source
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    ∃ j : ℤ, j • localFieldFiniteStageFundamentalClass K Ω E = x :=
  localFieldFiniteStageFundamentalClass_generates K Ω E x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- Exact original-object consumer of `localFieldFiniteStageFundamentalClass_transition`. -/
theorem actual_relative_fundamental_2307_localFieldFiniteStageFundamentalClass_transition_source
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (localFieldFiniteStageFundamentalClass K Ω E) =
      Module.finrank E F • localFieldFiniteStageFundamentalClass K Ω F :=
  localFieldFiniteStageFundamentalClass_transition K Ω E F hEF

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicNormQuotient_card`. -/
theorem actual_relative_fundamental_2308_localFieldFiniteCyclicNormQuotient_card_source :
    Nat.card (Additive Kˣ ⧸ LinearMap.range
      (galoisUnitFieldNormLinear (K := K) (L := E))) = Module.finrank K E :=
  localFieldFiniteCyclicNormQuotient_card K Ω E

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicNormResidue_eq_zero_iff`. -/
theorem actual_relative_fundamental_2309_localFieldFiniteCyclicNormResidue_eq_zero_iff_source (u : Additive Kˣ) :
    localFieldFiniteCyclicNormResidue K Ω E g hg u = 0 ↔
      ∃ v : Eˣ, Units.map (Algebra.norm K (S := E)) v = u.toMul :=
  localFieldFiniteCyclicNormResidue_eq_zero_iff K Ω E g hg u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (E : FiniteGaloisIntermediateField K Ω)

variable [IsGalois K Ω] [IsSepClosed Ω] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCharacterCarryClass_eq_period`. -/
theorem actual_relative_fundamental_2310_localFieldFiniteCharacterCarryClass_eq_period_source
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldFiniteCharacterCarryClass K Ω E χ u =
      (∑ i ∈ Finset.range (orderOf g),
        zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) •
          (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm
            (Submodule.Quotient.mk (Additive.ofMul u)) :=
  localFieldFiniteCharacterCarryClass_eq_period K Ω E g hg χ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise





/-- Exact original-object consumer of `cyclicCharacter_rationalInvariant_pairing`. -/
theorem actual_relative_fundamental_2311_cyclicCharacter_rationalInvariant_pairing_source
    {G : Type} [Group G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {N n : ℕ} [NeZero N] [NeZero n] (hN : Nat.card G = N)
    (χ : G →* Multiplicative (ZMod n)) (j : ZMod N) :
    rationalCyclicInvariant n
      (χ (zmodMulEquivOfGenerator hg hN (Multiplicative.ofAdd j))).toAdd =
        (∑ i ∈ Finset.range (orderOf g),
          zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) •
            rationalCyclicInvariant N j :=
  cyclicCharacter_rationalInvariant_pairing g hg hN χ j

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicNormResidue_generator_independent`. -/
theorem actual_relative_fundamental_2312_localFieldFiniteCyclicNormResidue_generator_independent_source
    (g h : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hh : ∀ x, x ∈ Subgroup.zpowers h) (u : Additive Kˣ) :
    localFieldFiniteCyclicNormResidue K Ω E g hg u =
      localFieldFiniteCyclicNormResidue K Ω E h hh u :=
  localFieldFiniteCyclicNormResidue_generator_independent K Ω E g h hg hh u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_eq_zero_iff`. -/
theorem actual_relative_fundamental_2313_localFieldFiniteCyclicReciprocity_eq_zero_iff_source (u : Additive Kˣ) :
    localFieldFiniteCyclicReciprocity K Ω E u = 0 ↔
      ∃ v : Eˣ, Units.map (Algebra.norm K (S := E)) v = u.toMul :=
  localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω E u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_frobenius`. -/
theorem actual_relative_fundamental_2314_localFieldFiniteCyclicReciprocity_frobenius_source (u : Kˣ) :
    letI : IsCyclic Gal(E/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
    localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u) =
      Additive.ofMul ((localFieldArithmeticFrobenius K E) ^
        localFieldUnitOrder K (Additive.ofMul u)) :=
  localFieldFiniteCyclicReciprocity_frobenius K Ω E u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]


/-- Exact original-object consumer of `localFieldFiniteCharacterCarryClass_transition`. -/
theorem actual_relative_fundamental_2315_localFieldFiniteCharacterCarryClass_transition_source
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      localFieldFiniteCharacterCarryClass K Ω F
        (χ.comp (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))) u :=
  localFieldFiniteCharacterCarryClass_transition K Ω E F hEF χ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `localFieldFiniteCyclicReciprocity_restrict`. -/
theorem actual_relative_fundamental_2316_localFieldFiniteCyclicReciprocity_restrict_source
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    [IsCyclic Gal(E/K)] [IsCyclic Gal(F/K)] (u : Kˣ) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    AlgEquiv.restrictNormalHom E
      (localFieldFiniteCyclicReciprocity K Ω F (Additive.ofMul u)).toMul =
        (localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u)).toMul :=
  localFieldFiniteCyclicReciprocity_restrict K Ω E F hEF u

end

section

open Matrix
open scoped NumberField WithZero

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localFieldRootH2Invariant_mem_range_iff`. -/
theorem actual_local_cup_2317_localFieldRootH2Invariant_mem_range_iff_source (q : AddCircle (1 : ℚ)) :
    q ∈ (localFieldRootH2Invariant K Ω n).range ↔ n • q = 0 :=
  localFieldRootH2Invariant_mem_range_iff K Ω n q

end

section

open Matrix
open scoped NumberField WithZero

variable (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Exact original-object consumer of `rationalPrimeRootH2CyclicEquiv_invariant`. -/
theorem actual_local_cup_2318_rationalPrimeRootH2CyclicEquiv_invariant_source
    (x : GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) n) :
    rationalCyclicInvariant n (rationalPrimeRootH2CyclicEquiv p hp n x) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
          (Ω := rationalPrimeLocalClosure p hp) n x) :=
  rationalPrimeRootH2CyclicEquiv_invariant p hp n x

end

section

open Matrix
open scoped NumberField WithZero

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) (B : Rep S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (e : A ≃+ B) (he : Continuous e) (hei : Continuous e.symm)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousH2AdditiveCoefficientEquiv_mk`. -/
theorem actual_local_cup_2319_continuousH2AdditiveCoefficientEquiv_mk_source (c : continuousRepresentationCocyclesTwo A) :
    continuousH2AdditiveCoefficientEquiv A B e he hei heρ hA hB
      (Submodule.Quotient.mk c) =
        Submodule.Quotient.mk (continuousCocycleTwoAdditiveEquiv A B e he hei heρ c) :=
  continuousH2AdditiveCoefficientEquiv_mk A B e he hei heρ hA hB c

end

section

open Matrix
open scoped NumberField WithZero

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]

variable
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Exact original-object consumer of `rationalPrimeCyclotomicH2ScalarEquiv_invariant`. -/
theorem actual_local_cup_2320_rationalPrimeCyclotomicH2ScalarEquiv_invariant_source
    (x : ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalPrimeCyclotomicH2ScalarEquiv p hp q x) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
          (Ω := rationalPrimeLocalClosure p hp) q
          (rationalPrimeCyclotomicH2RootEquiv p hp q x)) :=
  rationalPrimeCyclotomicH2ScalarEquiv_invariant p hp q x

end

section

open Matrix
open scoped NumberField WithZero

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : (rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
    rationalPrimeLocalClosure p hp) →* GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)

omit ρ hρ in
/-- Exact original-object consumer of `rationalArithmeticTraceH1ScalarCup_prime_restriction`. -/
theorem actual_local_cup_2321_rationalArithmeticTraceH1ScalarCup_prime_restriction_source
    (a : 𝓞 ℚ) (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
    (hσ : Continuous σ)
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)) =
      rationalPrimeTraceH1ScalarCup p hp q (σ.comp j.toMonoidHom)
        (hσ.comp j.continuous)
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y) :=
  rationalArithmeticTraceH1ScalarCup_prime_restriction p hp q a hqa σ hσ x y

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousRootOneCocycle_exists_radical`. -/
theorem actual_local_kummer_2322_continuousRootOneCocycle_exists_radical_source
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    ∃ (a : Kˣ) (β : Ωˣ),
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ g : Gal(Ω/K), g • β / β =
        ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) :=
  continuousRootOneCocycle_exists_radical n c

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (a : Kˣ) (β : Ωˣ) (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)

/-- Exact original-object consumer of `galoisRootRadicalOneCocycle_class_zero_iff`. -/
theorem actual_local_kummer_2323_galoisRootRadicalOneCocycle_class_zero_iff_source :
    (Submodule.Quotient.mk (galoisRootRadicalOneCocycle n a β hβ) :
      ContinuousRepresentationH1
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
        (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) = 0 ↔
      a ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
  galoisRootRadicalOneCocycle_class_zero_iff n a β hβ

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisKummerH1Equiv_apply`. -/
theorem actual_local_kummer_2324_galoisKummerH1Equiv_apply_source (a : Kˣ) :
    galoisKummerH1Equiv (Ω := Ω) n
      (Additive.ofMul (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a)) =
        galoisKummerH1Class n a :=
  galoisKummerH1Equiv_apply (Ω := Ω) n a

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (n : ℕ) [NeZero n]

/-- Exact original-object consumer of `galoisRootExponentPairing_equivariant`. -/
theorem actual_local_kummer_2325_galoisRootExponentPairing_equivariant_source (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (t : ZMod n) :
    galoisRootExponentPairing n
      ((galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x)
      ((Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))).ρ g t) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g
      (galoisRootExponentPairing n x t) :=
  galoisRootExponentPairing_equivariant n g x t

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))

/-- Exact original-object consumer of `continuousGaloisRootCharacterH1Cup_mk`. -/
theorem actual_local_kummer_2326_continuousGaloisRootCharacterH1Cup_mk_source
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    continuousGaloisRootCharacterH1Cup n χ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousGaloisRootCharacterCupCocycle n χ c) :=
  continuousGaloisRootCharacterH1Cup_mk n χ c

end

end Dubon2026.SemanticRegression
