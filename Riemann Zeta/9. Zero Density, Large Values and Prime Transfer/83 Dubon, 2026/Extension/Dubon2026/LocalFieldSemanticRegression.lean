import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology



section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `galoisUnitH2FiniteTransition_comp`. -/
theorem actual_galois_unit_h2_finite_directed_system_galoisUnitH2FiniteTransition_comp_source (E F H : FiniteGaloisIntermediateField K Ω)
    (hEF : E ≤ F) (hFH : F ≤ H) (x : GaloisUnitH2FiniteStage K Ω E) :
    galoisUnitH2FiniteTransition K Ω F H hFH
        (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      galoisUnitH2FiniteTransition K Ω E H (hEF.trans hFH) x :=
  galoisUnitH2FiniteTransition_comp K Ω E F H hEF hFH x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitH2FiniteColimitToH2_of`. -/
theorem actual_galois_unit_h2_finite_colimit_map_galoisUnitH2FiniteColimitToH2_of_source (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitToH2 K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x :=
  galoisUnitH2FiniteColimitToH2_of K Ω F x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitH2FiniteColimitEquiv_of`. -/
theorem actual_galois_unit_h2_finite_colimit_equiv_galoisUnitH2FiniteColimitEquiv_of_source (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitEquiv K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x :=
  galoisUnitH2FiniteColimitEquiv_of K Ω F x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (g : G) (n : ℕ)

/-- Exact original-object consumer of `representationCyclicTwoCochainPeriodSum_coboundary`. -/
theorem actual_cyclic_two_cocycle_period_sum_representationCyclicTwoCochainPeriodSum_coboundary_source (hn : g ^ n = 1)
    (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g n (groupCohomology.d₁₂ A b) =
      ∑ i ∈ Finset.range n, A.ρ (g ^ i) (b g) :=
  representationCyclicTwoCochainPeriodSum_coboundary A g n hn b

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg

/-- Exact original-object consumer of `representationCyclicPeriodSum_coboundary_eq_norm`. -/
theorem actual_cyclic_generator_norm_sum_representationCyclicPeriodSum_coboundary_eq_norm_source (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g (orderOf g) (groupCohomology.d₁₂ A b) =
      A.ρ.norm (b g) :=
  representationCyclicPeriodSum_coboundary_eq_norm A g hg b

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `galoisGeneratorInvariantBaseEquiv_symm_coefficient`. -/
theorem actual_galois_generator_invariant_base_equiv_galoisGeneratorInvariantBaseEquiv_symm_coefficient_source
    (x : LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    galoisUnitsBaseCoefficient (L := L)
      ((galoisGeneratorInvariantBaseEquiv g hg).symm x).toMul = x.val :=
  galoisGeneratorInvariantBaseEquiv_symm_coefficient g hg x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `galoisUnitCyclicPeriodBase_coboundary`. -/
theorem actual_galois_unit_cyclic_period_base_galoisUnitCyclicPeriodBase_coboundary_source
    (b : C(Gal(L/K), Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase g hg
        (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) b) =
      Additive.ofMul (Units.map (Algebra.norm K (S := L))
        (Additive.toMul (Rep.toAdditive (b g)))) :=
  galoisUnitCyclicPeriodBase_coboundary g hg b

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `cyclicGaloisH2PeriodNormMap_mk`. -/
theorem actual_cyclic_galois_h2_period_norm_map_cyclicGaloisH2PeriodNormMap_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    cyclicGaloisH2PeriodNormMap g hg (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (galoisUnitCyclicPeriodBase g hg c) :=
  cyclicGaloisH2PeriodNormMap_mk g hg c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `zmodAdditionCarry_sum_one`. -/
theorem actual_z_mod_addition_carry_zmodAdditionCarry_sum_one_source {n : ℕ} (hn : 1 < n) :
    ∑ i ∈ Finset.range n, zmodAdditionCarry (i : ZMod n) 1 = 1 :=
  zmodAdditionCarry_sum_one hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- Exact original-object consumer of `representationCarryCocycle_apply`. -/
theorem actual_representation_carry_cocycle_representationCarryCocycle_apply_source (x y : G) :
    representationCarryCocycle A χ a ha (x, y) =
      zmodAdditionCarry (χ x).toAdd (χ y).toAdd • a :=
  representationCarryCocycle_apply A χ a ha x y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- Exact original-object consumer of `representationCarryCocycle_period`. -/
theorem actual_representation_carry_period_representationCarryCocycle_period_source (g : G)
    (hχ : χ g = Multiplicative.ofAdd 1) (hn : 1 < n) :
    representationCyclicTwoCochainPeriodSum A g n
      (representationCarryCocycle A χ a ha) = a :=
  representationCarryCocycle_period A χ a ha g hχ hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `galoisUnitCarryCocycle_period`. -/
theorem actual_galois_unit_carry_cocycle_galoisUnitCarryCocycle_period_source (u : Kˣ) (hn : 1 < Nat.card Gal(L/K)) :
    galoisUnitCyclicPeriodBase g hg (galoisUnitCarryCocycle g hg u) = Additive.ofMul u :=
  galoisUnitCarryCocycle_period g hg u hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `cyclicGaloisH2PeriodNormMap_bijective`. -/
theorem actual_cyclic_galois_h2_period_surjective_cyclicGaloisH2PeriodNormMap_bijective_source
    [Finite (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)))] :
    Function.Bijective (cyclicGaloisH2PeriodNormMap g hg) :=
  cyclicGaloisH2PeriodNormMap_bijective g hg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `representationCyclicTwoCochainPeriodSum_repeat`. -/
theorem actual_cyclic_generator_repeated_period_representationCyclicTwoCochainPeriodSum_repeat_source
    {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (g : G) (n : ℕ) (hn : g ^ n = 1) (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum A g (n * k) c =
      k • representationCyclicTwoCochainPeriodSum A g n c :=
  representationCyclicTwoCochainPeriodSum_repeat A g n hn k c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `localFieldPeriodH2Equiv_mk`. -/
theorem actual_local_field_period_h2_equiv_localFieldPeriodH2Equiv_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodH2Equiv K L (Submodule.Quotient.mk c) =
      (localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) :
          ZMod (Module.finrank K L)) :=
  localFieldPeriodH2Equiv_mk K L c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_mk`. -/
theorem actual_local_field_period_rational_invariant_localFieldPeriodRationalInvariant_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodRationalInvariant K L (Submodule.Quotient.mk c) =
      ↑((localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) : ℚ) /
          Module.finrank K L) :=
  localFieldPeriodRationalInvariant_mk K L c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `representationCyclicPeriod_inflation`. -/
theorem actual_representation_period_inflation_representationCyclicPeriod_inflation_source
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (A : Rep R G) (B : Rep R H) (φ : H →* G) (j : A →ₗ[R] B)
    (g : G) (h : H) (hφ : φ h = g) (n : ℕ) (hn : g ^ n = 1)
    (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum B h (n * k)
        (fun p => j (c (φ p.1, φ p.2))) =
      k • j (representationCyclicTwoCochainPeriodSum A g n c) :=
  representationCyclicPeriod_inflation A B φ j g h hφ n hn k c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
  (h : Gal(M/K)) (hh : ∀ x, x ∈ Subgroup.zpowers h)

/-- Exact original-object consumer of `galoisUnitCyclicPeriodBase_tower`. -/
theorem actual_galois_unit_period_tower_galoisUnitCyclicPeriodBase_tower_source
    (hrestrict : AlgEquiv.restrictNormalHom L h = g)
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase h hh (finiteGaloisUnitTowerCocycleInflation K L M c) =
      Module.finrank L M • galoisUnitCyclicPeriodBase g hg c :=
  galoisUnitCyclicPeriodBase_tower K L M g hg h hh hrestrict c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_inflation`. -/
theorem actual_local_field_period_invariant_inflation_localFieldPeriodRationalInvariant_inflation_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional K M := localField_field_module_finite
    localFieldPeriodRationalInvariant K M (finiteGaloisUnitTowerH2Inflation K L M x) =
      localFieldPeriodRationalInvariant K L x :=
  localFieldPeriodRationalInvariant_inflation K L M x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_residue_extension_polynomial`. -/
theorem actual_local_field_residue_extension_polynomial_localField_exists_integral_residue_extension_polynomial_source
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ F : 𝒪[K][X], F.Monic ∧ F.natDegree = n ∧
      (F.map (IsLocalRing.residue 𝒪[K])).natDegree = n ∧
      Irreducible (F.map (IsLocalRing.residue 𝒪[K])) ∧
      (F.map (IsLocalRing.residue 𝒪[K])).Separable ∧
      Irreducible (F.map (algebraMap 𝒪[K] K)) :=
  localField_exists_integral_residue_extension_polynomial K n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `local_monic_separable_of_residue`. -/
theorem actual_local_monic_separable_reduction_local_monic_separable_of_residue_source {R : Type} [CommRing R]
    [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hs : (f.map (IsLocalRing.residue R)).Separable) : f.Separable :=
  local_monic_separable_of_residue f hf hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_separable_adjoinRoot_etale`. -/
theorem actual_monic_separable_adjoin_root_etale_monic_separable_adjoinRoot_etale_source {R : Type} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) :=
  monic_separable_adjoinRoot_etale f hf hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_residue_irreducible_adjoinRoot_local`. -/
theorem actual_monic_residue_irreducible_local_algebra_monic_residue_irreducible_adjoinRoot_local_source
    {R : Type} [CommRing R] [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    IsLocalRing (AdjoinRoot f) :=
  monic_residue_irreducible_adjoinRoot_local f hf hi

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_residue_irreducible_adjoinRoot_dvr`. -/
theorem actual_monic_residue_irreducible_d_v_r_monic_residue_irreducible_adjoinRoot_dvr_source
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime
      ((Polynomial.Monic.irreducible_of_irreducible_map
        (IsLocalRing.residue R) f hf hi).prime)
    IsDiscreteValuationRing (AdjoinRoot f) :=
  monic_residue_irreducible_adjoinRoot_dvr f hf hi

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_adjoinRoot_isAdicComplete`. -/
theorem actual_finite_basis_adic_completeness_monic_adjoinRoot_isAdicComplete_source
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : Polynomial R) (hf : f.Monic) :
    IsAdicComplete (I.map (algebraMap R (AdjoinRoot f))) (AdjoinRoot f) :=
  monic_adjoinRoot_isAdicComplete I f hf

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monicRootResidue_natCard`. -/
theorem actual_monic_root_residue_cardinality_monicRootResidue_natCard_source
    {R : Type} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
    Nat.card (IsLocalRing.ResidueField (AdjoinRoot f)) =
      Nat.card (IsLocalRing.ResidueField R) ^ f.natDegree :=
  monicRootResidue_natCard f hf hi

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `spectralFiniteExtension_isNonarchimedeanLocalField`. -/
theorem actual_spectral_finite_extension_local_field_spectralFiniteExtension_isNonarchimedeanLocalField_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [LocallyCompactSpace K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    IsNonarchimedeanLocalField L :=
  spectralFiniteExtension_isNonarchimedeanLocalField K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldOriginalNorm_compatible`. -/
theorem actual_local_field_original_norm_localFieldOriginalNorm_compatible_source :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    letI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
    (NormedField.valuation (K := K)).Compatible :=
  localFieldOriginalNorm_compatible K

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `spectralValuation_hasExtension`. -/
theorem actual_spectral_valuation_extension_spectralValuation_hasExtension_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
  spectralValuation_hasExtension K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `adicComplete_polynomial_splits_of_residue`. -/
theorem actual_adic_complete_residue_splitting_adicComplete_polynomial_splits_of_residue_source
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hf : f.Monic)
    (hs : (f.map (residue R)).Separable)
    (hsp : (f.map (residue R)).Splits) : f.Splits :=
  adicComplete_polynomial_splits_of_residue f hf hs hsp

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finiteResidue_complete_algebra_polynomial_splits`. -/
theorem actual_finite_residue_complete_algebra_splitting_finiteResidue_complete_algebra_polynomial_splits_source
    {R S : Type} [CommRing R] [CommRing S] [IsDomain S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal S) S]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (residue R)))
    (hs : (f.map (residue R)).Separable)
    (a : S) (ha : aeval a f = 0) :
    (f.map (algebraMap R S)).Splits :=
  finiteResidue_complete_algebra_polynomial_splits f hf hi hs a ha

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [FaithfulSMul R L]

/-- Exact original-object consumer of `originalFractionScalarAlgebra_tower`. -/
theorem actual_original_fraction_scalar_algebra_originalFractionScalarAlgebra_tower_source :
    letI : Algebra K L := originalFractionScalarAlgebra R K L
    IsScalarTower R K L :=
  originalFractionScalarAlgebra_tower R K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monicRootFraction_finrank_and_finite`. -/
theorem actual_monic_root_fraction_degree_monicRootFraction_finrank_and_finite_source
    (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] (f : R[X]) [IsDomain (AdjoinRoot f)]
    [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
    [IsScalarTower R (AdjoinRoot f) L]
    (hf : f.Monic) (hd : 0 < f.natDegree) :
    Module.finrank K L = f.natDegree ∧ FiniteDimensional K L :=
  monicRootFraction_finrank_and_finite R K L f hf hd

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  (f : R[X]) [Algebra (AdjoinRoot f) L]
  [IsScalarTower R (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]

/-- Exact original-object consumer of `adjoinRootFraction_isSplittingField`. -/
theorem actual_adjoin_root_fraction_generation_adjoinRootFraction_isSplittingField_source
    [Algebra.IsAlgebraic K L] (hf : f.Monic)
    (hs : ((f.map (algebraMap R K)).map (algebraMap K L)).Splits) :
    (f.map (algebraMap R K)).IsSplittingField K L :=
  adjoinRootFraction_isSplittingField R K L f hf hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (f : Polynomial 𝒪[K]) (hf : f.Monic)
  [IsDomain (AdjoinRoot f)] [IsIntegrallyClosed (AdjoinRoot f)]
  [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
  [IsScalarTower 𝒪[K] (AdjoinRoot f) L]

include hf in
omit [IsDomain (AdjoinRoot f)] in
/-- Exact original-object consumer of `localFieldMonicRootInteger_etale`. -/
theorem actual_local_field_monic_root_integer_equiv_localFieldMonicRootInteger_etale_source
    (hs : (f.map (IsLocalRing.residue 𝒪[K])).Separable) :
    Algebra.Etale 𝒪[K] 𝒪[L] :=
  localFieldMonicRootInteger_etale K L f hf hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_unramified_galois_extension`. -/
theorem actual_local_field_unramified_extension_existence_localField_exists_unramified_galois_extension_source
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L)
      (_ : IsNonarchimedeanLocalField L)
      (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)),
      FiniteDimensional K L ∧ IsGalois K L ∧
        Algebra.FormallyUnramified 𝒪[K] 𝒪[L] ∧ Module.finrank K L = n :=
  localField_exists_unramified_galois_extension K n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `finiteGalois_exists_original_stage`. -/
theorem actual_finite_galois_embedding_stage_finiteGalois_exists_original_stage_source [IsSepClosed Ω] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      Nonempty (L ≃ₐ[K] E) ∧ Module.finrank K E = Module.finrank K L :=
  finiteGalois_exists_original_stage (K := K) (L := L) (Ω := Ω)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localFieldIntegerAlgEquiv_coefficient`. -/
theorem actual_local_field_integer_alg_equiv_localFieldIntegerAlgEquiv_coefficient_source (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    algebraMap 𝒪[M] M (localFieldIntegerAlgEquiv K L M e x) =
      e (algebraMap 𝒪[L] L x) :=
  localFieldIntegerAlgEquiv_coefficient K L M e x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_original_unramified_stage`. -/
theorem actual_local_field_original_unramified_stage_existence_localField_exists_original_unramified_stage_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : ℕ) [NeZero n] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E)
        (_ : IsNonarchimedeanLocalField E)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[E] ∧ Module.finrank K E = n :=
  localField_exists_original_unramified_stage K Ω n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `exists_integral_normal_basis`. -/
theorem actual_integral_normal_basis_lattice_exists_integral_normal_basis_source :
    ∃ b : Module.Basis Gal(L/K) K L,
      (∀ σ, b σ = σ (b 1)) ∧ ∀ σ, IsIntegral R (b σ) :=
  exists_integral_normal_basis R K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)

/-- Exact original-object consumer of `regularBasis_groupCohomology_isZero`. -/
theorem actual_regular_basis_cohomology_regularBasis_groupCohomology_isZero_source
    (hb : ∀ g h, A.ρ g (b h) = b (g * h)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  regularBasis_groupCohomology_isZero A b hb n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)
  (hb : ∀ g h, A.ρ g (b h) = b (g * h))

include hb in
/-- Exact original-object consumer of `regularBasis_invariant_mem_norm`. -/
theorem actual_regular_basis_norm_regularBasis_invariant_mem_norm_source
    (a : A) (ha : ∀ g, A.ρ g a = a) :
    ∃ x : A, ∑ g : G, A.ρ g x = a :=
  regularBasis_invariant_mem_norm A b hb a ha

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))

omit [IsGalois K L] in
/-- Exact original-object consumer of `normalBasisLattice_invariant_mem_norm`. -/
theorem actual_normal_basis_lattice_cohomology_normalBasisLattice_invariant_mem_norm_source
    (a : Submodule.span R (Set.range b))
    (ha : ∀ σ, (normalBasisLatticeRep R K L b hb).ρ σ a = a) :
    ∃ x : Submodule.span R (Set.range b),
      ∑ σ : Gal(L/K), (normalBasisLatticeRep R K L b hb).ρ σ x = a :=
  normalBasisLattice_invariant_mem_norm R K L b hb a ha

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R K V ι : Type} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V]
  [Module K V] [Module R V] [IsScalarTower R K V] [Finite ι]

/-- Exact original-object consumer of `fullBasis_span_absorbs_uniformizer_power`. -/
theorem actual_full_basis_lattice_bounds_fullBasis_span_absorbs_uniformizer_power_source
    [IsDiscreteValuationRing R] (b : Module.Basis ι K V)
    (N : Submodule R V) (hN : N.FG) (π : R) (hπ : Irreducible π) :
    ∃ n : ℕ, ∀ x ∈ N, π ^ n • x ∈ Submodule.span R (Set.range b) :=
  fullBasis_span_absorbs_uniformizer_power b N hN π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `smallLattice_scaled_product`. -/
theorem actual_small_lattice_product_smallLattice_scaled_product_source
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (π : R) (n : ℕ)
    (hA : ∀ z : S, π ^ n • z ∈ A) (x y : S) :
    ∃ z : S, z ∈ A ∧
      (π ^ (n + 1) • x) * (π ^ (n + 1) • y) = π ^ (n + 2) • z :=
  smallLattice_scaled_product A π n hA x y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_normal_lattice`. -/
theorem actual_local_field_integral_normal_lattice_localField_exists_integral_normal_lattice_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b) :=
  localField_exists_integral_normal_lattice K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_complete_normal_lattice`. -/
theorem actual_local_field_complete_normal_lattice_localField_exists_complete_normal_lattice_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (n : ℕ),
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K])
        (Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ m : ℕ, CategoryTheory.Limits.IsZero
        (groupCohomology (normalBasisLatticeRep 𝒪[K] K L b hb) (m + 1))) ∧
      ∀ a : Submodule.span 𝒪[K] (Set.range b),
        (∀ σ, (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ a = a) →
        ∃ x : Submodule.span 𝒪[K] (Set.range b),
          ∑ σ : Gal(L/K), (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ x = a :=
  localField_exists_complete_normal_lattice K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `compactSubmonoid_inv_mem`. -/
theorem actual_compact_submonoid_inverse_compactSubmonoid_inv_mem_source
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (M : Submonoid G) (hM : IsCompact (M : Set G)) {u : G} (hu : u ∈ M) :
    u⁻¹ ∈ M :=
  compactSubmonoid_inv_mem M hM hu

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {L : Type*} [Field L] [TopologicalSpace L]
  [IsTopologicalDivisionRing L] [T2Space L]
  (A : AddSubgroup L) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)

include hmul in
/-- Exact original-object consumer of `latticeUnitSubmonoid_inverse_sub_one_mem`. -/
theorem actual_compact_lattice_unit_subgroup_latticeUnitSubmonoid_inverse_sub_one_mem_source
    (hA : IsCompact (A : Set L)) (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (u : Lˣ) (hu : (u : L) - 1 ∈ A) :
    ((u⁻¹ : Lˣ) : L) - 1 ∈ A :=
  latticeUnitSubmonoid_inverse_sub_one_mem A hmul hA hunit u hu

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_finite_lattice_isCompact`. -/
theorem actual_local_field_compact_lattice_localField_finite_lattice_isCompact_source
    (A : Submodule 𝒪[K] L) (hA : A.FG) : IsCompact (A : Set L) :=
  localField_finite_lattice_isCompact K L A hA

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `compact_exists_of_additive_filtered_approximations`. -/
theorem actual_compact_filtered_exactness_compact_exists_of_additive_filtered_approximations_source
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (f : X → Y) (hf : Continuous f) (F : ℕ → AddSubgroup Y)
    (hF : ∀ n, IsClosed (F n : Set Y)) (hmono : ∀ n, F (n + 1) ≤ F n)
    (hsep : ∀ z : Y, (∀ n, z ∈ F n) → z = 0)
    (y : Y) (happrox : ∀ n, ∃ x, f x - y ∈ F n) : ∃ x, f x = y :=
  compact_exists_of_additive_filtered_approximations f hf F hF hmono hsep y happrox

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `scalarLatticeImage_product_gain`. -/
theorem actual_scaled_lattice_products_scalarLatticeImage_product_gain_source
    (A : Submodule R S) (B : Subring S) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    {x y : S} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1)))
    (hy : y ∈ scalarLatticeImage A (π ^ (n + 1))) :
    ∃ z ∈ scalarLatticeImage A (π ^ (n + 1)), x * y = π • z :=
  scalarLatticeImage_product_gain A B π n hupper hlower hx hy

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_exists_compact_small_unit_subgroup`. -/
theorem actual_local_field_small_lattice_units_localField_exists_compact_small_unit_subgroup_source
    (A : Submodule 𝒪[K] L) (hA : A.FG)
    (π : 𝒪[K]) (hπ : ¬ IsUnit π) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x ∈ (ValuativeRel.valuation L).integer, π ^ n • x ∈ A) :
    ∃ U : Subgroup Lˣ, IsCompact (U : Set Lˣ) ∧
      ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ (n + 1)) :=
  localField_exists_compact_small_unit_subgroup K L A hA π hπ n hupper hlower

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `galoisNorm_small_lattice_error`. -/
theorem actual_small_lattice_norm_error_galoisNorm_small_lattice_error_source
    (R K L : Type) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : Submodule R L) (B : Subring L) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A)
    {x : L} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1))) :
    algebraMap K L (Algebra.norm K (1 + x)) - 1 -
        algebraMap K L (Algebra.trace K L x) ∈
      scalarLatticeImage (scalarLatticeImage A (π ^ (n + 1))) π :=
  galoisNorm_small_lattice_error R K L A B π n hupper hlower hstable hx

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_normal_lattice_unit_subgroup`. -/
theorem actual_local_field_normal_lattice_units_localField_exists_normal_lattice_unit_subgroup_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U :=
  localField_exists_normal_lattice_unit_subgroup K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- Exact original-object consumer of `localField_scaled_lattice_isOpen`. -/
theorem actual_local_field_open_lattice_localField_scaled_lattice_isOpen_source
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : π ≠ 0) (n : ℕ)
    (hbound : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ A) :
    IsOpen (scalarLatticeImage A (π ^ (n + 1)) : Set L) :=
  localField_scaled_lattice_isOpen K L A π hπ n hbound

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_exists_open_normal_lattice_unit_subgroup`. -/
theorem actual_local_field_open_small_units_localField_exists_open_normal_lattice_unit_subgroup_source [IsGalois K L]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U :=
  localField_exists_open_normal_lattice_unit_subgroup K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {L : Type*} [Field L] (B : Subring L) (U : Subgroup Lˣ)
  (hU : ∀ u ∈ U, (u : L) ∈ B)

/-- Exact original-object consumer of `subringUnitSubgroupEquiv_coefficient`. -/
theorem actual_subring_unit_subgroup_equiv_subringUnitSubgroupEquiv_coefficient_source
    (v : U.comap (Units.map B.subtype.toMonoidHom)) :
    (((subringUnitSubgroupEquiv B U hU v : U) : Lˣ) : L) =
      (((v : Bˣ) : B) : L) :=
  subringUnitSubgroupEquiv_coefficient B U hU v

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] in
/-- Exact original-object consumer of `localFieldSmallUnitIntegerEquiv_coefficient`. -/
theorem actual_local_field_integral_small_units_localFieldSmallUnitIntegerEquiv_coefficient_source
    (A : Submodule 𝒪[K] L) (r : 𝒪[K])
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (U : Subgroup Lˣ)
    (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A r)
    (v : U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) :
    (((localFieldSmallUnitIntegerEquiv K L A r hupper U hU v : U) : Lˣ) : L) =
      (((v : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  localFieldSmallUnitIntegerEquiv_coefficient K L A r hupper U hU v

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R L : Type} [CommRing R] [Field L] [Algebra R L]
  (A B : Submodule R L) (U : Subgroup Lˣ)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ A)

/-- Exact original-object consumer of `smallUnitGradedMap_surjective`. -/
theorem actual_small_unit_graded_quotient_smallUnitGradedMap_surjective_source
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B)
    (hunit : ∀ a ∈ A, (1 : L) + a ≠ 0) :
    Function.Surjective (smallUnitGradedMap A B U hU hmul) :=
  smallUnitGradedMap_surjective A B U hU hmul hunit

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r : R)

omit [IsGalois K L] in
/-- Exact original-object consumer of `scalarNormalLattice_invariant_mem_norm`. -/
theorem actual_scalar_normal_lattice_cohomology_scalarNormalLattice_invariant_mem_norm_source (hr : r ≠ 0)
    (a : scalarNormalLatticeRep R K L b hb r)
    (ha : ∀ σ, (scalarNormalLatticeRep R K L b hb r).ρ σ a = a) :
    ∃ x : scalarNormalLatticeRep R K L b hb r,
      ∑ σ : Gal(L/K), (scalarNormalLatticeRep R K L b hb r).ρ σ x = a :=
  scalarNormalLattice_invariant_mem_norm R K L b hb r hr a ha

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (r : R)

/-- Exact original-object consumer of `repScalarQuotient_groupCohomology_isZero`. -/
theorem actual_scalar_representation_quotient_repScalarQuotient_groupCohomology_isZero_source
    (hinj : Function.Injective (fun x : A => r • x)) (n : ℕ)
    (hn : Limits.IsZero (groupCohomology A n))
    (hs : Limits.IsZero (groupCohomology A (n + 1))) :
    Limits.IsZero (groupCohomology (repScalarQuotient A r) n) :=
  repScalarQuotient_groupCohomology_isZero A r hinj n hn hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- Exact original-object consumer of `repScalarQuotient_invariant_mem_norm`. -/
theorem actual_scalar_quotient_invariant_lift_repScalarQuotient_invariant_mem_norm_source [Fintype G] (r : R)
    (hinj : Function.Injective (fun x : A => r • x))
    (hA : Limits.IsZero (groupCohomology A 1))
    (hNorm : ∀ a : A, (∀ g, A.ρ g a = a) → ∃ x : A, ∑ g : G, A.ρ g x = a)
    (q : repScalarQuotient A r)
    (hq : ∀ g, (repScalarQuotient A r).ρ g q = q) :
    ∃ x : repScalarQuotient A r, ∑ g : G, (repScalarQuotient A r).ρ g x = q :=
  repScalarQuotient_invariant_mem_norm A r hinj hA hNorm q hq

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R)

omit [IsGalois K L] in
/-- Exact original-object consumer of `scalarNormalLatticeQuotient_invariant_mem_norm`. -/
theorem actual_scalar_normal_lattice_quotient_scalarNormalLatticeQuotient_invariant_mem_norm_source
    (hr : r ≠ 0) (hs : s ≠ 0)
    (q : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s)
    (hq : ∀ σ,
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ q = q) :
    ∃ x : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s,
      ∑ σ : Gal(L/K),
        (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ x = q :=
  scalarNormalLatticeQuotient_invariant_mem_norm R K L b hb r s hr hs q hq

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)

variable (R : Type) [CommRing R] [IsDomain R]
  [Algebra R K] [IsFractionRing R K] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r s : R)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- Exact original-object consumer of `normalLatticeUnitGradedMap_equivariant`. -/
theorem actual_normal_lattice_unit_graded_map_normalLatticeUnitGradedMap_equivariant_source (σ : Gal(L/K)) (u : Additive U) :
    normalLatticeUnitGradedMap K L U R b hb r s hU hmul
        ((galoisUnitSubgroupMap K L U hstable σ).toAdditive u) =
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ
        (normalLatticeUnitGradedMap K L U R b hb r s hU hmul u) :=
  normalLatticeUnitGradedMap_equivariant K L U hstable R b hb r s hU hmul σ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G U : Type} [CommRing R] [Group G] [CommGroup U]
  [MulDistribMulAction G U] (A : Rep R G) (f : Additive U →+ A)
  (hf : ∀ (g : G) (u : U), f (Additive.ofMul (g • u)) = A.ρ g (f (Additive.ofMul u)))

include hf in
/-- Exact original-object consumer of `unitGraded_cocycle_correction`. -/
theorem actual_unit_graded_correction_unitGraded_cocycle_correction_source (hsurj : Function.Surjective f)
    (hA : Limits.IsZero (groupCohomology A 1)) (c : G → U)
    (hc : ∀ g h, c (g * h) = (g • c h) * c g) :
    ∃ u : U, ∀ g, f (Additive.ofMul (c g / ((g • u) / u))) = 0 :=
  unitGraded_cocycle_correction A f hf hsurj hA c hc

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R) (hr : r ≠ 0) (hs : s ≠ 0) (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)
  (hunit : ∀ a ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    (1 : L) + a ≠ 0)

include hb hr hs hU hmul hunit in
omit [IsGalois K L] in
/-- Exact original-object consumer of `normalLatticeUnit_norm_correction`. -/
theorem actual_normal_lattice_unit_correction_normalLatticeUnit_norm_correction_source (u : U)
    (hu : ∀ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ u = u) :
    ∃ v : U,
      ((((u / ∏ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ v) : U) : Lˣ) : L) - 1 ∈
        scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s :=
  normalLatticeUnit_norm_correction R K L b hb r s hr hs U hstable hU hmul hunit u hu

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `scalarLatticeImage_level_product_gain`. -/
theorem actual_scalar_lattice_filtration_scalarLatticeImage_level_product_gain_source (A : Submodule R S) (π : R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ scalarLatticeImage A π)
    (j : ℕ) {x y : S}
    (hx : x ∈ scalarLatticeImage A (π ^ j))
    (hy : y ∈ scalarLatticeImage A (π ^ j)) :
    x * y ∈ scalarLatticeImage (scalarLatticeImage A (π ^ j)) π :=
  scalarLatticeImage_level_product_gain A π hmul j hx hy

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `scalarLatticeImage_separated_of_isHausdorff`. -/
theorem actual_scalar_lattice_filtration_separation_scalarLatticeImage_separated_of_isHausdorff_source
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (I : Ideal R) [IsHausdorff I A]
    (π : R) (hπ : π ∈ I) (x : S)
    (hx : ∀ j : ℕ, x ∈ scalarLatticeImage A (π ^ j)) : x = 0 :=
  scalarLatticeImage_separated_of_isHausdorff A I π hπ x hx

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_scalar_unit_filtration`. -/
theorem actual_local_field_scalar_unit_filtration_localField_exists_scalar_unit_filtration_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (A : Submodule 𝒪[K] L) (hA : A.FG) (π : 𝒪[K])
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ scalarLatticeImage A π)
    (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A) :
    ∃ U : ℕ → Subgroup Lˣ, ∀ j,
      IsCompact (U j : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ j)) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
      U (j + 1) ≤ U j :=
  localField_exists_scalar_unit_filtration K L A hA π hmul hunit hstable

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_separated_normal_unit_filtration`. -/
theorem actual_local_field_separated_normal_unit_filtration_localField_exists_separated_normal_unit_filtration_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : ℕ → Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ j, IsCompact (U j : Set Lˣ) ∧
        (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈
          scalarLatticeImage
            (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
            (π ^ j)) ∧
        (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
          Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
        U (j + 1) ≤ U j) ∧
      ∀ u : Lˣ, (∀ j, u ∈ U j) → u = 1 :=
  localField_exists_separated_normal_unit_filtration K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]

/-- Exact original-object consumer of `finiteActionUnitNorm_continuous`. -/
theorem actual_finite_action_unit_norm_finiteActionUnitNorm_continuous_source [TopologicalSpace U] [IsTopologicalGroup U]
    (hcont : ∀ g : G, Continuous (fun u : U => g • u)) :
    Continuous (finiteActionUnitNorm G U) :=
  finiteActionUnitNorm_continuous G U hcont

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]
  (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)

include hmono in
/-- Exact original-object consumer of `finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration`. -/
theorem actual_compact_filtered_unit_norm_finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration_source
    [TopologicalSpace U] [IsTopologicalGroup U]
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (u : U), u ∈ S j → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S j ∧ u / finiteActionUnitNorm G U v ∈ S (j + 1))
    (u : U) (hu : u ∈ S 0) (hinv : ∀ g : G, g • u = u) :
    ∃ v : U, v ∈ S 0 ∧ finiteActionUnitNorm G U v = u :=
  finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration G U S hmono hcompact hclosed hsep hcont hcorrect u hu hinv

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localField_algEquiv_units_continuous`. -/
theorem actual_local_field_alg_equiv_continuity_localField_algEquiv_units_continuous_source (e : L ≃ₐ[K] M) :
    Continuous (Units.map (e : L →+* M).toMonoidHom) :=
  localField_algEquiv_units_continuous K L M e

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_normal_unit_level_norm_correction`. -/
theorem actual_local_field_normal_unit_level_norm_localField_normal_unit_level_norm_correction_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (hupper : ∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
      x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b))
    (U : ℕ → Subgroup Lˣ)
    (hU : ∀ j (u : Lˣ), u ∈ U j ↔ (u : L) - 1 ∈
      scalarLatticeImage
        (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) (π ^ j))
    (hstable : ∀ j (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
      Units.map (σ : L →+* L).toMonoidHom u ∈ U j)
    (j : ℕ) (u : Lˣ) (hu : u ∈ U j) (hinv : ∀ σ : Gal(L/K), σ • u = u) :
    ∃ v : Lˣ, v ∈ U j ∧ u / finiteActionUnitNorm Gal(L/K) Lˣ v ∈ U (j + 1) :=
  localField_normal_unit_level_norm_correction K L b hb π hπ n hupper hlower U hU hstable j u hu hinv

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_small_unit_norm_surjective`. -/
theorem actual_local_field_small_unit_norm_surjectivity_localField_exists_small_unit_norm_surjective_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U) ∧
      (∀ u : Lˣ, u ∈ U → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : Lˣ, v ∈ U ∧ finiteActionUnitNorm Gal(L/K) Lˣ v = u) ∧
      ∃ F : ℕ → Subgroup Lˣ, F 0 = U ∧
        (∀ j, IsCompact (F j : Set Lˣ) ∧
          (∀ u : Lˣ, u ∈ F j ↔ (u : L) - 1 ∈
            scalarLatticeImage
              (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
              (π ^ j)) ∧
          (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ F j →
            Units.map (σ : L →+* L).toMonoidHom u ∈ F j) ∧
          F (j + 1) ≤ F j) ∧
        ∀ u : Lˣ, (∀ j, u ∈ F j) → u = 1 :=
  localField_exists_small_unit_norm_surjective K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]

/-- Exact original-object consumer of `unit_cocycle_filtered_approximations`. -/
theorem actual_unit_cocycle_corrections_unit_cocycle_filtered_approximations_source
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∀ j, ∃ u : U, u ∈ S 0 ∧ ∀ g, c g / ((g • u) / u) ∈ S j :=
  unit_cocycle_filtered_approximations S hmono hcorrect c hc hc0

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `unit_cocycle_coboundary_of_compact_filtration`. -/
theorem actual_compact_filtered_unit_cocycles_unit_cocycle_coboundary_of_compact_filtration_source
    {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∃ u : U, u ∈ S 0 ∧ ∀ g, (g • u) / u = c g :=
  unit_cocycle_coboundary_of_compact_filtration S hmono hcompact hclosed hsep hcont hcorrect c hc hc0

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_normal_unit_level_cocycle_correction`. -/
theorem actual_local_field_normal_unit_level_cocycle_localField_normal_unit_level_cocycle_correction_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (hupper : ∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
      x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b))
    (U : ℕ → Subgroup Lˣ)
    (hU : ∀ j (u : Lˣ), u ∈ U j ↔ (u : L) - 1 ∈
      scalarLatticeImage
        (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) (π ^ j))
    (hstable : ∀ j (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
      Units.map (σ : L →+* L).toMonoidHom u ∈ U j)
    (j : ℕ) (c : Gal(L/K) → Lˣ)
    (hc : ∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) (hcj : ∀ σ, c σ ∈ U j) :
    ∃ v : Lˣ, v ∈ U j ∧ ∀ σ : Gal(L/K),
      c σ / ((σ • v) / v) ∈ U (j + 1) :=
  localField_normal_unit_level_cocycle_correction K L b hb π hπ n hupper hlower U hU hstable j c hc hcj

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_small_unit_norm_and_coboundary`. -/
theorem actual_local_field_small_unit_cohomology_localField_exists_small_unit_norm_and_coboundary_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U) ∧
      (∀ u : Lˣ, u ∈ U → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : Lˣ, v ∈ U ∧ finiteActionUnitNorm Gal(L/K) Lˣ v = u) ∧
      ∀ c : Gal(L/K) → Lˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ U) →
          ∃ v : Lˣ, v ∈ U ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ :=
  localField_exists_small_unit_norm_and_coboundary K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldIntegerUnit_inclusion_equivariant`. -/
theorem actual_local_field_integer_unit_action_localFieldIntegerUnit_inclusion_equivariant_source (σ : Gal(L/K)) (u : 𝒪[L]ˣ) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Units.map (algebraMap 𝒪[L] L).toMonoidHom (σ • u) =
      σ • Units.map (algebraMap 𝒪[L] L).toMonoidHom u :=
  localFieldIntegerUnit_inclusion_equivariant K L σ u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G V U : Type} [Group G] [CommGroup V] [CommGroup U]
  [MulDistribMulAction G V] [MulDistribMulAction G U]
  (j : V →* U) (hj : Function.Injective j)
  (heq : ∀ (g : G) (v : V), j (g • v) = g • j v)

include hj heq in
/-- Exact original-object consumer of `injective_unit_cocycle_preimages`. -/
theorem actual_injective_unit_cohomology_transfer_injective_unit_cocycle_preimages_source
    (T : Subgroup V) (S : Subgroup U)
    (hmem : ∀ v : V, v ∈ T ↔ j v ∈ S)
    (honto : ∀ u : U, u ∈ S → ∃ v : V, v ∈ T ∧ j v = u)
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g)
    (c : G → V) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hcT : ∀ g, c g ∈ T) :
    ∃ v : V, v ∈ T ∧ ∀ g, (g • v) / v = c g :=
  injective_unit_cocycle_preimages j hj heq T S hmem honto hcob c hc hcT

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_small_unit_norm_and_coboundary`. -/
theorem actual_local_field_integral_small_unit_cohomology_localField_exists_integral_small_unit_norm_and_coboundary_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      (∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V) ∧
      (∀ u : 𝒪[L]ˣ, u ∈ V → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : 𝒪[L]ˣ, v ∈ V ∧ finiteActionUnitNorm Gal(L/K) 𝒪[L]ˣ v = u) ∧
      ∀ c : Gal(L/K) → 𝒪[L]ˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ V) →
          ∃ v : 𝒪[L]ˣ, v ∈ V ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ :=
  localField_exists_integral_small_unit_norm_and_coboundary K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- Exact original-object consumer of `stableSubgroup_firstCohomology_zero`. -/
theorem actual_stable_subgroup_cohomology_stableSubgroup_firstCohomology_zero_source
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g) :
    letI := stableSubgroupMulDistribMulAction G U S hS
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) 1) :=
  stableSubgroup_firstCohomology_zero G U S hS hcob

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- Exact original-object consumer of `cyclic_positiveCohomology_zero`. -/
theorem actual_cyclic_positive_cohomology_vanishing_cyclic_positiveCohomology_zero_source
    (hnorm : ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x)
    (hfirst : Limits.IsZero (groupCohomology A 1)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupCohomology A n) :=
  cyclic_positiveCohomology_zero A g hg hnorm hfirst n hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_cyclic_small_unit_acyclic`. -/
theorem actual_local_field_cyclic_small_unit_acyclicity_localField_exists_cyclic_small_unit_acyclic_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      ∃ hstable : ∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V,
        letI := stableSubgroupMulDistribMulAction Gal(L/K) 𝒪[L]ˣ V hstable
        ∀ n : ℕ, 0 < n →
          Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) V) n) :=
  localField_exists_cyclic_small_unit_acyclic K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Exact original-object consumer of `finite_periodic_homology_card_eq`. -/
theorem actual_finite_periodic_homology_cardinality_finite_periodic_homology_card_eq_source [Finite M]
    (f g : M →ₗ[R] M) (hgf : g.comp f = 0) (hfg : f.comp g = 0) :
    Nat.card (linearPeriodicHomology f g hgf) =
      Nat.card (linearPeriodicHomology g f hfg) :=
  finite_periodic_homology_card_eq f g hgf hfg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_cyclic_first_second_cohomology_card_eq`. -/
theorem actual_finite_cyclic_cohomology_cardinality_finite_cyclic_first_second_cohomology_card_eq_source
    {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) [Finite A] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) :=
  finite_cyclic_first_second_cohomology_card_eq A g hg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- Exact original-object consumer of `stableSubgroupQuotient_cohomology_isIso`. -/
theorem actual_stable_subgroup_quotient_cohomology_stableSubgroupQuotient_cohomology_isIso_source (n : ℕ)
    (hn : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) n))
    (hs : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) (n + 1))) :
    IsIso ((groupCohomology.functor ℤ G n).map
      (stableSubgroupShortComplex G U S hS).g) :=
  stableSubgroupQuotient_cohomology_isIso G U S hS n hn hs

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_integer_unit_first_second_cohomology_orders`. -/
theorem actual_local_field_integer_unit_cohomology_orders_localField_integer_unit_first_second_cohomology_orders_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) :=
  localField_integer_unit_first_second_cohomology_orders K L π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localFieldUnitOrder_galois_invariant`. -/
theorem actual_local_field_galois_unit_order_localFieldUnitOrder_galois_invariant_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (σ : Gal(L/K)) (x : Lˣ) :
    localFieldUnitOrder L (Additive.ofMul (σ • x)) = localFieldUnitOrder L (Additive.ofMul x) :=
  localFieldUnitOrder_galois_invariant K L σ x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldUnitValuationShortComplex_shortExact`. -/
theorem actual_local_field_unit_valuation_sequence_localFieldUnitValuationShortComplex_shortExact_source :
    (localFieldUnitValuationShortComplex K L).ShortExact :=
  localFieldUnitValuationShortComplex_shortExact K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `cyclic_trivial_integer_odd_cohomology_zero`. -/
theorem actual_cyclic_trivial_integer_cohomology_cyclic_trivial_integer_odd_cohomology_zero_source
    (G : Type) [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : Odd n) :
    Limits.IsZero (groupCohomology (Rep.trivial ℤ G ℤ) n) :=
  cyclic_trivial_integer_odd_cohomology_zero G g hg n hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B C D : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- Exact original-object consumer of `exact_four_module_cardinality`. -/
theorem actual_finite_exact_module_cardinality_exact_four_module_cardinality_source
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hh : Function.Surjective h)
    (hfg : f.range = g.ker) (hgh : g.range = h.ker) :
    Nat.card B * Nat.card D = Nat.card A * Nat.card C :=
  exact_four_module_cardinality f g h hf hh hfg hgh

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `cyclic_trivial_integer_even_cohomology_order`. -/
theorem actual_cyclic_integer_even_cohomology_cyclic_trivial_integer_even_cohomology_order_source
    (G : Type) [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) [NeZero n] (hn : Even n) :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) n) ∧
      Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) n) = Fintype.card G :=
  cyclic_trivial_integer_even_cohomology_order G g hg n hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `exact_cohomology_four_term_cardinality`. -/
theorem actual_exact_cohomology_cardinality_exact_cohomology_four_term_cardinality_source
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep k G)) (hX : X.ShortExact) (n : ℕ)
    (hprev : Limits.IsZero (groupCohomology X.X₃ n))
    (hnext : Limits.IsZero (groupCohomology X.X₂ (n + 1 + 1)))
    [Finite (groupCohomology X.X₁ (n + 1))]
    [Finite (groupCohomology X.X₃ (n + 1))] :
    Finite (groupCohomology X.X₂ (n + 1)) ∧
      Nat.card (groupCohomology X.X₂ (n + 1)) *
          Nat.card (groupCohomology X.X₁ (n + 1 + 1)) =
        Nat.card (groupCohomology X.X₁ (n + 1)) *
          Nat.card (groupCohomology X.X₃ (n + 1)) :=
  exact_cohomology_four_term_cardinality X hX n hprev hnext

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_cyclic_second_cohomology_order`. -/
theorem actual_local_field_cyclic_second_cohomology_order_localField_cyclic_second_cohomology_order_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) :=
  localField_cyclic_second_cohomology_order K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_cyclic_norm_index`. -/
theorem actual_local_field_cyclic_norm_index_localField_cyclic_norm_index_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Nat.card (Additive Kˣ ⧸ (galoisUnitFieldNormLinear (K := K) (L := L)).range) =
      Module.finrank K L :=
  localField_cyclic_norm_index K L

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `coinducedCosetValues_action`. -/
theorem actual_coinduced_coset_values_coinducedCosetValues_action_source
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) (h : G) (q : G ⧸ S) :
    coinducedCosetValues A S ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ h f) q =
      A.ρ h (coinducedCosetValues A S f (h⁻¹ • q)) :=
  coinducedCosetValues_action A S f h q

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)
  [Fintype (G ⧸ S)]

/-- Exact original-object consumer of `coinducedCosetTrace_comp_unit`. -/
theorem actual_coinduced_coset_trace_coinducedCosetTrace_comp_unit_source :
    Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _) ≫
      coinducedCosetTrace A S = Fintype.card (G ⧸ S) • 𝟙 A :=
  coinducedCosetTrace_comp_unit A S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

variable [Fintype (G ⧸ S)]

/-- Exact original-object consumer of `subgroupCohomologyComparison_trace`. -/
theorem actual_coinduced_cohomology_trace_subgroupCohomologyComparison_trace_source (n : ℕ) :
    subgroupCohomologyComparison A S n ≫ subgroupCohomologyTrace A S n =
      Fintype.card (G ⧸ S) • 𝟙 (groupCohomology A n) :=
  subgroupCohomologyComparison_trace A S n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `sylowCohomologyComparison_primary_injective`. -/
theorem actual_subgroup_cohomology_coprime_detection_sylowCohomologyComparison_primary_injective_source [Finite G]
    (n p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Function.Injective (fun x : AddCommGroup.primaryComponent (groupCohomology A n) p =>
      subgroupCohomologyComparison A (P : Subgroup G) n x.val) :=
  sylowCohomologyComparison_primary_injective A n p P

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- Exact original-object consumer of `finiteSecondCohomology_sylow_zero`. -/
theorem actual_finite_second_cohomology_sylow_detection_finiteSecondCohomology_sylow_zero_source
    (x : groupCohomology A 2)
    (hx : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Sylow p G,
      subgroupCohomologyComparison A (P : Subgroup G) 2 x = 0) : x = 0 :=
  finiteSecondCohomology_sylow_zero A x hx

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_second_cohomology_of_sylows`. -/
theorem actual_finite_second_cohomology_from_sylows_finite_second_cohomology_of_sylows_source
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hfinite : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2)) :
    Finite (groupCohomology A 2) :=
  finite_second_cohomology_of_sylows A hfinite

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G : Type} [Group G] (S : Subgroup G)

/-- Exact original-object consumer of `subgroupCosetRemainder_mul`. -/
theorem actual_original_subgroup_coset_coordinates_subgroupCosetRemainder_mul_source (g : G) (h : S) :
    subgroupCosetRemainder S (g * h) = subgroupCosetRemainder S g * h :=
  subgroupCosetRemainder_mul S g h

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- Exact original-object consumer of `originalCoinducedFunctionRep_action`. -/
theorem actual_original_coinduced_function_coefficients_originalCoinducedFunctionRep_action_source
    (f : originalCoinducedFunctionRep A) (h g : G) :
    ((originalCoinducedFunctionRep A).ρ h f).val g = f.val (g * h) :=
  originalCoinducedFunctionRep_action A f h g

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `originalCoinducedSubgroup_second_zero`. -/
theorem actual_original_coinduced_subgroup_acyclicity_originalCoinducedSubgroup_second_zero_source :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedFunctionRep A)) 2) :=
  originalCoinducedSubgroup_second_zero A S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- Exact original-object consumer of `originalCoinducedDimensionShift_isIso`. -/
theorem actual_original_coinduced_dimension_shift_originalCoinducedDimensionShift_isIso_source (S : Subgroup G) :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl) :=
  originalCoinducedDimensionShift_isIso A S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [S.Normal]

/-- Exact original-object consumer of `originalCoinducedInvariantQuotient_isomorphic`. -/
theorem actual_original_coinduced_invariant_quotient_originalCoinducedInvariantQuotient_isomorphic_source :
    Nonempty ((originalCoinducedFunctionRep A).quotientToInvariants S ≅
      originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A)) :=
  originalCoinducedInvariantQuotient_isomorphic A S

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalCoinducedInvariant_positive_zero`. -/
theorem actual_original_coinduced_invariant_acyclicity_originalCoinducedInvariant_positive_zero_source
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology
      ((originalCoinducedFunctionRep A).quotientToInvariants S) (n + 1)) :=
  originalCoinducedInvariant_positive_zero A S n

end

end Dubon2026.SemanticRegression
