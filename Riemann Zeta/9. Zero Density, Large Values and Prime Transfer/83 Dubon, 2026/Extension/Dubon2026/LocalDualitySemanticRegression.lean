import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))

/-- Exact original-object consumer of `continuousKummer_cup_add_carry_boundary`. -/
theorem actual_local_kummer_2327_continuousKummer_cup_add_carry_boundary_source (a : Kˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a) :
    continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
      (galoisRadicalCharacterOneCochain n χ β) =
    continuousCoefficientCocycleTwoMap
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (Rep.ofAlgebraAutOnUnits K Ω)
      (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
      (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
      (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
      (continuousGaloisRootCharacterCupCocycle n χ (galoisRootRadicalOneCocycle n a β hβ)) +
        continuousGaloisCharacterCarryCocycle n χ a :=
  continuousKummer_cup_add_carry_boundary n χ a β hβ

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) (a : Kˣ)

/-- Exact original-object consumer of `continuousKummerH1Cup_eq_zero_iff_carry`. -/
theorem actual_local_kummer_2328_continuousKummerH1Cup_eq_zero_iff_carry_source :
    continuousGaloisRootCharacterH1Cup n χ (galoisKummerH1Class n a) = 0 ↔
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ a) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) = 0 :=
  continuousKummerH1Cup_eq_zero_iff_carry n χ a

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω) {n : ℕ} [NeZero n]
  (χ : Gal(E/K) →* Multiplicative (ZMod n))

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable [IsAlgClosed Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]

/-- Exact original-object consumer of `continuousKummerH1Cup_inflated_eq_zero_iff`. -/
theorem actual_local_kummer_2329_continuousKummerH1Cup_inflated_eq_zero_iff_source (a : Kˣ) :
    continuousGaloisRootCharacterH1Cup n (finiteGaloisCharacterInflation E χ)
      (galoisKummerH1Class n a) = 0 ↔
        localFieldFiniteCharacterCarryClass K Ω E χ a = 0 :=
  continuousKummerH1Cup_inflated_eq_zero_iff E χ a

end

section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := K) (Ω := Ω) (Nat.card Gal(E/K)))]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := K) (Ω := Ω) (Nat.card Gal(E/K)))]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `localFieldKummer_generatorCup_exists_nonzero`. -/
theorem actual_local_kummer_2330_localFieldKummer_generatorCup_exists_nonzero_source
    (hn : 1 < Nat.card Gal(E/K)) :
    letI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
    ∃ a : Kˣ, continuousGaloisRootCharacterH1Cup (Nat.card Gal(E/K))
      (finiteGaloisCharacterInflation E (galoisUnitGeneratorIndex g hg))
      (galoisKummerH1Class (Nat.card Gal(E/K)) a) ≠ 0 :=
  localFieldKummer_generatorCup_exists_nonzero K Ω E g hg hn

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ}

/-- Exact original-object consumer of `continuousGaloisCharacter_faithful_cyclic_factor`. -/
theorem actual_local_kummer_2331_continuousGaloisCharacter_faithful_cyclic_factor_source
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* Multiplicative (ZMod n),
        Function.Injective ψ ∧ finiteGaloisCharacterInflation F ψ = χ :=
  continuousGaloisCharacter_faithful_cyclic_factor χ

end

section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localFieldKummer_character_eq_one_of_cup_zero`. -/
theorem actual_local_kummer_2332_localFieldKummer_character_eq_one_of_cup_zero_source
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))
    (h : ∀ x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n,
      continuousGaloisRootCharacterH1Cup n χ x = 0) : χ = 1 :=
  localFieldKummer_character_eq_one_of_cup_zero K Ω n χ h

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- Exact original-object consumer of `basePrimitiveRootExponentPairing_symm`. -/
theorem actual_local_kummer_2333_basePrimitiveRootExponentPairing_symm_source (x y : ZMod n) :
    galoisRootExponentPairing n (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ x) y =
      galoisRootExponentPairing n (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ y) x :=
  basePrimitiveRootExponentPairing_symm (Ω := Ω) hζ x y

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]

/-- Exact original-object consumer of `basePrimitiveRootCocycleCharacter_eq_one_iff`. -/
theorem actual_local_kummer_2334_basePrimitiveRootCocycleCharacter_eq_one_iff_source
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    basePrimitiveRootCocycleCharacter hζ c = 1 ↔ c = 0 :=
  basePrimitiveRootCocycleCharacter_eq_one_iff hζ c

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `basePrimitiveRootCocycleCup_swap_add`. -/
theorem actual_local_kummer_2335_basePrimitiveRootCocycleCup_swap_add_source
    (c d : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    continuousGaloisRootCharacterH1Cup n (basePrimitiveRootCocycleCharacter hζ c)
        (Submodule.Quotient.mk d) +
      continuousGaloisRootCharacterH1Cup n (basePrimitiveRootCocycleCharacter hζ d)
        (Submodule.Quotient.mk c) = 0 :=
  basePrimitiveRootCocycleCup_swap_add hζ c d

end

section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hζ

/-- Exact original-object consumer of `localFieldKummer_root_eq_zero_of_cup_zero`. -/
theorem actual_local_kummer_2336_localFieldKummer_root_eq_zero_of_cup_zero_source
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (h : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      continuousGaloisRootCharacterH1Cup n χ x = 0) : x = 0 :=
  localFieldKummer_root_eq_zero_of_cup_zero K Ω hζ x h

end

section

open scoped ValuativeRel

variable (K : Type) [NontriviallyNormedField K] [CompleteSpace K]

/-- Exact original-object consumer of `normedField_unitPower_range_isOpen`. -/
theorem actual_local_kummer_2337_normedField_unitPower_range_isOpen_source (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  normedField_unitPower_range_isOpen K n hn

end

section

open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localField_unitPower_quotient_finite`. -/
theorem actual_local_kummer_2338_localField_unitPower_quotient_finite_source (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :=
  localField_unitPower_quotient_finite K n hn

end

section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localFieldKummerH1_finite`. -/
theorem actual_local_kummer_2339_localFieldKummerH1_finite_source (hn : (n : K) ≠ 0) :
    Finite (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) :=
  localFieldKummerH1_finite K Ω n hn

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]

variable [IsGalois K Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousKummerCharacterPairing_apply`. -/
theorem actual_local_kummer_2340_continuousKummerCharacterPairing_apply_source
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (χ : Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod n))) :
    continuousKummerCharacterPairing n x χ =
      continuousGaloisRootCharacterH1Cup n χ.toMul x :=
  continuousKummerCharacterPairing_apply n x χ

end

section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localField_continuousFiniteCharacters_finite`. -/
theorem actual_local_kummer_2341_localField_continuousFiniteCharacters_finite_source (hn : (n : K) ≠ 0) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) :=
  localField_continuousFiniteCharacters_finite K Ω n hn

end

section

open scoped ValuativeRel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (n : ℕ) [NeZero n]

variable [IsGalois K Ω] [IsAlgClosed Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisRootContinuousH1_nsmul_eq_zero`. -/
theorem actual_local_kummer_2342_galoisRootContinuousH1_nsmul_eq_zero_source
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n) : n • x = 0 :=
  galoisRootContinuousH1_nsmul_eq_zero n x

end

section

open scoped ValuativeRel

attribute [local instance] galoisFiniteCharacterZModModule galoisRootH1ZModModule

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localFieldPrimeKummerPairing_eq_zero_iff`. -/
theorem actual_local_kummer_2343_localFieldPrimeKummerPairing_eq_zero_iff_source
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) q)
    (χ : Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod q))) :
    localFieldPrimeKummerPairing K Ω q x χ = 0 ↔
      continuousGaloisRootCharacterH1Cup q χ.toMul x = 0 :=
  localFieldPrimeKummerPairing_eq_zero_iff K Ω q x χ

end

section

open scoped ValuativeRel

attribute [local instance] galoisFiniteCharacterZModModule galoisRootH1ZModModule

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `localFieldPrimeKummerPairing_isPerfPair`. -/
theorem actual_local_kummer_2344_localFieldPrimeKummerPairing_isPerfPair_source
    {ζ : K} (hζ : IsPrimitiveRoot ζ q) (hq : (q : K) ≠ 0) :
    (localFieldPrimeKummerPairing K Ω q).IsPerfPair :=
  localFieldPrimeKummerPairing_isPerfPair K Ω q hζ hq

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  (S : Subgroup G) [Fintype (G ⧸ S)]



/-- Exact original-object consumer of `cosetTraceOne_coboundary`. -/
theorem actual_cup_descent_cosetTraceOne_coboundary_source (a : A) :
    cosetTraceOne A S (groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype) a) =
      groupCohomology.d₀₁ A (cosetTraceZero A S a) :=
  cosetTraceOne_coboundary A S a

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousRepresentationH1Corestriction_mk`. -/
theorem actual_cup_descent_continuousRepresentationH1Corestriction_mk_source
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationH1Corestriction A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCosetTraceOneCocycle A hA S hS c) :=
  continuousRepresentationH1Corestriction_mk A hA S hS c

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)



/-- Exact original-object consumer of `cosetTraceOne_restriction`. -/
theorem actual_cup_descent_cosetTraceOne_restriction_source [Fintype (G ⧸ S)] (c : groupCohomology.cocycles₁ A) :
    cosetTraceOne A S (fun h => c h) =
      Fintype.card (G ⧸ S) • (c : G → A) +
        groupCohomology.d₀₁ A (∑ q : G ⧸ S, c q.out) :=
  cosetTraceOne_restriction A S c

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

include hS

/-- Exact original-object consumer of `continuousRepresentationH1Restriction_coprime_zero`. -/
theorem actual_cup_descent_continuousRepresentationH1Restriction_coprime_zero_source
    (m : ℕ) (hm : m.Coprime (Fintype.card (G ⧸ S)))
    (x : ContinuousRepresentationH1 A hA) (hx : m • x = 0)
    (hres : continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x = 0) :
    x = 0 :=
  continuousRepresentationH1Restriction_coprime_zero A hA S hS m hm x hx hres

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (S : Subgroup G)

include hβ

/-- Exact original-object consumer of `cosetCupProjection_term`. -/
theorem actual_cup_descent_cosetCupProjection_term_source
    (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype))
    (g h : G) (q : G ⧸ S) :
    cosetTraceTwoTerm C S (fun z => β (c z.1) (B.ρ z.1 (v z.2))) g h q =
      β (c g) (B.ρ g (cosetTraceOneTerm B S v h q)) +
        C.ρ g (cosetCupProjectionCorrectionTerm A B C β S c v h q) -
        cosetCupProjectionCorrectionTerm A B C β S c v (g * h) q +
        cosetCupProjectionCorrectionTerm A B C β S c v g (h • q) :=
  cosetCupProjection_term A B C β hβ S c v g h q

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (S : Subgroup G) [Fintype (G ⧸ S)]

include hβ

/-- Exact original-object consumer of `cosetCupProjection_homotopy`. -/
theorem actual_cup_descent_cosetCupProjection_homotopy_source
    (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype)) :
    cosetTraceTwo C S (fun z => β (c z.1) (B.ρ z.1 (v z.2))) =
      (fun z : G × G => β (c z.1) (B.ρ z.1 (cosetTraceOne B S v z.2))) +
        groupCohomology.d₁₂ C (cosetCupProjectionCorrection A B C β S c v) :=
  cosetCupProjection_homotopy A B C β hβ S c v

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousH1Cup_corestriction_projection`. -/
theorem actual_cup_descent_continuousH1Cup_corestriction_projection_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep B S.subtype)
      (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB)) :
    continuousRepresentationH2Corestriction C hC S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep B S.subtype) (restrictedCoefficientRep C S.subtype)
        β (fun g a b => hβ g a b) hcβ
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB)
        (restrictedCoefficientAction_continuous C S.subtype continuous_subtype_val hC)
        (continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x) y) =
      continuousH1Cup A B C β hβ hcβ hA hB hC x
        (continuousRepresentationH1Corestriction B hB S hS y) :=
  continuousH1Cup_corestriction_projection A B C β hβ hcβ hA hB hC S hS x y

end

section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A B : Rep R G)
  (φ : A →ₗ[R] B) (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (S : Subgroup G) [Fintype (G ⧸ S)]

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hφ : Continuous φ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousCoefficientH2Map_corestriction`. -/
theorem actual_cup_descent_continuousCoefficientH2Map_corestriction_source
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)) :
    continuousCoefficientH2Map A B φ hφ hφρ hA hB
      (continuousRepresentationH2Corestriction A hA S hS x) =
      continuousRepresentationH2Corestriction B hB S hS
        (continuousCoefficientH2Map (restrictedCoefficientRep A S.subtype)
          (restrictedCoefficientRep B S.subtype) φ hφ (fun g a => hφρ g a)
          (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
          (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB) x) :=
  continuousCoefficientH2Map_corestriction A B φ hφρ S hφ hA hB hS x

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  {n : ℕ} [NeZero n] {μ : Ω} (hμ : IsPrimitiveRoot μ n)



/-- Exact original-object consumer of `originalPrimitiveRootStage_finrank_coprime`. -/
theorem actual_cup_descent_originalPrimitiveRootStage_finrank_coprime_source [Fact n.Prime] :
    n.Coprime (Module.finrank K (originalPrimitiveRootStage K Ω hμ)) :=
  originalPrimitiveRootStage_finrank_coprime K Ω hμ

end

section

open scoped BigOperators

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Exact original-object consumer of `continuousH1GroupEquiv_apply`. -/
theorem actual_cup_descent_continuousH1GroupEquiv_apply_source (x : ContinuousRepresentationH1 A hA) :
    continuousH1GroupEquiv A e he hei hA x =
      continuousRepresentationH1Restriction A hA e.toMonoidHom he x :=
  continuousH1GroupEquiv_apply A e he hei hA x

end

section

open scoped BigOperators

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



/-- Exact original-object consumer of `continuousH2GroupEquiv_apply`. -/
theorem actual_cup_descent_continuousH2GroupEquiv_apply_source (x : ContinuousRepresentationH2 A hA) :
    continuousH2GroupEquiv A e he hei hA x =
      continuousRepresentationH2Restriction A hA e.toMonoidHom he x :=
  continuousH2GroupEquiv_apply A e he hei hA x

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.fixingRootStageTopology Dubon2026.fixingRootStageDiscrete Dubon2026.fixingRootUnitTopology Dubon2026.fixingRootUnitDiscrete



/-- Exact original-object consumer of `galoisFixingRootH2Equiv_mk`. -/
theorem actual_cup_descent_galoisFixingRootH2Equiv_mk_source
    (c : continuousRepresentationCocyclesTwo
      (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)) :
    galoisFixingRootH2Equiv K Ω E n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction
        (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n)
        E.fixingSubgroupEquiv.toMonoidHom (fixingSubgroupEquiv_continuous K Ω E) c) :=
  galoisFixingRootH2Equiv_mk K Ω E n c

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.rootRestrictionStageTopology Dubon2026.rootRestrictionStageDiscrete Dubon2026.rootRestrictionUnitTopology Dubon2026.rootRestrictionUnitDiscrete



/-- Exact original-object consumer of `galoisRootContinuousRestriction_coprime_zero`. -/
theorem actual_cup_descent_galoisRootContinuousRestriction_coprime_zero_source [FiniteDimensional K E]
    [IsAlgClosed Ω] [NeZero n] (hn : n.Coprime (Module.finrank K E))
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (hx : galoisRootContinuousRestriction K Ω E n x = 0) : x = 0 :=
  galoisRootContinuousRestriction_coprime_zero K Ω E n hn x hx

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.rootCorestrictionStageTopology Dubon2026.rootCorestrictionStageDiscrete Dubon2026.rootCorestrictionUnitTopology Dubon2026.rootCorestrictionUnitDiscrete



/-- Exact original-object consumer of `galoisRootContinuousCorestriction_inclusion`. -/
theorem actual_cup_descent_galoisRootContinuousCorestriction_inclusion_source
    (x : GaloisRootContinuousH2 (K := E) (Ω := Ω) n) :
    galoisKummerH2Inclusion (K := K) (Ω := Ω) n
      (galoisRootContinuousCorestriction K Ω E n x) =
      galoisUnitContinuousCorestriction K Ω E
        (galoisKummerH2Inclusion (K := E) (Ω := Ω) n x) :=
  galoisRootContinuousCorestriction_inclusion K Ω E n x

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.rootLocalCorestrictionIsGalois Dubon2026.rootLocalCorestrictionStageTopology Dubon2026.rootLocalCorestrictionStageDiscrete Dubon2026.rootLocalCorestrictionUnitTopology Dubon2026.rootLocalCorestrictionUnitDiscrete

include dUnits

/-- Exact original-object consumer of `localFieldRootContinuousCorestriction_injective`. -/
theorem actual_cup_descent_localFieldRootContinuousCorestriction_injective_source :
    Function.Injective (galoisRootContinuousCorestriction K Ω E n) :=
  localFieldRootContinuousCorestriction_injective K Ω E n

end

section

open scoped BigOperators

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)



/-- Exact original-object consumer of `continuousGaloisFiniteCharacterH1_surjective`. -/
theorem actual_cup_descent_continuousGaloisFiniteCharacterH1_surjective_source
    (x : ContinuousRepresentationH1
      (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) continuous_snd) :
    ∃ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle n χ) = x :=
  continuousGaloisFiniteCharacterH1_surjective n x

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.fixingRootCupStageTopology Dubon2026.fixingRootCupStageDiscrete Dubon2026.fixingRootCupUnitTopology Dubon2026.fixingRootCupUnitDiscrete



/-- Exact original-object consumer of `galoisFixingRootH2Equiv_cup`. -/
theorem actual_cup_descent_galoisFixingRootH2Equiv_cup_source (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n))
    (x : GaloisRootContinuousH1 (K := E) (Ω := Ω) n) :
    galoisFixingRootH2Equiv K Ω E n (continuousGaloisRootCharacterH1Cup n χ x) =
      galoisFixingRootCharacterH1Cup K Ω E n χ (galoisFixingRootH1Equiv K Ω E n x) :=
  galoisFixingRootH2Equiv_cup K Ω E n χ x

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.rootCupCorestrictionStageTopology Dubon2026.rootCupCorestrictionStageDiscrete Dubon2026.rootCupCorestrictionUnitTopology Dubon2026.rootCupCorestrictionUnitDiscrete



/-- Exact original-object consumer of `galoisRootCharacterCup_corestriction`. -/
theorem actual_cup_descent_galoisRootCharacterCup_corestriction_source
    (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n)) :
    ∃ ψ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      ∀ x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n,
        galoisRootContinuousCorestriction K Ω E n
          (continuousGaloisRootCharacterH1Cup (K := E) (Ω := Ω) n χ
            (galoisRootContinuousRestriction K Ω E n x)) =
          continuousGaloisRootCharacterH1Cup (K := K) (Ω := Ω) n ψ x :=
  galoisRootCharacterCup_corestriction K Ω E n χ

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] Dubon2026.rootDescentIsGalois Dubon2026.rootDescentStageTopology Dubon2026.rootDescentStageDiscrete Dubon2026.rootDescentUnitTopology Dubon2026.rootDescentUnitDiscrete



/-- Exact original-object consumer of `localFieldKummer_root_annihilator_coprime_descent`. -/
theorem actual_cup_descent_localFieldKummer_root_annihilator_coprime_descent_source
    (hn : n.Coprime (Module.finrank K E)) {ζ : E} (hζ : IsPrimitiveRoot ζ n)
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (hx : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      continuousGaloisRootCharacterH1Cup n χ x = 0) : x = 0 :=
  localFieldKummer_root_annihilator_coprime_descent K Ω E n hn hζ x hx

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldPrimeKummer_root_eq_zero_of_cup_zero`. -/
theorem actual_cup_descent_localFieldPrimeKummer_root_eq_zero_of_cup_zero_source (hq : (q : K) ≠ 0)
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) q)
    (hx : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod q),
      continuousGaloisRootCharacterH1Cup q χ x = 0) : x = 0 :=
  localFieldPrimeKummer_root_eq_zero_of_cup_zero K Ω q hq x hx

end

section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] galoisFiniteCharacterZModModule galoisRootH1ZModModule

/-- Exact original-object consumer of `localFieldPrimeKummerPairing_isPerfPair_of_nonzero`. -/
theorem actual_cup_descent_localFieldPrimeKummerPairing_isPerfPair_of_nonzero_source (hq : (q : K) ≠ 0) :
    (localFieldPrimeKummerPairing K Ω q).IsPerfPair :=
  localFieldPrimeKummerPairing_isPerfPair_of_nonzero K Ω q hq

end

section

open Matrix

variable {G V : Type} [Group G] [TopologicalSpace G]
  (q : ℕ) [Fact q.Prime] [AddCommGroup V] [Module (ZMod q) V]
  [TopologicalSpace V] [DiscreteTopology V]

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `continuousTrivialCocycles_finite`. -/
theorem actual_finite_local_h1_continuousTrivialCocycles_finite_source [Module.Finite (ZMod q) V]
    [Finite (G →ₜ* Multiplicative (ZMod q))] :
    Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) G V))) :=
  continuousTrivialCocycles_finite q

end

section

open Matrix

variable (K Ω V : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [AddCommGroup V] [Module (ZMod q) V] [Finite V]
  [TopologicalSpace V] [DiscreteTopology V]

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `localField_finiteTrivialCocycles`. -/
theorem actual_finite_local_h1_localField_finiteTrivialCocycles_source (hq : (q : K) ≠ 0) :
    Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) Gal(Ω/K) V))) :=
  localField_finiteTrivialCocycles K Ω V q hq

end

section

open Matrix

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (S : Subgroup G)

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero

include S

/-- Exact original-object consumer of `continuousCocyclesOne_finite_of_restriction`. -/
theorem actual_finite_local_h1_continuousCocyclesOne_finite_of_restriction_source [Finite A] [Finite (G ⧸ S)]
    [Finite (continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype))] :
    Finite (continuousRepresentationCocyclesOne A) :=
  continuousCocyclesOne_finite_of_restriction A S

end

section

open Matrix

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]
  (A : Rep R G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `continuousFiniteCoefficient_exists_splittingField`. -/
theorem actual_finite_local_h1_continuousFiniteCoefficient_exists_splittingField_source
    (B : Rep R Gal(Ω/K)) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∀ g : Gal(Ω/K), g ∈ F.toIntermediateField.fixingSubgroup → ∀ b : B, B.ρ g b = b :=
  continuousFiniteCoefficient_exists_splittingField B hB

end

section

open Matrix

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(Ω/K))
  [TopologicalSpace A] [DiscreteTopology A] (E : IntermediateField K Ω)
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `finiteCoefficientFixingCocycleEquiv_apply`. -/
theorem actual_finite_local_h1_finiteCoefficientFixingCocycleEquiv_apply_source
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep A E.fixingSubgroup.subtype))
    (g : Gal(Ω/E)) :
    (finiteCoefficientFixingCocycleEquiv K Ω q A E hE c).val g =
      c.val (E.fixingSubgroupEquiv.symm g) :=
  finiteCoefficientFixingCocycleEquiv_apply K Ω q A E hE c g

end

section

open Matrix

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(Ω/K))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `localField_finiteCoefficientH1`. -/
theorem actual_finite_local_h1_localField_finiteCoefficientH1_source (hq : (q : K) ≠ 0) :
    Finite (ContinuousRepresentationH1 A hA) :=
  localField_finiteCoefficientH1 K Ω q A hA hq

end

section

open Matrix

variable {k G : Type} [Field k] [Group G] (q : ℕ) [Fact q.Prime] [CharP k q]
  (A : Rep.{0} k G)

variable [TopologicalSpace k] [DiscreteTopology k] [TopologicalSpace G]
  [TopologicalSpace A] [DiscreteTopology A]

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `localField_finiteScalarCoefficientH1`. -/
theorem actual_finite_local_h1_localField_finiteScalarCoefficientH1_source
    (B : Rep.{0} k Gal(Ω/K)) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2)) (hq : (q : K) ≠ 0) :
    Finite (ContinuousRepresentationH1 B hB) :=
  localField_finiteScalarCoefficientH1 q K Ω B hB hq

end

section

open Matrix

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime] [CharP k q]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι k) (hρ : Continuous ρ)

attribute [local instance] continuousTrivialCoordinateSMul finiteScalarPrimeModule finiteScalarOriginalContinuousSMul finiteScalarPrimeContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `rationalPrimeTraceCupDomains_finite`. -/
theorem actual_finite_local_h1_rationalPrimeTraceCupDomains_finite_source :
    Finite (ContinuousTraceZeroAdjointH1 ρ hρ) ∧
      Finite (ContinuousRepresentationH1
        (matrixTraceZeroCharacterRep ρ
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
        (matrixTraceZeroCharacterAction_continuous ρ hρ
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) :=
  rationalPrimeTraceCupDomains_finite p hp q ρ hρ

end

section

variable {R G : Type} [CommRing R] [Group G]
  (A B C : Rep.{0} R G)
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)

variable [TopologicalSpace R] [TopologicalSpace G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B]
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))



/-- Exact original-object consumer of `coefficientInvariantConnectingCocycle_map`. -/
theorem actual_connecting_cup_coefficientInvariantConnectingCocycle_map_source (c : C.ρ.invariants) (g : G) :
    φ ((coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val g) =
      B.ρ g (exactCoefficientSection ψ hψ c.val) - exactCoefficientSection ψ hψ c.val :=
  coefficientInvariantConnectingCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c g

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))



/-- Exact original-object consumer of `continuousCoefficientInvariantConnectingMap_apply`. -/
theorem actual_connecting_cup_continuousCoefficientInvariantConnectingMap_apply_source (c : C.ρ.invariants) :
    continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c =
      (Submodule.Quotient.mk
        (coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH1 A hA) :=
  continuousCoefficientInvariantConnectingMap_apply A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c

end

section

variable {R G : Type} [CommRing R] [Group G]
  (A B C U V W D : Rep.{0} R G)
  (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C)
  (ι : U →ₗ[R] V) (π : V →ₗ[R] W)
  (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
  (hπ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
  (α : A →ₗ[R] W →ₗ[R] D) (β : B →ₗ[R] V →ₗ[R] D)
  (γ : C →ₗ[R] U →ₗ[R] D)
  (hβ : ∀ g b v, β (B.ρ g b) (V.ρ g v) = D.ρ g (β b v))
  (hαβ : ∀ a v, β (φ a) v = α a (π v))
  (hγβ : ∀ b u, β b (ι u) = γ (ψ b) u)

include hι hπ hβ hαβ hγβ

/-- Exact original-object consumer of `connectingCupAdjunction_boundary`. -/
theorem actual_connecting_cup_connectingCupAdjunction_boundary_source
    (b : G → B) (a : G × G → A) (c : G → C) (u : G → U)
    (v : V) (w : W.ρ.invariants)
    (hb : ∀ g, ψ (b g) = c g)
    (ha : ∀ g h, φ (a (g, h)) = B.ρ g (b h) - b (g * h) + b g)
    (hu : ∀ g, ι (u g) = V.ρ g v - v) (hv : π v = w.val)
    (g h : G) :
    groupCohomology.d₁₂ D (fun t => β (b t) (V.ρ t v)) (g, h) =
      α (a (g, h)) w.val - γ (c g) (U.ρ g (u h)) :=
  connectingCupAdjunction_boundary A B C U V W D φ ψ ι π hι hπ α β γ hβ hαβ hγβ b a c u v w hb ha hu hv g h

end

section

variable {R G : Type} [CommRing R] [Group G]
  (A W D : Rep.{0} R G) (α : A →ₗ[R] W →ₗ[R] D)
  (hα : ∀ g a w, α (A.ρ g a) (W.ρ g w) = D.ρ g (α a w))

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace W]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  (hcα : Continuous (fun z : A × W => α z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))



/-- Exact original-object consumer of `continuousInvariantRightH2Map_mk`. -/
theorem actual_connecting_cup_continuousInvariantRightH2Map_mk_source (w : W.ρ.invariants)
    (c : continuousRepresentationCocyclesTwo A) :
    continuousInvariantRightH2Map A W D α hα hcα hA hD w (Submodule.Quotient.mk c) =
      (Submodule.Quotient.mk
        (continuousCoefficientCocycleTwoMap A D (α.flip w.val)
          (hcα.comp (continuous_id.prodMk continuous_const))
          (invariantRightPairing_equivariant A W D α hα w) c) :
        ContinuousRepresentationH2 D hD) :=
  continuousInvariantRightH2Map_mk A W D α hα hcα hA hD w c

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C U V W D : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul R U]
  [TopologicalSpace V] [DiscreteTopology V]
  [TopologicalSpace W]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (ι : U →ₗ[R] V) (hι : Function.Injective ι)
  (hιρ : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
  (π : V →ₗ[R] W) (hπ : Function.Surjective π)
  (hπρ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
  (hDualExact : LinearMap.range ι = LinearMap.ker π)
  (α : A →ₗ[R] W →ₗ[R] D) (β : B →ₗ[R] V →ₗ[R] D)
  (γ : C →ₗ[R] U →ₗ[R] D)
  (hα : ∀ g a w, α (A.ρ g a) (W.ρ g w) = D.ρ g (α a w))
  (hβ : ∀ g b v, β (B.ρ g b) (V.ρ g v) = D.ρ g (β b v))
  (hγ : ∀ g c u, γ (C.ρ g c) (U.ρ g u) = D.ρ g (γ c u))
  (hαβ : ∀ a v, β (φ a) v = α a (π v))
  (hγβ : ∀ b u, β b (ι u) = γ (ψ b) u)
  (hcα : Continuous (fun z : A × W => α z.1 z.2))
  (hcβ : Continuous (fun z : B × V => β z.1 z.2))
  (hcγ : Continuous (fun z : C × U => γ z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (hU : Continuous (fun z : G × U => U.ρ z.1 z.2))
  (hV : Continuous (fun z : G × V => V.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

include hβ hαβ hγβ hcβ

/-- Exact original-object consumer of `continuousConnectingCup_adjunction`. -/
theorem actual_connecting_cup_continuousConnectingCup_adjunction_source
    (x : ContinuousRepresentationH1 C hC) (w : W.ρ.invariants) :
    continuousInvariantRightH2Map A W D α hα hcα hA hD w
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) =
      continuousH1Cup C U D γ hγ hcγ hC hU hD x
        (continuousCoefficientInvariantConnectingMap U V W ι hι hιρ π hπ hπρ hDualExact hU hV w) :=
  continuousConnectingCup_adjunction A B C U V W D φ hφ hφρ ψ hψ hψρ hExact ι hι hιρ π hπ hπρ hDualExact α β γ hα hβ hγ hαβ hγβ hcα hcβ hcγ hA hB hC hU hV hD x w

end

section

variable {k G : Type} [Field k] [Group G]
  (A B C : Rep.{0} k G) (χ : G →* k)

attribute [local instance] characterDualSequenceContinuousSMul



/-- Exact original-object consumer of `characterDualCoefficientSequence_exact`. -/
theorem actual_dual_coefficients_characterDualCoefficientSequence_exact_source
    (φ : A →ₗ[k] B) (ψ : B →ₗ[k] C)
    (hExact : LinearMap.range φ = LinearMap.ker ψ) :
    LinearMap.range (characterDualCoefficientMap B C χ ψ) =
      LinearMap.ker (characterDualCoefficientMap A B χ φ) :=
  characterDualCoefficientSequence_exact A B C χ φ ψ hExact

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]

attribute [local instance] characterDualSequenceContinuousSMul



/-- Exact original-object consumer of `finiteCharacterDualAction_continuous`. -/
theorem actual_dual_coefficients_finiteCharacterDualAction_continuous_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ) :
    Continuous (fun z : G × characterDualCoefficientRep A χ =>
      (characterDualCoefficientRep A χ).ρ z.1 z.2) :=
  finiteCharacterDualAction_continuous A χ hA hχ

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul



/-- Exact original-object consumer of `continuousInvariantConnecting_mem_range_iff`. -/
theorem actual_dual_coefficients_continuousInvariantConnecting_mem_range_iff_source (hcφ : Continuous φ)
    (x : ContinuousRepresentationH1 A hA) :
    x ∈ LinearMap.range
      (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB) ↔
        continuousCoefficientH1Map A B φ hcφ hφρ hA hB x = 0 :=
  continuousInvariantConnecting_mem_range_iff A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hcφ x

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]

variable (A B C : Rep.{0} k G)
  [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul



/-- Exact original-object consumer of `finiteCharacterDualConnecting_adjunction`. -/
theorem actual_dual_coefficients_finiteCharacterDualConnecting_adjunction_source
    (x : ContinuousRepresentationH1 C hC)
    (w : (characterDualCoefficientRep A χ).ρ.invariants) :
    let U := characterDualCoefficientRep C χ
    let V := characterDualCoefficientRep B χ
    let W := characterDualCoefficientRep A χ
    let D := coefficientCharacterRep χ
    let hU := finiteCharacterDualAction_continuous C χ hC hχ
    let hV := finiteCharacterDualAction_continuous B χ hB hχ
    let hD := coefficientCharacterAction_continuous χ hχ
    continuousInvariantRightH2Map A W D (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ) continuous_of_discreteTopology hA hD w
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) =
      continuousH1Cup C U D (characterDualEvaluation C χ)
        (characterDualEvaluation_equivariant C χ) continuous_of_discreteTopology hC hU hD x
        (continuousCoefficientInvariantConnectingMap U V W
          (characterDualCoefficientMap B C χ ψ)
          (characterDualCoefficientMap_injective B C χ ψ hψ)
          (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
          (characterDualCoefficientMap A B χ φ)
          (characterDualCoefficientMap_surjective A B χ φ hφ)
          (characterDualCoefficientMap_equivariant A B χ φ hφρ)
          (characterDualCoefficientSequence_exact A B C χ φ ψ hExact) hU hV w):=
  finiteCharacterDualConnecting_adjunction A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC x w

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [Finite (G ⧸ S)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))

attribute [local instance] characterDualSequenceContinuousSMul

include hA hS

/-- Exact original-object consumer of `finiteCoinducedCoefficientAction_continuous`. -/
theorem actual_dual_coefficients_finiteCoinducedCoefficientAction_continuous_source :
    Continuous (fun z : G × Rep.coind S.subtype (Rep.res S.subtype A) =>
      (Rep.coind S.subtype (Rep.res S.subtype A)).ρ z.1 z.2) :=
  finiteCoinducedCoefficientAction_continuous A S hA hS

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedCosetReconstruct_values`. -/
theorem actual_continuous_shapiro_coinducedCosetReconstruct_values_source
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) :
    coinducedCosetReconstruct A S (coinducedCosetValues A S f) = f :=
  coinducedCosetReconstruct_values A S f

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedShapiroTwo_values`. -/
theorem actual_continuous_shapiro_coinducedShapiroTwo_values_source (c : S × S → A) (g h : G) :
    coinducedCosetValues A S (coinducedShapiroTwo A S c (g, h)) =
      fun q => cosetTraceTwoTerm A S c g h ((g * h)⁻¹ • q) :=
  coinducedShapiroTwo_values A S c g h

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedShapiroTwo_mem_cocycles`. -/
theorem actual_continuous_shapiro_coinducedShapiroTwo_mem_cocycles_source
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    coinducedShapiroTwo A S c ∈
      groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)) :=
  coinducedShapiroTwo_mem_cocycles A S c

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]

include hA hS

/-- Exact original-object consumer of `coinducedShapiroTwo_continuous`. -/
theorem actual_continuous_shapiro_coinducedShapiroTwo_continuous_source (c : S × S → A) (hc : Continuous c) :
    Continuous (coinducedShapiroTwo A S c) :=
  coinducedShapiroTwo_continuous A hA S hS c hc

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedShapiroH2_mk`. -/
theorem actual_continuous_shapiro_continuousCoinducedShapiroH2_mk_source
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousCoinducedShapiroH2 A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoinducedShapiroCocycleTwo A hA S hS c) :=
  continuousCoinducedShapiroH2_mk A hA S hS c

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedEvaluationH2_mk`. -/
theorem actual_continuous_shapiro_continuousCoinducedEvaluationH2_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.coind S.subtype (Rep.res S.subtype A))) :
    continuousCoinducedEvaluationH2 A S hA hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype)
        (restrictedCoefficientRep A S.subtype) (coinducedIdentityEvaluation A S)
        continuous_of_discreteTopology (coinducedIdentityEvaluation_equivariant A S)
        (continuousRepresentationCocycleTwoRestriction
          (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype continuous_subtype_val c)) :=
  continuousCoinducedEvaluationH2_mk A S hA hS c

end

section

variable {G : Type} [Group G] (S : Subgroup G)



/-- Exact original-object consumer of `coinducedSubgroupCoordinate_continuous`. -/
theorem actual_continuous_shapiro_coinducedSubgroupCoordinate_continuous_source [TopologicalSpace G] [IsTopologicalGroup G]
    (hS : IsOpen (S : Set G)) : Continuous (coinducedSubgroupCoordinate S) :=
  coinducedSubgroupCoordinate_continuous S hS

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedHomogeneousTwo_cocycle`. -/
theorem actual_continuous_shapiro_inverse_coinducedHomogeneousTwo_cocycle_source
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y z t : G) :
    coinducedHomogeneousTwo A S c x z t + coinducedHomogeneousTwo A S c x y z =
      coinducedHomogeneousTwo A S c y z t + coinducedHomogeneousTwo A S c x y t :=
  coinducedHomogeneousTwo_cocycle A S c x y z t

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedHomogeneousTwo_prism`. -/
theorem actual_continuous_shapiro_inverse_coinducedHomogeneousTwo_prism_source
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y z px py pz : G) :
    (coinducedHomogeneousTwo A S c y py pz - coinducedHomogeneousTwo A S c y z pz) -
      (coinducedHomogeneousTwo A S c x px pz - coinducedHomogeneousTwo A S c x z pz) +
      (coinducedHomogeneousTwo A S c x px py - coinducedHomogeneousTwo A S c x y py) =
        coinducedHomogeneousTwo A S c px py pz - coinducedHomogeneousTwo A S c x y z :=
  coinducedHomogeneousTwo_prism A S c x y z px py pz

end

section

variable {G : Type} [Group G] (S : Subgroup G)

variable {R : Type} [CommRing R] (A : Rep.{0} R G)



/-- Exact original-object consumer of `coinducedShapiroTwo_evaluation_value`. -/
theorem actual_continuous_shapiro_inverse_coinducedShapiroTwo_evaluation_value_source
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (g h t : G) :
    (coinducedShapiroTwo A S (fun z : S × S => (c (z.1, z.2)).val 1) (g, h)).val t =
      coinducedHomogeneousTwo A S c (coinducedSubgroupCoordinate S t)
        (coinducedSubgroupCoordinate S (t * g)) (coinducedSubgroupCoordinate S ((t * g) * h)) :=
  coinducedShapiroTwo_evaluation_value S A c g h t

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedShapiroH1_evaluation`. -/
theorem actual_continuous_shapiro_inverse_continuousCoinducedShapiroH1_evaluation_source
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS)) :
    continuousCoinducedShapiroH1 A hA S hS (continuousCoinducedEvaluationH1 A S hA hS x) = x :=
  continuousCoinducedShapiroH1_evaluation A S hA hS x

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedShapiroH1_bijective`. -/
theorem actual_continuous_shapiro_inverse_continuousCoinducedShapiroH1_bijective_source :
    Function.Bijective (continuousCoinducedShapiroH1 A hA S hS) :=
  continuousCoinducedShapiroH1_bijective A S hA hS

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]

include hA hS

/-- Exact original-object consumer of `coinducedHomogeneousTwo_continuous`. -/
theorem actual_continuous_shapiro_inverse_coinducedHomogeneousTwo_continuous_source {X : Type} [TopologicalSpace X]
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (hc : Continuous c)
    (x y z : X → G) (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun t => coinducedHomogeneousTwo A S c (x t) (y t) (z t)) :=
  coinducedHomogeneousTwo_continuous A hA S hS c hc x y z hx hy hz

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)



/-- Exact original-object consumer of `coinducedShapiroTwo_evaluation_sub`. -/
theorem actual_continuous_shapiro_inverse_coinducedShapiroTwo_evaluation_sub_source
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A))) :
    coinducedShapiroTwo A S (fun z : S × S => (c (z.1, z.2)).val 1) - c.val =
      groupCohomology.d₁₂ (Rep.coind S.subtype (Rep.res S.subtype A))
        (coinducedShapiroTwoHomotopy A S c) :=
  coinducedShapiroTwo_evaluation_sub A S c

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]

variable [TopologicalSpace R] [ContinuousSMul R A]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedShapiroH2_evaluation`. -/
theorem actual_continuous_shapiro_inverse_continuousCoinducedShapiroH2_evaluation_source
    (x : ContinuousRepresentationH2 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS)) :
    continuousCoinducedShapiroH2 A hA S hS (continuousCoinducedEvaluationH2 A S hA hS x) = x :=
  continuousCoinducedShapiroH2_evaluation A hA S hS x

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)



/-- Exact original-object consumer of `coinducedEvaluation_shapiroTwo_sub`. -/
theorem actual_continuous_shapiro_inverse_coinducedEvaluation_shapiroTwo_sub_source (S : Subgroup G)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    (fun z : S × S => (coinducedShapiroTwo A S c (z.1, z.2)).val 1) - c.val =
      groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype)
        (coefficientConjugationTwoHomotopy (restrictedCoefficientRep A S.subtype) c
          (coinducedSubgroupCoordinate S 1)) :=
  coinducedEvaluation_shapiroTwo_sub A S c

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedShapiroH2_bijective`. -/
theorem actual_continuous_shapiro_inverse_continuousCoinducedShapiroH2_bijective_source :
    Function.Bijective (continuousCoinducedShapiroH2 A hA S hS) :=
  continuousCoinducedShapiroH2_bijective A S hA hS

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  [Fintype (G ⧸ S)] (χ : G →* k)



/-- Exact original-object consumer of `coinducedCharacterDualEquiv_equivariant`. -/
theorem actual_induced_duality_coinducedCharacterDualEquiv_equivariant_source (g : G)
    (ℓ : Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))) :
    coinducedCharacterDualEquiv A S χ
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g ℓ) =
        (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ).ρ g
          (coinducedCharacterDualEquiv A S χ ℓ) :=
  coinducedCharacterDualEquiv_equivariant A S χ g ℓ

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  (χ : G →* k)



/-- Exact original-object consumer of `coinducedShapiroCup_values`. -/
theorem actual_induced_duality_coinducedShapiroCup_values_source (f : S → A) (u : S → characterDualCoefficientRep A χ)
    (g h : G) (q : G ⧸ S) :
    (coinducedCosetValues (characterDualCoefficientRep A χ) S
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g
        (coinducedShapiroOne (characterDualCoefficientRep A χ) S u h)) ((g * h) • q))
      (coinducedCosetValues A S (coinducedShapiroOne A S f g) ((g * h) • q)) =
    cosetTraceTwoTerm (coefficientCharacterRep χ) S
      (fun z : S × S => characterDualEvaluation A χ (f z.1)
        ((characterDualCoefficientRep A χ).ρ (z.1 : G) (u z.2))) g h q :=
  coinducedShapiroCup_values A S χ f u g h q

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  [Fintype (G ⧸ S)] (χ : G →* k)



/-- Exact original-object consumer of `coinducedShapiroCup_cochain`. -/
theorem actual_induced_duality_coinducedShapiroCup_cochain_source (f : S → A) (u : S → characterDualCoefficientRep A χ) :
    (fun z : G × G => coinducedCharacterPairing A S χ
      (coinducedShapiroOne A S f z.1)
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ z.1
        (coinducedShapiroOne (characterDualCoefficientRep A χ) S u z.2))) =
      cosetTraceTwo (coefficientCharacterRep χ) S
        (fun z : S × S => characterDualEvaluation A χ (f z.1)
          ((characterDualCoefficientRep A χ).ρ (z.1 : G) (u z.2))) :=
  coinducedShapiroCup_cochain A S χ f u

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k)
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [ContinuousSMul k (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul k (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [ContinuousSMul k (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hD : Continuous (fun z : G × characterDualCoefficientRep A χ =>
    (characterDualCoefficientRep A χ).ρ z.1 z.2))
  (hC : Continuous (fun z : G × coefficientCharacterRep χ =>
    (coefficientCharacterRep χ).ρ z.1 z.2)) (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousCoinducedShapiroH1_cup`. -/
theorem actual_induced_duality_continuousCoinducedShapiroH1_cup_source
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
        S.subtype continuous_subtype_val hD)) :
    continuousH1Cup (Rep.coind S.subtype (Rep.res S.subtype A))
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (coefficientCharacterRep χ) (coinducedCharacterPairing A S χ)
      (coinducedCharacterPairing_equivariant A S χ) continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S hD hS) hC
      (continuousCoinducedShapiroH1 A hA S hS x)
      (continuousCoinducedShapiroH1 (characterDualCoefficientRep A χ) hD S hS y) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ) hC S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
        (restrictedCoefficientRep (coefficientCharacterRep χ) S.subtype)
        (characterDualEvaluation A χ) (fun g a ℓ => characterDualEvaluation_equivariant A χ g a ℓ)
        continuous_of_discreteTopology
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
          S.subtype continuous_subtype_val hD)
        (restrictedCoefficientAction_continuous (coefficientCharacterRep χ)
          S.subtype continuous_subtype_val hC) x y) :=
  continuousCoinducedShapiroH1_cup A S χ hA hD hC hS x y

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]



/-- Exact original-object consumer of `continuousCoinducedEvaluationH2_unit`. -/
theorem actual_induced_duality_continuousCoinducedEvaluationH2_unit_source (x : ContinuousRepresentationH2 A hA) :
    continuousCoinducedEvaluationH2 A S hA hS
      (continuousCoefficientH2Map A (Rep.coind S.subtype (Rep.res S.subtype A))
        (finiteCoinducedCoefficientUnit A S) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A S) hA
        (finiteCoinducedCoefficientAction_continuous A S hA hS) x) =
      continuousRepresentationH2Restriction A hA S.subtype continuous_subtype_val x :=
  continuousCoinducedEvaluationH2_unit A S hA hS x

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



/-- Exact original-object consumer of `continuousH2_exists_openNormal_restriction_zero`. -/
theorem actual_induced_duality_continuousH2_exists_openNormal_restriction_zero_source (x : ContinuousRepresentationH2 A hA) :
    ∃ U : OpenNormalSubgroup G,
      continuousRepresentationH2Restriction A hA U.toSubgroup.subtype continuous_subtype_val x = 0 :=
  continuousH2_exists_openNormal_restriction_zero A hA x

end

section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [DiscreteTopology R]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep.{0} R G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

attribute [local instance] finiteEffacementCoefficientTopology finiteEffacementCoefficientDiscrete finiteEffacementScalarContinuous finiteEffacementCosets

/-- Exact original-object consumer of `continuousH2_exists_finite_coinduced_effacement`. -/
theorem actual_induced_duality_continuousH2_exists_finite_coinduced_effacement_source (x : ContinuousRepresentationH2 A hA) :
    ∃ U : OpenNormalSubgroup G,
      Finite (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A)) ∧
      Function.Injective (finiteCoinducedCoefficientUnit A U.toSubgroup) ∧
      continuousCoefficientH2Map A (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A))
        (finiteCoinducedCoefficientUnit A U.toSubgroup) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A U.toSubgroup) hA
        (finiteCoinducedCoefficientAction_continuous A U.toSubgroup hA U.isOpen) x = 0 :=
  continuousH2_exists_finite_coinduced_effacement A hA x

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

variable [TopologicalSpace G]

variable [IsTopologicalGroup G] [TopologicalSpace A] [DiscreteTopology A]
  [Finite (G ⧸ S)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (finiteCoinducedCoefficientQuotient A S)]
  [DiscreteTopology (finiteCoinducedCoefficientQuotient A S)]



/-- Exact original-object consumer of `finiteCoinducedCoefficientQuotientAction_continuous`. -/
theorem actual_induced_duality_finiteCoinducedCoefficientQuotientAction_continuous_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G)) :
    Continuous (fun z : G × finiteCoinducedCoefficientQuotient A S =>
      (finiteCoinducedCoefficientQuotient A S).ρ z.1 z.2) :=
  finiteCoinducedCoefficientQuotientAction_continuous A S hA hS

end

section

variable {k G ι : Type} [Field k] [Group G]
  (A : Rep.{0} k G)
  (χ : G →* k) (b : Module.Basis ι k A)
  (hscalar : ∀ g a, A.ρ g a = χ g • a)

variable [Fintype ι] [TopologicalSpace k] [IsTopologicalRing k]
  [TopologicalSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ)




/-- Exact original-object consumer of `continuousScalarH1_eq_zero_of_coordinates`. -/
theorem actual_split_duality_continuousScalarH1_eq_zero_of_coordinates_source (x : ContinuousRepresentationH1 A hA)
    (hx : ∀ i, continuousCoefficientH1Map A (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology (scalarCoefficientCoordinate_equivariant A χ b hscalar i)
      hA (coefficientCharacterAction_continuous χ hχ) x = 0) : x = 0 :=
  continuousScalarH1_eq_zero_of_coordinates A χ b hscalar hA hχ x hx

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

variable (B : Rep.{0} k G) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (φ : A →ₗ[k] B) (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH1Cup_naturality`. -/
theorem actual_split_duality_continuousCharacterDualH1Cup_naturality_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep B χ)
      (finiteCharacterDualAction_continuous B χ hB hχ)) :
    continuousCharacterDualH1Cup A χ hχ hA x
      (continuousCoefficientH1Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) y) =
      continuousCharacterDualH1Cup B χ hχ hB
        (continuousCoefficientH1Map A B φ continuous_of_discreteTopology hφρ hA hB x) y :=
  continuousCharacterDualH1Cup_naturality A χ hχ hA B hB φ hφρ x y

end

section

variable {k G ι : Type} [Field k] [Finite k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH1Cup_left_zero`. -/
theorem actual_split_duality_continuousTrivialCharacterDualH1Cup_left_zero_source
    (hbase : Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : G →* k)) χ hχ
      (coefficientCharacterAction_continuous (1 : G →* k) continuous_const)))
    (x : ContinuousRepresentationH1 A hA)
    (hx : ∀ y, continuousCharacterDualH1Cup A χ hχ hA x y = 0) : x = 0 :=
  continuousTrivialCharacterDualH1Cup_left_zero A χ hχ b htrivial hA hbase x hx

end

section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G]
  (A : Rep.{0} R G) (B : Rep.{0} S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (e : A ≃+ B) (he : Continuous e) (hei : Continuous e.symm)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))




/-- Exact original-object consumer of `continuousH1AdditiveCoefficientEquiv_mk`. -/
theorem actual_split_duality_continuousH1AdditiveCoefficientEquiv_mk_source (c : continuousRepresentationCocyclesOne A) :
    continuousH1AdditiveCoefficientEquiv A B e he hei heρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv A B e he hei heρ c) :=
  continuousH1AdditiveCoefficientEquiv_mk A B e he hei heρ hA hB c

end

section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep.{0} R G) (A' B' C' : Rep.{0} S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  [TopologicalSpace A'] [IsTopologicalAddGroup A'] [ContinuousSMul S A']
  [TopologicalSpace B'] [IsTopologicalAddGroup B'] [ContinuousSMul S B']
  [TopologicalSpace C'] [IsTopologicalAddGroup C'] [ContinuousSMul S C']
  (eA : A ≃+ A') (heA : Continuous eA) (heAi : Continuous eA.symm)
  (heAρ : ∀ g a, eA (A.ρ g a) = A'.ρ g (eA a))
  (eB : B ≃+ B') (heB : Continuous eB) (heBi : Continuous eB.symm)
  (heBρ : ∀ g b, eB (B.ρ g b) = B'.ρ g (eB b))
  (eC : C ≃+ C') (heC : Continuous eC) (heCi : Continuous eC.symm)
  (heCρ : ∀ g c, eC (C.ρ g c) = C'.ρ g (eC c))
  (β : A →ₗ[R] B →ₗ[R] C) (β' : A' →ₗ[S] B' →ₗ[S] C')
  (hβ : ∀ g a b, β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b))
  (hβ' : ∀ g a b, β' (A'.ρ g a) (B'.ρ g b) = C'.ρ g (β' a b))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hcβ' : Continuous (fun z : A' × B' => β' z.1 z.2))
  (hpair : ∀ a b, eC (β a b) = β' (eA a) (eB b))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (hA' : Continuous (fun z : G × A' => A'.ρ z.1 z.2))
  (hB' : Continuous (fun z : G × B' => B'.ρ z.1 z.2))
  (hC' : Continuous (fun z : G × C' => C'.ρ z.1 z.2))


include hpair

/-- Exact original-object consumer of `continuousH1Cup_additiveCoefficientEquiv`. -/
theorem actual_split_duality_continuousH1Cup_additiveCoefficientEquiv_source
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousH2AdditiveCoefficientEquiv C C' eC heC heCi heCρ hC hC'
      (continuousH1Cup A B C β hβ hcβ hA hB hC x y) =
      continuousH1Cup A' B' C' β' hβ' hcβ' hA' hB' hC'
        (continuousH1AdditiveCoefficientEquiv A A' eA heA heAi heAρ hA hA' x)
        (continuousH1AdditiveCoefficientEquiv B B' eB heB heBi heBρ hB hB' y) :=
  continuousH1Cup_additiveCoefficientEquiv A B C A' B' C' eA heA heAi heAρ eB heB heBi heBρ eC heC heCi heCρ β β' hβ hβ' hcβ hcβ' hpair hA hB hC hA' hB' hC' x y

end

section

variable {k G : Type} [Field k] [Group G] (χ : G →* k)




/-- Exact original-object consumer of `characterDualTrivialLine_pairing`. -/
theorem actual_split_duality_characterDualTrivialLine_pairing_source (x : k)
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ) :
    characterDualEvaluation (coefficientCharacterRep (1 : G →* k)) χ x ℓ =
      x * characterDualTrivialLineEquiv χ ℓ :=
  characterDualTrivialLine_pairing χ x ℓ

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))

attribute [local instance] galoisRootZModModule


/-- Exact original-object consumer of `scalarCharacterDualRootCoefficient_pairing`. -/
theorem actual_split_duality_scalarCharacterDualRootCoefficient_pairing_source (x : ZMod q)
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ) :
    e (characterDualEvaluation (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ x ℓ) =
      galoisRootExponentPairing q (scalarCharacterDualRootCoefficientEquiv K Ω q χ e ℓ) x :=
  scalarCharacterDualRootCoefficient_pairing K Ω q χ e x ℓ

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]

attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `scalarCharacterDualH1Cup_kummer`. -/
theorem actual_split_duality_scalarCharacterDualH1Cup_kummer_source
    (x : ContinuousRepresentationH1 (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q))
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const))
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) hχ)) :
    scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ
      (continuousCharacterDualH1Cup (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) x y) =
      continuousH1Cup (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q)))
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
        (galoisRootExponentPairing q).flip
        (fun g a b => galoisRootExponentPairing_equivariant q g b a)
        continuous_of_discreteTopology continuous_snd (discreteGaloisRootAction_continuous q)
        (discreteGaloisRootAction_continuous q)
        (scalarTrivialLineH1IntegerEquiv K Ω q x)
        (scalarCharacterDualH1RootEquiv K Ω q χ hχ e heρ y) :=
  scalarCharacterDualH1Cup_kummer K Ω q χ hχ e heρ x y

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]

attribute [local instance] characterDualSequenceContinuousSMul
include e heρ

/-- Exact original-object consumer of `localScalarCharacterDualH1Cup_left_injective`. -/
theorem actual_split_duality_localScalarCharacterDualH1Cup_left_injective_source :
    Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const)) :=
  localScalarCharacterDualH1Cup_left_injective K Ω q χ hχ e heρ

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul
include e heρ htrivial

/-- Exact original-object consumer of `localTrivialCharacterDualH1Cup_left_injective`. -/
theorem actual_split_duality_localTrivialCharacterDualH1Cup_left_injective_source :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA) :=
  localTrivialCharacterDualH1Cup_left_injective K Ω q χ hχ e heρ A htrivial hA

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]

attribute [local instance] characterDualSequenceContinuousSMul
include e heρ

/-- Exact original-object consumer of `localScalarCharacterDualH1Cup_right_injective`. -/
theorem actual_split_duality_localScalarCharacterDualH1Cup_right_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const)).flip :=
  localScalarCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ hq

end

section

variable {k G ι : Type} [Field k] [Group G] [Finite ι]
  (A : Rep.{0} k G) (χ : G →* k) (b : Module.Basis ι k A)
  (htrivial : ∀ g a, A.ρ g a = a)

variable [DecidableEq ι]




/-- Exact original-object consumer of `characterDualBasisCoordinate_evaluation`. -/
theorem actual_split_duality_characterDualBasisCoordinate_evaluation_source (i : ι) (ℓ : characterDualCoefficientRep A χ) :
    characterDualTrivialLineEquiv χ
      (characterDualCoefficientMap (coefficientCharacterRep (1 : G →* k)) A χ
        (LinearMap.toSpanSingleton k A (b i)) ℓ) = b.dualBasis.coord i ℓ :=
  characterDualBasisCoordinate_evaluation A χ b i ℓ

end

section

variable {k G ι : Type} [Field k] [Finite k] [Group G] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualBasisCoordinate_evaluation`. -/
theorem actual_split_duality_continuousCharacterDualBasisCoordinate_evaluation_source (i : ι)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousCoefficientH1Map (characterDualCoefficientRep A χ) (coefficientCharacterRep χ)
      (b.dualBasis.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant (characterDualCoefficientRep A χ) χ b.dualBasis
        (trivialCoefficient_characterDual_scalar A χ htrivial) i)
      (finiteCharacterDualAction_continuous A χ hA hχ) (coefficientCharacterAction_continuous χ hχ) y =
    continuousCoefficientH1Map (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)
      (coefficientCharacterRep χ) (characterDualTrivialLineEquiv χ).toLinearMap
      continuous_of_discreteTopology (characterDualTrivialLineEquiv_equivariant χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : G →* k)) χ
        (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) hχ)
      (coefficientCharacterAction_continuous χ hχ)
      (continuousCoefficientH1Map (characterDualCoefficientRep A χ)
        (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)
        (characterDualCoefficientMap (coefficientCharacterRep (1 : G →* k)) A χ
          (LinearMap.toSpanSingleton k A (b i))) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant (coefficientCharacterRep (1 : G →* k)) A χ
          (LinearMap.toSpanSingleton k A (b i)) (trivialCoefficientBasisVector_equivariant A b htrivial i))
        (finiteCharacterDualAction_continuous A χ hA hχ)
        (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : G →* k)) χ
          (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) hχ) y) :=
  continuousCharacterDualBasisCoordinate_evaluation A χ hχ b htrivial hA i y

end

section

variable {k G ι : Type} [Field k] [Finite k] [Group G] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH1Cup_right_zero`. -/
theorem actual_split_duality_continuousTrivialCharacterDualH1Cup_right_zero_source
    (hbase : Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : G →* k)) χ hχ
      (coefficientCharacterAction_continuous (1 : G →* k) continuous_const)).flip)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup A χ hχ hA x y = 0) : y = 0 :=
  continuousTrivialCharacterDualH1Cup_right_zero A χ hχ b htrivial hA hbase y hy

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul
include e heρ htrivial

/-- Exact original-object consumer of `localTrivialCharacterDualH1Cup_right_injective`. -/
theorem actual_split_duality_localTrivialCharacterDualH1Cup_right_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA).flip :=
  localTrivialCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ A htrivial hA hq

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `localCharacterDualH1ScalarCup_eq_zero_iff`. -/
theorem actual_split_duality_localCharacterDualH1ScalarCup_eq_zero_iff_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA x y = 0 ↔
      continuousCharacterDualH1Cup A χ hχ hA x y = 0 :=
  localCharacterDualH1ScalarCup_eq_zero_iff K Ω q χ hχ e heρ A hA x y

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul
include htrivial

/-- Exact original-object consumer of `localTrivialCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_split_duality_localTrivialCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localTrivialCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ A htrivial hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))

attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeTrivialCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_split_duality_rationalPrimeTrivialCharacterDualH1ScalarCup_isPerfPair_source
    (htrivial : ∀ g a, A.ρ g a = a) :
    (rationalPrimeCharacterDualH1ScalarCup p hp q A hA).IsPerfPair :=
  rationalPrimeTrivialCharacterDualH1ScalarCup_isPerfPair p hp q A hA htrivial

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite


/-- Exact original-object consumer of `continuousCoinducedCharacterDualH1Equiv_cup`. -/
theorem actual_induced_perfect_continuousCoinducedCharacterDualH1Equiv_cup_source
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (y : ContinuousRepresentationH1
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS y) =
    continuousH1Cup (Rep.coind S.subtype (Rep.res S.subtype A))
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (coefficientCharacterRep χ) (coinducedCharacterPairing A S χ)
      (coinducedCharacterPairing_equivariant A S χ) continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) x y :=
  continuousCoinducedCharacterDualH1Equiv_cup A S χ hχ hA hS x y

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
attribute [local instance] coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous

/-- Exact original-object consumer of `continuousCoinducedCharacterDualShapiro_cup`. -/
theorem actual_induced_perfect_continuousCoinducedCharacterDualShapiro_cup_source
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
        S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedShapiroH1 A hA S hS x)
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH1 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS y)) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
        (restrictedCoefficientRep (coefficientCharacterRep χ) S.subtype)
        (characterDualEvaluation A χ) (fun g a ℓ => characterDualEvaluation_equivariant A χ g a ℓ)
        continuous_of_discreteTopology
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
          S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))
        (restrictedCoefficientAction_continuous (coefficientCharacterRep χ)
          S.subtype continuous_subtype_val (coefficientCharacterAction_continuous χ hχ)) x y) :=
  continuousCoinducedCharacterDualShapiro_cup A S χ hχ hA hS x y

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousInducedCharacterDualH1Cup_right_zero`. -/
theorem actual_induced_perfect_continuousInducedCharacterDualH1Cup_right_zero_source
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
      (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
        (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x y = 0) : y = 0 :=
  continuousInducedCharacterDualH1Cup_right_zero A S χ hχ hA hS hcor hsub y hy

end

section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  (A : Rep.{0} R G) (B : Rep.{0} S G)
  (e : A ≃+ B)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

  (U : Subgroup G) [Fintype (G ⧸ U)]



variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (he : Continuous e) (hei : Continuous e.symm)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) (hU : IsOpen (U : Set G))






/-- Exact original-object consumer of `continuousH2AdditiveCoefficientEquiv_corestriction`. -/
theorem actual_induced_perfect_continuousH2AdditiveCoefficientEquiv_corestriction_source
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A U.subtype)
      (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)) :
    continuousH2AdditiveCoefficientEquiv A B e he hei heρ hA hB
      (continuousRepresentationH2Corestriction A hA U hU x) =
    continuousRepresentationH2Corestriction B hB U hU
      (continuousH2AdditiveCoefficientEquiv (restrictedCoefficientRep A U.subtype)
        (restrictedCoefficientRep B U.subtype) e he hei (fun g a => heρ g a)
        (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous B U.subtype continuous_subtype_val hB) x) :=
  continuousH2AdditiveCoefficientEquiv_corestriction A B e heρ U he hei hA hB hU x

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]




variable (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))



attribute [local instance] characterDualSequenceContinuousSMul
  rootLocalCorestrictionIsGalois rootLocalCorestrictionStageTopology
  rootLocalCorestrictionStageDiscrete rootLocalCorestrictionUnitTopology rootLocalCorestrictionUnitDiscrete
attribute [local instance] localCharacterLineCorestrictionCosets
include e heρ dUnits

/-- Exact original-object consumer of `localCharacterLineFixingCorestriction_injective`. -/
theorem actual_induced_perfect_localCharacterLineFixingCorestriction_injective_source :
    Function.Injective (continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) E.fixingSubgroup E.fixingSubgroup_isOpen) :=
  localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ

end

section

variable {k G H : Type} [Field k] [Group G] [Group H]



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)



attribute [local instance] characterDualSequenceContinuousSMul
include hji

/-- Exact original-object consumer of `continuousCharacterDualH1Cup_right_injective_of_groupEquiv`. -/
theorem actual_induced_perfect_continuousCharacterDualH1Cup_right_injective_of_groupEquiv_source
    (h : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA).flip :=
  continuousCharacterDualH1Cup_right_injective_of_groupEquiv A χ hχ hA j hj hji h

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  (E : IntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)



attribute [local instance] characterDualSequenceContinuousSMul
  fixingRootStageTopology fixingRootStageDiscrete fixingRootUnitTopology fixingRootUnitDiscrete
include e heρ hE

/-- Exact original-object consumer of `localFixingCharacterDualH1Cup_right_injective`. -/
theorem actual_induced_perfect_localFixingCharacterDualH1Cup_right_injective_source (hq : (q : E) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)).flip :=
  localFixingCharacterDualH1Cup_right_injective K Ω E q χ hχ e heρ A hA hE hq

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


  (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [DiscreteTopology (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [TopologicalSpace (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous
include hE

/-- Exact original-object consumer of `localInducedCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_induced_perfect_localInducedCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair :=
  localInducedCharacterDualH1ScalarCup_isPerfPair K Ω E q χ hχ e heρ A hA hE hq

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localField_exists_perfect_coinduced_embedding`. -/
theorem actual_induced_perfect_localField_exists_perfect_coinduced_embedding_source (hq : (q : K) ≠ 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), g ∈ F.toIntermediateField.fixingSubgroup → ∀ a : A, A.ρ g a = a) ∧
      let B := Rep.coind F.toIntermediateField.fixingSubgroup.subtype
        (Rep.res F.toIntermediateField.fixingSubgroup.subtype A)
      letI : TopologicalSpace B := ⊥
      letI : DiscreteTopology B := ⟨rfl⟩
      letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
      letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
      Finite B ∧ Function.Injective (finiteCoinducedCoefficientUnit A F.toIntermediateField.fixingSubgroup) ∧
        (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B
          (finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair :=
  localField_exists_perfect_coinduced_embedding K Ω q χ hχ e heρ A hA hq

end

section

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  (χ : G →* k) (b : Module.Basis ι k A) (hscalar : ∀ g a, A.ρ g a = χ g • a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ)






/-- Exact original-object consumer of `continuousScalarH2_eq_zero_of_coordinates`. -/
theorem actual_split_endpoint_continuousScalarH2_eq_zero_of_coordinates_source (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ i, continuousCoefficientH2Map A (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology (scalarCoefficientCoordinate_equivariant A χ b hscalar i)
      hA (coefficientCharacterAction_continuous χ hχ) x = 0) : x = 0 :=
  continuousScalarH2_eq_zero_of_coordinates A χ b hscalar hA hχ x hx

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_apply`. -/
theorem actual_split_endpoint_continuousCharacterDualH2InvariantPairing_apply_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w x :=
  continuousCharacterDualH2InvariantPairing_apply A χ hχ hA x w

end

section

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)



attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH2InvariantPairing_left_injective`. -/
theorem actual_split_endpoint_continuousTrivialCharacterDualH2InvariantPairing_left_injective_source :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA) :=
  continuousTrivialCharacterDualH2InvariantPairing_left_injective A χ hχ hA b htrivial

end

section

variable {k G ι : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)




attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH2InvariantPairing_right_injective`. -/
theorem actual_split_endpoint_continuousTrivialCharacterDualH2InvariantPairing_right_injective_source
    (c : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ))
    (hc : c ≠ 0) : Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip :=
  continuousTrivialCharacterDualH2InvariantPairing_right_injective A χ hχ hA b htrivial c hc

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



variable (htrivial : ∀ g a, A.ρ g a = a)



attribute [local instance] characterDualSequenceContinuousSMul
include htrivial

/-- Exact original-object consumer of `localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_split_endpoint_localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair_source :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair K Ω q χ hχ e heρ A hA htrivial

end

section

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)






/-- Exact original-object consumer of `coinducedShapiroZero_invariant`. -/
theorem actual_finite_duality_coinducedShapiroZero_invariant_source
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    coinducedShapiroZero A S w.val = (coinducedInvariantEquiv A S w).val :=
  coinducedShapiroZero_invariant A S w

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k)






/-- Exact original-object consumer of `coinducedShapiroTwoZero_pairing`. -/
theorem actual_finite_duality_coinducedShapiroTwoZero_pairing_source (c : S × S → characterDualCoefficientRep A χ)
    (w : A) (g h : G) :
    coinducedCharacterPairing A S χ (coinducedShapiroZero A S w)
      (coinducedShapiroTwo (characterDualCoefficientRep A χ) S c (g, h)) =
      cosetTraceTwo (coefficientCharacterRep χ) S
        (fun z => characterDualEvaluation A χ w (c z)) (g, h) :=
  coinducedShapiroTwoZero_pairing A S χ c w g h

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite


/-- Exact original-object consumer of `continuousCoinducedCharacterDualH2Equiv_pairing`. -/
theorem actual_finite_duality_continuousCoinducedCharacterDualH2Equiv_pairing_source
    (y : ContinuousRepresentationH2
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS))
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS y) w =
    continuousInvariantRightH2Map
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (Rep.coind S.subtype (Rep.res S.subtype A)) (coefficientCharacterRep χ)
      (coinducedCharacterPairing A S χ).flip
      (fun g ℓ a => coinducedCharacterPairing_equivariant A S χ g a ℓ)
      continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) w y :=
  continuousCoinducedCharacterDualH2Equiv_pairing A S χ hχ hA hS y w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousCoinducedShapiroH2Invariant_pairing`. -/
theorem actual_finite_duality_continuousCoinducedShapiroH2Invariant_pairing_source
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ) S.subtype
        continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ)))
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH2 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS x))
      (coinducedInvariantEquiv A S w) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
        (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x w) :=
  continuousCoinducedShapiroH2Invariant_pairing A S χ hχ hA hS x w

end

section

variable {k G H : Type} [Field k] [Group G] [Group H]



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)




attribute [local instance] characterDualSequenceContinuousSMul
include hji

/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv`. -/
theorem actual_finite_duality_continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv_source
    (h : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip :=
  continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv A χ hχ hA j hj hji h

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  (E : IntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)



attribute [local instance] characterDualSequenceContinuousSMul
  fixingRootStageTopology fixingRootStageDiscrete fixingRootUnitTopology fixingRootUnitDiscrete
include e heρ hE

/-- Exact original-object consumer of `localFixingCharacterDualH2InvariantPairing_right_injective`. -/
theorem actual_finite_duality_localFixingCharacterDualH2InvariantPairing_right_injective_source :
    Function.Injective (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)).flip :=
  localFixingCharacterDualH2InvariantPairing_right_injective K Ω E q χ hχ e heρ A hA hE

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousInducedCharacterDualH2InvariantPairing_right_zero`. -/
theorem actual_finite_duality_continuousInducedCharacterDualH2InvariantPairing_right_zero_source
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants)
    (hw : ∀ x, continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x w = 0) : w = 0 :=
  continuousInducedCharacterDualH2InvariantPairing_right_zero A S χ hχ hA hS hcor hsub w hw

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


  (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [DiscreteTopology (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [TopologicalSpace (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous
include hE

/-- Exact original-object consumer of `localInducedCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_finite_duality_localInducedCharacterDualH2InvariantScalarPairing_isPerfPair_source :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair :=
  localInducedCharacterDualH2InvariantScalarPairing_isPerfPair K Ω E q χ hχ e heρ A hA hE

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localField_exists_perfect_coinduced_endpoints`. -/
theorem actual_finite_duality_localField_exists_perfect_coinduced_endpoints_source (hq : (q : K) ≠ 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), g ∈ F.toIntermediateField.fixingSubgroup → ∀ a : A, A.ρ g a = a) ∧
      let B := Rep.coind F.toIntermediateField.fixingSubgroup.subtype
        (Rep.res F.toIntermediateField.fixingSubgroup.subtype A)
      letI : TopologicalSpace B := ⊥
      letI : DiscreteTopology B := ⟨rfl⟩
      letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
      letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
      Finite B ∧ Function.Injective (finiteCoinducedCoefficientUnit A F.toIntermediateField.fixingSubgroup) ∧
        (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B
          (finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair ∧
        (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B
          (finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair :=
  localField_exists_perfect_coinduced_endpoints K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G]
  (A B : Rep.{0} k G) (φ : A →ₗ[k] B)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_naturality`. -/
theorem actual_finite_duality_continuousCharacterDualH2InvariantPairing_naturality_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep B χ)
      (finiteCharacterDualAction_continuous B χ hB hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA
      (continuousCoefficientH2Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) x) w =
      continuousCharacterDualH2InvariantPairing B χ hχ hB x
        (coefficientInvariantLinearMap A B φ hφρ w) :=
  continuousCharacterDualH2InvariantPairing_naturality A B φ hφρ χ hχ hA hB x w

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localCharacterDualH2InvariantScalarPairing_surjective`. -/
theorem actual_finite_duality_localCharacterDualH2InvariantScalarPairing_surjective_source (hq : (q : K) ≠ 0) :
    Function.Surjective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA) :=
  localCharacterDualH2InvariantScalarPairing_surjective K Ω q χ hχ e heρ A hA hq

end

section

variable {k A₁ AD₁ B₁ BD₁ B₀ C₀ CD₂ BD₂ : Type} [Field k]
  [AddCommGroup A₁] [Module k A₁] [AddCommGroup AD₁] [Module k AD₁]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup B₀] [Module k B₀] [AddCommGroup C₀] [Module k C₀]
  [AddCommGroup CD₂] [Module k CD₂] [AddCommGroup BD₂] [Module k BD₂]
  (P : A₁ →ₗ[k] AD₁ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : CD₂ →ₗ[k] C₀ →ₗ[k] k) (T : BD₂ →ₗ[k] B₀ →ₗ[k] k)
  (i : A₁ →ₗ[k] B₁) (iD : BD₁ →ₗ[k] AD₁)
  (δ : C₀ →ₗ[k] A₁) (j : B₀ →ₗ[k] C₀)
  (δD : AD₁ →ₗ[k] CD₂) (jD : CD₂ →ₗ[k] BD₂)
  (hex₁ : LinearMap.range δ = LinearMap.ker i)
  (hex₀ : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ x y, Q (i x) y = P x (iD y))
  (hend : ∀ z b, T (jD z) b = R z (j b))
  (hadj : ∀ y w, R (δD y) w = -P (δ w) y)
  (hQ : Function.Injective Q) (hT : Function.Injective T)
  (hR : Function.Surjective R)




include hex₁ hex₀ hexD hnat hend hadj hQ hT hR

/-- Exact original-object consumer of `lowDegreeDuality_left_injective`. -/
theorem actual_finite_duality_lowDegreeDuality_left_injective_source : Function.Injective P :=
  lowDegreeDuality_left_injective P Q R T i iD δ j δD jD hex₁ hex₀ hexD hnat hend hadj hQ hT hR

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]



variable (A B C : Rep.{0} k G)
  [Finite A] [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteCharacterDualInvariantConnecting_adjunction`. -/
theorem actual_finite_duality_finiteCharacterDualInvariantConnecting_adjunction_source
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : C.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing C χ hχ hC
      (continuousCoefficientConnectingMap
        (characterDualCoefficientRep C χ) (characterDualCoefficientRep B χ)
        (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap B C χ ψ)
        (characterDualCoefficientMap_injective B C χ ψ hψ)
        (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
        (characterDualCoefficientMap A B χ φ)
        (characterDualCoefficientMap_surjective A B χ φ hφ)
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (characterDualCoefficientSequence_exact A B C χ φ ψ hExact)
        (finiteCharacterDualAction_continuous C χ hC hχ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) y) w =
      -continuousCharacterDualH1Cup A χ hχ hA
        (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB w) y :=
  finiteCharacterDualInvariantConnecting_adjunction A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC y w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]



variable (A B C : Rep.{0} k G)
  [Finite A] [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))



variable (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
  (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



attribute [local instance] characterDualSequenceContinuousSMul
include hφ hψ hφρ hψρ hExact

/-- Exact original-object consumer of `continuousCharacterDualH1_left_injective_of_exact`. -/
theorem actual_finite_duality_continuousCharacterDualH1_left_injective_of_exact_source
    (h₁ : Function.Injective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₂ : Function.Injective ((continuousCharacterDualH2InvariantPairing B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₃ : Function.Surjective ((continuousCharacterDualH2InvariantPairing C χ hχ hC).compr₂ e₂.toLinearMap)) :
    Function.Injective ((continuousCharacterDualH1Cup A χ hχ hA).compr₂ e₂.toLinearMap) :=
  continuousCharacterDualH1_left_injective_of_exact A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC e₂ h₁ h₂ h₃

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets finiteCoinducedCoefficientQuotient_finite


/-- Exact original-object consumer of `localCharacterDualH1ScalarCup_left_injective`. -/
theorem actual_finite_duality_localCharacterDualH1ScalarCup_left_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA) :=
  localCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) [Finite A]
  (χ : G →* k)



variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  (hχ : Continuous χ)
  [Finite (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH1Cup_bidual`. -/
theorem actual_finite_duality_continuousCharacterDualH1Cup_bidual_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousCharacterDualH1Cup (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) y (continuousCharacterBidualH1Equiv A χ hχ hA x) =
      -continuousCharacterDualH1Cup A χ hχ hA x y :=
  continuousCharacterDualH1Cup_bidual A χ hχ hA x y

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets finiteCoinducedCoefficientQuotient_finite


/-- Exact original-object consumer of `localCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_finite_duality_localCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_finite_duality_rationalPrimeCharacterDualH1ScalarCup_isPerfPair_source :
    (rationalPrimeCharacterDualH1ScalarCup p hp q A hA).IsPerfPair :=
  rationalPrimeCharacterDualH1ScalarCup_isPerfPair p hp q A hA

end

open Matrix

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  (A : Rep.{0} k G) (χ : G →* ZMod q)



variable [Finite A]



attribute [local instance] finiteScalarPrimeModule


/-- Exact original-object consumer of `finiteScalarTraceDualMap_surjective`. -/
theorem actual_extension_field_finiteScalarTraceDualMap_surjective_source : Function.Surjective (finiteScalarTraceDualMap q A χ) :=
  finiteScalarTraceDualMap_surjective q A χ

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



variable (χ : G →* ZMod q) (hχ : Continuous χ)



variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul
omit [Finite k] [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact original-object consumer of `finiteScalarTraceCharacter_equivariant`. -/
theorem actual_extension_field_finiteScalarTraceCharacter_equivariant_source (g : G) (a : k) :
    Algebra.trace (ZMod q) k
      ((finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))).ρ g a) =
      (coefficientCharacterRep χ).ρ g (Algebra.trace (ZMod q) k a) :=
  finiteScalarTraceCharacter_equivariant q χ g a

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



variable (χ : G →* ZMod q) (hχ : Continuous χ)



variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarTraceCharacterH2Map_cup`. -/
theorem actual_extension_field_finiteScalarTraceCharacterH2Map_cup_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x y) =
      continuousCharacterDualH1Cup (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarPrimeH1Equiv q A hA x) (finiteScalarTraceDualH1Equiv q A hA χ hχ y) :=
  finiteScalarTraceCharacterH2Map_cup q A hA χ hχ x y

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]



variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule
include e heρ

/-- Exact original-object consumer of `localFiniteScalarCharacterDualH1Cup_right_injective`. -/
theorem actual_extension_field_localFiniteScalarCharacterDualH1Cup_right_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
      (finiteScalarCharacter_continuous q χ hχ) hA).flip :=
  localFiniteScalarCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)



variable {ι : Type}
  (b : @Module.Basis ι (ZMod q) k _ _ (finiteScalarCharacterPrimeRep q χ (k := k)).hV2)



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul
attribute [local instance 1100] Rep.hV2
attribute [local instance 1100] finiteScalarLinePrimeModule


/-- Exact original-object consumer of `finiteScalarCharacterH2Extend_coordinate`. -/
theorem actual_extension_field_finiteScalarCharacterH2Extend_coordinate_source (i : ι) (a : k)
    (u : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ)) :
    continuousCoefficientH2Map
      (finiteScalarCharacterPrimeRep q χ (k := k))
      (coefficientCharacterRep χ) (b.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant
        (finiteScalarCharacterPrimeRep q χ (k := k)) χ b (finiteScalarCharacterPrime_action q χ) i)
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ))
      (coefficientCharacterAction_continuous χ hχ)
      (finiteScalarCharacterPrimeH2Equiv q χ hχ (a • finiteScalarCharacterH2Extend q χ hχ u)) =
      b.coord i a • u :=
  finiteScalarCharacterH2Extend_coordinate q χ hχ b i a u

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)



variable [Finite k]



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarCharacterH2Span_bijective`. -/
theorem actual_extension_field_finiteScalarCharacterH2Span_bijective_source :
    Function.Bijective (finiteScalarCharacterH2Span q χ hχ σ (k := k)) :=
  finiteScalarCharacterH2Span_bijective q χ hχ σ

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)


variable [Finite k]
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarCharacterH2ScalarEquiv_trace`. -/
theorem actual_extension_field_finiteScalarCharacterH2ScalarEquiv_trace_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ))) :
    σ (finiteScalarTraceCharacterH2Map q χ hχ (k := k) x) =
      Algebra.trace (ZMod q) k (finiteScalarCharacterH2ScalarEquiv q χ hχ σ x) :=
  finiteScalarCharacterH2ScalarEquiv_trace q χ hχ σ x

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]



variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule


/-- Exact original-object consumer of `localFiniteScalarCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_extension_field_localFiniteScalarCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localFiniteScalarCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (k : Type) [Field k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k]



variable [Finite k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]






/-- Exact original-object consumer of `rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff_source
    (x : ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) :
    rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k x = 0 ↔ x = 0 :=
  rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff p hp q k x

end

section

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (hn : (Fintype.card ι : k) ≠ 0)
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_dual`. -/
theorem actual_extension_field_matrixTraceZeroCharacterH1Cup_dual_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y =
      -continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (continuousTraceZeroH1GeneralEquiv ρ hρ y)
        (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x) :=
  matrixTraceZeroCharacterH1Cup_dual hn ρ hρ χ hχ x y

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {k : Type} [Field k] [Finite k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} k Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair_source :
    (rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA).IsPerfPair :=
  rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair p hp q A hA

end

section

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



variable (hn : (Fintype.card ι : k) ≠ 0)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]



variable [Module.Finite k (ContinuousTraceZeroAdjointH1 ρ hρ)]



attribute [local instance] characterDualSequenceContinuousSMul
include hn

/-- Exact original-object consumer of `matrixTraceZeroNormalizedH1Cup_isPerfPair`. -/
theorem actual_extension_field_matrixTraceZeroNormalizedH1Cup_isPerfPair_source
    (hdual : ((continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
      (matrixTraceZeroAdjointAction_continuous ρ hρ)).compr₂ σ.toLinearMap).IsPerfPair) :
    (matrixTraceZeroNormalizedH1Cup ρ hρ χ hχ σ).IsPerfPair :=
  matrixTraceZeroNormalizedH1Cup_isPerfPair ρ hρ χ hχ σ hn hdual

end

section

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι k) (hρ : Continuous ρ)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `rationalPrimeFiniteScalarTraceH1Cup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarTraceH1Cup_isPerfPair_source
    (hn : (Fintype.card ι : k) ≠ 0) :
    (rationalPrimeFiniteScalarTraceH1Cup p hp q ρ hρ).IsPerfPair :=
  rationalPrimeFiniteScalarTraceH1Cup_isPerfPair p hp q ρ hρ hn

end

section

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
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `rationalPrimeTraceH1ScalarCup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeTraceH1ScalarCup_isPerfPair_source
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalPrimeTraceH1ScalarCup p hp q ρ hρ).IsPerfPair :=
  rationalPrimeTraceH1ScalarCup_isPerfPair p hp q ρ hρ hn

end


section

variable {k A₂ AD₀ B₁ BD₁ C₁ CD₁ : Type} [Field k]
  [AddCommGroup A₂] [Module k A₂] [AddCommGroup AD₀] [Module k AD₀]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup C₁] [Module k C₁] [AddCommGroup CD₁] [Module k CD₁]
  (P : A₂ →ₗ[k] AD₀ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : C₁ →ₗ[k] CD₁ →ₗ[k] k)
  (j : B₁ →ₗ[k] C₁) (δ : C₁ →ₗ[k] A₂)
  (jD : CD₁ →ₗ[k] BD₁) (δD : AD₀ →ₗ[k] CD₁)
  (hex : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ b z, Q b (jD z) = R (j b) z)
  (hadj : ∀ u w, P (δ u) w = R u (δD w))
  (hQ : Function.Surjective Q) (hR : Function.Injective R)




include hex hexD hnat hadj hQ hR

/-- Exact original-object consumer of `lowDegreeH2_connecting_left_zero`. -/
theorem actual_local_h2_endpoint_lowDegreeH2_connecting_left_zero_source (u : C₁) (hu : ∀ w, P (δ u) w = 0) :
    δ u = 0 :=
  lowDegreeH2_connecting_left_zero P Q R j δ jD δD hex hexD hnat hadj hQ hR u hu

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterH2DualInvariantPairing_apply`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2DualInvariantPairing_apply_source
    (x : ContinuousRepresentationH2 A hA) (w : (characterDualCoefficientRep A χ).ρ.invariants) :
    continuousCharacterH2DualInvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w x :=
  continuousCharacterH2DualInvariantPairing_apply A χ hχ hA x w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep.{0} k G) [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



attribute [local instance] characterDualSequenceContinuousSMul
include hφ hψ hψρ hExact

/-- Exact original-object consumer of `continuousCharacterH2_left_zero_of_effacement`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2_left_zero_of_effacement_source
    (hQ : Function.Surjective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (hR : Function.Injective ((continuousCharacterDualH1Cup C χ hχ hC).compr₂ e₂.toLinearMap))
    (x : ContinuousRepresentationH2 A hA)
    (hx : continuousCoefficientH2Map A B φ continuous_of_discreteTopology hφρ hA hB x = 0)
    (hann : ∀ w, e₂ (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 :=
  continuousCharacterH2_left_zero_of_effacement A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC e₂ hQ hR x hx hann

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul
  finiteEffacementCoefficientTopology finiteEffacementCoefficientDiscrete finiteEffacementCosets


/-- Exact original-object consumer of `localCharacterH2DualInvariant_left_zero`. -/
theorem actual_local_h2_endpoint_localCharacterH2DualInvariant_left_zero_source (hq : (q : K) ≠ 0)
    (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ w, localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
      (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 :=
  localCharacterH2DualInvariant_left_zero K Ω q χ hχ e heρ A hA hq x hx

end

section

variable {k G : Type} [Field k] [Group G]
  (A : Rep.{0} k G) [Finite A] (χ : G →* k)



variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hχ : Continuous χ) (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterH2DualInvariantPairing_bidual`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2DualInvariantPairing_bidual_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterH2DualInvariantPairing (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) x (characterBidualInvariantEquiv A χ w) =
      continuousCharacterDualH2InvariantPairing A χ hχ hA x w :=
  continuousCharacterH2DualInvariantPairing_bidual A χ hχ hA x w

end

section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `localCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_localCharacterDualH2InvariantScalarPairing_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localCharacterDualH2InvariantScalarPairing_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (χ : G →* ZMod q) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarTraceCharacterH2Map_invariantPairing`. -/
theorem actual_local_h2_endpoint_finiteScalarTraceCharacterH2Map_invariantPairing_source
    (x : ContinuousRepresentationH2
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) (w : A.ρ.invariants) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH2InvariantPairing A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x w) =
      continuousCharacterDualH2InvariantPairing (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarTraceDualH2Equiv q A hA χ hχ x) (finiteScalarPrimeInvariantEquiv q A w) :=
  finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ x w

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule


/-- Exact original-object consumer of `localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {k : Type} [Field k] [Finite k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} k Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair_source :
    (rationalPrimeFiniteScalarCharacterDualH2Pairing p hp q A hA).IsPerfPair :=
  rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair p hp q A hA

end


noncomputable section
open Matrix
open scoped NumberField
section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {ζ : rationalPrimeLocalClosure p hp} (hζ : IsPrimitiveRoot ζ q)







/-- Exact original-object consumer of `rationalPrimePrimitiveRootCoefficientEquiv_equivariant`. -/
theorem actual_arithmetic_root_rationalPrimePrimitiveRootCoefficientEquiv_equivariant_source
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (x : ZMod q) :
    rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ
      ((coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).ρ g x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ x) :=
  rationalPrimePrimitiveRootCoefficientEquiv_equivariant p hp q hζ g x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)



variable (p : ℕ) (hp : p.Prime)







/-- Exact original-object consumer of `rationalArithmeticLocalRootCoefficientEquiv_compatible`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalRootCoefficientEquiv_compatible_source (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    (((Additive.toMul (Rep.toAdditive
      (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
        rootsOfUnity q (rationalPrimeLocalClosure p hp)) : (rationalPrimeLocalClosure p hp)ˣ) :
        rationalPrimeLocalClosure p hp) =
      rationalArithmeticLocalEmbedding a ((rationalArithmeticPrimitiveRoot a q hqa) ^ x.val) :=
  rationalArithmeticLocalRootCoefficientEquiv_compatible a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q



/-- Exact original-object consumer of `rationalArithmeticRootCoefficientEquiv_local`. -/
theorem actual_arithmetic_root_rationalArithmeticRootCoefficientEquiv_local_source
    (p : ℕ) (hp : p.Prime) (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding a
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticRootCoefficientEquiv a q hqa x)) : rootsOfUnity q U) : Uˣ) : U) =
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
          rootsOfUnity q (rationalPrimeLocalClosure p hp)) :
            (rationalPrimeLocalClosure p hp)ˣ) : rationalPrimeLocalClosure p hp) :=
  rationalArithmeticRootCoefficientEquiv_local a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q



/-- Exact original-object consumer of `rationalArithmeticRootLocalEquiv_equivariant`. -/
theorem actual_arithmetic_root_rationalArithmeticRootLocalEquiv_equivariant_source
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticRootLocalEquiv a q hqa p hp
      ((rationalArithmeticRootRepresentation a q).ρ
        (rationalPrimeArithmeticRestriction a p hp g) x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) :=
  rationalArithmeticRootLocalEquiv_equivariant a q hqa p hp g x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticGlobalRootContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootRepresentation a q).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩



/-- Exact original-object consumer of `rationalArithmeticRootH2Restriction_compatible`. -/
theorem actual_arithmetic_root_rationalArithmeticRootH2Restriction_compatible_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticRootH2Restriction a q hqa p hp
      (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) =
      rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp
        (rationalPrimeCyclotomicH2Restriction a q hqa p hp x) :=
  rationalArithmeticRootH2Restriction_compatible a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)



variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rationalUnramifiedExtension a)ˣ :=
  inferInstanceAs (MulDistribMulAction
    Gal(rationalUnramifiedExtension a / ℚ) (rationalUnramifiedExtension a)ˣ)



/-- Exact original-object consumer of `rationalArithmeticUnitLocalMap_kummer`. -/
theorem actual_arithmetic_root_rationalArithmeticUnitLocalMap_kummer_source
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticUnitLocalMap a p hp (rationalArithmeticKummerInclusion a q x) =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q).hom.toLinearMap
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) :=
  rationalArithmeticUnitLocalMap_kummer a p hp q hqa x

end

section

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]



attribute [local instance] arithmeticGlobalRootContinuousSMul

/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticGlobalUnitContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitRepresentation a).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩



/-- Exact original-object consumer of `rationalArithmeticUnitH2Restriction_kummer`. -/
theorem actual_arithmetic_root_rationalArithmeticUnitH2Restriction_kummer_source
    (x : ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q)) :
    rationalArithmeticUnitH2Restriction a p hp (rationalArithmeticKummerH2Inclusion a q x) =
      galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q
        (rationalArithmeticRootH2Restriction a q hqa p hp x) :=
  rationalArithmeticUnitH2Restriction_kummer a p hp q hqa x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `rationalArithmeticLocalH2ScalarEquiv_global_invariant`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH2ScalarEquiv_global_invariant_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp x)) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x))) :=
  rationalArithmeticLocalH2ScalarEquiv_global_invariant a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]







/-- Exact original-object consumer of `rationalArithmeticLocalH2ScalarEquiv_comparison`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH2ScalarEquiv_comparison_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)) :
    rationalArithmeticLocalH2ScalarEquiv a q hqa p hp x =
      rationalArithmeticLocalNormalizationScalar a q hqa p hp *
        rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x :=
  rationalArithmeticLocalH2ScalarEquiv_comparison a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `rationalArithmeticLocalH1ScalarCup_isPerfPair`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH1ScalarCup_isPerfPair_source :
    (rationalArithmeticLocalH1ScalarCup a q hqa p hp A hA).IsPerfPair :=
  rationalArithmeticLocalH1ScalarCup_isPerfPair a q hqa p hp A hA

end

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul



/-- Exact original-object consumer of `rationalArithmeticCoherentTraceCup_global_invariant`. -/
theorem actual_arithmetic_root_rationalArithmeticCoherentTraceCup_global_invariant_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y))) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa
              (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)))) :=
  rationalArithmeticCoherentTraceCup_global_invariant a q hqa σ hσ p hp x y

end


end

end Dubon2026.SemanticRegression
