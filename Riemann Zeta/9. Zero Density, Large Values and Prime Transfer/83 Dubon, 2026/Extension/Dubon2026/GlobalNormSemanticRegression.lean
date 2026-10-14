import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




noncomputable section
open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section



variable (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(ℂ/ℝ))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(ℂ/ℝ) × A => A.ρ z.1 z.2))





/-- Exact original-object consumer of `realPlaceFiniteCoefficientH2_eq_zero`. -/
theorem actual_global_norm_input_realPlaceFiniteCoefficientH2_eq_zero_source (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) : x = 0 :=
  realPlaceFiniteCoefficientH2_eq_zero q A hA hq x

end

section



variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) (rationalArithmeticGaloisGroup a))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))





/-- Exact original-object consumer of `rationalRealArithmeticH2Restriction_eq_zero`. -/
theorem actual_global_norm_input_rationalRealArithmeticH2Restriction_eq_zero_source (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (rationalRealArithmeticRestriction a).toMonoidHom
      (rationalRealArithmeticRestriction a).continuous x = 0 :=
  rationalRealArithmeticH2Restriction_eq_zero a q A hA hq x

end

section


attribute [local instance] Dubon2026.arithmeticPrimeInvariantRootTopology Dubon2026.arithmeticPrimeInvariantRootDiscrete Dubon2026.arithmeticPrimeInvariantUnitTopology Dubon2026.arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- Exact original-object consumer of `rationalArithmeticPrimeH2Invariant_finite_support`. -/
theorem actual_global_norm_input_rationalArithmeticPrimeH2Invariant_finite_support_source (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    (Function.support (fun p : Nat.Primes => rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x)).Finite :=
  rationalArithmeticPrimeH2Invariant_finite_support a q hqa ha x

end

section



variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)





/-- Exact original-object consumer of `rationalArithmeticFiniteH2InvariantSum_apply`. -/
theorem actual_global_norm_input_rationalArithmeticFiniteH2InvariantSum_apply_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha x =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x :=
  rationalArithmeticFiniteH2InvariantSum_apply a q hqa ha x

end

section

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticPrimeInvariantRootTopology arithmeticPrimeInvariantRootDiscrete
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]





/-- Exact original-object consumer of `rationalArithmeticFiniteH2InvariantSum_unit_invariants`. -/
theorem actual_global_norm_input_rationalArithmeticFiniteH2InvariantSum_unit_invariants_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x :=
  rationalArithmeticFiniteH2InvariantSum_unit_invariants a q hqa ha x

end

section







/-- Exact original-object consumer of `numberField_prime_classNumber_power_principal`. -/
theorem actual_global_norm_input_numberField_prime_classNumber_power_principal_source
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal ^ NumberField.classNumber K).IsPrincipal :=
  numberField_prime_classNumber_power_principal K v

end

section







/-- Exact original-object consumer of `numberFieldPrimePowerGenerator_intValuation`. -/
theorem actual_global_norm_input_numberFieldPrimePowerGenerator_intValuation_source
    (K : Type*) [Field K] [NumberField K] (v w : HeightOneSpectrum (𝓞 K)) :
    w.intValuation (numberFieldPrimePowerGenerator K v) =
      WithZero.exp (if w = v then -(NumberField.classNumber K : ℤ) else 0) :=
  numberFieldPrimePowerGenerator_intValuation K v w

end

section







/-- Exact original-object consumer of `numberFieldPrimePowerSUnit_coordinate`. -/
theorem actual_global_norm_input_numberFieldPrimePowerSUnit_coordinate_source (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v w : S) :
    sUnitValuationLinearMap S (Additive.ofMul (numberFieldPrimePowerSUnit K S v)) w =
      if w = v then -(NumberField.classNumber K : ℤ) else 0 :=
  numberFieldPrimePowerSUnit_coordinate K S v w

end

section







/-- Exact original-object consumer of `numberField_unit_finrank`. -/
theorem actual_global_norm_input_numberField_unit_finrank_source (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (Additive (𝓞 K)ˣ) = NumberField.Units.rank K :=
  numberField_unit_finrank K

end

section



variable (K : Type*) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))





/-- Exact original-object consumer of `numberField_sUnit_finrank`. -/
theorem actual_global_norm_input_numberField_sUnit_finrank_source (hS : S.Finite) :
    Module.finrank ℤ (Additive (S.unit K)) = NumberField.Units.rank K + S.ncard :=
  numberField_sUnit_finrank K S hS

end

section







/-- Exact original-object consumer of `finiteGeneratedAbelian_exists_rank_decomposition`. -/
theorem actual_global_norm_input_finiteGeneratedAbelian_exists_rank_decomposition_source
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (d : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (G ≃+ (Fin d → ℤ) × T) ∧ Module.finrank ℤ G = d :=
  finiteGeneratedAbelian_exists_rank_decomposition G

end

section







/-- Exact original-object consumer of `finiteGeneratedAbelian_nsmul_index`. -/
theorem actual_global_norm_input_finiteGeneratedAbelian_nsmul_index_source
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ Module.finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker :=
  finiteGeneratedAbelian_nsmul_index G n hn

end

section



variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]





/-- Exact original-object consumer of `sUnitPowerKernel_card`. -/
theorem actual_global_norm_input_sUnitPowerKernel_card_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (powMonoidHom (α := S.unit K) n).ker = n :=
  sUnitPowerKernel_card S n hn ζ hζ

end

section







/-- Exact original-object consumer of `numberField_sUnit_powerQuotient_card`. -/
theorem actual_global_norm_input_numberField_sUnit_powerQuotient_card_source
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_powerQuotient_card K S hS n hn ζ hζ

end


open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnit_mem_power_range_iff`. -/
theorem actual_sunit_kummer_sUnit_mem_power_range_iff_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (x : S.unit K) :
    x ∈ (powMonoidHom (α := S.unit K) n).range ↔
      x.val ∈ (powMonoidHom (α := Kˣ) n).range :=
  sUnit_mem_power_range_iff S n hn x

end

section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnitPowerQuotientToField_injective`. -/
theorem actual_sunit_kummer_sUnitPowerQuotientToField_injective_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) : Function.Injective (sUnitPowerQuotientToField (K := K) S n) :=
  sUnitPowerQuotientToField_injective S n hn

end

section



/-- Exact original-object consumer of `numberField_sUnit_radicalQuotient_card`. -/
theorem actual_sunit_kummer_numberField_sUnit_radicalQuotient_card_source
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range : Subgroup Kˣ) ⧸
      ((powMonoidHom (α := Kˣ) n).range).subgroupOf
        (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_radicalQuotient_card K S hS n hn ζ hζ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_isGalois`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_isGalois_source [IsGalois K Ω]
    (n : ℕ) (Δ : Subgroup Kˣ) :
    IsGalois K (originalKummerRadicalField (Ω := Ω) n Δ) :=
  originalKummerRadicalField_isGalois (Ω := Ω) n Δ

end

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `galoisRadicalRatio_pow_fixes`. -/
theorem actual_sunit_kummer_galoisRadicalRatio_pow_fixes_source (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (g : Gal(L/K)) :
    (g ^ n) • β = β :=
  galoisRadicalRatio_pow_fixes n hζ a β hβ g

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_galois_pow_eq_one`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_galois_pow_eq_one_source
    (n : ℕ) [NeZero n] (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (σ : Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) : σ ^ n = 1 :=
  originalKummerRadicalField_galois_pow_eq_one n hζ Δ σ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerClassRoot_pow`. -/
theorem actual_sunit_kummer_originalKummerClassRoot_pow_source [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
    (Δ : Subgroup Kˣ) (c : originalKummerClassSubgroup n Δ) :
    originalKummerClassRoot (Ω := Ω) n hn Δ c ^ n =
      Units.map (algebraMap K (originalKummerRadicalField (Ω := Ω) n Δ)).toMonoidHom
        (originalKummerClassRepresentative n Δ c).val :=
  originalKummerClassRoot_pow (Ω := Ω) n hn Δ c

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_finiteDimensional`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_finiteDimensional_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    FiniteDimensional K (originalKummerRadicalField (Ω := Ω) n Δ) :=
  originalKummerRadicalField_finiteDimensional (Ω := Ω) n hn hζ Δ

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_sUnit_kummerField_finiteDimensional`. -/
theorem actual_sunit_kummer_numberField_sUnit_kummerField_finiteDimensional_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) :
    FiniteDimensional K (originalKummerRadicalField (Ω := Ω) n
      (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) :=
  numberField_sUnit_kummerField_finiteDimensional K Ω S hS n hn hζ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerClassCharacter_mul`. -/
theorem actual_sunit_kummer_originalKummerClassCharacter_mul_source (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (c d : originalKummerClassSubgroup n Δ) :
    originalKummerClassCharacter (Ω := Ω) n hn hζ Δ (c * d) =
      originalKummerClassCharacter n hn hζ Δ c *
        originalKummerClassCharacter n hn hζ Δ d :=
  originalKummerClassCharacter_mul (Ω := Ω) n hn hζ Δ c d

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerClassPairing_injective`. -/
theorem actual_sunit_kummer_originalKummerClassPairing_injective_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Function.Injective (originalKummerClassPairing (Ω := Ω) n hn hζ Δ) :=
  originalKummerClassPairing_injective (Ω := Ω) n hn hζ Δ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_finrank`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_finrank_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Module.finrank K (originalKummerRadicalField (Ω := Ω) n Δ) =
      Nat.card (originalKummerClassSubgroup n Δ) :=
  originalKummerRadicalField_finrank (Ω := Ω) n hn hζ Δ

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_sUnit_kummerField_finrank`. -/
theorem actual_sunit_kummer_numberField_sUnit_kummerField_finrank_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank K (originalKummerRadicalField (Ω := Ω) n
      (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_kummerField_finrank K Ω S hS n hn ζ hζ

end


end
noncomputable section
open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `exists_finite_sUnit_support`. -/
theorem actual_kummer_containment_exists_finite_sUnit_support_source (s : Finset Kˣ) :
    ∃ S : Finset (HeightOneSpectrum R), ∀ x ∈ s, x ∈ (S : Set (HeightOneSpectrum R)).unit K :=
  exists_finite_sUnit_support (R := R) s

end

section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]



/-- Exact original-object consumer of `finiteAbelianGalois_exists_generating_radicals`. -/
theorem actual_kummer_containment_finiteAbelianGalois_exists_generating_radicals_source
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(L/K), g ^ n = 1) :
    ∃ (a : (Gal(L/K) →* Kˣ) → Kˣ) (β : (Gal(L/K) →* Kˣ) → Lˣ),
      (∀ χ, β χ ^ n = Units.map (algebraMap K L).toMonoidHom (a χ)) ∧
      (∀ χ g, g • β χ / β χ = Units.map (algebraMap K L).toMonoidHom (χ g)) ∧
      IntermediateField.adjoin K (Set.range fun χ => (β χ).val) = ⊤ :=
  finiteAbelianGalois_exists_generating_radicals n hn hζ hexp

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `finiteAbelian_exists_sUnit_kummer_containment`. -/
theorem actual_kummer_containment_finiteAbelian_exists_sUnit_kummer_containment_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range) :=
  finiteAbelian_exists_sUnit_kummer_containment E n hn hζ hexp S₀

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_exists_sUnit_kummer_restriction`. -/
theorem actual_kummer_containment_numberField_exists_sUnit_kummer_restriction_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 1 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (r : ℕ) (hcard : Nat.card Gal(E/K) = n ^ r)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        r ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nat.card f.ker = n ^ (Fintype.card (NumberField.InfinitePlace K) + S.card - r) :=
  numberField_exists_sUnit_kummer_restriction E n hn ζ hζ hexp r hcard S₀

end


open Classical NumberField IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldPrincipalIdele_mem_supported_iff`. -/
theorem actual_supported_idele_numberFieldPrincipalIdele_mem_supported_iff_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S ↔ x ∈ S.unit K :=
  numberFieldPrincipalIdele_mem_supported_iff K S x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldSupportedIdeleClassMap_ker`. -/
theorem actual_supported_idele_numberFieldSupportedIdeleClassMap_ker_source
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (numberFieldSupportedIdeleClassMap K S).ker =
      (numberFieldSupportedPrincipalIdele K S).range :=
  numberFieldSupportedIdeleClassMap_ker K S

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldIdeleOrder_principal`. -/
theorem actual_supported_idele_numberFieldIdeleOrder_principal_source (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdeleOrder K (numberFieldPrincipalIdele K x) v =
      FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K x).val :=
  numberFieldIdeleOrder_principal K x v

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldIdeleIdeal_principal`. -/
theorem actual_supported_idele_numberFieldIdeleIdeal_principal_source (x : Kˣ) :
    numberFieldIdeleIdeal K (numberFieldPrincipalIdele K x) = toPrincipalIdeal (𝓞 K) K x :=
  numberFieldIdeleIdeal_principal K x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberField_exists_finite_principal_idele_support`. -/
theorem actual_supported_idele_numberField_exists_finite_principal_idele_support_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ∃ x : Kˣ,
        a / numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S :=
  numberField_exists_finite_principal_idele_support K S₀

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberField_exists_supportedIdeleQuotientEquiv`. -/
theorem actual_supported_idele_numberField_exists_supportedIdeleQuotientEquiv_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Nonempty (numberFieldSupportedIdeles K S ⧸
        (numberFieldSupportedPrincipalIdele K S).range ≃* OriginalNumberFieldIdeleClassGroup K) :=
  numberField_exists_supportedIdeleQuotientEquiv K S₀

end



open Classical NumberField IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlaceEquiv_mul`. -/
theorem actual_galois_support_numberFieldGaloisPlaceEquiv_mul_source (σ τ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    numberFieldGaloisPlaceEquiv K L (σ * τ) v =
      numberFieldGaloisPlaceEquiv K L σ (numberFieldGaloisPlaceEquiv K L τ v) :=
  numberFieldGaloisPlaceEquiv_mul K L σ τ v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlace_valuation`. -/
theorem actual_galois_support_numberFieldGaloisPlace_valuation_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    (numberFieldGaloisPlaceEquiv K L σ v).valuation L (σ x) = v.valuation L x :=
  numberFieldGaloisPlace_valuation K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberField_exists_finite_galoisStable_support`. -/
theorem actual_galois_support_numberField_exists_finite_galoisStable_support_source [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S :=
  numberField_exists_finite_galoisStable_support K L S₀

end

section



/-- Exact original-object consumer of `numberField_exists_galoisStable_idele_support`. -/
theorem actual_galois_support_numberField_exists_galoisStable_idele_support_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) :=
  numberField_exists_galoisStable_idele_support K L S₀

end


open NumberField IsDedekindDomain UniformSpace
open scoped NumberField Topology
section

variable {A B Γ : Type*} [Field A] [Field B] [LinearOrderedCommGroupWithZero Γ]
  [Valued A Γ] [Valued B Γ]



/-- Exact original-object consumer of `valuationPreservingRingEquiv_uniformContinuous`. -/
theorem actual_equivariant_idele_valuationPreservingRingEquiv_uniformContinuous_source (f : A ≃+* B)
    (h : ∀ x : A, Valued.v (f x) = (Valued.v x : Γ)) : UniformContinuous f :=
  valuationPreservingRingEquiv_uniformContinuous f h

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisCompletion_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldGaloisCompletion_algebraMap_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    numberFieldGaloisCompletion K L σ v (algebraMap L (v.adicCompletion L) x) =
      algebraMap L ((numberFieldGaloisPlaceEquiv K L σ v).adicCompletion L) (σ x) :=
  numberFieldGaloisCompletion_algebraMap K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisCompletion_valuation`. -/
theorem actual_equivariant_idele_numberFieldGaloisCompletion_valuation_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) :
    Valued.v (numberFieldGaloisCompletion K L σ v x) =
      (Valued.v x : WithZero (Multiplicative ℤ)) :=
  numberFieldGaloisCompletion_valuation K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisLocalTransport_mul`. -/
theorem actual_equivariant_idele_numberFieldGaloisLocalTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L))
    (hτ : numberFieldGaloisPlaceEquiv K L τ v = u)
    (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (hστ : numberFieldGaloisPlaceEquiv K L (σ * τ) v = w)
    (x : v.adicCompletion L) :
    numberFieldGaloisLocalTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisLocalTransport K L σ u w hσ
        (numberFieldGaloisLocalTransport K L τ v u hτ x) :=
  numberFieldGaloisLocalTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldFiniteAdeleGaloisMap_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldFiniteAdeleGaloisMap_algebraMap_source (σ : Gal(L/K)) (x : L) :
    numberFieldFiniteAdeleGaloisMap K L σ
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ x) :=
  numberFieldFiniteAdeleGaloisMap_algebraMap K L σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldFiniteAdeleGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldFiniteAdeleGaloisMap_mul_source (σ τ : Gal(L/K))
    (a : FiniteAdeleRing (𝓞 L) L) :
    numberFieldFiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldFiniteAdeleGaloisMap K L σ (numberFieldFiniteAdeleGaloisMap K L τ a) :=
  numberFieldFiniteAdeleGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisArchimedeanTransport_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldGaloisArchimedeanTransport_algebraMap_source (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) (x : L) :
    numberFieldGaloisArchimedeanTransport K L σ v w h (algebraMap L v.Completion x) =
      algebraMap L w.Completion (σ x) :=
  numberFieldGaloisArchimedeanTransport_algebraMap K L σ v w h x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisArchimedeanTransport_mul`. -/
theorem actual_equivariant_idele_numberFieldGaloisArchimedeanTransport_mul_source (σ τ : Gal(L/K))
    (v u w : InfinitePlace L) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : v.Completion) :
    numberFieldGaloisArchimedeanTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisArchimedeanTransport K L σ u w hσ
        (numberFieldGaloisArchimedeanTransport K L τ v u hτ x) :=
  numberFieldGaloisArchimedeanTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldInfiniteAdeleGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldInfiniteAdeleGaloisMap_mul_source (σ τ : Gal(L/K)) (a : InfiniteAdeleRing L) :
    numberFieldInfiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldInfiniteAdeleGaloisMap K L σ (numberFieldInfiniteAdeleGaloisMap K L τ a) :=
  numberFieldInfiniteAdeleGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldPrincipalIdele_galois`. -/
theorem actual_equivariant_idele_numberFieldPrincipalIdele_galois_source (σ : Gal(L/K)) (x : Lˣ) :
    numberFieldIdeleGaloisMap K L σ (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele L (σ • x) :=
  numberFieldPrincipalIdele_galois K L σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldIdeleClassGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldIdeleClassGaloisMap_mul_source (σ τ : Gal(L/K))
    (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L (σ * τ) a =
      numberFieldIdeleClassGaloisMap K L σ (numberFieldIdeleClassGaloisMap K L τ a) :=
  numberFieldIdeleClassGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


variable (S : Set (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)


/-- Exact original-object consumer of `numberFieldSupportedIdeleClassMap_galois`. -/
theorem actual_equivariant_idele_numberFieldSupportedIdeleClassMap_galois_source :
    letI := numberFieldSupportedIdeleGaloisAction K L S hS
    letI := numberFieldIdeleClassGaloisAction K L
    ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
      numberFieldSupportedIdeleClassMap L S (σ • a) =
        σ • numberFieldSupportedIdeleClassMap L S a :=
  numberFieldSupportedIdeleClassMap_galois K L S hS

end

section



/-- Exact original-object consumer of `numberField_exists_equivariant_supported_idele_sequence`. -/
theorem actual_equivariant_idele_numberField_exists_equivariant_supported_idele_sequence_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v,
        v ∈ (S : Set (HeightOneSpectrum (𝓞 L))) ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
      Function.Injective (numberFieldSupportedPrincipalIdele L S) ∧
      (numberFieldSupportedIdeleClassMap L S).ker =
        (numberFieldSupportedPrincipalIdele L S).range ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
      (letI := numberFieldSUnitGaloisAction K L S hS
       letI := numberFieldSupportedIdeleGaloisAction K L S hS
       ∀ (σ : Gal(L/K)) (x : (S : Set (HeightOneSpectrum (𝓞 L))).unit L),
         numberFieldSupportedPrincipalIdele L S (σ • x) =
           σ • numberFieldSupportedPrincipalIdele L S x) ∧
      (letI := numberFieldSupportedIdeleGaloisAction K L S hS
       letI := numberFieldIdeleClassGaloisAction K L
       ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
         numberFieldSupportedIdeleClassMap L S (σ • a) =
           σ • numberFieldSupportedIdeleClassMap L S a) :=
  numberField_exists_equivariant_supported_idele_sequence K L S₀

end


end
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical Topology
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnitOrdinaryUnitEmbedding_range`. -/
theorem actual_reduced_log_sUnitOrdinaryUnitEmbedding_range_source (S : Set (HeightOneSpectrum R)) :
    (sUnitOrdinaryUnitEmbedding (K := K) S).range = (sUnitValuations (K := K) S).ker :=
  sUnitOrdinaryUnitEmbedding_range (R := R) (K := K) S

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLog_finite_zero_ordinary`. -/
theorem actual_reduced_log_sUnitReducedLog_finite_zero_ordinary_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (hx : (sUnitReducedLog K S x).2 = 0) :
    ∃ u : (𝓞 K)ˣ, sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul :=
  sUnitReducedLog_finite_zero_ordinary K S x hx

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLog_eq_zero_iff`. -/
theorem actual_reduced_log_sUnitReducedLog_eq_zero_iff_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitReducedLog K S x = 0 ↔
      ∃ u : (𝓞 K)ˣ, u ∈ Units.torsion K ∧
        sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul :=
  sUnitReducedLog_eq_zero_iff K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLogLattice_discrete`. -/
theorem actual_reduced_log_sUnitReducedLogLattice_discrete_source : DiscreteTopology (sUnitReducedLogLattice K S) :=
  sUnitReducedLogLattice_discrete K S

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLogLattice_isZLattice`. -/
theorem actual_reduced_log_sUnitReducedLogLattice_isZLattice_source :
    letI := sUnitReducedLogLattice_discrete K S
    IsZLattice ℝ (sUnitReducedLogLattice K S) :=
  sUnitReducedLogLattice_isZLattice K S

end


open scoped BigOperators
section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnit_sum_log_absoluteValues_eq_zero`. -/
theorem actual_full_log_sUnit_sum_log_absoluteValues_eq_zero_source
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∑ w : InfinitePlace K, w.mult * Real.log (w x.val.val)) +
      ∑ v : S, Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) = 0 :=
  sUnit_sum_log_absoluteValues_eq_zero K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnit_log_adicAbv_eq_coordinate`. -/
theorem actual_full_log_sUnit_log_adicAbv_eq_coordinate_source
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (v : S) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) =
      (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S (Additive.ofMul x) v : ℝ) *
        Real.log (Ideal.absNorm v.val.asIdeal : ℝ) :=
  sUnit_log_adicAbv_eq_coordinate K S x v

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitFullLogAmbient_mem_hyperplane`. -/
theorem actual_full_log_sUnitFullLogAmbient_mem_hyperplane_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitFullLogAmbient K S x ∈ SUnitLogHyperplane K S :=
  sUnitFullLogAmbient_mem_hyperplane K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitLogHyperplaneReduction_fullLog`. -/
theorem actual_full_log_sUnitLogHyperplaneReduction_fullLog_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneReduction K S (sUnitFullLog K S x) = sUnitReducedLog K S x :=
  sUnitLogHyperplaneReduction_fullLog K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitLogHyperplaneEquiv_fullLog`. -/
theorem actual_full_log_sUnitLogHyperplaneEquiv_fullLog_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneEquiv K S (sUnitFullLog K S x) = sUnitReducedLog K S x :=
  sUnitLogHyperplaneEquiv_fullLog K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitFullLogLattice_isZLattice`. -/
theorem actual_full_log_sUnitFullLogLattice_isZLattice_source :
    letI := sUnitFullLogLattice_discrete K S
    IsZLattice ℝ (sUnitFullLogLattice K S) :=
  sUnitFullLogLattice_isZLattice K S

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlace_adicAbv`. -/
theorem actual_full_log_numberFieldGaloisPlace_adicAbv_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L (numberFieldGaloisPlaceEquiv K L σ v) (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L v x :=
  numberFieldGaloisPlace_adicAbv K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogCoordinateSum_galois`. -/
theorem actual_full_log_sUnitLogCoordinateSum_galois_source (σ : Gal(L/K)) (z : SUnitFullLogSpace L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    sUnitLogCoordinateSum L S (σ • z) = sUnitLogCoordinateSum L S z :=
  sUnitLogCoordinateSum_galois K L S hS σ z

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitFullLog_galois`. -/
theorem actual_full_log_sUnitFullLog_galois_source (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitLogHyperplaneAction K L S hS
    sUnitFullLog L S (σ • x) = σ • sUnitFullLog L S x :=
  sUnitFullLog_galois K L S hS σ x

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogToLattice_galois`. -/
theorem actual_full_log_sUnitLogToLattice_galois_source (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitFullLogLatticeAction L S K hS
    sUnitLogToLattice L S (σ • x) = σ • sUnitLogToLattice L S x :=
  sUnitLogToLattice_galois L S K hS σ x

end


open Module Submodule
section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLogDiagonalSplit_surjective`. -/
theorem actual_sunit_permutation_sUnitLogDiagonalSplit_surjective_source : Function.Surjective (sUnitLogDiagonalSplit L S) :=
  sUnitLogDiagonalSplit_surjective L S

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLogProductLattice_mem`. -/
theorem actual_sunit_permutation_sUnitLogProductLattice_mem_source (z : SUnitLogHyperplane L S × ℝ) :
    z ∈ sUnitLogProductLattice L S ↔ z.1 ∈ sUnitFullLogLattice L S ∧ ∃ n : ℤ, (n : ℝ) = z.2 :=
  sUnitLogProductLattice_mem L S z

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtendedLogLattice_galois_mem`. -/
theorem actual_sunit_permutation_sUnitExtendedLogLattice_galois_mem_source (σ : Gal(L/K)) (z : SUnitFullLogSpace L S)
    (hz : z ∈ sUnitExtendedLogLattice L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    σ • z ∈ sUnitExtendedLogLattice L S :=
  sUnitExtendedLogLattice_galois_mem L S K hS σ z hz

end

section

variable {ι : Type*} [Fintype ι]

/-- Exact original-object consumer of `norm_sub_latticeApproximation_le`. -/
theorem actual_sunit_permutation_norm_sub_latticeApproximation_le_source
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) :
    ‖x - (latticeApproximation L x : ι → ℝ)‖ ≤
      latticeApproximationRadius L :=
  norm_sub_latticeApproximation_le L x

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `averagedLatticeVector_offDiagonal_bound`. -/
theorem actual_sunit_permutation_averagedLatticeVector_offDiagonal_bound_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) {i j : ι} (hji : j ≠ i) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) j| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L :=
  averagedLatticeVector_offDiagonal_bound ρ L hL t hji

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `averagedLatticeVector_linearIndependent`. -/
theorem actual_sunit_permutation_averagedLatticeVector_linearIndependent_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    LinearIndependent ℝ
      (fun i ↦
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i :
            ι → ℝ)) :=
  averagedLatticeVector_linearIndependent ρ L hL

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `permutationSublattice_finite_quotient`. -/
theorem actual_sunit_permutation_permutationSublattice_finite_quotient_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (L ⧸
        (permutationSublattice ρ L hL).comap
          L.subtype) :=
  permutationSublattice_finite_quotient ρ L hL

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_exists_finiteIndex_permutation_sublattice`. -/
theorem actual_sunit_permutation_sUnit_exists_finiteIndex_permutation_sublattice_source :
    letI := sUnitLogPlaceAction K L S hS
    letI := sUnitFullLogSpaceAction K L S hS
    ∃ T : Submodule ℤ (SUnitFullLogSpace L S),
      T ≤ sUnitExtendedLogLattice L S ∧ DiscreteTopology T ∧
      Submodule.span ℝ (T : Set (SUnitFullLogSpace L S)) = ⊤ ∧
      Finite (sUnitExtendedLogLattice L S ⧸ T.comap (sUnitExtendedLogLattice L S).subtype) ∧
      ∃ b : Module.Basis (SUnitLogPlace L S) ℤ T,
        ∀ (σ : Gal(L/K)) (p : SUnitLogPlace L S),
          σ • (b p : SUnitFullLogSpace L S) = (b (σ • p) : SUnitFullLogSpace L S) :=
  sUnit_exists_finiteIndex_permutation_sublattice K L S hS

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogRepHom_surjective`. -/
theorem actual_original_sunit_herbrand_sUnitLogRepHom_surjective_source : Function.Surjective (sUnitLogRepHom K L S hS).hom :=
  sUnitLogRepHom_surjective K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogarithmicShortComplex_shortExact`. -/
theorem actual_original_sunit_herbrand_sUnitLogarithmicShortComplex_shortExact_source :
    (sUnitLogarithmicShortComplex K L S hS).ShortExact :=
  sUnitLogarithmicShortComplex_shortExact K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogarithmicKernel_first_second_card_eq`. -/
theorem actual_original_sunit_herbrand_sUnitLogarithmicKernel_first_second_card_eq_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 1) =
      Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 2) :=
  sUnitLogarithmicKernel_first_second_card_eq K L S hS σ hgen

end

section



/-- Exact original-object consumer of `bounded_positive_cardinality_recurrence`. -/
theorem actual_original_sunit_herbrand_bounded_positive_cardinality_recurrence_source
    (d : ℕ → ℕ) (a b bound : ℕ) (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, d n ≤ bound) (hrec : ∀ n, d (n + 1) * a = d n * b) : a = b :=
  bounded_positive_cardinality_recurrence d a b bound hpos hbound hrec

end

section



/-- Exact original-object consumer of `exact_cohomology_connecting_cardinality`. -/
theorem actual_original_sunit_herbrand_exact_cohomology_connecting_cardinality_source
    {R G : Type} [CommRing R] [Group G]
    (X : ShortComplex (Rep R G)) (hX : X.ShortExact) (n : ℕ) :
    Nat.card (groupCohomology X.X₂ (n + 1)) *
        Nat.card (groupCohomology.δ hX n (n + 1) rfl).hom.range *
        Nat.card (groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl).hom.range =
      Nat.card (groupCohomology X.X₁ (n + 1)) * Nat.card (groupCohomology X.X₃ (n + 1)) :=
  exact_cohomology_connecting_cardinality X hX n

end

section

variable {G : Type} [CommGroup G] [Fintype G]
  (A : Rep ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)


include hg


/-- Exact original-object consumer of `cyclic_cohomology_positive_finite`. -/
theorem actual_original_sunit_herbrand_cyclic_cohomology_positive_finite_source [Finite (groupCohomology A 1)]
    [Finite (groupCohomology A 2)] (n : ℕ) : Finite (groupCohomology A (n + 1)) :=
  cyclic_cohomology_positive_finite A g hg n

end

section



/-- Exact original-object consumer of `cyclic_cohomology_herbrand_cardinality`. -/
theorem actual_original_sunit_herbrand_cyclic_cohomology_herbrand_cardinality_source
    {G : Type} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    Finite (groupCohomology X.X₂ 1) ∧ Finite (groupCohomology X.X₂ 2) ∧
      Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) *
          Nat.card (groupCohomology X.X₃ 1) =
        Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2) *
          Nat.card (groupCohomology X.X₃ 2) :=
  cyclic_cohomology_herbrand_cardinality X hX g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_logarithmic_herbrand_comparison`. -/
theorem actual_original_sunit_herbrand_sUnit_logarithmic_herbrand_comparison_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) :=
  sUnit_logarithmic_herbrand_comparison K L S hS σ hgen

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLatticeProdIntToExtended_bijective`. -/
theorem actual_original_sunit_herbrand_sUnitLatticeProdIntToExtended_bijective_source : Function.Bijective (sUnitLatticeProdIntToExtended L S) :=
  sUnitLatticeProdIntToExtended_bijective L S

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLatticeProdIntToExtended_galois`. -/
theorem actual_original_sunit_herbrand_sUnitLatticeProdIntToExtended_galois_source (σ : Gal(L/K)) (x : sUnitFullLogLattice L S × ℤ) :
    letI : SMul Gal(L/K) (sUnitFullLogLattice L S × ℤ) :=
      (sUnitLatticeProdIntAction K L S hS).toMulAction.toSMul
    letI : SMul Gal(L/K) (sUnitExtendedLogLattice L S) :=
      (sUnitExtendedLogLatticeAction K L S hS).toMulAction.toSMul
    sUnitLatticeProdIntToExtended L S (σ • x) = σ • sUnitLatticeProdIntToExtended L S x :=
  sUnitLatticeProdIntToExtended_galois K L S hS σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtendedProductRepIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_sUnitExtendedProductRepIso_hom_apply_source (x : sUnitFullLogLattice L S × ℤ) :
    (sUnitExtendedProductRepIso K L S hS).hom.hom x = sUnitLatticeProdIntToExtended L S x :=
  sUnitExtendedProductRepIso_hom_apply K L S hS x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogLattice_cohomology_finite_of_extended`. -/
theorem actual_original_sunit_herbrand_sUnitLogLattice_cohomology_finite_of_extended_source (n : ℕ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) n)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) n) :=
  sUnitLogLattice_cohomology_finite_of_extended K L S hS n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_diagonal_herbrand_factor`. -/
theorem actual_original_sunit_herbrand_sUnit_diagonal_herbrand_factor_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) * Nat.card Gal(L/K) :=
  sUnit_diagonal_herbrand_factor K L S hS σ hgen

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (W : Submodule R A)
  (hW : ∀ g, W ≤ W.comap (A.ρ g))



/-- Exact original-object consumer of `stableSubmoduleShortComplex_shortExact`. -/
theorem actual_original_sunit_herbrand_stableSubmoduleShortComplex_shortExact_source :
    (stableSubmoduleShortComplex A W hW).ShortExact :=
  stableSubmoduleShortComplex_shortExact A W hW

end

section

variable {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G)
  (W : Submodule ℤ A) (hW : ∀ g, W ≤ W.comap (A.ρ g))



/-- Exact original-object consumer of `finiteIndex_herbrand_comparison`. -/
theorem actual_original_sunit_herbrand_finiteIndex_herbrand_comparison_source
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (A ⧸ W)]
    [Finite (groupCohomology (A.subrepresentation W hW) 1)]
    [Finite (groupCohomology (A.subrepresentation W hW) 2)] :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 1) =
        Nat.card (groupCohomology A 1) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 2) :=
  finiteIndex_herbrand_comparison A W hW g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtended_exists_permutation_subrepresentation`. -/
theorem actual_original_sunit_herbrand_sUnitExtended_exists_permutation_subrepresentation_source :
    letI := sUnitLogPlaceAction K L S hS
    ∃ W : Submodule ℤ (sUnitExtendedLogRep K L S hS),
      ∃ hW : ∀ σ, W ≤ W.comap ((sUnitExtendedLogRep K L S hS).ρ σ),
        Finite ((sUnitExtendedLogRep K L S hS) ⧸ W) ∧
        ∃ b : Module.Basis (SUnitLogPlace L S) ℤ W,
          ∀ (σ : Gal(L/K)) p,
            ((sUnitExtendedLogRep K L S hS).subrepresentation W hW).ρ σ (b p) =
              b (σ • p) :=
  sUnitExtended_exists_permutation_subrepresentation K L S hS

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]



/-- Exact original-object consumer of `permutationCoordinateRep_apply`. -/
theorem actual_original_sunit_herbrand_permutationCoordinateRep_apply_source (g : G) (x : ι → R) (i : ι) :
    (permutationCoordinateRep R G ι).ρ g x i = x (g⁻¹ • i) :=
  permutationCoordinateRep_apply R G ι g x i

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  [MulAction.IsPretransitive G ι] (i : ι)



/-- Exact original-object consumer of `transitivePermutationCoindIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_transitivePermutationCoindIso_hom_apply_source (x : ι → R) (g : G) :
    ((transitivePermutationCoindIso R G ι i).hom.hom x).val g = x (g⁻¹ • i) :=
  transitivePermutationCoindIso_hom_apply R G ι i x g

end

section

variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [MulAction.IsPretransitive G ι] (i : ι)

include i


/-- Exact original-object consumer of `transitivePermutation_second_cohomology_order`. -/
theorem actual_original_sunit_herbrand_transitivePermutation_second_cohomology_order_source :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        Nat.card (MulAction.stabilizer G i) :=
  transitivePermutation_second_cohomology_order G ι i

end

section

variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)



variable [Fintype ι]



/-- Exact original-object consumer of `originalFinitePi_cohomology_card`. -/
theorem actual_original_sunit_herbrand_originalFinitePi_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (originalPiRep A) n) =
      ∏ i, Nat.card (groupCohomology (A i) n) :=
  originalFinitePi_cohomology_card A n

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]



/-- Exact original-object consumer of `permutationOrbitRepIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_permutationOrbitRepIso_hom_apply_source (x : ι → R)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (permutationOrbitRepIso R G ι).hom.hom x ω j = x j.val :=
  permutationOrbitRepIso_hom_apply R G ι x ω j

end

section

variable (G ι : Type) [CommGroup G] [MulAction G ι]



variable [Fintype G] [IsCyclic G] [Fintype ι]



/-- Exact original-object consumer of `permutationCoordinate_second_cohomology_order`. -/
theorem actual_original_sunit_herbrand_permutationCoordinate_second_cohomology_order_source :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) :=
  permutationCoordinate_second_cohomology_order G ι

end

section

variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [Fintype ι] (A : Rep ℤ G) (b : Module.Basis ι ℤ A)
  (hb : ∀ g i, A.ρ g (b i) = b (g • i))

include hb


/-- Exact original-object consumer of `permutedBasis_cohomology_orders`. -/
theorem actual_original_sunit_herbrand_permutedBasis_cohomology_orders_source :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = 1 ∧
      Nat.card (groupCohomology A 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) :=
  permutedBasis_cohomology_orders G ι A b hb

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtended_log_lattice_herbrand`. -/
theorem actual_original_sunit_herbrand_sUnitExtended_log_lattice_herbrand_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  sUnitExtended_log_lattice_herbrand K L S hS σ hgen

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_sUnit_herbrand_cardinality`. -/
theorem actual_original_sunit_herbrand_original_sUnit_herbrand_cardinality_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) * Nat.card Gal(L/K) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  original_sUnit_herbrand_cardinality K L S hS σ hgen

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] Rep.hV2
attribute [local instance] numberFieldGaloisPlaceAction
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedClassRepHom_apply`. -/
theorem actual_supported_local_originalSupportedClassRepHom_apply_source (x : Additive (numberFieldSupportedIdeles L S)) :
    (originalSupportedClassRepHom K L S hS).hom x =
      Additive.ofMul (numberFieldSupportedIdeleClassMap L S x.toMul) :=
  originalSupportedClassRepHom_apply K L S hS x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_exists_supportedIdele_shortExact`. -/
theorem actual_supported_local_original_exists_supportedIdele_shortExact_source [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
        (originalSupportedIdeleShortComplex K L S hS).ShortExact :=
  original_exists_supportedIdele_shortExact K L S₀

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_supported`. -/
theorem actual_supported_local_original_ideleClass_herbrand_of_supported_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1)]
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2)]
    (hfactor : letI := sUnitLogPlaceAction K L S hS
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_supported K L S hS σ hgen hsurj hfactor

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `unramified_integer_unit_norm_preimages`. -/
theorem actual_supported_local_unramified_integer_unit_norm_preimages_source :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x :=
  unramified_integer_unit_norm_preimages K L

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `unramified_integer_unit_positive_cohomology_zero`. -/
theorem actual_supported_local_unramified_integer_unit_positive_cohomology_zero_source (n : ℕ) (hn : 0 < n) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) n) :=
  unramified_integer_unit_positive_cohomology_zero K L n hn

end

section

variable {R G ι : Type} [CommRing R] [CommGroup G] [Fintype G]
  (A : ι → Rep R G)



/-- Exact original-object consumer of `cyclic_originalPi_cohomology_zero`. -/
theorem actual_supported_local_cyclic_originalPi_cohomology_zero_source
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : 0 < n)
    (hzero : ∀ i, Limits.IsZero (groupCohomology (A i) n)) :
    Limits.IsZero (groupCohomology (originalPiRep A) n) :=
  cyclic_originalPi_cohomology_zero A g hg n hn hzero

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldSupportedIdeleCoordinateEquiv_finite`. -/
theorem actual_supported_local_numberFieldSupportedIdeleCoordinateEquiv_finite_source
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : numberFieldSupportedIdeles K S)
    (v : HeightOneSpectrum (𝓞 K)) :
    (numberFieldSupportedIdeleCoordinateEquiv K S a).2.val v =
      numberFieldIdeleFiniteComponent K v a.val :=
  numberFieldSupportedIdeleCoordinateEquiv_finite K S a v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `numberFieldSupportedIdeleCoordinate_finite_galois`. -/
theorem actual_supported_local_numberFieldSupportedIdeleCoordinate_finite_galois_source
    (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S)
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    (numberFieldSupportedIdeleCoordinateEquiv L S
      (numberFieldSupportedIdeleGaloisMap K L S hS σ a)).2.val w =
      Units.map (numberFieldGaloisLocalTransport K L σ v w h).toMonoidHom
        ((numberFieldSupportedIdeleCoordinateEquiv L S a).2.val v) :=
  numberFieldSupportedIdeleCoordinate_finite_galois K L S hS σ a v w h

end

section

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `numberFieldSupportedFiniteFactorEquiv_outside`. -/
theorem actual_supported_local_numberFieldSupportedFiniteFactorEquiv_outside_source
    (x : numberFieldSupportedFiniteCoordinates K S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (((numberFieldSupportedFiniteFactorEquiv K S x).2 v).val : v.val.adicCompletion K) =
      (x.val v.val).val :=
  numberFieldSupportedFiniteFactorEquiv_outside K S x v

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)



/-- Exact original-object consumer of `transportedPiMap_apply`. -/
theorem actual_supported_local_transportedPiMap_apply_source (g : G) (x : ∀ i, M i) (i j : ι) (h : g • i = j) :
    transportedPiMap R G ι M T g x j = T g i j h (x i) :=
  transportedPiMap_apply R G ι M T g x i j h

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



/-- Exact original-object consumer of `transportedCoindHom_bijective`. -/
theorem actual_supported_local_transportedCoindHom_bijective_source :
    Function.Bijective (transportedCoindHom R G ι M T T_one T_mul i).hom :=
  transportedCoindHom_bijective R G ι M T T_one T_mul i

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


/-- Exact original-object consumer of `numberFieldFiniteUnitTransport_mul`. -/
theorem actual_supported_local_numberFieldFiniteUnitTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletion L)ˣ) :
    numberFieldFiniteUnitTransport K L (σ * τ) v w hστ x =
      numberFieldFiniteUnitTransport K L σ u w hσ
        (numberFieldFiniteUnitTransport K L τ v u hτ x) :=
  numberFieldFiniteUnitTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `transportedOrbitProductIso_hom_apply`. -/
theorem actual_supported_local_transportedOrbitProductIso_hom_apply_source (x : ∀ i, M i)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (transportedOrbitProductIso R G ι M T T_one T_mul).hom.hom x ω j = x j.val :=
  transportedOrbitProductIso_hom_apply R G ι M T T_one T_mul x ω j

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnitTransport_mul`. -/
theorem actual_supported_local_supportedUnrestrictedUnitTransport_mul_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (p q r : SUnitLogPlace L S) (hτ : τ • p = q) (hσ : σ • q = r)
      (hστ : (σ * τ) • p = r) (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitTransport K L S hS (σ * τ) p r hστ x =
        supportedUnrestrictedUnitTransport K L S hS σ q r hσ
          (supportedUnrestrictedUnitTransport K L S hS τ p q hτ x) :=
  supportedUnrestrictedUnitTransport_mul K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


/-- Exact original-object consumer of `numberFieldIntegerUnitTransport_mul`. -/
theorem actual_supported_local_numberFieldIntegerUnitTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletionIntegers L)ˣ) :
    numberFieldIntegerUnitTransport K L (σ * τ) v w hστ x =
      numberFieldIntegerUnitTransport K L σ u w hσ
        (numberFieldIntegerUnitTransport K L τ v u hτ x) :=
  numberFieldIntegerUnitTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedOutsideUnitTransport_mul`. -/
theorem actual_supported_local_supportedOutsideUnitTransport_mul_source :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (v u w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
      (hτ : τ • v = u) (hσ : σ • u = w) (hστ : (σ * τ) • v = w)
      (x : Additive (v.val.adicCompletionIntegers L)ˣ),
      supportedOutsideUnitTransport K L S hS (σ * τ) v w hστ x =
        supportedOutsideUnitTransport K L S hS σ u w hσ
          (supportedOutsideUnitTransport K L S hS τ v u hτ x) :=
  supportedOutsideUnitTransport_mul K L S hS

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `supportedIdeleLocalFactorLinearEquiv_outside`. -/
theorem actual_supported_local_supportedIdeleLocalFactorLinearEquiv_outside_source
    (a : Additive (numberFieldSupportedIdeles L S))
    (v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}) :
    (((supportedIdeleLocalFactorLinearEquiv L S a).2 v).toMul.val : v.val.adicCompletion L) =
      (numberFieldIdeleFiniteComponent L v.val a.toMul.val).val :=
  supportedIdeleLocalFactorLinearEquiv_outside L S a v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedIdeleLocalFactorRepIso_hom_apply`. -/
theorem actual_supported_local_supportedIdeleLocalFactorRepIso_hom_apply_source
    (a : Additive (numberFieldSupportedIdeles L S)) :
    (supportedIdeleLocalFactorRepIso K L S hS).hom.hom a =
      supportedIdeleLocalFactorLinearEquiv L S a :=
  supportedIdeleLocalFactorRepIso_hom_apply K L S hS a

end

section

variable (R G ι : Type) [CommRing R] [CommGroup G] [MulAction G ι] [Fintype ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `transportedFiniteOrbit_cohomology_card`. -/
theorem actual_supported_local_transportedFiniteOrbit_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (transportedPiRep R G ι M T T_one T_mul) n) =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        Nat.card (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
          (permutationOrbitPoint G ι ω)) n) :=
  transportedFiniteOrbit_cohomology_card R G ι M T T_one T_mul n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnit_cohomology_card`. -/
theorem actual_supported_local_supportedUnrestrictedUnit_cohomology_card_source (n : ℕ) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) =
      ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n) :=
  supportedUnrestrictedUnit_cohomology_card K L S hS n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedOutsideUnit_cohomology_zero_of_local`. -/
theorem actual_supported_local_supportedOutsideUnit_cohomology_zero_of_local_source (n : ℕ) (hn : 0 < n) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) n)) →
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n) :=
  supportedOutsideUnit_cohomology_zero_of_local K L S hS n hn

end

section

variable {R G : Type} [CommRing R] [Group G] (A B : Rep R G)



/-- Exact original-object consumer of `originalBinaryProduct_cohomology_card`. -/
theorem actual_supported_local_originalBinaryProduct_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (Rep.of (A.ρ.prod B.ρ)) n) =
      Nat.card (groupCohomology A n) * Nat.card (groupCohomology B n) :=
  originalBinaryProduct_cohomology_card A B n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedIdele_cohomology_of_outside_zero`. -/
theorem actual_supported_local_originalSupportedIdele_cohomology_of_outside_zero_source (n : ℕ)
    [Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n)]
    (hout : Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n)) :
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) n) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) n) =
        Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) :=
  originalSupportedIdele_cohomology_of_outside_zero K L S hS n hout

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_supportedIdele_cohomology_of_local`. -/
theorem actual_supported_local_original_supportedIdele_cohomology_of_local_source
    (hlocal : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) ∧
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1) ∧
      Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) = 1 ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  original_supportedIdele_cohomology_of_local K L S hS hlocal houtside

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_local`. -/
theorem actual_supported_local_original_ideleClass_herbrand_of_local_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hlocal : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) ∧
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
  original_ideleClass_herbrand_of_local K L S hS hsurj hlocal houtside

end


end

end Dubon2026.SemanticRegression
