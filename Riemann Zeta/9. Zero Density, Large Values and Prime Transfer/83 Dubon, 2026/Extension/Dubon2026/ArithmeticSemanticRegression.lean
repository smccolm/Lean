import Dubon2026

/-! Exact original arithmetic deformation, cotangent and matrix representation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticFramedUniversalRing_localData`. -/
theorem actual_arithmetic_framed_universal_ring_arithmeticFramedUniversalRing_localData_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     IsNoetherianRing (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ))
         (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) ∧
       (inferInstance : TopologicalSpace (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ)) =
         (IsLocalRing.maximalIdeal (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ)).adicTopology) :=
  arithmeticFramedUniversalRing_localData a ha p hp hpa σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Exact original-object consumer of `arithmeticFramedFiberEquiv_natural`. -/
theorem actual_arithmetic_framed_universality_arithmeticFramedFiberEquiv_natural_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     ∀ f : OriginalContinuousCoefficientFiber
       (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ) eA,
       arithmeticFramedFiberEquiv hB eB a ha p hp hpa σ hσ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB (rationalArithmeticGaloisGroup a) σ k hk hres
             (arithmeticFramedFiberEquiv hA eA a ha p hp hpa σ hσ f)) :=
  arithmeticFramedFiberEquiv_natural hA hB eA eB a ha p hp hpa σ hσ k hk hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `originalPresentedCoefficientRing_t2Space`. -/
theorem actual_original_presented_coefficient_compactness_originalPresentedCoefficientRing_t2Space_source
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    T2Space (OriginalPresentedCoefficientRing H q σ) :=
  originalPresentedCoefficientRing_t2Space H q σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]

/-- Exact original-object consumer of `originalLocalQuotientCoefficientFiberEquiv_bijective`. -/
theorem actual_local_quotient_coefficient_fibers_originalLocalQuotientCoefficientFiberEquiv_bijective_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    Function.Bijective (originalLocalQuotientCoefficientFiberEquiv eR eA J) :=
  originalLocalQuotientCoefficientFiberEquiv_bijective eR eA J

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]
  [CommRing A] [Algebra O A]

/-- Exact original-object consumer of `representationDeterminantIdeal_le_kernel_iff`. -/
theorem actual_representation_determinant_ideal_representationDeterminantIdeal_le_kernel_iff_source
    (ρ : G →* GeneralLinearGroup ι R) (δ : G →* Oˣ) (f : R →ₐ[O] A) :
    representationDeterminantIdeal ρ δ ≤ RingHom.ker f.toRingHom ↔
      ∀ g : G, GeneralLinearGroup.det (GeneralLinearGroup.map (n := ι) f.toRingHom (ρ g)) =
        Units.map (algebraMap O A) (δ g) :=
  representationDeterminantIdeal_le_kernel_iff ρ δ f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `representationDeterminantQuotient_isLocal`. -/
theorem actual_residual_determinant_quotient_representationDeterminantQuotient_isLocal_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g : G, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    IsLocalRing (R ⧸ representationDeterminantIdeal ρ δ) :=
  representationDeterminantQuotient_isLocal eR ρ σ hρ δ hδ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticFixedDeterminantRing_localData`. -/
theorem actual_arithmetic_fixed_determinant_ring_arithmeticFixedDeterminantRing_localData_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     IsNoetherianRing (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ))
         (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) ∧
       (inferInstance : TopologicalSpace (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ)) =
         (IsLocalRing.maximalIdeal (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ)).adicTopology) :=
  arithmeticFixedDeterminantRing_localData a ha p hp hpa σ hσ δ hδ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Exact original-object consumer of `arithmeticFixedDeterminantFramedFiberEquiv_natural`. -/
theorem actual_arithmetic_fixed_determinant_universality_arithmeticFixedDeterminantFramedFiberEquiv_natural_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     ∀ (f : OriginalContinuousCoefficientFiber
       (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ) eA)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticFixedDeterminantFramedFiberEquiv hB eB a ha p hp hpa σ hσ δ hδ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val.val g =
           GeneralLinearGroup.map (n := ι) k.toRingHom
             ((arithmeticFixedDeterminantFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ f).val.val g)) :=
  arithmeticFixedDeterminantFramedFiberEquiv_natural hA hB eA eB a ha p hp hpa σ hσ δ hδ k hk hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticFixedDeterminantRepresentation_residue`. -/
theorem actual_arithmetic_fixed_determinant_representation_arithmeticFixedDeterminantRepresentation_residue_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ)).toRingHom).comp
         (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom = σ) :=
  arithmeticFixedDeterminantRepresentation_residue a ha p hp hpa σ hσ δ hδ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [T2Space H]

/-- Exact original-object consumer of `finite_continuousMonoidHom_of_topological_generators`. -/
theorem actual_topological_generators_finite_hom_finite_continuousMonoidHom_of_topological_generators_source
    [Finite H] (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    Finite (G →ₜ* H) :=
  finite_continuousMonoidHom_of_topological_generators S hS

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Finite A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `arithmeticOriginalFramedFiber_finite`. -/
theorem actual_arithmetic_framed_finite_coefficients_arithmeticOriginalFramedFiber_finite_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    Finite (OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ) :=
  arithmeticOriginalFramedFiber_finite hA eA a ha p hp hpa σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R]

/-- Exact original-object consumer of `finiteDualNumber_maximal_isAdicComplete`. -/
theorem actual_finite_nilpotent_adic_coefficients_finiteDualNumber_maximal_isAdicComplete_source (K : Type*) [Field K] [Finite K] :
    IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber K)) (DualNumber K) :=
  finiteDualNumber_maximal_isAdicComplete K

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `dualNumberOriginalResidueEquiv_reduction`. -/
theorem actual_dual_number_original_residue_dualNumberOriginalResidueEquiv_reduction_source (K : Type*) [Field K]
    (z : DualNumber K) :
    localCoefficientReduction (dualNumberOriginalResidueEquiv K) z =
      IsLocalRing.residue K z.fst :=
  dualNumberOriginalResidueEquiv_reduction K z

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `dualNumberGL_continuous_iff`. -/
theorem actual_dual_number_adic_topology_dualNumberGL_continuous_iff_source
    (K : Type*) [Field K] [TopologicalSpace K] [DiscreteTopology K]
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (f : X → Matrix.GeneralLinearGroup ι (DualNumber K)) :
    (letI : TopologicalSpace (DualNumber K) :=
       (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
     Continuous f) ↔ Continuous f :=
  dualNumberGL_continuous_iff K f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Exact original-object consumer of `arithmeticContinuousFirstOrderLift_finite`. -/
theorem actual_arithmetic_first_order_finite_arithmeticContinuousFirstOrderLift_finite_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Finite {τ : MatrixFirstOrderLift ρ // Continuous τ.val} :=
  arithmeticContinuousFirstOrderLift_finite a ha p hp hpa ρ hρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Exact original-object consumer of `arithmeticContinuousAdjointH1_finiteDimensional`. -/
theorem actual_arithmetic_continuous_adjoint_finite_arithmeticContinuousAdjointH1_finiteDimensional_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Module.Finite K (ContinuousMatrixAdjointH1 ρ hρ) :=
  arithmeticContinuousAdjointH1_finiteDimensional a ha p hp hpa ρ hρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `numberField_card_inertia_eq_ramificationIdx`. -/
theorem actual_number_field_inertia_ramification_numberField_card_inertia_eq_ramificationIdx_source
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = v.asIdeal.ramificationIdx w.asIdeal :=
  numberField_card_inertia_eq_ramificationIdx v w

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_finiteGalois_inertia_eq_bot`. -/
theorem actual_unramified_union_finite_inertia_originalUnramifiedUnion_finiteGalois_inertia_eq_bot_source
    (a : 𝓞 K) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField K Ω)
    (hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal) :
    w.asIdeal.inertia Gal(F/K) = ⊥ :=
  originalUnramifiedUnion_finiteGalois_inertia_eq_bot a ha F hF w hw

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Normal K E]

/-- Exact original-object consumer of `integral_inertia_restrictNormal_mem`. -/
theorem actual_integral_inertia_restriction_integral_inertia_restrictNormal_mem_source
    (P : Ideal (𝓞 L)) (σ : Gal(L/K)) (hσ : σ ∈ P.inertia Gal(L/K)) :
    σ.restrictNormal E ∈ (P.under (𝓞 E)).inertia Gal(E/K) :=
  integral_inertia_restrictNormal_mem P σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_inertia_eq_bot`. -/
theorem actual_unramified_union_infinite_inertia_originalUnramifiedUnion_inertia_eq_bot_source
    (a : 𝓞 K) (ha : a ≠ 0)
    (P : Ideal (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)))
    [P.IsPrime] (hP : P ≠ ⊥)
    (haP : algebraMap (𝓞 K) (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)) a ∉ P) :
    P.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) = ⊥ :=
  originalUnramifiedUnion_inertia_eq_bot a ha P hP haP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_exists_prime_trivial_inertia`. -/
theorem actual_unramified_union_prime_inertia_originalUnramifiedUnion_exists_prime_trivial_inertia_source
    (a : 𝓞 K) (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (hv : a ∉ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)),
      w.asIdeal.LiesOver v.asIdeal ∧
        w.asIdeal.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) = ⊥ :=
  originalUnramifiedUnion_exists_prime_trivial_inertia a ha v hv

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]

/-- Exact original-object consumer of `integral_inertia_isClosed`. -/
theorem actual_integral_inertia_closed_integral_inertia_isClosed_source (P : Ideal (𝓞 L)) :
    IsClosed (P.inertia Gal(L/K) : Set Gal(L/K)) :=
  integral_inertia_isClosed P

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalArithmeticInertia_eq_bot`. -/
theorem actual_rational_arithmetic_inertia_rationalArithmeticInertia_eq_bot_source (a : 𝓞 ℚ) (ha : a ≠ 0) :
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     ∀ (P : Ideal (𝓞 U)), P.IsPrime → P ≠ ⊥ →
       algebraMap (𝓞 ℚ) (𝓞 U) a ∉ P → rationalArithmeticInertia a P = ⊥) :=
  rationalArithmeticInertia_eq_bot a ha

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `arithmeticUnramifiedAdjointClasses_firstOrder_iff`. -/
theorem actual_arithmetic_unramified_adjoint_classes_arithmeticUnramifiedAdjointClasses_firstOrder_iff_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ arithmeticUnramifiedAdjointClasses a ρ hρ P ↔
      ∃ X : Matrix ι ι R, ∀ σ : rationalArithmeticInertia a P,
        (ρ σ.val).val * X * (ρ σ.val⁻¹).val - X = matrixFirstOrderCocycle ρ τ σ.val :=
  arithmeticUnramifiedAdjointClasses_firstOrder_iff a ρ hρ P τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `matrixRepresentationRelationQuotient_isLocal`. -/
theorem actual_residual_relation_quotient_matrixRepresentationRelationQuotient_isLocal_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    IsLocalRing (R ⧸ matrixRepresentationRelationIdeal ρ N) :=
  matrixRepresentationRelationQuotient_isLocal eR ρ σ hρ N hN

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticFixedDeterminantRing_t2Space`. -/
theorem actual_arithmetic_fixed_determinant_compactness_arithmeticFixedDeterminantRing_t2Space_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ) :
    T2Space (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) :=
  arithmeticFixedDeterminantRing_t2Space a ha p hp hpa σ hσ δ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticUnramifiedDeformationRing_localData`. -/
theorem actual_arithmetic_unramified_deformation_ring_arithmeticUnramifiedDeformationRing_localData_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     IsNoetherianRing (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) ∧
       IsAdicComplete
         (IsLocalRing.maximalIdeal (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))
         (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) ∧
       (inferInstance : TopologicalSpace (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) =
         (IsLocalRing.maximalIdeal (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).adicTopology) :=
  arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `arithmeticUnramifiedFramedFiberEquiv_bijective`. -/
theorem actual_arithmetic_unramified_universality_arithmeticUnramifiedFramedFiberEquiv_bijective_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticUnramifiedFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ P hP) :=
  arithmeticUnramifiedFramedFiberEquiv_bijective hA eA a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticUnramifiedRepresentation_residue`. -/
theorem actual_arithmetic_unramified_representation_arithmeticUnramifiedRepresentation_residue_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction
         (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)).toRingHom).comp
         (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom = σ) :=
  arithmeticUnramifiedRepresentation_residue a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderLift_subgroup_kernel_iff`. -/
theorem actual_first_order_inertia_criterion_matrixFirstOrderLift_subgroup_kernel_iff_source
    (ρ : G →* GeneralLinearGroup ι R) (τ : MatrixFirstOrderLift ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker) :
    N ≤ τ.val.ker ↔ ∀ g ∈ N, matrixFirstOrderCocycle ρ τ g = 0 :=
  matrixFirstOrderLift_subgroup_kernel_iff ρ τ N hN

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `arithmeticUnramifiedAdjointClasses_firstOrder_inertia_iff`. -/
theorem actual_arithmetic_unramified_first_order_criterion_arithmeticUnramifiedAdjointClasses_firstOrder_inertia_iff_source
    (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ arithmeticUnramifiedAdjointClasses a ρ hρ P ↔
      rationalArithmeticInertia a P ≤ τ.val.ker :=
  arithmeticUnramifiedAdjointClasses_firstOrder_inertia_iff a ρ hρ P hP τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousFixedDeterminantClasses_firstOrder_iff`. -/
theorem actual_continuous_fixed_determinant_classes_continuousFixedDeterminantClasses_firstOrder_iff_source
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ continuousFixedDeterminantClasses ρ hρ ↔
      ∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val) :=
  continuousFixedDeterminantClasses_firstOrder_iff ρ hρ τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff`. -/
theorem actual_arithmetic_unramified_fixed_determinant_classes_arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P ↔
        (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
          rationalArithmeticInertia a P ≤ τ.val.ker :=
  arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff a ρ hρ P hP τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `arithmeticLocalFirstOrderClass_eq_iff`. -/
theorem actual_arithmetic_local_first_order_classes_arithmeticLocalFirstOrderClass_eq_iff_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ υ : ArithmeticLocalFirstOrderLift a ρ P) :
    arithmeticLocalFirstOrderClass a ρ hρ P hP τ = arithmeticLocalFirstOrderClass a ρ hρ P hP υ ↔
      MatrixFirstOrderStrictlyConjugate ρ τ.val.val υ.val.val :=
  arithmeticLocalFirstOrderClass_eq_iff a ρ hρ P hP τ υ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Exact original-object consumer of `originalDualNumberFramedFiberEquiv_bijective`. -/
theorem actual_original_dual_number_framed_equiv_originalDualNumberFramedFiberEquiv_bijective_source
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι K) :
    Function.Bijective (originalDualNumberFramedFiberEquiv H ρ) :=
  originalDualNumberFramedFiberEquiv_bijective H ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Exact original-object consumer of `arithmeticLocalDualNumberFramedFiberEquiv_bijective`. -/
theorem actual_arithmetic_local_dual_number_framed_equiv_arithmeticLocalDualNumberFramedFiberEquiv_bijective_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Bijective (arithmeticLocalDualNumberFramedFiberEquiv a ρ P) :=
  arithmeticLocalDualNumberFramedFiberEquiv_bijective a ρ P

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Exact original-object consumer of `matrixAdjointCoboundary_traceFree_representative`. -/
theorem actual_trace_free_adjoint_coboundaries_matrixAdjointCoboundary_traceFree_representative_source
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    (X : Matrix ι ι K) :
    ∃ Y : Matrix ι ι K, Matrix.trace Y = 0 ∧
      ∀ g, groupCohomology.d₀₁ (matrixAdjointRep ρ) Y g =
        groupCohomology.d₀₁ (matrixAdjointRep ρ) X g :=
  matrixAdjointCoboundary_traceFree_representative hn ρ X

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `relativeDualNumberResidueEquiv_reduction`. -/
theorem actual_relative_dual_number_residue_relativeDualNumberResidueEquiv_reduction_source (O : Type*) [CommRing O] [IsLocalRing O]
    (z : DualNumber (IsLocalRing.ResidueField O)) :
    localCoefficientReduction (relativeDualNumberResidueEquiv O) z = z.fst :=
  relativeDualNumberResidueEquiv_reduction O z

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `relativeDualNumberFramedFiberEquiv_bijective`. -/
theorem actual_relative_dual_number_framed_equiv_relativeDualNumberFramedFiberEquiv_bijective_source
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Bijective (relativeDualNumberFramedFiberEquiv H ρ) :=
  relativeDualNumberFramedFiberEquiv_bijective H ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticRelativeLocalDualNumberFramedFiberEquiv_bijective`. -/
theorem actual_arithmetic_relative_local_dual_number_framed_equiv_arithmeticRelativeLocalDualNumberFramedFiberEquiv_bijective_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (ρ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Bijective (arithmeticRelativeLocalDualNumberFramedFiberEquiv a ρ δ hδ P) :=
  arithmeticRelativeLocalDualNumberFramedFiberEquiv_bijective a ρ δ hδ P

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalTangentPointClass_eq_iff`. -/
theorem actual_arithmetic_local_tangent_points_arithmeticLocalTangentPointClass_eq_iff_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (f g : ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalTangentPointClass a ha p hp hpa σ hσ δ hδ P hP f =
      arithmeticLocalTangentPointClass a ha p hp hpa σ hσ δ hδ P hP g ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP f).val.val
          (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP g).val.val :=
  arithmeticLocalTangentPointClass_eq_iff a ha p hp hpa σ hσ δ hδ P hP f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixTraceZeroAdjointCoboundary_val`. -/
theorem actual_trace_zero_adjoint_representation_matrixTraceZeroAdjointCoboundary_val_source (ρ : G →* GeneralLinearGroup ι R)
    (X : matrixTraceZeroSubmodule ι R) (g : G) :
    (groupCohomology.d₀₁ (matrixTraceZeroAdjointRep ρ) X g).val =
      groupCohomology.d₀₁ (matrixAdjointRep ρ) X.val g :=
  matrixTraceZeroAdjointCoboundary_val ρ X g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousTraceZeroCocycleEquiv_bijective`. -/
theorem actual_continuous_trace_zero_cocycles_continuousTraceZeroCocycleEquiv_bijective_source (ρ : G →* GeneralLinearGroup ι R) :
    Function.Bijective (continuousTraceZeroCocycleEquiv ρ) :=
  continuousTraceZeroCocycleEquiv_bijective ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousTraceZeroCocycleInclusion_mem_coboundaries_iff`. -/
theorem actual_continuous_trace_zero_coboundaries_continuousTraceZeroCocycleInclusion_mem_coboundaries_iff_source
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousTraceZeroCocycleInclusion ρ c ∈ continuousMatrixAdjointCoboundaries ρ hρ ↔
      c ∈ continuousTraceZeroAdjointCoboundaries ρ hρ :=
  continuousTraceZeroCocycleInclusion_mem_coboundaries_iff hn ρ hρ c

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousTraceZeroH1FixedDeterminantEquiv_bijective`. -/
theorem actual_continuous_trace_zero_cohomology_continuousTraceZeroH1FixedDeterminantEquiv_bijective_source
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Function.Bijective (continuousTraceZeroH1FixedDeterminantEquiv hn ρ hρ) :=
  continuousTraceZeroH1FixedDeterminantEquiv_bijective hn ρ hρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `originalCoefficientMap_continuous_of_topology_eq`. -/
theorem actual_original_coefficient_automatic_continuity_originalCoefficientMap_continuous_of_topology_eq_source
    [TopologicalSpace R] [TopologicalSpace A]
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : R →ₐ[O] A)
    (hres : (localCoefficientReduction eA).comp f = localCoefficientReduction eR) :
    Continuous f :=
  originalCoefficientMap_continuous_of_topology_eq hR hA eR eA f hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalResidueDerivationEquiv_apply`. -/
theorem actual_relative_dual_number_derivations_originalResidueDerivationEquiv_apply_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueDerivations eR) (r : R) :
    (originalResidueDerivationEquiv eR d).val r =
      (d r : DualNumber (IsLocalRing.ResidueField O)) + originalResidueConstantDualLift eR r :=
  originalResidueDerivationEquiv_apply eR d r

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]

/-- Exact original-object consumer of `originalResidueDerivationContinuousFiberEquiv_bijective`. -/
theorem actual_original_relative_coefficient_fiber_equiv_originalResidueDerivationContinuousFiberEquiv_bijective_source
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Bijective (originalResidueDerivationContinuousFiberEquiv hR eR) :=
  originalResidueDerivationContinuousFiberEquiv_bijective hR eR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]

/-- Exact original-object consumer of `originalResidueCotangentContinuousFiberEquiv_bijective`. -/
theorem actual_original_relative_cotangent_points_originalResidueCotangentContinuousFiberEquiv_bijective_source
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Bijective (originalResidueCotangentContinuousFiberEquiv hR eR) :=
  originalResidueCotangentContinuousFiberEquiv_bijective hR eR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalResidueDerivationClass_eq_iff`. -/
theorem actual_arithmetic_local_residue_derivations_arithmeticLocalResidueDerivationClass_eq_iff_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d e : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP e ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val
          (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP e).val.val :=
  arithmeticLocalResidueDerivationClass_eq_iff a ha p hp hpa σ hσ δ hδ P hP d e

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalCotangentClass_eq_iff`. -/
theorem actual_arithmetic_local_cotangent_points_arithmeticLocalCotangentClass_eq_iff_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d e : ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP e ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val
          (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP e).val.val :=
  arithmeticLocalCotangentClass_eq_iff a ha p hp hpa σ hσ δ hδ P hP d e

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalResidueDerivationFirstOrderLift_cocycle`. -/
theorem actual_original_residue_derivation_matrices_originalResidueDerivationFirstOrderLift_cocycle_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) (g : G) :
    matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres d) g =
      originalResidueDerivationMatrix eR ρ d g * ((σ g)⁻¹).val :=
  originalResidueDerivationFirstOrderLift_cocycle eR ρ σ hres d g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [IsTopologicalRing R] in
/-- Exact original-object consumer of `originalResidueDerivationContinuousCocycleLinearMap_apply`. -/
theorem actual_original_residue_derivation_continuous_cocycles_originalResidueDerivationContinuousCocycleLinearMap_apply_source
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) (g : G) :
    (originalResidueDerivationContinuousCocycleLinearMap hR eR ρ hρ σ hσ hres d).val g =
      originalResidueDerivationMatrix eR ρ d g * ((σ g)⁻¹).val :=
  originalResidueDerivationContinuousCocycleLinearMap_apply hR eR ρ hρ σ hσ hres d g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalResidueDerivationClassLinearMap_surjective`. -/
theorem actual_arithmetic_local_derivation_linearity_arithmeticLocalResidueDerivationClassLinearMap_surjective_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalResidueDerivationClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  arithmeticLocalResidueDerivationClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalResidueCotangentDerivationLinearEquiv_point`. -/
theorem actual_original_residue_cotangent_linearity_originalResidueCotangentDerivationLinearEquiv_point_source
    [TopologicalSpace R]
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueCotangentMaps eR) :
    originalResidueDerivationContinuousFiberEquiv hR eR
      (originalResidueCotangentDerivationLinearEquiv eR d) =
        originalResidueCotangentContinuousFiberEquiv hR eR d :=
  originalResidueCotangentDerivationLinearEquiv_point hR eR d

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalCotangentClassLinearMap_surjective`. -/
theorem actual_arithmetic_local_cotangent_linearity_arithmeticLocalCotangentClassLinearMap_surjective_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  arithmeticLocalCotangentClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable (O R : Type*) [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `relativeMaximalCotangent_finite`. -/
theorem actual_relative_maximal_cotangent_relativeMaximalCotangent_finite_source [IsNoetherianRing R] :
    Module.Finite (IsLocalRing.ResidueField R) (RelativeMaximalCotangent O R) :=
  relativeMaximalCotangent_finite O R

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `relativeMaximalCotangentDerivation_surjective`. -/
theorem actual_relative_maximal_cotangent_derivation_relativeMaximalCotangentDerivation_surjective_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Surjective (relativeMaximalCotangentDerivation eR) :=
  relativeMaximalCotangentDerivation_surjective eR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R M : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [AddCommGroup M] [Module R M] [Module O M]

variable [IsScalarTower O R M]

/-- Exact original-object consumer of `relativeMaximalCotangentDerivationEquiv_apply`. -/
theorem actual_relative_maximal_cotangent_universal_relativeMaximalCotangentDerivationEquiv_apply_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (f : RelativeMaximalCotangent O R →ₗ[R] M) (r : R) :
    relativeMaximalCotangentDerivationEquiv eR hM f r =
      f (relativeMaximalCotangentDerivation eR r) :=
  relativeMaximalCotangentDerivationEquiv_apply eR hM f r

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalResidueMaximalCotangentLinearEquiv_apply`. -/
theorem actual_original_residue_maximal_cotangent_originalResidueMaximalCotangentLinearEquiv_apply_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) (r : R) :
    originalResidueMaximalCotangentLinearEquiv eR f (KaehlerDifferential.D O R r) =
      f (relativeMaximalCotangentDerivation eR r) :=
  originalResidueMaximalCotangentLinearEquiv_apply eR f r

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalMaximalCotangentClassLinearMap_eq_iff`. -/
theorem actual_arithmetic_local_maximal_cotangent_arithmeticLocalMaximalCotangentClassLinearMap_eq_iff_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (f g : ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP f =
      arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP g ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalMaximalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP f).val.val
          (arithmeticLocalMaximalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP g).val.val :=
  arithmeticLocalMaximalCotangentClassLinearMap_eq_iff a ha p hp hpa σ hσ δ hδ P hP f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalMaximalCotangentDualLinearEquiv_apply`. -/
theorem actual_original_relative_cotangent_dual_originalMaximalCotangentDualLinearEquiv_apply_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) (x : RelativeMaximalCotangent O R) :
    originalMaximalCotangentDualLinearEquiv eR f x = (f x).val.snd :=
  originalMaximalCotangentDualLinearEquiv_apply eR f x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `originalRelativeMaximalCotangentDual_finite`. -/
theorem actual_original_relative_cotangent_dual_finiteness_originalRelativeMaximalCotangentDual_finite_source [IsNoetherianRing R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module.Finite (IsLocalRing.ResidueField O) (OriginalRelativeMaximalCotangentDual eR) :=
  originalRelativeMaximalCotangentDual_finite eR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalClass_finrank_le_cotangent`. -/
theorem actual_arithmetic_local_cotangent_dual_arithmeticLocalClass_finrank_le_cotangent_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     letI : AddCommMonoid (RelativeMaximalCotangent O
       (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) :=
         (instAddCommGroupRelativeMaximalCotangent O
           (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toAddCommMonoid
     letI := originalMaximalCotangentResidueModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
     Module.finrank (IsLocalRing.ResidueField O)
       (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) ≤
         Module.finrank (IsLocalRing.ResidueField O)
           (RelativeMaximalCotangent O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))) :=
  arithmeticLocalClass_finrank_le_cotangent a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι K : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K] [IsTopologicalRing K]

/-- Exact original-object consumer of `continuousTraceZeroH1Restriction_eq_zero_iff`. -/
theorem actual_continuous_trace_zero_restriction_continuousTraceZeroH1Restriction_eq_zero_iff_source
    (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (φ : H →* G) (hφ : Continuous φ) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousTraceZeroH1Restriction ρ hρ φ hφ x = 0 ↔
      continuousMatrixAdjointH1Restriction ρ hρ φ hφ
        (continuousTraceZeroH1Inclusion ρ hρ x) = 0 :=
  continuousTraceZeroH1Restriction_eq_zero_iff hn ρ hρ φ hφ x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- Exact original-object consumer of `arithmeticUnramifiedTraceZeroClasses_finiteDimensional`. -/
theorem actual_arithmetic_unramified_trace_zero_classes_arithmeticUnramifiedTraceZeroClasses_finiteDimensional_source
    [Finite K] [DiscreteTopology K] (hn : (Fintype.card ι : K) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.Finite K (arithmeticUnramifiedTraceZeroClasses a ρ hρ P) :=
  arithmeticUnramifiedTraceZeroClasses_finiteDimensional hn a ha p hp hpa ρ hρ P

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticTraceZeroLocalClass_finrank_le_cotangent`. -/
theorem actual_arithmetic_trace_zero_cotangent_arithmeticTraceZeroLocalClass_finrank_le_cotangent_source
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     letI : AddCommMonoid (RelativeMaximalCotangent O
       (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) :=
         (instAddCommGroupRelativeMaximalCotangent O
           (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toAddCommMonoid
     letI := originalMaximalCotangentResidueModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
     Module.finrank (IsLocalRing.ResidueField O)
       (arithmeticUnramifiedTraceZeroClasses a σ hσ P.asIdeal) ≤
         Module.finrank (IsLocalRing.ResidueField O)
           (RelativeMaximalCotangent O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))) :=
  arithmeticTraceZeroLocalClass_finrank_le_cotangent hn a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `arithmeticLocalFirstOrderCocycleEquiv_bijective`. -/
theorem actual_arithmetic_local_first_order_cocycles_arithmeticLocalFirstOrderCocycleEquiv_bijective_source (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Function.Bijective (arithmeticLocalFirstOrderCocycleEquiv a ρ hρ P hP) :=
  arithmeticLocalFirstOrderCocycleEquiv_bijective a ρ hρ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalResidueDerivationLocalCocycleLinearMap_bijective`. -/
theorem actual_arithmetic_local_derivation_cocycles_arithmeticLocalResidueDerivationLocalCocycleLinearMap_bijective_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticLocalResidueDerivationLocalCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  arithmeticLocalResidueDerivationLocalCocycleLinearMap_bijective a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Exact original-object consumer of `arithmeticLocalFirstOrderCocycles_finrank`. -/
theorem actual_arithmetic_local_cocycle_classes_arithmeticLocalFirstOrderCocycles_finrank_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Module.finrank K (arithmeticLocalFirstOrderCocycles a ρ P) =
      Module.finrank K (arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P) +
        Module.finrank K (continuousMatrixAdjointCoboundaries ρ hρ) :=
  arithmeticLocalFirstOrderCocycles_finrank a ha p hp hpa ρ hρ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalRing K]

/-- Exact original-object consumer of `continuousMatrixAdjointCoboundaries_finrank_add_invariants`. -/
theorem actual_continuous_adjoint_coboundary_dimension_continuousMatrixAdjointCoboundaries_finrank_add_invariants_source
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Module.finrank K (continuousMatrixAdjointCoboundaries ρ hρ) +
      Module.finrank K (matrixAdjointRepresentation ρ).invariants = Fintype.card ι ^ 2 :=
  continuousMatrixAdjointCoboundaries_finrank_add_invariants ρ hρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalCotangentDual_finrank_add_invariants`. -/
theorem actual_arithmetic_local_cotangent_dimension_arithmeticLocalCotangentDual_finrank_add_invariants_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) +
      Module.finrank (IsLocalRing.ResidueField O) (matrixAdjointRepresentation σ).invariants =
    Module.finrank (IsLocalRing.ResidueField O)
      (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 :=
  arithmeticLocalCotangentDual_finrank_add_invariants a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Exact original-object consumer of `matrixAdjointInvariant_eq_scalar`. -/
theorem actual_matrix_adjoint_schur_matrixAdjointInvariant_eq_scalar_source [IsAlgClosed K]
    (ρ : G →* GeneralLinearGroup ι K) [Representation.IsIrreducible (matrixStandardRepresentation ρ)]
    (X : (matrixAdjointRepresentation ρ).invariants) :
    ∃ c : K, X.val = c • (1 : Matrix ι ι K) :=
  matrixAdjointInvariant_eq_scalar ρ X

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L]

/-- Exact original-object consumer of `matrixAdjointInvariant_eq_scalar_of_extension`. -/
theorem actual_matrix_adjoint_scalar_descent_matrixAdjointInvariant_eq_scalar_of_extension_source [Nonempty ι] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))]
    (X : (matrixAdjointRepresentation ρ).invariants) :
    ∃ c : K, X.val = c • (1 : Matrix ι ι K) :=
  matrixAdjointInvariant_eq_scalar_of_extension (L := L) ρ X

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

variable (L : Type) [Field L] [Algebra K L] [IsAlgClosed L] [Nonempty ι]

/-- Exact original-object consumer of `matrixAdjointInvariants_finrank_of_extension`. -/
theorem actual_matrix_adjoint_invariant_dimension_matrixAdjointInvariants_finrank_of_extension_source
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    Module.finrank K (matrixAdjointRepresentation ρ).invariants = 1 :=
  matrixAdjointInvariants_finrank_of_extension L ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalCotangentDual_finrank_of_absoluteIrreducible`. -/
theorem actual_arithmetic_absolutely_irreducible_cotangent_arithmeticLocalCotangentDual_finrank_of_absoluteIrreducible_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) + 1 =
      Module.finrank (IsLocalRing.ResidueField O)
        (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 :=
  arithmeticLocalCotangentDual_finrank_of_absoluteIrreducible a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

/-- Exact original-object consumer of `matrixTraceZeroAdjointInvariants_eq_bot`. -/
theorem actual_trace_zero_adjoint_invariants_matrixTraceZeroAdjointInvariants_eq_bot_source
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    (matrixTraceZeroAdjointRepresentation ρ).invariants = ⊥ :=
  matrixTraceZeroAdjointInvariants_eq_bot (L := L) hn ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticLocalCotangent_traceZero_invariants_dimension`. -/
theorem actual_arithmetic_trace_zero_cotangent_dimension_arithmeticLocalCotangent_traceZero_invariants_dimension_source
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (matrixTraceZeroAdjointRepresentation σ).invariants = ⊥ ∧
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) + 1 =
      Module.finrank (IsLocalRing.ResidueField O)
        (arithmeticUnramifiedTraceZeroClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 :=
  arithmeticLocalCotangent_traceZero_invariants_dimension hn a ha p hp hpa σ hσ δ hδ P hP

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable (K A V : Type*) [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [IsSimpleModule A V] [FiniteDimensional K V] [IsAlgClosed K]

/-- Exact original-object consumer of `simpleModule_algebraAction_surjective`. -/
theorem actual_simple_module_burnside_simpleModule_algebraAction_surjective_source :
    Function.Surjective (Module.toModuleEnd K (S := A) V) :=
  simpleModule_algebraAction_surjective K A V

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]

/-- Exact original-object consumer of `irreducibleMatrixRepresentation_span_eq_top`. -/
theorem actual_matrix_representation_burnside_irreducibleMatrixRepresentation_span_eq_top_source
    (ρ : G →* GeneralLinearGroup ι K) [Representation.IsIrreducible (matrixStandardRepresentation ρ)] :
    Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤ :=
  irreducibleMatrixRepresentation_span_eq_top ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L]

/-- Exact original-object consumer of `matrixRepresentation_span_eq_top_of_extension`. -/
theorem actual_matrix_representation_spanning_descent_matrixRepresentation_span_eq_top_of_extension_source [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤ :=
  matrixRepresentation_span_eq_top_of_extension (L := L) ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R]

/-- Exact original-object consumer of `localMatrixRepresentation_span_eq_top`. -/
theorem actual_local_matrix_representation_spanning_localMatrixRepresentation_span_eq_top_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Submodule.span R (Set.range (fun g => (ρ g).val)) = ⊤ :=
  localMatrixRepresentation_span_eq_top (L := L) ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R] [Field L]
  [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]

/-- Exact original-object consumer of `localMatrixRepresentation_stabilizer_scalar_unit`. -/
theorem actual_local_matrix_representation_centralizer_localMatrixRepresentation_stabilizer_scalar_unit_source
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))]
    (U : GeneralLinearGroup ι R) (hU : ∀ g, U * ρ g = ρ g * U) :
    ∃ a : Rˣ, U = GeneralLinearGroup.scalar ι a :=
  localMatrixRepresentation_stabilizer_scalar_unit (L := L) ρ U hU

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticUnramifiedRepresentation_stabilizer_scalar_unit`. -/
theorem actual_arithmetic_unramified_matrix_spanning_arithmeticUnramifiedRepresentation_stabilizer_scalar_unit_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (U : GeneralLinearGroup ι (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))
    (hU : ∀ g, U * arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g =
      arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g * U) :
    ∃ u : (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)ˣ,
      U = GeneralLinearGroup.scalar ι u :=
  arithmeticUnramifiedRepresentation_stabilizer_scalar_unit a ha p hp hpa σ hσ δ hδ P hP U hU

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Field L] [Algebra (IsLocalRing.ResidueField B) L] [IsAlgClosed L]

/-- Exact original-object consumer of `matrixRepresentation_stabilizer_lifts`. -/
theorem actual_matrix_representation_stabilizer_lifting_matrixRepresentation_stabilizer_lifts_source
    (f : A →+* B) (hf : Function.Surjective f)
    (ρ : G →* GeneralLinearGroup ι A)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue B)).comp
          ((GeneralLinearGroup.map f).comp ρ))))]
    (U : GeneralLinearGroup ι B)
    (hU : ∀ g, U * GeneralLinearGroup.map f (ρ g) = GeneralLinearGroup.map f (ρ g) * U) :
    ∃ V : GeneralLinearGroup ι A,
      GeneralLinearGroup.map f V = U ∧ ∀ g, V * ρ g = ρ g * V :=
  matrixRepresentation_stabilizer_lifts (L := L) f hf ρ U hU

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]

/-- Exact original-object consumer of `coefficientFiberProduct_isLocalRing`. -/
theorem actual_local_coefficient_fiber_product_coefficientFiberProduct_isLocalRing_source [IsLocalRing A]
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    IsLocalRing (CoefficientFiberProduct f g) :=
  coefficientFiberProduct_isLocalRing f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

/-- Exact original-object consumer of `generalLinearCoefficientFiberProduct_existsUnique`. -/
theorem actual_matrix_coefficient_fiber_product_generalLinearCoefficientFiberProduct_existsUnique_source (f : A →+* C) (g : B →+* C)
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (h : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V) :
    ∃! W : GeneralLinearGroup ι (CoefficientFiberProduct f g),
      GeneralLinearGroup.map (coefficientFiberProductFst f g) W = U ∧
      GeneralLinearGroup.map (coefficientFiberProductSnd f g) W = V :=
  generalLinearCoefficientFiberProduct_existsUnique f g U V h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B C : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

/-- Exact original-object consumer of `coefficientFiberProductRepresentation_existsUnique`. -/
theorem actual_coefficient_fiber_product_representation_coefficientFiberProductRepresentation_existsUnique_source (f : A →+* C) (g : B →+* C)
    (ρA : G →* GeneralLinearGroup ι A) (ρB : G →* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA = (GeneralLinearGroup.map g).comp ρB) :
    ∃! ρ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ = ρA ∧
      (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ = ρB :=
  coefficientFiberProductRepresentation_existsUnique f g ρA ρB h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B C : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]
  [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]

/-- Exact original-object consumer of `continuousCoefficientFiberProductRepresentation_existsUnique`. -/
theorem actual_continuous_coefficient_fiber_product_continuousCoefficientFiberProductRepresentation_existsUnique_source
    (f : A →+* C) (g : B →+* C)
    (ρA : G →ₜ* GeneralLinearGroup ι A) (ρB : G →ₜ* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA.toMonoidHom =
      (GeneralLinearGroup.map g).comp ρB.toMonoidHom) :
    ∃! ρ : G →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom = ρA.toMonoidHom ∧
      (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom = ρB.toMonoidHom :=
  continuousCoefficientFiberProductRepresentation_existsUnique f g ρA ρB h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]

/-- Exact original-object consumer of `generalLinearGroup_strict_lift`. -/
theorem actual_local_coefficient_matrix_lifting_generalLinearGroup_strict_lift_source {K : Type} [CommRing K]
    (f : A →+* B) (hf : Function.Surjective f) [IsLocalHom f]
    (rA : A →+* K) (rB : B →+* K) (hr : rB.comp f = rA)
    (U : GeneralLinearGroup ι B) (hU : GeneralLinearGroup.map rB U = 1) :
    ∃ V : GeneralLinearGroup ι A,
      GeneralLinearGroup.map f V = U ∧ GeneralLinearGroup.map rA V = 1 :=
  generalLinearGroup_strict_lift f hf rA rB hr U hU

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A K : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing K]

/-- Exact original-object consumer of `matrixStrictlyConjugate_reduction`. -/
theorem actual_matrix_representation_strict_conjugacy_matrixStrictlyConjugate_reduction_source (r : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate r ρ σ) :
    (GeneralLinearGroup.map r).comp σ = (GeneralLinearGroup.map r).comp ρ :=
  matrixStrictlyConjugate_reduction r ρ σ h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B C K : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C] [CommRing K]

/-- Exact original-object consumer of `matrixStrictlyConjugate_fiberProduct_of_compatible_conjugators`. -/
theorem actual_coefficient_fiber_product_strict_conjugacy_matrixStrictlyConjugate_fiberProduct_of_compatible_conjugators_source
    (f : A →+* C) (g : B →+* C) (rA : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (hUV : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V)
    (hU : GeneralLinearGroup.map rA U = 1)
    (hA : ∀ x, GeneralLinearGroup.map (coefficientFiberProductFst f g) (σ x) =
      U * GeneralLinearGroup.map (coefficientFiberProductFst f g) (ρ x) * U⁻¹)
    (hB : ∀ x, GeneralLinearGroup.map (coefficientFiberProductSnd f g) (σ x) =
      V * GeneralLinearGroup.map (coefficientFiberProductSnd f g) (ρ x) * V⁻¹) :
    MatrixStrictlyConjugate (rA.comp (coefficientFiberProductFst f g)) ρ σ :=
  matrixStrictlyConjugate_fiberProduct_of_compatible_conjugators f g rA ρ σ U V hUV hU hA hB

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B C L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

variable [IsLocalRing B] [IsLocalRing C] [Field L]
  [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]

/-- Exact original-object consumer of `matrixStrictlyConjugate_fiberProduct_of_projections`. -/
theorem actual_coefficient_fiber_product_conjugator_alignment_matrixStrictlyConjugate_fiberProduct_of_projections_source {K : Type} [CommRing K]
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g)
    (ρ σ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue C)).comp
          ((GeneralLinearGroup.map g).comp
            ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ)))))]
    (rA : A →+* K) (rB : B →+* K)
    (hA : MatrixStrictlyConjugate rA
      ((GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ)
      ((GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp σ))
    (hB : MatrixStrictlyConjugate rB
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ)
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp σ)) :
    MatrixStrictlyConjugate (rA.comp (coefficientFiberProductFst f g)) ρ σ :=
  matrixStrictlyConjugate_fiberProduct_of_projections (L := L) f g hg ρ σ rA rB hA hB

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Exact original-object consumer of `matrixRepresentationConjugate_continuous`. -/
theorem actual_matrix_representation_conjugation_matrixRepresentationConjugate_continuous_source [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalRing A]
    (ρ : G →* GeneralLinearGroup ι A) (hρ : Continuous ρ) (U : GeneralLinearGroup ι A) :
    Continuous (matrixRepresentationConjugate ρ U) :=
  matrixRepresentationConjugate_continuous ρ hρ U

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B C K : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C] [CommRing K]
  [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Exact original-object consumer of `continuousCoefficientFiberProduct_exists_of_strictlyConjugate`. -/
theorem actual_continuous_strict_conjugacy_gluing_continuousCoefficientFiberProduct_exists_of_strictlyConjugate_source
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* K)
    (ρA : G →ₜ* GeneralLinearGroup ι A) (ρB : G →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom)) :
    ∃ ρ : G →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) :=
  continuousCoefficientFiberProduct_exists_of_strictlyConjugate f g hg rC ρA ρB h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `originalUnframedClass_eq_iff`. -/
theorem actual_original_unframed_deformation_classes_originalUnframedClass_eq_iff_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ τ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedClass eA H σ ρ = originalUnframedClass eA H σ τ ↔
      ∃ U : GeneralLinearGroup ι A,
        GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom U = 1 ∧
        ∀ x : H, τ.val x = U * ρ.val x * U⁻¹ :=
  originalUnframedClass_eq_iff eA H σ ρ τ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Exact original-object consumer of `originalUnframedPostcomp_comp`. -/
theorem actual_original_unframed_deformation_naturality_originalUnframedPostcomp_comp_source {C : Type u}
    [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hkres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (l : B →ₐ[O] C) (hl : Continuous l)
    (hlres : (localCoefficientReduction eC).comp l = localCoefficientReduction eB)
    (q : OriginalUnframedDeformationClass eA H σ) :
    originalUnframedPostcomp eB eC H σ l hl hlres
      (originalUnframedPostcomp eA eB H σ k hk hkres q) =
    originalUnframedPostcomp eA eC H σ (l.comp k) (hl.comp hk)
      (by
        apply AlgHom.ext
        intro x
        exact (DFunLike.congr_fun hlres (k x)).trans (DFunLike.congr_fun hkres x)) q :=
  originalUnframedPostcomp_comp eA eB eC H σ k hk hkres l hl hlres q

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O A B C : Type*} [CommRing O] [CommRing A] [CommRing B] [CommRing C]
  [Algebra O A] [Algebra O B] [Algebra O C]

variable [IsLocalRing O] [IsLocalRing A]

/-- Exact original-object consumer of `coefficientFiberProductReduction_fst`. -/
theorem actual_coefficient_fiber_product_residue_coefficientFiberProductReduction_fst_source (f : A →ₐ[O] C) (g : B →ₐ[O] C)
    [IsLocalHom g.toRingHom] (hg : Function.Surjective g)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA) =
       (localCoefficientReduction eA).comp (coefficientFiberProductFstAlgHom f g)) :=
  coefficientFiberProductReduction_fst f g hg eA

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable (R : Type*) [CommRing R] [IsLocalRing R] [Finite R]

/-- Exact original-object consumer of `finiteLocalCoefficient_complete`. -/
theorem actual_finite_local_coefficient_topology_finiteLocalCoefficient_complete_source :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
  finiteLocalCoefficient_complete R

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [Finite A] [Finite B]

/-- Exact original-object consumer of `finiteCoefficientFiberProduct_original_adicTopology_eq_product`. -/
theorem actual_finite_coefficient_fiber_product_topology_finiteCoefficientFiberProduct_original_adicTopology_eq_product_source
    [IsLocalRing B] [WithIdeal A] [WithIdeal B]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology =
       (inferInstance : TopologicalSpace (CoefficientFiberProduct f g))) :=
  finiteCoefficientFiberProduct_original_adicTopology_eq_product hA hB f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O A B : Type*} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

variable {C : Type*} [CommRing C] [IsLocalRing C] [Algebra O C]

/-- Exact original-object consumer of `coefficientFiberProductReduction_snd`. -/
theorem actual_coefficient_fiber_product_residue_compatibility_coefficientFiberProductReduction_snd_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA) =
       (localCoefficientReduction eB).comp (coefficientFiberProductSndAlgHom f g)) :=
  coefficientFiberProductReduction_snd eA eB eC f g hg hfres hgres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]

/-- Exact original-object consumer of `originalFiniteFiberProductFramed_exists`. -/
theorem actual_original_finite_fiber_product_framed_gluing_originalFiniteFiberProductFramed_exists_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρA : OriginalContinuousFramedFiber eA H σ)
    (ρB : OriginalContinuousFramedFiber eB H σ)
    (h : MatrixStrictlyConjugate (localCoefficientReduction eC).toRingHom
      ((GeneralLinearGroup.map g.toRingHom).comp ρB.val.toMonoidHom)
      ((GeneralLinearGroup.map f.toRingHom).comp ρA.val.toMonoidHom)) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       ⟨IsLocalRing.maximalIdeal _⟩
     letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       (IsLocalRing.maximalIdeal _).adicTopology
     ∃ ρ : OriginalContinuousFramedFiber (coefficientFiberProductResidueEquiv f g hg eA) H σ,
       (GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp
           ρ.val.toMonoidHom = ρA.val.toMonoidHom ∧
       MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom ρB.val.toMonoidHom
         ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
           ρ.val.toMonoidHom)) :=
  originalFiniteFiberProductFramed_exists hA hB eA eB eC f g hg hgres H σ ρA ρB h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [Finite A] [Finite B] [WithIdeal A] [WithIdeal B]

/-- Exact original-object consumer of `finiteCoefficientFiberProductSnd_adic_continuous`. -/
theorem actual_finite_coefficient_fiber_product_projection_topology_finiteCoefficientFiberProductSnd_adic_continuous_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     @Continuous (CoefficientFiberProduct f g) B
       (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology
       inferInstance (coefficientFiberProductSnd f g)) :=
  finiteCoefficientFiberProductSnd_adic_continuous hA hB f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]

/-- Exact original-object consumer of `originalCoefficientFiberProductClassSnd_eq_iff`. -/
theorem actual_original_coefficient_fiber_product_classes_originalCoefficientFiberProductClassSnd_eq_iff_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ τ : OriginalCoefficientFiberProductFramedFiber eA f g hg H σ) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       ⟨IsLocalRing.maximalIdeal _⟩
     letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       (IsLocalRing.maximalIdeal _).adicTopology
     originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ ρ) =
       originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ τ) ↔
     MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom
       ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp ρ.val.toMonoidHom)
       ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp τ.val.toMonoidHom)) :=
  originalCoefficientFiberProductClassSnd_eq_iff hA hB eA eB eC f g hg hfres hgres H σ ρ τ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

/-- Exact original-object consumer of `originalFramedFiber_coefficient_trueResidue`. -/
theorem actual_original_framed_true_residue_transport_originalFramedFiber_coefficient_trueResidue_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    (GeneralLinearGroup.map (IsLocalRing.residue B)).comp
        ((GeneralLinearGroup.map k.toRingHom).comp ρ.val.toMonoidHom) =
      (GeneralLinearGroup.map eB.symm.toRingHom).comp σ :=
  originalFramedFiber_coefficient_trueResidue eA eB k hres H σ ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A B C L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]
  [Field L] [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]

/-- Exact original-object consumer of `originalCoefficientFiberProductClass_projections_injective`. -/
theorem actual_original_coefficient_fiber_product_class_injectivity_originalCoefficientFiberProductClass_projections_injective_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((GeneralLinearGroup.map eC.symm.toRingHom).comp σ)))] :
    Function.Injective (fun q : OriginalCoefficientFiberProductClass eA f g hg H σ =>
      (originalCoefficientFiberProductClassFst hA hB eA f g hg H σ q,
       originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ q)) :=
  originalCoefficientFiberProductClass_projections_injective (L := L) hA hB eA eB eC f g hg hfres hgres H σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Exact original-object consumer of `finiteOriginalUnframedPostcomp_comp`. -/
theorem actual_finite_original_coefficient_class_maps_finiteOriginalUnframedPostcomp_comp_source [Finite B] {C : Type u}
    [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B)
    (hkres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (l : B →ₐ[O] C)
    (hlres : (localCoefficientReduction eC).comp l = localCoefficientReduction eB)
    (q : OriginalUnframedDeformationClass eA H σ) :
    finiteOriginalUnframedPostcomp hB eB eC H σ l hlres
      (finiteOriginalUnframedPostcomp hA eA eB H σ k hkres q) =
    finiteOriginalUnframedPostcomp hA eA eC H σ (l.comp k)
      (by
        apply AlgHom.ext
        intro x
        exact (DFunLike.congr_fun hlres (k x)).trans (DFunLike.congr_fun hkres x)) q :=
  finiteOriginalUnframedPostcomp_comp hA hB eA eB eC H σ k hkres l hlres q

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]

/-- Exact original-object consumer of `originalCoefficientClassFiberProductMap_injective`. -/
theorem actual_original_coefficient_class_fiber_product_originalCoefficientClassFiberProductMap_injective_source {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((GeneralLinearGroup.map eC.symm.toRingHom).comp σ)))] :
    Function.Injective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ) :=
  originalCoefficientClassFiberProductMap_injective (L := L) hA hB eA eB eC f g hg hfres hgres H σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]

/-- Exact original-object consumer of `originalCoefficientClassFiberProductMap_bijective`. -/
theorem actual_original_coefficient_class_fiber_product_surjectivity_originalCoefficientClassFiberProductMap_bijective_source {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((GeneralLinearGroup.map eC.symm.toRingHom).comp σ)))] :
    Function.Bijective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ) :=
  originalCoefficientClassFiberProductMap_bijective (L := L) hA hB eA eB eC f g hg hfres hgres H σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [WithIdeal R]

/-- Exact original-object consumer of `closedCoefficientSubalgebra_isLocalRing`. -/
theorem actual_closed_coefficient_subalgebra_locality_closedCoefficientSubalgebra_isLocalRing_source
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) : IsLocalRing S :=
  closedCoefficientSubalgebra_isLocalRing hR eR S hS

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientSubalgebraReduction_eq`. -/
theorem actual_coefficient_subalgebra_residue_coefficientSubalgebraReduction_eq_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom] :
    localCoefficientReduction (coefficientSubalgebraResidueEquiv eR S) =
      (localCoefficientReduction eR).comp S.val :=
  coefficientSubalgebraReduction_eq eR S

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `eqOn_closedMatrixTraceAlgebra_of_strictConjugate`. -/
theorem actual_closed_matrix_trace_algebra_eqOn_closedMatrixTraceAlgebra_of_strictConjugate_source {B K : Type*}
    [CommRing B] [Algebra O B] [CommRing K] [TopologicalSpace B] [T2Space B]
    (ρ : G →* GeneralLinearGroup ι R) (f g : R →ₐ[O] B)
    (hf : Continuous f) (hg : Continuous g) (r : B →+* K)
    (h : MatrixStrictlyConjugate r
      ((GeneralLinearGroup.map f.toRingHom).comp ρ)
      ((GeneralLinearGroup.map g.toRingHom).comp ρ)) :
    Set.EqOn f g (closedMatrixTraceAlgebra (O := O) ρ : Set R) :=
  eqOn_closedMatrixTraceAlgebra_of_strictConjugate ρ f g hf hg r h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S : Type*} [Ring R] [Ring S]

/-- Exact original-object consumer of `idempotentNewtonStep_error`. -/
theorem actual_idempotent_newton_step_idempotentNewtonStep_error_source (x : R) :
    (idempotentNewtonStep x) ^ 2 - idempotentNewtonStep x =
      (x ^ 2 - x) ^ 2 * (4 * (x ^ 2 - x) - 3) :=
  idempotentNewtonStep_error x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- Exact original-object consumer of `closedMatrixTraceReduction_eq`. -/
theorem actual_closed_matrix_trace_coefficient_ring_closedMatrixTraceReduction_eq_source
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) :
    letI := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
    localCoefficientReduction (closedMatrixTraceResidueEquiv hR eR ρ) =
      (localCoefficientReduction eR).comp (closedMatrixTraceAlgebra (O := O) ρ).val :=
  closedMatrixTraceReduction_eq hR eR ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `fullMatrixTracePairing_bijective`. -/
theorem actual_full_matrix_trace_pairing_fullMatrixTracePairing_bijective_source :
    Function.Bijective (fullMatrixTracePairing (ι := ι) (R := R)) :=
  fullMatrixTracePairing_bijective (ι := ι) (R := R)

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing R]

/-- Exact original-object consumer of `matrixTraceGram_det_isUnit`. -/
theorem actual_matrix_trace_gram_matrixTraceGram_det_isUnit_source (b : Basis κ R (Matrix ι ι R)) :
    IsUnit (matrixTraceGram b).det :=
  matrixTraceGram_det_isUnit b

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R]

/-- Exact original-object consumer of `localMatrixRepresentation_exists_basis`. -/
theorem actual_local_matrix_representation_basis_localMatrixRepresentation_exists_basis_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → G) (b : Basis κ R (Matrix ι ι R)),
      ∀ i, b i = (ρ (a i)).val :=
  localMatrixRepresentation_exists_basis (L := L) ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι κ O R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `matrix_mem_subalgebra_span_of_trace`. -/
theorem actual_matrix_trace_basis_coordinates_matrix_mem_subalgebra_span_of_trace_source
    (S : Subalgebra O R) [IsLocalHom S.val.toRingHom]
    (b : Basis κ R (Matrix ι ι R))
    (hb : ∀ i j, Matrix.trace (b i * b j) ∈ S)
    (X : Matrix ι ι R) (hX : ∀ j, Matrix.trace (X * b j) ∈ S) :
    X ∈ Submodule.span S (Set.range b) :=
  matrix_mem_subalgebra_span_of_trace S b hb X hX

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- Exact original-object consumer of `originalMatrixTraceBasis_exists`. -/
theorem actual_original_matrix_trace_basis_originalMatrixTraceBasis_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → G) (b : Basis κ R (Matrix ι ι R)),
      (∀ i, b i = (ρ (a i)).val) ∧
      ∀ x i, b.repr (ρ x).val i ∈ closedMatrixTraceAlgebra (O := O) ρ :=
  originalMatrixTraceBasis_exists (L := L) hR eR ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι κ O R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `isClosed_matrix_subalgebra_basis_span`. -/
theorem actual_matrix_basis_subalgebra_span_isClosed_matrix_subalgebra_basis_span_source [TopologicalSpace R] [IsTopologicalRing R]
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) (b : Basis κ R (Matrix ι ι R)) :
    IsClosed (Submodule.span S (Set.range b) : Set (Matrix ι ι R)) :=
  isClosed_matrix_subalgebra_basis_span S hS b

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι κ O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `isClosed_coefficientRepresentationMatrixAlgebra`. -/
theorem actual_coefficient_representation_matrix_algebra_isClosed_coefficientRepresentationMatrixAlgebra_source
    [TopologicalSpace R] [IsTopologicalRing R]
    (S : Subalgebra O R) (hS : IsClosed (S : Set R))
    (ρ : G →* GeneralLinearGroup ι R) (a : κ → G)
    (b : Basis κ R (Matrix ι ι R)) (hb : ∀ i, b i = (ρ (a i)).val)
    (hcoord : ∀ x i, b.repr (ρ x).val i ∈ S) :
    IsClosed (coefficientRepresentationMatrixAlgebra S ρ : Set (Matrix ι ι R)) :=
  isClosed_coefficientRepresentationMatrixAlgebra S hS ρ a b hb hcoord

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- Exact original-object consumer of `originalClosedTraceMatrixAlgebra_finite_free_closed`. -/
theorem actual_original_closed_trace_matrix_algebra_originalClosedTraceMatrixAlgebra_finite_free_closed_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Module.Finite (closedMatrixTraceAlgebra (O := O) ρ)
        (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ) ∧
      Module.Free (closedMatrixTraceAlgebra (O := O) ρ)
        (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ) ∧
      IsClosed (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ :
        Set (Matrix ι ι R)) :=
  originalClosedTraceMatrixAlgebra_finite_free_closed (L := L) hR eR ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixIdempotentNewtonSequence_error`. -/
theorem actual_matrix_idempotent_newton_bounds_matrixIdempotentNewtonSequence_error_source (I : Ideal R) (X : Matrix ι ι R)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ I) (n : ℕ) :
    ∀ i j, ((matrixIdempotentNewtonSequence X n) ^ 2 -
      matrixIdempotentNewtonSequence X n) i j ∈ I ^ (2 ^ n) :=
  matrixIdempotentNewtonSequence_error I X hX n

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R] [WithIdeal R]
  [IsPrecomplete (WithIdeal.i : Ideal R) R]

/-- Exact original-object consumer of `adicMatrixSequence_exists_limit_of_steps`. -/
theorem actual_adic_matrix_sequence_convergence_adicMatrixSequence_exists_limit_of_steps_source {ι : Type*} (u : ℕ → Matrix ι ι R)
    (hu : ∀ n i j, (u (n + 1) - u n) i j ∈ (WithIdeal.i : Ideal R) ^ n) :
    ∃ X : Matrix ι ι R, Tendsto u atTop (𝓝 X) :=
  adicMatrixSequence_exists_limit_of_steps u hu

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [WithIdeal R]

/-- Exact original-object consumer of `adicMatrixIdempotent_exists_mem_closedSubalgebra`. -/
theorem actual_adic_matrix_idempotent_lifting_adicMatrixIdempotent_exists_mem_closedSubalgebra_source
    [IsAdicComplete (WithIdeal.i : Ideal R) R]
    {O : Type*} [CommRing O] [Algebra O (Matrix ι ι R)]
    (S : Subalgebra O (Matrix ι ι R)) (hS : IsClosed (S : Set (Matrix ι ι R)))
    (X : Matrix ι ι R) (hXS : X ∈ S)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ (WithIdeal.i : Ideal R)) :
    ∃ E : Matrix ι ι R, E ∈ S ∧ E ^ 2 = E ∧
      ∀ i j, (E - X) i j ∈ (WithIdeal.i : Ideal R) :=
  adicMatrixIdempotent_exists_mem_closedSubalgebra S hS X hXS hX

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientRepresentationMatrixAlgebra_residue_surjective`. -/
theorem actual_coefficient_matrix_algebra_residue_coefficientRepresentationMatrixAlgebra_residue_surjective_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Function.Surjective ((RingHom.mapMatrix (IsLocalRing.residue R)).comp
      (coefficientRepresentationMatrixAlgebra S ρ).val.toRingHom) :=
  coefficientRepresentationMatrixAlgebra_residue_surjective (L := L) eR S ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- Exact original-object consumer of `originalTraceMatrixIdempotent_exists`. -/
theorem actual_original_trace_matrix_idempotent_originalTraceMatrixIdempotent_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    ∃ e : coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ,
      e ^ 2 = e ∧ (RingHom.mapMatrix (IsLocalRing.residue R)) e.val =
        Matrix.single i₀ i₀ 1 :=
  originalTraceMatrixIdempotent_exists (L := L) hR eR ρ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {S A : Type*} [CommRing S] [Ring A] [Algebra S A]

/-- Exact original-object consumer of `algebraIdempotentLeftIdeal_mem_ideal_smul`. -/
theorem actual_algebra_idempotent_left_ideal_algebraIdempotentLeftIdeal_mem_ideal_smul_source (I : Ideal S)
    (e : A) (he : e ^ 2 = e) (x : algebraIdempotentLeftIdeal (S := S) e)
    (hx : (x : A) ∈ I • (⊤ : Submodule S A)) :
    x ∈ I • (⊤ : Submodule S (algebraIdempotentLeftIdeal (S := S) e)) :=
  algebraIdempotentLeftIdeal_mem_ideal_smul I e he x hx

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixBasisCoordinates_mem_ideal_iff`. -/
theorem actual_matrix_basis_ideal_coordinates_matrixBasisCoordinates_mem_ideal_iff_source [Fintype κ]
    (I : Ideal R) (b : Basis κ R (Matrix ι ι R)) (X : Matrix ι ι R) :
    (∀ i j, X i j ∈ I) ↔ ∀ k, b.repr X k ∈ I :=
  matrixBasisCoordinates_mem_ideal_iff I b X

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι κ O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientRepresentationMatrixAlgebra_mem_maximal_smul`. -/
theorem actual_coefficient_matrix_algebra_reduction_kernel_coefficientRepresentationMatrixAlgebra_mem_maximal_smul_source
    [IsLocalRing R] (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (ρ : G →* GeneralLinearGroup ι R) (a : κ → G)
    (b : Basis κ R (Matrix ι ι R)) (hb : ∀ i, b i = (ρ (a i)).val)
    (hcoord : ∀ x i, b.repr (ρ x).val i ∈ S)
    (X : coefficientRepresentationMatrixAlgebra S ρ)
    (hX : ∀ i j, X.val i j ∈ IsLocalRing.maximalIdeal R) :
    X ∈ IsLocalRing.maximalIdeal S •
      (⊤ : Submodule S (coefficientRepresentationMatrixAlgebra S ρ)) :=
  coefficientRepresentationMatrixAlgebra_mem_maximal_smul S ρ a b hb hcoord X hX

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

/-- Exact original-object consumer of `matrix_eq_sum_single_column`. -/
theorem actual_matrix_unit_left_ideal_columns_matrix_eq_sum_single_column_source (X : Matrix ι ι K) (i₀ : ι)
    (hX : X * Matrix.single i₀ i₀ 1 = X) :
    X = ∑ i, X i i₀ • Matrix.single i i₀ 1 :=
  matrix_eq_sum_single_column X i₀ hX

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `matrixIdempotentLeftIdeal_span`. -/
theorem actual_matrix_idempotent_left_ideal_spanning_matrixIdempotentLeftIdeal_span_source
    (S : Subalgebra O R) [IsLocalRing S]
    (A : Subalgebra S (Matrix ι ι R)) [Module.Finite S A]
    (e : A) (he : e ^ 2 = e) (i₀ : ι)
    (hebar : (RingHom.mapMatrix (IsLocalRing.residue R)) e.val = Matrix.single i₀ i₀ 1)
    (hscalar : Function.Surjective (fun c : S => IsLocalRing.residue R c.val))
    (hker : ∀ x : A, (∀ i j, x.val i j ∈ IsLocalRing.maximalIdeal R) →
      x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S A))
    (v : ι → algebraIdempotentLeftIdeal (S := S) e)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i).val.val =
      Matrix.single i i₀ 1) :
    letI : Module S (algebraIdempotentLeftIdeal (S := S) e) :=
      (algebraIdempotentLeftIdeal (S := S) e).module
    Submodule.span S (Set.range v) = ⊤ :=
  matrixIdempotentLeftIdeal_span S A e he i₀ hebar hscalar hker v hv

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsLocalRing R]

/-- Exact original-object consumer of `residualMatrixColumns_linearIndependent`. -/
theorem actual_residual_matrix_column_independence_residualMatrixColumns_linearIndependent_source (v : ι → Matrix ι ι R) (i₀ : ι)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i) =
      Matrix.single i i₀ 1) : LinearIndependent R v :=
  residualMatrixColumns_linearIndependent v i₀ hv

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- Exact original-object consumer of `originalTraceLeftIdealBasis_exists`. -/
theorem actual_original_trace_left_ideal_basis_originalTraceLeftIdealBasis_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O) ρ
    let A := coefficientRepresentationMatrixAlgebra S ρ
    ∃ (e : A), e ^ 2 = e ∧
      (RingHom.mapMatrix (IsLocalRing.residue R)) e.val = Matrix.single i₀ i₀ 1 ∧
      letI : Module S (algebraIdempotentLeftIdeal (S := S) e) :=
        (algebraIdempotentLeftIdeal (S := S) e).module
      ∃ b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e),
        ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (b i).val.val =
          Matrix.single i i₀ 1 :=
  originalTraceLeftIdealBasis_exists (L := L) hR eR ρ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι S A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing S] [Ring A] [Algebra S A]

/-- Exact original-object consumer of `algebraIdempotentMatrixRepresentation_apply`. -/
theorem actual_algebra_idempotent_matrix_action_algebraIdempotentMatrixRepresentation_apply_source (σ : G →* A) (e : A)
    (b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) (g : G) (i j : ι) :
    (algebraIdempotentMatrixRepresentation σ e b g).val i j =
      b.repr (algebraIdempotentLeftAction e (σ g) (b j)) i :=
  algebraIdempotentMatrixRepresentation_apply σ e b g i j

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientRepresentationAlgebraHom_inclusion`. -/
theorem actual_coefficient_representation_algebra_hom_coefficientRepresentationAlgebraHom_inclusion_source (S : Subalgebra O R)
    (ρ : G →* GeneralLinearGroup ι R) :
    (coefficientRepresentationMatrixAlgebra S ρ).val.toRingHom.toMonoidHom.comp
        (coefficientRepresentationAlgebraHom S ρ) =
      (Units.coeHom (Matrix ι ι R)).comp ρ :=
  coefficientRepresentationAlgebraHom_inclusion S ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `matrixIdempotentBasis_intertwines`. -/
theorem actual_matrix_idempotent_basis_intertwiner_matrixIdempotentBasis_intertwines_source (S : Subalgebra O R)
    (A : Subalgebra S (Matrix ι ι R)) (σ : G →* A) (e : A)
    (b : letI : Module S (algebraIdempotentLeftIdeal (S := S) e) :=
      (algebraIdempotentLeftIdeal (S := S) e).module
      Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) (i₀ : ι) (g : G) :
    (σ g).val * residualColumnMatrix (fun i => (b i).val.val) i₀ =
      residualColumnMatrix (fun i => (b i).val.val) i₀ *
        (RingHom.mapMatrix S.val.toRingHom) (algebraIdempotentMatrixRepresentation σ e b g).val :=
  matrixIdempotentBasis_intertwines S A σ e b i₀ g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- Exact original-object consumer of `originalTraceRepresentationDescent_exists`. -/
theorem actual_original_trace_representation_descent_originalTraceRepresentationDescent_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    ∃ τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ :=
  originalTraceRepresentationDescent_exists (L := L) hR eR ρ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]
  [TopologicalSpace G] [TopologicalSpace R]

/-- Exact original-object consumer of `matrixStrictlyConjugate_subalgebra_continuous`. -/
theorem actual_coefficient_subalgebra_representation_continuity_matrixStrictlyConjugate_subalgebra_continuous_source [Group G] [IsTopologicalRing R]
    {K : Type*} [CommRing K] (r : R →+* K)
    (S : Subalgebra O R) (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : G →* GeneralLinearGroup ι S)
    (h : MatrixStrictlyConjugate r ((GeneralLinearGroup.map S.val.toRingHom).comp τ) ρ) :
    Continuous τ :=
  matrixStrictlyConjugate_subalgebra_continuous r S ρ hρ τ h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [TopologicalSpace G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- Exact original-object consumer of `originalContinuousTraceRepresentationDescent_exists`. -/
theorem actual_original_continuous_trace_representation_descent_originalContinuousTraceRepresentationDescent_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →ₜ* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ.toMonoidHom)))] (i₀ : ι) :
    ∃ τ : G →ₜ* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom) ρ.toMonoidHom :=
  originalContinuousTraceRepresentationDescent_exists (L := L) hR eR ρ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R]

/-- Exact original-object consumer of `adicCompletion_original_dense`. -/
theorem actual_adic_completion_original_density_adicCompletion_original_dense_source (I : Ideal R) (hI : I.FG)
    [TopologicalSpace (AdicCompletion I R)]
    (h : IsAdic (I.map (algebraMap R (AdicCompletion I R)))) :
    DenseRange (algebraMap R (AdicCompletion I R)) :=
  adicCompletion_original_dense I hI h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationCompletion_original_dense`. -/
theorem actual_residual_completion_original_density_residualRepresentationCompletion_original_dense_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    DenseRange (algebraMap (ResidualRepresentationLocalRing ρ)
      (ResidualRepresentationCompletion ρ)) :=
  residualRepresentationCompletion_original_dense ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R L A : Type*} [CommRing O] [CommRing R] [CommRing L] [CommRing A]
  [Algebra O A] [Algebra R L]

/-- Exact original-object consumer of `localization_image_mem_subalgebra`. -/
theorem actual_localization_subalgebra_image_localization_image_mem_subalgebra_source (M : Submonoid R) [IsLocalization M L]
    (S : Subalgebra O A) (f : L →+* A)
    (hbase : ∀ r : R, f (algebraMap R L r) ∈ S)
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x) (x : L) : f x ∈ S :=
  localization_image_mem_subalgebra M S f hbase hunit x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing A] [Algebra O A]

/-- Exact original-object consumer of `representationCoordinate_image_mem_subalgebra`. -/
theorem actual_representation_coordinate_subalgebra_image_representationCoordinate_image_mem_subalgebra_source (S : Subalgebra O A)
    (f : RepresentationCoordinateAlgebra G ι O →ₐ[O] A)
    (hentry : ∀ g i j, f (representationCoordinateMatrix G ι O g i j) ∈ S)
    (x : RepresentationCoordinateAlgebra G ι O) : f x ∈ S :=
  representationCoordinate_image_mem_subalgebra S f hentry x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [Algebra O A] [TopologicalSpace A]

/-- Exact original-object consumer of `completedResidual_image_mem_subalgebra`. -/
theorem actual_completed_residual_subalgebra_image_completedResidual_image_mem_subalgebra_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (S : Subalgebra O A) (hS : IsClosed (S : Set A))
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x)
    (f : ResidualRepresentationCompletion ρ →ₐ[O] A) (hf : Continuous f)
    (hentry : ∀ g i j, f ((completedUniversalMatrixRepresentation ρ g).val i j) ∈ S)
    (x : ResidualRepresentationCompletion ρ) : f x ∈ S :=
  completedResidual_image_mem_subalgebra ρ S hS hunit f hf hentry x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientSubalgebra_isNoetherian_of_retraction`. -/
theorem actual_coefficient_subalgebra_retraction_coefficientSubalgebra_isNoetherian_of_retraction_source [IsNoetherianRing R]
    (S : Subalgebra O R) (f : R →ₐ[O] R) (hf : ∀ x, f x ∈ S)
    (hfix : ∀ x : S, f x = (x : R)) : IsNoetherianRing S :=
  coefficientSubalgebra_isNoetherian_of_retraction S f hf hfix

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing K] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- Exact original-object consumer of `originalTraceAlgebra_isNoetherian_of_endomorphism`. -/
theorem actual_original_trace_endomorphism_retraction_originalTraceAlgebra_isNoetherian_of_endomorphism_source [IsNoetherianRing R]
    (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (f : R →ₐ[O] R) (hf : Continuous f)
    (h : MatrixStrictlyConjugate r ((GeneralLinearGroup.map f.toRingHom).comp ρ) ρ)
    (himage : ∀ x, f x ∈ closedMatrixTraceAlgebra (O := O) ρ) :
    IsNoetherianRing (closedMatrixTraceAlgebra (O := O) ρ) :=
  originalTraceAlgebra_isNoetherian_of_endomorphism r ρ f hf h himage

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentation_conjugating_endomorphism_exists`. -/
theorem actual_completed_presentation_conjugating_endomorphism_completedPresentation_conjugating_endomorphism_exists_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    (τ : H →ₜ* GeneralLinearGroup ι (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      τ.toMonoidHom (completedPresentationRepresentation ρ H q hq)) :
    ∃ f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O]
        CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker,
      (∀ h : H, GeneralLinearGroup.map f.toRingHom
        (completedPresentationRepresentation ρ H q hq h) = τ h) ∧ Continuous f :=
  completedPresentation_conjugating_endomorphism_exists ρ H q hq hR τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [Algebra O A] [TopologicalSpace A]

/-- Exact original-object consumer of `completedPresentation_image_mem_subalgebra`. -/
theorem actual_completed_presentation_subalgebra_image_completedPresentation_image_mem_subalgebra_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (S : Subalgebra O A) (hS : IsClosed (S : Set A))
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x)
    (f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A)
    (hf : Continuous f)
    (hentry : ∀ h i j, f ((completedPresentationRepresentation ρ H q hq h).val i j) ∈ S)
    (x : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker) : f x ∈ S :=
  completedPresentation_image_mem_subalgebra ρ H q hq S hS hunit f hf hentry x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientRetraction_maximalIdeal_pow_comap`. -/
theorem actual_coefficient_retraction_ideal_powers_coefficientRetraction_maximalIdeal_pow_comap_source
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).comap S.val.toRingHom =
      (IsLocalRing.maximalIdeal S) ^ n :=
  coefficientRetraction_maximalIdeal_pow_comap S f hfix n

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `coefficientRetraction_isAdicComplete`. -/
theorem actual_coefficient_retraction_adic_topology_coefficientRetraction_isAdicComplete_source [WithIdeal R]
    [IsAdicComplete (WithIdeal.i : Ideal R) R]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (hS : IsClosed (S : Set R))
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
  coefficientRetraction_isAdicComplete hR S hS f hfix

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type} [Group G] [TopologicalSpace G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [t : TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Exact original-object consumer of `originalAdicContinuousTraceRepresentationDescent_exists`. -/
theorem actual_original_adic_trace_representation_descent_originalAdicContinuousTraceRepresentationDescent_exists_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →ₜ* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ.toMonoidHom)))] (i₀ : ι) :
    ∃ τ : G →ₜ* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom) ρ.toMonoidHom :=
  originalAdicContinuousTraceRepresentationDescent_exists (L := L) hR eR ρ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [t : TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `originalAdicCoefficientSubalgebra_isLocalRing`. -/
theorem actual_original_adic_coefficient_subalgebra_locality_originalAdicCoefficientSubalgebra_isLocalRing_source
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) : IsLocalRing S :=
  originalAdicCoefficientSubalgebra_isLocalRing hR eR S hS

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationTraceAlgebra_isNoetherian`. -/
theorem actual_completed_presentation_trace_retraction_completedPresentationTraceAlgebra_isNoetherian_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue
          (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))).comp
          (completedPresentationRepresentation ρ H q hq))))] (i₀ : ι) :
    IsNoetherianRing (closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation ρ H q hq)) :=
  completedPresentationTraceAlgebra_isNoetherian (L := L) ρ H q hq hR i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [t : TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Exact original-object consumer of `originalAdicCoefficientRetraction_localTopology`. -/
theorem actual_original_adic_coefficient_retraction_completeness_originalAdicCoefficientRetraction_localTopology_source
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (hS : IsClosed (S : Set R))
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) :
    IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
  originalAdicCoefficientRetraction_localTopology hR S hS f hfix

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationTraceAlgebra_localData`. -/
theorem actual_completed_presentation_trace_local_data_completedPresentationTraceAlgebra_localData_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue
          (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))).comp
          (completedPresentationRepresentation ρ H q hq))))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)
    letI : IsLocalRing S := originalAdicCoefficientSubalgebra_isLocalRing hR
      (completedPresentationResidueEquiv ρ q.toMonoidHom.ker) S
      (isClosed_closedMatrixTraceAlgebra (completedPresentationRepresentation ρ H q hq))
    IsNoetherianRing S ∧ IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] S,
        (∀ x : S, f x = x) ∧ Continuous f :=
  completedPresentationTraceAlgebra_localData (L := L) ρ H q hq hR i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L]

/-- Exact original-object consumer of `trueResidueScalarExtension_eq`. -/
theorem actual_true_residue_scalar_extension_trueResidueScalarExtension_eq_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    letI : Algebra (IsLocalRing.ResidueField R) L :=
      ((algebraMap (IsLocalRing.ResidueField O) L).comp eR.toRingHom).toAlgebra
    matrixCoefficientExtension (L := L)
      ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ) =
        matrixCoefficientExtension (L := L) σ :=
  trueResidueScalarExtension_eq (L := L) eR ρ σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `originalPresentedTraceAlgebra_localData`. -/
theorem actual_original_presented_trace_local_data_originalPresentedTraceAlgebra_localData_source
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ.toMonoidHom))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation (originalPresentedResidualRestriction H q σ) H q hq)
    ∃ hlocal : IsLocalRing S,
      letI := hlocal
      IsNoetherianRing S ∧ IsAdic (IsLocalRing.maximalIdeal S) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
        ∃ f : OriginalPresentedCoefficientRing H q σ →ₐ[O] S,
          (∀ x : S, f x = x) ∧ Continuous f :=
  originalPresentedTraceAlgebra_localData (L := L) H q hq σ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing K] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `descendedTraceCoefficientMaps_eq`. -/
theorem actual_descended_trace_coefficient_generation_descendedTraceCoefficientMaps_eq_source {A B : Type*} [CommRing A] [CommRing B]
    [Algebra O A] [TopologicalSpace A] [T2Space A]
    (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (h : MatrixStrictlyConjugate r
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ)
    (f g : closedMatrixTraceAlgebra (O := O) ρ →ₐ[O] A)
    (hf : Continuous f) (hg : Continuous g) (rA : A →+* B)
    (hfg : MatrixStrictlyConjugate rA
      ((GeneralLinearGroup.map f.toRingHom).comp τ)
      ((GeneralLinearGroup.map g.toRingHom).comp τ)) : f = g :=
  descendedTraceCoefficientMaps_eq r ρ τ h f g hf hg rA hfg

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B K L : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing K] [CommRing L]

omit [CommRing L] in
/-- Exact original-object consumer of `matrixStrictlyConjugate_map`. -/
theorem actual_matrix_strict_conjugacy_coefficient_change_matrixStrictlyConjugate_map_source (rA : A →+* K) (rB : B →+* K)
    (f : A →+* B) (hres : rB.comp f = rA)
    (ρ τ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate rA ρ τ) :
    MatrixStrictlyConjugate rB ((GeneralLinearGroup.map f).comp ρ)
      ((GeneralLinearGroup.map f).comp τ) :=
  matrixStrictlyConjugate_map rA rB f hres ρ τ h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedPresentationTraceCoefficient_exists_unique`. -/
theorem actual_completed_presentation_unframed_universality_completedPresentationTraceCoefficient_exists_unique_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →ₜ* GeneralLinearGroup ι
      (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      ((GeneralLinearGroup.map
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val.toRingHom).comp
          τ.toMonoidHom) (completedPresentationRepresentation ρ H q hq))
    (σ : H →ₜ* GeneralLinearGroup ι A)
    (hσ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      (profiniteMatrixRestriction (σ.comp q)) = ρ) :
    ∃! f : closedMatrixTraceAlgebra (O := O)
        (completedPresentationRepresentation ρ H q hq) →ₐ[O] A,
      Continuous f ∧
      (localCoefficientReduction eA).comp f =
        (localCoefficientReduction (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)).comp
          (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val ∧
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((GeneralLinearGroup.map f.toRingHom).comp τ.toMonoidHom) σ.toMonoidHom :=
  completedPresentationTraceCoefficient_exists_unique hA ρ H q hq eA τ hτ σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `originalPresentedTraceDescent_exists`. -/
theorem actual_original_presented_trace_descent_originalPresentedTraceDescent_exists_source
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ.toMonoidHom))] (i₀ : ι) :
    letI := originalPresentedCoefficientRing_isLocal H q σ
    let υ := completedPresentationRepresentation (originalPresentedResidualRestriction H q σ) H q hq
    let S := closedMatrixTraceAlgebra (O := O) υ
    let eR := completedPresentationResidueEquiv
      (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker
    ∃ τ : H →ₜ* GeneralLinearGroup ι S,
      MatrixStrictlyConjugate (IsLocalRing.residue (OriginalPresentedCoefficientRing H q σ))
        ((GeneralLinearGroup.map S.val.toRingHom).comp τ.toMonoidHom) υ ∧
      (GeneralLinearGroup.map ((localCoefficientReduction eR).comp S.val).toRingHom).comp
        τ.toMonoidHom = σ.toMonoidHom :=
  originalPresentedTraceDescent_exists (L := L) H q hq σ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `originalCoefficientRepresentationClass_eq_iff`. -/
theorem actual_original_coefficient_representation_class_originalCoefficientRepresentationClass_eq_iff_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (f g : OriginalContinuousCoefficientFiber eR eA) :
    originalCoefficientRepresentationClass eR eA H σ τ hτ f =
        originalCoefficientRepresentationClass eR eA H σ τ hτ g ↔
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((GeneralLinearGroup.map f.val.toRingHom).comp τ.toMonoidHom)
        ((GeneralLinearGroup.map g.val.toRingHom).comp τ.toMonoidHom) :=
  originalCoefficientRepresentationClass_eq_iff eR eA H σ τ hτ f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedTraceCoefficientClass_bijective`. -/
theorem actual_completed_trace_coefficient_class_bijection_completedTraceCoefficientClass_bijective_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsLocalRing (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq))]
    [IsLocalHom (closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation ρ H q hq)).val.toRingHom]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (σ₀ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ₀ : (σ₀.comp q.toMonoidHom).comp
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom = ρ)
    (τ : H →ₜ* GeneralLinearGroup ι
      (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      ((GeneralLinearGroup.map
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val.toRingHom).comp
          τ.toMonoidHom) (completedPresentationRepresentation ρ H q hq))
    (hτres : (GeneralLinearGroup.map (localCoefficientReduction
      (coefficientSubalgebraResidueEquiv (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))).toRingHom).comp
          τ.toMonoidHom = σ₀) :
    Function.Bijective (originalCoefficientRepresentationClass
      (coefficientSubalgebraResidueEquiv (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
      eA H σ₀ τ hτres) :=
  completedTraceCoefficientClass_bijective hA ρ H q hq eA σ₀ hσ₀ τ hτ hτres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `originalTraceUnframedUniversality_exists`. -/
theorem actual_original_trace_unframed_universality_originalTraceUnframedUniversality_exists_source
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ.toMonoidHom))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation (originalPresentedResidualRestriction H q σ) H q hq)
    ∃ hlocal : IsLocalRing S,
      letI := hlocal
      IsNoetherianRing S ∧ IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ (eS : IsLocalRing.ResidueField S ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι S)
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eS).toRingHom).comp
          τ.toMonoidHom = σ.toMonoidHom),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eS eA H
            σ.toMonoidHom τ hτres) :=
  originalTraceUnframedUniversality_exists (L := L) H q hq σ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O R A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Exact original-object consumer of `originalCoefficientRepresentationClass_natural`. -/
theorem actual_original_coefficient_representation_naturality_originalCoefficientRepresentationClass_natural_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedPostcomp eA eB H σ k hk hres
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) =
      originalCoefficientRepresentationClass eR eB H σ τ hτ
        (originalCoefficientFiberPostcomp eR eA eB k hk hres f) :=
  originalCoefficientRepresentationClass_natural eR eA eB H σ τ hτ k hk hres f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G H V : Type*} [Field K] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module K V]

/-- Exact original-object consumer of `representation_irreducible_of_restriction`. -/
theorem actual_representation_irreducibility_from_restriction_representation_irreducible_of_restriction_source (q : G →* H) (ρ : Representation K H V)
    [Representation.IsIrreducible (ρ.comp q)] : Representation.IsIrreducible ρ :=
  representation_irreducible_of_restriction q ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι R K O : Type*} [Group G] [Group H] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing K]

omit [CommRing K] in
/-- Exact original-object consumer of `closedMatrixTraceAlgebra_comp_surjective`. -/
theorem actual_matrix_strict_conjugacy_surjective_restriction_closedMatrixTraceAlgebra_comp_surjective_source [CommRing O] [Algebra O R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (q : G →* H) (hq : Function.Surjective q) (ρ : H →* GeneralLinearGroup ι R) :
    closedMatrixTraceAlgebra (O := O) (ρ.comp q) = closedMatrixTraceAlgebra (O := O) ρ :=
  closedMatrixTraceAlgebra_comp_surjective q hq ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L]

/-- Exact original-object consumer of `fixedResidualOriginalRepresentation_absoluteIrreducible`. -/
theorem actual_fixed_residual_absolute_irreducibility_fixedResidualOriginalRepresentation_absoluteIrreducible_source
    (p : ℕ) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)) :=
  fixedResidualOriginalRepresentation_absoluteIrreducible (L := L) p H σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `originalUnframedFixedQuotientEquiv_class`. -/
theorem actual_original_unframed_fixed_quotient_equivalence_originalUnframedFixedQuotientEquiv_class_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedFixedQuotientEquiv hA eA p hp H σ hσ (originalUnframedClass eA H σ ρ) =
      originalUnframedClass eA _ (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom
        (originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ ρ) :=
  originalUnframedFixedQuotientEquiv_class hA eA p hp H σ hσ ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `fixedResidualTraceAlgebra_localData`. -/
theorem actual_fixed_residual_trace_universal_ring_fixedResidualTraceAlgebra_localData_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]
    (p : ℕ) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) (i₀ : ι) :
    let T := closedMatrixTraceAlgebra (O := O)
      (fixedResidualFramedUniversalRepresentation p H σ hσ S hS)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ f : FixedResidualFramedCoefficientRing p H σ hσ S →ₐ[O] T,
        (∀ x : T, f x = x) ∧ Continuous f :=
  fixedResidualTraceAlgebra_localData (L := L) p H σ hσ S hS i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `arithmeticTraceCoefficientRing_localData`. -/
theorem actual_arithmetic_trace_universal_ring_arithmeticTraceCoefficientRing_localData_source
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι) :
    ∃ hlocal : IsLocalRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ),
      letI := hlocal
      IsNoetherianRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      IsAdic (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ))
        (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      ∃ f : ArithmeticFramedUniversalRing a ha p hp hpa σ hσ →ₐ[O]
          ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ,
        (∀ x : ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, f x = x) ∧
          Continuous f :=
  arithmeticTraceCoefficientRing_localData (L := L) a ha p hp hpa σ hσ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `originalCoefficientRepresentationClass_fixedQuotient_bijective`. -/
theorem actual_original_coefficient_class_fixed_quotient_originalCoefficientRepresentationClass_fixedQuotient_bijective_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (τq : fixedResidualProfiniteQuotient p H σ.ker
      (originalResidualMatrixKernel_isClosed H σ hσ) →ₜ* GeneralLinearGroup ι R)
    (hτq : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τq.toMonoidHom = (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
    (hwhole : ∀ g : H, τ g = τq (QuotientGroup.mk'
      (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) g))
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA _
      (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom τq hτq)) :
    Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ) :=
  originalCoefficientRepresentationClass_fixedQuotient_bijective hA eR eA p hp H σ hσ τ hτ τq hτq hwhole hbij

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `fixedResidualTraceUnframedUniversality_exists`. -/
theorem actual_fixed_residual_trace_unframed_universality_fixedResidualTraceUnframedUniversality_exists_source
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) (i₀ : ι) :
    let T := closedMatrixTraceAlgebra (O := O)
      (fixedResidualFramedUniversalRepresentation p H σ hσ S hS)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA H σ τ hτres) :=
  fixedResidualTraceUnframedUniversality_exists (L := L) p hp H σ hσ S hS i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticTraceUnframedUniversality_exists`. -/
theorem actual_arithmetic_trace_unframed_universality_arithmeticTraceUnframedUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι) :
    ∃ hlocal : IsLocalRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ),
      letI := hlocal
      IsNoetherianRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      IsAdic (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ))
        (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      ∃ (eT : IsLocalRing.ResidueField (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)
          ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι
          (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ))
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA
            (rationalArithmeticGaloisGroup a) σ τ hτres) :=
  arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing K]

/-- Exact original-object consumer of `matrixStrictlyConjugate_ker`. -/
theorem actual_matrix_strict_conjugacy_conditions_matrixStrictlyConjugate_ker_source (r : R →+* K)
    (ρ τ : G →* GeneralLinearGroup ι R) (h : MatrixStrictlyConjugate r ρ τ) :
    ρ.ker = τ.ker :=
  matrixStrictlyConjugate_ker r ρ τ h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `originalUnframedKillsSubgroup_class_iff`. -/
theorem actual_original_unframed_determinant_inertia_conditions_originalUnframedKillsSubgroup_class_iff_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedKillsSubgroup eA H σ N (originalUnframedClass eA H σ ρ) ↔
      N ≤ ρ.val.toMonoidHom.ker :=
  originalUnframedKillsSubgroup_class_iff eA H σ N ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `originalUnframedDeterminantSubgroup_coefficient_iff`. -/
theorem actual_original_unframed_condition_coefficient_ideals_originalUnframedDeterminantSubgroup_coefficient_iff_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H) (f : OriginalContinuousCoefficientFiber eR eA) :
    (originalUnframedHasDeterminant eA H σ δ
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ∧
      originalUnframedKillsSubgroup eA H σ N
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f)) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixRepresentationRelationIdeal τ.toMonoidHom N ≤ RingHom.ker f.val.toRingHom :=
  originalUnframedDeterminantSubgroup_coefficient_iff eR eA H σ τ hτ δ N f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R] [IsLocalRing R]
  [t : TopologicalSpace R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Exact original-object consumer of `originalAdicCompleteLocal_compactSpace`. -/
theorem actual_original_adic_complete_local_compactness_originalAdicCompleteLocal_compactSpace_source [IsNoetherianRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) : CompactSpace R :=
  originalAdicCompleteLocal_compactSpace hR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Finite (IsLocalRing.ResidueField R)] [TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Exact original-object consumer of `originalAdicLocalQuotient_localData`. -/
theorem actual_original_adic_local_quotient_data_originalAdicLocalQuotient_localData_source
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (J : Ideal R)
    [IsLocalRing (R ⧸ J)] :
    IsNoetherianRing (R ⧸ J) ∧
      IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) :=
  originalAdicLocalQuotient_localData hR J

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `representationDeterminantSubgroupQuotient_localData`. -/
theorem actual_residual_determinant_subgroup_quotient_representationDeterminantSubgroupQuotient_localData_source
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace R] [IsTopologicalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    let J := representationDeterminantIdeal ρ δ ⊔ matrixRepresentationRelationIdeal ρ N
    letI := representationDeterminantSubgroupQuotient_isLocal eR ρ σ hρ δ hδ N hN
    IsNoetherianRing (R ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) :=
  representationDeterminantSubgroupQuotient_localData hR eR ρ σ hρ δ hδ N hN

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `originalUnframedConditionQuotientEquiv_evaluation`. -/
theorem actual_original_unframed_condition_quotient_equivalence_originalUnframedConditionQuotientEquiv_evaluation_source
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H)
    [IsLocalRing (R ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixRepresentationRelationIdeal τ.toMonoidHom N))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR
      (representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixRepresentationRelationIdeal τ.toMonoidHom N)) eA) :
    (originalUnframedConditionQuotientEquiv eR eA H σ τ hτ δ N hbij f).val =
      originalCoefficientRepresentationClass eR eA H σ τ hτ
        (originalQuotientCoefficientRestriction eR eA
          (representationDeterminantIdeal τ.toMonoidHom δ ⊔
            matrixRepresentationRelationIdeal τ.toMonoidHom N) f).val :=
  originalUnframedConditionQuotientEquiv_evaluation eR eA H σ τ hτ δ N hbij f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticUnframedInertiaUniversality_exists`. -/
theorem actual_arithmetic_unframed_inertia_universality_arithmeticUnframedInertiaUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixRepresentationRelationIdeal τ.toMonoidHom (rationalArithmeticInertia a P.asIdeal)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedHasDeterminant eA _ σ δ c ∧
                originalUnframedKillsSubgroup eA _ σ (rationalArithmeticInertia a P.asIdeal) c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA _ σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticUnframedInertiaUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ δ hδ P hP

end

end Dubon2026.SemanticRegression
