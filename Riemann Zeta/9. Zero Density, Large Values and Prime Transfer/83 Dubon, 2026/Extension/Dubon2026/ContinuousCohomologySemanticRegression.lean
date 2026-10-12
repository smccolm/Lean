import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology



section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
variable (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroCyclotomicTwist_restriction`. -/
theorem actual_arithmetic_trace_zero_cyclotomic_duality_rationalArithmeticTraceZeroCyclotomicTwist_restriction_source
    (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticTraceZeroCyclotomicTwist a n hna σ).comp
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      coefficientCharacterTwist
        (matrixTraceZeroAdjointRepresentation
          (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))
        (rationalPrimeCyclotomicCoefficientCharacter p hp n k).toMonoidHom :=
  rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `matrixTraceZeroCharacterAction_continuous`. -/
theorem actual_trace_zero_twisted_action_continuity_matrixTraceZeroCharacterAction_continuous_source
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (χ : G →* R) (hχ : Continuous χ) :
    Continuous (fun z : G × matrixTraceZeroSubmodule ι R =>
      coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ z.1 z.2) :=
  matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]

omit [TopologicalSpace R] [ContinuousSMul R A] in
/-- Exact original-object consumer of `representationOneDifferential_continuous`. -/
theorem actual_continuous_representation_cocycles_representationOneDifferential_continuous_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (f : G → A) (hf : Continuous f) :
    Continuous (fun z => groupCohomology.d₁₂ A f z) :=
  representationOneDifferential_continuous A hA f hf

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousRepresentationH2_eq_iff`. -/
theorem actual_continuous_representation_cohomology_continuousRepresentationH2_eq_iff_source
    (c d : continuousRepresentationCocyclesTwo A) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH2 A hA) =
        Submodule.Quotient.mk d ↔
      ∃ f : C(G, A), continuousRepresentationCoboundaryTwo A hA f = c - d :=
  continuousRepresentationH2_eq_iff A hA c d

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `continuousTraceZeroH1GeneralEquiv_mk`. -/
theorem actual_continuous_adjoint_general_comparison_continuousTraceZeroH1GeneralEquiv_mk_source
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousTraceZeroH1GeneralEquiv ρ hρ (Submodule.Quotient.mk c) =
      (Submodule.Quotient.mk (⟨c.val, c.property⟩ :
        continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ)) :
        ContinuousRepresentationH1 (matrixTraceZeroAdjointRep ρ)
          (matrixTraceZeroAdjointAction_continuous ρ hρ)) :=
  continuousTraceZeroH1GeneralEquiv_mk ρ hρ c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

include hβ in
/-- Exact original-object consumer of `equivariantOneCocycleCup_mem`. -/
theorem actual_equivariant_cocycle_cup_equivariantOneCocycleCup_mem_source
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) :
    (fun z : G × G => β (f z.1) (B.ρ z.1 (u z.2))) ∈ groupCohomology.cocycles₂ C :=
  equivariantOneCocycleCup_mem A B C β hβ f u

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

/-- Exact original-object consumer of `equivariantOneCocycleCup_coboundary_right`. -/
theorem actual_equivariant_cup_coboundaries_equivariantOneCocycleCup_coboundary_right_source
    (f : groupCohomology.cocycles₁ A) (b : B) :
    (equivariantOneCocycleCup A B C β hβ f
      ⟨groupCohomology.d₀₁ B b, groupCohomology.d₀₁_apply_mem_cocycles₁ (A := B) b⟩ :
        G × G → C) =
      groupCohomology.d₁₂ C (fun g => -β (f g) (B.ρ g b)) :=
  equivariantOneCocycleCup_coboundary_right A B C β hβ f b

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousOneCocycleCupBilinear_apply`. -/
theorem actual_continuous_equivariant_cup_continuousOneCocycleCupBilinear_apply_source
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B)
    (g h : G) :
    (continuousOneCocycleCupBilinear A B C β hβ hcβ hB f u).val (g, h) =
      β (f.val g) (B.ρ g (u.val h)) :=
  continuousOneCocycleCupBilinear_apply A B C β hβ hcβ hB f u g h

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


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

/-- Exact original-object consumer of `continuousH1Cup_mk`. -/
theorem actual_continuous_cohomology_cup_continuousH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousH1Cup A B C β hβ hcβ hA hB hC
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk (continuousOneCocycleCup A B C β hβ hcβ hB f u) :
        ContinuousRepresentationH2 C hC) :=
  continuousH1Cup_mk A B C β hβ hcβ hA hB hC f u

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k] in
/-- Exact original-object consumer of `matrixTraceZeroTracePairing_character_equivariant`. -/
theorem actual_trace_zero_continuous_character_pairing_matrixTraceZeroTracePairing_character_equivariant_source
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (g : G)
    (X Y : matrixTraceZeroSubmodule ι k) :
    matrixTraceZeroTracePairing ((matrixTraceZeroCharacterRep ρ χ).ρ g X)
        ((matrixTraceZeroAdjointRep ρ).ρ g Y) =
      (coefficientCharacterRep χ).ρ g (matrixTraceZeroTracePairing X Y) :=
  matrixTraceZeroTracePairing_character_equivariant ρ χ g X Y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_mk`. -/
theorem actual_trace_zero_character_cohomology_cup_matrixTraceZeroCharacterH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ))
    (u : continuousTraceZeroAdjointCocycles ρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep ρ χ) (matrixTraceZeroAdjointRep ρ)
          (coefficientCharacterRep χ) matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant ρ χ)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous ρ hρ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ)
          (coefficientCharacterAction_continuous χ hχ)) :=
  matrixTraceZeroCharacterH1Cup_mk ρ hρ χ hχ f u

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroH1Cup_mk`. -/
theorem actual_arithmetic_trace_zero_cohomology_cup_rationalArithmeticTraceZeroH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep σ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom))
    (u : continuousTraceZeroAdjointCocycles σ) :
    let χ := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    rationalArithmeticTraceZeroH1Cup a n hna σ hσ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep σ χ.toMonoidHom)
          (matrixTraceZeroAdjointRep σ) (coefficientCharacterRep χ.toMonoidHom)
          matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant σ χ.toMonoidHom)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous σ hσ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep σ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ.toMonoidHom)
          (coefficientCharacterAction_continuous χ.toMonoidHom χ.continuous)) :=
  rationalArithmeticTraceZeroH1Cup_mk a n hna σ hσ f u

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousRepresentationCocycleTwoRestriction_coboundary`. -/
theorem actual_continuous_representation_restriction_continuousRepresentationCocycleTwoRestriction_coboundary_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (f : C(G, A)) :
    continuousRepresentationCocycleTwoRestriction A j hj
        (continuousRepresentationCoboundaryTwo A hA f) =
      continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) (f.comp ⟨j, hj⟩) :=
  continuousRepresentationCocycleTwoRestriction_coboundary A j hj hA f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousRepresentationH2Restriction_mk`. -/
theorem actual_continuous_cohomology_restriction_continuousRepresentationH2Restriction_mk_source
    (c : continuousRepresentationCocyclesTwo A) :
    continuousRepresentationH2Restriction A hA j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction A j hj c) :=
  continuousRepresentationH2Restriction_mk A hA j hj c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
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
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousH1Cup_restriction`. -/
theorem actual_continuous_cup_restriction_continuousH1Cup_restriction_source
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousRepresentationH2Restriction C hC j hj
        (continuousH1Cup A B C β hβ hcβ hA hB hC x y) =
      continuousH1Cup (restrictedCoefficientRep A j) (restrictedCoefficientRep B j)
        (restrictedCoefficientRep C j) β (fun h v w => hβ (j h) v w) hcβ
        (restrictedCoefficientAction_continuous A j hj hA)
        (restrictedCoefficientAction_continuous B j hj hB)
        (restrictedCoefficientAction_continuous C j hj hC)
        (continuousRepresentationH1Restriction A hA j hj x)
        (continuousRepresentationH1Restriction B hB j hj y) :=
  continuousH1Cup_restriction A B C β hβ hcβ hA hB hC j hj x y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixTraceZeroAdjointRepresentation_comp`. -/
theorem actual_adjoint_representation_restriction_matrixTraceZeroAdjointRepresentation_comp_source
    (ρ : G →* GeneralLinearGroup ι R) (j : H →* G) :
    (matrixTraceZeroAdjointRepresentation ρ).comp j =
      matrixTraceZeroAdjointRepresentation (ρ.comp j) :=
  matrixTraceZeroAdjointRepresentation_comp ρ j

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul R V]
  {ρ σ : Representation R G V} (h : ρ = σ)

variable (hρ : Continuous (fun z : G × V => ρ z.1 z.2))
  (hσ : Continuous (fun z : G × V => σ z.1 z.2))

/-- Exact original-object consumer of `continuousH2CoefficientCongr_mk`. -/
theorem actual_continuous_cohomology_coefficient_congr_continuousH2CoefficientCongr_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.of ρ)) :
    continuousH2CoefficientCongr h hρ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoCoefficientCongr h c) :=
  continuousH2CoefficientCongr_mk h hρ hσ c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace R] [IsTopologicalRing R]

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `continuousTraceZeroH1GeneralEquiv_restriction`. -/
theorem actual_continuous_adjoint_restriction_comparison_continuousTraceZeroH1GeneralEquiv_restriction_source
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousH1CoefficientCongr (matrixTraceZeroAdjointRepresentation_comp ρ j)
      (restrictedCoefficientAction_continuous (matrixTraceZeroAdjointRep ρ) j hj
        (matrixTraceZeroAdjointAction_continuous ρ hρ))
      (matrixTraceZeroAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
      (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj
        (continuousTraceZeroH1GeneralEquiv ρ hρ x)) =
      continuousTraceZeroH1GeneralEquiv (ρ.comp j) (hρ.comp hj)
        (continuousTraceZeroH1Restriction ρ hρ j hj x) :=
  continuousTraceZeroH1GeneralEquiv_restriction ρ hρ j hj x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {n : ℕ} [NeZero n] {μ : K}

/-- Exact original-object consumer of `primitiveRootAdditiveEquiv_galois`. -/
theorem actual_cyclotomic_root_additive_equiv_primitiveRootAdditiveEquiv_galois_source
    (hμ : IsPrimitiveRoot μ n) (g : K ≃ₐ[F] K) (x : ZMod n) :
    restrictRootsOfUnity g n (Additive.toMul (primitiveRootAdditiveEquiv hμ x)) =
      Additive.toMul (primitiveRootAdditiveEquiv hμ ((hμ.autToPow F g : ZMod n) * x)) :=
  primitiveRootAdditiveEquiv_galois hμ g x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousH1Cup_skew`. -/
theorem actual_continuous_cup_skew_symmetry_continuousH1Cup_skew_source
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousH1Cup A B C β hβ hcβ hA hB hC x y =
      -continuousH1Cup B A C β.flip (fun g v w => hβ g w v)
        (hcβ.comp continuous_swap) hB hA hC y x :=
  continuousH1Cup_skew A B C β hβ hcβ hA hB hC x y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G : Type} [Field K] [Group G] [Fintype G] (A : Rep K G)

/-- Exact original-object consumer of `finiteTwoCocycle_average_coboundary`. -/
theorem actual_finite_coefficient_cocycle_averaging_finiteTwoCocycle_average_coboundary_source
    (hn : (Fintype.card G : K) ≠ 0) (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (fun g => (Fintype.card G : K)⁻¹ • ∑ t, c (g, t)) = c.val :=
  finiteTwoCocycle_average_coboundary A hn c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G : Type} [Field K] [Group G] [Fintype G]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep K G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul K A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousFiniteH2_eq_zero`. -/
theorem actual_continuous_finite_cohomology_vanishing_continuousFiniteH2_eq_zero_source
    (hn : (Fintype.card G : K) ≠ 0) (x : ContinuousRepresentationH2 A hA) : x = 0 :=
  continuousFiniteH2_eq_zero A hA hn x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteFunction_exists_openNormalPeriods`. -/
theorem actual_compact_discrete_function_periods_compactDiscreteFunction_exists_openNormalPeriods_source (f : C(G, A)) :
    ∃ U : OpenNormalSubgroup G, ∀ g u, u ∈ U → f (g * u) = f g :=
  compactDiscreteFunction_exists_openNormalPeriods f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteTwoFunction_exists_commonPeriods`. -/
theorem actual_compact_discrete_finite_quotient_compactDiscreteTwoFunction_exists_commonPeriods_source [CompactSpace G] (f : C(G × G, A)) :
    ∃ V : OpenNormalSubgroup G, ∀ g h u v, u ∈ V → v ∈ V → f (g * u, h * v) = f (g, h) :=
  compactDiscreteTwoFunction_exists_commonPeriods f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteTwoFunction_exists_finiteQuotient`. -/
theorem actual_compact_discrete_two_quotient_function_compactDiscreteTwoFunction_exists_finiteQuotient_source [CompactSpace G]
    (f : C(G × G, A)) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ q : C((G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup), A),
        ∀ g h, q (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) = f (g, h) :=
  compactDiscreteTwoFunction_exists_finiteQuotient f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul R V]

/-- Exact original-object consumer of `continuousTrivialTwoCocycle_exists_finiteQuotient`. -/
theorem actual_continuous_trivial_cocycle_finite_quotient_continuousTrivialTwoCocycle_exists_finiteQuotient_source [CompactSpace G]
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation R G V))) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ d : continuousRepresentationCocyclesTwo
          (Rep.of (1 : Representation R (G ⧸ U.toSubgroup) V)),
        ∀ g h, d.val (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) =
          c.val (g, h) :=
  continuousTrivialTwoCocycle_exists_finiteQuotient c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G V : Type} [Field K] [CharZero K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

/-- Exact original-object consumer of `continuousCompactTrivialH2_eq_zero`. -/
theorem actual_continuous_compact_trivial_h2_vanishing_continuousCompactTrivialH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 :=
  continuousCompactTrivialH2_eq_zero x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G A B C : Type} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  {ρA σA : Representation R G A} {ρB σB : Representation R G B}
  {ρC σC : Representation R G C}

/-- Exact original-object consumer of `continuousH1Cup_coefficientCongr`. -/
theorem actual_continuous_cup_coefficient_congr_continuousH1Cup_coefficientCongr_source
    (eA : ρA = σA) (eB : ρB = σB) (eC : ρC = σC)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβρ : ∀ g x y, β (ρA g x) (ρB g y) = ρC g (β x y))
    (hβσ : ∀ g x y, β (σA g x) (σB g y) = σC g (β x y))
    (hcβ : Continuous (fun z : A × B => β z.1 z.2))
    (hρA : Continuous (fun z : G × A => ρA z.1 z.2))
    (hρB : Continuous (fun z : G × B => ρB z.1 z.2))
    (hρC : Continuous (fun z : G × C => ρC z.1 z.2))
    (hσA : Continuous (fun z : G × A => σA z.1 z.2))
    (hσB : Continuous (fun z : G × B => σB z.1 z.2))
    (hσC : Continuous (fun z : G × C => σC z.1 z.2))
    (x : ContinuousRepresentationH1 (Rep.of ρA) hρA)
    (y : ContinuousRepresentationH1 (Rep.of ρB) hρB) :
    continuousH2CoefficientCongr eC hρC hσC
        (continuousH1Cup (Rep.of ρA) (Rep.of ρB) (Rep.of ρC)
          β hβρ hcβ hρA hρB hρC x y) =
      continuousH1Cup (Rep.of σA) (Rep.of σB) (Rep.of σC)
        β hβσ hcβ hσA hσB hσC
        (continuousH1CoefficientCongr eA hρA hσA x)
        (continuousH1CoefficientCongr eB hρB hσB y) :=
  continuousH1Cup_coefficientCongr eA eB eC β hβρ hβσ hcβ hρA hρB hρC hσA hσB hσC x y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Restriction_mk`. -/
theorem actual_trace_zero_character_cohomology_restriction_matrixTraceZeroCharacterH1Restriction_mk_source
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ)) :
    matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (matrixTraceZeroCharacterCocycleRestriction ρ χ j hj c) :=
  matrixTraceZeroCharacterH1Restriction_mk ρ hρ χ hχ j hj c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_restriction`. -/
theorem actual_trace_zero_character_cup_restriction_matrixTraceZeroCharacterH1Cup_restriction_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    coefficientCharacterH2Restriction χ hχ j hj
        (matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y) =
      matrixTraceZeroCharacterH1Cup (ρ.comp j) (hρ.comp hj) (χ.comp j) (hχ.comp hj)
        (matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj x)
        (continuousTraceZeroH1Restriction ρ hρ j hj y) :=
  matrixTraceZeroCharacterH1Cup_restriction ρ hρ χ hχ j hj x y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousDiscreteH2Equiv_mk`. -/
theorem actual_continuous_discrete_h2_comparison_continuousDiscreteH2Equiv_mk_source [DiscreteTopology G]
    (c : continuousRepresentationCocyclesTwo A) :
    continuousDiscreteH2Equiv A hA (Submodule.Quotient.mk c) =
      groupCohomology.H2π A c.val :=
  continuousDiscreteH2Equiv_mk A hA c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

variable [CompactSpace G] [CharZero K]

/-- Exact original-object consumer of `continuousCompactTrivialH1_eq_zero`. -/
theorem actual_continuous_compact_trivial_h1_vanishing_continuousCompactTrivialH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 :=
  continuousCompactTrivialH1_eq_zero x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

variable [IsTopologicalRing k]
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Exact original-object consumer of `rationalPrimeCyclotomicAdjointH1Restriction_mk`. -/
theorem actual_arithmetic_cyclotomic_cohomology_restriction_rationalPrimeCyclotomicAdjointH1Restriction_mk_source
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)) :
    rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (continuousCocycleOneCoefficientCongr
          (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp)
          (continuousRepresentationCocycleOneRestriction (matrixTraceZeroCharacterRep σ
            (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous c)) :=
  rationalPrimeCyclotomicAdjointH1Restriction_mk a n hna p hp σ hσ c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroH1Cup_prime_restriction`. -/
theorem actual_arithmetic_cyclotomic_cup_restriction_rationalArithmeticTraceZeroH1Cup_prime_restriction_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalPrimeCyclotomicH2Restriction a n hna p hp
        (rationalArithmeticTraceZeroH1Cup a n hna σ hσ x y) =
      matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y) :=
  rationalArithmeticTraceZeroH1Cup_prime_restriction a n hna σ hσ p hp x y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousFiniteCyclicH2Pi_eq_iff`. -/
theorem actual_continuous_finite_cyclic_h2_continuousFiniteCyclicH2Pi_eq_iff_source
    (x y : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    continuousFiniteCyclicH2Pi A hA g hg x = continuousFiniteCyclicH2Pi A hA g hg y ↔
      x.val - y.val ∈ LinearMap.range A.norm.hom.toLinearMap :=
  continuousFiniteCyclicH2Pi_eq_iff A hA g hg x y

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]

variable [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `finiteFieldGaloisUnit_invariant_mem_normRange`. -/
theorem actual_finite_galois_unit_norm_range_finiteFieldGaloisUnit_invariant_mem_normRange_source [Finite L]
    (x : Rep.ofAlgebraAutOnUnits K L)
    (hx : x ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants) :
    x ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  finiteFieldGaloisUnit_invariant_mem_normRange x hx

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable [Finite L] [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace Gal(L/K)] [DiscreteTopology Gal(L/K)]

/-- Exact original-object consumer of `continuousFiniteFieldGaloisUnitH2_eq_zero`. -/
theorem actual_continuous_finite_field_galois_unit_h2_continuousFiniteFieldGaloisUnitH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K L)
      (finiteFieldGaloisUnitAction_continuous (K := K) (L := L))) : x = 0 :=
  continuousFiniteFieldGaloisUnitH2_eq_zero x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [TopologicalSpace Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [IsTopologicalAddGroup (Rep.ofAlgebraAutOnUnits K L)]
  [@ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits K L)
    (Rep.ofAlgebraAutOnUnits K L).hV2.toSMul inferInstance inferInstance]
  (hA : Continuous (fun z : Gal(L/K) × Rep.ofAlgebraAutOnUnits K L =>
    (Rep.ofAlgebraAutOnUnits K L).ρ z.1 z.2))

/-- Exact original-object consumer of `continuousGaloisUnitH1_eq_zero`. -/
theorem actual_continuous_galois_unit_h1_vanishing_continuousGaloisUnitH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K L) hA) : x = 0 :=
  continuousGaloisUnitH1_eq_zero hA x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientCocycleTwoMap_coboundary`. -/
theorem actual_continuous_equivariant_coefficient_map_continuousCoefficientCocycleTwoMap_coboundary_source (f : C(G, A)) :
    continuousCoefficientCocycleTwoMap A B φ hφ hφρ
      (continuousRepresentationCoboundaryTwo A hA f) =
        continuousRepresentationCoboundaryTwo B hB
          ⟨fun g => φ (f g), hφ.comp f.continuous⟩ :=
  continuousCoefficientCocycleTwoMap_coboundary A B φ hφ hφρ hA hB f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientH2Map_mk`. -/
theorem actual_continuous_cohomology_coefficient_map_continuousCoefficientH2Map_mk_source (c : continuousRepresentationCocyclesTwo A) :
    continuousCoefficientH2Map A B φ hφ hφρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap A B φ hφ hφρ c) :=
  continuousCoefficientH2Map_mk A B φ hφ hφρ hA hB c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B C : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- Exact original-object consumer of `exactCoefficientPreimage_map`. -/
theorem actual_continuous_exact_coefficient_lifts_exactCoefficientPreimage_map_source (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
    (b : B) (hb : b ∈ LinearMap.range φ) : φ (exactCoefficientPreimage φ hφ b) = b :=
  exactCoefficientPreimage_map φ hφ b hb

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A] in
include hψρ hExact in
/-- Exact original-object consumer of `coefficientConnectingBoundary_mem_range`. -/
theorem actual_continuous_coefficient_connecting_lift_coefficientConnectingBoundary_mem_range_source
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    (continuousRepresentationCoboundaryTwo B hB
      (coefficientConnectingOneLift B C ψ hψ c)).val z ∈ LinearMap.range φ :=
  coefficientConnectingBoundary_mem_range A B C φ ψ hψ hψρ hExact hB c z

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `coefficientConnectingTwoCocycle_image_class_zero`. -/
theorem actual_continuous_coefficient_connecting_cocycle_coefficientConnectingTwoCocycle_image_class_zero_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hcφ : Continuous φ)
    (c : continuousRepresentationCocyclesOne C) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)) = 0 :=
  coefficientConnectingTwoCocycle_image_class_zero A B C φ hφ hφρ ψ hψ hψρ hExact hB hA hcφ c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `coefficientConnectingClass_eq_of_lift`. -/
theorem actual_continuous_connecting_lift_independence_coefficientConnectingClass_eq_of_lift_source
    (c : continuousRepresentationCocyclesOne C)
    (a : continuousRepresentationCocyclesTwo A) (b : C(G, B))
    (hb : ∀ g, ψ (b g) = c.val g)
    (ha : ∀ z, φ (a.val z) = (continuousRepresentationCoboundaryTwo B hB b).val z) :
    (Submodule.Quotient.mk
      (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
      ContinuousRepresentationH2 A hA) = Submodule.Quotient.mk a :=
  coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c a b hb ha

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousConnectingCocycleClass_apply`. -/
theorem actual_continuous_connecting_cocycle_class_continuousConnectingCocycleClass_apply_source (c : continuousRepresentationCocyclesOne C) :
    continuousConnectingCocycleClass A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c =
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH2 A hA) :=
  continuousConnectingCocycleClass_apply A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientConnectingMap_image_zero`. -/
theorem actual_continuous_coefficient_connecting_map_continuousCoefficientConnectingMap_image_zero_source (hcφ : Continuous φ)
    (x : ContinuousRepresentationH1 C hC) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) = 0 :=
  continuousCoefficientConnectingMap_image_zero A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC hcφ x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousConnectingH2_range_eq_ker`. -/
theorem actual_continuous_connecting_h2_exactness_continuousConnectingH2_range_eq_ker_source :
    LinearMap.range
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) =
        LinearMap.ker (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) :=
  continuousConnectingH2_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

include hcφ in
/-- Exact original-object consumer of `continuousConnectingH1_range_eq_ker`. -/
theorem actual_continuous_connecting_h1_exactness_continuousConnectingH1_range_eq_ker_source :
    LinearMap.range (continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC) =
      LinearMap.ker
        (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) :=
  continuousConnectingH1_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Exact original-object consumer of `continuousCocycle_exists_openNormal_periods_and_fixed`. -/
theorem actual_continuous_cocycle_period_invariants_continuousCocycle_exists_openNormal_periods_and_fixed_source
    (c : continuousRepresentationCocyclesOne A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g u, u ∈ U → c.val (g * u) = c.val g) ∧
      (∀ u, u ∈ U → ∀ g, A.ρ u (c.val g) = c.val g) :=
  continuousCocycle_exists_openNormal_periods_and_fixed A c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitCocycle_exists_finiteField`. -/
theorem actual_continuous_galois_cocycle_finite_field_continuousGaloisUnitCocycle_exists_finiteField_source
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val g)) : Ωˣ) : Ω) ∈
        F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        c.val (g * u) = c.val g) :=
  continuousGaloisUnitCocycle_exists_finiteField c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₁ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c g)) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → c (g * u) = c g)

/-- Select the pinned original Galois unit action for this exact consumer. -/
noncomputable local instance galoisUnitFiniteDescentSourceAction : SMul Gal(F/K) Fˣ :=
  AlgEquiv.instMulDistribMulActionUnits.toSMul

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitCocycle_exists_finite_descent`. -/
theorem actual_galois_unit_cocycle_finite_descent_galoisUnitCocycle_exists_finite_descent_source :
    ∃ f : Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₁ f ∧
      ∀ g : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = Additive.toMul (Rep.toAdditive (c g)) :=
  galoisUnitCocycle_exists_finite_descent F c hvalues hperiod

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (hA : Continuous (fun z : Gal(Ω/K) × Rep.ofAlgebraAutOnUnits K Ω =>
  (Rep.ofAlgebraAutOnUnits K Ω).ρ z.1 z.2))

/-- Exact original-object consumer of `continuousInfiniteGaloisUnitH1_eq_zero`. -/
theorem actual_continuous_infinite_galois_unit_h1_continuousInfiniteGaloisUnitH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω) hA) : x = 0 :=
  continuousInfiniteGaloisUnitH1_eq_zero hA x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `discreteInfiniteGaloisUnitH1_eq_zero`. -/
theorem actual_discrete_galois_unit_action_continuity_discreteInfiniteGaloisUnitH1_eq_zero_source [IsGalois K Ω]
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 :=
  discreteInfiniteGaloisUnitH1_eq_zero x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω : Type} [Field Ω]

/-- Exact original-object consumer of `algebraicallyClosedUnitPower_surjective`. -/
theorem actual_algebraically_closed_unit_power_sequence_algebraicallyClosedUnitPower_surjective_source [IsAlgClosed Ω]
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : Ωˣ →* Ωˣ) :=
  algebraicallyClosedUnitPower_surjective n hn

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hExact : LinearMap.range φ = LinearMap.ker ψ)

/-- Exact original-object consumer of `coefficientKernelTwoCocycle_coefficient_map`. -/
theorem actual_continuous_coefficient_kernel_two_cocycle_coefficientKernelTwoCocycle_coefficient_map_source (hcφ : Continuous φ)
    (b : continuousRepresentationCocyclesTwo B) (hb : ∀ z, ψ (b.val z) = 0) :
    continuousCoefficientCocycleTwoMap A B φ hcφ hφρ
      (coefficientKernelTwoCocycle A B C φ hφ hφρ ψ hExact b hb) = b :=
  coefficientKernelTwoCocycle_coefficient_map A B C φ hφ hφρ ψ hExact hcφ b hb

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

include hφ hψ hExact in
/-- Exact original-object consumer of `continuousCoefficientH2_middle_range_eq_ker`. -/
theorem actual_continuous_coefficient_h2_middle_exactness_continuousCoefficientH2_middle_range_eq_ker_source :
    LinearMap.range (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) =
      LinearMap.ker (continuousCoefficientH2Map B C ψ continuous_of_discreteTopology hψρ hB hC) :=
  continuousCoefficientH2_middle_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- Exact original-object consumer of `galoisRootOfUnityRepresentation_apply`. -/
theorem actual_galois_root_of_unity_representation_galoisRootOfUnityRepresentation_apply_source (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x =
      Rep.toAdditive.symm (Additive.ofMul (g • Additive.toMul (Rep.toAdditive x))) :=
  galoisRootOfUnityRepresentation_apply n g x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- Exact original-object consumer of `galoisKummerCoefficient_exact`. -/
theorem actual_galois_kummer_coefficient_sequence_galoisKummerCoefficient_exact_source :
    LinearMap.range (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap =
      LinearMap.ker (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap :=
  galoisKummerCoefficient_exact (K := K) (Ω := Ω) n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `discreteGaloisRootAction_continuous`. -/
theorem actual_discrete_kummer_coefficient_continuity_discreteGaloisRootAction_continuous_source [Algebra.IsIntegral K Ω] :
    Continuous (fun z : Gal(Ω/K) × galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n =>
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ z.1 z.2) :=
  discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

omit [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] in
/-- Exact original-object consumer of `galoisKummerH2Power_eq_nsmul`. -/
theorem actual_continuous_kummer_h2_maps_galoisKummerH2Power_eq_nsmul_source (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisKummerH2Power (K := K) (Ω := Ω) n x = n • x :=
  galoisKummerH2Power_eq_nsmul n x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisKummerH2KernelEquiv_apply`. -/
theorem actual_continuous_kummer_h2_torsion_galoisKummerH2KernelEquiv_apply_source
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :
    (galoisKummerH2KernelEquiv (K := K) (Ω := Ω) n hn x).val =
      galoisKummerH2Inclusion (K := K) (Ω := Ω) n x :=
  galoisKummerH2KernelEquiv_apply n hn x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Exact original-object consumer of `continuousTwoCocycle_exists_openNormal_periods_and_fixed`. -/
theorem actual_continuous_two_cocycle_period_invariants_continuousTwoCocycle_exists_openNormal_periods_and_fixed_source
    (c : continuousRepresentationCocyclesTwo A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g h u v, u ∈ U → v ∈ U → c.val (g * u, h * v) = c.val (g, h)) ∧
      (∀ u, u ∈ U → ∀ g h, A.ρ u (c.val (g, h)) = c.val (g, h)) :=
  continuousTwoCocycle_exists_openNormal_periods_and_fixed A c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitTwoCocycle_exists_finiteField`. -/
theorem actual_continuous_galois_two_cocycle_finite_field_continuousGaloisUnitTwoCocycle_exists_finiteField_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g h : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h)) :=
  continuousGaloisUnitTwoCocycle_exists_finiteField c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g h : Gal(Ω/K),
    ((Additive.toMul (Rep.toAdditive (c (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
    AlgEquiv.restrictNormalHom F v = 1 → c (g * u, h * v) = c (g, h))

/-- Select the pinned original finite-field Galois unit action. -/
noncomputable local instance galoisUnitTwoCocycleFiniteDescentSourceAction : SMul Gal(F/K) Fˣ :=
  AlgEquiv.instMulDistribMulActionUnits.toSMul

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitTwoCocycle_exists_finite_descent`. -/
theorem actual_galois_unit_two_cocycle_finite_descent_galoisUnitTwoCocycle_exists_finite_descent_source :
    ∃ f : Gal(F/K) × Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₂ f ∧
      ∀ g h : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
        Additive.toMul (Rep.toAdditive (c (g, h))) :=
  galoisUnitTwoCocycle_exists_finite_descent F c hvalues hperiod

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Finite K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousFiniteBaseGaloisUnitH2_eq_zero`. -/
theorem actual_continuous_finite_base_galois_unit_h2_continuousFiniteBaseGaloisUnitH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 :=
  continuousFiniteBaseGaloisUnitH2_eq_zero x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitCochain_exists_finiteField`. -/
theorem actual_continuous_galois_cochain_finite_field_continuousGaloisUnitCochain_exists_finiteField_source
    (E : FiniteGaloisIntermediateField K Ω)
    (b : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (b g)) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g) :=
  continuousGaloisUnitCochain_exists_finiteField E b

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] [Finite K] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hn in
/-- Exact original-object consumer of `continuousFiniteBaseRootH2_eq_zero`. -/
theorem actual_continuous_finite_base_root_h2_continuousFiniteBaseRootH2_eq_zero_source
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) : x = 0 :=
  continuousFiniteBaseRootH2_eq_zero n hn x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_mk`. -/
theorem actual_galois_unit_finite_stage_inflation_galoisUnitFiniteStageH2Inflation_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F)) :
    galoisUnitFiniteStageH2Inflation F (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)))
        (Rep.ofAlgebraAutOnUnits K Ω) (galoisUnitFiniteStageInclusion F).hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply (galoisUnitFiniteStageInclusion F))
        (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K))
          (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) c)) :=
  galoisUnitFiniteStageH2Inflation_mk F c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_exists_finite_stage`. -/
theorem actual_continuous_galois_unit_h2_finite_stage_continuousGaloisUnitH2_exists_finite_stage_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
        galoisUnitFiniteStageH2Inflation F y = x :=
  continuousGaloisUnitH2_exists_finite_stage x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] [Fintype G] (A : Rep R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousFiniteH2_card_nsmul_eq_zero`. -/
theorem actual_continuous_finite_h2_card_annihilation_continuousFiniteH2_card_nsmul_eq_zero_source
    (x : ContinuousRepresentationH2 A hA) : Fintype.card G • x = 0 :=
  continuousFiniteH2_card_nsmul_eq_zero A hA x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_is_torsion`. -/
theorem actual_continuous_galois_unit_h2_torsion_continuousGaloisUnitH2_is_torsion_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 :=
  continuousGaloisUnitH2_is_torsion x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]

variable [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `galoisUnitsBaseCoefficient_mem_normRange_iff`. -/
theorem actual_galois_unit_invariant_base_descent_galoisUnitsBaseCoefficient_mem_normRange_iff_source (u : Kˣ) :
    galoisUnitsBaseCoefficient (L := L) u ∈
        LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap ↔
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u :=
  galoisUnitsBaseCoefficient_mem_normRange_iff u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

variable (g : Gal(L/K))

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousCyclicGaloisUnitH2Class_eq_iff`. -/
theorem actual_continuous_cyclic_galois_unit_h2_classes_continuousCyclicGaloisUnitH2Class_eq_iff_source (u v : Kˣ) :
    continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul u) =
        continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul v) ↔
      ∃ w : Lˣ, Units.map (Algebra.norm K (S := L)) w = u / v :=
  continuousCyclicGaloisUnitH2Class_eq_iff g hg u v

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousCyclicGaloisNormQuotientEquiv_mk`. -/
theorem actual_continuous_cyclic_galois_norm_quotient_continuousCyclicGaloisNormQuotientEquiv_mk_source (u : Additive Kˣ) :
    continuousCyclicGaloisNormQuotientEquiv g hg (Submodule.Quotient.mk u) =
      continuousCyclicGaloisUnitH2Class g hg u :=
  continuousCyclicGaloisNormQuotientEquiv_mk g hg u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L Γ₀ : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation L Γ₀)
  (hv : ∀ (g : Gal(L/K)) (x : L), v (g x) = v x)

include hv in
/-- Exact original-object consumer of `galoisInvariantValuation_norm`. -/
theorem actual_galois_invariant_valuation_norm_galoisInvariantValuation_norm_source (x : L) :
    v (algebraMap K L (Algebra.norm K x)) = v x ^ Module.finrank K L :=
  galoisInvariantValuation_norm v hv x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [CompleteSpace K]

/-- Exact original-object consumer of `completeNonarchimedeanGalois_norm_fieldNorm`. -/
theorem actual_complete_nonarchimedean_galois_norm_completeNonarchimedeanGalois_norm_fieldNorm_source
    [FiniteDimensional K L] [IsGalois K L] (x : L) :
    ‖Algebra.norm K x‖ = ‖x‖ ^ Module.finrank K L :=
  completeNonarchimedeanGalois_norm_fieldNorm x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnitOrder_nonneg_iff`. -/
theorem actual_local_field_normalized_unit_order_localFieldUnitOrder_nonneg_iff_source (u : Kˣ) :
    0 ≤ localFieldUnitOrder K (Additive.ofMul u) ↔ ValuativeRel.valuation K u.val ≤ 1 :=
  localFieldUnitOrder_nonneg_iff K u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (x : S)

/-- Exact original-object consumer of `finiteFreeNormLinePolynomial_derivative_zero`. -/
theorem actual_finite_free_norm_line_polynomial_finiteFreeNormLinePolynomial_derivative_zero_source :
    (finiteFreeNormLinePolynomial b x).derivative.eval 0 = Algebra.trace R S x :=
  finiteFreeNormLinePolynomial_derivative_zero b x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring




/-- Exact original-object consumer of `adicComplete_polynomial_simple_root`. -/
theorem actual_adic_complete_simple_root_adicComplete_polynomial_simple_root_source
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I :=
  adicComplete_polynomial_simple_root I f a₀ h₁ h₂

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- Exact original-object consumer of `adicComplete_exists_principal_unit_norm`. -/
theorem actual_adic_complete_principal_norm_lifting_adicComplete_exists_principal_unit_norm_source
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (u : Rˣ) (hu : 1 - u.val ∈ I) :
    ∃ v : Sˣ, Units.map (Algebra.norm R (S := S)) v = u :=
  adicComplete_exists_principal_unit_norm b I x hx u hu

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- Exact original-object consumer of `adicComplete_unit_norm_surjective`. -/
theorem actual_adic_complete_unit_norm_lifting_adicComplete_unit_norm_surjective_source
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (hres : ∀ u : Rˣ, ∃ a : Sˣ,
      Ideal.Quotient.mk I (Algebra.norm R a.val) = Ideal.Quotient.mk I u.val) :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  adicComplete_unit_norm_surjective b I x hx hres

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Free R S] [Module.Finite R S]

/-- Exact original-object consumer of `localRingNorm_quotient_mk`. -/
theorem actual_local_ring_norm_reduction_localRingNorm_quotient_mk_source (x : S) :
    Algebra.norm (R ⧸ maximalIdeal R)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) x) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) :=
  localRingNorm_quotient_mk x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [Module.Free R S] [Module.Finite R S]
  [IsAdicComplete (maximalIdeal R) R]
  [Finite (R ⧸ maximalIdeal R)]
  [(Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal]

/-- Exact original-object consumer of `completeLocalFiniteResidue_unit_norm_surjective`. -/
theorem actual_complete_local_finite_residue_norm_completeLocalFiniteResidue_unit_norm_surjective_source :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  completeLocalFiniteResidue_unit_norm_surjective (R := R) (S := S)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- Exact original-object consumer of `unramifiedCompleteLocal_unit_norm_surjective`. -/
theorem actual_unramified_complete_local_unit_norm_unramifiedCompleteLocal_unit_norm_surjective_source :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  unramifiedCompleteLocal_unit_norm_surjective (R := R) (S := S)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnitOrder_eq_zero_iff_integer_unit`. -/
theorem actual_local_field_integer_unit_order_kernel_localFieldUnitOrder_eq_zero_iff_integer_unit_source (u : Kˣ) :
    localFieldUnitOrder K (Additive.ofMul u) = 0 ↔
      ∃ a : 𝒪[K]ˣ, Units.map (algebraMap 𝒪[K] K).toMonoidHom a = u :=
  localFieldUnitOrder_eq_zero_iff_integer_unit K u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [Field K] [Field L] [Algebra R S] [FaithfulSMul R S]
  [Algebra R K] [Algebra S L] [Algebra K L] [Algebra R L]
  [IsFractionRing R K] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- Exact original-object consumer of `unramifiedLocal_exists_fraction_field_unit_norm`. -/
theorem actual_unramified_local_fraction_field_norm_unramifiedLocal_exists_fraction_field_unit_norm_source (u : Rˣ) :
    ∃ v : Sˣ,
      Units.map (Algebra.norm K (S := L)) (Units.map (algebraMap S L).toMonoidHom v) =
        Units.map (algebraMap R K).toMonoidHom u :=
  unramifiedLocal_exists_fraction_field_unit_norm u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_exists_norm_of_order_zero`. -/
theorem actual_unramified_local_field_zero_order_norm_unramifiedLocalField_exists_norm_of_order_zero_source (u : Kˣ)
    (hu : localFieldUnitOrder K (Additive.ofMul u) = 0) :
    ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u :=
  unramifiedLocalField_exists_norm_of_order_zero u hu

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnit_eq_integer_unit_mul_order_power`. -/
theorem actual_local_field_uniformizer_order_localFieldUnit_eq_integer_unit_mul_order_power_source (q : 𝒪[K])
    (hq : Irreducible q) (x : Kˣ) :
    ∃ a : 𝒪[K]ˣ, x = Units.map (algebraMap 𝒪[K] K).toMonoidHom a *
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)) ^
        (localFieldUnitOrder K (Additive.ofMul x)) :=
  localFieldUnit_eq_integer_unit_mul_order_power K q hq x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localField_norm_integer_unit_order_zero`. -/
theorem actual_local_field_integer_unit_norm_localField_norm_integer_unit_order_zero_source (a : 𝒪[L]ˣ) :
    localFieldUnitOrder K (Additive.ofMul
      (Units.map (Algebra.norm K (S := L))
        (Units.map (algebraMap 𝒪[L] L).toMonoidHom a))) = 0 :=
  localField_norm_integer_unit_order_zero a

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_irreducible_algebraMap`. -/
theorem actual_unramified_local_field_uniformizer_unramifiedLocalField_irreducible_algebraMap_source (q : 𝒪[K])
    (hq : Irreducible q) : Irreducible (algebraMap 𝒪[K] 𝒪[L] q) :=
  unramifiedLocalField_irreducible_algebraMap q hq

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_norm_order`. -/
theorem actual_unramified_local_field_norm_order_unramifiedLocalField_norm_order_source (v : Lˣ) :
    localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
      (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v) :=
  unramifiedLocalField_norm_order v

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]

/-- Exact original-object consumer of `localFieldUnit_mem_normRange_iff_order_dvd`. -/
theorem actual_local_field_norm_order_criterion_localFieldUnit_mem_normRange_iff_order_dvd_source
    (hnorm : ∀ v : Lˣ,
      localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
        (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v))
    (hzero : ∀ u : Kˣ, localFieldUnitOrder K (Additive.ofMul u) = 0 →
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u)
    (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) :=
  localFieldUnit_mem_normRange_iff_order_dvd hnorm hzero u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_mem_normRange_iff_order_dvd`. -/
theorem actual_unramified_local_field_norm_image_unramifiedLocalField_mem_normRange_iff_order_dvd_source (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) :=
  unramifiedLocalField_mem_normRange_iff_order_dvd u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {K} {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalNormQuotientEquiv_mk`. -/
theorem actual_unramified_local_norm_quotient_unramifiedLocalNormQuotientEquiv_mk_source (u : Additive Kˣ) :
    unramifiedLocalNormQuotientEquiv (L := L) (Submodule.Quotient.mk u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  unramifiedLocalNormQuotientEquiv_mk u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousUnramifiedCyclicGaloisH2OrderEquiv_class`. -/
theorem actual_continuous_unramified_cyclic_galois_h2_order_continuousUnramifiedCyclicGaloisH2OrderEquiv_class_source (u : Additive Kˣ) :
    continuousUnramifiedCyclicGaloisH2OrderEquiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  continuousUnramifiedCyclicGaloisH2OrderEquiv_class g hg u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R]
  [IsHausdorff (maximalIdeal R) R]

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace S] [T2Space S] [IsLocalRing S] [IsNoetherianRing S]
  [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `compactSeparatedLocalRingHom_continuous`. -/
theorem actual_compact_separated_local_adic_topology_compactSeparatedLocalRingHom_continuous_source (f : R →+* S) [IsLocalHom f] :
    Continuous f :=
  compactSeparatedLocalRingHom_continuous f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space S] [ContinuousSMul R S]
  [IsNoetherianRing S]

/-- Exact original-object consumer of `compactFiniteResidue_module_finite`. -/
theorem actual_compact_finite_residue_module_compactFiniteResidue_module_finite_source (I : Ideal S) [IsHausdorff I S]
    (π : R) (hπ : algebraMap R S π ∈ I)
    [Finite (S ⧸ Ideal.span {algebraMap R S π})] : Module.Finite R S :=
  compactFiniteResidue_module_finite I π hπ

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S : Type} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
  [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space R] [T2Space S]
  [IsHausdorff (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `compactDVRLocalAlgebra_module_finite`. -/
theorem actual_compact_d_v_r_local_algebra_finite_compactDVRLocalAlgebra_module_finite_source : Module.Finite R S :=
  compactDVRLocalAlgebra_module_finite (R := R) (S := S)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_field_module_finite`. -/
theorem actual_local_field_integer_algebra_finite_localField_field_module_finite_source : FiniteDimensional K L :=
  localField_field_module_finite (K := K) (L := L)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

variable [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `unramifiedLocalFieldArithmeticH2Equiv_class`. -/
theorem actual_unramified_local_field_arithmetic_h2_unramifiedLocalFieldArithmeticH2Equiv_class_source (u : Additive Kˣ) :
    unramifiedLocalFieldArithmeticH2Equiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  unramifiedLocalFieldArithmeticH2Equiv_class g hg u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_integer_isIntegralClosure`. -/
theorem actual_local_field_integer_integral_closure_localField_integer_isIntegralClosure_source : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localField_integer_isIntegralClosure (K := K) (L := L)

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldIntegerGaloisEquiv_apply`. -/
theorem actual_local_field_integer_galois_restriction_localFieldIntegerGaloisEquiv_apply_source (g : Gal(L/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] L (localFieldIntegerGaloisEquiv K L g x) =
      g (algebraMap 𝒪[L] L x) :=
  localFieldIntegerGaloisEquiv_apply K L g x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `unramifiedSeparated_algEquiv_eq_of_residue`. -/
theorem actual_unramified_separated_residue_faithfulness_unramifiedSeparated_algEquiv_eq_of_residue_source (f g : S ≃ₐ[R] S)
    (h : ∀ x, residue S (f x) = residue S (g x)) : f = g :=
  unramifiedSeparated_algEquiv_eq_of_residue f g h

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]

/-- Exact original-object consumer of `localAlgebraAut_maximalIdeal_fixed`. -/
theorem actual_local_algebra_aut_maximal_stabilizer_localAlgebraAut_maximalIdeal_fixed_source (g : S ≃ₐ[R] S) :
    g • maximalIdeal S = maximalIdeal S :=
  localAlgebraAut_maximalIdeal_fixed g

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Exact original-object consumer of `localAlgebraAutResidueHom_apply`. -/
theorem actual_local_algebra_aut_residue_hom_localAlgebraAutResidueHom_apply_source (g : S ≃ₐ[R] S) (x : S) :
    localAlgebraAutResidueHom g (residue S x) = residue S (g x) :=
  localAlgebraAutResidueHom_apply g x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

variable [Finite (S ≃ₐ[R] S)] [Algebra.IsInvariant R S (S ≃ₐ[R] S)]

/-- Exact original-object consumer of `unramifiedLocalResidueAutEquiv_apply`. -/
theorem actual_unramified_local_residue_aut_equiv_unramifiedLocalResidueAutEquiv_apply_source (g : S ≃ₐ[R] S) (x : S) :
    unramifiedLocalResidueAutEquiv g (residue S x) = residue S (g x) :=
  unramifiedLocalResidueAutEquiv_apply g x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalFieldResidueGaloisEquiv_apply`. -/
theorem actual_unramified_local_field_residue_galois_unramifiedLocalFieldResidueGaloisEquiv_apply_source (g : Gal(L/K)) (x : 𝒪[L]) :
    unramifiedLocalFieldResidueGaloisEquiv K L g (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) :=
  unramifiedLocalFieldResidueGaloisEquiv_apply K L g x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_generates`. -/
theorem actual_local_field_arithmetic_frobenius_localFieldArithmeticFrobenius_generates_source (g : Gal(L/K)) :
    g ∈ Subgroup.zpowers (localFieldArithmeticFrobenius K L) :=
  localFieldArithmeticFrobenius_generates K L g

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

/-- Exact original-object consumer of `localFieldArithmeticH2Equiv_class`. -/
theorem actual_local_field_arithmetic_h2_normalization_localFieldArithmeticH2Equiv_class_source (u : Additive Kˣ) :
    localFieldArithmeticH2Equiv K L (localFieldArithmeticH2Class K L u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  localFieldArithmeticH2Equiv_class K L u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (n : ℕ) [NeZero n]

/-- Exact original-object consumer of `rationalCyclicInvariant_mem_range_iff`. -/
theorem actual_rational_cyclic_invariant_rationalCyclicInvariant_mem_range_iff_source (x : AddCircle (1 : ℚ)) :
    x ∈ (rationalCyclicInvariant n).range ↔ n • x = 0 :=
  rationalCyclicInvariant_mem_range_iff n x

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

/-- Exact original-object consumer of `unramifiedLocalRationalH2Invariant_class`. -/
theorem actual_unramified_local_rational_h2_invariant_unramifiedLocalRationalH2Invariant_class_source (u : Additive Kˣ) :
    unramifiedLocalRationalH2Invariant K L (localFieldArithmeticH2Class K L u) =
      ↑((localFieldUnitOrder K u : ℚ) / Module.finrank K L) :=
  unramifiedLocalRationalH2Invariant_class K L u

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_eq_of_residue`. -/
theorem actual_local_field_arithmetic_frobenius_uniqueness_localFieldArithmeticFrobenius_eq_of_residue_source (g : Gal(L/K))
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K]) :
    g = localFieldArithmeticFrobenius K L :=
  localFieldArithmeticFrobenius_eq_of_residue K L g hg

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localFieldIntegerGaloisEquiv_restrict`. -/
theorem actual_local_field_integer_galois_tower_localFieldIntegerGaloisEquiv_restrict_source (g : Gal(M/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] 𝒪[M]
        (localFieldIntegerGaloisEquiv K L (AlgEquiv.restrictNormalHom L g) x) =
      localFieldIntegerGaloisEquiv K M g (algebraMap 𝒪[L] 𝒪[M] x) :=
  localFieldIntegerGaloisEquiv_restrict K L M g x

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

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_restrict`. -/
theorem actual_local_field_arithmetic_frobenius_restriction_localFieldArithmeticFrobenius_restrict_source :
    AlgEquiv.restrictNormalHom L (localFieldArithmeticFrobenius K M) =
      localFieldArithmeticFrobenius K L :=
  localFieldArithmeticFrobenius_restrict K L M

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω) (b : Gal(Ω/K) → Ωˣ)
  (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
  (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitCochain_exists_finite_descent`. -/
theorem actual_galois_unit_cochain_finite_descent_galoisUnitCochain_exists_finite_descent_source :
    ∃ f : Gal(F/K) → Fˣ, ∀ g : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = b g :=
  galoisUnitCochain_exists_finite_descent F b hvalues hperiod

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

/-- Exact original-object consumer of `galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq`. -/
theorem actual_galois_unit_finite_coboundary_reflection_galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq_source
    (c : Gal(F/K) × Gal(F/K) → Fˣ) (b : Gal(Ω/K) → Ωˣ)
    (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
    (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)
    (hc : ∀ g h : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (c (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
          g • b h / b (g * h) * b g) :
    ∃ f : Gal(F/K) → Fˣ, ∀ σ τ : Gal(F/K),
      c (σ, τ) = Units.map σ (f τ) / f (σ * τ) * f σ :=
  galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq F c b hvalues hperiod hc

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_mk`. -/
theorem actual_finite_galois_unit_tower_inflation_finiteGaloisUnitTowerH2Inflation_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitTowerH2Inflation K L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitTowerCocycleInflation K L M c) :=
  finiteGaloisUnitTowerH2Inflation_mk K L M c

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_tower`. -/
theorem actual_galois_unit_finite_stage_tower_galoisUnitFiniteStageH2Inflation_tower_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitFiniteStageH2Inflation E x =
      galoisUnitFiniteStageH2Inflation F (finiteGaloisUnitTowerH2Inflation K E F x) :=
  galoisUnitFiniteStageH2Inflation_tower E F hEF x

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_zero_detected_at_finite_stage`. -/
theorem actual_continuous_galois_unit_h2_finite_zero_detection_continuousGaloisUnitH2_zero_detected_at_finite_stage_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E))
    (hx : galoisUnitFiniteStageH2Inflation E x = 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hEF : E ≤ F,
      letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      finiteGaloisUnitTowerH2Inflation K E F x = 0 :=
  continuousGaloisUnitH2_zero_detected_at_finite_stage E x hx

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower K L M] [IsScalarTower K L N]
  [IsScalarTower K M N] [IsScalarTower L M N]
  [FiniteDimensional K M] [FiniteDimensional K N]
  [IsGalois K L] [IsGalois K M] [IsGalois K N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K N)]

/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_comp`. -/
theorem actual_finite_galois_unit_tower_composition_finiteGaloisUnitTowerH2Inflation_comp_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    finiteGaloisUnitTowerH2Inflation K M N (finiteGaloisUnitTowerH2Inflation K L M x) =
      finiteGaloisUnitTowerH2Inflation K L N x :=
  finiteGaloisUnitTowerH2Inflation_comp K L M N x

end

end Dubon2026.SemanticRegression
