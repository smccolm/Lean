import Dubon2026.FiniteCoefficientCocycleDescent
import Dubon2026.ContinuousCohomologyCoefficientMap
import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual finite-stage presentation of original finite-coefficient H2

Both the finite coefficient action and representative cocycle are constructed.
The inflation uses the original Galois restriction and the identity on actual
coefficients, preparing DUB-17's finite support through local unramified stages.
-/

namespace Dubon2026
noncomputable section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- Actual finite-stage inflation, with the same original coefficient vectors
and the proved comparison of the original and descended actions. -/
def finiteCoefficientGaloisH2Inflation (F : FiniteGaloisIntermediateField K Ω)
    (ρ : Representation R Gal(F/K) A)
    (hρ : ∀ g : Gal(Ω/K), ∀ a : A, ρ (AlgEquiv.restrictNormalHom F g) a = A.ρ g a) :
    ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology →ₗ[R]
      ContinuousRepresentationH2 A hA := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Continuous j := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  exact (continuousCoefficientH2Map (restrictedCoefficientRep (Rep.of ρ) j) A
    LinearMap.id continuous_id hρ
    (restrictedCoefficientAction_continuous (Rep.of ρ) j hj continuous_of_discreteTopology) hA).comp
      (continuousRepresentationH2Restriction (Rep.of ρ) continuous_of_discreteTopology j hj)

/-- Every original finite-coefficient continuous H2 class comes from a
constructed actual finite Galois stage, with exact original inflation equality. -/
theorem continuousFiniteCoefficientH2_exists_finite_stage [Finite A]
    (x : ContinuousRepresentationH2 A hA) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ρ : Representation R Gal(F/K) A,
        ∃ hρ : ∀ g : Gal(Ω/K), ∀ a : A, ρ (AlgEquiv.restrictNormalHom F g) a = A.ρ g a,
          ∃ y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology,
            finiteCoefficientGaloisH2Inflation A hA F ρ hρ y = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨F, ρ, d, hρ, hd⟩ := continuousFiniteCoefficientTwoCocycle_exists_finite_descent A c hA
    refine ⟨F, ρ, hρ, Submodule.Quotient.mk d, ?_⟩
    unfold finiteCoefficientGaloisH2Inflation
    rw [LinearMap.comp_apply, continuousRepresentationH2Restriction_mk,
      continuousCoefficientH2Map_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact hd z.1 z.2

end
end Dubon2026
