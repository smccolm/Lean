import Dubon2026.ContinuousFiniteCoefficientCocycleStage

/-! # Descent of the original coefficient action to an actual finite Galois field

This retains the nontrivial action needed to descend actual arithmetic H2
cocycles before applying unramified-stage vanishing for DUB-17 local support.
-/

namespace Dubon2026
noncomputable section

variable {R K Ω : Type} [CommRing R] [Field K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) (F : FiniteGaloisIntermediateField K Ω)
  (hker : ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a)

/-- The original action descends along actual surjective Galois restriction. -/
def finiteStageCoefficientRepresentation : Representation R Gal(F/K) A :=
  (Units.coeHom (A →ₗ[R] A)).comp
    ((AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)).liftOfSurjective
      (AlgEquiv.restrictNormalHom_surjective Ω)
      ⟨A.ρ.asGroupHom, fun u hu => by
        apply Units.ext
        apply LinearMap.ext
        exact hker u hu⟩)

/-- Every descended coefficient action has precisely the original value
on restriction of the same original field automorphism. -/
theorem finiteStageCoefficientRepresentation_apply (g : Gal(Ω/K)) (a : A) :
    finiteStageCoefficientRepresentation A F hker (AlgEquiv.restrictNormalHom F g) a =
      A.ρ g a := by
  unfold finiteStageCoefficientRepresentation
  rw [MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

end
end Dubon2026
