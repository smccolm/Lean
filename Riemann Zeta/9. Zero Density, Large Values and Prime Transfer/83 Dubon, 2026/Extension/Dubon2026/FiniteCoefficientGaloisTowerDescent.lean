import Dubon2026.FiniteCoefficientGaloisDescent

/-! The larger field constructed by the original relation-extension criterion
must carry the restriction of the original descended coefficient. These
identities discharge that action comparison in DUB-17's route from a zero
Cartier total to reverse H1 localization; no new representation is assumed. -/
namespace Dubon2026
noncomputable section

variable {R K Ω : Type} [CommRing R] [Field K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) (F N : FiniteGaloisIntermediateField K Ω)
  (hFN : F.toIntermediateField ≤ N.toIntermediateField)
  (hF : ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a)

include hFN hF in
omit [IsGalois K Ω] in
/-- A larger original finite field still kills the original coefficient kernel. -/
theorem finiteStageCoefficientKernel_mono :
    ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom N u = 1 → ∀ a : A, A.ρ u a = a := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : IsScalarTower K F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  letI : IsScalarTower F N Ω := IsScalarTower.of_algebraMap_eq' rfl
  intro u hu a
  apply hF u _ a
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F N, hu, map_one]

/-- Descending at the actual larger stage gives exactly the restricted
original finite action, pointwise on the unchanged coefficient carrier. -/
theorem finiteStageCoefficientRepresentation_restrict
    (u : Gal(N/K)) (a : A) :
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : IsScalarTower K F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
    finiteStageCoefficientRepresentation A N (finiteStageCoefficientKernel_mono A F N hFN hF) u a =
      finiteStageCoefficientRepresentation A F hF (AlgEquiv.restrictNormalHom F u) a := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : IsScalarTower K F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  letI : IsScalarTower F N Ω := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω u
  rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F N,
    finiteStageCoefficientRepresentation_apply, finiteStageCoefficientRepresentation_apply]

end
end Dubon2026
