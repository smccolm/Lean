import Dubon2026.FiniteBaseCMConjugation
import Dubon2026.PolarizedTwistedDual
import Dubon2026.MatrixRepresentationConjugation

/-! The actual residual CM symmetric power has the precise conjugate-dual
identity for the prescribed base multiplier. This discharges the residual
polarization hypothesis of DUB-17's trace-ring intertwiner construction. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Preserve the original rational algebra in the residual CM comparison. -/
local instance finiteBaseCMSymmetricResidualDualityUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {O : Type} [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
  (hn : (n.factorial : IsLocalRing.ResidueField O) ≠ 0)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K,
    (GeneralLinearGroup.det (ρ g.val)) ^ n =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g.val))

include hνk in
/-- The same original residual matrices satisfy conjugate duality with
their original real-place polarization and the reduction of the prescribed
base character. -/
theorem finiteBaseCMSymmetricResidual_duality :
    let σ := (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom
    σ.comp (finiteBaseCMConjugation a F K).toMonoidHom =
      matrixRepresentationConjugate
        (polarizedTwistedDual σ (((Units.map (algebraMap O (IsLocalRing.ResidueField O)).toMonoidHom).comp ν).comp
          (FiniteBaseCMKernel a F K).subtype))
        (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) := by
  dsimp only
  rw [finiteBaseCMConjugation_eq]
  apply MonoidHom.ext
  intro g
  have he := congrArg Prod.fst (finiteBaseCMSymmetricMatrices_polarization a F K n ρ hn g)
  change (finiteBaseCMSymmetricMatrices a F K n ρ
    ((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g)).1 =
      symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)) *
        (GeneralLinearGroup.scalar (Fin (n + 1)) ((GeneralLinearGroup.det (ρ g.val)) ^ n) *
          polarizedContragredient (homogeneousSymmetricGL n (ρ g.val))) *
        (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)))⁻¹ at he
  rw [hνk g] at he
  exact he

end
end Dubon2026
