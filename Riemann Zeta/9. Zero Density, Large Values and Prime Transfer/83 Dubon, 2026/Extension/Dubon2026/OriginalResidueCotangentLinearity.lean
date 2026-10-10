import Dubon2026.OriginalRelativeCotangentPoints
import Dubon2026.OriginalResidueDerivationMatrices

/-! # Residue-field linearity of actual original relative cotangent maps -/

namespace Dubon2026

noncomputable section

variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The original residue field acts on genuine relative cotangent maps through the actual epsilon ideal. -/
instance originalResidueCotangentMapsModule
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module (IsLocalRing.ResidueField O) (OriginalResidueCotangentMaps eR) := by
  let K := IsLocalRing.ResidueField O
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  letI : SMulCommClass R K (TrivSqZeroExt.kerIdeal K K) := by
    refine ⟨?_⟩
    intro r k x
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
    exact mul_left_comm _ _ _
  exact inferInstanceAs (Module K (KaehlerDifferential O R →ₗ[R] TrivSqZeroExt.kerIdeal K K))

/-- The actual universal differential identifies original relative cotangent maps with original residue derivations linearly over the original residue field. -/
def originalResidueCotangentDerivationLinearEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueCotangentMaps eR ≃ₗ[IsLocalRing.ResidueField O] OriginalResidueDerivations eR := by
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  refine { (KaehlerDifferential.linearMapEquivDerivation O R
      (M := TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
        (IsLocalRing.ResidueField O))).toEquiv with
    map_add' := ?_, map_smul' := ?_ }
  · intro d e
    apply Derivation.ext
    intro r
    rfl
  · intro k d
    apply Derivation.ext
    intro r
    rfl

/-- The actual residue-field-linear comparison evaluates on every original universal differential. -/
theorem originalResidueCotangentDerivationLinearEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueCotangentMaps eR) (r : R) :
    originalResidueCotangentDerivationLinearEquiv eR d r =
      d (KaehlerDifferential.D O R r) := rfl

/-- The original cotangent and derivation classifications give exactly the same continuous coefficient point. -/
theorem originalResidueCotangentDerivationLinearEquiv_point
    [TopologicalSpace R]
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueCotangentMaps eR) :
    originalResidueDerivationContinuousFiberEquiv hR eR
      (originalResidueCotangentDerivationLinearEquiv eR d) =
        originalResidueCotangentContinuousFiberEquiv hR eR d := rfl

end
end Dubon2026
