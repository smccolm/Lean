import Dubon2026.PolarizedCotangentEvaluation
import Dubon2026.OriginalResidueCotangentLinearity

/-! Residue-field linearity of the actual polarized coefficient cotangent
comparison, serving the source tangent and Selmer comparison for DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
  (H : ProfiniteGrp) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The original continuous full-adjoint cocycle comparison preserves addition of the actual cotangent maps. -/
theorem fixedResidualPolarizedCotangentCocycleEquiv_add :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ d e : OriginalResidueCotangentMaps
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν),
       fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν (d + e) =
         fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν d +
           fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν e) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  intro d e
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro g
  change (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν (d + e)).val g =
    (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν d).val g +
      (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν e).val g
  rw [fixedResidualPolarizedCotangentCocycleEquiv_evaluation,
    fixedResidualPolarizedCotangentCocycleEquiv_evaluation,
    fixedResidualPolarizedCotangentCocycleEquiv_evaluation, ← add_mul]
  rfl

/-- The original cocycle comparison preserves scaling by the actual original residue field. -/
theorem fixedResidualPolarizedCotangentCocycleEquiv_smul :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ (a : IsLocalRing.ResidueField O) (d : OriginalResidueCotangentMaps
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν)),
       fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν (a • d) =
         a • fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν d) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  intro a d
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro g
  change (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν (a • d)).val g =
    a • (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν d).val g
  rw [fixedResidualPolarizedCotangentCocycleEquiv_evaluation,
    fixedResidualPolarizedCotangentCocycleEquiv_evaluation, ← smul_mul_assoc]
  rfl

/-- The actual original relative cotangent module is linearly equivalent to the continuous full-adjoint cocycles of the original polarized representation. -/
def fixedResidualPolarizedCotangentCocycleLinearEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     OriginalResidueCotangentMaps
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) ≃ₗ[IsLocalRing.ResidueField O]
       continuousRepresentationCocyclesOne (polarizedAdjointRep σ)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  exact { fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν with
    map_add' := fixedResidualPolarizedCotangentCocycleEquiv_add p hp H σ hσ S hS ν hν
    map_smul' := fixedResidualPolarizedCotangentCocycleEquiv_smul p hp H σ hσ S hS ν hν }

/-- The residue-field dual of the original relative maximal-ideal quotient is linearly equivalent to the actual continuous full-adjoint cocycles. -/
def fixedResidualPolarizedMaximalCotangentCocycleLinearEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     OriginalRelativeMaximalCotangentDual
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) ≃ₗ[IsLocalRing.ResidueField O]
       continuousRepresentationCocyclesOne (polarizedAdjointRep σ)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  exact ((originalMaximalCotangentDualLinearEquiv eR).symm.trans
    (originalResidueMaximalCotangentLinearEquiv eR)).trans
      (fixedResidualPolarizedCotangentCocycleLinearEquiv p hp H σ hσ S hS ν hν)

end
end Dubon2026

