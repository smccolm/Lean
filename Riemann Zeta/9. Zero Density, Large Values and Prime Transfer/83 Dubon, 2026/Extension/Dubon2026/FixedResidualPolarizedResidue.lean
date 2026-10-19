import Dubon2026.FixedResidualPolarizedRepresentationMatrices
import Dubon2026.FixedResidualPolarizedRepresentationCharacters
import Dubon2026.PolarizedResidualComparison

/-! The true residue field and original residual representation of the
source polarized coefficient quotient. These are proved compatibilities
of the constructed quotient, not separately supplied identifications,
on DUB-17's CM deformation route. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  (p : ℕ) (H : ProfiniteGrp.{u})
  (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The actual polarized quotient has its original coefficient residue field. -/
@[irreducible] def fixedResidualPolarizedCoefficientResidueEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     IsLocalRing.ResidueField (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) ≃ₐ[O]
       IsLocalRing.ResidueField O) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedAlgebra
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  have hlocal := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing at hlocal
  exact @originalLocalQuotientResidueEquiv O _ _ _ _ _ _
    (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S) _ hlocal

/-- The actual residue identification preserves reduction of every original coefficient. -/
theorem fixedResidualPolarizedCoefficientResidueEquiv_original :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
     letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ r : FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S,
       localCoefficientReduction (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν)
           (fixedResidualPolarizedCoefficientMap p H σ hσ S hS ν r) =
         localCoefficientReduction
           (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S) r) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  intro r
  unfold fixedResidualPolarizedCoefficientMap fixedResidualPolarizedCoefficientResidueEquiv
    FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing fixedResidualPolarizedAlgebra
  have hlocal := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing at hlocal
  exact @originalLocalQuotientResidueEquiv_original O _ _ _ _ _ _
    (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S) _ hlocal r

variable [Nonempty ι]

/-- The actual quotient representation reduces to the original full polarized residual representation. -/
theorem fixedResidualPolarizedUniversalRepresentation_residue :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ g : H, polarizedCoefficientMap
         (localCoefficientReduction
           (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν)).toRingHom
         (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) = σ g) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  let eR := fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S
  let eQ := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  have hf : (localCoefficientReduction eQ).toRingHom.comp
      (fixedResidualPolarizedCoefficientMap p H σ hσ S hS ν).toRingHom =
      (localCoefficientReduction eR).toRingHom := by
    ext r
    exact fixedResidualPolarizedCoefficientResidueEquiv_original p H σ hσ S hS ν hν r
  intro g
  exact polarizedRepresentation_residue_of_block_diagram
    (fixedResidualPolarizedCoefficientMap p H σ hσ S hS ν).toRingHom
    (localCoefficientReduction eQ).toRingHom (localCoefficientReduction eR).toRingHom
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν) σ hf
    (fixedResidualPolarizedUniversalRepresentation_block p H σ hσ S hS ν hν)
    (fun x => DFunLike.congr_fun
      (fixedResidualFramedUniversalRepresentation_residue p H
        (polarizedBlockRepresentation.comp σ) hσ S hS) x) g

end
end Dubon2026
