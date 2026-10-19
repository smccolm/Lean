import Dubon2026.FixedResidualPolarizedRepresentation

/-! Exact original matrix and character compatibility for the constructed polarized representation on the DUB-17 CM deformation route. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
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

/-- Every original universal matrix is retained modulo the actual polarized ideal. -/
theorem fixedResidualPolarizedUniversalRepresentation_block (g : H) :
    polarizedBlockRepresentation (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) =
      GeneralLinearGroup.map (fixedResidualPolarizedCoefficientMap p H σ hσ S hS ν).toRingHom
        (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS g) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  unfold fixedResidualPolarizedUniversalRepresentation fixedResidualPolarizedCoefficientMap
    FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedAlgebra
  exact representationPolarizedLocalCoefficientRepresentation_block
    (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S)
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    σ (fun g => DFunLike.congr_fun
      (fixedResidualFramedUniversalRepresentation_residue p H
        (polarizedBlockRepresentation.comp σ) hσ S hS) g) ν hν g


end
end Dubon2026
