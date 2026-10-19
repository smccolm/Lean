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

/-- The actual source representation has its original component and prescribed base similitude. -/
theorem fixedResidualPolarizedUniversalRepresentation_characters (g : H) :
    polarizedComponent (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) =
        polarizedComponent (σ g) ∧
      polarizedSimilitude (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) =
        Units.map (algebraMap O (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν)).toMonoidHom (ν g) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  unfold fixedResidualPolarizedUniversalRepresentation
    FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedAlgebra
  exact representationPolarizedLocalCoefficientRepresentation_characters
    (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S)
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    σ (fun g => DFunLike.congr_fun
      (fixedResidualFramedUniversalRepresentation_residue p H
        (polarizedBlockRepresentation.comp σ) hσ S hS) g) ν hν g

end
end Dubon2026
