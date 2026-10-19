import Dubon2026.FixedResidualPolarizedLocalData
import Dubon2026.PolarizedLocalCoefficientRepresentation
import Dubon2026.LocalQuotientCoefficientFibers

/-! The source polarized representation over the actual quotient of the
native framed coefficient ring. This consumer preserves the original
matrix family and fixed characters required for DUB-17's CM deformation
comparison. The arithmetic residual inputs remain explicit. -/

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

/-- The literal source polarized representation over its actual original coefficient quotient. -/
@[irreducible] def fixedResidualPolarizedUniversalRepresentation :
    H →* PolarizedGaloisGroup ι (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  let eR := fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S
  exact representationPolarizedLocalCoefficientRepresentation eR
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    σ (fun g => DFunLike.congr_fun
      (fixedResidualFramedUniversalRepresentation_residue p H
        (polarizedBlockRepresentation.comp σ) hσ S hS) g) ν hν

/-- The original coefficient quotient map imposing the literal source polarized equations. -/
@[irreducible] def fixedResidualPolarizedCoefficientMap :
    FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S →ₐ[O]
      FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedAlgebra
  exact Ideal.Quotient.mkₐ O _

end
end Dubon2026
