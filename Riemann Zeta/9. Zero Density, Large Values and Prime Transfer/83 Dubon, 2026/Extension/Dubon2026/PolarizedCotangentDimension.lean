import Dubon2026.PolarizedCotangentLinearity
import Dubon2026.PolarizedAdjointCoboundaryDimension
import Dubon2026.OriginalRelativeCotangentDualFiniteness

/-! The actual polarized coefficient quotient supplies finiteness and the
original framed tangent dimension used by the DUB-17 Selmer comparison.
No crystalline local condition or its dimension is assumed here. -/

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

include hp hS hν in
/-- The actual Noetherian polarized coefficient quotient proves finite-dimensionality of its original continuous full-adjoint cocycles. -/
theorem fixedResidualPolarizedCocycles_finite :
    Module.Finite (IsLocalRing.ResidueField O)
      (continuousRepresentationCocyclesOne (polarizedAdjointRep σ)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  letI := (fixedResidualPolarizedCoefficientRing_localData p H σ hσ S hS ν hν).1
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  letI := originalRelativeMaximalCotangentDual_finite eR
  let e := fixedResidualPolarizedMaximalCotangentCocycleLinearEquiv p hp H σ hσ S hS ν hν
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

include hp in
/-- The literal original maximal-ideal cotangent quotient obeys the full-adjoint framed versus strict-class dimension formula. -/
theorem fixedResidualPolarizedCotangent_finrank_add_invariants :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
     letI := originalMaximalCotangentResidueModule eR
     Module.finrank (IsLocalRing.ResidueField O)
       (RelativeMaximalCotangent O (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν)) +
       Module.finrank (IsLocalRing.ResidueField O)
         (Representation.invariants (polarizedAdjointRepresentation.comp σ)) =
       Module.finrank (IsLocalRing.ResidueField O)
         (ContinuousRepresentationH1 (polarizedAdjointRep σ)
           (polarizedAdjointAction_continuous σ ((continuous_polarized_iff_block σ).mpr hσ))) +
         Fintype.card ι ^ 2) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  letI := originalMaximalCotangentResidueModule eR
  letI := fixedResidualPolarizedCocycles_finite p hp H σ hσ S hS ν hν
  dsimp only
  rw [← originalRelativeMaximalCotangentDual_finrank eR,
    (fixedResidualPolarizedMaximalCotangentCocycleLinearEquiv p hp H σ hσ S hS ν hν).finrank_eq]
  exact continuousPolarizedAdjointCocycles_finrank_add_invariants σ
    ((continuous_polarized_iff_block σ).mpr hσ)

end
end Dubon2026

