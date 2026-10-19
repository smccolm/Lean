import Dubon2026.FixedResidualPolarizedQuotient
import Dubon2026.OriginalAdicLocalQuotientData

/-! The same source-compatible polarized coefficient quotient is complete,
Noetherian and maximally adic in its original quotient topology. This
reuses native framed and quotient results rather than constructing a new
completion for the DUB-17 CM deformation problem. -/

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

/-- The actual polarized quotient inherits complete local Noetherian data in its own topology. -/
theorem fixedResidualPolarizedCoefficientRing_localData :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     IsNoetherianRing (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) ∧
       IsAdic (IsLocalRing.maximalIdeal (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν)) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν))
         (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν)) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedTopologicalSpace
  let R := FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  let eR := fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S
  have hd := fixedResidualFramedCoefficientRing_localData p H (polarizedBlockRepresentation.comp σ) hσ S
  letI : IsNoetherianRing R := hd.1
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hd.2.1
  letI : Finite (IsLocalRing.ResidueField R) :=
    Finite.of_equiv (IsLocalRing.ResidueField O) eR.toEquiv.symm
  have hlocal := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing at hlocal
  exact @originalAdicLocalQuotient_localData R _ _ _ _ _ _ _ hd.2.2 _ hlocal

end
end Dubon2026
