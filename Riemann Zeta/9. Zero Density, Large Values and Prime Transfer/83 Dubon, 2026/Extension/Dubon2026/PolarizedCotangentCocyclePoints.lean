import Dubon2026.PolarizedDualCoefficientBridge
import Dubon2026.FixedResidualPolarizedUniversality
import Dubon2026.OriginalRelativeCotangentPoints
import Dubon2026.OriginalRelativeCotangentDual

/-! The actual complete local polarized coefficient quotient has its
original relative cotangent points identified with continuous full-adjoint
cocycles. This composes native residue derivations and coefficient
universality with the exact dual-number bridge. It is the source cotangent
entry on DUB-17's Selmer route; linearity and local crystalline conditions
are not asserted by this equivalence of underlying sets. -/

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

/-- The original relative cotangent maps of the actual polarized quotient classify its genuine continuous full-adjoint cocycles. -/
def fixedResidualPolarizedCotangentCocycleEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     OriginalResidueCotangentMaps
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) ≃
       continuousRepresentationCocyclesOne (polarizedAdjointRep σ)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  let k := IsLocalRing.ResidueField O
  letI : WithIdeal (DualNumber k) := ⟨IsLocalRing.maximalIdeal (DualNumber k)⟩
  letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber k)) (DualNumber k) :=
    finiteDualNumber_maximal_isAdicComplete k
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  have hd := fixedResidualPolarizedCoefficientRing_localData p H σ hσ S hS ν hν
  have hc : Continuous σ := (continuous_polarized_iff_block σ).mpr hσ
  exact (originalResidueCotangentContinuousFiberEquiv hd.2.1 eR).trans
    ((fixedResidualPolarizedFiberEquiv rfl (relativeDualNumberResidueEquiv O)
      p hp H σ hσ S hS ν hν).trans
      ((originalPolarizedDualFiberEquiv H σ ν hν).trans
        (continuousPolarizedFirstOrderLiftEquiv σ hc)))

/-- The original residue-field dual of the literal maximal-ideal cotangent quotient has the same actual continuous cocycle points. -/
def fixedResidualPolarizedMaximalCotangentCocycleEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     OriginalRelativeMaximalCotangentDual
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) ≃
       continuousRepresentationCocyclesOne (polarizedAdjointRep σ)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  exact ((originalMaximalCotangentDualLinearEquiv eR).symm.toEquiv.trans
    (originalResidueMaximalCotangentLinearEquiv eR).toEquiv).trans
      (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν)

end
end Dubon2026
