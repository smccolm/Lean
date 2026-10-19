import Dubon2026.FixedResidualPolarizedResidue
import Dubon2026.PolarizedQuotientUniversality

/-! Restricting the native framed universal property by the literal
polarized coefficient equations. The result classifies genuine continuous
polarized lifts over all complete Noetherian local coefficient algebras
with their original residue comparison and prescribed similitude. This
serves the source CM deformation comparison in DUB-17; the original
arithmetic residual representation and finite generators remain inputs. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
  (H : ProfiniteGrp.{u}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The actual polarized coefficient quotient classifies all original continuous
polarized lifts with fixed similitude over genuine complete local coefficient algebras. -/
@[irreducible] def fixedResidualPolarizedFiberEquiv :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     OriginalContinuousCoefficientFiber
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) eA ≃
       OriginalContinuousPolarizedFiber eA H σ ν) := by
  unfold fixedResidualPolarizedCoefficientResidueEquiv FixedResidualPolarizedCoefficientRing
    fixedResidualPolarizedCommRing fixedResidualPolarizedAlgebra
    fixedResidualPolarizedTopologicalSpace
  let R := FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  have hlocal := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing at hlocal
  letI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_equiv (IsLocalRing.ResidueField O) eA.toEquiv.symm
  letI : T2Space A := completeLocalAdic_t2Space hA
  letI : CompactSpace A := completeLocalAdic_compactSpace hA
  let eR := fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S
  let τ := fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS
  let χ := (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ
  let J := representationPolarizedIdeal τ χ ((Units.map (algebraMap O R).toMonoidHom).comp ν)
  letI : IsLocalRing (R ⧸ J) := hlocal
  let F := fixedResidualFramedFiberEquiv hA eA p hp H (polarizedBlockRepresentation.comp σ) hσ S hS
  exact polarizedQuotientFiberEquiv eR eA H σ ν τ F
    (fixedResidualFramedFiberEquiv_evaluation hA eA p hp H
      (polarizedBlockRepresentation.comp σ) hσ S hS)

end
end Dubon2026
