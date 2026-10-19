import Dubon2026.FixedResidualPolarizedUniversality

/-! Exact evaluation of the polarized coefficient classification on the DUB-17 CM route. -/

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

/-- The polarized classification evaluates the actual universal representation,
so the equivalence retains the original coefficient map and every original group element. -/
theorem fixedResidualPolarizedFiberEquiv_evaluation :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ (f : OriginalContinuousCoefficientFiber
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) eA) (g : H),
       (fixedResidualPolarizedFiberEquiv hA eA p hp H σ hσ S hS ν hν f).val g =
         polarizedCoefficientMap f.val.toRingHom
           (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  letI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_equiv (IsLocalRing.ResidueField O) eA.toEquiv.symm
  letI : T2Space A := completeLocalAdic_t2Space hA
  letI : CompactSpace A := completeLocalAdic_compactSpace hA
  intro f g
  apply polarizedBlockRepresentation_injective
  rw [← polarizedBlockRepresentation_map, fixedResidualPolarizedUniversalRepresentation_block]
  unfold fixedResidualPolarizedFiberEquiv fixedResidualPolarizedCoefficientMap
  unfold fixedResidualPolarizedCoefficientResidueEquiv FixedResidualPolarizedCoefficientRing
    fixedResidualPolarizedCommRing fixedResidualPolarizedAlgebra
    fixedResidualPolarizedTopologicalSpace at f ⊢
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  have hlocal := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing at hlocal
  exact polarizedQuotientFiberEquiv_block (hQ := hlocal)
    (fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S)
    eA H σ ν
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    (fixedResidualFramedFiberEquiv hA eA p hp H (polarizedBlockRepresentation.comp σ) hσ S hS)
    (fixedResidualFramedFiberEquiv_evaluation hA eA p hp H
      (polarizedBlockRepresentation.comp σ) hσ S hS) f g

end
end Dubon2026
