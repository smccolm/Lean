import Dubon2026.FixedResidualPolarizedEvaluation

/-! Coefficient naturality of the actual polarized classification serving DUB-17. -/

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

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The original polarized classification is natural under every genuine continuous
residue-preserving coefficient map, evaluated at every original group element. -/
theorem fixedResidualPolarizedFiberEquiv_natural
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ (f : OriginalContinuousCoefficientFiber
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν) eA) (g : H),
       (fixedResidualPolarizedFiberEquiv hB eB p hp H σ hσ S hS ν hν
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val g =
       polarizedCoefficientMap k.toRingHom
         ((fixedResidualPolarizedFiberEquiv hA eA p hp H σ hσ S hS ν hν f).val g)) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  intro f g
  calc
    (fixedResidualPolarizedFiberEquiv hB eB p hp H σ hσ S hS ν hν
        (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val g =
        polarizedCoefficientMap (k.toRingHom.comp f.val.toRingHom)
          (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) :=
      fixedResidualPolarizedFiberEquiv_evaluation hB eB p hp H σ hσ S hS ν hν _ g
    _ = polarizedCoefficientMap k.toRingHom
        (polarizedCoefficientMap f.val.toRingHom
          (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g)) :=
      DFunLike.congr_fun (polarizedCoefficientMap_comp f.val.toRingHom k.toRingHom) _
    _ = _ := congrArg (polarizedCoefficientMap k.toRingHom)
      (fixedResidualPolarizedFiberEquiv_evaluation hA eA p hp H σ hσ S hS ν hν f g).symm

end
end Dubon2026
