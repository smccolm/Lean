import Dubon2026.OriginalPolarizedCoefficientClass
import Dubon2026.PolarizedTraceCoefficientUniqueness

/-! The precise unframed criterion used on DUB-17: original framed
universality, full polarized trace descent and existing CM trace generation
give a bijection with the actual strict polarized deformation classes. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {H ι O R A : Type} [Group H] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [T2Space A]
  (ρ : H →* GeneralLinearGroup ι R) [IsLocalRing (closedMatrixTraceAlgebra (O := O) ρ)]
  (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
  (eT : IsLocalRing.ResidueField (closedMatrixTraceAlgebra (O := O) ρ) ≃ₐ[O] IsLocalRing.ResidueField O)
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)

/-- The genuine full polarized trace descent classifies original
unframed lifts whenever the existing original framed representation
classifies the same lifts. Uniqueness comes from the actual CM traces. -/
theorem polarizedTraceUnframed_bijective_of_framed
    (G : ProfiniteGrp.{0}) (q : H →* G)
    (σ : G →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O)) (ν : G →* Oˣ)
    (υ : G →ₜ* PolarizedGaloisGroup ι R)
    (τ : G →ₜ* PolarizedGaloisGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (hτres : (polarizedCoefficientMap (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom = σ)
    (hτν : ∀ g, polarizedSimilitude (τ g) =
      Units.map (algebraMap O (closedMatrixTraceAlgebra (O := O) ρ)).toMonoidHom (ν g))
    (hcR : ∀ h, polarizedComponent (υ (q h)) = 1)
    (hcT : ∀ h, polarizedComponent (τ (q h)) = 1)
    (hm : polarizedIdentityMatrices (υ.toMonoidHom.comp q) hcR = ρ)
    (heT : localCoefficientReduction eT =
      (localCoefficientReduction eR).comp (closedMatrixTraceAlgebra (O := O) ρ).val)
    (hdesc : PolarizedStrictlyConjugate (localCoefficientReduction eR).toRingHom
      ((polarizedCoefficientMap (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ.toMonoidHom)
      υ.toMonoidHom)
    (hframed : ∀ ω : OriginalContinuousPolarizedFiber eA G σ ν,
      ∃ f : OriginalContinuousCoefficientFiber eR eA,
        (polarizedCoefficientMap f.val.toRingHom).comp υ.toMonoidHom = ω.val.toMonoidHom) :
    Function.Bijective (originalPolarizedCoefficientClass eT eA G σ ν τ hτres hτν) := by
  let T := closedMatrixTraceAlgebra (O := O) ρ
  have hmatrix := polarizedStrictlyConjugate_identityMatrices (localCoefficientReduction eR).toRingHom
    (((polarizedCoefficientMap T.val.toRingHom).comp τ.toMonoidHom).comp q)
    (υ.toMonoidHom.comp q)
    (fun h => (polarizedCoefficientMap_component T.val.toRingHom (τ (q h))).trans (hcT h)) hcR
    (polarizedStrictlyConjugate_comp _ _ _ hdesc q)
  rw [hm] at hmatrix
  constructor
  · intro f g hfg
    apply Subtype.ext
    exact polarizedTraceCoefficientMaps_eq (localCoefficientReduction eR).toRingHom ρ q
      τ.toMonoidHom hcT hmatrix f.val g.val f.property.1 g.property.1
      (localCoefficientReduction eA).toRingHom
      ((originalPolarizedCoefficientClass_eq_iff eT eA G σ ν τ hτres hτν f g).mp hfg)
  · intro c
    obtain ⟨ω, rfl⟩ := originalPolarizedUnframedClass_surjective eA G σ ν c
    obtain ⟨f, hf⟩ := hframed ω
    let g : OriginalContinuousCoefficientFiber eT eA :=
      ⟨f.val.comp T.val, f.property.1.comp continuous_subtype_val, by
        rw [← AlgHom.comp_assoc, f.property.2, ← heT]⟩
    refine ⟨g, ?_⟩
    apply (originalPolarizedUnframedClass_eq_iff eA G σ ν _ _).mpr
    have he := polarizedStrictlyConjugate_map (localCoefficientReduction eR).toRingHom
      (localCoefficientReduction eA).toRingHom f.val.toRingHom
      (congrArg AlgHom.toRingHom f.property.2) _ _ hdesc
    rw [hf] at he
    exact he

end
end Dubon2026
