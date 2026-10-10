import Dubon2026.CompletedResidualSubalgebraImage
import Dubon2026.CompletedPresentationRepresentation

/-! # The actual whole presented representation controls every completed coefficient image -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [Algebra O A] [TopologicalSpace A]

/-- The actual original presented coefficient map lands in a closed unit-reflecting coefficient subalgebra as soon as the images of its whole original universal representation entries do. -/
theorem completedPresentation_image_mem_subalgebra
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (S : Subalgebra O A) (hS : IsClosed (S : Set A))
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x)
    (f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A)
    (hf : Continuous f)
    (hentry : ∀ h i j, f ((completedPresentationRepresentation ρ H q hq h).val i j) ∈ S)
    (x : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker) : f x ∈ S := by
  let J := completedPresentationRelationIdeal ρ q.toMonoidHom.ker
  let π := Ideal.Quotient.mkₐ O J
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply completedResidual_image_mem_subalgebra ρ S hS hunit (f.comp π)
    (hf.comp (QuotientRing.isOpenQuotientMap_mk J).continuous)
  intro g i j
  have he := hentry (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) i j
  rw [completedPresentationRepresentation_original,
    completedUniversalProfiniteRepresentation_eta] at he
  exact he

end
end Dubon2026
