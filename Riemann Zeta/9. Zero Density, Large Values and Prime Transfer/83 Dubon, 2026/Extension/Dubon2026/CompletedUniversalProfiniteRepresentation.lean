import Dubon2026.CompletedResidualMatrixTopology
import Dubon2026.ProfiniteRepresentationExtension

/-! # The actual original completed universal representation on the genuine profinite completion -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original completed universal matrix representation extends continuously to the actual profinite completion of its original abstract group. -/
def completedUniversalProfiniteRepresentation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι (ResidualRepresentationCompletion ρ) :=
  profiniteRepresentationExtension (completedUniversalMatrixRepresentation ρ)

/-- The genuine continuous universal representation retains every original whole matrix value. -/
theorem completedUniversalProfiniteRepresentation_eta
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (g : G) :
    completedUniversalProfiniteRepresentation ρ
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
        completedUniversalMatrixRepresentation ρ g :=
  profiniteRepresentationExtension_eta (completedUniversalMatrixRepresentation ρ) g

/-- The actual continuous representation extending the original completed universal matrices is unique. -/
theorem completedUniversalProfiniteRepresentation_unique
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hσ : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      completedUniversalMatrixRepresentation ρ g) :
    σ = completedUniversalProfiniteRepresentation ρ :=
  profiniteRepresentationExtension_unique (completedUniversalMatrixRepresentation ρ) σ hσ

end
end Dubon2026
