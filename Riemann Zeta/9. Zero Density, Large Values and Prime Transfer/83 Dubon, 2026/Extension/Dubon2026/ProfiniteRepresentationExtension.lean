import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-! # Actual extension of original group representations to the genuine profinite completion -/

namespace Dubon2026

noncomputable section
open CategoryTheory

universe u
variable {G H : Type u} [Group G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]

/-- An original representation into a genuine profinite target extends over the actual finite-quotient completion. -/
def profiniteRepresentationExtension (τ : G →* H) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H :=
  (ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of H) (GrpCat.ofHom τ)).hom

/-- The genuine extension has exactly the original representation value on every original group element. -/
theorem profiniteRepresentationExtension_eta (τ : G →* H) (g : G) :
    profiniteRepresentationExtension τ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      τ g :=
  ConcreteCategory.congr_hom
    (ProfiniteGrp.ProfiniteCompletion.lift_eta (P := ProfiniteGrp.of H) (GrpCat.ofHom τ)) g

/-- Continuity and the genuine density of the original group determine the extension uniquely. -/
theorem profiniteRepresentationExtension_unique (τ : G →* H)
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hσ : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = τ g) :
    σ = profiniteRepresentationExtension τ := by
  apply ContinuousMonoidHom.ext
  have he := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    σ.continuous_toFun (profiniteRepresentationExtension τ).continuous_toFun
    (funext fun g => (hσ g).trans (profiniteRepresentationExtension_eta τ g).symm)
  exact congrFun he

end
end Dubon2026
