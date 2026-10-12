import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Connecting maps commute with original group and coefficient maps -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {X : ShortComplex (Rep.{0} k H)} {Y : ShortComplex (Rep.{0} k G)}
  (f : G →* H) (φ : X.map (Rep.resFunctor f) ⟶ Y)

/-- Apply the actual cochain pullbacks and original coefficient maps
to a commuting map between the original short coefficient sequences. -/
def originalGroupChangeCochainSequenceMap :
    X.map (groupCohomology.cochainsFunctor k H) ⟶
      Y.map (groupCohomology.cochainsFunctor k G) where
  τ₁ := groupCohomology.cochainsMap f φ.τ₁
  τ₂ := groupCohomology.cochainsMap f φ.τ₂
  τ₃ := groupCohomology.cochainsMap f φ.τ₃
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext g
    exact congrArg (fun t : Rep.res f X.X₁ ⟶ Y.X₂ => t.hom (x (f ∘ g))) φ.comm₁₂
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext g
    exact congrArg (fun t : Rep.res f X.X₂ ⟶ Y.X₃ => t.hom (x (f ∘ g))) φ.comm₂₃

/-- The original connecting map commutes with the actual group-change
cohomology maps. This is naturality of the genuine cochain snake sequence. -/
theorem originalCohomologyGroupChange_delta_naturality
    (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map f φ.τ₁ j =
      groupCohomology.map f φ.τ₃ i ≫ groupCohomology.δ hY i j hij := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (originalGroupChangeCochainSequenceMap f φ)
    (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact hY) i j hij

end
end Dubon2026
