import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Actual homology boundaries commute with group and coefficient maps

This is the chain analogue of the existing cohomology group-change map.
It supplies the ordinary-homology comparison needed to relate the actual
norm-homology equivalence to subgroup norms in DUB-17's prescribed-support
fixed-field construction. No reciprocity or inertia comparison is assumed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {X : ShortComplex (Rep.{0} k G)} {Y : ShortComplex (Rep.{0} k H)}
  (f : G →* H) (φ : X ⟶ Y.map (Rep.resFunctor f))

/-- The actual chain maps of a commuting group-change coefficient diagram
form a map between the literal short chain sequences. -/
def originalGroupChangeChainSequenceMap :
    X.map (groupHomology.chainsFunctor k G) ⟶
      Y.map (groupHomology.chainsFunctor k H) where
  τ₁ := groupHomology.chainsMap f φ.τ₁
  τ₂ := groupHomology.chainsMap f φ.τ₂
  τ₃ := groupHomology.chainsMap f φ.τ₃
  comm₁₂ := by
    change groupHomology.chainsMap f φ.τ₁ ≫
      groupHomology.chainsMap (MonoidHom.id H) Y.f =
      groupHomology.chainsMap (MonoidHom.id G) X.f ≫ groupHomology.chainsMap f φ.τ₂
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact congrArg (fun t : X.X₁ ⟶ Rep.res f Y.X₂ => groupHomology.chainsMap f t) φ.comm₁₂
  comm₂₃ := by
    change groupHomology.chainsMap f φ.τ₂ ≫
      groupHomology.chainsMap (MonoidHom.id H) Y.g =
      groupHomology.chainsMap (MonoidHom.id G) X.g ≫ groupHomology.chainsMap f φ.τ₃
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact congrArg (fun t : X.X₂ ⟶ Rep.res f Y.X₃ => groupHomology.chainsMap f t) φ.comm₂₃

/-- The literal homology connecting map is natural for the actual group
and coefficient maps. -/
theorem originalHomologyGroupChange_delta_naturality
    (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : j + 1 = i) :
    groupHomology.δ hX i j hij ≫ groupHomology.map f φ.τ₁ j =
      groupHomology.map f φ.τ₃ i ≫ groupHomology.δ hY i j hij := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (originalGroupChangeChainSequenceMap f φ)
    (groupHomology.map_chainsFunctor_shortExact hX)
    (groupHomology.map_chainsFunctor_shortExact hY) i j hij

end
end Dubon2026
