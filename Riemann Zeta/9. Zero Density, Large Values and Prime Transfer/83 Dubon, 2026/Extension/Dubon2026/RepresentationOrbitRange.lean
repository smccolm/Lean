import Mathlib.RepresentationTheory.Basic
import Dubon2026.GramFamilyIsometry

/-! # The genuine algebraic cyclic range of an original group representation -/

namespace Dubon2026

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V)

/-- The literal image of finite linear combinations of the original orbit vectors. -/
def representationOrbitRange : Submodule ℂ V :=
  (Finsupp.linearCombination ℂ (fun g => ρ g v)).range

/-- The original finite-orbit image is exactly the original algebraic cyclic span. -/
theorem representationOrbitRange_eq_span :
    representationOrbitRange ρ v = Submodule.span ℂ (Set.range (fun g => ρ g v)) :=
  Finsupp.range_linearCombination ℂ

/-- Translation of the original finite orbit combination is its literal translated finite coefficient family. -/
theorem representation_orbit_linearCombination (g : G) (a : G →₀ ℂ) :
    ρ g (Finsupp.linearCombination ℂ (fun h => ρ h v) a) =
      Finsupp.linearCombination ℂ (fun h => ρ h v) (a.mapDomain (fun h => g * h)) := by
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_mapDomain]
  congr 1
  apply congrArg (Finsupp.linearCombination ℂ)
  funext h
  exact (congrArg (fun T : Module.End ℂ V => T v) (ρ.map_mul g h)).symm

/-- The actual algebraic cyclic range is stable under every original group action. -/
theorem representationOrbitRange_invariant (g : G) (x : V)
    (hx : x ∈ representationOrbitRange ρ v) : ρ g x ∈ representationOrbitRange ρ v := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a.mapDomain (fun h => g * h), (representation_orbit_linearCombination ρ v g a).symm⟩

/-- The original action restricted to its actual finite-orbit span. -/
def representationOrbitRepresentation : Representation ℂ G (representationOrbitRange ρ v) :=
  Representation.subrepresentation ρ (representationOrbitRange ρ v)
    (fun g x hx => representationOrbitRange_invariant ρ v g x hx)

/-- Every original orbit vector belongs to the genuine cyclic range. -/
theorem representationOrbitRange_orbit_mem (g : G) : ρ g v ∈ representationOrbitRange ρ v := by
  rw [representationOrbitRange_eq_span]
  exact Submodule.subset_span ⟨g, rfl⟩

end
end Dubon2026
