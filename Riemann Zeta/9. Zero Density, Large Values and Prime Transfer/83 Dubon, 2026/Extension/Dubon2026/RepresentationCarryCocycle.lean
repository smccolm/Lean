import Dubon2026.ZModAdditionCarry
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Original representation cocycles from the actual cyclic addition carry -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- Pull the actual addition carry back through the displayed cyclic character,
with coefficients in the original invariant element of the original representation. -/
def representationCarryCocycle : groupCohomology.cocycles₂ A := by
  refine ⟨fun p => zmodAdditionCarry (χ p.1).toAdd (χ p.2).toAdd • a, ?_⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro x y z
  change zmodAdditionCarry (χ (x * y)).toAdd (χ z).toAdd • a +
      zmodAdditionCarry (χ x).toAdd (χ y).toAdd • a =
    A.ρ x (zmodAdditionCarry (χ y).toAdd (χ z).toAdd • a) +
      zmodAdditionCarry (χ x).toAdd (χ (y * z)).toAdd • a
  rw [map_nsmul, ha, ← add_nsmul, ← add_nsmul, χ.map_mul, χ.map_mul]
  exact congrArg (fun m : ℕ => m • a)
    (zmodAdditionCarry_assoc (χ x).toAdd (χ y).toAdd (χ z).toAdd)

/-- The constructed original cocycle keeps the literal carry and original coefficient. -/
theorem representationCarryCocycle_apply (x y : G) :
    representationCarryCocycle A χ a ha (x, y) =
      zmodAdditionCarry (χ x).toAdd (χ y).toAdd • a := by
  rfl

end
end Dubon2026
