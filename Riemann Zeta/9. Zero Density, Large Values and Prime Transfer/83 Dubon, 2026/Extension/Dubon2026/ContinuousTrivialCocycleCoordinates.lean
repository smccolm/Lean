import Dubon2026.ContinuousRootCharacterCup
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual finite-field coordinates of continuous trivial cocycles

This reduces the constant-module finiteness input of local finite-module
duality to the already proved finiteness of actual finite characters.
-/

namespace Dubon2026
noncomputable section

variable {G V : Type} [Group G] [TopologicalSpace G]
  (q : ℕ) [Fact q.Prime] [AddCommGroup V] [Module (ZMod q) V]
  [TopologicalSpace V] [DiscreteTopology V]

/-- The original finite-field scalar action is continuous in the discrete topology. -/
local instance continuousTrivialCoordinateSMul : ContinuousSMul (ZMod q) V :=
  ⟨continuous_of_discreteTopology⟩

/-- Each actual finite-field linear coordinate of an original continuous
trivial cocycle is an actual continuous finite character. -/
def continuousTrivialCocycleCoordinateCharacter (ℓ : V →ₗ[ZMod q] ZMod q)
    (c : continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) G V))) :
    G →ₜ* Multiplicative (ZMod q) where
  toFun g := Multiplicative.ofAdd (ℓ (c.val g))
  map_one' := by
    change ℓ (c.val 1) = 0
    rw [groupCohomology.cocycles₁_map_one, map_zero]
  map_mul' g h := by
    change ℓ (c.val (g * h)) = ℓ (c.val g) + ℓ (c.val h)
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h
    change c.val (g * h) = c.val h + c.val g at hc
    rw [hc, map_add, add_comm]
  continuous_toFun := (continuous_of_discreteTopology (f := ℓ)).comp c.property

/-- Original continuous trivial cocycles are determined by their actual
coordinate characters in any basis of the original coefficient space. -/
theorem continuousTrivialCocycleCoordinates_injective {ι : Type} (b : Module.Basis ι (ZMod q) V) :
    Function.Injective (fun c : continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) G V)) =>
        fun i => continuousTrivialCocycleCoordinateCharacter q (b.coord i) c) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  exact congrArg (fun f => (f i g).toAdd) h

/-- Finiteness of original finite characters implies finiteness of all original
continuous trivial cocycles in a finite-dimensional prime-field space. -/
theorem continuousTrivialCocycles_finite [Module.Finite (ZMod q) V]
    [Finite (G →ₜ* Multiplicative (ZMod q))] :
    Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) G V))) := by
  exact Finite.of_injective _ (continuousTrivialCocycleCoordinates_injective q
    (Module.finBasis (ZMod q) V))

end
end Dubon2026
