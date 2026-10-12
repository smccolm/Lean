import Dubon2026.ContinuousTrivialCocycleCoordinates
import Dubon2026.LocalFieldKummerCharacterFinite

/-! # Original local cocycles with finite constant prime-field coefficients

The finite-character theorem supplies every coordinate. This is the constant
coefficient input for finiteness of the full local H1 spaces in finite-module
duality, beyond the geometric subspaces already treated by deformation theory.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] continuousTrivialCoordinateSMul

variable (K Ω V : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [AddCommGroup V] [Module (ZMod q) V] [Finite V]
  [TopologicalSpace V] [DiscreteTopology V]

/-- The full set of original continuous trivial cocycles in a finite
prime-field module is finite. The auxiliary root and unit coefficient topologies
are constructed locally, so no such topology assumptions occur in the statement. -/
theorem localField_finiteTrivialCocycles (hq : (q : K) ≠ 0) :
    Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) Gal(Ω/K) V))) := by
  letI : TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q) := ⊥
  haveI : DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  haveI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  haveI := localField_continuousFiniteCharacters_finite K Ω q hq
  haveI : Module.Finite (ZMod q) V := Module.Finite.of_finite
  exact continuousTrivialCocycles_finite q

end
end Dubon2026
