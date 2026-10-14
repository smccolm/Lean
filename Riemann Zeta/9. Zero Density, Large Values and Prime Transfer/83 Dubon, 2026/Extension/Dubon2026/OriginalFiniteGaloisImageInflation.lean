import Dubon2026.OriginalFiniteGaloisImage
import Dubon2026.ContinuousGaloisBaseChangeFiniteStage

/-! # Inflation through the actual finite image preserves the original class

This puts the constructed cyclic arithmetic stage inside the same original
unramified union as a bundled finite stage. It is the exact entry needed
for DUB-17's existing arithmetic finite-local restriction and carry pairing.
-/
namespace Dubon2026
noncomputable section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Finite inflation from the literal image of an original finite Galois field equals original continuous inflation, on the same class. -/
theorem originalFiniteGaloisImage_inflation
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    let E := originalFiniteGaloisImage K L Ω
    letI := originalFiniteGaloisImageAlgebra K L Ω
    letI := originalFiniteGaloisImage_baseTower K L Ω
    letI := originalFiniteGaloisImage_ambientTower K L Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
    galoisUnitFiniteStageH2Inflation E (finiteGaloisUnitBaseChangeH2 K K L E x) =
      continuousGaloisUnitBaseChangeH2 K K L Ω x := by
  let E := originalFiniteGaloisImage K L Ω
  letI := originalFiniteGaloisImageAlgebra K L Ω
  letI := originalFiniteGaloisImage_baseTower K L Ω
  letI := originalFiniteGaloisImage_ambientTower K L Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact (continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω E
    (finiteGaloisUnitBaseChangeH2 K K L E x)).symm.trans
      (continuousGaloisUnitBaseChangeH2_comp K K K L E Ω x)

end
end Dubon2026
