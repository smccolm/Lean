import Dubon2026.FiniteGaloisImageH2Surjectivity
import Dubon2026.OriginalFiniteGaloisImageInflation
import Dubon2026.LocalFieldFiniteStageFundamentalClass

/-! # The normalized local class in the literal original finite extension

The existing finite-stage fundamental class is pulled back along the
actual field-image map. Its inflation and positive reciprocal-degree
normalization are proved, removing the local input in DUB-17's original
full-order idele-class construction.
-/
namespace Dubon2026
noncomputable section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The literal original finite Galois local extension has an actual class with positive reciprocal-degree invariant under its actual ambient inflation. -/
theorem originalFiniteLocal_exists_normalized_class :
    ∃ x : GaloisUnitContinuousH2 (K := K) (Ω := L),
      localFieldContinuousH2InvariantEquiv K Ω (continuousGaloisUnitBaseChangeH2 K K L Ω x) =
        (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) := by
  let E := originalFiniteGaloisImage K L Ω
  letI := originalFiniteGaloisImageAlgebra K L Ω
  letI := originalFiniteGaloisImage_baseTower K L Ω
  letI := originalFiniteGaloisImage_ambientTower K L Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  obtain ⟨x, hx⟩ := finiteGaloisUnitBaseChangeH2_surjective_of_equiv K L E
    (originalFiniteGaloisImageEquiv K L Ω) (fun _ => rfl)
    (localFieldFiniteStageFundamentalClass K Ω E)
  refine ⟨x, ?_⟩
  have hf := originalFiniteGaloisImage_inflation K L Ω x
  change galoisUnitFiniteStageH2Inflation E (finiteGaloisUnitBaseChangeH2 K K L E x) =
    continuousGaloisUnitBaseChangeH2 K K L Ω x at hf
  rw [hx] at hf
  have hv := localFieldFiniteStageFundamentalClass_invariant K Ω E
  change localFieldContinuousH2InvariantEquiv K Ω
    (galoisUnitFiniteStageH2Inflation E (localFieldFiniteStageFundamentalClass K Ω E)) = _ at hv
  rw [hf] at hv
  have hd : Module.finrank K E = Module.finrank K L :=
    (originalFiniteGaloisImageEquiv K L Ω).toLinearEquiv.finrank_eq.symm
  exact hv.trans (congrArg (fun n : ℕ => (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) hd)

end
end Dubon2026
