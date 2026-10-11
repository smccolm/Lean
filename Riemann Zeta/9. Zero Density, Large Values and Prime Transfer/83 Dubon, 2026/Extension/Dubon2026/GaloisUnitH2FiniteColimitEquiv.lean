import Dubon2026.GaloisUnitH2FiniteColimitMap
import Dubon2026.ContinuousGaloisUnitH2FiniteZeroDetection
import Dubon2026.ContinuousGaloisUnitH2FiniteStage

/-! # Original continuous Galois unit H2 is its genuine finite-stage colimit -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact finite cocycle descent makes the actual colimit map surjective. -/
theorem galoisUnitH2FiniteColimitToH2_surjective :
    Function.Surjective (galoisUnitH2FiniteColimitToH2 K Ω) := by
  intro x
  obtain ⟨F, y, hy⟩ := continuousGaloisUnitH2_exists_finite_stage x
  refine ⟨Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
    (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F y, ?_⟩
  rw [galoisUnitH2FiniteColimitToH2_of]
  exact hy

/-- Actual continuous coboundary witnesses descend to finite stages,
so the original colimit map is injective. This does not assume injectivity of
individual finite-stage inflation maps. -/
theorem galoisUnitH2FiniteColimitToH2_injective :
    Function.Injective (galoisUnitH2FiniteColimitToH2 K Ω) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [galoisUnitH2FiniteColimitToH2_of] at hx
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  obtain ⟨F, hEF, hy⟩ := continuousGaloisUnitH2_zero_detected_at_finite_stage E y hx
  have hy' : galoisUnitH2FiniteTransition K Ω E F hEF y = 0 := hy
  rw [← Module.DirectLimit.of_f (hij := hEF), hy', map_zero]

/-- The actual finite-stage colimit is linearly equivalent to original
continuous Galois unit H2, by exact cocycle and coboundary descent. -/
def galoisUnitH2FiniteColimitEquiv :
    GaloisUnitH2FiniteColimit K Ω ≃ₗ[ℤ] GaloisUnitContinuousH2 (K := K) (Ω := Ω) :=
  LinearEquiv.ofBijective (galoisUnitH2FiniteColimitToH2 K Ω)
    ⟨galoisUnitH2FiniteColimitToH2_injective K Ω, galoisUnitH2FiniteColimitToH2_surjective K Ω⟩

/-- The colimit equivalence keeps the exact original finite-stage class. -/
theorem galoisUnitH2FiniteColimitEquiv_of (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitEquiv K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x := by
  exact galoisUnitH2FiniteColimitToH2_of K Ω F x

end
end Dubon2026
