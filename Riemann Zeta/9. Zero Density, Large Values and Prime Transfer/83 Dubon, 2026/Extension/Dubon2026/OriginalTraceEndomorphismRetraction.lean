import Dubon2026.ClosedMatrixTraceAlgebra
import Dubon2026.CoefficientSubalgebraRetraction

/-! # An actual representation-conjugating endomorphism fixes its original closed trace coefficients -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing K] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- A genuine continuous coefficient endomorphism preserving the whole original representation up to strict conjugacy fixes every element of its literal closed trace algebra. -/
theorem originalTraceEndomorphism_fixes_trace_algebra
    (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (f : R →ₐ[O] R) (hf : Continuous f)
    (h : MatrixStrictlyConjugate r ((GeneralLinearGroup.map f.toRingHom).comp ρ) ρ)
    (x : closedMatrixTraceAlgebra (O := O) ρ) : f x = (x : R) := by
  have heq := eqOn_closedMatrixTraceAlgebra ρ f (AlgHom.id O R) hf continuous_id
  apply heq _ x.property
  intro g
  have ht := matrixStrictlyConjugate_trace r _ _ h g
  change Matrix.trace (ρ g).val = Matrix.trace ((ρ g).val.map f) at ht
  rw [← AddMonoidHom.map_trace] at ht
  exact ht.symm

/-- The actual original trace ring is Noetherian if a continuous representation-conjugating endomorphism of the original Noetherian coefficient ring has its proved image in that trace ring. -/
theorem originalTraceAlgebra_isNoetherian_of_endomorphism [IsNoetherianRing R]
    (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (f : R →ₐ[O] R) (hf : Continuous f)
    (h : MatrixStrictlyConjugate r ((GeneralLinearGroup.map f.toRingHom).comp ρ) ρ)
    (himage : ∀ x, f x ∈ closedMatrixTraceAlgebra (O := O) ρ) :
    IsNoetherianRing (closedMatrixTraceAlgebra (O := O) ρ) := by
  exact coefficientSubalgebra_isNoetherian_of_retraction _ f himage
    (originalTraceEndomorphism_fixes_trace_algebra r ρ f hf h)

end
end Dubon2026
