import Dubon2026.ClosedMatrixTraceAlgebra

/-! # Actual strict conjugacy and closed trace coefficients under a genuine surjective group map -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G H ι R K O : Type*} [Group G] [Group H] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing K]

/-- A genuine surjective original group map preserves and reflects the same whole strict conjugator and its actual residue identity. -/
theorem matrixStrictlyConjugate_comp_surjective_iff (r : R →+* K)
    (q : G →* H) (hq : Function.Surjective q) (ρ τ : H →* GeneralLinearGroup ι R) :
    MatrixStrictlyConjugate r (ρ.comp q) (τ.comp q) ↔ MatrixStrictlyConjugate r ρ τ := by
  constructor
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, ?_⟩
    intro x
    obtain ⟨g, rfl⟩ := hq x
    exact h g
  · rintro ⟨U, hU, h⟩
    exact ⟨U, hU, fun g => h (q g)⟩

omit [CommRing K] in
/-- Surjective original restriction preserves the literal closed trace coefficient algebra, since it preserves the exact range of actual whole representation traces. -/
theorem closedMatrixTraceAlgebra_comp_surjective [CommRing O] [Algebra O R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (q : G →* H) (hq : Function.Surjective q) (ρ : H →* GeneralLinearGroup ι R) :
    closedMatrixTraceAlgebra (O := O) (ρ.comp q) = closedMatrixTraceAlgebra (O := O) ρ := by
  have hr : Set.range (fun g : G => Matrix.trace ((ρ.comp q) g).val) =
      Set.range (fun h : H => Matrix.trace (ρ h).val) := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨q g, rfl⟩
    · rintro ⟨h, rfl⟩
      obtain ⟨g, rfl⟩ := hq h
      exact ⟨g, rfl⟩
  unfold closedMatrixTraceAlgebra
  rw [hr]

end
end Dubon2026
