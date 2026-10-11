import Dubon2026.MatrixAdjointSchur
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # A genuine residual ordinary invariant line supplies a nontrivial original inertia element -/

namespace Dubon2026
open Matrix

variable {G K : Type*} [Group G] [Field K]

/-- An actual residual two-dimensional representation whose entire invariant submodule has rank one cannot be the trivial representation. Thus genuine residual ordinary data supplies an original element with nonidentity residual matrix. -/
theorem residualOrdinary_exists_nonidentity
    (ρ : G →* GeneralLinearGroup (Fin 2) K)
    (e : (matrixStandardRepresentation ρ).invariants ≃ₗ[K] K) :
    ∃ g, ρ g ≠ 1 := by
  classical
  by_contra h
  have htriv (g : G) : ρ g = 1 := by
    by_contra hg
    exact h ⟨g, hg⟩
  have htop : (matrixStandardRepresentation ρ).invariants = ⊤ := by
    apply top_unique
    intro v _hv g
    change (ρ g).val *ᵥ v = v
    rw [htriv g]
    exact Matrix.one_mulVec v
  have hdim : Module.finrank K (matrixStandardRepresentation ρ).invariants = 2 := by
    rw [htop]
    simp
  have hdimOne : Module.finrank K (matrixStandardRepresentation ρ).invariants = 1 := by
    simpa using e.finrank_eq
  have : (2 : ℕ) = 1 := hdim.symm.trans hdimOne
  cases this

end Dubon2026
