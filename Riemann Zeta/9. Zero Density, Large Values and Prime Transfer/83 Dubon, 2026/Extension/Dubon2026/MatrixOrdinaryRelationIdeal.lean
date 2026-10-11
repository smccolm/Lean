import Dubon2026.MatrixOrdinaryRelationCriterion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The literal coefficient ideal of the original ordinary matrix relations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R A : Type*} [Group G] [CommRing R] [CommRing A]

/-- The original ordinary relation operator, using the determinant of the same original matrix. -/
def matrixOrdinaryRelation (ρ : G →* GeneralLinearGroup (Fin 2) R) (g₀ g : G) :
    Matrix (Fin 2) (Fin 2) R :=
  ((ρ g).val - 1) * ((ρ g₀).val - (GeneralLinearGroup.det (ρ g₀) : R) • 1)

/-- The actual original relation operator commutes with every coefficient ring homomorphism. -/
theorem matrixOrdinaryRelation_map (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (g₀ g : G) (f : R →+* A) :
    (matrixOrdinaryRelation ρ g₀ g).map f =
      matrixOrdinaryRelation ((GeneralLinearGroup.map f).comp ρ) g₀ g := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOrdinaryRelation, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.map_det, Matrix.one_apply]

/-- All entries of all actual original ordinary operators generate this coefficient ideal. -/
def matrixOrdinaryRelationIdeal (ρ : G →* GeneralLinearGroup (Fin 2) R) (g₀ : G) :
    Ideal R :=
  Ideal.span (Set.range fun t : G × Fin 2 × Fin 2 =>
    matrixOrdinaryRelation ρ g₀ t.1 t.2.1 t.2.2)

/-- A coefficient map annihilates the literal ordinary ideal exactly when every original ordinary relation vanishes after that coefficient change. -/
theorem matrixOrdinaryRelationIdeal_le_kernel_iff
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (g₀ : G) (f : R →+* A) :
    matrixOrdinaryRelationIdeal ρ g₀ ≤ RingHom.ker f ↔
      ∀ g, matrixOrdinaryRelation ((GeneralLinearGroup.map f).comp ρ) g₀ g = 0 := by
  constructor
  · intro h g
    rw [← matrixOrdinaryRelation_map]
    ext i j
    exact h (Ideal.subset_span (Set.mem_range_self (g, i, j)))
  · intro h
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨g, i, j⟩, rfl⟩
    have hg := congrArg (fun B : Matrix (Fin 2) (Fin 2) A => B i j) (h g)
    rw [← matrixOrdinaryRelation_map] at hg
    exact hg

end
end Dubon2026
