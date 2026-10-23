import Dubon2026.SourceHeckeMatrixRationalSpan
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! DUB-17/18 -> rank-two original Tate Hecke realization -> descent of
two real generators to rational and padic generators of the same integral
matrix action. Adapted from the W1D determinant argument in
S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The actual original lattice
representation, real spanning and rank equality remain required inputs
until the native consumer supplies them.
-/
namespace Dubon2026.SourceHeckeMatrixDescent
noncomputable section
open Module Matrix
variable {R₀ : Type} [CommRing R₀] {n : ℕ} (Mℤ : R₀ →+* Matrix (Fin n) (Fin n) ℤ)

variable (hn : 2 * g Mℤ = n)

/-- Index the two copies of the operator basis by the ambient matrix columns. -/
def σ : Fin 2 × Fin (g Mℤ) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp [hn])

/-- Columns obtained by applying the operator basis to two candidate generators. -/
def Φ (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (cK Mℤ K ((σ Mℤ hn).symm j).2 *ᵥ v ((σ Mℤ hn).symm j).1) i

theorem Φ_col (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) (ak : Fin 2 × Fin (g Mℤ)) :
    (Φ Mℤ hn K v).col (σ Mℤ hn ak) = cK Mℤ K ak.2 *ᵥ v ak.1 := by
  funext i
  simp [Φ]

theorem Φ_map (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → ℚ) :
    (Φ Mℤ hn ℚ v).map (algebraMap ℚ K) = Φ Mℤ hn K (fun a => (algebraMap ℚ K) ∘ v a) := by
  ext i j
  simp only [Φ, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  simp only [cK, Matrix.map_map]
  congr 2

theorem span_cols_Φ_eq_top (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    Submodule.span K (Set.range (Φ Mℤ hn K w).col) = ⊤ := by
  apply top_le_iff.mp
  rw [← hw]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨t, a⟩, rfl⟩
  have hmem := MK_mem_span_cK Mℤ K t
  simp only [SetLike.mem_coe]

  refine Submodule.span_induction (p := fun x _ => x *ᵥ w a ∈ Submodule.span K (Set.range (Φ Mℤ hn K w).col))
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨σ Mℤ hn (a, k), ?_⟩
    exact Φ_col Mℤ hn K w (a, k)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ r hx

theorem isUnit_Φ (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    IsUnit (Φ Mℤ hn K w) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_cols_Φ_eq_top Mℤ hn K w hw).ge (by simp)

theorem span_cols_Φ_of_isUnit (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K)
    (hv : IsUnit (Φ Mℤ hn K v)) :
    Submodule.span K (Set.range (Φ Mℤ hn K v).col) = ⊤ := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit] at hv
  exact hv.span_eq_top_of_card_eq_finrank' (by simp)


end
end Dubon2026.SourceHeckeMatrixDescent
