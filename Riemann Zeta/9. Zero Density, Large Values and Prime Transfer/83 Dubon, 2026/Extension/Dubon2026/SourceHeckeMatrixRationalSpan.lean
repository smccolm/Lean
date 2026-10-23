import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Basis.VectorSpace

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

/-- The same integral matrices with coefficients in the target ring. -/
def MK (K : Type) [CommRing K] : R₀ →+* Matrix (Fin n) (Fin n) K :=
  ((Int.castRingHom K).mapMatrix).comp Mℤ

theorem MK_apply (K : Type) [CommRing K] (t : R₀) : MK Mℤ K t = (Mℤ t).map (Int.cast : ℤ → K) := rfl

theorem MK_map (K : Type) [Field K] [CharZero K] (t : R₀) :
    (MK Mℤ ℚ t).map (algebraMap ℚ K) = MK Mℤ K t := by
  rw [MK_apply, MK_apply, Matrix.map_map]
  congr 1
  funext z
  simp

/-- Rational span of the given integral matrix action. -/
def Tℚ : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ) := Submodule.span ℚ (Set.range (MK Mℤ ℚ))

/-- Dimension of the rational operator span. -/
def g : ℕ := finrank ℚ (Tℚ Mℤ)

/-- A finite rational basis of the actual operator span. -/
def c : Basis (Fin (g Mℤ)) ℚ (Tℚ Mℤ) := Module.finBasis ℚ (Tℚ Mℤ)

/-- The rational operator basis with coefficients in the target field. -/
def cK (K : Type) [Field K] [CharZero K] (k : Fin (g Mℤ)) : Matrix (Fin n) (Fin n) K :=
  ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K)

theorem smul_map_algebraMap (K : Type) [Field K] [CharZero K] (q : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (q • A).map (algebraMap ℚ K) = (q : K) • A.map (algebraMap ℚ K) := by
  ext i j; simp

theorem eq_sum_of_mem_Tℚ (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ) = ∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ) := by
  have h := congrArg (Submodule.subtype (Tℚ Mℤ)) ((c Mℤ).sum_repr x).symm
  rw [map_sum] at h
  simpa using h

theorem map_mem_span_cK (K : Type) [Field K] [CharZero K] (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K) ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  rw [eq_sum_of_mem_Tℚ Mℤ x]
  rw [show (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ K)
      = (algebraMap ℚ K).mapMatrix (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ))
      from rfl, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [RingHom.mapMatrix_apply, smul_map_algebraMap]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem MK_mem_span_cK (K : Type) [Field K] [CharZero K] (t : R₀) :
    MK Mℤ K t ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  have hmem : MK Mℤ ℚ t ∈ Tℚ Mℤ := Submodule.subset_span (Set.mem_range_self t)
  rw [← MK_map Mℤ K t]
  exact map_mem_span_cK Mℤ K ⟨MK Mℤ ℚ t, hmem⟩

theorem map_mem_of_mem_Tℚ (K : Type) [Field K] [CharZero K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ t, MK Mℤ K t ∈ S) {x : Matrix (Fin n) (Fin n) ℚ} (hx : x ∈ Tℚ Mℤ) :
    x.map (algebraMap ℚ K) ∈ S := by
  refine Submodule.span_induction (p := fun x _ => x.map (algebraMap ℚ K) ∈ S) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨t, rfl⟩
    rw [MK_map]; exact hS t
  · simp only [Matrix.map_zero, map_zero]; exact S.zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.map_add _ (map_add (algebraMap ℚ K))]; exact S.add_mem hx hy
  · intro r x _ hx
    rw [smul_map_algebraMap]; exact S.smul_mem _ hx


end
end Dubon2026.SourceHeckeMatrixDescent
