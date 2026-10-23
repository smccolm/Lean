import Dubon2026.SourceHeckeMatrixRationalGenerators
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
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
variable {n : ℕ}

/-- Flatten a square matrix into its function of pairs of indices. -/
def flat (K : Type) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flat_injective (K : Type) [CommRing K] : Function.Injective (flat (n := n) K) := by
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem ker_flat (K : Type) [CommRing K] : LinearMap.ker (flat (n := n) K) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (flat_injective K)

/-- Extend rational matrix coefficients to real coefficients. -/
def castMat : Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
  ((Algebra.ofId ℚ ℝ).mapMatrix).toLinearMap

@[scoped simp] theorem castMat_apply (A : Matrix (Fin n) (Fin n) ℚ) :
    castMat A = A.map (algebraMap ℚ ℝ) := rfl

theorem linearIndependent_real_of_rat {ι : Type*} (v : ι → Matrix (Fin n) (Fin n) ℚ)
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℝ (fun i => (v i).map (algebraMap ℚ ℝ)) := by

  have h1 : LinearIndependent ℚ (fun i => flat ℚ (v i)) := hv.map' (flat ℚ) (ker_flat ℚ)
  have h2 : LinearIndependent ℝ (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mpr h1
  have h3 : (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) = fun i => flat ℝ ((v i).map (algebraMap ℚ ℝ)) := by
    funext i; funext ij; rfl
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat ℝ) h2

theorem finrank_real_span_eq {ι : Type*} (f : ι → Matrix (Fin n) (Fin n) ℚ) :
    finrank ℝ (Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ))) =
      finrank ℚ (Submodule.span ℚ (Set.range f)) := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range f)
  have hfin : s.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  haveI : Fintype s := hfin.fintype

  have hq : finrank ℚ (Submodule.span ℚ (Set.range f)) = Fintype.card s := by
    rw [← hspan, ← finrank_span_eq_card (b := ((↑) : s → Matrix (Fin n) (Fin n) ℚ)) hli]
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have hli' : LinearIndependent ℝ (fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ)) :=
    linearIndependent_real_of_rat _ hli
  have hspan' : Submodule.span ℝ (Set.range fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))
      = Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ)) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hs hx
      exact ⟨i, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : f i ∈ Submodule.span ℚ s := by rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

      have : castMat (f i) ∈ (Submodule.span ℚ s).map castMat := Submodule.mem_map_of_mem hi
      rw [Submodule.map_span] at this
      have hle : Submodule.span ℚ (castMat '' s) ≤
          (Submodule.span ℝ (Set.range fun i : s =>
            ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))).restrictScalars ℚ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact hle this
  rw [← hspan', finrank_span_eq_card hli', hq]


end
end Dubon2026.SourceHeckeMatrixDescent
