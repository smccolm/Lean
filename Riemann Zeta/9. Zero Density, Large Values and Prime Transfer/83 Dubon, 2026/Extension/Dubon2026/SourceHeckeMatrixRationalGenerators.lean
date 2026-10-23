import Dubon2026.SourceHeckeMatrixRankTwoDeterminant
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.FunProp

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

theorem continuous_det_Φ : Continuous fun v : Fin 2 → Fin n → ℝ => (Φ Mℤ hn ℝ v).det := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Φ, Matrix.of_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem exists_rat_isUnit_Φ
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : R₀ × Fin 2 => MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ v : Fin 2 → Fin n → ℚ, IsUnit (Φ Mℤ hn ℚ v) := by
  obtain ⟨w, hw⟩ := hw
  have hU : IsOpen {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0} :=
    isOpen_ne_fun (continuous_det_Φ Mℤ hn) continuous_const
  have hne : {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0}.Nonempty :=
    ⟨w, by
      have := isUnit_Φ Mℤ hn ℝ w hw
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
      exact this⟩
  have hdense : DenseRange (fun v : Fin 2 → Fin n → ℚ => fun a => fun j => ((v a j : ℚ) : ℝ)) := by
    have h1 : DenseRange (fun x : Fin n → ℚ => fun j => ((x j : ℚ) : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact DenseRange.piMap fun _ => h1
  obtain ⟨v, hv⟩ := hdense.exists_mem_open hU hne
  refine ⟨v, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply hv
  have hmap := RingHom.map_det (algebraMap ℚ ℝ) (Φ Mℤ hn ℚ v)
  rw [h0, map_zero, RingHom.mapMatrix_apply, Φ_map] at hmap
  exact hmap.symm


end
end Dubon2026.SourceHeckeMatrixDescent
