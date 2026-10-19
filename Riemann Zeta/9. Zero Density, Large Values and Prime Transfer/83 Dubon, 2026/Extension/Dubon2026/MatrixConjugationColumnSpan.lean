import Dubon2026.MatrixRepresentationSpanningDescent
import Mathlib.Data.Matrix.Basis

/-! A full column inside an invariant matrix subspace, combined with
the already proved Burnside spanning property, fills the whole matrix
space. DUB-17 uses this for conjugates of a regular element's diagonal
projector, yielding the required commuting trace test. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped BigOperators

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Left multiplication of a single matrix unit is its literal column
expansion in the original standard matrix units. -/
theorem matrix_mul_single_column_sum (X : Matrix ι ι K) (i j : ι) :
    X * Matrix.single i j 1 = ∑ k, X k i • Matrix.single k j 1 := by
  ext a b
  by_cases hb : j = b
  · subst b
    simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply]
  · simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply, hb]

/-- The full original column and conjugation invariance suffice for full
matrix span when the original representation matrices already span. -/
theorem conjugationStable_eq_top_of_column
    (ρ : G →* GeneralLinearGroup ι K) (S : Submodule K (Matrix ι ι K))
    (hS : ∀ g X, X ∈ S → (ρ g).val * X * (ρ g⁻¹).val ∈ S)
    (j : ι) (hcol : ∀ i, Matrix.single i j 1 ∈ S)
    (hspan : Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤) : S = ⊤ := by
  have hleft (X : Matrix ι ι K) (i : ι) : X * Matrix.single i j 1 ∈ S := by
    rw [matrix_mul_single_column_sum]
    exact S.sum_mem (fun k _ => S.smul_mem _ (hcol k))
  have hright (i : ι) (g : G) : Matrix.single i j 1 * (ρ g).val ∈ S := by
    have h := hS g⁻¹ _ (hleft (ρ g).val i)
    simpa only [inv_inv, map_inv, ← mul_assoc, Units.inv_mul, one_mul] using h
  have hmul (i : ι) (Y : Matrix ι ι K) : Matrix.single i j 1 * Y ∈ S := by
    have hY : Y ∈ Submodule.span K (Set.range (fun g => (ρ g).val)) := by rw [hspan]; trivial
    induction hY using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hright i g
    | zero => simpa only [mul_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [mul_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [Matrix.mul_smul] using S.smul_mem a hx
  apply top_unique
  intro X _
  rw [Matrix.matrix_eq_sum_single X]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro k _
  have h := hmul i (Matrix.single j k (X i k))
  simpa only [Matrix.single_mul_single_same, one_mul] using h

end
end Dubon2026
