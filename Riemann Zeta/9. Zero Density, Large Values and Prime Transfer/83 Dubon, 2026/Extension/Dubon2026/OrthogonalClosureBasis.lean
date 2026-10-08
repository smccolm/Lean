import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # An actual Hilbert basis for the closed span of an original orthogonal family -/

namespace Dubon2026

noncomputable section

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Normalizing an actual nonzero orthogonal family yields an orthonormal family in the same original inner product. -/
theorem normalizedOrthogonal_orthonormal (v : ι → V) (hn : ∀ i, v i ≠ 0)
    (ho : Pairwise (fun i j => inner ℂ (v i) (v j) = 0)) :
    Orthonormal ℂ (fun i => ((‖v i‖⁻¹ : ℝ) : ℂ) • v i) := by
  constructor
  · intro i
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i))
  · intro i j hij
    simp only [inner_smul_left, inner_smul_right, ho hij, mul_zero]

/-- Pointwise normalization leaves the literal original algebraic span unchanged. -/
theorem normalizedOrthogonal_span (v : ι → V) (hn : ∀ i, v i ≠ 0) :
    Submodule.span ℂ (Set.range (fun i => ((‖v i‖⁻¹ : ℝ) : ℂ) • v i)) =
      Submodule.span ℂ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hmem := Submodule.smul_mem
      (Submodule.span ℂ (Set.range (fun i => ((‖v i‖⁻¹ : ℝ) : ℂ) • v i)))
      ((‖v i‖ : ℝ) : ℂ) (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn i))), one_smul] using hmem

/-- A vector in the original closed span orthogonal to every original vector must vanish. -/
theorem closureSpan_eq_zero_of_inner (v : ι → V) (w : V)
    (hw : w ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure)
    (hi : ∀ i, inner ℂ (v i) w = 0) : w = 0 := by
  have hs : ∀ u ∈ Submodule.span ℂ (Set.range v), inner ℂ u w = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hi i
    | zero => exact inner_zero_left w
    | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
    | smul a x hx ih => simp only [inner_smul_left, ih, mul_zero]
  exact inner_self_eq_zero.mp
    ((Submodule.orthogonal_closure' (Submodule.span ℂ (Set.range v)) w).mp hs w hw)

/-- A vector of the original closed span orthogonal to all but one original orthogonal line lies on that exact original line. -/
theorem closureSpan_eq_smul_of_inner (v : ι → V)
    (ho : Pairwise (fun i j => inner ℂ (v i) (v j) = 0))
    (i : ι) (hn : v i ≠ 0) (w : V)
    (hw : w ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure)
    (hi : ∀ j, j ≠ i → inner ℂ (v j) w = 0) : ∃ a : ℂ, w = a • v i := by
  classical
  let a : ℂ := inner ℂ (v i) w / inner ℂ (v i) (v i)
  refine ⟨a, sub_eq_zero.mp ?_⟩
  apply closureSpan_eq_zero_of_inner v (w - a • v i)
  · exact Submodule.sub_mem _ hw (Submodule.smul_mem _ a
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)))
  · intro j
    rw [inner_sub_right, inner_smul_right]
    by_cases hj : j = i
    · subst j
      have hne : inner ℂ (v i) (v i) ≠ 0 := inner_self_ne_zero.mpr hn
      dsimp only [a]
      rw [div_mul_cancel₀ _ hne, sub_self]
    · rw [hi j hj, ho hj, mul_zero, sub_zero]

/-- An orthonormal original family gives a genuine Hilbert basis of precisely its original closed span. -/
def orthonormalClosureBasis (v : ι → V) (hv : Orthonormal ℂ v)
    (p : Submodule ℂ V) [CompleteSpace p]
    (hp : p = (Submodule.span ℂ (Set.range v)).topologicalClosure) : HilbertBasis ι ℂ p := by
  have hm (i : ι) : v i ∈ p := by
    rw [hp]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : ι → p := fun i => ⟨v i, hm i⟩
  have hb : Orthonormal ℂ b := hv.codRestrict p hm
  apply HilbertBasis.mkOfOrthogonalEqBot hb
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  apply Subtype.ext
  apply closureSpan_eq_zero_of_inner v w.val (hp ▸ w.property)
  intro i
  exact hw (b i) (Submodule.subset_span ⟨i, rfl⟩)

/-- The constructed Hilbert basis retains the original vectors exactly, through the actual closed-subspace inclusion. -/
theorem orthonormalClosureBasis_apply (v : ι → V) (hv : Orthonormal ℂ v)
    (p : Submodule ℂ V) [CompleteSpace p]
    (hp : p = (Submodule.span ℂ (Set.range v)).topologicalClosure) (i : ι) :
    (orthonormalClosureBasis v hv p hp i).val = v i := by
  simp only [orthonormalClosureBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end
end Dubon2026
