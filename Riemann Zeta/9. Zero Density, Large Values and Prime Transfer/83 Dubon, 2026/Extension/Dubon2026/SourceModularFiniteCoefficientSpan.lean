import Dubon2026.SourceModularPrimitiveScaling

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
actual coefficient valuation on the modular function field. An integral Laurent
fraction has a denominator with nonzero literal coefficient reduction. Primitive
normalization of finite integer coefficient spans puts every actual modular
function or its inverse in this ring. This constructs the valuation ring; its
residue map and good-reduction properties still require their own consumers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, constant-reduction construction.
Native finite-span selection replaces the external finite-subset argument. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IntermediateField
open scoped Classical

variable (L : Type*) [Field L] (N : ℕ)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (divisorExpansionsCoeff N L)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨d, hd, _, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      have hm : (qExpand L d (jqModC L)).coeff n =
          ((qExpand ℤ d (jqModC ℤ)).coeff n : L) := by
        have h := congrArg (fun z : LaurentSeries L => z.coeff n)
          (coefficientMap_j_expansion (Int.castRingHom L) d)
        exact h.symm
      rw [hm, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

end
end Dubon2026.SourceFunctionField.GaussReduction
