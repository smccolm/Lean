import Dubon2026.FiniteGeneratedAbelianRankDecomposition
import Mathlib.GroupTheory.IndexNSmul

/-! # Power-quotient size from rank and actual power torsion

This evaluates the power quotient needed for the original S-units. The
pinned free-module index theorem and finite kernel/cokernel equality remove
the need for a separate logarithmic-lattice decomposition.
-/

namespace Dubon2026
noncomputable section

/-- An actual additive equivalence identifies the multiplication-by-n kernels. -/
def nsmulKernelEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).ker ≃+
      (nsmulAddMonoidHom (α := H) n).ker where
  toFun x := ⟨e x.val, by
    change n • e x.val = 0
    rw [← map_nsmul, (show n • x.val = 0 from x.property), map_zero]⟩
  invFun x := ⟨e.symm x.val, by
    change n • e.symm x.val = 0
    rw [← map_nsmul, (show n • x.val = 0 from x.property), map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)

/-- The image of multiplication by n on a product is the product of its actual images. -/
theorem nsmul_range_prod (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ) :
    (nsmulAddMonoidHom (α := G × H) n).range =
      ((nsmulAddMonoidHom (α := G) n).range).prod
        ((nsmulAddMonoidHom (α := H) n).range) := by
  ext x
  change (∃ y : G × H, n • y = x) ↔
    (∃ y : G, n • y = x.1) ∧ ∃ y : H, n • y = x.2
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- A torsion-free factor contributes no nonzero power torsion to a product. -/
def nsmulKernelFreeProdEquiv (F T : Type*) [AddCommGroup F] [AddCommGroup T]
    [Module.IsTorsionFree ℤ F] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := F × T) n).ker ≃+
      (nsmulAddMonoidHom (α := T) n).ker where
  toFun x := ⟨x.val.2, congrArg Prod.snd x.property⟩
  invFun x := ⟨(0, x.val), Prod.ext (nsmul_zero n) x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn
      exact (nsmul_zero n).trans (congrArg Prod.fst x.property).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- For a finitely generated abelian group, the nth-power quotient has size
equal to its actual n-torsion size times n to the original integer rank. -/
theorem finiteGeneratedAbelian_nsmul_index
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ Module.finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨d, T, hT, hfin, ⟨e⟩, hd⟩ := finiteGeneratedAbelian_exists_rank_decomposition G
  letI : AddCommGroup T := hT
  letI : Finite T := hfin
  have hindex := AddSubgroup.index_map_equiv (G' := (Fin d → ℤ) × T)
    (nsmulAddMonoidHom (α := G) n).range e
  rw [AddEquiv.map_range_nsmulAddMonoidHom] at hindex
  have hk : Nat.card (nsmulAddMonoidHom (α := G) n).ker =
      Nat.card (nsmulAddMonoidHom (α := T) n).ker :=
    Nat.card_congr ((nsmulKernelEquiv e n).trans
      (nsmulKernelFreeProdEquiv (Fin d → ℤ) T n hn)).toEquiv
  rw [← hindex, nsmul_range_prod, AddSubgroup.index_prod,
    AddSubgroup.index_range_nsmul, AddSubgroup.index_range, hk, hd]
  simp

end
end Dubon2026
