import Dubon2026.SourceCurveAdeleLocalQuotient

/-! Local valuation bounds, with zero included, for the conjugate-polynomial
proof of the wild different estimate needed by DUB-17/18. The valuation
and unequal-order addition APIs are reused. This is the OrdGe fragment of
S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, adapted to actual local Places. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The local order filtration includes zero at every level. -/
def OrdGe (m : ℤ) (f : F) : Prop := f = 0 ∨ m ≤ v.ord f

theorem ordGe_zero (m : ℤ) : v.OrdGe m 0 := Or.inl rfl

theorem ordGe_iff_valuation_le (m : ℤ) (f : F) :
    v.OrdGe m f ↔ v.adicValuation f ≤ WithZero.exp (-m) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [OrdGe]
  · rw [OrdGe, or_iff_right hf, v.adicValuation_eq_exp_neg_ord hf,
      WithZero.exp_le_exp, neg_le_neg_iff]

variable {v}

theorem OrdGe.mono {m n : ℤ} {f : F} (h : v.OrdGe n f) (hmn : m ≤ n) :
    v.OrdGe m f := h.imp_right hmn.trans

theorem OrdGe.le_ord {m : ℤ} {f : F} (h : v.OrdGe m f) (hf : f ≠ 0) :
    m ≤ v.ord f := h.resolve_left hf

theorem OrdGe.add {m : ℤ} {f g : F} (hf : v.OrdGe m f) (hg : v.OrdGe m g) :
    v.OrdGe m (f + g) := by
  rw [ordGe_iff_valuation_le] at hf hg ⊢
  exact (Valuation.map_add _ _ _).trans (max_le hf hg)

theorem OrdGe.neg {m : ℤ} {f : F} (hf : v.OrdGe m f) : v.OrdGe m (-f) := by
  simpa only [ordGe_iff_valuation_le, Valuation.map_neg] using hf

theorem OrdGe.sub {m : ℤ} {f g : F} (hf : v.OrdGe m f) (hg : v.OrdGe m g) :
    v.OrdGe m (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem OrdGe.mul {m n : ℤ} {f g : F} (hf : v.OrdGe m f) (hg : v.OrdGe n g) :
    v.OrdGe (m + n) (f * g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl (zero_mul g)
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl (mul_zero f)
  exact Or.inr (by rw [v.ord_mul hf0 hg0]; exact add_le_add (hf.le_ord hf0) (hg.le_ord hg0))

theorem OrdGe.sum {ι : Type*} (s : Finset ι) {m : ℤ} {f : ι → F}
    (h : ∀ i ∈ s, v.OrdGe m (f i)) : v.OrdGe m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ordGe_zero v m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem OrdGe.mem_of_zero {f : F} (hf : v.OrdGe 0 f) : f ∈ v.toValuationSubring := by
  rcases hf with rfl | hf
  · exact zero_mem _
  · exact v.mem_of_ord_nonneg hf

theorem ord_add_eq_of_ordGe {m : ℤ} {f g : F} (hf0 : f ≠ 0)
    (hfm : v.ord f = m) (hg : v.OrdGe (m + 1) g) :
    f + g ≠ 0 ∧ v.ord (f + g) = m := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa only [add_zero] using And.intro hf0 hfm
  have hlt : v.ord f < v.ord g := by have := hg.le_ord hg0; omega
  have hne : f + g ≠ 0 := by
    intro h
    have he := eq_neg_of_add_eq_zero_left h
    have ho : v.ord (-g) = v.ord g := by simp only [ord, Valuation.map_neg]
    rw [he, ho] at hlt
    exact (lt_irrefl _ hlt)
  exact ⟨hne, (v.ord_add_eq_of_lt hf0 hg0 hlt).trans hfm⟩

end
end Dubon2026.SourceCurve.Place
