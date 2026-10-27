import Dubon2026.SourceGammaOneCuspCosetBound
import Dubon2026.SourceGammaOneCuspPoleDegree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! DUB-17/18 -> actual Gamma1 cusp bijection -> real period dimension
comparison. Positive pole weights, a surjective cusp map, and the proved
upper orbit-size bound turn equality of total degree into injectivity
and termwise equality. The argument reuses the existing finite-fiber
positive-weight proof and retains the new upper-bound input explicitly. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CuspCounting
noncomputable section

theorem bijective_and_eq_of_positive_weight_bound
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (w : B → ℤ) (hw : ∀ b, 0 < w b)
    (v : A → ℤ) (hv : ∀ a, w (f a) ≤ v a)
    (hsum : ∑ a, v a = ∑ b, w b) :
    Function.Bijective f ∧ ∀ a, w (f a) = v a := by
  classical
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hi : Function.Injective g := hg.injective
  have himage : ∑ a ∈ Finset.univ.image g, w (f a) = ∑ b, w b := by
    rw [Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_congr rfl (fun b _ => congrArg w (hg b))
  have hlo : (∑ b, w b) ≤ ∑ a, w (f a) := by
    rw [← himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => (hw (f a)).le)
  have hhi : (∑ a, w (f a)) ≤ ∑ a, v a := Finset.sum_le_sum (fun a _ => hv a)
  have he : (∑ a, w (f a)) = ∑ b, w b := le_antisymm (hhi.trans_eq hsum) hlo
  have hgs : Function.Surjective g := by
    intro a
    by_contra ha
    have hnot : a ∉ Finset.univ.image g := by simpa using ha
    have hlt := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.image g))
      (Finset.mem_univ a) hnot (hw (f a)) (fun b _ _ => (hw (f b)).le)
    rw [himage, he] at hlt
    exact lt_irrefl _ hlt
  refine ⟨⟨?_, hf⟩, ?_⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := hgs a
    obtain ⟨b', rfl⟩ := hgs b
    apply congrArg g
    simpa only [hg a', hg b'] using hab
  · intro a
    exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hv b)).mp
      (he.trans hsum.symm) a (Finset.mem_univ _)

end
end Dubon2026.SourceFunctionField.GammaOne.CuspCounting
