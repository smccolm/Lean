import Dubon2026.DirichletDivisor

/-! # The existing rectangle argument principle for the literal open-rectangle zero count -/

namespace Dubon2026

open Set Complex

theorem rectangle_interior_coordinates {z w s : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hs : s ∈ Rectangle z w) (hb : s ∉ RectangleBorder z w) :
    z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im := by
  rw [mem_Rect hre him] at hs
  refine ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2.1 ?_,
    lt_of_le_of_ne hs.2.2.1 ?_, lt_of_le_of_ne hs.2.2.2 ?_⟩
  · intro he
    exact hb (by simp [RectangleBorder, he, hs.2.2.1, hs.2.2.2, him, mem_reProdIm])
  · intro he
    exact hb (by simp [RectangleBorder, he, hs.2.2.1, hs.2.2.2, him, mem_reProdIm])
  · intro he
    exact hb (by simp [RectangleBorder, he, hs.1, hs.2.1, hre, mem_reProdIm])
  · intro he
    exact hb (by simp [RectangleBorder, he, hs.1, hs.2.1, hre, mem_reProdIm])

theorem dirichlet_divisor_support_eq_open_zeros {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0) :
    (MeromorphicOn.divisor (dirichletSum a N)
      (Rectangle (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ))).support =
        zerosInOpenRectangle a N l u T := by
  ext s
  rw [mem_dirichlet_divisor_support hN ha]
  constructor
  · rintro ⟨hs, hz⟩
    have hc := rectangle_interior_coordinates hlu (neg_le_self hT) hs (fun h => hb s h hz)
    exact ⟨hc.1, hc.2.1, abs_lt.mpr hc.2.2, hz⟩
  · rintro ⟨hl, hu, ht, hz⟩
    refine ⟨?_, hz⟩
    rw [mem_Rect hlu (neg_le_self hT)]
    exact ⟨hl.le, hu.le, (abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩

theorem rectangleIntegral_logDeriv_eq_verticalZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0) :
    RectangleIntegral' (logDeriv (dirichletSum a N)) (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
      (verticalZeroCount a N hN ha l u T : ℂ) := by
  have hsets : (divisor_support_rectangle_finite (dirichletSum a N)
      (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ)).toFinset =
        zerosInOpenRectangleFinset a N hN ha l u T := by
    ext s
    simp only [Set.Finite.mem_toFinset, zerosInOpenRectangleFinset,
      dirichlet_divisor_support_eq_open_zeros hN ha hlu hT hb]
  rw [dirichlet_rectangle_argument_principle hN ha hlu (neg_le_self hT) hb, hsets]
  simp only [verticalZeroCount, Nat.cast_sum]

end Dubon2026
