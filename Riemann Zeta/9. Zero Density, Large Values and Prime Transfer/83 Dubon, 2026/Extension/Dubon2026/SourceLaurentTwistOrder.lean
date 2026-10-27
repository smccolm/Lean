import Dubon2026.SourceFrickeSpanLaurentRealization

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> cusp stability under coefficient twists. An injective coefficient map
preserves literal Laurent order, including the zero series. The existing
analytic germ/order theorem then identifies the cusp order without assuming
continuity of the complex automorphism. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Filter
open scoped Topology

theorem coeffMap_order {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (A : LaurentSeries K) : (coeffMap σ A).order = A.order := by
  by_cases hA : A = 0
  · simp [hA]
  have hB : coeffMap σ A ≠ 0 := fun he => hA ((coeffMap σ).injective (by simpa using he))
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [coeffMap_coeff]
    exact fun he => hA (HahnSeries.coeff_order_eq_zero.mp (σ.injective (by simpa using he)))
  · apply HahnSeries.order_le_of_coeff_ne_zero
    intro he
    apply hB
    apply HahnSeries.coeff_order_eq_zero.mp
    rw [coeffMap_coeff, he, map_zero]

theorem coeffMap_orderTop {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (A : LaurentSeries K) : (coeffMap σ A).orderTop = A.orderTop := by
  by_cases hA : A = 0
  · simp [hA]
  have hB : coeffMap σ A ≠ 0 := fun he => hA ((coeffMap σ).injective (by simpa using he))
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hB,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hA, coeffMap_order]

theorem CuspTaylor.Represents.orderTop {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : CuspTaylor.Represents A F) : meromorphicOrderAt F 0 = A.orderTop := by
  by_cases hA : A = 0
  · subst A
    rw [HahnSeries.orderTop_zero, meromorphicOrderAt_eq_top_iff]
    exact hF.unique (by simpa only [map_zero] using CuspTaylor.represents_const 0)
  · exact (hF.order hA).trans (HahnSeries.order_eq_orderTop_of_ne_zero hA)

end
end Dubon2026.SourceFunctionField
