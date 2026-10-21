import Dubon2026.SourceCurvePlaces
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Algebraic.Basic

/-! DUB-17/18 -> regular differential realization -> local derivative orders
-> finite extension over an actual uniformizer. A nonzero place order forces
transcendence. Pinned integral closedness of valuation rings replaces the
external monic-polynomial membership development.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_isAlgebraic {x : F} (hx : IsAlgebraic K x) :
    x ∈ v.toValuationSubring := by
  have hint : IsIntegral v.toValuationSubring x := hx.isIntegral.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

theorem ord_eq_zero_of_isAlgebraic {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact v.ord_zero
  · let u : v.toValuationSubringˣ :=
      { val := ⟨x, v.mem_of_isAlgebraic hx⟩
        inv := ⟨x⁻¹, v.mem_of_isAlgebraic hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u

theorem transcendental_of_ord_ne_zero {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t :=
  fun h => ht (v.ord_eq_zero_of_isAlgebraic h)

end
end Dubon2026.SourceCurve.Place
