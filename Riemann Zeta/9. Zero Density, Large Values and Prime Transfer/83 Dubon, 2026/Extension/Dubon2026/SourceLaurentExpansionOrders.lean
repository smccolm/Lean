import Dubon2026.SourceOriginalSlotEmbedding

/-! DUB-17/18 -> numerical modular genus -> cusp widths. The literal
substitution multiplies Laurent order by the level; a unit twist preserves
it. Applied to the actual conjugate j series, these give its pole order.
The substitution argument follows the selected order_qExpand proof in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native coefficient/order APIs
replace the deprecated coefficient-nonzero helper.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K]

theorem laurent_order_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries K) :
    (qExpand K N f).order = (N : ℤ) * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have hc : (qExpand K N f).coeff ((N : ℤ) * f.order) ≠ 0 := by
    rw [qExpand_coeff_mul]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand K N f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  by_cases hdvd : (N : ℤ) ∣ (qExpand K N f).order
  · obtain ⟨m, hm⟩ := hdvd
    rw [hm, qExpand_coeff_mul] at hk
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmlt : m < f.order := by
      rw [hm] at hlt
      exact lt_of_mul_lt_mul_left hlt hNpos.le
    exact hk (HahnSeries.coeff_eq_zero_of_lt_order hmlt)
  · exact hk (qExpand_coeff_of_not_dvd N f hdvd)

theorem laurent_order_qTwist (u : Kˣ) (f : LaurentSeries K) (hf : f ≠ 0) :
    (qTwist u f).order = f.order := by
  have hc : (qTwist u f).coeff f.order ≠ 0 := by
    rw [qTwist_coeff]
    exact mul_ne_zero (Units.ne_zero _) (HahnSeries.coeff_order_eq_zero.not.mpr hf)
  have hne : qTwist u f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  apply hk
  rw [qTwist_coeff, HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]

theorem laurent_order_TS (N : ℕ) [NeZero N] (u : Kˣ) :
    (TS K N u).order = -(N : ℤ) := by
  rw [TS, laurent_order_qExpand, laurent_order_qTwist u _ (jqModC_ne_zero K),
    order_jqModC, mul_neg_one]

end
end Dubon2026.SourceFunctionField
