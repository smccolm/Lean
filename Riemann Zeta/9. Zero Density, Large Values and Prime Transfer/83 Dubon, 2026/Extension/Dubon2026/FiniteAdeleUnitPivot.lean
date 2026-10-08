import Dubon2026.RationalFiniteAdeleDensity
import Dubon2026.RingSL2Elementary

/-! # An actual unit pivot in the canonical finite adele ring -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- A coordinatewise zero-or-one elementary row operation on two genuine finite adeles. -/
def finiteAdelePivotParameter (a c : FiniteAdeleRing ℤ ℚ) : FiniteAdeleRing ℤ ℚ :=
  ⟨fun v => if Valued.v (c v) ≤ Valued.v (a v) then 0 else 1,
    Filter.Eventually.of_forall (fun v => by dsimp only; split_ifs <;> simp)⟩

/-- The selected elementary pivot has the larger local valuation of the original entries. -/
theorem finiteAdelePivotParameter_valuation (a c : FiniteAdeleRing ℤ ℚ)
    (v : HeightOneSpectrum ℤ) :
    Valued.v (a v + finiteAdelePivotParameter a c v * c v) =
      max (Valued.v (a v)) (Valued.v (c v)) := by
  change Valued.v (a v + (if Valued.v (c v) ≤ Valued.v (a v) then 0 else 1) * c v) = _
  split_ifs with h
  · simp [max_eq_left h]
  · simp only [one_mul]
    exact Valued.v.map_add_of_distinct_val (lt_of_not_ge h).ne

/-- For an actual determinant-one adelic matrix the selected pivot is a unit of the adele ring. -/
theorem finiteAdeleSL2_pivot_isUnit (g : SL(2, FiniteAdeleRing ℤ ℚ)) :
    IsUnit (g 0 0 + finiteAdelePivotParameter (g 0 0) (g 1 0) * g 1 0) := by
  have hd (v : HeightOneSpectrum ℤ) :
      g 0 0 v * g 1 1 v - g 0 1 v * g 1 0 v = 1 := by
    have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    exact congrArg (fun a : FiniteAdeleRing ℤ ℚ => a v) h
  apply FiniteAdeleRing.isUnit_iff.mpr
  constructor
  · intro v hz
    have hv := finiteAdelePivotParameter_valuation (g 0 0) (g 1 0) v
    change g 0 0 v + finiteAdelePivotParameter (g 0 0) (g 1 0) v * g 1 0 v = 0 at hz
    rw [hz, map_zero] at hv
    have ha : Valued.v (g 0 0 v) = 0 := le_antisymm
      ((le_max_left _ _).trans_eq hv.symm) zero_le
    have hc : Valued.v (g 1 0 v) = 0 := le_antisymm
      ((le_max_right _ _).trans_eq hv.symm) zero_le
    have haz : g 0 0 v = 0 := (Valuation.zero_iff _).mp ha
    have hcz : g 1 0 v = 0 := (Valuation.zero_iff _).mp hc
    simpa [haz, hcz] using hd v
  · filter_upwards [(g 0 0).property, (g 0 1).property,
      (g 1 0).property, (g 1 1).property] with v ha hb hc he
    change Valued.v (g 0 0 v + finiteAdelePivotParameter (g 0 0) (g 1 0) v * g 1 0 v) = 1
    rw [finiteAdelePivotParameter_valuation]
    change Valued.v (g 0 0 v) ≤ 1 at ha
    change Valued.v (g 0 1 v) ≤ 1 at hb
    change Valued.v (g 1 0 v) ≤ 1 at hc
    change Valued.v (g 1 1 v) ≤ 1 at he
    apply le_antisymm (max_le ha hc)
    have hsub := Valued.v.map_sub (g 0 0 v * g 1 1 v) (g 0 1 v * g 1 0 v)
    rw [hd, map_one, map_mul, map_mul] at hsub
    apply hsub.trans
    apply max_le
    · have hmul : Valued.v (g 0 0 v) * Valued.v (g 1 1 v) ≤ Valued.v (g 0 0 v) := by
        simpa only [mul_one] using mul_le_mul_right he (Valued.v (g 0 0 v))
      exact hmul.trans (le_max_left _ _)
    · have hmul : Valued.v (g 0 1 v) * Valued.v (g 1 0 v) ≤ Valued.v (g 1 0 v) := by
        simpa only [one_mul] using mul_le_mul_left hb (Valued.v (g 1 0 v))
      exact hmul.trans (le_max_right _ _)

/-- Every subgroup containing all actual adelic elementary matrices is the whole determinant-one group. -/
theorem finiteAdeleSL2_mem_of_unipotents
    (H : Subgroup SL(2, FiniteAdeleRing ℤ ℚ))
    (hU : ∀ t : FiniteAdeleRing ℤ ℚ, ringUpperUnipotent t ∈ H)
    (hL : ∀ t : FiniteAdeleRing ℤ ℚ, ringLowerUnipotent t ∈ H)
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) : g ∈ H := by
  apply ringSL2_mem_of_elementary_unit_pivot H hU hL g
    (finiteAdelePivotParameter (g 0 0) (g 1 0))
  simpa [ringUpperUnipotent, coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using
    finiteAdeleSL2_pivot_isUnit g

end
end Dubon2026
