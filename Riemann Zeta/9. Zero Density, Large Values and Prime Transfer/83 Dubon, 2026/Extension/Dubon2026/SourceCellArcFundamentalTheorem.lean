import Dubon2026.SourceCellRadialRegion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> centered cell residue contour.
Apply the native fundamental theorem on the exact finite source arcs, then
telescope. Continuous extensions of the arc derivatives supply integrability;
the finitely many nonsmooth endpoints do not change the actual integral.
This single consumer serves both primitive boundary integrals and log-radius
integration in the centered winding calculation.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Set Filter MeasureTheory intervalIntegral
open scoped Real Topology Interval

theorem integral_eq_sub_of_arc_derivatives (R : RadialRegion) (f F : ℝ → ℂ)
    (hF : Continuous F)
    (hd : ∀ k : Fin R.N, ∀ φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ),
      HasDerivAt F (f φ) φ)
    (hext : ∀ k : Fin R.N, ∃ g : ℝ → ℂ, Continuous g ∧
      EqOn f g (Ioo (R.φs k.castSucc) (R.φs k.succ))) :
    IntervalIntegrable f volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), f φ) = F (2 * π) - F 0 := by
  let a : ℕ → ℝ := fun k => if hk : k < R.N + 1 then R.φs ⟨k, hk⟩ else 2 * π
  have ha0 : a 0 = 0 := by simpa only [a, dif_pos (Nat.succ_pos R.N)] using R.hφ0
  have haN : a R.N = 2 * π := by simpa only [a, dif_pos (Nat.lt_succ_self R.N)] using R.hφN
  have hk1 : ∀ k (hk : k < R.N), a k = R.φs (⟨k, hk⟩ : Fin R.N).castSucc := by
    intro k hk
    simp only [a, dif_pos (show k < R.N + 1 by omega)]
    rfl
  have hk2 : ∀ k (hk : k < R.N), a (k + 1) = R.φs (⟨k, hk⟩ : Fin R.N).succ := by
    intro k hk
    simp only [a, dif_pos (show k + 1 < R.N + 1 by omega)]
    rfl
  have harc : ∀ k, k < R.N → IntervalIntegrable f volume (a k) (a (k + 1)) ∧
      (∫ φ in a k..a (k + 1), f φ) = F (a (k + 1)) - F (a k) := by
    intro k hk
    rw [hk1 k hk, hk2 k hk]
    let i : Fin R.N := ⟨k, hk⟩
    have hlt : R.φs i.castSucc < R.φs i.succ := R.hmono Fin.castSucc_lt_succ
    obtain ⟨g, hg, he⟩ := hext i
    have hae : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Ι (R.φs i.castSucc) (R.φs i.succ) → g φ = f φ := by
      have hb : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∉ ({R.φs i.succ} : Set ℝ) :=
        compl_mem_ae_iff.mpr (measure_singleton _)
      filter_upwards [hb] with φ hφ hI
      rw [uIoc_of_le hlt.le] at hI
      exact (he ⟨hI.1, lt_of_le_of_ne hI.2 hφ⟩).symm
    have hint : IntervalIntegrable f volume (R.φs i.castSucc) (R.φs i.succ) := by
      rw [intervalIntegrable_iff]
      exact (intervalIntegrable_iff.mp (hg.intervalIntegrable _ _)).congr
        ((ae_restrict_iff' measurableSet_uIoc).mpr hae)
    exact ⟨hint, integral_eq_sub_of_hasDerivAt_of_le hlt.le hF.continuousOn (hd i) hint⟩
  have hint := IntervalIntegrable.trans_iterate fun k hk => (harc k hk).1
  have heq : (∫ φ in a 0..a R.N, f φ) = F (a R.N) - F (a 0) := by
    rw [← sum_integral_adjacent_intervals (a := a) (n := R.N) fun k hk => (harc k hk).1]
    simp_rw [Finset.sum_congr rfl fun k hk => (harc k (Finset.mem_range.mp hk)).2]
    exact Finset.sum_range_sub (fun k => F (a k)) R.N
  rw [ha0, haN] at hint heq
  exact ⟨hint, heq⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
