import Dubon2026.SourceRadialDissectionArcPaths
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse ->
weighted residue reciprocity. Adapt only the radial-cell consumers of the
existing boundary and interval-sum proofs. The constructed cover dissection
supplies the pole centers and carrier separation; no contour identity is assumed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped Real
variable {X : Type*} [TopologicalSpace X]

/-- Integral of a cell-indexed function along one oriented source arc. -/
def RadialCellDissection.arcInt (𝒟 : RadialCellDissection X) (H : 𝒟.ιC → ℝ → ℂ)
    (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : ℂ :=
  ∫ s in ((𝒟.cell p.1).R.φs p.2.castSucc)..((𝒟.cell p.1).R.φs p.2.succ), H p.1 s

theorem RadialCellDissection.integral_eq_sum_arcInt (𝒟 : RadialCellDissection X) (H : (C : 𝒟.ιC) → ℝ → ℂ)
    (C : 𝒟.ιC)
    (hint : ∀ k : Fin (𝒟.cell C).R.N, IntervalIntegrable (H C) volume
      ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :
    (∫ s in (0 : ℝ)..(2 * π), H C s) = ∑ k : Fin (𝒟.cell C).R.N, 𝒟.arcInt H ⟨C, k⟩ := by
  set R := (𝒟.cell C).R with hR
  set N := R.N with hN
  set aN : ℕ → ℝ := fun k => if hk : k < N + 1 then R.φs ⟨k, hk⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = R.φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, R.hφ0]
  have haNN : aN N = 2 * π := by
    have hN' : N < N + 1 := Nat.lt_succ_self N
    have : aN N = R.φs ⟨N, hN'⟩ := by simp only [haN, dif_pos hN']
    rw [this, show (⟨N, hN'⟩ : Fin (N + 1)) = Fin.last N from rfl, R.hφN]
  have hk1 : ∀ k (hk : k < N), aN k = R.φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = R.φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  rw [← haN0, ← haNN, ← sum_integral_adjacent_intervals]
  · rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ x in aN k..aN (k + 1), H C x) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RadialCellDissection.arcInt]
    rw [hk1 k k.2, hk2 k k.2]
  · intro k hk
    rw [hk1 k hk, hk2 k hk]
    exact hint _

end
end Dubon2026.SourceFunctionField.CellGeometry
