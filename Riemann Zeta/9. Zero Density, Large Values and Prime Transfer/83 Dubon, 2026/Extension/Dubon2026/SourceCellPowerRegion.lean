import Dubon2026.SourceCellPowerBreaks
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Separation.Regular

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch and pole cells.
The source power pullback retains the exact radial preimage, multiplicity,
arc laps and separated inverse branches needed for geometric pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing radial periodicity and periodic argument evaluation are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open scoped Real

theorem rootRadius_contDiffOn (r : ℝ → ℝ) (hper : Function.Periodic r (2 * π))
    (hpos : ∀ φ, 0 < r φ) (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0)
    (hφN : φs (Fin.last N) = 2 * π)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (e : ℕ) (he : e ≠ 0) (j : Fin (e * N)) :
    ContDiffOn ℝ 2 (rootRadius r e)
      (Set.Icc (rootBreaks N hN φs e j.castSucc) (rootBreaks N hN φs e j.succ)) := by
  have heR := natCast_pos_of_ne_zero he
  have h00 : ∀ h : 0 < N + 1, φs ⟨0, h⟩ = 0 := fun _ => hφ0
  have hNN : ∀ h : N < N + 1, φs ⟨N, h⟩ = 2 * π := fun _ => hφN
  have hC2' : ∀ (i : Fin N) (k : ℕ), ContDiffOn ℝ 2 r
      (Set.Icc (2 * π * k + φs i.castSucc) (2 * π * k + φs i.succ)) := by
    intro i k
    have hmaps : Set.MapsTo (fun x : ℝ => x - 2 * π * k)
        (Set.Icc (2 * π * k + φs i.castSucc) (2 * π * k + φs i.succ))
        (Set.Icc (φs i.castSucc) (φs i.succ)) := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2]
    refine ((hC2 i).comp ((contDiff_id.sub contDiff_const).contDiffOn) hmaps).congr ?_
    intro x hx
    show r x = r (x - 2 * π * k)
    rw [show x - 2 * π * (k : ℝ) = x - (k : ℝ) * (2 * π) by ring]
    exact (hper.sub_nat_mul_eq k).symm
  have hpiece : ∀ (i : Fin N) (k : ℕ), ContDiffOn ℝ 2
      (fun ψ : ℝ => (r (e * ψ)) ^ ((e : ℝ)⁻¹))
      (Set.Icc ((2 * π * k + φs i.castSucc) / e) ((2 * π * k + φs i.succ) / e)) := by
    intro i k
    refine ContDiffOn.rpow_const_of_ne ?_ (fun ψ _ => (hpos _).ne')
    have hmaps2 : Set.MapsTo (fun ψ : ℝ => (e : ℝ) * ψ)
        (Set.Icc ((2 * π * k + φs i.castSucc) / e) ((2 * π * k + φs i.succ) / e))
        (Set.Icc (2 * π * k + φs i.castSucc) (2 * π * k + φs i.succ)) := by
      intro ψ hψ
      simp only [Set.mem_Icc] at hψ ⊢
      exact ⟨le_of_div_le heR hψ.1, div_le_of_le heR hψ.2⟩
    exact (hC2' i k).comp ((contDiff_const.mul contDiff_id).contDiffOn) hmaps2
  have hi : j.val % N < N := Nat.mod_lt _ hN
  have hdm : j.val = N * (j.val / N) + j.val % N := (Nat.div_add_mod j.val N).symm
  show ContDiffOn ℝ 2 (fun ψ : ℝ => (r (e * ψ)) ^ ((e : ℝ)⁻¹)) (Set.Icc
    ((2 * π * (j.castSucc.val / N : ℕ) + φs _) / e)
    ((2 * π * (j.succ.val / N : ℕ) + φs _) / e))
  rcases Nat.lt_or_ge (j.val % N + 1) N with hsplit | hsplit
  · have hd1 : j.succ.val / N = j.castSucc.val / N := by
      rw [Fin.val_succ, Fin.val_castSucc]
      conv_lhs => rw [hdm]
      conv_rhs => rw [hdm]
      rw [add_assoc, Nat.mul_add_div hN, Nat.mul_add_div hN,
        Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hsplit]
    have hm1 : j.succ.val % N = j.val % N + 1 := by
      rw [Fin.val_succ]
      conv_lhs => rw [hdm]
      rw [add_assoc, add_comm (N * (j.val / N)) (j.val % N + 1),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsplit]
    have hfin1 : (⟨j.succ.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1))
        = ⟨j.val % N + 1, Nat.succ_lt_succ hi⟩ := Fin.ext hm1
    have hfin2 : (⟨j.castSucc.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1))
        = ⟨j.val % N, Nat.lt_succ_of_lt hi⟩ := Fin.ext (by rw [Fin.val_castSucc])
    rw [hd1, hfin1, hfin2, Fin.val_castSucc]
    exact hpiece ⟨j.val % N, hi⟩ (j.val / N)
  · have hiN : j.val % N + 1 = N := le_antisymm (Nat.mod_lt _ hN) hsplit
    have hd2 : j.succ.val / N = j.val / N + 1 := by
      rw [Fin.val_succ]
      conv_lhs => rw [hdm, add_assoc, hiN, ← Nat.mul_succ]
      exact Nat.mul_div_cancel_left _ hN
    have hm2 : j.succ.val % N = 0 := by
      rw [Fin.val_succ]
      conv_lhs => rw [hdm, add_assoc, hiN, ← Nat.mul_succ]
      exact Nat.mul_mod_right N _
    have hfin1 : (⟨j.succ.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1))
        = ⟨0, Nat.succ_pos N⟩ := Fin.ext hm2
    have hfin2 : (⟨j.castSucc.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1))
        = ⟨j.val % N, Nat.lt_succ_of_lt hi⟩ := Fin.ext (by rw [Fin.val_castSucc])
    rw [hd2, hfin1, hfin2, Fin.val_castSucc]
    have hright : (2 * π * ((j.val / N : ℕ) + 1 : ℕ) + φs ⟨0, Nat.succ_pos N⟩) / e
        = (2 * π * (j.val / N : ℕ) + φs ⟨N, N.lt_succ_self⟩) / e := by
      rw [h00, hNN]
      push_cast
      ring
    rw [hright]
    have hp := hpiece ⟨j.val % N, hi⟩ (j.val / N)
    rw [show (⟨j.val % N, hi⟩ : Fin N).succ = ⟨N, N.lt_succ_self⟩ from
      Fin.ext (by rw [Fin.val_succ]; exact hiN)] at hp
    exact hp

theorem radialRegion_N_pos (R : RadialRegion) : 0 < R.N := by
  rcases Nat.eq_zero_or_pos R.N with h | h
  · exfalso
    have hlast : Fin.last R.N = (0 : Fin (R.N + 1)) :=
      Fin.ext (by exact h)
    have h1 := R.hφN
    rw [hlast, R.hφ0] at h1
    linarith [Real.pi_pos]
  · exact h

/- As constructed below. -/
/-- The exact radial preimage of a region under its centered power map. -/
noncomputable def efold (R : RadialRegion) (e : ℕ) (he : e ≠ 0) : RadialRegion where
  q := 0
  r := rootRadius R.r e
  hcont := rootRadius_continuous R.r R.hcont R.hpos e
  hper := rootRadius_periodic R.r R.hper e
  hpos := rootRadius_pos R.r R.hpos e
  N := e * R.N
  φs := rootBreaks R.N (radialRegion_N_pos R) R.φs e
  hφ0 := rootBreaks_zero R.N (radialRegion_N_pos R) R.φs R.hφ0 e
  hφN := rootBreaks_last R.N (radialRegion_N_pos R) R.φs R.hφ0 e he
  hmono := rootBreaks_strictMono R.N (radialRegion_N_pos R) R.φs R.hφ0 R.hφN R.hmono e he
  hC2 := rootRadius_contDiffOn R.r R.hper R.hpos R.N (radialRegion_N_pos R) R.φs R.hφ0 R.hφN
    R.hC2 e he

theorem efold_q (R : RadialRegion) (e : ℕ) (he : e ≠ 0) : (efold R e he).q = 0 := rfl

theorem efold_N (R : RadialRegion) (e : ℕ) (he : e ≠ 0) : (efold R e he).N = e * R.N := rfl

theorem efold_r (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (ψ : ℝ) :
    (efold R e he).r ψ = (R.r (e * ψ)) ^ ((e : ℝ)⁻¹) := rfl


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
