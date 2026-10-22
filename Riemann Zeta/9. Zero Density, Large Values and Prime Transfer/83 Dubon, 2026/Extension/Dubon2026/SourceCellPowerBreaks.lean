import Dubon2026.SourceCellPowerRadius
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

/- As constructed below. -/
/-- The ordered breakpoints of all power-map laps of the original boundary. -/
def rootBreaks (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ) (e : ℕ)
    (j : Fin (e * N + 1)) : ℝ :=
  (2 * π * (j.val / N : ℕ) + φs ⟨j.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩) / e

theorem rootBreaks_eq (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ) (e : ℕ)
    (i : Fin (e * N + 1)) (a : ℕ) (m : Fin (N + 1)) (hdiv : i.val / N = a)
    (hmod : i.val % N = m.val) :
    rootBreaks N hN φs e i = (2 * π * a + φs m) / e := by
  have hfin : (⟨i.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1)) = m :=
    Fin.ext hmod
  show (2 * π * (i.val / N : ℕ) + φs ⟨i.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩) / e
    = (2 * π * a + φs m) / e
  rw [hdiv, hfin]

theorem rootBreaks_zero (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0)
    (e : ℕ) : rootBreaks N hN φs e 0 = 0 := by
  have h00 : ∀ h : 0 < N + 1, φs ⟨0, h⟩ = 0 := fun _ => hφ0
  show (2 * π * ((0 : Fin (e * N + 1)).val / N : ℕ) + φs _) / e = 0
  simp only [Fin.val_zero, Nat.zero_div, Nat.zero_mod, Nat.cast_zero, mul_zero, h00, add_zero,
    zero_div]

theorem rootBreaks_last (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0)
    (e : ℕ) (he : e ≠ 0) : rootBreaks N hN φs e (Fin.last (e * N)) = 2 * π := by
  have heR := natCast_pos_of_ne_zero he
  have h00 : ∀ h : 0 < N + 1, φs ⟨0, h⟩ = 0 := fun _ => hφ0
  show (2 * π * ((Fin.last (e * N)).val / N : ℕ) + φs _) / e = 2 * π
  have hd : (Fin.last (e * N)).val / N = e := by
    rw [Fin.val_last, Nat.mul_div_assoc e (dvd_refl N), Nat.div_self hN, mul_one]
  have hm : (Fin.last (e * N)).val % N = 0 := by
    rw [Fin.val_last]; exact Nat.mul_mod_left e N
  rw [hd]
  have hfin : (⟨(Fin.last (e * N)).val % N,
      Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1)) = ⟨0, Nat.succ_pos N⟩ :=
    Fin.ext hm
  rw [hfin, h00, add_zero, div_eq_iff heR.ne']

theorem rootBreaks_strictMono (N : ℕ) (hN : 0 < N) (φs : Fin (N + 1) → ℝ)
    (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * π) (hmono : StrictMono φs)
    (e : ℕ) (he : e ≠ 0) : StrictMono (rootBreaks N hN φs e) := by
  have heR := natCast_pos_of_ne_zero he
  have h00 : ∀ h : 0 < N + 1, φs ⟨0, h⟩ = 0 := fun _ => hφ0
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  have hi : j.val % N < N := Nat.mod_lt _ hN
  have hdm : j.val = N * (j.val / N) + j.val % N := (Nat.div_add_mod j.val N).symm
  show (2 * π * (j.castSucc.val / N : ℕ) + φs _) / e
    < (2 * π * (j.succ.val / N : ℕ) + φs _) / e
  rcases Nat.lt_or_ge (j.val % N + 1) N with hsplit | hsplit
  ·
    have hd1 : j.succ.val / N = j.castSucc.val / N := by
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
    rw [hd1, hfin1, hfin2]
    refine div_lt_div_aux heR ?_
    have hlt : φs ⟨j.val % N, Nat.lt_succ_of_lt hi⟩
        < φs ⟨j.val % N + 1, Nat.succ_lt_succ hi⟩ :=
      hmono (Fin.mk_lt_mk.mpr (lt_add_one _))
    linarith
  ·
    have hiN : j.val % N + 1 = N := le_antisymm (Nat.mod_lt _ hN) hsplit
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
    rw [hd2, hfin1, hfin2, h00, Fin.val_castSucc]
    refine div_lt_div_aux heR ?_
    have hlt : φs ⟨j.val % N, Nat.lt_succ_of_lt hi⟩ < 2 * π := by
      rw [← hφN]
      exact hmono (by rw [Fin.lt_def]; exact hi)
    push_cast
    linarith


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
