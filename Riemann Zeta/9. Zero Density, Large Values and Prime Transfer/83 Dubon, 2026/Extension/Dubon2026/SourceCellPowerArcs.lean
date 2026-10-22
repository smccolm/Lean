import Dubon2026.SourceCellPowerRegion
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
/-- The boundary-arc index corresponding to a chosen lap and original arc. -/
def lapIdx (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    Fin (efold R e he).N :=
  ⟨j.val * R.N + k.val, by
    show j.val * R.N + k.val < e * R.N
    exact lap_lt j.isLt k.isLt⟩

theorem lapIdx_val (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    (lapIdx R e he j k).val = j.val * R.N + k.val := rfl

theorem lapIdx_injective (R : RadialRegion) (e : ℕ) (he : e ≠ 0) :
    Function.Injective (fun jk : Fin e × Fin R.N => lapIdx R e he jk.1 jk.2) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  have hv : j.val * R.N + k.val = j'.val * R.N + k'.val := by
    have hv0 := congrArg Fin.val h
    exact hv0
  have hj : j.val = j'.val := by
    have h1 : (j.val * R.N + k.val) / R.N = j.val := lap_div k.isLt
    have h2 : (j'.val * R.N + k'.val) / R.N = j'.val := lap_div k'.isLt
    rw [hv] at h1
    exact h1.symm.trans h2
  have hk : k.val = k'.val := by
    have h1 : (j.val * R.N + k.val) % R.N = k.val := lap_mod k.isLt
    have h2 : (j'.val * R.N + k'.val) % R.N = k'.val := lap_mod k'.isLt
    rw [hv] at h1
    exact h1.symm.trans h2
  have hj' : j = j' := Fin.ext hj
  have hk' : k = k' := Fin.ext hk
  subst hj' hk'
  rfl

theorem lapIdx_surjective (R : RadialRegion) (e : ℕ) (he : e ≠ 0) :
    Function.Surjective (fun jk : Fin e × Fin R.N => lapIdx R e he jk.1 jk.2) := by
  intro i
  have hN : 0 < R.N := radialRegion_N_pos R
  have hi : i.val < e * R.N := i.isLt
  refine ⟨(⟨i.val / R.N, (Nat.div_lt_iff_lt_mul hN).2 hi⟩, ⟨i.val % R.N, Nat.mod_lt _ hN⟩), ?_⟩
  apply Fin.ext
  show i.val / R.N * R.N + i.val % R.N = i.val
  exact Nat.div_add_mod' i.val R.N

theorem φs_lapIdx_castSucc (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    (efold R e he).φs (lapIdx R e he j k).castSucc
      = (2 * π * ((j : ℕ) : ℝ) + R.φs k.castSucc) / (e : ℝ) := by
  have hdiv : (lapIdx R e he j k).castSucc.val / R.N = j.val := by
    show (j.val * R.N + k.val) / R.N = j.val
    exact lap_div k.isLt
  have hmod : (lapIdx R e he j k).castSucc.val % R.N = (k.castSucc).val := by
    show (j.val * R.N + k.val) % R.N = k.val
    exact lap_mod k.isLt
  exact rootBreaks_eq R.N (radialRegion_N_pos R) R.φs e (lapIdx R e he j k).castSucc j.val
    k.castSucc hdiv hmod

theorem φs_lapIdx_succ (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    (efold R e he).φs (lapIdx R e he j k).succ
      = (2 * π * ((j : ℕ) : ℝ) + R.φs k.succ) / (e : ℝ) := by
  have hN : 0 < R.N := radialRegion_N_pos R
  rcases Nat.lt_or_ge (k.val + 1) R.N with hsplit | hsplit
  ·
    have hdiv : (lapIdx R e he j k).succ.val / R.N = j.val := by
      show (j.val * R.N + k.val + 1) / R.N = j.val
      rw [Nat.add_assoc]
      exact lap_div hsplit
    have hmod : (lapIdx R e he j k).succ.val % R.N = (k.succ).val := by
      show (j.val * R.N + k.val + 1) % R.N = k.val + 1
      rw [Nat.add_assoc]
      exact lap_mod hsplit
    exact rootBreaks_eq R.N (radialRegion_N_pos R) R.φs e (lapIdx R e he j k).succ j.val k.succ
      hdiv hmod
  ·
    have hkN : k.val + 1 = R.N := by
      have hk := k.isLt
      omega
    have hdiv : (lapIdx R e he j k).succ.val / R.N = j.val + 1 := by
      show (j.val * R.N + k.val + 1) / R.N = j.val + 1
      rw [Nat.add_assoc, hkN, Nat.add_div_right _ hN, Nat.mul_div_cancel _ hN]
    have hmod : (lapIdx R e he j k).succ.val % R.N
        = (⟨0, Nat.succ_pos R.N⟩ : Fin (R.N + 1)).val := by
      show (j.val * R.N + k.val + 1) % R.N = 0
      rw [Nat.add_assoc, hkN, Nat.add_mod_right, Nat.mul_mod_left]
    have h00 : R.φs ⟨0, Nat.succ_pos R.N⟩ = 0 := R.hφ0
    have hks : k.succ = Fin.last R.N :=
      Fin.ext (by exact hkN)
    refine (rootBreaks_eq R.N (radialRegion_N_pos R) R.φs e (lapIdx R e he j k).succ (j.val + 1)
      ⟨0, Nat.succ_pos R.N⟩ hdiv hmod).trans ?_
    rw [h00, hks, R.hφN]
    push_cast
    ring

theorem arcIcc_lapIdx (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    (efold R e he).arcIcc (lapIdx R e he j k) =
      (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k := by
  have heR := natCast_pos_of_ne_zero he
  unfold RadialRegion.arcIcc
  rw [φs_lapIdx_castSucc, φs_lapIdx_succ]
  exact (image_shift_div_Icc (2 * π * ((j : ℕ) : ℝ)) heR (R.φs k.castSucc)
    (R.φs k.succ)).symm

theorem mem_K_iff (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (u : ℂ) :
    u ∈ (efold R e he).K ↔ R.q + u ^ e ∈ R.K := by
  show ‖u - 0‖ ≤ rootRadius R.r e (Complex.arg (u - 0))
    ↔ ‖R.q + u ^ e - R.q‖ ≤ R.r (Complex.arg (R.q + u ^ e - R.q))
  rw [sub_zero]
  exact norm_le_rootRadius_iff R.hper R.hpos he R.q u

theorem mem_Kint_iff (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (u : ℂ) :
    u ∈ (efold R e he).Kint ↔ R.q + u ^ e ∈ R.Kint := by
  show ‖u - 0‖ < rootRadius R.r e (Complex.arg (u - 0))
    ↔ ‖R.q + u ^ e - R.q‖ < R.r (Complex.arg (R.q + u ^ e - R.q))
  rw [sub_zero]
  exact norm_lt_rootRadius_iff R.hper R.hpos he R.q u

theorem zero_mem_Kint (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (h : R.q ∈ R.Kint) :
    (0 : ℂ) ∈ (efold R e he).Kint := by
  rw [mem_Kint_iff, zero_pow he, add_zero]
  exact h

theorem loop_pow (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (ψ : ℝ) :
    R.q + ((efold R e he).loop ψ) ^ e = R.loop (e * ψ) := by
  have hA : (0 : ℝ) ≤ R.r (e * ψ) := (R.hpos _).le
  show R.q + ((0 : ℂ) + ((R.r (e * ψ) ^ ((e : ℝ)⁻¹) : ℝ) : ℂ)
      * Complex.exp ((ψ : ℂ) * Complex.I)) ^ e
    = R.q + (R.r (e * ψ) : ℂ) * Complex.exp (((e * ψ : ℝ) : ℂ) * Complex.I)
  rw [zero_add, mul_pow, ← Complex.ofReal_pow, Real.rpow_inv_natCast_pow hA he,
    ← Complex.exp_nat_mul,
    show ((e : ℂ) * ((ψ : ℂ) * Complex.I)) = (((e * ψ : ℝ) : ℂ) * Complex.I) by push_cast; ring]

theorem loop_nat_add (R : RadialRegion) (n : ℕ) (t : ℝ) :
    R.loop (2 * π * n + t) = R.loop t := by
  rw [show 2 * π * (n : ℝ) + t = t + n * (2 * π) by ring]
  exact (R.loop_periodic.nat_mul n) t

theorem loop_lap (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (n : ℕ) (t : ℝ) :
    R.q + ((efold R e he).loop ((2 * Real.pi * n + t) / e)) ^ e = R.loop t := by
  have heR := natCast_pos_of_ne_zero he
  rw [loop_pow, mul_div_self_aux heR, loop_nat_add]

theorem image_pow_arcSet (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e) (k : Fin R.N) :
    (fun u : ℂ => R.q + u ^ e) '' (efold R e he).arcSet (lapIdx R e he j k) = R.arcSet k := by
  unfold RadialRegion.arcSet
  rw [arcIcc_lapIdx, Set.image_image, Set.image_image]
  exact Set.image_congr (fun t _ => loop_lap R e he j.val t)


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
