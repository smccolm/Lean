import GafniTao.FordShiftedWeylCore

/-!
# Applying the real-base Weyl estimate to Ford's literal source sum

The reindexing below retains the half-open source interval and the real shift.
The two estimates split according to whether the height lies below or above
the square of the dyadic base; the lower branch records the exact slack
`4 N^2 / t` instead of silently rounding it to a constant.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

def fordCubeRoot (t : ℝ) : ℝ := t ^ (1 / 3 : ℝ)

theorem fordCubeRoot_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fordCubeRoot t := by
  unfold fordCubeRoot
  exact Real.rpow_nonneg ht _

theorem fordCubeRoot_cube {t : ℝ} (ht : 0 < t) :
    fordCubeRoot t ^ 3 = t := by
  unfold fordCubeRoot
  calc
    (t ^ (1 / 3 : ℝ)) ^ 3 = (t ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by
      exact (Real.rpow_natCast (t ^ (1 / 3 : ℝ)) 3).symm
    _ = t ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul ht.le _ _).symm
    _ = t := by norm_num

theorem one_le_fordCubeRoot {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ fordCubeRoot t := by
  unfold fordCubeRoot
  simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) ht
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

theorem fordCubeRoot_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    fordCubeRoot s ≤ fordCubeRoot t := by
  unfold fordCubeRoot
  exact Real.rpow_le_rpow hs hst (by norm_num)

theorem ford_integerLogarithmicPrefix_eq_range
    (t A : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.Ico (0 : ℤ) L, integerLogarithmicTerm t A n) =
      ∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + n)) := by
  apply Finset.sum_bij (fun n _hn => Int.toNat n)
  case hi =>
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    apply Finset.mem_range.mpr
    have hcast : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn'.1
    exact_mod_cast (show ((Int.toNat n : ℕ) : ℤ) < (L : ℤ) by
      rw [hcast]
      exact hn'.2)
  case i_inj =>
    intro n₁ hn₁ n₂ hn₂ heq
    have h₁ := (Finset.mem_Ico.mp hn₁).1
    have h₂ := (Finset.mem_Ico.mp hn₂).1
    have heqInt := congrArg (fun m : ℕ => (m : ℤ)) heq
    change ((Int.toNat n₁ : ℕ) : ℤ) = ((Int.toNat n₂ : ℕ) : ℤ) at heqInt
    simpa [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂] using heqInt
  case i_surj =>
    intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    exact Finset.mem_Ico.mpr ⟨by positivity, by exact_mod_cast Finset.mem_range.mp hn⟩
  case h =>
    intro n hn
    have hn0 := (Finset.mem_Ico.mp hn).1
    unfold integerLogarithmicTerm
    congr 2
    have hcast : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    have hcastReal : ((Int.toNat n : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hcast
    rw [hcastReal]

theorem ford_integerLogarithmicPrefix_eq_source
    (N L : ℕ) (u t : ℝ) :
    (∑ n ∈ Finset.Ico (0 : ℤ) L,
        integerLogarithmicTerm t ((N + 1 : ℕ) + u) n) =
      fordShiftedExponentialSum N (N + L) u t := by
  rw [ford_integerLogarithmicPrefix_eq_range]
  rw [fordShiftedExponentialSum_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [fordShiftedLogPhase_eq_unitaryPhase]
  unfold fordShiftedRealPhase
  congr 2
  push_cast
  ring

theorem ford_shifted_weyl_below_square
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      30 * Real.sqrt
        ((4 * (N : ℝ) ^ 2 / t) * ((N + 1 : ℕ) + u) * fordCubeRoot t) := by
  let L := R - N
  let A : ℝ := (N + 1 : ℕ) + u
  let Y : ℝ := fordCubeRoot t
  let X : ℝ := 4 * (N : ℝ) ^ 2 / t
  have hNpos : (0 : ℝ) < N := by positivity
  have ht : 0 < t := hNpos.trans_le hNt
  have hYcube : Y ^ 3 = t := fordCubeRoot_cube ht
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNTwo : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hY : 1 ≤ Y := one_le_fordCubeRoot (hNOne.trans hNt)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    norm_num
    linarith
  have hYA : Y ≤ A := by
    have hroot := fordCubeRoot_mono ht.le htN
    have hrootSq : fordCubeRoot ((N : ℝ) ^ 2) ≤ (N : ℝ) := by
      have hcubeN : ((N : ℝ) ^ 2) ≤ (N : ℝ) ^ 3 := by
        nlinarith [hNpos, show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
      have hmono := fordCubeRoot_mono (sq_nonneg (N : ℝ)) hcubeN
      rw [show fordCubeRoot ((N : ℝ) ^ 3) = (N : ℝ) by
        apply (pow_left_inj₀ (fordCubeRoot_nonneg (by positivity))
          hNpos.le (by norm_num : (3 : ℕ) ≠ 0)).mp
        rw [fordCubeRoot_cube (by positivity)] ] at hmono
      exact hmono
    have hNA : (N : ℝ) ≤ A := by
      dsimp [A]
      norm_num
      linarith
    exact hroot.trans (hrootSq.trans hNA)
  have hX : 1 ≤ X := by
    dsimp [X]
    rw [le_div_iff₀ ht]
    nlinarith [htN, sq_nonneg (N : ℝ)]
  have hAY : A ^ 2 ≤ X * Y ^ 3 := by
    rw [hYcube]
    dsimp [X]
    field_simp [ht.ne']
    nlinarith [hAle, hA, hNpos]
  have hLNat : L ≤ N := by dsimp [L]; omega
  have hLA : (L : ℝ) ≤ A := by
    have hNA : (N : ℝ) ≤ A := by
      dsimp [A]
      norm_num
      linarith
    exact (Nat.cast_le.mpr hLNat).trans hNA
  have hcore := ford_real_base_weyl_prefix hY hX hA hYA hAY hLA
  rw [hYcube, ford_integerLogarithmicPrefix_eq_source] at hcore
  have hNL : N + L = R := by dsimp [L]; omega
  rw [hNL] at hcore
  exact hcore

theorem ford_shifted_weyl_above_square
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t) (hN2t : (N : ℝ) ^ 2 ≤ t)
    (htN3 : t ≤ (N : ℝ) ^ 3) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      30 * Real.sqrt (4 * ((N + 1 : ℕ) + u) * fordCubeRoot t) := by
  let L := R - N
  let A : ℝ := (N + 1 : ℕ) + u
  let Y : ℝ := fordCubeRoot t
  have hNpos : (0 : ℝ) < N := by positivity
  have ht : 0 < t := hNpos.trans_le hNt
  have hYcube : Y ^ 3 = t := fordCubeRoot_cube ht
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNTwo : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hY : 1 ≤ Y := one_le_fordCubeRoot (hNOne.trans hNt)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    norm_num
    linarith
  have hYA : Y ≤ A := by
    have hroot := fordCubeRoot_mono ht.le htN3
    have hrootCube : fordCubeRoot ((N : ℝ) ^ 3) = (N : ℝ) := by
      apply (pow_left_inj₀ (fordCubeRoot_nonneg (by positivity))
        hNpos.le (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [fordCubeRoot_cube (by positivity)]
    rw [hrootCube] at hroot
    have hNA : (N : ℝ) ≤ A := by
      dsimp [A]
      norm_num
      linarith
    exact hroot.trans hNA
  have hAY : A ^ 2 ≤ (4 : ℝ) * Y ^ 3 := by
    rw [hYcube]
    nlinarith [hAle, hA, hN2t, hNpos]
  have hLNat : L ≤ N := by dsimp [L]; omega
  have hLA : (L : ℝ) ≤ A := by
    have hNA : (N : ℝ) ≤ A := by
      dsimp [A]
      norm_num
      linarith
    exact (Nat.cast_le.mpr hLNat).trans hNA
  have hcore := ford_real_base_weyl_prefix hY (by norm_num : (1 : ℝ) ≤ 4)
    hA hYA hAY hLA
  rw [hYcube, ford_integerLogarithmicPrefix_eq_source] at hcore
  have hNL : N + L = R := by dsimp [L]; omega
  rw [hNL] at hcore
  exact hcore

#print axioms fordCubeRoot_cube
#print axioms ford_integerLogarithmicPrefix_eq_source
#print axioms ford_shifted_weyl_below_square
#print axioms ford_shifted_weyl_above_square

end

end GafniTao
