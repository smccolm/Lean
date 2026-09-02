import GafniTao.FordShiftedWeylApplication

/-!
# The complete shifted Weyl range `1.9 <= lambda <= 2.6`

This file converts the two exact A/B-process majorants into a common power
saving and then into the deliberately weaker exponent used by the current
Ford detector.  The split at `t = N^2` is internal; the public theorem is
stated only in terms of Ford's physical logarithmic scale.
-/

namespace GafniTao

noncomputable section

theorem fordCubeRoot_rpow {x a : ℝ} (hx : 0 < x) :
    fordCubeRoot (x ^ a) = x ^ (a / 3) := by
  unfold fordCubeRoot
  rw [← Real.rpow_mul hx.le]
  congr 1
  ring

theorem fordCubeRoot_le_rpow
    {N : ℕ} {t a : ℝ} (hN : 0 < N) (ht : 0 ≤ t)
    (hta : t ≤ (N : ℝ) ^ a) :
    fordCubeRoot t ≤ (N : ℝ) ^ (a / 3) := by
  calc
    fordCubeRoot t ≤ fordCubeRoot ((N : ℝ) ^ a) :=
      fordCubeRoot_mono ht hta
    _ = (N : ℝ) ^ (a / 3) := fordCubeRoot_rpow (by positivity)

theorem ford_rpow_le_cubeRoot
    {N : ℕ} {t a : ℝ} (hN : 0 < N)
    (hta : (N : ℝ) ^ a ≤ t) :
    (N : ℝ) ^ (a / 3) ≤ fordCubeRoot t := by
  calc
    (N : ℝ) ^ (a / 3) = fordCubeRoot ((N : ℝ) ^ a) :=
      (fordCubeRoot_rpow (by positivity)).symm
    _ ≤ fordCubeRoot t :=
      fordCubeRoot_mono (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) a) hta

theorem ford_shifted_weyl_below_square_power
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t)
    (hLow : (N : ℝ) ^ (19 / 10 : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      90 * (N : ℝ) ^ (13 / 15 : ℝ) := by
  have hraw := ford_shifted_weyl_below_square
    hN hNR hR hu0 hu1 hNt htN
  let A : ℝ := (N + 1 : ℕ) + u
  let Y : ℝ := fordCubeRoot t
  let Z : ℝ := (N : ℝ) ^ (13 / 15 : ℝ)
  have hNpos : (0 : ℝ) < N := by positivity
  have ht : 0 < t := hNpos.trans_le hNt
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one
    (one_le_fordCubeRoot (show 1 ≤ t by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      exact this.trans hNt))
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    norm_num
    have hNTwo : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    linarith
  have hYcube : Y ^ 3 = t := fordCubeRoot_cube ht
  have hYlow : (N : ℝ) ^ (19 / 30 : ℝ) ≤ Y := by
    have hroot := ford_rpow_le_cubeRoot (show 0 < N by omega) hLow
    norm_num at hroot ⊢
    exact hroot
  have hYsqLow : (N : ℝ) ^ (19 / 15 : ℝ) ≤ Y ^ 2 := by
    have hsq := mul_le_mul hYlow hYlow
      (Real.rpow_nonneg hNpos.le _) hYpos.le
    have hp : ((N : ℝ) ^ (19 / 30 : ℝ)) ^ 2 =
        (N : ℝ) ^ (19 / 15 : ℝ) := by
      calc
        ((N : ℝ) ^ (19 / 30 : ℝ)) ^ 2 =
            ((N : ℝ) ^ (19 / 30 : ℝ)) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (N : ℝ) ^ ((19 / 30 : ℝ) * 2) :=
          (Real.rpow_mul hNpos.le _ _).symm
        _ = (N : ℝ) ^ (19 / 15 : ℝ) := by norm_num
    rw [← hp]
    simpa only [pow_two] using hsq
  have hsplit : (N : ℝ) ^ 3 =
      (N : ℝ) ^ (26 / 15 : ℝ) *
        (N : ℝ) ^ (19 / 15 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num [Real.rpow_natCast]
  have hZsq : Z ^ 2 = (N : ℝ) ^ (26 / 15 : ℝ) := by
    dsimp [Z]
    calc
      ((N : ℝ) ^ (13 / 15 : ℝ)) ^ 2 =
          ((N : ℝ) ^ (13 / 15 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((13 / 15 : ℝ) * 2) :=
        (Real.rpow_mul hNpos.le _ _).symm
      _ = (N : ℝ) ^ (26 / 15 : ℝ) := by norm_num
  have hinside :
      (4 * (N : ℝ) ^ 2 / t) * A * Y ≤ 9 * Z ^ 2 := by
    rw [← hYcube]
    rw [show (4 * (N : ℝ) ^ 2 / Y ^ 3) * A * Y =
      (4 * (N : ℝ) ^ 2 * A * Y) / Y ^ 3 by ring]
    rw [div_le_iff₀ (pow_pos hYpos 3)]
    have hleft : 4 * (N : ℝ) ^ 2 * A ≤ 8 * (N : ℝ) ^ 3 := by
      nlinarith [hAle, hNpos, sq_nonneg (N : ℝ)]
    have hmul : 8 * (N : ℝ) ^ 3 ≤ 8 * Z ^ 2 * Y ^ 2 := by
      calc
        8 * (N : ℝ) ^ 3 =
            8 * (Z ^ 2 * (N : ℝ) ^ (19 / 15 : ℝ)) := by
          rw [hsplit, hZsq]
        _ ≤ 8 * (Z ^ 2 * Y ^ 2) := by gcongr
        _ = 8 * Z ^ 2 * Y ^ 2 := by ring
    have hbase : 4 * (N : ℝ) ^ 2 * A ≤ 9 * Z ^ 2 * Y ^ 2 := by
      nlinarith [hleft, hmul, sq_nonneg Z, sq_nonneg Y]
    have := mul_le_mul_of_nonneg_right hbase hYpos.le
    nlinarith [sq_nonneg Y]
  have hZpos : 0 < Z := Real.rpow_pos_of_pos hNpos _
  have hsqrt :
      Real.sqrt ((4 * (N : ℝ) ^ 2 / t) * A * Y) ≤ 3 * Z := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrt' :
      Real.sqrt ((4 * (N : ℝ) ^ 2 / t) * ((N + 1 : ℕ) + u) *
        fordCubeRoot t) ≤ 3 * (N : ℝ) ^ (13 / 15 : ℝ) := by
    simpa only [A, Y, Z] using hsqrt
  exact hraw.trans (by nlinarith)

theorem ford_shifted_weyl_above_square_power
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t) (hN2t : (N : ℝ) ^ 2 ≤ t)
    (hHigh : t ≤ (N : ℝ) ^ (13 / 5 : ℝ)) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      90 * (N : ℝ) ^ (14 / 15 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow3 : (N : ℝ) ^ (13 / 5 : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNOne
      (by norm_num : (13 / 5 : ℝ) ≤ 3)
  have htN3 : t ≤ (N : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast]
    exact hHigh.trans hpow3
  have hraw := ford_shifted_weyl_above_square
    hN hNR hR hu0 hu1 hNt hN2t htN3
  let A : ℝ := (N + 1 : ℕ) + u
  let Y : ℝ := fordCubeRoot t
  let Z : ℝ := (N : ℝ) ^ (14 / 15 : ℝ)
  have ht : 0 < t := hNpos.trans_le hNt
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    norm_num
    have hNTwo : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    linarith
  have hYle : Y ≤ (N : ℝ) ^ (13 / 15 : ℝ) := by
    have := fordCubeRoot_le_rpow (show 0 < N by omega) ht.le hHigh
    norm_num at this ⊢
    exact this
  have hprod : (N : ℝ) * (N : ℝ) ^ (13 / 15 : ℝ) = Z ^ 2 := by
    dsimp [Z]
    calc
      (N : ℝ) * (N : ℝ) ^ (13 / 15 : ℝ) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (13 / 15 : ℝ) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ (1 + 13 / 15 : ℝ) :=
        (Real.rpow_add hNpos _ _).symm
      _ =
          (N : ℝ) ^ ((14 / 15 : ℝ) * 2) := by norm_num
      _ = ((N : ℝ) ^ (14 / 15 : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_mul hNpos.le _ _
      _ = ((N : ℝ) ^ (14 / 15 : ℝ)) ^ 2 := Real.rpow_natCast _ 2
  have hinside : 4 * A * Y ≤ 9 * Z ^ 2 := by
    have hmul := mul_le_mul hAle hYle (fordCubeRoot_nonneg ht.le) (by positivity)
    calc
      4 * A * Y ≤ 8 * ((N : ℝ) * (N : ℝ) ^ (13 / 15 : ℝ)) := by
        nlinarith
      _ = 8 * Z ^ 2 := by rw [hprod]
      _ ≤ 9 * Z ^ 2 := by nlinarith [sq_nonneg Z]
  have hsqrt : Real.sqrt (4 * A * Y) ≤ 3 * Z := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith⟩
  have hsqrt' :
      Real.sqrt (4 * ((N + 1 : ℕ) + u) * fordCubeRoot t) ≤
        3 * (N : ℝ) ^ (14 / 15 : ℝ) := by
    simpa only [A, Y, Z] using hsqrt
  exact hraw.trans (by nlinarith)

#print axioms ford_shifted_weyl_below_square_power
#print axioms ford_shifted_weyl_above_square_power

end

end GafniTao
