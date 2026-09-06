import GafniTao.HeathBrownFiniteLossAbsorption

/-!
# Finite-loss absorption on the high powered scale

The high source window only guarantees `U ≤ (N^p)^2`, rather than the
stronger low-cell inequality `U^2 ≤ (N^p)^3`.  This file gives the exact
square-root replacement and therefore uses the strict margin
`epsilon < zeta / 2`.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem rpow_one_half_le_of_le_sq
    {U y : Real} (hU : 0 ≤ U) (hy : 0 ≤ y) (hScale : U ≤ y ^ 2) :
    U ^ (1 / 2 : Real) ≤ y := by
  have hRoot := Real.rpow_le_rpow hU hScale
    (by norm_num : (0 : Real) ≤ 1 / 2)
  have hRight : (y ^ 2) ^ (1 / 2 : Real) = y := by
    have hTwo : y ^ (2 : Nat) = y ^ (2 : Real) :=
      (Real.rpow_natCast y 2).symm
    calc
      (y ^ 2) ^ (1 / 2 : Real) =
          (y ^ (2 : Real)) ^ (1 / 2 : Real) := by rw [hTwo]
      _ = y ^ ((2 : Real) * (1 / 2 : Real)) :=
        (Real.rpow_mul hy 2 (1 / 2 : Real)).symm
      _ = y := by norm_num
  simpa only [hRight] using hRoot

theorem eventually_heathBrown_high_finite_loss_le_power
    {P : Nat} {epsilon zeta C0 C2 C4 : Real}
    (hzeta : 0 < zeta) (hmargin : epsilon < zeta / 2)
    (hC0 : 0 ≤ C0) :
    ∀ᶠ U : Real in atTop,
      ∀ (N p : Nat), 0 < N → 0 < p → p ≤ P →
        U ≤ ((N ^ p : Nat) : Real) ^ 2 →
        (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
            (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
            (((2 ^ P : Real) * U) ^ epsilon) ≤
          (((2 ^ P * N ^ p : Nat) : Real) ^ zeta) := by
  let K : Real :=
    (((P ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
      (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
      ((2 ^ P : Real) ^ epsilon)
  have hSmall := eventually_const_mul_rpow_le_rpow
    (D := K) (a := epsilon) (b := zeta / 2) hmargin
  filter_upwards [hSmall, eventually_ge_atTop (1 : Real)] with U hSmallU hU
  intro N p hN hp hpP hScale
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hNp0 : (0 : Real) ≤ ((N ^ p : Nat) : Real) := Nat.cast_nonneg _
  have hLower : U ^ (1 / 2 : Real) ≤ ((N ^ p : Nat) : Real) :=
    rpow_one_half_le_of_le_sq hU0 hNp0 hScale
  have hBase : ((N ^ p : Nat) : Real) ≤
      ((2 ^ P * N ^ p : Nat) : Real) := by
    exact_mod_cast Nat.le_mul_of_pos_left (N ^ p)
      (pow_pos (by omega) P)
  have hPower : U ^ (zeta / 2) ≤
      ((2 ^ P * N ^ p : Nat) : Real) ^ zeta := by
    calc
      U ^ (zeta / 2) = (U ^ (1 / 2 : Real)) ^ zeta := by
        have h := Real.rpow_mul hU0 (1 / 2 : Real) zeta
        simpa only [show (1 / 2 : Real) * zeta = zeta / 2 by ring] using h
      _ ≤ ((N ^ p : Nat) : Real) ^ zeta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hU0 _) hLower hzeta.le
      _ ≤ ((2 ^ P * N ^ p : Nat) : Real) ^ zeta :=
        Real.rpow_le_rpow hNp0 hBase hzeta.le
  have hp4 : (p ^ 4 : Nat) ≤ P ^ 4 := Nat.pow_le_pow_left hpP 4
  have hp4Real : ((p ^ 4 : Nat) : Real) ≤ (P ^ 4 : Nat) := by
    exact_mod_cast hp4
  have hFixed :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          ((2 ^ P : Real) ^ epsilon) ≤ K := by
    dsimp only [K]
    gcongr
  calc
    (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        (((2 ^ P : Real) * U) ^ epsilon) =
      ((((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        ((2 ^ P : Real) ^ epsilon)) * U ^ epsilon := by
          rw [Real.mul_rpow (by positivity : 0 ≤ (2 ^ P : Real)) hU0]
          ring
    _ ≤ K * U ^ epsilon :=
      mul_le_mul_of_nonneg_right hFixed (Real.rpow_nonneg hU0 _)
    _ ≤ U ^ (zeta / 2) := hSmallU
    _ ≤ ((2 ^ P * N ^ p : Nat) : Real) ^ zeta := hPower

theorem eventually_heathBrown_high_cardinality_coefficients
    {P : Nat} {C zeta : Real} (hC : 0 < C) (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      ∀ (N p : Nat), 0 < N → 0 < p → p + 1 ≤ P →
        U ≤ ((N ^ p : Nat) : Real) ^ 2 →
        2 * ((P : Real) * C) ≤
            ((2 ^ P * N ^ p : Nat) : Real) ^ zeta ∧
          2 * (((P + 1 : Nat) : Real) * C) ≤
            ((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ zeta := by
  let K : Real := 2 * (((P + 1 : Nat) : Real) * C)
  have hmargin : (0 : Real) < zeta / 2 := by positivity
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := K) (a := (0 : Real)) (b := zeta / 2) hmargin
  filter_upwards [hAbsorb, eventually_ge_atTop (1 : Real)] with U hAbsorbU hU
  intro N p hN hp _hpNextP hSquare
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hLower := rpow_one_half_le_of_le_sq hU0
    (Nat.cast_nonneg (N ^ p)) hSquare
  have hNpNext : N ^ p ≤ N ^ (p + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hN
  have hBaseMain : U ^ (1 / 2 : Real) ≤
      ((2 ^ P * N ^ p : Nat) : Real) := by
    apply hLower.trans
    exact_mod_cast Nat.le_mul_of_pos_left (N ^ p)
      (pow_pos (by omega : (0 : Nat) < 2) P)
  have hBaseNext : U ^ (1 / 2 : Real) ≤
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) := by
    apply hBaseMain.trans
    exact_mod_cast Nat.mul_le_mul_left (2 ^ P) hNpNext
  have hK : K ≤ U ^ (zeta / 2) := by
    simpa only [Real.rpow_zero, mul_one] using hAbsorbU
  have hLift {x : Real} (hx : U ^ (1 / 2 : Real) ≤ x)
      (hx0 : 0 ≤ x) : K ≤ x ^ zeta := by
    calc
      K ≤ U ^ (zeta / 2) := hK
      _ = (U ^ (1 / 2 : Real)) ^ zeta := by
        have h := Real.rpow_mul hU0 (1 / 2 : Real) zeta
        simpa only [show (1 / 2 : Real) * zeta = zeta / 2 by ring] using h
      _ ≤ x ^ zeta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hU0 _) hx hzeta.le
  have hP : (P : Real) ≤ (P + 1 : Nat) := by
    exact_mod_cast Nat.le_add_right P 1
  have hMainK : 2 * ((P : Real) * C) ≤ K := by
    dsimp only [K]
    gcongr
  exact ⟨hMainK.trans (hLift hBaseMain (by positivity)),
    hLift hBaseNext (by positivity)⟩

#print axioms rpow_one_half_le_of_le_sq
#print axioms eventually_heathBrown_high_finite_loss_le_power
#print axioms eventually_heathBrown_high_cardinality_coefficients

end
end GafniTao
