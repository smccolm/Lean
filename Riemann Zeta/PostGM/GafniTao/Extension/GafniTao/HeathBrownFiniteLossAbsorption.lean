import GafniTao.HeathBrownActualLogarithmicRelation

/-!
# Absorption of the finite powered-energy loss

The selected source power is bounded by a fixed `P`.  This makes the colour
count and defect window fixed.  The only growing analytic loss is `B^epsilon`.
The source inequality `U^2 <= (N^p)^3` supplies the exact lower scale
`U^(2/3) <= N^p`, leaving the strict margin `epsilon < 2*zeta/3`.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_const_mul_rpow_le_rpow
    {D a b : Real} (hab : a < b) :
    ∀ᶠ U : Real in atTop, D * U ^ a <= U ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hTend : Tendsto (fun U : Real => U ^ (b - a)) atTop atTop :=
    tendsto_rpow_atTop hgap
  have hEventually : ∀ᶠ U : Real in atTop, D <= U ^ (b - a) :=
    (tendsto_atTop.1 hTend) D
  filter_upwards [hEventually, eventually_gt_atTop (0 : Real)] with U hU hUpos
  calc
    D * U ^ a <= U ^ (b - a) * U ^ a :=
      mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hUpos.le _)
    _ = U ^ b := by
      rw [<- Real.rpow_add hUpos]
      congr 1
      ring

/-- Cubing is inverted exactly on nonnegative reals in the source scale
comparison. -/
theorem rpow_two_thirds_le_of_sq_le_cube
    {U y : Real} (hU : 0 <= U) (hy : 0 <= y)
    (hScale : U ^ 2 <= y ^ 3) :
    U ^ (2 / 3 : Real) <= y := by
  have hRoot := Real.rpow_le_rpow (sq_nonneg U) hScale
    (by norm_num : (0 : Real) <= 1 / 3)
  have hLeft : (U ^ 2) ^ (1 / 3 : Real) = U ^ (2 / 3 : Real) := by
    have hTwo : U ^ (2 : Nat) = U ^ (2 : Real) :=
      (Real.rpow_natCast U 2).symm
    calc
      (U ^ 2) ^ (1 / 3 : Real) =
          (U ^ (2 : Real)) ^ (1 / 3 : Real) := by
            rw [hTwo]
      _ = U ^ ((2 : Real) * (1 / 3 : Real)) :=
        (Real.rpow_mul hU 2 (1 / 3 : Real)).symm
      _ = U ^ (2 / 3 : Real) := by
        apply congrArg (fun a : Real => U ^ a)
        ring
  have hRight : (y ^ 3) ^ (1 / 3 : Real) = y := by
    have hThree : y ^ (3 : Nat) = y ^ (3 : Real) :=
      (Real.rpow_natCast y 3).symm
    calc
      (y ^ 3) ^ (1 / 3 : Real) =
          (y ^ (3 : Real)) ^ (1 / 3 : Real) := by
            rw [hThree]
      _ = y ^ ((3 : Real) * (1 / 3 : Real)) :=
        (Real.rpow_mul hy 3 (1 / 3 : Real)).symm
      _ = y := by norm_num
  simpa only [hLeft, hRight] using hRoot

/-- Uniform absorption of every finite factor in the actual powered-energy
output.  Constants may depend on `P`, `epsilon`, and the analytic moment
constants, but not on `U`, `N`, or the selected `p <= P`. -/
theorem eventually_heathBrown_finite_loss_le_power
    {P : Nat} {epsilon zeta C0 C2 C4 : Real}
    (hzeta : 0 < zeta)
    (hmargin : epsilon < (2 / 3 : Real) * zeta)
    (hC0 : 0 <= C0) :
    ∀ᶠ U : Real in atTop,
      ∀ (N p : Nat), 0 < N → 0 < p → p <= P →
        U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3 →
        (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
            (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
            (((2 ^ P : Real) * U) ^ epsilon) <=
          (((2 ^ p * N ^ p : Nat) : Real) ^ zeta) := by
  let K : Real :=
    (((P ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
      (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
      ((2 ^ P : Real) ^ epsilon)
  have hSmall := eventually_const_mul_rpow_le_rpow (D := K) hmargin
  filter_upwards [hSmall, eventually_ge_atTop (1 : Real)] with U hSmallU hU
  intro N p hN hp hpP hScale
  have hU0 : 0 <= U := zero_le_one.trans hU
  have hNpNat : 0 < N ^ p := pow_pos hN p
  have hNp0 : (0 : Real) <= ((N ^ p : Nat) : Real) := Nat.cast_nonneg _
  have hLower : U ^ (2 / 3 : Real) <= ((N ^ p : Nat) : Real) :=
    rpow_two_thirds_le_of_sq_le_cube hU0 hNp0 hScale
  have hBase : ((N ^ p : Nat) : Real) <=
      ((2 ^ p * N ^ p : Nat) : Real) := by
    exact_mod_cast Nat.le_mul_of_pos_left (N ^ p) (pow_pos (by omega) p)
  have hPower : U ^ ((2 / 3 : Real) * zeta) <=
      ((2 ^ p * N ^ p : Nat) : Real) ^ zeta := by
    calc
      U ^ ((2 / 3 : Real) * zeta) =
          (U ^ (2 / 3 : Real)) ^ zeta :=
        Real.rpow_mul hU0 (2 / 3 : Real) zeta
      _ <= ((N ^ p : Nat) : Real) ^ zeta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hU0 _)
          hLower hzeta.le
      _ <= ((2 ^ p * N ^ p : Nat) : Real) ^ zeta :=
        Real.rpow_le_rpow hNp0 hBase hzeta.le
  have hp4 : (p ^ 4 : Nat) <= P ^ 4 :=
    Nat.pow_le_pow_left hpP 4
  have hp4Real : ((p ^ 4 : Nat) : Real) <= (P ^ 4 : Nat) := by
    exact_mod_cast hp4
  have hFixed :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          ((2 ^ P : Real) ^ epsilon) <= K := by
    dsimp only [K]
    gcongr
  calc
    (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        (((2 ^ P : Real) * U) ^ epsilon) =
      ((((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        ((2 ^ P : Real) ^ epsilon)) * U ^ epsilon := by
          rw [Real.mul_rpow (by positivity : 0 <= (2 ^ P : Real)) hU0]
          ring
    _ <= K * U ^ epsilon :=
      mul_le_mul_of_nonneg_right hFixed (Real.rpow_nonneg hU0 _)
    _ <= U ^ ((2 / 3 : Real) * zeta) := hSmallU
    _ <= ((2 ^ p * N ^ p : Nat) : Real) ^ zeta := hPower

#print axioms eventually_const_mul_rpow_le_rpow
#print axioms rpow_two_thirds_le_of_sq_le_cube
#print axioms eventually_heathBrown_finite_loss_le_power

end

end GafniTao
