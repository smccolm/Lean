import GafniTao.HeathBrownFiniteLossAbsorption

/-!
# The actual relation at the common source base

The analytic height is `B = 2^P U`.  Choosing the common base
`x = 2^P N^p` makes every selected powered length at most `x` and preserves
the exact source inequality `B^2 <= x^3`.  Thus the crucial upper bound
`tau <= 3/2` is obtained without an asymptotic dilation error.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem heathBrownLogExponent_one_le
    {x y : Real} (hx : 1 < x) (hxy : x <= y) :
    1 <= heathBrownLogExponent x y := by
  have hy : 0 < y := (zero_lt_one.trans hx).trans_le hxy
  have hpow : x ^ (1 : Real) <=
      x ^ heathBrownLogExponent x y := by
    rw [Real.rpow_one, rpow_heathBrownLogExponent hx hy]
    exact hxy
  exact (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp hpow

theorem heathBrownLogExponent_le_three_halves
    {x y : Real} (hx : 1 < x) (hy : 0 < y)
    (hScale : y ^ 2 <= x ^ 3) :
    heathBrownLogExponent x y <= 3 / 2 := by
  let tau := heathBrownLogExponent x y
  have hyPower : x ^ tau = y := rpow_heathBrownLogExponent hx hy
  have hx0 : 0 <= x := (zero_lt_one.trans hx).le
  have hPower : x ^ (2 * tau) <= x ^ (3 : Real) := by
    calc
      x ^ (2 * tau) = (x ^ tau) ^ (2 : Nat) := by
        calc
          x ^ (2 * tau) = x ^ (tau * 2) := by ring_nf
          _ = (x ^ tau) ^ (2 : Nat) :=
            Real.rpow_mul_natCast hx0 tau 2
      _ = y ^ 2 := by rw [hyPower]
      _ <= x ^ 3 := hScale
      _ = x ^ (3 : Real) := (Real.rpow_natCast x 3).symm
  have hExponent : 2 * tau <= 3 :=
    (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp hPower
  dsimp only [tau] at hExponent
  linarith

/-- The source physical window gives the exact common logarithmic interval
`1 <= tau <= 3/2`. -/
theorem heathBrown_common_logarithmic_scale
    {U : Real} {N p P : Nat}
    (hU : 0 < U) (hN : 0 < N) (hp : 0 < p) (hpP : p <= P)
    (hBase : ((N ^ p : Nat) : Real) <= U)
    (hCube : U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3) :
    let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
    let B : Real := (2 ^ P : Real) * U
    1 < x /\
      1 <= heathBrownLogExponent x B /\
      heathBrownLogExponent x B <= 3 / 2 := by
  dsimp only
  have hPpos : 0 < P := lt_of_lt_of_le hp hpP
  have hDOne : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
  have hNpPosNat : 0 < N ^ p := pow_pos hN p
  have hxStrict : 1 < ((2 ^ P * N ^ p : Nat) : Real) := by
    have hTwo : 2 <= 2 ^ P := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ <= 2 ^ P := Nat.pow_le_pow_right (by omega) hPpos
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      nlinarith [Nat.le_mul_of_pos_right (2 ^ P) hNpPosNat])
  have hLower : ((2 ^ P * N ^ p : Nat) : Real) <= (2 ^ P : Real) * U := by
    calc
      ((2 ^ P * N ^ p : Nat) : Real) =
          ((2 ^ P : Nat) : Real) * ((N ^ p : Nat) : Real) := by norm_num
      _ <= ((2 ^ P : Nat) : Real) * U :=
        mul_le_mul_of_nonneg_left hBase (by positivity)
      _ = (2 ^ P : Real) * U := by norm_num
  have hBpos : 0 < (2 ^ P : Real) * U := by positivity
  have hTauLower := heathBrownLogExponent_one_le hxStrict hLower
  have hScale : ((2 ^ P : Real) * U) ^ 2 <=
      ((2 ^ P * N ^ p : Nat) : Real) ^ 3 := by
    have hDsqCube : ((2 ^ P : Real)) ^ 2 <= ((2 ^ P : Real)) ^ 3 :=
      pow_le_pow_right₀ hDOne (by omega)
    calc
      ((2 ^ P : Real) * U) ^ 2 =
          ((2 ^ P : Real)) ^ 2 * U ^ 2 := by ring
      _ <= ((2 ^ P : Real)) ^ 3 *
          (((N ^ p : Nat) : Real) ^ 3) :=
        mul_le_mul hDsqCube hCube (sq_nonneg U)
          (pow_nonneg (by positivity) 3)
      _ = ((2 ^ P * N ^ p : Nat) : Real) ^ 3 := by
        norm_num
        ring
  exact ⟨hxStrict, hTauLower,
    heathBrownLogExponent_le_three_halves hxStrict hBpos hScale⟩

/-- Actual powered-energy relation at `x = 2^P N^p`. -/
theorem HeathBrownFullyUniformOutputs.logarithmic_relation_common
    {epsilon B R eta L zeta : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat -> Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hN : 0 < N) (hp : 0 < p) (hpP : p <= P) (hL : 0 < L)
    (hB : 0 < B) (hC0 : 0 <= C0) (hC2 : 0 <= C2) (hC4 : 0 <= C4)
    (hW : W.Nonempty)
    (hLoss :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon <=
        (((2 ^ P * N ^ p : Nat) : Real) ^ zeta)) :
    let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
    let V := heathBrownPoweredThreshold N p L Cp eta
    let E : Real := (ApproxAddEnergy 1 W : Real)
    let sigma := heathBrownLogExponent x V
    let tau := heathBrownLogExponent x B
    let rho := heathBrownLogExponent x (W.card : Real)
    let rhoStar := heathBrownLogExponent x E
    rhoStar <= zeta +
      (1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2))) := by
  dsimp only
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let E : Real := (ApproxAddEnergy 1 W : Real)
  let F : Real := ((p ^ 4 : Nat) : Real) *
    (doubleFloorDefectWindow 1).card
  have hNp : 0 < N ^ p := pow_pos hN p
  have hD : 2 ^ p <= 2 ^ P := Nat.pow_le_pow_right (by omega) hpP
  have hxNat : 1 < 2 ^ P * N ^ p := by
    have hPpos : 0 < P := lt_of_lt_of_le hp hpP
    have hTwo : 2 <= 2 ^ P := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ <= 2 ^ P := Nat.pow_le_pow_right (by omega) hPpos
    nlinarith [Nat.le_mul_of_pos_right (2 ^ P) hNp]
  have hx : 1 < x := by dsimp only [x]; exact_mod_cast hxNat
  have hV : 0 < V := by
    dsimp only [V]
    unfold heathBrownPoweredThreshold
    have hpReal : (0 : Real) < p := by exact_mod_cast hp
    have hCpEnergy := full.energy.hCp
    rw [full.energy_Cp] at hCpEnergy
    positivity
  have hCard : 0 < W.card := Finset.card_pos.mpr hW
  have hEnergyNat : W.card ^ 2 <= ApproxAddEnergy 1 W :=
    card_sq_le_approxAddEnergy (by norm_num) W
  have hE : 0 < E := by
    dsimp only [E]
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCard 2) hEnergyNat)
  have hRaw := full.energy.energy_le_common_power hC0 hC2 hC4 hB.le
  have hFamily : E <= F *
      heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V
        (2 ^ p * N ^ p) W := by
    dsimp only [E, F, V]
    calc
      (ApproxAddEnergy 1 W : Real) =
          (1 / 4 : Real) * (4 * (ApproxAddEnergy 1 W : Real)) := by ring
      _ <= (1 / 4 : Real) *
          ((((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
            (4 * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L full.energy.Cp eta)
              (2 ^ p * N ^ p) W)) := by gcongr
      _ = (((p ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card) *
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L full.energy.Cp eta)
              (2 ^ p * N ^ p) W := by ring
      _ = (((p ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card) *
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L Cp eta)
              (2 ^ p * N ^ p) W := by rw [full.energy_Cp]
  have hM : (((2 ^ p * N ^ p : Nat) : Real)) <= x := by
    dsimp only [x]
    exact_mod_cast Nat.mul_le_mul_right (N ^ p) hD
  have hResult := heathBrown_logarithmic_relation_of_family_bound
    (x := x) (L := F) (E := E) (zeta := zeta)
    hx hB hV (by positivity) hE hCard hC0 hC2 hC4 hM rfl hFamily
    (by simpa only [F, x] using hLoss)
  simpa only [x, V, E] using hResult

#print axioms heathBrownLogExponent_one_le
#print axioms heathBrownLogExponent_le_three_halves
#print axioms heathBrown_common_logarithmic_scale
#print axioms HeathBrownFullyUniformOutputs.logarithmic_relation_common

end

end GafniTao
