import GafniTao.HeathBrownSourceLossAbsorption

/-!
# Uniform lower bound for the powered source threshold

This is the quantitative bridge from the detector threshold to the scale
used in Heath--Brown's second- and fourth-moment relation.  It retains both
normalization losses and bounds the finite source power before absorbing its
constant denominator.
-/

open Filter

namespace GafniTao

noncomputable section

/-- The powered threshold is monotone in its nonnegative base threshold. -/
theorem heathBrownPoweredThreshold_mono
    {N p : Nat} {L L' Cp eta : Real}
    (hL : 0 ≤ L) (hLL' : L ≤ L') (hCp : 0 < Cp) (hp : 0 < p) :
    heathBrownPoweredThreshold N p L Cp eta ≤
      heathBrownPoweredThreshold N p L' Cp eta := by
  unfold heathBrownPoweredThreshold
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hPow : L ^ p ≤ L' ^ p := (pow_le_pow_left₀ hL hLL') p
  apply div_le_div_of_nonneg_right _ hpR.le
  exact div_le_div_of_nonneg_right hPow (by positivity)

/-- A fixed positive constant is eventually dominated by any positive
power of the physical height. -/
theorem eventually_const_le_rpow
    {D zeta : Real} (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop, D ≤ U ^ zeta := by
  have hTend : Tendsto (fun U : Real => U ^ zeta) atTop atTop :=
    tendsto_rpow_atTop hzeta
  exact (tendsto_atTop.1 hTend) D

/-- The denominator belonging to any positive source power `p ≤ P` is
bounded by one height-independent constant. -/
theorem powered_normalization_denominator_le
    {Cp eta : Real} {p P : Nat}
    (hCp : 0 ≤ Cp) (heta : 0 ≤ eta) (hp : p ≤ P) :
    Cp * (p : Real) * (2 : Real) ^ ((p : Real) * eta) ≤
      Cp * (P : Real) * (2 : Real) ^ ((P : Real) * eta) := by
  have hpR : (p : Real) ≤ P := by exact_mod_cast hp
  have hExp : (p : Real) * eta ≤ (P : Real) * eta := by gcongr
  have hPow : (2 : Real) ^ ((p : Real) * eta) ≤
      (2 : Real) ^ ((P : Real) * eta) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  gcongr

/-- Exact finite lower bound after both the shell normalization and the
powered-coefficient normalization have been absorbed. -/
theorem heathBrownPoweredThreshold_lower_of_source
    {U sigma eta zetaShell zetaConst Cp : Real} {N p P : Nat}
    (hU : 1 ≤ U) (hN : 0 < N) (hp : 0 < p) (hpP : p ≤ P)
    (heta : 0 < eta) (hzetaShell : 0 ≤ zetaShell)
    (hCp : 0 < Cp)
    (hSource : U ^ (-zetaShell) *
        (N : Real) ^ (sigma - eta) ≤ L)
    (hDenom : Cp * (P : Real) *
        (2 : Real) ^ ((P : Real) * eta) ≤ U ^ zetaConst) :
    U ^ (-(zetaShell * (P : Real) + zetaConst)) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) ≤
      heathBrownPoweredThreshold N p L Cp eta := by
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hBasePos : 0 < U ^ (-zetaShell) *
      (N : Real) ^ (sigma - eta) := by positivity
  have hMono := heathBrownPoweredThreshold_mono (N := N) (eta := eta)
    hBasePos.le hSource hCp hp
  have hExact := heathBrownPoweredThreshold_normalized
    (sigma := sigma) (eta := eta) (c := U ^ (-zetaShell))
    (Cp := Cp) hN hp (by positivity) hCp
  rw [hExact] at hMono
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hPR : (0 : Real) < P := by exact_mod_cast hp.trans_le hpP
  have hDenPos : 0 < Cp * (p : Real) *
      (2 : Real) ^ ((p : Real) * eta) := by positivity
  have hDenMaxPos : 0 < Cp * (P : Real) *
      (2 : Real) ^ ((P : Real) * eta) := by positivity
  have hDenLeMax := powered_normalization_denominator_le
    hCp.le heta.le hpP
  have hDenLeU : Cp * (p : Real) *
      (2 : Real) ^ ((p : Real) * eta) ≤ U ^ zetaConst :=
    hDenLeMax.trans hDenom
  have hUPowConst : 0 < U ^ zetaConst :=
    Real.rpow_pos_of_pos hUPos _
  have hInvDen : U ^ (-zetaConst) ≤
      (Cp * (p : Real) *
        (2 : Real) ^ ((p : Real) * eta))⁻¹ := by
    rw [Real.rpow_neg hUPos.le]
    simpa only [one_div] using one_div_le_one_div_of_le hDenPos hDenLeU
  have hShellPower : U ^ (-(zetaShell * (P : Real))) ≤
      (U ^ (-zetaShell)) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUPos.le]
    exact Real.rpow_le_rpow_of_exponent_le hU
      (by nlinarith [show (p : Real) ≤ P by exact_mod_cast hpP])
  have hCoefficient :
      U ^ (-(zetaShell * (P : Real) + zetaConst)) ≤
        (U ^ (-zetaShell)) ^ p /
          (Cp * (p : Real) *
            (2 : Real) ^ ((p : Real) * eta)) := by
    rw [neg_add, Real.rpow_add hUPos]
    rw [div_eq_mul_inv]
    exact mul_le_mul hShellPower hInvDen
      (Real.rpow_nonneg hUPos.le _) (by positivity)
  have hScaleNonneg : 0 ≤
      ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by positivity
  calc
    U ^ (-(zetaShell * (P : Real) + zetaConst)) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) ≤
      (((U ^ (-zetaShell)) ^ p /
          (Cp * (p : Real) *
            (2 : Real) ^ ((p : Real) * eta))) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta)) :=
      mul_le_mul_of_nonneg_right hCoefficient hScaleNonneg
    _ ≤ heathBrownPoweredThreshold N p L Cp eta := hMono

/-- The source window `U^2 ≤ M^3` converts a height loss into the exact
`3/2` multiple of that loss on the powered polynomial scale. -/
theorem rpow_three_halves_loss_le_of_sq_le_cube
    {U M a : Real} (hU : 0 < U) (hM : 0 < M) (ha : 0 ≤ a)
    (hScale : U ^ (2 : Nat) ≤ M ^ (3 : Nat)) :
    M ^ (-(3 * a / 2)) ≤ U ^ (-a) := by
  have hPower := Real.rpow_le_rpow (pow_nonneg hU.le 2) hScale
    (by positivity : 0 ≤ a / 2)
  have hForward : U ^ a ≤ M ^ (3 * a / 2) := by
    calc
      U ^ a = (U ^ (2 : Nat)) ^ (a / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
        congr 1
        ring
      _ ≤ (M ^ (3 : Nat)) ^ (a / 2) := hPower
      _ = M ^ (3 * a / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
        congr 1
        ring
  rw [Real.rpow_neg hM.le, Real.rpow_neg hU.le]
  simpa only [one_div] using
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hU a) hForward

/-- Powered-threshold lower bound expressed wholly on the selected powered
polynomial scale. -/
theorem heathBrownPoweredThreshold_lower_on_power_scale
    {U sigma eta zetaShell zetaConst Cp L : Real} {N p P : Nat}
    (hU : 1 ≤ U) (hN : 0 < N) (hp : 0 < p) (hpP : p ≤ P)
    (heta : 0 < eta) (hzetaShell : 0 ≤ zetaShell)
    (hzetaConst : 0 ≤ zetaConst) (hCp : 0 < Cp)
    (hSource : U ^ (-zetaShell) *
        (N : Real) ^ (sigma - eta) ≤ L)
    (hDenom : Cp * (P : Real) *
        (2 : Real) ^ ((P : Real) * eta) ≤ U ^ zetaConst)
    (hScale : U ^ (2 : Nat) ≤ ((N ^ p : Nat) : Real) ^ (3 : Nat)) :
    ((N ^ p : Nat) : Real) ^
        (sigma - 2 * eta -
          (3 / 2) * (zetaShell * (P : Real) + zetaConst)) ≤
      heathBrownPoweredThreshold N p L Cp eta := by
  let loss : Real := zetaShell * (P : Real) + zetaConst
  have hLoss : 0 ≤ loss := by
    dsimp only [loss]
    positivity
  have hMPos : (0 : Real) < (N ^ p : Nat) := by positivity
  have hHeightLoss := rpow_three_halves_loss_le_of_sq_le_cube
    (U := U) (M := ((N ^ p : Nat) : Real))
    (a := loss) (zero_lt_one.trans_le hU) hMPos hLoss hScale
  have hPowered := heathBrownPoweredThreshold_lower_of_source
    hU hN hp hpP heta hzetaShell hCp hSource hDenom
  calc
    ((N ^ p : Nat) : Real) ^
        (sigma - 2 * eta - (3 / 2) * loss) =
      ((N ^ p : Nat) : Real) ^ (-loss * (3 / 2)) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by
      rw [← Real.rpow_add hMPos]
      congr 1
      ring
    _ ≤ U ^ (-loss) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by
      gcongr
      have hExponent : -(3 * loss / 2) = -loss * (3 / 2) := by ring
      rw [hExponent] at hHeightLoss
      exact hHeightLoss
    _ ≤ heathBrownPoweredThreshold N p L Cp eta := by
      simpa only [loss] using hPowered

/-- Eventual source form for an actual Type-II detector label.  All shell,
coefficient, powering, and physical-scale losses are present in the single
displayed exponent. -/
theorem eventually_typeII_poweredThreshold_lower_on_power_scale
    {delta eta zetaShell zetaConst C Cp : Real} {P : Nat}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hC : 0 < C) (hCp : 0 < Cp) :
    ∀ᶠ U : Real in atTop,
      ∀ (Y X kI kII : Nat) (sigma q0 : Real)
          (q : Fin (kI * 2 + kII * 2)) (r : Fin (kII * 2))
          (p : Nat),
        1 ≤ U → kII ≤ Nat.clog 2 (Nat.floor (U ^ delta)) →
        0 < kII → binaryScaleLabel q = Sum.inr r →
        0 < classicalBinarySelectedN Y X kI kII q →
        0 < p → p ≤ P →
        U ^ (2 : Nat) ≤
          ((classicalBinarySelectedN Y X kI kII q ^ p : Nat) : Real) ^
            (3 : Nat) →
        ((classicalBinarySelectedN Y X kI kII q ^ p : Nat) : Real) ^
            (sigma - 2 * eta -
              (3 / 2) *
                (zetaShell * (P : Real) + zetaConst)) ≤
          heathBrownPoweredThreshold
            (classicalBinarySelectedN Y X kI kII q) p
            (classicalBinarySelectedThreshold
              Y X kI kII sigma q0 eta C q) Cp eta := by
  have hSource := eventually_typeII_selectedThreshold_lower
    (eta := eta) hdelta hzetaShell hC
  have hDenom := eventually_const_le_rpow
    (D := Cp * (P : Real) * (2 : Real) ^ ((P : Real) * eta))
    hzetaConst
  filter_upwards [hSource, hDenom] with U hSourceU hDenomU
  intro Y X kI kII sigma q0 q r p hU hkII hkIIPos hq hN hp hpP hScale
  have hThreshold := hSourceU Y X kI kII sigma q0 q r
    hkII hkIIPos hq hN
  exact heathBrownPoweredThreshold_lower_on_power_scale
    hU hN hp hpP heta hzetaShell.le hzetaConst.le hCp
    hThreshold hDenomU hScale

#print axioms heathBrownPoweredThreshold_mono
#print axioms eventually_const_le_rpow
#print axioms powered_normalization_denominator_le
#print axioms heathBrownPoweredThreshold_lower_of_source
#print axioms rpow_three_halves_loss_le_of_sq_le_cube
#print axioms heathBrownPoweredThreshold_lower_on_power_scale
#print axioms eventually_typeII_poweredThreshold_lower_on_power_scale

end

end GafniTao
