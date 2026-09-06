import GafniTao.HeathBrownSourceScale
import GafniTao.HeathBrownPoweredEnergy

/-!
# Exact source-threshold normalization for the Heath--Brown branch

The Type-II alternative initially carries the normalization used by the
sharp-mollifier detector.  This file rewrites that literal quotient into a
constant times the expected power `N ^ (sigma - eta)`.  Keeping the equality
exact avoids hiding the coefficient, dyadic, or mollifier losses when the
finite cardinality estimates are converted to logarithmic exponents.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A Type-II label selects exactly its sharp-mollifier block length. -/
theorem classicalBinarySelectedN_typeII_eq
    {Y X kI kII : Nat} {q : Fin (kI * 2 + kII * 2)}
    {r : Fin (kII * 2)} (hq : binaryScaleLabel q = Sum.inr r) :
    classicalBinarySelectedN Y X kI kII q =
      classicalTypeIIShellScaleN X r := by
  unfold classicalBinarySelectedN
  rw [hq]
  rfl

/-- Literal Type-II branch of the selected normalized threshold. -/
theorem classicalBinarySelectedThreshold_typeII_eq
    {Y X kI kII : Nat} {sigma q0 eta C : Real}
    {q : Fin (kI * 2 + kII * 2)} {r : Fin (kII * 2)}
    (hq : binaryScaleLabel q = Sum.inr r) :
    classicalBinarySelectedThreshold Y X kI kII sigma q0 eta C q =
      ((3 / 4 : Real) * (3 / 4) / (kII : Real)) /
        (C * (2 * classicalTypeIIShellScaleN X r : Real) ^ eta *
          (classicalTypeIIShellScaleN X r : Real) ^ (-sigma)) := by
  unfold classicalBinarySelectedThreshold
  rw [hq]
  rfl

/-- Exact algebraic normalization of the Type-II threshold. -/
theorem classicalBinarySelectedThreshold_typeII_normalized
    {Y X kI kII : Nat} {sigma q0 eta C : Real}
    {q : Fin (kI * 2 + kII * 2)} {r : Fin (kII * 2)}
    (hq : binaryScaleLabel q = Sum.inr r)
    (hN : 0 < classicalTypeIIShellScaleN X r)
    (hkII : 0 < kII) (hC : 0 < C) :
    classicalBinarySelectedThreshold Y X kI kII sigma q0 eta C q =
      (9 / (16 * (kII : Real) * C * (2 : Real) ^ eta)) *
        (classicalTypeIIShellScaleN X r : Real) ^ (sigma - eta) := by
  rw [classicalBinarySelectedThreshold_typeII_eq hq]
  have hNR : (0 : Real) < classicalTypeIIShellScaleN X r := by
    exact_mod_cast hN
  have hkR : (0 : Real) < kII := by exact_mod_cast hkII
  rw [show (2 * classicalTypeIIShellScaleN X r : Real) ^ eta =
      (2 : Real) ^ eta *
        (classicalTypeIIShellScaleN X r : Real) ^ eta by
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hNR.le]]
  rw [Real.rpow_neg hNR.le, Real.rpow_sub hNR]
  field_simp [hkR.ne', hC.ne', Real.rpow_ne_zero (by norm_num : (0 : Real) <= 2)]
  ring

/-- Branch-independent form of the preceding equality, with the selected
length itself on the right. -/
theorem classicalBinarySelectedThreshold_typeII_selected_normalized
    {Y X kI kII : Nat} {sigma q0 eta C : Real}
    {q : Fin (kI * 2 + kII * 2)} {r : Fin (kII * 2)}
    (hq : binaryScaleLabel q = Sum.inr r)
    (hN : 0 < classicalBinarySelectedN Y X kI kII q)
    (hkII : 0 < kII) (hC : 0 < C) :
    classicalBinarySelectedThreshold Y X kI kII sigma q0 eta C q =
      (9 / (16 * (kII : Real) * C * (2 : Real) ^ eta)) *
        (classicalBinarySelectedN Y X kI kII q : Real) ^
          (sigma - eta) := by
  have hEq := classicalBinarySelectedN_typeII_eq
    (Y := Y) (X := X) hq
  have hN' : 0 < classicalTypeIIShellScaleN X r := by
    simpa [hEq] using hN
  rw [hEq]
  exact classicalBinarySelectedThreshold_typeII_normalized
    hq hN' hkII hC

/-- Exact second normalization after positive-sign powering.  The original
Type-II normalization costs `eta`, and normalization of the powered
coefficients costs a second `eta`; hence the physical exponent is
`sigma - 2 * eta`. -/
theorem heathBrownPoweredThreshold_normalized
    {N p : Nat} {sigma eta c Cp : Real}
    (hN : 0 < N) (hp : 0 < p) (hc : c ≠ 0) (hCp : 0 < Cp) :
    heathBrownPoweredThreshold N p
        (c * (N : Real) ^ (sigma - eta)) Cp eta =
      (c ^ p /
          (Cp * (p : Real) * (2 : Real) ^ ((p : Real) * eta))) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hNpR : (0 : Real) < (N ^ p : Nat) := by positivity
  unfold heathBrownPoweredThreshold
  rw [mul_pow]
  have hPowScale : ((N : Real) ^ (sigma - eta)) ^ p =
      ((N ^ p : Nat) : Real) ^ (sigma - eta) := by
    calc
      ((N : Real) ^ (sigma - eta)) ^ p =
          ((N : Real) ^ (sigma - eta)) ^ (p : Real) := by
            rw [Real.rpow_natCast]
      _ = (N : Real) ^ ((sigma - eta) * (p : Real)) := by
            rw [Real.rpow_mul hNR.le]
      _ = (N : Real) ^ ((p : Real) * (sigma - eta)) := by
            congr 1
            ring
      _ = ((N : Real) ^ (p : Real)) ^ (sigma - eta) := by
            rw [Real.rpow_mul hNR.le]
      _ = ((N ^ p : Nat) : Real) ^ (sigma - eta) := by
            rw [Real.rpow_natCast]
            norm_num
  rw [hPowScale]
  have hDyadicCast : ((2 ^ p * N ^ p : Nat) : Real) =
      (2 : Real) ^ p * ((N ^ p : Nat) : Real) := by
    norm_num
  rw [hDyadicCast, Real.mul_rpow (by positivity) hNpR.le]
  have hTwoPow : ((2 : Real) ^ p) ^ eta =
      (2 : Real) ^ ((p : Real) * eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  rw [hTwoPow, Real.rpow_sub hNpR]
  have hExponent : sigma - 2 * eta = (sigma - eta) - eta := by ring
  rw [hExponent, Real.rpow_sub hNpR]
  field_simp [hc, hCp.ne', hpR.ne',
    Real.rpow_ne_zero (by norm_num : (0 : Real) <= 2),
    Real.rpow_ne_zero hNpR.le]
  rw [← Real.rpow_add hNpR]
  congr 1
  ring

#print axioms classicalBinarySelectedN_typeII_eq
#print axioms classicalBinarySelectedThreshold_typeII_eq
#print axioms classicalBinarySelectedThreshold_typeII_normalized
#print axioms classicalBinarySelectedThreshold_typeII_selected_normalized
#print axioms heathBrownPoweredThreshold_normalized

end

end GafniTao
