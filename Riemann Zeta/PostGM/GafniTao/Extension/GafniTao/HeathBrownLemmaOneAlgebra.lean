import GafniTao.HeathBrownLemmaOneReal

/-!
# Cancellation of the Heath-Brown averaging volume

This file performs the exact algebraic cancellation in the normalized
Lemma 1 estimate.  In particular, the two half-powers of the block length
coming from the VMVT term and the reciprocal coefficient-cell volume cancel
the averaging denominator, leaving only the deliberately allocated epsilon
power of `H`.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownLemmaOneNormalizedRealBound
    (N k : ℕ) (A lambda epsilon C : ℝ) : ℝ :=
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let D := (2 : ℝ) ^ (k - 1)
  let r := 1 / (2 * (s : ℝ))
  let P := heathBrownLemmaTwoConstant k A *
    (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
    (1 + Real.log N)
  (1 + 2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1)) * H) *
      (1 + 2 * Real.pi * ((k : ℝ) ^ 2 / H) * H) *
      (C ^ r * P ^ r * (N : ℝ) ^ (1 - 1 / (s : ℝ)) *
        D ^ (-r) * (H : ℝ) ^ (epsilon * r)) +
    H

theorem heathBrown_normalization_algebra
    {H S D C P X epsilon a b : ℝ}
    (hH : 0 < H) (hS : 0 < S) (hD : 0 < D)
    (hC : 0 < C) (hP : 0 < P) (hX : 0 < X) :
    let r := 1 / (2 * S)
    let q := 1 - 1 / S
    let V := D * H ^ (-S)
    (a * b *
          ((C * H ^ (S + epsilon)) ^ r *
            (P * V) ^ r * (X * V) ^ q) +
        V * H ^ 2) / (V * H) =
      a * b *
          (C ^ r * P ^ r * X ^ q * D ^ (-r) * H ^ (epsilon * r)) +
        H := by
  dsimp only
  let r : ℝ := 1 / (2 * S)
  let q : ℝ := 1 - 1 / S
  let V : ℝ := D * H ^ (-S)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hr : r = 1 / (2 * S) := rfl
  have hq : q = 1 - 1 / S := rfl
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hH.le _),
    ← Real.rpow_mul hH.le,
    Real.mul_rpow hP.le hV.le,
    Real.mul_rpow hX.le hV.le]
  change
    (a * b *
          ((C ^ r * H ^ ((S + epsilon) * r)) *
            (P ^ r * V ^ r) * (X ^ q * V ^ q)) +
        V * H ^ 2) / (V * H) =
      a * b *
          (C ^ r * P ^ r * X ^ q * D ^ (-r) * H ^ (epsilon * r)) + H
  dsimp only [V]
  repeat' rw [Real.mul_rpow hD.le (Real.rpow_nonneg hH.le _)]
  repeat' rw [← Real.rpow_mul hH.le]
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero hD.ne'
    (Real.rpow_pos_of_pos hH _).ne') hH.ne')]
  have hS0 : S ≠ 0 := hS.ne'
  have hTwoS0 : 2 * S ≠ 0 := by positivity
  have hDexp : r + q = 1 - r := by
    dsimp only [r, q]
    field_simp [hS0, hTwoS0]
    ring
  have hHexp :
      (S + epsilon) * r + (-S) * r + (-S) * q =
        epsilon * r + (-S) + 1 := by
    dsimp only [r, q]
    field_simp [hS0, hTwoS0]
    ring
  have hmain :
      (C ^ r * H ^ ((S + epsilon) * r)) *
          (P ^ r * (D ^ r * H ^ ((-S) * r))) *
          (X ^ q * (D ^ q * H ^ ((-S) * q))) =
        C ^ r * P ^ r * X ^ q * D ^ (-r) * H ^ (epsilon * r) *
          (D * H ^ (-S)) * H := by
    calc
      _ = C ^ r * P ^ r * X ^ q *
          (D ^ r * D ^ q) *
          (H ^ ((S + epsilon) * r) * H ^ ((-S) * r) *
            H ^ ((-S) * q)) := by ring
      _ = C ^ r * P ^ r * X ^ q *
          D ^ (r + q) *
          H ^ ((S + epsilon) * r + (-S) * r + (-S) * q) := by
        rw [Real.rpow_add hD, Real.rpow_add hH, Real.rpow_add hH]
      _ = C ^ r * P ^ r * X ^ q *
          D ^ (1 - r) * H ^ (epsilon * r + (-S) + 1) := by
        rw [hDexp, hHexp]
      _ = _ := by
        rw [show 1 - r = -r + 1 by ring,
          Real.rpow_add hD, Real.rpow_one,
          Real.rpow_add hH, Real.rpow_add hH, Real.rpow_one]
        ring
  rw [hmain]
  ring

theorem heathBrownLemmaOneExpanded_eq_normalized
    {N k : ℕ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) (hC : 0 < C) :
    heathBrownLemmaOneExpandedRealBound N k A lambda epsilon C =
      heathBrownLemmaOneNormalizedRealBound N k A lambda epsilon C := by
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let D := (2 : ℝ) ^ (k - 1)
  let r := 1 / (2 * (s : ℝ))
  let P := heathBrownLemmaTwoConstant k A *
    (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
    (1 + Real.log N)
  have hHnat : 0 < H := heathBrownHChoice_pos (by omega) hA hlambda hsmall
  have hH : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hsNat : 0 < s := by
    dsimp only [s, heathBrownCriticalMoment]
    have hprod : 2 ≤ k * (k - 1) := by
      calc
        2 = 2 * 1 := by omega
        _ ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos hprod (by omega)
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hD : 0 < D := by dsimp only [D]; positivity
  have hP : 0 < P := by
    dsimp only [P]
    exact heathBrownLemmaOne_source_P_pos hN hA hlambda
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold heathBrownLemmaOneExpandedRealBound
    heathBrownLemmaOneNormalizedRealBound
  dsimp only
  have hHpow : (H : ℝ) ^ s = (H : ℝ) ^ (s : ℝ) := by
    exact (Real.rpow_natCast (H : ℝ) s).symm
  rw [hHpow]
  rw [← Real.rpow_neg hH.le]
  exact heathBrown_normalization_algebra hH hs hD hC hP hNreal

#print axioms heathBrownLemmaOneExpanded_eq_normalized
#print axioms heathBrown_normalization_algebra

end

end GafniTao
