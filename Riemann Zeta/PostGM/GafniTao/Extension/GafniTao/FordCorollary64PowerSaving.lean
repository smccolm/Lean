import GafniTao.FordCorollary64Real
import GafniTao.FordPowerInterpolation

/-!
# The power-saving form used in Ford Lemma 6.8

This module performs the algebra between Corollary 6.4 and equation (6.6).
It leaves only the row-specific moment coefficient and elementary numerical
inequalities to the Table 6.1 certificates.
-/

namespace GafniTao

noncomputable section

def fordCorollary64Saving (s k : ℕ) (delta : ℝ) : ℝ :=
  (1 - (2 + 2 * delta) / (k + 1 : ℝ)) / (2 * s : ℝ)

def fordCorollary64PowerCoefficient (s k : ℕ) (C : ℝ) : ℝ :=
  4 * (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) ^
      (1 / (2 * s : ℝ)) + 2

theorem fordCorollary64_le_power_saving
    {k n N R : ℕ} {P u t lambda C delta : ℝ}
    (hk : 4 ≤ k) (hn : 1 ≤ n)
    (hN : 1 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (htEq : t = (N : ℝ) ^ lambda)
    (hPscale : P = (N : ℝ) ^ fordCorollary64Mu k lambda)
    (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hmoment : FordVinogradovMomentBound (n * k) k C delta)
    (hcK : fordCorollary64Saving (n * k) k delta ≤ 1 / (k + 1 : ℝ))
    (hcTwo : fordCorollary64Saving (n * k) k delta ≤
      1 - 2 / (k + 1 : ℝ)) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordCorollary64PowerCoefficient (n * k) k C *
        (N : ℝ) ^ (1 - fordCorollary64Saving (n * k) k delta) := by
  let s : ℕ := n * k
  let q : ℝ := 1 / (2 * s : ℝ)
  let e : ℝ := (2 + 2 * delta) / (k + 1 : ℝ)
  let A : ℝ := C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)
  let c : ℝ := fordCorollary64Saving s k delta
  have hs : 1 ≤ s := Nat.mul_pos (Nat.zero_lt_of_lt hn) (by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNe : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hNpos.le _
  have hsource := fordCorollary64_corrected_real_scale
    hk hn hN hRlower hR hu0 hu1 hlower hupper htEq hPscale
      hC hdelta hmoment
  have hcEq : c = q * (1 - e) := by
    dsimp [c, q, e, s, fordCorollary64Saving]
    ring
  have hleadEq :
      4 * (N : ℝ) ^ (1 - q) *
          (A * (N : ℝ) ^ e) ^ q =
        4 * A ^ q * (N : ℝ) ^ (1 - c) := by
    rw [Real.mul_rpow hA hNe]
    calc
      4 * (N : ℝ) ^ (1 - q) *
          (A ^ q * ((N : ℝ) ^ e) ^ q) =
        4 * A ^ q * ((N : ℝ) ^ (1 - q) *
          ((N : ℝ) ^ e) ^ q) := by ring
      _ = 4 * A ^ q * ((N : ℝ) ^ (1 - q) *
          (N : ℝ) ^ (e * q)) := by
        rw [← Real.rpow_mul hNpos.le]
      _ = 4 * A ^ q * (N : ℝ) ^ ((1 - q) + e * q) := by
        rw [Real.rpow_add hNpos]
      _ = 4 * A ^ q * (N : ℝ) ^ (1 - c) := by
        congr 2
        rw [hcEq]
        ring
  have hkDen : (0 : ℝ) < k + 1 := by positivity
  have hkExp : (k : ℝ) / (k + 1 : ℝ) =
      1 - 1 / (k + 1 : ℝ) := by
    field_simp [ne_of_gt hkDen]
    ring
  have hremOne :
      (N : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) ≤
        (N : ℝ) ^ (1 - c) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    rw [hkExp]
    dsimp [c, s] at hcK ⊢
    linarith
  have hremTwo :
      (N : ℝ) ^ (2 / (k + 1 : ℝ)) ≤
        (N : ℝ) ^ (1 - c) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    dsimp [c, s] at hcTwo ⊢
    linarith
  apply hsource.trans
  change
    4 * (N : ℝ) ^ (1 - q) * (A * (N : ℝ) ^ e) ^ q +
          (N : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) +
          (N : ℝ) ^ (2 / (k + 1 : ℝ)) ≤
      fordCorollary64PowerCoefficient s k C * (N : ℝ) ^ (1 - c)
  rw [hleadEq]
  unfold fordCorollary64PowerCoefficient
  dsimp [A, q]
  calc
    4 * A ^ q * (N : ℝ) ^ (1 - c) +
          (N : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) +
          (N : ℝ) ^ (2 / (k + 1 : ℝ)) ≤
      4 * A ^ q * (N : ℝ) ^ (1 - c) +
          (N : ℝ) ^ (1 - c) + (N : ℝ) ^ (1 - c) := by
      gcongr
    _ = (4 * A ^ q + 2) * (N : ℝ) ^ (1 - c) := by ring

/-- Pointwise form of equation (6.6), convenient after a specific row and
endpoint have already been selected. -/
theorem ford_equation_6_6_pointwise
    {X N C c d : ℝ}
    (hN : 1 ≤ N) (hC : 1 ≤ C)
    (hc : 0 < c) (hd : 0 < d) (hdc : d < c)
    (htrivial : X ≤ N) (hstrong : X ≤ C * N ^ (1 - c)) :
    X ≤ C ^ (d / c) * N ^ (1 - d) := by
  let F : ℝ → ℝ := fun x => if x = N then X else 0
  have htrivialAll : ∀ {x : ℝ}, 1 ≤ x → F x ≤ x := by
    intro x hx
    by_cases h : x = N
    · simpa [F, h] using htrivial
    · simp [F, h, hx.trans' zero_le_one]
  have hstrongAll : ∀ {x : ℝ}, 1 ≤ x → F x ≤ C * x ^ (1 - c) := by
    intro x hx
    by_cases h : x = N
    · simpa [F, h] using hstrong
    · have hC0 : 0 ≤ C := zero_le_one.trans hC
      simp [F, h, mul_nonneg hC0 (Real.rpow_nonneg (zero_le_one.trans hx) _)]
  have h := ford_equation_6_6 hC hc hd hdc htrivialAll hstrongAll hN
  simpa [F] using h

theorem fordCorollary64_interpolated
    {k n N R : ℕ} {P u t lambda C delta d : ℝ}
    (hk : 4 ≤ k) (hn : 1 ≤ n)
    (hN : 1 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (htEq : t = (N : ℝ) ^ lambda)
    (hPscale : P = (N : ℝ) ^ fordCorollary64Mu k lambda)
    (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hmoment : FordVinogradovMomentBound (n * k) k C delta)
    (hcPos : 0 < fordCorollary64Saving (n * k) k delta)
    (hdPos : 0 < d) (hdc : d < fordCorollary64Saving (n * k) k delta)
    (hcK : fordCorollary64Saving (n * k) k delta ≤ 1 / (k + 1 : ℝ))
    (hcTwo : fordCorollary64Saving (n * k) k delta ≤
      1 - 2 / (k + 1 : ℝ)) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordCorollary64PowerCoefficient (n * k) k C ^
          (d / fordCorollary64Saving (n * k) k delta) *
        (N : ℝ) ^ (1 - d) := by
  let B := fordCorollary64PowerCoefficient (n * k) k C
  have hB : 1 ≤ B := by
    unfold B fordCorollary64PowerCoefficient
    have : 0 ≤ (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) ^
        (1 / (2 * (n * k : ℕ) : ℝ)) := by positivity
    linarith
  have hstrong := fordCorollary64_le_power_saving hk hn hN
    hRlower hR hu0 hu1 hlower hupper htEq hPscale hC hdelta hmoment
      hcK hcTwo
  have htrivial :
      ‖fordShiftedExponentialSum N R u t‖ ≤ (N : ℝ) :=
    norm_fordShiftedExponentialSum_le_N hR u t
  exact ford_equation_6_6_pointwise (by exact_mod_cast hN)
    hB hcPos hdPos hdc htrivial hstrong

#print axioms fordCorollary64_le_power_saving
#print axioms ford_equation_6_6_pointwise
#print axioms fordCorollary64_interpolated

end

end GafniTao
