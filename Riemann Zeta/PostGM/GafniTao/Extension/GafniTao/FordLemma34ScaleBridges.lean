import GafniTao.FordLemma34Scales

/-!
# Ford Lemma 3.4: floor, ceiling, and packet bridges

These lemmas are the complete rounding ledger needed to feed Ford's real
scales into the exact finite counts.  Every strict natural inequality is
obtained from a displayed real `+1` margin.
-/

namespace GafniTao

noncomputable section

theorem ford_nat_lt_floor_of_succ_le {n : ℕ} {x : ℝ}
    (h : ((n + 1 : ℕ) : ℝ) ≤ x) :
    n < ⌊x⌋₊ := by
  have hle : n + 1 ≤ ⌊x⌋₊ := Nat.le_floor h
  omega

theorem ford_floor_P_large {k : ℕ} {P : ℝ}
    (hP : (((4 * k ^ 4 + 1 : ℕ) : ℝ)) ≤ P) :
    4 * k ^ 4 < ⌊P⌋₊ := by
  exact ford_nat_lt_floor_of_succ_le hP

theorem ford_floor_Q_box {s : ℕ} {M Q : ℝ}
    (hQ : (((32 * s ^ 2 * ⌈M⌉₊ + 1 : ℕ) : ℝ)) ≤ Q) :
    32 * s ^ 2 * ⌈M⌉₊ < ⌊Q⌋₊ := by
  exact ford_nat_lt_floor_of_succ_le hQ

theorem ford_nat_le_floor_scale {n : ℕ} {M : ℝ}
    (h : (n : ℝ) ≤ M) :
    n ≤ ⌊M⌋₊ :=
  Nat.le_floor h

theorem ford_floor_div_prime_le_next_scale
    {Q M Qnext : ℝ} {p : ℕ}
    (hQ : 0 < Q) (hM : 0 < M) (hp : M < p)
    (hscale : Q / M = Qnext) :
    ((⌊Q⌋₊ / p : ℕ) : ℝ) ≤ Qnext := by
  have hpReal : (0 : ℝ) < p := hM.trans hp
  have hfloorQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ.le
  exact (calc
      ((⌊Q⌋₊ / p : ℕ) : ℝ) ≤ (⌊Q⌋₊ : ℝ) / p := Nat.cast_div_le
      _ ≤ Q / p := div_le_div_of_nonneg_right hfloorQ hpReal.le
      _ < Q / M := (div_lt_div_iff₀ hpReal hM).2 (by nlinarith)
      _ = Qnext := hscale).le

/-- A canonical packet contained in Ford's relative interval is contained in
the finite core's upper box `2*ceil M`. -/
theorem fordPrimeSet_upper_box_of_relative
    {k : ℕ} {M delta : ℝ} (hM : 0 ≤ M)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hpacket : ∀ p ∈ fordPrimeSet k ⌊M⌋₊,
      p ≤ fordRelativePrimeBound delta ⌊M⌋₊) :
    ∀ p ∈ fordPrimeSet k ⌊M⌋₊, p ≤ 2 * ⌈M⌉₊ := by
  intro p hp
  have hpBound := hpacket p hp
  have harg : 0 ≤ (1 + delta) * (⌊M⌋₊ : ℝ) := by positivity
  have hfloorBound :
      (fordRelativePrimeBound delta ⌊M⌋₊ : ℝ) ≤
        (1 + delta) * (⌊M⌋₊ : ℝ) := by
    exact Nat.floor_le harg
  have hfloorM : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le hM
  have hceilM : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have hpReal : (p : ℝ) ≤ fordRelativePrimeBound delta ⌊M⌋₊ := by
    exact_mod_cast hpBound
  have htarget : (p : ℝ) ≤ (2 * ⌈M⌉₊ : ℕ) := by
    push_cast
    calc
      (p : ℝ) ≤ fordRelativePrimeBound delta ⌊M⌋₊ := hpReal
      _ ≤ (1 + delta) * (⌊M⌋₊ : ℝ) := hfloorBound
      _ ≤ 2 * M := by nlinarith
      _ ≤ 2 * (⌈M⌉₊ : ℝ) := by linarith
  exact_mod_cast htarget

/-- The lower `phi_i ≥ 1/(k+1)` hypothesis gives the exact real source
scale inequality `P ≤ M_i^(k+1)`. -/
theorem ford_P_le_MScale_pow
    {k r j : ℕ} {delta P : ℝ}
    (hP : 1 ≤ P) (hk : 1 ≤ k)
    (Φ : FordPhiSchedule k r j delta) {i : ℕ}
    (hlower : 1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i) :
    P ≤ (fordMScale P Φ i) ^ (k + 1) := by
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hexp : (1 : ℝ) ≤ Φ.phi i * (k + 1 : ℕ) := by
    have := mul_le_mul_of_nonneg_right hlower (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))
    field_simp at this
    simpa [mul_comm] using this
  calc
    P = P ^ (1 : ℝ) := (Real.rpow_one P).symm
    _ ≤ P ^ (Φ.phi i * (k + 1 : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hP hexp
    _ = (P ^ Φ.phi i) ^ ((k + 1 : ℕ) : ℝ) :=
      Real.rpow_mul (zero_le_one.trans hP) _ _
    _ = (fordMScale P Φ i) ^ (k + 1) := by
      rw [fordMScale, Real.rpow_natCast]

/-- The upper `phi_i≤1/r` hypothesis gives `M_i^r≤P`. -/
theorem ford_MScale_pow_le_P
    {k r j : ℕ} {delta P : ℝ}
    (hP : 1 ≤ P) (hr : 1 ≤ r)
    (Φ : FordPhiSchedule k r j delta) {i : ℕ}
    (hupper : Φ.phi i ≤ 1 / (r : ℝ)) :
    (fordMScale P Φ i) ^ r ≤ P := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hexp : Φ.phi i * (r : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hupper hrR.le
    field_simp at this
    simpa [mul_comm] using this
  rw [fordMScale_rpow_nat (zero_le_one.trans hP)]
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hP hexp

#print axioms ford_nat_lt_floor_of_succ_le
#print axioms ford_floor_Q_box
#print axioms ford_floor_div_prime_le_next_scale
#print axioms fordPrimeSet_upper_box_of_relative
#print axioms ford_P_le_MScale_pow
#print axioms ford_MScale_pow_le_P

end

end GafniTao
