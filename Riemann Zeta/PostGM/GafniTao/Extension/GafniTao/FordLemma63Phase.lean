import GafniTao.FordEquation67
import GafniTao.FordTaylorPhase

/-!
# Ford Lemma 6.3: phase box and derivative

This is the literal phase `delta(w; beta)` and the rectangular neighborhood
`Omega_n` from equation (6.8).  The final theorem proves the source bound
`|delta'| <= 1/(pi*M)` from the physical scale inequality.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordLemma63Radius (k M : ℕ) (j : Fin k) : ℝ :=
  1 / (2 * Real.pi * ((j : ℕ) + 1) * k * (M : ℝ) ^ ((j : ℕ) + 1))

def fordLemma63Omega
    (k M n : ℕ) (u t : ℝ) : Set (Fin k → ℝ) :=
  {β | ∀ j, |β j - fordTaylorGamma t ((n : ℝ) + u) j| ≤
    fordLemma63Radius k M j}

def fordLemma63Delta
    (k n : ℕ) (u t : ℝ) (β : Fin k → ℝ) (w : ℝ) : ℝ :=
  -t / (2 * Real.pi) * Real.log (1 + w / ((n : ℝ) + u)) -
    ∑ j : Fin k, β j * w ^ ((j : ℕ) + 1)

def fordLemma63DeltaDeriv
    (k n : ℕ) (u t : ℝ) (β : Fin k → ℝ) (w : ℝ) : ℝ :=
  -t / (2 * Real.pi * ((n : ℝ) + u + w)) -
    ∑ j : Fin k, β j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)

theorem hasDerivAt_fordLemma63Delta
    {k n : ℕ} {u t : ℝ} {β : Fin k → ℝ} {w : ℝ}
    (hz : (n : ℝ) + u ≠ 0) (hlog : 1 + w / ((n : ℝ) + u) ≠ 0) :
    HasDerivAt (fordLemma63Delta k n u t β)
      (fordLemma63DeltaDeriv k n u t β w) w := by
  unfold fordLemma63Delta fordLemma63DeltaDeriv
  have hinner : HasDerivAt
      (fun x : ℝ => 1 + x / ((n : ℝ) + u))
      (1 / ((n : ℝ) + u)) w := by
    simpa using
      ((hasDerivAt_id w).div_const ((n : ℝ) + u)).const_add (1 : ℝ)
  have hlogDeriv := hinner.log hlog
  have hmain := HasDerivAt.const_mul (-t / (2 * Real.pi)) hlogDeriv
  have hterm (j : Fin k) : HasDerivAt
      (fun x : ℝ => β j * x ^ ((j : ℕ) + 1))
      (β j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)) w := by
    simpa [mul_assoc] using
      HasDerivAt.const_mul (β j) ((hasDerivAt_id w).pow ((j : ℕ) + 1))
  have hpoly : HasDerivAt
      (fun x : ℝ => ∑ j : Fin k, β j * x ^ ((j : ℕ) + 1))
      (∑ j : Fin k, β j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)) w :=
    HasDerivAt.fun_sum fun j hj => hterm j
  convert hmain.sub hpoly using 1
  all_goals field_simp [hz, hlog, Real.pi_ne_zero]

/-- Exact finite geometric remainder for the derivative of `log(1+x)`. -/
theorem ford_geometric_derivative_remainder
    (k : ℕ) {x : ℝ} (hx : 1 + x ≠ 0) :
    1 / (1 + x) - ∑ j ∈ Finset.range k, (-x) ^ j =
      (-x) ^ k / (1 + x) := by
  have hgeom := geom_sum_mul (-x) k
  field_simp [hx]
  nlinarith [hgeom]

/-- The derivative of the Taylor polynomial has Ford's exact geometric-sum
normalization. -/
theorem fordTaylorGamma_derivative_sum
    {k : ℕ} {t z w : ℝ} (hz : z ≠ 0) :
    (∑ j : Fin k,
      fordTaylorGamma t z j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)) =
      -t / (2 * Real.pi * z) *
        ∑ j ∈ Finset.range k, (-(w / z)) ^ j := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => fordTaylorGamma t z j * ((j + 1 : ℕ) : ℝ) * w ^ j) k]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold fordTaylorGamma
  have hjpos : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hzpow : z ^ (j + 1) ≠ 0 := pow_ne_zero _ hz
  rw [show (-(w / z)) ^ j = (-1 : ℝ) ^ j * w ^ j / z ^ j by
    rw [neg_pow, div_pow]
    ring]
  rw [show (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) by
    rw [pow_succ]
    ring]
  rw [pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [Real.pi_ne_zero, hjpos, hzpow, hz]

/-- The exact derivative remainder after inserting Ford's Taylor
coefficients. -/
theorem fordLemma63_exact_derivative_remainder
    {k : ℕ} {t z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) :
    -t / (2 * Real.pi * (z + w)) -
        (∑ j : Fin k,
          fordTaylorGamma t z j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)) =
      -t / (2 * Real.pi * z) *
        ((-(w / z)) ^ k / (1 + w / z)) := by
  rw [fordTaylorGamma_derivative_sum hz.ne']
  have hden : 1 + w / z ≠ 0 := by positivity
  have hzw : z + w = z * (1 + w / z) := by field_simp
  have hgeom := ford_geometric_derivative_remainder k hden
  have hbase :
      1 / (z + w) - 1 / z * (∑ j ∈ Finset.range k, (-(w / z)) ^ j) =
        1 / z * ((-(w / z)) ^ k / (1 + w / z)) := by
    calc
      1 / (z + w) - 1 / z * (∑ j ∈ Finset.range k, (-(w / z)) ^ j) =
          1 / z * (1 / (1 + w / z) -
            ∑ j ∈ Finset.range k, (-(w / z)) ^ j) := by
        rw [hzw]
        field_simp [hz.ne', hden]
      _ = _ := by rw [hgeom]
  calc
    -t / (2 * Real.pi * (z + w)) -
        -t / (2 * Real.pi * z) *
          (∑ j ∈ Finset.range k, (-(w / z)) ^ j) =
      -t / (2 * Real.pi) *
        (1 / (z + w) - 1 / z *
          (∑ j ∈ Finset.range k, (-(w / z)) ^ j)) := by
        field_simp [Real.pi_ne_zero, hz.ne', (add_pos_of_pos_of_nonneg hz hw).ne']
        ring
    _ = -t / (2 * Real.pi) *
        (1 / z * ((-(w / z)) ^ k / (1 + w / z))) := by rw [hbase]
    _ = _ := by
      field_simp [Real.pi_ne_zero, hz.ne', hden]

/-- The Taylor derivative remainder is bounded by the first term on the
right of Ford (6.8). -/
theorem abs_fordLemma63_exact_derivative_remainder_le
    {k : ℕ} {t z w M N : ℝ}
    (ht : 0 ≤ t) (hzN : N ≤ z) (hN : 0 < N)
    (hw : w ∈ Set.Icc (0 : ℝ) M) :
    |-t / (2 * Real.pi * (z + w)) -
        (∑ j : Fin k,
          fordTaylorGamma t z j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ))| ≤
      t * M ^ k / (2 * Real.pi * N ^ (k + 1)) := by
  have hz : 0 < z := hN.trans_le hzN
  rw [fordLemma63_exact_derivative_remainder hz hw.1]
  have hwz : 0 ≤ w / z := div_nonneg hw.1 hz.le
  have hzw : 0 < 1 + w / z := by linarith
  simp only [abs_mul, abs_div, abs_pow, abs_neg]
  rw [abs_of_nonneg ht, abs_of_pos Real.pi_pos, abs_of_nonneg hw.1,
    abs_of_pos hz, abs_of_pos hzw]
  norm_num
  have hdenOne : 1 ≤ 1 + w / z := by linarith
  have hM0 : 0 ≤ M := hw.1.trans hw.2
  have hratio : w / z ≤ M / N := by
    apply (div_le_div_iff₀ hz hN).2
    exact mul_le_mul hw.2 hzN hN.le hM0
  have hpow : (w / z) ^ k ≤ (M / N) ^ k := by
    exact pow_le_pow_left₀ hwz hratio k
  have hdiv : (w / z) ^ k / (1 + w / z) ≤ (M / N) ^ k := by
    exact (div_le_self (pow_nonneg hwz k) hdenOne).trans hpow
  have hfactor : 0 ≤ t / (2 * Real.pi * z) := by positivity
  calc
    t / (2 * Real.pi * z) * ((w / z) ^ k / (1 + w / z)) ≤
        t / (2 * Real.pi * z) * (M / N) ^ k :=
      mul_le_mul_of_nonneg_left hdiv hfactor
    _ ≤ t / (2 * Real.pi * N) * (M / N) ^ k := by
      have hinv : 1 / z ≤ 1 / N := one_div_le_one_div_of_le hN hzN
      have hcoeff : t / (2 * Real.pi * z) ≤ t / (2 * Real.pi * N) := by
        calc
          t / (2 * Real.pi * z) = t / (2 * Real.pi) * (1 / z) := by ring
          _ ≤ t / (2 * Real.pi) * (1 / N) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = t / (2 * Real.pi * N) := by ring
      exact mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (div_nonneg hM0 hN.le) _)
    _ = t * M ^ k / (2 * Real.pi * N ^ (k + 1)) := by
      rw [div_pow, pow_succ]
      field_simp [hN.ne', Real.pi_ne_zero]

/-- The contribution from moving `beta` inside `Omega_n`. -/
theorem abs_fordLemma63_beta_derivative_error_le
    {k M : ℕ} {n : ℕ} {u t w : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hw : w ∈ Set.Icc (0 : ℝ) M)
    (hβ : β ∈ fordLemma63Omega k M n u t) :
    |∑ j : Fin k,
        (fordTaylorGamma t ((n : ℝ) + u) j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)| ≤
      1 / (2 * Real.pi * M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  change ‖∑ j : Fin k,
        (fordTaylorGamma t ((n : ℝ) + u) j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)‖ ≤ _
  calc
    ‖∑ j : Fin k,
        (fordTaylorGamma t ((n : ℝ) + u) j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)‖ ≤
      ∑ j : Fin k,
        ‖(fordTaylorGamma t ((n : ℝ) + u) j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, 1 / (2 * Real.pi * k * M) := by
      apply Finset.sum_le_sum
      intro j hj
      have hbox := hβ j
      rw [abs_sub_comm] at hbox
      simp only [Real.norm_eq_abs, abs_mul, abs_pow]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℕ) + 1 : ℕ)),
        abs_of_nonneg hw.1]
      have hwpow : w ^ (j : ℕ) ≤ (M : ℝ) ^ (j : ℕ) :=
        pow_le_pow_left₀ hw.1 hw.2 _
      have hrad :
          fordLemma63Radius k M j * (((j : ℕ) + 1 : ℕ) : ℝ) *
              (M : ℝ) ^ (j : ℕ) =
            1 / (2 * Real.pi * k * M) := by
        unfold fordLemma63Radius
        have hj : (((j : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hkR : (k : ℝ) ≠ 0 := by positivity
        simp only [Nat.cast_add, Nat.cast_one]
        rw [pow_succ]
        field_simp [Real.pi_ne_zero, hj, hkR, hMpos.ne']
      have hradNonneg : 0 ≤ fordLemma63Radius k M j := by
        unfold fordLemma63Radius
        positivity
      have hdegNonneg : (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
      calc
        |fordTaylorGamma t ((n : ℝ) + u) j - β j| *
            (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ) ≤
          fordLemma63Radius k M j * (((j : ℕ) + 1 : ℕ) : ℝ) *
            w ^ (j : ℕ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hbox hdegNonneg)
                (pow_nonneg hw.1 _)
        _ ≤
          fordLemma63Radius k M j * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (M : ℝ) ^ (j : ℕ) :=
              mul_le_mul_of_nonneg_left hwpow (mul_nonneg hradNonneg hdegNonneg)
        _ = _ := hrad
    _ = 1 / (2 * Real.pi * M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero, hkR, hMpos.ne']

/-- Ford's equation (6.8), after imposing the source scale inequality
`t*M^(k+1) <= N^(k+1)`. -/
theorem abs_fordLemma63DeltaDeriv_le
    {k M N n : ℕ} {u t w : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hw : w ∈ Set.Icc (0 : ℝ) M)
    (hβ : β ∈ fordLemma63Omega k M n u t) :
    |fordLemma63DeltaDeriv k n u t β w| ≤ 1 / (Real.pi * M) := by
  let z : ℝ := (n : ℝ) + u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hzN : (N : ℝ) ≤ z := by
    dsimp [z]
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hrem := abs_fordLemma63_exact_derivative_remainder_le
    (k := k) (t := t) (z := z) (w := w) (M := M) (N := N)
    ht hzN hNpos hw
  have hbeta := abs_fordLemma63_beta_derivative_error_le
    (k := k) (M := M) (n := n) (u := u) (t := t) hk hM hw hβ
  have hfirst :
      t * (M : ℝ) ^ k / (2 * Real.pi * (N : ℝ) ^ (k + 1)) ≤
        1 / (2 * Real.pi * M) := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hcore : t * (M : ℝ) ^ k ≤ (N : ℝ) ^ (k + 1) / M := by
      apply (le_div_iff₀ hMpos).2
      rw [mul_assoc, ← pow_succ]
      exact hscale
    calc
      t * (M : ℝ) ^ k / (2 * Real.pi * (N : ℝ) ^ (k + 1)) ≤
          ((N : ℝ) ^ (k + 1) / M) /
            (2 * Real.pi * (N : ℝ) ^ (k + 1)) := by gcongr
      _ = 1 / (2 * Real.pi * M) := by
        have hNpow : (N : ℝ) ^ (k + 1) ≠ 0 := (pow_pos hNpos _).ne'
        field_simp [hNpow, hMpos.ne', Real.pi_ne_zero]
  unfold fordLemma63DeltaDeriv
  change
    |-t / (2 * Real.pi * (z + w)) -
      ∑ j : Fin k, β j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)| ≤ _
  have hsplit :
      -t / (2 * Real.pi * (z + w)) -
          ∑ j : Fin k, β j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ) =
        (-t / (2 * Real.pi * (z + w)) -
          ∑ j : Fin k, fordTaylorGamma t z j *
            (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)) +
        ∑ j : Fin k, (fordTaylorGamma t z j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc
    |_ + _| ≤
        |-t / (2 * Real.pi * (z + w)) -
          ∑ j : Fin k, fordTaylorGamma t z j *
            (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)| +
        |∑ j : Fin k, (fordTaylorGamma t z j - β j) *
          (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)| := abs_add_le _ _
    _ ≤ 1 / (2 * Real.pi * M) + 1 / (2 * Real.pi * M) := by
      exact add_le_add (hrem.trans hfirst) hbeta
    _ = 1 / (Real.pi * M) := by ring

#print axioms hasDerivAt_fordLemma63Delta
#print axioms ford_geometric_derivative_remainder
#print axioms fordLemma63_exact_derivative_remainder
#print axioms abs_fordLemma63DeltaDeriv_le

end

end GafniTao
