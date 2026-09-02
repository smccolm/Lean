import GafniTao.FordCorollary64Remainder

/-!
# Ford Corollary 6.4

This module assembles the exact result supplied by Lemma 6.3 at an integral
power scale.  The final remainder is the exponent actually implied by the
proof, `N^(2/(k+1))`; the raw source prints `N^(1/(k+1))` there.  The separate
nonintegral-cutoff bridge remains an explicit obligation.
-/

namespace GafniTao

noncomputable section

/-- Ford Corollary 6.4 with the source proof's correct final remainder, under
the explicit condition that the selected power scale is integral.  The upper
bound `n <= k^2` is faithfully retained although the corollary's deduction
does not use it once the moment hypothesis is supplied. -/
theorem fordCorollary64_corrected_integral_scale
    {k n M N R : ℕ} {u t lambda C delta : ℝ}
    (hk : 4 ≤ k) (hn : 1 ≤ n) (_hnUpper : n ≤ k ^ 2)
    (hN : 1 ≤ N) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (htEq : t = (N : ℝ) ^ lambda)
    (hMscale : (M : ℝ) =
      (N : ℝ) ^ fordCorollary64Mu k lambda)
    (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hmoment : FordVinogradovMomentBound (n * k) k C delta) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
        ((C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
          (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))) ^
            (1 / (2 * (n * k : ℕ) : ℝ)) +
        (N : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) +
        (N : ℝ) ^ (2 / (k + 1 : ℝ)) := by
  have hs : 1 ≤ n * k := Nat.mul_pos (Nat.zero_lt_of_lt hn) (by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  have hmuBounds := fordCorollary64Mu_bounds hlower hupper
  have hMreal : (1 : ℝ) ≤ M := by
    rw [hMscale]
    have hmu0 : 0 ≤ fordCorollary64Mu k lambda :=
      (by positivity : (0 : ℝ) ≤ 1 / (k + 1 : ℝ)).trans hmuBounds.1
    exact Real.one_le_rpow hNreal hmu0
  have hM : 1 ≤ M := by exact_mod_cast hMreal
  have hmuOne : fordCorollary64Mu k lambda ≤ 1 := by
    have hden : (0 : ℝ) < k + 1 := by positivity
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    exact hmuBounds.2.trans (by
      rw [div_le_one hden]
      nlinarith)
  have hMNreal : (M : ℝ) ≤ N := by
    rw [hMscale]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hNreal hmuOne)
  have hMN : M ≤ N := by exact_mod_cast hMNreal
  have ht : 0 < t := by rw [htEq]; positivity
  have htN : t ≤ (N : ℝ) ^ k := by
    rw [htEq]
    exact fordCorollary64_height_le_degree hNreal hupper
  have hscaleEq :
      t * (M : ℝ) ^ (k + 1) = (N : ℝ) ^ (k + 1) := by
    rw [htEq, hMscale]
    exact fordCorollary64_height_mul_scale hNpos
  have hW : fordLemma63W N k M t ≤ (2 : ℝ) ^ k * M :=
    fordLemma63W_le_source_scale hk hM ht hscaleEq
  have h63 := fordLemma63_native
    (s := n * k) (k := k) (M := M) (N := N) (R := R)
    (u := u) (t := t) hs (by omega) hM hMN hN hR hu0 hu1 ht
      htN hscaleEq.le
  have hroot := fordCorollary64_root_factor_le
    (s := n * k) (k := k) (M := M) (N := N)
    hs hM hN ht hC hdelta hlower hupper hMscale hW hmoment
  let X : ℝ :=
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k) *
      fordLemma63W N k M t *
      (fordVinogradovMomentNat (n * k) k M : ℝ)
  let Y : ℝ :=
    (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
      (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))
  have hlead :
      4 * ((N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) / M) *
          X ^ (1 / (2 * (n * k : ℕ) : ℝ)) ≤
        4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          Y ^ (1 / (2 * (n * k : ℕ) : ℝ)) := by
    calc
      4 * ((N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) / M) *
          X ^ (1 / (2 * (n * k : ℕ) : ℝ)) =
        4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          ((1 / (M : ℝ)) *
            X ^ (1 / (2 * (n * k : ℕ) : ℝ))) := by ring
      _ ≤ 4 * (N : ℝ) ^
          (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          Y ^ (1 / (2 * (n * k : ℕ) : ℝ)) := by
        gcongr
  have hrem := fordCorollary64_remainders_le_corrected
    (k := k) (N := (N : ℝ)) (M := (M : ℝ))
    hNreal hlower hupper hMscale
  dsimp [X, Y] at hlead
  exact h63.trans (by linarith)

#print axioms fordCorollary64_corrected_integral_scale

end

end GafniTao
