import GafniTao.FordCorollary64RealRoot
import GafniTao.FordCorollary64Remainder

/-!
# Ford Corollary 6.4 at the source's real power scale

This removes the artificial integrality condition from the earlier bridge.
The last displayed remainder is the exponent proved by Ford's argument,
`N^(2/(k+1))`; the raw TeX prints `N^(1/(k+1))` at that one location.
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_corrected_real_scale
    {k n N R : ℕ} {P u t lambda C delta : ℝ}
    (hk : 4 ≤ k) (hn : 1 ≤ n)
    (hN : 1 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (htEq : t = (N : ℝ) ^ lambda)
    (hPscale : P = (N : ℝ) ^ fordCorollary64Mu k lambda)
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
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmuBounds := fordCorollary64Mu_bounds hlower hupper
  have hP : 1 ≤ P := by
    rw [hPscale]
    exact Real.one_le_rpow hNreal
      ((by positivity : (0 : ℝ) ≤ 1 / (k + 1 : ℝ)).trans hmuBounds.1)
  have hmuOne : fordCorollary64Mu k lambda ≤ 1 := by
    have hden : (0 : ℝ) < k + 1 := by positivity
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    exact hmuBounds.2.trans (by
      rw [div_le_one hden]
      nlinarith)
  have hPN : P ≤ N := by
    rw [hPscale]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hNreal hmuOne)
  have ht : 0 < t := by rw [htEq]; positivity
  have htN : t ≤ (N : ℝ) ^ k := by
    rw [htEq]
    exact fordCorollary64_height_le_degree hNreal hupper
  have hscaleEq : t * P ^ (k + 1) = (N : ℝ) ^ (k + 1) := by
    rw [htEq, hPscale]
    exact fordCorollary64_height_mul_scale hNpos
  have hW : fordLemma63WReal N k P t ≤ (2 : ℝ) ^ k * P :=
    fordLemma63WReal_le_source_scale hk hP ht hscaleEq
  have h63 := fordLemma63_real_cutoff
    (s := n * k) (k := k) (N := N) (R := R)
    (P := P) (u := u) (t := t)
    hs (by omega) hP hPN hN hRlower hR hu0 hu1 ht htN hscaleEq.le
  have hroot := fordCorollary64_real_root_factor_le
    (s := n * k) (k := k) (N := N) (P := P) (t := t)
    hs hP hN ht hC hdelta hlower hupper hPscale hW hmoment
  let X : ℝ :=
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        P ^ fordVinogradovKappa k) *
      fordLemma63WReal N k P t *
      (fordVinogradovMoment (n * k) k P : ℝ)
  let Y : ℝ :=
    (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
      (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))
  have hlead :
      4 * ((N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) / P) *
          X ^ (1 / (2 * (n * k : ℕ) : ℝ)) ≤
        4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          Y ^ (1 / (2 * (n * k : ℕ) : ℝ)) := by
    calc
      4 * ((N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) / P) *
          X ^ (1 / (2 * (n * k : ℕ) : ℝ)) =
        4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          ((1 / P) * X ^ (1 / (2 * (n * k : ℕ) : ℝ))) := by ring
      _ ≤ 4 * (N : ℝ) ^ (1 - 1 / (2 * (n * k : ℕ) : ℝ)) *
          Y ^ (1 / (2 * (n * k : ℕ) : ℝ)) := by
        gcongr
  have hrem := fordCorollary64_remainders_le_corrected
    (k := k) (N := (N : ℝ)) (M := P)
    hNreal hlower hupper hPscale
  dsimp [X, Y] at hlead
  exact h63.trans (by linarith)

#print axioms fordCorollary64_corrected_real_scale

end

end GafniTao
