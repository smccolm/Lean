import GafniTao.FordEquation67Real
import GafniTao.FordLemma63Equation69

/-!
# Ford equation (6.9) at a real shift length

The actual polynomial sum ends at `floor P`, but the volume and overlap
combination in (6.9) is monotone as a whole in the real parameter `P`.
Crucially, one must compare `P^kappa * W(P)` rather than `W(P)` alone;
flooring makes the latter larger but the former smaller when `k >= 2`.
-/

namespace GafniTao

noncomputable section

/-- Ford's overlap expression with its literal real shift length. -/
def fordLemma63WReal (N k : ℕ) (P t : ℝ) : ℝ :=
  2 ^ (k + 2) * (N : ℝ) ^ (k + 1) /
      ((k : ℝ) ^ 2 * t * P ^ k) + 1

theorem fordLemma63WReal_natCast (N k M : ℕ) (t : ℝ) :
    fordLemma63WReal N k M t = fordLemma63W N k M t := by
  rfl

theorem ford_k_le_vinogradovKappa {k : ℕ} (hk : 1 ≤ k) :
    k ≤ fordVinogradovKappa k := by
  unfold fordVinogradovKappa
  rw [Nat.le_div_iff_mul_le (by omega)]
  nlinarith

private theorem ford_pow_mul_div_pow_normalize
    {a C : ℝ} {k K : ℕ} (ha : 0 < a) (hkK : k ≤ K) :
    a ^ K * (C / a ^ k + 1) = C * a ^ (K - k) + a ^ K := by
  have hsum : K - k + k = K := Nat.sub_add_cancel hkK
  field_simp [ne_of_gt ha]
  have hp : a ^ K = a ^ (K - k) * a ^ k := by
    rw [← pow_add, hsum]
  rw [hp]
  ring

/-- The combined volume-overlap factor in equation (6.9) is monotone in the
real cutoff.  This is the exact bridge that prevents any floor loss in
Corollary 6.4. -/
theorem fordLemma63_volume_overlap_mono
    {N k : ℕ} {Q : ℕ} {P t : ℝ}
    (hk : 2 ≤ k) (hQ : 1 ≤ Q) (hQP : (Q : ℝ) ≤ P) (ht : 0 < t) :
    (Q : ℝ) ^ fordVinogradovKappa k * fordLemma63W N k Q t ≤
      P ^ fordVinogradovKappa k * fordLemma63WReal N k P t := by
  let K := fordVinogradovKappa k
  let C : ℝ :=
    2 ^ (k + 2) * (N : ℝ) ^ (k + 1) / ((k : ℝ) ^ 2 * t)
  have hkK : k ≤ K := by
    dsimp [K]
    exact ford_k_le_vinogradovKappa (by omega)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hPpos : 0 < P := hQpos.trans_le hQP
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpowSmall : (Q : ℝ) ^ (K - k) ≤ P ^ (K - k) :=
    pow_le_pow_left₀ hQpos.le hQP _
  have hpowLarge : (Q : ℝ) ^ K ≤ P ^ K :=
    pow_le_pow_left₀ hQpos.le hQP _
  have hleft :
      (Q : ℝ) ^ K * fordLemma63W N k Q t =
        C * (Q : ℝ) ^ (K - k) + (Q : ℝ) ^ K := by
    rw [show fordLemma63W N k Q t = C / (Q : ℝ) ^ k + 1 by
      unfold fordLemma63W
      dsimp [C]
      field_simp]
    exact ford_pow_mul_div_pow_normalize hQpos hkK
  have hright :
      P ^ K * fordLemma63WReal N k P t =
        C * P ^ (K - k) + P ^ K := by
    rw [show fordLemma63WReal N k P t = C / P ^ k + 1 by
      unfold fordLemma63WReal
      dsimp [C]
      field_simp]
    exact ford_pow_mul_div_pow_normalize hPpos hkK
  rw [hleft, hright]
  exact add_le_add (mul_le_mul_of_nonneg_left hpowSmall hC) hpowLarge

/-- Equation (6.9) with the source's real cutoff convention.  The moment is
the actual count at `floor P`; only the displayed scale factors are real. -/
theorem ford_equation_6_9_real_cutoff
    {s k N : ℕ} {P u t : ℝ}
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hP : 1 ≤ P) (hPN : P ≤ N)
    (hN : 1 ≤ N) (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    (hscale : t * P ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    fordLemma63Moment ⌊P⌋₊ N u t s ≤
      ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          P ^ fordVinogradovKappa k) *
        fordLemma63WReal N k P t) *
        ((2 : ℝ) ^ (4 * s) * (fordVinogradovMoment s k P : ℝ)) := by
  let Q : ℕ := ⌊P⌋₊
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.floor_pos.mpr hP
  have hQP : (Q : ℝ) ≤ P := by
    dsimp [Q]
    exact Nat.floor_le hPpos.le
  have hQNreal : (Q : ℝ) ≤ N := hQP.trans hPN
  have hQN : Q ≤ N := by exact_mod_cast hQNreal
  have hQscale :
      t * (Q : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1) := by
    have hpow : (Q : ℝ) ^ (k + 1) ≤ P ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) hQP _
    exact (mul_le_mul_of_nonneg_left hpow ht.le).trans hscale
  have h69 := ford_equation_6_9
    (s := s) (k := k) (M := Q) (N := N) (u := u) (t := t)
    hs hk hQ hN hu0 hu1 ht htN hQscale
  let A : ℝ := Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hvol := fordLemma63_volume_overlap_mono
    (N := N) (k := k) (Q := Q) (P := P) hk hQ hQP ht
  have hDW :
      (A * (Q : ℝ) ^ fordVinogradovKappa k) *
          fordLemma63W N k Q t ≤
        (A * P ^ fordVinogradovKappa k) *
          fordLemma63WReal N k P t := by
    calc
      (A * (Q : ℝ) ^ fordVinogradovKappa k) *
          fordLemma63W N k Q t =
        A * ((Q : ℝ) ^ fordVinogradovKappa k *
          fordLemma63W N k Q t) := by ring
      _ ≤ A * (P ^ fordVinogradovKappa k *
          fordLemma63WReal N k P t) :=
        mul_le_mul_of_nonneg_left hvol hA
      _ = (A * P ^ fordVinogradovKappa k) *
          fordLemma63WReal N k P t := by ring
  have htail :
      0 ≤ (2 : ℝ) ^ (4 * s) * (fordVinogradovMoment s k P : ℝ) := by
    positivity
  apply h69.trans
  dsimp [A, Q] at hDW ⊢
  exact mul_le_mul_of_nonneg_right hDW htail

#print axioms fordLemma63_volume_overlap_mono
#print axioms ford_equation_6_9_real_cutoff

end

end GafniTao
