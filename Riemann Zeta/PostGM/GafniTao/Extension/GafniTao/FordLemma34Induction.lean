import GafniTao.FordLemma34Backward
import GafniTao.FordLemma34ScaleBridges

/-! # Ford Lemma 3.4: iteration of equation (3.10) -/

namespace GafniTao

noncomputable section

/-- A packet bounded by the literal real endpoint `(1+omega)M`, with
`omega ≤ 1`, lies in the finite upper box `2 ceil M`. -/
theorem fordPrimeSet_upper_box_of_real_relative
    {k : ℕ} {M omega : ℝ} (hM : 0 ≤ M) (homega : omega ≤ 1)
    (hpacket : ∀ p ∈ fordPrimeSet k ⌊M⌋₊, (p : ℝ) ≤ (1 + omega) * M) :
    ∀ p ∈ fordPrimeSet k ⌊M⌋₊, p ≤ 2 * ⌈M⌉₊ := by
  intro p hp
  have hpR := hpacket p hp
  have hceil : M ≤ (⌈M⌉₊ : ℕ) := Nat.le_ceil M
  have htarget : (p : ℝ) ≤ ((2 * ⌈M⌉₊ : ℕ) : ℝ) := by
    push_cast
    calc
      (p : ℝ) ≤ (1 + omega) * M := hpR
      _ ≤ 2 * M := by nlinarith
      _ ≤ 2 * (⌈M⌉₊ : ℝ) := by gcongr
  exact_mod_cast htarget

/-- The complete decreasing induction proving equation (3.10) at every
index.  Its only analytic scale inputs are the two literal consequences of
Ford equation (3.9): `M_i ≥ k` and the rounded `Q_i` box margin, together
with the canonical packet's relative upper endpoint. -/
theorem ford_equation_3_10_all_indices
    {s k r j : ℕ} {C delta P eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k)
    (hks : k ≤ s)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (hP : 1 ≤ P) (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega)
    (hMlarge : ∀ i, 1 ≤ i → i ≤ j →
      (k : ℝ) ≤ fordMScale P Φ i)
    (hQbox : ∀ i, 1 ≤ i → i < j →
      (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
        fordQScale P Φ i)
    (hpacket : ∀ i, 1 ≤ i → i ≤ j →
      ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ i⌋₊,
        (p : ℝ) ≤ eta * fordMScale P Φ i)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    ∀ J, J ≤ j - 1 →
      FordEquation310Eta s k r j C delta P eta Φ Esch J := by
  have hupper : ∀ i, 1 ≤ i → i ≤ j →
      Φ.phi i ≤ 1 / (r : ℝ) :=
    Φ.le_inv_r (show 1 ≤ k by omega) (show 1 ≤ r by omega)
      hrk hj h38 hlower
  have homega0 : 0 ≤ omega := by
    have hlog : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have : 0 < 1 / (3 * Real.log (k : ℝ)) := by positivity
    linarith
  have heta : 1 ≤ eta := by rw [hetaEq]; linarith
  intro J hJ
  refine Nat.decreasingInduction
    (motive := fun J _ => FordEquation310Eta s k r j C delta P eta Φ Esch J)
    ?_ ?_ hJ
  · intro d hd ih
    have hdj : d + 1 < j := by omega
    have hi : 1 ≤ d + 2 := by omega
    have hij : d + 2 ≤ j := by omega
    have hMreal := hMlarge (d + 2) hi hij
    have hM : 1 < fordMScale P Φ (d + 2) := by
      have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
      exact hkR.trans_le hMreal
    have hkM : k ≤ ⌊fordMScale P Φ (d + 2)⌋₊ :=
      ford_nat_le_floor_scale hMreal
    have hPM : P ≤ (fordMScale P Φ (d + 2)) ^ (k + 1) :=
      ford_P_le_MScale_pow hP (show 1 ≤ k by omega) Φ
        (hlower (d + 2) hi hij)
    have hbox := ford_floor_Q_box (hQbox (d + 1) (by omega) hdj)
    have hpacketBound := hpacket (d + 2) hi hij
    have hpacketTwo := fordPrimeSet_upper_box_of_real_relative
      (zero_le_one.trans hM.le)
      (show omega ≤ 1 by linarith)
      (by simpa [hetaEq] using hpacketBound)
    have hquotient :
        ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
          ((⌊fordQScale P Φ (d + 1)⌋₊ / p : ℕ) : ℝ) ≤
            fordQScale P Φ (d + 2) := by
      intro p hp
      exact ford_floor_div_prime_le_next_scale
        (fordQScale_pos (zero_lt_one.trans_le hP) Φ (d + 1))
        (fordMScale_pos (zero_lt_one.trans_le hP) Φ (d + 2))
        (fordPrimeSet_gt_real hp)
        (fordQScale_div_MScale (zero_lt_one.trans_le hP) Φ (d + 1))
    have hir : 10 * (d + 1) ≤ 9 * r := by omega
    have hQone := fordQScale_one_le_of_ten_index_le_nine_r Φ hP
      (show 1 ≤ r by omega) (show d + 1 ≤ j by omega) hupper hir
    unfold FordEquation310Eta
    intro T Ψ hT hTbound p hp q hq
    exact (ford_equation_3_10_backward Φ Esch hk (show 2 ≤ r by omega)
      hrk hks hdj (by omega) hP hPbig heta homegaLower hetaEq hM hkM hPM
      hbox hpacketTwo hpacketBound hquotient hQone hmoment ih) Ψ hT hTbound p hp q hq
  · dsimp
    have hQj := fordQScale_terminal_one_le Φ hP (show 1 ≤ r by omega)
      hupper hjr
    unfold FordEquation310Eta
    intro T Ψ hT hTbound p hp q hq
    exact (ford_equation_3_10_terminal Φ Esch (show 1 ≤ r by omega)
      hj hP hQj hmoment) Ψ hT hTbound p hp q hq

#print axioms fordPrimeSet_upper_box_of_real_relative
#print axioms ford_equation_3_10_all_indices

end

end GafniTao
