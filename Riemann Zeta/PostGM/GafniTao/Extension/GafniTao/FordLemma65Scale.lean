import GafniTao.FordLemma34ScaleBridges
import GafniTao.FordPrimePacketEventually

/-!
# Ford Lemma 6.5: the one-step root scale

Ford specializes Lemma 3.2 with `d = 0`, `r = k`, `P = Q`, and
`M = Q^(1/k)`.  This file records the exact real-power identities and the
eventual rounded hypotheses needed by that specialization.  No numerical
prime-packet threshold is assumed: the packet is supplied by the audited PNT.
-/

open Filter
open scoped Topology

namespace GafniTao

noncomputable section

/-- The literal `Q^(1/k)` scale in Ford's proof of Lemma 6.5. -/
def fordLemma65Scale (k : ℕ) (Q : ℝ) : ℝ :=
  Q ^ (1 / (k : ℝ))

theorem fordLemma65Scale_pos
    {k : ℕ} {Q : ℝ} (hQ : 0 < Q) :
    0 < fordLemma65Scale k Q := by
  unfold fordLemma65Scale
  positivity

theorem fordLemma65Scale_pow
    {k : ℕ} {Q : ℝ} (hk : 0 < k) (hQ : 0 ≤ Q) :
    fordLemma65Scale k Q ^ k = Q := by
  rw [← Real.rpow_natCast, fordLemma65Scale, ← Real.rpow_mul hQ]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [one_div, inv_mul_cancel₀ hkR, Real.rpow_one]

theorem fordLemma65Scale_one_le
    {k : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) :
    1 ≤ fordLemma65Scale k Q := by
  unfold fordLemma65Scale
  exact Real.one_le_rpow hQ (by positivity)

theorem fordLemma65_source_scale
    {k : ℕ} {Q : ℝ} (hk : 0 < k) (hQ : 1 ≤ Q) :
    Q ≤ fordLemma65Scale k Q ^ (k + 1) := by
  have hM := fordLemma65Scale_one_le (k := k) hQ
  rw [pow_succ, fordLemma65Scale_pow hk (zero_le_one.trans hQ)]
  exact le_mul_of_one_le_right (zero_le_one.trans hQ) hM

/-- Dividing by the root scale gives the exponent `1-1/k` used in Lemma 6.5. -/
theorem fordLemma65_div_scale
    {k : ℕ} {Q : ℝ} (hQ : 0 < Q) :
    Q / fordLemma65Scale k Q = Q ^ (1 - 1 / (k : ℝ)) := by
  unfold fordLemma65Scale
  rw [div_eq_mul_inv, ← Real.rpow_neg hQ.le]
  nth_rewrite 1 [← Real.rpow_one Q]
  rw [← Real.rpow_add hQ]
  congr 1

theorem fordLemma65_next_scale_one_le
    {k : ℕ} {Q : ℝ} (hk : 2 ≤ k) (hQ : 1 ≤ Q) :
    1 ≤ Q ^ (1 - 1 / (k : ℝ)) := by
  apply Real.one_le_rpow hQ
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by positivity
  rw [sub_nonneg, div_le_one hkPos]
  exact_mod_cast (show 1 ≤ k by omega)

theorem fordLemma65_terminal_power
    {k p : ℕ} {Q : ℝ} (hk : 0 < k) (hQ : 0 < Q)
    (hp : fordLemma65Scale k Q < p) :
    Q < (p : ℝ) ^ k := by
  rw [← fordLemma65Scale_pow hk hQ.le]
  exact pow_lt_pow_left₀ hp (fordLemma65Scale_pos hQ).le (Nat.ne_of_gt hk)

/-- The root scale tends to infinity at natural endpoints. -/
theorem tendsto_fordLemma65Scale_nat_atTop
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun Q : ℕ => fordLemma65Scale k (Q : ℝ)) atTop atTop := by
  exact (tendsto_rpow_atTop (show 0 < 1 / (k : ℝ) by positivity)).comp
    tendsto_natCast_atTop_atTop

/-- Ford's rounded equation-(3.9) box at the one-step root scale. -/
theorem fordLemma65_rounded_box
    {s k Q : ℕ} (hQ : 1 ≤ Q)
    (hMone : 1 ≤ fordLemma65Scale k (Q : ℝ))
    (hnext : 64 * (s : ℝ) ^ 2 + 1 ≤
      (Q : ℝ) ^ (1 - 1 / (k : ℝ))) :
    32 * s ^ 2 * ⌈fordLemma65Scale k (Q : ℝ)⌉₊ < Q := by
  let M := fordLemma65Scale k (Q : ℝ)
  let R := (Q : ℝ) ^ (1 - 1 / (k : ℝ))
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hMpos : 0 < M := fordLemma65Scale_pos hQpos
  have hfactor : M * R = (Q : ℝ) := by
    have hRM : R * M = (Q : ℝ) := (eq_div_iff hMpos.ne').mp (by
      simpa [M, R] using (fordLemma65_div_scale (k := k) hQpos).symm)
    simpa [mul_comm] using hRM
  have hceil : ((⌈M⌉₊ : ℕ) : ℝ) ≤ M + 1 :=
    (Nat.ceil_lt_add_one hMpos.le).le
  have hreal :
      (((32 * s ^ 2 * ⌈M⌉₊ + 1 : ℕ) : ℝ)) ≤ (Q : ℝ) := by
    push_cast
    calc
      32 * (s : ℝ) ^ 2 * (⌈M⌉₊ : ℝ) + 1 ≤
          32 * (s : ℝ) ^ 2 * (M + 1) + 1 := by gcongr
      _ ≤ M * (64 * (s : ℝ) ^ 2 + 1) := by
        nlinarith [sq_nonneg (s : ℝ)]
      _ ≤ M * R := by gcongr
      _ = (Q : ℝ) := hfactor
  have hfloor := ford_floor_Q_box (s := s) (M := M) (Q := (Q : ℝ)) hreal
  simpa [M] using hfloor

/-- All rounded and packet hypotheses needed by the one-step Lemma 3.2
specialization hold for all sufficiently large natural endpoints. -/
theorem eventually_fordLemma65_inputs
    (s k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ Q : ℕ in atTop,
      1 < fordLemma65Scale k (Q : ℝ) ∧
      k ≤ ⌊fordLemma65Scale k (Q : ℝ)⌋₊ ∧
      4 * k ^ 4 < Q ∧
      32 * s ^ 2 * ⌈fordLemma65Scale k (Q : ℝ)⌉₊ < Q ∧
      (∀ p ∈ fordPrimeSet k ⌊fordLemma65Scale k (Q : ℝ)⌋₊,
        p ≤ 2 * ⌈fordLemma65Scale k (Q : ℝ)⌉₊) := by
  have hkpos : 0 < k := by omega
  have hscaleTop := tendsto_fordLemma65Scale_nat_atTop (k := k) hkpos
  have hscaleLarge := hscaleTop.eventually
    (eventually_gt_atTop (max (k : ℝ) 1))
  have hexp : (0 : ℝ) < 1 - 1 / (k : ℝ) := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hkRpos : (0 : ℝ) < k := by positivity
    rw [sub_pos, div_lt_one hkRpos]
    exact_mod_cast (show 1 < k by omega)
  have hnextLarge :=
    ((tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (64 * (s : ℝ) ^ 2 + 1))
  have hQlarge : ∀ᶠ Q : ℕ in atTop, 4 * k ^ 4 < Q :=
    eventually_gt_atTop (4 * k ^ 4)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (eventually_fordPrimeSet_le_two_mul k)
  have hfloorTop : Tendsto
      (fun Q : ℕ => ⌊fordLemma65Scale k (Q : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hscaleTop
  have hpacketScale := hfloorTop.eventually (eventually_ge_atTop M₀)
  filter_upwards [hscaleLarge, hnextLarge, hQlarge, hpacketScale]
    with Q hscale hnext hQlarge hpacketScale
  have hQone : 1 ≤ Q := by omega
  have hMone : 1 ≤ fordLemma65Scale k (Q : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hscale)
  have hkM : (k : ℝ) ≤ fordLemma65Scale k (Q : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hscale)
  refine ⟨lt_of_le_of_lt (le_max_right _ _) hscale,
    ford_nat_le_floor_scale hkM, hQlarge,
    fordLemma65_rounded_box hQone hMone hnext, ?_⟩
  intro p hp
  exact (hM₀ _ hpacketScale p hp).trans
    (Nat.mul_le_mul_left 2 (Nat.floor_le_ceil _))

/-- The stronger real packet estimate used to remove the selected prime from
the final power ledger. -/
theorem eventually_fordLemma65_packet_real
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ Q : ℕ in atTop,
      ∀ p ∈ fordPrimeSet k ⌊fordLemma65Scale k (Q : ℝ)⌋₊,
        (p : ℝ) ≤ 2 * fordLemma65Scale k (Q : ℝ) := by
  have hscaleTop := tendsto_fordLemma65Scale_nat_atTop (k := k) hk
  have hfloorTop : Tendsto
      (fun Q : ℕ => ⌊fordLemma65Scale k (Q : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hscaleTop
  have hpull := hfloorTop.eventually (eventually_fordPrimeSet_le_two_mul k)
  filter_upwards [hpull, eventually_ge_atTop 1] with Q hpacket hQ
  intro p hp
  have hpNat := hpacket p hp
  have hfloor : ((⌊fordLemma65Scale k (Q : ℝ)⌋₊ : ℕ) : ℝ) ≤
      fordLemma65Scale k (Q : ℝ) :=
    Nat.floor_le (fordLemma65Scale_pos
      (by exact_mod_cast (show 0 < Q by omega))).le
  have hpReal : (p : ℝ) ≤ 2 * (⌊fordLemma65Scale k (Q : ℝ)⌋₊ : ℕ) := by
    exact_mod_cast hpNat
  exact hpReal.trans (by gcongr)

#print axioms fordLemma65Scale_pos
#print axioms fordLemma65Scale_pow
#print axioms fordLemma65Scale_one_le
#print axioms fordLemma65_source_scale
#print axioms fordLemma65_div_scale
#print axioms fordLemma65_next_scale_one_le
#print axioms fordLemma65_terminal_power
#print axioms tendsto_fordLemma65Scale_nat_atTop
#print axioms fordLemma65_rounded_box
#print axioms eventually_fordLemma65_inputs
#print axioms eventually_fordLemma65_packet_real

end

end GafniTao
