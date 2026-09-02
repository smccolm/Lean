import GafniTao.FordLemma34Induction
import GafniTao.FordPrimePacketEventually

/-!
# Ford Lemma 3.4: eventual source data

The pinned Rosser--Schoenfeld checkout contains admitted explicit prime-counting
bounds, so it cannot justify Ford's printed numerical threshold `V`.  The
Gafni--Tao application only needs the large-parameter form.  This file derives
that form from the independently audited PNT, while retaining Ford's literal
scales, canonical prime packets, and rounded equation-(3.9) box.
-/

open Filter
open scoped Topology

namespace GafniTao

noncomputable section

/-- The lower bound `phi_i >= 1/(k+1)` gives a single lower scale valid at
every active index. -/
theorem fordMScale_ge_uniform_base
    {k r j i : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta) (hP : 1 ≤ P)
    (hlower : 1 / (((k + 1 : ℕ) : ℝ)) ≤ Φ.phi i) :
    P ^ (1 / (((k + 1 : ℕ) : ℝ))) ≤ fordMScale P Φ i := by
  exact Real.rpow_le_rpow_of_exponent_le hP hlower

/-- The strip restriction leaves at least one tenth of the original exponent
in every `Q_i` used by the backwards induction. -/
theorem fordQScale_ge_tenth_power
    {k r j i : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta) (hP : 1 ≤ P) (hr : 1 ≤ r)
    (hi : i ≤ j)
    (hupper : ∀ n, 1 ≤ n → n ≤ j → Φ.phi n ≤ 1 / (r : ℝ))
    (hir : 10 * i ≤ 9 * r) :
    P ^ (1 / 10 : ℝ) ≤ fordQScale P Φ i := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hprefix := fordPhiPrefix_le_index_div_r Φ hupper hi
  have hirR : (10 : ℝ) * i ≤ 9 * r := by exact_mod_cast hir
  have hratio : (i : ℝ) / r ≤ 9 / 10 := by
    rw [div_le_iff₀ hrR]
    nlinarith
  have hexp : (1 / 10 : ℝ) ≤ 1 - fordPhiPrefix Φ i := by
    linarith
  exact Real.rpow_le_rpow_of_exponent_le hP hexp

/-- A large uniform `M` base and a large one-tenth `Q` base imply the exact
rounded box required by the finite Lemma 3.2 consumer. -/
theorem ford_equation_3_9_rounded
    {s k r j i : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta) (hP : 1 ≤ P) (hr : 1 ≤ r)
    (hi : i + 1 ≤ j)
    (hupper : ∀ n, 1 ≤ n → n ≤ j → Φ.phi n ≤ 1 / (r : ℝ))
    (hir : 10 * (i + 1) ≤ 9 * r)
    (hMone : 1 ≤ fordMScale P Φ (i + 1))
    (hQlarge : (64 * (s : ℝ) ^ 2 + 1) ≤ P ^ (1 / 10 : ℝ)) :
    (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
      fordQScale P Φ i := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hM0 : 0 ≤ fordMScale P Φ (i + 1) :=
    (fordMScale_pos hP0 Φ (i + 1)).le
  have hQnext : (64 * (s : ℝ) ^ 2 + 1) ≤ fordQScale P Φ (i + 1) :=
    hQlarge.trans (fordQScale_ge_tenth_power Φ hP hr hi hupper hir)
  have hceil : ((⌈fordMScale P Φ (i + 1)⌉₊ : ℕ) : ℝ) ≤
      fordMScale P Φ (i + 1) + 1 :=
    (Nat.ceil_lt_add_one hM0).le
  rw [fordQScale_eq_MScale_mul_succ hP0 Φ i]
  push_cast
  calc
    32 * (s : ℝ) ^ 2 * (⌈fordMScale P Φ (i + 1)⌉₊ : ℝ) + 1 ≤
        32 * (s : ℝ) ^ 2 * (fordMScale P Φ (i + 1) + 1) + 1 := by
      gcongr
    _ ≤ fordMScale P Φ (i + 1) * (64 * (s : ℝ) ^ 2 + 1) := by
      nlinarith [sq_nonneg (s : ℝ)]
    _ ≤ fordMScale P Φ (i + 1) * fordQScale P Φ (i + 1) := by
      gcongr

/-- The two uniform powers used in the eventual version of Ford's equation
(3.9) tend to infinity. -/
theorem eventually_ford_lemma_3_4_uniform_powers
    (s k : ℕ) :
    ∀ᶠ P : ℝ in atTop,
      (k : ℝ) ≤ P ^ (1 / (((k + 1 : ℕ) : ℝ))) ∧
      (64 * (s : ℝ) ^ 2 + 1) ≤ P ^ (1 / 10 : ℝ) ∧
      4 * k ^ 4 < ⌊P⌋₊ := by
  have hkexp : 0 < (1 / (((k + 1 : ℕ) : ℝ))) := by positivity
  have hten : (0 : ℝ) < 1 / 10 := by norm_num
  have hkTop := (tendsto_rpow_atTop hkexp).eventually (eventually_ge_atTop (k : ℝ))
  have hsTop := (tendsto_rpow_atTop hten).eventually
    (eventually_ge_atTop (64 * (s : ℝ) ^ 2 + 1))
  have hfloor : ∀ᶠ P : ℝ in atTop, 4 * k ^ 4 < ⌊P⌋₊ := by
    filter_upwards [eventually_gt_atTop ((4 * k ^ 4 + 1 : ℕ) : ℝ)] with P hP
    have hP0 : (0 : ℝ) ≤ P := by
      exact (Nat.cast_nonneg (4 * k ^ 4 + 1)).trans (le_of_lt hP)
    have hle : 4 * k ^ 4 + 1 ≤ ⌊P⌋₊ :=
      (Nat.le_floor_iff hP0).2 (le_of_lt hP)
    omega
  filter_upwards [hkTop, hsTop, hfloor] with P hk hs hf
  exact ⟨hk, hs, hf⟩

/-- All physical hypotheses of the equation-(3.10) induction hold eventually
in `P`.  The packet statement uses the canonical first `k^3` primes above the
literal floored `M_i`; no arbitrary packet is inserted. -/
theorem eventually_ford_equation_3_10_inputs
    {s k r j : ℕ} {delta eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (hetaEq : eta = 1 + omega) :
    ∀ᶠ P : ℝ in atTop,
      1 ≤ P ∧
      4 * k ^ 4 < ⌊P⌋₊ ∧
      (∀ i, 1 ≤ i → i ≤ j → (k : ℝ) ≤ fordMScale P Φ i) ∧
      (∀ i, i < j →
        (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
          fordQScale P Φ i) ∧
      (∀ i, 1 ≤ i → i ≤ j →
        ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ i⌋₊,
          (p : ℝ) ≤ eta * fordMScale P Φ i) := by
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have homega0 : 0 < omega :=
    (show 0 < 1 / (3 * Real.log (k : ℝ)) by positivity).trans_le homegaLower
  have hupper : ∀ i, 1 ≤ i → i ≤ j → Φ.phi i ≤ 1 / (r : ℝ) :=
    Φ.le_inv_r (show 1 ≤ k by omega) (show 1 ≤ r by omega)
      hrk hj h38 hlower
  obtain ⟨M₀, hM₀⟩ := exists_fordPrimeSet_relative_threshold k homega0
  have hbaseM₀ := (tendsto_rpow_atTop
    (show 0 < 1 / (((k + 1 : ℕ) : ℝ)) by positivity)).eventually
      (eventually_ge_atTop (M₀ : ℝ))
  have hpowers := eventually_ford_lemma_3_4_uniform_powers s k
  filter_upwards [eventually_ge_atTop (1 : ℝ), hbaseM₀, hpowers]
    with P hP hbaseM₀ hpowers
  rcases hpowers with ⟨hbaseK, hbaseQ, hPfloor⟩
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hMlarge : ∀ i, 1 ≤ i → i ≤ j →
      (k : ℝ) ≤ fordMScale P Φ i := by
    intro i hi hij
    exact hbaseK.trans (fordMScale_ge_uniform_base Φ hP (hlower i hi hij))
  have hQbox : ∀ i, i < j →
      (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
        fordQScale P Φ i := by
    intro i hij
    have hMone : 1 ≤ fordMScale P Φ (i + 1) := by
      exact (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)).trans
        (hMlarge (i + 1) (by omega) (by omega))
    exact ford_equation_3_9_rounded Φ hP (show 1 ≤ r by omega)
      (by omega) hupper (by omega) hMone hbaseQ
  have hpacket : ∀ i, 1 ≤ i → i ≤ j →
      ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ i⌋₊,
        (p : ℝ) ≤ eta * fordMScale P Φ i := by
    intro i hi hij p hp
    have hbaseScale : (M₀ : ℝ) ≤ fordMScale P Φ i :=
      hbaseM₀.trans (fordMScale_ge_uniform_base Φ hP (hlower i hi hij))
    have hscale0 : 0 ≤ fordMScale P Φ i := (fordMScale_pos hP0 Φ i).le
    have hM₀floor : M₀ ≤ ⌊fordMScale P Φ i⌋₊ :=
      (Nat.le_floor_iff hscale0).2 hbaseScale
    have hpBound := hM₀ ⌊fordMScale P Φ i⌋₊ hM₀floor p hp
    have hfloor : ((⌊fordMScale P Φ i⌋₊ : ℕ) : ℝ) ≤ fordMScale P Φ i :=
      Nat.floor_le hscale0
    rw [hetaEq]
    exact hpBound.trans (mul_le_mul_of_nonneg_left hfloor (by linarith))
  exact ⟨hP, hPfloor, hMlarge, hQbox, hpacket⟩

/-- Eventual, fully assembled equation (3.10).  This is the exact induction
needed by the asymptotic Ford consumer, with every physical scale and prime
packet derived rather than supplied to the conclusion. -/
theorem eventually_ford_equation_3_10_all_indices
    {s k r j : ℕ} {C delta eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k)
    (hks : k ≤ s)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    ∀ᶠ P : ℝ in atTop, ∀ J, J ≤ j - 1 →
      FordEquation310Eta s k r j C delta P eta Φ Esch J := by
  filter_upwards [eventually_ford_equation_3_10_inputs Φ hk hr hrk hj hjr
    h38 hlower homegaLower hetaEq] with P hinputs
  rcases hinputs with ⟨hP, hPbig, hMlarge, hQbox, hpacket⟩
  exact ford_equation_3_10_all_indices Φ Esch hk hr hrk hks hj hjr h38
    hlower hP hPbig homegaLower homegaUpper hetaEq hMlarge
      (fun i _hi hij => hQbox i hij) hpacket hmoment

#print axioms fordMScale_ge_uniform_base
#print axioms fordQScale_ge_tenth_power
#print axioms ford_equation_3_9_rounded
#print axioms eventually_ford_lemma_3_4_uniform_powers
#print axioms eventually_ford_equation_3_10_inputs
#print axioms eventually_ford_equation_3_10_all_indices

end

end GafniTao
