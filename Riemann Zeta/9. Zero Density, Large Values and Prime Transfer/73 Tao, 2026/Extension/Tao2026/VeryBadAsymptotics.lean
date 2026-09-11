import Tao2026.PowerfulLimit
import Tao2026.PowerfulRelationCounting
import Tao2026.VeryBadEquidistribution
import Tao2026.VeryBadIntervals

/-!
# Asymptotic closure for Tao's Theorem 1.8

This module isolates the final asymptotic bookkeeping in the very-bad case.
The difficult counting input is exactly the `2/5+o(1)` bound for nontrivial
values.  Once that bound is available, it is little-oh of the proved
one-term square-root main term, so the exact finite count decomposition gives
the public asymptotic equivalence.
-/

open Filter Asymptotics

namespace Tao2026

noncomputable section

/-! ## Exact finite cover by nontrivial very-bad intervals -/

/-- The literal finite set counted by `nontrivialVeryBadCount`. -/
noncomputable def nontrivialVeryBadNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n =>
    n ∈ veryBadSet \ veryBadOneTermSet

@[simp]
theorem card_nontrivialVeryBadNumbersUpTo (x : ℕ) :
    (nontrivialVeryBadNumbersUpTo x).card = nontrivialVeryBadCount x := by
  classical
  unfold nontrivialVeryBadNumbersUpTo nontrivialVeryBadCount countUpTo
  congr

theorem mem_nontrivialVeryBadNumbersUpTo {x n : ℕ} :
    n ∈ nontrivialVeryBadNumbersUpTo x ↔
      1 ≤ n ∧ n ≤ x ∧ n ∈ veryBadSet ∧ n ∉ veryBadOneTermSet := by
  classical
  simp [nontrivialVeryBadNumbersUpTo, and_assoc]

/-- All positive-start, non-one-term interval witnesses relevant below `x`.
The elementary part of Lemma 3.1 makes both coordinates bounded by `x`. -/
noncomputable def nontrivialVeryBadIntervalsUpTo (x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 0 x).product (Finset.Icc 2 x)).filter fun t =>
    IsVeryBadInterval t.1 t.2

theorem mem_nontrivialVeryBadIntervalsUpTo {x : ℕ} {t : ℕ × ℕ} :
    t ∈ nontrivialVeryBadIntervalsUpTo x ↔
      t.1 ≤ x ∧ 2 ≤ t.2 ∧ t.2 ≤ x ∧
        IsVeryBadInterval t.1 t.2 := by
  classical
  simp [nontrivialVeryBadIntervalsUpTo, and_assoc]

/-- The union of the values, truncated at `x`, in all finite nontrivial
interval witnesses relevant to that cutoff. -/
noncomputable def nontrivialVeryBadIntervalCover (x : ℕ) : Finset ℕ := by
  classical
  exact (nontrivialVeryBadIntervalsUpTo x).biUnion fun t =>
    (consecutiveInterval t.1 t.2).filter fun n => n ≤ x

/-- Every nontrivial very-bad value has a witness in the finite interval
cover.  The proof uses the exact zero-start classification to exclude the
only exceptional interval, and excludes `H=1` from non-one-term membership. -/
theorem nontrivialVeryBadNumbersUpTo_subset_intervalCover (x : ℕ) :
    nontrivialVeryBadNumbersUpTo x ⊆ nontrivialVeryBadIntervalCover x := by
  classical
  intro n hn
  have hn' := mem_nontrivialVeryBadNumbersUpTo.mp hn
  rcases hn'.2.2.1 with ⟨N, H, hnInterval, hveryBad⟩
  have hnotEdge : ¬(N = 0 ∧ H = 1) := by
    rintro ⟨rfl, rfl⟩
    have hnOne : n = 1 := by
      simpa [consecutiveInterval] using hnInterval
    subst n
    exact hn'.2.2.2 ⟨by omega, by simpa using hveryBad⟩
  have hHltN : H < N :=
    ((IsVeryBadInterval.eq_zero_one_or_length_lt_start hveryBad).resolve_left
      hnotEdge)
  have hHTwo : 2 ≤ H := by
    by_contra hH
    have hHpos : 1 ≤ H := hveryBad.length_pos
    have hHOne : H = 1 := by omega
    subst H
    have hnEq : n = N + 1 := by
      simpa [consecutiveInterval] using hnInterval
    have hNsub : n - 1 = N := by omega
    exact hn'.2.2.2 ⟨hn'.1, by simpa [hNsub] using hveryBad⟩
  have hNle : N ≤ x := by
    have hNlt : N < n := (Finset.mem_Ioc.mp hnInterval).1
    omega
  have hHle : H ≤ x := by omega
  rw [nontrivialVeryBadIntervalCover, Finset.mem_biUnion]
  refine ⟨(N, H), ?_, ?_⟩
  · exact mem_nontrivialVeryBadIntervalsUpTo.mpr
      ⟨hNle, hHTwo, hHle, hveryBad⟩
  · simp only [Finset.mem_filter]
    exact ⟨hnInterval, hn'.2.1⟩

/-- Exact first counting reduction: the nontrivial value count is bounded by
the total lengths of the finitely many nontrivial interval witnesses. -/
theorem nontrivialVeryBadCount_le_sum_intervalLengths (x : ℕ) :
    nontrivialVeryBadCount x ≤
      ∑ t ∈ nontrivialVeryBadIntervalsUpTo x, t.2 := by
  classical
  rw [← card_nontrivialVeryBadNumbersUpTo]
  calc
    (nontrivialVeryBadNumbersUpTo x).card ≤
        (nontrivialVeryBadIntervalCover x).card :=
      Finset.card_le_card (nontrivialVeryBadNumbersUpTo_subset_intervalCover x)
    _ ≤ ∑ t ∈ nontrivialVeryBadIntervalsUpTo x,
          ((consecutiveInterval t.1 t.2).filter fun n => n ≤ x).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ t ∈ nontrivialVeryBadIntervalsUpTo x, t.2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simp [consecutiveInterval])

/-! ## Uniform subpolynomial length budget from Lemma 3.1 -/

/-- Fixed-slack natural length budget obtained from Lemma 3.1 at `η=1/12`. -/
noncomputable def veryBadLemma31LengthBudget (x : ℕ) : ℕ :=
  ⌈Real.exp ((Real.log x) ^ (3 / 4 : ℝ))⌉₊

theorem tendsto_veryBadLemma31LengthBudget_atTop :
    Tendsto veryBadLemma31LengthBudget atTop atTop := by
  have hreal : Tendsto (fun x : ℕ =>
      Real.exp ((Real.log x) ^ (3 / 4 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  rw [tendsto_atTop]
  intro b
  filter_upwards [hreal.eventually (eventually_ge_atTop (b : ℝ))] with x hx
  have hcast : (b : ℝ) ≤ (veryBadLemma31LengthBudget x : ℝ) :=
    hx.trans (Nat.le_ceil _)
  exact_mod_cast hcast

/-- Lemma 3.1 supplies one cutoff-dependent length budget uniformly for every
nontrivial interval witness.  Finitely many starts below its eventual
threshold are absorbed using the elementary `H<N` branch. -/
theorem eventually_nontrivialVeryBadInterval_length_le_lemma31Budget
    (h31 : TaoLemma31Conclusion) :
    ∀ᶠ x : ℕ in atTop, ∀ t ∈ nontrivialVeryBadIntervalsUpTo x,
      t.2 ≤ veryBadLemma31LengthBudget x := by
  have h31fixed := h31.2 (1 / 12) (by norm_num)
  rw [eventually_atTop] at h31fixed
  obtain ⟨N₀, hN₀⟩ := h31fixed
  have hbudgetLarge : ∀ᶠ x : ℕ in atTop,
      N₀ ≤ veryBadLemma31LengthBudget x :=
    tendsto_veryBadLemma31LengthBudget_atTop.eventually
      (eventually_ge_atTop N₀)
  filter_upwards [hbudgetLarge] with x hbudget t ht
  have ht' := mem_nontrivialVeryBadIntervalsUpTo.mp ht
  by_cases hNlarge : N₀ ≤ t.1
  · have hraw := hN₀ t.1 hNlarge t.2 ht'.2.2.2
    have hHltN : t.2 < t.1 := by
      apply (IsVeryBadInterval.eq_zero_one_or_length_lt_start
        ht'.2.2.2).resolve_left
      intro hedge
      omega
    have hNpos : (0 : ℝ) < t.1 := by
      exact_mod_cast (show 0 < t.1 by omega)
    have hxpos : (0 : ℝ) < x := by
      exact lt_of_lt_of_le hNpos (by exact_mod_cast ht'.1)
    have hlogMono : Real.log (t.1 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hNpos hxpos (by exact_mod_cast ht'.1)
    have hlogNonneg : 0 ≤ Real.log (t.1 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ t.1 by omega))
    have hpowMono : (Real.log (t.1 : ℝ)) ^ (3 / 4 : ℝ) ≤
        (Real.log (x : ℝ)) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow hlogNonneg hlogMono (by norm_num)
    have hexpMono :
        Real.exp ((Real.log (t.1 : ℝ)) ^ (3 / 4 : ℝ)) ≤
          Real.exp ((Real.log (x : ℝ)) ^ (3 / 4 : ℝ)) :=
      Real.exp_le_exp.mpr hpowMono
    have hcast : (t.2 : ℝ) ≤ (veryBadLemma31LengthBudget x : ℝ) :=
      calc
        (t.2 : ℝ) ≤ Real.exp ((Real.log t.1) ^ (3 / 4 : ℝ)) := by
          norm_num at hraw ⊢
          exact hraw
        _ ≤ Real.exp ((Real.log x) ^ (3 / 4 : ℝ)) := hexpMono
        _ ≤ (veryBadLemma31LengthBudget x : ℝ) := Nat.le_ceil _
    exact_mod_cast hcast
  · have hHltN : t.2 < t.1 := by
      apply (IsVeryBadInterval.eq_zero_one_or_length_lt_start
        ht'.2.2.2).resolve_left
      intro hedge
      omega
    exact hHltN.le.trans (Nat.le_of_lt (Nat.lt_of_not_ge hNlarge)) |>.trans
      hbudget

/-- The fixed Lemma 3.1 length budget is subpolynomial. -/
theorem veryBadLemma31LengthBudget_powerUpperBound :
    PowerUpperBound (fun x => (veryBadLemma31LengthBudget x : ℝ)) 0 := by
  intro ε hε
  have hquarterTop : Tendsto (fun x : ℕ =>
      (Real.log x) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hquarter : ∀ᶠ x : ℕ in atTop,
      1 / ε ≤ (Real.log x) ^ (1 / 4 : ℝ) :=
    hquarterTop.eventually (eventually_ge_atTop _)
  have hlogEvent : ∀ᶠ x : ℕ in atTop, 1 < Real.log x :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 1)
  refine IsBigO.of_bound 2 ?_
  filter_upwards [hquarter, hlogEvent,
    eventually_ge_atTop (2 : ℕ)] with x hx hlog hxTwo
  let L : ℝ := Real.log x
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hquarterNonneg : 0 ≤ L ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hone : 1 ≤ L ^ (1 / 4 : ℝ) * ε := by
    rw [← div_le_iff₀ hε]
    simpa only [L] using hx
  have hexponent : L ^ (3 / 4 : ℝ) ≤ ε * L := by
    calc
      L ^ (3 / 4 : ℝ) = L ^ (3 / 4 : ℝ) * 1 := by ring
      _ ≤ L ^ (3 / 4 : ℝ) * (L ^ (1 / 4 : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg hLpos.le _)
      _ = (L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ)) * ε := by ring
      _ = L ^ ((3 / 4 : ℝ) + 1 / 4) * ε := by
        rw [Real.rpow_add hLpos]
      _ = ε * L := by norm_num; ring
  have hxpos : (0 : ℝ) < x := by exact_mod_cast
    (lt_of_lt_of_le (by omega : 0 < 2) hxTwo)
  have hexp : Real.exp (L ^ (3 / 4 : ℝ)) ≤ (x : ℝ) ^ ε := by
    calc
      Real.exp (L ^ (3 / 4 : ℝ)) ≤ Real.exp (ε * L) :=
        Real.exp_le_exp.mpr hexponent
      _ = (x : ℝ) ^ ε := by
        rw [Real.rpow_def_of_pos hxpos]
        dsimp only [L]
        congr 1
        exact mul_comm _ _
  have hxpowOne : 1 ≤ (x : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ x by omega)) hε.le
  have hceil : (veryBadLemma31LengthBudget x : ℝ) <
      Real.exp (L ^ (3 / 4 : ℝ)) + 1 := by
    simpa only [veryBadLemma31LengthBudget, L] using
      Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hbound : (veryBadLemma31LengthBudget x : ℝ) ≤
      2 * (x : ℝ) ^ (0 + ε) := by
    norm_num
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
  exact hbound

/-! ## Polynomial coefficient budget from Lemma 3.2 -/

/-- A fixed natural exponent dominating the polynomial coefficient exponent
in Lemma 3.2. -/
noncomputable def veryBadLemma32CoefficientDegree : ℕ :=
  ⌈3 * coefficientExponentConstant⌉₊

theorem veryBadLemma32CoefficientDegree_pos :
    0 < veryBadLemma32CoefficientDegree := by
  rw [veryBadLemma32CoefficientDegree, Nat.ceil_pos]
  exact mul_pos (by norm_num) coefficientExponentConstant_pos

theorem three_mul_coefficientExponentConstant_le_degree :
    3 * coefficientExponentConstant ≤
      (veryBadLemma32CoefficientDegree : ℝ) := by
  exact Nat.le_ceil _

/-- The coefficient cutoff induced by the uniform Lemma 3.1 length cutoff.
Using a natural power avoids any rounding loss in later finite counts. -/
noncomputable def veryBadLemma32CoefficientBudget (x : ℕ) : ℕ :=
  veryBadLemma31LengthBudget x ^ veryBadLemma32CoefficientDegree

/-- A fixed natural power of a subpolynomial budget remains
subpolynomial. -/
theorem veryBadLemma32CoefficientBudget_powerUpperBound :
    PowerUpperBound (fun x => (veryBadLemma32CoefficientBudget x : ℝ)) 0 := by
  intro ε hε
  let d : ℕ := veryBadLemma32CoefficientDegree
  have hd : 0 < d := veryBadLemma32CoefficientDegree_pos
  let δ : ℝ := ε / d
  have hδ : 0 < δ := div_pos hε (by exact_mod_cast hd)
  have hpow := (veryBadLemma31LengthBudget_powerUpperBound δ hδ).pow d
  have hnormalize :
      (fun x : ℕ => ((x : ℝ) ^ ((0 : ℝ) + δ)) ^ d) =O[atTop]
        (fun x : ℕ => (x : ℝ) ^ ((0 : ℝ) + ε)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
    have heq : ((x : ℝ) ^ ((0 : ℝ) + δ)) ^ d =
        (x : ℝ) ^ ((0 : ℝ) + ε) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hxpos.le]
      congr 1
      dsimp only [δ]
      field_simp
      ring
    rw [Real.norm_of_nonneg (pow_nonneg (Real.rpow_nonneg hxpos.le _) _),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul, heq]
  simpa only [veryBadLemma32CoefficientBudget, Nat.cast_pow, d] using
    hpow.trans hnormalize

/-! ## Lemma 3.2 certificates for interval witnesses -/

/-- The five arithmetic parameters supplied by Tao's Lemma 3.2. -/
structure VeryBadRelationCertificate where
  coeffLeft : ℕ
  coeffRight : ℕ
  coreLeft : ℕ
  coreRight : ℕ
  shift : ℕ
deriving DecidableEq

/-- A relation certificate records the full source conclusion for one very
bad interval, including the two actual interval elements. -/
def VeryBadRelationCertificate.Certifies
    (c : VeryBadRelationCertificate) (N H : ℕ) : Prop :=
  0 < c.shift ∧ c.shift < H ∧
    Powerful c.coreLeft ∧ Powerful c.coreRight ∧
    c.coeffLeft * c.coreLeft + c.shift = c.coeffRight * c.coreRight ∧
    c.coeffLeft ∣ H.factorial ∧ c.coeffRight ∣ H.factorial ∧
    (c.coeffLeft : ℝ) ≤ (H : ℝ) ^ (3 * coefficientExponentConstant) ∧
    (c.coeffRight : ℝ) ≤ (H : ℝ) ^ (3 * coefficientExponentConstant) ∧
    c.coeffLeft * c.coreLeft ∈ consecutiveInterval N H ∧
    c.coeffRight * c.coreRight ∈ consecutiveInterval N H

/-- Lemma 3.2 repackaged as existence of one structured certificate. -/
theorem exists_veryBadRelationCertificate
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H) :
    ∃ c : VeryBadRelationCertificate, c.Certifies N H := by
  obtain ⟨a, b, n, m, h, hh, hhH, hn, hm, heq, haDvd, hbDvd,
      haBound, hbBound, hleft, hright⟩ :=
    veryBadInterval_exists_polynomial_powerfulRelation hveryBad hH
  exact ⟨⟨a, b, n, m, h⟩, hh, hhH, hn, hm, heq, haDvd, hbDvd,
    haBound, hbBound, hleft, hright⟩

/-- A deterministic Lemma 3.2 certificate for every interval in the finite
cover.  Classical choice is harmless here and is exposed by the audit. -/
noncomputable def chosenVeryBadRelationCertificate (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    VeryBadRelationCertificate := by
  have ht := mem_nontrivialVeryBadIntervalsUpTo.mp t.property
  exact Classical.choose
    (exists_veryBadRelationCertificate ht.2.2.2 ht.2.1)

theorem chosenVeryBadRelationCertificate_spec (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    (chosenVeryBadRelationCertificate x t).Certifies t.1.1 t.1.2 := by
  have ht := mem_nontrivialVeryBadIntervalsUpTo.mp t.property
  exact Classical.choose_spec
    (exists_veryBadRelationCertificate ht.2.2.2 ht.2.1)

/-- Once Lemma 3.1 bounds an interval length by the uniform budget, both
coefficients in its chosen Lemma 3.2 certificate obey the induced natural
coefficient cutoff. -/
theorem chosenVeryBadRelationCertificate_coefficients_le_budget
    (x : ℕ) (t : ↥(nontrivialVeryBadIntervalsUpTo x))
    (hG : t.1.2 ≤ veryBadLemma31LengthBudget x) :
    (chosenVeryBadRelationCertificate x t).coeffLeft ≤
        veryBadLemma32CoefficientBudget x ∧
      (chosenVeryBadRelationCertificate x t).coeffRight ≤
        veryBadLemma32CoefficientBudget x := by
  let c := chosenVeryBadRelationCertificate x t
  have hspec := chosenVeryBadRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have htwo : 2 ≤ t.1.2 :=
    (mem_nontrivialVeryBadIntervalsUpTo.mp t.property).2.1
  have hbase : (1 : ℝ) ≤ t.1.2 := by
    exact_mod_cast (show 1 ≤ t.1.2 by omega)
  have hexponent : (t.1.2 : ℝ) ^ (3 * coefficientExponentConstant) ≤
      (t.1.2 : ℝ) ^ (veryBadLemma32CoefficientDegree : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase
      three_mul_coefficientExponentConstant_le_degree
  have hpowCast :
      (t.1.2 : ℝ) ^ (veryBadLemma32CoefficientDegree : ℝ) =
        ((t.1.2 ^ veryBadLemma32CoefficientDegree : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, Nat.cast_pow]
  have hnatPow : t.1.2 ^ veryBadLemma32CoefficientDegree ≤
      veryBadLemma31LengthBudget x ^ veryBadLemma32CoefficientDegree :=
    Nat.pow_le_pow_left hG _
  have hnatPowReal :
      ((t.1.2 ^ veryBadLemma32CoefficientDegree : ℕ) : ℝ) ≤
        ((veryBadLemma31LengthBudget x ^
          veryBadLemma32CoefficientDegree : ℕ) : ℝ) := by
    exact_mod_cast hnatPow
  constructor
  · have hreal : (c.coeffLeft : ℝ) ≤
        (veryBadLemma32CoefficientBudget x : ℝ) := by
      simpa only [veryBadLemma32CoefficientBudget] using
        hspec.2.2.2.2.2.2.2.1.trans
          ((hexponent.trans_eq hpowCast).trans hnatPowReal)
    have hnat : c.coeffLeft ≤ veryBadLemma32CoefficientBudget x := by
      exact_mod_cast hreal
    simpa only [c] using hnat
  · have hreal : (c.coeffRight : ℝ) ≤
        (veryBadLemma32CoefficientBudget x : ℝ) := by
      simpa only [veryBadLemma32CoefficientBudget] using
        hspec.2.2.2.2.2.2.2.2.1.trans
          ((hexponent.trans_eq hpowCast).trans hnatPowReal)
    have hnat : c.coeffRight ≤ veryBadLemma32CoefficientBudget x := by
      exact_mod_cast hreal
    simpa only [c] using hnat

/-- Every interval in the nontrivial finite cover is in the positive-start
branch of the elementary Lemma 3.1 alternative. -/
theorem nontrivialVeryBadInterval_length_lt_start (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) : t.1.2 < t.1.1 := by
  have ht := mem_nontrivialVeryBadIntervalsUpTo.mp t.property
  apply (IsVeryBadInterval.eq_zero_one_or_length_lt_start ht.2.2.2).resolve_left
  intro hedge
  omega

/-- The two powerful cores in the chosen certificate form an element of the
exact Corollary 2.11 relation set at cutoff `2x`.  This is the principal
finite bridge from Lemma 3.2 to the source counting theorem. -/
theorem chosenVeryBadRelationPair_mem (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    let c := chosenVeryBadRelationCertificate x t
    (c.coreLeft, c.coreRight) ∈
      powerfulRelationPairsUpTo c.coeffLeft c.coeffRight c.shift (2 * x) := by
  dsimp only
  let c := chosenVeryBadRelationCertificate x t
  have hspec := chosenVeryBadRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  rcases hspec with ⟨hshift, hshiftH, hpowLeft, hpowRight, heq,
    _haDvd, _hbDvd, _haBound, _hbBound, hleft, hright⟩
  have ht := mem_nontrivialVeryBadIntervalsUpTo.mp t.property
  have hHltN := nontrivialVeryBadInterval_length_lt_start x t
  have hend : t.1.1 + t.1.2 < 2 * x := by omega
  have hleftPos : 0 < c.coeffLeft * c.coreLeft :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hleft).1
  have hrightPos : 0 < c.coeffRight * c.coreRight :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hright).1
  have hcoeffLeft : 0 < c.coeffLeft := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hleftPos
  have hcoeffRight : 0 < c.coeffRight := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hrightPos
  have hcoreLeft : 0 < c.coreLeft := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hleftPos
  have hcoreRight : 0 < c.coreRight := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hrightPos
  have hleftLe : c.coeffLeft * c.coreLeft ≤ 2 * x :=
    (Finset.mem_Ioc.mp hleft).2.trans hend.le
  have hrightLe : c.coeffRight * c.coreRight ≤ 2 * x :=
    (Finset.mem_Ioc.mp hright).2.trans hend.le
  have hcoreLeftLe : c.coreLeft ≤ 2 * x :=
    (Nat.le_mul_of_pos_left c.coreLeft hcoeffLeft).trans hleftLe
  have hcoreRightLe : c.coreRight ≤ 2 * x :=
    (Nat.le_mul_of_pos_left c.coreRight hcoeffRight).trans hrightLe
  rw [mem_powerfulRelationPairsUpTo]
  exact ⟨hcoreLeft, hcoreLeftLe, hcoreRight,
    hcoreRightLe.trans (Nat.le_add_right _ _), hpowLeft, hpowRight,
    heq, hleftLe⟩

/-- The certificate together with the interval length and the position of its
left selected element determines the original interval. -/
structure VeryBadIntervalCode where
  certificate : VeryBadRelationCertificate
  intervalLength : ℕ
  leftOffset : ℕ
deriving DecidableEq

noncomputable def chosenVeryBadIntervalCode (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) : VeryBadIntervalCode :=
  let c := chosenVeryBadRelationCertificate x t
  ⟨c, t.1.2, c.coeffLeft * c.coreLeft - t.1.1 - 1⟩

theorem chosenVeryBadIntervalCode_length_le (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    (chosenVeryBadIntervalCode x t).intervalLength ≤ x := by
  change t.1.2 ≤ x
  exact (mem_nontrivialVeryBadIntervalsUpTo.mp t.property).2.2.1

theorem chosenVeryBadIntervalCode_offset_lt_length (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    (chosenVeryBadIntervalCode x t).leftOffset <
      (chosenVeryBadIntervalCode x t).intervalLength := by
  let c := chosenVeryBadRelationCertificate x t
  have hleft :=
    (chosenVeryBadRelationCertificate_spec x t).2.2.2.2.2.2.2.2.2.1
  change c.coeffLeft * c.coreLeft ∈ consecutiveInterval t.1.1 t.1.2 at hleft
  have hmem := Finset.mem_Ioc.mp hleft
  change c.coeffLeft * c.coreLeft - t.1.1 - 1 < t.1.2
  omega

/-- Exact multiplicity bookkeeping for the source proof: no two interval
witnesses have the same chosen relation certificate, length, and left offset.
The start is recovered from the selected left interval element. -/
theorem injective_chosenVeryBadIntervalCode (x : ℕ) :
    Function.Injective (chosenVeryBadIntervalCode x) := by
  intro t u hcode
  have hcert := congrArg VeryBadIntervalCode.certificate hcode
  have hlength := congrArg VeryBadIntervalCode.intervalLength hcode
  have hoffset := congrArg VeryBadIntervalCode.leftOffset hcode
  change chosenVeryBadRelationCertificate x t =
    chosenVeryBadRelationCertificate x u at hcert
  change t.1.2 = u.1.2 at hlength
  change
    (chosenVeryBadRelationCertificate x t).coeffLeft *
          (chosenVeryBadRelationCertificate x t).coreLeft - t.1.1 - 1 =
      (chosenVeryBadRelationCertificate x u).coeffLeft *
          (chosenVeryBadRelationCertificate x u).coreLeft - u.1.1 - 1
    at hoffset
  have hproduct :
      (chosenVeryBadRelationCertificate x t).coeffLeft *
          (chosenVeryBadRelationCertificate x t).coreLeft =
        (chosenVeryBadRelationCertificate x u).coeffLeft *
          (chosenVeryBadRelationCertificate x u).coreLeft :=
    congrArg (fun c => c.coeffLeft * c.coreLeft) hcert
  have htStart : t.1.1 <
      (chosenVeryBadRelationCertificate x t).coeffLeft *
        (chosenVeryBadRelationCertificate x t).coreLeft :=
    (Finset.mem_Ioc.mp
      (chosenVeryBadRelationCertificate_spec x t).2.2.2.2.2.2.2.2.2.1).1
  have huStart : u.1.1 <
      (chosenVeryBadRelationCertificate x u).coeffLeft *
        (chosenVeryBadRelationCertificate x u).coreLeft :=
    (Finset.mem_Ioc.mp
      (chosenVeryBadRelationCertificate_spec x u).2.2.2.2.2.2.2.2.2.1).1
  apply Subtype.ext
  apply Prod.ext
  · omega
  · exact hlength

/-- A finite ambient set of all Lemma 3.2 certificates relevant below `x`.
The factorial coefficient cutoff is intentionally coarse at this stage; the
source's subpolynomial cutoff is imposed in the next asymptotic layer. -/
noncomputable def veryBadRelationCertificatesUpTo (x : ℕ) :
    Finset VeryBadRelationCertificate := by
  classical
  exact ((Finset.Icc 1 x.factorial).product
      (Finset.Icc 1 x.factorial)).biUnion fun ab =>
    (Finset.Icc 1 x).biUnion fun h =>
      (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
        ⟨ab.1, ab.2, nm.1, nm.2, h⟩

/-- Every chosen certificate lies in the finite ambient certificate set. -/
theorem chosenVeryBadRelationCertificate_mem (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    chosenVeryBadRelationCertificate x t ∈
      veryBadRelationCertificatesUpTo x := by
  classical
  let c := chosenVeryBadRelationCertificate x t
  have hspec := chosenVeryBadRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  rcases hspec with ⟨hshift, hshiftH, _hpowLeft, _hpowRight, _heq,
    haDvd, hbDvd, _haBound, _hbBound, hleft, hright⟩
  have ht := mem_nontrivialVeryBadIntervalsUpTo.mp t.property
  have hleftPos : 0 < c.coeffLeft * c.coreLeft :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hleft).1
  have hrightPos : 0 < c.coeffRight * c.coreRight :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hright).1
  have haPos : 0 < c.coeffLeft := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hleftPos
  have hbPos : 0 < c.coeffRight := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hrightPos
  have haLe : c.coeffLeft ≤ x.factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) haDvd).trans
      (Nat.factorial_le ht.2.2.1)
  have hbLe : c.coeffRight ≤ x.factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) hbDvd).trans
      (Nat.factorial_le ht.2.2.1)
  have hshiftLe : c.shift ≤ x := by omega
  rw [veryBadRelationCertificatesUpTo, Finset.mem_biUnion]
  refine ⟨(c.coeffLeft, c.coeffRight), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨haPos, haLe⟩,
        Finset.mem_Icc.mpr ⟨hbPos, hbLe⟩⟩
  · rw [Finset.mem_biUnion]
    refine ⟨c.shift, Finset.mem_Icc.mpr ⟨hshift, hshiftLe⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨(c.coreLeft, c.coreRight),
      chosenVeryBadRelationPair_mem x t, rfl⟩

/-- Finite ambient range for the injective interval code. -/
noncomputable def veryBadIntervalCodesUpTo (x : ℕ) :
    Finset VeryBadIntervalCode := by
  classical
  exact (veryBadRelationCertificatesUpTo x).product
      ((Finset.Icc 2 x).product (Finset.range x)) |>.image fun q =>
    ⟨q.1, q.2.1, q.2.2⟩

theorem chosenVeryBadIntervalCode_mem (x : ℕ)
    (t : ↥(nontrivialVeryBadIntervalsUpTo x)) :
    chosenVeryBadIntervalCode x t ∈ veryBadIntervalCodesUpTo x := by
  classical
  rw [veryBadIntervalCodesUpTo, Finset.mem_image]
  refine ⟨(chosenVeryBadRelationCertificate x t,
      ((chosenVeryBadIntervalCode x t).intervalLength,
        (chosenVeryBadIntervalCode x t).leftOffset)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨chosenVeryBadRelationCertificate_mem x t, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨(mem_nontrivialVeryBadIntervalsUpTo.mp t.property).2.1,
        chosenVeryBadIntervalCode_length_le x t⟩, Finset.mem_range.mpr ?_⟩
    exact (chosenVeryBadIntervalCode_offset_lt_length x t).trans_le
      (chosenVeryBadIntervalCode_length_le x t)
  · rfl

/-- The injective code embeds every relevant interval into its explicit
finite ambient range. -/
theorem card_nontrivialVeryBadIntervalsUpTo_le_codes (x : ℕ) :
    (nontrivialVeryBadIntervalsUpTo x).card ≤
      (veryBadIntervalCodesUpTo x).card := by
  classical
  let s := nontrivialVeryBadIntervalsUpTo x
  have himage : s.attach.image (chosenVeryBadIntervalCode x) ⊆
      veryBadIntervalCodesUpTo x := by
    intro c hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨t, _ht, rfl⟩
    exact chosenVeryBadIntervalCode_mem x t
  calc
    (nontrivialVeryBadIntervalsUpTo x).card = s.attach.card := by
      simp [s]
    _ = (s.attach.image (chosenVeryBadIntervalCode x)).card := by
      rw [Finset.card_image_iff.mpr
        (injective_chosenVeryBadIntervalCode x).injOn]
    _ ≤ (veryBadIntervalCodesUpTo x).card := Finset.card_le_card himage

/-- The code range costs at most two bounded natural parameters beyond its
relation certificate. -/
theorem card_veryBadIntervalCodesUpTo_le (x : ℕ) :
    (veryBadIntervalCodesUpTo x).card ≤
      (veryBadRelationCertificatesUpTo x).card * (x * x) := by
  classical
  have hIcc : (Finset.Icc 2 x).card ≤ x := by simp
  calc
    (veryBadIntervalCodesUpTo x).card ≤
        ((veryBadRelationCertificatesUpTo x).product
          ((Finset.Icc 2 x).product (Finset.range x))).card :=
      Finset.card_image_le
    _ = (veryBadRelationCertificatesUpTo x).card *
        ((Finset.Icc 2 x).card * x) := by simp
    _ ≤ (veryBadRelationCertificatesUpTo x).card * (x * x) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right x hIcc)

/-- Exact finite reduction of the nontrivial value count to Lemma 3.2
relation certificates, with the source's two interval-multiplicity factors
made explicit. -/
theorem nontrivialVeryBadCount_le_cube_mul_relationCertificates (x : ℕ) :
    nontrivialVeryBadCount x ≤
      x ^ 3 * (veryBadRelationCertificatesUpTo x).card := by
  calc
    nontrivialVeryBadCount x ≤
        ∑ t ∈ nontrivialVeryBadIntervalsUpTo x, t.2 :=
      nontrivialVeryBadCount_le_sum_intervalLengths x
    _ ≤ ∑ _t ∈ nontrivialVeryBadIntervalsUpTo x, x := by
      apply Finset.sum_le_sum
      intro t ht
      exact (mem_nontrivialVeryBadIntervalsUpTo.mp ht).2.2.1
    _ = x * (nontrivialVeryBadIntervalsUpTo x).card := by
      simp [mul_comm]
    _ ≤ x * (veryBadIntervalCodesUpTo x).card :=
      Nat.mul_le_mul_left x (card_nontrivialVeryBadIntervalsUpTo_le_codes x)
    _ ≤ x * ((veryBadRelationCertificatesUpTo x).card * (x * x)) :=
      Nat.mul_le_mul_left x (card_veryBadIntervalCodesUpTo_le x)
    _ = x ^ 3 * (veryBadRelationCertificatesUpTo x).card := by ring

/-! ## Budgeted certificate range for the asymptotic count -/

/-- Certificate range with independent length/shift and coefficient budgets.
This is the source-faithful finite family used for the asymptotic assembly. -/
noncomputable def veryBadRelationCertificatesUpToBudgets
    (x G A : ℕ) : Finset VeryBadRelationCertificate := by
  classical
  exact ((Finset.Icc 1 A).product (Finset.Icc 1 A)).biUnion fun ab =>
    (Finset.Icc 1 G).biUnion fun h =>
      (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
        ⟨ab.1, ab.2, nm.1, nm.2, h⟩

/-- A natural pointwise envelope for the uniform Corollary 2.11 estimate at
cutoff `2x`. -/
noncomputable def veryBadRelationCountBudget (ε : ℝ) (x : ℕ) : ℕ :=
  ⌈powerfulRelationEpsilonConstant ε *
      ((2 * x : ℕ) : ℝ) ^ ((2 : ℝ) / 5 + ε)⌉₊

theorem card_powerfulRelationPairsUpTo_two_mul_le_budget
    {a b h x : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hx : 1 ≤ x) (haX : a ≤ 2 * x) (hbX : b ≤ 2 * x)
    (hhX : h ≤ 2 * x) {ε : ℝ} (hε : 0 < ε) :
    (powerfulRelationPairsUpTo a b h (2 * x)).card ≤
      veryBadRelationCountBudget ε x := by
  have hpoint := card_powerfulRelationPairsUpTo_le_const_mul_rpow
    ha hb hh (by omega : 2 ≤ 2 * x) haX hbX hhX hε
  have hceil : powerfulRelationEpsilonConstant ε *
      ((2 * x : ℕ) : ℝ) ^ ((2 : ℝ) / 5 + ε) ≤
        (veryBadRelationCountBudget ε x : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hpoint.trans hceil

/-- The full finite certificate family costs only the three parameter
ranges times one uniform Corollary 2.11 relation-count budget. -/
theorem card_veryBadRelationCertificatesUpToBudgets_le
    (x G A : ℕ) (hx : 1 ≤ x) (hG : G ≤ 2 * x) (hA : A ≤ 2 * x)
    {ε : ℝ} (hε : 0 < ε) :
    (veryBadRelationCertificatesUpToBudgets x G A).card ≤
      A ^ 2 * G * veryBadRelationCountBudget ε x := by
  classical
  let R := veryBadRelationCountBudget ε x
  let P := (Finset.Icc 1 A).product (Finset.Icc 1 A)
  have hP : P.card ≤ A ^ 2 := by
    dsimp only [P]
    simp [pow_two]
  have hinner : ∀ ab ∈ P,
      ((Finset.Icc 1 G).biUnion fun h =>
        (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
          (⟨ab.1, ab.2, nm.1, nm.2, h⟩ :
            VeryBadRelationCertificate)).card ≤ G * R := by
    intro ab hab
    have hab' := Finset.mem_product.mp hab
    calc
      ((Finset.Icc 1 G).biUnion fun h =>
          (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
            (⟨ab.1, ab.2, nm.1, nm.2, h⟩ :
              VeryBadRelationCertificate)).card
          ≤ ∑ h ∈ Finset.Icc 1 G,
              ((powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
                (⟨ab.1, ab.2, nm.1, nm.2, h⟩ :
                  VeryBadRelationCertificate)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _h ∈ Finset.Icc 1 G, R := by
        apply Finset.sum_le_sum
        intro h hhmem
        exact Finset.card_image_le.trans
          (card_powerfulRelationPairsUpTo_two_mul_le_budget
            (Finset.mem_Icc.mp hab'.1).1 (Finset.mem_Icc.mp hab'.2).1
            (Finset.mem_Icc.mp hhmem).1 hx
            ((Finset.mem_Icc.mp hab'.1).2.trans hA)
            ((Finset.mem_Icc.mp hab'.2).2.trans hA)
            ((Finset.mem_Icc.mp hhmem).2.trans hG) hε)
      _ = (Finset.Icc 1 G).card * R := by simp
      _ ≤ G * R := Nat.mul_le_mul_right R (by simp)
  rw [veryBadRelationCertificatesUpToBudgets]
  change (P.biUnion _).card ≤ _
  calc
    (P.biUnion fun ab =>
        (Finset.Icc 1 G).biUnion fun h =>
          (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
            (⟨ab.1, ab.2, nm.1, nm.2, h⟩ :
              VeryBadRelationCertificate)).card
        ≤ ∑ ab ∈ P,
            ((Finset.Icc 1 G).biUnion fun h =>
              (powerfulRelationPairsUpTo ab.1 ab.2 h (2 * x)).image fun nm =>
                (⟨ab.1, ab.2, nm.1, nm.2, h⟩ :
                  VeryBadRelationCertificate)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ab ∈ P, G * R := Finset.sum_le_sum hinner
    _ = P.card * (G * R) := by simp
    _ ≤ A ^ 2 * (G * R) := Nat.mul_le_mul_right _ hP
    _ = A ^ 2 * G * veryBadRelationCountBudget ε x := by
      dsimp only [R]
      ring

/-- For every fixed positive epsilon, the rounded uniform relation envelope
has its displayed power upper bound. -/
theorem veryBadRelationCountBudget_powerUpperBound
    {δ : ℝ} (hδ : 0 < δ) :
    PowerUpperBound (fun x => (veryBadRelationCountBudget δ x : ℝ))
      ((2 : ℝ) / 5 + δ) := by
  intro ε hε
  let r : ℝ := (2 : ℝ) / 5 + δ
  let q : ℝ := r + ε
  let C : ℝ := powerfulRelationEpsilonConstant δ
  let K : ℝ := C * (2 : ℝ) ^ r + 1
  have hr : 0 < r := by dsimp only [r]; linarith
  have hC : 0 ≤ C := by
    exact (powerfulRelationEpsilonConstant_pos hδ).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hxreal : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxnonneg : (0 : ℝ) ≤ x := hxreal.trans' zero_le_one
  have hexp : r ≤ q := by dsimp only [q]; linarith
  have hxpow : (x : ℝ) ^ r ≤ (x : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le hxreal hexp
  have honepow : (1 : ℝ) ≤ (x : ℝ) ^ q :=
    Real.one_le_rpow hxreal (by dsimp only [q, r]; linarith)
  have hceil : (veryBadRelationCountBudget δ x : ℝ) <
      C * ((2 * x : ℕ) : ℝ) ^ r + 1 := by
    simpa only [veryBadRelationCountBudget, C, r] using
      Nat.ceil_lt_add_one (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hxnonneg _)]
  calc
    (veryBadRelationCountBudget δ x : ℝ)
        ≤ C * ((2 * x : ℕ) : ℝ) ^ r + 1 := hceil.le
    _ = C * (2 : ℝ) ^ r * (x : ℝ) ^ r + 1 := by
      push_cast
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxnonneg]
      ring
    _ ≤ C * (2 : ℝ) ^ r * (x : ℝ) ^ q + (x : ℝ) ^ q := by
      gcongr
    _ = K * (x : ℝ) ^ q := by
      dsimp only [K]
      ring
    _ = K * (x : ℝ) ^ (((2 : ℝ) / 5 + δ) + ε) := rfl

theorem chosenVeryBadRelationCertificate_mem_budgets
    (x G A : ℕ) (t : ↥(nontrivialVeryBadIntervalsUpTo x))
    (hG : t.1.2 ≤ G)
    (haA : (chosenVeryBadRelationCertificate x t).coeffLeft ≤ A)
    (hbA : (chosenVeryBadRelationCertificate x t).coeffRight ≤ A) :
    chosenVeryBadRelationCertificate x t ∈
      veryBadRelationCertificatesUpToBudgets x G A := by
  classical
  let c := chosenVeryBadRelationCertificate x t
  have hspec := chosenVeryBadRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  rcases hspec with ⟨hshift, hshiftH, _hpowLeft, _hpowRight, _heq,
    _haDvd, _hbDvd, _haBound, _hbBound, hleft, hright⟩
  have hleftPos : 0 < c.coeffLeft * c.coreLeft :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hleft).1
  have hrightPos : 0 < c.coeffRight * c.coreRight :=
    lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hright).1
  have haPos : 0 < c.coeffLeft := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hleftPos
  have hbPos : 0 < c.coeffRight := by
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hrightPos
  have hshiftLe : c.shift ≤ G := hshiftH.le.trans hG
  rw [veryBadRelationCertificatesUpToBudgets, Finset.mem_biUnion]
  refine ⟨(c.coeffLeft, c.coeffRight), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨haPos, haA⟩,
        Finset.mem_Icc.mpr ⟨hbPos, hbA⟩⟩
  · rw [Finset.mem_biUnion]
    refine ⟨c.shift, Finset.mem_Icc.mpr ⟨hshift, hshiftLe⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨(c.coreLeft, c.coreRight),
      chosenVeryBadRelationPair_mem x t, rfl⟩

noncomputable def veryBadIntervalCodesUpToBudgets
    (x G A : ℕ) : Finset VeryBadIntervalCode := by
  classical
  exact (veryBadRelationCertificatesUpToBudgets x G A).product
      ((Finset.Icc 2 G).product (Finset.range G)) |>.image fun q =>
    ⟨q.1, q.2.1, q.2.2⟩

theorem chosenVeryBadIntervalCode_mem_budgets
    (x G A : ℕ) (t : ↥(nontrivialVeryBadIntervalsUpTo x))
    (hG : t.1.2 ≤ G)
    (haA : (chosenVeryBadRelationCertificate x t).coeffLeft ≤ A)
    (hbA : (chosenVeryBadRelationCertificate x t).coeffRight ≤ A) :
    chosenVeryBadIntervalCode x t ∈
      veryBadIntervalCodesUpToBudgets x G A := by
  classical
  rw [veryBadIntervalCodesUpToBudgets, Finset.mem_image]
  refine ⟨(chosenVeryBadRelationCertificate x t,
      ((chosenVeryBadIntervalCode x t).intervalLength,
        (chosenVeryBadIntervalCode x t).leftOffset)), ?_, rfl⟩
  apply Finset.mem_product.mpr
  refine ⟨chosenVeryBadRelationCertificate_mem_budgets x G A t hG haA hbA, ?_⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr
    ⟨(mem_nontrivialVeryBadIntervalsUpTo.mp t.property).2.1, hG⟩,
      Finset.mem_range.mpr ?_⟩
  exact (chosenVeryBadIntervalCode_offset_lt_length x t).trans_le hG

theorem card_nontrivialVeryBadIntervalsUpTo_le_budgetCodes
    (x G A : ℕ)
    (hG : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x), t.1.2 ≤ G)
    (haA : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x),
      (chosenVeryBadRelationCertificate x t).coeffLeft ≤ A)
    (hbA : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x),
      (chosenVeryBadRelationCertificate x t).coeffRight ≤ A) :
    (nontrivialVeryBadIntervalsUpTo x).card ≤
      (veryBadIntervalCodesUpToBudgets x G A).card := by
  classical
  let s := nontrivialVeryBadIntervalsUpTo x
  have himage : s.attach.image (chosenVeryBadIntervalCode x) ⊆
      veryBadIntervalCodesUpToBudgets x G A := by
    intro c hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨t, _ht, rfl⟩
    exact chosenVeryBadIntervalCode_mem_budgets x G A t (hG t) (haA t) (hbA t)
  calc
    (nontrivialVeryBadIntervalsUpTo x).card = s.attach.card := by simp [s]
    _ = (s.attach.image (chosenVeryBadIntervalCode x)).card := by
      rw [Finset.card_image_iff.mpr
        (injective_chosenVeryBadIntervalCode x).injOn]
    _ ≤ (veryBadIntervalCodesUpToBudgets x G A).card :=
      Finset.card_le_card himage

theorem card_veryBadIntervalCodesUpToBudgets_le (x G A : ℕ) :
    (veryBadIntervalCodesUpToBudgets x G A).card ≤
      (veryBadRelationCertificatesUpToBudgets x G A).card * (G * G) := by
  classical
  have hIcc : (Finset.Icc 2 G).card ≤ G := by simp
  calc
    (veryBadIntervalCodesUpToBudgets x G A).card ≤
        ((veryBadRelationCertificatesUpToBudgets x G A).product
          ((Finset.Icc 2 G).product (Finset.range G))).card :=
      Finset.card_image_le
    _ = (veryBadRelationCertificatesUpToBudgets x G A).card *
        ((Finset.Icc 2 G).card * G) := by simp
    _ ≤ (veryBadRelationCertificatesUpToBudgets x G A).card * (G * G) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right G hIcc)

/-- Complete exact finite multiplicity reduction at arbitrary source budgets.
All remaining asymptotic work is now in the size of the parameter family and
the uniform Corollary 2.11 relation count. -/
theorem nontrivialVeryBadCount_le_budgetCube_mul_relationCertificates
    (x G A : ℕ)
    (hG : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x), t.1.2 ≤ G)
    (haA : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x),
      (chosenVeryBadRelationCertificate x t).coeffLeft ≤ A)
    (hbA : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x),
      (chosenVeryBadRelationCertificate x t).coeffRight ≤ A) :
    nontrivialVeryBadCount x ≤ G ^ 3 *
      (veryBadRelationCertificatesUpToBudgets x G A).card := by
  calc
    nontrivialVeryBadCount x ≤
        ∑ t ∈ nontrivialVeryBadIntervalsUpTo x, t.2 :=
      nontrivialVeryBadCount_le_sum_intervalLengths x
    _ ≤ ∑ _t ∈ nontrivialVeryBadIntervalsUpTo x, G := by
      apply Finset.sum_le_sum
      intro t ht
      exact hG ⟨t, ht⟩
    _ = G * (nontrivialVeryBadIntervalsUpTo x).card := by simp [mul_comm]
    _ ≤ G * (veryBadIntervalCodesUpToBudgets x G A).card :=
      Nat.mul_le_mul_left G
        (card_nontrivialVeryBadIntervalsUpTo_le_budgetCodes x G A hG haA hbA)
    _ ≤ G * ((veryBadRelationCertificatesUpToBudgets x G A).card * (G * G)) :=
      Nat.mul_le_mul_left G (card_veryBadIntervalCodesUpToBudgets_le x G A)
    _ = G ^ 3 * (veryBadRelationCertificatesUpToBudgets x G A).card := by ring

/-- Lemmas 3.1 and 3.2, together with the proved uniform Corollary 2.11
count, give the complete nontrivial `x^(2/5+o(1))` upper bound. -/
theorem nontrivialVeryBadCount_powerUpperBound_of_taoLemma31
    (h31 : TaoLemma31Conclusion) :
    PowerUpperBound (fun x => (nontrivialVeryBadCount x : ℝ))
      (2 / 5 : ℝ) := by
  let G : ℕ → ℕ := veryBadLemma31LengthBudget
  let A : ℕ → ℕ := veryBadLemma32CoefficientBudget
  have hGpub : PowerUpperBound (fun x => (G x : ℝ)) 0 := by
    simpa only [G] using veryBadLemma31LengthBudget_powerUpperBound
  have hApub : PowerUpperBound (fun x => (A x : ℝ)) 0 := by
    simpa only [A] using veryBadLemma32CoefficientBudget_powerUpperBound
  have hGlinear : ∀ᶠ x : ℕ in atTop, G x ≤ 2 * x :=
    eventually_nat_le_two_mul_self_of_powerUpperBound_zero G hGpub
  have hAlinear : ∀ᶠ x : ℕ in atTop, A x ≤ 2 * x :=
    eventually_nat_le_two_mul_self_of_powerUpperBound_zero A hApub
  have hlength : ∀ᶠ x : ℕ in atTop,
      ∀ t ∈ nontrivialVeryBadIntervalsUpTo x, t.2 ≤ G x := by
    simpa only [G] using
      eventually_nontrivialVeryBadInterval_length_le_lemma31Budget h31
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  let R : ℕ → ℕ := veryBadRelationCountBudget δ
  have hfinite :
      (fun x => (nontrivialVeryBadCount x : ℝ)) =O[atTop]
        (fun x =>
          (((G x : ℝ) * (G x : ℝ)) * ((G x : ℝ) * (G x : ℝ))) *
            ((A x : ℝ) * (A x : ℝ)) * (R x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hlength, hGlinear, hAlinear,
      eventually_ge_atTop (1 : ℕ)] with x hxLength hxG hxA hxOne
    have hcoeff : ∀ t : ↥(nontrivialVeryBadIntervalsUpTo x),
        (chosenVeryBadRelationCertificate x t).coeffLeft ≤ A x ∧
          (chosenVeryBadRelationCertificate x t).coeffRight ≤ A x := by
      intro t
      simpa only [A, G] using
        chosenVeryBadRelationCertificate_coefficients_le_budget x t
          (hxLength t.1 t.property)
    have hcount :=
      nontrivialVeryBadCount_le_budgetCube_mul_relationCertificates
        x (G x) (A x)
        (fun t => hxLength t.1 t.property)
        (fun t => (hcoeff t).1) (fun t => (hcoeff t).2)
    have hcert := card_veryBadRelationCertificatesUpToBudgets_le
      x (G x) (A x) hxOne hxG hxA hδ
    have hnat : nontrivialVeryBadCount x ≤
        ((G x * G x) * (G x * G x)) * (A x * A x) * R x := by
      calc
        nontrivialVeryBadCount x ≤ G x ^ 3 *
            (veryBadRelationCertificatesUpToBudgets x (G x) (A x)).card :=
          hcount
        _ ≤ G x ^ 3 * (A x ^ 2 * G x *
            veryBadRelationCountBudget δ x) :=
          Nat.mul_le_mul_left _ hcert
        _ = ((G x * G x) * (G x * G x)) *
            (A x * A x) * R x := by
          dsimp only [R]
          ring
    have htarget : 0 ≤
        (((G x : ℝ) * (G x : ℝ)) * ((G x : ℝ) * (G x : ℝ))) *
          ((A x : ℝ) * (A x : ℝ)) * (R x : ℝ) := by positivity
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg htarget, one_mul]
    exact_mod_cast hnat
  have hGtwo : PowerUpperBound
      (fun x => (G x : ℝ) * (G x : ℝ)) 0 := by
    simpa only [zero_add] using hGpub.mul hGpub
  have hGfour : PowerUpperBound
      (fun x => ((G x : ℝ) * (G x : ℝ)) *
        ((G x : ℝ) * (G x : ℝ))) 0 := by
    simpa only [zero_add] using hGtwo.mul hGtwo
  have hAtwo : PowerUpperBound
      (fun x => (A x : ℝ) * (A x : ℝ)) 0 := by
    simpa only [zero_add] using hApub.mul hApub
  have hparameters : PowerUpperBound
      (fun x =>
        (((G x : ℝ) * (G x : ℝ)) * ((G x : ℝ) * (G x : ℝ))) *
          ((A x : ℝ) * (A x : ℝ))) 0 := by
    simpa only [zero_add] using hGfour.mul hAtwo
  have hR : PowerUpperBound (fun x => (R x : ℝ))
      ((2 : ℝ) / 5 + δ) := by
    simpa only [R] using veryBadRelationCountBudget_powerUpperBound hδ
  have htotal : PowerUpperBound
      (fun x =>
        (((G x : ℝ) * (G x : ℝ)) * ((G x : ℝ) * (G x : ℝ))) *
          ((A x : ℝ) * (A x : ℝ)) * (R x : ℝ))
      ((2 : ℝ) / 5 + δ) := by
    simpa only [zero_add] using hparameters.mul hR
  have hout := htotal (ε / 2) (by linarith)
  have hnormalize :
      (fun n : ℕ => (n : ℝ) ^
        (((2 : ℝ) / 5 + δ) + ε / 2)) =
      (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / 5 + ε)) := by
    funext n
    congr 1
    dsimp only [δ]
    ring
  rw [hnormalize] at hout
  exact hfinite.trans hout

/-- The exponent gap `2/5 < 1/2` turns the source upper-bound language into
little-oh of the square-root scale. -/
theorem isLittleO_sqrt_of_powerUpperBound_two_fifths
    {f : ℕ → ℝ} (hf : PowerUpperBound f (2 / 5 : ℝ)) :
    f =o[atTop] fun x : ℕ => Real.sqrt x := by
  have hfO := hf (1 / 20 : ℝ) (by norm_num)
  have hrpow :
      (fun x : ℕ => (x : ℝ) ^ (9 / 20 : ℝ)) =o[atTop]
        fun x : ℕ => Real.sqrt x := by
    rw [isLittleO_iff_tendsto']
    · have ht := (tendsto_rpow_neg_atTop
          (show (0 : ℝ) < 1 / 20 by norm_num)).comp
        tendsto_natCast_atTop_atTop
      refine ht.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      simp only [Function.comp_apply]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hxpos]
      congr 1
      norm_num
    · filter_upwards [eventually_ge_atTop 1] with x hx hsqrt
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      exfalso
      exact (Real.sqrt_pos.2 hxpos).ne' hsqrt
  have hfO' : f =O[atTop] fun x : ℕ => (x : ℝ) ^ (9 / 20 : ℝ) := by
    simpa only [show (2 / 5 : ℝ) + 1 / 20 = 9 / 20 by norm_num] using hfO
  exact hfO'.trans_isLittleO hrpow

/-- The zeta-ratio constant in Theorem 1.8 is strictly positive. -/
theorem powerfulNumberConstant_pos : 0 < powerfulNumberConstant := by
  rw [← squarefreePSeriesConstant_eq_powerfulNumberConstant]
  exact squarefreePSeriesConstant_pos

/-- Any proof of the nontrivial-value estimate completes Tao's literal
Theorem 1.8 contract; the one-term asymptotic and the finite decomposition are
already unconditional. -/
theorem taoTheorem18_of_nontrivial_powerUpperBound
    (hnontrivial :
      PowerUpperBound (fun x => (nontrivialVeryBadCount x : ℝ)) (2 / 5 : ℝ)) :
    TaoTheorem18Conclusion := by
  refine ⟨hnontrivial, ?_⟩
  have hsmallSqrt :=
    isLittleO_sqrt_of_powerUpperBound_two_fifths hnontrivial
  have hsmallMain :
      (fun x : ℕ => (nontrivialVeryBadCount x : ℝ)) =o[atTop]
        fun x : ℕ => powerfulNumberConstant * Real.sqrt x :=
    hsmallSqrt.const_mul_right powerfulNumberConstant_pos.ne'
  have hadd := hsmallMain.add_isEquivalent
    veryBadOneTermCount_asymptotic_powerfulNumberConstant
  apply hadd.congr_left
  filter_upwards [] with x
  change (nontrivialVeryBadCount x : ℝ) +
      (veryBadOneTermCount x : ℝ) = (veryBadCount x : ℝ)
  exact_mod_cast nontrivialVeryBadCount_add_veryBadOneTermCount x

/-- Source-facing conditional closure of Theorem 1.8 from the corrected
Lemma 3.1 contract. -/
theorem taoTheorem18_of_taoLemma31
    (h31 : TaoLemma31Conclusion) : TaoTheorem18Conclusion :=
  taoTheorem18_of_nontrivial_powerUpperBound
    (nontrivialVeryBadCount_powerUpperBound_of_taoLemma31 h31)

/-- The exact specialization of Theorem 2.5 used by Lemma 3.1 therefore
closes Theorem 1.8. -/
theorem taoTheorem18_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion) : TaoTheorem18Conclusion :=
  taoTheorem18_of_taoLemma31
    (taoLemma31_of_taoTheorem25Specialized h25)

/-- Source-facing closure of Theorem 1.8 from the full Theorem 2.5
contract. -/
theorem taoTheorem18_of_taoTheorem25
    (h25 : TaoTheorem25Conclusion) : TaoTheorem18Conclusion :=
  taoTheorem18_of_taoLemma31 (taoLemma31_of_taoTheorem25 h25)

end

end Tao2026
