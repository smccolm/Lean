import Tao2026.BadIntervalSourceScales
import Tao2026.FactorialLargeSieveMaximal

/-!
# Large-sieve setup for long normalized bad intervals

This module builds the exact finite Corollary 2.9 input used when typicality
condition (i) fails.  For every prime `p₀ < p ≤ 2p₀`, a normalized bad
interval is `p₀`-smooth and therefore avoids all `H` residue classes in which
one of `N+1, ..., N+H` is divisible by `p`.
-/

open Finset
open Filter
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The `H` residue classes represented by `-1, ..., -H` are distinct modulo
`p` as soon as `H < p`. -/
theorem card_factorialAllowedStartResidues_eq_of_lt
    {p H : ℕ} (hHp : H < p) :
    (factorialAllowedStartResidues p H).card = H := by
  rw [factorialAllowedStartResidues]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have haBounds := Finset.mem_Icc.mp ha
    have hbBounds := Finset.mem_Icc.mp hb
    have hcast : (a : ZMod p) = (b : ZMod p) := by
      simpa only [neg_inj] using hab
    have hmod := (ZMod.natCast_eq_natCast_iff' a b p).mp hcast
    simpa only [Nat.mod_eq_of_lt (haBounds.2.trans_lt hHp),
      Nat.mod_eq_of_lt (hbBounds.2.trans_lt hHp)] using hmod

/-- Prime moduli in the source interval `p₀ < p ≤ 2p₀`. -/
def badIntervalUpperPrimes (p₀ : ℕ) : Finset ℕ :=
  factorialUpperHalfPrimes (2 * p₀)

theorem mem_badIntervalUpperPrimes {p₀ p : ℕ} :
    p ∈ badIntervalUpperPrimes p₀ ↔ p₀ < p ∧ p ≤ 2 * p₀ ∧ p.Prime := by
  simp [badIntervalUpperPrimes, factorialUpperHalfPrimes, and_assoc]

/-- A source prime packaged as a nonzero sieve modulus. -/
def badIntervalPrimeSieveModulus (p₀ : ℕ)
    (p : ↥(badIntervalUpperPrimes p₀)) : SieveModulus where
  modulus := p.1
  ne_zero := (mem_badIntervalUpperPrimes.mp p.2).2.2.ne_zero

/-- Remove precisely the residue classes for which the interval contains a
multiple of the current modulus. -/
def badIntervalRestrictions (H : ℕ) :
    (qs : List SieveModulus) → SieveRestrictions qs
  | [] => PUnit.unit
  | q :: qs =>
      (factorialAllowedStartResidues q.modulus H,
        badIntervalRestrictions H qs)

theorem badIntervalRestrictions_proper
    (H : ℕ) : ∀ (qs : List SieveModulus),
      (∀ q ∈ qs, H < q.modulus) →
      SieveRestrictionsProper (badIntervalRestrictions H qs)
  | [], _ => by simp [SieveRestrictionsProper]
  | q :: qs, hmod => by
      constructor
      · exact (card_factorialAllowedStartResidues_le q.modulus H).trans_lt
          (hmod q (by simp))
      · exact badIntervalRestrictions_proper H qs fun r hr =>
          hmod r (by simp [hr])

/-- Literal removed-to-surviving ratio for one prime modulus. -/
def badIntervalRestrictionWeight (H : ℕ) (q : SieveModulus) : ℝ :=
  ((factorialAllowedStartResidues q.modulus H).card : ℝ) /
    (factorialAllowedStartResidues q.modulus H)ᶜ.card

theorem sieveRestrictionRatio_badIntervalRestrictions
    (H : ℕ) : ∀ qs : List SieveModulus,
    sieveRestrictionRatio (badIntervalRestrictions H qs) =
      (qs.map (badIntervalRestrictionWeight H)).prod
  | [] => by simp [sieveRestrictionRatio]
  | q :: qs => by
      simp [badIntervalRestrictions, sieveRestrictionRatio,
        badIntervalRestrictionWeight,
        sieveRestrictionRatio_badIntervalRestrictions H qs]

/-- The source surrogate `H/p` is below the exact one-prime sieve ratio. -/
theorem badIntervalRestrictionWeight_ge
    {H : ℕ} (hH : 1 ≤ H) {q : SieveModulus}
    (hHq : H < q.modulus) :
    (H : ℝ) / q.modulus ≤ badIntervalRestrictionWeight H q := by
  have hcard : (factorialAllowedStartResidues q.modulus H).card = H :=
    card_factorialAllowedStartResidues_eq_of_lt hHq
  have hcomp :
      (factorialAllowedStartResidues q.modulus H)ᶜ.card = q.modulus - H := by
    rw [Finset.card_compl, ZMod.card, hcard]
  have hsubPos : (0 : ℝ) < ((q.modulus - H : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hHq
  rw [badIntervalRestrictionWeight, hcard, hcomp]
  exact div_le_div_of_nonneg_left (by positivity) hsubPos (by
    exact_mod_cast Nat.sub_le q.modulus H)

/-- Natural starts up to `2x` which avoid all source residue classes. -/
def badIntervalLargeSieveSurvivorStarts
    (x p₀ H : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 * x)).filter fun N =>
    ∀ p ∈ badIntervalUpperPrimes p₀,
      (N : ZMod p) ∉ factorialAllowedStartResidues p H

theorem mem_badIntervalLargeSieveSurvivorStarts
    {x p₀ H N : ℕ} :
    N ∈ badIntervalLargeSieveSurvivorStarts x p₀ H ↔
      N ≤ 2 * x ∧ ∀ p ∈ badIntervalUpperPrimes p₀,
        (N : ZMod p) ∉ factorialAllowedStartResidues p H := by
  simp [badIntervalLargeSieveSurvivorStarts]

/-- Smoothness of every interval element supplies all simultaneous residue
avoidance conditions needed by the large sieve. -/
theorem IsNormalizedBadInterval.start_mem_badIntervalLargeSieveSurvivors
    {x N H p₀ k m : ℕ}
    (hnorm : IsNormalizedBadInterval N H p₀ k m)
    (hscale : N + H ≤ 2 * x) :
    N ∈ badIntervalLargeSieveSurvivorStarts x p₀ H := by
  rw [mem_badIntervalLargeSieveSurvivorStarts]
  refine ⟨by omega, ?_⟩
  intro p hp hN
  have hpData := mem_badIntervalUpperPrimes.mp hp
  letI : NeZero p := ⟨hpData.2.2.ne_zero⟩
  rw [factorialAllowedStartResidues, Finset.mem_image] at hN
  obtain ⟨h, hh, hNh⟩ := hN
  have hhBounds := Finset.mem_Icc.mp hh
  have hj : N + h ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hz : ((N + h : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [← hNh]
    ring
  have hpDvd : p ∣ N + h := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact hz
  have hpLe := (isSmooth_iff.mp (hnorm.isSmooth_of_mem hj)).2
    p hpData.2.2 hpDvd
  omega

/-- Avoiding the finite tensor restriction is exactly simultaneous avoidance
of the interval's forbidden start residues. -/
theorem badIntervalRestrictions_avoids_natSieveCube
    (H N : ℕ) : ∀ qs : List SieveModulus,
    SieveAvoids (badIntervalRestrictions H qs) (natSieveCube qs N) ↔
      ∀ q ∈ qs,
        (N : ZMod q.modulus) ∉
          factorialAllowedStartResidues q.modulus H
  | [] => by simp [SieveAvoids]
  | q :: qs => by
      change ((N : ZMod q.modulus) ∉
          factorialAllowedStartResidues q.modulus H ∧
          SieveAvoids (badIntervalRestrictions H qs)
            (natSieveCube qs N)) ↔ _
      simp only [List.forall_mem_cons,
        badIntervalRestrictions_avoids_natSieveCube H N qs]

/-- Every selected product of source prime moduli is at most `(2p₀)^k`. -/
theorem selected_badInterval_moduli_product_le
    {p₀ k : ℕ}
    (s : FixedCardModulusSelections
      (↥(badIntervalUpperPrimes p₀)) k) :
    sieveModulusProduct
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s) ≤
      (2 * p₀) ^ k := by
  simp only [sieveModulusProduct, selectedModuliList, List.map_map]
  change (s.1.toList.map fun p => p.1).prod ≤ (2 * p₀) ^ k
  rw [Finset.prod_map_toList]
  calc
    ∏ p ∈ s.1, p.1 ≤ ∏ _p ∈ s.1, 2 * p₀ := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (mem_badIntervalUpperPrimes.mp p.2).2.1
    _ = (2 * p₀) ^ k := by rw [Finset.prod_const, s.2]

theorem selected_badIntervalRestrictions_proper
    {p₀ H k : ℕ} (hHp₀ : H < p₀)
    (s : FixedCardModulusSelections
      (↥(badIntervalUpperPrimes p₀)) k) :
    SieveRestrictionsProper
      (badIntervalRestrictions H
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
  apply badIntervalRestrictions_proper
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  obtain ⟨p, _hp, rfl⟩ := hq
  exact hHp₀.trans (mem_badIntervalUpperPrimes.mp p.2).1

/-- Exact reindexing of a selected tensor ratio as a product of the literal
one-prime interval weights. -/
theorem sieveRestrictionRatio_selected_badIntervalRestrictions
    (p₀ H k : ℕ)
    (s : FixedCardModulusSelections
      (↥(badIntervalUpperPrimes p₀)) k) :
    sieveRestrictionRatio (badIntervalRestrictions H
      (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) =
      ∏ p ∈ s.1,
        badIntervalRestrictionWeight H
          (badIntervalPrimeSieveModulus p₀ p) := by
  rw [sieveRestrictionRatio_badIntervalRestrictions]
  simp [selectedModuliList]

/-- Each prime in `(p₀,2p₀]` contributes at least `H/(2p₀)` to the exact
removed-to-surviving ratio. -/
theorem badInterval_selectedRestrictionWeight_ge
    {p₀ H : ℕ} (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (p : ↥(badIntervalUpperPrimes p₀)) :
    (H : ℝ) / (2 * p₀) ≤
      badIntervalRestrictionWeight H
        (badIntervalPrimeSieveModulus p₀ p) := by
  have hpData := mem_badIntervalUpperPrimes.mp p.2
  have hHmod : H < (badIntervalPrimeSieveModulus p₀ p).modulus :=
    hHp₀.trans hpData.1
  have hfirst : (H : ℝ) / (2 * p₀) ≤ (H : ℝ) / p.1 :=
    div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast hpData.2.2.pos)
    (by exact_mod_cast hpData.2.1)
  exact hfirst.trans (badIntervalRestrictionWeight_ge hH hHmod)

/-- Fixed-cardinality denominator lower bound for the source residue family. -/
theorem badInterval_selection_ratio_sum_ge
    {p₀ H k : ℕ} (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k ≤
      ∑ s : FixedCardModulusSelections
          (↥(badIntervalUpperPrimes p₀)) k,
        sieveRestrictionRatio (badIntervalRestrictions H
          (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
  have h := fixedCardSelection_weightSum_ge_halfCard
    (Q := ↥(badIntervalUpperPrimes p₀))
    (fun p => badIntervalRestrictionWeight H
      (badIntervalPrimeSieveModulus p₀ p))
    ((H : ℝ) / (2 * p₀)) k (by positivity)
    (badInterval_selectedRestrictionWeight_ge hH hHp₀) hk (by
      simpa only [Fintype.card_coe] using hkcard)
  simpa only [Fintype.card_coe,
    sieveRestrictionRatio_selected_badIntervalRestrictions] using h

/-- Embed the literal start survivor set into the initial interval required
by the global finite large sieve. -/
def badIntervalLargeSieveSurvivorEmbedding (x p₀ H : ℕ) :
    ↥(badIntervalLargeSieveSurvivorStarts x p₀ H) ↪ Fin (2 * x + 1) where
  toFun n := ⟨n.1, Nat.lt_succ_iff.mpr
    (mem_badIntervalLargeSieveSurvivorStarts.mp n.2).1⟩
  inj' := by
    intro n m h
    apply Subtype.ext
    exact congrArg Fin.val h

def badIntervalLargeSieveSurvivorFinset (x p₀ H : ℕ) :
    Finset (Fin (2 * x + 1)) :=
  (badIntervalLargeSieveSurvivorStarts x p₀ H).attach.map
    (badIntervalLargeSieveSurvivorEmbedding x p₀ H)

@[simp]
theorem card_badIntervalLargeSieveSurvivorFinset (x p₀ H : ℕ) :
    (badIntervalLargeSieveSurvivorFinset x p₀ H).card =
      (badIntervalLargeSieveSurvivorStarts x p₀ H).card := by
  simp [badIntervalLargeSieveSurvivorFinset]

theorem badIntervalLargeSieveSurvivorFinset_avoids
    {x p₀ H k : ℕ}
    {n : Fin (2 * x + 1)}
    (hn : n ∈ badIntervalLargeSieveSurvivorFinset x p₀ H)
    (s : FixedCardModulusSelections
      (↥(badIntervalUpperPrimes p₀)) k) :
    SieveAvoids
      (badIntervalRestrictions H
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))
      (natSieveCube
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s) n) := by
  rw [badIntervalLargeSieveSurvivorFinset, Finset.mem_map] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [badIntervalRestrictions_avoids_natSieveCube]
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  obtain ⟨p, _hp, rfl⟩ := hq
  exact (mem_badIntervalLargeSieveSurvivorStarts.mp m.2).2 p.1 p.2

/-- Literal finite Corollary 2.9 for normalized bad-interval starts. -/
theorem badIntervalLargeSieveSurvivor_card_mul_ratio_le
    {x p₀ H k : ℕ} (hHp₀ : H < p₀)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤ 2 * x + 1) :
    (∑ s : FixedCardModulusSelections
        (↥(badIntervalUpperPrimes p₀)) k,
      sieveRestrictionRatio (badIntervalRestrictions H
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))) *
        ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ) ≤
      8 * (2 * x + 1) := by
  have hglobal := montgomery_global_survivor_card_fixedCardSelections
    (Q := ↥(badIntervalUpperPrimes p₀))
    (modulus := badIntervalPrimeSieveModulus p₀)
    (k := k) (K := (2 * p₀) ^ k) (L := 2 * x + 1)
    (fun p q hpq =>
      (Nat.coprime_primes
        (mem_badIntervalUpperPrimes.mp p.2).2.2
        (mem_badIntervalUpperPrimes.mp q.2).2.2).2
          (fun h => hpq (Subtype.ext h)))
    (by omega)
    selected_badInterval_moduli_product_le
    hproduct
    (fun s => badIntervalRestrictions H
      (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))
    (selected_badIntervalRestrictions_proper hHp₀)
    (badIntervalLargeSieveSurvivorFinset x p₀ H)
    (fun n hn s => badIntervalLargeSieveSurvivorFinset_avoids hn s)
  simpa only [card_badIntervalLargeSieveSurvivorFinset, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hglobal

/-- Combined exact finite large-sieve estimate for one `(p₀,H)` fiber. -/
theorem badIntervalLargeSieveSurvivor_card_source_bound
    {x p₀ H k : ℕ} (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤ 2 * x + 1) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
        ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ) ≤
      8 * (2 * x + 1) := by
  calc
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
          ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ)
        ≤ (∑ s : FixedCardModulusSelections
            (↥(badIntervalUpperPrimes p₀)) k,
          sieveRestrictionRatio (badIntervalRestrictions H
            (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))) *
          ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ) :=
      mul_le_mul_of_nonneg_right
        (badInterval_selection_ratio_sum_ge hH hHp₀ hk hkcard)
        (by positivity)
    _ ≤ 8 * (2 * x + 1) :=
      badIntervalLargeSieveSurvivor_card_mul_ratio_le hHp₀ hproduct

/-- Actual comparable-scale normalized starts in one fixed `(p₀,H)` fiber. -/
noncomputable def scaleNormalizedBadIntervalStartsAt
    (x p₀ H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * x)).filter fun N =>
    ∃ k m : ℕ, IsNormalizedBadInterval N H p₀ k m ∧
      x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x

theorem mem_scaleNormalizedBadIntervalStartsAt
    {x p₀ H N : ℕ} :
    N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H ↔
      N < 2 * x ∧ ∃ k m : ℕ,
        IsNormalizedBadInterval N H p₀ k m ∧
          x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x := by
  classical
  simp only [scaleNormalizedBadIntervalStartsAt, Finset.mem_filter,
    Finset.mem_range]

theorem scaleNormalizedBadIntervalStartsAt_subset_survivors
    (x p₀ H : ℕ) :
    scaleNormalizedBadIntervalStartsAt x p₀ H ⊆
      badIntervalLargeSieveSurvivorStarts x p₀ H := by
  intro N hN
  obtain ⟨_hNbound, k, m, hnorm, _hleft, hright⟩ :=
    mem_scaleNormalizedBadIntervalStartsAt.mp hN
  exact hnorm.start_mem_badIntervalLargeSieveSurvivors hright

theorem card_scaleNormalizedBadIntervalStartsAt_le_survivors
    (x p₀ H : ℕ) :
    (scaleNormalizedBadIntervalStartsAt x p₀ H).card ≤
      (badIntervalLargeSieveSurvivorStarts x p₀ H).card :=
  Finset.card_le_card
    (scaleNormalizedBadIntervalStartsAt_subset_survivors x p₀ H)

/-- The union of all normalized intervals in one fixed `(p₀,H)` fiber. -/
def scaleNormalizedBadIntervalUnionAt (x p₀ H : ℕ) : Finset ℕ :=
  (scaleNormalizedBadIntervalStartsAt x p₀ H).biUnion fun N =>
    consecutiveInterval N H

theorem card_scaleNormalizedBadIntervalUnionAt_le
    (x p₀ H : ℕ) :
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
      H * (scaleNormalizedBadIntervalStartsAt x p₀ H).card := by
  classical
  calc
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card
        ≤ ∑ _N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H,
            (consecutiveInterval _N H).card := by
          exact Finset.card_biUnion_le
    _ = ∑ _N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H, H := by
          apply Finset.sum_congr rfl
          intro N hN
          simp [consecutiveInterval]
    _ = H * (scaleNormalizedBadIntervalStartsAt x p₀ H).card := by
          simp [Nat.mul_comm]

/-- Source finite large-sieve bound for the actual interval union in one
fixed `(p₀,H)` fiber. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_sourceWeight_le
    {x p₀ H k : ℕ} (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤ 2 * x + 1) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (8 * (2 * x + 1)) := by
  have hstart := card_scaleNormalizedBadIntervalStartsAt_le_survivors x p₀ H
  have hunion := card_scaleNormalizedBadIntervalUnionAt_le x p₀ H
  have hunionReal :
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) *
          ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ) := by
    exact_mod_cast hunion.trans
      (Nat.mul_le_mul_left H hstart)
  have hbaseNonneg : 0 ≤
      ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k := by positivity
  calc
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ)
        ≤ ((((badIntervalUpperPrimes p₀).card : ℝ) *
            ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
            ((H : ℝ) *
              (badIntervalLargeSieveSurvivorStarts x p₀ H).card) :=
      mul_le_mul_of_nonneg_left hunionReal hbaseNonneg
    _ = (H : ℝ) *
        (((((badIntervalUpperPrimes p₀).card : ℝ) *
            ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
          ((badIntervalLargeSieveSurvivorStarts x p₀ H).card : ℝ)) := by ring
    _ ≤ (H : ℝ) * (8 * (2 * x + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (badIntervalLargeSieveSurvivor_card_source_bound
          hH hHp₀ hk hkcard hproduct) (by positivity)

/-! ## An ambient-start maximal sieve degree -/

/-- The maximal degree for the already-compiled sieve on interval starts,
with ambient interval length `2 * x + 1` and prime scale `2 * p₀`.

Tao's literal source degree instead sieves the cofactor `m` in the smaller
range `m ≤ 2x / p₀²`; it is defined separately below. -/
def badIntervalSieveDegree (x p₀ : ℕ) : ℕ :=
  factorialSieveDegree (2 * x) (2 * p₀)

theorem badIntervalSieveDegree_product_le
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    ((2 * p₀) ^ badIntervalSieveDegree x p₀) *
        ((2 * p₀) ^ badIntervalSieveDegree x p₀) ≤ 2 * x + 1 := by
  simpa only [badIntervalSieveDegree] using
    (factorialSieveDegree_product_le
      (x := 2 * x) (a := 2 * p₀) (by omega : 2 ≤ 2 * p₀))

theorem badIntervalSieveDegree_pos
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hsq : (2 * p₀) ^ 2 ≤ 2 * x + 1) :
    1 ≤ badIntervalSieveDegree x p₀ := by
  simpa only [badIntervalSieveDegree] using
    (factorialSieveDegree_pos
      (x := 2 * x) (a := 2 * p₀) (by omega : 2 ≤ 2 * p₀) hsq)

theorem two_mul_badIntervalSieveDegree_le_card
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log ((2 * x + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ)) :
    2 * badIntervalSieveDegree x p₀ ≤
      (badIntervalUpperPrimes p₀).card := by
  simpa only [badIntervalSieveDegree, badIntervalUpperPrimes] using
    (two_mul_factorialSieveDegree_le_card
      (x := 2 * x) (a := 2 * p₀) (by omega : 2 ≤ 2 * p₀)
      hcard hlarge)

/-- The pinned PNT eventually supplies the prime-cardinality hypothesis at
every doubled bad-interval scale. -/
theorem eventually_card_badIntervalUpperPrimes_lower :
    ∀ᶠ p₀ : ℕ in atTop,
      ((2 * p₀ : ℕ) : ℝ) /
          (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
        ((badIntervalUpperPrimes p₀).card : ℝ) := by
  obtain ⟨a₀, ha₀⟩ :=
    (eventually_atTop.1 eventually_card_factorialUpperHalfPrimes_lower)
  refine eventually_atTop.2 ⟨a₀, ?_⟩
  intro p₀ hp₀
  simpa only [badIntervalUpperPrimes] using ha₀ (2 * p₀) (by omega)

/-- The finite condition-(i) large-sieve estimate with the source degree.
The floor, positivity, product, and cardinality constraints have all been
discharged explicitly. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_canonicalSourceWeight_le
    {x p₀ H : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hsq : (2 * p₀) ^ 2 ≤ 2 * x + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log ((2 * x + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ)) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) /
        (2 * badIntervalSieveDegree x p₀)) ^ badIntervalSieveDegree x p₀ *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (8 * (2 * x + 1)) := by
  exact scaleNormalizedBadIntervalUnionAt_mul_sourceWeight_le
    hH hHp₀
    (badIntervalSieveDegree_pos hp₀ hsq)
    (two_mul_badIntervalSieveDegree_le_card hp₀ hcard hlarge)
    (badIntervalSieveDegree_product_le hp₀)

/-- After the pinned PNT threshold, the canonical source-weight estimate only
retains the two scale inequalities used in the subsequent optimization. -/
theorem eventually_scaleNormalizedBadIntervalUnionAt_mul_canonicalSourceWeight_le :
    ∀ᶠ p₀ : ℕ in atTop, ∀ x H : ℕ,
      1 ≤ H → H < p₀ →
      (2 * p₀) ^ 2 ≤ 2 * x + 1 →
      4 * Real.log ((2 * x + 1 : ℕ) : ℝ) ≤
          ((2 * p₀ : ℕ) : ℝ) →
      ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) /
          (2 * badIntervalSieveDegree x p₀)) ^ badIntervalSieveDegree x p₀ *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) * (8 * (2 * x + 1)) := by
  filter_upwards [eventually_card_badIntervalUpperPrimes_lower,
    eventually_ge_atTop (1 : ℕ)] with p₀ hcard hp₀
  intro x H hH hHp₀ hsq hlarge
  exact scaleNormalizedBadIntervalUnionAt_mul_canonicalSourceWeight_le
    hp₀ hH hHp₀ hsq hcard hlarge

/-! ## The literal source cofactor degree -/

/-- Exact finite cofactor budget furnished by `p₀² m ≤ 2x`. -/
def badIntervalCofactorBudget (x p₀ : ℕ) : ℕ :=
  2 * x / p₀ ^ 2

/-- Tao's floor-defined choice of `k` for sieving the cofactor `m`. -/
def badIntervalCofactorSieveDegree (x p₀ : ℕ) : ℕ :=
  factorialSieveDegree (badIntervalCofactorBudget x p₀) (2 * p₀)

theorem badIntervalCofactorSieveDegree_product_le
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    ((2 * p₀) ^ badIntervalCofactorSieveDegree x p₀) *
        ((2 * p₀) ^ badIntervalCofactorSieveDegree x p₀) ≤
      badIntervalCofactorBudget x p₀ + 1 := by
  simpa only [badIntervalCofactorSieveDegree] using
    (factorialSieveDegree_product_le
      (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
      (by omega : 2 ≤ 2 * p₀))

theorem badIntervalCofactorSieveDegree_pos
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hsq : (2 * p₀) ^ 2 ≤ badIntervalCofactorBudget x p₀ + 1) :
    1 ≤ badIntervalCofactorSieveDegree x p₀ := by
  simpa only [badIntervalCofactorSieveDegree] using
    (factorialSieveDegree_pos
      (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
      (by omega : 2 ≤ 2 * p₀) hsq)

theorem le_badIntervalCofactorSieveDegree_of_power_le
    {x p₀ n : ℕ} (hp₀ : 1 ≤ p₀)
    (hpow : (2 * p₀) ^ (2 * n) ≤ badIntervalCofactorBudget x p₀ + 1) :
    n ≤ badIntervalCofactorSieveDegree x p₀ := by
  simpa only [badIntervalCofactorSieveDegree] using
    (le_factorialSieveDegree_of_power_le
      (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
      (by omega : 2 ≤ 2 * p₀) hpow)

theorem four_le_badIntervalCofactorSieveDegree
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hpow : (2 * p₀) ^ 8 ≤ badIntervalCofactorBudget x p₀ + 1) :
    4 ≤ badIntervalCofactorSieveDegree x p₀ := by
  exact le_badIntervalCofactorSieveDegree_of_power_le hp₀ (by
    simpa only [show 2 * 4 = 8 by norm_num] using hpow)

theorem two_mul_badIntervalCofactorSieveDegree_le_card
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ)) :
    2 * badIntervalCofactorSieveDegree x p₀ ≤
      (badIntervalUpperPrimes p₀).card := by
  simpa only [badIntervalCofactorSieveDegree, badIntervalUpperPrimes] using
    (two_mul_factorialSieveDegree_le_card
      (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
      (by omega : 2 ≤ 2 * p₀) hcard hlarge)

/-- All three finite side conditions for Tao's literal cofactor degree.  The
remaining source-facing step is to transport the two endpoint orientations to
affine residue restrictions on `m`. -/
theorem badIntervalCofactorSieveDegree_constraints
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hsq : (2 * p₀) ^ 2 ≤ badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ)) :
    1 ≤ badIntervalCofactorSieveDegree x p₀ ∧
      2 * badIntervalCofactorSieveDegree x p₀ ≤
        (badIntervalUpperPrimes p₀).card ∧
      ((2 * p₀) ^ badIntervalCofactorSieveDegree x p₀) *
          ((2 * p₀) ^ badIntervalCofactorSieveDegree x p₀) ≤
        badIntervalCofactorBudget x p₀ + 1 := by
  exact ⟨badIntervalCofactorSieveDegree_pos hp₀ hsq,
    two_mul_badIntervalCofactorSieveDegree_le_card hp₀ hcard hlarge,
    badIntervalCofactorSieveDegree_product_le hp₀⟩

end

end Tao2026
