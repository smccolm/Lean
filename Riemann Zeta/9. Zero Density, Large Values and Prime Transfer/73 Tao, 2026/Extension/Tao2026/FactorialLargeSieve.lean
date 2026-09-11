import Tao2026.FactorialSmallIndexCounting

/-!
# The large-sieve branch for Tao's Theorem 1.9

This file isolates the exact finite residue restrictions in the complementary
Section 4 regime.  For fixed factorial index `a` and length `H`, every prime
`a/2 < p ≤ a` forces the interval start into one of at most `H` classes modulo
`p`, equivalently removing at least `p-H` classes.  The resulting fixed-fiber
interval family injects into the literal survivor set to which Corollary 2.9
will be applied.
-/

namespace Tao2026

noncomputable section

open Filter

/-- Complementary source regime after removing bounded lengths and the fixed
small-index case. -/
def factorialLargeSieveIntervalsUpTo (x B : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    B < t.1.2 ∧
      (t.1.2 : ℝ) * Real.log (x + 2) / 100 <
        (chosenFactorialRelationCertificate x t).factorialIndex

theorem mem_factorialLargeSieveIntervalsUpTo
    {x B : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialLargeSieveIntervalsUpTo x B ↔
      B < t.1.2 ∧
        (t.1.2 : ℝ) * Real.log (x + 2) / 100 <
          (chosenFactorialRelationCertificate x t).factorialIndex := by
  simp [factorialLargeSieveIntervalsUpTo]

def factorialLargeSieveEndpointsUpTo (x B : ℕ) : Finset ℕ :=
  (factorialLargeSieveIntervalsUpTo x B).image fun t => t.1.1 + t.1.2

/-- Every nontrivial interval lies in one of the bounded-length, small-index,
or complementary large-sieve families. -/
theorem boundedLength_union_smallIndex_union_largeSieve
    (x B : ℕ) :
    (nontrivialFactorialThreeIntervalsUpTo x).attach =
      factorialBoundedLengthIntervalsUpTo x B ∪
        factorialSmallIndexSourceIntervalsUpTo x ∪
          factorialLargeSieveIntervalsUpTo x B := by
  ext t
  simp only [Finset.mem_attach, true_iff, Finset.mem_union,
    mem_factorialBoundedLengthIntervalsUpTo,
    mem_factorialSmallIndexSourceIntervalsUpTo,
    mem_factorialLargeSieveIntervalsUpTo]
  by_cases hB : t.1.2 ≤ B
  · exact Or.inl (Or.inl hB)
  · by_cases hs :
        ((chosenFactorialRelationCertificate x t).factorialIndex : ℝ) ≤
          (t.1.2 : ℝ) * Real.log (x + 2) / 100
    · exact Or.inl (Or.inr hs)
    · exact Or.inr ⟨Nat.lt_of_not_ge hB, lt_of_not_ge hs⟩

/-- Endpoint images inherit the three-way source decomposition. -/
theorem allFactorialIntervalEndpoints_subset_three_cases
    (x B : ℕ) :
    (nontrivialFactorialThreeIntervalsUpTo x).image (fun t => t.1 + t.2) ⊆
      factorialBoundedLengthEndpointsUpTo x B ∪
        factorialSmallIndexSourceEndpointsUpTo x ∪
          factorialLargeSieveEndpointsUpTo x B := by
  intro n hn
  rw [Finset.mem_image] at hn
  rcases hn with ⟨t, ht, rfl⟩
  have htAttach : (⟨t, ht⟩ : ↥(nontrivialFactorialThreeIntervalsUpTo x)) ∈
      (nontrivialFactorialThreeIntervalsUpTo x).attach := by simp
  rw [boundedLength_union_smallIndex_union_largeSieve x B,
    Finset.mem_union, Finset.mem_union] at htAttach
  rcases htAttach with (htBounded | htSmall) | htLarge
  · rw [Finset.mem_union, Finset.mem_union]
    left
    left
    rw [factorialBoundedLengthEndpointsUpTo, Finset.mem_image]
    exact ⟨⟨t, ht⟩, htBounded, rfl⟩
  · rw [Finset.mem_union, Finset.mem_union]
    left
    right
    rw [factorialSmallIndexSourceEndpointsUpTo, Finset.mem_image]
    exact ⟨⟨t, ht⟩, htSmall, rfl⟩
  · rw [Finset.mem_union, Finset.mem_union]
    right
    rw [factorialLargeSieveEndpointsUpTo, Finset.mem_image]
    exact ⟨⟨t, ht⟩, htLarge, rfl⟩

/-- Exact total-count reduction to the two completed easy families and the
remaining complementary sieve family. -/
theorem nontrivialFactorialThreeCount_le_three_cases (x B : ℕ) :
    nontrivialFactorialThreeCount x ≤
      (factorialBoundedLengthEndpointsUpTo x B).card +
        (factorialSmallIndexSourceEndpointsUpTo x).card +
          (factorialLargeSieveEndpointsUpTo x B).card := by
  rw [← card_nontrivialFactorialThreeNumbersUpTo]
  calc
    (nontrivialFactorialThreeNumbersUpTo x).card ≤
        ((nontrivialFactorialThreeIntervalsUpTo x).image
          (fun t => t.1 + t.2)).card :=
      Finset.card_le_card
        (nontrivialFactorialThreeNumbersUpTo_subset_endpointImage x)
    _ ≤ (factorialBoundedLengthEndpointsUpTo x B ∪
          factorialSmallIndexSourceEndpointsUpTo x ∪
            factorialLargeSieveEndpointsUpTo x B).card :=
      Finset.card_le_card
        (allFactorialIntervalEndpoints_subset_three_cases x B)
    _ ≤ (factorialBoundedLengthEndpointsUpTo x B).card +
        (factorialSmallIndexSourceEndpointsUpTo x).card +
          (factorialLargeSieveEndpointsUpTo x B).card := by
      calc
        _ ≤ (factorialBoundedLengthEndpointsUpTo x B ∪
              factorialSmallIndexSourceEndpointsUpTo x).card +
            (factorialLargeSieveEndpointsUpTo x B).card :=
          Finset.card_union_le _ _
        _ ≤ ((factorialBoundedLengthEndpointsUpTo x B).card +
              (factorialSmallIndexSourceEndpointsUpTo x).card) +
            (factorialLargeSieveEndpointsUpTo x B).card := by
          gcongr
          exact Finset.card_union_le _ _
        _ = _ := by omega

/-- Residue classes available to an interval start when some `N+h` with
`1 ≤ h ≤ H` must be divisible by `p`. -/
def factorialAllowedStartResidues (p H : ℕ) : Finset (ZMod p) :=
  (Finset.Icc 1 H).image fun h : ℕ => -(h : ZMod p)

theorem card_factorialAllowedStartResidues_le (p H : ℕ) :
    (factorialAllowedStartResidues p H).card ≤ H := by
  calc
    (factorialAllowedStartResidues p H).card ≤ (Finset.Icc 1 H).card :=
      Finset.card_image_le
    _ ≤ H := by simp

/-- Thus at least `p-H` residue classes are removed. -/
theorem factorialAllowedStartResidues_compl_card_ge (p H : ℕ) [NeZero p] :
    p - H ≤ (factorialAllowedStartResidues p H)ᶜ.card := by
  classical
  rw [Finset.card_compl, ZMod.card]
  exact Nat.sub_le_sub_left (card_factorialAllowedStartResidues_le p H) p

/-- The pinned prime number theorem supplies the source-order number of
upper-half prime moduli.  The deliberately coarse constant is sufficient for
the simplified large sieve and leaves all floor effects explicit. -/
theorem eventually_card_factorialUpperHalfPrimes_lower :
    ∀ᶠ a : ℕ in atTop,
      (a : ℝ) / (4 * Real.log a) ≤
        ((factorialUpperHalfPrimes a).card : ℝ) := by
  filter_upwards [eventually_nat_factorialUpperHalfTheta_lower,
    eventually_ge_atTop (2 : ℕ)] with a htheta ha
  have hlogpos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hsum :
      ∑ p ∈ factorialUpperHalfPrimes a, Real.log p ≤
        ((factorialUpperHalfPrimes a).card : ℝ) * Real.log a := by
    calc
      ∑ p ∈ factorialUpperHalfPrimes a, Real.log p ≤
          ∑ _p ∈ factorialUpperHalfPrimes a, Real.log a := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log
          (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
          (by exact_mod_cast
            (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
      _ = ((factorialUpperHalfPrimes a).card : ℝ) * Real.log a := by simp
  rw [sum_log_factorialUpperHalfPrimes_eq_theta_sub] at hsum
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogpos)).2
  nlinarith

/-- The upper-half prime moduli are pairwise coprime, as required by
Corollaries 2.8 and 2.9. -/
theorem factorialUpperHalfPrimes_pairwise_coprime (a : ℕ) :
    Set.Pairwise (factorialUpperHalfPrimes a : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes
    (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).2 hpq

/-- Every product of a selected family of upper-half primes is bounded by
the corresponding power of `a`.  Thus `a^k ≤ √x` discharges the product
condition in the simplified large sieve. -/
theorem prod_subset_factorialUpperHalfPrimes_le
    {a : ℕ} {s : Finset ℕ} (hs : s ⊆ factorialUpperHalfPrimes a) :
    ∏ p ∈ s, p ≤ a ^ s.card := by
  calc
    ∏ p ∈ s, p ≤ ∏ _p ∈ s, a := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hs hp)).1).2
    _ = a ^ s.card := by simp

/-- In the complementary regime, every upper-half prime contributes at
least `log(x+2)/400` to the surrogate removed/allowed ratio `(p-H)/H`.
The constants absorb the natural floor in `a/2` and the subtraction of
`H`. -/
theorem factorialSieveSurrogateRatio_ge
    {x a H p : ℕ}
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hp : p ∈ factorialUpperHalfPrimes a) :
    Real.log (x + 2) / 400 ≤ ((p - H : ℕ) : ℝ) / H := by
  have hpBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have ha2p : a < 2 * p := by
    simpa [mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hpBounds.1
  have ha2pReal : (a : ℝ) < 2 * p := by exact_mod_cast ha2p
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hpHReal : (H : ℝ) < p := by
    nlinarith
  have hpH : H ≤ p := by exact_mod_cast hpHReal.le
  rw [Nat.cast_sub hpH]
  apply (le_div_iff₀ hHpos).2
  nlinarith

/-- Removing at most `k` of the largest weights costs at most half of the
available prime moduli when `2k ≤ #Q`.  This is the exact `[-k]` deletion
step used in Tao's Corollary 2.9 application. -/
theorem factorialSieveSurrogateRatio_sum_after_deletion_ge
    {x a H k : ℕ} {D : Finset ℕ}
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hD : D ⊆ factorialUpperHalfPrimes a)
    (hDcard : D.card ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card) :
    ((factorialUpperHalfPrimes a).card : ℝ) / 2 *
        (Real.log (x + 2) / 400) ≤
      ∑ p ∈ factorialUpperHalfPrimes a \ D,
        ((p - H : ℕ) : ℝ) / H := by
  let Q := factorialUpperHalfPrimes a
  change D ⊆ Q at hD
  change 2 * k ≤ Q.card at hkcard
  have hcardEq : (Q \ D).card + D.card = Q.card :=
    Finset.card_sdiff_add_card_eq_card hD
  have hcardNat : Q.card ≤ 2 * (Q \ D).card := by
    omega
  have hcardReal : (Q.card : ℝ) / 2 ≤ ((Q \ D).card : ℝ) := by
    have hcardNat' : (Q.card : ℝ) ≤ 2 * ((Q \ D).card : ℝ) := by
      exact_mod_cast hcardNat
    linarith
  have hLnonneg : 0 ≤ Real.log (x + 2) / 400 := by positivity
  calc
    (Q.card : ℝ) / 2 * (Real.log (x + 2) / 400) ≤
        ((Q \ D).card : ℝ) * (Real.log (x + 2) / 400) :=
      mul_le_mul_of_nonneg_right hcardReal hLnonneg
    _ = ∑ _p ∈ Q \ D, Real.log (x + 2) / 400 := by simp
    _ ≤ ∑ p ∈ Q \ D, ((p - H : ℕ) : ℝ) / H := by
      apply Finset.sum_le_sum
      intro p hp
      exact factorialSieveSurrogateRatio_ge hH hlog hhard
        (Finset.mem_sdiff.mp hp).1

/-- After the PNT cardinal estimate, the deleted surrogate-weight sum has
exactly the scale appearing in equation (cak) of the source. -/
theorem factorialSieveSurrogateRatio_sum_source_scale
    {x a H k : ℕ} {D : Finset ℕ}
    (ha : 2 ≤ a)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hD : D ⊆ factorialUpperHalfPrimes a)
    (hDcard : D.card ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card) :
    (a : ℝ) * Real.log (x + 2) / (3200 * Real.log a) ≤
      ∑ p ∈ factorialUpperHalfPrimes a \ D,
        ((p - H : ℕ) : ℝ) / H := by
  have hlogapos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hLnonneg : 0 ≤ Real.log (x + 2) / 400 := by positivity
  have hhalf : (a : ℝ) / (4 * Real.log a) / 2 ≤
      ((factorialUpperHalfPrimes a).card : ℝ) / 2 := by linarith
  calc
    (a : ℝ) * Real.log (x + 2) / (3200 * Real.log a) =
        ((a : ℝ) / (4 * Real.log a) / 2) *
          (Real.log (x + 2) / 400) := by field_simp; ring
    _ ≤ ((factorialUpperHalfPrimes a).card : ℝ) / 2 *
          (Real.log (x + 2) / 400) :=
      mul_le_mul_of_nonneg_right hhalf hLnonneg
    _ ≤ _ := factorialSieveSurrogateRatio_sum_after_deletion_ge
      hH hlog hhard hD hDcard hkcard

/-- For positive interval length the allowed residue family is nonempty. -/
theorem factorialAllowedStartResidues_nonempty
    (p H : ℕ) [NeZero p] (hH : 1 ≤ H) :
    (factorialAllowedStartResidues p H).Nonempty := by
  refine ⟨-(1 : ZMod p), ?_⟩
  rw [factorialAllowedStartResidues, Finset.mem_image]
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hH⟩, by simp⟩

/-- The surrogate `(p-H)/H` is bounded by the literal ratio of removed to
surviving residue classes.  This connects the elementary source arithmetic
above to the exact weight in Corollaries 2.8 and 2.9. -/
theorem factorialSieveSurrogateRatio_le_actual
    {p H : ℕ} [NeZero p] (hH : 1 ≤ H) :
    ((p - H : ℕ) : ℝ) / H ≤
      ((factorialAllowedStartResidues p H)ᶜ.card : ℝ) /
        (factorialAllowedStartResidues p H).card := by
  have hAllowedPosNat : 0 < (factorialAllowedStartResidues p H).card :=
    (factorialAllowedStartResidues_nonempty p H hH).card_pos
  have hAllowedPos : (0 : ℝ) <
      (factorialAllowedStartResidues p H).card := by
    exact_mod_cast hAllowedPosNat
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hRemoved : ((p - H : ℕ) : ℝ) ≤
      ((factorialAllowedStartResidues p H)ᶜ.card : ℝ) := by
    exact_mod_cast factorialAllowedStartResidues_compl_card_ge p H
  have hAllowed : ((factorialAllowedStartResidues p H).card : ℝ) ≤ H := by
    exact_mod_cast card_factorialAllowedStartResidues_le p H
  rw [div_le_div_iff₀ hHpos hAllowedPos]
  calc
    ((p - H : ℕ) : ℝ) * (factorialAllowedStartResidues p H).card ≤
        ((p - H : ℕ) : ℝ) * H :=
      mul_le_mul_of_nonneg_left hAllowed (Nat.cast_nonneg _)
    _ ≤ ((factorialAllowedStartResidues p H)ᶜ.card : ℝ) * H :=
      mul_le_mul_of_nonneg_right hRemoved hHpos.le

/-- A prime divisor of an interval product divides one actual interval
element. -/
theorem exists_mem_consecutiveInterval_of_prime_dvd_product
    {N H p : ℕ} (hp : p.Prime) (hpdvd : p ∣ consecutiveProduct N H) :
    ∃ k ∈ consecutiveInterval N H, p ∣ k := by
  rw [consecutiveProduct] at hpdvd
  exact (hp.prime.dvd_finsetProd_iff id).mp hpdvd

/-- Exact source congruence restriction: every upper-half prime for the
factorial index places the interval start in the allowed residue set. -/
theorem factorialThree_start_mem_allowedResidues
    {N H a p : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hpMem : p ∈ factorialUpperHalfPrimes a) :
    (N : ZMod p) ∈ factorialAllowedStartResidues p H := by
  have hp : p.Prime := (Finset.mem_filter.mp hpMem).2
  have hpdvd := upperHalfPrime_dvd_consecutiveProduct haData hpMem
  obtain ⟨k, hk, hpk⟩ :=
    exists_mem_consecutiveInterval_of_prime_dvd_product hp hpdvd
  have hkBounds := Finset.mem_Ioc.mp hk
  let h := k - N
  have hh : 1 ≤ h ∧ h ≤ H := by
    dsimp only [h]
    omega
  have hNh : N + h = k := by
    dsimp only [h]
    omega
  have hz : ((N + h : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    simpa only [hNh] using hpk
  rw [factorialAllowedStartResidues, Finset.mem_image]
  refine ⟨h, Finset.mem_Icc.mpr hh, ?_⟩
  symm
  calc
    (N : ZMod p) = ((N + h : ℕ) : ZMod p) - (h : ZMod p) := by
      push_cast
      ring
    _ = -(h : ZMod p) := by rw [hz, zero_sub]

/-- Literal set of starts surviving all upper-half-prime restrictions for
fixed `x,a,H`. -/
def factorialLargeSieveSurvivorStarts (x a H : ℕ) : Finset ℕ :=
  (Finset.Icc 0 x).filter fun N =>
    ∀ p ∈ factorialUpperHalfPrimes a,
      (N : ZMod p) ∈ factorialAllowedStartResidues p H

theorem mem_factorialLargeSieveSurvivorStarts
    {x a H N : ℕ} :
    N ∈ factorialLargeSieveSurvivorStarts x a H ↔
      N ≤ x ∧ ∀ p ∈ factorialUpperHalfPrimes a,
        (N : ZMod p) ∈ factorialAllowedStartResidues p H := by
  simp [factorialLargeSieveSurvivorStarts]

/-- The fixed `(a,H)` fiber of complementary interval witnesses. -/
def factorialLargeSieveIntervalsAt (x B a H : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (factorialLargeSieveIntervalsUpTo x B).filter fun t =>
    (chosenFactorialRelationCertificate x t).factorialIndex = a ∧ t.1.2 = H

theorem mem_factorialLargeSieveIntervalsAt
    {x B a H : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialLargeSieveIntervalsAt x B a H ↔
      t ∈ factorialLargeSieveIntervalsUpTo x B ∧
        (chosenFactorialRelationCertificate x t).factorialIndex = a ∧
        t.1.2 = H := by
  simp [factorialLargeSieveIntervalsAt]

theorem factorialLargeSieveInterval_start_mem_survivors
    {x B a H : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)}
    (ht : t ∈ factorialLargeSieveIntervalsAt x B a H) :
    t.1.1 ∈ factorialLargeSieveSurvivorStarts x a H := by
  have htAt := mem_factorialLargeSieveIntervalsAt.mp ht
  have htBase := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have htFiber := htAt.2
  change c.factorialIndex = a ∧ t.1.2 = H at htFiber
  rw [mem_factorialLargeSieveSurvivorStarts]
  refine ⟨htBase.1, ?_⟩
  intro p hp
  have hp' : p ∈ factorialUpperHalfPrimes c.factorialIndex := by
    simpa only [htFiber.1] using hp
  have hres := factorialThree_start_mem_allowedResidues
    ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩ hp'
  simpa only [htFiber.2] using hres

/-- For fixed `(a,H)`, projection to the interval start is injective. -/
theorem injective_factorialLargeSieveInterval_start
    (x B a H : ℕ) :
    Function.Injective
      (fun t : ↥(factorialLargeSieveIntervalsAt x B a H) => t.1.1.1) := by
  intro t u htu
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact htu
  · have ht := mem_factorialLargeSieveIntervalsAt.mp t.property
    have hu := mem_factorialLargeSieveIntervalsAt.mp u.property
    exact ht.2.2.trans hu.2.2.symm

/-- Exact fixed-fiber reduction to the survivor set counted by the large
sieve. -/
theorem card_factorialLargeSieveIntervalsAt_le_survivors
    (x B a H : ℕ) :
    (factorialLargeSieveIntervalsAt x B a H).card ≤
      (factorialLargeSieveSurvivorStarts x a H).card := by
  let s := factorialLargeSieveIntervalsAt x B a H
  let encode : ↥s → ℕ := fun t => t.1.1.1
  have hinj : Function.Injective encode :=
    injective_factorialLargeSieveInterval_start x B a H
  have himage : s.attach.image encode ⊆
      factorialLargeSieveSurvivorStarts x a H := by
    intro N hN
    rw [Finset.mem_image] at hN
    rcases hN with ⟨t, _ht, rfl⟩
    have htAt : t.1 ∈ factorialLargeSieveIntervalsAt x B a H := by
      simpa only [s] using t.property
    exact factorialLargeSieveInterval_start_mem_survivors htAt
  calc
    (factorialLargeSieveIntervalsAt x B a H).card = s.attach.card := by
      simp [s]
    _ = (s.attach.image encode).card := by
      rw [Finset.card_image_iff.mpr hinj.injOn]
    _ ≤ (factorialLargeSieveSurvivorStarts x a H).card :=
      Finset.card_le_card himage

/-! ## Reassembly of the fixed fibers -/

/-- Complementary intervals obeying supplied global index and length
budgets. -/
def factorialLargeSieveBudgetedIntervalsUpTo
    (x B A G : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (factorialLargeSieveIntervalsUpTo x B).filter fun t =>
    (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
      t.1.2 ≤ G

theorem mem_factorialLargeSieveBudgetedIntervalsUpTo
    {x B A G : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialLargeSieveBudgetedIntervalsUpTo x B A G ↔
      t ∈ factorialLargeSieveIntervalsUpTo x B ∧
        (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
        t.1.2 ≤ G := by
  simp [factorialLargeSieveBudgetedIntervalsUpTo]

def factorialLargeSieveBudgetedEndpointsUpTo
    (x B A G : ℕ) : Finset ℕ :=
  (factorialLargeSieveBudgetedIntervalsUpTo x B A G).image fun t =>
    t.1.1 + t.1.2

/-- The budgeted complementary family is exactly the union of its fixed
`(a,H)` fibers. -/
theorem factorialLargeSieveBudgetedIntervalsUpTo_eq_biUnion
    (x B A G : ℕ) :
    factorialLargeSieveBudgetedIntervalsUpTo x B A G =
      (Finset.Icc 1 A).biUnion fun a =>
        (Finset.Icc 2 G).biUnion fun H =>
          factorialLargeSieveIntervalsAt x B a H := by
  ext t
  constructor
  · intro ht
    have hb := mem_factorialLargeSieveBudgetedIntervalsUpTo.mp ht
    let c := chosenFactorialRelationCertificate x t
    have hspec := chosenFactorialRelationCertificate_spec x t
    change c.Certifies t.1.1 t.1.2 at hspec
    have hbBudget := hb.2
    change c.factorialIndex ≤ A ∧ t.1.2 ≤ G at hbBudget
    rw [Finset.mem_biUnion]
    refine ⟨c.factorialIndex, Finset.mem_Icc.mpr ⟨hspec.1, hbBudget.1⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨t.1.2, Finset.mem_Icc.mpr
      ⟨(mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property).2.1,
        hbBudget.2⟩, ?_⟩
    rw [mem_factorialLargeSieveIntervalsAt]
    exact ⟨hb.1, rfl, rfl⟩
  · intro ht
    rw [Finset.mem_biUnion] at ht
    rcases ht with ⟨a, ha, ht⟩
    rw [Finset.mem_biUnion] at ht
    rcases ht with ⟨H, hH, ht⟩
    have htAt := mem_factorialLargeSieveIntervalsAt.mp ht
    rw [mem_factorialLargeSieveBudgetedIntervalsUpTo]
    exact ⟨htAt.1, htAt.2.1.le.trans (Finset.mem_Icc.mp ha).2,
      htAt.2.2.le.trans (Finset.mem_Icc.mp hH).2⟩

/-- Exact sum of survivor counts controlling the budgeted endpoint image. -/
theorem card_factorialLargeSieveBudgetedEndpointsUpTo_le_sum_survivors
    (x B A G : ℕ) :
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤
      ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        (factorialLargeSieveSurvivorStarts x a H).card := by
  calc
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤
        (factorialLargeSieveBudgetedIntervalsUpTo x B A G).card :=
      Finset.card_image_le
    _ = ((Finset.Icc 1 A).biUnion fun a =>
        (Finset.Icc 2 G).biUnion fun H =>
          factorialLargeSieveIntervalsAt x B a H).card := by
      rw [factorialLargeSieveBudgetedIntervalsUpTo_eq_biUnion]
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((Finset.Icc 2 G).biUnion fun H =>
          factorialLargeSieveIntervalsAt x B a H).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        (factorialLargeSieveIntervalsAt x B a H).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        (factorialLargeSieveSurvivorStarts x a H).card := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro H hH
      exact card_factorialLargeSieveIntervalsAt_le_survivors x B a H

/-- Uniform survivor estimates reassemble with only the number of possible
`a` and `H` values as a loss. -/
theorem card_factorialLargeSieveBudgetedEndpointsUpTo_le
    (x B A G S : ℕ)
    (hS : ∀ a ∈ Finset.Icc 1 A, ∀ H ∈ Finset.Icc 2 G,
      (factorialLargeSieveSurvivorStarts x a H).card ≤ S) :
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤ A * G * S := by
  calc
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤
        ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
          (factorialLargeSieveSurvivorStarts x a H).card :=
      card_factorialLargeSieveBudgetedEndpointsUpTo_le_sum_survivors x B A G
    _ ≤ ∑ _a ∈ Finset.Icc 1 A, ∑ _H ∈ Finset.Icc 2 G, S := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum fun H hH => hS a ha H hH
    _ = (Finset.Icc 1 A).card * ((Finset.Icc 2 G).card * S) := by simp
    _ ≤ A * (G * S) := by
      gcongr <;> simp
    _ = A * G * S := by ring

end

end Tao2026
