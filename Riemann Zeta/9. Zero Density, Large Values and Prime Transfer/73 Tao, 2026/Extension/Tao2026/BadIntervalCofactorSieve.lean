import Tao2026.BadIntervalLongSieve

/-!
# Large sieve on Tao's normalized-interval cofactor

This module transports the two possible square endpoints
`p₀²m = N+1` and `p₀²m = N+H` to affine forbidden residue classes for
`m`.  This is the source-faithful reduction from the ambient interval scale to
the smaller cofactor budget `m ≤ 2x/p₀²`.
-/

open Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

inductive BadIntervalEndpointOrientation
  | first
  | second
  deriving DecidableEq, Fintype

/-- A totalized inverse of `p₀²` modulo `q`.  On the source prime moduli
the guarded coprimality branch is always selected. -/
def badIntervalCofactorInverse (p₀ q : ℕ) : ZMod q :=
  if h : (p₀ ^ 2).Coprime q then
    ((ZMod.unitOfCoprime (p₀ ^ 2) h)⁻¹ : (ZMod q)ˣ)
  else 0

/-- The residue of `m` which makes the offset `l` divisible by `q`. -/
def badIntervalCofactorForbiddenResidue
    (o : BadIntervalEndpointOrientation) (p₀ q l : ℕ) : ZMod q :=
  match o with
  | .first => -(badIntervalCofactorInverse p₀ q * (l : ZMod q))
  | .second => badIntervalCofactorInverse p₀ q * (l : ZMod q)

/-- The `H` affine forbidden classes for one endpoint orientation. -/
def badIntervalCofactorForbiddenResidues
    (o : BadIntervalEndpointOrientation) (p₀ q H : ℕ) : Finset (ZMod q) :=
  (Finset.range H).image (badIntervalCofactorForbiddenResidue o p₀ q)

theorem isUnit_badIntervalCofactorCoefficient
    {p₀ q : ℕ} (hp₀ : 0 < p₀) (hp₀q : p₀ < q) (hq : q.Prime) :
    IsUnit ((p₀ : ZMod q) ^ 2) := by
  rw [← Nat.cast_pow, ZMod.isUnit_iff_coprime]
  have hcop : p₀.Coprime q := Nat.coprime_comm.mpr
    ((hq.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt hp₀ hp₀q))
  exact hcop.pow_left 2

theorem coprime_badIntervalCofactorCoefficient
    {p₀ q : ℕ} (hp₀ : 0 < p₀) (hp₀q : p₀ < q) (hq : q.Prime) :
    (p₀ ^ 2).Coprime q := by
  have hcop : p₀.Coprime q := Nat.coprime_comm.mpr
    ((hq.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt hp₀ hp₀q))
  exact hcop.pow_left 2

theorem isUnit_badIntervalCofactorInverse
    {p₀ q : ℕ} (hp₀ : 0 < p₀) (hp₀q : p₀ < q) (hq : q.Prime) :
    IsUnit (badIntervalCofactorInverse p₀ q) := by
  rw [badIntervalCofactorInverse,
    dif_pos (coprime_badIntervalCofactorCoefficient hp₀ hp₀q hq)]
  exact Units.isUnit _

theorem card_badIntervalCofactorForbiddenResidues
    {o : BadIntervalEndpointOrientation} {p₀ q H : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀) (hp₀q : p₀ < q) (hq : q.Prime) :
    (badIntervalCofactorForbiddenResidues o p₀ q H).card = H := by
  rw [badIntervalCofactorForbiddenResidues, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have haLt : a < q := (Finset.mem_range.mp ha).trans (hHp₀.trans hp₀q)
    have hbLt : b < q := (Finset.mem_range.mp hb).trans (hHp₀.trans hp₀q)
    have hu := isUnit_badIntervalCofactorInverse hp₀ hp₀q hq
    have hcast : (a : ZMod q) = (b : ZMod q) := by
      cases o with
      | first =>
          apply hu.mul_left_cancel
          simpa only [badIntervalCofactorForbiddenResidue, neg_inj] using hab
      | second =>
          apply hu.mul_left_cancel
          simpa only [badIntervalCofactorForbiddenResidue] using hab
    have hmod := (ZMod.natCast_eq_natCast_iff' a b q).mp hcast
    simpa only [Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] using hmod

/-- Tensor restrictions after the affine endpoint change of variables. -/
def badIntervalCofactorRestrictions
    (o : BadIntervalEndpointOrientation) (p₀ H : ℕ) :
    (qs : List SieveModulus) → SieveRestrictions qs
  | [] => PUnit.unit
  | q :: qs =>
      (badIntervalCofactorForbiddenResidues o p₀ q.modulus H,
        badIntervalCofactorRestrictions o p₀ H qs)

theorem badIntervalCofactorRestrictions_proper
    (o : BadIntervalEndpointOrientation) {p₀ H : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀) : ∀ (qs : List SieveModulus),
      (∀ q ∈ qs, p₀ < q.modulus ∧ q.modulus.Prime) →
      SieveRestrictionsProper (badIntervalCofactorRestrictions o p₀ H qs)
  | [], _ => by simp [SieveRestrictionsProper]
  | q :: qs, hmod => by
      constructor
      · change (badIntervalCofactorForbiddenResidues
          o p₀ q.modulus H).card < q.modulus
        rw [card_badIntervalCofactorForbiddenResidues hp₀ hHp₀
          (hmod q (by simp)).1 (hmod q (by simp)).2]
        exact hHp₀.trans (hmod q (by simp)).1
      · exact badIntervalCofactorRestrictions_proper o hp₀ hHp₀ qs fun r hr =>
          hmod r (by simp [hr])

/-- The affine change of variables preserves every one-prime ratio and hence
the full tensor restriction ratio. -/
theorem sieveRestrictionRatio_badIntervalCofactorRestrictions
    (o : BadIntervalEndpointOrientation) {p₀ H : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀) : ∀ (qs : List SieveModulus),
      (∀ q ∈ qs, p₀ < q.modulus ∧ q.modulus.Prime) →
      sieveRestrictionRatio (badIntervalCofactorRestrictions o p₀ H qs) =
        sieveRestrictionRatio (badIntervalRestrictions H qs)
  | [], _ => by simp [sieveRestrictionRatio]
  | q :: qs, hmod => by
      have hq := hmod q (by simp)
      have hcardC := card_badIntervalCofactorForbiddenResidues (o := o)
        hp₀ hHp₀ hq.1 hq.2
      have hcardS := card_factorialAllowedStartResidues_eq_of_lt
        (hHp₀.trans hq.1)
      have hcompC :
          (badIntervalCofactorForbiddenResidues o p₀ q.modulus H)ᶜ.card =
            q.modulus - H := by
        rw [Finset.card_compl, ZMod.card, hcardC]
      have hcompS :
          (factorialAllowedStartResidues q.modulus H)ᶜ.card =
            q.modulus - H := by
        rw [Finset.card_compl, ZMod.card, hcardS]
      simp only [badIntervalCofactorRestrictions, badIntervalRestrictions,
        sieveRestrictionRatio]
      rw [hcardC, hcardS, hcompC, hcompS]
      rw [sieveRestrictionRatio_badIntervalCofactorRestrictions o hp₀ hHp₀ qs
        (fun r hr => hmod r (by simp [hr]))]

theorem mul_badIntervalCofactorInverse
    {p₀ q : ℕ} (hp₀ : 0 < p₀) (hp₀q : p₀ < q) (hq : q.Prime) :
    ((p₀ : ZMod q) ^ 2) * badIntervalCofactorInverse p₀ q = 1 := by
  have hcop := coprime_badIntervalCofactorCoefficient hp₀ hp₀q hq
  rw [badIntervalCofactorInverse, dif_pos hcop, ← Nat.cast_pow]
  let u := ZMod.unitOfCoprime (p₀ ^ 2) hcop
  have hu := congrArg (fun v : (ZMod q)ˣ => (v : ZMod q)) (mul_inv_cancel u)
  simpa only [Units.val_mul, ZMod.coe_unitOfCoprime, Units.val_one] using hu

theorem badIntervalCofactorRestrictions_avoids_natSieveCube
    (o : BadIntervalEndpointOrientation) (p₀ H m : ℕ) :
    ∀ qs : List SieveModulus,
      SieveAvoids (badIntervalCofactorRestrictions o p₀ H qs)
          (natSieveCube qs m) ↔
        ∀ q ∈ qs, (m : ZMod q.modulus) ∉
          badIntervalCofactorForbiddenResidues o p₀ q.modulus H
  | [] => by simp [SieveAvoids]
  | q :: qs => by
      change ((m : ZMod q.modulus) ∉
          badIntervalCofactorForbiddenResidues o p₀ q.modulus H ∧
          SieveAvoids (badIntervalCofactorRestrictions o p₀ H qs)
            (natSieveCube qs m)) ↔ _
      simp only [List.forall_mem_cons,
        badIntervalCofactorRestrictions_avoids_natSieveCube o p₀ H m qs]

/-- Cofactors in Tao's exact finite range which survive one endpoint-oriented
family of affine restrictions. -/
def badIntervalCofactorSurvivors
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (badIntervalCofactorBudget x p₀)).filter fun m =>
    ∀ p ∈ badIntervalUpperPrimes p₀,
      (m : ZMod p) ∉ badIntervalCofactorForbiddenResidues o p₀ p H

theorem mem_badIntervalCofactorSurvivors
    {o : BadIntervalEndpointOrientation} {x p₀ H m : ℕ} :
    m ∈ badIntervalCofactorSurvivors o x p₀ H ↔
      m ≤ badIntervalCofactorBudget x p₀ ∧
      ∀ p ∈ badIntervalUpperPrimes p₀,
        (m : ZMod p) ∉ badIntervalCofactorForbiddenResidues o p₀ p H := by
  simp [badIntervalCofactorSurvivors]

/-- A normalized square-endpoint cofactor lies in the source range and avoids
the affine restrictions belonging to its endpoint orientation. -/
theorem IsNormalizedBadInterval.cofactor_mem_badIntervalCofactorSurvivors
    {o : BadIntervalEndpointOrientation} {x N H p₀ k m : ℕ}
    (hnorm : IsNormalizedBadInterval N H p₀ k m)
    (hscale : N + H ≤ 2 * x)
    (horient : match o with
      | .first => k = N + 1
      | .second => k = N + H) :
    m ∈ badIntervalCofactorSurvivors o x p₀ H := by
  obtain ⟨_hH, _hbad, hp₀prime, hHp₀, _hpMax, hkMem, _hmSmooth,
    hkEq, _hkEndpoint, _hpow⟩ := hnorm
  rw [mem_badIntervalCofactorSurvivors]
  constructor
  · apply (Nat.le_div_iff_mul_le (pow_pos hp₀prime.pos 2)).2
    have hkLe : k ≤ 2 * x :=
      (Finset.mem_Ioc.mp hkMem).2.trans hscale
    simpa only [hkEq, Nat.mul_comm] using hkLe
  · intro q hq hmForbidden
    have hqData := mem_badIntervalUpperPrimes.mp hq
    letI : NeZero q := ⟨hqData.2.2.ne_zero⟩
    rw [badIntervalCofactorForbiddenResidues, Finset.mem_image] at hmForbidden
    obtain ⟨l, hl, hml⟩ := hmForbidden
    have hlH : l < H := Finset.mem_range.mp hl
    have hmulInv := mul_badIntervalCofactorInverse hp₀prime.pos hqData.1 hqData.2.2
    cases o with
    | first =>
        change k = N + 1 at horient
        have hj : k + l ∈ consecutiveInterval N H := by
          simp only [consecutiveInterval, Finset.mem_Ioc]
          omega
        have hz : ((k + l : ℕ) : ZMod q) = 0 := by
          push_cast
          rw [hkEq, Nat.cast_mul, Nat.cast_pow, ← hml]
          simp only [badIntervalCofactorForbiddenResidue]
          rw [mul_neg, ← mul_assoc, hmulInv, one_mul]
          ring
        have hqDvd : q ∣ k + l := by
          rw [← ZMod.natCast_eq_zero_iff]
          exact hz
        have hqLe := (isSmooth_iff.mp
          (intervalElement_isSmooth_largestPrime _hpMax hj)).2
          q hqData.2.2 hqDvd
        omega
    | second =>
        change k = N + H at horient
        have hlk : l ≤ k := by
          omega
        have hj : k - l ∈ consecutiveInterval N H := by
          simp only [consecutiveInterval, Finset.mem_Ioc]
          omega
        have hkCast : (k : ZMod q) = (l : ZMod q) := by
          rw [hkEq, Nat.cast_mul, Nat.cast_pow, ← hml]
          simp only [badIntervalCofactorForbiddenResidue]
          rw [← mul_assoc, hmulInv, one_mul]
        have hz : ((k - l : ℕ) : ZMod q) = 0 := by
          rw [Nat.cast_sub hlk, hkCast, sub_self]
        have hqDvd : q ∣ k - l := by
          rw [← ZMod.natCast_eq_zero_iff]
          exact hz
        have hqLe := (isSmooth_iff.mp
          (intervalElement_isSmooth_largestPrime _hpMax hj)).2
          q hqData.2.2 hqDvd
        omega

theorem selected_badIntervalCofactorRestrictions_proper
    (o : BadIntervalEndpointOrientation) {p₀ H k : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀)
    (s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k) :
    SieveRestrictionsProper
      (badIntervalCofactorRestrictions o p₀ H
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
  apply badIntervalCofactorRestrictions_proper o hp₀ hHp₀
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  obtain ⟨p, _hp, rfl⟩ := hq
  exact ⟨(mem_badIntervalUpperPrimes.mp p.2).1,
    (mem_badIntervalUpperPrimes.mp p.2).2.2⟩

theorem sieveRestrictionRatio_selected_badIntervalCofactorRestrictions
    (o : BadIntervalEndpointOrientation) {p₀ H k : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀)
    (s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k) :
    sieveRestrictionRatio
        (badIntervalCofactorRestrictions o p₀ H
          (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) =
      sieveRestrictionRatio
        (badIntervalRestrictions H
          (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
  apply sieveRestrictionRatio_badIntervalCofactorRestrictions o hp₀ hHp₀
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  obtain ⟨p, _hp, rfl⟩ := hq
  exact ⟨(mem_badIntervalUpperPrimes.mp p.2).1,
    (mem_badIntervalUpperPrimes.mp p.2).2.2⟩

theorem badIntervalCofactor_selection_ratio_sum_ge
    (o : BadIntervalEndpointOrientation) {p₀ H k : ℕ}
    (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k ≤
      ∑ s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k,
        sieveRestrictionRatio
          (badIntervalCofactorRestrictions o p₀ H
            (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
  calc
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k ≤
        ∑ s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k,
          sieveRestrictionRatio
            (badIntervalRestrictions H
              (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) :=
      badInterval_selection_ratio_sum_ge hH hHp₀ hk hkcard
    _ = ∑ s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k,
          sieveRestrictionRatio
            (badIntervalCofactorRestrictions o p₀ H
              (selectedModuliList (badIntervalPrimeSieveModulus p₀) s)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact (sieveRestrictionRatio_selected_badIntervalCofactorRestrictions
        o (by omega : 0 < p₀) hHp₀ s).symm

def badIntervalCofactorSurvivorEmbedding
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) :
    ↥(badIntervalCofactorSurvivors o x p₀ H) ↪
      Fin (badIntervalCofactorBudget x p₀ + 1) where
  toFun m := ⟨m.1, Nat.lt_succ_iff.mpr
    (mem_badIntervalCofactorSurvivors.mp m.2).1⟩
  inj' := by
    intro m n h
    apply Subtype.ext
    exact congrArg Fin.val h

def badIntervalCofactorSurvivorFinset
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) :
    Finset (Fin (badIntervalCofactorBudget x p₀ + 1)) :=
  (badIntervalCofactorSurvivors o x p₀ H).attach.map
    (badIntervalCofactorSurvivorEmbedding o x p₀ H)

@[simp]
theorem card_badIntervalCofactorSurvivorFinset
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) :
    (badIntervalCofactorSurvivorFinset o x p₀ H).card =
      (badIntervalCofactorSurvivors o x p₀ H).card := by
  simp [badIntervalCofactorSurvivorFinset]

theorem badIntervalCofactorSurvivorFinset_avoids
    {o : BadIntervalEndpointOrientation} {x p₀ H k : ℕ}
    {m : Fin (badIntervalCofactorBudget x p₀ + 1)}
    (hm : m ∈ badIntervalCofactorSurvivorFinset o x p₀ H)
    (s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k) :
    SieveAvoids
      (badIntervalCofactorRestrictions o p₀ H
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))
      (natSieveCube
        (selectedModuliList (badIntervalPrimeSieveModulus p₀) s) m) := by
  rw [badIntervalCofactorSurvivorFinset, Finset.mem_map] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  rw [badIntervalCofactorRestrictions_avoids_natSieveCube]
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  obtain ⟨p, _hp, rfl⟩ := hq
  exact (mem_badIntervalCofactorSurvivors.mp n.2).2 p.1 p.2

/-- Loss-free global Corollary 2.9 on Tao's cofactor range. -/
theorem badIntervalCofactorSurvivor_card_mul_ratio_le
    {o : BadIntervalEndpointOrientation} {x p₀ H k : ℕ}
    (hp₀ : 0 < p₀) (hHp₀ : H < p₀)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1) :
    (∑ s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k,
      sieveRestrictionRatio
        (badIntervalCofactorRestrictions o p₀ H
          (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))) *
        ((badIntervalCofactorSurvivors o x p₀ H).card : ℝ) ≤
      8 * (badIntervalCofactorBudget x p₀ + 1) := by
  have hglobal := montgomery_global_survivor_card_fixedCardSelections
    (Q := ↥(badIntervalUpperPrimes p₀))
    (modulus := badIntervalPrimeSieveModulus p₀)
    (k := k) (K := (2 * p₀) ^ k)
    (L := badIntervalCofactorBudget x p₀ + 1)
    (fun p q hpq =>
      (Nat.coprime_primes
        (mem_badIntervalUpperPrimes.mp p.2).2.2
        (mem_badIntervalUpperPrimes.mp q.2).2.2).2
          (fun h => hpq (Subtype.ext h)))
    (by omega)
    selected_badInterval_moduli_product_le
    hproduct
    (fun s => badIntervalCofactorRestrictions o p₀ H
      (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))
    (selected_badIntervalCofactorRestrictions_proper o hp₀ hHp₀)
    (badIntervalCofactorSurvivorFinset o x p₀ H)
    (fun m hm s => badIntervalCofactorSurvivorFinset_avoids hm s)
  simpa only [card_badIntervalCofactorSurvivorFinset, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hglobal

/-- The source-weighted cofactor survivor estimate for either endpoint. -/
theorem badIntervalCofactorSurvivor_card_source_bound
    {o : BadIntervalEndpointOrientation} {x p₀ H k : ℕ}
    (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
        ((badIntervalCofactorSurvivors o x p₀ H).card : ℝ) ≤
      8 * (badIntervalCofactorBudget x p₀ + 1) := by
  calc
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
          ((badIntervalCofactorSurvivors o x p₀ H).card : ℝ) ≤
        (∑ s : FixedCardModulusSelections (↥(badIntervalUpperPrimes p₀)) k,
          sieveRestrictionRatio
            (badIntervalCofactorRestrictions o p₀ H
              (selectedModuliList (badIntervalPrimeSieveModulus p₀) s))) *
          ((badIntervalCofactorSurvivors o x p₀ H).card : ℝ) :=
      mul_le_mul_of_nonneg_right
        (badIntervalCofactor_selection_ratio_sum_ge o hH hHp₀ hk hkcard)
        (by positivity)
    _ ≤ 8 * (badIntervalCofactorBudget x p₀ + 1) :=
      badIntervalCofactorSurvivor_card_mul_ratio_le
        (by omega : 0 < p₀) hHp₀ hproduct

/-- The start determined by a cofactor and one of the two normalized endpoint
orientations. -/
def badIntervalCofactorStart
    (o : BadIntervalEndpointOrientation) (p₀ H m : ℕ) : ℕ :=
  match o with
  | .first => p₀ ^ 2 * m - 1
  | .second => p₀ ^ 2 * m - H

/-- Intervals generated by all source-range cofactor survivors in one
orientation. -/
def badIntervalCofactorOrientationCover
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) : Finset ℕ :=
  (badIntervalCofactorSurvivors o x p₀ H).biUnion fun m =>
    consecutiveInterval (badIntervalCofactorStart o p₀ H m) H

theorem card_badIntervalCofactorOrientationCover_le
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) :
    (badIntervalCofactorOrientationCover o x p₀ H).card ≤
      H * (badIntervalCofactorSurvivors o x p₀ H).card := by
  classical
  calc
    (badIntervalCofactorOrientationCover o x p₀ H).card ≤
        ∑ _m ∈ badIntervalCofactorSurvivors o x p₀ H,
          (consecutiveInterval (badIntervalCofactorStart o p₀ H _m) H).card := by
      exact Finset.card_biUnion_le
    _ = ∑ _m ∈ badIntervalCofactorSurvivors o x p₀ H, H := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [consecutiveInterval]
    _ = H * (badIntervalCofactorSurvivors o x p₀ H).card := by
      simp [Nat.mul_comm]

/-- The actual fixed-`(p₀,H)` normalized union is covered by the two
source-cofactor survivor families. -/
theorem scaleNormalizedBadIntervalUnionAt_subset_cofactorCovers
    (x p₀ H : ℕ) :
    scaleNormalizedBadIntervalUnionAt x p₀ H ⊆
      badIntervalCofactorOrientationCover .first x p₀ H ∪
        badIntervalCofactorOrientationCover .second x p₀ H := by
  classical
  intro n hn
  rw [scaleNormalizedBadIntervalUnionAt, Finset.mem_biUnion] at hn
  obtain ⟨N, hN, hn⟩ := hn
  obtain ⟨_hNbound, k, m, hnorm, _hleft, hscale⟩ :=
    mem_scaleNormalizedBadIntervalStartsAt.mp hN
  have hnorm' := hnorm
  obtain ⟨_hH, _hbad, _hp, _hHp, _hpMax, _hkMem, _hmSmooth,
    hkEq, hkEndpoint, _hpow⟩ := hnorm
  rcases hkEndpoint with hkFirst | hkSecond
  · have hm : m ∈ badIntervalCofactorSurvivors .first x p₀ H :=
      hnorm'.cofactor_mem_badIntervalCofactorSurvivors hscale hkFirst
    have hstart : badIntervalCofactorStart .first p₀ H m = N := by
      simp only [badIntervalCofactorStart]
      omega
    apply Finset.mem_union_left
    rw [badIntervalCofactorOrientationCover, Finset.mem_biUnion]
    exact ⟨m, hm, by simpa only [hstart] using hn⟩
  · have hm : m ∈ badIntervalCofactorSurvivors .second x p₀ H :=
      hnorm'.cofactor_mem_badIntervalCofactorSurvivors hscale hkSecond
    have hstart : badIntervalCofactorStart .second p₀ H m = N := by
      simp only [badIntervalCofactorStart]
      omega
    apply Finset.mem_union_right
    rw [badIntervalCofactorOrientationCover, Finset.mem_biUnion]
    exact ⟨m, hm, by simpa only [hstart] using hn⟩

theorem card_scaleNormalizedBadIntervalUnionAt_le_cofactorSurvivors
    (x p₀ H : ℕ) :
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
      H * ((badIntervalCofactorSurvivors .first x p₀ H).card +
        (badIntervalCofactorSurvivors .second x p₀ H).card) := by
  calc
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
        (badIntervalCofactorOrientationCover .first x p₀ H ∪
          badIntervalCofactorOrientationCover .second x p₀ H).card :=
      Finset.card_le_card
        (scaleNormalizedBadIntervalUnionAt_subset_cofactorCovers x p₀ H)
    _ ≤ (badIntervalCofactorOrientationCover .first x p₀ H).card +
        (badIntervalCofactorOrientationCover .second x p₀ H).card :=
      Finset.card_union_le _ _
    _ ≤ H * (badIntervalCofactorSurvivors .first x p₀ H).card +
        H * (badIntervalCofactorSurvivors .second x p₀ H).card :=
      Nat.add_le_add
        (card_badIntervalCofactorOrientationCover_le .first x p₀ H)
        (card_badIntervalCofactorOrientationCover_le .second x p₀ H)
    _ = H * ((badIntervalCofactorSurvivors .first x p₀ H).card +
        (badIntervalCofactorSurvivors .second x p₀ H).card) := by
      rw [Nat.mul_add]

theorem card_badIntervalCofactorSurvivors_le_budget
    (o : BadIntervalEndpointOrientation) (x p₀ H : ℕ) :
    (badIntervalCofactorSurvivors o x p₀ H).card ≤
      badIntervalCofactorBudget x p₀ + 1 := by
  calc
    (badIntervalCofactorSurvivors o x p₀ H).card ≤
        (Finset.Icc 0 (badIntervalCofactorBudget x p₀)).card := by
      exact Finset.card_filter_le _ _
    _ = badIntervalCofactorBudget x p₀ + 1 := by simp

/-- The unsieved cofactor-cover estimate used for the finite small-degree
(equivalently large-`p₀`) branch. -/
theorem card_scaleNormalizedBadIntervalUnionAt_le_two_mul_budget
    (x p₀ H : ℕ) :
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
      2 * H * (badIntervalCofactorBudget x p₀ + 1) := by
  calc
    (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
        H * ((badIntervalCofactorSurvivors .first x p₀ H).card +
          (badIntervalCofactorSurvivors .second x p₀ H).card) :=
      card_scaleNormalizedBadIntervalUnionAt_le_cofactorSurvivors x p₀ H
    _ ≤ H * ((badIntervalCofactorBudget x p₀ + 1) +
          (badIntervalCofactorBudget x p₀ + 1)) := by
      gcongr
      · exact card_badIntervalCofactorSurvivors_le_budget .first x p₀ H
      · exact card_badIntervalCofactorSurvivors_le_budget .second x p₀ H
    _ = 2 * H * (badIntervalCofactorBudget x p₀ + 1) := by ring

/-- Source-faithful fixed-fiber interval-union estimate: the ambient factor is
`2x/p₀²+1`, and the factor `16` accounts for the two endpoint orientations. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
    {x p₀ H k : ℕ} (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  let W : ℝ := ((((badIntervalUpperPrimes p₀).card : ℝ) *
    ((H : ℝ) / (2 * p₀))) / (2 * k)) ^ k
  have hcover := card_scaleNormalizedBadIntervalUnionAt_le_cofactorSurvivors x p₀ H
  have hcoverReal :
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) *
          (((badIntervalCofactorSurvivors .first x p₀ H).card : ℝ) +
           ((badIntervalCofactorSurvivors .second x p₀ H).card : ℝ)) := by
    exact_mod_cast hcover
  have hfirst : W *
      ((badIntervalCofactorSurvivors .first x p₀ H).card : ℝ) ≤
      8 * (badIntervalCofactorBudget x p₀ + 1) := by
    exact badIntervalCofactorSurvivor_card_source_bound
      hH hHp₀ hk hkcard hproduct
  have hsecond : W *
      ((badIntervalCofactorSurvivors .second x p₀ H).card : ℝ) ≤
      8 * (badIntervalCofactorBudget x p₀ + 1) := by
    exact badIntervalCofactorSurvivor_card_source_bound
      hH hHp₀ hk hkcard hproduct
  have hW : 0 ≤ W := by positivity
  change W * ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤ _
  calc
    W * ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        W * ((H : ℝ) *
          (((badIntervalCofactorSurvivors .first x p₀ H).card : ℝ) +
           ((badIntervalCofactorSurvivors .second x p₀ H).card : ℝ))) :=
      mul_le_mul_of_nonneg_left hcoverReal hW
    _ = (H : ℝ) *
        (W * ((badIntervalCofactorSurvivors .first x p₀ H).card : ℝ) +
         W * ((badIntervalCofactorSurvivors .second x p₀ H).card : ℝ)) := by ring
    _ ≤ (H : ℝ) *
        (8 * (badIntervalCofactorBudget x p₀ + 1) +
         8 * (badIntervalCofactorBudget x p₀ + 1)) := by
      gcongr
    _ = (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by ring

/-- The exact fixed-fiber interval-union estimate at Tao's floor-defined
cofactor degree. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_canonicalCofactorWeight_le
    {x p₀ H : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hsq : (2 * p₀) ^ 2 ≤ badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ)) :
    ((((badIntervalUpperPrimes p₀).card : ℝ) *
        ((H : ℝ) / (2 * p₀))) /
        (2 * badIntervalCofactorSieveDegree x p₀)) ^
          badIntervalCofactorSieveDegree x p₀ *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  obtain ⟨hk, hkcard, hproduct⟩ :=
    badIntervalCofactorSieveDegree_constraints hp₀ hsq hcard hlarge
  exact scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
    hH hHp₀ hk hkcard hproduct

/-- Beyond the pinned PNT threshold, only Tao's two cofactor-scale inequalities
remain as hypotheses of the canonical fixed-fiber estimate. -/
theorem eventually_scaleNormalizedBadIntervalUnionAt_mul_canonicalCofactorWeight_le :
    ∀ᶠ p₀ : ℕ in Filter.atTop, ∀ x H : ℕ,
      1 ≤ H → H < p₀ →
      (2 * p₀) ^ 2 ≤ badIntervalCofactorBudget x p₀ + 1 →
      4 * Real.log
          ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
        ((2 * p₀ : ℕ) : ℝ) →
      ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / (2 * p₀))) /
          (2 * badIntervalCofactorSieveDegree x p₀)) ^
            badIntervalCofactorSieveDegree x p₀ *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  filter_upwards [eventually_card_badIntervalUpperPrimes_lower,
    Filter.eventually_ge_atTop (1 : ℕ)] with p₀ hcard hp₀
  intro x H hH hHp₀ hsq hlarge
  exact scaleNormalizedBadIntervalUnionAt_mul_canonicalCofactorWeight_le
    hp₀ hH hHp₀ hsq hcard hlarge

end

end Tao2026
