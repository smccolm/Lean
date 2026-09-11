import Tao2026.FactorialLargeSieve
import Tao2026.LargeSieveDenominator

/-!
# Corollary 2.9 for the factorial residue family

This file packages the literal upper-half-prime residue restrictions, proves
their exact tensor ratio formula, and applies the loss-free global large sieve
together with the fixed-cardinality denominator lower bound.  The endpoint is
the source-scale fixed-`(a,H)` fiber estimate used in Theorem 1.9.
-/

open Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- An upper-half prime packaged as a nonzero sieve modulus. -/
def factorialPrimeSieveModulus (a : ℕ)
    (p : ↥(factorialUpperHalfPrimes a)) : SieveModulus where
  modulus := p.1
  ne_zero := (Finset.mem_filter.mp p.2).2.ne_zero

/-- On every modulus, remove the complement of the literal allowed start
residues.  Thus `SieveAvoids` means membership in the allowed family. -/
def factorialRestrictions (H : ℕ) :
    (qs : List SieveModulus) → SieveRestrictions qs
  | [] => PUnit.unit
  | q :: qs =>
      ((factorialAllowedStartResidues q.modulus H)ᶜ,
        factorialRestrictions H qs)

theorem factorialRestrictions_proper
    (H : ℕ) (hH : 1 ≤ H) :
    ∀ qs : List SieveModulus,
      SieveRestrictionsProper (factorialRestrictions H qs)
  | [] => by simp [SieveRestrictionsProper]
  | q :: qs => by
      constructor
      · change (factorialAllowedStartResidues q.modulus H)ᶜ.card < q.modulus
        simpa only [ZMod.card] using
          (Finset.card_compl_lt_iff_nonempty
            (factorialAllowedStartResidues q.modulus H)).2
              (factorialAllowedStartResidues_nonempty q.modulus H hH)
      · exact factorialRestrictions_proper H hH qs

/-- The literal removed/allowed ratio at one packaged modulus. -/
def factorialRestrictionWeight (H : ℕ) (q : SieveModulus) : ℝ :=
  ((factorialAllowedStartResidues q.modulus H)ᶜ.card : ℝ) /
    (factorialAllowedStartResidues q.modulus H).card

theorem sieveRestrictionRatio_factorialRestrictions
    (H : ℕ) : ∀ qs : List SieveModulus,
    sieveRestrictionRatio (factorialRestrictions H qs) =
      (qs.map (factorialRestrictionWeight H)).prod
  | [] => by simp [sieveRestrictionRatio]
  | q :: qs => by
      simp [factorialRestrictions, sieveRestrictionRatio,
        factorialRestrictionWeight,
        sieveRestrictionRatio_factorialRestrictions H qs]

/-- Exact reindexing of a selected tensor restriction ratio as the product of
the literal one-prime ratios. -/
theorem sieveRestrictionRatio_selected_factorialRestrictions
    (a H k : ℕ)
    (s : FixedCardModulusSelections
      (↥(factorialUpperHalfPrimes a)) k) :
    sieveRestrictionRatio (factorialRestrictions H
      (selectedModuliList (factorialPrimeSieveModulus a) s)) =
      ∏ p ∈ s.1,
        factorialRestrictionWeight H (factorialPrimeSieveModulus a p) := by
  rw [sieveRestrictionRatio_factorialRestrictions]
  simp [selectedModuliList]

/-- Each literal factorial restriction weight dominates the uniform source
surrogate `log(x+2)/400`. -/
theorem factorialRestrictionWeight_ge
    {x a H : ℕ}
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (p : ↥(factorialUpperHalfPrimes a)) :
    Real.log (x + 2) / 400 ≤
      factorialRestrictionWeight H (factorialPrimeSieveModulus a p) := by
  letI : NeZero p.1 := ⟨(Finset.mem_filter.mp p.2).2.ne_zero⟩
  exact (factorialSieveSurrogateRatio_ge hH hlog hhard p.2).trans
    (factorialSieveSurrogateRatio_le_actual hH)

/-- The literal sum of selected tensor ratios has the fixed-cardinality
elementary-symmetric lower bound. -/
theorem factorial_selection_ratio_sum_ge_halfCard
    {x a H k : ℕ}
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hk : 1 ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card) :
    ((((factorialUpperHalfPrimes a).card : ℝ) *
        (Real.log (x + 2) / 400)) / (2 * k)) ^ k ≤
      ∑ s : FixedCardModulusSelections
          (↥(factorialUpperHalfPrimes a)) k,
        sieveRestrictionRatio (factorialRestrictions H
          (selectedModuliList (factorialPrimeSieveModulus a) s)) := by
  have h := fixedCardSelection_weightSum_ge_halfCard
    (Q := ↥(factorialUpperHalfPrimes a))
    (fun p => factorialRestrictionWeight H
      (factorialPrimeSieveModulus a p))
    (Real.log (x + 2) / 400) k (by positivity)
    (factorialRestrictionWeight_ge hH hlog hhard) hk (by
      simpa only [Fintype.card_coe] using hkcard)
  simpa only [Fintype.card_coe,
    sieveRestrictionRatio_selected_factorialRestrictions] using h

/-- After the PNT cardinal input, the selected-ratio sum has the exact source
scale raised to the `k`th power. -/
theorem factorial_selection_ratio_sum_ge_source_scale
    {x a H k : ℕ}
    (ha : 2 ≤ a)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hk : 1 ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card) :
    (((a : ℝ) * Real.log (x + 2) /
        (3200 * Real.log a)) / k) ^ k ≤
      ∑ s : FixedCardModulusSelections
          (↥(factorialUpperHalfPrimes a)) k,
        sieveRestrictionRatio (factorialRestrictions H
          (selectedModuliList (factorialPrimeSieveModulus a) s)) := by
  have hlogapos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hc : 0 ≤ Real.log (x + 2) / 400 := by positivity
  have hhalf : (a : ℝ) / (4 * Real.log a) / 2 ≤
      ((factorialUpperHalfPrimes a).card : ℝ) / 2 := by
    linarith
  have hscale : (a : ℝ) * Real.log (x + 2) /
        (3200 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ) / 2 *
        (Real.log (x + 2) / 400) := by
    calc
      (a : ℝ) * Real.log (x + 2) / (3200 * Real.log a) =
          ((a : ℝ) / (4 * Real.log a) / 2) *
            (Real.log (x + 2) / 400) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hc
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : ((a : ℝ) * Real.log (x + 2) /
        (3200 * Real.log a)) / k ≤
      (((factorialUpperHalfPrimes a).card : ℝ) *
        (Real.log (x + 2) / 400)) / (2 * k) := by
    calc
      ((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) / k ≤
          (((factorialUpperHalfPrimes a).card : ℝ) / 2 *
            (Real.log (x + 2) / 400)) / k :=
        div_le_div_of_nonneg_right hscale hkpos.le
      _ = _ := by ring
  exact (pow_le_pow_left₀ (by positivity) hbase k).trans
    (factorial_selection_ratio_sum_ge_halfCard
      hH hlog hhard hk hkcard)

/-- Every selected product of upper-half-prime moduli is at most `a^k`. -/
theorem selected_factorial_moduli_product_le
    {a k : ℕ}
    (s : FixedCardModulusSelections
      (↥(factorialUpperHalfPrimes a)) k) :
    sieveModulusProduct
        (selectedModuliList (factorialPrimeSieveModulus a) s) ≤ a ^ k := by
  simp only [sieveModulusProduct, selectedModuliList, List.map_map]
  change (s.1.toList.map fun p => p.1).prod ≤ a ^ k
  rw [Finset.prod_map_toList]
  calc
    ∏ p ∈ s.1, p.1 ≤ ∏ _p ∈ s.1, a := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.2).1).2
    _ = a ^ k := by rw [Finset.prod_const, s.2]

/-- Avoiding the complement restrictions is exactly simultaneous membership
in the literal allowed residue sets. -/
theorem factorialRestrictions_avoids_natSieveCube
    (H N : ℕ) : ∀ qs : List SieveModulus,
    SieveAvoids (factorialRestrictions H qs) (natSieveCube qs N) ↔
      ∀ q ∈ qs,
        (N : ZMod q.modulus) ∈
          factorialAllowedStartResidues q.modulus H
  | [] => by simp [SieveAvoids]
  | q :: qs => by
      change ((N : ZMod q.modulus) ∉
          (factorialAllowedStartResidues q.modulus H)ᶜ ∧
          SieveAvoids (factorialRestrictions H qs)
            (natSieveCube qs N)) ↔ _
      simp only [Finset.mem_compl, not_not, List.forall_mem_cons,
        factorialRestrictions_avoids_natSieveCube H N qs]

/-- Embed the literal natural-number survivor set into the initial interval
`Fin (x+1)` used by the global finite large sieve. -/
def factorialLargeSieveSurvivorEmbedding (x a H : ℕ) :
    ↥(factorialLargeSieveSurvivorStarts x a H) ↪ Fin (x + 1) where
  toFun n := ⟨n.1, Nat.lt_succ_iff.mpr
    (mem_factorialLargeSieveSurvivorStarts.mp n.2).1⟩
  inj' := by
    intro n m h
    apply Subtype.ext
    exact congrArg Fin.val h

def factorialLargeSieveSurvivorFinset (x a H : ℕ) :
    Finset (Fin (x + 1)) :=
  (factorialLargeSieveSurvivorStarts x a H).attach.map
    (factorialLargeSieveSurvivorEmbedding x a H)

@[simp]
theorem card_factorialLargeSieveSurvivorFinset (x a H : ℕ) :
    (factorialLargeSieveSurvivorFinset x a H).card =
      (factorialLargeSieveSurvivorStarts x a H).card := by
  simp [factorialLargeSieveSurvivorFinset]

theorem factorialLargeSieveSurvivorFinset_avoids
    {x a H k : ℕ}
    {n : Fin (x + 1)}
    (hn : n ∈ factorialLargeSieveSurvivorFinset x a H)
    (s : FixedCardModulusSelections
      (↥(factorialUpperHalfPrimes a)) k) :
    SieveAvoids
      (factorialRestrictions H
        (selectedModuliList (factorialPrimeSieveModulus a) s))
      (natSieveCube
        (selectedModuliList (factorialPrimeSieveModulus a) s) n) := by
  rw [factorialLargeSieveSurvivorFinset, Finset.mem_map] at hn
  rcases hn with ⟨m, hm, rfl⟩
  rw [factorialRestrictions_avoids_natSieveCube]
  intro q hq
  rw [selectedModuliList, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩
  have hmSurv := mem_factorialLargeSieveSurvivorStarts.mp m.2
  exact hmSurv.2 p.1 p.2

/-- Literal finite Corollary 2.9 before inserting the denominator lower
bound. -/
theorem factorialLargeSieveSurvivor_card_mul_ratio_le
    {x a H k : ℕ}
    (hH : 1 ≤ H)
    (hproduct : (a ^ k) * (a ^ k) ≤ x + 1) :
    (∑ s : FixedCardModulusSelections
        (↥(factorialUpperHalfPrimes a)) k,
      sieveRestrictionRatio (factorialRestrictions H
        (selectedModuliList (factorialPrimeSieveModulus a) s))) *
        ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
      8 * (x + 1) := by
  have hglobal := montgomery_global_survivor_card_fixedCardSelections
    (Q := ↥(factorialUpperHalfPrimes a))
    (modulus := factorialPrimeSieveModulus a)
    (k := k) (K := a ^ k) (L := x + 1)
    (fun p q hpq => factorialUpperHalfPrimes_pairwise_coprime a
      p.2 q.2 (fun h => hpq (Subtype.ext h)))
    (by omega)
    selected_factorial_moduli_product_le
    hproduct
    (fun s => factorialRestrictions H
      (selectedModuliList (factorialPrimeSieveModulus a) s))
    (fun s => factorialRestrictions_proper H hH _)
    (factorialLargeSieveSurvivorFinset x a H)
    (fun n hn s => factorialLargeSieveSurvivorFinset_avoids hn s)
  simpa only [card_factorialLargeSieveSurvivorFinset, Nat.cast_add,
    Nat.cast_one] using hglobal

/-- Source-scale survivor bound obtained by combining Corollaries 2.8 and
2.9 with the PNT modulus count. -/
theorem factorialLargeSieveSurvivor_card_source_bound
    {x a H k : ℕ}
    (ha : 2 ≤ a)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hk : 1 ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card)
    (hproduct : (a ^ k) * (a ^ k) ≤ x + 1) :
    (((a : ℝ) * Real.log (x + 2) /
        (3200 * Real.log a)) / k) ^ k *
        ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
      8 * (x + 1) := by
  calc
    (((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) / k) ^ k *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
        (∑ s : FixedCardModulusSelections
            (↥(factorialUpperHalfPrimes a)) k,
          sieveRestrictionRatio (factorialRestrictions H
            (selectedModuliList (factorialPrimeSieveModulus a) s))) *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) :=
      mul_le_mul_of_nonneg_right
        (factorial_selection_ratio_sum_ge_source_scale
          ha hcard hH hlog hhard hk hkcard) (by positivity)
    _ ≤ 8 * (x + 1) :=
      factorialLargeSieveSurvivor_card_mul_ratio_le hH hproduct

/-- Final fixed-fiber source-scale large-sieve estimate. -/
theorem factorialLargeSieveIntervalsAt_card_source_bound
    {x B a H k : ℕ}
    (ha : 2 ≤ a)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hk : 1 ≤ k)
    (hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card)
    (hproduct : (a ^ k) * (a ^ k) ≤ x + 1) :
    (((a : ℝ) * Real.log (x + 2) /
        (3200 * Real.log a)) / k) ^ k *
        ((factorialLargeSieveIntervalsAt x B a H).card : ℝ) ≤
      8 * (x + 1) := by
  have hfiber := card_factorialLargeSieveIntervalsAt_le_survivors x B a H
  have hfiberReal :
      ((factorialLargeSieveIntervalsAt x B a H).card : ℝ) ≤
        (factorialLargeSieveSurvivorStarts x a H).card := by
    exact_mod_cast hfiber
  calc
    (((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) / k) ^ k *
          ((factorialLargeSieveIntervalsAt x B a H).card : ℝ) ≤
        (((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) / k) ^ k *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) :=
      mul_le_mul_of_nonneg_left hfiberReal (by positivity)
    _ ≤ 8 * (x + 1) := factorialLargeSieveSurvivor_card_source_bound
      ha hcard hH hlog hhard hk hkcard hproduct

end

end Tao2026
