import Tao2026.BadIntervalLargePrimeMoment
import Tao2026.BadIntervalCharacterExpansion

/-!
# Character fibers for the large-prime moments

This module supplies the exact character-expansion precursor for Propositions
6.7 and 6.8.  A single large-prime divisibility event is empty or one primitive
residue fiber modulo the prime.  For two distinct primes, the joint event is
empty or one primitive residue fiber modulo their product.  The resulting
probability bounds feed directly into the existing 1000th-power character
moment estimate; no analytic exceptional-character estimate is assumed here.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

theorem taoLargePrimeDivisibilityEvent_modEq
    {m' : ℕ} {a : ℕ × ℕ} {w₁ w₂ : TaoPrimeTuple}
    (h₁ : TaoLargePrimeDivisibilityEvent m' a w₁)
    (h₂ : TaoLargePrimeDivisibilityEvent m' a w₂) :
    taoPrimeTupleStart m' w₁ ≡ taoPrimeTupleStart m' w₂ [MOD a.2] := by
  exact Nat.ModEq.add_right_cancel' a.1
    (h₁.modEq_zero_nat.trans h₂.modEq_zero_nat.symm)

theorem taoLargePrimeDivisibilityEvent_of_modEq
    {m' : ℕ} {a : ℕ × ℕ} {w₀ w : TaoPrimeTuple}
    (h₀ : TaoLargePrimeDivisibilityEvent m' a w₀)
    (hw : taoPrimeTupleStart m' w ≡ taoPrimeTupleStart m' w₀ [MOD a.2]) :
    TaoLargePrimeDivisibilityEvent m' a w := by
  exact Nat.modEq_zero_iff_dvd.mp
    ((hw.add_right a.1).trans h₀.modEq_zero_nat)

theorem taoLargePrimeDivisibilityEvent_coprime
    {m' : ℕ} {a : ℕ × ℕ} {w : TaoPrimeTuple}
    (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1)
    (hw : TaoLargePrimeDivisibilityEvent m' a w) :
    Nat.Coprime (taoPrimeTupleStart m' w) a.2 := by
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hpStart
  have hlMod : a.1 ≡ 0 [MOD a.2] := by
    simpa using (hpStart.modEq_zero_nat.add_right a.1).symm.trans
      hw.modEq_zero_nat
  exact hpl (Nat.modEq_zero_iff_dvd.mp hlMod)

theorem taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
    {m' : ℕ} {a : ℕ × ℕ} (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1) :
    {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' a w} = ∅ ∨
      ∃ r : ℕ, Nat.Coprime r a.2 ∧
        {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' a w} =
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} := by
  by_cases hE : ∃ w : TaoPrimeTuple, TaoLargePrimeDivisibilityEvent m' a w
  · right
    obtain ⟨w₀, hw₀⟩ := hE
    refine ⟨taoPrimeTupleStart m' w₀,
      taoLargePrimeDivisibilityEvent_coprime hp hpl hw₀, ?_⟩
    ext w
    constructor
    · exact fun hw => taoLargePrimeDivisibilityEvent_modEq hw hw₀
    · exact fun hw => taoLargePrimeDivisibilityEvent_of_modEq hw₀ hw
  · left
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hw => hE ⟨w, hw⟩

theorem taoLargePrimeJointDivisibilityEvent_modEq_mul
    {m' : ℕ} {a b : ℕ × ℕ} {w₁ w₂ : TaoPrimeTuple}
    (hpq : Nat.Coprime a.2 b.2)
    (h₁ : TaoLargePrimeJointDivisibilityEvent m' a b w₁)
    (h₂ : TaoLargePrimeJointDivisibilityEvent m' a b w₂) :
    taoPrimeTupleStart m' w₁ ≡ taoPrimeTupleStart m' w₂
      [MOD a.2 * b.2] := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp
  exact ⟨taoLargePrimeDivisibilityEvent_modEq h₁.1 h₂.1,
    taoLargePrimeDivisibilityEvent_modEq h₁.2 h₂.2⟩

theorem taoLargePrimeJointDivisibilityEvent_of_modEq_mul
    {m' : ℕ} {a b : ℕ × ℕ} {w₀ w : TaoPrimeTuple}
    (hpq : Nat.Coprime a.2 b.2)
    (h₀ : TaoLargePrimeJointDivisibilityEvent m' a b w₀)
    (hw : taoPrimeTupleStart m' w ≡ taoPrimeTupleStart m' w₀
      [MOD a.2 * b.2]) :
    TaoLargePrimeJointDivisibilityEvent m' a b w := by
  have hpair := (Nat.modEq_and_modEq_iff_modEq_mul hpq).mpr hw
  exact ⟨taoLargePrimeDivisibilityEvent_of_modEq h₀.1 hpair.1,
    taoLargePrimeDivisibilityEvent_of_modEq h₀.2 hpair.2⟩

theorem taoLargePrimeJointDivisibilityEvent_coprime_mul
    {m' : ℕ} {a b : ℕ × ℕ} {w : TaoPrimeTuple}
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hw : TaoLargePrimeJointDivisibilityEvent m' a b w) :
    Nat.Coprime (taoPrimeTupleStart m' w) (a.2 * b.2) := by
  exact (taoLargePrimeDivisibilityEvent_coprime hp hpa hw.1).mul_right
    (taoLargePrimeDivisibilityEvent_coprime hq hqb hw.2)

theorem taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    {m' : ℕ} {a b : ℕ × ℕ}
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1) :
    {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} = ∅ ∨
      ∃ r : ℕ, Nat.Coprime r (a.2 * b.2) ∧
        {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} =
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} := by
  have hcop : Nat.Coprime a.2 b.2 := (Nat.coprime_primes hp hq).mpr hpq
  by_cases hE : ∃ w : TaoPrimeTuple,
      TaoLargePrimeJointDivisibilityEvent m' a b w
  · right
    obtain ⟨w₀, hw₀⟩ := hE
    refine ⟨taoPrimeTupleStart m' w₀,
      taoLargePrimeJointDivisibilityEvent_coprime_mul hp hq hpa hqb hw₀, ?_⟩
    ext w
    constructor
    · exact fun hw => taoLargePrimeJointDivisibilityEvent_modEq_mul hcop hw hw₀
    · exact fun hw =>
        taoLargePrimeJointDivisibilityEvent_of_modEq_mul hcop hw₀ hw
  · left
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hw => hE ⟨w, hw⟩

theorem taoLargePrimeProbability_le_primeCharacterMoments
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1) :
    taoLargePrimeProbability P hP m' a ≤
      ‖(1 / (a.2.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ a.2,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  rcases taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
      (m' := m') (a := a) hp hpl with hEmpty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeProbability, hEmpty, MeasureTheory.measureReal_empty]
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun χ _ =>
      Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _)
  · rw [taoLargePrimeProbability, hset]
    exact primitiveResidueFiber_probability_le_primeCharacterMoments
      hp.pos hr P hP m'

theorem taoLargePrimeJointProbability_le_primeCharacterMoments
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1) :
    taoLargePrimeJointProbability P hP m' a b ≤
      ‖(1 / ((a.2 * b.2).totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ (a.2 * b.2),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  rcases taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
      (m' := m') (a := a) (b := b) hp hq hpq hpa hqb with
    hEmpty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeJointProbability, hEmpty,
      MeasureTheory.measureReal_empty]
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun χ _ =>
      Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _)
  · rw [taoLargePrimeJointProbability, hset]
    exact primitiveResidueFiber_probability_le_primeCharacterMoments
      (Nat.mul_pos hp.pos hq.pos) hr P hP m'

end

end Tao2026


