import Tao2026.BurgessWeilPrimeKummerLegendreReduction

/-!
# Frobenius systems for the power-Legendre trace sequence

The canonical three-root polynomial has an explicit character sum over every
finite extension.  Its local characters are the powers `χ^m`, `χ^n`, and
`χ^k` at the marked points `0`, `1`, and `t`.

This file proves that identity degree by degree and restates the remaining
three-root geometric input as a rank-at-most-two integral weight-one
Frobenius system for the literal power-Legendre sums.  The polynomial and
character-sum system formulations are equivalent without loss.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def finiteFieldPowerLegendreCorrelation
    (F : Type*) [Field F] [Fintype F]
    (α β γ : MulChar F ℂ) (t : F) : ℂ :=
  ∑ x : F, α x * β (x - 1) * γ (x - t)

theorem eval_map_primeKummerLegendrePolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p)
    {L : Type*} [Field L] [Algebra (ZMod p) L] (x : L) :
    ((primeKummerLegendrePolynomial m n k t).map
      (algebraMap (ZMod p) L)).eval x =
        x ^ m * (x - 1) ^ n *
          (x - algebraMap (ZMod p) L t) ^ k := by
  simp [primeKummerLegendrePolynomial, Multiset.map_add,
    Multiset.prod_add]

theorem finiteFieldPolynomialCharacterCorrelation_primeKummerLegendrePolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (L : Type*) [Field L] [Fintype L] [DecidableEq L]
    [Algebra (ZMod p) L]
    (ψ : MulChar L ℂ) :
    finiteFieldPolynomialCharacterCorrelation L ψ
        ((primeKummerLegendrePolynomial m n k t).map
          (algebraMap (ZMod p) L)) =
      finiteFieldPowerLegendreCorrelation L (ψ ^ m) (ψ ^ n) (ψ ^ k)
        (algebraMap (ZMod p) L t) := by
  unfold finiteFieldPolynomialCharacterCorrelation finiteFieldPowerLegendreCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  rw [eval_map_primeKummerLegendrePolynomial, map_mul, map_mul, map_pow, map_pow, map_pow,
    MulChar.pow_apply' ψ hm.ne', MulChar.pow_apply' ψ hn.ne',
    MulChar.pow_apply' ψ hk.ne']

def primePowerLegendreExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : ℕ → ℂ
  | 0 => finiteFieldPowerLegendreCorrelation (ZMod p) (χ ^ m) (χ ^ n) (χ ^ k) t
  | q + 1 => by
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact finiteFieldPowerLegendreCorrelation E (χE ^ m) (χE ^ n) (χE ^ k)
        (algebraMap (ZMod p) E t)

theorem primeKummerExtensionCorrelation_eq_powerLegendre
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) :
    ∀ q : ℕ,
      primeKummerExtensionCorrelation p χ
          (primeKummerLegendrePolynomial m n k t) q =
        primePowerLegendreExtensionCorrelation p χ m n k t q
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero]
      unfold primePolynomialCharacterCorrelation primePowerLegendreExtensionCorrelation
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (primeKummerLegendrePolynomial m n k t).eval x =
          x ^ m * (x - 1) ^ n * (x - t) ^ k by
        simpa using eval_map_primeKummerLegendrePolynomial m n k t x,
        map_mul, map_mul, map_pow, map_pow, map_pow,
        MulChar.pow_apply' χ hm.ne', MulChar.pow_apply' χ hn.ne',
        MulChar.pow_apply' χ hk.ne']
  | q + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change finiteFieldPolynomialCharacterCorrelation E χE
          ((primeKummerLegendrePolynomial m n k t).map
            (algebraMap (ZMod p) E)) =
        finiteFieldPowerLegendreCorrelation E (χE ^ m) (χE ^ n) (χE ^ k)
          (algebraMap (ZMod p) E t)
      exact finiteFieldPolynomialCharacterCorrelation_primeKummerLegendrePolynomial
        m n k t hm hn hk E χE

structure PrimePowerLegendreFrobeniusSystem
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) where
  rank : ℕ
  eigenvalue : Fin rank → ℂ
  rank_le : rank ≤ 2
  integral : ∀ i, IsIntegral ℤ (eigenvalue i)
  weight_le : ∀ i, ‖eigenvalue i‖ ≤ Real.sqrt p
  trace_eq : primePowerLegendreExtensionCorrelation p χ m n k t 0 =
    -∑ i : Fin rank, eigenvalue i
  extensionTrace_eq : ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t q =
      -∑ i : Fin rank, eigenvalue i ^ (q + 1)

def PrimeKummerIsotypicFrobeniusSystem.toPowerLegendre
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerLegendrePolynomial m n k t))
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    PrimePowerLegendreFrobeniusSystem p χ m n k t where
  rank := s.rank
  eigenvalue := s.eigenvalue
  rank_le := by
    have hs := s.rank_le
    have hroots := primeKummerLegendrePolynomial_roots_toFinset
      m n k t hm hn hk
    rw [hroots] at hs
    simpa [Ne.symm ht0, Ne.symm ht1] using hs
  integral := s.integral
  weight_le := s.weight_le
  trace_eq := by
    rw [← primeKummerExtensionCorrelation_eq_powerLegendre p χ m n k t hm hn hk 0]
    exact s.trace_eq
  extensionTrace_eq q := by
    rw [← primeKummerExtensionCorrelation_eq_powerLegendre p χ m n k t hm hn hk q]
    exact s.extensionTrace_eq q

def PrimePowerLegendreFrobeniusSystem.toKummer
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreFrobeniusSystem p χ m n k t)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerLegendrePolynomial m n k t) where
  rank := s.rank
  eigenvalue := s.eigenvalue
  rank_le := by
    rw [primeKummerLegendrePolynomial_roots_toFinset m n k t hm hn hk]
    simpa [Ne.symm ht0, Ne.symm ht1] using s.rank_le
  integral := s.integral
  weight_le := s.weight_le
  trace_eq := by
    change primeKummerExtensionCorrelation p χ
      (primeKummerLegendrePolynomial m n k t) 0 = _
    rw [primeKummerExtensionCorrelation_eq_powerLegendre p χ m n k t hm hn hk 0]
    exact s.trace_eq
  extensionTrace_eq q := by
    rw [primeKummerExtensionCorrelation_eq_powerLegendre p χ m n k t hm hn hk q]
    exact s.extensionTrace_eq q

theorem nonempty_primeKummerIsotypicFrobeniusSystem_iff_powerLegendre
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerLegendrePolynomial m n k t)) ↔
      Nonempty (PrimePowerLegendreFrobeniusSystem p χ m n k t) := by
  constructor
  · exact fun h => h.map (fun s => s.toPowerLegendre hm hn hk ht0 ht1)
  · exact fun h => h.map (fun s => s.toKummer hm hn hk ht0 ht1)

def TaoPrimePowerLegendreFrobeniusSystem : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        Nonempty (PrimePowerLegendreFrobeniusSystem p χ m n k t)

theorem taoPrimeKummerLegendreReducedExponentFrobeniusSystem_iff_powerLegendre :
    TaoPrimeKummerLegendreReducedExponentFrobeniusSystem ↔
      TaoPrimePowerLegendreFrobeniusSystem := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (nonempty_primeKummerIsotypicFrobeniusSystem_iff_powerLegendre hm hn hk ht0 ht1).mp
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (nonempty_primeKummerIsotypicFrobeniusSystem_iff_powerLegendre hm hn hk ht0 ht1).mpr
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

def TaoPrimePowerLegendreOrFourRootsFrobeniusSystem : Prop :=
  TaoPrimePowerLegendreFrobeniusSystem ∧
    TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore

theorem taoPrimeKummerLegendreOrFourRootsFrobeniusSystem_iff_powerLegendreOrFourRoots :
    TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem ↔
      TaoPrimePowerLegendreOrFourRootsFrobeniusSystem := by
  rw [TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem,
    TaoPrimePowerLegendreOrFourRootsFrobeniusSystem, taoPrimeKummerLegendreReducedExponentFrobeniusSystem_iff_powerLegendre]

theorem TaoPrimePowerLegendreOrFourRootsFrobeniusSystem.toFull
    (h : TaoPrimePowerLegendreOrFourRootsFrobeniusSystem) : TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem.toFull
    (taoPrimeKummerLegendreOrFourRootsFrobeniusSystem_iff_powerLegendreOrFourRoots.mpr h)

end
end Tao2026


