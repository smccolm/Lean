import Tao2026.BurgessWeilPrimeKummerLegendreFrobeniusSystem

/-!
# Exact eigenpair form of the Legendre Frobenius source

A power-Legendre Frobenius system has rank at most two.  This file removes
the variable finite index type by padding ranks zero and one with zero and
representing every system by an explicit ordered pair of eigenvalues.

The pair formulation is equivalent to the original system, satisfies the
expected quadratic trace recurrence, and directly implies the earlier
base-field Legendre Weil bound.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

structure PrimePowerLegendreEigenpair
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) where
  first : ℂ
  second : ℂ
  integral_first : IsIntegral ℤ first
  integral_second : IsIntegral ℤ second
  weight_first : ‖first‖ ≤ Real.sqrt p
  weight_second : ‖second‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t q =
      -(first ^ (q + 1) + second ^ (q + 1))

def PrimePowerLegendreFrobeniusSystem.toEigenpair
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreFrobeniusSystem p χ m n k t) :
    PrimePowerLegendreEigenpair p χ m n k t := by
  by_cases hzero : s.rank = 0
  · exact {
      first := 0
      second := 0
      integral_first := isIntegral_zero
      integral_second := isIntegral_zero
      weight_first := by simp
      weight_second := by simp
      trace_eq := fun q => by
        rw [s.extensionTrace_eq q]
        have hsum : (∑ i : Fin s.rank,
            s.eigenvalue i ^ (q + 1)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exfalso
          have hiLt := i.isLt
          omega
        rw [hsum]
        simp }
  by_cases hone : s.rank = 1
  · let i0 : Fin s.rank := ⟨0, by omega⟩
    exact {
      first := s.eigenvalue i0
      second := 0
      integral_first := s.integral i0
      integral_second := isIntegral_zero
      weight_first := s.weight_le i0
      weight_second := by simp
      trace_eq := fun q => by
        rw [s.extensionTrace_eq q]
        have hsum : (∑ i : Fin s.rank,
            s.eigenvalue i ^ (q + 1)) = s.eigenvalue i0 ^ (q + 1) := by
          rw [Finset.sum_eq_single i0]
          · intro b hb hne
            exact (hne (Fin.ext (by omega))).elim
          · simp
        rw [hsum]
        simp }
  · have hrank_le := s.rank_le
    have hrank : s.rank = 2 := by omega
    let i0 : Fin s.rank := ⟨0, by omega⟩
    let i1 : Fin s.rank := ⟨1, by omega⟩
    exact {
      first := s.eigenvalue i0
      second := s.eigenvalue i1
      integral_first := s.integral i0
      integral_second := s.integral i1
      weight_first := s.weight_le i0
      weight_second := s.weight_le i1
      trace_eq := fun q => by
        rw [s.extensionTrace_eq q]
        have hsum : (∑ i : Fin s.rank,
            s.eigenvalue i ^ (q + 1)) =
              s.eigenvalue i0 ^ (q + 1) +
                s.eigenvalue i1 ^ (q + 1) := by
          let e : Fin s.rank ≃ Fin 2 := (Fin.castOrderIso hrank).toEquiv
          calc
            (∑ i : Fin s.rank, s.eigenvalue i ^ (q + 1)) =
                ∑ j : Fin 2, s.eigenvalue (e.symm j) ^ (q + 1) :=
              (Equiv.sum_comp e.symm
                (fun i : Fin s.rank => s.eigenvalue i ^ (q + 1))).symm
            _ = s.eigenvalue i0 ^ (q + 1) +
                s.eigenvalue i1 ^ (q + 1) := by
              rw [Fin.sum_univ_two]
              have h0 : e.symm 0 = i0 := by
                apply Fin.ext
                rfl
              have h1 : e.symm 1 = i1 := by
                apply Fin.ext
                rfl
              rw [h0, h1]
        rw [hsum] }

def PrimePowerLegendreEigenpair.toFrobeniusSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (e : PrimePowerLegendreEigenpair p χ m n k t) :
    PrimePowerLegendreFrobeniusSystem p χ m n k t where
  rank := 2
  eigenvalue := Fin.cases e.first (fun _ => e.second)
  rank_le := le_rfl
  integral i := by
    fin_cases i
    · exact e.integral_first
    · exact e.integral_second
  weight_le i := by
    fin_cases i
    · exact e.weight_first
    · exact e.weight_second
  trace_eq := by
    rw [Fin.sum_univ_two]
    simpa using e.trace_eq 0
  extensionTrace_eq q := by
    rw [Fin.sum_univ_two]
    exact e.trace_eq q

theorem nonempty_primePowerLegendreFrobeniusSystem_iff_eigenpair
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreFrobeniusSystem p χ m n k t) ↔
      Nonempty (PrimePowerLegendreEigenpair p χ m n k t) := by
  constructor
  · exact fun h => h.map PrimePowerLegendreFrobeniusSystem.toEigenpair
  · exact fun h => h.map PrimePowerLegendreEigenpair.toFrobeniusSystem

theorem PrimePowerLegendreEigenpair.trace_recurrence
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (e : PrimePowerLegendreEigenpair p χ m n k t) (q : ℕ) :
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      (e.first + e.second) *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        (e.first * e.second) *
          primePowerLegendreExtensionCorrelation p χ m n k t q := by
  rw [e.trace_eq (q + 2), e.trace_eq (q + 1), e.trace_eq q]
  ring

theorem PrimePowerLegendreEigenpair.base_norm_le_two_mul_sqrt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (e : PrimePowerLegendreEigenpair p χ m n k t) :
    ‖primePowerLegendreExtensionCorrelation p χ m n k t 0‖ ≤
      2 * Real.sqrt p := by
  rw [e.trace_eq 0]
  simp only [Nat.zero_add, pow_one, norm_neg]
  calc
    ‖e.first + e.second‖ ≤ ‖e.first‖ + ‖e.second‖ := norm_add_le _ _
    _ ≤ Real.sqrt p + Real.sqrt p :=
      add_le_add e.weight_first e.weight_second
    _ = 2 * Real.sqrt p := by ring

def TaoPrimePowerLegendreEigenpair : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        Nonempty (PrimePowerLegendreEigenpair p χ m n k t)

theorem taoPrimePowerLegendreFrobeniusSystem_iff_eigenpair :
    TaoPrimePowerLegendreFrobeniusSystem ↔ TaoPrimePowerLegendreEigenpair := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (nonempty_primePowerLegendreFrobeniusSystem_iff_eigenpair).mp
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (nonempty_primePowerLegendreFrobeniusSystem_iff_eigenpair).mpr
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

def TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem : Prop :=
  TaoPrimePowerLegendreEigenpair ∧
    TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore

theorem taoPrimePowerLegendreOrFourRootsFrobeniusSystem_iff_eigenpairOrFourRoots :
    TaoPrimePowerLegendreOrFourRootsFrobeniusSystem ↔
      TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem := by
  rw [TaoPrimePowerLegendreOrFourRootsFrobeniusSystem,
    TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem, taoPrimePowerLegendreFrobeniusSystem_iff_eigenpair]

theorem TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem.toFull
    (h : TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem) : TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimePowerLegendreOrFourRootsFrobeniusSystem.toFull
    (taoPrimePowerLegendreOrFourRootsFrobeniusSystem_iff_eigenpairOrFourRoots.mpr h)

theorem TaoPrimePowerLegendreEigenpair.toReducedPowerLegendreWeilBoundAboveSixtyFour
    (h : TaoPrimePowerLegendreEigenpair) :
    TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k t hmred hnred hkred
    hpowM hpowN hpowK hpowSum ht0 ht1
  have hχ : χ ≠ 1 := by
    intro hχ
    subst χ
    simp at hpowM
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm
    subst m
    simp at hpowM
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    simp at hpowN
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk
    subst k
    simp at hpowK
  have hsum : ¬orderOf χ ∣ m + n + k := by
    intro hdvd
    exact hpowSum (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨e⟩ := h p χ m n k t hχ hm hn hk hmred hnred hkred
    ht0 ht1 hsum
  change ‖primePowerLegendreExtensionCorrelation p χ m n k t 0‖ ≤
    2 * Real.sqrt p
  exact e.base_norm_le_two_mul_sqrt

end
end Tao2026


