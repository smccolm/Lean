import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
import Theorems.Thm_ValuationSubring_inertiaCharacter_eq_one_of_apply_kummerRoot_eq
import P2M.Util
namespace P2MW.S_ValuationSubring_inertiaCharacter_eq_one_of_cyclotomic_eq_one

set_option autoImplicit false
open IsLocalRing Polynomial

theorem solution
    {R : Type} [CommRing R] {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hwild : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ξ σ = 1)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ (q - 1) = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1) :
    ξ σ = 1 := by
  classical
  have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure ℚ, α ^ (q - 1) = (q : AlgebraicClosure ℚ) :=
    IsAlgClosed.exists_pow_nat_eq _ hq1
  have hcop : (q - 1).Coprime q := by
    have h : Nat.Coprime (q - 1 + 1) (q - 1) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
    rw [Nat.sub_add_cancel hq.one_lt.le] at h
    exact h.symm
  exact ValuationSubring.inertiaCharacter_eq_one_of_apply_kummerRoot_eq hq P hP hq1 hcop α hα ξ hmul hexp hcont hσ
    (ValuationSubring.apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one hq P hP cyc hcyc hσ hσc α hα)
