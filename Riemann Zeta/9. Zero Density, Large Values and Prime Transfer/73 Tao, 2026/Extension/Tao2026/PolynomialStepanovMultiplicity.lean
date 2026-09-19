import Tao2026.BurgessWeilPrimeKummerLiteralWeilOnly
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Multiplicity and linear algebra for the Stepanov polynomial method

Hasse-derivative vanishing gives the exact degree-versus-root-count bound.
A dimension inequality supplies a nonzero auxiliary polynomial whenever the
chosen polynomial parametrization is injective.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem polynomial_X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero
    {K : Type*} [Field K] (P : K[X]) (a : K) (m : ℕ) :
    (X - C a) ^ m ∣ P ↔ ∀ j < m, (hasseDeriv j P).eval a = 0 := by
  rw [← map_dvd_iff (taylorEquiv a)]
  have hshift : taylorEquiv a ((X - C a) ^ m) = X ^ m := by
    change taylor a ((X - C a) ^ m) = X ^ m
    simp [taylor_apply]
  rw [hshift, X_pow_dvd_iff]
  change (∀ j < m, (taylor a P).coeff j = 0) ↔ _
  simp only [taylor_coeff]

theorem polynomial_card_mul_le_natDegree_of_hasseDeriv_vanishing
    {K : Type*} [Field K] (P : K[X]) (hP : P ≠ 0) (S : Finset K) (m : ℕ)
    (hvan : ∀ a ∈ S, ∀ j < m, (hasseDeriv j P).eval a = 0) :
    S.card * m ≤ P.natDegree := by
  classical
  have hprod : (∏ a ∈ S, (X - C a) ^ m) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact (pairwise_coprime_X_sub_C Function.injective_id hab).pow
    · intro a ha
      exact (polynomial_X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero P a m).2 (hvan a ha)
  have hdeg := natDegree_le_of_dvd hprod hP
  have hmon : ∀ a ∈ S, ((X - C a) ^ m : K[X]).Monic :=
    fun a _ => (monic_X_sub_C a).pow m
  rw [natDegree_prod_of_monic _ _ hmon] at hdeg
  simpa using hdeg

theorem polynomial_exists_nonzero_auxiliary_of_finrank_lt
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (P : V →ₗ[K] K[X]) (hP : Function.Injective P) (L : V →ₗ[K] W)
    (hdim : Module.finrank K W < Module.finrank K V) :
    ∃ v : V, L v = 0 ∧ P v ≠ 0 := by
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv, fun h => hv0 (hP (by simpa using h))⟩

end
end Tao2026
