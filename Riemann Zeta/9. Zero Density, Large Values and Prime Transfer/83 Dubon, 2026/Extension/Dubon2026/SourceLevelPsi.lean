import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> matching period dimension bounds -> original level index and genus numerics.
Selected from anthropics/fermats-last-theorem (Apache-2.0), commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the solutions
S_ModularCurve_card_projectiveLine_zmod, S_ModularCurve_dedekindPsi_prime_pow
and S_ModularCurve_dedekindPsi_mul_of_coprime. Only the necessary finite-ring
and arithmetic-function proofs are retained; the unrelated modular-polynomial
and function-field developments in the source files are omitted.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section
open Finset Nat Finset.Nat

/-- The squarefree-divisor sum giving the original level-index factor. -/
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

/-- The level-index factor is one at level one. -/
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]
  norm_num

open ArithmeticFunction

private def squarefreeIndicator : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

@[simp]
private theorem squarefreeIndicator_apply {n : ℕ} :
    squarefreeIndicator n = if Squarefree n then 1 else 0 :=
  rfl

private theorem isMultiplicative_squarefreeIndicator :
    squarefreeIndicator.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [squarefreeIndicator_apply, Nat.squarefree_mul h]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp [hm, hn]

private theorem dedekindPsi_eq_mul_apply (N : ℕ) :
    dedekindPsi N = (squarefreeIndicator * ArithmeticFunction.id) N :=
  calc dedekindPsi N
      = ∑ d ∈ N.divisors, squarefreeIndicator d * ArithmeticFunction.id (N / d) := by
        rw [dedekindPsi, sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : Squarefree d <;> simp [hd]
    _ = ∑ x ∈ N.divisorsAntidiagonal, squarefreeIndicator x.1 * ArithmeticFunction.id x.2 :=
        (Nat.sum_divisorsAntidiagonal fun d e =>
          squarefreeIndicator d * ArithmeticFunction.id e).symm
    _ = (squarefreeIndicator * ArithmeticFunction.id) N := ArithmeticFunction.mul_apply.symm

private theorem isMultiplicative_squarefreeIndicator_mul_id :
    (squarefreeIndicator * ArithmeticFunction.id).IsMultiplicative :=
  isMultiplicative_squarefreeIndicator.mul isMultiplicative_id

theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by
  simp only [dedekindPsi_eq_mul_apply]
  exact isMultiplicative_squarefreeIndicator_mul_id.map_mul_of_coprime h

theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hsqfree : ∀ j, Squarefree (p ^ j) ↔ j ≤ 1 := fun j => by
    constructor
    · intro hsq
      by_contra hj
      exact hp.one_lt.ne'
        (Nat.isUnit_iff.mp (hsq p (by rw [← pow_two]; exact pow_dvd_pow p (by omega))))
    · intro hj
      interval_cases j
      · simp
      · simpa using hp.prime.squarefree
  have hfilter : {d ∈ (p ^ k).divisors | Squarefree d} = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hsq⟩
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have : j ≤ 1 := (hsqfree j).mp hsq
      interval_cases j
      · exact Or.inl (pow_zero p)
      · exact Or.inr (pow_one p)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.pos.ne'⟩, squarefree_one⟩
      · exact ⟨⟨dvd_pow_self _ hk, pow_ne_zero _ hp.pos.ne'⟩, hp.prime.squarefree⟩
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  rw [dedekindPsi, hfilter, Finset.sum_pair hp.one_lt.ne, Nat.div_one, hdiv]

end
end Dubon2026.SourceLevelProjective
