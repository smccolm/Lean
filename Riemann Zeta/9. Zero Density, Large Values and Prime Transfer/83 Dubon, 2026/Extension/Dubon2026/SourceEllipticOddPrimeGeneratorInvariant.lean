import Dubon2026.SourceIntegralOddCyclicRoots

/-! The actual quotient j-value depends only on the odd-prime cyclic subgroup.
Compare two complete products that differ at one generator, then cancel the
common monic factors. This reuses the proved arbitrary-field product and avoids
a second quotient-isomorphism or rational-function argument in positive characteristic. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticCyclicCount SourceEllipticVelu.OddDiscriminant
noncomputable section

/-- Actual odd-prime quotient j-values are independent of the generator in every allowed characteristic. -/
theorem oddQuotientJ_eq_of_prime_zmultiples_eq
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    {P Q : W.toAffine.Point}
    (hP : addOrderOf P = 2 * (p / 2) + 1) (hQ : addOrderOf Q = 2 * (p / 2) + 1)
    (hPQ : AddSubgroup.zmultiples P = AddSubgroup.zmultiples Q) :
    oddQuotientJ W hP = oddQuotientJ W hQ := by
  classical
  have hpodd : p = 2 * (p / 2) + 1 := by
    obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    omega
  obtain ⟨R, hR, hRinj, i, hi⟩ :=
    exists_prime_cyclic_generators_containing W p hp P (hP.trans hpodd.symm)
  have hR' (j) := (hR j).trans hpodd
  let S := Function.update R i Q
  have hS (j : Fin (p + 1)) : addOrderOf (S j) = 2 * (p / 2) + 1 := by
    by_cases h : j = i
    · subst j
      simpa only [S, Function.update_self] using hQ
    · simpa only [S, Function.update_of_ne h] using hR' j
  have hker : (fun j => AddSubgroup.zmultiples (S j)) =
      (fun j => AddSubgroup.zmultiples (R j)) := by
    funext j
    by_cases h : j = i
    · subst j
      simpa only [S, Function.update_self, hi] using hPQ.symm
    · simp only [S, Function.update_of_ne h]
  have hSinj : Function.Injective (fun j => AddSubgroup.zmultiples (S j)) := by
    simpa only [hker] using hRinj
  have heq := (modularPolynomial_eq_oddQuotientProduct W p hp2 hp R hR' hRinj).symm.trans
    (modularPolynomial_eq_oddQuotientProduct W p hp2 hp S hS hSinj)
  have hrest : (∏ j ∈ Finset.univ.erase i, (X - C (oddQuotientJ W (hS j)))) =
      ∏ j ∈ Finset.univ.erase i, (X - C (oddQuotientJ W (hR' j))) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [S, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hn : (∏ j ∈ Finset.univ.erase i, (X - C (oddQuotientJ W (hR' j)))) ≠ 0 :=
    (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero
  rw [oddQuotientProduct, oddQuotientProduct,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hrest] at heq
  have hfac := mul_right_cancel₀ hn heq
  have hz := congrArg (Polynomial.eval 0) hfac
  simpa only [eval_sub, eval_X, eval_C, zero_sub, neg_inj, hi, S,
    Function.update_self] using hz

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
