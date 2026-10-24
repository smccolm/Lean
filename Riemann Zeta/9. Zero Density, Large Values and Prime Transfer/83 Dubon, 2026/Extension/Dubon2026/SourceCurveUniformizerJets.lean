import Dubon2026.SourceConstantFieldTraceOrders
import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> good reduction -> principal-divisor pushforward -> local
fiber-order inequality. Powers of an actual uniformizer have independent
jets: a polynomial of degree less than m cannot vanish to order m unless
all constant coefficients vanish. The proof uses the existing constant-plus-
positive-order identity and the exact local order arithmetic.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem coefficients_eq_zero_of_uniformizer_order (Q : Place K F) {t : F} (ht : Q.ord t = 1) :
    ∀ (m : ℕ) (e : Fin m → K),
      ((∑ i, algebraMap K F (e i) * t ^ (i : ℕ)) = 0 ∨
        (m : ℤ) ≤ Q.ord (∑ i, algebraMap K F (e i) * t ^ (i : ℕ))) → ∀ i, e i = 0 := by
  have ht0 : t ≠ 0 := fun h => by rw [h, Q.ord_zero] at ht; exact zero_ne_one ht
  have htO : t ∈ Q.toValuationSubring := Q.mem_of_ord_nonneg (by omega)
  intro m
  induction m with
  | zero => intro e _ i; exact i.elim0
  | succ m ih =>
    intro e he
    set s : F := ∑ i : Fin m, algebraMap K F (e i.succ) * t ^ (i : ℕ) with hs
    have hsO : s ∈ Q.toValuationSubring :=
      sum_mem fun i _ => mul_mem (Q.algebraMap_mem' _) (pow_mem htO _)
    have hsplit : ∑ i : Fin (m + 1), algebraMap K F (e i) * t ^ (i : ℕ) =
        algebraMap K F (e 0) + t * s := by
      rw [Fin.sum_univ_succ, hs, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit] at he
    have he0 : e 0 = 0 := by
      by_contra hne
      by_cases hs0 : s = 0
      · simp only [hs0, mul_zero, add_zero] at he
        rcases he with he | he
        · exact hne ((map_eq_zero _).mp he)
        · rw [Q.ord_algebraMap] at he
          omega
      · have hpos : 0 < Q.ord (t * s) := by
          rw [Q.ord_mul ht0 hs0, ht]
          have := Q.ord_nonneg_of_mem hsO
          omega
        rcases he with he | he
        · have heq := congrArg Q.ord (eq_neg_of_add_eq_zero_left he)
          rw [Q.ord_algebraMap, Q.ord_neg] at heq
          omega
        · rw [ConstantField.ord_algebraMap_add_eq_zero Q hne hpos] at he
          omega
    rw [he0, map_zero, zero_add] at he
    have hs' : s = 0 ∨ (m : ℤ) ≤ Q.ord s := by
      rcases eq_or_ne s 0 with h0 | h0
      · exact Or.inl h0
      · right
        rcases he with he | he
        · exact absurd he (mul_ne_zero ht0 h0)
        · rw [Q.ord_mul ht0 h0, ht] at he
          omega
    have ih' := ih (fun i => e i.succ) hs'
    intro i
    exact Fin.cases he0 (fun j => ih' j) i

end
end Dubon2026.SourceCurve.Place
