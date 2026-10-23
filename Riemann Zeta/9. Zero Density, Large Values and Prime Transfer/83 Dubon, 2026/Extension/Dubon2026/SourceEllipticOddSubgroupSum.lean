import Dubon2026.SourceEllipticTranslationTrace
import Dubon2026.SourceEllipticOddOrbitTrace

/-! Enumerating and pairing an actual odd cyclic subgroup. Native finite-order
enumeration and the existing interval reflection argument supply the sum formula
needed to identify both normalized coordinate sums with the literal Velu sums.
No new abstract orbit or cardinality certificate is assumed. -/

namespace Dubon2026.SourceEllipticFunctionField

variable {G A : Type*} [AddGroup G] [AddCommMonoid A]

/-- An actual point of nonzero finite order generates a finite subgroup. -/
theorem finite_zmultiples_of_order {Q : G} {N : ℕ} (hQ : addOrderOf Q = N) (hN : N ≠ 0) :
    Finite (AddSubgroup.zmultiples Q) := by
  have hf : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by omega)
  exact Finite.of_equiv (Fin (addOrderOf Q)) (finEquivZMultiples hf)

/-- The actual subgroup sum is the sum over the native enumeration by multiples. -/
theorem sum_zmultiples_eq_range {Q : G} [Finite (AddSubgroup.zmultiples Q)]
    {N : ℕ} (hQ : addOrderOf Q = N) (hN : N ≠ 0) (f : G → A) :
    letI := Fintype.ofFinite (AddSubgroup.zmultiples Q)
    ∑ P : AddSubgroup.zmultiples Q, f P = ∑ j ∈ Finset.range N, f (j • Q) := by
  classical
  letI := Fintype.ofFinite (AddSubgroup.zmultiples Q)
  have hf : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by omega)
  have he := (finEquivZMultiples hf).sum_comp (fun P : AddSubgroup.zmultiples Q => f P)
  have hsum : (∑ j : Fin (addOrderOf Q), f ((j : ℕ) • Q)) =
      ∑ P : AddSubgroup.zmultiples Q, f P := he
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j • Q)), hQ] at hsum
  exact hsum.symm

/-- An odd cyclic sum pairs each nonzero multiple with its negative. -/
theorem sum_odd_multiples_fold {Q : G} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    (f : G → A) :
    ∑ j ∈ Finset.range (2 * n + 1), f (j • Q) =
      f 0 + ∑ k ∈ Finset.Icc 1 n, (f (k • Q) + f (-(k • Q))) := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun j => f (j • Q))
      (by omega : (0 : ℕ) ≤ n + 1) (by omega : n + 1 ≤ 2 * n + 1),
    ← Finset.sum_Ico_consecutive (fun j => f (j • Q))
      (by omega : (0 : ℕ) ≤ 1) (by omega : (1 : ℕ) ≤ n + 1)]
  have hA : ∑ j ∈ Finset.Ico 0 1, f (j • Q) = f 0 := by simp
  have hB : ∑ j ∈ Finset.Ico 1 (n + 1), f (j • Q) = ∑ k ∈ Finset.Icc 1 n, f (k • Q) := by
    have hset : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
  have hC : ∑ j ∈ Finset.Ico (n + 1) (2 * n + 1), f (j • Q) =
      ∑ k ∈ Finset.Icc 1 n, f (-(k • Q)) := by
    refine Finset.sum_nbij' (fun j => 2 * n + 1 - j) (fun k => 2 * n + 1 - k)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_Icc]
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      change 2 * n + 1 - (2 * n + 1 - j) = j
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      change 2 * n + 1 - (2 * n + 1 - k) = k
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hN : (2 * n + 1) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
      have he : (2 * n + 1 - j) • Q + j • Q = 0 := by
        rw [← add_nsmul, Nat.sub_add_cancel (by omega), hN]
      rw [eq_neg_of_add_eq_zero_left he, neg_neg]
  rw [hA, hB, hC, add_assoc, ← Finset.sum_add_distrib]

end Dubon2026.SourceEllipticFunctionField
