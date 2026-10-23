import Dubon2026.SourceEllipticOddReindex

/-! Reindexing the actual odd cyclic subgroup for its quotient
discriminant. This supplies the doubling permutation and orbit-trace identities
used to prove the odd quotient elliptic, then the prime quotient products and
inertia census required by DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing coordinate injectivity
supplies finite sums and products; no cardinality or permutation is assumed. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
section Trace

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

/-- The finite odd Velu x-coordinate sum. -/
def xvSum (V : WeierstrassCurve F) (Q : V.toAffine.Point) (n : ℕ) (v : F) : F :=
  v + ∑ k ∈ Finset.Icc 1 n,
    (veluT V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2 / (v - ((coordsOrZero (k • Q))).1)
      + veluU V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2
          / (v - ((coordsOrZero (k • Q))).1) ^ 2)

/-- Sum of x-coordinates over the actual cyclic orbit. -/
def orbitTrace (V : WeierstrassCurve F) (Q : V.toAffine.Point) (n : ℕ)
    (P : V.toAffine.Point) : F :=
  ∑ j ∈ Finset.range (2 * n + 1), ((coordsOrZero (P + j • Q))).1

theorem orbitTrace_add_right (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) :
    orbitTrace V Q n (P + Q) = orbitTrace V Q n P := by
  have hN : (2 * n + 1) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  unfold orbitTrace
  have key : ∀ j : ℕ, P + Q + j • Q = P + (j + 1) • Q := by
    intro j
    rw [succ_nsmul]
    abel
  simp only [key]
  have h1 := Finset.sum_range_succ' (fun j => ((coordsOrZero (P + j • Q))).1) (2 * n + 1)
  have h2 := Finset.sum_range_succ (fun j => ((coordsOrZero (P + j • Q))).1) (2 * n + 1)
  have hf : ((coordsOrZero (P + (2 * n + 1) • Q))).1 = ((coordsOrZero (P + 0 • Q))).1 := by
    rw [hN, zero_nsmul]
  have hcomb := h1.symm.trans h2
  rw [hf] at hcomb
  simpa using add_right_cancel hcomb

theorem orbitTrace_add_smul (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) (m : ℕ) :
    orbitTrace V Q n (P + m • Q) = orbitTrace V Q n P := by
  induction m with
  | zero => rw [zero_nsmul, add_zero]
  | succ m ih =>
    have : P + (m + 1) • Q = P + m • Q + Q := by rw [succ_nsmul]; abel
    rw [this, orbitTrace_add_right hQ, ih]

theorem orbitTrace_fold (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) :
    orbitTrace V Q n P = ((coordsOrZero P)).1
      + ∑ k ∈ Finset.Icc 1 n,
          (((coordsOrZero (P + k • Q))).1 + ((coordsOrZero (P - k • Q))).1) := by
  unfold orbitTrace
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun j => ((coordsOrZero (P + j • Q))).1)
      (by omega : (0 : ℕ) ≤ n + 1) (by omega : n + 1 ≤ 2 * n + 1),
    ← Finset.sum_Ico_consecutive (fun j => ((coordsOrZero (P + j • Q))).1)
      (by omega : (0 : ℕ) ≤ 1) (by omega : (1 : ℕ) ≤ n + 1)]
  have hA : ∑ j ∈ Finset.Ico 0 1, ((coordsOrZero (P + j • Q))).1 = ((coordsOrZero P)).1 := by
    simp
  have hB : ∑ j ∈ Finset.Ico 1 (n + 1), ((coordsOrZero (P + j • Q))).1
      = ∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (P + k • Q))).1 := by
    have hset : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
  have hC : ∑ j ∈ Finset.Ico (n + 1) (2 * n + 1), ((coordsOrZero (P + j • Q))).1
      = ∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (P - k • Q))).1 := by
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
      rw [sub_smul_eq_neg_smul hQ (show j ≤ 2 * n + 1 by omega), sub_neg_eq_add]
  rw [hA, hB, hC, add_assoc, ← Finset.sum_add_distrib]

end Trace


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
