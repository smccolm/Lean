import Dubon2026.SourceEllipticOddSummingStructure

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
section Reindex

variable {V : Affine F}

omit [DecidableEq F] in

theorem coordsOrZero_neg_fst (P : V.Point) :
    (coordsOrZero (-P)).1 = (coordsOrZero P).1 := by
  cases P <;> rfl

theorem sub_smul_eq_neg_smul {Q : V.Point} {N m : ℕ} (hN : addOrderOf Q = N) (hm : m ≤ N) :
    (N - m) • Q = -(m • Q) := by
  have h0 : N • Q = 0 := by rw [← hN]; exact addOrderOf_nsmul_eq_zero Q
  have hadd : (N - m) • Q + m • Q = 0 := by
    rw [← add_nsmul, Nat.sub_add_cancel hm, h0]
  exact eq_neg_of_add_eq_zero_left hadd

theorem coordsOrZero_sub_smul_fst {Q : V.Point} {N m : ℕ} (hN : addOrderOf Q = N)
    (hm : m ≤ N) :
    (coordsOrZero ((N - m) • Q)).1 = (coordsOrZero (m • Q)).1 := by
  rw [sub_smul_eq_neg_smul hN hm, coordsOrZero_neg_fst]

/-- Doubling modulo the sign of an odd cyclic subgroup. -/
def fold2 (n k : ℕ) : ℕ := if 2 * k ≤ n then 2 * k else 2 * n + 1 - 2 * k

/-- Inverse index for doubling modulo sign. -/
def unfold2 (n m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else (2 * n + 1 - m) / 2

theorem fold2_mem {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) : fold2 n k ∈ Finset.Icc 1 n := by
  simp only [Finset.mem_Icc] at *
  unfold fold2
  split <;> omega

theorem unfold2_fold2 {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) : unfold2 n (fold2 n k) = k := by
  simp only [Finset.mem_Icc] at hk
  unfold fold2 unfold2
  split <;> split <;> omega

theorem coordsOrZero_fold2_smul_fst {Q : V.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    (coordsOrZero ((fold2 n k) • Q)).1 = (coordsOrZero ((2 * k) • Q)).1 := by
  simp only [Finset.mem_Icc] at hk
  unfold fold2
  split
  · rfl
  · exact coordsOrZero_sub_smul_fst hQ (by omega)

end Reindex


variable {V : WeierstrassCurve F}

theorem image_fold2_Icc (n : ℕ) : (Finset.Icc 1 n).image (fold2 n) = Finset.Icc 1 n := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    exact fold2_mem hk
  · rw [Finset.card_image_of_injOn (fun k hk k' hk' h => by
      have := congrArg (unfold2 n) h
      rwa [unfold2_fold2 hk, unfold2_fold2 hk'] at this)]

theorem multiset_map_double {Q : V.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) :
    (Finset.Icc 1 n).val.map (fun k => (coordsOrZero ((2 : ℕ) • (k • Q))).1)
      = (Finset.Icc 1 n).val.map (fun k => (coordsOrZero ((k : ℕ) • Q)).1) := by
  have hstep : ∀ k ∈ (Finset.Icc 1 n).val,
      (coordsOrZero ((2 : ℕ) • (k • Q))).1 = ((coordsOrZero (fold2 n k • Q))).1 := by
    intro k hk
    rw [coordsOrZero_fold2_smul_fst hQ (by simpa using hk), smul_smul]
  rw [Multiset.map_congr rfl hstep]
  have himg : (Finset.Icc 1 n).val.map (fold2 n) = (Finset.Icc 1 n).val := by
    have hinj : Set.InjOn (fold2 n) (Finset.Icc 1 n) := fun k hk k' hk' h => by
      have := congrArg (unfold2 n) h
      rwa [unfold2_fold2 (by simpa using hk), unfold2_fold2 (by simpa using hk')] at this
    rw [← Finset.image_val_of_injOn hinj, image_fold2_Icc]
  calc (Finset.Icc 1 n).val.map (fun k => ((coordsOrZero (fold2 n k • Q))).1)
      = ((Finset.Icc 1 n).val.map (fold2 n)).map (fun m => ((coordsOrZero (m • Q))).1) := by
        rw [Multiset.map_map]; rfl
    _ = (Finset.Icc 1 n).val.map (fun m => ((coordsOrZero (m • Q))).1) := by rw [himg]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
