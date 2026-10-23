import Dubon2026.SourceEllipticOddOrbitInvariance
import Dubon2026.SourceEllipticOddSummingStructure

/-! Actual characteristic-two ordinary quotient coordinates and discriminant.
The odd summing-set equation, nonzero tangent term and x-coordinate injection
are reused from the proved actual torsion structure. The quotient-coordinate
orbit trace supplies the two-torsion coset identities. These discharge the
finite norm premises for odd quotient ellipticity, then cyclic quotient
products, inertia census and good reduction in DUB-17 / DUB-18.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
section CosetFacts

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

theorem two_torsion_ne_nsmul (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (m : ℕ) : T ≠ m • Q := by
  intro hTm
  apply hT0
  have h1 : (2 * n + 1) • T = 0 := by
    rw [hTm, ← mul_nsmul', mul_comm, mul_nsmul', ← hQ, addOrderOf_nsmul_eq_zero, nsmul_zero]
  have h2 : (2 * n + 1 + 1) • T = 0 := by
    have he : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [he, mul_comm, mul_nsmul', hT2, nsmul_zero]
  rw [succ_nsmul, h1, zero_add] at h2
  exact h2

theorem coset_rel_nsmul (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (i c : ℕ) (h : T + i • Q = c • Q) :
    T = (c + (2 * n + 1 - i % (2 * n + 1))) • Q := by
  have hmod : (i % (2 * n + 1)) • Q = i • Q := by
    rw [← hQ]
    exact mod_addOrderOf_nsmul Q i
  have hlt : i % (2 * n + 1) < 2 * n + 1 := Nat.mod_lt _ (by omega)
  have key : T + (i % (2 * n + 1)) • Q = c • Q := by rw [hmod]; exact h
  have hNQ : (2 * n + 1) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  have hsum : T + ((i % (2 * n + 1)) + (2 * n + 1 - i % (2 * n + 1))) • Q
      = (c + (2 * n + 1 - i % (2 * n + 1))) • Q := by
    rw [add_nsmul, ← add_assoc, key, ← add_nsmul]
  rwa [Nat.add_sub_cancel' (le_of_lt hlt), hNQ, add_zero] at hsum

theorem coset_add_nsmul_ne_zero (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (j : ℕ) : T + j • Q ≠ 0 := by
  intro h
  exact two_torsion_ne_nsmul hQ hT0 hT2 _
    (coset_rel_nsmul hQ j 0 (by rw [h, zero_nsmul]))

theorem coset_xco_ne_kernel (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (j : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((coordsOrZero (T + j • Q))).1 ≠ ((coordsOrZero (k • Q))).1 := by
  intro heq
  have hTj : T + j • Q ≠ 0 := coset_add_nsmul_ne_zero hQ hT0 hT2 j
  have hkQ : k • Q ≠ 0 := kernel_ne_zero hQ hk1 (by omega)
  obtain ⟨x, y, h, hPeq, hPc⟩ := exists_affine_coords_of_ne_zero hTj
  obtain ⟨x', y', h', hkeq, hkc⟩ := exists_affine_coords_of_ne_zero hkQ
  have hxx : x = x' := by
    have e1 : ((coordsOrZero (T + j • Q))).1 = x := by rw [hPc]
    have e2 : ((coordsOrZero (k • Q))).1 = x' := by rw [hkc]
    rw [e1, e2] at heq
    exact heq
  rcases (Affine.Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hxx with hc | hc
  · refine two_torsion_ne_nsmul hQ hT0 hT2 _ (coset_rel_nsmul hQ j k ?_)
    rw [hPeq, hkeq, hc]
  · refine two_torsion_ne_nsmul hQ hT0 hT2 _ (coset_rel_nsmul hQ (j + k) 0 ?_)
    have h1 : T + j • Q = -(k • Q) := by rw [hPeq, hkeq, hc]
    rw [zero_nsmul, add_nsmul, ← add_assoc, h1, neg_add_cancel]

theorem xco_nsmul_injOn (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (fun k : ℕ => (coordsOrZero (k • Q)).1) (Finset.Icc 1 n : Finset ℕ) := by
  intro k hk l hl hx
  have hk' := Finset.mem_Icc.mp hk
  have hl' := Finset.mem_Icc.mp hl
  apply coordsOrZero_odd_nsmul_injOn hQ hk hl
  exact (isOddVeluSet_oddOrderSummingSet hQ).x_injOn _
    (mem_oddOrderSummingSet.mpr ⟨k, hk'.1, hk'.2, rfl⟩) _
    (mem_oddOrderSummingSet.mpr ⟨l, hl'.1, hl'.2, rfl⟩) hx

theorem xvSum_coset (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (m : ℕ) :
    xvSum V Q n (((coordsOrZero (T + m • Q))).1) = xvSum V Q n (((coordsOrZero T)).1) :=
  xvSum_orbit_const' hQ (coset_add_nsmul_ne_zero hQ hT0 hT2)
    (fun j _ hk1 hkn => coset_xco_ne_kernel hQ hT0 hT2 j hk1 hkn) m


end CosetFacts

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
