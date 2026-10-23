import Dubon2026.SourceEllipticOddCharTwoKernelCoordinates
import Dubon2026.SourceEllipticOddCharTwoNorm

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
theorem odd_quotient_discriminant_of_ordinary_model {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (h2 : (2 : K) = 0) (V : WeierstrassCurve K) (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0)
    (ha₄ : V.a₄ = 0) [V.IsElliptic] {n : ℕ} (Q : V.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient V (oddOrderSummingSet V Q n)).Δ *
        (∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) := by
  have hΔ : V.Δ = V.a₆ :=
    Δ_V h2 V ha₁ ha₃ ha₄
  have hrow : (veluQuotient V (oddOrderSummingSet V Q n)).Δ *
          (∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2) ^ 4
        = V.Δ ^ (2 * n + 1) ↔
      (V.a₆ + (∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1)
          + (∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1) ^ 2)
        * (∏ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1 ^ 2) ^ 4
      = V.a₆ ^ (2 * (Finset.Icc 1 n).card + 1) :=
    row_iff_chain h2 V ha₁ ha₃ ha₄ hQ
  let xv : K → K :=
    xvSum V Q n
  have hxv : ∀ v, xv v = v + ∑ k ∈ Finset.Icc 1 n,
      (((coordsOrZero (k • Q))).1 / (v - ((coordsOrZero (k • Q))).1)
        + ((coordsOrZero (k • Q))).1 ^ 2 / (v - ((coordsOrZero (k • Q))).1) ^ 2) :=
    xvSum_V h2 V ha₁ ha₃ ha₄ hQ
  have hx0 : ∀ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1 ≠ 0 :=
    fun _ hk => xk_ne_zero h2 V ha₁ ha₃ hQ (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  have hinj : Set.InjOn (fun k : ℕ => ((coordsOrZero (k • Q))).1) (Finset.Icc 1 n) :=
    xco_nsmul_injOn hQ
  have hne : ∀ T : V.toAffine.Point, T ≠ 0 → (2 : ℕ) • T = 0 → ∀ (j : ℕ) {k : ℕ}, 1 ≤ k → k ≤ n →
      ((coordsOrZero (T + j • Q))).1 ≠ ((coordsOrZero (k • Q))).1 :=
    fun _ hT0 hT2 j _ hk1 hkn => coset_xco_ne_kernel hQ hT0 hT2 j hk1 hkn
  have hcoset : ∀ T : V.toAffine.Point, T ≠ 0 → (2 : ℕ) • T = 0 → ∀ m : ℕ,
      xv ((coordsOrZero (T + m • Q))).1 = xv ((coordsOrZero T)).1 :=
    fun _ hT0 hT2 m => xvSum_coset hQ hT0 hT2 m
  obtain ⟨c, hc'⟩ := IsAlgClosed.exists_eq_mul_self V.a₆
  have hc : c ^ 2 = V.a₆ := (sq c).trans hc'.symm
  have ha₆ : V.a₆ ≠ 0 := hΔ ▸ V.isUnit_Δ.ne_zero
  have hT : V.toAffine.Nonsingular 0 c := nonsingular_twoTorsion ha₃ ha₄ hc
  have hT0 : (Affine.Point.some 0 c hT : V.toAffine.Point) ≠ 0 := Affine.Point.some_ne_zero hT
  have hT2 : (2 : ℕ) • (Affine.Point.some 0 c hT : V.toAffine.Point) = 0 := by
    rw [two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (negY_twoTorsion h2 ha₃ c).symm
  have hξ : ∀ k ∈ Finset.Icc 1 n, ((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1
      = c / ((coordsOrZero (k • Q))).1 := by
    intro k hk
    have hxk := hx0 k hk
    rcases hP : k • Q with _ | ⟨xk, yk, hk'⟩
    · rw [hP, coordsOrZero] at hxk
      exact absurd rfl hxk
    · rw [hP, coordsOrZero] at hxk
      rw [coordsOrZero]
      exact coordsOrZero_twoTorsion_add_fst h2 ha₁ ha₃ ha₄ hT hc hk' hxk
  have hxv0 : xv 0 = 0 := by
    rw [hxv, zero_add]
    exact Finset.sum_eq_zero fun k _ => by field_simp; ring
  have hvan : ∀ k ∈ Finset.Icc 1 n, ((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1
      + ∑ j ∈ Finset.Icc 1 n,
        (((coordsOrZero (j • Q))).1 / (((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1
            - ((coordsOrZero (j • Q))).1)
          + ((coordsOrZero (j • Q))).1 ^ 2 / (((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1
            - ((coordsOrZero (j • Q))).1) ^ 2) = 0 := by
    intro k _
    have h1 := hcoset (Affine.Point.some 0 c hT) hT0 hT2 k
    rw [coordsOrZero, hxv0, hxv] at h1
    exact h1
  have hξx : ∀ k ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n,
      ((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1 ≠ ((coordsOrZero (j • Q))).1 :=
    fun k _ j hj => hne _ hT0 hT2 k (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have key := char_two_chain (Finset.Icc 1 n) (fun k => ((coordsOrZero (k • Q))).1) h2
    (fun k => ((coordsOrZero (Affine.Point.some 0 c hT + k • Q))).1) V.a₆ c hc ha₆ hx0 hinj
    hξ hξx hvan
  exact hrow.mpr key


theorem odd_quotient_isElliptic_of_ordinary_model {K : Type*}
    [Field K] [DecidableEq K] [IsAlgClosed K] (h2 : (2 : K) = 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)
    [V.IsElliptic] {n : ℕ} (Q : V.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient V (oddOrderSummingSet V Q n)).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  have h := odd_quotient_discriminant_of_ordinary_model h2 V ha₁ ha₃ ha₄ Q hQ
  rw [hΔ, zero_mul] at h
  exact pow_ne_zero _ V.isUnit_Δ.ne_zero h.symm

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
