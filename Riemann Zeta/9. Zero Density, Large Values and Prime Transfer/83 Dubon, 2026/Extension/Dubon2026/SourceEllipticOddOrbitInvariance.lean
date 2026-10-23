import Dubon2026.SourceEllipticOddOrbitTrace
import Dubon2026.SourceEllipticOddCurveCoordinates

/-! The actual odd quotient x-coordinate is constant on kernel translates.
The chord sum identifies it with the proved finite cyclic orbit trace minus
a fixed kernel sum. This discharges the translation-invariance premise of
the odd norm identity, needed for quotient ellipticity and products, the
inertia census and modular-curve good reduction in DUB-17 / DUB-18.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem exists_affine_coords_of_ne_zero {V : WeierstrassCurve F}
    {P : V.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : V.toAffine.Nonsingular x y),
      P = .some x y h ∧ coordsOrZero P = (x, y) := by
  obtain ⟨h, he⟩ := affine_decomp P hP
  exact ⟨_, _, h, he, rfl⟩

section TraceTwins

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

theorem xvSum_eq_orbitTrace' (hQ : addOrderOf Q = 2 * n + 1) {xP yP : F}
    (hns : V.toAffine.Nonsingular xP yP)
    (hx : ∀ k, 1 ≤ k → k ≤ n → xP ≠ ((coordsOrZero (k • Q))).1) :
    xvSum V Q n xP
      = orbitTrace V Q n (Affine.Point.some xP yP hns)
        - 2 * ∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1 := by
  rw [orbitTrace_fold hQ]
  have hper : ∀ k ∈ Finset.Icc 1 n,
      ((coordsOrZero (Affine.Point.some xP yP hns + k • Q))).1
        + ((coordsOrZero (Affine.Point.some xP yP hns - k • Q))).1
      = 2 * ((coordsOrZero (k • Q))).1
        + (veluT V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2
            / (xP - ((coordsOrZero (k • Q))).1)
          + veluU V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2
            / (xP - ((coordsOrZero (k • Q))).1) ^ 2) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨xk, yk, hknd, hkeq, hkc⟩ :=
      exists_affine_coords_of_ne_zero (kernel_ne_zero hQ hk.1 (by omega))
    have hxk : xP ≠ xk := by
      have := hx k hk.1 hk.2
      rwa [hkc] at this
    have hadd : Affine.Point.some xP yP hns + k • Q
        = Affine.Point.some _ _ (Affine.nonsingular_add hns hknd
            (fun hxy => absurd hxy.1 hxk)) := by
      rw [hkeq]
      exact Affine.Point.add_some (fun hxy => absurd hxy.1 hxk)
    have hneg : -(k • Q) = Affine.Point.some xk (V.toAffine.negY xk yk)
        ((Affine.nonsingular_neg ..).mpr hknd) := by
      rw [hkeq, Affine.Point.neg_some]
    have hsub : Affine.Point.some xP yP hns - k • Q
        = Affine.Point.some _ _ (Affine.nonsingular_add hns
            ((Affine.nonsingular_neg ..).mpr hknd) (fun hxy => absurd hxy.1 hxk)) := by
      rw [sub_eq_add_neg, hneg]
      exact Affine.Point.add_some (fun hxy => absurd hxy.1 hxk)
    rw [hadd, hsub, hkc]
    simp only [coordsOrZero]
    linear_combination chord_sum' V hns.1 hknd.1 hxk
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.mul_sum, xvSum]
  simp only [coordsOrZero]
  ring

theorem xvSum_orbit_const' (hQ : addOrderOf Q = 2 * n + 1) {P : V.toAffine.Point}
    (haff : ∀ j : ℕ, P + j • Q ≠ 0)
    (hx : ∀ j : ℕ, ∀ k, 1 ≤ k → k ≤ n →
      ((coordsOrZero (P + j • Q))).1 ≠ ((coordsOrZero (k • Q))).1) (m : ℕ) :
    xvSum V Q n (((coordsOrZero (P + m • Q))).1) = xvSum V Q n (((coordsOrZero P)).1) := by
  obtain ⟨xP, yP, hPns, hPeq, hPc⟩ := exists_affine_coords_of_ne_zero
    (by simpa using haff 0)
  obtain ⟨xM, yM, hMns, hMeq, hMc⟩ := exists_affine_coords_of_ne_zero (haff m)
  have hxP : ∀ k, 1 ≤ k → k ≤ n → xP ≠ ((coordsOrZero (k • Q))).1 := by
    intro k h1 h2
    have := hx 0 k h1 h2
    rwa [zero_nsmul, add_zero, hPeq, coordsOrZero] at this
  have hxM : ∀ k, 1 ≤ k → k ≤ n → xM ≠ ((coordsOrZero (k • Q))).1 := by
    intro k h1 h2
    have := hx m k h1 h2
    rwa [hMeq, coordsOrZero] at this
  have e1 := xvSum_eq_orbitTrace' hQ hPns hxP
  have e2 := xvSum_eq_orbitTrace' hQ hMns hxM
  have htr : orbitTrace V Q n (Affine.Point.some xM yM hMns)
      = orbitTrace V Q n (Affine.Point.some xP yP hPns) := by
    rw [← hMeq, ← hPeq]
    rw [orbitTrace_add_smul hQ P m]
  rw [hMc, hPc]
  rw [e1, e2, htr]


end TraceTwins

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
