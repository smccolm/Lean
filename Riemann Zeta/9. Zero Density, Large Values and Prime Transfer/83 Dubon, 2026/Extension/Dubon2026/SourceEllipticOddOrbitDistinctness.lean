import Dubon2026.SourceEllipticOddCurveCoordinates

/-! Actual odd-orbit coordinate inputs for quotient ellipticity.
The native point group and already proved coordinate identities supply
distinct translated roots and the two-torsion fiber factorization. These
serve the explicit quotient discriminant, prime quotient products and
cyclic-subgroup inertia census required by DUB-17 / DUB-18.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native finite-order nonvanishing
replaces the duplicate divisibility proof. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Polynomial
open Algebra
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
/-- Actual point x-coordinate, fixed to zero at infinity. -/
def xco (P : V.toAffine.Point) : F := (coordsOrZero P).1

omit [DecidableEq F] in
theorem eq_or_eq_neg_of_xco_eq {P P' : V.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (h : xco P = xco P') : P = P' ∨ P = -P' := by
  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨a', b', hab'⟩
  · exact absurd rfl hP'
  exact (Affine.Point.X_eq_iff (h₁ := hab) (h₂ := hab')).mp h

variable {Q z : V.toAffine.Point} {n : ℕ}

theorem good_add_nsmul_ne_zero (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0) (j : ℕ) : z + j • Q ≠ 0 := by
  intro h
  apply hz (2 * j)
  rw [mul_nsmul', ← nsmul_add, h, nsmul_zero]

theorem good_xco_ne (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0)
    {j₁ j₂ : ℕ} (hlt : j₁ < j₂) (hlt' : j₂ < j₁ + (2 * n + 1)) :
    xco (z + j₁ • Q) ≠ xco (z + j₂ • Q) := by
  intro h
  rcases eq_or_eq_neg_of_xco_eq (good_add_nsmul_ne_zero hz j₁) (good_add_nsmul_ne_zero hz j₂) h
    with e | e
  · have h0 : (j₂ - j₁) • Q = 0 := by
      have e2 : z + j₁ • Q + (j₂ - j₁) • Q = z + j₁ • Q + 0 := by
        rw [add_zero, add_assoc, ← add_nsmul, Nat.add_sub_cancel' hlt.le, ← e]
      exact add_left_cancel e2
    have hdvd : 2 * n + 1 ∣ j₂ - j₁ := hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · apply hz (j₁ + j₂)
    have e2 : z + j₁ • Q + (z + j₂ • Q) = 0 := by rw [e, neg_add_cancel]
    rw [two_nsmul, add_nsmul, ← e2]
    abel

theorem good_xco_ne_kernel (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0)
    (j k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * n) : xco (z + j • Q) ≠ xco (k • Q) := by
  intro h
  have hk0 : k • Q ≠ 0 := kernel_ne_zero hQ hk1 hk
  rcases eq_or_eq_neg_of_xco_eq (good_add_nsmul_ne_zero hz j) hk0 h with e | e
  · apply good_add_nsmul_ne_zero hz (j + (2 * n + 1 - k))
    rw [add_nsmul, ← add_assoc, e, ← add_nsmul, Nat.add_sub_cancel' (by omega : k ≤ 2 * n + 1),
      ← hQ, addOrderOf_nsmul_eq_zero]
  · apply good_add_nsmul_ne_zero hz (j + k)
    rw [add_nsmul, ← add_assoc, e, neg_add_cancel]

theorem good_distinct (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0) :
    (∀ k ∈ Finset.Icc 1 n, xco z ≠ xco (z + k • Q))
    ∧ (∀ k ∈ Finset.Icc 1 n, xco z ≠ xco (z + (2 * n + 1 - k) • Q))
    ∧ Set.InjOn (fun k => xco (z + k • Q)) (↑(Finset.Icc 1 n) : Set ℕ)
    ∧ Set.InjOn (fun k => xco (z + (2 * n + 1 - k) • Q)) (↑(Finset.Icc 1 n) : Set ℕ)
    ∧ (∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
        xco (z + k • Q) ≠ xco (z + (2 * n + 1 - k') • Q)) := by
  have hz0 : xco z = xco (z + 0 • Q) := by rw [zero_nsmul, add_zero]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk k' hk' e => ?_, fun k hk k' hk' e => ?_,
    fun k hk k' hk' => ?_⟩
  · rw [Finset.mem_Icc] at hk
    rw [hz0]
    exact good_xco_ne hQ hz (by omega) (by omega)
  · rw [Finset.mem_Icc] at hk
    rw [hz0]
    exact good_xco_ne hQ hz (by omega) (by omega)
  · rw [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact good_xco_ne hQ hz hlt (by omega) e
    · exact good_xco_ne hQ hz hlt (by omega) e.symm
  · rw [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact good_xco_ne hQ hz (j₁ := 2 * n + 1 - k') (j₂ := 2 * n + 1 - k) (by omega) (by omega)
        e.symm
    · exact good_xco_ne hQ hz (j₁ := 2 * n + 1 - k) (j₂ := 2 * n + 1 - k') (by omega) (by omega) e
  · rw [Finset.mem_Icc] at hk hk'
    exact good_xco_ne hQ hz (by omega) (by omega)


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
