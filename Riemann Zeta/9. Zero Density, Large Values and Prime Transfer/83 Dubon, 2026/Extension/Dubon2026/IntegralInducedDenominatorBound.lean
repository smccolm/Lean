import Dubon2026.IntegralInducedDeterminantDivisibility

/-! Uniform determinant denominators for the actual integral induced module.
The first-row weight is the last original weight because the source uses
w0(lambda). The proved original numerator divisibility cancels every
denominator above max(0,-lambda_last), without changing the function.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R]

/-- Increasing an actual determinant denominator and multiplying the original numerator by the same determinant power leaves the original regular function unchanged. -/
theorem generalLinearRegularFractionMap_add_detpow (n d e : ℕ)
    (P : MvPolynomial (Fin n × Fin n) R) :
    generalLinearRegularFractionMap R n (d + e)
      ((Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) ^ e * P) =
      generalLinearRegularFractionMap R n d P := by
  have hu : (generalLinearRegularDeterminantUnit (R := R) (n := n) ^ (d + e))⁻¹ *
      generalLinearRegularDeterminantUnit ^ e = (generalLinearRegularDeterminantUnit ^ d)⁻¹ := by
    rw [pow_add, _root_.mul_inv_rev]
    group
  simp only [generalLinearRegularFractionMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply]
  rw [map_mul, map_pow, ← generalLinearRegularDeterminantUnit_val,
    ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul, hu]

/-- Cancelling one original determinant factor lowers the actual denominator by one. -/
theorem generalLinearRegularFractionMap_succ_det (n d : ℕ)
    (P : MvPolynomial (Fin n × Fin n) R) :
    generalLinearRegularFractionMap R n (d + 1)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) * P) =
      generalLinearRegularFractionMap R n d P := by
  simpa only [pow_one] using generalLinearRegularFractionMap_add_detpow R n d 1 P

variable [IsDomain R] [UniqueFactorizationMonoid R] [CharZero R]

/-- Every function in the literal integral induced module has the same determinant denominator bounded solely by the original final weight. -/
theorem integralInduced_exists_fixed_denominator {n : ℕ}
    (lam : Fin (n + 1) → ℤ)
    (p : generalLinearIntegralInducedSubmodule R (n + 1) lam) :
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R,
      generalLinearRegularFractionMap R (n + 1)
        (-lam (0 : Fin (n + 1)).rev).toNat P = p.val := by
  let B := (-lam (0 : Fin (n + 1)).rev).toNat
  have reduce : ∀ d (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R),
      generalLinearRegularFractionMap R (n + 1) d P = p.val →
      ∃ e, e ≤ B ∧ ∃ Q, generalLinearRegularFractionMap R (n + 1) e Q = p.val := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hP
      by_cases hd : d ≤ B
      · exact ⟨d, hd, P, hP⟩
      have hdpos : 0 < d := by omega
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
      have hmem : generalLinearRegularFractionMap R (n + 1) (e + 1) P ∈
          generalLinearIntegralInducedSubmodule R (n + 1) lam := hP ▸ p.property
      have ha : (fun i => lam i + ((e + 1 : ℕ) : ℤ)) (0 : Fin (n + 1)).rev ≠ 0 := by
        dsimp [B] at hd ⊢
        omega
      obtain ⟨Q, hQ⟩ := integralInducedPolynomial_determinant_dvd R
        (fun i => lam i + ((e + 1 : ℕ) : ℤ)) P
        (generalLinearIntegralInduced_polynomial_numerator R (n + 1) lam (e + 1) P hmem) ha
      apply ih e (Nat.lt_succ_self e) Q
      rw [hQ, generalLinearRegularFractionMap_succ_det] at hP
      exact hP
  obtain ⟨d, P, hP⟩ := generalLinearRegular_exists_fraction R (n + 1) p.val
  obtain ⟨e, he, Q, hQ⟩ := reduce d P hP
  refine ⟨Matrix.det (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) R) ^ (B - e) * Q, ?_⟩
  have h := generalLinearRegularFractionMap_add_detpow R (n + 1) e (B - e) Q
  have hs : e + (B - e) = B := by omega
  rw [hs, hQ] at h
  exact h

end
end Dubon2026
