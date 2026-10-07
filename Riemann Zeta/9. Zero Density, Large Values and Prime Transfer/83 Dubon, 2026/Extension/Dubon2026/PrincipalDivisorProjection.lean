import Dubon2026.PrincipalTranslation

/-! # Actual finite translation averages extract divisible Fourier indices -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The genuine average of f(z+bN/d), for d dividing the principal level. -/
def principalDivisorProjection (N : ℕ) (k : ℤ) (d : ℕ) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k :=
  (d : ℂ)⁻¹ • ∑ b ∈ Finset.range d, principalTranslation N k (b * (N / d) : ℕ)

/-- One translation step has exactly the primitive d-th root of unity as its period-N phase. -/
theorem qParam_divisor_step {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) :
    Function.Periodic.qParam N (N / d : ℕ) = Function.Periodic.qParam 1 (1 / (d : ℂ)) := by
  have hq : N / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hd)
    (Nat.pos_of_neZero d)).ne'
  have hmul : (N : ℂ) = (d : ℂ) * (N / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  unfold Function.Periodic.qParam
  congr 1
  simp only [Complex.ofReal_natCast, Complex.ofReal_one]
  rw [hmul]
  field_simp
  rw [div_mul_eq_div_div, div_self (show ((N / d : ℕ) : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hq)]

/-- The literal finite translation average preserves exactly the coefficients on multiples of d. -/
theorem principalDivisorProjection_coeff {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalDivisorProjection N k d f) n =
      if d ∣ n then principalCuspCoefficients f n else 0 := by
  let L := principalCuspCoefficientLinear N k n
  change L (principalDivisorProjection N k d f) = _
  simp only [principalDivisorProjection, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  change (d : ℂ)⁻¹ • (∑ b ∈ Finset.range d,
    principalCuspCoefficients (principalTranslation N k (b * (N / d) : ℕ) f) n) = _
  simp only [principalTranslation_coeff, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    qParam_nat_mul_eq_pow, qParam_divisor_step hd, ← pow_mul]
  simp_rw [mul_comm _ n]
  rw [← Finset.mul_sum, sum_qParam_reciprocal_pow]
  split_ifs with hdn
  · simp [smul_eq_mul, Nat.cast_ne_zero.mpr (NeZero.ne d), mul_comm]
  · simp

/-- Every actual divisor average is idempotent. -/
theorem principalDivisorProjection_idempotent {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ) : IsIdempotentElem (principalDivisorProjection N k d) := by
  apply LinearMap.ext
  intro f
  apply principalCuspCoefficients_injective N k
  funext n
  change principalCuspCoefficients (principalDivisorProjection N k d
    (principalDivisorProjection N k d f)) n = principalCuspCoefficients (principalDivisorProjection N k d f) n
  simp only [principalDivisorProjection_coeff hd]
  split_ifs <;> rfl

/-- Divisor averages commute as genuine cusp-form endomorphisms. -/
theorem principalDivisorProjection_commute {N d e : ℕ} [NeZero N] [NeZero d] [NeZero e]
    (hd : d ∣ N) (he : e ∣ N) (k : ℤ) :
    Commute (principalDivisorProjection N k d) (principalDivisorProjection N k e) := by
  apply LinearMap.ext
  intro f
  apply principalCuspCoefficients_injective N k
  funext n
  change principalCuspCoefficients (principalDivisorProjection N k d
    (principalDivisorProjection N k e f)) n = principalCuspCoefficients (principalDivisorProjection N k e
      (principalDivisorProjection N k d f)) n
  simp only [principalDivisorProjection_coeff hd, principalDivisorProjection_coeff he]
  split_ifs <;> rfl

/-- Fixed vectors of the actual average are precisely forms supported on multiples of d. -/
theorem principalDivisorProjection_fixed_iff {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    principalDivisorProjection N k d f = f ↔
      ∀ n, ¬d ∣ n → principalCuspCoefficients f n = 0 := by
  constructor
  · intro hf n hn
    have h := congrArg (fun g => principalCuspCoefficients g n) hf
    simpa only [principalDivisorProjection_coeff hd, if_neg hn] using h.symm
  · intro hf
    apply principalCuspCoefficients_injective N k
    funext n
    rw [principalDivisorProjection_coeff hd]
    split_ifs with hn
    · rfl
    · exact (hf n hn).symm

end
end Dubon2026
