import Dubon2026.RealWhittakerCoefficients

/-! # The exact classical-to-unitary Whittaker normalization -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups CongruenceSubgroup

/-- The actual holomorphic archimedean Whittaker factor on positive height. -/
def holomorphicWhittaker (k : ℤ) (y : ℝ) : ℂ :=
  ((y ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-2 * Real.pi * y) : ℂ)

/-- The original square-root slash factor is exactly the half-weight real power. -/
theorem sqrt_zpow_eq_half_weight (k : ℤ) {y : ℝ} (hy : 0 < y) :
    ((Real.sqrt y : ℝ) : ℂ) ^ k = ((y ^ ((k : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_zpow, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul hy.le]
  congr 2
  ring

/-- The actual unipotent coefficient has precisely λ(n)/sqrt(n) times the holomorphic archimedean factor at ny. -/
theorem realWhittakerCoefficient_normalized {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n) :
    realWhittakerCoefficient f hy (n : ℤ) = normalizedCuspCoefficients f n *
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * holomorphicWhittaker k ((n : ℝ) * y) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : (n : ℝ) ^ (-((k : ℝ) - 1) / 2) * (n : ℝ) ^ (-(1 : ℝ) / 2) *
      (n : ℝ) ^ ((k : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
    rw [show -((k : ℝ) - 1) / 2 + -(1 : ℝ) / 2 + (k : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  rw [realWhittakerCoefficient_nat, sqrt_zpow_eq_half_weight k hy,
    normalizedCuspCoefficients, shiftedCoefficients, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hnR.le, holomorphicWhittaker,
    Real.mul_rpow hnR.le hy.le]
  simp only [Complex.ofReal_mul]
  have heC := congrArg (fun x : ℝ => (x : ℂ)) he
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at heC
  have hx : -2 * Real.pi * n * y = -2 * Real.pi * ((n : ℝ) * y) := by ring
  rw [hx]
  calc
    _ = cuspCoefficients f n *
        ((((n : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
          (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
          (((n : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) *
        (((y ^ ((k : ℝ) / 2) : ℝ)) : ℂ) *
        (Real.exp (-2 * Real.pi * ((n : ℝ) * y)) : ℂ) := by rw [heC, mul_one]
    _ = _ := by ring

/-- At height y, normalization of the original first coefficient gives the exact archimedean vector. -/
theorem realWhittakerCoefficient_one {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : cuspCoefficients f 1 = 1) {y : ℝ} (hy : 0 < y) :
    realWhittakerCoefficient f hy 1 = holomorphicWhittaker k y := by
  simpa [hf, holomorphicWhittaker, sqrt_zpow_eq_half_weight k hy] using
    realWhittakerCoefficient_nat f hy 1

end
end Dubon2026
