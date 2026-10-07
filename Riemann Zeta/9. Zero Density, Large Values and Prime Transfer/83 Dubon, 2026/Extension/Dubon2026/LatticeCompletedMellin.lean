import Dubon2026.LatticeThetaFEPair

/-! # Continuation and residues of the actual completed lattice theta Mellin transform -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The meromorphic theta Mellin transform, with the actual half-lattice normalization. -/
def latticeCompletedMellin (z : ℍ) (s : ℂ) : ℂ := (latticeThetaFEPair z).Λ s / 2

/-- The entire regular part of the actual theta Mellin continuation. -/
def latticeCompletedMellinRegular (z : ℍ) (s : ℂ) : ℂ := (latticeThetaFEPair z).Λ₀ s / 2

/-- The actual Mellin continuation differs from its entire regular part by exactly two polar terms. -/
theorem latticeCompletedMellin_eq_regular (z : ℍ) (s : ℂ) :
    latticeCompletedMellin z s = latticeCompletedMellinRegular z s - 1 / (2 * s) + 1 / (2 * (s - 1)) := by
  simp only [latticeCompletedMellin, latticeCompletedMellinRegular, WeakFEPair.Λ,
    latticeThetaFEPair, smul_eq_mul, mul_one, Complex.ofReal_one]
  rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual regularized theta Mellin integral is entire. -/
theorem differentiable_latticeCompletedMellinRegular (z : ℍ) :
    Differentiable ℂ (latticeCompletedMellinRegular z) :=
  (latticeThetaFEPair z).differentiable_Λ₀.div_const 2

/-- The actual theta Mellin continuation is holomorphic away from its two possible poles. -/
theorem differentiableAt_latticeCompletedMellin (z : ℍ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (latticeCompletedMellin z) s :=
  ((latticeThetaFEPair z).differentiableAt_Λ (Or.inl hs0) (Or.inl (by simpa [latticeThetaFEPair] using hs1))).div_const 2

/-- The genuine self-dual theta Mellin transform satisfies s↦1−s. -/
theorem latticeCompletedMellin_functional_equation (z : ℍ) (s : ℂ) :
    latticeCompletedMellin z (1 - s) = latticeCompletedMellin z s := by
  have h := (latticeThetaFEPair z).functional_equation s
  rw [latticeThetaFEPair_symm] at h
  simpa only [latticeThetaFEPair, Complex.ofReal_one, one_smul] using congrArg (fun w : ℂ => w / 2) h

/-- The genuine half-lattice theta Mellin transform has residue exactly 1/2 at s=1. -/
theorem latticeCompletedMellin_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * latticeCompletedMellin z s)
      (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) := by
  have h := ((latticeThetaFEPair z).Λ_residue_k).div_const (2 : ℂ)
  simpa only [latticeThetaFEPair, Complex.ofReal_one, smul_eq_mul, one_mul,
    latticeCompletedMellin, mul_div_assoc] using h

/-- The genuine half-lattice theta Mellin transform has residue exactly −1/2 at s=0. -/
theorem latticeCompletedMellin_residue_zero (z : ℍ) :
    Tendsto (fun s : ℂ => s * latticeCompletedMellin z s)
      (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) := by
  have h := ((latticeThetaFEPair z).Λ_residue_zero).div_const (2 : ℂ)
  simpa only [latticeThetaFEPair, smul_eq_mul, latticeCompletedMellin, mul_div_assoc] using h

/-- The actual full theta Mellin integral is absolutely convergent in its classical half-plane. -/
theorem integrableOn_latticeThetaMellinKernel_full (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (latticeThetaMellinKernel z s) (Ioi 0) := by
  have h := ((latticeThetaFEPair z).hasMellin hs).1
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (t : ℂ) ^ (s - 1) • ((latticeTheta z t : ℂ) - 1) = latticeThetaMellinKernel z s t
  rw [latticeThetaMellinKernel, latticeThetaRemainder_eq z ht,
    Complex.ofReal_sub, Complex.ofReal_one, smul_eq_mul]

/-- The continuation agrees with the literal full theta Mellin integral, with no integrability premise supplied. -/
theorem latticeCompletedMellin_eq_integral (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    latticeCompletedMellin z s = (∫ t : ℝ in Ioi 0, latticeThetaMellinKernel z s t) / 2 := by
  have h := ((latticeThetaFEPair z).hasMellin hs).2
  rw [latticeCompletedMellin, ← h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (t : ℂ) ^ (s - 1) • ((latticeTheta z t : ℂ) - 1) = latticeThetaMellinKernel z s t
  rw [latticeThetaMellinKernel, latticeThetaRemainder_eq z ht,
    Complex.ofReal_sub, Complex.ofReal_one, smul_eq_mul]

end
end Dubon2026
