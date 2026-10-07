import Dubon2026.LatticeThetaKernel
import Dubon2026.ShiftedGaussianPoisson

/-! # The absolutely convergent Fourier form of the lattice theta series -/

namespace Dubon2026

open UpperHalfPlane Complex

noncomputable section

/-- The actual two-dimensional Gaussian with its bilinear Fourier phase. -/
def latticeFourierTerm (a b x : ℝ) (v : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a * (v.1 : ℂ) ^ 2 + b * (v.2 : ℂ) ^ 2) +
    2 * Real.pi * Complex.I * v.1 * v.2 * x)

/-- The phase has unit modulus, leaving the exact product of real Gaussians. -/
theorem norm_latticeFourierTerm (a b x : ℝ) (v : ℤ × ℤ) :
    ‖latticeFourierTerm a b x v‖ =
      Real.exp (-Real.pi * a * (v.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * b * (v.2 : ℝ) ^ 2) := by
  rw [latticeFourierTerm, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- The actual Fourier lattice sum is absolutely convergent for positive Gaussian coefficients. -/
theorem summable_norm_latticeFourierTerm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Summable (fun v : ℤ × ℤ => ‖latticeFourierTerm a b x v‖) := by
  simp_rw [norm_latticeFourierTerm]
  exact (summable_lattice_gaussian ha).mul_of_nonneg (summable_lattice_gaussian hb)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)

/-- Exchanging the actual lattice coordinates interchanges the two Gaussian coefficients. -/
theorem latticeFourierTerm_swap (a b x : ℝ) (v : ℤ × ℤ) :
    latticeFourierTerm a b x (v.2, v.1) = latticeFourierTerm b a x v := by
  unfold latticeFourierTerm
  congr 1
  ring

/-- Coordinate exchange gives the exact symmetry of the genuine double Fourier series. -/
theorem latticeFourier_tsum_swap (a b x : ℝ) :
    (∑' v : ℤ × ℤ, latticeFourierTerm a b x v) =
      ∑' v : ℤ × ℤ, latticeFourierTerm b a x v := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (latticeFourierTerm a b x)]
  exact tsum_congr (fun v => latticeFourierTerm_swap a b x v)

end
end Dubon2026
