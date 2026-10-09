import Dubon2026.MatrixCongruenceKernelPGroup

/-! # Actual nilpotent matrix kernels at the original ideal-power quotients -/

namespace Dubon2026

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The original ideal becomes genuinely nilpotent in its own power quotient. -/
theorem idealPowerQuotient_image_nilpotent (I : Ideal R) (n : ℕ) :
    (I.map (Ideal.Quotient.mk (I ^ n))) ^ n = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

/-- Reducing the original coefficient prime retains its membership in the actual image ideal. -/
theorem idealPowerQuotient_prime_mem (I : Ideal R) (p n : ℕ) (hpI : (p : R) ∈ I) :
    (p : R ⧸ I ^ n) ∈ I.map (Ideal.Quotient.mk (I ^ n)) := by
  simpa only [map_natCast] using Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ n)) hpI

/-- Every original ideal-power quotient has an actual p-group as its matrix kernel modulo the original image ideal. -/
theorem idealPowerMatrixKernel_isPGroup (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (n : ℕ) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι)
      (I.map (Ideal.Quotient.mk (I ^ n)))) :=
  matrixCongruenceKernel_isPGroup (I.map (Ideal.Quotient.mk (I ^ n))) hp
    (idealPowerQuotient_prime_mem I p n hpI) (idealPowerQuotient_image_nilpotent I n)

end Dubon2026
