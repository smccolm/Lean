import Dubon2026.IdealPowerMatrixKernels

/-! # Actual coefficient-map images of original matrix congruence kernels -/

namespace Dubon2026

open Matrix

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-- An original ideal-compatible coefficient map sends the genuine matrix kernel into the genuine target kernel. -/
theorem matrixCongruenceKernel_map_le (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ Ideal.comap f J) :
    (MatrixCongruenceKernel (ι := ι) I).map
      (GeneralLinearGroup.map (n := ι) (R := R) (S := S) f) ≤
        MatrixCongruenceKernel (ι := ι) J := by
  rintro _ ⟨u, hu, rfl⟩
  let q : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J f hf
  have hcomm : (Ideal.Quotient.mk J).comp f = q.comp (Ideal.Quotient.mk I) := by
    ext x
    rfl
  change GeneralLinearGroup.map (n := ι) ((Ideal.Quotient.mk J).comp f) u = 1
  rw [hcomm, GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
  change GeneralLinearGroup.map q
    (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk I) u) = 1
  rw [show GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk I) u = 1 from hu, map_one]

/-- The actual reduction image of the original matrix residual kernel in each ideal-power quotient is a p-group. -/
theorem matrixCongruenceKernel_powerImage_isPGroup (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (n : ℕ) :
    IsPGroup p ((MatrixCongruenceKernel (ι := ι) I).map
      (GeneralLinearGroup.map (n := ι) (R := R) (S := R ⧸ I ^ n)
        (Ideal.Quotient.mk (I ^ n)))) :=
  (idealPowerMatrixKernel_isPGroup (ι := ι) I hp hpI n).to_le
    (matrixCongruenceKernel_map_le I (I.map (Ideal.Quotient.mk (I ^ n)))
      (Ideal.Quotient.mk (I ^ n)) Ideal.le_comap_map)

end Dubon2026
