import Dubon2026.SourceBinaryFlagTriangular
import Dubon2026.SourceIntegralCohomologyFinite

/-! Original congruence-group and Hecke actions on the residual coefficient flag.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> the exact flag of original residual binary coefficients. Divisibility of
the actual level by the residue characteristic makes the original group
matrices triangular, while the genuine Hecke coefficient matrices are diagonal.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup MvPolynomial Matrix.SpecialLinearGroup

variable (R : Type) [CommRing R] (p Q : ℕ) [CharP R p]

/-- At a level divisible by the residue characteristic, the actual lower-left
congruence-group matrix entry vanishes in the original coefficient ring. -/
theorem sourceBinaryFlag_lower_zero (hpQ : p ∣ Q) (g : Gamma0 Q) :
    ((g.val 1 0 : ℤ) : R) = 0 := by
  have hg := Gamma0_mem.mp g.property
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hg
  obtain ⟨a, ha⟩ := (Int.natCast_dvd_natCast.mpr hpQ).trans hg
  rw [ha, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

/-- The original residual Gamma0 action preserves every actual coefficient-flag step. -/
theorem sourceBinaryFlag_group_stable (hpQ : p ∣ Q) (n j : ℕ) (g : Gamma0 Q)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    (sourceBinaryCoefficientRep R Q n).ρ g P ∈ sourceBinaryCoefficientFlag R n j := by
  apply sourceBinaryCoefficientFlag_upper_stable
  · exact sourceBinaryFlag_lower_zero R p Q hpQ g
  · exact hP

omit [CharP R p] in
/-- Every genuine diagonal Hecke coefficient map preserves each original coefficient-flag step. -/
theorem sourceBinaryFlag_hecke_stable (n j ell : ℕ)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    homogeneousMatrixAction n (Matrix.diagonal ![(ell : R), 1]) P ∈
      sourceBinaryCoefficientFlag R n j :=
  sourceBinaryCoefficientFlag_upper_stable n j _ (by simp) P hP

/-- The action of the actual residual congruence group on the coefficient
quotient is its literal diagonal character. -/
theorem sourceBinaryFlag_group_graded (hpQ : p ∣ Q) (n j : ℕ) (g : Gamma0 Q)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    coeff (sourceBinaryFlagExponent n j) ((sourceBinaryCoefficientRep R Q n).ρ g P).val =
      ((g.val 0 0 : ℤ) : R) ^ j * ((g.val 1 1 : ℤ) : R) ^ (n - j) *
        coeff (sourceBinaryFlagExponent n j) P.val :=
  sourceBinaryFlagGraded_upper n j _ (sourceBinaryFlag_lower_zero R p Q hpQ g) P hP

omit [CharP R p] in
/-- The action of the actual Hecke diagonal on the j-th original coefficient
quotient is exactly multiplication by ell^j. -/
theorem sourceBinaryFlag_hecke_graded (n j ell : ℕ)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    coeff (sourceBinaryFlagExponent n j)
        (homogeneousMatrixAction n (Matrix.diagonal ![(ell : R), 1]) P).val =
      (ell : R) ^ j * coeff (sourceBinaryFlagExponent n j) P.val := by
  have h := sourceBinaryFlagGraded_upper n j (Matrix.diagonal ![(ell : R), 1])
    (by simp) P hP
  simpa using h

end
end Dubon2026
