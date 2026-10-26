import Dubon2026.SourceSemilinearH1ReductionKernel
import Dubon2026.SourceBinaryCoefficientReduction

/-! DUB-17/18 -> original all-weight adic association -> actual finite-precision
Hecke realization -> exact kernel of original integral binary H1 reduction.
The existing coefficient-surjectivity, scalar-division and semilinear H1
kernel proof applies at every nonzero modulus, including all prime powers.
No new cohomology exact-sequence theory is introduced.
-/

namespace Dubon2026
noncomputable section

/-- At every nonzero modulus, original integral binary H1 reduction has
exactly the scalar-divisible classes as its kernel. -/
theorem sourceBinaryH1Change_zmod_nonzero_eq_zero_iff (Q w ell : ℕ) (hell : ell ≠ 0)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1Change (Int.castRingHom (ZMod ell)) Q w x = 0 ↔
      ∃ y : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w), x = (ell : ℤ) • y := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := sourceSemilinearH1_exists_smul_of_zero
      (sourceBinaryCoefficientRep ℤ Q w) (sourceBinaryCoefficientRep (ZMod ell) Q w)
      (Int.castRingHom (ZMod ell)) (homogeneousCoefficientMap w (Int.castRingHom (ZMod ell)))
      (sourceBinaryCoefficientMap_equivariant _ Q w) (ell : ℤ)
      (sourceBinaryCoefficientMap_surjective w _ (ZMod.ringHom_surjective _))
      (sourceBinaryCoefficientMap_zmod_kernel w ell)
      (sourceBinaryCoefficient_int_smul_injective w ell (by exact_mod_cast hell))
      x hx
    exact ⟨y, hy.trans (int_smul_eq_zsmul _ _ _)⟩
  · rintro ⟨y, rfl⟩
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod ell), Int.cast_natCast,
      ZMod.natCast_self, zero_smul]

end
end Dubon2026
