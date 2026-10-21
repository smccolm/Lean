import Dubon2026.SourceSemilinearH1ReductionKernel
import Dubon2026.SourceBinaryCoefficientReduction

/-! Exact kernel of prime reduction on the original native binary H1.
DUB-17/18 -> residual modular Galois association -> nonzero residual H1
eigensystem -> injective tensor coefficient change -> prime-reduction kernel.
All coefficient surjectivity, division and regularity hypotheses are derived
for the actual integral homogeneous module.
-/

namespace Dubon2026
noncomputable section

/-- At every prime, an actual integral binary H1 class vanishes under the literal
coefficient reduction exactly when it is divisible by that prime in integral H1. -/
theorem sourceBinaryH1Change_zmod_eq_zero_iff (Q w ell : ℕ) (hell : ell.Prime)
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
      (sourceBinaryCoefficient_int_smul_injective w ell (by exact_mod_cast hell.ne_zero))
      x hx
    exact ⟨y, hy.trans (int_smul_eq_zsmul _ _ _)⟩
  · rintro ⟨y, rfl⟩
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod ell), Int.cast_natCast,
      ZMod.natCast_self, zero_smul]

end
end Dubon2026
