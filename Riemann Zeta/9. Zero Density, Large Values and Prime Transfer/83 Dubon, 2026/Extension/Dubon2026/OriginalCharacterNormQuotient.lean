import Dubon2026.OriginalCharacterNormDetection
import Dubon2026.OriginalNormQuotientCohomology

/-! # The actual degree-zero character norm quotient is detected faithfully

Combine the original coefficient norm quotient with the proved literal
norm-kernel annihilator identity. This closes the character-detection
base step for DUB-17's required low-degree integral duality; it does not
assert the higher-degree class-coefficient pairing or its compatibility.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- A class in the actual character norm quotient is zero exactly when its original equivariant character annihilates the original norm kernel. -/
theorem originalCharacterNormQuotient_mk_eq_zero_iff
    {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
    (φ : M ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ))) :
    (Submodule.Quotient.mk φ : OriginalCoefficientNormQuotient M
      (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) = 0 ↔
        ∀ x : M, M.ρ.norm x = 0 → φ.hom x = 0 := by
  rw [originalCoefficientNormQuotient_mk_eq_zero_iff]
  exact (originalCharacter_norm_kernel_iff_sum M φ.hom.toLinearMap).symm

end
end Dubon2026
