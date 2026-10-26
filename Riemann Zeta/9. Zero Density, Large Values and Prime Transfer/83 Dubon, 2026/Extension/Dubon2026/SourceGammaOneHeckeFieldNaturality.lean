import Dubon2026.SourceGammaOneFieldCoefficients
import Dubon2026.SourceGammaOneHeckeDegeneracy

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> Hecke/constant-field comparison. Both actual finite field maps
commute with coefficient transport, hence with arithmetic automorphisms and
the Qbar-to-C embedding. Divisor/Picard naturality and H1 comparison remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup
variable {L L' : Type*} [Field L] [Field L'] [Algebra ℚ L] [Algebra ℚ L']

theorem heckeAlpha_coefficientMap (M d : ℕ) (σ : L →ₐ[ℚ] L')
    (x : laurentBaseChange L (x1FunctionField M)) :
    fieldCoefficientMap (Gamma1 M ⊓ Gamma0 (d * M)) σ (heckeAlpha L M d x) =
      heckeAlpha L' M d (fieldCoefficientMap (Gamma1 M) σ x) := by
  apply Subtype.ext
  change coeffMap σ.toRingHom (heckeAlpha L M d x : LaurentSeries L) =
    (heckeAlpha L' M d (fieldCoefficientMap (Gamma1 M) σ x) : LaurentSeries L')
  rw [heckeAlpha_coe, heckeAlpha_coe]
  rfl

theorem heckeBeta_coefficientMap (M d : ℕ) [NeZero d] (σ : L →ₐ[ℚ] L')
    (x : laurentBaseChange L (x1FunctionField M)) :
    fieldCoefficientMap (Gamma1 M ⊓ Gamma0 (d * M)) σ (heckeBeta L M d x) =
      heckeBeta L' M d (fieldCoefficientMap (Gamma1 M) σ x) :=
  Subtype.ext (coeffMap_qExpand σ.toRingHom d x.val)

end
end Dubon2026.SourceFunctionField.GammaOne
