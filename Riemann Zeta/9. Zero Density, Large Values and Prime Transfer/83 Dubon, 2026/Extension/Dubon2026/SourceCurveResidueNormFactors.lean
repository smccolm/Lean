import Dubon2026.SourceCurveResidueNormBaseChange
import Dubon2026.SourceRamifiedResidueNorm
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! DUB-17/18 -> original Weil reciprocity and Hecke adjointness ->
evaluation of norms on place fibers. Apply Mathlib's existing ramified
Chinese remainder equivalence to the actual integral closure. The residue
norm becomes the product of its actual prime-power factor norms, avoiding
a second construction of fiber ideals and their decomposition. The local
scalar-power evaluation and identification with original places remain. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing UniqueFactorizationMonoid
open scoped Classical
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The native ramified-factor algebra, expressed over the place residue field. -/
local instance residueRamifiedFactorAlgebra (v : Place K F) (P : Ideal (integralClosureAt E v)) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt E v ⧸ P ^ (maximalIdeal v.toValuationSubring).ramificationIdx P) :=
  Ideal.Quotient.algebraQuotientPowRamificationIdx _ _

theorem residue_norm_eq_prod_ramified_factors (v : Place K F) (c : integralClosureAt E v) :
    IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c) =
      ∏ P : (factors (residueFiberIdeal E v)).toFinset,
        Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk
            (P.val ^ (maximalIdeal v.toValuationSubring).ramificationIdx P.val) c) := by
  rw [residue_norm_eq_norm_residueFiber]
  exact norm_residue_quotient_eq_prod (maximalIdeal v.toValuationSubring)
    (residueFiberIdeal_ne_bot v) c

end
end Dubon2026.SourceCurve.Place
