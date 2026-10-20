import Dubon2026.CMFiniteAdelicUnitaryGroup
import Dubon2026.NumberFieldIntegralMatrixLevel

/-! # A compact open level in the original finite-adelic CM unitary group

Intersecting the actual integral matrix level with the constructed
closed unitary group gives an original compact open subgroup. This
removes a supplied ambient compact-level existence premise in DUB-17;
the source local refinements and arithmetic double-coset finiteness
remain required separately.
-/

namespace Dubon2026

noncomputable section

open NumberField
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original integral matrices in the actual finite-adelic unitary group. -/
def cmFiniteAdelicIntegralLevel (H : Matrix ι ι K) : Subgroup (cmFiniteAdelicUnitaryGroup K H) :=
  (numberFieldIntegralMatrixLevel K ι).subgroupOf (cmFiniteAdelicUnitaryGroup K H)

/-- The original integral unitary level is open. -/
theorem cmFiniteAdelicIntegralLevel_isOpen (H : Matrix ι ι K) :
    IsOpen (cmFiniteAdelicIntegralLevel K H : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (numberFieldIntegralMatrixLevel_isOpen K ι).preimage continuous_subtype_val

/-- The original integral unitary level is compact. -/
theorem cmFiniteAdelicIntegralLevel_isCompact (H : Matrix ι ι K) :
    IsCompact (cmFiniteAdelicIntegralLevel K H : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicUnitaryGroup_isClosed K H).isClosedEmbedding_subtypeVal.isCompact_preimage
    (numberFieldIntegralMatrixLevel_isCompact K ι)

end
end Dubon2026
