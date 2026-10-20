import Dubon2026.CMFiniteAdelicParabolicLevels
import Dubon2026.ParabolicResidueLevelTopology
import Dubon2026.NumberFieldPrincipalMatrixLevel

/-! # Compact openness of the actual unitary parabolic levels

Original integral evaluation pulls back the proved open residue
conditions. The levels are closed subgroups of the compact original
integral unitary group, hence compact. These are the topological
hypotheses needed by DUB-17's actual automorphic module comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original lower parabolic level is open in the actual integral unitary group. -/
theorem cmFiniteAdelicParabolicLevelOne_isOpen
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    IsOpen (cmFiniteAdelicParabolicLevelOne K H v a : Set (cmFiniteAdelicIntegralLevel K H)) := by
  letI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp (original_adicCompletion_properSpace K v)
  exact (parabolicResidueLevelOneAmbient_isOpen (Valued.integer (v.adicCompletion K)) a).preimage
    (cmFiniteAdelicIntegralLocalMap_continuous K H v)

/-- The original upper parabolic level is open in the actual integral unitary group. -/
theorem cmFiniteAdelicParabolicLevelZero_isOpen
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    IsOpen (cmFiniteAdelicParabolicLevelZero K H v a : Set (cmFiniteAdelicIntegralLevel K H)) :=
  Subgroup.isOpen_mono (cmFiniteAdelicParabolicLevelOne_le K H v a)
    (cmFiniteAdelicParabolicLevelOne_isOpen K H v a)

/-- The original lower parabolic level is compact in the actual integral unitary group. -/
theorem cmFiniteAdelicParabolicLevelOne_isCompact
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    IsCompact (cmFiniteAdelicParabolicLevelOne K H v a : Set (cmFiniteAdelicIntegralLevel K H)) := by
  letI : CompactSpace (cmFiniteAdelicIntegralLevel K H) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicIntegralLevel_isCompact K H)
  exact ((cmFiniteAdelicParabolicLevelOne K H v a).isClosed_of_isOpen
    (cmFiniteAdelicParabolicLevelOne_isOpen K H v a)).isCompact

/-- The original upper parabolic level is compact in the actual integral unitary group. -/
theorem cmFiniteAdelicParabolicLevelZero_isCompact
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    IsCompact (cmFiniteAdelicParabolicLevelZero K H v a : Set (cmFiniteAdelicIntegralLevel K H)) := by
  letI : CompactSpace (cmFiniteAdelicIntegralLevel K H) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicIntegralLevel_isCompact K H)
  exact ((cmFiniteAdelicParabolicLevelZero K H v a).isClosed_of_isOpen
    (cmFiniteAdelicParabolicLevelZero_isOpen K H v a)).isCompact

end
end Dubon2026
