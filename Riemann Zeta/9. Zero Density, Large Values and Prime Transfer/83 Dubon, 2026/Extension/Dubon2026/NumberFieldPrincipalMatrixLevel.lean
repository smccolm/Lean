import Dubon2026.IntegralFiniteAdelicLocalMatrixMap
import Dubon2026.CompactLocalMatrixCongruenceTopology
import Dubon2026.CMHermitianCongruenceSmallLevel
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The original compact open level with one principal congruence condition

The actual integral finite-adelic matrix group is refined at a specified
original finite place. The construction proves compactness, openness
and the exact local congruence condition needed by DUB-17's arithmetic
smallness theorem; no level-existence certificate is assumed.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open scoped NumberField

variable (K ι : Type*) [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]

/-- The actual principal residue kernel inside the original integral finite-adelic level. -/
def numberFieldPrincipalIntegralKernel (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (numberFieldIntegralMatrixLevel K ι) :=
  (MatrixCongruenceKernel (ι := ι)
    (maximalIdeal (Valued.integer (v.adicCompletion K)))).comap
      (numberFieldIntegralMatrixLocalMap K ι v)

/-- The actual original one-place principal kernel is open. -/
theorem numberFieldPrincipalIntegralKernel_isOpen (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (numberFieldPrincipalIntegralKernel K ι v : Set (numberFieldIntegralMatrixLevel K ι)) := by
  letI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp (original_adicCompletion_properSpace K v)
  exact (compactLocalMatrixCongruenceKernel_isOpen (Valued.integer (v.adicCompletion K)) ι).preimage
    (numberFieldIntegralMatrixLocalMap_continuous K ι v)

/-- The original one-place principal kernel is compact in the integral level. -/
theorem numberFieldPrincipalIntegralKernel_isCompact (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (numberFieldPrincipalIntegralKernel K ι v : Set (numberFieldIntegralMatrixLevel K ι)) := by
  letI : CompactSpace (numberFieldIntegralMatrixLevel K ι) :=
    isCompact_iff_compactSpace.mp (numberFieldIntegralMatrixLevel_isCompact K ι)
  exact ((numberFieldPrincipalIntegralKernel K ι v).isClosed_of_isOpen
    (numberFieldPrincipalIntegralKernel_isOpen K ι v)).isCompact

/-- The original principal level in the full original finite-adelic matrix group. -/
def numberFieldPrincipalMatrixLevel (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ :=
  (numberFieldPrincipalIntegralKernel K ι v).map (numberFieldIntegralMatrixLevel K ι).subtype

/-- The actual principal matrix level is open in the original finite-adelic group. -/
theorem numberFieldPrincipalMatrixLevel_isOpen (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (numberFieldPrincipalMatrixLevel K ι v :
      Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :=
  (numberFieldIntegralMatrixLevel_isOpen K ι).isOpenMap_subtype_val _
    (numberFieldPrincipalIntegralKernel_isOpen K ι v)

/-- The actual principal matrix level is compact. -/
theorem numberFieldPrincipalMatrixLevel_isCompact (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (numberFieldPrincipalMatrixLevel K ι v :
      Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :=
  (numberFieldPrincipalIntegralKernel_isCompact K ι v).image continuous_subtype_val

/-- Its original finite-place projection satisfies precisely the required principal congruence. -/
theorem numberFieldPrincipalMatrixLevel_projection (v : HeightOneSpectrum (𝓞 K)) :
    (numberFieldPrincipalMatrixLevel K ι v).map (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
      finitePlacePrincipalCongruenceImage K ι v := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨numberFieldIntegralMatrixLocalMap K ι v a, ha,
    numberFieldIntegralMatrixLocalMap_compatibility K ι v a⟩

end
end Dubon2026
