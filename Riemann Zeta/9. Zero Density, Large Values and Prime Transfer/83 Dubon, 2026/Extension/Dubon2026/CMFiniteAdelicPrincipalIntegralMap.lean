import Dubon2026.CMFiniteAdelicIntegralLocalFaithful
import Dubon2026.CMFiniteAdelicPrincipalLevel

/-! # The original principal unitary level inside the integral level

The existing source smallness level is included in the original
integral unitary group. Original local evaluation still controls its
principal condition. This retains the arithmetic-smallness input while
realizing DUB-17's auxiliary parabolic family.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual original principal unitary level lies in the original integral unitary level. -/
theorem cmFiniteAdelicPrincipalLevel_le_integral
    (H : Matrix ι ι K) (w : HeightOneSpectrum (𝓞 K)) :
    cmFiniteAdelicPrincipalLevel K H w ≤ cmFiniteAdelicIntegralLevel K H := by
  intro M hM
  obtain ⟨a, _, ha⟩ := hM
  change a.val = M.val at ha
  change M.val ∈ numberFieldIntegralMatrixLevel K ι
  rw [← ha]
  exact a.property

/-- The original principal unitary level includes in the actual integral unitary group. -/
def cmFiniteAdelicPrincipalIntegralMap
    (H : Matrix ι ι K) (w : HeightOneSpectrum (𝓞 K)) :
    cmFiniteAdelicPrincipalLevel K H w →* cmFiniteAdelicIntegralLevel K H :=
  Subgroup.inclusion (cmFiniteAdelicPrincipalLevel_le_integral K H w)

/-- Original inclusion of the principal unitary level into the integral level is continuous. -/
theorem cmFiniteAdelicPrincipalIntegralMap_continuous
    (H : Matrix ι ι K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (cmFiniteAdelicPrincipalIntegralMap K H w) :=
  continuous_subtype_val.subtype_mk _

/-- An original integral unitary matrix with identity component at the principal place belongs to the actual principal level. -/
theorem cmFiniteAdelicIntegral_mem_principal_of_local_one
    (H : Matrix ι ι K) (w : HeightOneSpectrum (𝓞 K))
    (M : cmFiniteAdelicIntegralLevel K H)
    (hM : cmFiniteAdelicIntegralLocalMap K H w M = 1) :
    M.val ∈ cmFiniteAdelicPrincipalLevel K H w := by
  refine ⟨cmFiniteAdelicIntegralMatrixInclusion K H M, ?_, rfl⟩
  change cmFiniteAdelicIntegralLocalMap K H w M ∈
    MatrixCongruenceKernel (ι := ι) (IsLocalRing.maximalIdeal (Valued.integer (w.adicCompletion K)))
  rw [hM]
  exact one_mem _

end
end Dubon2026
