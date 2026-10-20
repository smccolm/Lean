import Dubon2026.CMFiniteAdelicIntegralLocalMap
import Dubon2026.ParabolicResidueAmbientQuotient

/-! # The source parabolic levels inside the actual integral unitary group

The two levels are literal inverse images of the printed residue row
conditions under the original integral local matrix evaluation. Their
quotient character is the actual final residue entry, and its kernel is
exactly the lower level. These are the actual global level objects for
DUB-17's integral unitary auxiliary modules.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain IsLocalRing
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Original unitary integral matrices with the source parabolic residue row. -/
def cmFiniteAdelicParabolicLevelZero (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    Subgroup (cmFiniteAdelicIntegralLevel K H) :=
  (parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) a).comap
    (cmFiniteAdelicIntegralLocalMap K H v)

/-- Original unitary integral matrices with the same residue row and last entry one. -/
def cmFiniteAdelicParabolicLevelOne (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    Subgroup (cmFiniteAdelicIntegralLevel K H) :=
  (parabolicResidueLevelOneAmbient (Valued.integer (v.adicCompletion K)) a).comap
    (cmFiniteAdelicIntegralLocalMap K H v)

/-- The original lower unitary parabolic level is contained in the upper level. -/
theorem cmFiniteAdelicParabolicLevelOne_le (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    cmFiniteAdelicParabolicLevelOne K H v a ≤ cmFiniteAdelicParabolicLevelZero K H v a :=
  Subgroup.comap_mono (parabolicResidueLevelOneAmbient_le (Valued.integer (v.adicCompletion K)) a)

/-- The actual integral local evaluation restricted to the original unitary parabolic level. -/
def cmFiniteAdelicParabolicLocalMap (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    cmFiniteAdelicParabolicLevelZero K H v a →*
      parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) a :=
  ((cmFiniteAdelicIntegralLocalMap K H v).comp
    (cmFiniteAdelicParabolicLevelZero K H v a).subtype).codRestrict _ (fun M => M.property)

/-- The source single-character quotient map on the actual unitary parabolic level. -/
def cmFiniteAdelicParabolicCharacter (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    cmFiniteAdelicParabolicLevelZero K H v a →* (ResidueField (Valued.integer (v.adicCompletion K)))ˣ :=
  (parabolicResidueCharacter (Valued.integer (v.adicCompletion K)) a).comp
    (cmFiniteAdelicParabolicLocalMap K H v a)

/-- The actual unitary quotient character is the original residue of the selected diagonal entry. -/
theorem cmFiniteAdelicParabolicCharacter_val
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι)
    (M : cmFiniteAdelicParabolicLevelZero K H v a) :
    (cmFiniteAdelicParabolicCharacter K H v a M).val =
      residue (Valued.integer (v.adicCompletion K))
        ((cmFiniteAdelicIntegralLocalMap K H v M.val).val a a) := rfl

/-- The kernel of the actual unitary parabolic character is precisely the original lower level inside the upper level. -/
theorem cmFiniteAdelicParabolicLevelOne_kernel
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    (cmFiniteAdelicParabolicLevelOne K H v a).subgroupOf
      (cmFiniteAdelicParabolicLevelZero K H v a) = (cmFiniteAdelicParabolicCharacter K H v a).ker := by
  ext M
  change cmFiniteAdelicIntegralLocalMap K H v M.val ∈
    parabolicResidueLevelOneAmbient (Valued.integer (v.adicCompletion K)) a ↔
      cmFiniteAdelicParabolicCharacter K H v a M = 1
  rw [parabolicResidueLevelOneAmbient_mem_iff, Units.ext_iff, cmFiniteAdelicParabolicCharacter_val]
  exact and_iff_right ((parabolicResidueLevelZero_mem_iff
    (Valued.integer (v.adicCompletion K)) a _).mp M.property)

/-- Normality of the actual lower unitary parabolic level follows from its proved character kernel. -/
instance cmFiniteAdelicParabolicLevelOne_normal
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) (a : ι) :
    ((cmFiniteAdelicParabolicLevelOne K H v a).subgroupOf
      (cmFiniteAdelicParabolicLevelZero K H v a)).Normal := by
  rw [cmFiniteAdelicParabolicLevelOne_kernel]
  infer_instance

end
end Dubon2026
