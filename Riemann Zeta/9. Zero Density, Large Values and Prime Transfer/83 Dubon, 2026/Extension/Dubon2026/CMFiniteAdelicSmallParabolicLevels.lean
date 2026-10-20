import Dubon2026.CMFiniteAdelicPrincipalFamilyMap
import Dubon2026.SubgroupPairPreimageQuotient
import Dubon2026.SubgroupPairImageQuotient

/-! # The actual small auxiliary levels in the full unitary adelic group

The source row conditions are imposed inside the original principal
level and then included in the full original unitary group. Both levels
retain the principal-congruence condition needed for arithmetic
smallness in DUB-17; their quotient is computed separately by the proved
original local evaluation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
variable (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K))

/-- The actual upper auxiliary level inside the original principal unitary level. -/
def cmFiniteAdelicPrincipalParabolicZero : Subgroup (cmFiniteAdelicPrincipalLevel K H w) :=
  (finitePlaceParabolicFamilyLevelZero K v n).comap (cmFiniteAdelicPrincipalFamilyMap K v n H w)

/-- The actual lower auxiliary level inside the original principal unitary level. -/
def cmFiniteAdelicPrincipalParabolicOne : Subgroup (cmFiniteAdelicPrincipalLevel K H w) :=
  (finitePlaceParabolicFamilyLevelOne K v n).comap (cmFiniteAdelicPrincipalFamilyMap K v n H w)

/-- The lower principal-refined auxiliary level lies in the upper level. -/
theorem cmFiniteAdelicPrincipalParabolicOne_le :
    cmFiniteAdelicPrincipalParabolicOne K v n H w ≤ cmFiniteAdelicPrincipalParabolicZero K v n H w :=
  Subgroup.comap_mono (finitePlaceParabolicFamilyLevelOne_le K v n)

/-- The lower principal-refined auxiliary level is normal in the upper level. -/
instance cmFiniteAdelicPrincipalParabolicOne_normal :
    ((cmFiniteAdelicPrincipalParabolicOne K v n H w).subgroupOf
      (cmFiniteAdelicPrincipalParabolicZero K v n H w)).Normal :=
  subgroupPairPreimage_normal _ _ _

/-- The actual upper source auxiliary level in the full original unitary adelic group. -/
def cmFiniteAdelicSmallParabolicZero : Subgroup (cmFiniteAdelicUnitaryGroup K H) :=
  (cmFiniteAdelicPrincipalParabolicZero K v n H w).map (cmFiniteAdelicPrincipalLevel K H w).subtype

/-- The actual lower source auxiliary level in the full original unitary adelic group. -/
def cmFiniteAdelicSmallParabolicOne : Subgroup (cmFiniteAdelicUnitaryGroup K H) :=
  (cmFiniteAdelicPrincipalParabolicOne K v n H w).map (cmFiniteAdelicPrincipalLevel K H w).subtype

/-- The actual lower source auxiliary level lies in the upper level in the full original group. -/
theorem cmFiniteAdelicSmallParabolicOne_le :
    cmFiniteAdelicSmallParabolicOne K v n H w ≤ cmFiniteAdelicSmallParabolicZero K v n H w :=
  Subgroup.map_mono (cmFiniteAdelicPrincipalParabolicOne_le K v n H w)

/-- The actual source auxiliary levels retain normality in the full original unitary group. -/
instance cmFiniteAdelicSmallParabolicOne_normal :
    ((cmFiniteAdelicSmallParabolicOne K v n H w).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H w)).Normal :=
  subgroupPairImage_normal _ _ _ Subtype.val_injective

/-- The actual upper auxiliary level preserves the original principal-congruence smallness condition. -/
theorem cmFiniteAdelicSmallParabolicZero_le_principal :
    cmFiniteAdelicSmallParabolicZero K v n H w ≤ cmFiniteAdelicPrincipalLevel K H w :=
  Subgroup.map_subtype_le _

/-- The original finite-place projection of the actual upper auxiliary level satisfies the proved principal congruence. -/
theorem cmFiniteAdelicSmallParabolicZero_projection :
    ((cmFiniteAdelicSmallParabolicZero K v n H w).map (cmFiniteAdelicUnitaryGroup K H).subtype).map
      (numberFieldFiniteAdelicMatrixProjection K (Fin (n + 1)) w) ≤
        finitePlacePrincipalCongruenceImage K (Fin (n + 1)) w :=
  le_trans (Subgroup.map_mono (Subgroup.map_mono
    (cmFiniteAdelicSmallParabolicZero_le_principal K v n H w)))
      (cmFiniteAdelicPrincipalLevel_projection K H w)

end
end Dubon2026
