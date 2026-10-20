import Dubon2026.CMFiniteAdelicSmallParabolicLevels
import Dubon2026.CMFiniteAdelicParabolicFamilyTopology

/-! # The actual small auxiliary levels are compact open

The source row conditions are pulled back through the original
continuous principal-level inclusion. Including these compact open
subgroups into the full original unitary adelic group supplies exactly
the topology required by DUB-17's automorphic comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} [Finite S] (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
variable (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K))

/-- The actual upper auxiliary level is open inside the original principal level. -/
theorem cmFiniteAdelicPrincipalParabolicZero_isOpen :
    IsOpen (cmFiniteAdelicPrincipalParabolicZero K v n H w : Set (cmFiniteAdelicPrincipalLevel K H w)) :=
  (cmFiniteAdelicParabolicFamilyLevelZero_isOpen K v n H).preimage
    (cmFiniteAdelicPrincipalIntegralMap_continuous K H w)

/-- The actual lower auxiliary level is open inside the original principal level. -/
theorem cmFiniteAdelicPrincipalParabolicOne_isOpen :
    IsOpen (cmFiniteAdelicPrincipalParabolicOne K v n H w : Set (cmFiniteAdelicPrincipalLevel K H w)) :=
  (cmFiniteAdelicParabolicFamilyLevelOne_isOpen K v n H).preimage
    (cmFiniteAdelicPrincipalIntegralMap_continuous K H w)

/-- The actual upper auxiliary level is compact inside the original principal level. -/
theorem cmFiniteAdelicPrincipalParabolicZero_isCompact :
    IsCompact (cmFiniteAdelicPrincipalParabolicZero K v n H w : Set (cmFiniteAdelicPrincipalLevel K H w)) := by
  letI : CompactSpace (cmFiniteAdelicPrincipalLevel K H w) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicPrincipalLevel_isCompact K H w)
  exact ((cmFiniteAdelicPrincipalParabolicZero K v n H w).isClosed_of_isOpen
    (cmFiniteAdelicPrincipalParabolicZero_isOpen K v n H w)).isCompact

/-- The actual lower auxiliary level is compact inside the original principal level. -/
theorem cmFiniteAdelicPrincipalParabolicOne_isCompact :
    IsCompact (cmFiniteAdelicPrincipalParabolicOne K v n H w : Set (cmFiniteAdelicPrincipalLevel K H w)) := by
  letI : CompactSpace (cmFiniteAdelicPrincipalLevel K H w) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicPrincipalLevel_isCompact K H w)
  exact ((cmFiniteAdelicPrincipalParabolicOne K v n H w).isClosed_of_isOpen
    (cmFiniteAdelicPrincipalParabolicOne_isOpen K v n H w)).isCompact

/-- The actual upper source auxiliary level is open in the full original unitary adelic group. -/
theorem cmFiniteAdelicSmallParabolicZero_isOpen :
    IsOpen (cmFiniteAdelicSmallParabolicZero K v n H w : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicPrincipalLevel_isOpen K H w).isOpenMap_subtype_val _
    (cmFiniteAdelicPrincipalParabolicZero_isOpen K v n H w)

/-- The actual lower source auxiliary level is open in the full original unitary adelic group. -/
theorem cmFiniteAdelicSmallParabolicOne_isOpen :
    IsOpen (cmFiniteAdelicSmallParabolicOne K v n H w : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicPrincipalLevel_isOpen K H w).isOpenMap_subtype_val _
    (cmFiniteAdelicPrincipalParabolicOne_isOpen K v n H w)

/-- The actual upper source auxiliary level is compact in the full original unitary adelic group. -/
theorem cmFiniteAdelicSmallParabolicZero_isCompact :
    IsCompact (cmFiniteAdelicSmallParabolicZero K v n H w : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicPrincipalParabolicZero_isCompact K v n H w).image continuous_subtype_val

/-- The actual lower source auxiliary level is compact in the full original unitary adelic group. -/
theorem cmFiniteAdelicSmallParabolicOne_isCompact :
    IsCompact (cmFiniteAdelicSmallParabolicOne K v n H w : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicPrincipalParabolicOne_isCompact K v n H w).image continuous_subtype_val

end
end Dubon2026
