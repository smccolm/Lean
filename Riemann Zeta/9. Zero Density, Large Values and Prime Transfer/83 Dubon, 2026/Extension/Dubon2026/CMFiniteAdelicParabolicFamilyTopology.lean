import Dubon2026.CMFiniteAdelicParabolicFamilyLevels
import Dubon2026.CMFiniteAdelicParabolicTopology

/-! # Compact openness of the original unitary auxiliary family

Only the source finite set of places is used. The original local row
conditions give finite intersections of the proved compact open levels,
as required by DUB-17's actual automorphic module comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
variable (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)

/-- The original upper unitary family level imposes exactly the original row conditions at each selected place. -/
theorem cmFiniteAdelicParabolicFamilyLevelZero_eq_iInf :
    cmFiniteAdelicParabolicFamilyLevelZero K v n H =
      ⨅ s, cmFiniteAdelicParabolicLevelZero K H (v s) (Fin.last n) := by
  ext M
  simp [cmFiniteAdelicParabolicFamilyLevelZero, cmFiniteAdelicParabolicLevelZero,
    cmFiniteAdelicIntegralLocalFamilyMap, Subgroup.mem_pi]

/-- The original lower unitary family level imposes exactly the original row-one conditions at each selected place. -/
theorem cmFiniteAdelicParabolicFamilyLevelOne_eq_iInf :
    cmFiniteAdelicParabolicFamilyLevelOne K v n H =
      ⨅ s, cmFiniteAdelicParabolicLevelOne K H (v s) (Fin.last n) := by
  ext M
  simp [cmFiniteAdelicParabolicFamilyLevelOne, cmFiniteAdelicParabolicLevelOne,
    cmFiniteAdelicIntegralLocalFamilyMap, Subgroup.mem_pi]

variable [Finite S]

/-- The original upper unitary auxiliary family level is open. -/
theorem cmFiniteAdelicParabolicFamilyLevelZero_isOpen :
    IsOpen (cmFiniteAdelicParabolicFamilyLevelZero K v n H : Set (cmFiniteAdelicIntegralLevel K H)) := by
  rw [cmFiniteAdelicParabolicFamilyLevelZero_eq_iInf, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun s => cmFiniteAdelicParabolicLevelZero_isOpen K H (v s) (Fin.last n)

/-- The original lower unitary auxiliary family level is open. -/
theorem cmFiniteAdelicParabolicFamilyLevelOne_isOpen :
    IsOpen (cmFiniteAdelicParabolicFamilyLevelOne K v n H : Set (cmFiniteAdelicIntegralLevel K H)) := by
  rw [cmFiniteAdelicParabolicFamilyLevelOne_eq_iInf, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun s => cmFiniteAdelicParabolicLevelOne_isOpen K H (v s) (Fin.last n)

/-- The original upper unitary auxiliary family level is compact. -/
theorem cmFiniteAdelicParabolicFamilyLevelZero_isCompact :
    IsCompact (cmFiniteAdelicParabolicFamilyLevelZero K v n H : Set (cmFiniteAdelicIntegralLevel K H)) := by
  letI : CompactSpace (cmFiniteAdelicIntegralLevel K H) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicIntegralLevel_isCompact K H)
  exact ((cmFiniteAdelicParabolicFamilyLevelZero K v n H).isClosed_of_isOpen
    (cmFiniteAdelicParabolicFamilyLevelZero_isOpen K v n H)).isCompact

/-- The original lower unitary auxiliary family level is compact. -/
theorem cmFiniteAdelicParabolicFamilyLevelOne_isCompact :
    IsCompact (cmFiniteAdelicParabolicFamilyLevelOne K v n H : Set (cmFiniteAdelicIntegralLevel K H)) := by
  letI : CompactSpace (cmFiniteAdelicIntegralLevel K H) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicIntegralLevel_isCompact K H)
  exact ((cmFiniteAdelicParabolicFamilyLevelOne K v n H).isClosed_of_isOpen
    (cmFiniteAdelicParabolicFamilyLevelOne_isOpen K v n H)).isCompact

end
end Dubon2026
