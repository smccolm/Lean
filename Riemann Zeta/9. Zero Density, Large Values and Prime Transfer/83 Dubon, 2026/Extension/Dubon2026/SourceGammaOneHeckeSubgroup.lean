import Dubon2026.SourceIntegralHeckeHom
import Dubon2026.SourceHeckeCohomologyTrace

/-! DUB-17/18 -> original all-weight adic association -> arithmetic
Gamma1 realization -> exact Hecke comparison on the Gamma1 cover.
Restrict the existing integral upper-subgroup correspondence to Gamma1,
proving that its literal diagonal conjugation stays in Gamma1. Existing
finite-index and native trace infrastructure can then define the actual
constant-coefficient correspondence without a compatibility premise. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup

/-- The genuine upper-congruence subgroup inside the actual Gamma1 level. -/
def sourceGammaOneHeckeUpper (M n : ℕ) : Subgroup (Gamma1 M) :=
  (heckeUpperSubgroup M n).comap (Subgroup.inclusion (Gamma1_in_Gamma0 M))

/-- The actual Gamma1 upper subgroup has finite index by the already
proved Gamma0 upper-subgroup index. -/
theorem sourceGammaOneHeckeUpper_finiteIndex (M n : ℕ) [NeZero n] :
    (sourceGammaOneHeckeUpper M n).FiniteIndex := by
  letI : (heckeUpperSubgroup M n).FiniteIndex := sourceHeckeUpper_finiteIndex
  letI : (heckeUpperSubgroup M n).IsFiniteRelIndex
      (Subgroup.inclusion (Gamma1_in_Gamma0 M)).range :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  constructor
  change ((heckeUpperSubgroup M n).comap
    (Subgroup.inclusion (Gamma1_in_Gamma0 M))).index ≠ 0
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_ne_zero

/-- Inclusion into the original integral upper correspondence subgroup. -/
def sourceGammaOneUpperToGammaZero (M n : ℕ) :
    sourceGammaOneHeckeUpper M n →* heckeUpperSubgroup M n :=
  ((Subgroup.inclusion (Gamma1_in_Gamma0 M)).comp
    (sourceGammaOneHeckeUpper M n).subtype).codRestrict _ (fun g => g.property)

/-- Literal diagonal conjugation on the genuine Gamma1 Hecke subgroup.
Its integral matrix and homomorphism laws come from the existing map. -/
def sourceGammaOneHeckeConjugation (M n : ℕ) [NeZero n] :
    sourceGammaOneHeckeUpper M n →* Gamma1 M := by
  let φ := (Gamma0 M).subtype.comp
    ((sourceIntegralHeckeHom (Q := M) (n := n)).comp (sourceGammaOneUpperToGammaZero M n))
  refine φ.codRestrict (Gamma1 M) ?_
  intro g
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem M g.val.val).mp g.val.property
  rw [Gamma1_mem]
  change (g.val.val 0 0 : ZMod M) = 1 ∧ (g.val.val 1 1 : ZMod M) = 1 ∧
    (((g.val.val 1 0 * (n : ℤ) : ℤ)) : ZMod M) = 0
  exact ⟨ha, hd, by rw [Int.cast_mul, hc, zero_mul]⟩

/-- The restricted Gamma1 correspondence retains the same original
integral diagonal equation, with no convention change. -/
theorem sourceGammaOneHeckeConjugation_matrix
    (M n : ℕ) [NeZero n] (g : sourceGammaOneHeckeUpper M n) :
    heckeTriangularMatrix 1 n 0 * mapGL ℝ g.val.val =
      mapGL ℝ (sourceGammaOneHeckeConjugation M n g).val * heckeTriangularMatrix 1 n 0 :=
  sourceIntegralHeckeConjugate_matrix (sourceGammaOneUpperToGammaZero M n g)

end
end Dubon2026
