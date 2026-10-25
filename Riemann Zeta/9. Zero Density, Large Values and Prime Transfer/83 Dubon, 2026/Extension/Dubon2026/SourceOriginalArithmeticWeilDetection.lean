import Dubon2026.SourceOriginalWeilComplexComparison
import Dubon2026.SourceOriginalComplexWeilDetection
import Dubon2026.SourceOriginalTorsionComparison

/-! DUB-17/18 -> original Tate nondegeneracy. The proved arithmetic-to-complex
torsion bijection and exact Weil-pairing compatibility descend the actual
complex detecting partner to the original arithmetic Picard torsion. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve OriginalConstantField
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem originalArithmeticWeilPairing_detects
    (x : Pic0.torsion (K := Qbar) (F := FQ) n) (hx : x ≠ 0) :
    ∃ y : Pic0.torsion (K := Qbar) (F := FQ) n,
      originalWeilPairing N Qbar n x y ≠ 1 := by
  let xc : Pic0.torsion (K := ℂ) (F := FC) n :=
    ⟨complexPicardMap N x.val, complexPicardMap_mem_torsion N x.property⟩
  have hxc : xc ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    apply complexPicardMap_injective N
    exact (congrArg Subtype.val h).trans (map_zero (complexPicardMap N)).symm
  obtain ⟨yc, hyc⟩ := originalComplexWeilPairing_detects N n xc hxc
  obtain ⟨y, hy, he⟩ := exists_original_torsion_preimage N n (NeZero.ne n) yc.val yc.property
  refine ⟨⟨y, hy⟩, fun h => hyc ?_⟩
  have he' : (⟨complexPicardMap N y, complexPicardMap_mem_torsion N hy⟩ :
      Pic0.torsion (K := ℂ) (F := FC) n) = yc := Subtype.ext he
  have hp := originalWeilPairing_complex N n x ⟨y, hy⟩
  rw [he', h] at hp
  apply Subtype.ext
  apply Units.ext
  exact hp.trans (map_one OriginalConstantField.sigma)

end
end Dubon2026.SourceFunctionField
