import Dubon2026.SourceGammaOnePrincipalDescent
import Dubon2026.SourceGammaOneComplexPicardMap
import Dubon2026.SourceGammaOneComplexTorsionFinite

/-! DUB-17/18 -> original Tate module -> arithmetic torsion comparison.
Actual principal-divisor descent makes the arithmetic-to-complex Picard map
injective. The proved complex count then implies finite arithmetic n-torsion
for every nonzero n. Surjectivity on torsion and exact arithmetic cardinality
remain required; neither is inferred from injectivity.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

theorem complexPicardMap_injective : Function.Injective (complexPicardMap N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [complexPicardMap_mk, Pic0.mk_eq_zero_iff] at hx
  rw [Pic0.mk_eq_zero_iff]
  exact isPrincipal_of_conorm N hx

theorem finite_arithmetic_torsion (n : ℕ) (hn : n ≠ 0) :
    Finite (Pic0.torsion (K := AlgebraicClosure ℚ)
      (F := functionFieldOver (Gamma1 N) (AlgebraicClosure ℚ)) n) := by
  letI := finite_complex_torsion N n hn
  exact Finite.of_injective
    (fun x => (⟨complexPicardMap N x.val, complexPicardMap_mem_torsion N x.property⟩ :
      Pic0.torsion (K := ℂ) (F := FC) n))
    (fun x y h => Subtype.ext (complexPicardMap_injective N (congrArg Subtype.val h)))

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
