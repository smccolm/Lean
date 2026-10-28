import Dubon2026.SourceGammaOneDiamondFieldJ
import Dubon2026.SourceGammaOneComplexFieldExtension

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond descent. The original arithmetic field is finite over its original
j coordinate field. The proved complex diamond fixes that coordinate and
the embedded arithmetic constants, so the same integral relation transports
to its image. No algebraicity premise for that image is supplied.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open CongruenceSubgroup Polynomial
open scoped MatrixGroups
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (M : ℕ) [NeZero M] (g : Gamma0 M)
local notation "FQ" => functionFieldOver (Gamma1 M) Qbar
local notation "FC" => functionFieldOver (Gamma1 M) ℂ

theorem diamondFieldHom_fieldMap_coordinate
    (z : IntermediateField.adjoin Qbar ({jCoordinateOver (Gamma1 M) Qbar} : Set FQ)) :
    diamondFieldHom M g (fieldMap M (z : FQ)) = fieldMap M (z : FQ) := by
  have H (y : FQ) (hy : y ∈ IntermediateField.adjoin Qbar
      ({jCoordinateOver (Gamma1 M) Qbar} : Set FQ)) :
      diamondFieldHom M g (fieldMap M y) = fieldMap M y := by
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
        obtain rfl := Set.mem_singleton_iff.mp hy
        rw [fieldMap_j, diamondFieldHom_j]
    | algebraMap c => rw [fieldMap_constants, diamondFieldHom_constants]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | inv x _ hx => simp only [map_inv₀, hx]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]
  exact H z z.property

theorem exists_diamond_arithmetic_laurent_relation (x : FQ) :
    ∃ p : Polynomial (LaurentSeries Qbar), p ≠ 0 ∧
      Polynomial.eval₂ (coeffMap (algebraMap Qbar ℂ))
        (diamondFieldHom M g (fieldMap M x) : LaurentSeries ℂ) p = 0 := by
  let kx := IntermediateField.adjoin Qbar ({jCoordinateOver (Gamma1 M) Qbar} : Set FQ)
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 M)
    (by simp [Gamma1_mem, ModularGroup.T]) Qbar
  let vQ := (functionFieldOver (Gamma1 M) Qbar).val.toRingHom
  let vC := (functionFieldOver (Gamma1 M) ℂ).val.toRingHom
  let b : kx →+* LaurentSeries Qbar := vQ.comp (algebraMap kx FQ)
  let f : FQ →+* LaurentSeries ℂ := vC.comp ((diamondFieldHom M g).comp (fieldMap M))
  let ι := coeffMap (algebraMap Qbar ℂ)
  have hc : f.comp (algebraMap kx FQ) = ι.comp b := by
    apply RingHom.ext
    intro z
    change (diamondFieldHom M g (fieldMap M (z : FQ)) : LaurentSeries ℂ) = _
    rw [diamondFieldHom_fieldMap_coordinate]
    rfl
  have hi : IsIntegral kx x := Algebra.IsIntegral.isIntegral x
  obtain ⟨p, hp, hx⟩ := hi
  refine ⟨p.map b, (hp.map b).ne_zero, ?_⟩
  have he := congrArg f hx
  rw [Polynomial.hom_eval₂, hc, map_zero] at he
  simpa only [Polynomial.eval₂_map] using he

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
