import Dubon2026.SourceOriginalTensorCoefficientEquivR2
import Dubon2026.SourceOriginalAtkinInvolution
import Dubon2026.SourceOriginalHeckeDegeneracy

/-! DUB-17/18 -> actual Hecke norm product. Extend the proved rational
Atkin-Lehner involution to the actual algebraic coefficient extension.
Its action exchanges the two original degeneracy maps on every element.
The tensor realization and two-generator field theorem discharge the
extension and compatibility obligations without a new symmetry premise. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField
variable (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
variable (N p : ℕ) [NeZero N] [Fact p.Prime]

theorem exists_original_atkin_over (hpN : ¬ p ∣ N) :
    ∃ w : modularFunctionFieldOver (N * p) L ≃ₐ[L] modularFunctionFieldOver (N * p) L,
      Function.Involutive w ∧
      (∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x) ∧
      (∀ x, w (originalHeckeBeta L N p x) = originalHeckeAlpha L N p x) := by
  obtain ⟨σ, hσ, hbase, _, _⟩ := exists_original_atkin_involution N p hpN
  let σa : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p) :=
    { σ with commutes' := σ.toRingHom.map_rat_algebraMap }
  let w := geomAut L (modularFunctionFieldFull (N * p)) σa
  have hσ2 : σa * σa = 1 := by
    apply AlgEquiv.ext
    intro x
    exact hσ x
  have hw2 : w * w = 1 := by
    change geomAut L (modularFunctionFieldFull (N * p)) σa *
      geomAut L (modularFunctionFieldFull (N * p)) σa = 1
    rw [← map_mul, hσ2, map_one]
  have hw : Function.Involutive w := fun x => congrArg (fun e => e x) hw2
  have hcoeff (z : modularFunctionFieldFull N) :
      w (originalHeckeAlpha L N p
        ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩) =
      originalHeckeBeta L N p
        ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩ := by
    apply Subtype.ext
    have hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull (N * p) :=
      original_full_mono_of_dvd (dvd_mul_right N p) z.2
    have hc := coe_geomAut_coeffEmb L (modularFunctionFieldFull (N * p)) σa ⟨z, hz⟩
    change (w (originalHeckeAlpha L N p
      ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩) : LaurentSeries L) =
        qExpand L p (coeffEmb L z)
    apply hc.trans
    change coeffEmb L (σ ⟨z, hz⟩) = _
    rw [hbase z hz]
    exact coeffMap_qExpand (algebraMap ℚ L) p z
  have hf : w.toAlgHom.comp (originalHeckeAlpha L N p) = originalHeckeBeta L N p := by
    apply IntermediateField.algHom_ext_of_eq_adjoin L (original_field_eq_pair_over N L)
    intro x hx
    rcases hx with rfl | hx
    · exact hcoeff ⟨jq, jq_mem_full N⟩
    · rcases hx with rfl
      exact hcoeff ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩
  have hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x :=
    fun x => DFunLike.congr_fun hf x
  refine ⟨w, hw, hforward, fun x => ?_⟩
  rw [← hforward x]
  exact hw (originalHeckeAlpha L N p x)

end
end Dubon2026.SourceFunctionField
