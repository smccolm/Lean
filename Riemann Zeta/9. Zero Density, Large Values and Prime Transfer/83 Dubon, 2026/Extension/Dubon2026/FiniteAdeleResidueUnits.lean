import Dubon2026.FiniteAdeleResidueRing
import Dubon2026.FinitePlaceIntegerUnits
import Dubon2026.HeckeUpperCosets

/-! # Every ordinary residue unit lifts to an actual integral finite idele -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- A family of actual local integral units gives an original everywhere-integral finite idele. -/
def finiteAdeleIntegralUnitOfLocals (u : ∀ v : HeightOneSpectrum ℤ, (v.adicCompletionIntegers ℚ)ˣ) :
    finiteAdeleIntegerSubringˣ where
  val := ⟨finiteAdeleIntegralEmbedding (fun v => (u v).val), fun v => ((u v).val).property⟩
  inv := ⟨finiteAdeleIntegralEmbedding (fun v => (u v).inv), fun v => ((u v).inv).property⟩
  val_inv := by
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    exact congrArg Subtype.val (u v).val_inv
  inv_val := by
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    exact congrArg Subtype.val (u v).inv_val

/-- Original local evaluation of the integral unit family retains its prescribed original coordinate. -/
theorem finiteAdeleIntegralUnitOfLocals_apply
    (u : ∀ v : HeightOneSpectrum ℤ, (v.adicCompletionIntegers ℚ)ˣ) (v : HeightOneSpectrum ℤ) :
    (finiteAdeleIntegralUnitOfLocals u).val.val v = ((u v).val : v.adicCompletion ℚ) := rfl

/-- Coprimality forces the original residue representative outside every actual prime ideal dividing the modulus. -/
theorem finitePlace_coprime_not_mem (n D : ℕ) (hn : n.Coprime D) (v : HeightOneSpectrum ℤ)
    (hD : (D : ℤ) ∈ v.asIdeal) : (n : ℤ) ∉ v.asIdeal := by
  intro hnv
  apply v.isPrime.one_notMem
  rw [← heckePrime_bezout hn]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hnv) (v.asIdeal.mul_mem_right _ hD)

/-- The original local integral unit equal to n at places dividing D and to one at all other places. -/
def finiteAdeleResidueLocalUnit (D n : ℕ) (hn : n.Coprime D) (v : HeightOneSpectrum ℤ) :
    (v.adicCompletionIntegers ℚ)ˣ := by
  classical
  exact if hD : (D : ℤ) ∈ v.asIdeal then
    Classical.choose (finitePlace_integer_unit v (n : ℤ) (finitePlace_coprime_not_mem n D hn v hD))
  else 1

/-- At each actual divisor of the modulus the selected original local unit has precisely the original integer value. -/
theorem finiteAdeleResidueLocalUnit_at_divisor (D n : ℕ) (hn : n.Coprime D)
    (v : HeightOneSpectrum ℤ) (hD : (D : ℤ) ∈ v.asIdeal) :
    ((finiteAdeleResidueLocalUnit D n hn v).val : v.adicCompletion ℚ) = (n : ℤ) := by
  classical
  simp only [finiteAdeleResidueLocalUnit, dif_pos hD]
  exact Classical.choose_spec (finitePlace_integer_unit v (n : ℤ)
    (finitePlace_coprime_not_mem n D hn v hD))

/-- At each original place away from the modulus the selected local unit is exactly one. -/
theorem finiteAdeleResidueLocalUnit_away (D n : ℕ) (hn : n.Coprime D)
    (v : HeightOneSpectrum ℤ) (hD : (D : ℤ) ∉ v.asIdeal) :
    finiteAdeleResidueLocalUnit D n hn v = 1 := by
  classical
  simp only [finiteAdeleResidueLocalUnit, dif_neg hD]

/-- The genuine integral finite unit assembled from those original coordinates has residue n. -/
theorem finiteAdeleResidue_unit_lift (D n : ℕ) [NeZero D] (hn : n.Coprime D) :
    finiteAdeleResidue D (finiteAdeleIntegralUnitOfLocals (finiteAdeleResidueLocalUnit D n hn)).val =
      (n : ZMod D) := by
  have hs : finiteAdeleLevelMultiple D
      ((finiteAdeleIntegralUnitOfLocals (finiteAdeleResidueLocalUnit D n hn)).val.val - (n : ℤ)) := by
    apply (finiteAdeleLevelMultiple_iff D _).mpr
    intro v
    change algebraMap ℚ (v.adicCompletion ℚ) ((D : ℚ)⁻¹) *
      (((finiteAdeleResidueLocalUnit D n hn v).val : v.adicCompletion ℚ) - (n : ℤ)) ∈
        v.adicCompletionIntegers ℚ
    by_cases hD : (D : ℤ) ∈ v.asIdeal
    · rw [finiteAdeleResidueLocalUnit_at_divisor D n hn v hD, sub_self, mul_zero]
      exact (v.adicCompletionIntegers ℚ).zero_mem
    · rw [finiteAdeleResidueLocalUnit_away D n hn v hD]
      exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (finitePlace_inverse_level_integral D v hD)
        ((v.adicCompletionIntegers ℚ).toSubring.sub_mem (by simp) (by simp))
  simpa only [Int.cast_natCast] using (finiteAdeleResidue_eq_intCast_iff D _ (n : ℤ)).mpr hs

/-- Every genuine ordinary residue unit is the image of an actual original integral finite idele. -/
theorem finiteAdeleResidue_units_surjective (D : ℕ) [NeZero D] :
    Function.Surjective (Units.map (finiteAdeleResidue D).toMonoidHom) := by
  intro u
  refine ⟨finiteAdeleIntegralUnitOfLocals
    (finiteAdeleResidueLocalUnit D u.val.val (ZMod.val_coe_unit_coprime u)), ?_⟩
  apply Units.ext
  change finiteAdeleResidue D _ = u.val
  rw [finiteAdeleResidue_unit_lift]
  exact ZMod.natCast_zmod_val u.val

end
end Dubon2026
