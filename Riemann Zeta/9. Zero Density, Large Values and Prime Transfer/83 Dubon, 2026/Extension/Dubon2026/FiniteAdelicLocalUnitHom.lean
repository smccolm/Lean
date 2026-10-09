import Dubon2026.FiniteAdelicLocalUnits
import Dubon2026.FiniteAdelicLocalTopology

/-! # The original local idèle insertion as a continuous group homomorphism -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Equality at all original finite places determines equality of genuine finite ideles. -/
theorem finiteAdeleUnit_ext (a b : (FiniteAdeleRing ℤ ℚ)ˣ)
    (h : ∀ v : HeightOneSpectrum ℤ, Units.map (finiteAdelePlace v).toMonoidHom a =
      Units.map (finiteAdelePlace v).toMonoidHom b) : a = b := by
  apply Units.ext
  apply DFunLike.ext
  intro v
  exact congrArg Units.val (h v)

/-- Insertion of an actual local unit into the original finite ideles preserves the group law. -/
def finiteAdeleLocalUnitHom (v : HeightOneSpectrum ℤ) :
    (v.adicCompletion ℚ)ˣ →* (FiniteAdeleRing ℤ ℚ)ˣ where
  toFun := finiteAdeleLocalUnit v
  map_one' := by
    apply finiteAdeleUnit_ext
    intro w
    by_cases h : w = v
    · subst w
      rw [finiteAdeleLocalUnit_same, map_one]
    · rw [finiteAdeleLocalUnit_ne v w h, map_one]
  map_mul' a b := by
    apply finiteAdeleUnit_ext
    intro w
    rw [map_mul]
    by_cases h : w = v
    · subst w
      rw [finiteAdeleLocalUnit_same, finiteAdeleLocalUnit_same, finiteAdeleLocalUnit_same]
    · rw [finiteAdeleLocalUnit_ne v w h, finiteAdeleLocalUnit_ne v w h,
        finiteAdeleLocalUnit_ne v w h, one_mul]

/-- The actual local idele insertion has its literal one-plus-single-coordinate formula in the original adele ring. -/
theorem finiteAdeleLocalUnit_val (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) :
    (finiteAdeleLocalUnit v u).val = 1 + finiteAdelePlaceSingle v (u.val - 1) := by
  apply DFunLike.ext
  intro w
  change finiteAdelePlace w (finiteAdeleLocalUnit v u).val =
    finiteAdelePlace w (1 + finiteAdelePlaceSingle v (u.val - 1))
  rw [map_add, map_one]
  by_cases h : w = v
  · subst w
    rw [finiteAdelePlace_single_same]
    have he := congrArg Units.val (finiteAdeleLocalUnit_same v u)
    change finiteAdelePlace v (finiteAdeleLocalUnit v u).val = u.val at he
    rw [he]
    ring
  · rw [finiteAdelePlace_single_ne v w h, add_zero]
    exact congrArg Units.val (finiteAdeleLocalUnit_ne v w h u)

/-- The genuine local idele group embedding is continuous in the original unit topologies. -/
theorem finiteAdeleLocalUnitHom_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdeleLocalUnitHom v) := by
  have hc : Continuous (fun u : (v.adicCompletion ℚ)ˣ => (finiteAdeleLocalUnitHom v u).val) := by
    have he : (fun u : (v.adicCompletion ℚ)ˣ => (finiteAdeleLocalUnitHom v u).val) =
        fun u => 1 + finiteAdelePlaceSingle v (u.val - 1) := funext (finiteAdeleLocalUnit_val v)
    rw [he]
    exact continuous_const.add ((finiteAdelePlaceSingle_continuous v).comp
      (Units.continuous_val.sub continuous_const))
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  have he : (fun u : (v.adicCompletion ℚ)ˣ => ((finiteAdeleLocalUnitHom v u)⁻¹).val) =
      fun u => (finiteAdeleLocalUnitHom v u⁻¹).val := by
    funext u
    rw [map_inv]
  rw [he]
  exact hc.comp continuous_inv

/-- The determinant of the original local matrix insertion is exactly the inserted original local determinant. -/
theorem finiteAdelicLocalGL2_det (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup.det (finiteAdelicLocalGL2 v g) = finiteAdeleLocalUnit v (GeneralLinearGroup.det g) := by
  apply finiteAdeleUnit_ext
  intro w
  have hd : Units.map (finiteAdelePlace w).toMonoidHom
      (GeneralLinearGroup.det (finiteAdelicLocalGL2 v g)) =
      GeneralLinearGroup.det (GeneralLinearGroup.map (finiteAdelePlace w) (finiteAdelicLocalGL2 v g)) :=
    (GeneralLinearGroup.map_det (finiteAdelePlace w) (finiteAdelicLocalGL2 v g)).symm
  rw [hd]
  by_cases h : w = v
  · subst w
    rw [finiteAdelicLocalGL2_same, finiteAdeleLocalUnit_same]
  · rw [finiteAdelicLocalGL2_ne v w h, finiteAdeleLocalUnit_ne v w h, map_one]

end
end Dubon2026
