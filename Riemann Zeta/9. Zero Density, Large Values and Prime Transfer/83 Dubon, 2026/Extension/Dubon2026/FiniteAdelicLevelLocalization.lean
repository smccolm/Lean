import Dubon2026.FiniteAdelicPlaceRemoval

/-! # Genuine split surjection from the original finite level group to each actual local level group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Evaluation of the original finite adelic level group in its actual local level group. -/
def finiteAdelicLevelAt (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    finiteAdeleGL2Gamma0 N →* finitePlaceGL2Gamma0 N v where
  toFun g := ⟨GeneralLinearGroup.map (finiteAdelePlace v) g.val,
    (finiteAdeleGL2Gamma0_iff_places N g.val).mp g.property v⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

/-- The actual single-place insertion of any original local level matrix lies in the genuine global finite level group. -/
theorem finiteAdelicLocal_level_mem (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (g : finitePlaceGL2Gamma0 N v) : finiteAdelicLocalGL2 v g.val ∈ finiteAdeleGL2Gamma0 N := by
  apply (finiteAdeleGL2Gamma0_iff_places N _).mpr
  intro w
  by_cases h : w = v
  · subst w
    rw [finiteAdelicLocalGL2_same]
    exact g.property
  · rw [finiteAdelicLocalGL2_ne v w h]
    exact (finitePlaceGL2Gamma0 N w).one_mem

/-- The original local level group has its genuine single-place embedding into the full finite level group. -/
def finiteAdelicLocalLevelHom (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    finitePlaceGL2Gamma0 N v →* finiteAdeleGL2Gamma0 N where
  toFun g := ⟨finiteAdelicLocalGL2 v g.val, finiteAdelicLocal_level_mem N v g⟩
  map_one' := Subtype.ext (finiteAdelicLocalGL2_one v)
  map_mul' g h := Subtype.ext (finiteAdelicLocalGL2_mul v g.val h.val)

/-- Actual place evaluation is a retraction of the original local level embedding. -/
theorem finiteAdelicLevelAt_local (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (g : finitePlaceGL2Gamma0 N v) : finiteAdelicLevelAt N v (finiteAdelicLocalLevelHom N v g) = g :=
  Subtype.ext (finiteAdelicLocalGL2_same v g.val)

/-- Every actual local level matrix is the genuine coordinate of an original global level matrix. -/
theorem finiteAdelicLevelAt_surjective (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    Function.Surjective (finiteAdelicLevelAt N v) :=
  fun g => ⟨finiteAdelicLocalLevelHom N v g, finiteAdelicLevelAt_local N v g⟩

end
end Dubon2026
