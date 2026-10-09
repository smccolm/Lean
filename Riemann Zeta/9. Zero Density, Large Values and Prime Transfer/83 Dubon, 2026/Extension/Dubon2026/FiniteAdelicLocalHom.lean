import Dubon2026.FiniteAdelicLocalGL2

/-! # Faithful local group homomorphisms and disjoint-place commutation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Genuine evaluation homomorphisms at all finite places separate the original finite adelic GL2 group. -/
theorem finiteAdelicGL2_ext {g h : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)}
    (he : ∀ v, GeneralLinearGroup.map (finiteAdelePlace v) g =
      GeneralLinearGroup.map (finiteAdelePlace v) h) : g = h := by
  apply Units.ext
  exact finiteAdeleMatrix_ext (fun v => congrArg Units.val (he v))

/-- The actual one-place insertion preserves the identity matrix. -/
theorem finiteAdelicLocalGL2_one (v : HeightOneSpectrum ℤ) : finiteAdelicLocalGL2 v 1 = 1 := by
  apply finiteAdelicGL2_ext
  intro w
  by_cases h : w = v
  · subst w
    rw [finiteAdelicLocalGL2_same, map_one]
  · rw [finiteAdelicLocalGL2_ne v w h, map_one]

/-- The actual one-place insertion preserves original local matrix multiplication. -/
theorem finiteAdelicLocalGL2_mul (v : HeightOneSpectrum ℤ)
    (g h : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    finiteAdelicLocalGL2 v (g * h) = finiteAdelicLocalGL2 v g * finiteAdelicLocalGL2 v h := by
  apply finiteAdelicGL2_ext
  intro w
  rw [map_mul]
  by_cases he : w = v
  · subst w
    rw [finiteAdelicLocalGL2_same, finiteAdelicLocalGL2_same, finiteAdelicLocalGL2_same]
  · rw [finiteAdelicLocalGL2_ne v w he, finiteAdelicLocalGL2_ne v w he,
      finiteAdelicLocalGL2_ne v w he, one_mul]

/-- The genuine local GL2 group embeds into the original finite adelic group as matrices supported at this actual place. -/
def finiteAdelicLocalGL2Hom (v : HeightOneSpectrum ℤ) :
    GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) →*
      GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) where
  toFun := finiteAdelicLocalGL2 v
  map_one' := finiteAdelicLocalGL2_one v
  map_mul' := finiteAdelicLocalGL2_mul v

/-- Evaluation at the actual place proves faithfulness of its original local group embedding. -/
theorem finiteAdelicLocalGL2Hom_injective (v : HeightOneSpectrum ℤ) :
    Function.Injective (finiteAdelicLocalGL2Hom v) := by
  intro g h he
  have hh := congrArg (GeneralLinearGroup.map (finiteAdelePlace v)) he
  simpa only [finiteAdelicLocalGL2Hom, MonoidHom.coe_mk, OneHom.coe_mk,
    finiteAdelicLocalGL2_same] using hh

/-- The original local subgroups at distinct actual finite places commute inside the genuine adelic group. -/
theorem finiteAdelicLocalGL2_commute (v w : HeightOneSpectrum ℤ) (hne : v ≠ w)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (h : GeneralLinearGroup (Fin 2) (w.adicCompletion ℚ)) :
    Commute (finiteAdelicLocalGL2 v g) (finiteAdelicLocalGL2 w h) := by
  apply finiteAdelicGL2_ext
  intro u
  simp only [map_mul]
  by_cases hv : u = v
  · subst u
    rw [finiteAdelicLocalGL2_ne w v hne, mul_one, one_mul]
  · rw [finiteAdelicLocalGL2_ne v u hv, one_mul, mul_one]

end
end Dubon2026
