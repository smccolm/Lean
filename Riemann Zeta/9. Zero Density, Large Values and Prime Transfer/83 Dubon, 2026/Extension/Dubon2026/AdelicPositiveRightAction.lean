import Dubon2026.AdelicProjectiveL2Embedding

/-! # Actual positive adelic right translations preserve the original quotient L2 pairing -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- The genuine positive real and finite matrix pair is embedded in the original canonical full adelic group. -/
def positiveAdelicGL2Embedding :
    GL(2, ℝ)⁺ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* RationalAdelicGL2 :=
  rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom.comp
    (((GLPos (Fin 2) ℝ).subtype.comp (MonoidHom.fst _ _)).prod (MonoidHom.snd _ _))

/-- The actual projective coordinate of an original positive real and finite matrix pair. -/
def positiveAdelicGL2Projective :
    GL(2, ℝ)⁺ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* AdelicProjectiveGroup :=
  (((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp realPositiveNormalize).comp
    (MonoidHom.fst _ _)).prod (ProjGenLinGroup.mk.comp (MonoidHom.snd _ _))

/-- Original positive full adelic right translation descends exactly to genuine projective right translation. -/
theorem adelicCyclicProjectiveFunction_positive_right (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (h : GL(2, ℝ)⁺ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (positiveAdelicGL2Embedding h) v) p =
        adelicCyclicProjectiveFunction N f v (p * positiveAdelicGL2Projective h) := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp, adelicCyclicProjectiveFunction_mk]
  have he : (QuotientGroup.mk r, ProjGenLinGroup.mk a) * positiveAdelicGL2Projective h =
      (QuotientGroup.mk (realPositiveNormalize (toGLPos r * h.1)), ProjGenLinGroup.mk (a * h.2)) := by
    apply Prod.ext
    · simp only [positiveAdelicGL2Projective, MonoidHom.prod_apply, MonoidHom.comp_apply,
        Prod.fst_mul, map_mul, realPositiveNormalize_toGLPos,
        QuotientGroup.mk_mul]
      rfl
    · simp only [positiveAdelicGL2Projective, MonoidHom.prod_apply, MonoidHom.comp_apply,
        Prod.snd_mul, map_mul]
      rfl
  rw [he, adelicCyclicProjectiveFunction_recover_positive]
  change v.val (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a) *
    rationalAdelicGL2RealFiniteEquiv.symm (h.1.val, h.2)) = _
  rw [← map_mul]
  rfl

/-- Every original positive adelic matrix preserves the actual faithful L2 inner product of its original cyclic representation. -/
theorem adelicLiftCyclic_positive_inner (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (h : GL(2, ℝ)⁺ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    inner ℂ (adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (positiveAdelicGL2Embedding h) v))
      (adelicProjectiveCyclicToL2 N f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation (positiveAdelicGL2Embedding h) w)) =
      inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) := by
  rw [adelicProjectiveCyclicToL2_inner, adelicProjectiveCyclicToL2_inner]
  change (∫ p in adelicProjectiveGamma0Domain N,
    conj (adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (positiveAdelicGL2Embedding h) v) p) *
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (positiveAdelicGL2Embedding h) w) p
    ∂adelicProjectiveMeasure) = _
  simp_rw [adelicCyclicProjectiveFunction_positive_right]
  exact adelicProjectiveCyclicPairing_right N f v w (positiveAdelicGL2Projective h)

end
end Dubon2026
