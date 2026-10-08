import Dubon2026.AdelicScalarCoordinates

/-! # Exact continuous projective descent of genuinely scalar-invariant adelic functions -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The original finite projective relation preserves each actual scalar-invariant full adelic function. -/
theorem adelicFunction_finite_projective_compatible
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (r : SL(2, ℝ)) (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (hab : QuotientGroup.leftRel (Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) a b) :
    v (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a)) =
      v (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, b)) := by
  have he : (QuotientGroup.mk a : RationalFiniteProjectiveGL2) = QuotientGroup.mk b := Quotient.sound hab
  have hc := QuotientGroup.eq_iff_div_mem.mp he
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have ha : a = GeneralLinearGroup.scalar (Fin 2) u * b := by rw [hu, div_mul_cancel]
  rw [ha]
  simpa only [map_one, one_mul] using adelicFunction_scalar_pair v hv (1 : ℝˣ) u (toGL r) b

/-- The original function descends through the actual finite general-projective quotient at each real special-linear point. -/
def adelicScalarFiniteQuotientFunction
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (r : SL(2, ℝ)) : RationalFiniteProjectiveGL2 → ℂ :=
  Quotient.lift (fun a => v (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a)))
    (adelicFunction_finite_projective_compatible v hv r)

/-- The original real special-projective relation also preserves this same actual descended function. -/
theorem adelicFunction_real_projective_compatible
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (r s : SL(2, ℝ)) (hrs : QuotientGroup.leftRel (Subgroup.center SL(2, ℝ)) r s)
    (a : RationalFiniteProjectiveGL2) :
    adelicScalarFiniteQuotientFunction v hv r a = adelicScalarFiniteQuotientFunction v hv s a := by
  obtain ⟨b, rfl⟩ := ProjGenLinGroup.mk_surjective a
  have he : (QuotientGroup.mk r : PSL(2, ℝ)) = QuotientGroup.mk s := Quotient.sound hrs
  rcases (realSL2_projective_eq_iff r s).mp he with h | h
  · rw [h]
  · change v (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, b)) =
      v (rationalAdelicGL2RealFiniteEquiv.symm (toGL s, b))
    rw [h, realSL2_toGL_neg_scalar]
    simpa only [map_one, one_mul] using adelicFunction_scalar_pair v hv (-1 : ℝˣ)
      (1 : (FiniteAdeleRing ℤ ℚ)ˣ) (toGL s) b

/-- Exact descent of the original scalar-invariant function to the actual real and finite projective coordinates. -/
def adelicProjectiveFunction
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (p : AdelicProjectiveGroup) : ℂ :=
  Quotient.lift (fun r => adelicScalarFiniteQuotientFunction v hv r p.2)
    (fun r s hrs => adelicFunction_real_projective_compatible v hv r s hrs p.2) p.1

/-- Evaluating the actual descended projective function on its original representatives gives precisely the original full adelic value. -/
theorem adelicProjectiveFunction_mk
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (r : SL(2, ℝ)) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicProjectiveFunction v hv (QuotientGroup.mk r, ProjGenLinGroup.mk a) =
      v (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a)) := rfl

/-- The actual projective descent preserves continuity of the original full adelic function. -/
theorem adelicProjectiveFunction_continuous
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (hc : Continuous v) : Continuous (adelicProjectiveFunction v hv) := by
  have hq : IsOpenQuotientMap
      (fun p : SL(2, ℝ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
        ((QuotientGroup.mk p.1 : PSL(2, ℝ)), (ProjGenLinGroup.mk p.2 : RationalFiniteProjectiveGL2))) :=
    QuotientGroup.isOpenQuotientMap_mk.prodMap QuotientGroup.isOpenQuotientMap_mk
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : SL(2, ℝ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    v (rationalAdelicGL2RealFiniteEquiv.symm (toGL p.1, p.2)))
  exact hc.comp (rationalAdelicGL2RealFiniteEquiv_symm_continuous.comp
    ((continuous_toGL.comp continuous_fst).prodMk continuous_snd))

end
end Dubon2026
