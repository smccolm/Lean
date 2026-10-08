import Dubon2026.RealProjectiveCyclic

/-! # Actual invariant quotient integrals and the original cyclic Petersson pairing -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- Right translation carries the actual projective arithmetic domain to another genuine domain. -/
theorem realProjectiveGamma0Domain_right (Q : ℕ) [NeZero Q] (a : PSL(2, ℝ)) :
    IsFundamentalDomain (projectiveGamma0 Q)
      ((fun q : PSL(2, ℝ) => q * a) '' realProjectiveGamma0Domain Q) realProjectiveMeasure := by
  apply (realProjectiveGamma0Domain_isFundamental Q).image_of_equiv
    (Equiv.mulRight a) (realProjectiveMeasure_right_invariant a⁻¹).quasiMeasurePreserving
    (Equiv.refl _)
  intro g q
  exact mul_assoc (integralToRealPSL g.val) q a

/-- A genuine arithmetic-invariant quotient integral is unchanged by every right projective translation. -/
theorem realProjective_integral_right (Q : ℕ) [NeZero Q] (F : PSL(2, ℝ) → ℂ)
    (hF : ∀ (γ : projectiveGamma0 Q) q, F (γ • q) = F q) (a : PSL(2, ℝ)) :
    (∫ q in realProjectiveGamma0Domain Q, F (q * a) ∂realProjectiveMeasure) =
      ∫ q in realProjectiveGamma0Domain Q, F q ∂realProjectiveMeasure := by
  rw [← (realProjectiveMeasure_right_invariant a).setIntegral_image_emb
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding]
  exact (realProjectiveGamma0Domain_right Q a).setIntegral_eq
    (realProjectiveGamma0Domain_isFundamental Q) hF

/-- The actual Petersson integral of the two genuine descended cyclic vectors. -/
def realProjectiveCyclicPairing {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) : ℂ :=
  ∫ q in realProjectiveGamma0Domain Q,
    conj (realProjectiveCyclicVector f v q) * realProjectiveCyclicVector f w q
      ∂realProjectiveMeasure

/-- The actual product defining the quotient pairing is integrable. -/
theorem realProjectiveCyclicPairing_integrable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    IntegrableOn (fun q => conj (realProjectiveCyclicVector f v q) *
      realProjectiveCyclicVector f w q) (realProjectiveGamma0Domain Q) realProjectiveMeasure := by
  obtain ⟨Cv, hCv0, hCv⟩ := realProjectiveCyclicVector_bounded f v
  obtain ⟨Cw, _, hCw⟩ := realProjectiveCyclicVector_bounded f w
  apply IntegrableOn.of_bound (realProjectiveGamma0Domain_volume_lt_top Q)
    (((realProjectiveCyclicVector_continuous f v).star.mul
      (realProjectiveCyclicVector_continuous f w)).aestronglyMeasurable.restrict) (Cv * Cw)
  apply Filter.Eventually.of_forall
  intro q
  simpa only [Pi.mul_apply, norm_mul, norm_star] using
    mul_le_mul (hCv q) (hCw q) (norm_nonneg _) hCv0

/-- Simultaneous original right translation preserves the genuine cyclic quotient pairing. -/
theorem realProjectiveCyclicPairing_right {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) (a : PSL(2, ℝ)) :
    (∫ q in realProjectiveGamma0Domain Q,
      conj (realProjectiveCyclicVector f v (q * a)) * realProjectiveCyclicVector f w (q * a)
        ∂realProjectiveMeasure) = realProjectiveCyclicPairing f v w := by
  exact realProjective_integral_right Q (fun q =>
    conj (realProjectiveCyclicVector f v q) * realProjectiveCyclicVector f w q)
    (fun γ q => by
      dsimp only
      rw [realProjectiveCyclicVector_arithmetic, realProjectiveCyclicVector_arithmetic]) a

end
end Dubon2026
