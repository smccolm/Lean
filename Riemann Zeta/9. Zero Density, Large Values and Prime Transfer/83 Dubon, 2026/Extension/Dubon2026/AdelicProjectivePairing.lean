import Dubon2026.AdelicCyclicL2

/-! # Genuine arithmetic quotient integrals and the original adelic cyclic pairing -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- Original right translation carries the actual adelic arithmetic domain to another genuine fundamental domain. -/
theorem adelicProjectiveGamma0Domain_right (N : ℕ) [NeZero N] (a : AdelicProjectiveGroup) :
    IsFundamentalDomain adelicProjectiveArithmetic
      ((fun p : AdelicProjectiveGroup => p * a) '' adelicProjectiveGamma0Domain N)
        adelicProjectiveMeasure := by
  apply (adelicProjectiveGamma0Domain_isFundamental N).image_of_equiv
    (Equiv.mulRight a) (adelicProjectiveMeasure_right_invariant a⁻¹).quasiMeasurePreserving
    (Equiv.refl _)
  intro γ p
  exact mul_assoc γ.val p a

/-- Every genuine arithmetic-invariant quotient integral is unchanged by actual right projective translation. -/
theorem adelicProjective_integral_right (N : ℕ) [NeZero N] (F : AdelicProjectiveGroup → ℂ)
    (hF : ∀ (γ : adelicProjectiveArithmetic) p, F (γ • p) = F p) (a : AdelicProjectiveGroup) :
    (∫ p in adelicProjectiveGamma0Domain N, F (p * a) ∂adelicProjectiveMeasure) =
      ∫ p in adelicProjectiveGamma0Domain N, F p ∂adelicProjectiveMeasure := by
  rw [← (adelicProjectiveMeasure_right_invariant a).setIntegral_image_emb
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding]
  exact (adelicProjectiveGamma0Domain_right N a).setIntegral_eq
    (adelicProjectiveGamma0Domain_isFundamental N) hF

/-- The actual adelic Petersson pairing integrates the original faithful cyclic functions over the genuine arithmetic domain. -/
def adelicProjectiveCyclicPairing (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) : ℂ :=
  ∫ p in adelicProjectiveGamma0Domain N,
    conj (adelicCyclicProjectiveFunction N f v p) * adelicCyclicProjectiveFunction N f w p
      ∂adelicProjectiveMeasure

/-- The actual product defining the original adelic cyclic pairing is integrable. -/
theorem adelicProjectiveCyclicPairing_integrable (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    IntegrableOn (fun p => conj (adelicCyclicProjectiveFunction N f v p) *
      adelicCyclicProjectiveFunction N f w p) (adelicProjectiveGamma0Domain N)
        adelicProjectiveMeasure := by
  obtain ⟨Cv, hCv0, hCv⟩ := adelicCyclicProjectiveFunction_bounded N f v
  obtain ⟨Cw, _, hCw⟩ := adelicCyclicProjectiveFunction_bounded N f w
  apply IntegrableOn.of_bound (adelicProjectiveGamma0Domain_volume_lt_top N)
    (((adelicCyclicProjectiveFunction_continuous N f v).star.mul
      (adelicCyclicProjectiveFunction_continuous N f w)).aestronglyMeasurable.restrict) (Cv * Cw)
  apply Filter.Eventually.of_forall
  intro p
  simpa only [Pi.mul_apply, norm_mul, norm_star] using
    mul_le_mul (hCv p) (hCw p) (norm_nonneg _) hCv0

/-- Every actual simultaneous right projective translation preserves the original adelic cyclic pairing. -/
theorem adelicProjectiveCyclicPairing_right (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) (a : AdelicProjectiveGroup) :
    (∫ p in adelicProjectiveGamma0Domain N,
      conj (adelicCyclicProjectiveFunction N f v (p * a)) *
        adelicCyclicProjectiveFunction N f w (p * a) ∂adelicProjectiveMeasure) =
      adelicProjectiveCyclicPairing N f v w := by
  exact adelicProjective_integral_right N (fun p =>
    conj (adelicCyclicProjectiveFunction N f v p) * adelicCyclicProjectiveFunction N f w p)
    (fun γ p => by
      change conj (adelicCyclicProjectiveFunction N f v (γ.val * p)) *
        adelicCyclicProjectiveFunction N f w (γ.val * p) = _
      rw [adelicCyclicProjectiveFunction_arithmetic_invariant,
        adelicCyclicProjectiveFunction_arithmetic_invariant]) a

end
end Dubon2026
