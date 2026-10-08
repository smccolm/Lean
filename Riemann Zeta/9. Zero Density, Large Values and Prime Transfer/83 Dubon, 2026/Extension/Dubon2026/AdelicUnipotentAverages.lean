import Dubon2026.AdelicUnipotentQuotient
import Dubon2026.CompactRealOrbitAverage

/-! # Actual vanishing adelic unipotent integrals on the positive real component -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix.SpecialLinearGroup
open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm unitInterval

/-- Addition of original real unipotent parameters is exactly multiplication in the genuine positive real group. -/
theorem realPositiveUpperUnipotent_add (s t : ℝ) :
    toGLPos (realUpperUnipotent (s + t)) =
      toGLPos (realUpperUnipotent s) * toGLPos (realUpperUnipotent t) := by
  apply Subtype.ext
  change toGL (realUpperUnipotent (s + t)) =
    toGL (realUpperUnipotent s) * toGL (realUpperUnipotent t)
  simp only [← realUpperRightHom_eq_toGL, AddChar.map_add_eq_mul]

/-- The original interval integral equals integration over the actual unit interval probability space. -/
theorem unitInterval_integral_eq_intervalIntegral (F : ℝ → ℂ) :
    (∫ t : I, F (t : ℝ)) = ∫ t in (0 : ℝ)..1, F t := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

/-- The original unipotent quotient function has a genuine zero real-period average at every point of its dense real orbit. -/
theorem adelicUnipotentQuotientFunction_real_average_zero (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (a : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∃ h : ℝ, 0 < h ∧ ∀ b : ℝ,
      (∫ t : I, adelicUnipotentQuotientFunction N f
        (rationalAdelicGL2RealFiniteEquiv.symm (g.val, a))
        (rationalAdelicRealQuotientMap (h * (t : ℝ)) + rationalAdelicRealQuotientMap b)) = 0 := by
  obtain ⟨h, hh, hz⟩ := positiveAdelicGL2CuspLift_unipotent_period_zero N f a
  refine ⟨h, hh, ?_⟩
  intro b
  simp_rw [← map_add, adelicUnipotentQuotientFunction_real,
    realPositiveUpperUnipotent_add, mul_assoc]
  rw [unitInterval_integral_eq_intervalIntegral (fun t =>
    positiveAdelicGL2CuspLift N k f
      (toGLPos (realUpperUnipotent (h * t)) * (toGLPos (realUpperUnipotent b) * g)) a)]
  exact hz (toGLPos (realUpperUnipotent b) * g)

/-- The genuine additive Haar unipotent integral of the original cusp function is zero at every positive real adelic point. -/
theorem adelicUnipotentQuotientFunction_integral_zero_positive (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (a : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    (∫ z, adelicUnipotentQuotientFunction N f
      (rationalAdelicGL2RealFiniteEquiv.symm (g.val, a)) z ∂rationalAdelicAdditiveHaar) = 0 := by
  obtain ⟨h, _, hz⟩ := adelicUnipotentQuotientFunction_real_average_zero N f g a
  exact compact_additive_integral_zero_of_dense_real_period rationalAdelicAdditiveHaar
    rationalAdelicRealQuotientMap rationalAdelicRealQuotientMap_continuous
    rationalAdelicRealQuotientMap_dense _ (adelicUnipotentQuotientFunction_continuous N f _) h hz

end
end Dubon2026
