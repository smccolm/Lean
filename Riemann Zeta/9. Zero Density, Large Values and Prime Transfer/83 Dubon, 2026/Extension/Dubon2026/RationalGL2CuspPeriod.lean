import Dubon2026.RationalGL2CuspFactor

/-! # Genuine vanishing real unipotent averages after every rational positive cusp translation -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

/-- Every actual positive rational cusp translate has a proved positive zero-average unipotent period, uniform in the real-group point. -/
theorem rationalPositiveGL2_unipotent_period_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (γ : GL(2, ℚ)⁺) :
    ∃ h : ℝ, 0 < h ∧ ∀ g : GL(2, ℝ)⁺,
      (∫ x in (0 : ℝ)..1, realPositiveUnitaryLift k f
        (rationalPositiveGL2ToReal γ * toGLPos (realUpperUnipotent (h * x)) * g)) = 0 := by
  obtain ⟨σ, b, hγ, hb⟩ := positiveRationalGL2_integral_upper_factor γ
  let B := realPositiveNormalize (rationalPositiveGL2ToReal b)
  have hB : B 1 0 = 0 := realPositiveNormalize_rational_upper b hb
  have ha : B 0 0 ≠ 0 := realSL2_upper_first_ne_zero B hB
  let h : ℝ := (N : ℝ) / B 0 0 ^ 2
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  refine ⟨h, div_pos hN (sq_pos_of_ne_zero ha), ?_⟩
  intro g
  have he (x : ℝ) : realPositiveUnitaryLift k f
      (rationalPositiveGL2ToReal γ * toGLPos (realUpperUnipotent (h * x)) * g) =
      realWeightLift k f (integralToRealSL σ * realUpperUnipotent ((N : ℝ) * x) *
        (B * realPositiveNormalize g)) := by
    rw [hγ, map_mul, rationalPositiveGL2ToReal_integral]
    simp only [realPositiveUnitaryLift, map_mul, realPositiveNormalize_toGLPos]
    change realWeightLift k f ((integralToRealSL σ * B) * realUpperUnipotent (h * x) *
      realPositiveNormalize g) = _
    rw [mul_assoc (integralToRealSL σ) B, realSL2_upper_unipotent B hB]
    have hh : B 0 0 ^ 2 * (h * x) = (N : ℝ) * x := by
      dsimp only [h]
      field_simp
    rw [hh]
    simp only [mul_assoc]
  simp_rw [he]
  exact realWeightLift_integral_cusp_period_zero f σ (B * realPositiveNormalize g)

/-- The original finite adelic GL2 cusp function has a genuine positive real unipotent period with zero average at every finite point. -/
theorem positiveAdelicGL2CuspLift_unipotent_period_zero (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (a : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    ∃ h : ℝ, 0 < h ∧ ∀ g : GL(2, ℝ)⁺,
      (∫ x in (0 : ℝ)..1, positiveAdelicGL2CuspLift N k f
        (toGLPos (realUpperUnipotent (h * x)) * g) a) = 0 := by
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N a
  let r := positiveAdelicGL2Representative N a
  obtain ⟨h, hh, hz⟩ := rationalPositiveGL2_unipotent_period_zero f r⁻¹
  refine ⟨h, hh, ?_⟩
  intro g
  have he (x : ℝ) : positiveAdelicGL2CuspLift N k f
      (toGLPos (realUpperUnipotent (h * x)) * g) a =
      realPositiveUnitaryLift k f
        (rationalPositiveGL2ToReal r⁻¹ * toGLPos (realUpperUnipotent (h * x)) * g) := by
    rw [positiveAdelicGL2CuspLift_of_decomposition N f _ a r u hu, map_inv, mul_assoc]
  simp_rw [he]
  exact hz g

end
end Dubon2026
