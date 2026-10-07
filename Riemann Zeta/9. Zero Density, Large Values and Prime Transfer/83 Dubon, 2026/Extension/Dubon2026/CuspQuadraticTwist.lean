import Dubon2026.CharacterTwistInvariant

/-! # Genuine quadratic character twists of Gamma0 cusp forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual quadratic twist endomorphism when the level contains the squared character modulus. -/
def cuspQuadraticTwistAtLevel {D H : ℕ} [NeZero D] [NeZero H] (hDH : D ∣ H) (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic) :
    CuspForm ((Gamma0 (D * H)).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 (D * H)).map (mapGL ℝ)) k :=
  (principalUpperToGamma0 (D * H) k).comp
    (((principalCharacterTwist (D * H) k χ).comp (cuspRescaledPrincipal (D * H) k)).codRestrict
      (principalUpperInvariantSpace (D * H) k) (fun f =>
        principalCharacterTwist_mem_upper hDH k χ hq _
          (fun γ => cuspRescaledPrincipal_upper_fixed (D * H) k f γ.val γ.property)))

/-- Every coefficient of the constructed cusp form is the literal character twist. -/
theorem cuspQuadraticTwistAtLevel_coeff {D H : ℕ} [NeZero D] [NeZero H]
    (hDH : D ∣ H) (k : ℤ) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 (D * H)).map (mapGL ℝ)) k) (n : ℕ) :
    cuspCoefficients (cuspQuadraticTwistAtLevel hDH k χ hq f) n =
      characterCoefficients χ n * cuspCoefficients f n := by
  rw [cuspQuadraticTwistAtLevel, LinearMap.comp_apply, principalUpperToGamma0_coeff]
  change principalCuspCoefficients
      (principalCharacterTwist (D * H) k χ (cuspRescaledPrincipal (D * H) k f)) n = _
  rw [principalCharacterTwist_coeff (dvd_mul_right D H) k χ hχ hq, cuspRescaledPrincipal_coeff]

/-- The actual twist of a level-Q cusp form, at the explicit level D²Q. -/
def cuspQuadraticTwist {Q D : ℕ} [NeZero Q] [NeZero D] (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 (D * (D * Q))).map (mapGL ℝ)) k :=
  (cuspQuadraticTwistAtLevel (dvd_mul_right D Q) k χ hq).comp
    (cuspLevelInclusion (show Q ∣ D * (D * Q) from ⟨D * D, by ring⟩) k)

/-- The level-D²Q twist has the exact original coefficients multiplied by χ(n). -/
theorem cuspQuadraticTwist_coeff {Q D : ℕ} [NeZero Q] [NeZero D] (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    cuspCoefficients (cuspQuadraticTwist k χ hq f) n =
      characterCoefficients χ n * cuspCoefficients f n := by
  rw [cuspQuadraticTwist, LinearMap.comp_apply, cuspQuadraticTwistAtLevel_coeff _ _ _ hχ,
    cuspLevelInclusion_coeff]

/-- Twisting preserves the normalization of the actual first Fourier coefficient. -/
theorem cuspQuadraticTwist_normalized {Q D : ℕ} [NeZero Q] [NeZero D] (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1) :
    cuspCoefficients (cuspQuadraticTwist k χ hq f) 1 = 1 := by
  rw [cuspQuadraticTwist_coeff k χ hχ hq, characterCoefficients_one, one_mul, hf]

/-- The constructed twist of a normalized genuine cusp form is nonzero. -/
theorem cuspQuadraticTwist_ne_zero {Q D : ℕ} [NeZero Q] [NeZero D] (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1) :
    cuspQuadraticTwist k χ hq f ≠ 0 := by
  intro hz
  have hn := cuspQuadraticTwist_normalized k χ hχ hq f hf
  change cuspCoefficientLinear (D * (D * Q)) k 1 (cuspQuadraticTwist k χ hq f) = 1 at hn
  rw [hz, map_zero] at hn
  exact zero_ne_one hn

end
end Dubon2026
