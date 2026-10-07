import Dubon2026.TwistFrickeTransition
import Dubon2026.FrickeCusp

/-! # The exact Fricke functional identity of a level-one quadratic twist -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- Positive determinant makes the actual Fricke slash action complex linear. -/
theorem fricke_smul_slash (N : ℕ) [NeZero N] (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] frickeMatrix N = c • (f ∣[k] frickeMatrix N) := by
  rw [ModularForm.smul_slash]
  simp only [UpperHalfPlane.σ, if_pos (frickeMatrix_det_pos N), ContinuousAlgEquiv.refl_apply]

/-- A character-weighted finite sum is exactly its sum over unit residues. -/
theorem character_smul_sum_units {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (F : ZMod D → (ℍ → ℂ)) :
    (∑ a : ZMod D, χ a • F a) = ∑ u : (ZMod D)ˣ, χ (u : ZMod D) • F u := by
  symm
  apply Fintype.sum_of_injective (fun u : (ZMod D)ˣ => (u : ZMod D)) Units.val_injective
  · intro a ha
    have hn : ¬IsUnit a := by
      intro h
      exact ha ⟨h.unit, h.unit_spec⟩
    rw [χ.map_nonunit hn, zero_smul]
  · intro u
    rfl

/-- The negative-inverse residue permutation transforms a quadratic character by χ(-1). -/
theorem quadratic_character_negative_inverse {D : ℕ} (χ : DirichletCharacter ℂ D)
    (hq : χ.IsQuadratic) (u : (ZMod D)ˣ) :
    χ (u : ZMod D) = χ (-1) * χ (-↑u⁻¹ : ZMod D) := by
  have hs : χ (-1 : ZMod D) ^ 2 = 1 := by
    have hs' : χ ((-1 : (ZMod D)ˣ) : ZMod D) ^ 2 = 1 := by
      rw [← χ.pow_apply_coe, hq.sq_eq_one, MulChar.one_apply_coe]
    simpa only [Units.coe_neg_one] using hs'
  have hi : χ (u : ZMod D) = χ (↑u⁻¹ : ZMod D) := by
    have hr := quadratic_character_unit_square χ hq u (↑u⁻¹ : ZMod D)
    simpa only [pow_two, mul_assoc, Units.mul_inv, mul_one] using hr
  rw [← neg_one_mul (↑u⁻¹ : ZMod D), map_mul, ← mul_assoc, ← pow_two, hs, one_mul]
  exact hi

/-- The actual cusp twist is the exact finite sum of determinant-normalized equal-diagonal translates. -/
theorem cuspQuadraticTwist_slash_sum {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    (cuspQuadraticTwist k χ hq f : ℍ → ℂ) =
      ((gaussSum χ ZMod.stdAddChar)⁻¹ * (D : ℂ) ^ (2 - k)) •
        ∑ a : ZMod D, χ a • ((f : ℍ → ℂ) ∣[k] heckeTriangularMatrix D D a.val) := by
  funext τ
  rw [cuspQuadraticTwist_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have ha := congr_fun (rationalTranslation_slash D a.val k (f : ℍ → ℂ)) τ
  dsimp only [Pi.smul_apply, smul_eq_mul] at ha
  rw [ha]
  ring

/-- The weighted actual slash translates have the exact Fricke functional symmetry. -/
theorem quadratic_slash_sum_fricke {D : ℕ} [NeZero D] {k : ℤ}
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) :
    (∑ a : ZMod D, χ a •
        (((f : ℍ → ℂ) ∣[k] heckeTriangularMatrix D D a.val) ∣[k] frickeMatrix (D * D))) =
      (χ (-1) * (D : ℂ) ^ (k - 2)) •
        ∑ a : ZMod D, χ a • ((f : ℍ → ℂ) ∣[k] heckeTriangularMatrix D D a.val) := by
  rw [character_smul_sum_units, character_smul_sum_units, Finset.smul_sum]
  let e : (ZMod D)ˣ ≃ (ZMod D)ˣ :=
    { toFun := fun u => -u⁻¹
      invFun := fun u => -u⁻¹
      left_inv := by intro u; simp
      right_inv := by intro u; simp }
  apply Fintype.sum_equiv e
  intro u
  rw [levelOne_translate_fricke D _ _ (twistFrickeTransition_unit_divisibility D u),
    smul_smul, smul_smul, quadratic_character_negative_inverse χ hq u]
  change (χ (-1) * χ (-↑u⁻¹ : ZMod D) * (D : ℂ) ^ (k - 2)) • _ =
    (χ (-1) * (D : ℂ) ^ (k - 2) * χ (-↑u⁻¹ : ZMod D)) • _
  congr 1
  ring

/-- The genuine level-one quadratic twist satisfies its exact Fricke functional identity. -/
theorem cuspQuadraticTwist_fricke {D : ℕ} [NeZero D] {k : ℤ}
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) :
    cuspFricke (D * (D * 1)) k (cuspQuadraticTwist k χ hq f) =
      (χ (-1) * (D : ℂ) ^ (k - 2)) • cuspQuadraticTwist k χ hq f := by
  apply DFunLike.coe_injective
  change ((cuspQuadraticTwist k χ hq f : ℍ → ℂ) ∣[k] frickeMatrix (D * (D * 1))) =
    (χ (-1) * (D : ℂ) ^ (k - 2)) • (cuspQuadraticTwist k χ hq f : ℍ → ℂ)
  rw [cuspQuadraticTwist_slash_sum, fricke_smul_slash, SlashAction.sum_slash]
  simp_rw [fricke_smul_slash]
  simp only [mul_one]
  rw [quadratic_slash_sum_fricke χ hq f, smul_comm]

end
end Dubon2026
