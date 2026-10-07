import Dubon2026.CharacterTwistCongruence

/-! # Actual upper congruence invariance of quadratic twists -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

/-- Upper congruence acts on the actual translates by the proved finite coset permutation. -/
theorem principalTranslation_upper_relation {D H : ℕ} (hDH : D ∣ H) (k : ℤ)
    (f : CuspForm ((Gamma (D * H)).map (mapGL ℝ)) k)
    (hf : f ∈ principalUpperInvariantSpace (D * H) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper (D * H)) (a b : ℤ)
    (hab : (b : ZMod D) = (γ 1 1 : ZMod D) ^ 2 * (a : ZMod D)) :
    normalCuspAction (Gamma (D * H)) k γ⁻¹
        (principalTranslation (D * H) k (a * H) f) =
      principalTranslation (D * H) k (b * H) f := by
  let ρ := normalCuspAction (Gamma (D * H)) k
  let δ := ModularGroup.T ^ (a * H) * γ * (ModularGroup.T ^ (b * H))⁻¹
  have hδ : δ ∈ GammaUpper (D * H) := characterTwist_translation_conjugate hDH γ hγ a b hab
  have hfix : ρ δ⁻¹ f = f := hf ⟨δ⁻¹, (GammaUpper (D * H)).inv_mem hδ⟩
  change ρ γ⁻¹ (ρ (ModularGroup.T ^ (a * H))⁻¹ f) = ρ (ModularGroup.T ^ (b * H))⁻¹ f
  calc
    _ = ρ (ModularGroup.T ^ (b * H))⁻¹ (ρ δ⁻¹ f) := by
      have hg : γ⁻¹ * (ModularGroup.T ^ (a * H))⁻¹ =
          (ModularGroup.T ^ (b * H))⁻¹ * δ⁻¹ := by
        dsimp only [δ]
        group
      simpa only [map_mul, Module.End.mul_apply] using congrArg (fun x => ρ x f) hg
    _ = _ := by rw [hfix]

/-- A quadratic character is unchanged by multiplication by a unit square. -/
theorem quadratic_character_unit_square {D : ℕ} (χ : DirichletCharacter ℂ D)
    (hq : χ.IsQuadratic) (u : (ZMod D)ˣ) (a : ZMod D) :
    χ ((u : ZMod D) ^ 2 * a) = χ a := by
  have hs : χ (u : ZMod D) ^ 2 = 1 := by
    rw [← χ.pow_apply_coe, hq.sq_eq_one, MulChar.one_apply_coe]
  rw [map_mul, map_pow, hs, one_mul]

set_option maxHeartbeats 800000 in
/-- When D² divides the level, the genuine quadratic character sum preserves upper invariance. -/
theorem principalCharacterTwist_mem_upper {D H : ℕ} [NeZero D] (hDH : D ∣ H) (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma (D * H)).map (mapGL ℝ)) k)
    (hf : f ∈ principalUpperInvariantSpace (D * H) k) :
    principalCharacterTwist (D * H) k χ f ∈ principalUpperInvariantSpace (D * H) k := by
  rintro ⟨γ, hγ⟩
  change normalCuspAction (Gamma (D * H)) k γ (principalCharacterTwist (D * H) k χ f) = _
  have hδ : γ⁻¹ ∈ GammaUpper (D * H) := (GammaUpper (D * H)).inv_mem hγ
  have hd := GammaUpper_diagonal_mul (dvd_mul_right D H) γ⁻¹ hδ
  have hu : IsUnit ((γ⁻¹) 1 1 : ZMod D) :=
    IsUnit.of_mul_eq_one ((γ⁻¹) 0 0 : ZMod D) (by simpa only [mul_comm] using hd)
  let u : (ZMod D)ˣ := hu.unit
  let e : ZMod D ≃ ZMod D := (u ^ 2).mulLeft
  have huval : (u : ZMod D) = ((γ⁻¹) 1 1 : ZMod D) := hu.unit_spec
  have he (a : ZMod D) : e a = ((γ⁻¹) 1 1 : ZMod D) ^ 2 * a := by
    change (u : ZMod D) ^ 2 * a = _
    rw [huval]
  have hw (a : ZMod D) : χ (e a) = χ a := quadratic_character_unit_square χ hq u a
  have ht (a : ZMod D) :
      normalCuspAction (Gamma (D * H)) k γ
          (principalTranslation (D * H) k (a.val * ((D * H) / D) : ℕ) f) =
        principalTranslation (D * H) k ((e a).val * ((D * H) / D) : ℕ) f := by
    have hr := principalTranslation_upper_relation hDH k f hf γ⁻¹ hδ a.val (e a).val (by
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      exact he a)
    simpa only [inv_inv, Nat.mul_div_cancel_left H (Nat.pos_of_neZero D), Nat.cast_mul] using hr
  simp only [principalCharacterTwist, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv e
  intro a
  rw [ht, hw]

end
end Dubon2026
