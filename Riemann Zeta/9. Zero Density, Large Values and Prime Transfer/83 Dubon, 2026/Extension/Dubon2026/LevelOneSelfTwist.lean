import Dubon2026.CuspFiniteDepletion
import Dubon2026.QuadraticTwistFricke

/-! # Level-one primitive forms have no nontrivial quadratic self-twist -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Coprimality only depends on the actual set of prime divisors. -/
theorem coprime_primeFactors_product (D : ℕ) [NeZero D] (n : ℕ) :
    n.Coprime (∏ p ∈ D.primeFactors, p) ↔ n.Coprime D := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpn hpD
    have hpR : p ∣ ∏ q ∈ D.primeFactors, q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (hp.mem_primeFactors' hpD)
    exact hp.not_dvd_one (Nat.eq_one_of_dvd_coprimes h hpn hpR ▸ dvd_refl p)
  · intro h
    exact h.of_dvd_right (Nat.prod_primeFactors_dvd D)

/-- A genuine level-one self-twist is exactly the deletion of coefficients not coprime to the modulus. -/
theorem levelOne_selfTwist_coeff {D : ℕ} [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm 1 k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (ht : IsCoefficientSelfTwist 1 χ (cuspCoefficients f.toCuspForm)) (n : ℕ) :
    cuspCoefficients (cuspQuadraticTwist k χ hq f.toCuspForm) n =
      if n.Coprime D then cuspCoefficients f.toCuspForm n else 0 := by
  rw [cuspQuadraticTwist_coeff k χ hχ]
  by_cases hn : n.Coprime D
  · rw [if_pos hn]
    exact primitiveCuspForm_selfTwist_coefficients f χ hq ht n (by simpa only [one_mul] using hn)
  · rw [if_neg hn, characterCoefficients_of_not_coprime χ hn, zero_mul]

/-- Normalization and the exact Fricke identity determine the actual first coefficient of a twist. -/
theorem levelOne_twist_fricke_first {D : ℕ} [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm 1 k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    cuspCoefficients (cuspFricke (D * (D * 1)) k (cuspQuadraticTwist k χ hq f.toCuspForm)) 1 =
      χ (-1) * (D : ℂ) ^ (k - 2) := by
  rw [cuspQuadraticTwist_fricke]
  change cuspCoefficientLinear (D * (D * 1)) k 1 (_ • _) = _
  rw [map_smul]
  change _ * cuspCoefficients (cuspQuadraticTwist k χ hq f.toCuspForm) 1 = _
  rw [cuspQuadraticTwist_normalized k χ hχ hq f.toCuspForm f.normalized, mul_one]

/-- Comparing the actual Fricke coefficient with genuine finite depletion forces every primitive quadratic self-twist modulus at level one to equal one. -/
theorem primitiveCuspForm_levelOne_selfTwist_modulus {D : ℕ} [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm 1 k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (ht : IsCoefficientSelfTwist 1 χ (cuspCoefficients f.toCuspForm)) : D = 1 := by
  let R : ℕ := ∏ p ∈ D.primeFactors, p
  have hRpos : 0 < R := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  letI : NeZero R := ⟨hRpos.ne'⟩
  obtain ⟨g, hg, _, hw⟩ := exists_cuspFiniteDepletion D.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (R := R) rfl (L := R * R) rfl f
  have hRD : R ∣ D := Nat.prod_primeFactors_dvd D
  obtain ⟨t, hD⟩ := hRD
  have ht0 : t ≠ 0 := by intro hz; simp [hz] at hD; exact NeZero.ne D hD
  letI : NeZero t := ⟨ht0⟩
  have hinc : 1 * (R * R) ∣ D * (D * 1) := ⟨t * t, by rw [hD]; ring⟩
  let G := cuspDegeneracyMap 1 hinc k g
  have hG : G = cuspQuadraticTwist k χ hq f.toCuspForm := by
    apply cuspCoefficients_injective (D * (D * 1)) k
    funext n
    dsimp only [G]
    rw [cuspDegeneracyMap_coeff, if_pos (one_dvd n), Nat.div_one, hg,
      levelOne_selfTwist_coeff f χ hχ hq ht]
    exact if_congr (coprime_primeFactors_product D n) rfl rfl
  have hW := cuspFricke_degeneracy_coeff_one (N := D * (D * 1))
    1 (t * t) (by rw [hD]; ring) k g
  simp only [Nat.cast_one] at hW
  change cuspCoefficients (cuspFricke (D * (D * 1)) k G) 1 =
    (if t * t = 1 then (1 : ℂ)⁻¹ * cuspCoefficients (cuspFricke (R * R) k g) 1 else 0) at hW
  rw [hG, levelOne_twist_fricke_first f χ hχ hq, hw, inv_one, one_mul] at hW
  have hc : ‖χ (-1 : ZMod D)‖ = 1 := by
    simpa only [Units.coe_neg_one] using χ.unit_norm_eq_one (-1)
  have hc0 : χ (-1 : ZMod D) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hc
    exact zero_ne_one hc
  have htt : t * t = 1 := by
    by_contra hn
    rw [if_neg hn] at hW
    exact (mul_ne_zero hc0 (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne D)))) hW
  have ht1 : t = 1 := by nlinarith [Nat.pos_of_ne_zero ht0]
  have hRD' : R = D := by simpa only [ht1, mul_one] using hD.symm
  rw [if_pos htt, hRD'] at hW
  have hpow : (D : ℂ) ^ (k - 2) = (D : ℂ) ^ (k - 3) * D := by
    rw [show k - 2 = (k - 3) + 1 by omega,
      zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne D)), zpow_one]
  have heq : χ (-1) * (D : ℂ) = 1 := by
    apply mul_right_cancel₀ (zpow_ne_zero (k - 3) (Nat.cast_ne_zero.mpr (NeZero.ne D)))
    calc
      _ = χ (-1) * (D : ℂ) ^ (k - 2) := by rw [hpow]; ring
      _ = _ := by rw [hW, one_mul]
  have hn := congrArg norm heq
  rw [norm_mul, hc, Complex.norm_natCast, norm_one, one_mul] at hn
  exact_mod_cast hn

/-- Every genuine level-one primitive form is non-CM in the actual quadratic self-twist sense. -/
theorem primitiveCuspForm_levelOne_nonCM {k : ℤ} (f : PrimitiveCuspForm 1 k) :
    IsNonCMCuspForm f.toCuspForm := by
  rintro ⟨D, χ, hχ, hne, hq, ht⟩
  exact hne (DirichletCharacter.level_one' χ
    (primitiveCuspForm_levelOne_selfTwist_modulus f χ hχ hq ht))

/-- A genuine normalized level-one eigenform carries the non-CM primitive structure, with both properties proved. -/
def nonCMPrimitiveCuspFormLevelOne {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1)
    (he : IsCuspHeckeEigenform f) : NonCMPrimitiveCuspForm 1 k where
  toPrimitiveCuspForm := primitiveCuspFormLevelOne f hf he
  nonCM := primitiveCuspForm_levelOne_nonCM (primitiveCuspFormLevelOne f hf he)

end
end Dubon2026
