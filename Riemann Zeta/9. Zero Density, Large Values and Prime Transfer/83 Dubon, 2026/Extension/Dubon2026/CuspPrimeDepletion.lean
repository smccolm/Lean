import Dubon2026.QuadraticTwistHecke

/-! # Exact prime depletion by genuine degeneracy maps -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual three-term prime depletion, realized in the level-p²M cusp space. -/
def cuspPrimeDepletion {M p : ℕ} [NeZero p] (k : ℤ) (eigenvalue : ℂ) :
    CuspForm ((Gamma0 M).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 (p * (p * M))).map (mapGL ℝ)) k :=
  cuspDegeneracyMap 1 (by simp only [one_mul]; exact ⟨p * p, by ring⟩) k -
    eigenvalue • cuspDegeneracyMap p (dvd_mul_left (p * M) p) k +
    (p : ℂ) ^ (k - 1) • cuspDegeneracyMap (p * p) (by rw [mul_assoc]) k

/-- Exact q-expansion of the three genuine degeneracy terms. -/
theorem cuspPrimeDepletion_coeff_formula {M p : ℕ} [NeZero p] (k : ℤ) (eigenvalue : ℂ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (n : ℕ) :
    cuspCoefficients (cuspPrimeDepletion (p := p) k eigenvalue f) n = cuspCoefficients f n -
      eigenvalue * (if p ∣ n then cuspCoefficients f (n / p) else 0) +
      (p : ℂ) ^ (k - 1) * (if p * p ∣ n then cuspCoefficients f (n / (p * p)) else 0) := by
  change cuspCoefficientLinear (p * (p * M)) k n (cuspPrimeDepletion (p := p) k eigenvalue f) = _
  simp only [cuspPrimeDepletion, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  change cuspCoefficients (cuspDegeneracyMap 1 _ k f) n -
      eigenvalue * cuspCoefficients (cuspDegeneracyMap p _ k f) n +
      (p : ℂ) ^ (k - 1) * cuspCoefficients (cuspDegeneracyMap (p * p) _ k f) n = _
  simp only [cuspDegeneracyMap_coeff, one_dvd, if_true, Nat.div_one]

/-- For an actual good-prime eigenvector, the three-term cusp construction deletes precisely the p-multiple coefficients. -/
theorem cuspPrimeDepletion_coeff {M p : ℕ} [NeZero M] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpM : p.Coprime M) (eigenvalue : ℂ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (hf : cuspHeckeLinear M k p f = eigenvalue • f) (n : ℕ) :
    cuspCoefficients (cuspPrimeDepletion (p := p) k eigenvalue f) n = if p ∣ n then 0 else cuspCoefficients f n := by
  rw [cuspPrimeDepletion_coeff_formula]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have he := congrArg (cuspCoefficientLinear M k m) hf
    change cuspCoefficients (cuspHecke p f) m = cuspCoefficientLinear M k m (eigenvalue • f) at he
    rw [cuspHecke_coeff, map_smul, classicalHeckeCoefficient_prime M k hp] at he
    change cuspCoefficients f (p * m) +
        (if p.Coprime M ∧ p ∣ m then (p : ℂ) ^ (k - 1) * cuspCoefficients f (m / p) else 0) =
      eigenvalue * cuspCoefficients f m at he
    have hdiv : p * m / (p * p) = m / p := by
      rw [mul_comm p m, Nat.mul_div_mul_right _ _ hp.pos]
    simp only [dvd_mul_right p m, if_true, Nat.mul_div_cancel_left m hp.pos,
      Nat.mul_dvd_mul_iff_left hp.pos, hdiv]
    split_ifs with hm
    · rw [if_pos ⟨hpM, hm⟩] at he
      linear_combination he
    · rw [if_neg (fun h => hm h.2)] at he
      linear_combination he
  · have hppn : ¬p * p ∣ n := fun h => hpn ((dvd_mul_right p p).trans h)
    simp only [if_neg hpn, if_neg hppn, mul_zero, sub_zero, add_zero]

/-- Good-prime Hecke operators away from the enlarged level commute with the actual depletion map. -/
theorem cuspPrimeDepletion_hecke_commute {M p q : ℕ} [NeZero M] [NeZero p] [NeZero q]
    (k : ℤ) (eigenvalue : ℂ) (hq : Nat.Prime q) (hqN : q.Coprime (p * (p * M)))
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspHeckeLinear (p * (p * M)) k q (cuspPrimeDepletion (p := p) k eigenvalue f) =
      cuspPrimeDepletion (p := p) k eigenvalue (cuspHeckeLinear M k q f) := by
  simp only [cuspPrimeDepletion, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    map_add, map_sub, map_smul, cuspHeckeLinear_prime_degeneracy _ _ k hq hqN]

end
end Dubon2026
