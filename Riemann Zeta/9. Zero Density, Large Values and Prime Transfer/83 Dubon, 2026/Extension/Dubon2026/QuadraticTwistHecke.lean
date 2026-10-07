import Dubon2026.CuspQuadraticTwist

/-! # Actual Hecke action on the constructed quadratic cusp-form twist -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Removing a square divisor from two indices preserves the quadratic character factor. -/
theorem quadratic_character_divisor_product {D n m d : ℕ} (χ : DirichletCharacter ℂ D)
    (hq : χ.IsQuadratic) (hdD : d.Coprime D) (hdn : d ∣ n) (hdm : d ∣ m) :
    characterCoefficients χ ((n / d) * (m / d)) =
      characterCoefficients χ n * characterCoefficients χ m := by
  symm
  calc
    _ = characterCoefficients χ (d * (n / d)) * characterCoefficients χ (d * (m / d)) := by
      rw [Nat.mul_div_cancel' hdn, Nat.mul_div_cancel' hdm]
    _ = characterCoefficients χ d ^ 2 * characterCoefficients χ ((n / d) * (m / d)) := by
      simp only [characterCoefficients_mul]
      ring
    _ = _ := by rw [quadratic_characterCoefficients_sq χ hq hdD, one_mul]

/-- The literal Fourier divisor sum commutes with the character twist with its exact χ(n) factor. -/
theorem classicalHeckeCoefficient_quadraticTwist {Q D n : ℕ} (k : ℤ)
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (a : ℕ → ℂ) (m : ℕ) :
    classicalHeckeCoefficient (D * (D * Q)) k n (fun j => characterCoefficients χ j * a j) m =
      characterCoefficients χ n * characterCoefficients χ m * classicalHeckeCoefficient Q k n a m := by
  rw [classicalHeckeCoefficient, classicalHeckeCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := Nat.dvd_of_mem_divisors hd
  by_cases hdD : d.Coprime D
  · have he : d.Coprime (D * (D * Q)) ↔ d.Coprime Q := by
      constructor
      · intro h
        exact (Nat.coprime_mul_iff_right.mp (Nat.coprime_mul_iff_right.mp h).2).2
      · intro h
        exact hdD.mul_right (hdD.mul_right h)
    simp only [he]
    by_cases hdm : d.Coprime Q ∧ d ∣ m
    · simp only [if_pos hdm]
      rw [quadratic_character_divisor_product χ hq hdD hdn hdm.2]
      ring
    · simp only [if_neg hdm, mul_zero]
  · have hnD : ¬n.Coprime D := fun h => hdD (h.of_dvd_left hdn)
    have hdN : ¬d.Coprime (D * (D * Q)) := fun h => hdD (Nat.coprime_mul_iff_right.mp h).1
    simp only [hdN, false_and, if_false, characterCoefficients_of_not_coprime χ hnD, zero_mul]

/-- The constructed twist of a genuine primitive form has the expected actual eigenvalue at every positive index. -/
theorem cuspQuadraticTwist_eigenvector {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) {n : ℕ} (hn : 0 < n) :
    cuspHeckeLinear (D * (D * Q)) k n (cuspQuadraticTwist k χ hq f.toCuspForm) =
      (characterCoefficients χ n * cuspCoefficients f.toCuspForm n) •
        cuspQuadraticTwist k χ hq f.toCuspForm := by
  apply cuspCoefficients_injective (D * (D * Q)) k
  funext m
  change cuspCoefficients (cuspHecke n (cuspQuadraticTwist k χ hq f.toCuspForm)) m =
    cuspCoefficientLinear (D * (D * Q)) k m
      ((characterCoefficients χ n * cuspCoefficients f.toCuspForm n) • cuspQuadraticTwist k χ hq f.toCuspForm)
  rw [cuspHecke_coeff, map_smul]
  change classicalHeckeCoefficient (D * (D * Q)) k n
      (cuspCoefficients (cuspQuadraticTwist k χ hq f.toCuspForm)) m =
    (characterCoefficients χ n * cuspCoefficients f.toCuspForm n) *
      cuspCoefficients (cuspQuadraticTwist k χ hq f.toCuspForm) m
  have hcf : cuspCoefficients (cuspQuadraticTwist k χ hq f.toCuspForm) =
      fun j => characterCoefficients χ j * cuspCoefficients f.toCuspForm j :=
    funext (cuspQuadraticTwist_coeff k χ hχ hq f.toCuspForm)
  rw [hcf, classicalHeckeCoefficient_quadraticTwist k χ hq,
    primitiveCuspForm_hecke_coefficient_all f hn]
  ring

/-- The finite-sum twist is an actual simultaneous eigenform for all positive classical Hecke functions. -/
theorem cuspQuadraticTwist_isFullEigenform {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    IsFullCuspHeckeEigenform (cuspQuadraticTwist k χ hq f.toCuspForm) := by
  intro n hn
  refine ⟨characterCoefficients χ n * cuspCoefficients f.toCuspForm n, fun τ => ?_⟩
  have he := DFunLike.congr_fun (cuspQuadraticTwist_eigenvector f χ hχ hq hn) τ
  change cuspHecke n (cuspQuadraticTwist k χ hq f.toCuspForm) τ = _ at he
  rwa [cuspHecke_apply] at he

/-- At every prime dividing the twist modulus, the actual U operator kills the twist. -/
theorem cuspQuadraticTwist_bad_prime_zero {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) {p : ℕ} (hp : Nat.Prime p) (hpD : p ∣ D) :
    cuspHeckeLinear (D * (D * Q)) k p (cuspQuadraticTwist k χ hq f) = 0 := by
  apply cuspCoefficients_injective (D * (D * Q)) k
  funext m
  change cuspCoefficients (cuspHecke p (cuspQuadraticTwist k χ hq f)) m =
    cuspCoefficientLinear (D * (D * Q)) k m 0
  rw [cuspHecke_coeff, map_zero, classicalHeckeCoefficient_prime _ _ hp]
  have hpN : ¬p.Coprime (D * (D * Q)) := fun hc =>
    hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hc).1 hpD
  have hmD : ¬(p * m).Coprime D := fun hc =>
    hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp hc).1 hpD
  simp only [hpN, false_and, if_false, add_zero, cuspQuadraticTwist_coeff _ χ hχ hq,
    characterCoefficients_of_not_coprime χ hmD, zero_mul]

end
end Dubon2026
