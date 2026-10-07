import Dubon2026.HeckePrimePowerArithmetic
import Mathlib.Data.Nat.Factorization.Induction

/-! # Genuine cusp-space preservation at every classical Hecke index

Prime-power recurrences and coprime divisor convolution construct actual cusp
forms. Their convergent Fourier expansions then identify the output with the
literal finite analytic Hecke function; no preservation hypothesis is assumed.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The genuine prime-power Hecke endomorphism, built by its classical two-step recurrence. -/
def cuspHeckePrimePower {Q p : ℕ} [NeZero Q] [NeZero p] (k : ℤ) (hp : Nat.Prime p) :
    ℕ → Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
  | 0 => 1
  | 1 => cuspHeckePrimeLinear k hp
  | r + 2 => cuspHeckePrimeLinear k hp * cuspHeckePrimePower k hp (r + 1) -
      heckeDivisorWeight Q k p • cuspHeckePrimePower k hp r

/-- The constructed prime-power cusp operator has the exact literal classical Fourier transform. -/
theorem cuspHeckePrimePower_coeff {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ} (hp : Nat.Prime p)
    (r : ℕ) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (m : ℕ) :
    cuspCoefficients (cuspHeckePrimePower k hp r f) m =
      classicalHeckeCoefficient Q k (p ^ r) (cuspCoefficients f) m := by
  induction r using Nat.twoStepInduction generalizing f m with
  | zero => simp [cuspHeckePrimePower, classicalHeckeCoefficient]
  | one => simpa only [cuspHeckePrimePower, pow_one] using cuspHeckePrime_coeff hp f m
  | more r ih0 ih1 =>
    change cuspCoefficientLinear Q k m
      (cuspHeckePrime hp (cuspHeckePrimePower k hp (r + 1) f) -
        heckeDivisorWeight Q k p • cuspHeckePrimePower k hp r f) = _
    rw [map_sub, map_smul]
    change cuspCoefficients (cuspHeckePrime hp (cuspHeckePrimePower k hp (r + 1) f)) m -
      heckeDivisorWeight Q k p * cuspCoefficients (cuspHeckePrimePower k hp r f) m = _
    have hcoeff : cuspCoefficients (cuspHeckePrimePower k hp (r + 1) f) =
        classicalHeckeCoefficient Q k (p ^ (r + 1)) (cuspCoefficients f) := funext (ih1 f)
    rw [cuspHeckePrime_coeff, hcoeff, ih0]
    exact classicalHeckeCoefficient_primePower Q k hp (cuspCoefficients f) r m

/-- Every actual classical Fourier transform is realized by a cusp form at the original level. -/
theorem exists_cuspForm_hecke_coeff {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ∃ g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k,
      ∀ m, cuspCoefficients g m = classicalHeckeCoefficient Q k n (cuspCoefficients f) m := by
  induction n using Nat.recOnPrimeCoprime generalizing f with
  | zero =>
    refine ⟨0, fun m => ?_⟩
    change cuspCoefficientLinear Q k m 0 = _
    rw [map_zero]
    simp [classicalHeckeCoefficient]
  | prime_pow p r hp =>
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact ⟨cuspHeckePrimePower k hp r f, cuspHeckePrimePower_coeff hp r f⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨gb, hgb⟩ := ihb f
    obtain ⟨ga, hga⟩ := iha gb
    refine ⟨ga, fun m => ?_⟩
    rw [hga, funext hgb]
    exact (classicalHeckeCoefficient_coprime_comp Q k (by omega) (by omega) hab
      (cuspCoefficients f) m).symm

/-- The finite classical Hecke function is realized by an actual cusp form at the same level. -/
theorem exists_cuspForm_hecke_function {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ∃ g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k,
      (∀ τ, g τ = classicalHeckeFunction Q k n f τ) ∧
      ∀ m, cuspCoefficients g m = classicalHeckeCoefficient Q k n (cuspCoefficients f) m := by
  obtain ⟨g, hg⟩ := exists_cuspForm_hecke_coeff n f
  refine ⟨g, ?_, hg⟩
  intro τ
  have hs := cuspCoefficients_hasSum g τ
  simp_rw [hg] at hs
  exact hs.unique (by
    simpa only [smul_eq_mul] using hasSum_classicalHeckeFunction Q k n f (cuspCoefficients f) τ
      (fun σ => by simpa only [smul_eq_mul] using cuspCoefficients_hasSum f σ))

/-- The actual all-index classical Hecke cusp form, identified with its literal finite formula. -/
def cuspHecke {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k := (exists_cuspForm_hecke_function n f).choose

/-- The all-index cusp operator evaluates to the actual finite analytic Hecke function. -/
theorem cuspHecke_apply {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspHecke n f τ = classicalHeckeFunction Q k n f τ :=
  (exists_cuspForm_hecke_function n f).choose_spec.1 τ

/-- The all-index cusp operator has the actual classical Fourier divisor formula. -/
theorem cuspHecke_coeff {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (m : ℕ) :
    cuspCoefficients (cuspHecke n f) m = classicalHeckeCoefficient Q k n (cuspCoefficients f) m :=
  (exists_cuspForm_hecke_function n f).choose_spec.2 m

/-- The classical Hecke operator at every index is a genuine complex linear cusp endomorphism. -/
def cuspHeckeLinear (Q : ℕ) [NeZero Q] (k : ℤ) (n : ℕ) :
    Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) where
  toFun := cuspHecke n
  map_add' f g := by
    ext τ
    simp only [cuspHecke_apply, CuspForm.add_apply]
    exact classicalHeckeFunction_add Q k n f g τ
  map_smul' c f := by
    ext τ
    change cuspHecke n (c • f) τ = c * cuspHecke n f τ
    rw [cuspHecke_apply, cuspHecke_apply]
    exact classicalHeckeFunction_smul Q k n c f τ

/-- All classical finite Hecke functions are slash invariant at the original positive level. -/
theorem classicalHeckeFunction_slash {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma0 Q).map (mapGL ℝ)) :
    classicalHeckeFunction Q k n f ∣[k] γ = classicalHeckeFunction Q k n f := by
  have he : classicalHeckeFunction Q k n f = ⇑(cuspHecke n f) :=
    (funext (cuspHecke_apply n f)).symm
  rw [he]
  exact (cuspHecke n f).slash_action_eq' γ hγ

/-- The actual convergent Fourier coefficients determine a Gamma0 cusp form. -/
theorem cuspCoefficients_injective (Q : ℕ) (k : ℤ) :
    Function.Injective (cuspCoefficients : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k → ℕ → ℂ) := by
  intro f g h
  apply CuspForm.ext
  intro τ
  exact (cuspCoefficients_hasSum f τ).unique (by simpa only [h] using cuspCoefficients_hasSum g τ)

/-- At coprime positive indices, composition is the actual product-index cusp operator. -/
theorem cuspHeckeLinear_coprime_mul (Q : ℕ) [NeZero Q] (k : ℤ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    cuspHeckeLinear Q k a * cuspHeckeLinear Q k b = cuspHeckeLinear Q k (a * b) := by
  apply LinearMap.ext
  intro f
  apply cuspCoefficients_injective Q k
  funext m
  change cuspCoefficients (cuspHecke a (cuspHecke b f)) m = cuspCoefficients (cuspHecke (a * b) f) m
  rw [cuspHecke_coeff, cuspHecke_coeff, funext (cuspHecke_coeff b f)]
  exact (classicalHeckeCoefficient_coprime_comp Q k ha hb hab (cuspCoefficients f) m).symm

/-- The all-index operator agrees with the directly constructed prime cusp operator. -/
theorem cuspHeckeLinear_prime (Q : ℕ) [NeZero Q] (k : ℤ) {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) : cuspHeckeLinear Q k p = cuspHeckePrimeLinear k hp := by
  apply LinearMap.ext
  intro f
  apply cuspCoefficients_injective Q k
  funext m
  exact (cuspHecke_coeff p f m).trans (cuspHeckePrime_coeff hp f m).symm

/-- The all-index operator agrees with the genuine prime-power recurrence. -/
theorem cuspHeckeLinear_primePower (Q : ℕ) [NeZero Q] (k : ℤ) {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (r : ℕ) : cuspHeckeLinear Q k (p ^ r) = cuspHeckePrimePower k hp r := by
  apply LinearMap.ext
  intro f
  apply cuspCoefficients_injective Q k
  funext m
  exact (cuspHecke_coeff (p ^ r) f m).trans (cuspHeckePrimePower_coeff hp r f m).symm

/-- The genuine primitive form is an eigenvector of every good-index cusp endomorphism. -/
theorem primitiveCuspForm_eigenvector {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k)
    {n : ℕ} (hn : 0 < n) (hnQ : Nat.Coprime n Q) :
    cuspHeckeLinear Q k n f.toCuspForm = cuspCoefficients f.toCuspForm n • f.toCuspForm := by
  apply CuspForm.ext
  intro τ
  change cuspHecke n f.toCuspForm τ = _
  rw [cuspHecke_apply]
  exact cuspHeckeEigenform_normalized_action f.toCuspForm f.normalized f.isEigen hn hnQ τ

end
end Dubon2026
