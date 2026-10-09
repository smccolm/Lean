import Dubon2026.PrimitiveStrongMultiplicityOne
import Dubon2026.PrimitiveFullCoefficients

/-! # A primitive form's genuine good-prime eigenvalues already determine its entire original-level cusp line -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The proved actual operator and primitive coefficient recurrences propagate a genuine shared prime eigenvalue through every prime power. -/
theorem primitiveCuspForm_shared_primePower_eigen {N p : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hp : p.Prime) (hg : cuspHeckeLinear N k p g = cuspCoefficients f.toCuspForm p • g) (r : ℕ) :
    cuspHeckeLinear N k (p ^ r) g = cuspCoefficients f.toCuspForm (p ^ r) • g := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  induction r using Nat.twoStepInduction with
  | zero => simp only [pow_zero, cuspHeckeLinear_one, Module.End.one_apply, f.normalized, one_smul]
  | one => simpa only [pow_one] using hg
  | more r ih0 ih1 =>
    rw [cuspHeckeLinear_primePower_recurrence N k hp]
    change cuspHeckeLinear N k p (cuspHeckeLinear N k (p ^ (r + 1)) g) -
      heckeDivisorWeight N k p • cuspHeckeLinear N k (p ^ r) g = _
    rw [ih1, map_smul, hg, ih0, smul_smul, smul_smul, ← sub_smul,
      primitiveCuspForm_primePower_recurrence f hp r]
    congr 1
    ring

/-- The genuine Hecke multiplication law propagates the original good-prime eigensystem to every actual good positive index. -/
theorem primitiveCuspForm_good_prime_eigen_all {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : ∀ p, p.Prime → p.Coprime N →
      cuspHeckeLinear N k p g = cuspCoefficients f.toCuspForm p • g)
    (n : ℕ) (hn : n.Coprime N) :
    cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp only [cuspHeckeLinear_zero, LinearMap.zero_apply, cuspCoefficients_zero, zero_smul]
  | prime_pow p r hp =>
    cases r with
    | zero => simp only [pow_zero, cuspHeckeLinear_one, Module.End.one_apply, f.normalized, one_smul]
    | succ r =>
      exact primitiveCuspForm_shared_primePower_eigen f g hp
        (hg p hp (hn.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero r)))) (r + 1)
  | coprime a b ha hb hab iha ihb =>
    rw [← cuspHeckeLinear_coprime_mul N k (by omega) (by omega) hab]
    change cuspHeckeLinear N k a (cuspHeckeLinear N k b g) = _
    rw [ihb (Nat.coprime_mul_iff_left.mp hn).2, map_smul,
      iha (Nat.coprime_mul_iff_left.mp hn).1, smul_smul, primitiveCuspForm_coefficient_mul_all f a b hab]
    congr 1
    exact mul_comm _ _

/-- Every original-level cusp vector with the genuine good-prime eigenvalues of a primitive form is its first-coefficient multiple. -/
theorem primitiveCuspForm_good_prime_eigensystem_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : ∀ p, p.Prime → p.Coprime N →
      cuspHeckeLinear N k p g = cuspCoefficients f.toCuspForm p • g) :
    g = cuspCoefficients g 1 • f.toCuspForm :=
  primitiveCuspForm_good_eigensystem_scalar f g
    (fun n _ hn => primitiveCuspForm_good_prime_eigen_all f g hg n hn)

end
end Dubon2026
