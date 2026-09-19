import Tao2026.BurgessWeilPrimeKummerNewtonAllDegreeIntegrality
import Mathlib.LinearAlgebra.Lagrange

/-!
# Monic polynomial character sums and the conductor-degree cutoff

Translation by a Lagrange interpolation polynomial changes one evaluation
coordinate freely while fixing all other support evaluations. Summing over
that translation parameter and using character orthogonality proves that
the monic-polynomial character sum vanishes in every degree at least the
support size, provided one local character is nontrivial.

This is the polynomial cancellation input to the Kummer recurrence route.
Its identification with the literal Newton coefficients is a separate task.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem finiteAffineMulCharSum_eq_zero
    {K V ι : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    (S : Finset ι) (ψ : ι → MulChar K ℂ)
    (b : ι → K) (E : ι → V →ₗ[K] K)
    (r₀ : ι) (hr₀ : r₀ ∈ S) (hψ : ψ r₀ ≠ 1)
    (H : V) (hH₀ : E r₀ H = 1)
    (hH : ∀ r ∈ S, r ≠ r₀ → E r H = 0) :
    (∑ v : V, ∏ r ∈ S, ψ r (b r + E r v)) = 0 := by
  classical
  let w (v : V) : ℂ := ∏ r ∈ S, ψ r (b r + E r v)
  have htranslate (t : K) : (∑ v : V, w (v + t • H)) = ∑ v : V, w v :=
    Fintype.sum_equiv (Equiv.addRight (t • H)) _ _ (fun _ => rfl)
  have hterm (v : V) (t : K) :
      w (v + t • H) = ψ r₀ (b r₀ + E r₀ v + t) *
        ∏ r ∈ S.erase r₀, ψ r (b r + E r v) := by
    dsimp [w]
    rw [← Finset.mul_prod_erase S _ hr₀]
    congr 1
    · simp [map_add, map_smul, hH₀, add_assoc]
    · apply prod_congr rfl
      intro r hr
      simp [map_add, map_smul, hH r (mem_of_mem_erase hr) (mem_erase.mp hr).1]
  have hinner (v : V) : (∑ t : K, w (v + t • H)) = 0 := by
    simp_rw [hterm v]
    rw [← Finset.sum_mul]
    have hz : (∑ t : K, ψ r₀ (b r₀ + E r₀ v + t)) = 0 := by
      rw [Fintype.sum_equiv (Equiv.addLeft (b r₀ + E r₀ v))
        (fun t => ψ r₀ (b r₀ + E r₀ v + t)) (fun t => ψ r₀ t) (fun _ => rfl)]
      exact MulChar.sum_eq_zero_of_ne_one hψ
    rw [hz, zero_mul]
  have hdouble : (Fintype.card K : ℂ) * (∑ v : V, w v) = 0 := by
    calc
      _ = ∑ t : K, ∑ v : V, w (v + t • H) := by
        simp_rw [htranslate]
        simp
      _ = ∑ v : V, ∑ t : K, w (v + t • H) := Finset.sum_comm
      _ = 0 := by simp_rw [hinner]; simp
  exact (mul_eq_zero.mp hdouble).resolve_left
    (by exact_mod_cast Fintype.card_ne_zero (α := K))

def finiteFieldMonicPolynomialCorrelation
    (K : Type*) [Field K] [Fintype K]
    (S : Finset K) (ψ : K → MulChar K ℂ) (n : ℕ) : ℂ :=
  letI : Fintype (degreeLT K n) :=
    Fintype.ofEquiv (Fin n → K) (degreeLTEquiv K n).symm.toEquiv
  ∑ f : degreeLT K n, ∏ r ∈ S, ψ r ((X ^ n + (f : K[X])).eval r)

theorem finiteFieldMonicPolynomialCorrelation_eq_zero
    (K : Type*) [Field K] [Fintype K]
    (S : Finset K) (ψ : K → MulChar K ℂ) (n : ℕ)
    (hn : S.card ≤ n) (r₀ : K) (hr₀ : r₀ ∈ S) (hψ : ψ r₀ ≠ 1) :
    finiteFieldMonicPolynomialCorrelation K S ψ n = 0 := by
  classical
  letI : Fintype (degreeLT K n) :=
    Fintype.ofEquiv (Fin n → K) (degreeLTEquiv K n).symm.toEquiv
  let H : degreeLT K n := ⟨Lagrange.interpolate S id (fun r => if r = r₀ then 1 else 0),
    degreeLT_mono hn (mem_degreeLT.mpr
      (Lagrange.degree_interpolate_lt _ (fun _ _ _ _ h => h)))⟩
  let E (r : K) : degreeLT K n →ₗ[K] K := (Polynomial.leval r).comp (degreeLT K n).subtype
  have hE (r : K) (f : degreeLT K n) : E r f = (f : K[X]).eval r := rfl
  have hH (r : K) (hr : r ∈ S) : E r H = if r = r₀ then 1 else 0 :=
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => h) hr
  have h := finiteAffineMulCharSum_eq_zero S ψ (fun r => r ^ n) E
    r₀ hr₀ hψ H (by simpa using hH r₀ hr₀)
    (fun r hr hne => by simpa [hne] using hH r hr)
  simpa only [finiteFieldMonicPolynomialCorrelation, eval_add, eval_pow,
    eval_X, hE] using h

theorem finiteFieldMonicPolynomialCorrelation_eq_monic_sum
    (K : Type*) [Field K] [Fintype K]
    (S : Finset K) (ψ : K → MulChar K ℂ) (n : ℕ) :
    letI : Fintype (degreeLT K n) :=
      Fintype.ofEquiv (Fin n → K) (degreeLTEquiv K n).symm.toEquiv
    letI : Fintype {f : K[X] // f.Monic ∧ f.natDegree = n} :=
      Fintype.ofEquiv (degreeLT K n) (monicEquivDegreeLT n).symm
    finiteFieldMonicPolynomialCorrelation K S ψ n =
      ∑ f : {f : K[X] // f.Monic ∧ f.natDegree = n}, ∏ r ∈ S, ψ r (f.val.eval r) := by
  classical
  letI : Fintype (degreeLT K n) :=
    Fintype.ofEquiv (Fin n → K) (degreeLTEquiv K n).symm.toEquiv
  letI : Fintype {f : K[X] // f.Monic ∧ f.natDegree = n} :=
    Fintype.ofEquiv (degreeLT K n) (monicEquivDegreeLT n).symm
  exact Fintype.sum_equiv (monicEquivDegreeLT n).symm _ _ (fun _ => rfl)

def primeRootMultisetMonicPolynomialCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (n : ℕ) : ℂ :=
  finiteFieldMonicPolynomialCorrelation (ZMod p) R.toFinset (fun r => χ ^ R.count r) n

theorem primeRootMultisetMonicPolynomialCorrelation_eq_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (n : ℕ)
    (hn : R.toFinset.card ≤ n) (r₀ : ZMod p) (hr₀ : r₀ ∈ R)
    (hcount : R.count r₀ < orderOf χ) :
    primeRootMultisetMonicPolynomialCorrelation p χ R n = 0 := by
  apply finiteFieldMonicPolynomialCorrelation_eq_zero (ZMod p) R.toFinset
    (fun r => χ ^ R.count r) n hn r₀ (Multiset.mem_toFinset.mpr hr₀)
  intro h
  have hdiv : orderOf χ ∣ R.count r₀ := orderOf_dvd_of_pow_eq_one h
  have hpos : 0 < R.count r₀ := Multiset.count_pos.mpr hr₀
  exact (Nat.not_le_of_gt hcount) (Nat.le_of_dvd hpos hdiv)

end
end Tao2026
