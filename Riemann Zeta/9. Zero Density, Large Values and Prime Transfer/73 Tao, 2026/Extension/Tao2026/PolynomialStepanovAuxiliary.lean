import Tao2026.PolynomialTwistedHasse
import Tao2026.PolynomialStepanovMultiplicity
import Tao2026.PolynomialKummerIrreducibility
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# The Stepanov auxiliary polynomial and its linear constraints

An explicit coefficient space parametrizes Frobenius-spaced polynomial
terms. Normalized Hasse derivatives give low-degree linear constraints whose
vanishing forces high multiplicity on each character fiber. The construction
here keeps injectivity of the parametrization as an explicit hypothesis.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

abbrev polynomialStepanovCoefficients (K : Type*) [Field K] (e B S : ℕ) :=
  Fin e → Fin (B + 1) → degreeLT K (S + 1)

def polynomialStepanovAuxiliary
    {K : Type*} [Field K] (g : K[X]) (e B S h Q : ℕ) :
    polynomialStepanovCoefficients K e B S →ₗ[K] K[X] where
  toFun v := ∑ j, ∑ k, (v j k : K[X]) * g ^ (h * j.val) * X ^ (Q * k.val)
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

def polynomialStepanovConstraint
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (e B S h r : ℕ) (c : K) :
    polynomialStepanovCoefficients K e B S →ₗ[K] K[X] where
  toFun v := ∑ j, ∑ k,
    polynomialTwistedHasseLinear g hg (h * j.val) r (v j k) * C (c ^ j.val) * X ^ k.val
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

theorem polynomialStepanovAuxiliary_natDegree_le
    {K : Type*} [Field K] (g : K[X]) (e B S h Q : ℕ)
    (v : polynomialStepanovCoefficients K e B S) :
    (polynomialStepanovAuxiliary g e B S h Q v).natDegree ≤
      S + h * (e - 1) * g.natDegree + Q * B := by
  change (∑ j, ∑ k, (v j k : K[X]) * g ^ (h * j.val) * X ^ (Q * k.val)).natDegree ≤ _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_sum_le_of_forall_le
  intro k _
  have hv : (v j k : K[X]).natDegree ≤ S := by
    simpa only [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
      using (v j k).property
  calc
    _ ≤ ((v j k : K[X]) * g ^ (h * j.val)).natDegree + (X ^ (Q * k.val) : K[X]).natDegree :=
      natDegree_mul_le
    _ ≤ ((v j k : K[X]).natDegree + (g ^ (h * j.val)).natDegree) + Q * k.val := by
      rw [natDegree_X_pow]
      exact Nat.add_le_add_right natDegree_mul_le _
    _ ≤ _ := by
      rw [natDegree_pow]
      exact Nat.add_le_add
        (Nat.add_le_add hv (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left h (by omega))))
        (Nat.mul_le_mul_left Q (by omega))

theorem polynomialStepanovConstraint_natDegree_le
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (e B S h r : ℕ) (c : K)
    (v : polynomialStepanovCoefficients K e B S) :
    (polynomialStepanovConstraint g hg e B S h r c v).natDegree ≤ S + r * g.natDegree + B := by
  change (∑ j : Fin e, ∑ k : Fin (B + 1),
    polynomialTwistedHasse (v j k) g (h * j.val) r * C (c ^ j.val) * X ^ k.val).natDegree ≤ _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_sum_le_of_forall_le
  intro k _
  have hv : (v j k : K[X]).natDegree ≤ S := by
    simpa only [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
      using (v j k).property
  let T := polynomialTwistedHasse (v j k) g (h * j.val) r
  have hmul := natDegree_mul_le (p := T * C (c ^ j.val)) (q := (X : K[X]) ^ k.val)
  have hC := natDegree_mul_C_le T (c ^ j.val)
  have hT : T.natDegree ≤ (v j k : K[X]).natDegree + r * g.natDegree :=
    polynomialTwistedHasse_natDegree_le (v j k) g hg (h * j.val) r
  rw [natDegree_X_pow] at hmul
  change (T * C (c ^ j.val) * X ^ k.val).natDegree ≤ _
  omega

theorem polynomialStepanovConstraint_eval_eq_scaled_hasseDeriv
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (g : K[X]) (hg : g ≠ 0) (e B S h n r : ℕ) (hr : r < p ^ n) (c x : K)
    (hx : x ^ p ^ n = x) (hchar : g.eval x ^ h = c)
    (v : polynomialStepanovCoefficients K e B S) :
    (polynomialStepanovConstraint g hg e B S h r c v).eval x =
      g.eval x ^ r * (hasseDeriv r (polynomialStepanovAuxiliary g e B S h (p ^ n) v)).eval x := by
  simp only [polynomialStepanovConstraint, polynomialStepanovAuxiliary,
    LinearMap.coe_mk, AddHom.coe_mk, map_sum, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [polynomial_hasseDeriv_mul_X_pow_expChar_eval p _ n r k.val hr x hx]
  have hs := congrArg (fun P : K[X] => P.eval x)
    (polynomialTwistedHasse_spec (v j k) g hg (h * j.val) r)
  simp only [eval_mul, eval_pow] at hs
  rw [pow_mul, hchar] at hs
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  change (polynomialTwistedHasse (v j k) g (h * j.val) r).eval x * c ^ j.val * x ^ k.val = _
  linear_combination hs * x ^ k.val

abbrev polynomialStepanovConstraintSpace (K : Type*) [Field K] (g : K[X]) (B S M : ℕ) :=
  (r : Fin M) → degreeLT K (S + r.val * g.natDegree + B + 1)

def polynomialStepanovConstraints
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (e B S h M : ℕ) (c : K) :
    polynomialStepanovCoefficients K e B S →ₗ[K] polynomialStepanovConstraintSpace K g B S M :=
  LinearMap.pi fun r => (polynomialStepanovConstraint g hg e B S h r.val c).codRestrict
    (degreeLT K (S + r.val * g.natDegree + B + 1)) (fun v => by
      rw [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
      exact polynomialStepanovConstraint_natDegree_le g hg e B S h r.val c v)

theorem polynomial_degreeLT_finrank (K : Type*) [Field K] (n : ℕ) :
    Module.finrank K (degreeLT K n) = n := by
  rw [(degreeLTEquiv K n).finrank_eq, Module.finrank_pi, Fintype.card_fin]

theorem polynomialStepanovCoefficients_finrank (K : Type*) [Field K] (e B S : ℕ) :
    Module.finrank K (polynomialStepanovCoefficients K e B S) = e * (B + 1) * (S + 1) := by
  simp [polynomialStepanovCoefficients, Module.finrank_pi_fintype,
    polynomial_degreeLT_finrank, Nat.mul_assoc]

theorem polynomialStepanovConstraintSpace_finrank
    (K : Type*) [Field K] (g : K[X]) (B S M : ℕ) :
    Module.finrank K (polynomialStepanovConstraintSpace K g B S M) =
      ∑ r : Fin M, (S + r.val * g.natDegree + B + 1) := by
  simp [polynomialStepanovConstraintSpace, Module.finrank_pi_fintype, polynomial_degreeLT_finrank]

theorem polynomialStepanovAuxiliary_exists_of_injective
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (g : K[X]) (hg : g ≠ 0) (e B S h n M : ℕ) (c : K)
    (hM : M ≤ p ^ n)
    (hinj : Function.Injective (polynomialStepanovAuxiliary g e B S h (p ^ n)))
    (hdim : (∑ r : Fin M, (S + r.val * g.natDegree + B + 1)) < e * (B + 1) * (S + 1)) :
    ∃ F : K[X], F ≠ 0 ∧ F.natDegree ≤ S + h * (e - 1) * g.natDegree + p ^ n * B ∧
      ∀ x : K, x ^ p ^ n = x → g.eval x ≠ 0 → g.eval x ^ h = c →
        ∀ r < M, (hasseDeriv r F).eval x = 0 := by
  have hdim' : Module.finrank K (polynomialStepanovConstraintSpace K g B S M) <
      Module.finrank K (polynomialStepanovCoefficients K e B S) := by
    rwa [polynomialStepanovConstraintSpace_finrank, polynomialStepanovCoefficients_finrank]
  obtain ⟨v, hv, hnonzero⟩ := polynomial_exists_nonzero_auxiliary_of_finrank_lt
    (polynomialStepanovAuxiliary g e B S h (p ^ n)) hinj
    (polynomialStepanovConstraints g hg e B S h M c) hdim'
  refine ⟨polynomialStepanovAuxiliary g e B S h (p ^ n) v, hnonzero,
    polynomialStepanovAuxiliary_natDegree_le g e B S h (p ^ n) v, ?_⟩
  intro x hx hgx hchar r hr
  have hconstraint : polynomialStepanovConstraint g hg e B S h r c v = 0 := by
    have hv' := congrFun hv (⟨r, hr⟩ : Fin M)
    exact congrArg (fun P : degreeLT K (S + r * g.natDegree + B + 1) => (P : K[X])) hv'
  have hscaled := polynomialStepanovConstraint_eval_eq_scaled_hasseDeriv
    p g hg e B S h n r (hr.trans_le hM) c x hx hchar v
  rw [hconstraint, eval_zero] at hscaled
  exact (mul_eq_zero.mp hscaled.symm).resolve_left (pow_ne_zero r hgx)

end
end Tao2026
