import Tao2026.BurgessWeilPrimeKummerHasseDavenportMonic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Trace.Basic

/-!
# Multiplicative monic weights for Hasse--Davenport

This file supplies the unique-factorization layer of the classical
Hasse--Davenport generating-function proof.  The constant/subleading
coefficient weight is extended to every polynomial, proved multiplicative on
monic polynomials, and decomposed exactly over normalized monic irreducible
factors with preservation of total degree.
-/

namespace Tao2026

open scoped BigOperators

noncomputable section

/-- The global Hasse--Davenport polynomial weight.  On a monic polynomial it
is the product of the multiplicative character of the roots and the additive
character of their sum. -/
def hasseDavenportMonicWeight
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (p : Polynomial K) : ℂ :=
  χ ((-1 : K) ^ p.natDegree * p.coeff 0) * ψ (-p.nextCoeff)

@[simp]
theorem hasseDavenportMonicWeight_one
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    hasseDavenportMonicWeight χ ψ 1 = 1 := by
  have hnext : (1 : Polynomial K).nextCoeff = 0 := by
    rw [← Polynomial.C_1]
    exact Polynomial.nextCoeff_C_eq_zero 1
  rw [hasseDavenportMonicWeight, hnext]
  simp [AddChar.map_zero_eq_one]

/-- The global weight is multiplicative on monic polynomials. -/
theorem hasseDavenportMonicWeight_mul
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    {p q : Polynomial K} (hp : p.Monic) (hq : q.Monic) :
    hasseDavenportMonicWeight χ ψ (p * q) =
      hasseDavenportMonicWeight χ ψ p *
        hasseDavenportMonicWeight χ ψ q := by
  rw [hasseDavenportMonicWeight, hasseDavenportMonicWeight,
    hasseDavenportMonicWeight]
  rw [Polynomial.natDegree_mul hp.ne_zero hq.ne_zero]
  rw [hp.nextCoeff_mul hq]
  rw [show (p * q).coeff 0 = p.coeff 0 * q.coeff 0 by simp]
  rw [show -(p.nextCoeff + q.nextCoeff) =
      -p.nextCoeff + -q.nextCoeff by ring]
  simp only [pow_add, map_mul, AddChar.map_add_eq_mul]
  ring

/-- The weight of a power of a monic polynomial is the corresponding power
of its weight. -/
@[simp]
theorem hasseDavenportMonicWeight_pow
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    {p : Polynomial K} (hp : p.Monic) (n : ℕ) :
    hasseDavenportMonicWeight χ ψ (p ^ n) =
      hasseDavenportMonicWeight χ ψ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, hasseDavenportMonicWeight_mul χ ψ (hp.pow n) hp,
        ih, pow_succ]

/-- The global weight agrees with the fixed-degree polynomial weight used in
the monic coefficient identities. -/
theorem hasseDavenportMonicWeight_eq_fixedDegree
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (n : ℕ) (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n + 1}) :
    hasseDavenportMonicWeight χ ψ p.1 =
      hasseDavenportMonicPolynomialWeight χ ψ n p := by
  have hpos : 0 < p.1.natDegree := by rw [p.2.2]; omega
  rw [hasseDavenportMonicWeight, hasseDavenportMonicPolynomialWeight]
  rw [Polynomial.nextCoeff_of_natDegree_pos hpos, p.2.2]
  simp

/-- A linear monic factor has precisely the character weight of its root. -/
@[simp]
theorem hasseDavenportMonicWeight_X_sub_C
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (x : K) :
    hasseDavenportMonicWeight χ ψ
        (Polynomial.X - Polynomial.C x) = χ x * ψ x := by
  simp [hasseDavenportMonicWeight, Polynomial.nextCoeff_X_sub_C]

/-- Multiplicativity over an arbitrary multiset of monic polynomials. -/
theorem hasseDavenportMonicWeight_multiset_prod
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (s : Multiset (Polynomial K)) (hs : ∀ p ∈ s, p.Monic) :
    hasseDavenportMonicWeight χ ψ s.prod =
      (s.map (hasseDavenportMonicWeight χ ψ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
      have hp : p.Monic := hs p (by simp)
      have hs' : ∀ q ∈ s, q.Monic := by
        intro q hq
        exact hs q (Multiset.mem_cons_of_mem hq)
      have hprod : s.prod.Monic := by
        simpa using
          Polynomial.monic_multiset_prod_of_monic s (fun q => q) hs'
      rw [Multiset.prod_cons,
        hasseDavenportMonicWeight_mul χ ψ hp hprod,
        Multiset.map_cons, Multiset.prod_cons, ih hs']

/-- The weight of a product of linear factors is the product of the root
character weights. -/
theorem hasseDavenportMonicWeight_multiset_prod_X_sub_C
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (s : Multiset K) :
    hasseDavenportMonicWeight χ ψ
        (s.map (fun x => Polynomial.X - Polynomial.C x)).prod =
      (s.map (fun x => χ x * ψ x)).prod := by
  rw [hasseDavenportMonicWeight_multiset_prod]
  · simp
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
    exact Polynomial.monic_X_sub_C x

open UniqueFactorizationMonoid in
/-- Every normalized factor of a monic polynomial is a positive-degree monic
irreducible polynomial. -/
theorem normalizedFactor_monic_irreducible_natDegree_pos
    {K : Type*} [Field K] [DecidableEq K]
    {p q : Polynomial K} (hp : p.Monic)
    (hq : q ∈ normalizedFactors p) :
    Irreducible q ∧ q.Monic ∧ 0 < q.natDegree := by
  rcases (Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hq with
    ⟨hirr, hmonic, hdvd⟩
  exact ⟨hirr, hmonic,
    hmonic.natDegree_pos_of_not_isUnit hirr.not_isUnit⟩

open UniqueFactorizationMonoid in
/-- The weight of a monic polynomial is exactly the product of the weights of
its normalized irreducible factors, with multiplicity. -/
theorem hasseDavenportMonicWeight_eq_prod_normalizedFactors
    {K : Type*} [Field K] [DecidableEq K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    {p : Polynomial K} (hp : p.Monic) :
    hasseDavenportMonicWeight χ ψ p =
      ((normalizedFactors p).map
        (hasseDavenportMonicWeight χ ψ)).prod := by
  classical
  have hprod : (normalizedFactors p).prod = p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors p
    simpa [hp.leadingCoeff] using h
  calc
    hasseDavenportMonicWeight χ ψ p =
        hasseDavenportMonicWeight χ ψ
          (normalizedFactors p).prod := by rw [hprod]
    _ = ((normalizedFactors p).map
        (hasseDavenportMonicWeight χ ψ)).prod := by
      apply hasseDavenportMonicWeight_multiset_prod
      intro q hq
      exact ((Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hq).2.1

open UniqueFactorizationMonoid in
/-- The degrees of the normalized irreducible factors of a monic polynomial
sum to its degree. -/
theorem sum_natDegree_normalizedFactors_of_monic
    {K : Type*} [Field K] [DecidableEq K]
    {p : Polynomial K} (hp : p.Monic) :
    ((normalizedFactors p).map Polynomial.natDegree).sum = p.natDegree := by
  have hmonic : ∀ q ∈ normalizedFactors p, q.Monic := by
    intro q hq
    exact (normalizedFactor_monic_irreducible_natDegree_pos hp hq).2.1
  have hprod : (normalizedFactors p).prod = p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors p
    simpa [hp.leadingCoeff] using h
  calc
    ((normalizedFactors p).map Polynomial.natDegree).sum =
        (normalizedFactors p).prod.natDegree := by
      symm
      exact Polynomial.natDegree_multiset_prod_of_monic _ hmonic
    _ = p.natDegree := by rw [hprod]

/-- The norm/trace character weight of one extension element is the weight of
its minimal polynomial raised to the relative multiplicity of its closed
point in the extension. -/
theorem normTraceCharacterWeight_eq_minpolyWeight_pow
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (x : L) :
    χ (Algebra.norm K x) * ψ (Algebra.trace K L x) =
      hasseDavenportMonicWeight χ ψ (minpoly K x) ^
        Module.finrank (IntermediateField.adjoin K {x}) L := by
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  have hnormGen :
      Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
        (-1 : K) ^ (minpoly K x).natDegree *
          (minpoly K x).coeff 0 := by
    rw [← IntermediateField.adjoin.powerBasis_gen hx]
    simpa [IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen K x] using
      (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hx))
  rw [Algebra.norm_eq_norm_adjoin K x, hnormGen, map_pow]
  rw [trace_eq_finrank_mul_minpoly_nextCoeff K x]
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [hasseDavenportMonicWeight]
  ring

/-- The lifted Gauss sum is exactly the sum of minimal-polynomial weights,
with each weight raised to its closed-point multiplicity. -/
theorem gaussSum_normTraceLift_eq_sum_minpolyWeight_pow
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    gaussSum (finiteFieldNormLiftMulChar K L χ)
        (finiteFieldTraceLiftAddChar K L ψ) =
      ∑ x : L, hasseDavenportMonicWeight χ ψ (minpoly K x) ^
        Module.finrank (IntermediateField.adjoin K {x}) L := by
  apply Finset.sum_congr rfl
  intro x hx
  exact normTraceCharacterWeight_eq_minpolyWeight_pow K L χ ψ x

end

end Tao2026
