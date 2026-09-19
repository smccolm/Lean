import Tao2026.BurgessWeilPrimeKummerNewtonAllDegreeIntegrality
import Tao2026.BurgessWeilPrimeKummerMonicPolynomialSums
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# Frobenius orbits as irreducible polynomial factors

Finite-field Frobenius cycles are exactly conjugate-root classes. Their
minimal polynomials have degree equal to the cycle length, and evaluation
of the orbit product identifies the partial norm with the signed minimal
polynomial value. The resulting polynomial weight is multiplicative on
monic polynomials and agrees with the literal orbit weight.

The signed monic-polynomial coefficient sequence has the support-degree
vanishing property required by the prospective characteristic recurrence.
The formal Euler-product coefficient identification remains separate.
-/

namespace Tao2026
open Finset Polynomial Function
open scoped BigOperators
noncomputable section

theorem primeFieldFrobeniusPerm_pow_eq_algEquiv
    (p n i : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) :
    (primeFieldFrobeniusPerm p n ^ i) x =
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (primeFieldExtension p n) ^ i) x := by
  rw [primeFieldFrobeniusPerm_pow_apply, FiniteField.Extension.frob_iterate_apply,
    AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp only [ZMod.card, Nat.card_zmod]

theorem primeFieldFrobeniusPerm_sameCycle_iff_isConjRoot
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x y : primeFieldExtension p n) :
    (primeFieldFrobeniusPerm p n).SameCycle x y ↔ IsConjRoot (ZMod p) x y := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
    rw [primeFieldFrobeniusPerm_pow_eq_algEquiv]
    exact isConjRoot_of_algEquiv x
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (primeFieldExtension p n) ^ i)
  · intro h
    obtain ⟨φ, hφ⟩ := h.symm.exists_algEquiv
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod p) (primeFieldExtension p n)).2 φ
    have hx : (primeFieldFrobeniusPerm p n ^ (i : ℕ)) x = y := by
      rw [primeFieldFrobeniusPerm_pow_eq_algEquiv]
      exact (congrArg (fun f : Gal(primeFieldExtension p n/ZMod p) => f x) hi).trans hφ
    rw [← hx]
    exact Equiv.Perm.SameCycle.rfl.pow_right

theorem finitePermutation_sameCycle_prod_eq_range
    {α M : Type*} [Fintype α] [CommMonoid M]
    (σ : Equiv.Perm α) (x : α) (f : α → M) :
    letI : DecidableRel σ.SameCycle := Classical.decRel _
    (∏ y ∈ univ.filter (σ.SameCycle x), f y) =
      ∏ i ∈ range (minimalPeriod σ x), f ((σ ^ i) x) := by
  classical
  letI : DecidableRel σ.SameCycle := Classical.decRel _
  symm
  refine prod_bij (fun i _ => (σ ^ i) x) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    simp only [mem_filter, mem_univ, true_and]
    exact Equiv.Perm.SameCycle.rfl.pow_right
  · intro i hi j hj hij
    exact iterate_injOn_Iio_minimalPeriod (mem_range.mp hi) (mem_range.mp hj) hij
  · intro y hy
    obtain ⟨i, hi⟩ := (mem_filter.mp hy).2.exists_nat_pow_eq
    refine ⟨i % minimalPeriod σ x,
      mem_range.mpr (Nat.mod_lt _
        (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x))), ?_⟩
    exact (iterate_mod_minimalPeriod_eq (n := i)).trans hi

theorem primeField_minpoly_map_eq_frobenius_product
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) :
    (minpoly (ZMod p) x).map (algebraMap (ZMod p) (primeFieldExtension p n)) =
      ∏ i ∈ range (minimalPeriod (primeFieldFrobeniusPerm p n) x),
        (X - C ((primeFieldFrobeniusPerm p n ^ i) x)) := by
  classical
  letI : Fintype (primeFieldExtension p n) := Fintype.ofFinite _
  letI : DecidableRel (primeFieldFrobeniusPerm p n).SameCycle := Classical.decRel _
  let c := ConjRootClass.mk (ZMod p) x
  have hcarrier : c.carrier.toFinset =
      univ.filter ((primeFieldFrobeniusPerm p n).SameCycle x) := by
    ext y
    simp only [Set.mem_toFinset, ConjRootClass.mem_carrier, c,
      ConjRootClass.mk_eq_mk, mem_filter, mem_univ, true_and,
      primeFieldFrobeniusPerm_sameCycle_iff_isConjRoot]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hpoly := ConjRootClass.minpoly.map_eq_prod c
  rw [hcarrier] at hpoly
  exact hpoly.trans (finitePermutation_sameCycle_prod_eq_range
    (primeFieldFrobeniusPerm p n) x (fun y => X - C y))

theorem primeField_minpoly_natDegree_eq_frobenius_period
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) :
    (minpoly (ZMod p) x).natDegree = minimalPeriod (primeFieldFrobeniusPerm p n) x := by
  have h := congrArg Polynomial.natDegree (primeField_minpoly_map_eq_frobenius_product p n x)
  simpa using h

theorem primeFieldFrobeniusNorm_eq_minpoly_eval
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) (r : ZMod p) :
    primeFieldFrobeniusNorm p n (minimalPeriod (primeFieldFrobeniusPerm p n) x)
      (x - algebraMap (ZMod p) (primeFieldExtension p n) r) =
      (-1 : ZMod p) ^ (minimalPeriod (primeFieldFrobeniusPerm p n) x) *
        (minpoly (ZMod p) x).eval r := by
  let d := minimalPeriod (primeFieldFrobeniusPerm p n) x
  let ι := algebraMap (ZMod p) (primeFieldExtension p n)
  have hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x := by
    rw [← primeFieldFrobeniusPerm_pow_apply]
    exact iterate_minimalPeriod
  have hxr : (FiniteField.Extension.frob (ZMod p) p n ^ d) (x - ι r) = x - ι r := by
    rw [primeFieldFrob_pow_sub_base, hx]
  have heval : ι ((minpoly (ZMod p) x).eval r) =
      ∏ i ∈ range d, (ι r - (primeFieldFrobeniusPerm p n ^ i) x) := by
    have h := congrArg (Polynomial.eval (ι r))
      (primeField_minpoly_map_eq_frobenius_product p n x)
    simpa only [ι, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h
  apply ι.injective
  rw [primeFieldFrobeniusNorm_spec p n d _ hxr, map_mul, map_pow, map_neg, map_one, heval]
  unfold primeFieldFrobeniusProduct
  calc
    _ = ∏ i ∈ range d, -(ι r - (primeFieldFrobeniusPerm p n ^ i) x) := by
      apply prod_congr rfl
      intro i _
      rw [primeFieldFrob_pow_sub_base, primeFieldFrobeniusPerm_pow_apply]
      ring
    _ = _ := by rw [Finset.prod_neg, card_range]

def primeRootMultisetPolynomialWeight
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (P : (ZMod p)[X]) : ℂ :=
  ∏ r ∈ R.toFinset, (χ ^ R.count r) ((-1 : ZMod p) ^ P.natDegree * P.eval r)

theorem primeRootMultisetPolynomialWeight_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    primeRootMultisetPolynomialWeight p χ R 1 = 1 := by
  simp [primeRootMultisetPolynomialWeight]

theorem primeRootMultisetPolynomialWeight_mul
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (P Q : (ZMod p)[X]) (hP : P.Monic) (hQ : Q.Monic) :
    primeRootMultisetPolynomialWeight p χ R (P * Q) =
      primeRootMultisetPolynomialWeight p χ R P *
        primeRootMultisetPolynomialWeight p χ R Q := by
  classical
  unfold primeRootMultisetPolynomialWeight
  rw [← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro r _
  rw [natDegree_mul hP.ne_zero hQ.ne_zero, pow_add, eval_mul]
  rw [show (-1 : ZMod p) ^ P.natDegree * (-1) ^ Q.natDegree * (P.eval r * Q.eval r) =
      ((-1) ^ P.natDegree * P.eval r) * ((-1) ^ Q.natDegree * Q.eval r) by ring]
  exact map_mul _ _ _

theorem primeRootMultisetPolynomialWeight_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (P : (ZMod p)[X]) :
    IsIntegral ℤ (primeRootMultisetPolynomialWeight p χ R P) :=
  IsIntegral.prod _ (fun _ _ => isIntegral_finiteFieldMulChar_apply _ _)

theorem primeFieldFrobeniusWeight_eq_minpoly_weight
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (x : primeFieldExtension p n) :
    primeFieldFrobeniusWeight p n (minimalPeriod (primeFieldFrobeniusPerm p n) x) χ R x =
      primeRootMultisetPolynomialWeight p χ R (minpoly (ZMod p) x) := by
  classical
  unfold primeFieldFrobeniusWeight primeRootMultisetPolynomialWeight
  apply prod_congr rfl
  intro r _
  rw [primeFieldFrobeniusNorm_eq_minpoly_eval,
    primeField_minpoly_natDegree_eq_frobenius_period]

def primeFieldOrbitMinpoly
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (o : finitePermutationOrbits (primeFieldFrobeniusPerm p n)) : (ZMod p)[X] :=
  minpoly (ZMod p) o.out

theorem primeFieldOrbitMinpoly_injective
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n] :
    Function.Injective (primeFieldOrbitMinpoly p n) := by
  intro o o' h
  have hcycle := (primeFieldFrobeniusPerm_sameCycle_iff_isConjRoot p n o.out o'.out).2 h
  have hq : Quotient.mk (Equiv.Perm.SameCycle.setoid (primeFieldFrobeniusPerm p n)) o.out =
      Quotient.mk (Equiv.Perm.SameCycle.setoid (primeFieldFrobeniusPerm p n)) o'.out :=
    Quotient.sound hcycle
  simpa only [Quotient.out_eq] using hq

theorem primeFieldOrbitMinpoly_monic
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (o : finitePermutationOrbits (primeFieldFrobeniusPerm p n)) :
    (primeFieldOrbitMinpoly p n o).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral o.out)

theorem primeFieldOrbitMinpoly_irreducible
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (o : finitePermutationOrbits (primeFieldFrobeniusPerm p n)) :
    Irreducible (primeFieldOrbitMinpoly p n o) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral o.out)

theorem primeFieldOrbitMinpoly_natDegree
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (o : finitePermutationOrbits (primeFieldFrobeniusPerm p n)) :
    (primeFieldOrbitMinpoly p n o).natDegree =
      finitePermutationOrbitLength (primeFieldFrobeniusPerm p n) o :=
  primeField_minpoly_natDegree_eq_frobenius_period p n o.out

theorem primeRootMultisetPolynomialWeight_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (P : (ZMod p)[X]) (hP : P.Monic) (k : ℕ) :
    primeRootMultisetPolynomialWeight p χ R (P ^ k) =
      primeRootMultisetPolynomialWeight p χ R P ^ k := by
  induction k with
  | zero => simp [primeRootMultisetPolynomialWeight_one]
  | succ k ih =>
      rw [pow_succ, primeRootMultisetPolynomialWeight_mul p χ R _ _ (hP.pow k) hP,
        ih, pow_succ]

def primeRootMultisetMonicLseriesCoefficient
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (n : ℕ) : ℂ :=
  letI : Fintype (degreeLT (ZMod p) n) :=
    Fintype.ofEquiv (Fin n → ZMod p) (degreeLTEquiv (ZMod p) n).symm.toEquiv
  ∑ f : degreeLT (ZMod p) n,
    primeRootMultisetPolynomialWeight p χ R (X ^ n + (f : (ZMod p)[X]))

theorem primeRootMultisetMonicLseriesCoefficient_eq_twist_mul
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (n : ℕ) :
    primeRootMultisetMonicLseriesCoefficient p χ R n =
      (∏ r ∈ R.toFinset, (χ ^ R.count r) ((-1 : ZMod p) ^ n)) *
        primeRootMultisetMonicPolynomialCorrelation p χ R n := by
  classical
  letI : Fintype (degreeLT (ZMod p) n) :=
    Fintype.ofEquiv (Fin n → ZMod p) (degreeLTEquiv (ZMod p) n).symm.toEquiv
  unfold primeRootMultisetMonicLseriesCoefficient primeRootMultisetMonicPolynomialCorrelation
    finiteFieldMonicPolynomialCorrelation
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro f _
  have hdeg : (X ^ n + (f : (ZMod p)[X])).natDegree = n :=
    ((monicEquivDegreeLT n).symm f).property.2
  simp only [primeRootMultisetPolynomialWeight, hdeg, map_mul, Finset.prod_mul_distrib]

theorem primeRootMultisetMonicLseriesCoefficient_eq_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (n : ℕ)
    (hn : R.toFinset.card ≤ n) (r₀ : ZMod p) (hr₀ : r₀ ∈ R)
    (hcount : R.count r₀ < orderOf χ) :
    primeRootMultisetMonicLseriesCoefficient p χ R n = 0 := by
  rw [primeRootMultisetMonicLseriesCoefficient_eq_twist_mul,
    primeRootMultisetMonicPolynomialCorrelation_eq_zero p χ R n hn r₀ hr₀ hcount,
    mul_zero]

theorem primeField_exists_aeval_zero_of_irreducible_degree_dvd
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (P : (ZMod p)[X]) (hP : P.Monic) (hirr : Irreducible P)
    (hdegree : P.natDegree ∣ n) :
    ∃ x : primeFieldExtension p n, aeval x P = 0 := by
  classical
  letI : Fact (Irreducible P) := ⟨hirr⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := hP.finite_adjoinRoot
  letI : Fintype (AdjoinRoot P) := Fintype.ofEquiv
    (Fin P.natDegree → ZMod p) (AdjoinRoot.powerBasis' hP).basis.equivFun.symm.toEquiv
  have hdim : Module.finrank (ZMod p) (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis' hP).finrank
  obtain ⟨φ⟩ : Nonempty (AdjoinRoot P →ₐ[ZMod p] primeFieldExtension p n) :=
    FiniteField.nonempty_algHom_of_finrank_dvd
      (by simpa only [hdim, primeFieldExtension_finrank] using hdegree)
  exact ⟨φ (AdjoinRoot.root P), AdjoinRoot.aeval_algHom_eq_zero P φ⟩

theorem primeFieldOrbitMinpoly_mk
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) :
    primeFieldOrbitMinpoly p n
      (Quotient.mk (Equiv.Perm.SameCycle.setoid (primeFieldFrobeniusPerm p n)) x) =
        minpoly (ZMod p) x := by
  apply (primeFieldFrobeniusPerm_sameCycle_iff_isConjRoot p n _ x).1
  exact finitePermutation_sameCycle_out (primeFieldFrobeniusPerm p n) _ x rfl

theorem primeFieldOrbitMinpoly_exists_of_irreducible_degree_dvd
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (P : (ZMod p)[X]) (hP : P.Monic) (hirr : Irreducible P)
    (hdegree : P.natDegree ∣ n) :
    ∃ o : finitePermutationOrbits (primeFieldFrobeniusPerm p n),
      primeFieldOrbitMinpoly p n o = P := by
  obtain ⟨x, hx⟩ := primeField_exists_aeval_zero_of_irreducible_degree_dvd p n P hP hirr hdegree
  refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid (primeFieldFrobeniusPerm p n)) x, ?_⟩
  rw [primeFieldOrbitMinpoly_mk]
  exact (minpoly.eq_of_irreducible_of_monic hirr hx hP).symm

end
end Tao2026
