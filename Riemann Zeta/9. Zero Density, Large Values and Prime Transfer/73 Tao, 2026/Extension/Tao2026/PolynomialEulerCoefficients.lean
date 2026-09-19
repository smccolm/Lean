import Tao2026.BurgessWeilPrimeKummerOrbitPolynomials
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Coefficients of finite polynomial Euler products

For an injective family of monic irreducible polynomials covering the
factors of every polynomial in the requested degree, unique factorization
identifies the Euler-product coefficient with the weighted monic-polynomial
sum. The proof gives an explicit bijection from divisible degree allocations
to monic polynomials, retaining all factor multiplicities.
-/

namespace Tao2026
open Finset Polynomial UniqueFactorizationMonoid
open scoped BigOperators
noncomputable section

theorem monicIrreducibleFamily_count_normalizedFactors_prod
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (hirr : ∀ i, Irreducible (P i))
    (hinj : Function.Injective P) (e : ι → ℕ) (j : ι) (s : Finset ι) :
    (normalizedFactors (∏ i ∈ s, P i ^ e i)).count (P j) = if j ∈ s then e j else 0 := by
  have hpow (i : ι) : normalizedFactors (P i ^ e i) = Multiset.replicate (e i) (P i) := by
    simpa only [(hmon i).normalize_eq_self] using (hirr i).normalizedFactors_pow (e i)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, normalizedFactors_mul
        (pow_ne_zero _ (hmon a).ne_zero)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hmon i).ne_zero)),
        Multiset.count_add, hpow, ih]
      by_cases hja : j = a
      · subst j
        simp [ha]
      · rw [Multiset.count_replicate]
        simp [hja, Ne.symm (hinj.ne hja)]

theorem monicIrreducibleFamily_count_normalizedFactors
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (hirr : ∀ i, Irreducible (P i))
    (hinj : Function.Injective P) (e : ι → ℕ) (j : ι) :
    (normalizedFactors (∏ i, P i ^ e i)).count (P j) = e j := by
  simpa using monicIrreducibleFamily_count_normalizedFactors_prod P hmon hirr hinj e j univ

theorem monicIrreducibleFamily_prod_count
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (P : ι → K[X]) (hinj : Function.Injective P)
    (Q : K[X]) (hQ : Q.Monic)
    (hcover : ∀ f ∈ normalizedFactors Q, ∃ i, P i = f) :
    (∏ i, P i ^ (normalizedFactors Q).count (P i)) = Q := by
  have hsubset : (normalizedFactors Q).toFinset ⊆ univ.image P := by
    intro f hf
    obtain ⟨i, rfl⟩ := hcover f (Multiset.mem_toFinset.mp hf)
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  calc
    _ = ∏ f ∈ univ.image P, f ^ (normalizedFactors Q).count f := by
      rw [prod_image]
      exact fun _ _ _ _ h => hinj h
    _ = (normalizedFactors Q).prod :=
      (prod_multiset_count_of_subset (normalizedFactors Q) _ hsubset).symm
    _ = Q := by rw [prod_normalizedFactors_eq hQ.ne_zero, hQ.normalize_eq_self]

def polynomialFactorDegreeAllocations
    {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → K[X]) (m : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (finsuppAntidiag univ m).filter (fun a => ∀ i, (P i).natDegree ∣ a i)

def polynomialFactorAllocationPolynomial
    {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → K[X]) (a : ι →₀ ℕ) : K[X] :=
  ∏ i, P i ^ (a i / (P i).natDegree)

theorem polynomialFactorAllocationPolynomial_monic
    {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (a : ι →₀ ℕ) :
    (polynomialFactorAllocationPolynomial P a).Monic :=
  monic_prod_of_monic _ _ (fun i _ => (hmon i).pow _)

theorem polynomialFactorAllocationPolynomial_natDegree
    {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (m : ℕ)
    (a : ι →₀ ℕ) (ha : a ∈ polynomialFactorDegreeAllocations P m) :
    (polynomialFactorAllocationPolynomial P a).natDegree = m := by
  classical
  have ha' := mem_filter.mp ha
  have hsum := (mem_finsuppAntidiag.mp ha'.1).1
  unfold polynomialFactorAllocationPolynomial
  rw [natDegree_prod_of_monic _ _ (fun i _ => (hmon i).pow _)]
  simp only [natDegree_pow]
  calc
    _ = ∑ i, a i := by
      apply sum_congr rfl
      intro i _
      exact Nat.div_mul_cancel (ha'.2 i)
    _ = m := hsum

theorem polynomialFactorAllocationPolynomial_injOn
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (hirr : ∀ i, Irreducible (P i))
    (hinj : Function.Injective P) (m : ℕ) :
    Set.InjOn (polynomialFactorAllocationPolynomial P)
      (polynomialFactorDegreeAllocations P m) := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  apply Finsupp.ext
  intro i
  have hcount := congrArg (fun Q : K[X] => (normalizedFactors Q).count (P i)) hab
  simp only [polynomialFactorAllocationPolynomial,
    monicIrreducibleFamily_count_normalizedFactors P hmon hirr hinj] at hcount
  calc
    a i = (P i).natDegree * (a i / (P i).natDegree) := (Nat.mul_div_cancel' (ha' i)).symm
    _ = (P i).natDegree * (b i / (P i).natDegree) := by rw [hcount]
    _ = b i := Nat.mul_div_cancel' (hb' i)

theorem polynomialFactorAllocationPolynomial_surjective
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (hirr : ∀ i, Irreducible (P i))
    (hinj : Function.Injective P) (m : ℕ) (Q : K[X]) (hQ : Q.Monic)
    (hdeg : Q.natDegree = m) (hcover : ∀ f ∈ normalizedFactors Q, ∃ i, P i = f) :
    ∃ a ∈ polynomialFactorDegreeAllocations P m, polynomialFactorAllocationPolynomial P a = Q := by
  classical
  letI : DecidableEq ι := Classical.decEq _
  let e (i : ι) := (normalizedFactors Q).count (P i)
  let a : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (P i).natDegree * e i)
  have ha (i : ι) : a i = (P i).natDegree * e i := rfl
  have hpos (i : ι) : 0 < (P i).natDegree := (hirr i).natDegree_pos
  have hprod : (∏ i, P i ^ e i) = Q := monicIrreducibleFamily_prod_count P hinj Q hQ hcover
  have hsum : ∑ i, (P i).natDegree * e i = m := by
    have h := congrArg Polynomial.natDegree hprod
    rw [natDegree_prod_of_monic _ _ (fun i _ => (hmon i).pow _), hdeg] at h
    simpa only [natDegree_pow, Nat.mul_comm] using h
  refine ⟨a, ?_, ?_⟩
  · apply mem_filter.mpr
    refine ⟨mem_finsuppAntidiag.mpr ⟨?_, subset_univ _⟩, ?_⟩
    · simpa only [ha] using hsum
    · intro i
      exact ⟨e i, ha i⟩
  · unfold polynomialFactorAllocationPolynomial
    simpa only [ha, Nat.mul_div_cancel_left _ (hpos _)] using hprod

theorem monicIrreducibleFamily_covers_normalizedFactors
    {K ι : Type*} [Field K] [DecidableEq K]
    (P : ι → K[X]) (m : ℕ)
    (hcover : ∀ f : K[X], f.Monic → Irreducible f → f.natDegree ≤ m → ∃ i, P i = f)
    (Q : K[X]) (hQ : Q.Monic) (hdeg : Q.natDegree ≤ m) :
    ∀ f ∈ normalizedFactors Q, ∃ i, P i = f := by
  intro f hf
  obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hQ.ne_zero).1 hf
  exact hcover f hmon hirr ((natDegree_le_of_dvd hdvd hQ.ne_zero).trans hdeg)

theorem monicIrreducibleFamily_eulerCoefficient
    {K ι : Type*} [Field K] [DecidableEq K] [Fintype K] [Fintype ι]
    (P : ι → K[X]) (hmon : ∀ i, (P i).Monic) (hirr : ∀ i, Irreducible (P i))
    (hinj : Function.Injective P) (b : ι → ℂ) (m : ℕ)
    (hcover : ∀ f : K[X], f.Monic → Irreducible f → f.natDegree ≤ m → ∃ i, P i = f) :
    letI : Fintype (degreeLT K m) :=
      Fintype.ofEquiv (Fin m → K) (degreeLTEquiv K m).symm.toEquiv
    letI : Fintype {Q : K[X] // Q.Monic ∧ Q.natDegree = m} :=
      Fintype.ofEquiv (degreeLT K m) (monicEquivDegreeLT m).symm
    PowerSeries.coeff m (∏ i, complexEulerFactor (P i).natDegree (hirr i).natDegree_pos.ne' (b i)) =
      ∑ Q : {Q : K[X] // Q.Monic ∧ Q.natDegree = m},
        ∏ i, b i ^ (normalizedFactors Q.val).count (P i) := by
  classical
  letI : Fintype (degreeLT K m) :=
    Fintype.ofEquiv (Fin m → K) (degreeLTEquiv K m).symm.toEquiv
  letI : Fintype {Q : K[X] // Q.Monic ∧ Q.natDegree = m} :=
    Fintype.ofEquiv (degreeLT K m) (monicEquivDegreeLT m).symm
  rw [PowerSeries.coeff_prod]
  calc
    _ = ∑ a ∈ polynomialFactorDegreeAllocations P m,
        ∏ i, b i ^ (a i / (P i).natDegree) := by
      rw [polynomialFactorDegreeAllocations, sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : ∀ i, (P i).natDegree ∣ a i
      · rw [if_pos ha]
        apply prod_congr rfl
        intro i _
        rw [complexEulerFactor_coeff, if_pos (ha i)]
      · rw [if_neg ha]
        push Not at ha
        obtain ⟨i, hi⟩ := ha
        apply Finset.prod_eq_zero (mem_univ i)
        rw [complexEulerFactor_coeff, if_neg hi]
    _ = _ := by
      refine Finset.sum_bij
        (fun a ha => (⟨polynomialFactorAllocationPolynomial P a,
          polynomialFactorAllocationPolynomial_monic P hmon a,
          polynomialFactorAllocationPolynomial_natDegree P hmon m a ha⟩ :
            {Q : K[X] // Q.Monic ∧ Q.natDegree = m})) ?_ ?_ ?_ ?_
      · intro _ _
        exact mem_univ _
      · intro a ha a' ha' h
        exact polynomialFactorAllocationPolynomial_injOn P hmon hirr hinj m ha ha'
          (congrArg Subtype.val h)
      · intro Q _
        obtain ⟨a, ha, heq⟩ := polynomialFactorAllocationPolynomial_surjective P hmon hirr hinj
          m Q.val Q.property.1 Q.property.2
          (monicIrreducibleFamily_covers_normalizedFactors P m hcover Q.val Q.property.1
            Q.property.2.le)
        exact ⟨a, ha, Subtype.ext heq⟩
      · intro a _
        simp only [polynomialFactorAllocationPolynomial,
          monicIrreducibleFamily_count_normalizedFactors P hmon hirr hinj]

end
end Tao2026
