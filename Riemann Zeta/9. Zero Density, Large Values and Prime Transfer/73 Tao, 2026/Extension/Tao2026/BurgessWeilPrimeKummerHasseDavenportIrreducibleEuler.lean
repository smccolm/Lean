import Tao2026.BurgessWeilPrimeKummerHasseDavenportEulerProduct
import Mathlib.Data.Fintype.Sigma

/-!
# The irreducible-polynomial Hasse--Davenport Euler product

This file specializes the finite weighted Euler-product engine to monic
irreducible polynomials over a finite field. The alphabet contains all such
polynomials of degree at most a fixed cutoff. Its Euler coefficients and
closed-point coefficients satisfy the exact logarithmic-derivative recurrence,
and the latter are rewritten both as a sum over irreducibles and as a sum by
degree.

For the coefficient side, every contributing degree allocation is sent to the
product of the corresponding irreducible powers. This polynomial is proved
monic, to have the prescribed total degree, and to have exactly the product
weight appearing in the Euler coefficient. The remaining algebraic step is
the inverse construction from normalized factorization.
-/

open scoped BigOperators

noncomputable section

namespace Tao2026

open PowerSeries

/-- A monic irreducible polynomial of prescribed natural degree. -/
def HasseDavenportMonicIrreduciblePolynomial
    (K : Type*) [Field K] (d : ℕ) :=
  {p : {p : Polynomial K // p.Monic ∧ p.natDegree = d} //
    Irreducible p.1}

instance hasseDavenportMonicIrreduciblePolynomialFintype
    (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    Fintype (HasseDavenportMonicIrreduciblePolynomial K d) := by
  classical
  letI : Fintype {p : Polynomial K // p.Monic ∧ p.natDegree = d} :=
    monicPolynomialNatDegreeFintype K d
  exact Fintype.ofInjective (fun p => p.1) Subtype.val_injective

/-- Monic irreducible polynomials whose degree is at most `N`, indexed by
their degree. -/
def HasseDavenportIrreduciblePolynomialUpTo
    (K : Type*) [Field K] (N : ℕ) :=
  Σ d : Fin (N + 1), HasseDavenportMonicIrreduciblePolynomial K d.1

instance hasseDavenportIrreduciblePolynomialUpToFintype
    (K : Type*) [Field K] [Fintype K] (N : ℕ) :
    Fintype (HasseDavenportIrreduciblePolynomialUpTo K N) := by
  classical
  exact Sigma.instFintype

noncomputable instance hasseDavenportIrreduciblePolynomialUpToDecidableEq
    (K : Type*) [Field K] (N : ℕ) :
    DecidableEq (HasseDavenportIrreduciblePolynomialUpTo K N) := Classical.decEq _

def hasseDavenportIrreduciblePolynomial {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : Polynomial K := q.2.1.1

def hasseDavenportIrreducibleDegree {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : ℕ := q.1.1

theorem hasseDavenportIrreduciblePolynomial_monic {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : (hasseDavenportIrreduciblePolynomial q).Monic := q.2.1.2.1

theorem hasseDavenportIrreduciblePolynomial_irreducible {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : Irreducible (hasseDavenportIrreduciblePolynomial q) := q.2.2

@[simp] theorem hasseDavenportIrreduciblePolynomial_natDegree {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) :
    (hasseDavenportIrreduciblePolynomial q).natDegree = hasseDavenportIrreducibleDegree q := q.2.1.2.2

theorem hasseDavenportIrreducibleDegree_pos {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : 0 < hasseDavenportIrreducibleDegree q := by
  rw [hasseDavenportIrreducibleDegree, ← q.2.1.2.2]
  exact q.2.1.2.1.natDegree_pos_of_not_isUnit q.2.2.not_isUnit

def hasseDavenportIrreducibleWeight {K : Type*} [Field K] {N : ℕ}
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) : ℂ :=
  hasseDavenportMonicWeight χ ψ (hasseDavenportIrreduciblePolynomial q)

/-- The monic polynomial obtained from a degree allocation by dividing every
allocated degree by the corresponding irreducible degree. -/
def hasseDavenportIrreducibleAllocationPolynomial
    (K : Type*) [Field K] [Fintype K] (N : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ) : Polynomial K :=
  ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
    hasseDavenportIrreduciblePolynomial q ^ (l q / hasseDavenportIrreducibleDegree q)

theorem hasseDavenportIrreducibleAllocationPolynomial_monic
    (K : Type*) [Field K] [Fintype K] (N : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ) :
    (hasseDavenportIrreducibleAllocationPolynomial K N l).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro q hq
  exact (hasseDavenportIrreduciblePolynomial_monic q).pow _

theorem hasseDavenportIrreducibleAllocationPolynomial_natDegree
    (K : Type*) [Field K] [Fintype K] (N n : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ)
    (hl : l ∈ Finset.finsuppAntidiag
      (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) n)
    (hdiv : ∀ q : HasseDavenportIrreduciblePolynomialUpTo K N, hasseDavenportIrreducibleDegree q ∣ l q) :
    (hasseDavenportIrreducibleAllocationPolynomial K N l).natDegree = n := by
  rw [hasseDavenportIrreducibleAllocationPolynomial]
  have hdegree :
      (∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        hasseDavenportIrreduciblePolynomial q ^ (l q / hasseDavenportIrreducibleDegree q)).natDegree =
      ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        (hasseDavenportIrreduciblePolynomial q ^ (l q / hasseDavenportIrreducibleDegree q)).natDegree := by
    apply Polynomial.natDegree_prod_of_monic
    intro q hq
    exact (hasseDavenportIrreduciblePolynomial_monic q).pow _
  rw [hdegree]
  calc
    (∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        (hasseDavenportIrreduciblePolynomial q ^ (l q / hasseDavenportIrreducibleDegree q)).natDegree) =
        ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          (l q / hasseDavenportIrreducibleDegree q) * hasseDavenportIrreducibleDegree q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(hasseDavenportIrreduciblePolynomial_monic q).natDegree_pow,
        hasseDavenportIrreduciblePolynomial_natDegree]
    _ = ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N, l q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Nat.div_mul_cancel (hdiv q)
    _ = n := (Finset.mem_finsuppAntidiag.mp hl).1

theorem hasseDavenportIrreducibleAllocationPolynomial_weight
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ) :
    hasseDavenportMonicWeight χ ψ
        (hasseDavenportIrreducibleAllocationPolynomial K N l) =
      ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        hasseDavenportIrreducibleWeight χ ψ q ^ (l q / hasseDavenportIrreducibleDegree q) := by
  classical
  let e : HasseDavenportIrreduciblePolynomialUpTo K N → ℕ := fun q => l q / hasseDavenportIrreducibleDegree q
  have h (s : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) :
      hasseDavenportMonicWeight χ ψ
          (∏ q ∈ s, hasseDavenportIrreduciblePolynomial q ^ e q) =
        ∏ q ∈ s, hasseDavenportIrreducibleWeight χ ψ q ^ e q := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert q s hqs ih =>
        have hsmonic : (∏ r ∈ s, hasseDavenportIrreduciblePolynomial r ^ e r).Monic := by
          apply Polynomial.monic_prod_of_monic
          intro r hr
          exact (hasseDavenportIrreduciblePolynomial_monic r).pow _
        rw [Finset.prod_insert hqs, Finset.prod_insert hqs,
          hasseDavenportMonicWeight_mul χ ψ
            ((hasseDavenportIrreduciblePolynomial_monic q).pow _) hsmonic,
          hasseDavenportMonicWeight_pow χ ψ
            (hasseDavenportIrreduciblePolynomial_monic q), ih]
        rfl
  simpa [hasseDavenportIrreducibleAllocationPolynomial, e, hasseDavenportIrreducibleWeight] using
    h (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N))

/-- The coefficient sequence of the bounded irreducible Euler product. -/
def hasseDavenportIrreducibleEulerCoefficient
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) : ℂ :=
  weightedEulerProductCoefficient
    (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N))
    (hasseDavenportIrreducibleWeight χ ψ) hasseDavenportIrreducibleDegree n

/-- The closed-point sequence of the bounded irreducible Euler product. -/
def hasseDavenportIrreducibleClosedPointCoefficient
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N : ℕ) : ℕ → ℂ :=
  weightedEulerClosedPointCoefficient
    (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N))
    (hasseDavenportIrreducibleWeight χ ψ) hasseDavenportIrreducibleDegree

/-- The bounded irreducible Euler coefficients and closed-point coefficients
satisfy the Hasse--Davenport logarithmic-derivative recurrence. -/
theorem hasseDavenportIrreducibleEulerRecurrence
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N : ℕ) :
    HasseDavenportLogDerivativeRecurrence
      (hasseDavenportIrreducibleEulerCoefficient K χ ψ N)
      (hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N) := by
  exact weightedEulerProduct_logDerivativeRecurrence
    (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N))
    (hasseDavenportIrreducibleWeight χ ψ) hasseDavenportIrreducibleDegree

theorem hasseDavenportIrreducibleClosedPointCoefficient_eq_sum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) :
    hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N (n + 1) =
      ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        if hasseDavenportIrreducibleDegree q ∣ n + 1 then
          (hasseDavenportIrreducibleDegree q : ℂ) *
            hasseDavenportIrreducibleWeight χ ψ q ^ ((n + 1) / hasseDavenportIrreducibleDegree q)
        else 0 := by
  classical
  apply weightedEulerClosedPointCoefficient_eq_sum
  intro q hq
  exact (hasseDavenportIrreducibleDegree_pos q).ne'

theorem hasseDavenportIrreducibleClosedPointCoefficient_eq_degree_sum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) :
    hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N (n + 1) =
      ∑ d : Fin (N + 1), if d.1 ∣ n + 1 then
        (d.1 : ℂ) *
          ∑ q : HasseDavenportMonicIrreduciblePolynomial K d.1,
            hasseDavenportMonicWeight χ ψ q.1.1 ^ ((n + 1) / d.1)
      else 0 := by
  rw [hasseDavenportIrreducibleClosedPointCoefficient_eq_sum]
  simp only [HasseDavenportIrreduciblePolynomialUpTo]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdiv : d.1 ∣ n + 1
  · simp only [hdiv, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    simp [hasseDavenportIrreducibleDegree, hasseDavenportIrreducibleWeight, hasseDavenportIrreduciblePolynomial, hdiv]
  · simp [hasseDavenportIrreducibleDegree, hdiv]

theorem hasseDavenportIrreducibleEulerCoefficient_eq_sum_allocations
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) :
    hasseDavenportIrreducibleEulerCoefficient K χ ψ N n =
      ∑ l ∈ Finset.finsuppAntidiag
          (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) n,
        ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          if hasseDavenportIrreducibleDegree q ∣ l q then
            hasseDavenportIrreducibleWeight χ ψ q ^ (l q / hasseDavenportIrreducibleDegree q)
          else 0 := by
  classical
  rw [hasseDavenportIrreducibleEulerCoefficient, weightedEulerProductCoefficient,
    weightedEulerProduct, coeff_prod]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro q hq
  exact coeff_weightedEulerFactor (hasseDavenportIrreducibleWeight χ ψ q)
    (hasseDavenportIrreducibleDegree_pos q).ne'

end Tao2026
