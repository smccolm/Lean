import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Interval
import RiemannZeta.FiniteDirichletPolynomial

open Complex Finset

namespace RiemannZeta.GuthMaynard

/-- 
The exact interval convention used in Section 13.1 for dyadic Dirichlet polynomials.
`n ∼ N` is interpreted as `n ∈ (N, 2N]`, which matches `Finset.Ioc N (2 * N)`.
-/
def dyadicInterval (N : ℕ) : Finset ℕ :=
  Ioc N (2 * N)

/-- 
An interval-indexed Dirichlet polynomial $D_N(t) = \sum_{n \sim N} a_n n^{-it}$.
-/
noncomputable def dirichletPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (-t * I)

/-- 
The normalized coefficients $\widetilde{b}_n = (N/n)^\sigma b_n$. 
-/
noncomputable def normalizedCoeffs (N : ℕ) (σ : ℝ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((N : ℝ) / (n : ℝ) : ℂ) ^ (σ : ℂ) * b n

/--
A bridge from the interval-indexed `dirichletPoly` to the existing `RiemannZeta.dirichletPoly` over `PNat`.
-/
theorem dirichletPoly_eq_existing (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPoly N a t = 
      RiemannZeta.dirichletPoly 
        (fun n => a n.val) 
        ((dyadicInterval N).subtype (fun n => 0 < n)) 
        (t * I) := by
  dsimp [dirichletPoly, RiemannZeta.dirichletPoly]
  apply Finset.sum_bij (fun (n : ℕ) _ => (⟨n, by 
      have hn : n ∈ dyadicInterval N := by assumption
      rw [dyadicInterval, mem_Ioc] at hn
      omega⟩ : { n // 0 < n }))
  case hi =>
    intro n hn
    simp only [mem_subtype]
    exact hn
  case h =>
    intro n hn
    simp
  case i_inj =>
    intro n1 hn1 n2 hn2 h_eq
    exact Subtype.mk.inj h_eq
  case i_surj =>
    intro b hb
    simp only [mem_subtype] at hb
    exact ⟨b.val, hb, Subtype.ext rfl⟩
end RiemannZeta.GuthMaynard
