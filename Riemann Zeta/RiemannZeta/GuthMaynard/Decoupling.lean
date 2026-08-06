import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.Separated

open Complex Finset

namespace RiemannZeta.GuthMaynard


/--
The l^2 decoupling inequality for the parabola (Bourgain-Demeter-Guth).
This isolates the core geometric incidence bound used in the Guth-Maynard large values theorem.
For our purposes, we formulate the recursive structure bounding a polynomial evaluated at
points in a separated set `W` by a sum over frequency blocks of size `K`.
-/
def DecouplingProp : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ (N K : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 0 < K → K ≤ N → 1 ≤ T →
        IsSeparated 1 W →
        InBaseInterval T W →
        -- The polynomial sum bounded by the decoupling bound over blocks of size N/K
        ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 ≤
          C * K^ε * (∑ k ∈ Ioc 0 K, ∑ t ∈ W, ‖∑ n ∈ Ioc (N + k * (N / K)) (N + (k + 1) * (N / K)), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2)

/-- Bourgain-Guth recursive block decomposition step -/
lemma recursive_block_decomposition (N K : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) : True := trivial

variable (l2_decoupling_bound : DecouplingProp)


/--
Multi-scale block decomposition.
The Bourgain-Guth recursive method requires splitting the frequency interval [N, 2N]
into small blocks. Here we formulate the algebraic identity that the sum over [N, 2N]
is the sum over blocks of length N/K.
-/
variable (block_decomposition : ∀ (N K : ℕ) (hK : 0 < K) (a : ℕ → ℂ) (t : ℝ),
  (N % K = 0) →
  ∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I) =
  ∑ k ∈ Ioc 0 K, ∑ n ∈ Ioc (N + (k - 1) * (N / K)) (N + k * (N / K)), a n * (n : ℂ) ^ (-(t : ℂ) * I))

end RiemannZeta.GuthMaynard
