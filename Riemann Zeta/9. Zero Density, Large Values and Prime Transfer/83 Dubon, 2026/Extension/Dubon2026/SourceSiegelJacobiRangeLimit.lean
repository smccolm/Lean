import Dubon2026.SourceSiegelJacobiDominatedLimit

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> Siegel-product transformation
and holomorphy -> Jacobi theta product. These are the exact convergence
bounds for the finite Gaussian approximation. Mathlib supplies the
geometric-product convergence and dominated convergence; the source
quotient bounds discharge their actual denominator hypotheses.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
open Finset Filter Topology
variable {Q : ℂ}

theorem tendsto_sum_range (hQ : ‖Q‖ < 1) {t : ℤ → ℂ} (ht : Summable fun j => ‖t j‖)
    (d : ℕ → ℕ → ℂ)
    (hd : ∀ (N k : ℕ), k ≤ 2 * N → d N k = qfact Q (2 * N) / (qfact Q k * qfact Q (2 * N - k))) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), d N k * t ((k : ℤ) - N)) atTop
      (𝓝 ((∏' n : ℕ, (1 - Q ^ (n + 1)))⁻¹ * ∑' j : ℤ, t j)) := by
  have hre : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N + 1), d N k * t ((k : ℤ) - N)
      = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, d N (j + N).toNat * t j := by
    intro N
    refine Finset.sum_nbij' (fun k => (k : ℤ) - N) (fun j => (j + N).toNat) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range] at hk
      show (k : ℤ) - N ∈ Finset.Icc (-(N : ℤ)) N
      rw [Finset.mem_Icc]
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show (j + N).toNat ∈ Finset.range (2 * N + 1)
      rw [Finset.mem_range]
      omega
    · intro k _
      show ((k : ℤ) - N + N).toNat = k
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show (((j + N).toNat : ℕ) : ℤ) - N = j
      omega
    · intro k _
      show d N k * t ((k : ℤ) - N) = d N ((k : ℤ) - N + N).toNat * t ((k : ℤ) - N)
      rw [show ((k : ℤ) - N + N).toNat = k by omega]
  simp_rw [hre]
  refine tendsto_sum_Icc hQ ht (fun N j => d N (j + N).toNat) fun N j h1 h2 => ?_
  show d N (j + N).toNat = qfact Q (2 * N) / (qfact Q (N + j).toNat * qfact Q (N - j).toNat)
  rw [hd N (j + N).toNat (by omega), show (j + (N : ℤ)).toNat = ((N : ℤ) + j).toNat by rw [add_comm],
    show 2 * N - ((N : ℤ) + j).toNat = ((N : ℤ) - j).toNat by omega]

end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
