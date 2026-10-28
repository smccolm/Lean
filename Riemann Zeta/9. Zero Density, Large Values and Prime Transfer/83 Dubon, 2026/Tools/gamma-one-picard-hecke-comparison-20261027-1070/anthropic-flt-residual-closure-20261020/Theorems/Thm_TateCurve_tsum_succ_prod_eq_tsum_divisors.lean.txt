import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import P2M.Util
import P2M.Sol.S_TateCurve_tsum_succ_prod_eq_tsum_divisors

theorem TateCurve.tsum_succ_prod_eq_tsum_divisors {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_tsum_succ_prod_eq_tsum_divisors.solution
