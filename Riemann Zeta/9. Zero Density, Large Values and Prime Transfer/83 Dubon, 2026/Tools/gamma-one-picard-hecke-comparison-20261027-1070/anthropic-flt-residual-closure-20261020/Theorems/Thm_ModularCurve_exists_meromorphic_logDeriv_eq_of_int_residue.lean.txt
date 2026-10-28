import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue

open scoped Topology

theorem ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
    (m : ℂ → ℤ) (ω : ℂ → ℂ)
    (hres : ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)) :
    ∃ G : ℂ → ℂ, ∀ a : ℂ, 0 < a.im →
      MeromorphicAt G a ∧ meromorphicOrderAt G a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G a = 0) ∧
      (m a = 0 → AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ HasDerivAt G (ω a * G a) a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.solution
