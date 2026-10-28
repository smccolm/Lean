import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qExpansion_prod

open UpperHalfPlane
open scoped Manifold
theorem UpperHalfPlane.qExpansion_prod {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qExpansion_prod.solution
