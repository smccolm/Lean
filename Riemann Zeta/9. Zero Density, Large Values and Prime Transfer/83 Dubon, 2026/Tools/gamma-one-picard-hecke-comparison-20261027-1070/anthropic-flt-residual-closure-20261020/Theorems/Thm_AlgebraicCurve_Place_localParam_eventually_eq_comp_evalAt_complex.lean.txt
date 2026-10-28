import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (γ γ' : ℂ → Place ℂ F) (t : F) (U U' : Set ℂ) (z₀ z₀' : ℂ)
    (hU : U ∈ 𝓝 z₀) (hU' : U' ∈ 𝓝 z₀') (h₀ : γ' z₀' = γ z₀)
    (ht : ∀ z ∈ U, (γ z).ord (t - algebraMap ℂ F z) = 1)
    (hγ : ∀ f : F, f ≠ 0 → ∀ z ∈ U,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z))
    (hγ' : ∀ f : F, f ≠ 0 → ∀ z ∈ U',
        MeromorphicAt (fun u : ℂ => (γ' u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ' u).evalAt f) z = ((γ' z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ' z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ' u).evalAt f) z)) :
    ∀ᶠ z in 𝓝 z₀', γ' z = γ ((γ' z).evalAt t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.solution
