import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (ρ : Place ℂ F → ℝ) (γ : Place ℂ F → ℂ → Place ℂ F) (t : Place ℂ F → F)
    (hρ : ∀ v, 0 < ρ v) (h₀ : ∀ v, γ v 0 = v)
    (ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1)
    (hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
        MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)) :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ γ v z = w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.solution
