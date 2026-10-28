import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic (N : ℕ) [NeZero N]
    (F : ℍ → ℂ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic.solution
