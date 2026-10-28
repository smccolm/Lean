import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst

open UpperHalfPlane

theorem ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (F G : ℍ → ℂ) (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1) (hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFbd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hG : ∀ τ τ' : ℍ, ((τ' : ℂ) = ((a : ℂ) * τ + b) / d) → G τ = F τ') :
    Function.Periodic (G ∘ UpperHalfPlane.ofComplex) N ∧ MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G ∧ UpperHalfPlane.IsBoundedAtImInfty G ∧
      ((qExpansion N G : PowerSeries ℂ) : LaurentSeries ℂ)
        = ModularCurve.cosetSubst ζ a b ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.solution
