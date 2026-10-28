import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow

open UpperHalfPlane

theorem ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.solution
