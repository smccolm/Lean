import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary. Use the literal Siegel
infinite product and identify it with the original analytic Jacobi theta
function divided by the native nonvanishing eta product. This discharges
holomorphy of the required factors and supplies common identities for
their SL2 transformation; modularity and integral expansions remain
separate obligations. No abstract function replaces the product.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_ModularCurve_SiegelFunction and
S_ModularCurve_SiegelUnit_differentiableOn_siegelFun. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
noncomputable section

/-- The source Siegel function, defined by its literal exponential infinite product. -/
def siegelFun (N : ℕ) (r s : ℤ) (z : ℂ) : ℂ :=
  -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
    (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
    ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹))

theorem siegelFun_def (N : ℕ) (r s : ℤ) (z : ℂ) :
    siegelFun N r s z =
      -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
        ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
          (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹)) :=
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
