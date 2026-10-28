import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental
attribute [-instance] FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
        ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) := by p2m_exact_reverting @_root_.P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.solution
