import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular

theorem FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) (hf : IntegrableOn f (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ)) :
    ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ∫ τ in ModularGroup.fd, f ((Quotient.out q)⁻¹ • τ) := by p2m_exact_reverting @_root_.P2MW.S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd.solution
