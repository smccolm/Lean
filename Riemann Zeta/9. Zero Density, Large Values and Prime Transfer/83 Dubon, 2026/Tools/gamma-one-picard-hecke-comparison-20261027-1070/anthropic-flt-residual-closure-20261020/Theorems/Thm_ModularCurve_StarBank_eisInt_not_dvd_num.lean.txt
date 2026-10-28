import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_eisInt_not_dvd_num

open scoped ArithmeticFunction.sigma
open Finset
theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_eisInt_not_dvd_num.solution
