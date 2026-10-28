import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_eisInt_series

open scoped ArithmeticFunction.sigma
open Finset
theorem ModularCurve.StarBank.eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_eisInt_series.solution
