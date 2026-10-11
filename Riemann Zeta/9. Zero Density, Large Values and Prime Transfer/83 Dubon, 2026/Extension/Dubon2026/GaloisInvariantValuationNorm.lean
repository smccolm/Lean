import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.Basic

/-! # The actual field norm under a genuine Galois-invariant valuation -/

namespace Dubon2026
noncomputable section

variable {K L Γ₀ : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation L Γ₀)
  (hv : ∀ (g : Gal(L/K)) (x : L), v (g x) = v x)

include hv in
/-- The actual product formula for the original field norm and genuine
Galois invariance give its valuation as the degree power of the original
element valuation. Invariance remains an explicit narrower input here. -/
theorem galoisInvariantValuation_norm (x : L) :
    v (algebraMap K L (Algebra.norm K x)) = v x ^ Module.finrank K L := by
  rw [Algebra.norm_eq_prod_automorphisms, map_prod]
  simp_rw [hv]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank]

end
end Dubon2026
