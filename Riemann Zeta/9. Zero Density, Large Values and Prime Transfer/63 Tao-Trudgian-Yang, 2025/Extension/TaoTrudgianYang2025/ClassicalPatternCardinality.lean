import TaoTrudgianYang2025.ClassicalTypeIEnergyTransfer
import TaoTrudgianYang2025.CardinalityPartition

/-! # Exact cardinality of actual classical source patterns -/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

/-- Packaging a separated indexed source preserves its exact cardinality. -/
theorem indexedDirichletLargeValuePattern_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (threshold a b : ℝ) (coeff : ℕ → ℂ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hcoeff : ∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖dirichletPoly N coeff (W x)‖) :
    (indexedDirichletLargeValuePattern N threshold a b coeff W hN
      hthreshold hab hcoeff hW hsep hlarge).ordinates.card = Fintype.card ι := by
  rw [indexedDirichletLargeValuePattern_ordinates,
    Finset.card_image_of_injective _ (injective_of_indexed_oneSeparated W hsep)]
  exact Finset.card_univ

/-- Zeta packaging retains every original separated index. -/
theorem indexedClassicalTypeIZetaPattern_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A N : ℕ) (V H : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hV : 0 < V) (hH : 0 < H)
    (hW : ∀ x, H ≤ W x ∧ W x ≤ 2 * H)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, V ≤
      ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (W x)‖) :
    (indexedClassicalTypeIZetaPattern A N V H W hN hV hH hW hsep hlarge).ordinates.card =
      Fintype.card ι := by
  change (Finset.univ.image W).card = Fintype.card ι
  rw [Finset.card_image_of_injective _ (injective_of_indexed_oneSeparated W hsep)]
  exact Finset.card_univ

end TaoTrudgianYang2025
