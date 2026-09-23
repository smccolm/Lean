import TaoTrudgianYang2025.ZeroEnergyAssembly
import TaoTrudgianYang2025.CardinalityPartition

/-!
# Multiplicity-preserving restrictions of indexed zero families

Every injection retains the copy number attached to a zero. Negative
ordinates use the proved conjugation equivalence, including vanishing orders.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem weightedCopy_family_card_le
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S T : Finset α) (weight : α → ℕ) (f : ι → WeightedCopy S weight)
    (hf : Function.Injective f) (hT : ∀ i, (f i).1.1 ∈ T) :
    Fintype.card ι ≤ ∑ x ∈ T, weight x := by
  let g : ι → WeightedCopy T weight := fun i => ⟨⟨(f i).1.1, hT i⟩, (f i).2⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hf
    have hz : (f i).1 = (f j).1 := Subtype.ext (congrArg (fun z => z.1.1) hij)
    apply Sigma.ext hz
    apply (Fin.heq_ext_iff (congrArg (fun z : ↥S => weight z.1) hz)).mpr
    exact congrArg (fun z => z.2.val) hij
  calc
    Fintype.card ι ≤ Fintype.card (WeightedCopy T weight) :=
      Fintype.card_le_of_injective g hg
    _ = ∑ x ∈ T, weight x := weightedCopy_card T weight

theorem zeroCopy_family_card_le_classicalSlab
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f)
    (hH : ∀ i, H ≤ ((f i).1 : ℂ).im ∧ ((f i).1 : ℂ).im ≤ 2 * H) :
    Fintype.card ι ≤ zeroCountRect σ 1 H (2 * H) := by
  apply weightedCopy_family_card_le (paperZeros σ T) (zerosInRect σ 1 H (2 * H))
    (analyticVanishingOrder riemannZeta) f hf
  intro i
  have hz := (mem_paperZeros_iff ((f i).1 : ℂ)).mp (f i).1.2
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_ZeroRectangle]
  exact ⟨⟨hz.1, hz.2.1, (hH i).1, (hH i).2⟩, hz.2.2.2⟩

theorem zeroCopy_family_card_le_classicalSlab_of_neg
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f)
    (hH : ∀ i, H ≤ -((f i).1 : ℂ).im ∧ -((f i).1 : ℂ).im ≤ 2 * H) :
    Fintype.card ι ≤ zeroCountRect σ 1 H (2 * H) := by
  let g := zeroCopyConjEquiv σ T ∘ f
  have hg : Function.Injective g := (zeroCopyConjEquiv σ T).injective.comp hf
  exact zeroCopy_family_card_le_classicalSlab σ T H g hg hH

theorem zeroCopy_family_card_le_low_height
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f) (hH : ∀ i, |((f i).1 : ℂ).im| ≤ H) :
    Fintype.card ι ≤ paperZeroCount σ H := by
  apply weightedCopy_family_card_le (paperZeros σ T) (paperZeros σ H)
    (analyticVanishingOrder riemannZeta) f hf
  intro i
  have hz := (mem_paperZeros_iff ((f i).1 : ℂ)).mp (f i).1.2
  exact (mem_paperZeros_iff _).mpr ⟨hz.1, hz.2.1, hH i, hz.2.2.2⟩

end TaoTrudgianYang2025
