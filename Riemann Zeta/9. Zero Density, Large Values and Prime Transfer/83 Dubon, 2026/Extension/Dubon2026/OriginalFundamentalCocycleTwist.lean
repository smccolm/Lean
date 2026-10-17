import Dubon2026.OriginalAugmentationSequence

/-! # The actual fundamental cocycle's twist on the augmentation ideal

The explicit cocycle construction, inspected at the pinned AnthropicFLT
source revision, avoids introducing an abstract extension certificate.
The identities below are precisely the group-action laws needed for the
fundamental-class splitting coefficient on DUB-17's finite duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (C : Rep k G) (φ : groupCohomology.cocycles₂ C)

/-- Extend the original two-cocycle linearly in its second group coordinate. -/
def originalFundamentalCocycleTwist (g : G) : (G →₀ k) →ₗ[k] C :=
  Finsupp.linearCombination k (fun h => φ (g, h))

/-- Evaluation on an actual group-ring generator. -/
theorem originalFundamentalCocycleTwist_single (g h : G) (r : k) :
    originalFundamentalCocycleTwist C φ g (Finsupp.single h r) = r • φ (g, h) := by
  rw [originalFundamentalCocycleTwist, Finsupp.linearCombination_single]

/-- Evaluation is the finite sum of the original cocycle values. -/
theorem originalFundamentalCocycleTwist_apply (g : G) (f : G →₀ k) :
    originalFundamentalCocycleTwist C φ g f = f.sum (fun h r => r • φ (g, h)) :=
  Finsupp.linearCombination_apply _ _

/-- A two-cocycle's first identity coordinate has its fixed identity value. -/
theorem originalFundamentalCocycle_one_left (h : G) : φ (1, h) = φ (1, 1) := by
  have hx := (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2 1 1 h
  rw [one_mul, one_mul, map_one] at hx
  change φ (1, h) + φ (1, 1) = φ (1, h) + φ (1, h) at hx
  exact (add_left_cancel hx).symm

/-- The identity twist vanishes on the actual augmentation ideal, without requiring a normalized cocycle representative. -/
theorem originalFundamentalCocycleTwist_one (f : G →₀ k)
    (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    originalFundamentalCocycleTwist C φ 1 f = 0 := by
  rw [originalFundamentalCocycleTwist_apply, Finsupp.sum,
    Finset.sum_congr rfl (fun h _ => by rw [originalFundamentalCocycle_one_left]),
    ← Finset.sum_smul]
  change (f.sum fun _ r => r) • φ (1, 1) = 0
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul]

/-- The cocycle equation gives the exact twisted multiplication law on the augmentation ideal. -/
theorem originalFundamentalCocycleTwist_mul (g h : G) (f : G →₀ k)
    (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    originalFundamentalCocycleTwist C φ (g * h) f =
      C.ρ g (originalFundamentalCocycleTwist C φ h f) +
        originalFundamentalCocycleTwist C φ g (Finsupp.lmapDomain k k (h * ·) f) := by
  have hx := (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2
  have ht : originalFundamentalCocycleTwist C φ g (Finsupp.lmapDomain k k (h * ·) f) =
      f.sum (fun t r => r • φ (g, h * t)) := by
    rw [originalFundamentalCocycleTwist, Finsupp.lmapDomain_apply,
      Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    rfl
  rw [ht, originalFundamentalCocycleTwist_apply, originalFundamentalCocycleTwist_apply]
  simp only [Finsupp.sum]
  rw [map_sum, ← Finset.sum_add_distrib]
  have hs : ∀ t, f t • φ (g * h, t) + f t • φ (g, h) =
      C.ρ g (f t • φ (h, t)) + f t • φ (g, h * t) := fun t => by
    rw [map_smul, ← smul_add, ← smul_add, hx g h t]
  rw [← Finset.sum_congr rfl (fun t _ => hs t), Finset.sum_add_distrib,
    ← Finset.sum_smul]
  change _ = _ + (f.sum fun _ r => r) • φ (g, h)
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul, add_zero]

end
end Dubon2026
