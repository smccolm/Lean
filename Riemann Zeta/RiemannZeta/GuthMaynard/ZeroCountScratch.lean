import RiemannZeta.GuthMaynard.ZeroCount

open Complex Finset Set

namespace RiemannZeta.GuthMaynard

lemma zeroCountRect_symm (model : ZetaZeroCountModel) (σ T : ℝ) :
    zeroCountRect model σ 1 (-T) 0 = zeroCountRect model σ 1 0 T := by
  unfold zeroCountRect
  apply Finset.sum_bij (fun s _ => conj s)
  · intro s hs
    sorry
  · intro s₁ hs₁ s₂ hs₂ h
    sorry
  · intro s hs
    sorry
  · intro s hs
    sorry

end RiemannZeta.GuthMaynard
