import GafniTao.FordWNormalized
import GafniTao.FordFullWindowMoment

/-!
# A quantitative complete-window core bound for Ford's Lemma 5.1

This is the exact consumer joining the two Vinogradov mean-value estimates to
the normalized `W_j` product.  It deliberately leaves the resulting powers
unsimplified; subsequent files substitute Ford's scales and perform the
exponent arithmetic.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma51SourceCore_full_le
    {k r s M Q N : ℕ} {M₁ M₂ t C delta q : ℝ}
    (hfloor : ⌊M₁⌋₊ = M)
    (hM₂ : 0 < M₂) (hr : 0 < r) (hs : 0 < s)
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hN : (0 : ℝ) < N) (ht : 0 < t)
    (hC : 0 ≤ C)
    (hmomentR : FordVinogradovMomentBound r k C delta)
    (hmomentS : FordVinogradovMomentBound s k C delta)
    (hgood : ∀ j ∈ fordGoodDegreeSet k,
      fordWNormalizedFactor s M₂ r M N t j ≤ q) :
    fordLemma51SourceCore k 1 k r s M₁ M₂ N (Finset.Icc 1 Q) t ≤
      (5 * (r : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
        (M : ℝ) ^ (-(2 * r : ℝ) + fordVinogradovKappa k) *
        (C * (M : ℝ) ^ fordLambda34 r k delta) *
        (C * (Q : ℝ) ^ fordLambda34 s k delta) *
        ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k *
          q ^ (fordGoodDegreeSet k).card) := by
  have hmomentM := hmomentR M hM
  have hmomentQ := hmomentS Q hQ
  have hprod := fordLemma51WReal_full_prod_le
    (k := k) (s := s) (r := r) (M := M) (M₂ := M₂)
    (N := (N : ℝ)) (t := t) hs hM₂ hr (by omega) hN ht hgood
  unfold fordLemma51SourceCore
  rw [hfloor, fordLemma51WindowMoment_full_eq_vinogradov]
  have hprod0 : 0 ≤ ∏ j : FordLemma51DegreeWindow k 1 k,
      fordLemma51WReal s M₂ r M N t j.1 := by
    exact Finset.prod_nonneg fun j _ =>
      fordLemma51WReal_nonneg hs hM₂.le hr (by omega) hN ht j.1
  gcongr

#print axioms fordLemma51SourceCore_full_le

end

end GafniTao
