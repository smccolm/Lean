import GafniTao.HeathBrownEquation44
import GafniTao.HeathBrownLemmaThreeTail

/-!
# Unconditional Heath--Brown equation (44)

This file closes the sole analytic premise of the finite equation-(44)
consumer with the contour proof of Heath--Brown's Lemma 3.  Keeping this
composition in a separate module avoids making the source-shaped consumer
circular while exposing an unconditional theorem to the twelfth-moment
assembly.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Heath--Brown (1978), equation (44), obtained from the proved contour,
tail, and compact-range versions of Lemma 3. -/
theorem heathBrown_equation44_native :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        IsSeparated 1 W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ heathBrownCriticalZetaNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * heathBrownLocalSecondMoment center G) :=
  heathBrown_equation44_of_lemmaThree heathBrownLemmaThree_native


end

end GafniTao
