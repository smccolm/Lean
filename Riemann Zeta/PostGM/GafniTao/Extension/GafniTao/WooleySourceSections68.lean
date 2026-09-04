import GafniTao.WooleySourceMixed
import GafniTao.WooleyPolynomialLemma63
import GafniTao.WooleySection8

/-!
# Source-sequence consumers for Wooley Sections 6 and 8

The analytic inequalities were first proved on a finite box.  The exact
boxing equalities now allow those results to be stated and consumed on the
source's finitely supported integer sequences.  Every displayed mean below
is the literal source mean from (3.7), (3.8), or (3.19).
-/

namespace GafniTao

noncomputable section

/-- Literal source-sequence form of the easy branch `B' ≤ nu` in Wooley
Lemma 7.1. -/
theorem wooleySourcePolynomial_section7_easy
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p nu a b B s r gammaVal : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hnua : nu ≤ a) (hnub : nu ≤ b)
    (haa' : a ≤ wooleySection7NextB k r b)
    (hgamma : gammaVal < nu)
    (hBPrime : wooleySection7BPrimeInt k r a b gammaVal ≤ (nu : ℤ))
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleySection7NextB k r b) b nu gamma := by
  have hnuNext : nu ≤ wooleySection7NextB k r b := hnua.trans haa'
  let phiBox := wooleyBoxedPolynomialSystem phi gamma
  let gammaBox := wooleySourceBoxCoefficients gamma
  have hfinite := wooleyPolynomial_section7_easy
    (Q := wooleySourceBoxLength gamma) (p := p) (nu := nu)
    (a := a) (b := b) (B := B) (k := k) (s := s)
    (r := r) (gammaVal := gammaVal)
    phiBox hp hr hrk hnu hnua haa' hgamma hBPrime gammaBox
  simpa only [phiBox, gammaBox,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi s r p B a b nu hnua hnub gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi s r p B (wooleySection7NextB k r b) b nu
        hnuNext hnub gamma] using hfinite

/-- Source-sequence form of Wooley Lemma 6.3. -/
theorem wooleySourcePolynomial_lemma_6_3
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B nu theta H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : WooleySourceSequence) {epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ H) (hnuTheta : nu ≤ theta)
    (hnu : 4 * epsilon * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) *
          wooleySourcePolynomialConditionedMean
            s (p ^ B) (p ^ H) phi gamma ≤
        wooleySourcePolynomialMean s (p ^ B) phi gamma)
    (hupper :
      wooleySourcePolynomialConditionedMean
          s (p ^ B) (p ^ nu) phi gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            s (p ^ B) (p ^ H) phi gamma)
    (hlarge : 2 * 2 ^ (s - 1) *
      (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) ≤ 1) :
    wooleySourcePolynomialMean s (p ^ B) phi gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ theta : ℝ) ^ s *
        wooleySourcePolynomialMixedMean
          phi s 1 p B theta theta nu gamma := by
  let phiBox := wooleyBoxedPolynomialSystem phi gamma
  let gammaBox := wooleySourceBoxCoefficients gamma
  have hlowerBox :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) *
          wooleyPolynomialConditionedGridMean
            phiBox s (p ^ B) (p ^ H) gammaBox ≤
        wooleyPolynomialWeightedGridMean phiBox s (p ^ B) gammaBox := by
    simpa only [phiBox, gammaBox,
      ← wooleySourcePolynomialConditionedMean_eq_boxed,
      ← wooleySourcePolynomialMean_eq_boxed] using hlower
  have hupperBox :
      wooleyPolynomialConditionedGridMean
          phiBox s (p ^ B) (p ^ nu) gammaBox ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyPolynomialConditionedGridMean
            phiBox s (p ^ B) (p ^ H) gammaBox := by
    simpa only [phiBox, gammaBox,
      ← wooleySourcePolynomialConditionedMean_eq_boxed] using hupper
  have hfinite := wooleyPolynomial_lemma_6_3
    phiBox p B nu theta H s gammaBox hp hs hepsilon hLambda
      hnuH hnuTheta hnu hlowerBox hupperBox hlarge
  simpa only [phiBox, gammaBox,
    ← wooleySourcePolynomialMean_eq_boxed,
    ← wooleySourcePolynomialMixedMean_eq_boxed
      phi s 1 p B theta theta nu hnuTheta hnuTheta gamma] using hfinite

/-- Source-sequence form of the two-factor Hölder estimate (8.3). -/
theorem wooleySourcePolynomial_equation_8_3
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B r bPrime b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hr : 1 ≤ r) (hrk : r < k) (hnuPrime : nu ≤ bPrime)
    (hnub : nu ≤ b) (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B bPrime b nu gamma ≤
      (wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) ^
        (1 / ((k - r + 1 : ℕ) : ℝ)) *
      (wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) ^
        (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) := by
  let phiBox := wooleyBoxedPolynomialSystem phi gamma
  let gammaBox := wooleySourceBoxCoefficients gamma
  have hfinite := wooleyPolynomial_equation_8_3
    (Q := wooleySourceBoxLength gamma) (p := p) (B := B)
    (k := k) (r := r) (bPrime := bPrime) (b := b) (nu := nu)
    phiBox hr hrk gammaBox
  simpa only [phiBox, gammaBox,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) r p B bPrime b nu hnuPrime hnub gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) (k - r) p B b bPrime nu hnub hnuPrime gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) (r - 1) p B bPrime b nu hnuPrime hnub gamma]
    using hfinite

/-- Source version of (8.1), explicitly consuming the source form of
Lemma 7.1. -/
theorem wooleySourcePolynomial_equation_8_1_of_section7
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B r a b bPrime nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hr : 2 ≤ r) (hrk : r < k)
    (hnub : nu ≤ b) (hnuPrime : nu ≤ bPrime)
    (gamma : WooleySourceSequence)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) r p B a b nu gamma ≤
        (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) r p B bPrime b nu gamma) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B a b nu gamma ≤
      (p : ℝ) ^ (k ^ 2 * nu) *
        ((wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) ^
          (1 / ((k - r + 1 : ℕ) : ℝ)) *
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) ^
          (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ))) := by
  exact hsection7.trans (mul_le_mul_of_nonneg_left
    (wooleySourcePolynomial_equation_8_3
      phi p B r bPrime b nu (by omega) hrk hnuPrime hnub gamma)
    (by positivity))

#print axioms wooleySourcePolynomial_lemma_6_3
#print axioms wooleySourcePolynomial_section7_easy
#print axioms wooleySourcePolynomial_equation_8_3
#print axioms wooleySourcePolynomial_equation_8_1_of_section7

end

end GafniTao
