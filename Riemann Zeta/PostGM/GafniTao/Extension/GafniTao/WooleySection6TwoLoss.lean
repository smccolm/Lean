import GafniTao.WooleySection10Upper
import GafniTao.WooleyPolynomialLemma63
import GafniTao.WooleySection10Initial

/-!
# A quantifier-correct two-loss form of Wooley's initial conditioning

The limiting definition chooses the below-critical counterexample before the
smaller iteration parameter is selected.  Consequently the loss in (6.3)
and the loss in the Lemma-4.1 upper bound need not be the same real number.
This file proves the exact two-loss variant needed to respect that quantifier
order.  Setting the two losses equal recovers the numerical content used in
the paper.
-/

namespace GafniTao

noncomputable section

/-- The two-loss exponent comparison behind the initial contraction. -/
theorem wooley_initial_conditioning_exponent_twoLoss
    {eta epsilon Lambda : ℝ} {H nu : ℕ}
    (hepsilon : 0 ≤ epsilon)
    (hLambda : 0 < Lambda) (hnuH : nu ≤ H)
    (hnu : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ)) :
    (Lambda + epsilon) * ((H - nu : ℕ) : ℝ) -
        (Lambda - eta) * (H : ℝ) ≤
      -(eta + epsilon) * (H : ℝ) := by
  rw [Nat.cast_sub hnuH]
  have hLambdaNu : 2 * (eta + epsilon) * (H : ℝ) ≤
      Lambda * (nu : ℝ) := by
    rw [div_le_iff₀ hLambda] at hnu
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hnu
  have hnuNonneg : (0 : ℝ) ≤ nu := by positivity
  nlinarith

/-- Polynomial-system conditioned mean decay with distinct lower and upper
losses. -/
theorem wooleyPolynomial_conditioned_mean_le_decay_twoLoss {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {eta epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hepsilon : 0 ≤ epsilon)
    (hLambda : 0 < Lambda) (hnuH : nu ≤ H)
    (hnu : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma ≤
        wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma)
    (hupper :
      wooleyPolynomialConditionedGridMean
          phi s (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma) :
    wooleyPolynomialConditionedGridMean
        phi s (p ^ B) (p ^ nu) gamma ≤
      (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) *
        wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma := by
  let VH := wooleyPolynomialConditionedGridMean
    phi s (p ^ B) (p ^ H) gamma
  have hVH : 0 ≤ VH := by
    unfold VH wooleyPolynomialConditionedGridMean
    split_ifs with hmass
    · exact le_rfl
    · apply mul_nonneg
      · exact inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma)
      · apply Finset.sum_nonneg
        intro xi hxi
        apply mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
        apply mul_nonneg
        · positivity
        · exact Finset.sum_nonneg fun alpha halpha =>
            pow_nonneg (norm_nonneg _) _
  have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hexp := wooley_initial_conditioning_exponent_twoLoss
    hepsilon hLambda hnuH hnu
  have hpow :
      (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) ≤
        (p : ℝ) ^
          ((H : ℝ) * (Lambda - eta) +
            (-(eta + epsilon) * (H : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hpReal
    linarith
  calc
    wooleyPolynomialConditionedGridMean
        phi s (p ^ B) (p ^ nu) gamma ≤
      (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) * VH :=
        hupper
    _ ≤ (p : ℝ) ^
          ((H : ℝ) * (Lambda - eta) +
            (-(eta + epsilon) * (H : ℝ))) * VH := by gcongr
    _ = (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) *
          ((p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) * VH) := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < p)]
      ring
    _ ≤ (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) *
          wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma := by
      gcongr

/-- Lemma 6.1 with the counterexample loss and the upper-bound loss kept
separate. -/
theorem wooleyPolynomial_lemma_6_1_twoLoss {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {eta epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 ≤ epsilon)
    (hLambda : 0 < Lambda) (hnuH : nu ≤ H)
    (hnu : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma ≤
        wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma)
    (hupper :
      wooleyPolynomialConditionedGridMean
          phi s (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma)
    (hlarge : 2 * 2 ^ (s - 1) *
      (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) ≤ 1) :
    wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ nu : ℝ) ^ s *
        wooleyPolynomialMixedGridMean
          phi s 1 p B nu nu nu gamma := by
  have h69 := wooleyPolynomial_equation_6_9 phi p B nu s gamma hs
  have hdecay := wooleyPolynomial_conditioned_mean_le_decay_twoLoss
    phi p B nu H s gamma hp hepsilon hLambda hnuH hnu hlower hupper
  have hU : 0 ≤ wooleyPolynomialWeightedGridMean
      phi s (p ^ B) gamma := by
    unfold wooleyPolynomialWeightedGridMean
    positivity
  have hmain :
      wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
        2 ^ (s - 1) *
          ((p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) *
              wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma +
            (p ^ nu : ℝ) ^ s *
              wooleyPolynomialMixedGridMean
                phi s 1 p B nu nu nu gamma) := by
    calc
      wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
        2 ^ (s - 1) *
          (wooleyPolynomialConditionedGridMean
              phi s (p ^ B) (p ^ nu) gamma +
            (p ^ nu : ℝ) ^ s *
              wooleyPolynomialMixedGridMean
                phi s 1 p B nu nu nu gamma) := h69
      _ ≤ _ := by gcongr
  have habs := wooley_absorb_contraction
    (U := wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma)
    (K := (p ^ nu : ℝ) ^ s *
      wooleyPolynomialMixedGridMean phi s 1 p B nu nu nu gamma)
    hU hmain hlarge
  simpa [mul_assoc] using habs

/-- Lemma 6.3 with distinct lower and upper losses. -/
theorem wooleyPolynomial_lemma_6_3_twoLoss {Q k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B nu theta H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {eta epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 ≤ epsilon)
    (hLambda : 0 < Lambda) (hnuH : nu ≤ H) (hnuTheta : nu ≤ theta)
    (hnu : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma ≤
        wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma)
    (hupper :
      wooleyPolynomialConditionedGridMean
          phi s (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyPolynomialConditionedGridMean
            phi s (p ^ B) (p ^ H) gamma)
    (hlarge : 2 * 2 ^ (s - 1) *
      (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) ≤ 1) :
    wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ theta : ℝ) ^ s *
        wooleyPolynomialMixedGridMean
          phi s 1 p B theta theta nu gamma := by
  have hinitial := wooleyPolynomial_lemma_6_1_twoLoss
    phi p B nu H s gamma hp hs hepsilon hLambda hnuH hnu
      hlower hupper hlarge
  exact wooleyPolynomial_lemma_6_3_of_initial_conditioning
    (C := 2 * 2 ^ (s - 1)) phi (by positivity)
      hnuTheta hs gamma hinitial

/-- Source-sequence form of the quantifier-correct two-loss Lemma 6.3. -/
theorem wooleySourcePolynomial_lemma_6_3_twoLoss
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B nu theta H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : WooleySourceSequence) {eta epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 ≤ epsilon)
    (hLambda : 0 < Lambda) (hnuH : nu ≤ H) (hnuTheta : nu ≤ theta)
    (hnu : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) *
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
      (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) ≤ 1) :
    wooleySourcePolynomialMean s (p ^ B) phi gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ theta : ℝ) ^ s *
        wooleySourcePolynomialMixedMean
          phi s 1 p B theta theta nu gamma := by
  let phiBox := wooleyBoxedPolynomialSystem phi gamma
  let gammaBox := wooleySourceBoxCoefficients gamma
  have hfinite := wooleyPolynomial_lemma_6_3_twoLoss
    phiBox p B nu theta H s gammaBox hp hs hepsilon hLambda
      hnuH hnuTheta hnu
      (by simpa only [phiBox, gammaBox,
        ← wooleySourcePolynomialConditionedMean_eq_boxed,
        ← wooleySourcePolynomialMean_eq_boxed] using hlower)
      (by simpa only [phiBox, gammaBox,
        ← wooleySourcePolynomialConditionedMean_eq_boxed] using hupper)
      hlarge
  simpa only [phiBox, gammaBox,
    ← wooleySourcePolynomialMean_eq_boxed,
    ← wooleySourcePolynomialMixedMean_eq_boxed
      phi s 1 p B theta theta nu hnuTheta hnuTheta gamma] using hfinite

/-- The first normalized mixed-mean lower bound with its below-critical and
upper-bound losses separated. -/
theorem wooleySourceNormalizedMixedMean_initial_twoLoss
    {k p B nu theta : ℕ} [NeZero p]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    {eta epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hepsilon : 0 ≤ epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ B ⌈/⌉ k) (hnuTheta : nu ≤ theta)
    (hnu : 2 * (eta + epsilon) * (B ⌈/⌉ k : ℕ) / Lambda ≤
      (nu : ℝ))
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ nu) phi gamma ≤
        (p : ℝ) ^ ((((B ⌈/⌉ k) - nu : ℕ) : ℝ) *
            (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma)
    (hlarge : 2 * 2 ^ (wooleyTriangular k - 1) *
      (p : ℝ) ^ (-(eta + epsilon) * (B ⌈/⌉ k : ℕ)) ≤ 1)
    (hcounter :
      (p : ℝ) ^ (((B ⌈/⌉ k : ℕ) : ℝ) * (Lambda - eta)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma <
        wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) phi gamma) :
    (2 * 2 ^ (wooleyTriangular k - 1) : ℝ)⁻¹ *
        (p : ℝ) ^
          (-(((B ⌈/⌉ k : ℕ) : ℝ) * eta) -
            (wooleyTriangular k : ℝ) * theta) ≤
      wooleySourceNormalizedMixedMean phi p (B) (B ⌈/⌉ k)
        (wooleyTriangular k) 1 theta theta nu Lambda gamma := by
  let H := B ⌈/⌉ k
  let s := wooleyTriangular k
  let U := wooleySourcePolynomialMean s (p ^ B) phi gamma
  let Z := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma
  let K := wooleySourcePolynomialMixedMean phi s 1 p B theta theta nu gamma
  let C : ℝ := 2 * 2 ^ (s - 1)
  have hs : 2 ≤ s := by
    exact (show 2 ≤ wooleyTriangular 2 by norm_num [wooleyTriangular]).trans
      (wooleyTriangular_mono hk)
  have hpPow : NeZero (p ^ B) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hpNu : NeZero (p ^ nu) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have h310 := wooleySourcePolynomial_equation_3_10
    (k := k) (p := p) (B := B) phi gamma (by omega)
  have hleft0 : 0 ≤
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) * Z := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (wooleySourcePolynomialConditionedMean_nonneg phi s (p ^ B)
        (p ^ H) gamma)
  have hUpos : 0 < U := by
    exact lt_of_le_of_lt hleft0 (by simpa only [H, s, U, Z] using hcounter)
  have hZpos : 0 < Z := by
    have h310' : U ≤ ((p ^ H : ℕ) : ℝ) ^ s * Z := by
      simpa only [H, s, U, Z] using h310
    have hZ0 := wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ H) gamma
    exact lt_of_le_of_ne hZ0 (fun hz => by
      rw [← hz, mul_zero] at h310'
      linarith)
  have h63 := wooleySourcePolynomial_lemma_6_3_twoLoss
    phi p B nu theta H s gamma hp hs hepsilon hLambda
      (by simpa only [H] using hnuH) hnuTheta
      (by simpa only [H] using hnu)
      (by simpa only [H, s, U, Z] using hcounter.le)
      (by simpa only [H, s, Z] using hupper)
      (by simpa only [H, s] using hlarge)
  have halgebra := wooley_initial_normalization_algebra
    (p := p) (H := H) (theta := theta) (s := s)
    (Lambda := Lambda) (epsilon := eta) (C := C)
    (U := U) (K := K) (Z := Z) (by omega) (by dsimp [C]; positivity)
    hZpos (by simpa only [H, s, U, Z] using hcounter.le)
    (by simpa only [C, H, s, U, K] using h63)
  rw [wooleySourceNormalizedMixedMean, wooleyNormalizationExponent_one hk]
  simp only [Real.rpow_one]
  simpa only [C, H, s, K, Z, wooleySourceNormalizationScale,
    mul_comm (Lambda : ℝ) (H : ℝ)] using halgebra

#print axioms wooley_initial_conditioning_exponent_twoLoss
#print axioms wooleyPolynomial_conditioned_mean_le_decay_twoLoss
#print axioms wooleyPolynomial_lemma_6_1_twoLoss
#print axioms wooleyPolynomial_lemma_6_3_twoLoss
#print axioms wooleySourcePolynomial_lemma_6_3_twoLoss
#print axioms wooleySourceNormalizedMixedMean_initial_twoLoss

end

end GafniTao
