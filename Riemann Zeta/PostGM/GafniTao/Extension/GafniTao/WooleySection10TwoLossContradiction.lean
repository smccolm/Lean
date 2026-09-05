import GafniTao.WooleySection6TwoLoss
import GafniTao.WooleySection10Contradiction

/-!
# The Section 10 contradiction with separately quantified losses

The lower counterexample loss and the subsequent iteration loss are merged
only at the final elementary comparison.  This removes the circular choice
of `epsilon` and `tau` implicit in the paper's hierarchy notation.
-/

namespace GafniTao

noncomputable section

/-- The numerical comparison remains contradictory when the initial and
terminal estimates use two different nonnegative losses. -/
theorem wooley_section10_force_final_bound_twoLoss
    {p k s N theta H : ℕ}
    {Lambda eta epsilon D C0 Cterm Cacc E R K0 Kfinal : ℝ}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (htheta : 0 < theta) (hLambda : 0 < Lambda)
    (heta : 0 ≤ eta) (hD : 1 ≤ D)
    (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hKfinal : 0 ≤ Kfinal) (hR : 0 ≤ R) (hRone : R ≤ 1)
    (hinitial :
      C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * eta) - (s : ℝ) * theta) ≤ K0)
    (hiterated : K0 ≤ Cacc * Kfinal ^ R *
      (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))))
    (hCaccUpper : Cacc ≤ D ^ N)
    (hE : (N : ℝ) * theta ≤ E)
    (hterminal : Kfinal ≤ Cterm *
      (p : ℝ) ^ ((H : ℝ) * epsilon))
    (hHeta : (H : ℝ) * eta ≤ theta)
    (hHepsilon : (H : ℝ) * epsilon ≤ theta)
    (hconstants : C0 * D ^ N * max 1 Cterm ≤ (p : ℝ) ^ theta) :
    (N : ℝ) * Lambda / (2 * (k : ℝ)) ≤ 4 * (s : ℝ) := by
  let zeta := max eta epsilon
  have hzeta : 0 ≤ zeta := by exact le_max_of_le_left heta
  have hetaZeta : eta ≤ zeta := le_max_left _ _
  have hepsilonZeta : epsilon ≤ zeta := le_max_right _ _
  have hHzeta : (H : ℝ) * zeta ≤ theta := by
    dsimp only [zeta]
    rcases le_total eta epsilon with h | h
    · simpa only [max_eq_right h] using hHepsilon
    · simpa only [max_eq_left h] using hHeta
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hinitialZeta :
      C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * zeta) - (s : ℝ) * theta) ≤ K0 := by
    have hexp :
        -((H : ℝ) * zeta) - (s : ℝ) * theta ≤
          -((H : ℝ) * eta) - (s : ℝ) * theta := by
      have hH0 : (0 : ℝ) ≤ H := by positivity
      nlinarith
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hpOne hexp)
      (inv_nonneg.mpr hC0.le)).trans hinitial
  have hterminalZeta : Kfinal ≤ Cterm *
      (p : ℝ) ^ ((H : ℝ) * zeta) := by
    apply hterminal.trans
    apply mul_le_mul_of_nonneg_left _ hCterm
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    exact mul_le_mul_of_nonneg_left hepsilonZeta (by positivity)
  exact wooley_section10_force_final_bound hp hk hs htheta hLambda
    hzeta hD hC0 hCterm hKfinal hR hRone hinitialZeta hiterated
    hCaccUpper hE hterminalZeta hHzeta hconstants

/-- With Wooley's prescribed iteration length, the two-loss estimates are
inconsistent. -/
theorem wooley_section10_bounds_contradict_twoLoss
    {p k s theta H : ℕ}
    {Lambda eta epsilon D C0 Cterm Cacc E R K0 Kfinal : ℝ}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (htheta : 0 < theta) (hLambda : 0 < Lambda)
    (heta : 0 ≤ eta) (hD : 1 ≤ D)
    (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hKfinal : 0 ≤ Kfinal) (hR : 0 ≤ R) (hRone : R ≤ 1)
    (hinitial : C0⁻¹ * (p : ℝ) ^
      (-((H : ℝ) * eta) - (s : ℝ) * theta) ≤ K0)
    (hiterated : K0 ≤ Cacc * Kfinal ^ R *
      (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))))
    (hCaccUpper : Cacc ≤ D ^ (wooleyIterationLength s k Lambda))
    (hE : (wooleyIterationLength s k Lambda : ℝ) * theta ≤ E)
    (hterminal : Kfinal ≤ Cterm *
      (p : ℝ) ^ ((H : ℝ) * epsilon))
    (hHeta : (H : ℝ) * eta ≤ theta)
    (hHepsilon : (H : ℝ) * epsilon ≤ theta)
    (hconstants : C0 * D ^ (wooleyIterationLength s k Lambda) *
      max 1 Cterm ≤ (p : ℝ) ^ theta) : False := by
  exact wooley_iteration_length_final_bound_impossible hs hk hLambda
    (wooley_section10_force_final_bound_twoLoss hp hk hs htheta hLambda
      heta hD hC0 hCterm hKfinal hR hRone hinitial hiterated
      hCaccUpper hE hterminal hHeta hHepsilon hconstants)

/-- The actual iteration-chain consumer with separately quantified initial
and iteration losses. -/
theorem wooleySourcePolynomial_iterationChain_contradict_twoLoss
    {k p B H theta nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    {Lambda eta epsilon D C0 Cterm delta : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (htheta : 0 < theta)
    (hLambda : 0 < Lambda) (heta : 0 ≤ eta) (hepsilon : 0 ≤ epsilon)
    (hD : 1 ≤ D) (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hinitial :
      C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * eta) -
            (wooleyTriangular k : ℝ) * theta) ≤
        wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          1 theta theta nu Lambda gamma)
    (hchain : WooleyIterationChain k p Lambda D delta theta
      (fun r a b => wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu Lambda gamma)
      (wooleyIterationLength (wooleyTriangular k) k Lambda)
      theta theta 1)
    (hterminalZero : ∀ r a b : ℕ, 1 ≤ r → r ≤ k - 1 →
      max a b ≤ k ^
        (2 * wooleyIterationLength (wooleyTriangular k) k Lambda + 1) * theta →
      wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          r a b nu 0 gamma ≤
        Cterm * (p : ℝ) ^
          (((H : ℝ) * (Lambda + epsilon)) *
            wooleyNormalizationExponent k r))
    (hHeta : (H : ℝ) * eta ≤ theta)
    (hHepsilon : (H : ℝ) * epsilon ≤ theta)
    (hconstants : C0 * D ^
        (wooleyIterationLength (wooleyTriangular k) k Lambda) *
        max 1 Cterm ≤ (p : ℝ) ^ theta) : False := by
  let K : ℕ → ℕ → ℕ → ℝ := fun r a b =>
    wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
      r a b nu Lambda gamma
  have hKnonneg : ∀ r a b, 0 ≤ K r a b := by
    intro r a b
    exact wooleySourceNormalizedMixedMean_nonneg
      phi p B H (wooleyTriangular k) r a b nu Lambda gamma
  obtain ⟨aFinal, bFinal, rFinal, R, Cacc, E,
    haFinal, hbFinal, hrelFinal, hrFinal, hrFinalTop,
    hRpos, hRone, hweighted, hscale, hCacc, hCaccUpper,
    hE, hiterated⟩ := WooleyIterationChain.composed_bound
      hp hD hKnonneg (by simpa only [K] using hchain)
  have hterminal : K rFinal aFinal bFinal ≤
      Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon) := by
    have haScale : aFinal ≤ k * bFinal := by
      calc
        aFinal ≤ rFinal * aFinal :=
          Nat.le_mul_of_pos_left aFinal (by omega)
        _ ≤ (k - rFinal + 1) * bFinal := hrelFinal
        _ ≤ k * bFinal := Nat.mul_le_mul_right bFinal (by omega)
    have hbScale : bFinal ≤ k ^
        (2 * wooleyIterationLength (wooleyTriangular k) k Lambda + 1) *
          theta := by
      calc
        bFinal ≤ k ^
            (2 * wooleyIterationLength (wooleyTriangular k) k Lambda) *
              theta := hscale
        _ ≤ k ^
            (2 * wooleyIterationLength (wooleyTriangular k) k Lambda + 1) *
              theta := by
          apply Nat.mul_le_mul_right theta
          rw [pow_succ]
          exact Nat.le_mul_of_pos_right _ (by omega)
    have haScale' : aFinal ≤ k ^
        (2 * wooleyIterationLength (wooleyTriangular k) k Lambda + 1) *
          theta := by
      calc
        aFinal ≤ k * bFinal := haScale
        _ ≤ k * (k ^
            (2 * wooleyIterationLength (wooleyTriangular k) k Lambda) *
              theta) := Nat.mul_le_mul_left k hscale
        _ = k ^
            (2 * wooleyIterationLength (wooleyTriangular k) k Lambda + 1) *
              theta := by rw [pow_succ']; ring
    exact wooleySourceNormalizedMixedMean_terminal
      phi p B H rFinal aFinal bFinal nu Lambda epsilon Cterm gamma
        hp hrFinal (by omega) hepsilon hCterm
        (hterminalZero rFinal aFinal bFinal hrFinal hrFinalTop
          (max_le haScale' hbScale))
  exact wooley_section10_bounds_contradict_twoLoss
    hp (by omega) (show 1 ≤ wooleyTriangular k by
      exact (show 1 ≤ wooleyTriangular 1 by simp [wooleyTriangular]).trans
        (wooleyTriangular_mono (by omega)))
    htheta hLambda heta hD hC0 hCterm
    (hKnonneg rFinal aFinal bFinal) hRpos.le hRone
    (by simpa only [K] using hinitial) hiterated hCaccUpper hE
    hterminal hHeta hHepsilon hconstants

#print axioms wooley_section10_force_final_bound_twoLoss
#print axioms wooley_section10_bounds_contradict_twoLoss
#print axioms wooleySourcePolynomial_iterationChain_contradict_twoLoss

end

end GafniTao
