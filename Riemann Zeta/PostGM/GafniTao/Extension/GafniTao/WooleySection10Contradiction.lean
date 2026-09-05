import GafniTao.WooleySection10Initial
import GafniTao.WooleySection10Terminal
import GafniTao.WooleyIterationArithmetic

/-!
# The final numerical comparison in Wooley Section 10

The theorem below joins the initial normalized lower bound, the fully
composed iteration, and the terminal normalized upper bound.  All constants
are exposed until the single scale-absorption hypothesis used in the source.
-/

namespace GafniTao

noncomputable section

/-- The lower/iterated/terminal estimates force equation (10.10). -/
theorem wooley_section10_force_final_bound
    {p k s N theta H : ℕ}
    {Lambda epsilon D C0 Cterm Cacc E R K0 Kfinal : ℝ}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (htheta : 0 < theta) (hLambda : 0 < Lambda)
    (hepsilon : 0 ≤ epsilon) (hD : 1 ≤ D)
    (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hKfinal : 0 ≤ Kfinal)
    (hR : 0 ≤ R) (hRone : R ≤ 1)
    (hinitial :
      C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤ K0)
    (hiterated : K0 ≤ Cacc * Kfinal ^ R *
      (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))))
    (hCaccUpper : Cacc ≤ D ^ N)
    (hE : (N : ℝ) * theta ≤ E)
    (hterminal : Kfinal ≤ Cterm *
      (p : ℝ) ^ ((H : ℝ) * epsilon))
    (hHepsilon : (H : ℝ) * epsilon ≤ theta)
    (hconstants : C0 * D ^ N * max 1 Cterm ≤ (p : ℝ) ^ theta) :
    (N : ℝ) * Lambda / (2 * (k : ℝ)) ≤ 4 * (s : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := lt_trans (by norm_num) hpR
  have hbase : (1 : ℝ) ≤ p := hpR.le
  have hHepsilon0 : 0 ≤ (H : ℝ) * epsilon := by positivity
  have hCtermPow : Cterm ^ R ≤ max 1 Cterm := by
    rcases le_total Cterm 1 with hle | hle
    · exact (Real.rpow_le_one hCterm hle hR).trans (le_max_left 1 Cterm)
    · exact (Real.rpow_le_self_of_one_le hle hRone).trans
        (le_max_right 1 Cterm)
  have hterminalPow : Kfinal ^ R ≤
      max 1 Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon) := by
    have hpow := Real.rpow_le_rpow hKfinal hterminal hR
    have hproduct :
        (Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon)) ^ R =
          Cterm ^ R * (p : ℝ) ^ (((H : ℝ) * epsilon) * R) := by
      rw [Real.mul_rpow hCterm (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
    have hpowerExponent :
        (p : ℝ) ^ (((H : ℝ) * epsilon) * R) ≤
          (p : ℝ) ^ ((H : ℝ) * epsilon) :=
      Real.rpow_le_rpow_of_exponent_le hbase
        (mul_le_of_le_one_right hHepsilon0 hRone)
    calc
      Kfinal ^ R ≤
          (Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon)) ^ R := hpow
      _ = Cterm ^ R *
          (p : ℝ) ^ (((H : ℝ) * epsilon) * R) := hproduct
      _ ≤ max 1 Cterm *
          (p : ℝ) ^ ((H : ℝ) * epsilon) :=
        mul_le_mul hCtermPow hpowerExponent
          (Real.rpow_nonneg (by positivity) _) (le_trans (by norm_num) (le_max_left 1 Cterm))
  have htail :
      (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))) ≤
        (p : ℝ) ^
          (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have := mul_le_mul_of_nonneg_right hE hLambda.le
    have hdenK : 0 < (2 : ℝ) * k := mul_pos (by norm_num) hkR
    rw [div_le_div_iff₀ hdenK hdenK]
    nlinarith
  have hupper : K0 ≤
      D ^ N * max 1 Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon) *
        (p : ℝ) ^
          (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by
    calc
      K0 ≤ Cacc * Kfinal ^ R *
          (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))) := hiterated
      _ ≤ D ^ N *
          (max 1 Cterm * (p : ℝ) ^ ((H : ℝ) * epsilon)) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by
        gcongr
      _ = D ^ N * max 1 Cterm *
          (p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by ring
  have hcompare :
      (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤
        (p : ℝ) ^ theta *
          (p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by
    have hchain := hinitial.trans hupper
    have hC0nonneg : 0 ≤ C0 := hC0.le
    have hrest0 : 0 ≤ D ^ N * max 1 Cterm := by positivity
    have hmul := mul_le_mul_of_nonneg_left hchain hC0nonneg
    have hcancel : C0 * (C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta)) =
        (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) := by
      field_simp
    rw [hcancel] at hmul
    calc
      (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤
        C0 * (D ^ N * max 1 Cterm *
          (p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ)))) := hmul
      _ = (C0 * D ^ N * max 1 Cterm) *
          ((p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ)))) := by ring
      _ ≤ (p : ℝ) ^ theta *
          ((p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ)))) :=
        mul_le_mul_of_nonneg_right hconstants (by positivity)
      _ = (p : ℝ) ^ theta *
          (p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := by ring
  have hexponents :
      -((H : ℝ) * epsilon) - (s : ℝ) * theta ≤
        theta + (H : ℝ) * epsilon -
          (N : ℝ) * theta * Lambda / (2 * (k : ℝ)) := by
    apply (Real.strictMono_rpow_of_base_gt_one hpR).le_iff_le.mp
    calc
      (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤
        (p : ℝ) ^ theta *
          (p : ℝ) ^ ((H : ℝ) * epsilon) *
          (p : ℝ) ^
            (-((N : ℝ) * theta) * Lambda / (2 * (k : ℝ))) := hcompare
      _ = (p : ℝ) ^
          (theta + (H : ℝ) * epsilon -
            (N : ℝ) * theta * Lambda / (2 * (k : ℝ))) := by
        have hthetaPow : (p : ℝ) ^ theta =
            (p : ℝ) ^ (theta : ℝ) := by
          symm
          exact Real.rpow_natCast p theta
        rw [hthetaPow, ← Real.rpow_add hpPos, ← Real.rpow_add hpPos]
        congr 1
        ring
  have hthetaR : (0 : ℝ) < theta := by exact_mod_cast htheta
  have hraw :
      (N : ℝ) * theta * Lambda / (2 * (k : ℝ)) ≤
        ((s : ℝ) + 3) * theta := by
    nlinarith
  have hdivide :
      (N : ℝ) * Lambda / (2 * (k : ℝ)) ≤ (s : ℝ) + 3 := by
    have hfactored : (theta : ℝ) *
        ((N : ℝ) * Lambda / (2 * (k : ℝ))) ≤
          (theta : ℝ) * ((s : ℝ) + 3) := by
      convert hraw using 1 <;> ring
    exact le_of_mul_le_mul_left hfactored hthetaR
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- With Wooley's prescribed iteration length, the three estimates and the
single constant-absorption inequality are inconsistent. -/
theorem wooley_section10_bounds_contradict
    {p k s theta H : ℕ}
    {Lambda epsilon D C0 Cterm Cacc E R K0 Kfinal : ℝ}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (htheta : 0 < theta) (hLambda : 0 < Lambda)
    (hepsilon : 0 ≤ epsilon) (hD : 1 ≤ D)
    (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hKfinal : 0 ≤ Kfinal)
    (hR : 0 ≤ R) (hRone : R ≤ 1)
    (hinitial : C0⁻¹ * (p : ℝ) ^
      (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤ K0)
    (hiterated : K0 ≤ Cacc * Kfinal ^ R *
      (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))))
    (hCaccUpper : Cacc ≤ D ^ (wooleyIterationLength s k Lambda))
    (hE : (wooleyIterationLength s k Lambda : ℝ) * theta ≤ E)
    (hterminal : Kfinal ≤ Cterm *
      (p : ℝ) ^ ((H : ℝ) * epsilon))
    (hHepsilon : (H : ℝ) * epsilon ≤ theta)
    (hconstants : C0 * D ^ (wooleyIterationLength s k Lambda) *
      max 1 Cterm ≤ (p : ℝ) ^ theta) : False := by
  exact wooley_iteration_length_final_bound_impossible hs hk hLambda
    (wooley_section10_force_final_bound hp hk hs htheta hLambda
      hepsilon hD hC0 hCterm hKfinal hR hRone hinitial hiterated
      hCaccUpper hE hterminal hHepsilon hconstants)

/-- The actual iteration-chain consumer: it unpacks the endpoint selected by
the finite Lemma-9.3 recursion, applies the sharp terminal Lemma 4.2 estimate,
and feeds the resulting quantities to the numerical contradiction above. -/
theorem wooleySourcePolynomial_iterationChain_contradict
    {k p B H theta nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    {Lambda epsilon D C0 Cterm delta : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (htheta : 0 < theta)
    (hLambda : 0 < Lambda) (hepsilon : 0 ≤ epsilon)
    (hD : 1 ≤ D) (hC0 : 0 < C0) (hCterm : 0 ≤ Cterm)
    (hinitial :
      C0⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * epsilon) -
            (wooleyTriangular k : ℝ) * theta) ≤
        wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          1 theta theta nu Lambda gamma)
    (hchain : WooleyIterationChain k p Lambda D delta theta
      (fun r a b => wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu Lambda gamma)
      (wooleyIterationLength (wooleyTriangular k) k Lambda)
      theta theta 1)
    (hterminalZero : ∀ r a b : ℕ, 1 ≤ r → r ≤ k - 1 →
      wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          r a b nu 0 gamma ≤
        Cterm * (p : ℝ) ^
          (((H : ℝ) * (Lambda + epsilon)) *
            wooleyNormalizationExponent k r))
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
    exact wooleySourceNormalizedMixedMean_terminal
      phi p B H rFinal aFinal bFinal nu Lambda epsilon Cterm gamma
        hp hrFinal (by omega) hepsilon hCterm
        (hterminalZero rFinal aFinal bFinal hrFinal hrFinalTop)
  exact wooley_section10_bounds_contradict
    hp (by omega) (show 1 ≤ wooleyTriangular k by
      exact (show 1 ≤ wooleyTriangular 1 by simp [wooleyTriangular]).trans
        (wooleyTriangular_mono (by omega)))
    htheta hLambda hepsilon hD hC0 hCterm
    (hKnonneg rFinal aFinal bFinal) hRpos.le hRone
    (by simpa only [K] using hinitial)
    hiterated hCaccUpper hE hterminal hHepsilon hconstants

#print axioms wooley_section10_force_final_bound
#print axioms wooley_section10_bounds_contradict
#print axioms wooleySourcePolynomial_iterationChain_contradict

end

end GafniTao
