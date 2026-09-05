import GafniTao.WooleySection10SeparatedHierarchy
import GafniTao.WooleySection9Admissible
import GafniTao.WooleyExponent

/-!
# Completion of Wooley's Section 10 contradiction

This file closes the critical-exponent argument.  The loss used to obtain an
actual below-critical counterexample is kept distinct from the smaller loss
used in the iteration, so the order of quantifiers in the operational
critical exponent is respected.
-/

namespace GafniTao

noncomputable section

set_option maxHeartbeats 4000000 in
/-- Assuming Corollary 3.2 in every smaller positive degree, the critical
exponent at degree `k >= 2` vanishes.  This is the source induction step
proved by Sections 6--10. -/
theorem wooleyCriticalExponent_eq_zero_of_lower
    {k p : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hlower : ∀ r, 1 ≤ r → r < k → WooleyPolynomialCorollary32At r p) :
    wooleyCriticalExponent k p = 0 := by
  let Lambda : ℝ := wooleyCriticalExponent k p
  have hLambda0 : 0 ≤ Lambda := by
    simpa only [Lambda] using wooleyCriticalExponent_nonneg (k := k) (p := p) (by omega)
  apply le_antisymm ?_ hLambda0
  by_contra hnot
  have hLambda : 0 < Lambda := lt_of_not_ge hnot
  let s : ℕ := wooleyTriangular k
  let N : ℕ := wooleyIterationLength s k Lambda
  obtain ⟨mu, delta, tauA, eta, epsilonA, Hhier,
      heta, hetaLambda, hepsilonA, hepsilonATau,
      htauALeOne, htauADelta, hdeltaMu, hmuOne,
      hdeltaScale, htauAScale, hetaMu, hepsilonAEta, hglobalA⟩ :=
    wooley_section10_separatedHierarchy_exists
      (k := k) (N := N) (Lambda := Lambda) (tau0 := (1 : ℝ))
        hk hLambda zero_lt_one
  obtain ⟨tauC, htauC, hcounterexamples⟩ :=
    wooley_arbitrarilyLarge_counterexamples
      (k := k) (p := p) heta (by simpa only [Lambda] using hetaLambda)
  let tau : ℝ := min tauA tauC
  have htauA0 : 0 < tauA := hepsilonA.trans hepsilonATau
  have htau : 0 < tau := by dsimp [tau]; exact lt_min htauA0 htauC
  have htauA : tau ≤ tauA := by dsimp [tau]; exact min_le_left _ _
  have htauC' : tau ≤ tauC := by dsimp [tau]; exact min_le_right _ _
  let epsilonCap : ℝ := min epsilonA tau
  let epsilon : ℝ := epsilonCap / 2
  have hepsilonCap : 0 < epsilonCap := by dsimp [epsilonCap]; positivity
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsilonLtCap : epsilon < epsilonCap := by dsimp [epsilon]; linarith
  have hepsilonA' : epsilon ≤ epsilonA :=
    hepsilonLtCap.le.trans (by dsimp [epsilonCap]; exact min_le_left _ _)
  have hepsilonTau : epsilon < tau :=
    hepsilonLtCap.trans_le (by dsimp [epsilonCap]; exact min_le_right _ _)
  have hepsilonEta : epsilon ≤ eta := hepsilonA'.trans hepsilonAEta
  have htauDelta : tau < delta := htauA.trans_lt htauADelta
  have hmu : 0 < mu := htau.trans (htauDelta.trans hdeltaMu)
  have htauScale : 4 * tau * (k : ℝ) ^ 2 ≤ 1 := by
    have hfac : 0 ≤ 4 * (k : ℝ) ^ 2 := by positivity
    have hle := mul_le_mul_of_nonneg_right htauA hfac
    nlinarith [htauAScale]
  have hglobal : ∀ H : ℕ, Hhier ≤ H →
      WooleySection10GlobalHierarchy k N H
        (wooleyIterationTheta mu H) (wooleyInitialNu eta Lambda H)
          Lambda delta tau epsilon := by
    intro H hH
    exact ((hglobalA H hH).mono_tau htauA).mono_epsilon
      hepsilon.le hepsilonA'
  obtain ⟨Csection, hCsection, Bsection, hsection7⟩ :=
    wooleySourcePolynomial_lemma_7_1_uniform_global hpPrime hkp hlower
      tau epsilon htau hepsilon
  have hdeltaHalf : delta ≤ 1 / 2 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hdelta0 : 0 ≤ delta := (htau.trans htauDelta).le
    nlinarith [sq_nonneg ((k : ℝ) - 2)]
  obtain ⟨Bupper, hupper⟩ :=
    wooleySourcePolynomial_lemma_4_1_coefficientOne_half
      hpPrime (by omega) hkp hepsilon (by linarith) htauDelta hdeltaHalf
  obtain ⟨Hsection, hHsection⟩ :=
    wooley_initialNu_eventually_ge heta hLambda Bsection
  obtain ⟨Hlarge, hHlarge⟩ :=
    wooley_initial_twoLoss_absorption_eventually
      (p := p) (s := s) hpPrime.one_lt (by linarith : 0 < eta + epsilon)
  let C0 : ℝ := 2 * 2 ^ (s - 1)
  let D : ℝ := Csection ^ ((2 * k : ℕ) : ℝ)
  let Ctotal : ℝ := C0 * D ^ N
  obtain ⟨Hconstant, hHconstant⟩ :=
    wooley_constant_le_prime_pow_iterationTheta_eventually
      hpPrime.one_lt hmu (C := Ctotal)
  obtain ⟨Btau, hBtau⟩ := exists_nat_ge (1 / tau)
  let Hrequired : ℕ := max Hhier (max Hsection (max Hlarge Hconstant))
  let Brequired : ℕ := max Bupper (max Btau (k * Hrequired))
  obtain ⟨B, phi, gamma, hB, hphiC, hgamma, hcounterRaw⟩ :=
    hcounterexamples 1 zero_lt_one Brequired
  let H : ℕ := B ⌈/⌉ k
  let thetaNat : ℕ := wooleyIterationTheta mu H
  let nu : ℕ := wooleyInitialNu eta Lambda H
  letI : NeZero (p ^ B) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hBupper : Bupper ≤ B :=
    (le_max_left _ _).trans hB
  have hBtau' : Btau ≤ B :=
    (le_max_left Btau (k * Hrequired)).trans
      ((le_max_right Bupper _).trans hB)
  have hkHrequired : k * Hrequired ≤ B :=
    (le_max_right Btau (k * Hrequired)).trans
      ((le_max_right Bupper _).trans hB)
  have hHrequired : Hrequired ≤ H :=
    wooley_le_ceilDiv_of_mul_le (by omega) hkHrequired
  have hHhier : Hhier ≤ H :=
    (le_max_left _ _).trans hHrequired
  have hHsection' : Hsection ≤ H :=
    (le_max_left Hsection (max Hlarge Hconstant)).trans
      ((le_max_right Hhier _).trans hHrequired)
  have hHlarge' : Hlarge ≤ H :=
    (le_max_left Hlarge Hconstant).trans
      ((le_max_right Hsection _).trans
        ((le_max_right Hhier _).trans hHrequired))
  have hHconstant' : Hconstant ≤ H :=
    (le_max_right Hlarge Hconstant).trans
      ((le_max_right Hsection _).trans
        ((le_max_right Hhier _).trans hHrequired))
  have hglobalNow : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon := by
    simpa only [thetaNat, nu] using hglobal H hHhier
  rcases hglobalNow with
    ⟨htheta, hnu, hnuTheta, hreserve, hnuScale,
      hcurrent, hsecond, hepsilonNode, hhierarchy⟩
  have hglobalNow' : WooleySection10GlobalHierarchy k N H thetaNat nu
      Lambda delta tau epsilon :=
    ⟨htheta, hnu, hnuTheta, hreserve, hnuScale,
      hcurrent, hsecond, hepsilonNode, hhierarchy⟩
  have hphysical := WooleySection10GlobalHierarchy.physical_scales
    (B := B) (by omega : 1 ≤ k) (by rfl : H = B ⌈/⌉ k) hglobalNow'
  have hphi : phi.InPhiTau p B tau := hphiC.mono htauC'
  obtain ⟨c, hspaced, hcscale⟩ := hphi
  have htauB : (1 : ℝ) ≤ tau * (B : ℝ) := by
    have hBtauReal : (Btau : ℝ) ≤ B := by exact_mod_cast hBtau'
    have hquot : 1 / tau ≤ (B : ℝ) := hBtau.trans hBtauReal
    rw [div_le_iff₀ htau] at hquot
    simpa only [one_mul, mul_comm] using hquot
  have hc : 1 ≤ c := by
    have hcR : (1 : ℝ) ≤ c := htauB.trans hcscale
    exact_mod_cast hcR
  have hupperAll : ∀ h : ℕ,
      h ≤ k ^ (2 * N + 1) * thetaNat →
      wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ h) phi gamma ≤
        (p : ℝ) ^ (((H - h : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean (wooleyTriangular k)
            (p ^ B) (p ^ H) phi gamma := by
    intro h hh
    have hhalf : 2 * h ≤ H := by
      have htwice := Nat.mul_le_mul_left 2 hh
      omega
    have hu := hupper B phi gamma h hBupper
      (show phi.InPhiTau p B tau from ⟨c, hspaced, hcscale⟩) hgamma hhalf
    simpa only [H, Lambda,
      wooley_natPrimePower_rpow p (H - h)
        (wooleyCriticalExponent k p + epsilon) hpPrime.pos] using hu
  have hnuCap : nu ≤ k ^ (2 * N + 1) * thetaNat := by
    calc
      nu ≤ thetaNat := hnuTheta
      _ ≤ k ^ (2 * N + 1) * thetaNat :=
        Nat.le_mul_of_pos_left thetaNat
          (pow_pos (by omega : 0 < k) (2 * N + 1))
  have hupperNu := hupperAll nu hnuCap
  have hnuLower : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤ (nu : ℝ) := by
    simpa only [nu] using wooley_initialNu_twoLoss_lower
      (H := H) hLambda hepsilon.le hepsilonEta
  have hlargeNow : 2 * 2 ^ (wooleyTriangular k - 1) *
      (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) ≤ 1 := by
    simpa only [s] using hHlarge H hHlarge'
  have hcounter :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma <
        wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) phi gamma := by
    simpa only [one_mul, H, Lambda,
      wooley_natPrimePower_rpow p (B ⌈/⌉ k)
        (wooleyCriticalExponent k p - eta) hpPrime.pos] using hcounterRaw
  have hinitial := wooleySourceNormalizedMixedMean_initial_twoLoss
    phi gamma hpPrime.two_le hk hepsilon.le hLambda
      (by omega : nu ≤ B ⌈/⌉ k) hnuTheta
      (by simpa only [H] using hnuLower)
      (by simpa only [H] using hupperNu)
      (by simpa only [H] using hlargeNow)
      (by simpa only [H] using hcounter)
  have hscale : 0 < wooleySourceNormalizationScale phi p B H
      (wooleyTriangular k) Lambda gamma := by
    let U := wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) phi gamma
    let Z := wooleySourcePolynomialConditionedMean
      (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma
    have hleft0 : 0 ≤ (p : ℝ) ^ ((H : ℝ) * (Lambda - eta)) * Z := by
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (wooleySourcePolynomialConditionedMean_nonneg phi
          (wooleyTriangular k) (p ^ B) (p ^ H) gamma)
    have hUpos : 0 < U := lt_of_le_of_lt hleft0
      (by simpa only [U, Z] using hcounter)
    have h310 := wooleySourcePolynomial_equation_3_10
      (k := k) (p := p) (B := B) phi gamma (by omega)
    have hZ0 : 0 ≤ Z := by
      exact wooleySourcePolynomialConditionedMean_nonneg phi
        (wooleyTriangular k) (p ^ B) (p ^ H) gamma
    have hZpos : 0 < Z := lt_of_le_of_ne hZ0 (fun hz => by
      have h310' : U ≤ ((p ^ H : ℕ) : ℝ) ^ (wooleyTriangular k) * Z := by
        simpa only [U, Z, H] using h310
      rw [← hz, mul_zero] at h310'
      linarith)
    unfold wooleySourceNormalizationScale
    exact mul_pos (Real.rpow_pos_of_pos
      (by exact_mod_cast hpPrime.pos : (0 : ℝ) < p) _) hZpos
  have hLambdaLeS : Lambda ≤ (s : ℝ) := by
    simpa only [Lambda, s] using wooleyCriticalExponent_le_triangular
      (k := k) (p := p) (by omega)
  have hlossGlobal : epsilon * (H : ℝ) ≤ (s : ℝ) * (nu : ℝ) := by
    have hfour := wooley_initialNu_lower (epsilon := eta)
      (Lambda := Lambda) (H := H)
    have hLamNu : 4 * eta * (H : ℝ) ≤ Lambda * (nu : ℝ) := by
      rw [div_le_iff₀ hLambda] at hfour
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hfour
    have hH0 : (0 : ℝ) ≤ H := by positivity
    have hnu0 : (0 : ℝ) ≤ nu := by positivity
    nlinarith
  have hnodes := wooley_section10_nodes_of_globalHierarchy
    (B := B) hk hLambda htau.le (by rfl : H = B ⌈/⌉ k) hglobalNow'
  have hchain := wooleySourcePolynomial_iterationChain_of_hierarchy_ledger
    phi gamma Csection Lambda delta tau epsilon hpPrime hk hCsection
      hLambda (by exact_mod_cast htheta) (by linarith) hdeltaScale
      hnu (hHsection H hHsection') htau.le htauScale hlossGlobal
      hspaced hc hgamma hscale hupperAll hsection7 hnodes
  have hHeta : (H : ℝ) * eta ≤ (thetaNat : ℝ) :=
    wooley_H_mul_epsilon_le_iterationTheta hetaMu
  have hHepsilon : (H : ℝ) * epsilon ≤ (thetaNat : ℝ) :=
    wooley_H_mul_epsilon_le_iterationTheta (hepsilonEta.trans hetaMu)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact Real.one_le_rpow hCsection (by positivity)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hconstants : C0 * D ^
        (wooleyIterationLength (wooleyTriangular k) k Lambda) * max 1 (1 : ℝ) ≤
      (p : ℝ) ^ thetaNat := by
    have hcst := hHconstant H hHconstant'
    simpa only [Ctotal, N, s, max_self, mul_one] using hcst
  have hterminal : ∀ r a b : ℕ, 1 ≤ r → r ≤ k - 1 →
      max a b ≤ k ^ (2 * wooleyIterationLength
          (wooleyTriangular k) k Lambda + 1) * thetaNat →
      wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          r a b nu 0 gamma ≤
        (1 : ℝ) * (p : ℝ) ^
          (((H : ℝ) * (Lambda + epsilon)) *
            wooleyNormalizationExponent k r) := by
    intro r a b hr hrk hab
    have haCap : a ≤ k ^ (2 * N + 1) * thetaNat := by
      have := (le_max_left a b).trans hab
      simpa only [N, s] using this
    have hbCap : b ≤ k ^ (2 * N + 1) * thetaNat := by
      have := (le_max_right a b).trans hab
      simpa only [N, s] using this
    have haH : a ≤ H := haCap.trans hphysical.2
    have hbH : b ≤ H := hbCap.trans hphysical.2
    have ht := wooleySourcePolynomial_lemma_4_2_of_conditioned_bounds_with_constant
      phi p B H a b nu r Lambda epsilon 1 gamma hpPrime.two_le hr
        (by omega) haH hbH (by norm_num)
        (add_nonneg hLambda0 hepsilon.le)
        (by simpa using hupperAll a haCap)
        (by simpa using hupperAll b hbCap)
    simpa using ht
  exact wooleySourcePolynomial_iterationChain_contradict_twoLoss
    phi gamma hpPrime.two_le hk (by exact_mod_cast htheta) hLambda
      heta.le hepsilon.le hD hC0 (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [C0, H, thetaNat] using hinitial)
      (by simpa only [D, N, s] using hchain) hterminal hHeta hHepsilon hconstants

#print axioms wooleyCriticalExponent_eq_zero_of_lower

end

end GafniTao
