import GafniTao.WooleySection10TwoLossContradiction
import GafniTao.WooleySection10HierarchySelection

/-!
# Section 10 hierarchy after selection of the counterexample scale

This is the quantifier-order bridge missing from the informal hierarchy
notation.  A counterexample-spacing scale `tau0` is supplied first.  The
actual `tau` is decreased within that class, and only then is the still
smaller iteration loss selected.  The conditioning depth continues to use
the earlier loss `eta`.
-/

namespace GafniTao

noncomputable section

set_option maxHeartbeats 1000000 in
/-- A complete Section-10 hierarchy subordinate to an already selected
positive counterexample-spacing scale. -/
theorem wooley_section10_separatedHierarchy_exists
    {k N : ℕ} {Lambda tau0 : ℝ}
    (hk : 2 ≤ k) (hLambda : 0 < Lambda) (htau0 : 0 < tau0) :
    ∃ mu delta tau eta epsilon : ℝ, ∃ H0 : ℕ,
      0 < eta ∧ eta < Lambda ∧
      0 < epsilon ∧ epsilon < tau ∧ tau ≤ tau0 ∧
      tau < delta ∧ delta < mu ∧ mu < 1 ∧
      (k : ℝ) ^ 2 * delta ≤ 1 ∧
      4 * tau * (k : ℝ) ^ 2 ≤ 1 ∧
      eta ≤ mu ∧ epsilon ≤ eta ∧
      ∀ H : ℕ, H0 ≤ H →
        WooleySection10GlobalHierarchy k N H
          (wooleyIterationTheta mu H)
          (wooleyInitialNu eta Lambda H) Lambda delta tau epsilon := by
  obtain ⟨mu, delta, tauCap, eta, heta, hetaTauCap,
    htauCapDelta, hdeltaMu, hmuOne, hdeltaScale, htauCapScale,
    hetaMu, hscaleSlope, hnuThetaSlope, hnuScaleSlope,
    hcurrentCap, hsecondCap, hetaSlope, hhierarchySlope⟩ :=
      wooley_section10_slopeHierarchy_exists (N := N) hk hLambda
  let tau : ℝ := min tauCap (tau0 / 2)
  have htauCap : 0 < tauCap := lt_trans heta hetaTauCap
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauLeCap : tau ≤ tauCap := by dsimp [tau]; exact min_le_left _ _
  have htauLeTau0 : tau ≤ tau0 := by
    dsimp [tau]
    exact (min_le_right _ _).trans (by linarith)
  have htauDelta : tau < delta := htauLeCap.trans_lt htauCapDelta
  have hmu : 0 < mu := (htauDelta.trans hdeltaMu).trans' htau
  have hetaLambda : eta < Lambda := by
    have hraw : 4 * eta / Lambda < 1 := hnuThetaSlope.trans hmuOne
    rw [div_lt_one hLambda] at hraw
    linarith
  have htauScale : 4 * tau * (k : ℝ) ^ 2 ≤ 1 := by
    have hfactor : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left htauLeCap hfactor
    nlinarith [htauCapScale]
  have hcurrent :
      (tau * (k : ℝ) ^ (2 * N + 1)) * mu +
          (k : ℝ) * (4 * eta / Lambda) < delta * mu := by
    calc
      (tau * (k : ℝ) ^ (2 * N + 1)) * mu +
          (k : ℝ) * (4 * eta / Lambda) ≤
        (tauCap * (k : ℝ) ^ (2 * N + 1)) * mu +
          (k : ℝ) * (4 * eta / Lambda) := by
            gcongr
      _ < delta * mu := hcurrentCap
  have hsecond :
      (tau * (k : ℝ) ^ (2 * N + 2)) * mu +
          (k : ℝ) * (4 * eta / Lambda) <
        ((k : ℝ) ^ 2 * delta) * mu := by
    calc
      (tau * (k : ℝ) ^ (2 * N + 2)) * mu +
          (k : ℝ) * (4 * eta / Lambda) ≤
        (tauCap * (k : ℝ) ^ (2 * N + 2)) * mu +
          (k : ℝ) * (4 * eta / Lambda) := by
            gcongr
      _ < ((k : ℝ) ^ 2 * delta) * mu := hsecondCap
  let epsilonCap : ℝ := min eta tau
  let epsilon : ℝ := epsilonCap / 2
  have hepsilonCap : 0 < epsilonCap := by dsimp [epsilonCap]; positivity
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsilonLtCap : epsilon < epsilonCap := by dsimp [epsilon]; linarith
  have hepsilonEta : epsilon ≤ eta :=
    hepsilonLtCap.le.trans (by dsimp [epsilonCap]; exact min_le_left _ _)
  have hepsilonTau : epsilon < tau :=
    hepsilonLtCap.trans_le (by dsimp [epsilonCap]; exact min_le_right _ _)
  obtain ⟨H0, hglobalEta⟩ := wooley_section10_globalHierarchy_eventually
    hk hLambda
    (lt_trans (lt_trans htau htauDelta) hdeltaMu)
    (lt_trans htau htauDelta).le htau.le heta
    hscaleSlope hnuThetaSlope hnuScaleSlope
    hcurrent hsecond hetaSlope hhierarchySlope
  refine ⟨mu, delta, tau, eta, epsilon, H0,
    heta, hetaLambda, hepsilon, hepsilonTau, htauLeTau0,
    htauDelta, hdeltaMu, hmuOne, hdeltaScale, htauScale,
    hetaMu, hepsilonEta, ?_⟩
  intro H hH
  exact (hglobalEta H hH).mono_epsilon hepsilon.le hepsilonEta

/-- The conditioning depth selected with `eta` controls the sum of the
counterexample and iteration losses needed by the two-loss Lemma 6.3. -/
theorem wooley_initialNu_twoLoss_lower
    {eta epsilon Lambda : ℝ} {H : ℕ}
    (hLambda : 0 < Lambda) (hepsilon : 0 ≤ epsilon)
    (hepsilonEta : epsilon ≤ eta) :
    2 * (eta + epsilon) * (H : ℝ) / Lambda ≤
      (wooleyInitialNu eta Lambda H : ℝ) := by
  have heta0 : 0 ≤ eta := hepsilon.trans hepsilonEta
  have hfour := wooley_initialNu_lower
    (epsilon := eta) (Lambda := Lambda) (H := H)
  have htwo : 2 * (eta + epsilon) * (H : ℝ) / Lambda ≤
      4 * eta * (H : ℝ) / Lambda := by
    have hH0 : (0 : ℝ) ≤ H := by positivity
    apply div_le_div_of_nonneg_right _ hLambda.le
    nlinarith
  exact htwo.trans hfour

/-- Every fixed natural threshold is eventually below the selected
iteration scale `ceil(mu H)`. -/
theorem wooley_iterationTheta_eventually_ge
    {mu : ℝ} (hmu : 0 < mu) (n : ℕ) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      n ≤ wooleyIterationTheta mu H := by
  obtain ⟨H0 : ℕ, hH0⟩ := exists_nat_ge ((n : ℝ) / mu)
  refine ⟨H0, ?_⟩
  intro H hH
  have hHreal : (H0 : ℝ) ≤ H := by exact_mod_cast hH
  have hn : (n : ℝ) ≤ mu * (H : ℝ) := by
    have := hH0.trans hHreal
    rw [div_le_iff₀ hmu] at this
    simpa only [mul_comm] using this
  have := hn.trans (wooley_iterationTheta_lower (mu := mu) (H := H))
  exact_mod_cast this

/-- Every fixed Section-7 starting threshold is eventually below the
conditioning depth `ceil(4 eta H/Lambda)`. -/
theorem wooley_initialNu_eventually_ge
    {eta Lambda : ℝ} (heta : 0 < eta) (hLambda : 0 < Lambda) (n : ℕ) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      n ≤ wooleyInitialNu eta Lambda H := by
  have hslope : 0 < 4 * eta / Lambda := by positivity
  obtain ⟨H0 : ℕ, hH0⟩ := exists_nat_ge ((n : ℝ) / (4 * eta / Lambda))
  refine ⟨H0, ?_⟩
  intro H hH
  have hHreal : (H0 : ℝ) ≤ H := by exact_mod_cast hH
  have hn : (n : ℝ) ≤ (4 * eta / Lambda) * (H : ℝ) := by
    have := hH0.trans hHreal
    rw [div_le_iff₀ hslope] at this
    simpa only [mul_comm] using this
  have hfour := wooley_initialNu_lower
    (epsilon := eta) (Lambda := Lambda) (H := H)
  have hrearrange : (4 * eta / Lambda) * (H : ℝ) =
      4 * eta * (H : ℝ) / Lambda := by field_simp
  rw [hrearrange] at hn
  exact_mod_cast hn.trans hfour

/-- A fixed source constant is absorbed by the initial two-loss contraction
once the terminal depth is sufficiently large. -/
theorem wooley_initial_twoLoss_absorption_eventually
    {p s : ℕ} (hp : 1 < p) {eta epsilon : ℝ}
    (htotal : 0 < eta + epsilon) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      2 * 2 ^ (s - 1) *
        (p : ℝ) ^ (-(eta + epsilon) * (H : ℝ)) ≤ 1 := by
  let C : ℝ := 2 * 2 ^ (s - 1)
  obtain ⟨H0, hH0⟩ := wooley_constant_le_primePower_rpow_eventually
    hp htotal (C := C)
  refine ⟨H0, ?_⟩
  intro H hH
  have hbound := hH0 H hH
  have hpPos : 0 < p := by omega
  have hpowerPos : 0 < (p : ℝ) ^ ((H : ℝ) * (eta + epsilon)) := by
    positivity
  have hbound' : C ≤ (p : ℝ) ^ ((H : ℝ) * (eta + epsilon)) := by
    simpa only [wooley_natPrimePower_rpow p H (eta + epsilon) hpPos] using hbound
  have hneg : -(eta + epsilon) * (H : ℝ) =
      -((H : ℝ) * (eta + epsilon)) := by ring
  dsimp only [C] at hbound' ⊢
  rw [hneg, Real.rpow_neg (by positivity : (0 : ℝ) ≤ p),
    ← div_eq_mul_inv, div_le_one hpowerPos]
  exact hbound'

/-- Any fixed positive constant is eventually absorbed by the integral
power at the selected iteration scale. -/
theorem wooley_constant_le_prime_pow_iterationTheta_eventually
    {p : ℕ} (hp : 1 < p) {mu C : ℝ} (hmu : 0 < mu) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      C ≤ (p : ℝ) ^ wooleyIterationTheta mu H := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hpReal).eventually
      (Filter.eventually_ge_atTop C))
  obtain ⟨H0, hH0⟩ := wooley_iterationTheta_eventually_ge hmu n0
  refine ⟨H0, ?_⟩
  intro H hH
  exact hn0 _ (hH0 H hH)

/-- A lower bound on `B` transfers to the terminal height
`H=ceil(B/k)`. -/
theorem wooley_le_ceilDiv_of_mul_le
    {k H0 B : ℕ} (hk : 1 ≤ k) (hB : k * H0 ≤ B) :
    H0 ≤ B ⌈/⌉ k := by
  have hBceil : B ≤ k * (B ⌈/⌉ k) :=
    le_smul_ceilDiv (by omega : 0 < k)
  exact Nat.le_of_mul_le_mul_left (hB.trans hBceil) (by omega)

#print axioms wooley_section10_separatedHierarchy_exists
#print axioms wooley_initialNu_twoLoss_lower
#print axioms wooley_iterationTheta_eventually_ge
#print axioms wooley_initialNu_eventually_ge
#print axioms wooley_initial_twoLoss_absorption_eventually
#print axioms wooley_constant_le_prime_pow_iterationTheta_eventually
#print axioms wooley_le_ceilDiv_of_mul_le

end

end GafniTao
