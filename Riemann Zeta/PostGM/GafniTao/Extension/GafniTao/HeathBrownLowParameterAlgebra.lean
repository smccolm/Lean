import GafniTao.HeathBrownLowParameterDefinitions

/-!
# Verification of the explicit low-cell parameter hierarchy

Every inequality in this file concerns the single parameter choice from
`HeathBrownLowParameterDefinitions`.  These lemmas are used by the source
consumer; they are not an abstract certificate replacing that consumer.
-/

namespace GafniTao

noncomputable section

theorem heathBrownTuneGap_pos
    {sigma : Real} (hsigma : 1 / 2 < sigma) :
    0 < heathBrownTuneGap sigma := by
  unfold heathBrownTuneGap
  linarith

theorem heathBrownTuneGap_le_quarter
    {sigma : Real} (hsigmaUpper : sigma <= 3 / 4) :
    heathBrownTuneGap sigma <= 1 / 4 := by
  unfold heathBrownTuneGap
  linarith

theorem heathBrownTuneDelta1_pos
    {sigma : Real} (hsigma : 1 / 2 < sigma) :
    0 < heathBrownTuneDelta1 sigma := by
  unfold heathBrownTuneDelta1
  exact div_pos (heathBrownTuneGap_pos hsigma) (by norm_num)

theorem heathBrownTuneD_pos
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    0 < heathBrownTuneD sigma epsilon := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  have hg := heathBrownTuneGap_pos hsigma
  unfold heathBrownTuneD
  exact div_pos (mul_pos hq hg) (by norm_num)

theorem heathBrownTuneDelta2_pos
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    0 < heathBrownTuneDelta2 sigma epsilon := by
  unfold heathBrownTuneDelta2
  exact div_pos (heathBrownTuneD_pos hsigma hepsilon) (by norm_num)

theorem heathBrownTuneD_le_gap_div_thousand
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    heathBrownTuneD sigma epsilon <= heathBrownTuneGap sigma / 1000 := by
  have hgap := heathBrownTuneGap_pos hsigma
  have hq := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  unfold heathBrownTuneD
  nlinarith

theorem heathBrownTuneDelta2_le_d
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    heathBrownTuneDelta2 sigma epsilon <= heathBrownTuneD sigma epsilon := by
  have hd := heathBrownTuneD_pos hsigma hepsilon
  unfold heathBrownTuneDelta2
  linarith

theorem heathBrownTuneDelta2_le_one
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneDelta2 sigma epsilon <= 1 := by
  have hd := heathBrownTuneD_le_gap_div_thousand
    (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
  have hg := heathBrownTuneGap_le_quarter hsigmaUpper
  have hd2 := heathBrownTuneDelta2_le_d hsigma hepsilon
  linarith

theorem heathBrownTuneDelta2_half_le_delta1
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneDelta2 sigma epsilon / 2 <=
      heathBrownTuneDelta1 sigma := by
  have hd := heathBrownTuneD_le_gap_div_thousand
    (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
  have hd2 := heathBrownTuneDelta2_le_d hsigma hepsilon
  have hg := heathBrownTuneGap_pos hsigma
  unfold heathBrownTuneDelta1
  linarith

theorem heathBrownTuneCube
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    3 * (heathBrownTuneDelta1 sigma +
      heathBrownTuneDelta2 sigma epsilon / 2) <= 1 := by
  have hg := heathBrownTuneGap_le_quarter hsigmaUpper
  have hd := heathBrownTuneD_le_gap_div_thousand
    (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
  have hd2 := heathBrownTuneDelta2_le_d hsigma hepsilon
  unfold heathBrownTuneDelta1
  linarith

theorem heathBrownTuneSigma0_lower
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma) :
    1 / 2 <= heathBrownTuneSigma0 sigma epsilon := by
  have hq := heathBrownTuneQ_le_gap (sigma := sigma) (epsilon := epsilon)
  have hg := heathBrownTuneGap_pos hsigma
  unfold heathBrownTuneSigma0 heathBrownTuneGap at *
  nlinarith

theorem heathBrownTuneSigma0_le_sigma
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    heathBrownTuneSigma0 sigma epsilon <= sigma := by
  have hq := (heathBrownTuneQ_pos hsigma hepsilon).le
  unfold heathBrownTuneSigma0
  linarith

theorem heathBrownTuneSigma0_upper
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneSigma0 sigma epsilon <= 3 / 4 :=
  (heathBrownTuneSigma0_le_sigma hsigma hepsilon).trans hsigmaUpper

theorem heathBrownTuneDelta2_lt_gap
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneDelta2 sigma epsilon < heathBrownTuneGap sigma := by
  have hg := heathBrownTuneGap_pos hsigma
  have hd := heathBrownTuneD_le_gap_div_thousand
    (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
  have hd2 := heathBrownTuneDelta2_le_d hsigma hepsilon
  linarith

theorem heathBrownTuneScale_pos
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    0 < heathBrownTuneScale sigma epsilon := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  unfold heathBrownTuneScale
  linarith

theorem heathBrownTuneScale_lt_two_thirds
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    heathBrownTuneScale sigma epsilon < 2 / 3 := by
  have hq := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  unfold heathBrownTuneScale
  linarith

theorem heathBrownTune_rel_margin
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    heathBrownTuneDetectorEpsilon sigma epsilon <
      (2 / 3 : Real) * heathBrownTuneRel sigma epsilon := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  unfold heathBrownTuneDetectorEpsilon heathBrownTuneRel
  linarith

theorem heathBrownTune_wide_rel_margin
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneDetectorEpsilon sigma epsilon <
      (1 - heathBrownTuneScale sigma epsilon) *
        heathBrownTuneRel sigma epsilon := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  have hqOne := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  unfold heathBrownTuneDetectorEpsilon heathBrownTuneScale heathBrownTuneRel
  nlinarith

theorem heathBrownTune_scale_near
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    3 * heathBrownTuneScale sigma epsilon <=
      1 - heathBrownTuneSigma0 sigma epsilon := by
  have hqOne := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  unfold heathBrownTuneScale heathBrownTuneSigma0
  nlinarith

theorem heathBrownTune_lower_effective_eq
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma) :
    heathBrownLowerSourceEffectiveSigma sigma
        (heathBrownTuneDelta2 sigma epsilon)
        (heathBrownTuneEta sigma epsilon)
        (heathBrownTuneLog sigma epsilon)
        (heathBrownTunePower sigma epsilon)
        (heathBrownTuneDil sigma epsilon)
        (heathBrownTuneDelta1 sigma) =
      sigma - (9 / 125 : Real) * heathBrownTuneQ sigma epsilon := by
  have hg := heathBrownTuneGap_pos hsigma
  unfold heathBrownLowerSourceEffectiveSigma heathBrownTuneDelta2
    heathBrownTuneD heathBrownTuneEta heathBrownTuneLog heathBrownTunePower
    heathBrownTuneDil heathBrownTuneDelta1
  field_simp [hg.ne']
  ring

theorem heathBrownTune_sigma0_le_lower_effective
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    heathBrownTuneSigma0 sigma epsilon <=
      heathBrownLowerSourceEffectiveSigma sigma
        (heathBrownTuneDelta2 sigma epsilon)
        (heathBrownTuneEta sigma epsilon)
        (heathBrownTuneLog sigma epsilon)
        (heathBrownTunePower sigma epsilon)
        (heathBrownTuneDil sigma epsilon)
        (heathBrownTuneDelta1 sigma) := by
  rw [heathBrownTune_lower_effective_eq hsigma]
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  unfold heathBrownTuneSigma0
  linarith

theorem heathBrownTune_sigma0_le_wide_effective
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneSigma0 sigma epsilon <=
      heathBrownWideSourceEffectiveSigma sigma
        (heathBrownTuneDelta2 sigma epsilon)
        (heathBrownTuneEta sigma epsilon)
        (heathBrownTuneLog sigma epsilon)
        (heathBrownTunePower sigma epsilon)
        (heathBrownTuneScale sigma epsilon)
        (heathBrownTuneDil sigma epsilon) := by
  let q := heathBrownTuneQ sigma epsilon
  let g := heathBrownTuneGap sigma
  have hq : 0 < q := heathBrownTuneQ_pos hsigma hepsilon
  have hqOne : q <= 1 := heathBrownTuneQ_le_one hsigmaUpper
  have hg : 0 < g := heathBrownTuneGap_pos hsigma
  have hgQuarter : g <= 1 / 4 := heathBrownTuneGap_le_quarter hsigmaUpper
  have hden : 0 < 1 - q / 100 := by linarith
  have hnum :
      heathBrownTuneDelta2 sigma epsilon +
          heathBrownTuneLog sigma epsilon +
          heathBrownTunePower sigma epsilon =
        21 * q * g / 1000000 := by
    dsimp only [q, g]
    unfold heathBrownTuneDelta2 heathBrownTuneD heathBrownTuneLog
      heathBrownTunePower heathBrownTuneDelta1
    ring
  have hfrac :
      (heathBrownTuneDelta2 sigma epsilon +
          heathBrownTuneLog sigma epsilon +
          heathBrownTunePower sigma epsilon) /
          (1 - heathBrownTuneScale sigma epsilon) <= q / 100 := by
    rw [hnum]
    dsimp only [q] at hden ⊢
    unfold heathBrownTuneScale
    rw [div_le_iff₀ hden]
    nlinarith
  unfold heathBrownTuneSigma0 heathBrownWideSourceEffectiveSigma
    heathBrownTuneEta heathBrownTuneDil
  dsimp only [q] at hfrac ⊢
  linarith

theorem heathBrownTune_typeII_effective_between
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    1 / 2 <=
        heathBrownEffectiveSigma sigma
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneShell sigma epsilon)
          (heathBrownTuneConst sigma epsilon)
          (Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon) + 1) -
            heathBrownTuneDil sigma epsilon ∧
      heathBrownTuneSigma0 sigma epsilon <=
        heathBrownEffectiveSigma sigma
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneShell sigma epsilon)
          (heathBrownTuneConst sigma epsilon)
          (Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon) + 1) -
            heathBrownTuneDil sigma epsilon ∧
      heathBrownEffectiveSigma sigma
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneShell sigma epsilon)
          (heathBrownTuneConst sigma epsilon)
          (Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon) + 1) -
            heathBrownTuneDil sigma epsilon <= sigma := by
  let q := heathBrownTuneQ sigma epsilon
  let delta2 := heathBrownTuneDelta2 sigma epsilon
  have hq : 0 < q := heathBrownTuneQ_pos hsigma hepsilon
  have hdelta2 : delta2 <= 1 := heathBrownTuneDelta2_le_one
    hsigma hsigmaUpper hepsilon
  have hshell := heathBrownTune_shell_mul_power_succ sigma epsilon
  dsimp only [heathBrownTuneP] at hshell
  have hshellBound :
      heathBrownTuneShell sigma epsilon *
          (((Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon) + 1 : Nat) : Real)) <=
        q / 100 := by
    rw [hshell]
    dsimp only [q, delta2] at hdelta2 ⊢
    nlinarith
  have hsigma0Lower := heathBrownTuneSigma0_lower (epsilon := epsilon) hsigma
  have hshellPos : 0 < heathBrownTuneShell sigma epsilon := by
    unfold heathBrownTuneShell
    have hdelta2Pos := heathBrownTuneDelta2_pos hsigma hepsilon
    positivity
  constructor
  · unfold heathBrownEffectiveSigma heathBrownTuneEta heathBrownTuneConst
      heathBrownTuneDil heathBrownTuneSigma0 at *
    dsimp only [q] at hshellBound ⊢
    nlinarith
  · constructor
    · unfold heathBrownEffectiveSigma heathBrownTuneEta heathBrownTuneConst
        heathBrownTuneDil heathBrownTuneSigma0
      dsimp only [q] at hshellBound ⊢
      nlinarith
    · unfold heathBrownEffectiveSigma heathBrownTuneEta heathBrownTuneConst
        heathBrownTuneDil
      nlinarith

theorem heathBrownTune_shell_le_delta2_div_hundred
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownTuneShell sigma epsilon <=
      heathBrownTuneDelta2 sigma epsilon / 100 := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  have hqOne := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  have hd2 := heathBrownTuneDelta2_pos hsigma hepsilon
  have hshell := heathBrownTune_shell_mul_power_succ sigma epsilon
  have hshellPos : 0 < heathBrownTuneShell sigma epsilon := by
    unfold heathBrownTuneShell
    positivity
  have hcast : (1 : Real) <=
      ((heathBrownTuneP sigma epsilon + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hfirst : heathBrownTuneShell sigma epsilon <=
      heathBrownTuneQ sigma epsilon *
        heathBrownTuneDelta2 sigma epsilon / 100 := by
    nlinarith
  nlinarith

theorem heathBrownTune_reflected_budget
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    let g := (sigma - 1 / 2) / 2
    let Uscale := 2 / g
    let beta := reflectedPhysicalBeta (heathBrownTuneD sigma epsilon)
    heathBrownTuneDelta2 sigma epsilon +
          heathBrownTuneD sigma epsilon * (2 * sigma + 1) +
          beta * heathBrownTuneShell sigma epsilon +
          heathBrownTuneReflect sigma epsilon <=
      (heathBrownTuneLoss sigma epsilon +
          heathBrownTuneEta sigma epsilon) / Uscale := by
  let q := heathBrownTuneQ sigma epsilon
  let gap := heathBrownTuneGap sigma
  let d := heathBrownTuneD sigma epsilon
  let delta2 := heathBrownTuneDelta2 sigma epsilon
  let shell := heathBrownTuneShell sigma epsilon
  have hq : 0 < q := heathBrownTuneQ_pos hsigma hepsilon
  have hqOne : q <= 1 := heathBrownTuneQ_le_one hsigmaUpper
  have hgap : 0 < gap := heathBrownTuneGap_pos hsigma
  have hgapQuarter : gap <= 1 / 4 := heathBrownTuneGap_le_quarter hsigmaUpper
  have hd : 0 < d := heathBrownTuneD_pos hsigma hepsilon
  have hdOne : d <= 1 := by
    have := heathBrownTuneD_le_gap_div_thousand
      (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
    linarith
  have hdelta2 : 0 < delta2 := heathBrownTuneDelta2_pos hsigma hepsilon
  have hshell : 0 < shell := by
    dsimp only [shell]
    unfold heathBrownTuneShell
    positivity
  have hshellUpper : shell <= delta2 / 100 :=
    heathBrownTune_shell_le_delta2_div_hundred hsigma hsigmaUpper hepsilon
  have hbetaShell :
      reflectedPhysicalBeta d * shell <= 3 * delta2 / 100 := by
    unfold reflectedPhysicalBeta
    nlinarith
  have hrhs :
      (heathBrownTuneLoss sigma epsilon +
          heathBrownTuneEta sigma epsilon) /
          (2 / ((sigma - 1 / 2) / 2)) = q * gap / 200 := by
    dsimp only [q, gap]
    unfold heathBrownTuneLoss heathBrownTuneEta heathBrownTuneGap
    field_simp [ne_of_gt (by linarith : 0 < sigma - 1 / 2)]
    ring
  dsimp only
  rw [hrhs]
  change delta2 + d * (2 * sigma + 1) +
      reflectedPhysicalBeta d * shell +
        heathBrownTuneReflect sigma epsilon <= q * gap / 200
  have hmain : d * (2 * sigma + 1) <= (5 / 2 : Real) * d := by
    nlinarith
  have hreflect : heathBrownTuneReflect sigma epsilon = d := by
    dsimp only [d]
    unfold heathBrownTuneReflect heathBrownTuneD
    rfl
  calc
    delta2 + d * (2 * sigma + 1) + reflectedPhysicalBeta d * shell +
          heathBrownTuneReflect sigma epsilon <=
        delta2 + (5 / 2 : Real) * d + 3 * delta2 / 100 + d := by
      rw [hreflect]
      linarith
    _ <= q * gap / 200 := by
      dsimp only [d, delta2, q, gap]
      unfold heathBrownTuneDelta2 heathBrownTuneD
      nlinarith

theorem heathBrownTune_sigma0_le_reflected_effective
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    let g := (sigma - 1 / 2) / 2
    let Uscale := 2 / g
    heathBrownTuneSigma0 sigma epsilon <=
      reflectedPhysicalEffectiveSigma sigma
        (heathBrownTuneLoss sigma epsilon)
        (heathBrownTuneEta sigma epsilon)
        (heathBrownTuneShell sigma epsilon)
        (heathBrownTunePower sigma epsilon)
        (heathBrownTuneDil sigma epsilon)
        (heathBrownTuneD sigma epsilon) Uscale := by
  let q := heathBrownTuneQ sigma epsilon
  let gap := heathBrownTuneGap sigma
  let d := heathBrownTuneD sigma epsilon
  let beta := reflectedPhysicalBeta d
  let alpha := gap / (4 * beta)
  have hq : 0 < q := heathBrownTuneQ_pos hsigma hepsilon
  have hgap : 0 < gap := heathBrownTuneGap_pos hsigma
  have hd : 0 < d := heathBrownTuneD_pos hsigma hepsilon
  have hdOne : d <= 1 := by
    have hdBound := heathBrownTuneD_le_gap_div_thousand
      (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
    have hgBound := heathBrownTuneGap_le_quarter hsigmaUpper
    linarith
  have hbeta : 0 < beta := by
    dsimp only [beta]
    unfold reflectedPhysicalBeta
    linarith
  have hbetaUpper : beta <= 3 := by
    dsimp only [beta]
    unfold reflectedPhysicalBeta
    linarith
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  have halphaLower : gap / 12 <= alpha := by
    dsimp only [alpha]
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 12)
      (mul_pos (by norm_num) hbeta)]
    nlinarith
  have hshellUpper := heathBrownTune_shell_le_delta2_div_hundred
    hsigma hsigmaUpper hepsilon
  have hsum :
      heathBrownTuneShell sigma epsilon +
          heathBrownTunePower sigma epsilon <= q * gap / 10000 := by
    dsimp only [q, gap] at hshellUpper ⊢
    unfold heathBrownTuneDelta2 heathBrownTuneD at hshellUpper
    unfold heathBrownTunePower heathBrownTuneDelta1
    nlinarith
  have hfrac :
      (heathBrownTuneShell sigma epsilon +
          heathBrownTunePower sigma epsilon) / alpha <= q / 100 := by
    rw [div_le_iff₀ halpha]
    nlinarith
  have halphaEq :
      reflectedPhysicalAlpha d
          (2 / ((sigma - 1 / 2) / 2)) = alpha := by
    dsimp only [alpha, gap, beta, d]
    unfold reflectedPhysicalAlpha heathBrownTuneGap
    field_simp [ne_of_gt (by linarith : 0 < sigma - 1 / 2),
      ne_of_gt hbeta]
    ring
  dsimp only
  unfold reflectedPhysicalEffectiveSigma heathBrownTuneSigma0
    heathBrownTuneLoss heathBrownTuneEta heathBrownTuneDil
  rw [halphaEq]
  dsimp only [q] at hfrac ⊢
  linarith

theorem heathBrownLowMaxSlope_le_three
    {sigma : Real} (hsigmaLower : 1 / 2 <= sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) <= 3 := by
  by_cases htransition : sigma <= 2 / 3
  · rw [heathBrown_low_max_eq_first htransition]
    have hden : 0 < 2 - sigma := by linarith
    unfold heathBrownLowFirstSlope
    rw [div_le_iff₀ hden]
    nlinarith
  · have htransition' : 2 / 3 <= sigma := by linarith
    rw [heathBrown_low_max_eq_second htransition' hsigmaUpper]
    have hden : 0 < 4 - 2 * sigma := by linarith
    unfold heathBrownLowSecondSlope
    rw [div_le_iff₀ hden]
    nlinarith

theorem heathBrownLowMaxSlope_nonneg
    {sigma : Real} (hsigmaUpper : sigma <= 3 / 4) :
    0 <= max (heathBrownLowFirstSlope sigma)
      (heathBrownLowSecondSlope sigma) := by
  have hden : 0 < 2 - sigma := by linarith
  unfold heathBrownLowFirstSlope
  exact (div_nonneg (by linarith) hden.le).trans (le_max_left _ _)

theorem heathBrownTune_low_cell_exponent_le_four
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    heathBrownLowCellExponent (heathBrownTuneSigma0 sigma epsilon)
        (heathBrownTuneRel sigma epsilon)
        (heathBrownTuneCard sigma epsilon) <= 4 := by
  have hqOne := heathBrownTuneQ_le_one (sigma := sigma) (epsilon := epsilon)
    hsigmaUpper
  have hmax := heathBrownLowMaxSlope_le_three
    (heathBrownTuneSigma0_lower (epsilon := epsilon) hsigma)
    (heathBrownTuneSigma0_upper hsigma hsigmaUpper hepsilon)
  unfold heathBrownLowCellExponent heathBrownTuneRel heathBrownTuneCard
    heathBrownCardinalityShift at *
  nlinarith

theorem heathBrownTune_physical_exponents_le
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) (hepsilon : 0 < epsilon) :
    max
        (heathBrownTypeIEnvelopeExponent
          (heathBrownTuneD sigma epsilon)
          (heathBrownTuneExtract sigma epsilon)
          (heathBrownTuneSigma0 sigma epsilon)
          (heathBrownTuneRel sigma epsilon)
          (heathBrownTuneCard sigma epsilon)
          (heathBrownTuneFixed sigma epsilon))
        (heathBrownTypeIIEnvelopeExponent sigma
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneShell sigma epsilon)
          (heathBrownTuneConst sigma epsilon)
          (heathBrownTuneDil sigma epsilon)
          (heathBrownTuneRel sigma epsilon)
          (heathBrownTuneCard sigma epsilon)
          (heathBrownTuneDelta2 sigma epsilon)
          (heathBrownTuneFixed sigma epsilon)) <=
      max (heathBrownLowFirstSlope sigma)
          (heathBrownLowSecondSlope sigma) + epsilon / 4 := by
  let q := heathBrownTuneQ sigma epsilon
  let sigma0 := heathBrownTuneSigma0 sigma epsilon
  let sigmaII := heathBrownEffectiveSigma sigma
    (heathBrownTuneEta sigma epsilon)
    (heathBrownTuneShell sigma epsilon)
    (heathBrownTuneConst sigma epsilon)
    (Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon) + 1) -
      heathBrownTuneDil sigma epsilon
  have hq : 0 < q := heathBrownTuneQ_pos hsigma hepsilon
  have hqEpsilon : q <= epsilon / 1000000 := heathBrownTuneQ_le_epsilon
  have hgapQuarter := heathBrownTuneGap_le_quarter hsigmaUpper
  have hdBound : heathBrownTuneD sigma epsilon <= q / 4000 := by
    dsimp only [q]
    unfold heathBrownTuneD
    nlinarith
  have hcell := heathBrownTune_low_cell_exponent_le_four
    hsigma hsigmaUpper hepsilon
  have hII := heathBrownTune_typeII_effective_between
    hsigma hsigmaUpper hepsilon
  have hsigma0Lower := heathBrownTuneSigma0_lower (epsilon := epsilon) hsigma
  have hsigma0Order := heathBrownTuneSigma0_le_sigma hsigma hepsilon
  have hTypeIReserve :
      7 * (sigma - sigma0) +
          4 * (heathBrownTuneRel sigma epsilon +
            heathBrownCardinalityShift (heathBrownTuneCard sigma epsilon)) +
          heathBrownTuneFixed sigma epsilon <= epsilon / 4 := by
    dsimp only [sigma0, q]
    unfold heathBrownTuneSigma0 heathBrownTuneRel heathBrownTuneCard
      heathBrownCardinalityShift heathBrownTuneFixed
    nlinarith
  have hReflectedReserve :
      heathBrownTuneExtract sigma epsilon +
          2 * heathBrownTuneD sigma epsilon *
            heathBrownLowCellExponent sigma0
              (heathBrownTuneRel sigma epsilon)
              (heathBrownTuneCard sigma epsilon) +
          7 * (sigma - sigma0) +
          4 * (heathBrownTuneRel sigma epsilon +
            heathBrownCardinalityShift (heathBrownTuneCard sigma epsilon)) +
          heathBrownTuneFixed sigma epsilon <= epsilon / 4 := by
    have hmul :
        heathBrownTuneD sigma epsilon *
            heathBrownLowCellExponent (heathBrownTuneSigma0 sigma epsilon)
              (heathBrownTuneRel sigma epsilon)
              (heathBrownTuneCard sigma epsilon) <=
          heathBrownTuneD sigma epsilon * 4 :=
      mul_le_mul_of_nonneg_left hcell
        (heathBrownTuneD_pos hsigma hepsilon).le
    dsimp only [sigma0] at hcell ⊢
    unfold heathBrownTuneExtract heathBrownTuneSigma0 heathBrownTuneRel
      heathBrownTuneCard heathBrownCardinalityShift heathBrownTuneFixed
    dsimp only [q] at hdBound hqEpsilon ⊢
    unfold heathBrownTuneSigma0 heathBrownTuneRel heathBrownTuneCard at hmul
    nlinarith
  have hTypeIIReserve :
      7 * (sigma - sigmaII) +
          4 * (heathBrownTuneRel sigma epsilon +
            heathBrownCardinalityShift (heathBrownTuneCard sigma epsilon)) +
          heathBrownTuneFixed sigma epsilon <= epsilon / 4 := by
    have hsigmaIIDiff : sigma - sigmaII <= q := by
      dsimp only [sigmaII, q]
      have hlower := hII.2.1
      unfold heathBrownTuneSigma0 at hlower
      linarith
    unfold heathBrownTuneRel heathBrownTuneCard heathBrownCardinalityShift
      heathBrownTuneFixed
    dsimp only [q] at hsigmaIIDiff hqEpsilon ⊢
    nlinarith
  exact heathBrown_physical_majorant_exponents_le hsigmaUpper
    hsigma0Lower hsigma0Order hTypeIReserve hReflectedReserve hII.1 hII.2.2
    hTypeIIReserve

#print axioms heathBrownTuneCube
#print axioms heathBrownTuneSigma0_lower
#print axioms heathBrownTune_sigma0_le_lower_effective
#print axioms heathBrownTune_typeII_effective_between
#print axioms heathBrownTune_reflected_budget
#print axioms heathBrownTune_sigma0_le_reflected_effective
#print axioms heathBrownTune_physical_exponents_le

end

end GafniTao
