import GafniTao.HeathBrownFiniteMixedEnergy

/-!
# Finite power majorants for the Heath--Brown relation

This file proves the literal real-power inequalities whose logarithmic
exponents are the two maxima in Heath--Brown's equation (33).  The fourth
moment keeps the additive-energy exponent as an independent input; it is not
replaced by the elementary cubic cardinality bound.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The normalized exponent of the second-moment shape. -/
def heathBrownSecondExponent (tau rho : Real) : Real :=
  1 + max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2))

/-- The normalized exponent of the fourth-moment shape. -/
def heathBrownFourthExponent (tau rho rhoStar : Real) : Real :=
  1 + max (rhoStar + 1)
    (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))

private theorem sq_le_rpow_two_mul
    {x y a : Real} (hx : 0 <= x) (hy : 0 <= y) (hyx : y <= x ^ a) :
    y ^ 2 <= x ^ (2 * a) := by
  have hpow := pow_le_pow_left₀ hy hyx 2
  calc
    y ^ 2 <= (x ^ a) ^ 2 := hpow
    _ = x ^ (a * 2) := (Real.rpow_mul_natCast hx a 2).symm
    _ = x ^ (2 * a) := by ring_nf

private theorem rpow_le_rpow_of_le
    {x y a : Real} (hy : 0 <= y) (ha : 0 <= a) (hyx : y <= x) :
    y ^ a <= x ^ a :=
  Real.rpow_le_rpow hy hyx ha

/-- Each of the three second-moment terms is bounded at its exact source
exponent.  The outer factor `3` is retained rather than hidden in `X^epsilon`.
-/
theorem heathBrownSecondShape_le_three_rpow
    {x B R M tau rho : Real}
    (hx : 1 <= x) (hB : 0 <= B) (hR : 0 <= R) (hM : 0 <= M)
    (hBpow : B <= x ^ tau) (hRpow : R <= x ^ rho) (hMx : M <= x) :
    R ^ 2 * M + R * M ^ 2 +
        R ^ (5 / 4 : Real) * B ^ (1 / 2 : Real) * M <=
      3 * x ^ heathBrownSecondExponent tau rho := by
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hR2 : R ^ 2 <= x ^ (2 * rho) := sq_le_rpow_two_mul hx0 hR hRpow
  have hM2 : M ^ 2 <= x ^ (2 : Real) := by
    have hpow := pow_le_pow_left₀ hM hMx 2
    calc
      M ^ 2 <= x ^ (2 : Nat) := hpow
      _ = x ^ (2 : Real) := (Real.rpow_natCast x 2).symm
  have hR54 : R ^ (5 / 4 : Real) <= x ^ ((5 / 4 : Real) * rho) := by
    calc
      R ^ (5 / 4 : Real) <= (x ^ rho) ^ (5 / 4 : Real) :=
        rpow_le_rpow_of_le hR (by norm_num) hRpow
      _ = x ^ (rho * (5 / 4 : Real)) :=
        (Real.rpow_mul hx0 rho (5 / 4 : Real)).symm
      _ = x ^ ((5 / 4 : Real) * rho) := by ring_nf
  have hB12 : B ^ (1 / 2 : Real) <= x ^ ((1 / 2 : Real) * tau) := by
    calc
      B ^ (1 / 2 : Real) <= (x ^ tau) ^ (1 / 2 : Real) :=
        rpow_le_rpow_of_le hB (by norm_num) hBpow
      _ = x ^ (tau * (1 / 2 : Real)) :=
        (Real.rpow_mul hx0 tau (1 / 2 : Real)).symm
      _ = x ^ ((1 / 2 : Real) * tau) := by ring_nf
  have hTerm1 : R ^ 2 * M <= x ^ (2 * rho + 1) := by
    calc
      R ^ 2 * M <= x ^ (2 * rho) * x :=
        mul_le_mul hR2 hMx hM (Real.rpow_nonneg hx0 _)
      _ = x ^ (2 * rho + 1) := by
        simpa only [Real.rpow_one] using
          (Real.rpow_add hxpos (2 * rho) 1).symm
  have hTerm2 : R * M ^ 2 <= x ^ (rho + 2) := by
    calc
      R * M ^ 2 <= x ^ rho * x ^ (2 : Real) :=
        mul_le_mul hRpow hM2 (pow_nonneg hM 2) (Real.rpow_nonneg hx0 _)
      _ = x ^ (rho + 2) := (Real.rpow_add hxpos _ _).symm
  have hTerm3 : R ^ (5 / 4 : Real) * B ^ (1 / 2 : Real) * M <=
      x ^ (5 * rho / 4 + tau / 2 + 1) := by
    calc
      R ^ (5 / 4 : Real) * B ^ (1 / 2 : Real) * M <=
          x ^ ((5 / 4 : Real) * rho) * x ^ ((1 / 2 : Real) * tau) * x := by
        gcongr
      _ = x ^ (5 * rho / 4 + tau / 2 + 1) := by
        calc
          x ^ ((5 / 4 : Real) * rho) * x ^ ((1 / 2 : Real) * tau) * x =
              x ^ ((5 / 4 : Real) * rho + (1 / 2 : Real) * tau) * x := by
                rw [Real.rpow_add hxpos]
          _ = x ^ (((5 / 4 : Real) * rho + (1 / 2 : Real) * tau) + 1) := by
                simpa only [Real.rpow_one] using
                  (Real.rpow_add hxpos
                    ((5 / 4 : Real) * rho + (1 / 2 : Real) * tau) 1).symm
          _ = x ^ (5 * rho / 4 + tau / 2 + 1) := by
            apply congrArg (fun a : Real => x ^ a)
            ring
  let q := max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2))
  have h1 : 2 * rho + 1 <= 1 + q := by
    dsimp only [q]
    have hInner : 2 * rho <=
        max (2 * rho) (5 * rho / 4 + tau / 2) := le_max_left _ _
    have hOuter : 2 * rho <=
        max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) :=
      hInner.trans (le_max_right _ _)
    linarith
  have h2 : rho + 2 <= 1 + q := by
    dsimp only [q]
    linarith [le_max_left (rho + 1)
      (max (2 * rho) (5 * rho / 4 + tau / 2))]
  have h3 : 5 * rho / 4 + tau / 2 + 1 <= 1 + q := by
    dsimp only [q]
    have hInner : 5 * rho / 4 + tau / 2 <=
        max (2 * rho) (5 * rho / 4 + tau / 2) := le_max_right _ _
    have hOuter : 5 * rho / 4 + tau / 2 <=
        max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) :=
      hInner.trans (le_max_right _ _)
    linarith
  have hp1 : x ^ (2 * rho + 1) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h1
  have hp2 : x ^ (rho + 2) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h2
  have hp3 : x ^ (5 * rho / 4 + tau / 2 + 1) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h3
  dsimp only [heathBrownSecondExponent, q]
  nlinarith

/-- Fourth-moment analogue of `heathBrownSecondShape_le_three_rpow`.  The
input `E <= x^rhoStar` is the genuine self-referential energy bound.
-/
theorem heathBrownFourthShape_le_three_rpow
    {x B R E M tau rho rhoStar : Real}
    (hx : 1 <= x) (hB : 0 <= B) (hR : 0 <= R) (hE : 0 <= E)
    (hM : 0 <= M) (hBpow : B <= x ^ tau)
    (hRpow : R <= x ^ rho) (hEpow : E <= x ^ rhoStar) (hMx : M <= x) :
    R ^ 4 * M + E * M ^ 2 +
        E ^ (3 / 4 : Real) * R * B ^ (1 / 2 : Real) * M <=
      3 * x ^ heathBrownFourthExponent tau rho rhoStar := by
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hR4 : R ^ 4 <= x ^ (4 * rho) := by
    have hpow := pow_le_pow_left₀ hR hRpow 4
    calc
      R ^ 4 <= (x ^ rho) ^ 4 := hpow
      _ = x ^ (rho * 4) := (Real.rpow_mul_natCast hx0 rho 4).symm
      _ = x ^ (4 * rho) := by ring_nf
  have hM2 : M ^ 2 <= x ^ (2 : Real) := by
    have hpow := pow_le_pow_left₀ hM hMx 2
    calc
      M ^ 2 <= x ^ (2 : Nat) := hpow
      _ = x ^ (2 : Real) := (Real.rpow_natCast x 2).symm
  have hE34 : E ^ (3 / 4 : Real) <= x ^ ((3 / 4 : Real) * rhoStar) := by
    calc
      E ^ (3 / 4 : Real) <= (x ^ rhoStar) ^ (3 / 4 : Real) :=
        rpow_le_rpow_of_le hE (by norm_num) hEpow
      _ = x ^ (rhoStar * (3 / 4 : Real)) :=
        (Real.rpow_mul hx0 rhoStar (3 / 4 : Real)).symm
      _ = x ^ ((3 / 4 : Real) * rhoStar) := by ring_nf
  have hB12 : B ^ (1 / 2 : Real) <= x ^ ((1 / 2 : Real) * tau) := by
    calc
      B ^ (1 / 2 : Real) <= (x ^ tau) ^ (1 / 2 : Real) :=
        rpow_le_rpow_of_le hB (by norm_num) hBpow
      _ = x ^ (tau * (1 / 2 : Real)) :=
        (Real.rpow_mul hx0 tau (1 / 2 : Real)).symm
      _ = x ^ ((1 / 2 : Real) * tau) := by ring_nf
  have hTerm1 : R ^ 4 * M <= x ^ (4 * rho + 1) := by
    calc
      R ^ 4 * M <= x ^ (4 * rho) * x :=
        mul_le_mul hR4 hMx hM (Real.rpow_nonneg hx0 _)
      _ = x ^ (4 * rho + 1) := by
        simpa only [Real.rpow_one] using
          (Real.rpow_add hxpos (4 * rho) 1).symm
  have hTerm2 : E * M ^ 2 <= x ^ (rhoStar + 2) := by
    calc
      E * M ^ 2 <= x ^ rhoStar * x ^ (2 : Real) :=
        mul_le_mul hEpow hM2 (pow_nonneg hM 2) (Real.rpow_nonneg hx0 _)
      _ = x ^ (rhoStar + 2) := (Real.rpow_add hxpos _ _).symm
  have hTerm3 : E ^ (3 / 4 : Real) * R * B ^ (1 / 2 : Real) * M <=
      x ^ (3 * rhoStar / 4 + rho + tau / 2 + 1) := by
    calc
      E ^ (3 / 4 : Real) * R * B ^ (1 / 2 : Real) * M <=
          x ^ ((3 / 4 : Real) * rhoStar) * x ^ rho *
            x ^ ((1 / 2 : Real) * tau) * x := by
        gcongr
      _ = x ^ (3 * rhoStar / 4 + rho + tau / 2 + 1) := by
        calc
          x ^ ((3 / 4 : Real) * rhoStar) * x ^ rho *
                x ^ ((1 / 2 : Real) * tau) * x =
              x ^ ((3 / 4 : Real) * rhoStar + rho) *
                x ^ ((1 / 2 : Real) * tau) * x := by
                  rw [Real.rpow_add hxpos
                    ((3 / 4 : Real) * rhoStar) rho]
          _ = x ^ (((3 / 4 : Real) * rhoStar + rho) +
                (1 / 2 : Real) * tau) * x := by
                  rw [Real.rpow_add hxpos
                    ((3 / 4 : Real) * rhoStar + rho)
                    ((1 / 2 : Real) * tau)]
          _ = x ^ ((((3 / 4 : Real) * rhoStar + rho) +
                (1 / 2 : Real) * tau) + 1) := by
                  simpa only [Real.rpow_one] using
                    (Real.rpow_add hxpos
                      (((3 / 4 : Real) * rhoStar + rho) +
                        (1 / 2 : Real) * tau) 1).symm
          _ = x ^ (3 * rhoStar / 4 + rho + tau / 2 + 1) := by
                  apply congrArg (fun a : Real => x ^ a)
                  ring
  let q := max (rhoStar + 1)
    (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))
  have h1 : 4 * rho + 1 <= 1 + q := by
    dsimp only [q]
    have hInner : 4 * rho <=
        max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2) := le_max_left _ _
    have hOuter : 4 * rho <= max (rhoStar + 1)
        (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2)) :=
      hInner.trans (le_max_right _ _)
    linarith
  have h2 : rhoStar + 2 <= 1 + q := by
    dsimp only [q]
    linarith [le_max_left (rhoStar + 1)
      (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))]
  have h3 : 3 * rhoStar / 4 + rho + tau / 2 + 1 <= 1 + q := by
    dsimp only [q]
    have hInner : 3 * rhoStar / 4 + rho + tau / 2 <=
        max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2) := le_max_right _ _
    have hOuter : 3 * rhoStar / 4 + rho + tau / 2 <=
        max (rhoStar + 1)
          (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2)) :=
      hInner.trans (le_max_right _ _)
    linarith
  have hp1 : x ^ (4 * rho + 1) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h1
  have hp2 : x ^ (rhoStar + 2) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h2
  have hp3 : x ^ (3 * rhoStar / 4 + rho + tau / 2 + 1) <= x ^ (1 + q) :=
    Real.rpow_le_rpow_of_exponent_le hx h3
  dsimp only [heathBrownFourthExponent, q]
  nlinarith

private theorem sqrt_scaled_rpow
    {C B x epsilon q : Real} (hC : 0 <= C) (hB : 0 <= B)
    (hx : 0 <= x) :
    Real.sqrt (C * B ^ (epsilon / 2) * (3 * x ^ q)) =
      Real.sqrt (3 * C) * B ^ (epsilon / 4) * x ^ (q / 2) := by
  have hThreeC : 0 <= 3 * C := by positivity
  have hBpow : 0 <= B ^ (epsilon / 2) := Real.rpow_nonneg hB _
  calc
    Real.sqrt (C * B ^ (epsilon / 2) * (3 * x ^ q)) =
        Real.sqrt ((3 * C) * (B ^ (epsilon / 2) * x ^ q)) := by
          apply congrArg Real.sqrt
          ring
    _ = Real.sqrt (3 * C) *
        Real.sqrt (B ^ (epsilon / 2) * x ^ q) :=
          Real.sqrt_mul hThreeC _
    _ = Real.sqrt (3 * C) *
        (Real.sqrt (B ^ (epsilon / 2)) * Real.sqrt (x ^ q)) := by
          rw [Real.sqrt_mul hBpow]
    _ = Real.sqrt (3 * C) * B ^ (epsilon / 4) * x ^ (q / 2) := by
          simp only [Real.sqrt_eq_rpow]
          rw [<- Real.rpow_mul hB, <- Real.rpow_mul hx]
          have hepsilon : epsilon / 2 * (1 / 2 : Real) = epsilon / 4 := by
            ring
          have hq : q * (1 / 2 : Real) = q / 2 := by ring
          rw [hepsilon, hq]
          ring

/-- The exact finite family bound is controlled by equation (33)'s power.
All non-asymptotic constants and the complete `B^epsilon` loss remain
visible.  In particular, `rhoStar` enters through the genuine self-energy
hypothesis and is not replaced by a cubic cardinality estimate. -/
theorem heathBrownFiniteFamilyBound_le_relation_rpow
    {epsilon C0 C2 C4 B V x sigma tau rho rhoStar : Real}
    {M : Nat} {W : Finset Real}
    (hx : 1 <= x) (hB : 0 < B)
    (hC0 : 0 <= C0) (hC2 : 0 <= C2) (hC4 : 0 <= C4)
    (hBpow : B <= x ^ tau)
    (hCard : (W.card : Real) <= x ^ rho)
    (hEnergy : (ApproxAddEnergy 1 W : Real) <= x ^ rhoStar)
    (hM : (M : Real) <= x) (hThreshold : x ^ sigma <= V) :
    heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W <=
      (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon *
        x ^ (1 - 2 * sigma +
          (1 / 2 : Real) *
            max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
          (1 / 2 : Real) *
            max (rhoStar + 1)
              (max (4 * rho)
                (3 * rhoStar / 4 + rho + tau / 2))) := by
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hCard0 : 0 <= (W.card : Real) := Nat.cast_nonneg _
  have hEnergy0 : 0 <= (ApproxAddEnergy 1 W : Real) := Nat.cast_nonneg _
  have hM0 : 0 <= (M : Real) := Nat.cast_nonneg _
  have hSecond := heathBrownSecondShape_le_three_rpow
    hx hB.le hCard0 hM0 hBpow hCard hM
  have hFourth := heathBrownFourthShape_le_three_rpow
    hx hB.le hCard0 hEnergy0 hM0 hBpow hCard hEnergy hM
  have hSecondInside :
      C2 * B ^ (epsilon / 2) * heathBrownSecondMomentShape B M W <=
        C2 * B ^ (epsilon / 2) *
          (3 * x ^ heathBrownSecondExponent tau rho) := by
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg hC2 (Real.rpow_nonneg hB.le _))
    simpa only [heathBrownSecondMomentShape] using hSecond
  have hFourthInside :
      C4 * B ^ (epsilon / 2) * heathBrownFourthMomentShape B M W <=
        C4 * B ^ (epsilon / 2) *
          (3 * x ^ heathBrownFourthExponent tau rho rhoStar) := by
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg hC4 (Real.rpow_nonneg hB.le _))
    simpa only [heathBrownFourthMomentShape] using hFourth
  have hSecondSqrt := Real.sqrt_le_sqrt hSecondInside
  have hFourthSqrt := Real.sqrt_le_sqrt hFourthInside
  have hSecondSqrt' :
      Real.sqrt (C2 * B ^ (epsilon / 2) *
          heathBrownSecondMomentShape B M W) <=
        Real.sqrt (3 * C2) * B ^ (epsilon / 4) *
          x ^ (heathBrownSecondExponent tau rho / 2) := by
    rw [sqrt_scaled_rpow hC2 hB.le hx0] at hSecondSqrt
    exact hSecondSqrt
  have hFourthSqrt' :
      Real.sqrt (C4 * B ^ (epsilon / 2) *
          heathBrownFourthMomentShape B M W) <=
        Real.sqrt (3 * C4) * B ^ (epsilon / 4) *
          x ^ (heathBrownFourthExponent tau rho rhoStar / 2) := by
    rw [sqrt_scaled_rpow hC4 hB.le hx0] at hFourthSqrt
    exact hFourthSqrt
  have hOuter0 : 0 <= C0 * B ^ (epsilon / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg hB.le _)
  have hBcombine :
      B ^ (epsilon / 2) * B ^ (epsilon / 4) * B ^ (epsilon / 4) =
        B ^ epsilon := by
    rw [<- Real.rpow_add hB, <- Real.rpow_add hB]
    apply congrArg (fun a : Real => B ^ a)
    ring
  have hxcombine :
      x ^ (heathBrownSecondExponent tau rho / 2) *
          x ^ (heathBrownFourthExponent tau rho rhoStar / 2) =
        x ^ (heathBrownSecondExponent tau rho / 2 +
          heathBrownFourthExponent tau rho rhoStar / 2) :=
    (Real.rpow_add hxpos _ _).symm
  have hNumerator :
      C0 * B ^ (epsilon / 2) *
          Real.sqrt (C2 * B ^ (epsilon / 2) *
            heathBrownSecondMomentShape B M W) *
          Real.sqrt (C4 * B ^ (epsilon / 2) *
            heathBrownFourthMomentShape B M W) <=
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon * x ^
            (heathBrownSecondExponent tau rho / 2 +
              heathBrownFourthExponent tau rho rhoStar / 2) := by
    calc
      C0 * B ^ (epsilon / 2) *
          Real.sqrt (C2 * B ^ (epsilon / 2) *
            heathBrownSecondMomentShape B M W) *
          Real.sqrt (C4 * B ^ (epsilon / 2) *
            heathBrownFourthMomentShape B M W) <=
        C0 * B ^ (epsilon / 2) *
          (Real.sqrt (3 * C2) * B ^ (epsilon / 4) *
            x ^ (heathBrownSecondExponent tau rho / 2)) *
          (Real.sqrt (3 * C4) * B ^ (epsilon / 4) *
            x ^ (heathBrownFourthExponent tau rho rhoStar / 2)) := by
              gcongr
      _ = (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon * x ^
            (heathBrownSecondExponent tau rho / 2 +
              heathBrownFourthExponent tau rho rhoStar / 2) := by
            rw [<- hxcombine, <- hBcombine]
            ring
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hxpos _
  have hVpos : 0 < V := hxSigmaPos.trans_le hThreshold
  have hV2 : (x ^ sigma) ^ 2 <= V ^ 2 :=
    pow_le_pow_left₀ hxSigmaPos.le hThreshold 2
  have hMajor0 : 0 <=
      (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon * x ^
          (heathBrownSecondExponent tau rho / 2 +
            heathBrownFourthExponent tau rho rhoStar / 2) := by positivity
  unfold heathBrownFiniteFamilyBound
  calc
    (C0 * B ^ (epsilon / 2) *
        Real.sqrt (C2 * B ^ (epsilon / 2) *
          heathBrownSecondMomentShape B M W) *
        Real.sqrt (C4 * B ^ (epsilon / 2) *
          heathBrownFourthMomentShape B M W)) / V ^ 2 <=
      ((C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon * x ^
          (heathBrownSecondExponent tau rho / 2 +
            heathBrownFourthExponent tau rho rhoStar / 2)) / V ^ 2 :=
      div_le_div_of_nonneg_right hNumerator (sq_nonneg V)
    _ <= ((C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon * x ^
          (heathBrownSecondExponent tau rho / 2 +
            heathBrownFourthExponent tau rho rhoStar / 2)) /
          (x ^ sigma) ^ 2 :=
      div_le_div_of_nonneg_left hMajor0 (sq_pos_of_pos hxSigmaPos) hV2
    _ = (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon *
        x ^ (1 - 2 * sigma +
          (1 / 2 : Real) *
            max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
          (1 / 2 : Real) *
            max (rhoStar + 1)
              (max (4 * rho)
                (3 * rhoStar / 4 + rho + tau / 2))) := by
      rw [show (x ^ sigma) ^ 2 = x ^ (2 * sigma) by
        calc
          (x ^ sigma) ^ 2 = x ^ (sigma * 2) :=
            (Real.rpow_mul_natCast hx0 sigma 2).symm
          _ = x ^ (2 * sigma) := by ring_nf]
      let q := heathBrownSecondExponent tau rho / 2 +
        heathBrownFourthExponent tau rho rhoStar / 2
      have hDiv : x ^ q / x ^ (2 * sigma) = x ^ (q - 2 * sigma) := by
        rw [<- Real.rpow_sub hxpos]
      calc
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4) * B ^ epsilon *
              x ^ (heathBrownSecondExponent tau rho / 2 +
                heathBrownFourthExponent tau rho rhoStar / 2)) /
            x ^ (2 * sigma) =
            (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4) * B ^ epsilon) *
              (x ^ q / x ^ (2 * sigma)) := by
                dsimp only [q]
                ring
        _ = (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4) * B ^ epsilon) *
              x ^ (q - 2 * sigma) := by rw [hDiv]
        _ = (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) * B ^ epsilon *
            x ^ (1 - 2 * sigma +
              (1 / 2 : Real) *
                max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
              (1 / 2 : Real) *
                max (rhoStar + 1)
                  (max (4 * rho)
                    (3 * rhoStar / 4 + rho + tau / 2))) := by
          unfold q heathBrownSecondExponent heathBrownFourthExponent
          have hExponent :
              (1 + max (rho + 1)
                    (max (2 * rho) (5 * rho / 4 + tau / 2))) / 2 +
                  (1 + max (rhoStar + 1)
                    (max (4 * rho)
                      (3 * rhoStar / 4 + rho + tau / 2))) / 2 -
                    2 * sigma =
                1 - 2 * sigma +
                  (1 / 2 : Real) * max (rho + 1)
                    (max (2 * rho) (5 * rho / 4 + tau / 2)) +
                  (1 / 2 : Real) * max (rhoStar + 1)
                    (max (4 * rho)
                      (3 * rhoStar / 4 + rho + tau / 2)) := by ring
          rw [hExponent]

#print axioms heathBrownSecondShape_le_three_rpow
#print axioms heathBrownFourthShape_le_three_rpow
#print axioms heathBrownFiniteFamilyBound_le_relation_rpow

end

end GafniTao
