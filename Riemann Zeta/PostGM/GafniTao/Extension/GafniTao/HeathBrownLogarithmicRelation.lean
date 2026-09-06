import GafniTao.HeathBrownFiniteExponentMajorant
import GafniTao.HeathBrownExponentRelation

/-!
# Exact logarithmic extraction of the Heath--Brown relation

The source exponents are defined here from the actual finite quantities.
Consequently all four real-power identities are exact.  The only error in
the resulting relation is the explicitly supplied finite loss `x^zeta`.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exponent of a positive quantity `y` to a base `x > 1`. -/
noncomputable def heathBrownLogExponent (x y : Real) : Real :=
  Real.log y / Real.log x

theorem rpow_heathBrownLogExponent
    {x y : Real} (hx : 1 < x) (hy : 0 < y) :
    x ^ heathBrownLogExponent x y = y := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have harg : Real.log x * (Real.log y / Real.log x) = Real.log y := by
    field_simp
  rw [heathBrownLogExponent, harg, Real.exp_log hy]

/-- The exact finite family estimate implies equation (33), up to one
displayed exponent `zeta` that accounts for finite constants and selection
losses.  `rhoStar` is defined from the actual self-energy `E` and therefore
cannot be chosen independently to make the conclusion hold. -/
theorem heathBrown_logarithmic_relation_of_family_bound
    {epsilon C0 C2 C4 B V x L E zeta : Real}
    {M : Nat} {W : Finset Real}
    (hx : 1 < x) (hB : 0 < B) (hV : 0 < V) (hL : 0 <= L)
    (hE : 0 < E) (hCard : 0 < W.card)
    (hC0 : 0 <= C0) (hC2 : 0 <= C2) (hC4 : 0 <= C4)
    (hM : (M : Real) <= x)
    (hEnergyExact : E = (ApproxAddEnergy 1 W : Real))
    (hFamily : E <= L *
      heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W)
    (hLoss : L *
        (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon <= x ^ zeta) :
    let sigma := heathBrownLogExponent x V
    let tau := heathBrownLogExponent x B
    let rho := heathBrownLogExponent x (W.card : Real)
    let rhoStar := heathBrownLogExponent x E
    rhoStar <= zeta +
      (1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2))) := by
  dsimp only
  let sigma := heathBrownLogExponent x V
  let tau := heathBrownLogExponent x B
  let rho := heathBrownLogExponent x (W.card : Real)
  let rhoStar := heathBrownLogExponent x E
  have hxOne : 1 <= x := hx.le
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hCardReal : (0 : Real) < W.card := by exact_mod_cast hCard
  have hBpow : B <= x ^ tau := by
    rw [rpow_heathBrownLogExponent hx hB]
  have hCardPow : (W.card : Real) <= x ^ rho := by
    rw [rpow_heathBrownLogExponent hx hCardReal]
  have hEnergyPow : (ApproxAddEnergy 1 W : Real) <= x ^ rhoStar := by
    rw [<- hEnergyExact, rpow_heathBrownLogExponent hx hE]
  have hThreshold : x ^ sigma <= V := by
    rw [rpow_heathBrownLogExponent hx hV]
  have hFinite := heathBrownFiniteFamilyBound_le_relation_rpow
    (epsilon := epsilon)
    hxOne hB hC0 hC2 hC4 hBpow hCardPow hEnergyPow hM hThreshold
  let q : Real := 1 - 2 * sigma +
    (1 / 2 : Real) *
      max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
    (1 / 2 : Real) *
      max (rhoStar + 1)
        (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))
  have hFamily' : E <=
      (L * (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
        B ^ epsilon) * x ^ q := by
    calc
      E <= L * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W :=
        hFamily
      _ <= L * ((C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon * x ^ q) := by
        apply mul_le_mul_of_nonneg_left _ hL
        simpa only [q, sigma, tau, rho, rhoStar] using hFinite
      _ = (L * (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon) * x ^ q := by ring
  have hPower : E <= x ^ (zeta + q) := by
    calc
      E <= (L * (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon) * x ^ q := hFamily'
      _ <= x ^ zeta * x ^ q :=
        mul_le_mul_of_nonneg_right hLoss (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (zeta + q) := (Real.rpow_add hxpos _ _).symm
  have hEpowExact : x ^ rhoStar = E :=
    rpow_heathBrownLogExponent hx hE
  have hExponent : rhoStar <= zeta + q := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [hEpowExact] using hPower
  simpa only [q, sigma, tau, rho, rhoStar] using hExponent

/-- Zero finite loss recovers the proposition named in the source algebra
module. -/
theorem heathBrownExponentRelation_of_logarithmic_relation_zero
    {sigma tau rho rhoStar : Real}
    (h : rhoStar <= 0 +
      (1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    HeathBrownExponentRelation sigma tau rho rhoStar := by
  simpa only [zero_add, HeathBrownExponentRelation] using h

#print axioms rpow_heathBrownLogExponent
#print axioms heathBrown_logarithmic_relation_of_family_bound
#print axioms heathBrownExponentRelation_of_logarithmic_relation_zero

end

end GafniTao
