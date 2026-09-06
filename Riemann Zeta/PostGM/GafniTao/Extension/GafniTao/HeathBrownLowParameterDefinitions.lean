import GafniTao.HeathBrownPhysicalMajorantOptimization

/-!
# Explicit finite parameters for the low Heath--Brown cells

These definitions fix one conservative hierarchy of positive losses.  The
hierarchy is intentionally wasteful: its only purpose is to make every
strict inequality in the actual detector, reflected Type-I, powered Type-II,
selection, and final exponent ledgers simultaneously satisfiable.
-/

namespace GafniTao

noncomputable section

def heathBrownTuneGap (sigma : Real) : Real := sigma - 1 / 2

def heathBrownTuneQ (sigma epsilon : Real) : Real :=
  min (heathBrownTuneGap sigma) epsilon / 1000000

def heathBrownTuneDelta1 (sigma : Real) : Real :=
  heathBrownTuneGap sigma / 1000

def heathBrownTuneD (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon * heathBrownTuneGap sigma / 1000

def heathBrownTuneDelta2 (sigma epsilon : Real) : Real :=
  heathBrownTuneD sigma epsilon / 1000

def heathBrownTuneP (sigma epsilon : Real) : Nat :=
  Nat.ceil (4 / heathBrownTuneDelta2 sigma epsilon)

def heathBrownTuneEta (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneLoss (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneDil (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneLog (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon * heathBrownTuneDelta1 sigma / 100

def heathBrownTunePower (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon * heathBrownTuneDelta1 sigma / 100

def heathBrownTuneShell (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon * heathBrownTuneDelta2 sigma epsilon /
    (100 * ((heathBrownTuneP sigma epsilon + 1 : Nat) : Real))

def heathBrownTuneConst (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneScale (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneReflect (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon * heathBrownTuneGap sigma / 1000

def heathBrownTuneRel (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneCard (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneDetectorEpsilon (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 1000

def heathBrownTuneV (sigma epsilon : Real) : Real :=
  heathBrownTuneD sigma epsilon

def heathBrownTuneExtract (sigma epsilon : Real) : Real :=
  10 * heathBrownTuneD sigma epsilon

def heathBrownTuneFixed (sigma epsilon : Real) : Real :=
  heathBrownTuneQ sigma epsilon / 100

def heathBrownTuneSelection (sigma epsilon : Real) : Real :=
  20 * heathBrownTuneD sigma epsilon

def heathBrownTuneSigma0 (sigma epsilon : Real) : Real :=
  sigma - heathBrownTuneQ sigma epsilon

theorem heathBrownTuneQ_pos
    {sigma epsilon : Real} (hsigma : 1 / 2 < sigma)
    (hepsilon : 0 < epsilon) :
    0 < heathBrownTuneQ sigma epsilon := by
  unfold heathBrownTuneQ heathBrownTuneGap
  positivity

theorem heathBrownTuneQ_le_gap
    {sigma epsilon : Real} :
    heathBrownTuneQ sigma epsilon <= heathBrownTuneGap sigma / 1000000 := by
  unfold heathBrownTuneQ
  gcongr
  exact min_le_left _ _

theorem heathBrownTuneQ_le_epsilon
    {sigma epsilon : Real} :
    heathBrownTuneQ sigma epsilon <= epsilon / 1000000 := by
  unfold heathBrownTuneQ
  gcongr
  exact min_le_right _ _

theorem heathBrownTuneQ_le_one
    {sigma epsilon : Real} (hsigmaUpper : sigma <= 3 / 4) :
    heathBrownTuneQ sigma epsilon <= 1 := by
  calc
    heathBrownTuneQ sigma epsilon <= heathBrownTuneGap sigma / 1000000 :=
      heathBrownTuneQ_le_gap
    _ <= 1 := by
      unfold heathBrownTuneGap
      linarith

theorem heathBrownTune_shell_mul_power_succ
    (sigma epsilon : Real) :
    heathBrownTuneShell sigma epsilon *
        ((heathBrownTuneP sigma epsilon + 1 : Nat) : Real) =
      heathBrownTuneQ sigma epsilon * heathBrownTuneDelta2 sigma epsilon /
        100 := by
  unfold heathBrownTuneShell
  have hpos : (0 : Real) < ((heathBrownTuneP sigma epsilon + 1 : Nat) : Real) :=
    by positivity
  field_simp [hpos.ne']

#print axioms heathBrownTuneQ_pos
#print axioms heathBrownTuneQ_le_gap
#print axioms heathBrownTune_shell_mul_power_succ

end

end GafniTao
