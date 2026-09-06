import GafniTao.HeathBrownLowerSourceScale

/-!
# Uniform lower scale for every extracted source block

The lower bound for a dyadically extracted source length uses only the
physical lower cutoff `Y = floor(U^delta1)` and `Q < 4P`; it is independent
of the source classification index.  Isolating it here lets the square and
constant-factor transition cells use the same literal dyadic output.
-/

open Filter

namespace GafniTao

noncomputable section

theorem eventually_source_dyadic_lower_scale
    {delta1 : Real} (hdelta1 : 0 < delta1) :
    ∀ᶠ U : Real in atTop,
      let Y := Nat.floor (U ^ delta1)
      forall {r P : Nat}, 2 ^ r * Y < 4 * P ->
        U ^ (delta1 / 2) <= (P : Real) := by
  obtain ⟨Ufloor, _hUfloor, hFloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := 3 * delta1 / 4) (b := delta1) (by positivity) (by nlinarith)
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (4 : Real)) (a := delta1 / 2) (b := 3 * delta1 / 4)
      (by nlinarith)
  filter_upwards [eventually_ge_atTop Ufloor, hAbsorb,
      eventually_ge_atTop (2 : Real)]
    with U hUfloor hAbsorbU hUTwo
  dsimp only
  intro r P hQP
  let Y := Nat.floor (U ^ delta1)
  have hUPos : 0 < U := by linarith
  have hYLower : U ^ (3 * delta1 / 4) <= (Y : Real) := by
    simpa only [Y] using hFloor U hUfloor
  have hYQ : Y <= 2 ^ r * Y :=
    Nat.le_mul_of_pos_left _ (pow_pos (by omega : 0 < (2 : Nat)) r)
  have hYFourP : Y < 4 * P := hYQ.trans_lt hQP
  have hYFourPReal : (Y : Real) < 4 * (P : Real) := by
    exact_mod_cast hYFourP
  have hFourLower : 4 * U ^ (delta1 / 2) <= (Y : Real) :=
    hAbsorbU.trans hYLower
  linarith

#print axioms eventually_source_dyadic_lower_scale

end

end GafniTao
