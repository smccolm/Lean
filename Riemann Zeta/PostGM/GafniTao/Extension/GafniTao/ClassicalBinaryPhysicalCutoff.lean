import GafniTao.ClassicalBinarySelectedScale

/-!
# A common physical cutoff for the classical binary detector

Heath--Brown's source argument takes the two detector cutoffs at the same
power of the height.  Natural floors are retained here.  The factor-two loss
is made explicit and the cutoff is proved to lie below the actual sharp-zeta
cutoff used by the frozen detector.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Common natural cutoff at physical height `U`. -/
noncomputable def classicalBinaryPhysicalCutoff
    (U alpha : Real) : Nat :=
  Nat.floor (U ^ alpha)

/-- Eventually the common cutoff is positive, loses at most a factor two
from the real power, and is admissible for the frozen sharp-zeta detector. -/
theorem eventually_classicalBinaryPhysicalCutoff_spec
    {alpha : Real} (halpha : 0 < alpha) (halphaUpper : alpha <= 1) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := classicalBinaryPhysicalCutoff U alpha
      0 < X /\ U ^ alpha / 2 <= (X : Real) /\
        (X : Real) <= U ^ alpha /\ X <= Nat.floor (sharpZetaCutoff U) := by
  obtain ⟨Ufloor, hUfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor alpha halpha
  let U0 : Real := max 8 Ufloor
  refine ⟨U0, le_max_left _ _, ?_⟩
  intro U hU
  have hUfloor' : Ufloor <= U := (le_max_right _ _).trans hU
  have hUEight : 8 <= U := (le_max_left _ _).trans hU
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := by linarith
  have hFloorData := hFloor U hUfloor'
  have hXRealPos : (0 : Real) < classicalBinaryPhysicalCutoff U alpha :=
    lt_of_lt_of_le (by positivity : 0 < U ^ alpha / 2) hFloorData.1
  have hXPos : 0 < classicalBinaryPhysicalCutoff U alpha := by
    exact_mod_cast hXRealPos
  have hPowLeU : U ^ alpha <= U := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hUOne halphaUpper
  have hSharpReal : (classicalBinaryPhysicalCutoff U alpha : Real) <=
      sharpZetaCutoff U := by
    calc
      (classicalBinaryPhysicalCutoff U alpha : Real) <= U ^ alpha :=
        hFloorData.2
      _ <= U := hPowLeU
      _ <= 4 * U := by nlinarith
      _ <= sharpZetaCutoff U := (four_mul_lt_sharpZetaCutoff U).le
  have hSharpNat : classicalBinaryPhysicalCutoff U alpha <=
      Nat.floor (sharpZetaCutoff U) := by
    apply Nat.le_floor
    exact hSharpReal
  exact ⟨hXPos, hFloorData.1, hFloorData.2, hSharpNat⟩

/-- A Type-II scale selected from equal cutoffs lies between the common
cutoff and its square. -/
theorem classicalBinarySelectedN_typeII_equal_cutoff_range
    {X kI kII : Nat} (hX : 0 < X)
    (hkII : kII <= Nat.clog 2 X)
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kII * 2)) (hq : binaryScaleLabel q = Sum.inr r) :
    X <= classicalBinarySelectedN X X kI kII q /\
      classicalBinarySelectedN X X kI kII q < X ^ 2 := by
  have h := classicalBinarySelectedN_typeII_range hX hkII q r hq
  simpa only [pow_two] using h

#print axioms eventually_classicalBinaryPhysicalCutoff_spec
#print axioms classicalBinarySelectedN_typeII_equal_cutoff_range

end

end GafniTao
