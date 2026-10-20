import Dubon2026.PolarizedStrictKernel

/-! Original dual-number lifts of the source polarized representation with
fixed similitude. Their difference from the actual constant lift is proved
to lie in the full infinitesimal matrix kernel. This is the source fiber,
not an assumed tangent or Selmer identification, on DUB-17's route. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual first-order representation fiber, fixing the entire original similitude character. -/
def PolarizedFirstOrderLift (ρ : G →* PolarizedGaloisGroup ι R) :=
  {τ : G →* PolarizedGaloisGroup ι (DualNumber R) //
    polarizedDualReduction.comp τ = ρ ∧
      (polarizedSimilitude (R := DualNumber R) (ι := ι)).comp τ =
        (Units.map (TrivSqZeroExt.inlHom R R).toMonoidHom).comp (polarizedSimilitude.comp ρ)}

/-- The actual difference between an original lift and its constant reduction. -/
def polarizedFirstOrderDifference (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) : PolarizedGaloisGroup ι (DualNumber R) :=
  τ.val g * (polarizedDualConstant (ρ g))⁻¹

/-- The original difference reduces to the identity. -/
theorem polarizedFirstOrderDifference_reduction (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedDualReduction (polarizedFirstOrderDifference ρ τ g) = 1 := by
  have hr : polarizedDualReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property.1 g
  rw [polarizedFirstOrderDifference, map_mul, map_inv, polarizedDualReduction_constant,
    hr, mul_inv_cancel]

/-- Fixing the original similitude makes the actual difference have multiplier one. -/
theorem polarizedFirstOrderDifference_similitude (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedSimilitude (polarizedFirstOrderDifference ρ τ g) = 1 := by
  have hν := DFunLike.congr_fun τ.property.2 g
  change polarizedSimilitude (τ.val g) =
    Units.map (TrivSqZeroExt.inlHom R R).toMonoidHom (polarizedSimilitude (ρ g)) at hν
  rw [polarizedFirstOrderDifference, map_mul, map_inv, hν]
  change _ * (polarizedSimilitude (polarizedCoefficientMap (TrivSqZeroExt.inlHom R R) (ρ g)))⁻¹ = 1
  rw [polarizedCoefficientMap_similitude, mul_inv_cancel]

/-- The actual first-order matrix coordinates of the original polarized lift. -/
def polarizedFirstOrderCoordinate (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) : Matrix ι ι R :=
  dualMatrixInfinitesimal (polarizedFirstOrderDifference ρ τ g).left.1

/-- Original matrix coordinates recover the entire first-order difference. -/
theorem polarizedFirstOrderCoordinate_difference (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedStrictPoint (polarizedFirstOrderCoordinate ρ τ g) =
      polarizedFirstOrderDifference ρ τ g :=
  polarizedStrictPoint_of_kernel _ (polarizedFirstOrderDifference_reduction ρ τ g)
    (polarizedFirstOrderDifference_similitude ρ τ g)

/-- The coordinate reconstructs the original lift, with its actual constant reduction. -/
theorem polarizedFirstOrderCoordinate_reconstruct (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedStrictPoint (polarizedFirstOrderCoordinate ρ τ g) * polarizedDualConstant (ρ g) =
      τ.val g := by
  rw [polarizedFirstOrderCoordinate_difference, polarizedFirstOrderDifference, inv_mul_cancel_right]

end
end Dubon2026
