import Dubon2026.SourceGammaOnePrimitiveBoundaryGaloisWords

/-! DUB-17/18 -> original all-weight association -> character specialization.
The actual finite boundary Hecke and diamond operators commute. Together
with the geometric Frobenius route, this supplies the commutative original
joint image needed to reuse the existing faithful character-fiber theorem. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary ToricCoordinates
variable (Q N w : ℕ) [NeZero N]
local notation "M" => Q * N ^ 2

/-- The second primitive unit action commutes with the original diamond,
including its scalar and homogeneous coefficient factors. -/
theorem binaryPrimitiveColumnSecond_diamond_commute (u : (ZMod M)ˣ) (g : Gamma0 M) :
    Commute (binaryPrimitiveColumnSecond Q N w u) (binaryPrimitiveColumnDiamond Q N w g) := by
  have hc : Commute (binaryPrimitiveCoefficientUnits Q N w u)
      (sourceGammaOneBinaryDiamondCoefficient Q N w g) := by
    rw [binaryPrimitiveCoefficientUnits_eq, sourceGammaOneBinaryDiamondCoefficient_eq_diagonal]
    exact ((Commute.all
      ![(binaryPrimitiveUnitReduction Q N u : ZMod N), 1]
      ![(g.val 1 1 : ZMod N), (g.val 0 0 : ZMod N)]).map
        (Matrix.diagonalRingHom (Fin 2) (ZMod N))).map (homogeneousMatrixRepresentation w)
  apply LinearMap.ext
  intro f
  funext c
  change (binaryPrimitiveUnitReduction Q N u : ZMod N) •
      binaryPrimitiveCoefficientUnits Q N w u
        (sourceGammaOneBinaryDiamondCoefficient Q N w g
          (f (scale (gamma0Unit M g)⁻¹ (gamma0Unit M g) (scale u⁻¹ 1 c)))) =
    sourceGammaOneBinaryDiamondCoefficient Q N w g
      ((binaryPrimitiveUnitReduction Q N u : ZMod N) •
        binaryPrimitiveCoefficientUnits Q N w u
          (f (scale u⁻¹ 1 (scale (gamma0Unit M g)⁻¹ (gamma0Unit M g) c))))
  rw [map_smul, scale_comm]
  exact congrArg ((binaryPrimitiveUnitReduction Q N u : ZMod N) • ·)
    (LinearMap.congr_fun hc.eq _)

/-- All actual finite-column diamonds commute, by their literal diagonal
coefficient actions and commuting primitive-column scalings. -/
theorem binaryPrimitiveColumnDiamond_commute (g h : Gamma0 M) :
    Commute (binaryPrimitiveColumnDiamond Q N w g) (binaryPrimitiveColumnDiamond Q N w h) := by
  have hc : Commute (sourceGammaOneBinaryDiamondCoefficient Q N w g)
      (sourceGammaOneBinaryDiamondCoefficient Q N w h) := by
    rw [sourceGammaOneBinaryDiamondCoefficient_eq_diagonal,
      sourceGammaOneBinaryDiamondCoefficient_eq_diagonal]
    exact ((Commute.all ![(g.val 1 1 : ZMod N), (g.val 0 0 : ZMod N)]
      ![(h.val 1 1 : ZMod N), (h.val 0 0 : ZMod N)]).map
        (Matrix.diagonalRingHom (Fin 2) (ZMod N))).map (homogeneousMatrixRepresentation w)
  apply LinearMap.ext
  intro f
  funext c
  change sourceGammaOneBinaryDiamondCoefficient Q N w g
      (sourceGammaOneBinaryDiamondCoefficient Q N w h
        (f (scale (gamma0Unit M h)⁻¹ (gamma0Unit M h)
          (scale (gamma0Unit M g)⁻¹ (gamma0Unit M g) c)))) =
    sourceGammaOneBinaryDiamondCoefficient Q N w h
      (sourceGammaOneBinaryDiamondCoefficient Q N w g
        (f (scale (gamma0Unit M g)⁻¹ (gamma0Unit M g)
          (scale (gamma0Unit M h)⁻¹ (gamma0Unit M h) c))))
  rw [scale_comm]
  exact LinearMap.congr_fun hc.eq _

/-- Every pair of actual boundary prime/diamond generators commutes. -/
theorem binaryPrimitiveBoundaryHeckeDiamondOperators_commute
    (a b : sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M) :
    Commute (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w a)
      (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w b) := by
  cases a with
  | inl ell =>
    cases b with
    | inl ell' =>
      change Commute (binaryPrimitiveColumnHecke Q N w ell) (binaryPrimitiveColumnHecke Q N w ell')
      rw [binaryPrimitiveColumnHecke_eq_sum, binaryPrimitiveColumnHecke_eq_sum]
      apply Commute.add_left
      · exact ((Commute.all _ _).map (binaryPrimitiveColumnFirst Q N w)).add_right
          (binaryPrimitiveColumnFirst_second_commute Q N w _ _)
      · exact (binaryPrimitiveColumnFirst_second_commute Q N w _ _).symm.add_right
          ((Commute.all _ _).map (binaryPrimitiveColumnSecond Q N w))
    | inr g =>
      change Commute (binaryPrimitiveColumnHecke Q N w ell) (binaryPrimitiveColumnDiamond Q N w g)
      rw [binaryPrimitiveColumnHecke_eq_sum]
      exact (binaryPrimitiveColumnFirst_diamond_commute Q N w _ g).add_left
        (binaryPrimitiveColumnSecond_diamond_commute Q N w _ g)
  | inr g =>
    cases b with
    | inl ell =>
      change Commute (binaryPrimitiveColumnDiamond Q N w g) (binaryPrimitiveColumnHecke Q N w ell)
      rw [binaryPrimitiveColumnHecke_eq_sum]
      exact (binaryPrimitiveColumnFirst_diamond_commute Q N w _ g).symm.add_right
        (binaryPrimitiveColumnSecond_diamond_commute Q N w _ g).symm
    | inr h => exact binaryPrimitiveColumnDiamond_commute Q N w g h

end
end Dubon2026.SourceFunctionField.GammaOne
