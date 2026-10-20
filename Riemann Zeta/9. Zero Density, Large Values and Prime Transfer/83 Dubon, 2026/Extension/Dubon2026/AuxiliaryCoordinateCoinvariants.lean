import Dubon2026.AuxiliaryCoordinateTrace

/-! # Coinvariants are identified by the actual unnormalized coordinate trace -/

namespace Dubon2026

noncomputable section

variable {R D J W : Type*} [CommRing R] [Group D] [Fintype D]
variable [AddCommGroup W] [Module R W]

open scoped BigOperators

/-- Each actual coinvariant class is represented by its trace in the identity coordinate. -/
theorem auxiliaryCoordinate_coinvariant_trace (f : J → D → W) :
    Representation.Coinvariants.mk (quotientRightTranslation (R := R) (D := D) (J := J) (W := W)) f =
      Representation.Coinvariants.mk (quotientRightTranslation (R := R) (D := D) (J := J) (W := W))
        (auxiliaryCoordinateSingle (R := R) 1 (auxiliaryCoordinateTrace (R := R) f)) := by
  let σ := quotientRightTranslation (R := R) (D := D) (J := J) (W := W)
  let π := Representation.Coinvariants.mk σ
  change π f = π (auxiliaryCoordinateSingle (R := R) 1 (auxiliaryCoordinateTrace (R := R) f))
  calc
    π f = π (∑ d : D, auxiliaryCoordinateSingle (R := R) d (fun j => f j d)) :=
      congrArg π (auxiliaryCoordinateSingle_sum (R := R) f).symm
    _ = ∑ d : D, π (auxiliaryCoordinateSingle (R := R) d (fun j => f j d)) := map_sum _ _ _
    _ = ∑ d : D, π (auxiliaryCoordinateSingle (R := R) 1 (fun j => f j d)) := by
      apply Finset.sum_congr rfl
      intro d _
      exact auxiliaryCoordinateSingle_coinvariant (R := R) d _
    _ = π (auxiliaryCoordinateSingle (R := R) 1 (∑ d : D, fun j => f j d)) := by
      rw [map_sum, map_sum]
    _ = _ := by
      congr 2
      funext j
      simp only [Finset.sum_apply, auxiliaryCoordinateTrace, LinearMap.coe_mk, AddHom.coe_mk]

/-- The coordinate trace descends to the actual coinvariant quotient. -/
def auxiliaryCoordinateCoinvariantTrace :
    (quotientRightTranslation (R := R) (D := D) (J := J) (W := W)).Coinvariants →ₗ[R]
      (J → W) :=
  Representation.Coinvariants.lift _ auxiliaryCoordinateTrace (by
    intro d
    ext f j
    exact congrFun (auxiliaryCoordinateTrace_invariant (R := R) d f) j)

/-- The source's unnormalized trace is an isomorphism on coinvariants. -/
def auxiliaryCoordinateCoinvariantEquiv :
    (quotientRightTranslation (R := R) (D := D) (J := J) (W := W)).Coinvariants ≃ₗ[R]
      (J → W) :=
  LinearEquiv.ofLinear auxiliaryCoordinateCoinvariantTrace
    ((Representation.Coinvariants.mk _).comp (auxiliaryCoordinateSingle (R := R) 1))
    (by
      ext w j
      exact congrFun (auxiliaryCoordinateTrace_single (R := R) (1 : D) w) j)
    (by
      apply Representation.Coinvariants.hom_ext
      ext f
      exact (auxiliaryCoordinate_coinvariant_trace (R := R) f).symm)

/-- The resulting isomorphism evaluates to the actual sum of coordinate values. -/
theorem auxiliaryCoordinateCoinvariantEquiv_mk (f : J → D → W) :
    auxiliaryCoordinateCoinvariantEquiv (R := R) (D := D) (J := J) (W := W)
      (Representation.Coinvariants.mk (quotientRightTranslation (R := R) (D := D) (J := J) (W := W)) f) =
      auxiliaryCoordinateTrace (R := R) f := rfl

end
end Dubon2026
