import Dubon2026.FiniteFreeHopfPointModel
import Dubon2026.FreeHopfCoordinateTransfer
import Dubon2026.HopfCoordinateEquivPoints
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink

/-! # Realize the same original model with coordinates in the base ring's universe -/

namespace Dubon2026
noncomputable section

universe uR uF uK uV uC
variable {R : Type uR} {F : Type uF} {K : Type uK} {V : Type uV}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- The actual original finite module is small in the universe of its base ring. Its genuine algebra equivalence with the resized coordinates transfers the original Hopf structure and point realization. The represented group and specified Galois action are unchanged. -/
def finiteFreeHopfPointModelResize
    (m : FiniteFreeHopfPointModel.{uR, uF, uK, uV, uC} R F K V ρ) :
    FiniteFreeHopfPointModel.{uR, uF, uK, uV, uR} R F K V ρ := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  letI := m.finite
  letI := m.free
  letI : Small.{uR} m.Coordinates := Module.Finite.small R m.Coordinates
  let e := Shrink.algEquiv R m.Coordinates
  letI := freeHopfCoordinateTransfer e
  letI := freeHopfCoordinateTransfer_isCocomm e
  let E := hopfCoordinateEquivPoints (K := K) (freeHopfCoordinateTransferEquiv e)
  refine { Coordinates := Shrink.{uR} m.Coordinates
           pointEquiv := E.symm.trans m.pointEquiv
           galois := ?_ }
  intro g p
  have hE : E.symm (hopfPointsGaloisAction (R := R) (F := F) g p) =
      hopfPointsGaloisAction (R := R) (F := F) g (E.symm p) := by
    apply E.injective
    rw [E.apply_symm_apply]
    have he := hopfCoordinateEquivPoints_coefficient (freeHopfCoordinateTransferEquiv e)
      (g.restrictScalars R) (E.symm p)
    change E (hopfPointsGaloisAction (R := R) (F := F) g (E.symm p)) =
      hopfPointsGaloisAction (R := R) (F := F) g (E (E.symm p)) at he
    rw [E.apply_symm_apply] at he
    exact he.symm
  change m.pointEquiv (E.symm (hopfPointsGaloisAction (R := R) (F := F) g p)) =
    ρ g (m.pointEquiv (E.symm p))
  rw [hE]
  exact m.galois g (E.symm p)

/-- Any actual original finite free Hopf model admits a model with coordinates in the base ring's universe, derived from its finite module and actual coordinate equivalence. The target model is constructed. -/
theorem finiteFreeHopfPointModel_resize_exists
    (m : FiniteFreeHopfPointModel.{uR, uF, uK, uV, uC} R F K V ρ) :
    Nonempty (FiniteFreeHopfPointModel.{uR, uF, uK, uV, uR} R F K V ρ) := by
  exact ⟨finiteFreeHopfPointModelResize m⟩

end
end Dubon2026
