import Dubon2026.FiniteFreeHopfPointModelSubgroup
import Dubon2026.IntegralHopfSubgroupInvariantGalois

/-! # Actual invariant-coordinate models for original quotient Galois modules -/

namespace Dubon2026
noncomputable section
open WithConv

universe uR uF uK uV uC

variable {R : Type uR} {F : Type uF} {K : Type uK} {V : Type uV}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Module.Flat R K] [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- Construct an actual model for the original quotient representation using the literal invariant Hopf coordinates of the pulled-back original subgroup. Original quotient point comparison and its proved Galois compatibility derive the required point realization. -/
def finiteFreeHopfPointModelQuotient
    (m : FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K V ρ) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K (V ⧸ H)
      (galoisModuleQuotientAction ρ H hH) := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  letI := m.finite
  letI := m.free
  letI : CommGroup (WithConv (m.Coordinates →ₐ[R] K)) := finiteFreeHopfPointsCommGroup
  let X : Subgroup (WithConv (m.Coordinates →ₐ[R] K)) := H.comap m.pointEquiv.toMonoidHom
  have hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (m.Coordinates →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X := by
    intro g p hp
    change m.pointEquiv (hopfPointsGaloisAction (R := R) (F := F) g p) ∈ H
    rw [m.galois]
    exact hH g (m.pointEquiv p) hp
  have hmap : X.map m.pointEquiv.toMonoidHom = H := by
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hv
      refine ⟨m.pointEquiv.symm v, ?_, m.pointEquiv.apply_symm_apply v⟩
      change m.pointEquiv (m.pointEquiv.symm v) ∈ H
      rwa [m.pointEquiv.apply_symm_apply]
  let Q := QuotientGroup.congr X H m.pointEquiv hmap
  have hQ (g : K ≃ₐ[F] K) (z : WithConv (m.Coordinates →ₐ[R] K) ⧸ X) :
      Q (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        galoisModuleQuotientAction ρ H hH g (Q z) := by
    induction z using Quotient.inductionOn with
    | h p =>
      change QuotientGroup.mk
          (m.pointEquiv (hopfPointsGaloisAction (R := R) (F := F) g p)) =
        QuotientGroup.mk (ρ g (m.pointEquiv p))
      rw [m.galois]
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI : Coalgebra R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra X hX).toCoalgebra
  letI := integralHopfSubgroupInvariantPointGroup X hX
  letI : Module.Finite R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).1
  letI : Module.Free R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).2.1
  letI := integralHopfSubgroupInvariant_isCocomm X hX
  let E := integralHopfSubgroupInvariantQuotientPoints X hX
  refine { Coordinates := integralHopfSubgroupInvariantCoordinates X hX
           hopf := integralHopfSubgroupInvariantHopfAlgebra X hX
           cocomm := integralHopfSubgroupInvariant_isCocomm X hX
           finite := (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).1
           free := (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).2.1
           pointEquiv := E.symm.trans Q
           galois := ?_ }
  intro g p
  have hE : E.symm (hopfPointsGaloisAction (R := R) (F := F) g p) =
      integralHopfSubgroupQuotientGaloisAutomorphism X hX g (E.symm p) := by
    apply E.injective
    rw [E.apply_symm_apply, integralHopfSubgroupInvariantQuotientPoints_galois,
      E.apply_symm_apply]
    rfl
  change Q (E.symm (hopfPointsGaloisAction (R := R) (F := F) g p)) = _
  rw [hE]
  exact hQ g (E.symm p)

/-- The quotient by a stable subgroup of the original modeled Galois module has a genuine finite free Hopf model, constructed through the actual invariant coordinate algebra. No target model is assumed. -/
theorem finiteFreeHopfPointModel_quotient_exists
    (m : FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K V ρ) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    Nonempty (FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K (V ⧸ H)
      (galoisModuleQuotientAction ρ H hH)) := by
  exact ⟨finiteFreeHopfPointModelQuotient m H hH⟩

end
end Dubon2026
