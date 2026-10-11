import Dubon2026.FiniteFreeHopfPointModel
import Dubon2026.GaloisModuleSubquotientActions
import Dubon2026.IntegralHopfSubgroupCocommutativity

/-! # Actual integral coordinate models for stable subgroups of a given Galois module -/

namespace Dubon2026
noncomputable section
open WithConv

universe uR uF uK uV uC

variable {R : Type uR} {F : Type uF} {K : Type uK} {V : Type uV}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- The actual point pullback of a stable subgroup has a genuine integral Hopf quotient coordinate model. Its derived finite free cocommutative coordinates and original point restriction realize the given subgroup with precisely its original restricted Galois action. -/
def finiteFreeHopfPointModelSubgroup
    (m : FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K V ρ) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K H (galoisModuleSubgroupAction ρ H hH) := by
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
  let eX : X ≃* H := (m.pointEquiv.subgroupMap X).trans (MulEquiv.subgroupCongr hmap)
  letI := integralHopfSubgroupQuotient X hX
  letI : Module.Free R
      (m.Coordinates ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (m.Coordinates →ₐ[R] K)))) :=
    (integralHopfSubgroupQuotient_finitePoints X hX).2.1
  letI := integralHopfSubgroupQuotient_isCocomm X hX
  refine { Coordinates := m.Coordinates ⧸
             hopfPointsVanishingIdeal (X : Set (WithConv (m.Coordinates →ₐ[R] K)))
           pointEquiv := (integralHopfSubgroupPointsEquiv X hX).trans eX
           galois := ?_ }
  intro g p
  apply Subtype.ext
  change m.pointEquiv
      (integralHopfSubgroupPointsEquiv X hX
        (commutativeHopfPointsAutomorphism (g.restrictScalars R) p)).val =
    ρ g (m.pointEquiv (integralHopfSubgroupPointsEquiv X hX p).val)
  rw [integralHopfSubgroupPointsEquiv_galois]
  exact m.galois g (integralHopfSubgroupPointsEquiv X hX p).val

/-- A stable subgroup of the actual original Galois module admits a genuine finite free Hopf model, constructed from the original model by its actual subgroup coordinate quotient. The target model is derived rather than supplied. -/
theorem finiteFreeHopfPointModel_subgroup_exists
    (m : FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K V ρ) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    Nonempty (FiniteFreeHopfPointModel.{uR,uF,uK,uV,uC} R F K H
      (galoisModuleSubgroupAction ρ H hH)) := by
  exact ⟨finiteFreeHopfPointModelSubgroup m H hH⟩

end
end Dubon2026
