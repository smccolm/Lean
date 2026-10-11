import Dubon2026.FiniteFreeHopfPointModel

/-! # Transport of actual Hopf models along original equivariant group equivalences -/

namespace Dubon2026
noncomputable section

universe uC

variable {R F K V W : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- An equivariant equivalence of the original represented groups transports a genuine model using exactly the same original integral Hopf coordinates. -/
def finiteFreeHopfPointModelEquiv
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (e : V ≃* W)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), e (ρ g v) = τ g (e v)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  letI := m.finite
  letI := m.free
  refine { Coordinates := m.Coordinates
           pointEquiv := m.pointEquiv.trans e
           galois := ?_ }
  intro g p
  change e (m.pointEquiv (hopfPointsGaloisAction (R := R) (F := F) g p)) =
    τ g (e (m.pointEquiv p))
  rw [m.galois]
  exact he g (m.pointEquiv p)

/-- The transported model realizes every original coordinate point by the specified original group equivalence. -/
theorem finiteFreeHopfPointModel_equiv_points
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (e : V ≃* W)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), e (ρ g v) = τ g (e v)) :
    (finiteFreeHopfPointModelEquiv m e he).pointEquiv = m.pointEquiv.trans e := by
  rfl

end
end Dubon2026
