import Dubon2026.SourceCurveCorrespondencePlaces
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> self-adjointness of the original Hecke operator.
A proved top-field automorphism exchanging two finite embeddings
identifies the correspondence with its transpose. Normalized orders
and the actual induced place permutation supply both divisor identities. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]
variable (φ ψ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
variable (σ : E ≃ₐ[K] E) (hcomm : ∀ x, σ (φ x) = ψ x)
include hcomm

namespace Place

theorem restrictAlong_comapEquiv (w : Place K E) :
    restrictAlong φ hφ (w.comapEquiv σ) = restrictAlong ψ hψ w := by
  apply Place.ext
  ext x
  rw [mem_restrictAlong_iff, mem_comapEquiv_iff, mem_restrictAlong_iff, hcomm]

theorem ramificationAlong_comapEquiv (w : Place K E) :
    ramificationAlong φ hφ (w.comapEquiv σ) = ramificationAlong ψ hψ w := by
  rw [ramificationAlong, ord_comapEquiv, hcomm,
    restrictAlong_comapEquiv φ ψ hφ hψ σ hcomm]
  rfl

end Place
namespace Divisor

theorem finitePullbackAlong_domCongr (D : Divisor K F) :
    Finsupp.domCongr (Place.placeEquiv σ) (finitePullbackAlong ψ hψ D) =
      finitePullbackAlong φ hφ D := by
  ext w
  obtain ⟨v, rfl⟩ := (Place.placeEquiv σ).surjective w
  change Finsupp.equivMapDomain (Place.placeEquiv σ) (finitePullbackAlong ψ hψ D)
    (Place.placeEquiv σ v) = finitePullbackAlong φ hφ D (v.comapEquiv σ)
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
    finitePullbackAlong_apply, finitePullbackAlong_apply,
    Place.restrictAlong_comapEquiv φ ψ hφ hψ σ hcomm,
    Place.ramificationAlong_comapEquiv φ ψ hφ hψ σ hcomm]

theorem geometricPushforwardAlong_domCongr (A : Divisor K E) :
    geometricPushforwardAlong φ hφ (Finsupp.domCongr (Place.placeEquiv σ) A) =
      geometricPushforwardAlong ψ hψ A := by
  induction A using Finsupp.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | single_add w n A _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    congr 1
    change geometricPushforwardAlong φ hφ
      (Finsupp.equivMapDomain (Place.placeEquiv σ) (Finsupp.single w n)) = _
    rw [Finsupp.equivMapDomain_single, geometricPushforwardAlong_single,
      geometricPushforwardAlong_single]
    change Finsupp.single (Place.restrictAlong φ hφ (w.comapEquiv σ)) n = _
    rw [Place.restrictAlong_comapEquiv φ ψ hφ hψ σ hcomm]

theorem geometricCorrespondence_swap_of_equiv (hback : ∀ x, σ (ψ x) = φ x)
    (D : Divisor K F) : geometricCorrespondence ψ φ hψ hφ D =
      geometricCorrespondence φ ψ hφ hψ D := by
  change geometricPushforwardAlong φ hφ (finitePullbackAlong ψ hψ D) =
    geometricPushforwardAlong ψ hψ (finitePullbackAlong φ hφ D)
  rw [← finitePullbackAlong_domCongr ψ φ hψ hφ σ hback,
    geometricPushforwardAlong_domCongr φ ψ hφ hψ σ hcomm]

end Divisor
end
end Dubon2026.SourceCurve
