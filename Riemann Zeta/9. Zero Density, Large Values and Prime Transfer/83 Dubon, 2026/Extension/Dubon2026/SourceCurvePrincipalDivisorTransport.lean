import Dubon2026.SourceCurvePlaceTransport
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal-divisor
degree zero -> Galois averaging. The actual field equivalence permutes
literal places and their order divisors. When the proved residue maps are
bijective, divisor degree is invariant under this actual permutation. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E]

/-- Transport a divisor along the actual place equivalence of a field equivalence. -/
def divisorTransform (e : F ≃ₐ[K] E) (D : Divisor K F) : Divisor K E :=
  Finsupp.equivMapDomain (Place.placeEquiv e).symm D

theorem divisorTransform_apply (e : F ≃ₐ[K] E) (D : Divisor K F) (w : Place K E) :
    divisorTransform e D w = D (w.comapEquiv e) := rfl

theorem degree_divisorTransform (e : F ≃ₐ[K] E) (D : Divisor K F)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    Divisor.degree (divisorTransform e D) = Divisor.degree D := by
  rw [Divisor.degree_eq_finsum, Divisor.degree_eq_finsum]
  simp only [Module.finrank_of_bijective_algebraMap (hF _),
    Module.finrank_of_bijective_algebraMap (hE _), Nat.cast_one, mul_one,
    divisorTransform_apply]
  exact finsum_comp_equiv (Place.placeEquiv e) (f := fun v => D v)

theorem divisorTransform_orders (e : F ≃ₐ[K] E) {D : Divisor K F} {f : F}
    (hD : ∀ v : Place K F, D v = v.ord f) (w : Place K E) :
    divisorTransform e D w = w.ord (e f) := by
  rw [divisorTransform_apply, hD, Place.ord_comapEquiv]

end
end Dubon2026.SourceCurve
