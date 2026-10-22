import Dubon2026.SourceCurvePicardCorrespondence

/-! DUB-17/18 -> original Tate Hecke realization -> arithmetic Hecke
equivariance. These formulas expose the actual place restrictions and
normalized ramification orders in the already constructed divisor maps.
They are needed to compare those maps with the original coefficient action.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]

namespace Place

/-- Restrict a genuine place along the specified finite field map. -/
def restrictAlong (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite) (w : Place K E) : Place K F :=
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  w.restrict F

theorem mem_restrictAlong_iff (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (w : Place K E) (x : F) :
    x ∈ (restrictAlong φ hφ w).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

/-- The actual normalized ramification order along the specified field map. -/
def ramificationAlong (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite) (w : Place K E) : ℤ :=
  w.ord (φ (restrictAlong φ hφ w).uniformizer)

theorem ord_restrictAlong (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (w : Place K E) (f : F) :
    w.ord (φ f) = (restrictAlong φ hφ w).ord f * ramificationAlong φ hφ w := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact w.ord_algebraMap_restrict f

end Place
namespace Divisor

theorem finitePullbackAlong_apply (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (D : Divisor K F) (w : Place K E) :
    finitePullbackAlong φ hφ D w = D (Place.restrictAlong φ hφ w) *
      Place.ramificationAlong φ hφ w := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact finitePullback_apply E D w

theorem geometricPushforwardAlong_single (ψ : F →ₐ[K] E) (hψ : ψ.toRingHom.Finite)
    (w : Place K E) (n : ℤ) :
    geometricPushforwardAlong ψ hψ (Finsupp.single w n) =
      Finsupp.single (Place.restrictAlong ψ hψ w) n := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F E := hψ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact geometricPushforward_single F w n

end Divisor
end
end Dubon2026.SourceCurve
