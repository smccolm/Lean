import Dubon2026.SourceCurveCorrespondencePlaces

/-! DUB-17/18 -> original Tate Hecke comparison -> complex base change.
Positive ramification ensures that a complex place above an arithmetic
place cannot have trivial restriction to the original arithmetic field.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]

theorem ramificationAlong_pos (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (w : Place K E) : 0 < ramificationAlong φ hφ w := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact w.ord_restricted_uniformizer_pos

theorem comap_restrictAlong_eq_of_commute
    {K' F' E' : Type*} [Field K'] [Field F'] [Field E']
    [Algebra K' F'] [Algebra K' E'] [CharZero F']
    (φ : F →ₐ[K] E) (ψ : F' →ₐ[K'] E')
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (f : F →+* F') (g : E →+* E') (v : Place K E) (w : Place K' E')
    (h : w.toValuationSubring.comap g = v.toValuationSubring)
    (hcomm : ∀ x, g (φ x) = ψ (f x)) :
    (restrictAlong ψ hψ w).toValuationSubring.comap f =
      (restrictAlong φ hφ v).toValuationSubring := by
  ext x
  change f x ∈ (restrictAlong ψ hψ w).toValuationSubring ↔
    x ∈ (restrictAlong φ hφ v).toValuationSubring
  rw [mem_restrictAlong_iff, mem_restrictAlong_iff, ← hcomm]
  change φ x ∈ w.toValuationSubring.comap g ↔ φ x ∈ v.toValuationSubring
  rw [h]

end
end Dubon2026.SourceCurve.Place
