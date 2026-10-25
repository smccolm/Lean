import Dubon2026.SourceCurvePicardCorrespondence

/-! DUB-17/18 -> original Hecke reduction on torsion -> principal norm identity.
Retain the exact function whose orders represent the existing correspondence.
The already proved pullback ramification and pushforward norm formulas suffice;
no new finite-map or divisor theory is needed. -/
namespace Dubon2026.SourceCurve.Divisor
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]

theorem finitePullbackAlong_order (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (D : Divisor K F) (f : F) (hD : ∀ v, D v = v.ord f) (w : Place K E) :
    finitePullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  change finitePullback E D w = w.ord (algebraMap F E f)
  rw [finitePullback_apply, hD]
  exact (w.ord_algebraMap_restrict f).symm

theorem geometricCorrespondence_order (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (D : Divisor K F) (f : F) (hf : f ≠ 0) (hD : ∀ v, D v = v.ord f)
    (v : Place K F) :
    letI := algebraAlong ψ
    geometricCorrespondence φ ψ hφ hψ D v = v.ord (Algebra.norm F (φ f)) := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F E := hψ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  change geometricPushforward F (finitePullbackAlong φ hφ D) v = _
  rw [geometricPushforward_apply,
    v.ord_norm_eq_sum_fiber (hF v) hE ((map_ne_zero φ).mpr hf)]
  exact finsum_congr fun w => finitePullbackAlong_order φ hφ D f hD w.val

end
end Dubon2026.SourceCurve.Divisor
