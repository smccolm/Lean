import Dubon2026.SourceCurveCorrespondenceRamification

/-! DUB-17/18 -> Weil norm adjunction -> compatible representatives.
Disjointness from a pulled-back divisor forces disjointness after
pushforward, since every normalized ramification index is positive. -/
namespace Dubon2026.SourceCurve.Divisor
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]

theorem disjoint_pushforward_of_pullback (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (D : Divisor K F) (A : Divisor K E)
    (h : ∀ w, finitePullbackAlong φ hφ D w = 0 ∨ A w = 0) :
    ∀ v, D v = 0 ∨ geometricPushforwardAlong φ hφ A v = 0 := by
  classical
  intro v
  by_cases hv : D v = 0
  · exact Or.inl hv
  right
  change (A.mapDomain (fun w => w.restrictAlong φ hφ)) v = 0
  apply Finsupp.mapDomain_of_not_mem_image_support
  rintro ⟨w, hw, heq⟩
  dsimp only at heq
  have hz := (h w).resolve_right (Finsupp.mem_support_iff.mp hw)
  rw [finitePullbackAlong_apply, heq] at hz
  exact mul_ne_zero hv (ne_of_gt (Place.ramificationAlong_pos φ hφ w)) hz

end
end Dubon2026.SourceCurve.Divisor
