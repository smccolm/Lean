import Dubon2026.SourceEllipticPeriodUniformization
import Dubon2026.SourceEllipticComplexPeriodModel
import Dubon2026.SourceEllipticVariableAddEquiv

/-! Uniformization of every actual complex elliptic point group. The map is
the actual Weierstrass-function map followed by the existing proved inverse
coordinate change. Surjectivity and its exact period lattice are derived.
This removes the complex uniformization input from the odd-prime quotient
product route for DUB-17/18. The downstream odd quotient scalar and complex
product modules prove compatibility and the integral polynomial identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve
open SourceEllipticVariableChange
noncomputable section

/-- The actual period map followed by a literal inverse change of variables. -/
def periodModelHom (L : PeriodPair) [(periodCurve L).IsElliptic] (C : VariableChange ℂ) :
    ℂ →+ (C • periodCurve L).toAffine.Point :=
  (variableChangeAddEquiv C (periodCurve L).toAffine).symm.toAddMonoidHom.comp (periodHom L)

theorem periodModelHom_apply (L : PeriodPair) [(periodCurve L).IsElliptic]
    (C : VariableChange ℂ) (z : ℂ) :
    periodModelHom L C z = vcInvFun C (periodCurve L).toAffine (periodPoint L z) := rfl

theorem periodModelHom_surjective (L : PeriodPair) [(periodCurve L).IsElliptic]
    (C : VariableChange ℂ) : Function.Surjective (periodModelHom L C) :=
  (variableChangeAddEquiv C (periodCurve L).toAffine).symm.surjective.comp
    (periodHom_surjective L)

theorem ker_periodModelHom (L : PeriodPair) [(periodCurve L).IsElliptic]
    (C : VariableChange ℂ) : (periodModelHom L C).ker = L.lattice.toAddSubgroup := by
  ext z
  let e := (variableChangeAddEquiv C (periodCurve L).toAffine).symm
  change e (periodPoint L z) = 0 ↔ z ∈ L.lattice
  rw [← e.map_zero, e.injective.eq_iff]
  exact periodPoint_eq_zero_iff L z

theorem exists_complex_uniformization (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (τ : UpperHalfPlane) (φ : ℂ →+ W.toAffine.Point),
      Function.Surjective φ ∧ φ.ker =
        (SourceFunctionField.PeriodLattice.ofTau τ).lattice.toAddSubgroup := by
  obtain ⟨τ, C, hC⟩ := exists_complex_period_model W
  subst W
  exact ⟨τ, periodModelHom _ C, periodModelHom_surjective _ C, ker_periodModelHom _ C⟩

end
end Dubon2026.SourceEllipticPeriod
