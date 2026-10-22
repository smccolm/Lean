import Dubon2026.SourceOriginalInverseJRelationValues

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay.
The actual original regular differential supplies a positive-degree monic
relation for its analytic quotient, with coefficients polynomial in inverse
j. This original consumer discharges the relation needed by the analytic
root bound; it does not assume a polynomial relation for a separate function.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial KaehlerDifferential SourceCurve
open scoped Topology BigOperators

/-- The precise scalar expression appearing in the inverse-j integrality relation. -/
def inverseJExpression (M : ℕ) (u j : ℂ) : ℂ := u ^ (2 * M) * j ^ (M + 1) * (j - 1728) ^ M

theorem original_regular_inverse_j_analytic_relation (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g) :
    ∃ (n : ℕ) (c : ℕ → ℂ[X]), 0 < n ∧ ∀ τ : ℍ, h τ ≠ 0 → JMultiplicity.jf τ ≠ 0 →
      inverseJExpression (SourceLevelProjective.dedekindPsi N) (g τ / h τ) (JMultiplicity.jf τ) ^ n +
        ∑ i ∈ Finset.range n, (c i).eval ((JMultiplicity.jf τ)⁻¹) *
          inverseJExpression (SourceLevelProjective.dedekindPsi N) (g τ / h τ) (JMultiplicity.jf τ) ^ i = 0 := by
  let M := SourceLevelProjective.dedekindPsi N
  let y := x ^ (2 * M) * jOver N ℂ ^ (M + 1) *
    (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) ^ M
  obtain ⟨n, c, hn, hc⟩ := exists_original_inverse_j_monic_relation N y
    (original_regular_inverse_j_integral N x hx hreg)
  refine ⟨n, c, hn, ?_⟩
  intro τ hτ hj
  let φ : ℂ → ℂ := fun z => inverseJExpression M (g (ofComplex z) / h (ofComplex z))
    (JMultiplicity.jf (ofComplex z))
  have hq : ContinuousAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) :=
    (ModularRatios.analyticAt_comp_ofComplex g τ).continuousAt.div
      (ModularRatios.analyticAt_comp_ofComplex h τ).continuousAt (by simpa only [ofComplex_apply] using hτ)
  have hjc := (JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ).continuousAt
  have hφ : ContinuousAt φ (τ : ℂ) :=
    ((hq.pow (2 * M)).mul (hjc.pow (M + 1))).mul ((hjc.sub continuousAt_const).pow M)
  have he := original_inverse_j_relation_value N y n c hc τ hj φ hφ
    (original_differential_expression_germ N x g h hh hr M τ)
  simpa only [φ, ofComplex_apply, M] using he

end
end Dubon2026.SourceFunctionField
