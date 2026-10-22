import Dubon2026.SourceOriginalChartDerivativeGerms

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> actual
differential coordinate compatibility. The original chart germ map gives
the scalar action; its proved derivative identities define a derivation.
The native Kaehler universal map then identifies the reading of any
actual original differential from any original differential expression.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

/-- The original field acts on chart germs by its proved residue germ map. -/
abbrev chartGermAlgebra (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    Algebra (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
  (chartReadHom N v).toAlgebra

theorem chartGerm_smul (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) (m : Germ (𝓝[≠] (0 : ℂ)) ℂ) :
    letI := chartGermAlgebra N v
    letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N v).toSMul
    letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
    f • m = chartReadHom N v f * m := rfl

theorem chartGerm_scalarTower (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    letI := chartGermAlgebra N v
    letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N v).toSMul
    letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
    IsScalarTower ℂ (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N v
  letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N v).toSMul
  letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
  refine ⟨fun c f m => ?_⟩
  refine Germ.inductionOn m fun f => ?_
  rw [chartGerm_smul, chartGerm_smul, Algebra.smul_def, map_mul,
    chartReadHom_apply, chartRead_algebraMap, chartReadHom_apply]
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z => mul_assoc c _ _

/-- Analytic differentiation of the actual original chart germs. -/
def chartReadDerivation (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    letI := chartGermAlgebra N v
    letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N v).toSMul
    letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
    Derivation ℂ (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N v
  letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N v).toSMul
  letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
  exact {
    toFun := fun f => (deriv (chartRead N v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
    map_add' := fun f g => by
      rw [← Germ.coe_add]
      exact Germ.coe_eq.mpr (deriv_chartRead_add N v f g)
    map_smul' := fun c f => by
      rw [RingHom.id_apply, ← Germ.coe_smul]
      exact Germ.coe_eq.mpr (deriv_chartRead_smul N v c f)
    map_one_eq_zero' := by
      change (deriv (chartRead N v 1) : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0
      rw [deriv_chartRead_one, Germ.coe_zero]
    leibniz' := fun f g => by
      change (deriv (chartRead N v (f * g)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) =
        f • (deriv (chartRead N v g) : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
          g • (deriv (chartRead N v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
      rw [chartGerm_smul, chartGerm_smul, chartReadHom_apply, chartReadHom_apply,
        ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      filter_upwards [deriv_chartRead_mul N v f g] with z hz
      rw [hz]
      simp only [Pi.add_apply, Pi.mul_apply]
      ring }

theorem chartReadDerivation_apply (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) :
    chartReadDerivation N v f = (deriv (chartRead N v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := rfl

theorem chartReadDerivation_lift_smul_D (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (h g : modularFunctionFieldOver N ℂ) :
    letI := chartGermAlgebra N v
    letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N v).toSMul
    letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
    letI := chartGerm_scalarTower N v
    (chartReadDerivation N v).liftKaehlerDifferential (h • D ℂ (modularFunctionFieldOver N ℂ) g) =
      (chartRead N v h * deriv (chartRead N v g) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N v
  letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N v).toSMul
  letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
  letI := chartGerm_scalarTower N v
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, chartReadDerivation_apply,
    chartGerm_smul, chartReadHom_apply]

theorem readDifferential_eq_expression_germ (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) (h g : modularFunctionFieldOver N ℂ)
    (he : ω = h • D ℂ (modularFunctionFieldOver N ℂ) g) :
    readDifferential N v ω =ᶠ[𝓝[≠] (0 : ℂ)]
      chartRead N v h * deriv (chartRead N v g) := by
  letI := chartGermAlgebra N v
  letI : SMul (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N v).toSMul
  letI : Module (modularFunctionFieldOver N ℂ) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N v)
  letI := chartGerm_scalarTower N v
  haveI := original_place_dCoordGenerates N ℂ v
  have he' : ω = v.differentialCoeff ω • D ℂ (modularFunctionFieldOver N ℂ) v.uniformizer :=
    (v.differentialCoeff_smul_dCoord ω).symm
  have h1 := chartReadDerivation_lift_smul_D N v (v.differentialCoeff ω) v.uniformizer
  have h2 := chartReadDerivation_lift_smul_D N v h g
  rw [← he'] at h1
  rw [← he] at h2
  exact Germ.coe_eq.mp (h1.symm.trans h2)

end
end Dubon2026.SourceFunctionField.OriginalChart
