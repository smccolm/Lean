import Dubon2026.GaloisKummerCoefficientSequence
import Dubon2026.DiscreteGaloisUnitActionContinuity

/-! # Original discrete Kummer coefficient topologies and genuine action continuity -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Integer scalar multiplication is jointly continuous for the original
root representation module, in the original discrete coefficient topology. -/
instance galoisRootDiscreteContinuousSMul :
    @ContinuousSMul ℤ (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).hV2.toSMul
      inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

omit [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] in
/-- The original root inclusion is continuous in the original discrete coefficient topologies. -/
theorem galoisKummerInclusion_continuous :
    Continuous (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap :=
  continuous_of_discreteTopology

omit [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] in
/-- The original unit power map is continuous in the original discrete coefficient topology. -/
theorem galoisKummerPower_continuous :
    Continuous (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap :=
  continuous_of_discreteTopology

/-- The original root-of-unity action is jointly continuous for the actual
Krull topology. Its genuine equivariant inclusion into original discrete units
is an embedding, and the actual unit action is already proved continuous. -/
theorem discreteGaloisRootAction_continuous [Algebra.IsIntegral K Ω] :
    Continuous (fun z : Gal(Ω/K) × galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n =>
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ z.1 z.2) := by
  let φ := (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
  have he : Topology.IsEmbedding φ :=
    (Function.leftInverse_invFun (galoisKummerInclusion_injective (K := K) (Ω := Ω) n)).isEmbedding
      continuous_of_discreteTopology continuous_of_discreteTopology
  apply he.continuous_iff.mpr
  have hc := (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)).comp
    (continuous_fst.prodMk ((galoisKummerInclusion_continuous (K := K) (Ω := Ω) n).comp continuous_snd))
  simpa only [Function.comp_def, φ, Representation.IntertwiningMap.toLinearMap_apply,
    Rep.hom_comm_apply] using hc

end
end Dubon2026
