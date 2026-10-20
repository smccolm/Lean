import Dubon2026.NumberFieldPrincipalAdelesDiscrete
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Finiteness of principal elements with compact finite and bounded infinite parts

The arithmetic stabilizers in DUB-17 lie in a compact finite-adelic level.
This result turns their archimedean unitary entry bounds into finiteness,
without a separate common-denominator construction.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/-- A bounded closed ball in an original infinite completion is compact. -/
theorem numberFieldInfiniteCompletion_isCompact_norm_le
    (v : InfinitePlace K) (B : ℝ) : IsCompact {x : v.Completion | ‖x‖ ≤ B} := by
  have he := InfinitePlace.Completion.isometry_extensionEmbedding v
  have hc := he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall (0 : ℂ) B)
  have hn (x : v.Completion) :
      ‖InfinitePlace.Completion.extensionEmbedding v x‖ = ‖x‖ := by
    simpa only [map_zero, dist_zero_right] using he.dist_eq x 0
  convert hc using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hn]

omit [NumberField K] in
/-- The product of the bounded archimedean entry sets is compact in the original topology. -/
theorem numberFieldInfiniteAdeles_isCompact_bound (B : ℝ) :
    IsCompact {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ B} := by
  exact (show IsCompact {x : (v : InfinitePlace K) → v.Completion | ∀ v, ‖x v‖ ≤ B} from
    by
      convert (isCompact_univ_pi fun v =>
        numberFieldInfiniteCompletion_isCompact_norm_le K v B) using 1
      ext x
      simp)

/-- Compactness at finite places and an archimedean bound give only finitely many field elements. -/
theorem numberField_compactFinite_boundedInfinite_finite
    (C : Set (FiniteAdeleRing (𝓞 K) K)) (hC : IsCompact C) (B : ℝ) :
    {x : K | algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ C ∧
      ∀ v : InfinitePlace K, v x ≤ B}.Finite := by
  letI := numberFieldAdele_t2Space K
  letI := numberFieldAdelePrincipal_discreteTopology K
  let H := AdeleRing.principalSubgroup (𝓞 K) K
  let D : Set (AdeleRing (𝓞 K) K) :=
    {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ B} ×ˢ C
  have hD : IsCompact D := (numberFieldInfiniteAdeles_isCompact_bound K B).prod hC
  have hH : IsClosed (H : Set (AdeleRing (𝓞 K) K)) := AddSubgroup.isClosed_of_discrete
  have hf : ((Subtype.val : H → AdeleRing (𝓞 K) K) ⁻¹' D).Finite :=
    (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hD).finite_of_discrete
  let F : K → H := fun x => ⟨algebraMap K (AdeleRing (𝓞 K) K) x, x, rfl⟩
  have hF : Function.Injective F := by
    intro x y h
    let v : InfinitePlace K := Classical.choice inferInstance
    exact (algebraMap K v.Completion).injective (congrArg (fun z : H => z.val.1 v) h)
  apply (hf.preimage hF.injOn).subset
  intro x hx
  constructor
  · intro v
    change ‖algebraMap K v.Completion x‖ ≤ B
    rw [numberFieldInfiniteCompletion_norm]
    exact hx.2 v
  · exact hx.1

end
end Dubon2026
