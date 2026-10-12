import Dubon2026.ContinuousRootH1Radicals
import Dubon2026.ContinuousExactCoefficientLifts

/-! # The actual continuous root cocycle of an original radical

This supplies the forward Kummer map for the same H1 quotient appearing in the
local cup. The inverse radical construction and zero-class criterion are reused.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (a : Kˣ) (β : Ωˣ) (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)

include hβ in
omit [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] in
/-- The unit coboundary of an original radical lies in the actual root inclusion
range, because its nth power is the ratio of a fixed base-field unit. -/
theorem galoisRadicalCoboundary_mem_root_range (g : Gal(Ω/K)) :
    (continuousRepresentationCoboundaryOne (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
      (Rep.toAdditive.symm (Additive.ofMul β))).val g ∈
        LinearMap.range (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap := by
  rw [galoisKummerCoefficient_exact]
  change (g • β / β) ^ n = 1
  rw [div_pow, ← smul_pow', hβ, galois_base_unit_fixed, div_self']

/-- The original radical produces an actual continuous root-valued one-cocycle,
using the genuine inverse of the root inclusion on its actual range. -/
def galoisRootRadicalOneCocycle :
    continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) := by
  let A := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n
  let B := Rep.ofAlgebraAutOnUnits K Ω
  let φ := (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
  have hinj := galoisKummerInclusion_injective (K := K) (Ω := Ω) n
  have hcomm : ∀ g x, φ (A.ρ g x) = B.ρ g (φ x) :=
    Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n)
  let d := continuousRepresentationCoboundaryOne B
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    (Rep.toAdditive.symm (Additive.ofMul β))
  let f := fun g => exactCoefficientPreimage φ hinj (d.val g)
  have hi : ∀ g, φ (f g) = d.val g := by
    intro g
    exact exactCoefficientPreimage_map φ hinj (d.val g)
      (galoisRadicalCoboundary_mem_root_range n a β hβ g)
  refine ⟨⟨f, ?_⟩, (exactCoefficientPreimage_continuous φ hinj).comp d.property⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  apply hinj
  change φ (f (g * h)) = φ (A.ρ g (f h) + f g)
  rw [map_add, hcomm, hi, hi, hi]
  exact (groupCohomology.mem_cocycles₁_iff _).mp d.val.property g h

/-- The original cocycle takes exactly the Galois ratio of the same original
radical, through the same original root inclusion. -/
theorem galoisRootRadicalOneCocycle_ratio (g : Gal(Ω/K)) :
    ((Additive.toMul (Rep.toAdditive ((galoisRootRadicalOneCocycle n a β hβ).val g)) :
      rootsOfUnity n Ω) : Ωˣ) = g • β / β := by
  exact exactCoefficientPreimage_map
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerInclusion_injective (K := K) (Ω := Ω) n) _
    (galoisRadicalCoboundary_mem_root_range n a β hβ g)

/-- The forward radical cocycle has precisely the actual base nth-power kernel. -/
theorem galoisRootRadicalOneCocycle_class_zero_iff :
    (Submodule.Quotient.mk (galoisRootRadicalOneCocycle n a β hβ) :
      ContinuousRepresentationH1
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
        (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) = 0 ↔
      a ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
  continuousRootOneCocycle_class_zero_iff_power n
    (galoisRootRadicalOneCocycle n a β hβ) a β hβ
    (fun g => (galoisRootRadicalOneCocycle_ratio n a β hβ g).symm)

end
end Dubon2026
