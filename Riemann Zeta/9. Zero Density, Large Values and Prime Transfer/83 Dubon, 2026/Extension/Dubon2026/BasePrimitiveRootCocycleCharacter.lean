import Dubon2026.BasePrimitiveRootCoefficients

/-! # Actual root cocycles give actual finite characters over a base primitive root -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]

/-- An original continuous root cocycle is a genuine continuous finite
character under the actual base primitive-root identification. -/
def basePrimitiveRootCocycleCharacter
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    Gal(Ω/K) →ₜ* Multiplicative (ZMod n) := by
  let e := basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ
  refine { toFun := fun g => Multiplicative.ofAdd (e.symm (c.val g))
           map_one' := ?_
           map_mul' := ?_
           continuous_toFun := ?_ }
  · have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property 1 1
    rw [one_mul, basePrimitiveRootCoefficient_action hζ] at hc
    have hz : c.val 1 = 0 := add_eq_left.mp hc.symm
    change e.symm (c.val 1) = 0
    rw [hz, map_zero]
  · intro g h
    change e.symm (c.val (g * h)) = e.symm (c.val g) + e.symm (c.val h)
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h
    rw [basePrimitiveRootCoefficient_action hζ] at hc
    exact (congrArg e.symm hc).trans ((e.symm.map_add _ _).trans (add_comm _ _))
  · exact (show Continuous (fun x => Multiplicative.ofAdd (e.symm x)) from
      continuous_of_discreteTopology).comp c.property

/-- The actual character recovers the literal original cocycle values. -/
theorem basePrimitiveRootCocycleCharacter_apply
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) (g : Gal(Ω/K)) :
    basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ
      (basePrimitiveRootCocycleCharacter hζ c g).toAdd = c.val g :=
  (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ).apply_symm_apply (c.val g)

/-- A trivial actual character corresponds precisely to the zero original
cocycle. In particular a nonzero H1 representative gives a nontrivial character. -/
theorem basePrimitiveRootCocycleCharacter_eq_one_iff
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    basePrimitiveRootCocycleCharacter hζ c = 1 ↔ c = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have he := basePrimitiveRootCocycleCharacter_apply hζ c g
    rw [h] at he
    exact he.symm.trans (map_zero _)
  · rintro rfl
    apply ContinuousMonoidHom.ext
    intro g
    change (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ).symm 0 = 0
    exact map_zero _

end
end Dubon2026
