import Dubon2026.ContinuousRepresentationRestriction
import Mathlib.GroupTheory.Coset.Basic

/-! # Finite-index determination of original continuous one-cocycles

For the local trace-zero duality route, this reduces full cocycle finiteness to
the constant action on an actual finite splitting field. No spectral sequence
or assumed H1 dimension is needed for this finiteness step.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (S : Subgroup G)

/-- An original continuous one-cocycle is determined by its actual restriction
and its original values on one representative of each genuine coset. -/
theorem continuousCocycleOne_coset_restriction_injective :
    Function.Injective (fun c : continuousRepresentationCocyclesOne A =>
      ((fun t : G ⧸ S => c.val t.out),
        continuousRepresentationCocycleOneRestriction A S.subtype continuous_subtype_val c)) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  let t : G ⧸ S := QuotientGroup.mk g
  have hu : t.out⁻¹ * g ∈ S := QuotientGroup.eq.mp (Quotient.out_eq t)
  let u : S := ⟨t.out⁻¹ * g, hu⟩
  have hcoset : c.val t.out = d.val t.out := congrArg (fun p => p.1 t) h
  have hsub : c.val (u : G) = d.val (u : G) := congrArg (fun p => p.2.val u) h
  have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property t.out (u : G)
  have hd := (groupCohomology.mem_cocycles₁_iff _).mp d.val.property t.out (u : G)
  have hg : t.out * (u : G) = g := mul_inv_cancel_left _ _
  rw [hg] at hc hd
  exact hc.trans ((congrArg₂ (fun a b => A.ρ t.out a + b) hsub hcoset).trans hd.symm)

include S in
/-- A finite original coefficient module and finitely many genuine cosets
reduce finiteness of all original continuous cocycles to their actual restrictions. -/
theorem continuousCocyclesOne_finite_of_restriction [Finite A] [Finite (G ⧸ S)]
    [Finite (continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype))] :
    Finite (continuousRepresentationCocyclesOne A) :=
  Finite.of_injective _ (continuousCocycleOne_coset_restriction_injective A S)

end
end Dubon2026
