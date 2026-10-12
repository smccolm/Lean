import Dubon2026.LocalFieldFiniteCoefficientH1
import Mathlib.Algebra.Module.ZMod

/-! # Actual local H1 finiteness over the original coefficient field

Restriction to the prime field keeps the original coefficient elements, action
and continuous cocycles. This supplies finiteness for the finite extension-field
coefficients in DUB-17's trace-zero local duality dependency, without assuming
triviality of their action or constructing a new cohomology theory.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G] (q : ℕ) [Fact q.Prime] [CharP k q]
  (A : Rep.{0} k G)

/-- The original coefficient group carries its canonical prime-field action. -/
local instance finiteScalarPrimeModule : Module (ZMod q) A :=
  AddCommGroup.zmodModule (fun a => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k q, zero_smul])

/-- The original action, with the same values, viewed over the prime field. -/
abbrev finiteScalarPrimeRep : Rep (ZMod q) G :=
  Rep.of {
    toFun g := (A.ρ g).toAddMonoidHom.toZModLinearMap q
    map_one' := by
      apply LinearMap.ext
      intro a
      exact congrArg (fun f : A →ₗ[k] A => f a) A.ρ.map_one
    map_mul' g h := by
      apply LinearMap.ext
      intro a
      exact congrArg (fun f : A →ₗ[k] A => f a) (A.ρ.map_mul g h) }

variable [TopologicalSpace k] [DiscreteTopology k] [TopologicalSpace G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Original scalars act continuously on the original discrete coefficient group. -/
local instance finiteScalarOriginalContinuousSMul : ContinuousSMul k A :=
  ⟨continuous_of_discreteTopology⟩

/-- Prime scalars act continuously on the original discrete coefficient group. -/
local instance finiteScalarPrimeContinuousSMul : ContinuousSMul (ZMod q) A :=
  ⟨continuous_of_discreteTopology⟩

/-- The literal original continuous cocycle also satisfies the prime-field
cocycle equation, because the action has exactly the same values. -/
def finiteScalarPrimeCocycle (c : continuousRepresentationCocyclesOne A) :
    continuousRepresentationCocyclesOne (finiteScalarPrimeRep q A) :=
  ⟨⟨c.val, (groupCohomology.mem_cocycles₁_iff _).mpr
    ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property)⟩, c.property⟩

/-- Viewing actual cocycles over the prime field preserves all their values. -/
theorem finiteScalarPrimeCocycle_injective :
    Function.Injective (finiteScalarPrimeCocycle q A) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x => x.val.val) h

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- All original local continuous cocycles with finite characteristic-q
coefficients are finite, including finite extension-field coefficients. -/
theorem localField_finiteScalarCoefficientCocycles
    (B : Rep.{0} k Gal(Ω/K)) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2)) (hq : (q : K) ≠ 0) :
    Finite (continuousRepresentationCocyclesOne B) := by
  haveI := localField_finiteCoefficientCocycles K Ω q (finiteScalarPrimeRep q B) hB hq
  exact Finite.of_injective _ (finiteScalarPrimeCocycle_injective q B)

/-- The full original local H1 over the original coefficient field is finite;
the proof quotients its own coboundaries after proving its cocycles finite. -/
theorem localField_finiteScalarCoefficientH1
    (B : Rep.{0} k Gal(Ω/K)) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2)) (hq : (q : K) ≠ 0) :
    Finite (ContinuousRepresentationH1 B hB) := by
  haveI := localField_finiteScalarCoefficientCocycles q K Ω B hB hq
  exact Finite.of_surjective (continuousRepresentationCoboundariesOne B hB).mkQ
    (Submodule.mkQ_surjective _)

end
end Dubon2026
