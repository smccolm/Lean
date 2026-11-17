import Dubon2026.LocalFieldFiniteCoefficientH1

/-! DUB-17/18 -> original auxiliary-prime local deformation inputs ->
original-coefficient local unramified H1 dimension. Native finite prime-field
local cocycles suffice after restricting scalars on the same action. -/
namespace Dubon2026
noncomputable section

/-- Finite original coefficient modules have finitely many genuine local
continuous cocycles, over any field of the prescribed characteristic. -/
theorem localFieldOriginalCoefficientCocycles_finite
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (A : Rep.{0} F Gal(Ω/K))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul F A]
    (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2)) :
    Finite (continuousRepresentationCocyclesOne A) := by
  let j := ZMod.castHom (dvd_refl p) F
  letI : Module (ZMod p) A := Module.compHom A j
  letI : ContinuousSMul (ZMod p) A := ⟨continuous_of_discreteTopology⟩
  let ρp : Representation (ZMod p) Gal(Ω/K) A :=
    { toFun := fun g =>
        { toFun := A.ρ g
          map_add' := (A.ρ g).map_add
          map_smul' := fun r x => by
            change A.ρ g (j r • x) = j r • A.ρ g x
            exact (A.ρ g).map_smul (j r) x }
      map_one' := by
        ext x
        change A.ρ 1 x = x
        rw [map_one, Module.End.one_apply]
      map_mul' := fun g h => by
        ext x
        change A.ρ (g * h) x = A.ρ g (A.ρ h x)
        rw [map_mul, Module.End.mul_apply] }
  let B := Rep.of ρp
  have hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2) := hA
  haveI : Finite (continuousRepresentationCocyclesOne B) :=
    localField_finiteCoefficientCocycles K Ω p B hB hp
  let e : continuousRepresentationCocyclesOne A → continuousRepresentationCocyclesOne B :=
    fun c => ⟨⟨fun g => c.val g, by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro g h
      exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h⟩, c.property⟩
  apply Finite.of_injective e
  intro c d he
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact congrArg (fun z : continuousRepresentationCocyclesOne B => z.val g) he

/-- The actual original H1 quotient is finite; no class-finiteness premise
or comparison with a different H1 space is assumed. -/
theorem localFieldOriginalCoefficientH1_finite
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (A : Rep.{0} F Gal(Ω/K))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul F A]
    (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2)) :
    Finite (ContinuousRepresentationH1 A hA) := by
  haveI := localFieldOriginalCoefficientCocycles_finite K Ω p hp A hA
  exact Finite.of_surjective (continuousRepresentationCoboundariesOne A hA).mkQ
    (Submodule.mkQ_surjective _)

end
end Dubon2026
