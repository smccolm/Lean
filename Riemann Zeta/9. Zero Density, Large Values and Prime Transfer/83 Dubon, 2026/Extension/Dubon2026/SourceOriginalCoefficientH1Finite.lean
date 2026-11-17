import Dubon2026.ArithmeticFiniteCoefficientH1

/-! DUB-17/18 -> finite families of original detecting primes -> finiteness
of the actual original twisted H1 space. Restrict only the coefficient scalars
of the same action and continuous cocycles, then reuse native prime-field finiteness. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Finite original coefficient modules have finitely many genuine arithmetic
continuous cocycles, over any field of the prescribed characteristic. -/
theorem rationalArithmeticOriginalCoefficientCocycles_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (A : Rep.{0} F (rationalArithmeticGaloisGroup a))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul F A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2)) :
    Finite (continuousRepresentationCocyclesOne A) := by
  let j := ZMod.castHom (dvd_refl p) F
  letI : Module (ZMod p) A := Module.compHom A j
  letI : ContinuousSMul (ZMod p) A := ⟨continuous_of_discreteTopology⟩
  let ρp : Representation (ZMod p) (rationalArithmeticGaloisGroup a) A :=
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
  have hB : Continuous (fun z : rationalArithmeticGaloisGroup a × B => B.ρ z.1 z.2) := hA
  haveI : Finite (continuousRepresentationCocyclesOne B) :=
    rationalArithmeticFiniteCoefficientCocycles_finite a ha p hpa B hB
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
theorem rationalArithmeticOriginalCoefficientH1_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (A : Rep.{0} F (rationalArithmeticGaloisGroup a))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul F A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2)) :
    Finite (ContinuousRepresentationH1 A hA) := by
  haveI := rationalArithmeticOriginalCoefficientCocycles_finite a ha p hpa A hA
  exact Finite.of_surjective (continuousRepresentationCoboundariesOne A hA).mkQ
    (Submodule.mkQ_surjective _)

end
end Dubon2026
