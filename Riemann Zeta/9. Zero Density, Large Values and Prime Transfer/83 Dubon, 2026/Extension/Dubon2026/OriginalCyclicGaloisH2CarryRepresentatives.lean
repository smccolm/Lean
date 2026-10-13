import Dubon2026.CyclicTwoCocycleCarryComparison
import Dubon2026.GaloisUnitInvariantBaseDescent

/-! # Original global cyclic H2 classes have actual base-unit carry representatives

The explicit cocycle comparison supplies an invariant original field-unit
period. Proved fixed-field descent recovers an actual unit of the same base
field, giving the literal carry cocycle required by the local character
pairing. This advances DUB-17's cyclic principal-product to invariant
sum-zero implication without a finite global norm-quotient assumption.
-/
namespace Dubon2026
noncomputable section

/-- Every original finite Galois H2 class with a nontrivial faithful cyclic index is represented by the literal character carry of an actual original base-field unit. -/
theorem originalCyclicGaloisH2_exists_characterCarry
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {n : ℕ} [NeZero n] (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (hn : 1 < n)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ u : Kˣ, groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
      (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ.toMonoidHom
        (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u)) = x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    let g := χ.symm (Multiplicative.ofAdd 1)
    have hχ : χ g = Multiplicative.ofAdd 1 := χ.apply_symm_apply _
    let a := representationCyclicTwoCochainPeriodSum (Rep.ofAlgebraAutOnUnits K L) g n c
    have ha : a ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants :=
      cyclicCarryPeriod_invariant (Rep.ofAlgebraAutOnUnits K L) χ g hχ c
    obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base a ha
    refine ⟨u, ?_⟩
    rw [cyclicTwoCocycleH2_eq_carry_of_period (Rep.ofAlgebraAutOnUnits K L) χ g hχ hn c]
    apply congrArg (groupCohomology.H2π _)
    apply groupCohomology.cocycles₂_ext
    intro σ τ
    change zmodAdditionCarry (χ σ).toAdd (χ τ).toAdd • galoisUnitsBaseCoefficient u =
      zmodAdditionCarry (χ σ).toAdd (χ τ).toAdd • a
    rw [hu]

end
end Dubon2026
