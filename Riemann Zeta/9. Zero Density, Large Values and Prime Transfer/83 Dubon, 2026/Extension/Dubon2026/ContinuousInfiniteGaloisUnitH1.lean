import Dubon2026.GaloisUnitCocycleFiniteDescent

/-! # Original continuous Hilbert 90 for an actual infinite Galois extension -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original nontrivial continuous Galois unit cocycle has an actual
Hilbert-90 unit witness in the original extension. Its genuine finite Galois
coefficient field and descended cocycle are constructed from normal periods. -/
theorem continuousInfiniteGaloisUnitCocycle_exists_unit
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ β : Ωˣ, ∀ g : Gal(Ω/K),
      g • β / β = Additive.toMul (Rep.toAdditive (c.val g)) := by
  obtain ⟨F, hvalues, hperiod⟩ := continuousGaloisUnitCocycle_exists_finiteField c
  obtain ⟨f, hf, hfactor⟩ := galoisUnitCocycle_exists_finite_descent F c.val hvalues hperiod
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  let i := Units.map F.toIntermediateField.val.toMonoidHom
  refine ⟨i β, ?_⟩
  intro g
  have haction : i (AlgEquiv.restrictNormalHom F g • β) = g • i β := by
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes g F β.val
  calc
    g • i β / i β = i (AlgEquiv.restrictNormalHom F g • β / β) := by
      rw [map_div, haction]
    _ = i (f (AlgEquiv.restrictNormalHom F g)) := congrArg i (hβ _)
    _ = Additive.toMul (Rep.toAdditive (c.val g)) := hfactor g

variable (hA : Continuous (fun z : Gal(Ω/K) × Rep.ofAlgebraAutOnUnits K Ω =>
  (Rep.ofAlgebraAutOnUnits K Ω).ρ z.1 z.2))

/-- The same original Hilbert-90 unit is an actual coefficient witness for
the original continuous additive-tagged coboundary, with its original action. -/
theorem continuousInfiniteGaloisUnitCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ v : Rep.ofAlgebraAutOnUnits K Ω,
      continuousRepresentationCoboundaryOne (Rep.ofAlgebraAutOnUnits K Ω) hA v = c := by
  obtain ⟨β, hβ⟩ := continuousInfiniteGaloisUnitCocycle_exists_unit c
  refine ⟨Rep.toAdditive.symm (Additive.ofMul β), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hβ g

/-- The actual continuous H1 of the original Galois unit action vanishes for
an arbitrary original Galois extension and discrete coefficients. Finiteness
is used only for the constructed coefficient subfield, not assumed of Ω/K. -/
theorem continuousInfiniteGaloisUnitH1_eq_zero
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω) hA) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact continuousInfiniteGaloisUnitCocycle_exists_coboundary hA c

end
end Dubon2026
