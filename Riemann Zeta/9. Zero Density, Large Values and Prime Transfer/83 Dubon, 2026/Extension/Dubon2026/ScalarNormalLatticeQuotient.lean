import Dubon2026.ScalarNormalLatticeCohomology
import Dubon2026.ScalarRepresentationQuotient
import Dubon2026.ScalarQuotientInvariantLift

/-! # Cohomology of the actual successive scalar normal-lattice quotients -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

/-- The internal scalar image of a lattice is precisely the literal scalar
image inside the original field, pulled back along the original inclusion. -/
theorem lattice_scalar_range_eq_comap
    {R L : Type} [CommRing R] [Field L] [Algebra R L]
    (A : Submodule R L) (s : R) :
    LinearMap.range (s • (LinearMap.id : A →ₗ[R] A)) =
      (scalarLatticeImage A s).comap A.subtype := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact (mem_scalarLatticeImage A s _).mpr ⟨a, a.property, rfl⟩
  · intro hx
    obtain ⟨a, ha, he⟩ := (mem_scalarLatticeImage A s (x : L)).mp hx
    exact ⟨⟨a, ha⟩, Subtype.ext he⟩

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R)

omit [IsDomain R] [FiniteDimensional K L] [IsGalois K L] in
/-- Multiplication by the original nonzero scalar is injective on the
actual scalar normal lattice, by the original field inclusion. -/
theorem scalarNormalLattice_smul_injective (hs : s ≠ 0) :
    Function.Injective
      (fun x : scalarNormalLatticeRep R K L b hb r => s • x) := by
  have hmap : algebraMap R L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply, map_zero] using h
  intro x y h
  apply Subtype.ext
  apply mul_left_cancel₀ hmap
  have hc := congrArg
    (fun z : scalarLatticeImage (Submodule.span R (Set.range b)) r => (z : L)) h
  change s • (x : scalarLatticeImage (Submodule.span R (Set.range b)) r).val =
    s • (y : scalarLatticeImage (Submodule.span R (Set.range b)) r).val at hc
  simpa only [Algebra.smul_def] using hc

omit [IsGalois K L] in
/-- Each original scalar normal-lattice quotient has zero positive
cohomology. This consumes the proved actual lattice cohomology on both sides
of its genuine scalar short exact sequence. -/
theorem scalarNormalLatticeQuotient_groupCohomology_isZero
    (hr : r ≠ 0) (hs : s ≠ 0) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (groupCohomology
        (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s) (n + 1)) := by
  exact repScalarQuotient_groupCohomology_isZero
    (scalarNormalLatticeRep R K L b hb r) s
    (scalarNormalLattice_smul_injective R K L b hb r s hs) (n + 1)
    (scalarNormalLattice_groupCohomology_isZero R K L b hb r hr n)
    (scalarNormalLattice_groupCohomology_isZero R K L b hb r hr (n + 1))

omit [IsGalois K L] in
/-- Every invariant of the literal successive scalar lattice quotient is an
actual action norm, using invariant lifting and the original normal basis. -/
theorem scalarNormalLatticeQuotient_invariant_mem_norm
    (hr : r ≠ 0) (hs : s ≠ 0)
    (q : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s)
    (hq : ∀ σ,
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ q = q) :
    ∃ x : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s,
      ∑ σ : Gal(L/K),
        (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ x = q := by
  exact repScalarQuotient_invariant_mem_norm (scalarNormalLatticeRep R K L b hb r) s
    (scalarNormalLattice_smul_injective R K L b hb r s hs)
    (scalarNormalLattice_groupCohomology_isZero R K L b hb r hr 0)
    (scalarNormalLattice_invariant_mem_norm R K L b hb r hr) q hq

end
end Dubon2026
