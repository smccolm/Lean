import Dubon2026.IntegralNormalBasisLattice
import Dubon2026.RegularBasisCohomology
import Dubon2026.RegularBasisNorm

/-! # Actual positive cohomology vanishing for the original normal-basis lattice -/

namespace Dubon2026
noncomputable section

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))

/-- The actual Galois action on the original base-ring span of the original
normal basis. Stability is proved by span induction in the original field. -/
def normalBasisLatticeRep : Rep R Gal(L/K) := Rep.of
  ({ toFun σ :=
      { toFun x := ⟨σ x, normalBasis_span_galois_stable R K L b hb σ x.property⟩
        map_add' x y := Subtype.ext (map_add σ (x : L) (y : L))
        map_smul' a x := Subtype.ext ((σ.restrictScalars R).toLinearMap.map_smul a (x : L)) }
     map_one' := by ext x; rfl
     map_mul' σ τ := by ext x; rfl } :
    Representation R Gal(L/K) (Submodule.span R (Set.range b)))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The original restricted basis is regularly permuted by the actual
Galois action on the original lattice. -/
theorem normalBasisLatticeRep_basis_action (σ τ : Gal(L/K)) :
    (normalBasisLatticeRep R K L b hb).ρ σ ((b.restrictScalars R) τ) =
      (b.restrictScalars R) (σ * τ) := by
  apply Subtype.ext
  change σ (((b.restrictScalars R) τ : Submodule.span R (Set.range b)) : L) =
    (((b.restrictScalars R) (σ * τ) : Submodule.span R (Set.range b)) : L)
  rw [Module.Basis.restrictScalars_apply, Module.Basis.restrictScalars_apply,
    hb τ, hb (σ * τ)]
  rfl

omit [IsGalois K L] in
/-- The actual positive cohomology of the original normal-basis lattice
vanishes by its proved regular action and the genuine Shapiro isomorphism.
This does not yet identify a multiplicative unit filtration with the lattice. -/
theorem normalBasisLattice_groupCohomology_isZero (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (groupCohomology (normalBasisLatticeRep R K L b hb) (n + 1)) := by
  exact regularBasis_groupCohomology_isZero (normalBasisLatticeRep R K L b hb)
    (b.restrictScalars R) (normalBasisLatticeRep_basis_action R K L b hb) n

omit [IsGalois K L] in
/-- Every original invariant lattice element is the actual Galois action
norm of an original lattice element. This supplies the degree-zero norm
calculation in addition to positive additive cohomology vanishing. -/
theorem normalBasisLattice_invariant_mem_norm
    (a : Submodule.span R (Set.range b))
    (ha : ∀ σ, (normalBasisLatticeRep R K L b hb).ρ σ a = a) :
    ∃ x : Submodule.span R (Set.range b),
      ∑ σ : Gal(L/K), (normalBasisLatticeRep R K L b hb).ρ σ x = a := by
  exact regularBasis_invariant_mem_norm (normalBasisLatticeRep R K L b hb)
    (b.restrictScalars R) (normalBasisLatticeRep_basis_action R K L b hb) a ha

end
end Dubon2026
