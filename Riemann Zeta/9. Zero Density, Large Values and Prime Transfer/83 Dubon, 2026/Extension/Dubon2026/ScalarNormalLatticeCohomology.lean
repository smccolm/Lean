import Dubon2026.LocalFieldNormalLatticeUnits
import Dubon2026.NormalBasisLatticeCohomology

/-! # The actual Galois action and cohomology of original scalar normal lattices -/

namespace Dubon2026
noncomputable section

open scoped BigOperators nonZeroDivisors

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r : R)

/-- The original Galois action on the literal scalar image of the original
normal-basis lattice. Stability follows from the original coefficient action. -/
def scalarNormalLatticeRep : Rep R Gal(L/K) := Rep.of
  ({ toFun σ :=
      { toFun x := ⟨σ x, scalarLatticeImage_galois_stable R K L
          (Submodule.span R (Set.range b))
          (fun τ _ hx => normalBasis_span_galois_stable R K L b hb τ hx) r σ x.property⟩
        map_add' x y := Subtype.ext (map_add σ (x : L) (y : L))
        map_smul' a x := Subtype.ext ((σ.restrictScalars R).toLinearMap.map_smul a (x : L)) }
     map_one' := by ext x; rfl
     map_mul' σ τ := by ext x; rfl } :
    Representation R Gal(L/K) (scalarLatticeImage (Submodule.span R (Set.range b)) r))

/-- Multiplication by the nonzero original base scalar identifies the
original lattice with its literal image, by actual injectivity in the field. -/
def scalarNormalLatticeLinearEquiv (hr : r ≠ 0) :
    Submodule.span R (Set.range b) ≃ₗ[R]
      scalarLatticeImage (Submodule.span R (Set.range b)) r := by
  have hmap : algebraMap R L r ≠ 0 := by
    intro h
    apply hr
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply, map_zero] using h
  exact Submodule.equivMapOfInjective (r • (LinearMap.id : L →ₗ[R] L))
    (fun x y h => mul_left_cancel₀ hmap (by
      change r • x = r • y at h
      simpa only [Algebra.smul_def] using h)) _

/-- The actual restricted normal basis, scaled by the original nonzero
coefficient, is a basis of that same original scalar lattice. -/
def scalarNormalLatticeBasis (hr : r ≠ 0) :
    Module.Basis Gal(L/K) R (scalarNormalLatticeRep R K L b hb r) :=
  (b.restrictScalars R).map (scalarNormalLatticeLinearEquiv R K L b r hr)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The original scaled basis is regularly permuted by the original Galois action. -/
theorem scalarNormalLatticeBasis_action (hr : r ≠ 0) (σ τ : Gal(L/K)) :
    (scalarNormalLatticeRep R K L b hb r).ρ σ
        (scalarNormalLatticeBasis R K L b hb r hr τ) =
      scalarNormalLatticeBasis R K L b hb r hr (σ * τ) := by
  apply Subtype.ext
  change σ (r • (((b.restrictScalars R) τ : Submodule.span R (Set.range b)) : L)) =
    r • (((b.restrictScalars R) (σ * τ) : Submodule.span R (Set.range b)) : L)
  rw [Module.Basis.restrictScalars_apply, Module.Basis.restrictScalars_apply]
  have hs : σ (r • b τ) = r • σ (b τ) :=
    (σ.restrictScalars R).toLinearMap.map_smul r (b τ)
  rw [hs, hb τ, hb (σ * τ)]
  rfl

omit [IsGalois K L] in
/-- Every positive cohomology group of each actual nonzero scalar normal
lattice vanishes by its original regularly permuted basis and genuine Shapiro. -/
theorem scalarNormalLattice_groupCohomology_isZero (hr : r ≠ 0) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (groupCohomology (scalarNormalLatticeRep R K L b hb r) (n + 1)) := by
  exact regularBasis_groupCohomology_isZero (scalarNormalLatticeRep R K L b hb r)
    (scalarNormalLatticeBasis R K L b hb r hr)
    (scalarNormalLatticeBasis_action R K L b hb r hr) n

omit [IsGalois K L] in
/-- Every actual invariant of the original scalar normal lattice has an
original action-norm preimage in that same lattice. -/
theorem scalarNormalLattice_invariant_mem_norm (hr : r ≠ 0)
    (a : scalarNormalLatticeRep R K L b hb r)
    (ha : ∀ σ, (scalarNormalLatticeRep R K L b hb r).ρ σ a = a) :
    ∃ x : scalarNormalLatticeRep R K L b hb r,
      ∑ σ : Gal(L/K), (scalarNormalLatticeRep R K L b hb r).ρ σ x = a := by
  exact regularBasis_invariant_mem_norm (scalarNormalLatticeRep R K L b hb r)
    (scalarNormalLatticeBasis R K L b hb r hr)
    (scalarNormalLatticeBasis_action R K L b hb r hr) a ha

end
end Dubon2026
