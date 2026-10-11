import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual scalar quotients and their cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (r : R)

/-- The literal image of scalar multiplication in the original representation. -/
def repScalarRange : Submodule R A :=
  LinearMap.range (r • (LinearMap.id : A →ₗ[R] A))

/-- The original action preserves the image of its original scalar multiplication. -/
theorem repScalarRange_stable (g : G) :
    repScalarRange A r ≤ (repScalarRange A r).comap (A.ρ g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨A.ρ g y, by simp⟩

/-- The original representation modulo the actual scalar image. -/
def repScalarQuotient : Rep R G :=
  A.quotient (repScalarRange A r) (repScalarRange_stable A r)

/-- The actual scalar map followed by the original quotient map. -/
def repScalarShortComplex : ShortComplex (Rep R G) where
  X₁ := A
  X₂ := A
  X₃ := repScalarQuotient A r
  f := Rep.ofHom ⟨r • (LinearMap.id : A →ₗ[R] A), by intro g; ext x; simp⟩
  g := A.mkQ (repScalarRange A r) (repScalarRange_stable A r)
  zero := by
    ext x
    change (Submodule.Quotient.mk (r • x) : A ⧸ repScalarRange A r) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- Injectivity of the genuine scalar map makes its actual quotient sequence
short exact; exactness is proved from the literal range and kernel. -/
theorem repScalarShortComplex_shortExact
    (hinj : Function.Injective (fun x : A => r • x)) :
    (repScalarShortComplex A r).ShortExact where
  exact := by
    apply ((repScalarShortComplex A r).exact_map_iff_of_faithful
      (forget₂ (Rep R G) (ModuleCat R))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change repScalarRange A r = LinearMap.ker (repScalarRange A r).mkQ
    exact (Submodule.ker_mkQ _).symm
  mono_f := (Rep.mono_iff_injective _).mpr hinj
  epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The connecting homomorphism in the genuine long exact sequence proves
vanishing for the original scalar quotient from the two adjacent original
cohomology groups. The quotient is not assumed acyclic. -/
theorem repScalarQuotient_groupCohomology_isZero
    (hinj : Function.Injective (fun x : A => r • x)) (n : ℕ)
    (hn : Limits.IsZero (groupCohomology A n))
    (hs : Limits.IsZero (groupCohomology A (n + 1))) :
    Limits.IsZero (groupCohomology (repScalarQuotient A r) n) := by
  let hX := repScalarShortComplex_shortExact A r hinj
  exact @Limits.IsZero.of_mono _ _ _ _ _ (groupCohomology.δ hX n (n + 1) rfl)
    (groupCohomology.mono_δ_of_isZero hX n hn) hs

end
end Dubon2026
