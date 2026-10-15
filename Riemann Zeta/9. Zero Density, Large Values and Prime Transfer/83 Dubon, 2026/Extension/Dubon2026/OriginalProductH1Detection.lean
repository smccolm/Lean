import Dubon2026.OriginalProductH2Detection
import Dubon2026.OriginalTransportedOrbitH2

/-! # Original product and transported-product H1 detection

Coordinate coboundaries give a literal product coboundary in degree one.
Together with the existing orbit/Shapiro comparison this is the missing
outside-unit H1 input for original invariant class-quotient descent on
the DUB-17 arithmetic class-formation and localization-duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)

/-- An actual product H1 class is zero if every original coordinate image is zero. -/
theorem originalPiH1_zero_of_coordinates (x : groupCohomology (originalPiRep A) 1)
    (hx : ∀ i, (groupCohomology.functor R G 1).map (originalPiRepProjection A i) x = 0) :
    x = 0 := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    apply (groupCohomology.H1π_eq_zero_iff c).mpr
    have hc (i : ι) : ∃ b : A i,
        groupCohomology.d₀₁ (A i) b = fun g => c g i := by
      let ci := groupCohomology.mapCocycles₁ (MonoidHom.id G) (originalPiRepProjection A i) c
      have hi : groupCohomology.H1π (A i) ci = 0 := by
        have hi := hx i
        change groupCohomology.map (MonoidHom.id G) (originalPiRepProjection A i) 1
          (groupCohomology.H1π (originalPiRep A) c) = 0 at hi
        rwa [groupCohomology.H1π_comp_map_apply] at hi
      exact (groupCohomology.H1π_eq_zero_iff ci).mp hi
    choose b hb using hc
    refine ⟨b, ?_⟩
    funext g i
    exact congrFun (hb i) g

/-- Vanishing of the original factor H1 groups kills their arbitrary product H1. -/
theorem originalPi_first_cohomology_zero
    (hz : ∀ i, Limits.IsZero (groupCohomology (A i) 1)) :
    Limits.IsZero (groupCohomology (originalPiRep A) 1) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  apply originalPiH1_zero_of_coordinates A x
  intro i
  exact (ModuleCat.isZero_iff_subsingleton.mp (hz i)).elim _ _

variable (R G ι) [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- Original stabilizer H1 vanishing kills the actual transported-product H1. -/
theorem originalTransported_first_zero_of_stabilizers
    (hz : ∀ ω : MulAction.orbitRel.Quotient G ι,
      Limits.IsZero (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω)) 1)) :
    Limits.IsZero (groupCohomology (transportedPiRep R G ι M T T_one T_mul) 1) := by
  let B := transportedOrbitFactorRep R G ι M T T_one T_mul
  have hb (ω : MulAction.orbitRel.Quotient G ι) :
      Limits.IsZero (groupCohomology (B ω) 1) :=
    Limits.IsZero.of_iso (hz ω)
      (transportedOrbitFactorCohomologyIso R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω) 1)
  exact Limits.IsZero.of_iso (originalPi_first_cohomology_zero B hb)
    ((groupCohomology.functor R G 1).mapIso
      (transportedOrbitProductIso R G ι M T T_one T_mul))

end
end Dubon2026
