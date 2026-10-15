import Dubon2026.OriginalProductH2Detection
import Dubon2026.OriginalTransportedOrbitH2
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Third cohomology vanishing for the original coefficient product

Coordinate primitives assemble into one actual product primitive. This
specific degree-three input is needed to show that quotienting outside
units preserves H2 for noncyclic arithmetic extensions, so the existing
full-class H2 results apply to DUB-17's class-formation coefficient.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep.{0} R G)

/-- The original cochain differential is coordinatewise on the literal product coefficient. -/
theorem originalPiCochain_d_coordinate (n : ℕ)
    (c : (Fin n → G) → originalPiRep A) (g : Fin (n + 1) → G) (i : ι) :
    inhomogeneousCochains.d (originalPiRep A) n c g i =
      inhomogeneousCochains.d (A i) n (fun s => c s i) g := by
  classical
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply]
  change (A i).ρ (g 0) (c (fun j => g j.succ) i) +
    (∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) g)) i = _
  let e := (originalPiRepProjection A i).hom.toLinearMap
  change (A i).ρ (g 0) (c (fun j => g j.succ) i) +
    e (∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) g)) = _
  rw [map_sum]
  congr 1

/-- Zero third cohomology of every original factor implies zero third cohomology of their actual product. -/
theorem originalPi_third_cohomology_zero
    (hz : ∀ i, Limits.IsZero (groupCohomology (A i) 3)) :
    Limits.IsZero (groupCohomology (originalPiRep A) 3) := by
  have criterion (B : Rep R G) : Limits.IsZero (groupCohomology B 3) ↔
      ∀ c : (Fin 3 → G) → B, inhomogeneousCochains.d B 3 c = 0 →
        ∃ b : (Fin 2 → G) → B, inhomogeneousCochains.d B 2 b = c := by
    change Limits.IsZero ((groupCohomology.inhomogeneousCochains B).homology 3) ↔ _
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    rw [HomologicalComplex.exactAt_iff' _ 2 3 4 (by simp) (by simp)]
    exact ShortComplex.moduleCat_exact_iff _
  apply (criterion _).mpr
  intro c hc
  have hp (i : ι) : ∃ b : (Fin 2 → G) → A i,
      inhomogeneousCochains.d (A i) 2 b = fun g => c g i := by
    have hc' : inhomogeneousCochains.d (A i) 3 (fun g => c g i) = 0 := by
      funext g
      rw [← originalPiCochain_d_coordinate]
      have he := congrArg (fun f : (Fin 4 → G) → originalPiRep A => f g i) hc
      exact he
    exact (criterion _).mp (hz i) (fun g => c g i) hc'
  choose b hb using hp
  refine ⟨fun g i => b i g, ?_⟩
  funext g i
  change inhomogeneousCochains.d (originalPiRep A) 2 (fun g i => b i g) g i = c g i
  rw [originalPiCochain_d_coordinate]
  exact congrFun (hb i) g

variable (R G ι) [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- Actual stabilizer H3 vanishing kills the original transported-product H3. -/
theorem originalTransported_third_zero_of_stabilizers
    (hz : ∀ ω : MulAction.orbitRel.Quotient G ι,
      Limits.IsZero (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω)) 3)) :
    Limits.IsZero (groupCohomology (transportedPiRep R G ι M T T_one T_mul) 3) := by
  let B := transportedOrbitFactorRep R G ι M T T_one T_mul
  have hb (ω : MulAction.orbitRel.Quotient G ι) :
      Limits.IsZero (groupCohomology (B ω) 3) :=
    Limits.IsZero.of_iso (hz ω)
      (transportedOrbitFactorCohomologyIso R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω) 3)
  exact Limits.IsZero.of_iso (originalPi_third_cohomology_zero B hb)
    ((groupCohomology.functor R G 3).mapIso
      (transportedOrbitProductIso R G ι M T T_one T_mul))

end
end Dubon2026
