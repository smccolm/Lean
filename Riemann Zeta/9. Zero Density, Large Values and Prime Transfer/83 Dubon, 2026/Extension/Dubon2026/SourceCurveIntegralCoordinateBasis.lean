import Dubon2026.SourceCurveCoordinateSupport
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Polynomial.Basis

/-! DUB-17/18 -> function-field Riemann--Roch -> bounded global index.
Pinned integral-basis existence gives a full field basis regular outside
the coordinate poles. Pinned scalar-tower linear independence then counts
its independent polynomial multiples. These are the substantive basis
inputs of the source PoleDivisorPackage argument, without its general
place-restriction framework.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial

theorem exists_basis_regular_outside_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] :
    ∃ u : Fin (Module.finrank (RatFunc K) F) → F,
      LinearIndependent (RatFunc K) u ∧
        ∀ i (v : Place K F), 0 ≤ v.ord (algebraMap (RatFunc K) F RatFunc.X) →
          0 ≤ v.ord (u i) := by
  letI : Algebra K[X] F := ((algebraMap (RatFunc K) F).comp
    (algebraMap K[X] (RatFunc K))).toAlgebra
  letI : IsScalarTower K[X] (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F a = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) (C a))
    rw [← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) F]
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral K[X] (RatFunc K) F
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨fun i => b (e.symm i), b.linearIndependent.comp _ e.symm.injective, ?_⟩
  intro i v hv
  apply v.ord_nonneg_of_mem
  apply integralClosure_mem_of_base_mem v (c := ⟨b (e.symm i), hb (e.symm i)⟩)
  apply polynomial_mem_of_coordinate_mem v
  change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
  rw [RatFunc.algebraMap_X]
  exact v.mem_of_ord_nonneg hv

theorem linearIndependent_powers_of_transcendental
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx
  have hX : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have he : (fun j : ℕ => x ^ j) =
      (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j
    simp
  rw [he]
  exact hX.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

theorem linearIndependent_coordinate_powers_mul
    {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    {x : E} {n : ℕ} {u : Fin n → F}
    (hx : Transcendental K x) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have he : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) =
      (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def, map_pow]
  rw [he]
  exact linearIndependent_smul (R := K) (S := E) (A := F)
    (linearIndependent_powers_of_transcendental hx) hu

end
end Dubon2026.SourceCurve
