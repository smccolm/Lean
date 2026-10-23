import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Tactic

/-! The affine ideal-class route to the actual odd cyclic quotient map.
Adapted from TauCetiProject/TauCeti, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba; the point-class argument
credits Chris Birkbeck's AINTLIB. Only the elliptic-curve consumer is
needed: omit singular-curve cotangent spaces and the general isogeny category.
Dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation ->
arithmetic automorphy -> Frobenius/inertia -> modular-curve good reduction ->
reverse genus and inertia census -> cyclic modular-polynomial roots ->
explicit odd quotient homomorphism -> norm-induced map of ideal classes. -/
namespace Dubon2026.SourceEllipticClassGroup
noncomputable section
open Polynomial FractionalIdeal
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*}
  [CommRing P] [Algebra R P] [IsLocalization S P]
theorem isUnit_spanSingleton {x : P} (hx : IsUnit x) : IsUnit (spanSingleton S x) := by
  obtain ⟨u, rfl⟩ := hx
  exact IsUnit.of_mul_eq_one (spanSingleton S ((u⁻¹ : Pˣ) : P)) (by
    rw [spanSingleton_mul_spanSingleton, Units.mul_inv, spanSingleton_one])

/-- A fractional ideal is invertible exactly when its integral numerator is invertible.
This extends Mathlib's `FractionalIdeal.isUnit_num` to any localization. -/
@[simp]
theorem isUnit_num_iff {I : FractionalIdeal S P} :
    IsUnit (I.num : FractionalIdeal S P) ↔ IsUnit I := by
  rw [← den_mul_self_eq_num' S P I, IsUnit.mul_iff,
    and_iff_right (isUnit_spanSingleton (IsLocalization.map_units P I.den))]

theorem mk_eq_one_iff_exists {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff, ← MonoidHom.mem_range,
    mem_principal_ideals_iff]
  exact exists_congr fun _ ↦ eq_comm

/-- A principal fractional ideal has trivial ideal class. -/
@[simp]
theorem mk_toPrincipalIdeal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

-- Extracted from the point-to-class surjectivity argument, adapted from Chris Birkbeck's
-- AINTLIB (`github.com/CBirkbeck/AINTLIB`), `HasseWeil/Pic0/ToClassSurjective.lean`
-- (`dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
/-- Replacing an invertible fractional ideal by its integral numerator does not change its ideal
class. -/
@[simp]
theorem mk_num {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (I : (FractionalIdeal R⁰ K)ˣ) :
    let hnum : IsUnit (I.1.num : FractionalIdeal R⁰ K) :=
      isUnit_num_iff.mpr I.isUnit
    ClassGroup.mk K hnum.unit = ClassGroup.mk K I := by
  dsimp only
  let u : Kˣ := (IsLocalization.map_units K I.1.den).unit
  have hnum : (isUnit_num_iff.mpr I.isUnit).unit =
      toPrincipalIdeal R K u * I := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul, coe_toPrincipalIdeal, u]
    exact (FractionalIdeal.den_mul_self_eq_num' R⁰ K I.1).symm
  rw [hnum, map_mul, mk_toPrincipalIdeal, one_mul]

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- **An invertible ideal divides every invertible ideal it contains.** If `A ≤ I` are ideals
whose images in the fractional ideals are units, then `A = I * J` for an invertible `J`, namely
the integral ideal representing `A * I⁻¹`. (Such a `J` is automatically nonzero whenever the
fractional ideals are nontrivial; see `exists_isUnit_span_singleton_eq_mul`.) -/
theorem exists_isUnit_eq_mul_of_le {A I : Ideal R} (hAunit : IsUnit (A : FractionalIdeal R⁰ K))
    (hIunit : IsUnit (I : FractionalIdeal R⁰ K)) (hle : A ≤ I) :
    ∃ J : Ideal R, IsUnit (J : FractionalIdeal R⁰ K) ∧ A = I * J := by
  -- `A * I⁻¹` is contained in `1`, so it is (the image of) an integral ideal `J`.
  have hQ_le : (A : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ ≤ 1 := by
    calc
      (A : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ ≤
          (I : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ := by gcongr
      _ = 1 := hIunit.mul_val_inv
  obtain ⟨J, hJQ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hQ_le
  have hJ : A = I * J := by
    apply FractionalIdeal.coeIdeal_injective' (R := R) (P := K) le_rfl
    simp only [FractionalIdeal.coeIdeal_mul, hJQ]
    rw [mul_left_comm, hIunit.mul_val_inv, mul_one]
  -- `I * J` is a unit, so `J` is one too, and in particular `J ≠ ⊥`.
  have hJunit : IsUnit (J : FractionalIdeal R⁰ K) := by
    have hIJunit : IsUnit ((I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K)) := by
      rw [← FractionalIdeal.coeIdeal_mul, ← hJ]
      exact hAunit
    exact (IsUnit.mul_iff.mp hIJunit).2
  exact ⟨J, hJunit, hJ⟩

section Field

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An invertible ideal divides every principal ideal it contains**, a nonzero principal ideal
being invertible. -/
theorem exists_isUnit_span_singleton_eq_mul (I : Ideal R)
    (hIunit : IsUnit (I : FractionalIdeal R⁰ K)) {a : R} (ha : a ≠ 0) (ha_mem : a ∈ I) :
    ∃ J : Ideal R, IsUnit (J : FractionalIdeal R⁰ K) ∧ J ≠ ⊥ ∧ Ideal.span {a} = I * J := by
  have haK : algebraMap R K a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne ha
  have hspanUnit : IsUnit (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) := by
    refine ⟨toPrincipalIdeal R K (Units.mk0 (algebraMap R K a) haK), ?_⟩
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨J, hJunit, hJ⟩ := exists_isUnit_eq_mul_of_le hspanUnit hIunit
    (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha_mem)
  exact ⟨J, hJunit, FractionalIdeal.coeIdeal_ne_zero.mp hJunit.ne_zero, hJ⟩


end Field

end
end Dubon2026.SourceEllipticClassGroup
