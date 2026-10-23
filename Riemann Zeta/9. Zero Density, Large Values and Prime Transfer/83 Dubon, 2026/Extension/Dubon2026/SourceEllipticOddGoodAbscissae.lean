import Dubon2026.SourceEllipticOddSummingSet
import Dubon2026.SourceEllipticVeluTwoSurjective
import Dubon2026.SourceEllipticTorsionCardinality

/-! Infinitely many usable x-coordinates for the odd quotient factorization.
The existing actual torsion cardinality supplies finite doubling fibers;
the existing quadratic coordinate lift supplies a point at every x. This
avoids the reference's separate short-model two-torsion finiteness and lift
proofs. The result serves odd quotient ellipticity -> cyclic-subgroup root
interpretation -> inertia census -> reverse genus/good reduction ->
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
  {V : WeierstrassCurve K} [V.IsElliptic]

theorem doubling_fibre_finite (h2 : (2 : K) ≠ 0) (w : V.toAffine.Point) :
    {z : V.toAffine.Point | 2 • z = w}.Finite := by
  have hc : Nat.card {z : V.toAffine.Point // 2 • z = w} = 4 := by
    exact (SourceEllipticTorsion.card_smul_fiber_all V (K := K) (n := 2) h2 w).trans
      (by simpa using SourceEllipticTorsion.card_nTorsion V (K := K) (n := 2) h2)
  haveI : Finite {z : V.toAffine.Point // 2 • z = w} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact @Set.toFinite _ _ ‹Finite {z : V.toAffine.Point // 2 • z = w}›

theorem bad_finite (h2 : (2 : K) ≠ 0) {Q : V.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    {z : V.toAffine.Point | ∃ j : ℕ, 2 • z + j • Q = 0}.Finite := by
  have hsub : {z : V.toAffine.Point | ∃ j : ℕ, 2 • z + j • Q = 0}
      ⊆ ⋃ j ∈ Set.Iio (2 * n + 1), {z | 2 • z = -(j • Q)} := by
    rintro z ⟨j, hj⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    refine ⟨j % (2 * n + 1), Nat.mod_lt _ (by omega), ?_⟩
    rw [← hQ, mod_addOrderOf_nsmul]
    exact eq_neg_of_add_eq_zero_left hj
  exact ((Set.finite_Iio _).biUnion fun j _ => doubling_fibre_finite h2 _).subset hsub

theorem good_abscissae_infinite (h2 : (2 : K) ≠ 0) {Q : V.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    Set.Infinite {x₀ : K | ∃ z : V.toAffine.Point,
      (∀ j : ℕ, 2 • z + j • Q ≠ 0) ∧ (coordsOrZero z).1 = x₀} := by
  have hlift : ∀ x₀ : K, ∃ y₀, V.toAffine.Nonsingular x₀ y₀ := by
    intro x₀
    obtain ⟨y₀, hy₀⟩ := exists_equation_y V x₀
    exact ⟨y₀, (WeierstrassCurve.Affine.equation_iff_nonsingular (W := V)).mp hy₀⟩
  choose lift hlift using hlift
  have hinj : Function.Injective (fun x₀ =>
      (WeierstrassCurve.Affine.Point.some x₀ (lift x₀) (hlift x₀) : V.toAffine.Point)) := by
    intro a b h
    have := congrArg (fun P : V.toAffine.Point => (coordsOrZero P).1) h
    simpa only [coordsOrZero] using this
  have hfin := (bad_finite h2 hQ).preimage hinj.injOn
  refine (Set.infinite_univ.diff hfin).mono ?_
  rintro x₀ ⟨-, hx₀⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, not_exists] at hx₀
  exact ⟨_, hx₀, rfl⟩

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
