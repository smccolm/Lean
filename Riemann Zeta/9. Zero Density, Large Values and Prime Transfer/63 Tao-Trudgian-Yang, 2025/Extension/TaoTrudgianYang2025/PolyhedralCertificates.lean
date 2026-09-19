import TaoTrudgianYang2025.PiecewiseEnvelope

/-!
# Exact convex and polyhedral certificates

Certificate data are rational. Their soundness theorems cast the data to the
reals and prove the resulting convex-combination and projection claims inside
Lean; an external optimizer may suggest the data but cannot act as a proof
oracle.
-/

open scoped BigOperators

namespace TaoTrudgianYang2025

/-- Exact rational weights for a finite convex combination. -/
structure RationalConvexCombination (count : ℕ) where
  weight : Fin count → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  sum_eq_one : ∑ i, weight i = 1

namespace RationalConvexCombination

/-- A rational convex combination preserves a common real upper bound. -/
theorem weighted_sum_le {count : ℕ}
    (certificate : RationalConvexCombination count)
    (value : Fin count → ℝ) {bound : ℝ}
    (hBound : ∀ i, value i ≤ bound) :
    ∑ i, (certificate.weight i : ℝ) * value i ≤ bound := by
  calc
    ∑ i, (certificate.weight i : ℝ) * value i ≤
        ∑ i, (certificate.weight i : ℝ) * bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hBound i) (by
        exact_mod_cast certificate.nonnegative i)
    _ = (∑ i, (certificate.weight i : ℝ)) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      have hSum : ∑ i, (certificate.weight i : ℝ) = 1 := by
        exact_mod_cast certificate.sum_eq_one
      rw [hSum, one_mul]

/-- A rational convex combination preserves a common real lower bound. -/
theorem le_weighted_sum {count : ℕ}
    (certificate : RationalConvexCombination count)
    (value : Fin count → ℝ) {bound : ℝ}
    (hBound : ∀ i, bound ≤ value i) :
    bound ≤ ∑ i, (certificate.weight i : ℝ) * value i := by
  have hSum : ∑ i, (certificate.weight i : ℝ) = 1 := by
    exact_mod_cast certificate.sum_eq_one
  calc
    bound = (∑ i, (certificate.weight i : ℝ)) * bound := by
      rw [hSum, one_mul]
    _ = ∑ i, (certificate.weight i : ℝ) * bound := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i, (certificate.weight i : ℝ) * value i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hBound i) (by
        exact_mod_cast certificate.nonnegative i)

end RationalConvexCombination

/-- A rational half-space in a fixed finite dimension. -/
structure RationalHalfSpace (dimension : ℕ) where
  normal : Fin dimension → ℚ
  bound : ℚ

namespace RationalHalfSpace

/-- Membership in the real half-space represented by rational data. -/
def Contains {dimension : ℕ} (halfSpace : RationalHalfSpace dimension)
    (point : Fin dimension → ℝ) : Prop :=
  ∑ i, (halfSpace.normal i : ℝ) * point i ≤ halfSpace.bound

end RationalHalfSpace

/-- A rational polyhedron is a finite list of rational half-spaces. -/
structure RationalPolyhedron (dimension : ℕ) where
  constraints : List (RationalHalfSpace dimension)

namespace RationalPolyhedron

/-- Membership means satisfying every stored rational half-space. -/
def Contains {dimension : ℕ} (polyhedron : RationalPolyhedron dimension)
    (point : Fin dimension → ℝ) : Prop :=
  ∀ halfSpace ∈ polyhedron.constraints, halfSpace.Contains point

end RationalPolyhedron

/-- An exact affine formula for an eliminated real coordinate. -/
structure RationalEliminationWitness (dimension : ℕ) where
  coefficient : Fin dimension → ℚ
  constant : ℚ

namespace RationalEliminationWitness

/-- Evaluate the eliminated coordinate supplied by a rational witness. -/
def eval {dimension : ℕ} (witness : RationalEliminationWitness dimension)
    (point : Fin dimension → ℝ) : ℝ :=
  (witness.constant : ℝ) +
    ∑ i, (witness.coefficient i : ℝ) * point i

end RationalEliminationWitness

/-- An affine elimination witness certifies that every target point lifts to
the source polyhedron by placing the eliminated coordinate first. -/
def CertifiesProjection {dimension : ℕ}
    (source : RationalPolyhedron (dimension + 1))
    (target : RationalPolyhedron dimension)
    (witness : RationalEliminationWitness dimension) : Prop :=
  ∀ point, target.Contains point →
    source.Contains (Fin.cases (witness.eval point) point)

/-- Soundness of an explicit affine projection certificate. -/
theorem projection_sound {dimension : ℕ}
    {source : RationalPolyhedron (dimension + 1)}
    {target : RationalPolyhedron dimension}
    {witness : RationalEliminationWitness dimension}
    (hCertificate : CertifiesProjection source target witness) :
    ∀ point, target.Contains point →
      ∃ eliminated : ℝ,
        source.Contains (Fin.cases eliminated point) := by
  intro point hPoint
  exact ⟨witness.eval point, hCertificate point hPoint⟩

/-- Exact rational data witnessing that one rational point is a convex
combination of finitely many rational vertices. -/
structure RationalConvexHullWitness (count dimension : ℕ) where
  combination : RationalConvexCombination count
  vertex : Fin count → Fin dimension → ℚ
  target : Fin dimension → ℚ
  coordinate_eq : ∀ coordinate,
    ∑ i, combination.weight i * vertex i coordinate = target coordinate

namespace RationalConvexHullWitness

/-- The stored coordinate equations remain exact after casting to the reals. -/
theorem real_coordinate_eq {count dimension : ℕ}
    (witness : RationalConvexHullWitness count dimension)
    (coordinate : Fin dimension) :
    ∑ i, (witness.combination.weight i : ℝ) *
        (witness.vertex i coordinate : ℝ) =
      (witness.target coordinate : ℝ) := by
  exact_mod_cast witness.coordinate_eq coordinate

end RationalConvexHullWitness

end TaoTrudgianYang2025
