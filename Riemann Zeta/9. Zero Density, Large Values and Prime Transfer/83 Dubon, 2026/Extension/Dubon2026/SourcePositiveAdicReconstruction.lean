import Dubon2026.SourcePositiveAdicFamilyLift
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
complete original trace values. The proved positive-precision lift and
native Hausdorff extensionality supply exact reconstruction; native adic
neighborhoods will recover continuity from the original finite traces. -/
namespace Dubon2026
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

/-- The unique complete-ring value of a compatible positive-precision family. -/
def positiveAdicFamilyLift [IsAdicComplete I R]
    (a : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (ha : ∀ {m n : ℕ} (h : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1) (a n) = a m) : R :=
  (positiveAdicFamily_exists_unique_lift I a ha).choose

/-- Every original positive quotient of the actual lift is exactly the input. -/
theorem positiveAdicFamilyLift_mk [IsAdicComplete I R]
    (a : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (ha : ∀ {m n : ℕ} (h : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1) (a n) = a m) (n : ℕ) :
    Ideal.Quotient.mk (I ^ (n + 1)) (positiveAdicFamilyLift I a ha) = a n :=
  (positiveAdicFamily_exists_unique_lift I a ha).choose_spec.1 n

/-- Exact positive-quotient comparison identifies actual separated-ring values. -/
theorem positiveAdic_ext [IsHausdorff I R] {x y : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) x = Ideal.Quotient.mk (I ^ (n + 1)) y) : x = y := by
  have he : (fun _ : Unit => x) = (fun _ : Unit => y) :=
    IsHausdorff.StrictMono.funext' I (show StrictMono (fun n : ℕ => n + 1) from
      fun _ _ h => Nat.add_lt_add_right h 1) (fun n _ => h n)
  exact congrFun he ()

end
end Dubon2026
