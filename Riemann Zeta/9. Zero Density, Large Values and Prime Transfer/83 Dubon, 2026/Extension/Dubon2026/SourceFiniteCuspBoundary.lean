import Dubon2026.SourceCuspBoundaryValues

/-! DUB-17/18 -> residual Galois association -> boundary eigenvalues of
the original complex weight-two class. Actual cusp evaluation descends
to the finite set of primitive columns modulo the original level and
is nonzero for every nonparabolic original class. Existing integral
SL2 reduction supplies its representatives.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The finite primitive columns modulo the original level. -/
def P (N : ℕ) := {v : ZMod N × ZMod N // IsCoprime v.1 v.2}

/-- Primitive residue columns form an actual finite set at nonzero level. -/
instance instFiniteP (N : ℕ) [NeZero N] : Finite (P N) := by unfold P; infer_instance

variable {N : ℕ}

/-- Every primitive residue column has an actual integral cusp representative. -/
theorem exists_lift [NeZero N] (p : P N) : ∃ δ : SL(2, ℤ), colRed N δ = p.1 := by
  obtain ⟨g, hg0, hg1⟩ := p.2.exists_SL2_col 0
  obtain ⟨δ, hδ⟩ := SL2Reduction.SL2_reduction_surjective N g
  refine ⟨δ, ?_⟩
  have he (i j : Fin 2) : ((δ i j : ℤ) : ZMod N) = g i j :=
    congrArg (fun x : SL(2, ZMod N) => x i j) hδ
  exact Prod.ext ((he 0 0).trans hg0) ((he 1 0).trans hg1)

/-- An actual integral lift of the original primitive residue column. -/
def lift [NeZero N] (p : P N) : SL(2, ℤ) := Classical.choose (exists_lift p)

/-- The constructed cusp representative has the prescribed reduced column. -/
theorem colRed_lift [NeZero N] (p : P N) :
    colRed N (lift p) = p.1 := Classical.choose_spec (exists_lift p)

/-- An original integral cusp representative gives a primitive residue column. -/
def toP (δ : SL(2, ℤ)) : P N :=
  ⟨colRed N δ, by
    obtain ⟨x, y, hxy⟩ := isCoprime_col δ
    refine ⟨(x : ZMod N), (y : ZMod N), ?_⟩
    have he := congrArg (fun z : ℤ => (z : ZMod N)) hxy
    push_cast at he
    exact he⟩

/-- Independent unit scaling of the two original residue coordinates. -/
def scale (x y : (ZMod N)ˣ) (p : P N) : P N :=
  ⟨((x : ZMod N) * p.1.1, (y : ZMod N) * p.1.2),
    (isCoprime_mul_unit_left_left x.isUnit _ _).mpr
      ((isCoprime_mul_unit_left_right y.isUnit _ _).mpr p.2)⟩

/-- Scaling preserves the exact first-coordinate formula. -/
theorem scale_val_fst (x y : (ZMod N)ˣ) (p : P N) :
    (scale x y p).1.1 = (x : ZMod N) * p.1.1 := rfl

/-- Scaling preserves the exact second-coordinate formula. -/
theorem scale_val_snd (x y : (ZMod N)ˣ) (p : P N) :
    (scale x y p).1.2 = (y : ZMod N) * p.1.2 := rfl

/-- The original residue-coordinate action composes by unit multiplication. -/
theorem scale_scale (x y x' y' : (ZMod N)ˣ) (p : P N) :
    scale x y (scale x' y' p) = scale (x * x') (y * y') p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [scale, mul_assoc]

/-- The two-coordinate unit actions commute on the actual finite boundary. -/
theorem scale_comm (x y x' y' : (ZMod N)ˣ) (p : P N) :
    scale x y (scale x' y' p) = scale x' y' (scale x y p) := by
  rw [scale_scale, scale_scale, mul_comm x, mul_comm y]

/-- The identity units fix every original residue column. -/
theorem scale_one (p : P N) : scale 1 1 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [scale]

variable [NeZero N] {A : Type*} [AddCommGroup A]

/-- The actual cusp values as a function on the finite residue boundary. -/
def bOf (φ : Additive (Gamma0 N) →+ A) (p : P N) : A := B φ (lift p)

/-- Evaluating the finite boundary function at an original column recovers
the original subgroup homomorphism at its actual cusp translation. -/
theorem bOf_toP (φ : Additive (Gamma0 N) →+ A) (δ : SL(2, ℤ)) :
    bOf φ (toP δ) = B φ δ := B_congr φ (colRed_lift _)

/-- Coefficient scaling commutes with the original finite boundary function. -/
theorem bOf_smul {R : Type*} [Semiring R] [Module R A] (c : R)
    (φ : Additive (Gamma0 N) →+ A) (p : P N) :
    bOf (c • φ) p = c • bOf φ p := rfl

/-- The original Gamma0 boundary function is invariant under inverse
diagonal scaling; no extra diamond-eigenvalue premise is needed. -/
theorem bOf_diagonal (φ : Additive (Gamma0 N) →+ A) (d : (ZMod N)ˣ) (p : P N) :
    bOf φ (scale d⁻¹ d p) = bOf φ p := by
  apply B_eq_of_borel φ d 0
  · rw [colRed_lift, colRed_lift]
    simp only [scale_val_fst, zero_mul, add_zero]
  · rw [colRed_lift, colRed_lift]
    exact scale_val_snd _ _ _

/-- Every nonparabolic original complex homomorphism gives a nonzero
function on the actual finite cusp boundary. -/
theorem bOf_ne_zero (φ : Additive (Gamma0 N) →+ ℂ) (hφ : φ ∉ parabolicHoms N) :
    bOf φ ≠ 0 := by
  intro h
  apply hφ
  apply mem_parabolicHoms_of_B_eq_zero
  intro δ
  rw [← bOf_toP, h]
  rfl

end
end Dubon2026.SourceCuspBoundary
