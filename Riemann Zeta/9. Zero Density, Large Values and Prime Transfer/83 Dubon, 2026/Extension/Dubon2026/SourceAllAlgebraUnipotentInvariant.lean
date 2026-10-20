import Dubon2026.SourceAllAlgebraSquareZeroInvariant
import Dubon2026.SourceUnipotentGeneration
import Dubon2026.SourceStrictUpperLie

/-! The original infinitesimal upper invariant is an actual upper-unipotent
invariant over every coefficient algebra. Constant actual orbit polynomials
and exact root generation supply the all-algebra source quantifiers.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u v
variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

omit [CharZero K] in
/-- The original upper-root matrix belongs to the original strictly upper triangular Lie algebra. -/
theorem sourceStrictUpper_single_mem {i j : Fin n} (hij : i < j) :
    LieAlgebra.SpecialLinear.single i j hij.ne (1 : K) ∈ sourceStrictUpperLie K n := by
  intro a b hab
  change Matrix.single i j (1 : K) a b = 0
  simp only [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (not_lt_of_ge hab hij).elim
  · rfl

/-- An original strictly upper infinitesimal invariant is fixed by every actual upper root matrix over every coefficient algebra. -/
theorem sourceUpperRoot_allAlgebra_invariant
    (p : S) (hp : ∀ X : sourceStrictUpperLie K n,
      sourceRegularDifferential X.val.val p = 0)
    {A : Type v} [CommRing A] [Algebra K A]
    (g : GeneralLinearGroup (Fin n) A) {i j : Fin n} (hij : i < j) (t : A) :
    generalLinearRegularEval (R := K) (g * sourceUpperTransvection hij.ne t) p =
      generalLinearRegularEval (R := K) g p := by
  let X : sourceStrictUpperLie K n :=
    ⟨LieAlgebra.SpecialLinear.single i j hij.ne (1 : K), sourceStrictUpper_single_mem hij⟩
  have hX : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hij.ne.symm)]
  have hpX : sourceRegularDifferential (Matrix.single i j (1 : K)) p = 0 := hp X
  have he := sourceSquareZero_allAlgebra_invariant (Matrix.single i j (1 : K)) hX p hpX g t
  have hg :
      sourceSquareZeroLine ((Matrix.single i j (1 : K)).map (algebraMap K A))
        (sourceSquareZeroMatrix_map (algebraMap K A) _ hX) t =
          sourceUpperTransvection hij.ne t := by
    apply Units.ext
    change 1 + t • (Matrix.single i j (1 : K)).map (algebraMap K A) =
      1 + t • Matrix.single i j (1 : A)
    congr 2
    ext a b
    by_cases ha : i = a <;> by_cases hb : j = b <;>
      simp [ha, hb]
  rwa [hg] at he

/-- Every original strictly upper infinitesimal invariant satisfies the original all-algebra upper-unipotent invariance contract. -/
theorem sourceUnipotent_allAlgebra_invariant
    (p : S) (hp : ∀ X : sourceStrictUpperLie K n,
      sourceRegularDifferential X.val.val p = 0)
    {A : Type v} [CommRing A] [Algebra K A]
    (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n)
    (hb : ∀ i, generalLinearBorelDiagonalUnit b i = 1) :
    generalLinearRegularEval (R := K) (g * b.val) p =
      generalLinearRegularEval (R := K) g p := by
  have hdiag : ∀ i, b.val.val i i = 1 := fun i =>
    congrArg (fun z : Aˣ => (z : A)) (hb i)
  have h := sourceUnipotent_induction
    (P := fun u : GeneralLinearGroup (Fin n) A => ∀ v : GeneralLinearGroup (Fin n) A,
      generalLinearRegularEval (R := K) (v * u) p =
        generalLinearRegularEval (R := K) v p)
    (fun a b ha hb v => by rw [← mul_assoc, hb, ha])
    (fun {i j} hij t v => sourceUpperRoot_allAlgebra_invariant p hp v hij t)
    (by intro v; rw [mul_one])
    _ b.val b.property hdiag rfl
  exact h g

end
end Dubon2026
