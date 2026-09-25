import TaoTrudgianYang2025.RobertSargosMixedCharacter
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max

/-! Finite rectangular Abel summation, retaining one prefix for the whole outer family. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosAbelDifference (N : ℕ) (w : ℕ → ℂ) (j : ℕ) : ℂ :=
  if j+1 < N then w j-w (j+1) else w j

theorem robertSargos_abel_identity (w a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, w n*a n) =
      ∑ j ∈ Finset.range N, robertSargosAbelDifference N w j*
        ∑ n ∈ Finset.range (j+1), a n := by
  cases N with
  | zero => simp
  | succ N =>
    conv_rhs => rw [Finset.sum_range_succ]
    have hd : robertSargosAbelDifference (N+1) w N = w N := by
      simp [robertSargosAbelDifference]
    rw [hd]
    have hs :
        (∑ j ∈ Finset.range N, robertSargosAbelDifference (N+1) w j*
          ∑ n ∈ Finset.range (j+1), a n) =
        -(∑ j ∈ Finset.range N, (w (j+1)-w j)*
          ∑ n ∈ Finset.range (j+1), a n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j+1 < N+1 := by simpa using Finset.mem_range.mp hj
      rw [robertSargosAbelDifference,if_pos hj']
      ring
    rw [hs]
    have h := Finset.sum_range_by_parts w a (N+1)
    simp only [smul_eq_mul,Nat.add_sub_cancel] at h
    rw [h]
    ring

def robertSargosAbelCoefficient (X Y Z : ℕ) (w : ℕ → ℕ → ℕ → ℂ)
    (i j k : ℕ) : ℂ :=
  robertSargosAbelDifference X
    (fun x => robertSargosAbelDifference Y
      (fun y => robertSargosAbelDifference Z (w x y) k) j) i

theorem robertSargos_rectangular_abel_identity
    (w a : ℕ → ℕ → ℕ → ℂ) (X Y Z : ℕ) :
    (∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y,
      ∑ z ∈ Finset.range Z, w x y z*a x y z) =
    ∑ k ∈ Finset.range Z, ∑ j ∈ Finset.range Y, ∑ i ∈ Finset.range X,
      robertSargosAbelCoefficient X Y Z w i j k*
        ∑ x ∈ Finset.range (i+1), ∑ y ∈ Finset.range (j+1),
          ∑ z ∈ Finset.range (k+1), a x y z := by
  simp_rw [robertSargos_abel_identity (w _ _) (a _ _) Z]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [robertSargos_abel_identity
    (fun y => robertSargosAbelDifference Z (w _ y) k)
    (fun y => ∑ z ∈ Finset.range (k+1), a _ y z) Y]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact robertSargos_abel_identity
    (fun x => robertSargosAbelDifference Y
      (fun y => robertSargosAbelDifference Z (w x y) k) j)
    (fun x => ∑ y ∈ Finset.range (j+1), ∑ z ∈ Finset.range (k+1), a x y z) X

private theorem exists_common_family_sum_bound {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (hne : T.Nonempty)
    (w z : ι → κ → ℂ) :
    ∃ p ∈ T, (∑ m ∈ S, ‖∑ q ∈ T, w m q*z m q‖) ≤
      (∑ q ∈ T, ((S.sup (fun m => ‖w m q‖₊) : NNReal) : ℝ))*
        ∑ m ∈ S, ‖z m p‖ := by
  classical
  obtain ⟨p,hp,hmax⟩ := T.exists_max_image (fun q => ∑ m ∈ S, ‖z m q‖) hne
  refine ⟨p,hp,?_⟩
  calc
    _ ≤ ∑ m ∈ S, ∑ q ∈ T,
        ((S.sup (fun m => ‖w m q‖₊) : NNReal) : ℝ)*‖z m q‖ := by
      apply Finset.sum_le_sum
      intro m hm
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast (Finset.le_sup (f := fun m => ‖w m q‖₊) hm)
    _ = ∑ q ∈ T, ((S.sup (fun m => ‖w m q‖₊) : NNReal) : ℝ)*
        ∑ m ∈ S, ‖z m q‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ q ∈ T, ((S.sup (fun m => ‖w m q‖₊) : NNReal) : ℝ)*
        ∑ m ∈ S, ‖z m p‖ := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hmax q hq) (by positivity)
    _ = _ := by rw [Finset.sum_mul]

def robertSargosAbelVariation {ι : Type*} (S : Finset ι)
    (X Y Z : ℕ) (w : ι → ℕ → ℕ → ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range Z, ∑ j ∈ Finset.range Y, ∑ i ∈ Finset.range X,
    ((S.sup (fun m => ‖robertSargosAbelCoefficient X Y Z (w m) i j k‖₊) : NNReal) : ℝ)

theorem robertSargos_rectangular_common_prefix {ι : Type*}
    (S : Finset ι) (w a : ι → ℕ → ℕ → ℕ → ℂ)
    {X Y Z : ℕ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∃ i < X, ∃ j < Y, ∃ k < Z,
      (∑ m ∈ S, ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y,
        ∑ z ∈ Finset.range Z, w m x y z*a m x y z‖) ≤
      robertSargosAbelVariation S X Y Z w*
        ∑ m ∈ S, ‖∑ x ∈ Finset.range (i+1), ∑ y ∈ Finset.range (j+1),
          ∑ z ∈ Finset.range (k+1), a m x y z‖ := by
  classical
  let T := (Finset.range Z) ×ˢ ((Finset.range Y) ×ˢ (Finset.range X))
  have hT : T.Nonempty := ⟨(0,0,0),by simp [T,hX,hY,hZ]⟩
  obtain ⟨p,hp,h⟩ := exists_common_family_sum_bound S T hT
    (fun m p => robertSargosAbelCoefficient X Y Z (w m) p.2.2 p.2.1 p.1)
    (fun m p => ∑ x ∈ Finset.range (p.2.2+1), ∑ y ∈ Finset.range (p.2.1+1),
      ∑ z ∈ Finset.range (p.1+1), a m x y z)
  have hp' : p.1 < Z ∧ p.2.1 < Y ∧ p.2.2 < X := by simpa [T] using hp
  refine ⟨p.2.2,hp'.2.2,p.2.1,hp'.2.1,p.1,hp'.1,?_⟩
  simp only [T,Finset.sum_product] at h
  simpa only [← robertSargos_rectangular_abel_identity,robertSargosAbelVariation] using h

def robertSargosMixedAmplitude (f : ℝ → ℝ) (m r Q q h n : ℝ) : ℂ :=
  ((1-|q|/Q : ℝ):ℂ)*fordAdditiveCharacter (robertSargosMixedRemainder f m r q h n)

def robertSargosPolynomialCharacter (f : ℝ → ℝ) (m r q h n : ℝ) : ℂ :=
  fordAdditiveCharacter
    (2*iteratedDeriv 2 f m*robertSargosLinear (-r) q h n+
      iteratedDeriv 3 f m*robertSargosTaylorQuadratic r q h n)

theorem robertSargos_mixed_rectangular_norm (f : ℝ → ℝ) (m r Q : ℝ)
    (q h n : ℕ → ℝ) (X Y Z : ℕ) :
    ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range Z,
      ((1-|q x|/Q : ℝ):ℂ)*fordAdditiveCharacter
        (robertSargosSymmetricDifference f (m+n z+q x) (h y)-
          robertSargosSymmetricDifference f (m+n z) (h y+r))‖ =
    ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range Z,
      robertSargosMixedAmplitude f m r Q (q x) (h y) (n z)*
        robertSargosPolynomialCharacter f m r (q x) (h y) (n z)‖ := by
  have he := norm_robertSargos_mixed_sum_eq
    ((Finset.range X) ×ˢ ((Finset.range Y) ×ˢ (Finset.range Z)))
    (fun p => ((1-|q p.1|/Q : ℝ):ℂ))
    (fun p => q p.1) (fun p => h p.2.1) (fun p => n p.2.2) f m r
  simp only [Finset.sum_product] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  unfold robertSargosMixedAmplitude robertSargosPolynomialCharacter
  rw [fordAdditiveCharacter_add]
  ring

/-- One prefix is selected after summing over every actual outer ordinate.
The variation is literal; its uniform C4 bound is a separate analytic obligation. -/
theorem robertSargos_mixed_common_prefix (f : ℝ → ℝ) (S : Finset ℝ)
    (r Q : ℝ) (q h n : ℕ → ℝ) {X Y Z : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∃ i < X, ∃ j < Y, ∃ k < Z,
      (∑ m ∈ S, ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y,
        ∑ z ∈ Finset.range Z, ((1-|q x|/Q : ℝ):ℂ)*fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+n z+q x) (h y)-
            robertSargosSymmetricDifference f (m+n z) (h y+r))‖) ≤
      robertSargosAbelVariation S X Y Z
        (fun m x y z => robertSargosMixedAmplitude f m r Q (q x) (h y) (n z))*
      ∑ m ∈ S, ‖∑ x ∈ Finset.range (i+1), ∑ y ∈ Finset.range (j+1),
        ∑ z ∈ Finset.range (k+1),
          robertSargosPolynomialCharacter f m r (q x) (h y) (n z)‖ := by
  simpa only [robertSargos_mixed_rectangular_norm] using
    robertSargos_rectangular_common_prefix S
      (fun m x y z => robertSargosMixedAmplitude f m r Q (q x) (h y) (n z))
      (fun m x y z => robertSargosPolynomialCharacter f m r (q x) (h y) (n z))
      hX hY hZ


end TaoTrudgianYang2025
