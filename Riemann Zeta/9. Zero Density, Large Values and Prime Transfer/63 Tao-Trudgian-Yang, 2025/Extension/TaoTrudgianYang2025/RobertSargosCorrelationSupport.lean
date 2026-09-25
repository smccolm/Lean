import TaoTrudgianYang2025.RobertSargosSymmetricArray
import GafniTao.FordEquation54Expansion

/-! Exact source intersection support. The second factor uses h+r;
that dependence is retained in both endpoints of the m interval. -/

noncomputable section
open GafniTao
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace TaoTrudgianYang2025

def robertSargosHOverlap (H : ℕ) (r : ℤ) : Finset ℤ :=
  Finset.Icc (max (H:ℤ) (H-r)) (min (2*(H:ℤ)-1) (2*(H:ℤ)-1-r))

def robertSargosMOverlap (M : ℕ) (h q r : ℤ) : Finset ℤ :=
  Finset.Icc (max (h+1-q) (h+r+1)) (min ((M:ℤ)-h-q) ((M:ℤ)-h-r))

theorem mem_robertSargosHOverlap (H : ℕ) (h r : ℤ) :
    h ∈ robertSargosHOverlap H r ↔
      h ∈ Finset.Ico (H:ℤ) (2*H) ∧ h+r ∈ Finset.Ico (H:ℤ) (2*H) := by
  simp only [robertSargosHOverlap,Finset.mem_Icc,Finset.mem_Ico,max_le_iff,le_min_iff]
  omega

theorem mem_robertSargosMOverlap (M : ℕ) (m h q r : ℤ) :
    m ∈ robertSargosMOverlap M h q r ↔
      m+q ∈ Finset.Icc (h+1) ((M:ℤ)-h) ∧
        m ∈ Finset.Icc (h+r+1) ((M:ℤ)-(h+r)) := by
  simp only [robertSargosMOverlap,Finset.mem_Icc,max_le_iff,le_min_iff]
  omega

theorem robertSargos_symmetric_array_product (f : ℝ → ℝ) (M H : ℕ) (m h q r : ℤ) :
    robertSargosSymmetricArray f M H (m+q) h*
      conj (robertSargosSymmetricArray f M H m (h+r)) =
      if h ∈ robertSargosHOverlap H r ∧ m ∈ robertSargosMOverlap M h q r then
        fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+q) h-
            robertSargosSymmetricDifference f m (h+r))
      else 0 := by
  simp only [mem_robertSargosHOverlap,mem_robertSargosMOverlap]
  by_cases hh : h ∈ Finset.Ico (H:ℤ) (2*H)
  · by_cases hr : h+r ∈ Finset.Ico (H:ℤ) (2*H)
    · by_cases hm : m+q ∈ Finset.Icc (h+1) ((M:ℤ)-h)
      · by_cases hn : m ∈ Finset.Icc (h+r+1) ((M:ℤ)-(h+r))
        · simp only [robertSargosSymmetricArray,hh,hr,hm,hn,and_self,if_true]
          rw [conj_fordAdditiveCharacter,← fordAdditiveCharacter_add]
          simp only [sub_eq_add_neg,Int.cast_add]
        · simp only [robertSargosSymmetricArray,hh,hr,hm,hn,and_true,and_false,
            if_true,if_false,map_zero,mul_zero]
      · simp only [robertSargosSymmetricArray,hh,hr,hm,true_and,false_and,
          and_false,if_true,if_false,zero_mul]
    · simp only [robertSargosSymmetricArray,hh,hr,and_false,false_and,
        if_true,if_false,map_zero,mul_zero]
  · simp only [robertSargosSymmetricArray,hh,false_and,if_false,zero_mul]

theorem robertSargos_symmetric_array_inner (f : ℝ → ℝ) (M H : ℕ) (m h q r : ℤ) :
    ⟪robertSargosSymmetricArray f M H (m+q) h,
      robertSargosSymmetricArray f M H m (h+r)⟫_ℝ =
      if h ∈ robertSargosHOverlap H r ∧ m ∈ robertSargosMOverlap M h q r then
        (fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+q) h-
            robertSargosSymmetricDifference f m (h+r))).re
      else 0 := by
  rw [real_inner_comm,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  change (robertSargosSymmetricArray f M H (m+q) h*
    conj (robertSargosSymmetricArray f M H m (h+r))).re = _
  rw [robertSargos_symmetric_array_product]
  split_ifs <;> rfl

end TaoTrudgianYang2025
