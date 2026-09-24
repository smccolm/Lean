import TaoTrudgianYang2025.ClassicalTypeIUniformity

/-!
# Positive height windows near reflected logarithmic scale two

Four literal positive dyadic height slabs cover [T/4,4T], without
translation or coefficient twists. Their physical logarithmic heights
remain uniformly near [2,U] when the reflected source scale does.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def classicalReflectedHeightColor (T t : ℝ) : Fin 4 :=
  if t < T/2 then 0 else if t < T then 1 else if t < 2*T then 2 else 3

def classicalReflectedHeight (T : ℝ) (c : Fin 4) : ℝ :=
  if c = 0 then T/4 else if c = 1 then T/2 else if c = 2 then T else 2*T

theorem classicalReflectedHeight_bounds (T : ℝ) (hT : 0 < T) (c : Fin 4) :
    0 < classicalReflectedHeight T c ∧
      T/4 ≤ classicalReflectedHeight T c ∧ classicalReflectedHeight T c ≤ 2*T := by
  unfold classicalReflectedHeight
  split_ifs <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem classicalReflectedHeightColor_mem (T t : ℝ)
    (ht : T/4 ≤ t ∧ t ≤ 4*T) :
    classicalReflectedHeight T (classicalReflectedHeightColor T t) ≤ t ∧
      t ≤ 2*classicalReflectedHeight T (classicalReflectedHeightColor T t) := by
  unfold classicalReflectedHeightColor
  split_ifs <;>
    simp only [classicalReflectedHeight, Fin.reduceEq, ↓reduceIte] <;>
      constructor <;> linarith [ht.1,ht.2]

theorem classicalReflected_logScale_near_interval
    (U delta T H : ℝ) (N : ℕ) (hU : 2 ≤ U) (hdelta : 0 ≤ delta)
    (hT : 0 < T) (hN : 1 < N)
    (hLower : 2-delta/2 ≤ typeILogarithmicScale T N)
    (hUpper : typeILogarithmicScale T N ≤ U+delta/2)
    (hPower : 4 ≤ (N : ℝ)^(delta/2))
    (hHLower : T/4 ≤ H) (hHUpper : H ≤ 2*T) :
    ∃ alpha ∈ Set.Icc (2 : ℝ) U, |Real.logb N H-alpha| ≤ delta := by
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hHpos : 0 < H := (by positivity : 0 < T/4).trans_le hHLower
  have hScale := rpow_typeILogarithmicScale_eq hT hN
  have hTL : (N : ℝ)^(2-delta/2) ≤ T := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le hNreal.le hLower
  have hTU : T ≤ (N : ℝ)^(U+delta/2) := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le hNreal.le hUpper
  have hPowPos : 0 < (N : ℝ)^(delta/2) := Real.rpow_pos_of_pos hNpos _
  have hLogLower : 2-delta ≤ Real.logb N H := by
    apply (Real.le_logb_iff_rpow_le hNreal hHpos).mpr
    calc
      (N : ℝ)^(2-delta) =
          (N : ℝ)^(2-delta/2)/(N : ℝ)^(delta/2) := by
        rw [← Real.rpow_sub hNpos]
        congr 1
        ring
      _ ≤ T/(N : ℝ)^(delta/2) := div_le_div_of_nonneg_right hTL hPowPos.le
      _ ≤ T/4 := div_le_div_of_nonneg_left hT.le (by norm_num) hPower
      _ ≤ H := hHLower
  have hLogUpper : Real.logb N H ≤ U+delta := by
    apply (Real.logb_le_iff_le_rpow hNreal hHpos).mpr
    calc
      H ≤ 2*T := hHUpper
      _ ≤ (N : ℝ)^(delta/2)*(N : ℝ)^(U+delta/2) :=
        mul_le_mul (by linarith) hTU hT.le hPowPos.le
      _ = (N : ℝ)^(U+delta) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  exact exists_mem_Icc_abs_sub_le_of_bounds 2 U (Real.logb N H) delta
    hU hdelta hLogLower hLogUpper

end TaoTrudgianYang2025

