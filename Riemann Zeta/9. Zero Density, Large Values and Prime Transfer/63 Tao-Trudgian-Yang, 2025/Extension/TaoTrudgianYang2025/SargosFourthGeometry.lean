import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometry of the Robert--Sargos fourth-moment count

The two literal near-equalities from Robert--Sargos, section 5,
are reduced to bounded linear coordinates and a hyperbolic product.
The closed interval below contains the paper's half-open interval.
This is the geometric reduction, not the moment or C-process theorem.
-/

namespace TaoTrudgianYang2025

theorem sargos_fourth_product_sq_identity (a b c d : ℝ) :
    2*((a*b)^2-(c*d)^2) =
      (a^2+b^2-c^2-d^2)*(a^2+b^2+c^2+d^2)-
        (a^4+b^4-c^4-d^4) := by
  ring

theorem sargos_fourth_product_gap {N a b c d : ℝ} (hN : 0 < N)
    (ha : a ∈ Set.Icc N (2*N)) (hb : b ∈ Set.Icc N (2*N))
    (hc : c ∈ Set.Icc N (2*N)) (hd : d ∈ Set.Icc N (2*N))
    (h₂ : |a^2+b^2-c^2-d^2| ≤ N)
    (h₄ : |a^4+b^4-c^4-d^4| ≤ N^3) :
    |a*b-c*d| ≤ 5*N := by
  have hN₀ := le_of_lt hN
  have hab : N^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha.1 hb.1 hN₀ (hN₀.trans ha.1)
  have hcd : N^2 ≤ c*d := by
    simpa only [pow_two] using mul_le_mul hc.1 hd.1 hN₀ (hN₀.trans hc.1)
  have hsum : a^2+b^2+c^2+d^2 ≤ 16*N^2 := by
    have ha₂ : a^2 ≤ (2*N)^2 := sq_le_sq₀ (by linarith [ha.1]) (by positivity) |>.mpr ha.2
    have hb₂ : b^2 ≤ (2*N)^2 := sq_le_sq₀ (by linarith [hb.1]) (by positivity) |>.mpr hb.2
    have hc₂ : c^2 ≤ (2*N)^2 := sq_le_sq₀ (by linarith [hc.1]) (by positivity) |>.mpr hc.2
    have hd₂ : d^2 ≤ (2*N)^2 := sq_le_sq₀ (by linarith [hd.1]) (by positivity) |>.mpr hd.2
    nlinarith
  have hbound : |2*((a*b)^2-(c*d)^2)| ≤ 17*N^3 := by
    rw [sargos_fourth_product_sq_identity]
    calc
      _ ≤ |(a^2+b^2-c^2-d^2)*(a^2+b^2+c^2+d^2)|+
          |a^4+b^4-c^4-d^4| := abs_sub _ _
      _ = |a^2+b^2-c^2-d^2| *(a^2+b^2+c^2+d^2)+
          |a^4+b^4-c^4-d^4| := by
            rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ a^2+b^2+c^2+d^2)]
      _ ≤ N*(16*N^2)+N^3 :=
        add_le_add (mul_le_mul h₂ hsum (by positivity) hN₀) h₄
      _ = 17*N^3 := by ring
  have hprod : 0 ≤ a*b+c*d := by nlinarith [sq_nonneg N]
  have hfact : |2*((a*b)^2-(c*d)^2)| = 2*|a*b-c*d| *(a*b+c*d) := by
    rw [show 2*((a*b)^2-(c*d)^2) = 2*(a*b-c*d)*(a*b+c*d) by ring,
      abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hprod]
  rw [hfact] at hbound
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
  have hlower := mul_le_mul_of_nonneg_left (add_le_add hab hcd)
    (abs_nonneg (a*b-c*d))
  nlinarith only [hbound,hlower,pow_pos hN 3]

theorem sargos_fourth_sum_gap {N a b c d : ℝ} (hN : 0 < N)
    (ha : N ≤ a) (hb : N ≤ b) (hc : N ≤ c) (hd : N ≤ d)
    (h₂ : |a^2+b^2-c^2-d^2| ≤ N) (hp : |a*b-c*d| ≤ 5*N) :
    |a+b-c-d| ≤ 3 := by
  have hs : 0 ≤ a+b+c+d := by linarith
  have hbound : |(a+b)^2-(c+d)^2| ≤ 11*N := by
    calc
      _ = |(a^2+b^2-c^2-d^2)+2*(a*b-c*d)| := by congr 1; ring
      _ ≤ |a^2+b^2-c^2-d^2|+|2*(a*b-c*d)| := abs_add_le _ _
      _ = |a^2+b^2-c^2-d^2|+2*|a*b-c*d| := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 11*N := by linarith
  have hfact : |(a+b)^2-(c+d)^2| = |a+b-c-d| *(a+b+c+d) := by
    rw [show (a+b)^2-(c+d)^2 = (a+b-c-d)*(a+b+c+d) by ring,
      abs_mul,abs_of_nonneg hs]
  rw [hfact] at hbound
  apply (mul_le_mul_iff_right₀ hN).mp
  have hlower := mul_le_mul_of_nonneg_left (show 4*N ≤ a+b+c+d by linarith)
    (abs_nonneg (a+b-c-d))
  nlinarith

theorem sargos_fourth_difference_product {N a b c d : ℝ}
    (h₂ : |a^2+b^2-c^2-d^2| ≤ N) (hp : |a*b-c*d| ≤ 5*N) :
    |(a-b-c+d)*(a-b+c-d)| ≤ 11*N := by
  calc
    _ = |(a^2+b^2-c^2-d^2)-2*(a*b-c*d)| := by congr 1; ring
    _ ≤ |a^2+b^2-c^2-d^2|+|2*(a*b-c*d)| := abs_sub _ _
    _ = |a^2+b^2-c^2-d^2|+2*|a*b-c*d| := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 11*N := by linarith

/-- Sum, sum displacement, and the two factors of the difference of squares. -/
def sargosFourthCoordinates (q : Fin 4 → ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (q 0+q 1, q 2+q 3-q 0-q 1, q 0-q 1-q 2+q 3, q 0-q 1+q 2-q 3)

theorem sargosFourthCoordinates_injective :
    Function.Injective sargosFourthCoordinates := by
  intro q r h
  have hA := congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.1) h
  have hD := congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.1) h
  have hu := congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.1) h
  have hv := congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.2) h
  dsimp [sargosFourthCoordinates] at hA hD hu hv
  funext i
  fin_cases i <;> dsimp at * <;> omega


theorem sargos_fourth_coordinate_bounds {N a b c d : ℝ} (hN : 0 < N)
    (ha : a ∈ Set.Icc N (2*N)) (hb : b ∈ Set.Icc N (2*N))
    (hc : c ∈ Set.Icc N (2*N)) (hd : d ∈ Set.Icc N (2*N))
    (h₂ : |a^2+b^2-c^2-d^2| ≤ N)
    (h₄ : |a^4+b^4-c^4-d^4| ≤ N^3) :
    a+b ∈ Set.Icc (2*N) (4*N) ∧
      |c+d-a-b| ≤ 3 ∧ |a-b-c+d| ≤ 2*N ∧ |a-b+c-d| ≤ 2*N ∧
      |(a-b-c+d)*(a-b+c-d)| ≤ 11*N := by
  have hp := sargos_fourth_product_gap hN ha hb hc hd h₂ h₄
  have hs := sargos_fourth_sum_gap hN ha.1 hb.1 hc.1 hd.1 h₂ hp
  refine ⟨⟨by linarith [ha.1,hb.1],by linarith [ha.2,hb.2]⟩,?_,?_,?_,
    sargos_fourth_difference_product h₂ hp⟩
  · rwa [show c+d-a-b = -(a+b-c-d) by ring,abs_neg]
  · apply abs_le.mpr
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2]
  · apply abs_le.mpr
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2]

end TaoTrudgianYang2025
