import TaoTrudgianYang2025.RobertSargosWeightRemoval
import TaoTrudgianYang2025.RobertSargosNonzeroShiftReorder
import TaoTrudgianYang2025.RobertSargosPhysicalNonzeroShiftedTriple
import TaoTrudgianYang2025.RobertSargosCorrelationBoundary
import TaoTrudgianYang2025.SargosIntegerPrefix

/-! Exact signed source rectangles and physical common-prefix weight removal. -/

noncomputable section
open GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_nonzero_q_split {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (v : ℤ → A) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, v q) =
      (∑ x ∈ Finset.range (Q-1), v (1+x)) +
      ∑ x ∈ Finset.range (Q-1), v (1-(Q:ℤ)+x) := by
  have he : (Finset.Ioo (-(Q:ℤ)) Q).erase 0 =
      Finset.Icc (1:ℤ) (Q-1) ∪ Finset.Icc (1-(Q:ℤ)) (-1) := by
    ext q
    simp only [Finset.mem_erase,Finset.mem_Ioo,Finset.mem_union,Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc (1:ℤ) (Q-1))
      (Finset.Icc (1-(Q:ℤ)) (-1)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    simp only [Finset.mem_Icc] at hq hq'
    omega
  rw [he,Finset.sum_union hd,sargos_sum_Icc_eq_range,sargos_sum_Icc_eq_range]
  have hpos : ((Q:ℤ)-1+1-1).toNat = Q-1 := by omega
  have hneg : ((-1:ℤ)+1-(1-Q)).toNat = Q-1 := by omega
  rw [hpos,hneg]

theorem robertSargos_overlap_sum_range {A : Type*} [AddCommMonoid A]
    (H : ℕ) (r : ℤ) (v : ℤ → A) :
    (∑ h ∈ robertSargosHOverlap H r, v h) =
      ∑ y ∈ Finset.range (robertSargosHOverlap H r).card,
        v (max (H:ℤ) (H-r)+y) := by
  rw [robertSargosHOverlap,sargos_sum_Icc_eq_range]
  simp only [Int.card_Icc]

theorem robertSargos_nonzero_triple_rectangles (f : ℝ → ℝ)
    (H Q N : ℕ) (r m : ℤ) :
    robertSargosNonzeroShiftedTriple f H Q N r m =
      (∑ x ∈ Finset.range (Q-1),
        ∑ y ∈ Finset.range (robertSargosHOverlap H r).card,
          ∑ z ∈ Finset.range N,
            ((1-|(1:ℝ)+x|/Q : ℝ):ℂ)*fordAdditiveCharacter
              (robertSargosSymmetricDifference f ((m:ℝ)+(1+z)+(1+x))
                (((max (H:ℤ) (H-r):ℤ):ℝ)+y)-
               robertSargosSymmetricDifference f ((m:ℝ)+(1+z))
                (((max (H:ℤ) (H-r):ℤ):ℝ)+y+r))) +
      ∑ x ∈ Finset.range (Q-1),
        ∑ y ∈ Finset.range (robertSargosHOverlap H r).card,
          ∑ z ∈ Finset.range N,
            ((1-|(1:ℝ)-Q+x|/Q : ℝ):ℂ)*fordAdditiveCharacter
              (robertSargosSymmetricDifference f ((m:ℝ)+(1+z)+(1-Q+x))
                (((max (H:ℤ) (H-r):ℤ):ℝ)+y)-
               robertSargosSymmetricDifference f ((m:ℝ)+(1+z))
                (((max (H:ℤ) (H-r):ℤ):ℝ)+y+r)) := by
  unfold robertSargosNonzeroShiftedTriple
  rw [robertSargos_nonzero_q_split]
  simp_rw [robertSargos_overlap_sum_range,sargos_sum_Icc_eq_range]
  have hn : ((N:ℤ)+1-1).toNat = N := by omega
  simp only [hn,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_natCast]

theorem robertSargos_overlap_rectangle_bounds (H : ℕ) (r : ℤ)
    (hne : (robertSargosHOverlap H r).Nonempty) :
    (H:ℝ) ≤ ((max (H:ℤ) (H-r):ℤ):ℝ) ∧
    ((max (H:ℤ) (H-r):ℤ):ℝ)+(robertSargosHOverlap H r).card-1 ≤ 2*H ∧
    (H:ℝ) ≤ ((max (H:ℤ) (H-r):ℤ):ℝ)+r ∧
    ((max (H:ℤ) (H-r):ℤ):ℝ)+(robertSargosHOverlap H r).card-1+r ≤ 2*H := by
  let B := max (H:ℤ) (H-r)
  let U := min (2*(H:ℤ)-1) (2*(H:ℤ)-1-r)
  have hBU : B ≤ U := by
    simpa only [robertSargosHOverlap,Finset.nonempty_Icc] using hne
  have hc : ((robertSargosHOverlap H r).card:ℤ) = U+1-B := by
    simp only [robertSargosHOverlap,Int.card_Icc]
    exact Int.toNat_of_nonneg (by omega)
  have hBlo : (H:ℤ) ≤ B := le_max_left _ _
  have hBr : (H:ℤ)-r ≤ B := le_max_right _ _
  have hUhi : U ≤ 2*(H:ℤ)-1 := min_le_left _ _
  have hUr : U ≤ 2*(H:ℤ)-1-r := min_le_right _ _
  have hc' : ((robertSargosHOverlap H r).card:ℝ) = (U:ℝ)+1-B := by
    exact_mod_cast hc
  have hBlo' : (H:ℝ) ≤ (B:ℝ) := by exact_mod_cast hBlo
  have hBr' : (H:ℝ)-(r:ℝ) ≤ B := by exact_mod_cast hBr
  have hUhi' : (U:ℝ) ≤ 2*H-1 := by exact_mod_cast hUhi
  have hUr' : (U:ℝ) ≤ 2*H-1-r := by exact_mod_cast hUr
  change (H:ℝ) ≤ (B:ℝ) ∧ (B:ℝ)+(robertSargosHOverlap H r).card-1 ≤ 2*H ∧
    (H:ℝ) ≤ (B:ℝ)+r ∧ (B:ℝ)+(robertSargosHOverlap H r).card-1+r ≤ 2*H
  constructor
  · exact hBlo'
  constructor
  · linarith
  constructor <;> linarith


/-- The actual unweighted polynomial prefix, with the sign and all three cutoffs retained. -/
def robertSargosSignedPolynomialPrefix (f : ℝ → ℝ) (H Q : ℕ) (r m : ℤ)
    (positive : Bool) (X Y N : ℕ) : ℂ :=
  ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range N,
    robertSargosPolynomialCharacter f m r
      ((if positive then 1 else 1-(Q:ℝ))+x)
      (((max (H:ℤ) (H-r):ℤ):ℝ)+y) (1+z)

/-- Source weight removal chooses one sign and one prefix after summing over all m. -/
theorem robertSargos_physical_nonzero_common_prefix
    (f : ℝ → ℝ) (M H Q : ℕ) (r : ℤ) {C lam : ℝ}
    (hQeq : Q = ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ∃ (positive : Bool) (X Y N : ℕ),
      X ≤ Q-1 ∧ Y ≤ (robertSargosHOverlap H r).card ∧ N ≤ Q ∧
      (∑ m ∈ robertSargosCommonMInterval M H Q Q,
        ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) ≤
      32*(1+648*Real.pi*C)^3*
        ∑ m ∈ robertSargosCommonMInterval M H Q Q,
          ‖robertSargosSignedPolynomialPrefix f H Q r m positive X Y N‖ := by
  let S := robertSargosCommonMInterval M H Q Q
  let B : ℝ := ((max (H:ℤ) (H-r):ℤ):ℝ)
  let Y := (robertSargosHOverlap H r).card
  let D := 16*(1+648*Real.pi*C)^3
  let W := fun (positive : Bool) (m : ℤ) =>
    ∑ x ∈ Finset.range (Q-1), ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range Q,
      ((1-|(if positive then 1 else 1-(Q:ℝ))+x|/Q : ℝ):ℂ)*
        fordAdditiveCharacter
          (robertSargosSymmetricDifference f
            ((m:ℝ)+(1+z)+((if positive then 1 else 1-(Q:ℝ))+x)) (B+y)-
           robertSargosSymmetricDifference f ((m:ℝ)+(1+z)) (B+y+r))
  have hsplit (m : ℤ) :
      robertSargosNonzeroShiftedTriple f H Q Q r m = W true m+W false m := by
    simpa only [W,B,Y,Bool.false_eq_true,ite_true,ite_false] using
      robertSargos_nonzero_triple_rectangles f H Q Q r m
  by_cases he : Q-1 = 0 ∨ Y = 0
  · refine ⟨false,0,0,0,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,?_⟩
    have hz (m : ℤ) : robertSargosNonzeroShiftedTriple f H Q Q r m = 0 := by
      rw [hsplit]
      rcases he with hq | hy
      · simp [W,hq]
      · simp [W,hy]
    simp [hz,robertSargosSignedPolynomialPrefix]
  have hXp : 0 < Q-1 := by omega
  have hYp : 0 < Y := by omega
  have hQp : 0 < Q := by omega
  have hne : (robertSargosHOverlap H r).Nonempty := Finset.card_pos.mp hYp
  obtain ⟨hBlo,hBhi,hBrlo,hBrhi⟩ := robertSargos_overlap_rectangle_bounds H r hne
  have hHQ : H ≤ Q := by
    have h := robertSargos_floor_half_height hlam hsmall hH
    rw [← hQeq] at h
    have h' : (H:ℝ) ≤ Q := by linarith [Nat.cast_nonneg (α := ℝ) H]
    exact_mod_cast h'
  have hYQ : Y ≤ Q := (robertSargos_h_overlap_card H r).trans hHQ
  have hXm : ((Q-1:ℕ):ℝ) = (Q:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q),Nat.cast_one]
  have hrect (b : Bool) :
      ∃ X ≤ Q-1, ∃ V ≤ Y, ∃ N ≤ Q,
        (∑ m ∈ S, ‖W b m‖) ≤ D*
          ∑ m ∈ S, ‖robertSargosSignedPolynomialPrefix f H Q r m b X V N‖ := by
    let A : ℝ := if b then 1 else 1-Q
    let s : ℝ := if b then 1 else -1
    have hs : |s| = 1 := by cases b <;> norm_num [s]
    have hq : ∀ x ∈ Icc A (A+(Q-1:ℕ)-1), s*x ∈ Icc 0 (Q:ℝ) := by
      intro x hx
      rw [hXm] at hx
      cases b <;> dsimp [A,s] at hx ⊢ <;> constructor <;> linarith [hx.1,hx.2]
    obtain ⟨i,hi,j,hj,k,hk,hbound⟩ :=
      robertSargos_physical_rectangle_common_prefix f M H Q (Q-1) Y Q r A B s
        hQeq hC hlam hsmall hH hXp hYp hQp (by omega) hYQ le_rfl hs hq
        hBlo hBhi hBrlo hBrhi hf hlo hhi
    refine ⟨i+1,by omega,j+1,by omega,k+1,by omega,?_⟩
    simpa only [S,W,D,A,B,Y,robertSargosSignedPolynomialPrefix] using hbound
  obtain ⟨Xp,hXp',Yp,hYp',Np,hNp',hp⟩ := hrect true
  obtain ⟨Xm,hXm',Ym,hYm',Nm,hNm',hm⟩ := hrect false
  let P := ∑ m ∈ S, ‖robertSargosSignedPolynomialPrefix f H Q r m true Xp Yp Np‖
  let T := ∑ m ∈ S, ‖robertSargosSignedPolynomialPrefix f H Q r m false Xm Ym Nm‖
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have htotal :
      (∑ m ∈ S, ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) ≤ D*P+D*T := by
    calc
      _ ≤ ∑ m ∈ S, (‖W true m‖+‖W false m‖) := by
        apply Finset.sum_le_sum
        intro m _
        rw [hsplit]
        exact norm_add_le _ _
      _ = (∑ m ∈ S, ‖W true m‖)+(∑ m ∈ S, ‖W false m‖) := Finset.sum_add_distrib
      _ ≤ D*P+D*T := add_le_add hp hm
  rcases le_total P T with hPT | hTP
  · refine ⟨false,Xm,Ym,Nm,hXm',hYm',hNm',?_⟩
    change (∑ m ∈ S, ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) ≤
      32*(1+648*Real.pi*C)^3*T
    have hmul := mul_le_mul_of_nonneg_left hPT hD
    dsimp [D] at htotal hmul
    linarith
  · refine ⟨true,Xp,Yp,Np,hXp',hYp',hNp',?_⟩
    change (∑ m ∈ S, ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) ≤
      32*(1+648*Real.pi*C)^3*P
    have hmul := mul_le_mul_of_nonneg_left hTP hD
    dsimp [D] at htotal hmul
    linarith



/-- The original symmetric sum now feeds the unweighted signed polynomial family. -/
theorem robertSargos_physical_polynomial_reduction
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hHmin : lam^(-(1:ℝ)/7) ≤ H) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
    let R := ⌊lam^(-(1:ℝ)/13)⌋₊
    ∃ (positive : ℤ → Bool) (X Y N : ℤ → ℕ),
      (∀ r, X r ≤ Q-1 ∧ Y r ≤ (robertSargosHOverlap H r).card ∧ N r ≤ Q) ∧
      ‖robertSargosSymmetricSum f M H‖^2 ≤
        3140*C*(1+2*Real.pi*C)*(M:ℝ)^2+
          (256*(1+648*Real.pi*C)^3*(M:ℝ)*H/((Q:ℝ)*R*Q))*
            ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
              ∑ m ∈ robertSargosCommonMInterval M H Q Q,
                ‖robertSargosSignedPolynomialPrefix f H Q r m
                  (positive r) (X r) (Y r) (N r)‖ := by
  dsimp only
  let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
  let R := ⌊lam^(-(1:ℝ)/13)⌋₊
  choose positive X Y N hX hY hN hb using
    (fun r : ℤ => robertSargos_physical_nonzero_common_prefix
      f M H Q r rfl hC hlam hsmall hHmax hf hlo hhi)
  refine ⟨positive,X,Y,N,fun r => ⟨hX r,hY r,hN r⟩,?_⟩
  have hsum :
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        ∑ m ∈ robertSargosCommonMInterval M H Q Q,
          ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) ≤
      32*(1+648*Real.pi*C)^3*
        ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
          ∑ m ∈ robertSargosCommonMInterval M H Q Q,
            ‖robertSargosSignedPolynomialPrefix f H Q r m
              (positive r) (X r) (Y r) (N r)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => hb r)
  have hbase := robertSargos_physical_nonzero_shifted_triple f M H
    hC hlam hsmall hM hHmin hHmax hf hlo hhi
  have hcoeff : 0 ≤ 8*(M:ℝ)*H/((Q:ℝ)*R*Q) := by positivity
  have hbound := hbase.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hsum hcoeff) _)
  convert hbound using 1
  dsimp only [Q,R]
  simp only [div_eq_mul_inv]
  ring


end TaoTrudgianYang2025
