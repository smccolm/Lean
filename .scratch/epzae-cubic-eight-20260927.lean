import TaoTrudgianYang2025.IntegerIntervalCount
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-! Exact finite cubic-eighth to square/product-sixth reduction.
This is algebraic source entry for the alternate BI route, not a moment bound.
The logarithmic sixth moment and the sharp short-sum assembly remain open. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025.CubicEightPrototype

def hadamardFour (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 0+x 1+x 2+x 3, x 0+x 1-x 2-x 3,
    x 0-x 1+x 2-x 3, x 0-x 1-x 2+x 3]

/-- The actual integral coordinate change, with its scale and all four
inverse coordinates retained. No invertibility is postulated. -/
theorem hadamardFour_involution (x : Fin 4 → ℤ) :
    hadamardFour (hadamardFour x) = fun i => 4*x i := by
  funext i
  fin_cases i <;> simp [hadamardFour] <;> ring

theorem hadamardFour_injective : Function.Injective hadamardFour := by
  intro x y hxy
  have he := congrArg hadamardFour hxy
  rw [hadamardFour_involution,hadamardFour_involution] at he
  funext i
  have hi := congrFun he i
  omega

/-- The first three power sums in the literal four-coordinate transform. -/
theorem hadamardFour_power_sums (x : Fin 4 → ℤ) :
    (∑ i, x i)=hadamardFour x 0 ∧
      4*(∑ i, (x i)^2)=(hadamardFour x 0)^2+(hadamardFour x 1)^2+
        (hadamardFour x 2)^2+(hadamardFour x 3)^2 ∧
      16*(∑ i, (x i)^3)=(hadamardFour x 0)^3+
        3*hadamardFour x 0*((hadamardFour x 1)^2+
          (hadamardFour x 2)^2+(hadamardFour x 3)^2)+
        6*hadamardFour x 1*hadamardFour x 2*hadamardFour x 3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [Fin.sum_univ_succ,hadamardFour] <;> ring

/-- Equal first and second moments turn the cubic difference into an exact
triple-product difference, with the correct factor 3/8. -/
theorem hadamardFour_cubic_resonance (x y : Fin 4 → ℤ)
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2) :
    hadamardFour x 0=hadamardFour y 0 ∧
      (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
        (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 ∧
      3*(hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
        hadamardFour y 1*hadamardFour y 2*hadamardFour y 3) =
        8*((∑ i, (x i)^3)-∑ i, (y i)^3) := by
  obtain ⟨hx₁,hx₂,hx₃⟩ := hadamardFour_power_sums x
  obtain ⟨hy₁,hy₂,hy₃⟩ := hadamardFour_power_sums y
  have hzero : hadamardFour x 0=hadamardFour y 0 := by omega
  have hsq : (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
      (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 := by
    rw [hzero,hsecond] at hx₂
    linarith only [hx₂,hy₂]
  refine ⟨hzero,hsq,?_⟩
  rw [hzero,hsq] at hx₃
  linarith only [hx₃,hy₃]

/-- The finite near-cubic condition transfers without treating an
approximate moment equality as an exact one. -/
theorem hadamardFour_near_product (x y : Fin 4 → ℤ) {P : ℤ}
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2)
    (hthird : |(∑ i, (x i)^3)-∑ i, (y i)^3| ≤ P) :
    3*|hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
      hadamardFour y 1*hadamardFour y 2*hadamardFour y 3| ≤ 8*P := by
  have he := congrArg abs (hadamardFour_cubic_resonance x y hfirst hsecond).2.2
  simp only [abs_mul,show |(3:ℤ)|=3 by norm_num,show |(8:ℤ)|=8 by norm_num] at he
  linarith only [he,hthird]

/-- Every transformed integer remains in the literal enlarged box. -/
theorem hadamardFour_abs_le (x : Fin 4 → ℤ) {N : ℤ}
    (hx : ∀ i, |x i| ≤ N) (i : Fin 4) : |hadamardFour x i| ≤ 4*N := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have h2 := abs_le.mp (hx 2)
  have h3 := abs_le.mp (hx 3)
  fin_cases i <;> simp [hadamardFour,abs_le] <;> omega

def sixSquareProductSolutions (N P : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) := by
  classical
  let box := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N:ℤ)) N)
  exact (box ×ˢ box).filter (fun p => (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2 ∧
    |p.1 0*p.1 1*p.1 2-p.2 0*p.2 1*p.2 2| ≤ (P:ℤ))

def cubicEightCode (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) :
    ℤ × ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (hadamardFour p.1 0,(fun i => hadamardFour p.1 i.succ,
    fun i => hadamardFour p.2 i.succ))

/-- The common first moment plus the six transformed coordinates determines
the original eight integers; there is no lost source multiplicity. -/
theorem cubicEightCode_injOn :
    Set.InjOn cubicEightCode {p | (∑ i, p.1 i)=∑ i, p.2 i} := by
  intro p hp q hq he
  have h0 := congrArg (fun z => z.1) he
  have h1 := congrArg (fun z => z.2.1) he
  have h2 := congrArg (fun z => z.2.2) he
  have hp₀ : hadamardFour p.1 0=hadamardFour p.2 0 :=
    (hadamardFour_power_sums p.1).1.symm.trans (hp.trans (hadamardFour_power_sums p.2).1)
  have hq₀ : hadamardFour q.1 0=hadamardFour q.2 0 :=
    (hadamardFour_power_sums q.1).1.symm.trans (hq.trans (hadamardFour_power_sums q.2).1)
  apply Prod.ext
  · apply hadamardFour_injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun h1 j
  · apply hadamardFour_injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp₀.symm.trans (h0.trans hq₀)
    · exact congrFun h2 j

/-- Literal cardinality reduction of the cubic eight-variable source to
the six-variable square/product system, with all box and fiber losses proved.
The analytic bound for the right-hand cardinality is still missing. -/
theorem cubic_eight_count_le_six (N P : ℕ)
    (S : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)))
    (hbox : ∀ p∈S, (∀ i, |p.1 i| ≤ (N:ℤ)) ∧ ∀ i, |p.2 i| ≤ (N:ℤ))
    (hfirst : ∀ p∈S, (∑ i, p.1 i)=∑ i, p.2 i)
    (hsecond : ∀ p∈S, (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2)
    (hthird : ∀ p∈S, |(∑ i, (p.1 i)^3)-∑ i, (p.2 i)^3| ≤ (P:ℤ)) :
    S.card ≤ (8*N+1)*(sixSquareProductSolutions (4*N) (8*P)).card := by
  classical
  let T := Finset.Icc (-4*(N:ℤ)) (4*N) ×ˢ sixSquareProductSolutions (4*N) (8*P)
  have hmaps : Set.MapsTo cubicEightCode S T := by
    intro p hp
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr (abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 0))
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 i.succ)
          simpa only [cubicEightCode,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
            (Finset.mem_Icc.mpr hh)
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.2 (hbox p hp).2 i.succ)
          simpa only [cubicEightCode,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
            (Finset.mem_Icc.mpr hh)
      · constructor
        · have hh := (hadamardFour_cubic_resonance p.1 p.2
            (hfirst p hp) (hsecond p hp)).2.1
          simpa [cubicEightCode,Fin.sum_univ_succ,←add_assoc] using hh
        · have hh := hadamardFour_near_product p.1 p.2
            (hfirst p hp) (hsecond p hp) (hthird p hp)
          change |hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3| ≤ ((8*P:ℕ):ℤ)
          push_cast
          linarith [abs_nonneg (hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3)]
  have hc := Finset.card_le_card_of_injOn cubicEightCode hmaps
    (fun p hp q hq he => cubicEightCode_injOn (hfirst p hp) (hfirst q hq) he)
  have hcard : (Finset.Icc (-4*(N:ℤ)) (4*N)).card=8*N+1 := by
    rw [Int.card_Icc]
    omega
  simpa only [T,Finset.card_product,hcard] using hc

#print axioms hadamardFour_involution
#print axioms hadamardFour_injective
#print axioms hadamardFour_power_sums
#print axioms hadamardFour_cubic_resonance
#print axioms hadamardFour_near_product
#print axioms hadamardFour_abs_le
#print axioms cubicEightCode_injOn
#print axioms cubic_eight_count_le_six

-- Equal first two moments do not make the cubic difference vanish.
example :
    (∑ i : Fin 4, (![0,3,5,6] : Fin 4 → ℤ) i)=
      ∑ i : Fin 4, (![1,2,4,7] : Fin 4 → ℤ) i ∧
    (∑ i : Fin 4, ((![0,3,5,6] : Fin 4 → ℤ) i)^2)=
      ∑ i : Fin 4, ((![1,2,4,7] : Fin 4 → ℤ) i)^2 ∧
    (∑ i : Fin 4, ((![0,3,5,6] : Fin 4 → ℤ) i)^3)-
      (∑ i : Fin 4, ((![1,2,4,7] : Fin 4 → ℤ) i)^3) = -48 := by
  norm_num [Fin.sum_univ_succ]

-- The exact nonzero product difference is -128, not the cubic difference.
example :
    let x : Fin 4 → ℤ := ![0,3,5,6]
    let y : Fin 4 → ℤ := ![1,2,4,7]
    hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
      hadamardFour y 1*hadamardFour y 2*hadamardFour y 3 = -128 := by
  decide

-- The finite reduction retains the all-zero source and its enlarged-box boundary.
example : (sixSquareProductSolutions 0 0).card=1 := by
  simp [sixSquareProductSolutions,Finset.filter_singleton]

end TaoTrudgianYang2025.CubicEightPrototype
