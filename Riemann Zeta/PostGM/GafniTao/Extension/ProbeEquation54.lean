import GafniTao.FordTentSeries
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

#check Summable.prod
#check Summable.prod_factor
#check Summable.tsum_prod
#check Summable.tsum_prod'
#check Summable.mul_left
#check Summable.mul_right
#check Equiv.piOptionEquivProd
#check Equiv.piCongr
#check tsum_subtype
#check Summable.sum_le_tsum
#check HasSum.map
#check Finset.sum_pow
#check Fintype.sum_pow
#check map_sum
#check map_pow
#check Complex.sq_norm
#check Complex.normSq_apply
#check Summable.norm
#check NNReal.summable_coe
#check Fin.succFunEquiv
#check Equiv.summable_iff
#check Equiv.hasSum_iff
#check HasSum.map
#check summable_mul_of_summable_norm
#check HasSum.mul
#check Fin.prod_univ_succ
#check Fin.prod_univ_castSucc
#check Fin.sum_univ_succ
#check NNReal.coe_prod
#check NNReal.coe_tsum
#print Fin.succFunEquiv
#check hasSum_fintype
#check summable_of_hasFiniteSupport
#check Summable.of_nonneg_of_le
#check Summable.of_norm_bounded
#check Summable.mul_right
#check nnnorm_sum_le
#check coe_nnnorm
#check NNReal.sq_sqrt
#check Finset.sum_attach
#check map_ofNat
#check Complex.conj_ofReal
#check Complex.conj_I

open Finset
open scoped BigOperators NNReal ComplexConjugate

theorem probe_summable_pi_prod
    (k : ℕ) (f : (j : Fin k) → ℤ → ℝ≥0)
    (hf : ∀ j, Summable (f j)) :
    Summable (fun c : Fin k → ℤ => ∏ j : Fin k, f j (c j)) := by
  induction k with
  | zero => exact (hasSum_fintype _).summable
  | succ k ih =>
      let f0 : (j : Fin k) → ℤ → ℝ≥0 := fun j => f j.castSucc
      have h0 : Summable (fun c : Fin k → ℤ => ∏ j : Fin k, f0 j (c j)) :=
        ih f0 (fun j => hf j.castSucc)
      have hlast : Summable (f (Fin.last k)) := hf (Fin.last k)
      have h0R : Summable (fun c : Fin k → ℤ =>
          ((∏ j : Fin k, f0 j (c j) : ℝ≥0) : ℝ)) :=
        NNReal.summable_coe.mpr h0
      have hlastR : Summable (fun n : ℤ => ((f (Fin.last k) n : ℝ≥0) : ℝ)) :=
        NNReal.summable_coe.mpr hlast
      have hprodR : Summable (fun p : (Fin k → ℤ) × ℤ =>
          ((∏ j : Fin k, f0 j (p.1 j) : ℝ≥0) : ℝ) *
            ((f (Fin.last k) p.2 : ℝ≥0) : ℝ)) :=
        h0R.mul_of_nonneg hlastR (fun _ => by positivity) (fun _ => by positivity)
      have hprod : Summable (fun p : (Fin k → ℤ) × ℤ =>
          (∏ j : Fin k, f0 j (p.1 j)) * f (Fin.last k) p.2) :=
        NNReal.summable_coe.mp (by simpa using hprodR)
      apply ((Fin.succFunEquiv ℤ k).symm.summable_iff).mp
      convert hprod using 1
      funext p
      simp only [Function.comp_apply]
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _hj
        change f j.castSucc
            (Fin.append p.1 (fun _ : Fin 1 => p.2) j.castSucc) =
          f0 j (p.1 j)
        change f j.castSucc
            (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.castAdd 1 j)) =
          f j.castSucc (p.1 j)
        rw [Fin.append_left]
      · have hlastEq : Fin.last k = Fin.natAdd k (0 : Fin 1) := by
          ext
          simp
        rw [hlastEq]
        change f (Fin.natAdd k 0)
            (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.natAdd k 0)) =
          f (Fin.natAdd k 0) p.2
        rw [Fin.append_right]

theorem probe_hasSum_pi_prod_complex
    (k : ℕ) (f : (j : Fin k) → ℤ → ℂ) (a : Fin k → ℂ)
    (hf : ∀ j, HasSum (f j) (a j))
    (habs : ∀ j, Summable (fun n => ‖f j n‖)) :
    HasSum (fun c : Fin k → ℤ => ∏ j : Fin k, f j (c j))
      (∏ j : Fin k, a j) := by
  induction k with
  | zero =>
      convert (hasSum_fintype
        (fun c : Fin 0 → ℤ => ∏ j : Fin 0, f j (c j))) using 1 <;> simp
  | succ k ih =>
      let f0 : (j : Fin k) → ℤ → ℂ := fun j => f j.castSucc
      let a0 : Fin k → ℂ := fun j => a j.castSucc
      have h0 : HasSum (fun c : Fin k → ℤ => ∏ j : Fin k, f0 j (c j))
          (∏ j : Fin k, a0 j) :=
        ih f0 a0 (fun j => hf j.castSucc) (fun j => habs j.castSucc)
      have h0absNN : Summable (fun c : Fin k → ℤ =>
          ∏ j : Fin k, (⟨‖f0 j (c j)‖, norm_nonneg _⟩ : ℝ≥0)) :=
        probe_summable_pi_prod k
          (fun j n => ⟨‖f0 j n‖, norm_nonneg _⟩)
          (fun j => NNReal.summable_coe.mp (habs j.castSucc))
      have h0abs : Summable (fun c : Fin k → ℤ =>
          ‖∏ j : Fin k, f0 j (c j)‖) := by
        have h0absR := NNReal.summable_coe.mpr h0absNN
        convert h0absR using 1
        funext c
        rw [norm_prod]
        norm_cast
      have hlast := hf (Fin.last k)
      have hlastAbs := habs (Fin.last k)
      have hcross := summable_mul_of_summable_norm h0abs hlastAbs
      have hpair := h0.mul hlast hcross
      apply ((Fin.succFunEquiv ℤ k).symm.hasSum_iff).mp
      convert hpair using 1
      · funext p
        simp only [Function.comp_apply]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl
          intro j _hj
          change f j.castSucc
              (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.castAdd 1 j)) =
            f j.castSucc (p.1 j)
          rw [Fin.append_left]
        · have hlastEq : Fin.last k = Fin.natAdd k (0 : Fin 1) := by
            ext
            simp
          rw [hlastEq]
          change f (Fin.natAdd k 0)
              (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.natAdd k 0)) =
            f (Fin.natAdd k 0) p.2
          rw [Fin.append_right]
      · rw [Fin.prod_univ_castSucc]

namespace GafniTao

noncomputable section

theorem probe_summable_coordinate
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) :
    Summable (fun n : ℤ =>
      (⟨fordSincSquareWeight r M j (n : ℝ),
        fordSincSquareWeight_nonneg r M j (n : ℝ)⟩ : ℝ≥0)) := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hw : 0 < 1 / (2 * A) := by positivity
  have hcoeff := summable_fordTentFourierCoefficient hw
  have hscaled := hcoeff.mul_left (((Real.pi ^ 2 * A / 2 : ℝ) : ℂ))
  have hcomplex : Summable (fun n : ℤ =>
      (fordSincSquareWeight r M j (n : ℝ) : ℂ)) := by
    apply hscaled.congr
    intro n
    rw [fordSincSquareWeight_eq_tentCoefficient hr hM]
  have hreal : Summable (fun n : ℤ =>
      fordSincSquareWeight r M j (n : ℝ)) := by
    have hnorm := hcomplex.norm
    convert hnorm using 1
    funext n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fordSincSquareWeight_nonneg r M j (n : ℝ))]
  exact NNReal.summable_coe.mp hreal

end

end GafniTao

namespace GafniTao

noncomputable section

abbrev ProbeBTuple (s : ℕ) (B : Finset ℕ) := Fin s → B

def probeTerm (k M r : ℕ) (B : Finset ℕ) (t z : ℝ)
    (c : Fin k → ℤ) (b : B) : ℂ :=
  fordLemma51Epsilon k M r t z b *
    fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)

theorem probe_sum_subtype
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    fordLemma51FiberOscillatorySum k M r B t z c =
      ∑ b : B, probeTerm k M r B t z c b := by
  unfold fordLemma51FiberOscillatorySum probeTerm
  exact (Finset.sum_attach B (fun b =>
    fordLemma51Epsilon k M r t z b *
      fordAdditiveCharacter (fordLemma51FiberPhase k t z b c))).symm

theorem probe_conj_character (x : ℝ) :
    conj (fordAdditiveCharacter x) = fordAdditiveCharacter (-x) := by
  unfold fordAdditiveCharacter
  calc
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) =
        Complex.exp (conj (2 * Real.pi * Complex.I * (x : ℂ))) :=
      (Complex.exp_conj (2 * Real.pi * Complex.I * (x : ℂ))).symm
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
      congr 1
      rw [map_mul, map_mul, map_mul]
      simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

def probeTupleCoefficient
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : ProbeBTuple s B) : ℂ :=
  (∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
    conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))

def probeTuplePhase
    (k s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : ProbeBTuple s B) : ℝ :=
  (∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c) -
    ∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c

def probeDifferenceVector
    (k s : ℕ) (B : Finset ℕ) (x y : ProbeBTuple s B) : Fin k → ℤ :=
  fun j =>
    (∑ i : Fin s, ((x i : ℕ) : ℤ) ^ ((j : ℕ) + 1)) -
      ∑ i : Fin s, ((y i : ℕ) : ℤ) ^ ((j : ℕ) + 1)

def probeDifferencePhase
    (k : ℕ) (t z : ℝ) (d c : Fin k → ℤ) : ℝ :=
  ∑ j : Fin k,
    fordTaylorGamma t z (j : ℕ) * (d j : ℝ) * (c j : ℝ)

theorem probe_tuplePhase_eq_differencePhase
    (k s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : ProbeBTuple s B) :
    probeTuplePhase k s B t z c x y =
      probeDifferencePhase k t z (probeDifferenceVector k s B x y) c := by
  unfold probeTuplePhase probeDifferencePhase fordLemma51FiberPhase
  rw [Finset.sum_comm]
  rw [show (∑ i : Fin s, ∑ j : Fin k,
      fordTaylorGamma t z (j : ℕ) * (y i : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ)) =
      ∑ j : Fin k, ∑ i : Fin s,
        fordTaylorGamma t z (j : ℕ) * (y i : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ) by
    rw [Finset.sum_comm]]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold probeDifferenceVector
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  push_cast
  ring

theorem probe_prod_term
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x : ProbeBTuple s B) :
    (∏ i : Fin s, probeTerm k M r B t z c (x i)) =
      (∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter
          (∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c) := by
  unfold probeTerm
  rw [Finset.prod_mul_distrib]
  rw [← fordAdditiveCharacter_sum Finset.univ]

theorem probe_conj_prod_term
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (y : ProbeBTuple s B) :
    conj (∏ i : Fin s, probeTerm k M r B t z c (y i)) =
      conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter
          (-(∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c)) := by
  rw [probe_prod_term]
  rw [map_mul, probe_conj_character]

theorem probe_pair_term
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : ProbeBTuple s B) :
    (∏ i : Fin s, probeTerm k M r B t z c (x i)) *
        conj (∏ i : Fin s, probeTerm k M r B t z c (y i)) =
      probeTupleCoefficient k M r s B t z x y *
        fordAdditiveCharacter (probeTuplePhase k s B t z c x y) := by
  rw [probe_prod_term, probe_conj_prod_term]
  unfold probeTupleCoefficient probeTuplePhase
  let A := ∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c
  let D := ∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c
  have hchar : fordAdditiveCharacter A * fordAdditiveCharacter (-D) =
      fordAdditiveCharacter (A - D) := by
    rw [← fordAdditiveCharacter_add]
    congr 1
  change
    ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter A) *
      (conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter (-D)) =
      ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))) *
          fordAdditiveCharacter (A - D)
  rw [show
    ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter A) *
      (conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter (-D)) =
      ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))) *
          (fordAdditiveCharacter A * fordAdditiveCharacter (-D)) by ring]
  rw [hchar]

theorem probe_norm_power_expand
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    ((‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) : ℝ≥0) : ℂ) =
      ∑ x : ProbeBTuple s B, ∑ y : ProbeBTuple s B,
        probeTupleCoefficient k M r s B t z x y *
          fordAdditiveCharacter (probeTuplePhase k s B t z c x y) := by
  let Z := fordLemma51FiberOscillatorySum k M r B t z c
  have hZ : Z = ∑ b : B, probeTerm k M r B t z c b :=
    probe_sum_subtype k M r B t z c
  have hpowZ : Z ^ s = ∑ x : ProbeBTuple s B,
      ∏ i : Fin s, probeTerm k M r B t z c (x i) := by
    rw [hZ]
    exact Fintype.sum_pow _ s
  have hpowConj : conj Z ^ s = ∑ y : ProbeBTuple s B,
      conj (∏ i : Fin s, probeTerm k M r B t z c (y i)) := by
    rw [← map_pow, hpowZ, map_sum]
  calc
    ((‖Z‖₊ ^ (2 * s) : ℝ≥0) : ℂ) =
        Z ^ s * conj Z ^ s := by
      rw [ford_pow_mul_conj_pow]
      push_cast
      rfl
    _ = (∑ x : ProbeBTuple s B,
          ∏ i : Fin s, probeTerm k M r B t z c (x i)) *
        (∑ y : ProbeBTuple s B,
          conj (∏ i : Fin s, probeTerm k M r B t z c (y i))) := by
      rw [hpowZ, hpowConj]
    _ = ∑ x : ProbeBTuple s B, ∑ y : ProbeBTuple s B,
        (∏ i : Fin s, probeTerm k M r B t z c (x i)) *
          conj (∏ i : Fin s, probeTerm k M r B t z c (y i)) := by
      rw [Finset.sum_mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact probe_pair_term k M r s B t z c x y

end

end GafniTao
