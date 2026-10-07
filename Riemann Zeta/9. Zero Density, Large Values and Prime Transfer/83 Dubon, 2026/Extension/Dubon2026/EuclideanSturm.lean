import Dubon2026.SturmCertificate
import Dubon2026.RealRootCountLayers

/-! # Actual signed Euclidean remainder chains -/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The recursively computed tail after the two Euclidean seeds. -/
def signedRemainderTail (P Q : ℝ[X]) : ℕ → List ℝ[X]
  | 0 => []
  | k + 1 => if Q.natDegree = 0 then [] else
      (-(P % Q)) :: signedRemainderTail Q (-(P % Q)) k

theorem isCoprime_signed_remainder {P Q : ℝ[X]} (h : IsCoprime P Q) :
    IsCoprime Q (-(P % Q)) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨b + a * (P / Q), -a, ?_⟩
  calc
    (b + a * (P / Q)) * Q + -a * -(P % Q) = a * P + b * Q := by
      conv_rhs => rw [← EuclideanDomain.div_add_mod' P Q]
      ring
    _ = 1 := hab

theorem signed_remainder_ne_zero {P Q : ℝ[X]} (h : IsCoprime P Q)
    (hQ : Q.natDegree ≠ 0) : -(P % Q) ≠ 0 := by
  intro hz
  have hc := isCoprime_signed_remainder h
  rw [hz, isCoprime_zero_right] at hc
  exact hQ (Polynomial.natDegree_eq_zero_of_isUnit hc)

/-- A degree-bounded Euclidean computation supplies every algebraic chain condition. -/
theorem signedRemainderTail_chain (k : ℕ) {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hc : IsCoprime P Q) (hk : Q.natDegree < k) :
    Sturm.RemainderChain (P :: Q :: signedRemainderTail P Q k) := by
  induction k generalizing P Q with
  | zero => omega
  | succ k ih =>
    by_cases hd : Q.natDegree = 0
    · have he := Polynomial.eq_C_of_natDegree_eq_zero hd
      have hn : Q.coeff 0 ≠ 0 := by
        intro hz
        apply hQ
        rw [he, hz, Polynomial.C_0]
      simp only [signedRemainderTail, if_pos hd]
      rw [he]
      exact Sturm.RemainderChain.pair hP hn
    · have hr : -(P % Q) ≠ 0 := signed_remainder_ne_zero hc hd
      have hdeg : (-(P % Q)).natDegree < k := by
        rw [Polynomial.natDegree_neg]
        exact (Polynomial.natDegree_mod_lt P hd).trans_le (Nat.lt_succ_iff.mp hk)
      have ht := ih hQ hr (isCoprime_signed_remainder hc) hdeg
      simp only [signedRemainderTail, if_neg hd]
      apply Sturm.RemainderChain.cons ht hP (a := 1) (b := 1) (d := P / Q)
        (by norm_num) (by norm_num)
      simp only [Polynomial.C_1, one_mul, sub_neg_eq_add]
      exact (EuclideanDomain.div_add_mod' P Q).symm

/-- The Sturm chain computed from a nonconstant separable polynomial. -/
def euclideanSturmChain (P : ℝ[X]) : List ℝ[X] :=
  P :: P.derivative :: signedRemainderTail P P.derivative (P.derivative.natDegree + 1)

theorem euclideanSturmChain_isSturmChain {P : ℝ[X]} (hP : P.Separable)
    (hd : P.derivative ≠ 0) : Sturm.IsSturmChain P (euclideanSturmChain P) := by
  have hc := signedRemainderTail_chain (P.derivative.natDegree + 1)
    hP.ne_zero hd hP (Nat.lt_succ_self _)
  exact hc.isSturmChain (a := 1) (by norm_num) (by simp)

theorem euclideanSturmChain_count_Ioc {P : ℝ[X]} (hP : P.Separable)
    (hd : P.derivative ≠ 0) {l u : ℝ} (hlu : l ≤ u) :
    Sturm.sturmVar (euclideanSturmChain P) u +
      (P.roots.filter (fun t => t ∈ Set.Ioc l u)).card =
        Sturm.sturmVar (euclideanSturmChain P) l :=
  (euclideanSturmChain_isSturmChain hP hd).sturm_Ioc (Polynomial.nodup_roots hP) hlu

end

end Dubon2026
