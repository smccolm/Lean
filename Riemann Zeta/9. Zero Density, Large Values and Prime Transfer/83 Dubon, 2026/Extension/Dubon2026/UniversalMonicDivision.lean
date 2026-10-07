import Dubon2026.AlmostAnalytic

/-! # Monic polynomial division is polynomial in the bounded input coefficients -/

namespace Dubon2026

open Polynomial Filter
open scoped Topology

noncomputable section

/-- Universal bounded numerator, using the first family of coefficient variables. -/
def universalNumerator (d : ℕ) : Polynomial (MvPolynomial (ℕ ⊕ ℕ) ℝ) :=
  ∑ i ∈ Finset.range d, C (MvPolynomial.X (Sum.inl i)) * X ^ i

/-- Universal monic denominator of fixed degree, using the second family. -/
def universalMonicDenominator (m : ℕ) : Polynomial (MvPolynomial (ℕ ⊕ ℕ) ℝ) :=
  X ^ m + ∑ i ∈ Finset.range m, C (MvPolynomial.X (Sum.inr i)) * X ^ i

theorem universalMonicDenominator_monic (m : ℕ) : (universalMonicDenominator m).Monic := by
  apply Polynomial.monic_X_pow_add
  rw [← Fin.sum_univ_eq_sum_range]
  exact Polynomial.degree_sum_fin_lt _

theorem universalNumerator_map (P Q : ℝ[X]) {d : ℕ} (hP : P.natDegree < d) :
    (universalNumerator d).map
      (MvPolynomial.aeval (Sum.elim P.coeff Q.coeff)).toRingHom = P := by
  simpa only [universalNumerator, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    MvPolynomial.aeval_X, Sum.elim_inl] using (P.as_sum_range_C_mul_X_pow' hP).symm

theorem universalMonicDenominator_map (P Q : ℝ[X]) (hQ : Q.Monic) {m : ℕ}
    (hm : Q.natDegree = m) :
    (universalMonicDenominator m).map
      (MvPolynomial.aeval (Sum.elim P.coeff Q.coeff)).toRingHom = Q := by
  simpa only [universalMonicDenominator, Polynomial.map_add, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_X,
    Sum.elim_inr, hm] using hQ.as_sum.symm

theorem universal_monic_division_coeff (P Q : ℝ[X]) {d m : ℕ}
    (hP : P.natDegree < d) (hQ : Q.Monic) (hm : Q.natDegree = m) (k : ℕ) :
    MvPolynomial.aeval (Sum.elim P.coeff Q.coeff)
      ((universalNumerator d /ₘ universalMonicDenominator m).coeff k) = (P /ₘ Q).coeff k := by
  have he := congrArg (fun R : ℝ[X] => R.coeff k)
    (Polynomial.map_divByMonic (p := universalNumerator d)
      (MvPolynomial.aeval (Sum.elim P.coeff Q.coeff)).toRingHom
        (universalMonicDenominator_monic m))
  rw [universalNumerator_map P Q hP, universalMonicDenominator_map P Q hQ hm] at he
  simpa only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using he

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem analyticAt_monic_division_coeff {P Q : V → ℝ[X]} {x : V} {d m : ℕ}
    (hP : ∀ k, AnalyticAt ℝ (fun y => (P y).coeff k) x)
    (hQ : ∀ k, AnalyticAt ℝ (fun y => (Q y).coeff k) x)
    (hn : ∀ᶠ y in 𝓝 x, (P y).natDegree < d ∧ (Q y).Monic ∧ (Q y).natDegree = m)
    (k : ℕ) : AnalyticAt ℝ (fun y => (P y /ₘ Q y).coeff k) x := by
  have ha : AnalyticAt ℝ (fun y => MvPolynomial.aeval
      (Sum.elim (P y).coeff (Q y).coeff)
        ((universalNumerator d /ₘ universalMonicDenominator m).coeff k)) x := by
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    cases i with
    | inl i => exact hP i
    | inr i => exact hQ i
  apply ha.congr
  filter_upwards [hn] with y hy
  exact universal_monic_division_coeff (P y) (Q y) hy.1 hy.2.1 hy.2.2 k

end

end Dubon2026
