import Dubon2026.SourceEllipticTorsionFibers

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual n-torsion cardinality. The native division-polynomial
degrees and the proved point multiplication formula control actual point
fibers. Native perfect-field separability replaces the archive's generic
squarefree helpers, and one general surjectivity proof replaces its two
duplicated odd/general proofs. The torsion group is the native multiplication
homomorphism kernel. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsion
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
variable [IsAlgClosed K]

theorem smul_surjective_all [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Function.Surjective (fun P : (W.baseChange K).toAffine.Point => n • P) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  intro Q
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · refine ⟨0, ?_⟩
    show n • (0 : (W.baseChange K).toAffine.Point) = Point.zero
    rw [nsmul_zero]
    exact Point.zero_def
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hnQ : ((n : ℕ) : K) ≠ 0 := hn
  have hnZ : (((n : ℕ) : ℤ) : K) ≠ 0 := by exact_mod_cast hnQ
  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree = n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq (W.baseChange K) hnZ
    rw [Int.natAbs_natCast] at h
    rw [hGdef, h]
  have h1n : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
  set p : K[X] := F' - C xQ * G with hpdef
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le xQ G) ?_
    rw [hFdeg, hGdeg]
    omega
  have hpdegne : p.degree ≠ 0 := by
    have hpos' : 0 < p.natDegree := by rw [hpdeg]; omega
    exact (natDegree_pos_iff_degree_pos.mp hpos').ne'
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hpdegne
  have hpx : p.eval x₀ = 0 := hx₀
  have hroot : F'.eval x₀ = xQ * G.eval x₀ := by
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hpx
    exact hpx
  have hGx : G.eval x₀ ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x₀ = 0 := by rw [hroot, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x₀) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, (W.baseChange K).toAffine.Equation x₀ y := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
      (C 1 * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X
        + C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
            (W.baseChange K).a₆)))
      (by rw [degree_quadratic one_ne_zero]; norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
    linear_combination hy
  have h₀ : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hy₀
  obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W h₀ hGx
  rw [← hFdef, ← hGdef] at hx'
  have hx'Q : x' = xQ := by
    rw [hroot] at hx'
    exact mul_right_cancel₀ hGx hx'
  subst hx'Q
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQ.1 rfl with rfl | rfl
  · exact ⟨Point.some x₀ y₀ h₀, hsmul⟩
  · have hnegQ : -(Point.some x' yQ hQ : (W.baseChange K).toAffine.Point) =
        Point.some x' ((W.baseChange K).toAffine.negY x' yQ)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
    have hprev : n • (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) =
        -(Point.some x' yQ hQ) := by
      rw [hnegQ]
      exact hsmul
    have hsn : n • -(Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) =
        -(n • (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point)) :=
      neg_nsmul (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) n
    refine ⟨-(Point.some x₀ y₀ h₀), ?_⟩
    show n • -(Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) = Point.some x' yQ hQ
    rw [hsn, hprev, neg_neg]

theorem card_smul_fiber_all [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0)
    (Q : (W.baseChange K).toAffine.Point) :
    Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q} = Nat.card (nTorsion W (K := K) n) := by
  obtain ⟨P₀, hP₀⟩ := smul_surjective_all W hn Q
  have hP₀' : n • P₀ = Q := hP₀
  have e : nTorsion W (K := K) n ≃ {P : (W.baseChange K).toAffine.Point // n • P = Q} := by
    refine Equiv.subtypeEquiv (Equiv.addRight P₀) fun P => ?_
    show (P ∈ nTorsion W n) ↔ n • (P + P₀) = Q
    have hsa : n • (P + P₀) = n • P + n • P₀ := nsmul_add P P₀ n
    rw [hsa, hP₀']
    constructor
    · intro h
      have h' : n • P = 0 := h
      rw [h', zero_add]
    · intro h
      show n • P = 0
      exact add_right_cancel (h.trans (zero_add Q).symm)
  exact (Nat.card_congr e).symm


end
end Dubon2026.SourceEllipticTorsion
