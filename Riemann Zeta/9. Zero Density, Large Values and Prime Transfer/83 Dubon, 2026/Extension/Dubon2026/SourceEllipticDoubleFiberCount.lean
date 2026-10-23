import Dubon2026.SourceEllipticMultiplicationSurjective

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

private noncomputable def qpoly (x : K) : K[X] :=
  X ^ 2 + (C ((W.baseChange K).a₁ * x + (W.baseChange K).a₃) * X +
    C (-(x ^ 3 + (W.baseChange K).a₂ * x ^ 2 + (W.baseChange K).a₄ * x +
      (W.baseChange K).a₆)))

omit [DecidableEq K] [IsAlgClosed K] in
private theorem degree_qpoly (x : K) : (qpoly W x).degree = 2 := by
  have hlt : (C ((W.baseChange K).a₁ * x + (W.baseChange K).a₃) * X +
      C (-(x ^ 3 + (W.baseChange K).a₂ * x ^ 2 + (W.baseChange K).a₄ * x +
        (W.baseChange K).a₆))).degree < ((X : K[X]) ^ 2).degree := by
    refine lt_of_le_of_lt degree_linear_le ?_
    rw [degree_X_pow]
    exact_mod_cast one_lt_two
  unfold qpoly
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  exact Nat.cast_ofNat

omit [DecidableEq K] [IsAlgClosed K] in
private theorem qpoly_ne_zero (x : K) : qpoly W x ≠ 0 := by
  intro h
  have hd := degree_qpoly W x
  rw [h, degree_zero] at hd
  simp at hd

omit [DecidableEq K] [IsAlgClosed K] in
private theorem isRoot_qpoly_iff (x y : K) :
    (qpoly W x).IsRoot y ↔ (W.baseChange K).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold qpoly
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  constructor <;> intro h <;> linear_combination h

omit [DecidableEq K] in
private theorem exists_equation_y (x : K) :
    ∃ y : K, (W.baseChange K).toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (qpoly W x)
    (by rw [degree_qpoly]; norm_num)
  exact ⟨y, (isRoot_qpoly_iff W x y).mp hy⟩

private noncomputable def coords : (W.baseChange K).toAffine.Point → K × K
  | .zero => (0, 0)
  | .some x y _ => (x, y)

omit [DecidableEq K] [IsAlgClosed K] in

theorem Ψ₂Sq_ne_zero_of_isElliptic [W.IsElliptic] : (W.baseChange K).Ψ₂Sq ≠ 0 := by
  intro h0
  set E := W.baseChange K with hE
  rw [Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : K) = 0 := congrArg Cubic.a h0
  have hb₂ : E.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : E.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : K) = 0 := by
    have h22 : (2 : K) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : E.Δ = 0 := by
    rw [show E.Δ = -E.b₂ ^ 2 * E.b₈ - 8 * E.b₄ ^ 3 - 27 * E.b₆ ^ 2 +
        9 * E.b₂ * E.b₄ * E.b₆ from rfl]
    linear_combination (-E.b₂ * E.b₈ + 9 * E.b₄ * E.b₆) * hb₂ +
      (-27 * E.b₆) * hb₆ + (-4 * E.b₄ ^ 3) * h2
  exact E.isUnit_Δ.ne_zero hΔ

theorem exists_double_fiber_card [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) :
    ∃ Q : (W.baseChange K).toAffine.Point, Q ≠ -Q ∧
      Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q ∨ n • P = -Q} = 2 * n ^ 2 := by
  classical
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hnQ : ((n : ℕ) : K) ≠ 0 := hn
  have hnZ : (((n : ℕ) : ℤ) : K) ≠ 0 := by exact_mod_cast hnQ

  have hB : {c : K | ¬ Squarefree (F' - C c * G)}.Finite := finite_not_squarefree_fiber W hn
  have hΨ₂ne : (W.baseChange K).Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero_of_isElliptic W
  have hB' : ((fun x => F'.eval x / G.eval x) ''
      {x : K | (W.baseChange K).Ψ₂Sq.IsRoot x}).Finite :=
    (finite_setOf_isRoot hΨ₂ne).image _
  have hB'' : {x : K | (W.baseChange K).Ψ₂Sq.IsRoot x}.Finite :=
    finite_setOf_isRoot hΨ₂ne
  obtain ⟨c, hc⟩ := ((hB.union hB').union hB'').infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union] at hc
  push Not at hc
  obtain ⟨⟨hcB, hcB'⟩, hcB''⟩ := hc
  have hsqf : Squarefree (F' - C c * G) := not_not.mp hcB

  obtain ⟨yQ, hyQ⟩ := exists_equation_y W c
  have hQns : (W.baseChange K).toAffine.Nonsingular c yQ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hyQ
  have hQne : (Point.some c yQ hQns : (W.baseChange K).toAffine.Point) ≠
      -(Point.some c yQ hQns) := by
    intro heq
    rw [Point.neg_some, Point.some.injEq] at heq
    have hzero := sub_negY_sq_eq_Ψ₂Sq_eval (W.baseChange K) hyQ
    rw [← heq.2, sub_self, zero_pow two_ne_zero] at hzero
    exact hcB'' hzero.symm
  refine ⟨Point.some c yQ hQns, hQne, ?_⟩
  set p : K[X] := F' - C c * G with hpdef

  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree = n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq (W.baseChange K) hnZ
    rw [Int.natAbs_natCast] at h
    rw [hGdef, h]
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le c G) ?_
    rw [hFdeg, hGdeg]
    have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
    omega
  have hpco : p.coeff (n ^ 2) = 1 := by
    have hF1 : F'.coeff (n ^ 2) = 1 := by
      have h := WeierstrassCurve.coeff_Φ (W.baseChange K) (n : ℤ)
      rw [Int.natAbs_natCast] at h
      rw [hFdef, h]
    have hG0 : G.coeff (n ^ 2) = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [hGdeg]
      have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
      omega
    rw [hpdef, coeff_sub, coeff_C_mul, hF1, hG0, mul_zero, sub_zero]
  have hpne : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hpco
    exact zero_ne_one hpco

  have hnodup : p.roots.Nodup := Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hsqf)
  have hroots_card : p.roots.toFinset.card = n ^ 2 := by
    rw [Multiset.toFinset_card_of_nodup hnodup,
      ← (IsAlgClosed.splits p).natDegree_eq_card_roots, hpdeg]

  have key_F : ∀ x : K, p.eval x = 0 → F'.eval x = c * G.eval x := by
    intro x hx
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
    exact hx
  have key_G : ∀ x : K, p.eval x = 0 → G.eval x ≠ 0 := by
    intro x hx hG0
    have hF0 : F'.eval x = 0 := by rw [key_F x hx, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  have key_Ψ₂ : ∀ x : K, p.eval x = 0 → (W.baseChange K).Ψ₂Sq.eval x ≠ 0 := by
    intro x hx h2
    refine hcB' ⟨x, h2, ?_⟩
    show F'.eval x / G.eval x = c
    rw [key_F x hx, mul_div_assoc, div_self (key_G x hx), mul_one]

  set R2fin : Finset (K × K) := p.roots.toFinset.biUnion
    (fun x => (qpoly W x).roots.toFinset.image (fun y => (x, y))) with hR2def
  have hmemR2 : ∀ z : K × K, z ∈ R2fin ↔
      p.eval z.1 = 0 ∧ (W.baseChange K).toAffine.Equation z.1 z.2 := by
    intro z
    rw [hR2def, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hz⟩
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Multiset.mem_toFinset, mem_roots hpne] at hx
      rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W x)] at hy
      exact ⟨hx, (isRoot_qpoly_iff W x y).mp hy⟩
    · rintro ⟨h1, h2⟩
      refine ⟨z.1, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, mem_roots hpne]
        exact h1
      · rw [Finset.mem_image]
        exact ⟨z.2, by
          rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W z.1)]
          exact (isRoot_qpoly_iff W z.1 z.2).mpr h2, rfl⟩

  have hfiber2 : ∀ x ∈ p.roots.toFinset,
      ((qpoly W x).roots.toFinset.image (fun y => (x, y))).card = 2 := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hpne] at hx
    obtain ⟨y₀, hy₀⟩ := exists_equation_y W x
    have hny₀ : (W.baseChange K).toAffine.Equation x
        ((W.baseChange K).toAffine.negY x y₀) :=
      (WeierstrassCurve.Affine.equation_neg x y₀).mpr hy₀
    have hyne : y₀ ≠ (W.baseChange K).toAffine.negY x y₀ := by
      intro hy
      refine key_Ψ₂ x hx ?_
      have hsq := sub_negY_sq_eq_Ψ₂Sq_eval ((W.baseChange K).toAffine) hy₀
      rw [← hsq, ← hy, sub_self]
      ring
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).2)]
    refine le_antisymm ?_ ?_
    · refine le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' _) ?_)
      rw [natDegree_eq_of_degree_eq_some (degree_qpoly W x)]
    · have hsub : ({y₀, (W.baseChange K).toAffine.negY x y₀} : Finset K) ⊆
          (qpoly W x).roots.toFinset := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W x)]
        rcases hy with rfl | rfl
        · exact (isRoot_qpoly_iff W x y).mpr hy₀
        · exact (isRoot_qpoly_iff W x _).mpr hny₀
      calc 2 = ({y₀, (W.baseChange K).toAffine.negY x y₀} : Finset K).card :=
            (Finset.card_pair hyne).symm
        _ ≤ _ := Finset.card_le_card hsub

  have hR2card : R2fin.card = 2 * n ^ 2 := by
    rw [hR2def, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hfiber2, Finset.sum_const, smul_eq_mul, hroots_card,
        mul_comm]
    · intro x₁ hx₁ x₂ hx₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro z hz₁ hz₂
      rw [Finset.mem_image] at hz₁ hz₂
      obtain ⟨y₁, -, rfl⟩ := hz₁
      obtain ⟨y₂, -, hz⟩ := hz₂
      exact hne ((Prod.ext_iff.mp hz).1.symm)

  set Q : (W.baseChange K).toAffine.Point := Point.some c yQ hQns with hQdef
  have hQ0 : Q ≠ 0 := Point.some_ne_zero hQns
  have hnegQ : -Q = Point.some c ((W.baseChange K).toAffine.negY c yQ)
      ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQns) := Point.neg_some hQns
  have hPne0 : ∀ P : (W.baseChange K).toAffine.Point, (n • P = Q ∨ n • P = -Q) → P ≠ 0 := by
    rintro P hP rfl
    rw [nsmul_zero] at hP
    rcases hP with h | h
    · exact hQ0 h.symm
    · exact hQ0 (neg_eq_zero.mp h.symm)

  have hmaps : Set.MapsTo (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}
      ↑R2fin := by
    rintro P hP
    have hP0 : P ≠ 0 := hPne0 P hP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd Point.zero_def.symm hP0
    · have hP' : n • (Point.some x y h : (W.baseChange K).toAffine.Point) = Q ∨
          n • (Point.some x y h : (W.baseChange K).toAffine.Point) = -Q := hP
      have hGx : G.eval x ≠ 0 := by
        intro hG0
        have hz : n • (Point.some x y h : (W.baseChange K).toAffine.Point) = 0 :=
          smul_eq_zero_of_ΨSq_eval_eq_zero W h hG0
        rw [hz] at hP'
        rcases hP' with h' | h'
        · exact hQ0 h'.symm
        · exact hQ0 (neg_eq_zero.mp h'.symm)
      obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W h hGx
      have hx'c : x' = c := by
        rw [hsmul] at hP'
        rcases hP' with h'' | h''
        · rw [hQdef] at h''
          exact (Point.some.inj h'').1
        · rw [hnegQ] at h''
          exact (Point.some.inj h'').1
      have hpx : p.eval x = 0 := by
        rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero, ← hx'c]
        exact hx'.symm
      rw [Finset.mem_coe, hmemR2]
      exact ⟨hpx, h.1⟩
  have hinj : Set.InjOn (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q} := by
    rintro P₁ hP₁ P₂ hP₂ hco
    rcases P₁ with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd Point.zero_def.symm (hPne0 _ hP₁)
    · rcases P₂ with _ | ⟨x₂, y₂, h₂⟩
      · exact absurd Point.zero_def.symm (hPne0 _ hP₂)
      · simp only [coords] at hco
        obtain ⟨hx, hy⟩ := Prod.ext_iff.mp hco
        subst hx
        subst hy
        rfl
  have hsurj : Set.SurjOn (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}
      ↑R2fin := by
    rintro z hz
    rw [Finset.mem_coe, hmemR2] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨x, y⟩ := z
    have h : (W.baseChange K).toAffine.Nonsingular x y :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp hz2
    have hGx : G.eval x ≠ 0 := key_G x hz1
    obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W h hGx
    have hx'c : x' = c := by
      have hFc := key_F x hz1
      rw [hFc] at hx'
      exact mul_right_cancel₀ hGx hx'
    subst hx'c
    have hy' := WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQns.1 rfl
    refine ⟨Point.some x y h, ?_, rfl⟩
    rcases hy' with rfl | rfl
    · exact Or.inl hsmul
    · refine Or.inr ?_
      rw [hnegQ]
      exact hsmul

  have hbij : Set.BijOn (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}
      ↑R2fin := ⟨hmaps, hinj, hsurj⟩
  calc Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q ∨ n • P = -Q}
      = Set.ncard {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q} :=
        Nat.card_coe_set_eq _
    _ = (coords W '' {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}).ncard :=
        (hbij.injOn.ncard_image).symm
    _ = (↑R2fin : Set (K × K)).ncard := by rw [hbij.image_eq]
    _ = R2fin.card := Set.ncard_coe_finset _
    _ = 2 * n ^ 2 := hR2card


end
end Dubon2026.SourceEllipticTorsion
