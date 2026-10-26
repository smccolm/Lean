import Dubon2026.SourceWeierstrassNormalizedTorsion

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> cyclotomic
Fricke expansions. The actual torsion expansion is regrouped by its
finite exponent fibers and identified with the native q-expansion.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
No external theorem module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

/-- The constant, positive head and three paired-tail monomial indices. -/
abbrev WpIdx : Type := Unit ⊕ ℕ+ ⊕ ((ℕ+ × ℕ+) × Fin 3)

/-- The explicit cyclotomic coefficient of each torsion Fourier monomial. -/
def wpMonCoeff (N a₁ a₂ : ℕ) : WpIdx → ℂ
  | Sum.inl _ => 1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then 0 else ((m : ℕ) : ℂ) * zetaN N ^ (a₂ * (m : ℕ))
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.2 : ℕ) : ℂ) * zetaN N ^ (a₂ * (p.2 : ℕ)),
        ((p.2 : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)),
        -2 * ((p.2 : ℕ) : ℂ)] i

/-- The actual nonnegative Fourier exponent of each torsion monomial. -/
def wpMonExp (N a₁ : ℕ) : WpIdx → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then (m : ℕ) else a₁ * (m : ℕ)
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.1 : ℕ) * N + a₁) * (p.2 : ℕ), ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ),
        (p.1 : ℕ) * N * (p.2 : ℕ)] i

/-- The finite exponent-fiber sum giving the actual torsion Fourier coefficient. -/
def wpQCoeff (N a₁ a₂ : ℕ) (n : ℕ) : ℂ :=
  ∑' i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeff N a₁ a₂ i

lemma wpMonCoeff_mem_kN (N a₁ a₂ : ℕ) (i : WpIdx) : wpMonCoeff N a₁ a₂ i ∈ kN N := by
  rcases i with u | m | ⟨p, i⟩
  · simp only [wpMonCoeff]
    split_ifs
    · exact add_mem (one_div_twelve_mem_kN N) (div_mem (zetaN_pow_mem_kN N _)
        (pow_mem (sub_mem (one_mem _) (zetaN_pow_mem_kN N _)) 2))
    · exact add_mem (one_div_twelve_mem_kN N) (zero_mem _)
  · simp only [wpMonCoeff]
    split_ifs
    · exact zero_mem _
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
  · simp only [wpMonCoeff]
    fin_cases i
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
    · exact mul_mem (natCast_mem_kN N _) (zetaN_inv_pow_mem_kN N _)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact mul_mem (neg_mem (by exact_mod_cast natCast_mem_kN N 2)) (natCast_mem_kN N _)

lemma le_mul_sub_of_lt {N a₁ : ℕ} (ha₁ : a₁ < N) (c : ℕ+) : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
  have h1 : (c : ℕ) * (a₁ + 1) ≤ (c : ℕ) * N := Nat.mul_le_mul_left _ ha₁
  have h2 : a₁ ≤ (c : ℕ) * a₁ := Nat.le_mul_of_pos_left _ c.pos
  rw [mul_add, mul_one] at h1
  omega

lemma le_wpMonExp_tail {N a₁ : ℕ} (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) (i : Fin 3) :
    (p.1 : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr (p, i))) ∧
      (p.2 : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr (p, i))) := by
  have hc := le_mul_sub_of_lt ha₁ p.1
  have hm : 1 ≤ (p.2 : ℕ) := p.2.pos
  have hc1 : 1 ≤ (p.1 : ℕ) := p.1.pos
  have key : ∀ A : ℕ, (p.1 : ℕ) ≤ A → (p.1 : ℕ) ≤ A * (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ A * (p.2 : ℕ) :=
    fun A hA ↦ ⟨hA.trans (Nat.le_mul_of_pos_right _ p.2.pos),
      Nat.le_mul_of_pos_left _ (lt_of_lt_of_le p.1.pos hA)⟩
  have hN : 0 < N := by omega
  fin_cases i
  · exact key _ (le_add_right (Nat.le_mul_of_pos_right _ hN))
  · exact key _ hc
  · exact key _ (Nat.le_mul_of_pos_right _ hN)

lemma finite_wpMonExp_fiber {N a₁ : ℕ} (ha₁ : a₁ < N) (n : ℕ) :
    (wpMonExp N a₁ ⁻¹' {n}).Finite := by
  classical
  let φ : Unit ⊕ Fin (n + 1) ⊕ ((Fin (n + 1) × Fin (n + 1)) × Fin 3) → WpIdx :=
    Sum.map id (Sum.map (fun k ↦ Nat.toPNat' k)
      (Prod.map (Prod.map (fun k ↦ Nat.toPNat' k) (fun k ↦ Nat.toPNat' k)) id))
  refine (Set.finite_range φ).subset ?_
  rintro (u | m | ⟨⟨c, m⟩, i⟩) hi <;>
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
  · exact ⟨Sum.inl u, rfl⟩
  · have hm : (m : ℕ) ≤ n := by
      simp only [wpMonExp] at hi
      split_ifs at hi with h
      · omega
      · have : 1 ≤ a₁ := Nat.pos_of_ne_zero h
        nlinarith
    refine ⟨Sum.inr (Sum.inl ⟨m, by omega⟩), ?_⟩
    simp [φ, PNat.coe_toPNat']
  · obtain ⟨hc, hm⟩ := le_wpMonExp_tail ha₁ (c, m) i
    dsimp only at hc hm
    rw [hi] at hc hm
    refine ⟨Sum.inr (Sum.inr ((⟨c, Nat.lt_succ_of_le hc⟩, ⟨m, Nat.lt_succ_of_le hm⟩), i)), ?_⟩
    simp [φ, PNat.coe_toPNat']

theorem wpQCoeff_mem_kN {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) : wpQCoeff N a₁ a₂ n ∈ kN N := by
  have := (finite_wpMonExp_fiber ha₁ n).to_subtype
  haveI := Fintype.ofFinite (wpMonExp N a₁ ⁻¹' {n})
  rw [wpQCoeff, tsum_fintype]
  exact sum_mem fun i _ ↦ wpMonCoeff_mem_kN N a₁ a₂ i


end
end Dubon2026.SourceFricke
