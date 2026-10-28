module

public import NormalizerDelta.SigmaHCount
public import NormalizerDelta.DefsXN

@[expose] public section

/-!
# X(N): the order of the modular automorphism group

* Γ₁(N) = Γ_{1}(N) (d ≡ 1 forces a ≡ 1), so [Γ₀(N) : Γ₁(N)] = |(ℤ/N)ˣ| = φ(N) by `relindex_GammaDelta'`.
* γ ↦ b mod N is a homomorphism Γ₁(N) → ℤ/N (b' + b, as a ≡ d ≡ 1), onto via [[1, b], [0, 1]], with kernel
  Γ(N); so [Γ₁(N) : Γ(N)] = N.
* [SL₂(ℤ) : Γ(N)] = ψ(N)·φ(N)·N = N³∏(1 − 1/p²) (`Gamma0_index`), and = |SL₂(ℤ/N)| since Γ(N) is the kernel of
  the (surjective, `redSL_surjective`) reduction.
* The BG orders from `BG_GammaR_equiv'`, `BG_pmGammaR_equiv'`, |{±1}| = 2 for N ≥ 3, and for X_Δ(M²) from the
  conjugation `conj_GammaDelta_sq'` (relative indices are preserved by the isomorphism).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open CongruenceSubgroup

/-! ### [Γ₀(N) : Γ₁(N)] = φ(N) -/

theorem GammaDelta_bot (N : ℕ) : GammaDelta N ⊥ = Gamma1 N := by
  ext γ
  rw [Gamma1_mem]
  constructor
  · rintro ⟨h0, u, hu, hγ⟩
    rw [Subgroup.mem_bot] at hu
    subst hu
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 h0
    have hd : ((γ 1 1 : ℤ) : ZMod N) = 1 := by rw [← hγ]; simp
    have hdet := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
    simp only [det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, hc, hd, mul_zero, mul_one,
      sub_zero] at hdet
    exact ⟨hdet, hd, hc⟩
  · rintro ⟨ha, hd, hc⟩
    exact ⟨Gamma0_mem.2 hc, 1, Subgroup.one_mem _, by rw [hd]; simp⟩

theorem relIndex_Gamma1_Gamma0' (N : ℕ) [NeZero N] :
    (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
  rw [← GammaDelta_bot, relindex_GammaDelta', Subgroup.index_bot, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-! ### [Γ₁(N) : Γ(N)] = N -/

/-- γ ↦ b mod N on Γ₁(N). -/
def upperMap (N : ℕ) : Gamma1 N →* Multiplicative (ZMod N) where
  toFun γ := Multiplicative.ofAdd (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' γ γ' := by
    obtain ⟨ha, hd, -⟩ := (Gamma1_mem N γ).1 γ.2
    obtain ⟨ha', hd', -⟩ := (Gamma1_mem N γ').1 γ'.2
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, ha, hd']
    ring

theorem upperMap_surjective (N : ℕ) [NeZero N] : Function.Surjective (upperMap N) := by
  intro x
  have h : (1 : ℤ) * 1 - (Multiplicative.toAdd x).val * 0 = 1 := by ring
  refine ⟨⟨mkSL 1 (Multiplicative.toAdd x).val 0 1 h, (Gamma1_mem N _).2 ⟨by simp [mkSL],
    by simp [mkSL], by simp [mkSL]⟩⟩, ?_⟩
  show Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℤ) : ZMod N) = x
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

theorem upperMap_ker (N : ℕ) : (upperMap N).ker = (Gamma N).subgroupOf (Gamma1 N) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma_mem]
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).1 γ.2
  show Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one]
  exact ⟨fun h => ⟨ha, h, hc, hd⟩, fun h => h.2.1⟩

theorem relIndex_Gamma_Gamma1' (N : ℕ) [NeZero N] : (Gamma N).relIndex (Gamma1 N) = N := by
  rw [Subgroup.relIndex, ← upperMap_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (upperMap_surjective N), Subgroup.card_top]
  exact Nat.card_zmod N

/-! ### [SL₂(ℤ) : Γ(N)] -/

theorem Gamma_le_Gamma1 (N : ℕ) : Gamma N ≤ Gamma1 N := fun γ h => by
  obtain ⟨ha, -, hc, hd⟩ := Gamma_mem.1 h
  exact (Gamma1_mem N γ).2 ⟨ha, hd, hc⟩

theorem prod_one_sub_inv_sq (N : ℕ) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) =
      (∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹)) * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp
  ring

theorem index_Gamma' (N : ℕ) [NeZero N] :
    ((Gamma N).index : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma1 N),
    ← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 N), relIndex_Gamma_Gamma1',
    relIndex_Gamma1_Gamma0']
  push_cast
  rw [Gamma0_index', psi, Nat.totient_eq_mul_prod_factors, prod_one_sub_inv_sq]
  ring

/-! ### |SL₂(ℤ/N)| -/

theorem index_Gamma_eq_card (N : ℕ) [NeZero N] : (Gamma N).index = Nat.card SL(2, ZMod N) := by
  show (redSL N).ker.index = _
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (redSL_surjective N), Subgroup.card_top]

theorem card_SL2_ZMod' (N : ℕ) [NeZero N] :
    (Nat.card SL(2, ZMod N) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [← index_Gamma_eq_card, index_Gamma']

theorem card_BG_GammaR' (N : ℕ) [NeZero N] :
    (Nat.card (BG (GammaR N)) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  obtain ⟨e, -⟩ := BG_GammaR_equiv' N
  rw [Nat.card_congr e.toEquiv, card_SL2_ZMod']

/-! ### |SL₂(ℤ/N)/{±1}| -/

theorem neg_one_ne_one_SL {N : ℕ} (hN : 3 ≤ N) : (-1 : SL(2, ZMod N)) ≠ 1 := by
  have : Fact (2 < N) := ⟨by omega⟩
  intro h
  have := congrArg (fun g : SL(2, ZMod N) => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq] at this
  exact ZMod.neg_one_ne_one this

theorem card_pmOneSL {N : ℕ} (hN : 3 ≤ N) : Nat.card (pmOneSL N) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pmOneSL, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq, neg_one_mul, neg_neg]) (neg_one_ne_one_SL hN)

theorem card_PSL2_ZMod' (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    (Nat.card (SL(2, ZMod N) ⧸ pmOneSL N) : ℚ) =
      N ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have h := Subgroup.card_mul_index (pmOneSL N)
  rw [card_pmOneSL hN] at h
  have h' : (Nat.card (SL(2, ZMod N) ⧸ pmOneSL N) : ℚ) = Nat.card SL(2, ZMod N) / 2 := by
    rw [← h]; push_cast; rw [Subgroup.index]; ring
  rw [h', card_SL2_ZMod']
  ring

theorem card_BG_pmGammaR' (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    (Nat.card (BG (pmGammaR N)) : ℚ) = N ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  obtain ⟨e, -⟩ := BG_pmGammaR_equiv' N
  rw [Nat.card_congr e.toEquiv, card_PSL2_ZMod' N hN]

theorem card_BG_pmGammaR_le_two' (N : ℕ) [NeZero N] (hN : N ≤ 2) :
    (Nat.card (BG (pmGammaR N)) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  obtain ⟨e, -⟩ := BG_pmGammaR_equiv' N
  have hbot : pmOneSL N = ⊥ := by
    rw [pmOneSL, Subgroup.zpowers_eq_bot]
    have hN0 := NeZero.ne N
    have h1 : (-1 : ZMod N) = 1 := by
      have : 1 ≤ N := Nat.pos_of_ne_zero hN0
      interval_cases N
      · exact Subsingleton.elim _ _
      · decide
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, h1]
    · rw [Matrix.one_apply_ne hij, neg_zero]
  have : Nat.card (BG (pmGammaR N)) = Nat.card SL(2, ZMod N) := by
    rw [Nat.card_congr e.toEquiv, hbot]
    exact Subgroup.index_bot
  rw [this, card_SL2_ZMod']

theorem card_BG_pmGammaR_seven' : Nat.card (BG (pmGammaR 7)) = 168 := by
  have h := card_BG_pmGammaR' 7 (by norm_num)
  rw [Nat.Prime.primeFactors (by norm_num)] at h
  norm_num at h
  exact_mod_cast h

/-! ### X_Δ(M²) ≅ X(M) -/

/-- Conjugate subgroups have quotients by their normalizers of the same order. -/
theorem card_BG_map_conj (Γ : Subgroup SL(2, ℝ)) (D : SL(2, ℝ)) :
    Nat.card (BG (Γ.map (MulAut.conj D).toMonoidHom)) = Nat.card (BG Γ) := by
  show (Γ.map (MulAut.conj D).toMonoidHom).relIndex
      (Subgroup.normalizer ((Γ.map (MulAut.conj D).toMonoidHom : Subgroup SL(2, ℝ)) : Set SL(2, ℝ))) =
    Γ.relIndex (Subgroup.normalizer (Γ : Set SL(2, ℝ)))
  rw [← Subgroup.map_equiv_normalizer_eq Γ (MulAut.conj D)]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj D).injective

theorem card_BG_GammaDeltaR_sq' (M : ℕ) (hM : 3 ≤ M) :
    (Nat.card (BG (GammaDeltaR (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)))) : ℚ) =
      M ^ 3 / 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have : NeZero M := ⟨by omega⟩
  rw [← card_BG_map_conj _ (projSL !![(M : ℝ), 0; 0, 1]), conj_GammaDelta_sq' M (by omega),
    card_BG_pmGammaR' M hM]

theorem card_BG_GammaDeltaR_49' :
    Nat.card (BG (GammaDeltaR 49 (deltaPm 49 7 (by norm_num)))) = 168 := by
  have h := card_BG_GammaDeltaR_sq' 7 (by norm_num)
  rw [Nat.Prime.primeFactors (by norm_num)] at h
  norm_num at h
  exact_mod_cast h

end

end NormalizerLean
