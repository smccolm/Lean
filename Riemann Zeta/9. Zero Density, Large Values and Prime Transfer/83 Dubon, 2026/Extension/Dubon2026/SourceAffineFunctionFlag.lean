import Dubon2026.SourceAffineFunctionRepresentation
import Dubon2026.SourceFiniteFunctionFlag

/-! The actual affine function flag and its exact group and Hecke characters.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> native H1 lifting through this computed character quotient.
The triangular calculations are adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE), using the original native Rep
and the proved interpolation basis.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)

/-- The original affine action has the exact triangular binomial expansion. -/
theorem sourceAffineFunction_monomial (γ : Gamma0 Q) (n : ℕ) :
    (sourceAffineFunctionRep p Q F hpQ).ρ γ (sourceFiniteFunctionMonomial F p n)
      = ∑ m ∈ Finset.range (n + 1),
          ((ZMod.castHom (dvd_refl p) F (sourceAffineD p Q γ)) ^ (2 * m) * (ZMod.castHom (dvd_refl p) F (-(sourceAffineD p Q γ * sourceAffineB p Q γ))) ^ (n - m) * (n.choose m : F))
            • sourceFiniteFunctionMonomial F p m := by
  have h : (sourceAffineFunctionRep p Q F hpQ).ρ γ (sourceFiniteFunctionMonomial F p n)
      = fun u : ZMod p => (ZMod.castHom (dvd_refl p) F (sourceAffineD p Q γ) ^ 2 * ZMod.castHom (dvd_refl p) F u + ZMod.castHom (dvd_refl p) F (-(sourceAffineD p Q γ * sourceAffineB p Q γ))) ^ n := by
    funext u
    rw [sourceAffineFunctionRep_apply, sourceFiniteFunctionMonomial]
    congr 1
    simp only [map_mul, map_sub, map_neg]
    ring
  rw [h, sourceFiniteFunction_affine_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← pow_mul]

/-- The original Hecke coefficient action is diagonal on prime-field monomials. -/
theorem sourceAffineFunctionDiagonal_monomial (ℓ n : ℕ) : sourceAffineFunctionDiagonal p F ℓ (sourceFiniteFunctionMonomial F p n) = (ZMod.castHom (dvd_refl p) F ((ℓ : ZMod p)⁻¹)) ^ n • sourceFiniteFunctionMonomial F p n := by
  funext u
  simp only [sourceAffineFunctionDiagonal_apply, sourceFiniteFunctionMonomial, Pi.smul_apply, smul_eq_mul, map_mul, mul_pow]

/-- The actual congruence-group action preserves each required function flag. -/
theorem sourceAffineFunction_flag_stable {k : ℕ} (hkp : k < p) (γ : Gamma0 Q) {f : ZMod p → F} (hf : f ∈ sourceFiniteFunctionFlag F p k) :
    (sourceAffineFunctionRep p Q F hpQ).ρ γ f ∈ sourceFiniteFunctionFlag F p k := by
  change sourceAffineFunctionAction p Q F γ f ∈ sourceFiniteFunctionFlag F p k
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [sourceFiniteFunctionBasis_apply]
    have ha := sourceAffineFunction_monomial F p Q hpQ γ i.val
    change sourceAffineFunctionAction p Q F γ _ = _ at ha
    rw [ha]
    exact sourceFiniteFunction_sum_mem_flag F p hi hkp _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The original Hecke coefficient maps preserve the actual finite-function flag. -/
theorem sourceAffineFunctionDiagonal_flag_stable {k : ℕ} (ℓ : ℕ) {f : ZMod p → F} (hf : f ∈ sourceFiniteFunctionFlag F p k) : sourceAffineFunctionDiagonal p F ℓ f ∈ sourceFiniteFunctionFlag F p k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [sourceFiniteFunctionBasis_apply, sourceAffineFunctionDiagonal_monomial]
    exact Submodule.smul_mem _ _ (sourceFiniteFunctionMonomial_mem_flag F p hi i.2)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The actual leading-coordinate character is the lower diagonal to twice the degree. -/
theorem sourceAffineFunctionCoordinate_action (k : Fin p) (γ : Gamma0 Q) {f : ZMod p → F} (hf : f ∈ sourceFiniteFunctionFlag F p k.val) :
    sourceFiniteFunctionCoordinate F p k ((sourceAffineFunctionRep p Q F hpQ).ρ γ f) = (ZMod.castHom (dvd_refl p) F (sourceAffineD p Q γ)) ^ (2 * k.val) * sourceFiniteFunctionCoordinate F p k f := by
  change sourceFiniteFunctionCoordinate F p k (sourceAffineFunctionAction p Q F γ f) = _
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [sourceFiniteFunctionBasis_apply]
    have ha := sourceAffineFunction_monomial F p Q hpQ γ i.val
    change sourceAffineFunctionAction p Q F γ _ = _ at ha
    rw [ha, sourceFiniteFunctionCoordinate_sum F p k hi,
      sourceFiniteFunctionCoordinate_monomial F p k i.2]
    by_cases h : i.val = k.val
    · rw [if_pos h, if_pos h, h, Nat.sub_self, pow_zero, Nat.choose_self]; simp
    · rw [if_neg h, if_neg h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- The actual leading Hecke coordinate scales by the inverse prime to the degree. -/
theorem sourceAffineFunctionCoordinate_diagonal (k : Fin p) (ℓ : ℕ) {f : ZMod p → F} (hf : f ∈ sourceFiniteFunctionFlag F p k.val) :
    sourceFiniteFunctionCoordinate F p k (sourceAffineFunctionDiagonal p F ℓ f) = (ZMod.castHom (dvd_refl p) F ((ℓ : ZMod p)⁻¹)) ^ k.val * sourceFiniteFunctionCoordinate F p k f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [sourceFiniteFunctionBasis_apply, sourceAffineFunctionDiagonal_monomial, map_smul, sourceFiniteFunctionCoordinate_monomial F p k i.2, smul_eq_mul]
    by_cases h : i.val = k.val
    · rw [if_pos h, h]
    · rw [if_neg h, mul_zero, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

end
end Dubon2026
