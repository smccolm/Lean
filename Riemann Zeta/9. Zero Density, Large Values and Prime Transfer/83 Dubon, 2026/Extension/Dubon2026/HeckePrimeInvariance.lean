/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

The finite permutation assembly adapts HeckeT_p.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198,
specialized directly to Gamma0 and extended to primes dividing the level.
-/
import Dubon2026.HeckePrimeOrbits
import Dubon2026.HeckeCuspBehavior

/-! # Slash invariance of the actual classical prime Hecke operator -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset HeckePrimeReindex
open scoped MatrixGroups ModularForm

noncomputable section

/-- The literal classical prime operator consists of its p upper terms and the good diagonal term. -/
theorem classicalHeckeFunction_prime (Q : ℕ) (k : ℤ) {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (f : ℍ → ℂ) :
    classicalHeckeFunction Q k p f = heckeTriangularSum 1 p k f +
      if Nat.Coprime p Q then f ∣[k] heckeTriangularMatrix p 1 0 else 0 := by
  let e1 : {d // d ∈ p.divisors} := ⟨1, Nat.one_mem_divisors.mpr hp.ne_zero⟩
  let ep : {d // d ∈ p.divisors} := ⟨p, Nat.mem_divisors_self p hp.ne_zero⟩
  have hs : p.divisors.attach = {e1, ep} := by
    ext d
    simp only [Finset.mem_attach, true_iff, Finset.mem_insert, Finset.mem_singleton]
    have hd : d.val = 1 ∨ d.val = p := by simpa [hp.divisors] using d.property
    exact hd.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h))
  have hne : e1 ≠ ep := fun h => hp.ne_one (congrArg Subtype.val h).symm
  funext τ
  rw [classicalHeckeFunction, hs, Finset.sum_pair hne]
  change classicalHeckeTerm Q k p 1 e1.property f τ +
    classicalHeckeTerm Q k p p ep.property f τ = _
  have h1 : classicalHeckeTerm Q k p 1 e1.property f τ = heckeTriangularSum 1 p k f τ := by
    rw [heckeTriangularSum_apply]
    simp [classicalHeckeTerm]
  have hpterm : classicalHeckeTerm Q k p p ep.property f τ =
      (if Nat.Coprime p Q then f ∣[k] heckeTriangularMatrix p 1 0 else 0) τ := by
    by_cases hc : Nat.Coprime p Q
    · simp only [if_pos hc, heckeTriangular_slash_apply]
      dsimp only [classicalHeckeTerm]
      rw [if_pos hc]
      simp [Nat.div_self hp.pos, heckeAverage, heckeUpperPoint]
    · simp [classicalHeckeTerm, hc]
  rw [h1, hpterm]
  rfl

/-- Factoring a representative by an actual Gamma0 element preserves its slash translate. -/
theorem cusp_slash_factor {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    {A B : GL (Fin 2) ℝ} (σ : SL(2, ℤ))
    (h : ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧ A * mapGL ℝ σ = mapGL ℝ δ * B) :
    (⇑f ∣[k] A) ∣[k] mapGL ℝ σ = ⇑f ∣[k] B := by
  obtain ⟨δ, hδ, he⟩ := h
  have hf : (⇑f ∣[k] mapGL ℝ δ) = (⇑f : ℍ → ℂ) :=
    f.slash_action_eq' _ (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)
  rw [← SlashAction.slash_mul, he, SlashAction.slash_mul, hf]

/-- When the lower-left entry is divisible by p, the upper Hecke terms permute among themselves. -/
theorem heckeTriangularSum_slash_of_lower_dvd {Q p : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : (p : ℤ) ∣ σ.val 1 0) :
    heckeTriangularSum 1 p k f ∣[k] mapGL ℝ σ = heckeTriangularSum 1 p k f := by
  unfold heckeTriangularSum
  rw [SlashAction.sum_slash, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_equiv (Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp σ.val σ.prop)))
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) ?_
  intro b _
  exact cusp_slash_factor f σ (heckePrime_upper_factor hp σ hσ b
    (not_dvd_topLeft_add_of_dvd_botLeft p hp σ.val (sl2z_fin_two_det_eq_one σ) hC b.val))

/-- At a good prime and a nonzero lower-left residue, the pole exchanges with the diagonal term. -/
theorem heckePrime_good_slash_of_lower_not_dvd {Q p : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : ¬(p : ℤ) ∣ σ.val 1 0) :
    (heckeTriangularSum 1 p k f + (⇑f ∣[k] heckeTriangularMatrix p 1 0)) ∣[k] mapGL ℝ σ =
      heckeTriangularSum 1 p k f + (⇑f ∣[k] heckeTriangularMatrix p 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let b₀ : Fin p := ⟨(-(σ.val 0 0 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀ : (p : ℤ) ∣ σ.val 0 0 + b₀.val * σ.val 1 0 :=
    dvd_topLeft_add_canonicalIndex p hp σ.val
      (fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  have hupper (b : Fin p) :
      (⇑f ∣[k] heckeTriangularMatrix 1 p b.val) ∣[k] mapGL ℝ σ =
      if (p : ℤ) ∣ σ.val 0 0 + b.val * σ.val 1 0 then
        ⇑f ∣[k] heckeTriangularMatrix p 1 0 else
        ⇑f ∣[k] heckeTriangularMatrix 1 p (moebiusFin p hp σ.val b).val := by
    split_ifs with h
    · exact cusp_slash_factor f σ (heckePrime_upper_pole_factor σ hσ b h)
    · exact cusp_slash_factor f σ (heckePrime_upper_factor hp σ hσ b h)
  have hlower : (⇑f ∣[k] heckeTriangularMatrix p 1 0) ∣[k] mapGL ℝ σ =
      ⇑f ∣[k] heckeTriangularMatrix 1 p (moebiusFin p hp σ.val b₀).val := by
    have hm : (moebiusFin p hp σ.val b₀).val =
        ((σ.val 1 1 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val := by
      simp only [moebiusFin, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, if_true]
    rw [hm]
    exact cusp_slash_factor f σ (heckePrime_lower_factor hp σ hσ hC)
  rw [SlashAction.add_slash, heckeTriangularSum, SlashAction.sum_slash,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp_rw [hupper]
  rw [hlower]
  exact sum_ite_swap_eq (fun b : Fin p => ⇑f ∣[k] heckeTriangularMatrix 1 p b.val)
    (⇑f ∣[k] heckeTriangularMatrix p 1 0) (moebiusFin p hp σ.val)
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp σ.val σ.prop)) b₀ _
    (dvd_topLeft_add_iff_eq_canonicalIndex p hp σ.val σ.prop b₀ hb₀)

/-- The literal prime Hecke function is slash invariant at the original Gamma0 level,
including primes dividing the level. -/
theorem classicalHeckeFunction_prime_slash {Q p : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma0 Q).map (mapGL ℝ)) :
    classicalHeckeFunction Q k p f ∣[k] γ = classicalHeckeFunction Q k p f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [classicalHeckeFunction_prime Q k hp]
  by_cases hpQ : Nat.Coprime p Q
  · rw [if_pos hpQ]
    by_cases hC : (p : ℤ) ∣ σ.val 1 0
    · rw [SlashAction.add_slash, heckeTriangularSum_slash_of_lower_dvd hp f σ hσ hC,
        cusp_slash_factor f σ (heckePrime_lower_div_factor hpQ σ hσ hC)]
    · exact heckePrime_good_slash_of_lower_not_dvd hp f σ hσ hC
  · rw [if_neg hpQ, add_zero]
    have hpQdvd : p ∣ Q := by
      by_contra h
      exact hpQ (hp.coprime_iff_not_dvd.mpr h)
    have hC : (p : ℤ) ∣ σ.val 1 0 := dvd_trans
      (Int.natCast_dvd_natCast.mpr hpQdvd)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hσ))
    exact heckeTriangularSum_slash_of_lower_dvd hp f σ hσ hC

/-- The actual classical prime Hecke operator as a cusp form at the same positive level. -/
def cuspHeckePrime {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k where
  toFun := classicalHeckeFunction Q k p f
  slash_action_eq' := classicalHeckeFunction_prime_slash hp f
  holo' := classicalHeckeFunction_holomorphic Q k p f f.holo'
  zero_at_cusps' := classicalHeckeFunction_zero_at_cusps Q k p f

end
end Dubon2026
