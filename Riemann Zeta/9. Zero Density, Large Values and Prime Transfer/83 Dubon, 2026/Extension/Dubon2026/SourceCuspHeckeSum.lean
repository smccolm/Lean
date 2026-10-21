import Dubon2026.SourceCuspHeckeOrbitSum

/-! DUB-17/18 -> residual Galois association -> boundary eigenvalues of
original complex weight-two H1 -> the complete original Hecke cusp sum.
The proved orbit lengths and exact integral conjugates identify all terms;
the actual index ell+1 proves the remaining orbit has multiplicity one.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem colRed_fst {N : ℕ} (δ : SL(2, ℤ)) :
    (colRed N δ).1 = ((δ 0 0 : ℤ) : ZMod N) := rfl
private theorem colRed_snd {N : ℕ} (δ : SL(2, ℤ)) :
    (colRed N δ).2 = ((δ 1 0 : ℤ) : ZMod N) := rfl

/-- The actual lower diagonal unit of an original Gamma0 element. -/
def diagonalUnit {N : ℕ} (r : Gamma0 N) : (ZMod N)ˣ := by
  have hd : ((r.val 0 0 : ℤ) : ZMod N) * ((r.val 1 1 : ℤ) : ZMod N) = 1 := by
    have ht : r.val 0 0 * r.val 1 1 - r.val 0 1 * r.val 1 0 = 1 := by
      have he := r.val.det_coe
      rwa [Matrix.det_fin_two] at he
    have he := congrArg (fun z : ℤ => (z : ZMod N)) ht
    push_cast at he
    simpa only [Gamma0_mem.mp r.property, mul_zero, sub_zero] using he
  exact ⟨((r.val 1 1 : ℤ) : ZMod N), ((r.val 0 0 : ℤ) : ZMod N),
    by rwa [mul_comm], hd⟩

/-- The actual good prime as a unit modulo the original level. -/
def ellUnit {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : (ZMod N)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)

/-- The prime unit has the literal prime residue. -/
@[scoped simp] theorem coe_ellUnit {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    ((ellUnit hℓ hℓN : (ZMod N)ˣ) : ZMod N) = ℓ := ZMod.coe_unitOfCoprime _ _

/-- The inverse prime unit cancels the original prime residue. -/
theorem ellUnit_inv_mul {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (((ellUnit hℓ hℓN)⁻¹ : (ZMod N)ˣ) : ZMod N) * (ℓ : ZMod N) = 1 := by
  rw [← coe_ellUnit hℓ hℓN, Units.inv_mul]

/-- Multiplication by an original good prime is cancellable modulo the level. -/
theorem mul_ell_cancel {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {x y : ZMod N}
    (h : x * (ℓ : ZMod N) = y * ℓ) : x = y := by
  have hu : IsUnit (ℓ : ZMod N) := by rw [← coe_ellUnit hℓ hℓN]; exact Units.isUnit _
  exact (IsUnit.mul_left_inj hu).mp h

variable {N ℓ : ℕ} [NeZero N] [NeZero ℓ] {A : Type} [AddCommGroup A]
variable (δ : SL(2, ℤ)) (hℓ : ℓ.Prime) (hδ : (ℓ : ℤ) ∣ δ 0 0) (hℓN : ¬ℓ ∣ N)

private local instance upperIndex : (heckeUpperSubgroup N ℓ).FiniteIndex :=
  sourceHeckeUpper_finiteIndex
private local instance upperFinite : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :=
  sourceHeckeUpperFintype N ℓ

include hℓ hδ hℓN in

/-- The full original cusp Hecke sum has exactly the two required cusp values and multiplicities. -/
theorem hecke_sum_uOf (φ : Additive (Gamma0 N) →+ A) (σ₁ σ₂ : SL(2, ℤ))
    (hσ₂ : ((σ₂ 0 0 : ℤ) : ZMod N) * ℓ = δ 0 0 ∧ ((σ₂ 1 0 : ℤ) : ZMod N) = δ 1 0)
    (hσ₁ : ((σ₁ 0 0 : ℤ) : ZMod N) = δ 0 0 ∧ ((σ₁ 1 0 : ℤ) : ZMod N) = ℓ * δ 1 0) :
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ,
      φ (Additive.ofMul (sourceHeckeConjugation hℓ
        (cosetTransition (heckeUpperSubgroup N ℓ) (uOf N δ) q)))) = ℓ • B φ σ₂ + B φ σ₁ := by
  classical
  set u := uOf N δ with hudef
  letI : Fintype (OrbQ N ℓ u) := Fintype.ofFinite _
  have huK : u ∈ heckeUpperSubgroup N ℓ := uOf_mem_upper δ hδ
  have hper : ∀ O : OrbQ N ℓ u, O ≠ orbOne N ℓ u →
      Function.minimalPeriod (u • ·) O.out = ℓ := by
    intro O hO
    have hr : O.out.out ∉ heckeUpperSubgroup N ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have := minimalPeriod_eq δ hℓ hδ hℓN O.out.out hr
    rwa [QuotientGroup.out_eq'] at this

  have hterm : ∀ O : OrbQ N ℓ u, O ≠ orbOne N ℓ u →
      termOf hℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
        (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) = B φ σ₁ := by
    intro O hO
    have hr : O.out.out ∉ heckeUpperSubgroup N ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have hmem : O.out.out⁻¹ * u ^ ℓ * O.out.out ∈ heckeUpperSubgroup N ℓ := by
      have := QuotientGroup.out_conj_pow_minimalPeriod_mem (heckeUpperSubgroup N ℓ) u O.out
      rwa [hper O hO] at this
    rw [termOf_congr hℓ φ _ hmem (by rw [hper O hO])]
    obtain ⟨σ, hσ0, hσ1, hval⟩ := termOf_other hℓ δ hδ φ O.out.out hr hmem
    rw [hval]

    set r : Gamma0 N := O.out.out with hrdef
    have hr0 : r.val ∈ Gamma0 N := r.property
    have hr10 : (((r : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hr0
    refine B_eq_of_borel φ (diagonalUnit r)⁻¹
      (-(((r : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) * (((ellUnit hℓ hℓN)⁻¹ : (ZMod N)ˣ) : ZMod N)) ?_ ?_
    · rw [inv_inv, colRed_fst, colRed_fst, colRed_snd, hσ0, hσ₁.1, hσ₁.2, pOf_eq]
      have e1 : ((diagonalUnit r : (ZMod N)ˣ) : ZMod N) = (((r : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) := rfl
      rw [e1]
      push_cast
      linear_combination ((((r : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) * (((δ 1 0 : ℤ)) : ZMod N)) *
        ellUnit_inv_mul hℓ hℓN
    · rw [colRed_snd, colRed_snd, hσ1, hσ₁.2, qOf_eq]
      have e2 : (((diagonalUnit r)⁻¹ : (ZMod N)ˣ) : ZMod N) = (((r : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) := rfl
      rw [e2]
      push_cast
      rw [hr10]
      ring

  have hone : termOf hℓ φ ((orbOne N ℓ u).out.out⁻¹ *
      u ^ Function.minimalPeriod (u • ·) (orbOne N ℓ u).out * (orbOne N ℓ u).out.out)
      (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u _) = ℓ • B φ σ₂ := by
    have hr := orbOne_out_out_mem u huK
    have hmem : (orbOne N ℓ u).out.out⁻¹ * u * (orbOne N ℓ u).out.out ∈ heckeUpperSubgroup N ℓ :=
      mul_mem (mul_mem (inv_mem hr) huK) hr
    rw [termOf_congr hℓ φ _ hmem (by rw [minimalPeriod_orbOne_out u huK, pow_one]),
      termOf_conj hℓ φ huK hr hmem]
    obtain ⟨σ, hσ0, hσ1, hval⟩ := termOf_u hℓ δ hδ φ
    rw [hval]
    congr 1
    apply B_congr
    apply Prod.ext
    · rw [colRed_fst, colRed_fst]
      apply mul_ell_cancel hℓ hℓN
      rw [hσ₂.1]
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod N)) hσ0
    · rw [colRed_snd, colRed_snd, hσ1, hσ₂.2]
  have hidx : ℓ + 1 = ∑ O : OrbQ N ℓ u, Function.minimalPeriod (u • ·) O.out := by
    have hi : (heckeUpperSubgroup N ℓ).index = ℓ + 1 := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card,
        ← Fintype.card_congr (heckeUpperCosetEquiv hℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)),
        Fintype.card_option, ZMod.card]
    rw [← hi]
    exact Subgroup.index_eq_sum_minimalPeriod _ u
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (orbOne N ℓ u)),
    minimalPeriod_orbOne_out u huK, Finset.sum_congr rfl (fun O hO => hper O (by simpa using hO)),
    Finset.sum_const, smul_eq_mul, add_comm, Nat.add_left_cancel_iff, eq_comm,
    mul_eq_right₀ hℓ.ne_zero] at hidx
  rw [hecke_sum_eq_sum_orbits]
  let F : OrbQ N ℓ u → A := fun O =>
    termOf hℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
      (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out)
  change (∑ O : OrbQ N ℓ u, F O) = _
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ (orbOne N ℓ u)),
    show F (orbOne N ℓ u) = ℓ • B φ σ₂ from hone,
    Finset.sum_congr rfl (fun O hO => hterm O (by simpa using hO)), Finset.sum_const, hidx,
    one_smul]


end
end Dubon2026.SourceCuspBoundary
