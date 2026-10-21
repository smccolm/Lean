import Dubon2026.SourceFiniteFunctionFlag

/-! Translation controls the only possible invariant above the original function flag.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> survival in the whole function representation or its exact
Eisenstein exception -> the invariant quotient has at most the next monomial.
The maximal-coordinate argument is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). It uses the actual interpolation
basis and the original translation; no quotient dimension is assumed.
-/

namespace Dubon2026
noncomputable section
variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Translation by one on the actual prime-field function space. -/
def sourceFiniteFunctionShift : Module.End F (ZMod p → F) where
  toFun f u := f (u + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original translation has the exact binomial expansion on each monomial. -/
theorem sourceFiniteFunctionShift_monomial (n : ℕ) :
    sourceFiniteFunctionShift F p (sourceFiniteFunctionMonomial F p n) =
      ∑ m ∈ Finset.range (n + 1), (n.choose m : F) • sourceFiniteFunctionMonomial F p m := by
  have h : sourceFiniteFunctionShift F p (sourceFiniteFunctionMonomial F p n) =
      fun u : ZMod p => (1 * ZMod.castHom (dvd_refl p) F u + 1) ^ n := by
    funext u
    simp [sourceFiniteFunctionShift, sourceFiniteFunctionMonomial]
  rw [h, sourceFiniteFunction_affine_pow]
  simp

/-- If the actual first difference lies in the degree-k flag, the original
function differs from a scalar multiple of the next monomial by that flag. -/
theorem sourceFiniteFunctionDifference_degree {k : ℕ} (hk : k + 1 < p) {f : ZMod p → F}
    (hf : sourceFiniteFunctionShift F p f - f ∈ sourceFiniteFunctionFlag F p k) :
    ∃ r : F, f - r • sourceFiniteFunctionMonomial F p (k + 1) ∈ sourceFiniteFunctionFlag F p k := by
  classical
  set B := sourceFiniteFunctionBasis F p with hB
  set r : Fin p → F := fun i => B.repr f i with hr
  have hfsum : f = ∑ i : Fin p, r i • B i := (B.sum_repr f).symm

  have hΔB : ∀ i : Fin p, sourceFiniteFunctionShift F p (B i) - B i
      = ∑ m ∈ Finset.range i.val, ((i.val.choose m : F)) • sourceFiniteFunctionMonomial F p m := by
    intro i
    rw [hB, sourceFiniteFunctionBasis_apply, sourceFiniteFunctionShift_monomial, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_smul,
      add_sub_cancel_right]
  have hcoordΔ : ∀ j : Fin p, sourceFiniteFunctionCoordinate F p j (sourceFiniteFunctionShift F p f - f)
      = ∑ i : Fin p, if j.val < i.val then r i * (i.val.choose j.val : F) else 0 := by
    intro j
    conv_lhs => rw [hfsum]
    rw [map_sum, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← smul_sub, map_smul, hΔB, smul_eq_mul, map_sum]
    simp only [map_smul, smul_eq_mul]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]
      have hval : ∀ m ∈ Finset.range i.val, (i.val.choose m : F) * sourceFiniteFunctionCoordinate F p j (sourceFiniteFunctionMonomial F p m)
          = if m = j.val then (i.val.choose m : F) else 0 := by
        intro m hm
        rw [sourceFiniteFunctionCoordinate_monomial F p j (lt_trans (Finset.mem_range.mp hm) i.2)]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hji)]
    · rw [if_neg hji]
      have hval : ∀ m ∈ Finset.range i.val, (i.val.choose m : F) * sourceFiniteFunctionCoordinate F p j (sourceFiniteFunctionMonomial F p m) = 0 := by
        intro m hm
        rw [sourceFiniteFunctionCoordinate_monomial F p j (lt_trans (Finset.mem_range.mp hm) i.2), if_neg, mul_zero]
        intro hmj
        exact hji (hmj ▸ Finset.mem_range.mp hm)
      rw [Finset.sum_congr rfl hval, Finset.sum_const_zero, mul_zero]

  have hvan : ∀ i : Fin p, k + 1 < i.val → r i = 0 := by
    by_contra hcon
    push Not at hcon
    set S : Finset (Fin p) := Finset.univ.filter fun i => k + 1 < i.val ∧ r i ≠ 0 with hS
    have hSne : S.Nonempty := by
      obtain ⟨i, hi, hri⟩ := hcon
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hri⟩⟩
    set i₁ := S.max' hSne with hi₁
    have hi₁S : i₁ ∈ S := Finset.max'_mem S hSne
    obtain ⟨-, hi₁k, hri₁⟩ := Finset.mem_filter.mp hi₁S
    have hmax : ∀ i : Fin p, i₁ < i → k + 1 < i.val → r i = 0 := by
      intro i hi hik
      by_contra hri
      have : i ≤ i₁ := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik, hri⟩)
      exact absurd hi (not_lt.mpr this)
    have hjp : i₁.val - 1 < p := lt_of_le_of_lt (Nat.sub_le _ _) i₁.2
    set j : Fin p := ⟨i₁.val - 1, hjp⟩ with hj
    have hjk : k < j.val := by change k < i₁.val - 1; omega
    have hzero : sourceFiniteFunctionCoordinate F p j (sourceFiniteFunctionShift F p f - f) = 0 := sourceFiniteFunctionCoordinate_zero F p hjk hf
    rw [hcoordΔ j, Finset.sum_eq_single i₁] at hzero
    · rw [if_pos (by change i₁.val - 1 < i₁.val; omega)] at hzero
      have hchoose : (i₁.val.choose j.val : F) = (i₁.val : F) := by
        have hn : i₁.val = j.val + 1 := by change i₁.val = (i₁.val - 1) + 1; omega
        rw [hn, Nat.choose_succ_self_right]
      rw [hchoose] at hzero
      rcases mul_eq_zero.mp hzero with h | h
      · exact hri₁ h
      · rw [CharP.cast_eq_zero_iff F p] at h
        have := Nat.le_of_dvd (by omega) h
        exact absurd this (not_le.mpr i₁.2)
    · intro i _ hne
      by_cases hlt : j.val < i.val
      · rw [if_pos hlt]
        change i₁.val - 1 < i.val at hlt
        have hne' : i.val ≠ i₁.val := fun h => hne (Fin.ext h)
        have hgt : i₁ < i := by rw [Fin.lt_def]; omega
        rw [hmax i hgt (by omega), zero_mul]
      · rw [if_neg hlt]
    · intro h; exact absurd (Finset.mem_univ i₁) h
  refine ⟨if h : k + 1 < p then r ⟨k + 1, h⟩ else 0, ?_⟩
  rw [dif_pos hk]
  rw [(sourceFiniteFunctionFlag_mem_iff F p)]
  intro i hi
  by_contra hik
  push Not at hik
  apply hi
  rw [map_sub, map_smul, ← sourceFiniteFunctionBasis_apply F p ⟨k + 1, hk⟩, B.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.single_apply]
  by_cases hieq : (⟨k + 1, hk⟩ : Fin p) = i
  · rw [if_pos hieq, smul_eq_mul, mul_one, ← hieq, sub_self]
  · rw [if_neg hieq, smul_zero, sub_zero]
    have hik' : k + 1 < i.val := lt_of_le_of_ne hik fun h => hieq (Fin.ext h)
    exact hvan i hik'

end
end Dubon2026
