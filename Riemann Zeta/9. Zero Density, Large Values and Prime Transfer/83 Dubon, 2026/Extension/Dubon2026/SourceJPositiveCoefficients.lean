import Dubon2026.SourceJProductTruncation

/-! DUB-17/18 -> matching modular dimension -> numerical modular genus ->
exact j-map degree -> prime nonmembership. Nonzero positive coefficients
of the actual j series rule out a polynomial identity j(q^p)=P(j(q))
through the root-of-unity orbit sum. This proof uses the literal integral
Eisenstein and eta series already in the original function field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean. Only the coefficient
positivity chain is selected; no external proof options are imported.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
open scoped PowerSeries.WithPiTopology
open PowerSeries Finset

/-- The integral geometric series in the d-th power of the formal variable. -/
def geomSeries (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if d ∣ k then 1 else 0

@[simp]
theorem coeff_geomSeries (d k : ℕ) :
    PowerSeries.coeff k (geomSeries d) = if d ∣ k then 1 else 0 := by
  rw [geomSeries, PowerSeries.coeff_mk]

@[simp]
theorem constantCoeff_geomSeries (d : ℕ) :
    PowerSeries.constantCoeff (geomSeries d) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_geomSeries, if_pos (dvd_zero d)]

theorem coeff_geomSeries_nonneg (d k : ℕ) :
    0 ≤ PowerSeries.coeff k (geomSeries d) := by
  rw [coeff_geomSeries]
  split <;> norm_num

theorem coeff_geomSeries_one (k : ℕ) :
    PowerSeries.coeff k (geomSeries 1) = 1 := by
  rw [coeff_geomSeries, if_pos (one_dvd k)]

theorem one_sub_X_pow_mul_geomSeries {d : ℕ} (hd : d ≠ 0) :
    ((1 : PowerSeries ℤ) - X ^ d) * geomSeries d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, ← mul_comm (geomSeries d) (X ^ d),
    PowerSeries.coeff_mul_X_pow', coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hdn : d ≤ n
  ·
    have hn0 : ¬ (n = 0) := by omega
    rw [if_pos hdn, coeff_geomSeries, if_neg hn0]
    have hiff : d ∣ n ↔ d ∣ n - d := by
      constructor
      · intro h; exact Nat.dvd_sub h dvd_rfl
      · intro h
        have := Nat.dvd_add h (dvd_refl d)
        rwa [Nat.sub_add_cancel hdn] at this
    by_cases h : d ∣ n
    · rw [if_pos h, if_pos (hiff.mp h), sub_self]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), sub_self]
  ·
    rw [if_neg hdn, sub_zero]
    by_cases hn : n = 0
    · subst hn; rw [if_pos (dvd_zero d), if_pos rfl]
    · rw [if_neg hn, if_neg (fun hc => hdn (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hc))]

theorem coeff_mul_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hg : ∀ k, 0 ≤ PowerSeries.coeff k g) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀ i ∈ s, ∀ k, 0 ≤ PowerSeries.coeff k (f i)) :
    ∀ n, 0 ≤ PowerSeries.coeff n (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    split <;> norm_num
  | @insert a s ha ih =>
    intro n
    rw [Finset.prod_insert ha]
    exact coeff_mul_nonneg (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) n

theorem coeff_pow_nonneg {f : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 0 ≤ PowerSeries.coeff n (f ^ m) := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> norm_num
  | succ m ih =>
    intro n
    rw [pow_succ]
    exact coeff_mul_nonneg ih hf n

theorem one_le_coeff_mul_of_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hf0 : PowerSeries.constantCoeff f = 1)
    (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  have hterm : (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, one_mul]
    exact hg n
  calc (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := hterm
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (hf p.1) (le_trans zero_le_one (hg p.2))) hmem

theorem one_le_coeff_mul {f g : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  calc (1 : ℤ) = 1 * 1 := (one_mul 1).symm
    _ ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g :=
        mul_le_mul (hf 0) (hg n) zero_le_one (le_trans zero_le_one (hf 0))
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (le_trans zero_le_one (hf p.1))
            (le_trans zero_le_one (hg p.2))) hmem

theorem one_le_coeff_pow {f : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 1 ≤ PowerSeries.coeff n (f ^ (m + 1)) := by
  induction m with
  | zero => intro n; simpa using hf n
  | succ m ih => intro n; rw [pow_succ]; exact one_le_coeff_mul ih hf n

theorem coeff_mul_congr {A C g : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k (A * g) = PowerSeries.coeff k (C * g) := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : p.1 ≤ k := Finset.antidiagonal.fst_le hp
  rw [h p.1 (le_trans h1 hk)]

theorem coeff_pow_congr {A C : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) (m : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k (A ^ m) = PowerSeries.coeff k (C ^ m) := by
  induction m with
  | zero => intro k _; rfl
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h1 : p.1 ≤ k := Finset.antidiagonal.fst_le hp
    have h2 : p.2 ≤ k := Finset.antidiagonal.snd_le hp
    rw [ih p.1 (le_trans h1 hk), h p.2 (le_trans h2 hk)]

theorem coeff_inv_congr {A B C D : PowerSeries ℤ}
    (hAB : A * B = 1) (hCD : C * D = 1) {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k B = PowerSeries.coeff k D := by
  intro k hk

  have hCB : ∀ m ≤ n, PowerSeries.coeff m (C * B) =
      PowerSeries.coeff m (1 : PowerSeries ℤ) := by
    intro m hm
    rw [← hAB]
    exact (coeff_mul_congr (fun k hk => (h k hk).symm) m hm)

  have key : B = D * (C * B) := by
    rw [← mul_assoc, mul_comm D C, hCD, one_mul]
  rw [key, PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single_of_mem (k, 0) (by simp)]
  · rw [hCB 0 (Nat.zero_le n), PowerSeries.coeff_one, if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ k := Finset.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [hCB b₂ (le_trans hb₂ hk), PowerSeries.coeff_one, if_neg h2, mul_zero]

/-- The first N factors of the original eta product. -/
abbrev partialEta (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, ((1 : PowerSeries ℤ) - X ^ (i + 1))

/-- The product of the corresponding first N geometric inverses. -/
abbrev partialGeom (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, geomSeries (i + 1)

theorem partialEta_mul_partialGeom (N : ℕ) :
    partialEta N * partialGeom N = 1 := by
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl
    (fun i _ => one_sub_X_pow_mul_geomSeries (Nat.succ_ne_zero i))]
  exact Finset.prod_const_one

theorem coeff_etaProd_eq_coeff_partialEta {k n : ℕ} (hk : k ≤ n) :
    PowerSeries.coeff k etaProd = PowerSeries.coeff k (partialEta (n + 1)) := by
  rw [coeff_etaProd_eq_coeff_partialProd k]
  exact (coeff_prod_one_sub_pow_le n k hk).symm

theorem coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow (n : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnitInv =
      PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hunits : ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnit =
      PowerSeries.coeff k (partialEta (n + 1) ^ 24) := by
    intro k hk
    rw [dedekindEtaUnit]
    exact coeff_pow_congr (fun k hk => coeff_etaProd_eq_coeff_partialEta hk) 24 k hk

  have hinv : partialEta (n + 1) ^ 24 * partialGeom (n + 1) ^ 24 = 1 := by
    rw [← mul_pow, partialEta_mul_partialGeom, one_pow]
  exact coeff_inv_congr dedekindEtaUnit_mul_inv hinv hunits

theorem one_le_coeff_partialGeom_pow (n k : ℕ) :
    1 ≤ PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hsplit : partialGeom (n + 1) =
      (∏ i ∈ Finset.range n, geomSeries (i + 2)) * geomSeries 1 :=
    Finset.prod_range_succ' (fun i => geomSeries (i + 1)) n
  rw [hsplit, mul_pow]

  have htail_nonneg : ∀ j, 0 ≤ PowerSeries.coeff j
      ((∏ i ∈ Finset.range n, geomSeries (i + 2)) ^ 24) :=
    coeff_pow_nonneg
      (coeff_prod_nonneg _ _ (fun i _ k => coeff_geomSeries_nonneg (i + 2) k)) 24
  have htail_cc : PowerSeries.constantCoeff
      ((∏ i ∈ Finset.range n, geomSeries (i + 2)) ^ 24) = 1 := by
    rw [map_pow, map_prod]
    simp only [constantCoeff_geomSeries, Finset.prod_const_one, one_pow]

  have hhead : ∀ j, 1 ≤ PowerSeries.coeff j (geomSeries 1 ^ 24) :=
    one_le_coeff_pow (fun j => le_of_eq (coeff_geomSeries_one j).symm) 23
  exact one_le_coeff_mul_of_nonneg htail_nonneg htail_cc hhead k

theorem one_le_coeff_dedekindEtaUnitInv (n : ℕ) :
    1 ≤ PowerSeries.coeff n dedekindEtaUnitInv := by
  rw [coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow n n le_rfl]
  exact one_le_coeff_partialGeom_pow n n

theorem coeff_eisenstein4_nonneg (n : ℕ) :
    0 ≤ PowerSeries.coeff n eisenstein4 := by
  rw [eisenstein4, PowerSeries.coeff_mk]
  split
  · norm_num
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
    exact pow_nonneg (Int.natCast_nonneg d) 3

theorem one_le_coeff_jNum (n : ℕ) : 1 ≤ PowerSeries.coeff n jNum := by
  rw [jNum]
  exact one_le_coeff_mul_of_nonneg (coeff_pow_nonneg coeff_eisenstein4_nonneg 3)
    (by rw [map_pow, constantCoeff_eisenstein4, one_pow])
    one_le_coeff_dedekindEtaUnitInv n

theorem one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) := by
  have h : ((n : ℤ)) = ((n + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [h, coeff_jq_eq_coeff_jNum]
  exact_mod_cast one_le_coeff_jNum (n + 1)

theorem coeff_jq_ne_zero (n : ℕ) : jq.coeff (n : ℤ) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_coeff_jq n))

end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
