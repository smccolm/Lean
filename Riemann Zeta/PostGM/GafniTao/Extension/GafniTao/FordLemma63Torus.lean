import GafniTao.FordLemma63Overlap

/-!
# Ford Lemma 6.3: periodic majorant and phase boxes

The polynomial majorant is intrinsically periodic.  This file records it on
the normalized unit torus, so that translated phase boxes can be counted
without choosing incompatible representatives in the real unit cube.
-/

open Finset Set MeasureTheory Metric
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Ford's Abel majorant, regarded as a function on the unit torus. -/
def fordLemma63SZeroTorus
    (k M : ℕ) (α : UnitAddTorus (Fin k)) : ℝ :=
  ‖fordVinogradovWeylSum k M α‖ +
    (2 / (M : ℝ)) *
      ∑ q ∈ Finset.range (M - 1),
        ‖fordVinogradovWeylSum k (q + 1) α‖

theorem fordLemma63SZero_eq_torus
    (k M : ℕ) (β : Fin k → ℝ) :
    fordLemma63SZero k M β =
      fordLemma63SZeroTorus k M (fun j => (β j : UnitAddCircle)) := by
  unfold fordLemma63SZero fordLemma63SZeroTail fordLemma63SZeroTorus
  rw [fordLemma63PolynomialSum_eq_vinogradovWeylSum]
  apply congrArg (fun x : ℝ => _ + (2 / (M : ℝ)) * x)
  apply Finset.sum_congr rfl
  intro q _hq
  rw [fordLemma63PolynomialSum_eq_vinogradovWeylSum]

theorem fordLemma63_integral_SZeroTorus_two_s_le
    {s k M : ℕ} (hs : 1 ≤ s) (hM : 1 ≤ M) :
    (∫ α : UnitAddTorus (Fin k),
      fordLemma63SZeroTorus k M α ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
        (2 : ℝ) ^ (4 * s) * (fordVinogradovMomentNat s k M : ℝ) := by
  have hpre := UnitAddTorus.integral_preimage
    (fun α : UnitAddTorus (Fin k) =>
      fordLemma63SZeroTorus k M α ^ (2 * s))
    (fun _ : Fin k => 0)
  change
    (∫ α : UnitAddTorus (Fin k),
      fordLemma63SZeroTorus k M α ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      ∫ β : Fin k → ℝ in
        {β | ∀ j : Fin k, β j ∈ Set.Ioc (0 : ℝ) (0 + 1)},
        fordLemma63SZeroTorus k M
          (fun j => (β j : UnitAddCircle)) ^ (2 * s) at hpre
  have heq :
      (∫ α : UnitAddTorus (Fin k),
        fordLemma63SZeroTorus k M α ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      ∫ β : Fin k → ℝ in fordUnitCube k,
        fordLemma63SZero k M β ^ (2 * s) := by
    simpa only [fordUnitCube, zero_add, fordLemma63SZero_eq_torus] using hpre
  rw [heq]
  exact fordLemma63_integral_SZero_two_s_le hs hM

/-- The product of Ford's coordinate balls on the unit torus. -/
def fordLemma63TorusOmega
    (k M n : ℕ) (u t : ℝ) : Set (UnitAddTorus (Fin k)) :=
  { α | ∀ j : Fin k, α j ∈ closedBall
      (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
      (fordLemma63Radius k M j) }

theorem fordLemma63TorusOmega_mem
    {k M n : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)} :
    α ∈ fordLemma63TorusOmega k M n u t ↔
      ∀ j : Fin k, α j ∈ closedBall
        (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
        (fordLemma63Radius k M j) := by
  rfl

theorem measurableSet_fordLemma63TorusOmega
    (k M n : ℕ) (u t : ℝ) :
    MeasurableSet (fordLemma63TorusOmega k M n u t) := by
  have hmeas : MeasurableSet (Set.univ.pi fun j : Fin k =>
      (closedBall
        (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
        (fordLemma63Radius k M j) : Set UnitAddCircle)) :=
    MeasurableSet.univ_pi fun _j : Fin k => measurableSet_closedBall
  convert hmeas using 1
  ext α
  simp [fordLemma63TorusOmega]

theorem fordLemma63_two_radius_lt_one
    {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (j : Fin k) :
    2 * fordLemma63Radius k M j < 1 := by
  unfold fordLemma63Radius
  have hj : (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (j : ℕ))
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ ((j : ℕ) + 1) := one_le_pow₀ hMR
  have hden : 1 < Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (k : ℝ) *
      (M : ℝ) ^ ((j : ℕ) + 1) := by
    have hpi : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    nlinarith [mul_le_mul hj hkR (by positivity : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ)),
      mul_le_mul (mul_le_mul hj hkR (by positivity : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ))) hpow
        (by positivity : (0 : ℝ) ≤ 1) (by positivity)]
  let D : ℝ := Real.pi * (((j : ℕ) : ℝ) + 1) * (k : ℝ) *
    (M : ℝ) ^ ((j : ℕ) + 1)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  rw [show 2 * Real.pi * (((j : ℕ) : ℝ) + 1) * (k : ℝ) *
      (M : ℝ) ^ ((j : ℕ) + 1) = 2 * D by
    dsimp [D]
    ring]
  change 2 * (1 / (2 * D)) < 1
  rw [show 2 * (1 / (2 * D)) = 1 / D by
    field_simp [hDpos.ne']]
  norm_num only [Nat.cast_add, Nat.cast_one] at hden
  apply (div_lt_iff₀ hDpos).2
  dsimp [D]
  linarith

theorem fordLemma63TorusOmega_measure_toReal
    {k M n : ℕ} {u t : ℝ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    ((Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
      (fordLemma63TorusOmega k M n u t)).toReal =
        ∏ j : Fin k, 2 * fordLemma63Radius k M j := by
  have hset : fordLemma63TorusOmega k M n u t =
      Set.univ.pi fun j : Fin k =>
        (closedBall
          (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
          (fordLemma63Radius k M j) : Set UnitAddCircle) := by
    ext α
    simp [fordLemma63TorusOmega]
  rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  have hhaar : AddCircle.haarAddCircle =
      (volume : Measure UnitAddCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hhaar]
  rw [AddCircle.volume_closedBall]
  rw [min_eq_right (le_of_lt (fordLemma63_two_radius_lt_one hk hM j))]
  exact ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (fordLemma63Radius_nonneg k M j))

theorem fordLemma63TorusOmega_measure_exact
    {k M n : ℕ} {u t : ℝ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    ((Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
      (fordLemma63TorusOmega k M n u t)).toReal =
      1 / (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k) := by
  rw [fordLemma63TorusOmega_measure_toReal hk hM]
  exact fordLemma63_prod_two_mul_radius hk hM

theorem fordLemma63Radius_top
    {k M : ℕ} (hk : 1 ≤ k) :
    fordLemma63Radius k M ⟨k - 1, by omega⟩ =
      fordLemma63TopRadius k M := by
  unfold fordLemma63Radius fordLemma63TopRadius
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hsubR : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast hsub
  rw [hsub, hsubR]
  ring

/-- Indices of phase boxes containing a fixed point of the unit torus. -/
def fordLemma63TorusOmegaFiber
    (N k M : ℕ) (u t : ℝ) (α : UnitAddTorus (Fin k)) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N - 1)).filter fun n =>
    α ∈ fordLemma63TorusOmega k M n u t

theorem fordLemma63TorusOmegaFiber_mem
    {N k M n : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)} :
    n ∈ fordLemma63TorusOmegaFiber N k M u t α ↔
      N < n ∧ n ≤ 2 * N - 1 ∧
        α ∈ fordLemma63TorusOmega k M n u t := by
  simp [fordLemma63TorusOmegaFiber, and_assoc]

theorem fordLemma63TorusOmegaFiber_subset_periodicTopFiber
    {N k M : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)}
    (hk : 1 ≤ k) :
    fordLemma63TorusOmegaFiber N k M u t α ⊆
      fordLemma63PeriodicTopFiber N k M u t
        ((AddCircle.equivIoc 1 0
          (α ⟨k - 1, by omega⟩)).1 : ℝ) := by
  classical
  intro n hn
  have hnData := fordLemma63TorusOmegaFiber_mem.mp hn
  let j : Fin k := ⟨k - 1, by omega⟩
  let β : ℝ := (AddCircle.equivIoc 1 0 (α j)).1
  have hβcoe : (β : UnitAddCircle) = α j := by
    dsimp [β]
    change (AddCircle.equivIoc 1 0).symm
      ((AddCircle.equivIoc 1 0) (α j)) = α j
    exact (AddCircle.equivIoc 1 0).symm_apply_apply (α j)
  have hball := (fordLemma63TorusOmega_mem.mp hnData.2.2) j
  have hpre : β ∈ ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
      closedBall
        (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
        (fordLemma63Radius k M j)) := by
    show (β : UnitAddCircle) ∈
      (closedBall
        (fordTaylorGamma t ((n : ℝ) + u) j : UnitAddCircle)
        (fordLemma63Radius k M j) : Set UnitAddCircle)
    rw [hβcoe]
    exact hball
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hpre
  simp only [Set.mem_iUnion] at hpre
  obtain ⟨z, hz⟩ := hpre
  apply fordLemma63PeriodicTopFiber_mem.mpr
  refine ⟨hnData.1, hnData.2.1, -z, ?_⟩
  have hdist :
      |β - (fordTaylorGamma t ((n : ℝ) + u) j + (z : ℝ))| ≤
        fordLemma63Radius k M j := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one]
      using hz
  have hgamma : fordLemma63TopGamma k n u t =
      fordTaylorGamma t ((n : ℝ) + u) j := by
    exact fordLemma63TopGamma_eq_fordTaylorGamma hk
  have hradius : fordLemma63Radius k M j =
      fordLemma63TopRadius k M := by
    exact fordLemma63Radius_top hk
  rw [hgamma, ← hradius]
  rw [Int.cast_neg]
  have heq :
      fordTaylorGamma t ((n : ℝ) + u) j - (β + -(z : ℝ)) =
        -(β - (fordTaylorGamma t ((n : ℝ) + u) j + (z : ℝ))) := by
    ring
  rw [heq, abs_neg]
  exact hdist

theorem fordLemma63TorusOmegaFiber_card_le_W
    {N k M : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)}
    (hk : 2 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) :
    ((fordLemma63TorusOmegaFiber N k M u t α).card : ℝ) ≤
      fordLemma63W N k M t := by
  have hsubset := fordLemma63TorusOmegaFiber_subset_periodicTopFiber
    (N := N) (M := M) (u := u) (t := t) (α := α) (by omega : 1 ≤ k)
  have hcard := Finset.card_le_card hsubset
  have hcardR : ((fordLemma63TorusOmegaFiber N k M u t α).card : ℝ) ≤
      ((fordLemma63PeriodicTopFiber N k M u t
        ((AddCircle.equivIoc 1 0
          (α ⟨k - 1, by omega⟩)).1 : ℝ)).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (fordLemma63PeriodicTopFiber_card_le_W hk hM hN hu0 hu1 ht htN)

#print axioms fordLemma63SZero_eq_torus
#print axioms fordLemma63_integral_SZeroTorus_two_s_le
#print axioms measurableSet_fordLemma63TorusOmega
#print axioms fordLemma63_two_radius_lt_one
#print axioms fordLemma63TorusOmega_measure_exact
#print axioms fordLemma63TorusOmegaFiber_card_le_W

end

end GafniTao
