import RiemannZeta.GuthMaynard.DFIEquation23Main

/-!
# Reduced moduli in DFI equation (23)

DFI explicitly requires `a/q` and `b/q` to be reduced before applying the
divisor Voronoi formula.  This file formalizes that source convention and the
exact equality of the original and reduced additive characters.
-/

open Complex

namespace RiemannZeta.GuthMaynard

/-- The reduced numerator and denominator of `a/q`. -/
structure DFIReducedModulus (a q : ℕ) [NeZero q] where
  gcd : ℕ := a.gcd q
  numerator : ℕ := a / a.gcd q
  denominator : ℕ := q / a.gcd q
  gcd_pos : 0 < gcd
  denominator_pos : 0 < denominator
  numerator_reconstruct : gcd * numerator = a
  denominator_reconstruct : gcd * denominator = q
  coprime : numerator.Coprime denominator

noncomputable def dfiReducedModulus (a q : ℕ) [NeZero q] :
    DFIReducedModulus a q where
  gcd := a.gcd q
  numerator := a / a.gcd q
  denominator := q / a.gcd q
  gcd_pos := Nat.gcd_pos_of_pos_right a (NeZero.pos q)
  denominator_pos := Nat.div_pos (Nat.gcd_le_right a (NeZero.pos q))
    (Nat.gcd_pos_of_pos_right a (NeZero.pos q))
  numerator_reconstruct := Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)
  denominator_reconstruct := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
  coprime := Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_right a (NeZero.pos q))

instance (a q : ℕ) [NeZero q] : NeZero (dfiReducedModulus a q).denominator :=
  ⟨(dfiReducedModulus a q).denominator_pos.ne'⟩

theorem dfiReducedModulus_numerator_isUnit (a q : ℕ) [NeZero q] :
    IsUnit ((dfiReducedModulus a q).numerator :
      ZMod (dfiReducedModulus a q).denominator) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (dfiReducedModulus a q).coprime

/-- Multiplying a frequency by `a` modulo `q` gives exactly the same complex
additive character as multiplying it by the reduced numerator modulo the
reduced denominator. -/
theorem stdAddChar_mul_eq_reduced (a q d n : ℕ) [NeZero q] :
    ZMod.stdAddChar ((a * d * n : ℕ) : ZMod q) =
      ZMod.stdAddChar
        (((dfiReducedModulus a q).numerator * d * n : ℕ) :
          ZMod (dfiReducedModulus a q).denominator) := by
  let R := dfiReducedModulus a q
  have hleft := ZMod.stdAddChar_coe (N := q) ((a * d * n : ℕ) : ℤ)
  have hright := ZMod.stdAddChar_coe (N := R.denominator)
    ((R.numerator * d * n : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hleft hright
  rw [hleft, hright]
  apply congrArg Complex.exp
  have hg : (R.gcd : ℂ) ≠ 0 := by exact_mod_cast R.gcd_pos.ne'
  have hratio : (a : ℂ) / (q : ℂ) =
      (R.numerator : ℂ) / (R.denominator : ℂ) := by
    have haC : (R.gcd : ℂ) * (R.numerator : ℂ) = (a : ℂ) := by
      exact_mod_cast R.numerator_reconstruct
    have hqC : (R.gcd : ℂ) * (R.denominator : ℂ) = (q : ℂ) := by
      exact_mod_cast R.denominator_reconstruct
    rw [← haC, ← hqC]
    field_simp
  calc
    2 * (Real.pi : ℂ) * I * (((a * d * n : ℕ) : ℂ)) / q =
        (2 * (Real.pi : ℂ) * I * d * n) * ((a : ℂ) / q) := by
          push_cast
          ring
    _ = (2 * (Real.pi : ℂ) * I * d * n) *
        ((R.numerator : ℂ) / (R.denominator : ℂ)) := by rw [hratio]
    _ = 2 * (Real.pi : ℂ) * I * (((R.numerator * d * n : ℕ) : ℂ)) /
        (R.denominator : ℂ) := by
          push_cast
          ring

theorem stdAddChar_neg_mul_eq_reduced (a q d n : ℕ) [NeZero q] :
    ZMod.stdAddChar (-((a * d * n : ℕ) : ZMod q)) =
      ZMod.stdAddChar
        (-(((dfiReducedModulus a q).numerator * d * n : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)) := by
  rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv,
    stdAddChar_mul_eq_reduced]

theorem dfiReducedModulus_frequency_isUnit
    (a q d : ℕ) [NeZero q] (hd : d.Coprime q) :
    IsUnit ((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator)) := by
  rw [ZMod.isUnit_iff_coprime]
  let R := dfiReducedModulus a q
  have hden : R.denominator ∣ q := by
    refine ⟨R.gcd, ?_⟩
    simpa [mul_comm] using R.denominator_reconstruct.symm
  exact R.coprime.mul_left (hd.of_dvd_right hden)

theorem dfiReducedModulus_neg_frequency_isUnit
    (a q d : ℕ) [NeZero q] (hd : d.Coprime q) :
    IsUnit (-((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator))) :=
  (dfiReducedModulus_frequency_isUnit a q d hd).neg

theorem periodicDivisorCoeff_source_eq_reduced
    (a q d n : ℕ) [NeZero q] :
    periodicDivisorCoeff q
        (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q))) n =
      periodicDivisorCoeff (dfiReducedModulus a q).denominator
        (dfiVoronoiCharacter (dfiReducedModulus a q).denominator
          ((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator))) n := by
  rw [periodicDivisorCoeff_voronoiCharacter,
    periodicDivisorCoeff_voronoiCharacter]
  congr 1
  simpa only [Nat.cast_mul] using stdAddChar_mul_eq_reduced a q d n

theorem periodicDivisorCoeff_neg_source_eq_reduced
    (a q d n : ℕ) [NeZero q] :
    periodicDivisorCoeff q
        (dfiVoronoiCharacter q (-(((a * d : ℕ) : ZMod q)))) n =
      periodicDivisorCoeff (dfiReducedModulus a q).denominator
        (dfiVoronoiCharacter (dfiReducedModulus a q).denominator
          (-((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)))) n := by
  rw [periodicDivisorCoeff_voronoiCharacter,
    periodicDivisorCoeff_voronoiCharacter]
  congr 1
  simpa only [neg_mul, Nat.cast_mul] using stdAddChar_neg_mul_eq_reduced a q d n

/-- Equation (23) with the two independently reduced Voronoi moduli. -/
noncomputable def dfiEquation23ReducedLeft
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) : ℂ :=
  periodicDivisorWeightedSum qₓ (dfiVoronoiCharacter qₓ dₓ)
    (fun x => periodicDivisorWeightedSum qᵧ
      (dfiVoronoiCharacter qᵧ dᵧ) (E x))

/-- The double divisor series carrying the two additive phases in DFI (22),
before reducing `a/q` and `b/q` as required immediately before equation (23). -/
noncomputable def dfiEquation23SourceLeft
    (q a b d : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℂ :=
  periodicDivisorWeightedSum q
    (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q)))
    (fun x => periodicDivisorWeightedSum q
      (dfiVoronoiCharacter q (-(((b * d : ℕ) : ZMod q)))) (E x))

/-- Exact source-entry reduction of both phases in DFI equation (23). -/
theorem dfiEquation23SourceLeft_eq_reduced
    (q a b d : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) :
    dfiEquation23SourceLeft q a b d E =
      dfiEquation23ReducedLeft
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))) E := by
  unfold dfiEquation23SourceLeft dfiEquation23ReducedLeft
  unfold periodicDivisorWeightedSum
  apply tsum_congr
  intro m
  rw [periodicDivisorCoeff_source_eq_reduced]
  congr 1
  apply tsum_congr
  intro n
  rw [periodicDivisorCoeff_neg_source_eq_reduced]

noncomputable def dfiEquation23ReducedGroupedRight
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) : ℂ :=
  (∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue qₓ dₓ bx
        (fun x => dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x))) +
    ∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue qₓ dₓ bx
        (fun x => dfiVoronoiRemainderValue qᵧ dᵧ (E x))

structure DFIEquation23ReducedAdmissible
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) where
  ySlice : ∀ x : ℝ, DFIVoronoiTestFunction (E x)
  xMain : DFIVoronoiTestFunction
    (fun x => dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x))
  xRemainder : DFIVoronoiTestFunction
    (fun x => dfiVoronoiRemainderValue qᵧ dᵧ (E x))

theorem dfiEquation23_reduced_grouped_of_admissible
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ)
    (E : ℝ → ℝ → ℂ) (hE : DFIEquation23ReducedAdmissible qᵧ dᵧ E) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ E =
      dfiEquation23ReducedGroupedRight qₓ qᵧ dₓ dᵧ E := by
  unfold dfiEquation23ReducedLeft dfiEquation23ReducedGroupedRight
  have hinner : ∀ x : ℝ,
      periodicDivisorWeightedSum qᵧ (dfiVoronoiCharacter qᵧ dᵧ) (E x) =
        dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x) +
          dfiVoronoiRemainderValue qᵧ dᵧ (E x) := by
    intro x
    rw [(hE.ySlice x).dfiProposition1_native_branch_sum qᵧ dᵧ hdᵧ,
      sum_dfiVoronoiBranchValue_eq_main_add_remainder]
  simp_rw [hinner]
  have hsMain := hE.xMain.summable_periodicDivisorWeighted qₓ
    (dfiVoronoiCharacter qₓ dₓ)
  have hsRem := hE.xRemainder.summable_periodicDivisorWeighted qₓ
    (dfiVoronoiCharacter qₓ dₓ)
  unfold periodicDivisorWeightedSum
  simp_rw [mul_add]
  rw [Summable.tsum_add hsMain hsRem]
  congr 1
  · exact hE.xMain.dfiProposition1_native_branch_sum qₓ dₓ hdₓ
  · exact hE.xRemainder.dfiProposition1_native_branch_sum qₓ dₓ hdₓ

/-- The concrete equation-(21) weight is admissible for two independently
reduced moduli. -/
noncomputable def dfiEquation23Weight_reducedAdmissible
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) (hdᵧ : IsUnit dᵧ) :
    DFIEquation23ReducedAdmissible qᵧ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) where
  ySlice := dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q₀ hq₀
  xMain := dfiEquation23Weight_mainBranch
    w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ
  xRemainder := dfiEquation23Weight_remainderBranch
    w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ hdᵧ

theorem dfiEquation23Weight_reduced_grouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) =
    dfiEquation23ReducedGroupedRight qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) := by
  exact dfiEquation23_reduced_grouped_of_admissible qₓ qᵧ dₓ dᵧ hdₓ hdᵧ _
    (dfiEquation23Weight_reducedAdmissible
      w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ hdᵧ)

/-- DFI equation (23) at its source entry: the two phases from equation (22)
are reduced to their correct, generally different, Voronoi moduli and both
Voronoi formulas are then applied. -/
theorem dfiEquation23Weight_source_grouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) (d : ℕ) (hd : d.Coprime q) :
    dfiEquation23SourceLeft q a b d
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
      dfiEquation23ReducedGroupedRight
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator)))
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  rw [dfiEquation23SourceLeft_eq_reduced]
  exact dfiEquation23Weight_reduced_grouped
    w hf hbox hφ a b ha hb h q hq
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator
    ((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator))
    (-((((dfiReducedModulus b q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus b q).denominator)))
    (dfiReducedModulus_frequency_isUnit a q d hd)
    (dfiReducedModulus_neg_frequency_isUnit b q d hd)

end RiemannZeta.GuthMaynard
