import GafniTao.FordLReducedFourier

/-!
# Ford Lemma 3.3: deletion of a marked diagonal coordinate

A diagonal solution is marked at one coordinate, that common value is saved,
and the coordinate is deleted.  The remaining tuple satisfies the literal
zero-frequency equations with `k-1` polynomial-coordinate pairs.  This is the
finite source of Ford's factor `kP` in the estimate for `U₀`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordLAwayIndex {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}

def fordLAwayPolynomialMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k)
    (u : FordLAwayIndex i → FordLCongruentCoordinate P p r) : Fin k → ℤ :=
  fordFamilyMoment (fordLCoordinateMoment Ψ) u

def fordLAwayTotalMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (s Q q : ℕ)
    (v : (FordLAwayIndex i → FordLCongruentCoordinate P p r) ×
      FordLPowerPair s Q) : Fin k → ℤ :=
  fordLAwayPolynomialMoment Ψ i v.1 +
    fordLPowerPairMoment k Q p q s v.2

abbrev FordLAwaySolution
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (s Q q : ℕ) :=
  FordCharacterZero (fordLAwayTotalMoment (P := P) (p := p) (r := r)
    Ψ i s Q q)

abbrev FordLMarkedDiagonalSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :=
  Σ v : FordLSolution Ψ s P Q p q r,
    {i : Fin k // v.1.1.1 i = v.1.1.2 i}

noncomputable def fordLDiagonalToMarked
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} :
    FordLDiagonalSolution Ψ s P Q p q r →
      FordLMarkedDiagonalSolution Ψ s P Q p q r :=
  fun v ↦ ⟨v.1, ⟨Classical.choose v.2, Classical.choose_spec v.2⟩⟩

theorem fordLDiagonalToMarked_injective
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} :
    Function.Injective (fordLDiagonalToMarked :
      FordLDiagonalSolution Ψ s P Q p q r →
        FordLMarkedDiagonalSolution Ψ s P Q p q r) := by
  intro v w h
  exact Subtype.ext (congrArg Sigma.fst h)

def fordLMarkedToAway
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    FordLMarkedDiagonalSolution Ψ s P Q p q r →
      Σ i : Fin k, Fin P × FordLAwaySolution (P := P) (p := p) (r := r)
        Ψ i s Q q := by
  intro z
  let v := z.1
  let i := z.2.1
  let hv := fordLSolutionEquivCharacterZero Ψ s P Q p q r v
  let u : FordLAwayIndex i → FordLCongruentCoordinate P p r :=
    fun j ↦ hv.1.1 j.1
  have hdiag : fordLCoordinateMoment Ψ (hv.1.1 i) = 0 := by
    funext a
    unfold fordLCoordinateMoment
    apply sub_eq_zero.mpr
    simpa [v, i, hv, fordLSolutionEquivCharacterZero] using
      congrArg (fun x : Fin P ↦
        (Ψ.poly a).eval ((((x : ℕ) + 1 : ℕ) : ℤ))) z.2.2
  have hzero : fordLAwayTotalMoment Ψ i s Q q (u, hv.1.2) = 0 := by
    funext a
    have hfull := congrFun hv.2 a
    unfold fordLTotalMoment fordLPolynomialTupleMoment at hfull
    unfold fordLAwayTotalMoment fordLAwayPolynomialMoment
    simp only [Pi.add_apply] at hfull ⊢
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne
      (fun j : Fin k ↦ fordLCoordinateMoment Ψ (hv.1.1 j) a) i
    simp only [fordFamilyMoment, Finset.sum_apply] at hfull ⊢
    rw [hsplit, congrFun hdiag a] at hfull
    simpa [u] using hfull
  exact ⟨i, hv.1.1 i |>.1.1, ⟨(u, hv.1.2), hzero⟩⟩

theorem fordLMarkedToAway_injective
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    Function.Injective (fordLMarkedToAway Ψ s P Q p q r) := by
  intro z w h
  rcases z with ⟨v, ⟨i, hvi⟩⟩
  rcases w with ⟨w, ⟨j, hwj⟩⟩
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hpair :
      (fordLMarkedToAway Ψ s P Q p q r ⟨v, ⟨i, hvi⟩⟩).2 =
        (fordLMarkedToAway Ψ s P Q p q r ⟨w, ⟨i, hwj⟩⟩).2 := by
    exact heq_iff_eq.mp (Sigma.mk.inj_iff.mp h).2
  have hsaved : v.1.1.1 i = w.1.1.1 i :=
    congrArg Prod.fst hpair
  have haway :
      (fordLMarkedToAway Ψ s P Q p q r ⟨v, ⟨i, hvi⟩⟩).2.2.1.1 =
        (fordLMarkedToAway Ψ s P Q p q r ⟨w, ⟨i, hwj⟩⟩).2.2.1.1 :=
    congrArg (fun t ↦ t.2.1.1) hpair
  have hpower : v.1.2 = w.1.2 :=
    congrArg (fun t ↦ t.2.1.2) hpair
  have hvw : v = w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · funext a
        by_cases hai : a = i
        · subst a
          exact hsaved
        · exact congrArg (fun z ↦ z.1.1) (congrFun haway ⟨a, hai⟩)
      · funext a
        by_cases hai : a = i
        · subst a
          rw [← hvi, ← hwj]
          exact hsaved
        · exact congrArg (fun z ↦ z.1.2) (congrFun haway ⟨a, hai⟩)
    · exact hpower
  subst w
  rfl

theorem fordL_diagonal_le_marked
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLDiagonalCount Ψ s P Q p q r ≤
      Nat.card (FordLMarkedDiagonalSolution Ψ s P Q p q r) := by
  exact Nat.card_le_card_of_injective _ fordLDiagonalToMarked_injective

#print axioms fordLDiagonalToMarked_injective
#print axioms fordLMarkedToAway
#print axioms fordLMarkedToAway_injective
#print axioms fordL_diagonal_le_marked

end

end GafniTao
