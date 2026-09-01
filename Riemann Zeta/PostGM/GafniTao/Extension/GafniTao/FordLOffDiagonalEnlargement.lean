import GafniTao.FordLOffDiagonalFixed

/-!
# Ford Lemma 3.3: exact off-diagonal count enlargement

An off-diagonal solution determines, coordinate by coordinate, a sign, a
positive shift and a lower endpoint.  The sign/shift tuple is retained as a
partition parameter, while the lower endpoints are placed in the full box
`(Fin k → Fin P)`.  The construction below is injective and its target is the
literal zero-frequency solution type for the fixed signed-shift system.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordLOffDiagonalCoordinate
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} (v : FordLOffDiagonalSolution Ψ s P Q p q r)
    (i : Fin k) :
    {zw : FordLCongruentCoordinate P p r // zw.1.1 ≠ zw.1.2} :=
  ⟨⟨(v.1.1.1.1 i, v.1.1.1.2 i), v.1.2.1 i⟩, by
    intro h
    exact v.2 ⟨i, h⟩⟩

abbrev FordLOffDiagonalCode (k s P Q m : ℕ) :=
  (Fin k → FordOffDiagonalShiftCoordinate P m) × FordLPowerPair s Q

def fordLOffDiagonalCodeOf
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) :
    FordLOffDiagonalCode k s P Q (p ^ r) :=
  (fun i => fordOffDiagonalShiftCoordinate
      (fordLOffDiagonalCoordinate v i).1 (fordLOffDiagonalCoordinate v i).2,
    v.1.1.2)

theorem fordLOffDiagonalCodeOf_injective
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} [NeZero (p ^ r)] :
    Function.Injective (fordLOffDiagonalCodeOf :
      FordLOffDiagonalSolution Ψ s P Q p q r →
        FordLOffDiagonalCode k s P Q (p ^ r)) := by
  intro v w h
  have hcoords := congrArg
    (fun z : FordLOffDiagonalCode k s P Q (p ^ r) => z.1) h
  have hpower : v.1.1.2 = w.1.1.2 := congrArg
    (fun z : FordLOffDiagonalCode k s P Q (p ^ r) => z.2) h
  have hfirst : v.1.1.1.1 = w.1.1.1.1 := by
    funext i
    have henc := congrFun hcoords i
    have hsub := fordOffDiagonalShiftCoordinate_injective henc
    exact congrArg (fun z => z.1.1.1) hsub
  have hsecond : v.1.1.1.2 = w.1.1.1.2 := by
    funext i
    have henc := congrFun hcoords i
    have hsub := fordOffDiagonalShiftCoordinate_injective henc
    exact congrArg (fun z => z.1.1.2) hsub
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext hfirst hsecond) hpower

def fordLOffDiagonalParameterOf
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) :
    FordLOffDiagonalParameter k P (p ^ r) :=
  fun i => (((fordLOffDiagonalCodeOf v).1 i).1,
    ((fordLOffDiagonalCodeOf v).1 i).2.1)

def fordLOffDiagonalBaseOf
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) : Fin k → Fin P :=
  fun i => ((fordLOffDiagonalCodeOf v).1 i).2.2

theorem fordLFixedPolynomialMoment_of_offDiagonal
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) :
    fordLFixedPolynomialMoment Ψ (p ^ r)
        (fordLOffDiagonalParameterOf v) (fordLOffDiagonalBaseOf v) =
      fordLPolynomialTupleMoment Ψ
        (fun i => (fordLOffDiagonalCoordinate v i).1) := by
  funext j
  unfold fordLFixedPolynomialMoment fordLPolynomialTupleMoment fordFamilyMoment
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [fordLOffDiagonalParameterOf, fordLOffDiagonalBaseOf,
    fordLOffDiagonalCodeOf] using congrFun (fordLSignedShiftMoment_encoded Ψ
      (fordLOffDiagonalCoordinate v i).1 (fordLOffDiagonalCoordinate v i).2) j

def fordLFixedSolutionOf
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) :
    FordLFixedSolution Ψ (p ^ r) p q s Q
      (fordLOffDiagonalParameterOf v) := by
  refine ⟨(fordLOffDiagonalBaseOf v, v.1.1.2), ?_⟩
  funext j
  have hpoly := congrFun (fordLFixedPolynomialMoment_of_offDiagonal Ψ v) j
  have hzero := congrFun
    (fordLSolutionEquivCharacterZero Ψ s P Q p q r v.1).2 j
  unfold fordLFixedTotalMoment at ⊢
  unfold fordLTotalMoment at hzero
  simp only [Pi.add_apply]
  rw [hpoly]
  simpa [fordLSolutionEquivCharacterZero, fordLOffDiagonalCoordinate] using hzero

def fordLOffDiagonalToFixedSigma
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)] :
    FordLOffDiagonalSolution Ψ s P Q p q r →
      Σ u : FordLOffDiagonalParameter k P (p ^ r),
        FordLFixedSolution Ψ (p ^ r) p q s Q u :=
  fun v => ⟨fordLOffDiagonalParameterOf v, fordLFixedSolutionOf Ψ v⟩

def fordLFixedSigmaCode
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)] :
    (Σ u : FordLOffDiagonalParameter k P (p ^ r),
      FordLFixedSolution Ψ (p ^ r) p q s Q u) →
      FordLOffDiagonalCode k s P Q (p ^ r) :=
  fun z => ((fun i => ((z.1 i).1, (z.1 i).2, z.2.1.1 i)), z.2.1.2)

theorem fordLFixedSigmaCode_of_offDiagonal
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)]
    (v : FordLOffDiagonalSolution Ψ s P Q p q r) :
    fordLFixedSigmaCode Ψ (fordLOffDiagonalToFixedSigma Ψ v) =
      fordLOffDiagonalCodeOf v := by
  simp [fordLFixedSigmaCode, fordLOffDiagonalToFixedSigma,
    fordLOffDiagonalParameterOf, fordLFixedSolutionOf,
    fordLOffDiagonalBaseOf, fordLOffDiagonalCodeOf]

theorem fordLOffDiagonalToFixedSigma_injective
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    {s P Q p q r : ℕ} [NeZero (p ^ r)] :
    Function.Injective (fordLOffDiagonalToFixedSigma Ψ :
      FordLOffDiagonalSolution Ψ s P Q p q r →
        Σ u : FordLOffDiagonalParameter k P (p ^ r),
          FordLFixedSolution Ψ (p ^ r) p q s Q u) := by
  intro v w h
  apply fordLOffDiagonalCodeOf_injective
  rw [← fordLFixedSigmaCode_of_offDiagonal Ψ v,
    ← fordLFixedSigmaCode_of_offDiagonal Ψ w, h]

theorem fordLOffDiagonalCount_le_fixedSigma
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) [NeZero (p ^ r)] :
    fordLOffDiagonalCount Ψ s P Q p q r ≤
      Nat.card (Σ u : FordLOffDiagonalParameter k P (p ^ r),
        FordLFixedSolution Ψ (p ^ r) p q s Q u) := by
  exact Nat.card_le_card_of_injective _
    (fordLOffDiagonalToFixedSigma_injective Ψ)

#print axioms fordLOffDiagonalCodeOf_injective
#print axioms fordLFixedSolutionOf
#print axioms fordLOffDiagonalToFixedSigma_injective
#print axioms fordLOffDiagonalCount_le_fixedSigma

end

end GafniTao
