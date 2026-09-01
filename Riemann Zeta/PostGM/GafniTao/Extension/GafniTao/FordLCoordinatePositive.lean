import GafniTao.FordLFourier

/-!
# Ford Lemma 3.3: positivity of `I(α)`

The congruent-pair character sum is partitioned by the common residue class
modulo `p^r`.  This proves the literal identity
`I(α) = ∑_c |∑_{z ≡ c} e(α·Φ(z))|²`, hence reality and nonnegativity.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

abbrev FordPolynomialResidueInterval (P m : ℕ) (c : ZMod m) :=
  {x : Fin P // ((((x : ℕ) + 1 : ℕ) : ZMod m)) = c}

def fordPolynomialResidueWeylSum
    {k d T P m : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ZMod m) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ x : FordPolynomialResidueInterval P m c,
    UnitAddTorus.mFourier (fordPolynomialSingleMoment Ψ x.1) α

def fordLCongruentCoordinateEquivSigma
    (P p r : ℕ) [NeZero (p ^ r)] :
    FordLCongruentCoordinate P p r ≃
      Σ c : ZMod (p ^ r),
        FordPolynomialResidueInterval P (p ^ r) c ×
          FordPolynomialResidueInterval P (p ^ r) c where
  toFun zw := ⟨(((zw.1.1 : ℕ) + 1 : ℕ) : ZMod (p ^ r)),
    (⟨zw.1.1, rfl⟩, ⟨zw.1.2,
      (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).2 zw.2 |>.symm⟩)⟩
  invFun u := ⟨(u.2.1.1, u.2.2.1),
    (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).1
      (u.2.1.2.trans u.2.2.2.symm)⟩
  left_inv zw := by rfl
  right_inv u := by
    rcases u with ⟨c, ⟨x, hx⟩, ⟨y, hy⟩⟩
    subst c
    apply Sigma.ext rfl
    exact HEq.rfl

def fordLCoordinateEnergy
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) : ℝ :=
  ∑ c : ZMod (p ^ r),
    ‖fordPolynomialResidueWeylSum (P := P) Ψ c α‖ ^ 2

theorem fordLCoordinateWeylSum_eq_energy
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) :
    fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α =
      (fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α : ℂ) := by
  unfold fordLCoordinateWeylSum fordCharacterSum
  let e := fordLCongruentCoordinateEquivSigma P p r
  calc
    (∑ zw : FordLCongruentCoordinate P p r,
        UnitAddTorus.mFourier (fordLCoordinateMoment Ψ zw) α) =
        ∑ u : Σ c : ZMod (p ^ r),
            FordPolynomialResidueInterval P (p ^ r) c ×
              FordPolynomialResidueInterval P (p ^ r) c,
          UnitAddTorus.mFourier (fordLCoordinateMoment Ψ (e.symm u)) α := by
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ c : ZMod (p ^ r),
        ((‖fordPolynomialResidueWeylSum (P := P) Ψ c α‖ ^ 2 : ℝ) : ℂ) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Fintype.sum_prod_type]
      dsimp only [e, fordLCongruentCoordinateEquivSigma]
      change (∑ x : FordPolynomialResidueInterval P (p ^ r) c,
          ∑ y : FordPolynomialResidueInterval P (p ^ r) c,
            UnitAddTorus.mFourier
              (fordPolynomialSingleMoment Ψ x.1 -
                fordPolynomialSingleMoment Ψ y.1) α) = _
      simp_rw [sub_eq_add_neg, UnitAddTorus.mFourier_add,
        UnitAddTorus.mFourier_neg]
      rw [← Finset.sum_mul_sum, ← map_sum]
      change fordPolynomialResidueWeylSum (P := P) Ψ c α *
          conj (fordPolynomialResidueWeylSum (P := P) Ψ c α) = _
      rw [Complex.mul_conj']
      norm_num
    _ = (fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α : ℂ) := by
      norm_num [fordLCoordinateEnergy]

theorem fordLCoordinateEnergy_nonneg
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) :
    0 ≤ fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α := by
  unfold fordLCoordinateEnergy
  positivity

theorem fordLCoordinateWeylSum_re_nonneg
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) :
    0 ≤ (fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α).re := by
  rw [fordLCoordinateWeylSum_eq_energy]
  exact fordLCoordinateEnergy_nonneg Ψ α

#print axioms fordLCongruentCoordinateEquivSigma
#print axioms fordLCoordinateWeylSum_eq_energy
#print axioms fordLCoordinateEnergy_nonneg
#print axioms fordLCoordinateWeylSum_re_nonneg

end

end GafniTao
