import Dubon2026.SourceCuspNormalFormCriterion

/-! DUB-17/18 -> parabolic Hecke realization -> matching period dimensions
-> exact arithmetic genus bound -> count of original rational cusp orbits.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_CuspSpace_classification.lean.
The quotient and its level action are the previously proved SourceManin
objects. Cusp widths and unrelated geometric infrastructure are omitted.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups

namespace CuspSpace
variable {N : ℕ}

/-- Choose the proved coprime numerator of the original cusp normal form. -/
noncomputable def normalNumerator (hN : N ≠ 0) (x : CuspSpace N) : ℤ :=
  (Dubon2026.SourceManin.CuspSpace.exists_normalForm hN x).choose

lemma isCoprime_normalNumerator (hN : N ≠ 0) (x : CuspSpace N) :
    IsCoprime (normalNumerator hN x) (cuspDenom N x : ℤ) :=
  (Dubon2026.SourceManin.CuspSpace.exists_normalForm hN x).choose_spec.1

lemma mk_ratPoint_normalNumerator (hN : N ≠ 0) (x : CuspSpace N) :
    x = mk N (ratPoint (normalNumerator hN x) (cuspDenom N x)) :=
  (Dubon2026.SourceManin.CuspSpace.exists_normalForm hN x).choose_spec.2

lemma isUnit_intCast_of_isCoprime {d : ℕ} {a : ℤ} (ha : IsCoprime a (d : ℤ)) :
    IsUnit ((a : ZMod (Nat.gcd d (N / d)))) := by
  have hga : IsCoprime a ((Nat.gcd d (N / d) : ℕ) : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d (N / d)))
  exact .of_mul_eq_one _ (ZMod.coe_int_mul_inv_eq_one hga)

lemma exists_intCast_eq_unit {d : ℕ} (hd0 : d ≠ 0)
    (u : (ZMod (Nat.gcd d (N / d)))ˣ) :
    ∃ s : ℤ, IsCoprime s (d : ℤ) ∧
      ((s : ZMod (Nat.gcd d (N / d)))) = (u : ZMod (Nat.gcd d (N / d))) := by
  have hg0 : Nat.gcd d (N / d) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd0)).ne'
  have : NeZero (Nat.gcd d (N / d)) := ⟨hg0⟩

  have hval : Nat.Coprime ((u : ZMod (Nat.gcd d (N / d)))).val (Nat.gcd d (N / d)) :=
    ZMod.val_coe_unit_coprime u
  have hvalZ : IsCoprime (((u : ZMod (Nat.gcd d (N / d)))).val : ℤ)
      ((Nat.gcd d (N / d) : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hval

  obtain ⟨s, hs_mod, hs_cop⟩ :=
    exists_dvd_sub_and_isCoprime (M := ((Nat.gcd d (N / d) : ℕ) : ℤ))
      (by exact_mod_cast hg0) hvalZ hd0
  refine ⟨s, hs_cop, ?_⟩

  have h1 : ((((u : ZMod (Nat.gcd d (N / d)))).val : ℤ) : ZMod (Nat.gcd d (N / d)))
      = (s : ZMod (Nat.gcd d (N / d))) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hs_mod
  rw [← h1]
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- The unit residue of the original normalized cusp numerator. -/
noncomputable def fiberToUnits (hN : N ≠ 0) {d : ℕ}
    (x : {x : CuspSpace N // cuspDenom N x = d}) : (ZMod (Nat.gcd d (N / d)))ˣ :=
  (isUnit_intCast_of_isCoprime (x.2 ▸ isCoprime_normalNumerator hN x.1)).unit

@[simp] lemma val_fiberToUnits (hN : N ≠ 0) {d : ℕ}
    (x : {x : CuspSpace N // cuspDenom N x = d}) :
    (fiberToUnits hN x : ZMod (Nat.gcd d (N / d)))
      = ((normalNumerator hN x.1 : ℤ) : ZMod (Nat.gcd d (N / d))) :=
  IsUnit.unit_spec _

lemma eq_mk_ratPoint_normalNumerator (hN : N ≠ 0) {d : ℕ}
    (x : {x : CuspSpace N // cuspDenom N x = d}) :
    x.1 = mk N (ratPoint (normalNumerator hN x.1) d) := by
  conv_lhs => rw [mk_ratPoint_normalNumerator hN x.1]
  rw [x.2]

lemma fiberToUnits_injective (hN : N ≠ 0) (hcrit : NormalFormCriterion N) {d : ℕ}
    (hd : d ∣ N) : Function.Injective (fiberToUnits (N := N) hN (d := d)) := by
  intro x y hxy
  have hx := x.2 ▸ isCoprime_normalNumerator hN x.1
  have hy := y.2 ▸ isCoprime_normalNumerator hN y.1
  have hval : ((normalNumerator hN x.1 : ℤ) : ZMod (Nat.gcd d (N / d)))
      = ((normalNumerator hN y.1 : ℤ) : ZMod (Nat.gcd d (N / d))) := by
    rw [← val_fiberToUnits hN x, ← val_fiberToUnits hN y, hxy]
  refine Subtype.ext ?_
  rw [eq_mk_ratPoint_normalNumerator hN x, eq_mk_ratPoint_normalNumerator hN y]
  exact (hcrit _ _ d hd hx hy).mpr hval

lemma fiberToUnits_surjective (hN : N ≠ 0) (hcrit : NormalFormCriterion N) {d : ℕ}
    (hd : d ∣ N) : Function.Surjective (fiberToUnits (N := N) hN (d := d)) := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hd)
  intro u
  obtain ⟨s, hs_cop, hs_val⟩ := exists_intCast_eq_unit hd0 u

  have hyd : cuspDenom N (mk N (ratPoint s d)) = d := by
    rw [cuspDenom_mk_ratPoint hs_cop, Int.gcd_natCast_natCast, Nat.gcd_eq_left hd]
  refine ⟨⟨mk N (ratPoint s d), hyd⟩, ?_⟩

  refine Units.ext ?_
  rw [val_fiberToUnits]
  have ha : IsCoprime (normalNumerator hN (mk N (ratPoint s d))) ((d : ℕ) : ℤ) := by
    have h := isCoprime_normalNumerator hN (mk N (ratPoint s d))
    rwa [hyd] at h
  have hya : mk N (ratPoint (normalNumerator hN (mk N (ratPoint s d))) d)
      = mk N (ratPoint s d) :=
    (eq_mk_ratPoint_normalNumerator hN (⟨mk N (ratPoint s d), hyd⟩ :
      {x : CuspSpace N // cuspDenom N x = d})).symm
  rw [(hcrit _ _ d hd ha hs_cop).mp hya, hs_val]

/-- The proved equivalence between a denominator fiber and its unit residues. -/
noncomputable def fiberEquivUnits (hN : N ≠ 0) (hcrit : NormalFormCriterion N) {d : ℕ}
    (hd : d ∣ N) : {x : CuspSpace N // cuspDenom N x = d} ≃ (ZMod (Nat.gcd d (N / d)))ˣ :=
  Equiv.ofBijective _
    ⟨fiberToUnits_injective hN hcrit hd, fiberToUnits_surjective hN hcrit hd⟩

variable (N) in

/-- The actual cusp denominator as a divisor of the original level. -/
noncomputable def cuspDenomDvd (hN : N ≠ 0) (x : CuspSpace N) : N.divisors :=
  ⟨cuspDenom N x, Nat.mem_divisors.mpr ⟨cuspDenom_dvd x, hN⟩⟩

@[simp] lemma cuspDenomDvd_coe (hN : N ≠ 0) (x : CuspSpace N) :
    (cuspDenomDvd N hN x : ℕ) = cuspDenom N x := rfl

theorem classification_of_normalFormCriterion (hN : N ≠ 0)
    (hcrit : NormalFormCriterion N) : Classification N := by
  refine ⟨(Equiv.sigmaFiberEquiv (cuspDenomDvd N hN)).symm.trans
    (Equiv.sigmaCongrRight fun d => ?_)⟩
  refine (Equiv.subtypeEquivRight fun x => ?_).trans
    (fiberEquivUnits hN hcrit (Nat.mem_divisors.mp d.2).1)
  rw [Subtype.ext_iff, cuspDenomDvd_coe]

theorem classification {N : ℕ} (hN : N ≠ 0) :
    Dubon2026.SourceManin.CuspSpace.Classification N :=
  Dubon2026.SourceManin.CuspSpace.classification_of_normalFormCriterion hN (Dubon2026.SourceManin.CuspSpace.normalFormCriterion hN)

end CuspSpace

end
end Dubon2026.SourceManin
