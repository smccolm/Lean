import Dubon2026.SourceEllipticCubicDivisionComparison
import Dubon2026.SourcePrimeTorsionScalarAction
import Dubon2026.SourceEllipticTorsionStructure

/-! DUB-17/18 -> reverse genus -> exceptional j=0 census ->
non-scalar action of the actual cubic elliptic automorphism on prime
torsion. Reuse the already proved multiplication fraction, prime-torsion
scalar lemma, optional coordinates, actual torsion cardinality and basis.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the j=0 fixed-vcInvFun
subgroup-count source solution. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

theorem cubic_exists_order_prime_nonscalar [IsAlgClosed L] (B : L) (hB : B ≠ 0) (u : Lˣ) (hu1 : (u : L) ≠ 1)
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (σ : (EB B).toAffine.Point →+ (EB B).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), xco (σ (Point.some x y h)) = some ((u : L) * x))
    (hσ : ∀ P : (EB B).toAffine.Point, σ (σ P) + σ P + P = 0)
    (p : ℕ) (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    ∃ T : (EB B).toAffine.Point, addOrderOf T = p ∧ ∀ k : ℕ, σ T ≠ k • T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hE : (EB B).IsElliptic := isElliptic_EB B hB h2 h3
  have hσ0 : ∀ P : (EB B).toAffine.Point, σ P = 0 ↔ P = 0 := fun P =>
    ⟨fun h0 => by have := hσ P; rwa [h0, map_zero, zero_add, zero_add] at this,
     fun h0 => by rw [h0, map_zero]⟩

  suffices core : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y), addOrderOf (Point.some x y h) = p ∧
      ∀ k : ℕ, xco (k • Point.some x y h) ≠ some ((u : L) * x) by
    obtain ⟨x, y, h, hord, hk⟩ := core
    refine ⟨Point.some x y h, hord, fun k hk' => hk k ?_⟩
    rw [← hk', hσx]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    obtain ⟨a, ha⟩ : ∃ a : L, a ^ 3 = -B := by
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-B) (n := 3) (by norm_num)
      exact ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; apply hB; simpa using ha.symm
    have heq : (EB B).toAffine.Equation a 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]; simp; linear_combination -ha
    have hns : (EB B).toAffine.Nonsingular a 0 := by
      rw [WeierstrassCurve.Affine.nonsingular_iff']
      refine ⟨heq, Or.inl ?_⟩
      show (0 : L) * 0 - (3 * a ^ 2 + 2 * 0 * a + 0) ≠ 0
      intro h3a
      apply ha0
      have : (3 : L) * a ^ 2 = 0 := by linear_combination -h3a
      simpa [h3] using this
    have hneg : -Point.some a 0 hns = Point.some a 0 hns := by
      rw [Point.neg_some]; congr 1; simp [WeierstrassCurve.Affine.negY]
    have h2T : (2 : ℕ) • Point.some a 0 hns = 0 := by
      rw [two_nsmul]; nth_rewrite 1 [← hneg]; rw [neg_add_cancel]
    have hord : addOrderOf (Point.some a 0 hns) = 2 :=
      addOrderOf_eq_prime_iff.mpr ⟨h2T, Point.some_ne_zero hns⟩
    refine ⟨a, 0, hns, hord, fun k => ?_⟩
    have hkT : k • Point.some a 0 hns = 0 ∨ k • Point.some a 0 hns = Point.some a 0 hns := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; rw [← two_mul, mul_nsmul, h2T, nsmul_zero]
      · right; rw [add_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add, one_nsmul]
    rcases hkT with h0 | h1
    · rw [h0, xco_zero]; simp
    · rw [h1, xco_some]; simp only [ne_eq, Option.some.injEq]
      intro h; apply hu1
      have : (1 - (u : L)) * a = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact (sub_eq_zero.mp h').symm
      · exact absurd h' ha0
  ·
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases this.eq_or_lt with h | h
      · exact absurd hpodd (by rw [← h]; decide)
      · omega
    have hcard : Nat.card (Submodule.torsionBy ℤ (EB B).toAffine.Point p) = p ^ 2 := by
      have h := SourceEllipticTorsion.actual_torsion_cardinality (EB B) (K := L) hpL
      simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using h
    by_contra hcon
    push Not at hcon

    have heig : ∀ T : (EB B).toAffine.Point, (p : ℤ) • T = 0 → ∃ a : ℤ, σ T = a • T := by
      intro T hpT
      rcases T with _ | ⟨x, y, h⟩
      · exact ⟨0, by rw [zero_smul]; exact map_zero σ⟩
      · have hord : addOrderOf (Point.some x y h) = p := by
          refine addOrderOf_eq_prime_iff.mpr ⟨?_, Point.some_ne_zero h⟩
          rw [← natCast_zsmul]; exact hpT
        obtain ⟨k, hk⟩ := hcon x y h hord
        have hx : xco (σ (Point.some x y h)) = xco (k • Point.some x y h) := by rw [hσx, hk]
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨k, by rw [h1, natCast_zsmul]⟩
        · exact ⟨-k, by rw [h1, neg_smul, natCast_zsmul]⟩

    let Ep := (Submodule.torsionBy ℤ (EB B).toAffine.Point p).toAddSubgroup
    have hEp_mem : ∀ T : (EB B).toAffine.Point, T ∈ Ep ↔ (p : ℤ) • T = 0 := fun T => Submodule.mem_torsionBy_iff _ _
    have hσEp : ∀ T ∈ Ep, σ T ∈ Ep := by
      intro T hT
      rw [hEp_mem] at hT ⊢
      rw [← map_zsmul, hT, map_zero]
    let σ' : Ep →+ Ep := (σ.comp Ep.subtype).codRestrict Ep (fun T => hσEp T T.2)
    obtain ⟨eb⟩ : Nonempty (ZMod p × ZMod p ≃+ Ep) := by
      have h := SourceEllipticTorsionStructure.actual_torsion_structure (EB B) (K := L) hpL
      simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using h
    have heig' : ∀ v : Ep, ∃ a : ℤ, σ' v = a • v := by
      rintro ⟨T, hT⟩
      obtain ⟨a, ha⟩ := heig T ((hEp_mem T).mp hT)
      exact ⟨a, Subtype.ext ha⟩
    obtain ⟨c, hc⟩ := exists_common_scalar eb σ' heig'

    obtain ⟨m, hm1, hmle, hmx⟩ : ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ p - 1 ∧
        ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          xco ((m : ℤ) • Point.some x y h) = some ((u : L) * x) := by
      let r : ℕ := ((c : ZMod p)).val
      have hr : (r : ZMod p) = c := by simp [r]
      have hrp : r < p := ZMod.val_lt _
      have hσc : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          σ (Point.some x y h) = (r : ℤ) • Point.some x y h := by
        intro x y h hpT
        have hT : Point.some x y h ∈ Ep := (hEp_mem _).mpr hpT
        have := hc ⟨_, hT⟩
        have hval : σ (Point.some x y h) = c • Point.some x y h := congrArg Subtype.val this
        rw [hval]
        obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) c p).mp (by exact_mod_cast hr)
        have : c = r + p * k := by linarith
        rw [this, add_zsmul, mul_comm, mul_zsmul, hpT, zsmul_zero, add_zero]
      obtain ⟨x₀, y₀, h₀, hp₀⟩ : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 := by
        have h1 : 1 < Nat.card Ep := by rw [show Nat.card Ep = p ^ 2 from hcard]; nlinarith
        haveI : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
        haveI : Nontrivial Ep := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Ep)
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (hEp_mem _).mp hT⟩
      have hr0 : r ≠ 0 := by
        intro hr0
        have := hσc x₀ y₀ h₀ hp₀
        rw [hr0, Nat.cast_zero, zero_smul, hσ0] at this
        exact Point.some_ne_zero h₀ this
      by_cases hle : 2 * r ≤ p - 1
      · refine ⟨r, Nat.one_le_iff_ne_zero.mpr hr0, hle, fun x y h hpT => ?_⟩
        rw [← hσc x y h hpT, hσx]
      · obtain ⟨k0, hk0⟩ := hpodd
        refine ⟨p - r, by omega, by omega, fun x y h hpT => ?_⟩
        have : ((p - r : ℕ) : ℤ) • Point.some x y h = -((r : ℤ) • Point.some x y h) := by
          rw [Nat.cast_sub hrp.le, sub_zsmul, hpT]; simp
        rw [this, xco_neg, ← hσc x y h hpT, hσx]

    set F : L[X] := (EB B).Φ (m : ℤ) - C (u : L) * X * (EB B).ΨSq (m : ℤ) with hFdef
    have hFdeg : F.natDegree ≤ m ^ 2 := natDegree_Phi_sub_C_mul_X_mul_PsiSq_le (EB B) (u : L) m hm1

    have hxm := prime_torsion_mul_coordinates (EB B) m hm1
    have hF0 : F ≠ 0 := cubic_division_comparison_ne_zero B hB u h2 h3 σ hσx hσ m hm1
    have hroot : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 → F.IsRoot x := by
      intro x y h hpT
      obtain ⟨hΨ, hxp⟩ := hxm p hp (by omega) x y h hpT
      have hx : xco ((m : ℤ) • Point.some x y h) = some ((u : L) * x) := hmx x y h hpT
      rw [hxp, Option.some.injEq, div_eq_iff hΨ] at hx
      show F.eval x = 0
      rw [hFdef, eval_sub, eval_mul, eval_mul, eval_C, eval_X]
      linear_combination hx

    haveI hfinEp : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
    haveI : Fintype Ep := Fintype.ofFinite Ep
    classical
    let g : Ep → Option L := fun T => xco (T.1 : (EB B).toAffine.Point)
    let s : Finset Ep := Finset.univ.filter (fun T => T ≠ 0)
    have hs_card : s.card = p ^ 2 - 1 := by
      have : s.card + 1 = p ^ 2 := by
        rw [show s = Finset.univ.erase 0 by ext T; simp [s], Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card, show Nat.card Ep = p ^ 2 from hcard]
        have : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
      omega
    have hfib : ∀ b ∈ s.image g, (s.filter (fun T => g T = b)).card ≤ 2 := by
      intro b hb
      obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp hb
      have hsub : s.filter (fun T => g T = g T₁) ⊆ {T₁, -T₁} := by
        intro T hT
        rw [Finset.mem_filter] at hT
        have hx : xco (T.1 : (EB B).toAffine.Point) = xco (T₁.1 : (EB B).toAffine.Point) := hT.2
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · rw [Finset.mem_insert]; left; exact Subtype.ext h1
        · rw [Finset.mem_insert, Finset.mem_singleton]; right
          exact Subtype.ext (by rw [h1]; rfl)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    have hle : s.card ≤ 2 * (s.image g).card := Finset.card_le_mul_card_image s 2 hfib
    have himg : s.image g ⊆ (F.roots.toFinset).image some := by
      intro b hb
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_filter] at hT
      obtain ⟨⟨T, hTp⟩, hT0⟩ := T, hT.2
      rcases T with _ | ⟨x, y, h⟩
      · exact absurd rfl (fun h => hT0 (Subtype.ext h))
      · refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
        rw [Multiset.mem_toFinset, mem_roots hF0]
        exact hroot x y h ((hEp_mem _).mp hTp)
    have hR : ((F.roots.toFinset).image some).card ≤ m ^ 2 := by
      refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
      exact (Polynomial.card_roots' F).trans hFdeg
    have hfinal : p ^ 2 - 1 ≤ 2 * m ^ 2 := by
      rw [← hs_card]; exact hle.trans (Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans hR))
    have h4 : 4 * m ^ 2 ≤ (p - 1) ^ 2 := by nlinarith
    have hp1 : 1 ≤ p := hp.one_lt.le
    zify [hp1, Nat.one_le_iff_ne_zero.mpr (show p ^ 2 ≠ 0 by positivity)] at hfinal h4 hmle
    nlinarith


end
end Dubon2026.SourceEllipticExceptional
