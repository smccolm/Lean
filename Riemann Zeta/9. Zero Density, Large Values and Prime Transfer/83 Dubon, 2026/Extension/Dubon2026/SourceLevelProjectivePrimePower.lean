import Dubon2026.SourceLevelProjectiveLine
import Mathlib.Data.ZMod.Units

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> matching period dimension bounds -> original level index and genus numerics.
Selected from anthropics/fermats-last-theorem (Apache-2.0), commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the solutions
S_ModularCurve_card_projectiveLine_zmod, S_ModularCurve_dedekindPsi_prime_pow
and S_ModularCurve_dedekindPsi_mul_of_coprime. Only the necessary finite-ring
and arithmetic-function proofs are retained; the unrelated modular-polynomial
and function-field developments in the source files are omitted.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section
open Finset Nat Finset.Nat

section PrimePower

private theorem isUnit_zmod_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (z : ZMod (p ^ k)) :
    IsUnit z ↔ ZMod.castHom (dvd_pow_self p hk) (ZMod p) z ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h hzero
    exact (h.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))).ne_zero hzero
  · intro h
    by_contra hz
    apply h

    have hval : ¬z.val.Coprime (p ^ k) := fun hcop =>
      hz (by rw [← ZMod.natCast_zmod_val z]; exact (ZMod.isUnit_iff_coprime _ _).mpr hcop)
    have hdvd : p ∣ z.val := by
      by_contra hndvd
      exact hval (((hp.coprime_iff_not_dvd).mpr hndvd).symm.pow_right k)
    calc ZMod.castHom (dvd_pow_self p hk) (ZMod p) z
        = ZMod.castHom (dvd_pow_self p hk) (ZMod p) ((z.val : ℕ) : ZMod (p ^ k)) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((z.val : ℕ) : ZMod p) := map_natCast _ _
      _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd


private theorem isCoprime_isUnit_or_isUnit {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a c : ZMod (p ^ k)} (h : IsCoprime a c) : IsUnit a ∨ IsUnit c := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra hne
    exact hcon.1 ((isUnit_zmod_prime_pow_iff hp hk a).mpr hne)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra hne
    exact hcon.2 ((isUnit_zmod_prime_pow_iff hp hk c).mpr hne)
  obtain ⟨x, y, hxy⟩ := h
  apply_fun ZMod.castHom (dvd_pow_self p hk) (ZMod p) at hxy
  rw [map_add, map_mul, map_mul, map_one, ha, hc, mul_zero, mul_zero, add_zero] at hxy
  exact zero_ne_one hxy


private noncomputable def isUnitSubtypeEquivUnits (M : Type*) [Monoid M] :
    { z : M // IsUnit z } ≃ Mˣ where
  toFun z := z.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv z := Subtype.ext z.2.unit_spec
  right_inv u := Units.ext u.isUnit.unit_spec

private theorem card_not_isUnit_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  classical

  have hsplit : Nat.card { z : ZMod (p ^ k) // IsUnit z } +
      Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ k := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (IsUnit ·)),
      Nat.card_eq_fintype_card, ZMod.card]

  have hunits : Nat.card { z : ZMod (p ^ k) // IsUnit z } = (p ^ k).totient := by
    rw [Nat.card_congr (isUnitSubtypeEquivUnits (ZMod (p ^ k))), Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]

  have htot : (p ^ k).totient + p ^ (k - 1) = p ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
    calc (p ^ (j + 1)).totient + p ^ (j + 1 - 1)
        = p ^ j * (p - 1) + p ^ j := by rw [Nat.totient_prime_pow_succ hp, Nat.add_sub_cancel]
      _ = p ^ j * (p - 1 + 1) := by ring
      _ = p ^ j * p := by rw [hp1]
      _ = p ^ (j + 1) := (pow_succ p j).symm
  omega

theorem card_projectiveLine_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card (ProjectiveLine (ZMod (p ^ k))) = p ^ k + p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩

  let f : ZMod (p ^ k) ⊕ { z : ZMod (p ^ k) // ¬IsUnit z } → ProjectiveLine (ZMod (p ^ k)) :=
    fun s => Sum.rec (fun t => ⟦⟨(1, t), isCoprime_one_left⟩⟧)
      (fun m => ⟦⟨(m.1, 1), isCoprime_one_right⟩⟧) s
  have hbij : Function.Bijective f := by
    constructor
    · rintro (t | m) (t' | m') hff
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = 1 := h1
        have h2' : (u : ZMod (p ^ k)) * t = t' := h2
        rw [mul_one] at h1'
        rw [h1', one_mul] at h2'
        exact congrArg Sum.inl h2'
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = m'.1 := h1
        exact absurd (h1' ▸ (u.isUnit.mul isUnit_one)) m'.2
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = 1 := h1
        exact absurd ⟨⟨m.1, u, (mul_comm m.1 u).trans h1', h1'⟩, rfl⟩ m.2
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = m'.1 := h1
        have h2' : (u : ZMod (p ^ k)) * 1 = 1 := h2
        rw [mul_one] at h2'
        rw [h2', one_mul] at h1'
        exact congrArg Sum.inr (Subtype.ext h1')
    · intro q
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      by_cases ha : IsUnit v.1.1
      ·
        refine ⟨Sum.inl ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2), Quotient.sound ⟨ha.unit, ?_, ?_⟩⟩
        · show (ha.unit : ZMod (p ^ k)) * 1 = v.1.1
          rw [mul_one, ha.unit_spec]
        · show (ha.unit : ZMod (p ^ k)) * ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2) = v.1.2
          rw [Units.mul_inv_cancel_left]
      ·
        have hc : IsUnit v.1.2 := (isCoprime_isUnit_or_isUnit hp hk v.2).resolve_left ha
        have hm : ¬IsUnit ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) := fun hcon => by
          have : IsUnit ((hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1)) :=
            hc.unit.isUnit.mul hcon
          rw [Units.mul_inv_cancel_left] at this
          exact ha this
        refine ⟨Sum.inr ⟨(hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1, hm⟩,
          Quotient.sound ⟨hc.unit, ?_, ?_⟩⟩
        · show (hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) = v.1.1
          rw [Units.mul_inv_cancel_left]
        · show (hc.unit : ZMod (p ^ k)) * 1 = v.1.2
          rw [mul_one, hc.unit_spec]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_sum, Nat.card_eq_fintype_card, ZMod.card,
    card_not_isUnit_zmod_prime_pow hp hk]

end PrimePower


end
end Dubon2026.SourceLevelProjective
