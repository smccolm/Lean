import Dubon2026.SourcePrimePowerCoefficientAction

/-! DUB-17/18 -> numerical modular genus -> exact composite j-map degree
-> rational prime-power extension degree. The nonzero twisted roots form
one orbit under the actual cyclotomic coefficient automorphism. This is
the needed lower-degree argument after removing the previous-level root;
SourcePrimePowerExactFieldDegree assembles the degree consumer under
the explicit next-series nonmembership condition, which remains required.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean.
Existing literal twist coordinates and coefficient transport are reused.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K]

/-- The twisted root indexed by a power of a generator of the nonzero residue classes. -/
def rUnit (e : ℕ) [NeZero e] {p : ℕ} (ζ : Kˣ) (g : (ZMod p)ˣ) (i : ℕ) :
    LaurentSeries K :=
  TS K e (ζ ^ ((g ^ i : (ZMod p)ˣ) : ZMod p).val)

theorem range_map_eq_rUnit (p : ℕ) [hp : Fact (Nat.Prime p)] (e : ℕ) [NeZero e]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    (Multiset.range p).map (fun b => TS K e (ζ ^ b))
      = TS K e 1 ::ₘ (Multiset.range (p - 1)).map (rUnit e ζ g) := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  have hg1 : g ^ (p - 1) = 1 := by rw [← horder]; exact pow_orderOf_eq_one g
  have hgmod : ∀ a : ℕ, g ^ a = g ^ (a % (p - 1)) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a (p - 1)]
    rw [pow_add, pow_mul, hg1, one_pow, one_mul]
  have hexp : ∀ {a b : ℕ}, a < p → b < p → ζ ^ a = ζ ^ b → a = b := by
    intro a b ha hb h
    refine hζ.pow_inj ha hb ?_
    have h2 := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h2
  have hnd1 : ((Multiset.range p).map (fun b => TS K e (ζ ^ b))).Nodup := by
    refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro a ha b hb h
    rw [Multiset.mem_range] at ha hb
    exact hexp ha hb (TS_injective h).2
  have hnd2 : (TS K e 1 ::ₘ (Multiset.range (p - 1)).map (rUnit e ζ g)).Nodup := by
    rw [Multiset.nodup_cons]
    constructor
    · intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨i, hi, hTS⟩ := hmem
      rw [rUnit] at hTS
      have h0 : ζ ^ ((g ^ i : (ZMod p)ˣ) : ZMod p).val = ζ ^ (0 : ℕ) := by
        rw [pow_zero]
        exact (TS_injective hTS).2
      have he0 : ((g ^ i : (ZMod p)ˣ) : ZMod p).val = 0 :=
        hexp (ZMod.val_lt _) hp.out.pos h0
      have hz : ((g ^ i : (ZMod p)ˣ) : ZMod p) = 0 := by rwa [ZMod.val_eq_zero] at he0
      exact Units.ne_zero (g ^ i) hz
    · refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range (p - 1))
      intro a ha b hb h
      rw [Multiset.mem_range] at ha hb
      rw [rUnit, rUnit] at h
      have hval : ((g ^ a : (ZMod p)ˣ) : ZMod p).val = ((g ^ b : (ZMod p)ˣ) : ZMod p).val :=
        hexp (ZMod.val_lt _) (ZMod.val_lt _) (TS_injective h).2
      have hcoe : ((g ^ a : (ZMod p)ˣ) : ZMod p) = ((g ^ b : (ZMod p)ˣ) : ZMod p) :=
        ZMod.val_injective p hval
      have hgab : (g ^ a : (ZMod p)ˣ) = g ^ b := Units.ext hcoe
      have ha' : a ∈ Set.Iio (orderOf g) := by rw [horder]; exact ha
      have hb' : b ∈ Set.Iio (orderOf g) := by rw [horder]; exact hb
      exact pow_injOn_Iio_orderOf ha' hb' hgab
  rw [Multiset.Nodup.ext hnd1 hnd2]
  intro x
  simp only [Multiset.mem_map, Multiset.mem_range, Multiset.mem_cons]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · left
      rw [pow_zero]
    · right
      have hbp : ¬ p ∣ b := fun hdvd => absurd (Nat.le_of_dvd hb0 hdvd) (not_le.mpr hb)
      have hcop : Nat.Coprime b p := Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr hbp)
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
        ((isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr
          (hg (ZMod.unitOfCoprime b hcop)))
      refine ⟨k % (p - 1), Nat.mod_lt _ hp1, ?_⟩
      rw [rUnit, ← hgmod, hk, ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hb]
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨0, hp.out.pos, by rw [pow_zero]⟩
    · rw [rUnit]
      exact ⟨((g ^ i : (ZMod p)ˣ) : ZMod p).val, ZMod.val_lt _, rfl⟩


end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
