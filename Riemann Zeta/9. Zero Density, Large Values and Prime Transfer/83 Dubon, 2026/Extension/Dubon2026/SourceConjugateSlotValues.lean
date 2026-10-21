import Dubon2026.SourceConjugateSlotIndices
import Dubon2026.SourcePrimePowerCoefficientAction

/-! DUB-17/18 -> numerical modular genus -> all-level j degree ->
the explicit distinct Laurent conjugate list. The value at a=0 is only
a total extension of the formula; every actual index has a nonzero a.
Leading coefficients distinguish a, and the primitive root distinguishes b.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean, sv_inj.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K]

/-- The literal twisted j Laurent series for the triangular index (a,b). -/
def slotValue (ζ : Kˣ) (a b : ℕ) : LaurentSeries K :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    TS K (a * a) (ζ ^ (b * a))

theorem slotValue_eq (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    slotValue ζ a b = TS K (a * a) (ζ ^ (b * a)) := by
  rw [slotValue, dif_neg (NeZero.ne a)]

theorem slotValue_injective {N : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {a b a' b' : ℕ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b * a < N) (hb' : b' * a' < N)
    (h : slotValue ζ a b = slotValue ζ a' b') : a = a' ∧ b = b' := by
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero a' := ⟨ha'⟩
  rw [slotValue_eq, slotValue_eq] at h
  obtain ⟨he, hu⟩ := TS_injective h
  have haa : a = a' := Nat.mul_self_inj.mp he
  subst a'
  refine ⟨rfl, ?_⟩
  have hv : (ζ : K) ^ (b * a) = (ζ : K) ^ (b' * a) := by
    have h1 := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha) (hζ.pow_inj hb hb' hv)

theorem slotValue_injOn_indices {N : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N) :
    Set.InjOn (fun s : Σ _ : ℕ, ℕ => slotValue ζ s.1 s.2) (indices N) := by
  intro s hs t ht he
  obtain ⟨h1, h2⟩ := slotValue_injective hζ (index_fst_ne_zero hs)
    (index_fst_ne_zero ht) (index_phase_lt hs) (index_phase_lt ht) he
  cases s
  cases t
  simp_all

end
end Dubon2026.SourceFunctionField.ConjugateSlots
