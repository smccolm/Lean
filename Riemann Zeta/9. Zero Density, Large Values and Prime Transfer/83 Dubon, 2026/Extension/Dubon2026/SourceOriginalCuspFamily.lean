import Dubon2026.SourceCuspLabelWidthSum

/-! DUB-17/18 -> numerical modular genus -> cusp count. Choose the
actually constructed embedding and normalized place for each primitive
cusp label. The leading-coefficient distinction proves this family is
injective; the proved widths show every member is a pole. This makes the
finite candidate family concrete for comparison with the total pole degree.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)

/-- The actual conjugate embedding selected for a primitive cusp label. -/
def embedding (s : {s // s ∈ labels N}) : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L :=
  (original_cusp_place_with_width N L ζ hζ s.1 (label_mem_indices N s.1 s.2)).choose

/-- The actual normalized place selected with the conjugate embedding. -/
def place (s : {s // s ∈ labels N}) : Place L (modularFunctionFieldOver N L) :=
  (original_cusp_place_with_width N L ζ hζ s.1 (label_mem_indices N s.1 s.2)).choose_spec.choose

theorem embedding_spec (s : {s // s ∈ labels N}) :
    embedding N L ζ hζ s (jOver N L) = TS L N 1 ∧
      embedding N L ζ hζ s (jNOver N L) = slotValue ζ s.1.1 s.1.2 ∧
      (∀ f, (place N L ζ hζ s).ord f *
        ((s.1.1 * Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) = (embedding N L ζ hζ s f).order) ∧
      (place N L ζ hζ s).ord (jOver N L) = -((N / s.1.1 / Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) ∧
      (place N L ζ hζ s).ord (jNOver N L) = -((s.1.1 / Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) :=
  (original_cusp_place_with_width N L ζ hζ s.1 (label_mem_indices N s.1 s.2)).choose_spec.choose_spec

theorem place_injective : Function.Injective (place N L ζ hζ) := by
  intro s t he
  have hs := embedding_spec N L ζ hζ s
  have ht := embedding_spec N L ζ hζ t
  haveI : NeZero s.1.1 := ⟨index_fst_ne_zero (label_mem_indices N s.1 s.2)⟩
  haveI : NeZero t.1.1 := ⟨index_fst_ne_zero (label_mem_indices N t.1 t.2)⟩
  obtain ⟨ha, hb⟩ := cusp_parameters_of_same_place N L ζ hζ s.1.1 s.1.2 t.1.1 t.1.2
    ((mem_labels N s.1).mp s.2).1 (embedding N L ζ hζ s) (embedding N L ζ hζ t)
    hs.1 hs.2.1 ht.1 ht.2.1 (place N L ζ hζ s)
    (s.1.1 * Nat.gcd s.1.1 (N / s.1.1)) (t.1.1 * Nat.gcd t.1.1 (N / t.1.1)) hs.2.2.1
    (by rw [he]; exact ht.2.2.1)
  have hsb := ((mem_labels N s.1).mp s.2).2.1
  have htb : t.1.2 < Nat.gcd s.1.1 (N / s.1.1) := by
    rw [ha]
    exact ((mem_labels N t.1).mp t.2).2.1
  exact Subtype.ext (Sigma.ext ha (heq_of_eq (hb.eq_of_lt_of_lt hsb htb)))

theorem place_is_pole (s : {s // s ∈ labels N}) : (place N L ζ hζ s).ord (jOver N L) < 0 := by
  rw [(embedding_spec N L ζ hζ s).2.2.2.1]
  have ha := ((mem_labels N s.1).mp s.2).1
  have ha0 : 0 < s.1.1 := Nat.pos_of_ne_zero (index_fst_ne_zero (label_mem_indices N s.1 s.2))
  have hd : 0 < N / s.1.1 := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) ha) ha0
  have hg : 0 < Nat.gcd s.1.1 (N / s.1.1) := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left ha0.ne')
  have hw : 0 < N / s.1.1 / Nat.gcd s.1.1 (N / s.1.1) :=
    Nat.div_pos (Nat.gcd_le_right s.1.1 hd) hg
  exact neg_neg_of_pos (by exact_mod_cast hw)

end
end Dubon2026.SourceFunctionField.CuspLabels
