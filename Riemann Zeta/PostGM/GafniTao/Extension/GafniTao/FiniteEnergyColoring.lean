import GafniTao.ZeroOccurrenceEnergy

/-!
# Finite coloring of the multiplicity-replicated four-zero energy

The zero detector makes finitely many choices for each zero (branch, scale,
and displacement bin).  To preserve additive energy, those choices must be
pigeonholed simultaneously on all four coordinates of a resonant quadruple.
This file performs that finite step on the literal product-multiplicity type,
so no analytic multiplicity is lost or reconstructed heuristically.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Weighted four-coordinate pigeonhole on an arbitrary finite source. -/
theorem exists_four_coordinate_weighted_color_fiber
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) (weight : Alpha -> Nat)
    (m : Nat) (color : Alpha -> Fin 4 -> Fin m)
    (hS : S.Nonempty) :
    exists label : Fin 4 -> Fin m,
      (∑ x ∈ S, weight x) <= m ^ 4 *
        ∑ x ∈ S.filter (fun y => color y = label), weight x := by
  classical
  obtain ⟨label, -, hlabel⟩ :=
    RiemannZeta.GuthMaynard.weighted_finite_pigeonhole S
      (Finset.univ : Finset (Fin 4 -> Fin m)) weight color hS
      (fun x _ => Finset.mem_univ (color x))
  refine ⟨label, ?_⟩
  simpa using hlabel

/-- Empty-family extension of the weighted four-coordinate pigeonhole. -/
theorem exists_four_coordinate_weighted_color_fiber_of_pos
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) (weight : Alpha -> Nat)
    (m : Nat) (hm : 0 < m) (color : Alpha -> Fin 4 -> Fin m) :
    exists label : Fin 4 -> Fin m,
      (∑ x ∈ S, weight x) <= m ^ 4 *
        ∑ x ∈ S.filter (fun y => color y = label), weight x := by
  classical
  by_cases hS : S.Nonempty
  · exact exists_four_coordinate_weighted_color_fiber S weight m color hS
  · let label : Fin 4 -> Fin m := fun _ => ⟨0, hm⟩
    refine ⟨label, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Type-valued form used when a detector color is naturally a product of a
dyadic scale and a residue class. -/
theorem exists_four_coordinate_weighted_color_fiber_type
    {Alpha Kappa : Type*} [DecidableEq Alpha] [Fintype Kappa]
    [DecidableEq Kappa] [Nonempty Kappa]
    (S : Finset Alpha) (weight : Alpha -> Nat)
    (color : Alpha -> Fin 4 -> Kappa) :
    exists label : Fin 4 -> Kappa,
      (∑ x ∈ S, weight x) <= (Fintype.card Kappa) ^ 4 *
        ∑ x ∈ S.filter (fun y => color y = label), weight x := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨label, -, hlabel⟩ :=
      RiemannZeta.GuthMaynard.weighted_finite_pigeonhole S
        (Finset.univ : Finset (Fin 4 -> Kappa)) weight color hS
        (fun x _ => Finset.mem_univ (color x))
    refine ⟨label, ?_⟩
    simpa using hlabel
  · let label : Fin 4 -> Kappa := fun _ => Classical.choice inferInstance
    refine ⟨label, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Four-coordinate finite pigeonhole.  The source set may be empty; the
positive size hypothesis on the color space supplies a harmless label in
that case. -/
theorem exists_four_coordinate_color_fiber
    {Omega : Type*} [Fintype Omega]
    (m : Nat) (hm : 0 < m) (color : Omega -> Fin 4 -> Fin m) :
    exists label : Fin 4 -> Fin m,
      Fintype.card Omega <= m ^ 4 *
        (Finset.univ.filter fun q => color q = label).card := by
  classical
  cases isEmpty_or_nonempty Omega with
  | inl hEmpty =>
      let label : Fin 4 -> Fin m := fun _ => ⟨0, hm⟩
      refine ⟨label, ?_⟩
      have hCard : Fintype.card Omega = 0 := Fintype.card_eq_zero
      simp only [hCard, zero_le]
  | inr hNonempty =>
      obtain ⟨label, -, hFiber⟩ :=
        RiemannZeta.GuthMaynard.weighted_finite_pigeonhole
          (Finset.univ : Finset Omega)
          (Finset.univ : Finset (Fin 4 -> Fin m))
          (fun _ => 1) color Finset.univ_nonempty
          (fun q _ => Finset.mem_univ (color q))
      refine ⟨label, ?_⟩
      calc
        Fintype.card Omega =
            ∑ _q ∈ (Finset.univ : Finset Omega), 1 := by simp
        _ <= (Finset.univ : Finset (Fin 4 -> Fin m)).card *
            ∑ q ∈ (Finset.univ : Finset Omega).filter
              (fun y => color y = label), 1 := hFiber
        _ = m ^ 4 *
            (Finset.univ.filter fun q : Omega => color q = label).card := by
          simp

/-- Apply the four-coordinate pigeonhole directly to the canonical
product-multiplicity replication of the resonant zero quadruples. -/
theorem exists_resonant_zero_occurrence_color_fiber
    (sigma T : Real) (m : Nat) (hm : 0 < m)
    (color : Complex -> Fin m) :
    exists label : Fin 4 -> Fin m,
      zeroAdditiveEnergyCount sigma T <= m ^ 4 *
        (Finset.univ.filter fun q : ResonantZeroOccurrenceQuadruple sigma T =>
          (fun i => color (q.coord i)) = label).card := by
  obtain ⟨label, hlabel⟩ :=
    exists_four_coordinate_color_fiber m hm
      (fun (q : ResonantZeroOccurrenceQuadruple sigma T) i =>
        color (ResonantZeroOccurrenceQuadruple.coord i q))
  refine ⟨label, ?_⟩
  rw [← zeroOccurrenceAdditiveEnergyCount_eq]
  exact hlabel

/-- The additive defect after independently moving all four ordinates by at
most `H`.  This is the exact tolerance inflation used by the detector-entry
bridge. -/
theorem ResonantZeroOccurrenceQuadruple.shifted_defect_le
    {sigma T H : Real} (q : ResonantZeroOccurrenceQuadruple sigma T)
    (shift : Complex -> Real)
    (hShift : forall i : Fin 4,
      |(q.coord i).im - shift (q.coord i)| <= H) :
    |shift (q.coord 0) + shift (q.coord 1) -
        shift (q.coord 2) - shift (q.coord 3)| <= 1 + 4 * H := by
  have h0 := hShift 0
  have h1 := hShift 1
  have h2 := hShift 2
  have h3 := hShift 3
  have hRes := q.resonant
  rw [abs_le] at h0 h1 h2 h3 hRes ⊢
  constructor <;> linarith

#print axioms exists_four_coordinate_color_fiber
#print axioms exists_four_coordinate_weighted_color_fiber
#print axioms exists_four_coordinate_weighted_color_fiber_of_pos
#print axioms exists_four_coordinate_weighted_color_fiber_type
#print axioms exists_resonant_zero_occurrence_color_fiber
#print axioms ResonantZeroOccurrenceQuadruple.shifted_defect_le

end

end GafniTao
