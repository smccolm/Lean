import GafniTao.ReflectionSignEnergySplit

/-!
# One fixed reflection sign reduced to dyadic self energies

Negating every ordinate preserves approximate additive energy exactly.  This
allows the negative Poisson-reflection sign to use the same bounded-shift
extractor as the positive sign, without translating or discarding points.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

def signedReflectionBase (sign : Fin 2) (t : Real) : Real :=
  if sign.val = 0 then -t else t

noncomputable def signedReflectionFamily (sign : Fin 2) (W : Finset Real) :
    Finset Real :=
  W.image (signedReflectionBase sign)

theorem signedReflectionBase_injective (sign : Fin 2) :
    Function.Injective (signedReflectionBase sign) := by
  intro x y hxy
  by_cases hs : sign.val = 0
  · simpa [signedReflectionBase, hs] using hxy
  · simpa [signedReflectionBase, hs] using hxy

theorem signedReflectionFamily_separated
    (sign : Fin 2) (W : Finset Real) (hW : IsSeparated 1 W) :
    IsSeparated 1 (signedReflectionFamily sign W) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hbEq⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hxy hbEq
  subst y
  have hsep := hW a ha b hb hab
  rw [Real.dist_eq] at hsep ⊢
  by_cases hs : sign.val = 0
  · rw [show signedReflectionBase sign a - signedReflectionBase sign b =
        -(a - b) by simp [signedReflectionBase, hs]; ring, abs_neg]
    exact hsep
  · simpa [signedReflectionBase, hs] using hsep

theorem approxAddEnergy_signedReflectionFamily
    (eta : Real) (sign : Fin 2) (W : Finset Real) :
    ApproxAddEnergy eta (signedReflectionFamily sign W) =
      ApproxAddEnergy eta W := by
  by_cases hs : sign.val = 0
  · have hbase : signedReflectionBase sign = fun t : Real => -t := by
      funext t
      simp [signedReflectionBase, hs]
    have hfamily : signedReflectionFamily sign W = gmScale (-1) W := by
      simp only [signedReflectionFamily, hbase, gmScale]
      congr 2
      funext t
      ring
    rw [hfamily]
    simpa using (approxAddEnergy_scale eta (-1) (by norm_num) W)
  · have hbase : signedReflectionBase sign = id := by
      funext t
      simp [signedReflectionBase, hs]
    rw [show signedReflectionFamily sign W = W by
      simp only [signedReflectionFamily, hbase, Finset.image_id]]

/-- Once the reflection sign is fixed, exact negation invariance and the
bounded displacement feed the common shifted-wide energy theorem. -/
theorem signed_reflected_wide_energy_to_dyadic_self
    (sign : Fin 2) (W : Finset Real) (hW : IsSeparated 1 W)
    (H S R : Real) (k : Nat) (hk : 0 < k) (a : Nat → Complex)
    (hEach : ∀ t, t ∈ W →
      if sign = 0 then
        ∃ s : Real, |(-t) - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
          S ≤ ‖wideDirichletPoly 1 k a s‖
      else
        ∃ s : Real, |t - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
          S ≤ ‖wideDirichletPoly 1 k a s‖) :
    ∃ r : Fin 4 → Fin k, ∃ U : Fin 4 → Finset Real,
      (∀ i : Fin 4, IsSeparated 1 (U i)) ∧
      (∀ i : Fin 4, ∀ t, t ∈ U i → -R ≤ t ∧ t ≤ R) ∧
      (∀ i : Fin 4, ∀ t, t ∈ U i →
        S / k ≤ ‖dirichletPoly (2 ^ (r i : Nat)) a t‖) ∧
      4 * (ApproxAddEnergy 1 W : Real) ≤
        ((2 * k : Nat) : Real) ^ 4 *
          ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
          (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
          ((ApproxAddEnergy 1 (U 0) : Real) +
            (ApproxAddEnergy 1 (U 1) : Real) +
            (ApproxAddEnergy 1 (U 2) : Real) +
            (ApproxAddEnergy 1 (U 3) : Real)) := by
  have hBaseEach : ∀ x, x ∈ signedReflectionFamily sign W → ∃ s : Real,
      |x - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a s‖ := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    fin_cases sign
    · simpa [signedReflectionBase] using hEach t ht
    · simpa [signedReflectionBase] using hEach t ht
  obtain ⟨r, U, hSep, hRange, hLarge, hEnergy⟩ :=
    shifted_wide_energy_to_dyadic_self
      (signedReflectionFamily sign W)
      (signedReflectionFamily_separated sign W hW)
      H S R k hk a hBaseEach
  refine ⟨r, U, hSep, hRange, hLarge, ?_⟩
  rw [approxAddEnergy_signedReflectionFamily] at hEnergy
  exact hEnergy

#print axioms signedReflectionBase_injective
#print axioms signedReflectionFamily_separated
#print axioms approxAddEnergy_signedReflectionFamily
#print axioms signed_reflected_wide_energy_to_dyadic_self

end

end GafniTao
