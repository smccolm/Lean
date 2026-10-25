import Dubon2026.SourceEllipticFullTorsionFieldExtension

/-! DUB-17/18 -> characteristic-two genus/Picard -> full inertia image.
Use the existing specialization at level 3N. Full torsion descends to each
divisor by the actual point map into the algebraic closure and its proved
torsion count. This supplies both N-torsion and three-torsion without
reconstructing the faithful Deuring field. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

theorem card_torsion_of_dvd_full_torsion
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {m n : ℕ} (hn : (n : F) ≠ 0)
    (hmn : m ∣ n) (M : IntermediateField F Ω)
    (hcard : Nat.card {P : (E.baseChange M).toAffine.Point // n • P = 0} = n ^ 2) :
    Nat.card {P : (E.baseChange M).toAffine.Point // m • P = 0} = m ^ 2 := by
  have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hmΩ : (m : Ω) ≠ 0 := by
    obtain ⟨k, hk⟩ := hmn
    intro h
    apply hnΩ
    rw [hk, Nat.cast_mul, h, zero_mul]
  let g : (E.baseChange M).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    Point.map (IntermediateField.val M)
  let gT (d : ℕ) : {P : (E.baseChange M).toAffine.Point // d • P = 0} →
      {P : (E.baseChange Ω).toAffine.Point // d • P = 0} :=
    fun P => ⟨g P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hgT (d : ℕ) : Function.Injective (gT d) := fun P Q h =>
    Subtype.ext (Point.map_injective _ (congrArg Subtype.val h))
  have hΩ (d : ℕ) (hd : (d : Ω) ≠ 0) :
      Nat.card {P : (E.baseChange Ω).toAffine.Point // d • P = 0} = d ^ 2 := by
    change Nat.card ({P : (E.baseChange Ω).toAffine.Point | d • P = 0} : Set _) = d ^ 2
    rw [Nat.card_coe_set_eq]
    exact (finite_and_ncard_torsion E hd).2
  haveI : Finite {P : (E.baseChange Ω).toAffine.Point // n • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hΩ n hnΩ]; exact pow_ne_zero _ hn0)
  have hsurj : Function.Surjective (gT n) :=
    ((Nat.bijective_iff_injective_and_card (gT n)).mpr
      ⟨hgT n, hcard.trans (hΩ n hnΩ).symm⟩).2
  have hsurjm : Function.Surjective (gT m) := by
    intro Q
    have hQn : n • Q.1 = 0 := by
      obtain ⟨k, rfl⟩ := hmn
      rw [mul_nsmul, Q.2, smul_zero]
    obtain ⟨P, hP⟩ := hsurj ⟨Q.1, hQn⟩
    have hgP : g P.1 = Q.1 := congrArg Subtype.val hP
    have hPm : m • P.1 = 0 := by
      apply Point.map_injective (IntermediateField.val M)
      change g (m • P.1) = g 0
      rw [map_nsmul, hgP, Q.2, map_zero]
    exact ⟨⟨P.1, hPm⟩, Subtype.ext hgP⟩
  exact (Nat.card_congr (Equiv.ofBijective (gT m) ⟨hgT m, hsurjm⟩)).trans (hΩ m hmΩ)

end
end Dubon2026.SourceEllipticDivisionField
