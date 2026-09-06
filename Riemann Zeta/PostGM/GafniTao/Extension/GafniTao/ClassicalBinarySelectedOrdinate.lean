import GafniTao.ClassicalBinarySelectedAlternative
import RiemannZeta.GuthMaynard.TypeIFiniteEstimates

/-!
# Positive physical ordinates for a selected signed binary family

The binary detector records which signed shell produced a selected
polynomial.  This module uses that recorded sign to return the representative
to a positive physical ordinate.  In the Type-I branch the resulting large
value is exactly a large value of the frozen classical coefficient sequence,
so the terminal and medium Type-I estimates apply without an evenness
assumption or an absolute-value substitution.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The positive physical ordinate attached to a binary scale label. -/
def classicalBinaryOrientedOrdinate
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)) (t : Real) : Real :=
  if classicalBinaryShellScaleSign q = 0 then t else -t

/-- The positive-ordinate image of a family carrying one fixed binary scale
label.  Because the label is fixed, this map is globally either the identity
or reflection through the origin. -/
noncomputable def classicalBinaryOrientedFamily
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2))
    (W : Finset Real) : Finset Real :=
  W.image (classicalBinaryOrientedOrdinate q)

/-- Orientation by a fixed detector label is injective. -/
theorem classicalBinaryOrientedOrdinate_injective
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)) :
    Function.Injective (classicalBinaryOrientedOrdinate q) := by
  intro x y hxy
  unfold classicalBinaryOrientedOrdinate at hxy
  by_cases hs : classicalBinaryShellScaleSign q = 0
  · simpa [hs] using hxy
  · simp only [if_neg hs] at hxy
    linarith

/-- A fixed-label orientation preserves the family cardinality exactly. -/
theorem card_classicalBinaryOrientedFamily
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2))
    (W : Finset Real) :
    (classicalBinaryOrientedFamily q W).card = W.card := by
  unfold classicalBinaryOrientedFamily
  exact Finset.card_image_iff.mpr
    (classicalBinaryOrientedOrdinate_injective q).injOn

/-- A fixed-label orientation preserves metric separation exactly. -/
theorem isSeparated_classicalBinaryOrientedFamily
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2))
    {d : Real} {W : Finset Real} (hW : IsSeparated d W) :
    IsSeparated d (classicalBinaryOrientedFamily q W) := by
  intro x hx y hy hxy
  rw [classicalBinaryOrientedFamily, Finset.mem_image] at hx hy
  obtain ⟨x0, hx0, rfl⟩ := hx
  obtain ⟨y0, hy0, rfl⟩ := hy
  have hne : x0 ≠ y0 := by
    intro heq
    apply hxy
    rw [heq]
  have hsep := hW x0 hx0 y0 hy0 hne
  unfold classicalBinaryOrientedOrdinate
  by_cases hs : classicalBinaryShellScaleSign q = 0
  · simpa [hs] using hsep
  · simpa [hs, Real.dist_eq] using hsep

/-- A nonempty family remains nonempty after orientation. -/
theorem classicalBinaryOrientedFamily_nonempty
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2))
    {W : Finset Real} (hW : W.Nonempty) :
    (classicalBinaryOrientedFamily q W).Nonempty := by
  obtain ⟨t, ht⟩ := hW
  exact ⟨classicalBinaryOrientedOrdinate q t,
    Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩

/-- A representative selected by a fixed detector colour remains in the
positive physical interval after applying its recorded source sign. -/
theorem classicalBinaryOrientedOrdinate_mem_physical_interval
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    {t : Real}
    (ht : t ∈ ((absoluteDyadicZeroSlab sigma U).filter
      (fun rho => detectorColor d.scale d.shift rho = label)).image
        (detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) d.scale d.shift)) :
    U - U ^ delta ≤ classicalBinaryOrientedOrdinate label.1 t ∧
      classicalBinaryOrientedOrdinate label.1 t ≤ 2 * U + U ^ delta := by
  obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
  have hm := Finset.mem_filter.mp hrho
  have hscale : d.scale rho = label.1 := congrArg Prod.fst hm.2
  have hOrient := d.hOriented rho hm.1
  have hInterval := d.hInterval rho hm.1
  unfold classicalBinaryOrientedOrdinate
  rw [← hscale]
  by_cases hs : classicalBinaryShellScaleSign (d.scale rho) = 0
  · rw [if_pos hs] at hOrient ⊢
    exact ⟨hOrient, hInterval.2⟩
  · rw [if_neg hs] at hOrient ⊢
    constructor <;> linarith [hInterval.1]

/-- The complete fixed-colour family lies in the positive physical interval
after orientation. -/
theorem classicalBinaryOrientedFamily_in_physical_interval
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) :
    ∀ t ∈ classicalBinaryOrientedFamily label.1
        (((absoluteDyadicZeroSlab sigma U).filter
          (fun rho => detectorColor d.scale d.shift rho = label)).image
            (detectorRepresentative
              (absoluteDyadicZeroSlab sigma U) d.scale d.shift)),
      U - U ^ delta ≤ t ∧ t ≤ 2 * U + U ^ delta := by
  intro t ht
  rw [classicalBinaryOrientedFamily, Finset.mem_image] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  exact classicalBinaryOrientedOrdinate_mem_physical_interval d label ht0

/-- Once the displacement is at most half the shell height, the oriented
family lies in the frozen large-values base interval `[0,3U]`. -/
theorem classicalBinaryOrientedFamily_inBaseInterval
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hU : 0 ≤ U) (hShift : U ^ delta ≤ U / 2) :
    InBaseInterval (3 * U)
      (classicalBinaryOrientedFamily label.1
        (((absoluteDyadicZeroSlab sigma U).filter
          (fun rho => detectorColor d.scale d.shift rho = label)).image
            (detectorRepresentative
              (absoluteDyadicZeroSlab sigma U) d.scale d.shift))) := by
  intro t ht
  rw [Set.mem_Icc]
  have hRange :=
    classicalBinaryOrientedFamily_in_physical_interval d label t ht
  constructor <;> linarith

/-- In the selected Type-I branch, the source-signed detector large value is
exactly a positive-ordinate large value of the classical coefficient
sequence. -/
theorem classicalTypeIShellScaleLarge_oriented
    {A Y X kI kII : Nat} {sigma q0 t : Real}
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kI * 2)) (hq : binaryScaleLabel q = Sum.inl r)
    (hLarge : Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel q) t) :
    ((3 / 4 : Real) * (q0 / 2)) / (kI : Real) ≤
      ‖dirichletPoly (classicalTypeIShellScaleN Y r)
        (classicalZetaLongLineCoeff A sigma)
        (classicalBinaryOrientedOrdinate q t)‖ := by
  have hRaw : ((3 / 4 : Real) * (q0 / 2)) / (kI : Real) ≤
      ‖sourceDirichletPoly (classicalTypeIShellScaleN Y r)
        (classicalTypeIShellScaleCoeff A sigma r) t‖ := by
    simpa only [hq, Sum.elim_inl] using hLarge
  by_cases hs : (classicalTypeIShellScalePair r).2 = 0
  · have hCoeff : classicalTypeIShellScaleCoeff A sigma r =
        conjugateCoeffs (classicalZetaLongLineCoeff A sigma) := by
      funext n
      simp [classicalTypeIShellScaleCoeff, signedClassicalLongCoeff, hs]
    have hSign : classicalBinaryShellScaleSign q = 0 := by
      simp only [classicalBinaryShellScaleSign, hq, Sum.elim_inl, hs]
    rw [hCoeff, norm_sourceDirichletPoly_conjugateCoeffs] at hRaw
    simpa [classicalBinaryOrientedOrdinate, hSign] using hRaw
  · have hsOne : (classicalTypeIShellScalePair r).2 = 1 := by
      apply Fin.eq_of_val_eq
      have hlt := (classicalTypeIShellScalePair r).2.isLt
      have hne : (classicalTypeIShellScalePair r).2.val ≠ 0 := by
        intro hz
        apply hs
        apply Fin.eq_of_val_eq
        simpa using hz
      omega
    have hCoeff : classicalTypeIShellScaleCoeff A sigma r =
        classicalZetaLongLineCoeff A sigma := by
      funext n
      simp [classicalTypeIShellScaleCoeff, signedClassicalLongCoeff, hsOne]
    have hSign : classicalBinaryShellScaleSign q ≠ 0 := by
      simpa only [classicalBinaryShellScaleSign, hq, Sum.elim_inl] using hs
    rw [hCoeff] at hRaw
    simpa [classicalBinaryOrientedOrdinate, hSign,
      dirichletPoly_neg_eq_sourceDirichletPoly] using hRaw

/-- Every member of an oriented fixed-label Type-I family is a large value of
the actual frozen classical coefficient sequence. -/
theorem classicalTypeIShellScaleLarge_on_orientedFamily
    {A Y X kI kII : Nat} {sigma q0 : Real}
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kI * 2)) (hq : binaryScaleLabel q = Sum.inl r)
    (W : Finset Real)
    (hLarge : ∀ t ∈ W, Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel q) t) :
    ∀ s ∈ classicalBinaryOrientedFamily q W,
      ((3 / 4 : Real) * (q0 / 2)) / (kI : Real) ≤
        ‖dirichletPoly (classicalTypeIShellScaleN Y r)
          (classicalZetaLongLineCoeff A sigma) s‖ := by
  intro s hs
  rw [classicalBinaryOrientedFamily, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact classicalTypeIShellScaleLarge_oriented q r hq (hLarge t ht)

/-- Exact finite contradiction eliminating a Type-I block in the medium
physical range once the two explicit threshold comparisons have been
established. -/
theorem classicalTypeIShellScaleLarge_false_of_terminal_medium
    {A Y X kI kII : Nat} {sigma q0 t : Real}
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kI * 2)) (hq : binaryScaleLabel q = Sum.inl r)
    (hSigma : 0 ≤ sigma)
    (hN : 0 < classicalTypeIShellScaleN Y r)
    (hNA : classicalTypeIShellScaleN Y r < A)
    (hOne : 1 ≤ classicalBinaryOrientedOrdinate q t)
    (hSquare : classicalBinaryOrientedOrdinate q t ≤
      (classicalTypeIShellScaleN Y r : Real) ^ 2)
    (hTerminal :
      (classicalTypeIShellScaleN Y r + 1 : Real) ^ (-sigma) *
          (6 * Real.pi * (classicalTypeIShellScaleN Y r : Real) /
            classicalBinaryOrientedOrdinate q t) <
        ((3 / 4 : Real) * (q0 / 2)) / (kI : Real))
    (hMedium :
      (classicalTypeIShellScaleN Y r + 1 : Real) ^ (-sigma) *
          (100 * Real.sqrt (classicalBinaryOrientedOrdinate q t)) <
        ((3 / 4 : Real) * (q0 / 2)) / (kI : Real))
    (hLarge : Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel q) t) : False := by
  let N := classicalTypeIShellScaleN Y r
  let s := classicalBinaryOrientedOrdinate q t
  let L := ((3 / 4 : Real) * (q0 / 2)) / (kI : Real)
  have hLarge' : L ≤ ‖dirichletPoly N
      (classicalZetaLongLineCoeff A sigma) s‖ := by
    simpa only [L, N, s] using
      classicalTypeIShellScaleLarge_oriented q r hq hLarge
  have hNs : (N : Real) < s :=
    typeI_scale_lt_height_of_large A N sigma s L hSigma hN hNA hOne
      hLarge' (by simpa only [L, N, s] using hTerminal)
  exact mediumTypeILargeValue_false A N sigma s L hSigma hN hNA
    hNs.le (by simpa only [N, s] using hSquare)
    (by simpa only [L, N, s] using hMedium) hLarge'

#print axioms classicalBinaryOrientedOrdinate_mem_physical_interval
#print axioms card_classicalBinaryOrientedFamily
#print axioms isSeparated_classicalBinaryOrientedFamily
#print axioms classicalBinaryOrientedFamily_in_physical_interval
#print axioms classicalBinaryOrientedFamily_inBaseInterval
#print axioms classicalTypeIShellScaleLarge_oriented
#print axioms classicalTypeIShellScaleLarge_on_orientedFamily
#print axioms classicalTypeIShellScaleLarge_false_of_terminal_medium

end

end GafniTao
