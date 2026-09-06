import GafniTao.ClassicalBinaryHeathBrownFamily

/-!
# The retained Type-I long tail on an oriented detector colour

The pointwise classical detector first obtains a large value of the complete
zeta long tail and only then chooses a dyadic sharp block.  Four-zero energy
cannot discard that earlier fact: the four coordinates must be coloured before
the subsequent source-scale extraction.  This module exposes the retained
long-tail statement on the fixed-colour positive-ordinate family and records
that the fixed sign orientation preserves additive energy exactly.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Reflection by the sign attached to one fixed detector label preserves the
tolerance-one additive energy exactly. -/
theorem approxAddEnergy_classicalBinaryOrientedFamily
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)) (W : Finset Real) :
    ApproxAddEnergy 1 (classicalBinaryOrientedFamily q W) =
      ApproxAddEnergy 1 W := by
  by_cases hs : classicalBinaryShellScaleSign q = 0
  · have hFamily : classicalBinaryOrientedFamily q W = W := by
      ext t
      simp [classicalBinaryOrientedFamily, classicalBinaryOrientedOrdinate,
        hs]
    rw [hFamily]
  · have hFamily : classicalBinaryOrientedFamily q W = gmScale (-1) W := by
      ext t
      simp [classicalBinaryOrientedFamily, classicalBinaryOrientedOrdinate,
        gmScale, hs]
    rw [hFamily]
    simpa only [abs_neg, abs_one, one_mul] using
      approxAddEnergy_scale 1 (-1) (by norm_num) W

/-- On a Type-I detector colour, every member of the oriented family retains
the complete long-tail lower bound that preceded the sharp dyadic selection. -/
theorem classicalBinaryColorFamily_longTail_on_oriented
    {sigma U delta q0 : Real} {Y X A : Nat}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (r : Fin (d.kI * 2))
    (hlabel : binaryScaleLabel label.1 = Sum.inl r) :
    ∀ s ∈ classicalBinaryOrientedFamily label.1
        (classicalBinaryColorFamily d label),
      (3 / 4) * (q0 / 2) ≤
        ‖classicalZetaLongTail Y A
          ((sigma : Complex) + Complex.I * (s : Complex))‖ := by
  intro s hs
  rw [classicalBinaryOrientedFamily, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [classicalBinaryColorFamily, Finset.mem_image] at ht
  obtain ⟨rho, hrho, rfl⟩ := ht
  have hm := Finset.mem_filter.mp hrho
  have hscale : d.scale rho = label.1 := congrArg Prod.fst hm.2
  have hLong := d.hLong rho hm.1 r (by simpa only [hscale] using hlabel)
  simpa only [classicalBinaryOrientedOrdinate, hscale] using hLong

#print axioms approxAddEnergy_classicalBinaryOrientedFamily
#print axioms classicalBinaryColorFamily_longTail_on_oriented

end

end GafniTao
