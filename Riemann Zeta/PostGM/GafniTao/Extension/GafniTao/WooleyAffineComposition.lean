import GafniTao.WooleySection7LocalIdentity

/-!
# Composition of source affine pullbacks

This is the exact reindexing used between (7.19) and (7.20).  Refining the
parameter `y` modulo `h` after writing `n = q*y + xi` is the same as writing
`n = (q*h)*z + (q*zeta+xi)` in one step.
-/

namespace GafniTao

noncomputable section

theorem wooleyAffinePullback_comp
    (gamma : WooleySourceSequence) (q h : ℕ)
    (hq : 0 < q) (hh : 0 < h) (xi zeta : ℤ) :
    wooleyAffinePullback (wooleyAffinePullback gamma q hq xi)
        h hh zeta =
      wooleyAffinePullback gamma (q * h) (Nat.mul_pos hq hh)
        ((q : ℤ) * zeta + xi) := by
  ext y
  simp only [wooleyAffinePullback_apply]
  congr 1
  push_cast
  ring

theorem wooleyAffinePolynomialSystem_comp {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q h : ℕ) (xi zeta : ℤ) :
    wooleyAffinePolynomialSystem
        (wooleyAffinePolynomialSystem phi q xi) h zeta =
      wooleyAffinePolynomialSystem phi (q * h)
        ((q : ℤ) * zeta + xi) := by
  funext j
  apply Polynomial.funext
  intro y
  simp only [wooleyAffinePolynomialSystem_eval]
  push_cast
  congr 1
  ring

/-- Mass identity in the line following equation (7.19). -/
theorem wooleySourceResidueMassSq_affinePullback
    (gamma : WooleySourceSequence) (q h : ℕ)
    (hq : 0 < q) (hh : 0 < h) (xi zeta : ℤ) :
    wooleySourceResidueMassSq (wooleyAffinePullback gamma q hq xi)
        h (zeta : ZMod h) =
      wooleySourceResidueMassSq gamma (q * h)
        ((((q : ℤ) * zeta + xi : ℤ)) : ZMod (q * h)) := by
  rw [← wooleySourceMassSq_affinePullback
      (wooleyAffinePullback gamma q hq xi) h hh zeta,
    wooleyAffinePullback_comp,
    wooleySourceMassSq_affinePullback]

/-- Normalized phase-sum identity underlying equation (7.21). -/
theorem wooleySourceNormalizedPolynomialResidueSum_affinePullback
    {k qB : ℕ} [NeZero qB]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod qB) (q h : ℕ)
    (hq : 0 < q) (hh : 0 < h) (xi zeta : ℤ) :
    wooleySourceNormalizedPolynomialResidueSum
        (wooleyAffinePolynomialSystem phi q xi)
        (wooleyAffinePullback gamma q hq xi) alpha (zeta : ZMod h) =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        ((((q : ℤ) * zeta + xi : ℤ)) : ZMod (q * h)) := by
  calc
    wooleySourceNormalizedPolynomialResidueSum
        (wooleyAffinePolynomialSystem phi q xi)
        (wooleyAffinePullback gamma q hq xi) alpha (zeta : ZMod h) =
      wooleySourceNormalizedPolynomialSum
        (wooleyAffinePolynomialSystem
          (wooleyAffinePolynomialSystem phi q xi) h zeta)
        (wooleyAffinePullback (wooleyAffinePullback gamma q hq xi)
          h hh zeta) alpha := by
            symm
            exact wooleySourceNormalizedPolynomialSum_affinePullback
              hh _ _ _ _
    _ = wooleySourceNormalizedPolynomialSum
        (wooleyAffinePolynomialSystem phi (q * h)
          ((q : ℤ) * zeta + xi))
        (wooleyAffinePullback gamma (q * h) (Nat.mul_pos hq hh)
          ((q : ℤ) * zeta + xi)) alpha := by
            rw [wooleyAffinePolynomialSystem_comp,
              wooleyAffinePullback_comp]
    _ = wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        ((((q : ℤ) * zeta + xi : ℤ)) : ZMod (q * h)) :=
      wooleySourceNormalizedPolynomialSum_affinePullback
        (Nat.mul_pos hq hh) phi gamma alpha _

/-- Restricting a twisted sequence to a residue class is exactly the twist
of the restricted sequence.  This is the coefficient identity used when
the sequence `c(alpha)` in (7.19) is replaced by `c'(alpha)` in (7.21). -/
theorem wooleySourceResidueSequence_twist
    (gamma : WooleySourceSequence) (phase : ℤ → ℂ)
    (h : ℕ) (zeta : ZMod h) :
    wooleySourceResidueSequence (wooleySourceTwist gamma phase) h zeta =
      wooleySourceTwist (wooleySourceResidueSequence gamma h zeta) phase := by
  ext n
  simp only [wooleySourceResidueSequence_apply, wooleySourceTwist_apply]
  by_cases hn : (n : ZMod h) = zeta <;> simp [hn]

/-- The residue mass in a polynomially twisted source sequence is unchanged. -/
theorem wooleySourceResidueMassSq_polynomialTwist
    {k q : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (h : ℕ) (zeta : ZMod h) :
    wooleySourceResidueMassSq
        (wooleySourceTwist gamma
          (fun n => wooleySourcePolynomialPhase phi alpha n)) h zeta =
      wooleySourceResidueMassSq gamma h zeta := by
  exact wooleySourceResidueMassSq_twist gamma _
    (wooleySourcePolynomialPhase_norm phi alpha) h zeta

#print axioms wooleyAffinePullback_comp
#print axioms wooleyAffinePolynomialSystem_comp
#print axioms wooleySourceResidueMassSq_affinePullback
#print axioms wooleySourceNormalizedPolynomialResidueSum_affinePullback
#print axioms wooleySourceResidueSequence_twist
#print axioms wooleySourceResidueMassSq_polynomialTwist

end

end GafniTao
