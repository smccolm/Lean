import RiemannZeta.HardyZ
import RiemannZeta.Nonvanishing
import RiemannZeta.CompletedZetaSymmetry
import RiemannZeta.FiniteDirichletPolynomial
import RiemannZeta.CrossNormProduct

import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.Statements
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.SymmetryTransfer
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.BetaDependence
import RiemannZeta.GuthMaynard.Transfer
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.InghamBound
import RiemannZeta.GuthMaynard.DensityReduction

open RiemannZeta
open RiemannZeta.GuthMaynard

-- Finite Dirichlet Polynomial Declarations (6)

#print axioms dirichletPoly_conj
#print axioms dirichletPoly_norm_conj
#print axioms dirichletNormSquare_conj_line
#print axioms threshold_conj_line_iff
#print axioms dirichletPoly_zero_conj
#print axioms dirichletPoly_zero_conj_iff

-- Cross-Norm Product Declarations (7)
#print axioms crossNormProduct_nonneg
#print axioms conjCoeff_conjCoeff
#print axioms crossNormProduct_swap
#print axioms realPart_abs_le_crossNormProduct
#print axioms crossNormProduct_eq_zero_of_left
#print axioms crossNormProduct_eq_zero_of_right
#print axioms crossNormProduct_eq_zero_iff

-- Completed Zeta Symmetry Declarations (3)
#print axioms completedRiemannZeta_reflection
#print axioms completedRiemannZeta_zero_reflection_iff
#print axioms completedRiemannZeta_fourfold_zero_orbit

-- Complex Hardy-Type Normalization Declarations (3)
#print axioms hardyZ_norm_eq_riemannZeta_norm
#print axioms hardyZ_zero_iff_riemannZeta_zero
#print axioms hardyZ_neg_norm

-- Non-Vanishing Declarations (2)
#print axioms riemannZeta_ne_zero_on_one_line
#print axioms riemannZeta_ne_zero_totalized

-- Guth-Maynard Infrastructure and Statements

-- Asymptotics
#print axioms EpsilonPowerBound
#print axioms EpsilonPowerBound.refl
#print axioms EpsilonPowerBound.trans

-- Separated Sets
#print axioms IsSeparated
#print axioms InTargetInterval
#print axioms InBaseInterval
#print axioms translateSet
#print axioms isSeparated_translate
#print axioms inBaseInterval_translate

-- Statements
#print axioms GuthMaynardLargeValues
#print axioms GuthMaynardZeroDensity
#print axioms CombinedZeroDensity

-- Zero Count Interface
#print axioms ZetaZeroCountModel
#print axioms zerosInRect
#print axioms zeroCountRect
#print axioms N
#print axioms DyadicReductionProp
#print axioms ExtractSeparatedHypothesis

-- Symmetry Transfer
#print axioms FunctionalSymmetryHypothesis

-- Density Reduction
#print axioms SymmetricDensityReductionProp

-- Exponent Arithmetic
#print axioms denom_pos
#print axioms alpha
#print axioms final_exponent
#print axioms exists_k_bound

-- Zero Detector
#print axioms ZeroDetectorModel
#print axioms detectPoly
#print axioms IsTypeIZero
#print axioms IsTypeIIZero
#print axioms TypeIIBoundHypothesis

-- Beta Dependence
#print axioms BetaDependenceRemovalHypothesis

-- Transfer Theorem
#print axioms MeanValueHypothesis
#print axioms ConditionalZeroDensityTransfer

-- Polynomial Powers
#print axioms PolynomialPowerModel

-- Ingham Bound
#print axioms InghamZeroDensity
#print axioms CombinedZeroDensityTransfer
#print axioms NormalizedCoeffsBoundHypothesis
