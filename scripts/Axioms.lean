/-
Prints the axioms used by the main theorems of LCAnalysis.
Run with `lake env lean scripts/Axioms.lean`; every line should read
`[propext, Classical.choice, Quot.sound]` (the standard axioms of Lean and Mathlib).
-/
import LCAnalysis

open LCAnalysis

-- First-order calculus (`MichalBastiani.lean`)
#print axioms ContDiffMBOn.exists_clm
#print axioms ContDiffMBOn.integral_dMB
#print axioms sub_mem_of_hasDirDerivAt
#print axioms ContDiffMBOn.comp
#print axioms contDiffMBOn_one_of_partials
#print axioms ContDiffMBOn.dMB_dMB_symm
#print axioms ContDiffOn.contDiffMBOn
-- Higher differentials (`Higher.lean`)
#print axioms contDiffMBOn_iff_hasContIterDerivOn
#print axioms ContDiffMBOn.contDiffMBOn_iteratedDMB
#print axioms ContDiffMBOn.iteratedDMB_perm
#print axioms ContDiffMBOn.exists_iteratedDMB_multilinear
-- Rules (`Rules.lean`)
#print axioms contDiffMBOn_bilin
#print axioms ContDiffMBOn.dMB_bilin
#print axioms ContDiffMBOn.taylor
-- Comparison with Fréchet calculus (`MBFrechet.lean`)
#print axioms ContDiffMBOn.contDiffOn
#print axioms smoothMBOn_iff_contDiffOn
-- Weak integrals (`Integral.lean`, `IntegralExistence.lean`, `FundamentalTheorem.lean`)
#print axioms HasWeakIntegral.mem_smul
#print axioms hasDirDerivAt_weakIntegral
#print axioms exists_hasWeakIntegral
#print axioms ContDiffMBOn.exists_hasWeakIntegral
#print axioms ContDiffMBOn.contDiffMBOn_weakIntegral
#print axioms ContDiffMBOn.contDiffMBOn_weakIntegral_of_mackey
#print axioms SmoothMBOn.smoothMBOn_weakIntegral
#print axioms ContDiffMBOn.dMB_weakIntegral
#print axioms hasWeakIntegral_comp_smul_deriv_iff
#print axioms hasWeakIntegral_sub_of_hasDirDerivAt
#print axioms ContDiffMBOn.hasWeakIntegral_dMB
#print axioms hasDirDerivAt_weakIntegral_right_of_exists
#print axioms hasDirDerivAt_weakIntegral_right
-- Mackey completeness through Lipschitz curves (`MackeyLipschitz.lean`)
#print axioms MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve
#print axioms MackeyComplete.of_integratesLipschitzCurves
#print axioms mackeyComplete_iff_integratesLipschitzCurves
#print axioms LCAnalysis.exists_uniform_isSprayCurveOn_of_norm_le
#print axioms LCAnalysis.IsSprayCurveOn.eqOn_Ioo
#print axioms MultilinearMap.polarization
#print axioms LCAnalysis.isContHomPoly_iff_continuous
#print axioms LCAnalysis.cAnalyticOn_iff_smoothMBOn
#print axioms LCAnalysis.CAnalyticOn.hasPowerSeriesOnDisc
#print axioms LCAnalysis.tfae_complexAnalyticOn
#print axioms LCAnalysis.ComplexAnalyticOn.smoothMBOn
