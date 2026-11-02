# LCAnalysis

Differential and integral calculus on locally convex spaces (Michal–Bastiani calculus), formalized in Lean 4 on top of Mathlib.

* `LCAnalysis/MichalBastiani.lean`: directional derivatives, `C^k` maps, weak Riemann integral, fundamental theorem, mean value inclusion, chain rule, partial derivatives, symmetry of the second derivative.
* `LCAnalysis/Higher.lean`: higher differentials `d^(k) f`; the recursive definition of `C^k` agrees with Bastiani–Neeb's (Glöckner–Neeb, Prop. 1.3.10); `d^(k) f` is `C^{r-k}` (Remark 1.3.13); Schwarz's theorem: `d^(k) f (x, ·)` is a continuous symmetric `k`-linear map (Prop. 1.3.17).
* `LCAnalysis/Rules.lean`: continuous bilinear maps are smooth; product rule; Taylor's formula with integral remainder (weak form).
* `LCAnalysis/Integral.lean`: weak integrals of curves; mean value inclusion; continuity of parameter-dependent integrals; differentiation under the integral sign.
* `LCAnalysis/IntegralExistence.lean`: sequentially complete and Mackey complete spaces; weak integrals of continuous curves exist in sequentially complete spaces, and of `C^1` curves in Mackey complete spaces (limits of dyadic Riemann sums); parameter-dependent integrals of `C^k` maps are `C^k` (sequentially complete) or `C^{k-1}` (Mackey complete; smooth ⇒ smooth), with no existence hypotheses.
* `LCAnalysis/MBFrechet.lean`: for normed spaces, MB `C^{k+1}` ⇒ Fréchet `C^k`, and MB smooth ⇔ Fréchet smooth.

References: Neeb, arXiv:1501.06269; Glöckner–Neeb, arXiv:2602.12362.
