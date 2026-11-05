/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCAnalysis.ComplexAnalytic

/-! # Series of homogeneous polynomials

Pointwise convergence of a series `∑ pₙ` of continuous homogeneous polynomials between complex
topological vector spaces, after Bochnak and Siciak, *Analytic functions in topological vector
spaces*, Studia Math. 39 (1971), 77–112 (part II, §5). Bochnak and Siciak assume throughout
that `F` is locally convex and sequentially complete; the results below need neither
completeness nor, for the Baire lemma, local convexity of `F`.

## Main results

* `IsContHomPoly.seminorm_le_of_shift`: a bound `q (p (c + w)) ≤ M` on a balanced set `W`
  gives `q (p w) ≤ M` on `W`. This is a sharp complex form of Bochnak–Siciak, *Polynomials and
  multilinear mappings in topological vector spaces*, Studia Math. 39 (1971), 59–76, Lemma 2
  (ii), which over `ℝ` or `ℂ` gives the bound on `(2e)⁻¹ W`.
* `exists_nhds_geometric_bound`: over a complex **Baire** space `E`, if `∑ pₙ` converges on an
  absorbing set, then for each continuous seminorm `q` and each `θ > 0` the terms satisfy
  `q (pₙ w) ≤ C θⁿ` on a `0`-neighbourhood (Bochnak–Siciak II, Proposition 5.2, 1°: normal
  convergence at zero).
* `continuousAt_zero_of_tendsto_sum`: over a Baire space, the sum of a series converging on a
  `0`-neighbourhood is continuous at `0` (Bochnak–Siciak II, Proposition 5.2, 2°).

## Counterexamples

* **`E` not Baire** (Bochnak–Siciak II, Counterexample 5.1). On the finitely supported
  sequences with the norm of `ℓ²` (`finSeq`), `∑ (n xₙ)ⁿ` converges everywhere but its sum is
  not continuous at `0` (`not_continuousAt_bsSum`); in particular `finSeq` is not a Baire space
  (`not_baireSpace_finSeq`).
* **`F` not complete, one variable.** In `F = span {eₙ, (zⁿ)ₙ : ‖z‖ < 1} ⊆ ℓ²` (`geomSpan`),
  the power series `∑ zⁿ eₙ` converges on the whole unit disc (`hasPowerSeriesOnDisc_geomFun`),
  but its sum has no complex derivative at `1/2` (`not_hasCDerivAt_geomFun`), so it is not
  complex analytic on the disc (`not_cAnalyticOn_geomFun`). The derivative in `ℓ²` would be
  `∑ n 2^{1-n} eₙ`, whose coordinates are not eventually an exponential sum
  (`not_eventually_affine_eq_expSum`). Hence a disc of convergence need not be a disc of
  analyticity when `F` is incomplete: by `HasPowerSeriesOnDisc.hasCDerivAt_iff`, the derivative
  off the centre exists exactly when the derived series converges in `F`, and here it does
  not.

## Not formalized

Bochnak–Siciak II, Theorem 5.2 (over a Baire space, the sum of a series converging on an open
set `H` is analytic on `H`) needs, beyond Proposition 5.2, the propagation of the bounds from
`0` to the other points of `H`. Bochnak and Siciak obtain it from Siciak's polynomial lemma
(§4, Proposition 4.1), which rests on potential theory in `ℂ` (Siciak's extremal function,
Fekete points, regularity for the Dirichlet problem). It is not formalized here. The real
counterpart (Proposition 5.4) uses the same lemma.
-/

open Set Filter Function Metric Finset
open scoped Topology Real Pointwise

noncomputable section

namespace LCAnalysis

/-! ### Moving the centre of a bound (Bochnak–Siciak) -/

section Shift

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] {n : ℕ} {p : E → F}

/-- Averaging a homogeneous polynomial over a circle of roots of unity: with `m = n + 1` and
`ω = e^{2πi/m}`, `∑_{j < m} p (ωʲ c + w) = m • p w`. -/
theorem IsContHomPoly.sum_rootsOfUnity (hp : IsContHomPoly ℂ n p) (c w : E) :
    ∑ j ∈ range (n + 1), p (Complex.exp (2 * π * Complex.I / (n + 1 : ℕ)) ^ j • c + w) =
      ((n + 1 : ℕ) : ℂ) • p w := by
  classical
  obtain ⟨A, hA⟩ := hp
  set m := n + 1 with hm
  set ω := Complex.exp (2 * π * Complex.I / (m : ℕ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  set b : Finset (Fin n) → F := fun S ↦ A (S.piecewise (fun _ ↦ c) (fun _ ↦ w))
  have hexp : ∀ j : ℕ, p (ω ^ j • c + w) = ∑ S : Finset (Fin n), (ω ^ j) ^ S.card • b S := by
    intro j
    rw [hA]
    have e1 : (fun _ : Fin n ↦ ω ^ j • c + w) = (fun _ ↦ ω ^ j • c) + (fun _ ↦ w) := rfl
    rw [e1, A.map_add_univ]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have e2 : S.piecewise (fun _ : Fin n ↦ ω ^ j • c) (fun _ ↦ w) =
        S.piecewise (fun i ↦ (fun _ ↦ ω ^ j) i • (S.piecewise (fun _ ↦ c) (fun _ ↦ w)) i)
          (S.piecewise (fun _ ↦ c) (fun _ ↦ w)) := by
      ext i; by_cases hi : i ∈ S <;> simp [hi]
    rw [e2, A.map_piecewise_smul, Finset.prod_const]
  have hgeom : ∀ k ≤ n, ∑ j ∈ range m, (ω ^ j) ^ k = if k = 0 then (m : ℂ) else 0 := by
    intro k hk
    have e : ∀ j, (ω ^ j) ^ k = (ω ^ k) ^ j := fun j ↦ by rw [← pow_mul, ← pow_mul, mul_comm]
    simp only [e]
    split_ifs with hk0
    · subst hk0; simp
    · have hne : ω ^ k ≠ 1 := by
        rw [Ne, hω.pow_eq_one_iff_dvd]
        exact fun h ↦ hk0 (Nat.eq_zero_of_dvd_of_lt h (by omega))
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  calc ∑ j ∈ range m, p (ω ^ j • c + w)
      = ∑ S : Finset (Fin n), (∑ j ∈ range m, (ω ^ j) ^ S.card) • b S := by
        simp only [hexp, Finset.sum_smul]; exact Finset.sum_comm
    _ = (m : ℂ) • b ∅ := by
        rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
        · rw [Finset.card_empty, hgeom 0 (Nat.zero_le _)]; simp
        · intro S _ hS
          have hc : S.card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
          rw [hgeom S.card ((Finset.card_le_univ S).trans (by simp))]; simp [hc]
        · simp
    _ = (m : ℂ) • p w := by simp [b, hA]

/-- **Moving the centre of a bound** (Bochnak–Siciak, *Studia Math.* 39 (1971), Lemma 2 of
part I, used in the proof of Proposition 5.2 of part II): if a continuous homogeneous
polynomial satisfies `q (p (c + w)) ≤ M` on a balanced set `W`, then `q (p w) ≤ M` on `W`.
Only the algebraic structure of `p` is used, through `IsContHomPoly.sum_rootsOfUnity`. -/
theorem IsContHomPoly.seminorm_le_of_shift (hp : IsContHomPoly ℂ n p) (q : Seminorm ℂ F)
    {W : Set E} (hW : Balanced ℂ W) {c : E} {M : ℝ} (h : ∀ w ∈ W, q (p (c + w)) ≤ M) {w : E}
    (hw : w ∈ W) : q (p w) ≤ M := by
  set m := n + 1
  set ω := Complex.exp (2 * π * Complex.I / (m : ℕ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one (by omega)
  have hterm : ∀ j : ℕ, q (p (ω ^ j • c + w)) ≤ M := by
    intro j
    have hj : ω ^ j ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hω1]; exact one_ne_zero)
    have e : ω ^ j • c + w = ω ^ j • (c + (ω ^ j)⁻¹ • w) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hj, one_smul]
    have hw' : (ω ^ j)⁻¹ • w ∈ W := hW.smul_mem (by simp [norm_pow, hω1]) hw
    rw [e, hp.map_smul, map_smul_eq_mul, norm_pow, norm_pow, hω1]
    simp only [one_pow, one_mul]
    exact h _ hw'
  have hm0 : (0 : ℝ) < m := by positivity
  have key : (m : ℝ) * q (p w) ≤ m * M := by
    have h1 : q (((m : ℕ) : ℂ) • p w) = m * q (p w) := by
      rw [map_smul_eq_mul, Complex.norm_natCast]
    rw [← h1, ← hp.sum_rootsOfUnity c w]
    calc q (∑ j ∈ range m, p (ω ^ j • c + w)) ≤ ∑ j ∈ range m, q (p (ω ^ j • c + w)) :=
          Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑ _j ∈ range m, M := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = m * M := by simp
  exact le_of_mul_le_mul_left key hm0

end Shift

/-! ### Normal convergence at zero over a Baire space (Bochnak–Siciak, Proposition 5.2) -/

section Baire

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  {p : ℕ → E → F}

omit [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] in
/-- If `∑ pₙ (a)` converges, the terms are bounded for each continuous seminorm. -/
theorem exists_bound_of_tendsto_sum [IsTopologicalAddGroup F] {q : Seminorm ℂ F}
    (hq : Continuous q) {a : E} {y : F}
    (h : Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y)) :
    ∃ C, 0 ≤ C ∧ ∀ n, q (p n a) ≤ C := by
  have h0 : Tendsto (fun n ↦ p n a) atTop (𝓝 0) := by
    have h2 := (h.comp (tendsto_add_atTop_nat 1)).sub h
    rw [sub_self] at h2
    exact h2.congr fun n ↦ by simp [Finset.sum_range_succ]
  have ht := (hq.tendsto 0).comp h0
  rw [map_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  exact ⟨C, (apply_nonneg q _).trans (hC ⟨0, rfl⟩), fun n ↦ hC ⟨n, rfl⟩⟩

/-- **Normal convergence at zero** (Bochnak–Siciak, *Studia Math.* 39 (1971), part II,
Proposition 5.2, 1°). Let `E` be a complex Baire space and let `pₙ` be continuous homogeneous
polynomials of degree `n` such that `∑ pₙ (a)` converges for every `a` in an absorbing set `A`.
Then for every continuous seminorm `q` on `F` and every `θ > 0` there are a `0`-neighbourhood
`W` and `C` with `q (pₙ w) ≤ C θⁿ` for all `n` and `w ∈ W`. No completeness of `F` is needed,
and `F` need not be locally convex. -/
theorem exists_nhds_geometric_bound [BaireSpace E] [IsTopologicalAddGroup F]
    (hp : ∀ n, IsContHomPoly ℂ n (p n)) {A : Set E} (hA : Absorbent ℂ A)
    (hconv : ∀ a ∈ A, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y))
    {q : Seminorm ℂ F} (hq : Continuous q) {θ : ℝ} (hθ : 0 < θ) :
    ∃ W ∈ 𝓝 (0 : E), ∃ C, ∀ n, ∀ w ∈ W, q (p n w) ≤ C * θ ^ n := by
  -- pointwise geometric bounds on all of `E`
  have hpt : ∀ x : E, ∃ N k : ℕ, ∀ n, q (p n x) ≤ N * (k : ℝ) ^ n := by
    intro x
    obtain ⟨r, hr, hrA⟩ := (hA x).exists_pos
    obtain ⟨a, ha, hxa⟩ := hrA (r : ℂ) (by simp [abs_of_pos hr]) (mem_singleton x)
    obtain ⟨y, hy⟩ := hconv a ha
    obtain ⟨C, hC0, hC⟩ := exists_bound_of_tendsto_sum hq hy
    refine ⟨⌈C⌉₊, ⌈r⌉₊, fun n ↦ ?_⟩
    rw [← hxa, (hp n).map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    calc r ^ n * q (p n a) ≤ (⌈r⌉₊ : ℝ) ^ n * ⌈C⌉₊ :=
          mul_le_mul (pow_le_pow_left₀ hr.le (Nat.le_ceil r) n) ((hC n).trans (Nat.le_ceil C))
            (apply_nonneg _ _) (by positivity)
      _ = _ := by ring
  -- Baire
  set K : ℕ × ℕ → Set E := fun i ↦ {x | ∀ n, q (p n x) ≤ i.1 * (i.2 : ℝ) ^ n}
  have hKc : ∀ i, IsClosed (K i) := fun i ↦ by
    simp only [K, Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_le (hq.comp (hp n).continuous) continuous_const
  have hKU : ⋃ i, K i = Set.univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨N, k, h⟩ := hpt x
    exact mem_iUnion.2 ⟨(N, k), by simpa [K] using h⟩
  obtain ⟨⟨N, k⟩, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hKc hKU
  have hnhds : {w : E | x₀ + w ∈ K (N, k)} ∈ 𝓝 (0 : E) := by
    have h1 : Tendsto (fun w : E ↦ x₀ + w) (𝓝 0) (𝓝 x₀) := by
      simpa using (tendsto_const_nhds (x := x₀)).add (tendsto_id (x := 𝓝 (0 : E)))
    exact h1 (mem_interior_iff_mem_nhds.1 hx₀)
  set B := balancedCore ℂ {w : E | x₀ + w ∈ K (N, k)}
  have hB : B ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hnhds
  -- the bound on `x₀ + B` moves to `B`
  have hB' : ∀ n, ∀ w ∈ B, q (p n w) ≤ N * ((k + 1 : ℕ) : ℝ) ^ n := fun n w hw ↦ by
    refine ((hp n).seminorm_le_of_shift q (balancedCore.balanced _)
      (fun v hv ↦ (balancedCore_subset _ hv : v ∈ {w : E | x₀ + w ∈ K (N, k)}) n) hw).trans ?_
    gcongr; exact_mod_cast Nat.le_succ k
  -- rescale
  set s : ℝ := θ / (k + 1 : ℕ)
  have hs : 0 < s := by positivity
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨(s : ℂ) • B, (set_smul_mem_nhds_zero_iff hs0).2 hB, N, fun n w hw ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := hw
  rw [(hp n).map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc s ^ n * q (p n b) ≤ s ^ n * (N * ((k + 1 : ℕ) : ℝ) ^ n) := by gcongr; exact hB' n b hb
    _ = N * θ ^ n := by
        simp only [s, div_pow]
        field_simp

/-- **Continuity at zero** (Bochnak–Siciak, part II, Proposition 5.2, 2°): over a complex Baire
space, the sum of a series of continuous homogeneous polynomials converging on a
`0`-neighbourhood is continuous at `0`. No completeness of `F` is needed. -/
theorem continuousAt_zero_of_tendsto_sum [BaireSpace E] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] (hp : ∀ n, IsContHomPoly ℂ n (p n)) {U : Set E} (hU : U ∈ 𝓝 0)
    {f : E → F} (hf : ∀ x ∈ U, Tendsto (fun N ↦ ∑ n ∈ range N, p n x) atTop (𝓝 (f x))) :
    ContinuousAt f 0 := by
  refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
  obtain ⟨W, hW, C, hC⟩ := exists_nhds_geometric_bound hp (absorbent_nhds_zero hU)
    (fun a ha ↦ ⟨f a, hf a ha⟩) hq (by norm_num : (0 : ℝ) < 1 / 2)
  have hC0 : 0 ≤ C := by
    have := hC 0 0 (mem_of_mem_nhds hW)
    simpa using (apply_nonneg q _).trans this
  -- tail estimate
  have htail : ∀ x ∈ U ∩ W, ∀ K, q (f x - ∑ n ∈ range K, p n x) ≤ 2 * C * (1 / 2) ^ K := by
    intro x hx K
    have hlim : Tendsto (fun N ↦ q (∑ n ∈ range N, p n x - ∑ n ∈ range K, p n x)) atTop
        (𝓝 (q (f x - ∑ n ∈ range K, p n x))) :=
      (hq.tendsto _).comp ((hf x hx.1).sub_const _)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨K, fun N hN ↦ ?_⟩)
    rw [← Finset.sum_range_add_sum_Ico _ hN, add_sub_cancel_left]
    calc q (∑ n ∈ Ico K N, p n x) ≤ ∑ n ∈ Ico K N, q (p n x) :=
          Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑ n ∈ Ico K N, C * (1 / 2) ^ n := Finset.sum_le_sum fun n _ ↦ hC n x hx.2
      _ ≤ 2 * C * (1 / 2) ^ K := by
          rw [← Finset.mul_sum]
          have : ∑ n ∈ Ico K N, ((1 : ℝ) / 2) ^ n ≤ 2 * (1 / 2) ^ K := by
            rw [Finset.sum_Ico_eq_sum_range]
            simp only [pow_add, ← Finset.mul_sum]
            have hg : ∑ i ∈ range (N - K), ((1 : ℝ) / 2) ^ i ≤ 2 := by
              have := sum_geometric_two_le (N - K)
              simpa [one_div] using this
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) K]
          nlinarith
  -- choose `K` with a small tail
  obtain ⟨K, hK⟩ : ∃ K, 2 * C * (1 / 2) ^ K < ε / 3 := by
    have ht : Tendsto (fun K ↦ 2 * C * ((1 : ℝ) / 2) ^ K) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (2 * C)
    exact (ht.eventually (gt_mem_nhds (by positivity))).exists
  -- the partial sum is continuous
  have hSc : Continuous fun x ↦ ∑ n ∈ range K, p n x :=
    continuous_finsetSum _ fun n _ ↦ (hp n).continuous
  have hS : ∀ᶠ x in 𝓝 0, q (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) < ε / 3 := by
    have := (hq.tendsto _).comp ((hSc.tendsto 0).sub_const (∑ n ∈ range K, p n 0))
    rw [sub_self, map_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hS, inter_mem hU hW] with x hx hxUW
  have h0UW : (0 : E) ∈ U ∩ W := ⟨mem_of_mem_nhds hU, mem_of_mem_nhds hW⟩
  have e : f x - f 0 = (f x - ∑ n ∈ range K, p n x) +
      (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) - (f 0 - ∑ n ∈ range K, p n 0) := by abel
  rw [e]
  calc q ((f x - ∑ n ∈ range K, p n x) + (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) -
        (f 0 - ∑ n ∈ range K, p n 0))
      ≤ q (f x - ∑ n ∈ range K, p n x) + q (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) +
          q (f 0 - ∑ n ∈ range K, p n 0) := by
        refine (map_sub_le_add q _ _).trans ?_
        gcongr
        exact map_add_le_add q _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 := htail x hxUW K
        have h2 := htail 0 h0UW K
        linarith
    _ = ε := by ring

end Baire

/-! ### Exponential sums -/

section ExpSum

/-- A nonzero constant is not eventually an exponential sum `∑ cᵢ λᵢⁿ` in which the base `1`
carries no weight. The bases may repeat. -/
theorem not_eventually_const_eq_expSum : ∀ (m : ℕ) (c lam : Fin m → ℂ) {a : ℂ} (N : ℕ),
    (∀ i, lam i = 1 → c i = 0) → a ≠ 0 → ¬ ∀ n ≥ N, a = ∑ i, c i * lam i ^ n
  | 0, c, lam, a, N, _, ha, h => ha (by simpa using h N le_rfl)
  | m + 1, c, lam, a, N, hc1, ha, h => by
    set l := lam (Fin.last m) with hl_def
    by_cases hl : l = 1
    · have hcl : c (Fin.last m) = 0 := hc1 _ hl
      refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc) (fun i ↦ lam i.castSucc) N
        (fun i h ↦ hc1 _ h) ha fun n hn ↦ ?_
      rw [h n hn, Fin.sum_univ_castSucc, hcl, zero_mul, add_zero]
    · refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc * (lam i.castSucc - l))
        (fun i ↦ lam i.castSucc) (a := a * (1 - l)) N (fun i h ↦ by simp [hc1 _ h])
        (mul_ne_zero ha (sub_ne_zero.2 (Ne.symm hl))) fun n hn ↦ ?_
      have h1 := h (n + 1) (by omega)
      have h0 := h n hn
      rw [Fin.sum_univ_castSucc] at h1 h0
      have e : ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n =
          (∑ i : Fin m, c i.castSucc * lam i.castSucc ^ (n + 1)) -
            l * ∑ i : Fin m, c i.castSucc * lam i.castSucc ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e]
      linear_combination h1 - l * h0

/-- A non-constant affine sequence `a n + b` is not eventually an exponential sum
`∑ cᵢ λᵢⁿ`. The bases may repeat. -/
theorem not_eventually_affine_eq_expSum : ∀ (m : ℕ) (c lam : Fin m → ℂ) {a b : ℂ} (N : ℕ),
    a ≠ 0 → ¬ ∀ n ≥ N, a * n + b = ∑ i, c i * lam i ^ n
  | 0, c, lam, a, b, N, ha, h => by
    have h0 := h N le_rfl
    have h1 := h (N + 1) (by omega)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0 h1
    push_cast at h1
    exact ha (by linear_combination h1 - h0)
  | m + 1, c, lam, a, b, N, ha, h => by
    set l := lam (Fin.last m) with hl_def
    have key : ∀ n ≥ N, a * (1 - l) * n + (a + b * (1 - l)) =
        ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n := by
      intro n hn
      have h1 := h (n + 1) (by omega)
      have h0 := h n hn
      rw [Fin.sum_univ_castSucc] at h1 h0
      push_cast at h1
      have e : ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n =
          (∑ i : Fin m, c i.castSucc * lam i.castSucc ^ (n + 1)) -
            l * ∑ i : Fin m, c i.castSucc * lam i.castSucc ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e]
      linear_combination h1 - l * h0
    by_cases hl : l = 1
    · refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc * (lam i.castSucc - l))
        (fun i ↦ lam i.castSucc) (a := a) N (fun i h ↦ by simp [h, hl]) ha fun n hn ↦ ?_
      have := key n hn
      rw [hl] at this ⊢
      simpa using this
    · exact not_eventually_affine_eq_expSum m _ _ N
        (mul_ne_zero ha (sub_ne_zero.2 (Ne.symm hl))) key

end ExpSum

/-! ### Counterexamples in `ℓ²` -/

section Counterexamples

/-- The Hilbert space `ℓ²(ℕ, ℂ)`. -/
local notation "ℓ²" => lp (fun _ : ℕ ↦ ℂ) 2

/-- The `n`-th coordinate functional on `ℓ²`. -/
def coordCLM (n : ℕ) : ℓ² →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ x n
      map_add' := fun x y ↦ by simp
      map_smul' := fun c x ↦ by simp } 1
    (fun x ↦ by rw [one_mul]; exact lp.norm_apply_le_norm (by norm_num) x n)

@[simp] theorem coordCLM_apply (n : ℕ) (x : ℓ²) : coordCLM n x = x n := rfl

/-! #### `E` not Baire (Bochnak–Siciak, Counterexample 5.1) -/

/-- The finitely supported sequences, with the norm of `ℓ²`: a normed space which is not
complete, and not a Baire space (`not_baireSpace_finSeq`). -/
def finSeq : Submodule ℂ ℓ² where
  carrier := {x | ∃ M, ∀ n ≥ M, x n = 0}
  add_mem' := by
    rintro x y ⟨M, hM⟩ ⟨M', hM'⟩
    exact ⟨max M M', fun n hn ↦ by
      simp [hM n (le_of_max_le_left hn), hM' n (le_of_max_le_right hn)]⟩
  zero_mem' := ⟨0, fun n _ ↦ by simp⟩
  smul_mem' := by
    rintro c x ⟨M, hM⟩
    exact ⟨M, fun n hn ↦ by simp [hM n hn]⟩

theorem mem_finSeq {x : ℓ²} : x ∈ finSeq ↔ ∃ M, ∀ n ≥ M, x n = 0 := Iff.rfl

/-- The terms `pₙ (x) = (n xₙ)ⁿ` of Bochnak–Siciak's Counterexample 5.1. -/
def bsTerm (n : ℕ) (x : finSeq) : ℂ := ((n : ℂ) * (x : ℓ²) n) ^ n

theorem isContHomPoly_bsTerm (n : ℕ) : IsContHomPoly ℂ n (bsTerm n) := by
  refine ⟨(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun _ ↦ (n : ℂ) • (coordCLM n).comp finSeq.subtypeL), fun x ↦ ?_⟩
  simp [bsTerm, Finset.prod_const]

/-- At a finitely supported point only finitely many terms are nonzero. -/
theorem bsTerm_eventually_zero (x : finSeq) : ∃ M, ∀ n ≥ M, bsTerm n x = 0 := by
  obtain ⟨M, hM⟩ := mem_finSeq.1 x.2
  exact ⟨M + 1, fun n hn ↦ by simp [bsTerm, hM n (by omega), show n ≠ 0 by omega]⟩

/-- The series `∑ (n xₙ)ⁿ` converges at every point of `finSeq`. -/
theorem tendsto_bsSum (x : finSeq) :
    ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, bsTerm n x) atTop (𝓝 y) := by
  obtain ⟨M, hM⟩ := bsTerm_eventually_zero x
  refine ⟨∑ n ∈ range M, bsTerm n x, tendsto_atTop_of_eventually_const (i₀ := M) fun N hN ↦ ?_⟩
  rw [← Finset.sum_range_add_sum_Ico _ hN,
    Finset.sum_eq_zero (fun n hn ↦ hM n (Finset.mem_Ico.1 hn).1), add_zero]

/-- **Bochnak–Siciak, Counterexample 5.1.** On the space of finitely supported sequences with
the norm of `ℓ²`, the series of continuous homogeneous polynomials `∑ (n xₙ)ⁿ` converges
everywhere, but its sum is not continuous at `0` (hence not complex analytic). Thus
`continuousAt_zero_of_tendsto_sum` fails without the Baire property. -/
theorem not_continuousAt_bsSum {f : finSeq → ℂ}
    (hf : ∀ x, Tendsto (fun N ↦ ∑ n ∈ range N, bsTerm n x) atTop (𝓝 (f x))) :
    ¬ ContinuousAt f 0 := by
  have hval : ∀ x M, (∀ n ≥ M, bsTerm n x = 0) → f x = ∑ n ∈ range M, bsTerm n x := by
    intro x M hM
    refine tendsto_nhds_unique (hf x)
      (tendsto_atTop_of_eventually_const (i₀ := M) fun N hN ↦ ?_)
    rw [← Finset.sum_range_add_sum_Ico _ hN,
      Finset.sum_eq_zero (fun n hn ↦ hM n (Finset.mem_Ico.1 hn).1), add_zero]
  have h0 : f 0 = 1 := by
    rw [hval 0 1 (fun n hn ↦ by simp [bsTerm, show n ≠ 0 by omega])]
    simp [bsTerm]
  set xm : ℕ → finSeq := fun m ↦ ⟨lp.single 2 m ((2 : ℂ) / m), m + 1, fun n hn ↦ by
    simp [show n ≠ m by omega]⟩
  have hxm : ∀ m, 1 ≤ m → f (xm m) = 1 + 2 ^ m := by
    intro m hm
    have hterm : ∀ n, bsTerm n (xm m) = if n = 0 then 1 else if n = m then 2 ^ m else 0 := by
      intro n
      by_cases hn0 : n = 0
      · subst hn0; simp [bsTerm]
      · by_cases hnm : n = m
        · subst hnm
          have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
          simp [bsTerm, xm, hn0, mul_div_cancel₀ _ this]
        · simp [bsTerm, xm, hn0, hnm]
    rw [hval (xm m) (m + 1) ?_]
    · rw [Finset.sum_range_succ, Finset.sum_eq_single 0]
      · simp [hterm, show m ≠ 0 by omega]
      · intro n hn hn0
        have := Finset.mem_range.1 hn
        simp [hterm, hn0, show n ≠ m by omega]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · intro n hn
      simp [hterm, show n ≠ 0 by omega, show n ≠ m by omega]
  intro hc
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ + 1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) < m := by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hδ]
    exact_mod_cast this.le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hd : dist (xm m) 0 < δ := by
    have hcoe : ((xm m : finSeq) : ℓ²) = lp.single 2 m ((2 : ℂ) / m) := rfl
    rw [dist_zero_right, ← Submodule.norm_coe, hcoe, lp.norm_single (by norm_num), norm_div,
      Complex.norm_ofNat, Complex.norm_natCast,
      div_lt_iff₀ hmpos]
    have h2 : 2 / δ < m := by linarith
    rw [div_lt_iff₀ hδ] at h2
    linarith
  have := hδf hd
  rw [hxm m hm1, h0, dist_eq_norm, add_sub_cancel_left, norm_pow, Complex.norm_ofNat] at this
  exact absurd this (not_lt.2 (one_le_pow₀ (by norm_num)))

/-- The space of finitely supported sequences with the norm of `ℓ²` is not a Baire space:
otherwise `continuousAt_zero_of_tendsto_sum` would contradict `not_continuousAt_bsSum`. -/
theorem not_baireSpace_finSeq : ¬ BaireSpace finSeq := by
  intro hB
  choose f hf using tendsto_bsSum
  exact not_continuousAt_bsSum hf
    (continuousAt_zero_of_tendsto_sum isContHomPoly_bsTerm univ_mem fun x _ ↦ hf x)

/-! #### `F` not complete, in one variable -/

theorem memℓp_geom {z : ℂ} (hz : ‖z‖ < 1) : Memℓp (fun n : ℕ ↦ z ^ n) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h : Summable fun n : ℕ ↦ (‖z‖ ^ 2) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg z])
  refine h.congr fun n ↦ ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_pow, ← pow_mul, mul_comm]

/-- The vector `(zⁿ)ₙ ∈ ℓ²` for `‖z‖ < 1` (and `0` otherwise). -/
def geomVec (z : ℂ) : ℓ² := if h : ‖z‖ < 1 then ⟨fun n ↦ z ^ n, memℓp_geom h⟩ else 0

theorem geomVec_apply {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) : geomVec z n = z ^ n := by
  simp [geomVec, hz]

/-- The incomplete space `F = span {eₙ, (zⁿ)ₙ : n ∈ ℕ, ‖z‖ < 1} ⊆ ℓ²`. -/
def geomSpan : Submodule ℂ ℓ² :=
  Submodule.span ℂ (Set.range (fun n ↦ lp.single 2 n (1 : ℂ)) ∪ geomVec '' ball 0 1)

/-- The map `z ↦ ∑ zⁿ eₙ` from the unit disc to `geomSpan` (and `0` outside). -/
def geomFun (z : ℂ) : geomSpan :=
  if h : ‖z‖ < 1 then
    ⟨geomVec z, Submodule.subset_span (Or.inr ⟨z, mem_ball_zero_iff.2 h, rfl⟩)⟩
  else 0

/-- The basis vector `eₙ ∈ geomSpan`. -/
def geomCoeff (n : ℕ) : geomSpan :=
  ⟨lp.single 2 n 1, Submodule.subset_span (Or.inl ⟨n, rfl⟩)⟩

theorem coe_geomFun {z : ℂ} (hz : ‖z‖ < 1) : (geomFun z : ℓ²) = geomVec z := by
  simp [geomFun, hz]

/-- The power series `∑ zⁿ eₙ` converges **in `geomSpan`** on the whole unit disc. -/
theorem hasPowerSeriesOnDisc_geomFun : HasPowerSeriesOnDisc geomFun geomCoeff 0 1 := by
  intro z hz
  rw [zero_add]
  have hL : Topology.IsInducing (geomSpan.subtype) := Topology.IsInducing.subtypeVal
  rw [← hL.hasSum_iff]
  convert lp.hasSum_single (E := fun _ : ℕ ↦ ℂ) (p := 2) ENNReal.ofNat_ne_top (geomVec z)
    using 1
  · funext n
    simp [geomCoeff, geomVec_apply hz, ← lp.single_smul]
  · simp [coe_geomFun hz]

/-- Every generator of `geomSpan` has eventually exponential coordinates. -/
theorem exists_pow_of_mem_gen {s : ℓ²}
    (hs : s ∈ Set.range (fun n ↦ lp.single 2 n (1 : ℂ)) ∪ geomVec '' ball 0 1) :
    ∃ μ : ℂ, ∃ K : ℕ, ∀ n > K, s n = μ ^ n := by
  rcases hs with ⟨k, rfl⟩ | ⟨z, hz, rfl⟩
  · exact ⟨0, k, fun n hn ↦ by
      simp [show n ≠ k by omega, show n ≠ 0 by omega]⟩
  · exact ⟨z, 0, fun n _ ↦ geomVec_apply (mem_ball_zero_iff.1 hz) n⟩

/-- **Incomplete target, one variable.** The function `z ↦ ∑ zⁿ eₙ` with values in
`geomSpan` has no complex derivative at `1/2`: its derivative in `ℓ²` would be
`∑ n 2^{1-n} eₙ`, which does not lie in `geomSpan` (`not_eventually_affine_eq_expSum`). -/
theorem not_hasCDerivAt_geomFun (y : geomSpan) : ¬ HasCDerivAt geomFun (1 / 2) y := by
  intro h
  have hcoord : ∀ n : ℕ, (y : ℓ²) n = n * (1 / 2 : ℂ) ^ (n - 1) := by
    intro n
    set ℓ := (coordCLM n).comp geomSpan.subtypeL
    have h1 : Tendsto (fun w : ℂ ↦ w⁻¹ • (ℓ (geomFun (1 / 2 + w)) - ℓ (geomFun (1 / 2))))
        (𝓝[≠] 0) (𝓝 (ℓ y)) := by
      refine ((ℓ.continuous.tendsto y).comp h).congr fun w ↦ ?_
      simp only [Function.comp, map_smul, map_sub]
    have h2 : Tendsto (fun w : ℂ ↦ w⁻¹ • ((1 / 2 + w) ^ n - (1 / 2 : ℂ) ^ n)) (𝓝[≠] 0)
        (𝓝 (n * (1 / 2 : ℂ) ^ (n - 1))) := by
      have hd := hasDerivAt_pow n (1 / 2 : ℂ)
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      simpa using hd
    have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), ‖1 / 2 + w‖ < 1 := by
      have hc : Continuous fun w : ℂ ↦ ‖1 / 2 + w‖ := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
    have h3 : (fun w : ℂ ↦ w⁻¹ • (ℓ (geomFun (1 / 2 + w)) - ℓ (geomFun (1 / 2)))) =ᶠ[𝓝[≠] 0]
        fun w : ℂ ↦ w⁻¹ • ((1 / 2 + w) ^ n - (1 / 2 : ℂ) ^ n) := by
      filter_upwards [nhdsWithin_le_nhds hnear] with w hw
      have hh : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
      have e : ∀ z : ℂ, ‖z‖ < 1 → ℓ (geomFun z) = z ^ n := fun z hz ↦ by
        simp only [ℓ, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coordCLM_apply]
        rw [coe_geomFun hz, geomVec_apply hz]
      rw [e _ hw, e _ hh]
    exact tendsto_nhds_unique (h1.congr' h3) h2
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 y.2
  choose μ K hμK using fun i ↦ exists_pow_of_mem_gen (g i).2
  set KK := ∑ i, K i
  refine not_eventually_affine_eq_expSum m c (fun i ↦ 2 * μ i) (a := 2) (b := 0) (KK + 1)
    two_ne_zero fun n hn ↦ ?_
  have hyn := congrArg (fun v : ℓ² ↦ v n) hg
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hyn
  rw [hcoord n] at hyn
  have hK : ∀ i, n > K i := fun i ↦
    lt_of_le_of_lt (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j)) (Finset.mem_univ i))
      (by omega)
  simp only [fun i ↦ hμK i n (hK i)] at hyn
  have hn1 : 1 ≤ n := by omega
  have e : (2 : ℂ) * n + 0 = 2 ^ n * (n * (1 / 2 : ℂ) ^ (n - 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn1
    simp only [Nat.add_sub_cancel_left, pow_add, pow_one, one_div, inv_pow]
    field_simp
    push_cast
    ring
  rw [e, ← hyn, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Without completeness of `F` the disc of convergence of a power series need not be a disc of
analyticity: `∑ zⁿ eₙ` converges in `geomSpan` on the unit disc (`hasPowerSeriesOnDisc_geomFun`)
but is not complex analytic there. -/
theorem not_cAnalyticOn_geomFun : ¬ CAnalyticOn geomFun (ball 0 1) := fun h ↦
  not_hasCDerivAt_geomFun _ (h.hasCDerivAt (by norm_num : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1))

end Counterexamples

end LCAnalysis
