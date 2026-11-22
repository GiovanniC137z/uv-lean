import UV.FurtherCurvatureLine

/-! The determinant over the actual spherical mode family at positive depth,
with its zero-depth extension and uniform quartic bound. -/

noncomputable section

open Filter Real
open scoped BigOperators Topology

namespace UV.FurtherCurvatureDeterminant

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine
open UV.RevisionCurvatureDeterminant

def sphericalDeterminant (n : ℕ) (Λ ℓ : ℝ) : ℝ :=
  relativeDeterminant (sphericalModes Λ) latticeFrequency ℓ n

def depthSpectrum (ℓ : ℝ) (k : TorusMode) : ℝ :=
  if k = 0 then 0 else exp (-2*ℓ*latticeFrequency k)

def fullDeterminant (n : ℕ) (ℓ : ℝ) : ℝ :=
  if ℓ = 0 then if n = 0 then 1 else 0
  else exp (-(n:ℝ) * ∑' k, log (1 + depthSpectrum ℓ k))

/-- The actual positive-depth frequency multipliers are summable on the
mean-zero four-torus, the scalar diagonal trace estimate. -/
theorem depth_spectrum_summable {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable (depthSpectrum ℓ) := by
  obtain ⟨C, _, hc⟩ := full_weighted_line_bound (s := 2) (by norm_num)
  have hz (k : TorusMode) : 0 ≤ depthSpectrum ℓ k := by
    unfold depthSpectrum
    split <;> positivity
  apply (((hc hℓ).1.mul_left 2).of_nonneg_of_le hz)
  intro k
  by_cases hk : k = 0
  · simp [hk, depthSpectrum]
  have hr : 0 < latticeFrequency k := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (latticeHeight_ne_zero hk)))
    (latticeHeight_le_latticeFrequency k)
  let r := latticeFrequency k
  let e := exp (-2*ℓ*r)
  have he : 0 < e := exp_pos _
  have h1 : e ≤ 1 := by
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)
  have hdenom : 0 < r^2 * (1+e) := by positivity
  have hm : r^2 * (1+e) ≤ 2*(1+r)^2 := by
    calc
      _ ≤ r^2 * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by nlinarith
  simp only [depthSpectrum, if_neg hk, weightedLine, curvatureLine, curvatureCovariance]
  change e ≤ 2*((1+r)^(2:ℝ)*(e*(r^2*(1+e))⁻¹))
  rw [show (1+r)^(2:ℝ) = (1+r)^2 by norm_num]
  have haux : e * (r^2 * (1+e)) ≤ 2 * (1+r)^2 * e := by
    rw [mul_comm e]
    exact mul_le_mul_of_nonneg_right hm he.le
  simpa only [← div_eq_mul_inv, mul_assoc, mul_div_assoc] using (le_div_iff₀ hdenom).mpr haux

private theorem log_summable {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable fun k : TorusMode => log (1 + depthSpectrum ℓ k) := by
  have hn (k : TorusMode) : 0 ≤ depthSpectrum ℓ k := by
    unfold depthSpectrum
    split <;> positivity
  refine (depth_spectrum_summable hℓ).of_nonneg_of_le
    (fun k => log_nonneg (by linarith [hn k])) (fun k => ?_)
  simpa using log_le_sub_one_of_pos (show 0 < 1 + depthSpectrum ℓ k by linarith [hn k])

private theorem relative_determinant_exp_form (modes : Finset TorusMode) (n : ℕ) (ℓ : ℝ) :
    relativeDeterminant modes latticeFrequency ℓ n =
      exp (-(n:ℝ) * ∑ k ∈ modes, log (1 + exp (-2*ℓ*latticeFrequency k))) := by
  have hp : 0 < ∏ k ∈ modes, (1 + exp (-2*ℓ*latticeFrequency k)) ^ n :=
    Finset.prod_pos (fun _ _ => by positivity)
  unfold relativeDeterminant
  rw [← exp_log hp, ← exp_neg, log_prod _ _ (fun _ _ => by positivity)]
  simp only [log_pow, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]

private theorem spherical_determinant_as_log_sum (n : ℕ) (Λ ℓ : ℝ) :
    sphericalDeterminant n Λ ℓ =
      exp (-(n:ℝ) * ∑ k ∈ insert 0 (sphericalModes Λ), log (1 + depthSpectrum ℓ k)) := by
  classical
  have h0 : (0 : TorusMode) ∉ sphericalModes Λ := by simp [mem_sphericalModes]
  rw [Finset.sum_insert h0, sphericalDeterminant, relative_determinant_exp_form]
  have hz : log (1 + depthSpectrum ℓ 0) = 0 := by simp [depthSpectrum]
  rw [hz, zero_add]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  rw [depthSpectrum, if_neg (mem_sphericalModes.mp hk).1]

private theorem spherical_modes_cofinal :
    Tendsto (fun Λ : ℝ => insert (0 : TorusMode) (sphericalModes Λ)) atTop atTop := by
  classical
  refine tendsto_atTop.mpr (fun modes => ?_)
  refine eventually_atTop.mpr ⟨∑ k ∈ modes, latticeFrequency k, fun Λ hΛ k hk => ?_⟩
  by_cases he : k = 0
  · simpa only [he] using Finset.mem_insert_self (0 : TorusMode) (sphericalModes Λ)
  exact Finset.mem_insert_of_mem (mem_sphericalModes.mpr ⟨he,
    (Finset.single_le_sum (f := latticeFrequency) (fun _ _ => sqrt_nonneg _) hk).trans hΛ⟩)

theorem full_determinant_pos (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < fullDeterminant n ℓ := by simp [fullDeterminant, hℓ.ne', exp_pos]

theorem positive_depth_determinant_limit (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun Λ : ℝ => sphericalDeterminant n Λ ℓ) atTop (𝓝 (fullDeterminant n ℓ)) := by
  rw [fullDeterminant, if_neg hℓ.ne']
  simp_rw [spherical_determinant_as_log_sum]
  have hb : Tendsto (fun modes : Finset TorusMode =>
      ∑ k ∈ modes, log (1 + depthSpectrum ℓ k)) atTop
      (𝓝 (∑' k, log (1 + depthSpectrum ℓ k))) := (log_summable hℓ).hasSum
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((hb.comp spherical_modes_cofinal).const_mul (-(n:ℝ)))

/-- The inverse determinant is also the actual convergent scalar product
over all nonzero modes. Here the factor at the absent zero mode is one. -/
theorem full_determinant_hasProd (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasProd (fun k : TorusMode => ((1 + depthSpectrum ℓ k)^n)⁻¹) (fullDeterminant n ℓ) := by
  rw [fullDeterminant, if_neg hℓ.ne']
  have hb : Tendsto (fun modes : Finset TorusMode =>
      ∑ k ∈ modes, log (1 + depthSpectrum ℓ k)) atTop
      (𝓝 (∑' k, log (1 + depthSpectrum ℓ k))) := (log_summable hℓ).hasSum
  refine (Real.continuous_exp.continuousAt.tendsto.comp
    (hb.const_mul (-(n:ℝ)))).congr' ?_
  filter_upwards with modes
  have hp : 0 < ∏ k ∈ modes, (1 + depthSpectrum ℓ k)^n := by
    apply Finset.prod_pos
    intro k _
    have hh : 0 ≤ depthSpectrum ℓ k := by unfold depthSpectrum; split <;> positivity
    positivity
  rw [Finset.prod_inv_distrib, ← exp_log hp, ← exp_neg,
    log_prod _ _ (fun k _ => by
      have hh : 0 ≤ depthSpectrum ℓ k := by unfold depthSpectrum; split <;> positivity
      positivity)]
  simp only [Function.comp_apply, log_pow, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]

theorem spherical_determinant_quartic (n : ℕ) (Λ ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hR : 2 ≤ effectiveRadius Λ ℓ) :
    sphericalDeterminant n Λ ℓ ≤
      exp (-((n:ℝ) * log (1+exp (-2)) / 4^4) * (effectiveRadius Λ ℓ)^4) := by
  let R := effectiveRadius Λ ℓ
  have hΛR : R ≤ Λ := by unfold R effectiveRadius; split; exact le_rfl; exact min_le_left _ _
  have hshort (k : TorusMode) (hk : k ∈ sphericalModes R) :
      ℓ * latticeFrequency k ≤ 1 := by
    by_cases h : ℓ = 0
    · simp [h]
    have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ (Ne.symm h)
    have hr : R ≤ ℓ⁻¹ := by simp [R, effectiveRadius, h]
    exact (mul_le_mul_of_nonneg_left ((mem_sphericalModes.mp hk).2.trans hr) hℓ).trans
      (by simp [hℓpos.ne'])
  have hcard := lattice_ball_card_lower (sphericalModes R) hR
    (fun k hk hfreq => mem_sphericalModes.mpr ⟨hk,hfreq⟩)
  apply (relative_determinant_mode_bound (sphericalModes_mono hΛR) _ _ _ hshort).trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ (n:ℝ) * log (1+exp (-2)) by
      exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by linarith [exp_nonneg (-2)])))
  change -((n:ℝ) * (sphericalModes R).card) * log (1+exp (-2)) ≤
    -((n:ℝ) * log (1+exp (-2)) / 4^4) * R^4
  calc
    _ = -((sphericalModes R).card * ((n:ℝ)*log (1+exp (-2)))) := by ring
    _ ≤ -((R/4)^4 * ((n:ℝ)*log (1+exp (-2)))) := neg_le_neg hm
    _ = _ := by ring


theorem spherical_determinant_polynomial_control {n : ℕ} (hn : 0 < n) {D : ℝ}
    (hD : 0 ≤ D) :
    ∃ C > 0, ∀ {Λ ℓ : ℝ}, 0 ≤ Λ → 0 ≤ ℓ → sphericalDeterminant n Λ ℓ *
      (1 + effectiveRadius Λ ℓ)^D ≤ C := by
  let a := (n:ℝ) * log (1+exp (-2)) / 4^4
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have ha : 0 < a := by
    unfold a
    have hlog : 0 < log (1+exp (-2)) := log_pos (lt_add_of_pos_right _ (exp_pos _))
    positivity
  obtain ⟨C, hC, hc⟩ := quartic_determinant_polynomial_uniform ha hD
  refine ⟨max C (3^D), hC.trans_le (le_max_left _ _), fun {Λ ℓ} hΛ hℓ => ?_⟩
  let R := effectiveRadius Λ ℓ
  have hR : 0 ≤ R := by
    by_cases h : ℓ = 0
    · simpa [R, effectiveRadius, h] using hΛ
    · dsimp only [R]
      rw [effectiveRadius, if_neg h]
      exact le_min hΛ (inv_nonneg.mpr hℓ)
  by_cases hbig : 2 ≤ R
  · exact ((mul_le_mul_of_nonneg_right
      (spherical_determinant_quartic n Λ ℓ hℓ hbig) (by positivity)).trans
      (hc R hR)).trans (le_max_left _ _)
  have hh : sphericalDeterminant n Λ ℓ ≤ 1 :=
    (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).2
  have hp : (1+R)^D ≤ 3^D := Real.rpow_le_rpow (by positivity) (by linarith) hD
  exact (mul_le_mul hh hp (by positivity) zero_le_one).trans (by simp)

/-- The determinant suppresses an arbitrary fixed insertion polynomial
at the atom ℓ=0 before the spherical cutoff is removed. -/
theorem zero_depth_polynomial_limit {n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) :
    Tendsto (fun Λ : ℝ => sphericalDeterminant n Λ 0 * (1+Λ)^D)
      atTop (𝓝 0) := by
  let a := (n:ℝ) * log (1+exp (-2)) / 4^4
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have ha : 0 < a := by
    unfold a
    have hlog : 0 < log (1+exp (-2)) := log_pos (lt_add_of_pos_right _ (exp_pos _))
    positivity
  refine squeeze_zero' ?_ ?_ (quartic_determinant_polynomial_limit ha hD)
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with Λ hΛ
    exact mul_nonneg (relative_determinant_bounds (sphericalModes Λ) latticeFrequency 0 n).1.le
      (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with Λ hΛ
    have hb := spherical_determinant_quartic n Λ 0 le_rfl
      (by simpa [effectiveRadius] using hΛ)
    have hb' : sphericalDeterminant n Λ 0 ≤ exp (-a * Λ^4) := by
      simpa [effectiveRadius, a] using hb
    exact mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg (by linarith) _)

theorem zero_depth_determinant_limit {n : ℕ} (hn : 0 < n) :
    Tendsto (fun Λ : ℝ => sphericalDeterminant n Λ 0) atTop (𝓝 (fullDeterminant n 0)) := by
  simpa [fullDeterminant, hn.ne'] using zero_depth_polynomial_limit hn (D := 0) le_rfl

end UV.FurtherCurvatureDeterminant
