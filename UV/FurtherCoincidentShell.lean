import UV.FurtherShellBoundary

/-! Opposite-side resolvents at a common positive height, tested in the
regular invariant shell coordinate. The finite part is represented by
subtracting the even test's constant before the height is sent to zero. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set UV.Carrier
open scoped Topology NNReal

def oppositeShellKernel (h D : ℝ) : ℝ := (D ^ 2 + h ^ 2)⁻¹

def evenShellTest (f : ℝ → ℝ) (D : ℝ) : ℝ := (f D + f (-D)) / 2

def shellFinitePartTest (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  (evenShellTest f D - f 0) / D ^ 2

theorem opposite_shell_kernel_le_cauchy {h : ℝ} (hh : 0 < h) (D : ℝ) :
    oppositeShellKernel h D ≤ (min 1 (h ^ 2))⁻¹ * (1 + D ^ 2)⁻¹ := by
  have hm : 0 < min 1 (h ^ 2) := lt_min zero_lt_one (by positivity)
  unfold oppositeShellKernel
  rw [← mul_inv]
  apply inv_anti₀ (mul_pos hm (by positivity))
  calc
    min 1 (h ^ 2) * (1 + D ^ 2) = min 1 (h ^ 2) + min 1 (h ^ 2) * D ^ 2 := by ring
    _ ≤ h ^ 2 + 1 * D ^ 2 := add_le_add (min_le_right _ _)
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg D))
    _ = D ^ 2 + h ^ 2 := by ring

theorem opposite_shell_kernel_integrable {h : ℝ} (hh : 0 < h) :
    Integrable (oppositeShellKernel h) := by
  apply (integrable_inv_one_add_sq.const_mul ((min 1 (h ^ 2))⁻¹)).mono'
  · exact (((measurable_id.pow_const 2).add measurable_const).inv).aestronglyMeasurable
  · exact Eventually.of_forall fun D => by
      rw [Real.norm_of_nonneg (by unfold oppositeShellKernel; positivity)]
      exact opposite_shell_kernel_le_cauchy hh D

/-- The divergence on the coincident shell has the exact mass π/h. -/
theorem opposite_shell_kernel_mass {h : ℝ} (hh : 0 < h) :
    (∫ D : ℝ, oppositeShellKernel h D) = Real.pi / h := by
  have hmass := pole_poisson_scaling (fun _ => 1) hh
  simp only [mul_one, integral_univ_inv_one_add_sq] at hmass
  change (∫ D : ℝ, h / (D ^ 2 + h ^ 2)) = Real.pi at hmass
  simp_rw [div_eq_mul_inv] at hmass
  change (∫ D : ℝ, h * oppositeShellKernel h D) = Real.pi at hmass
  rw [integral_const_mul] at hmass
  exact (eq_div_iff hh.ne').2 (by rwa [mul_comm])

/-- The even test after subtraction is integrable for a bounded test
whose even increment is quadratically controlled near the shell. -/
theorem shell_finite_part_test_integrable {f : ℝ → ℝ} (hf : Continuous f)
    {C M : ℝ} (hC : ∀ D, ‖f D‖ ≤ C)
    (hM : ∀ D, |D| ≤ 1 → ‖evenShellTest f D - f 0‖ ≤ M * D ^ 2) :
    Integrable (shellFinitePartTest f) := by
  have hb (D : ℝ) : ‖evenShellTest f D - f 0‖ ≤ 2 * C := by
    have h : ‖evenShellTest f D‖ ≤ C := by
      unfold evenShellTest
      rw [norm_div, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      exact (div_le_iff₀ two_pos).2 ((norm_add_le _ _).trans (by linarith [hC D, hC (-D)]))
    exact (norm_sub_le _ _).trans (by linarith [hC 0])
  have hmeas : Measurable (shellFinitePartTest f) :=
    ((((hf.add (hf.comp continuous_neg)).div_const 2).sub continuous_const).measurable).div
      (measurable_id.pow_const 2)
  let B := max (2 * M) (4 * C)
  have hB : 0 ≤ B := (by linarith [(norm_nonneg (f 0)).trans (hC 0)] : 0 ≤ 4 * C).trans
    (le_max_right _ _)
  apply (integrable_inv_one_add_sq.const_mul B).mono' hmeas.aestronglyMeasurable
  refine Eventually.of_forall fun D => ?_
  by_cases hD : D = 0
  · simp [hD, shellFinitePartTest, hB]
  have hp : 0 < D ^ 2 := sq_pos_of_ne_zero hD
  unfold shellFinitePartTest
  rw [norm_div, Real.norm_of_nonneg hp.le, ← div_eq_mul_inv,
    div_le_div_iff₀ hp (by positivity : 0 < 1 + D ^ 2)]
  by_cases hnear : |D| ≤ 1
  · have hs : 1 + D ^ 2 ≤ 2 := by
      nlinarith [(sq_le_sq₀ (abs_nonneg D) zero_le_one).2 hnear, sq_abs D]
    calc
      _ ≤ ‖evenShellTest f D - f 0‖ * 2 :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ ≤ M * D ^ 2 * 2 := mul_le_mul_of_nonneg_right (hM D hnear) zero_le_two
      _ = 2 * M * D ^ 2 := by ring
      _ ≤ B * D ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le
  · have hs : 1 + D ^ 2 ≤ 2 * D ^ 2 := by
      nlinarith [(sq_lt_sq₀ zero_le_one (abs_nonneg D)).2 (lt_of_not_ge hnear), sq_abs D]
    calc
      _ ≤ ‖evenShellTest f D - f 0‖ * (2 * D ^ 2) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ ≤ 2 * C * (2 * D ^ 2) := mul_le_mul_of_nonneg_right (hb D) (by positivity)
      _ = 4 * C * D ^ 2 := by ring
      _ ≤ B * D ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le

/-- The mass subtraction leaves the regular-shell finite part. -/
theorem opposite_shell_finite_part_limit {f : ℝ → ℝ} (hf : Continuous f)
    {C M : ℝ} (hC : ∀ D, ‖f D‖ ≤ C)
    (hM : ∀ D, |D| ≤ 1 → ‖evenShellTest f D - f 0‖ ≤ M * D ^ 2) :
    Tendsto (fun h : ℝ =>
      (∫ D : ℝ, oppositeShellKernel h D * f D) - Real.pi / h * f 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ D : ℝ, shellFinitePartTest f D)) := by
  let g (h D : ℝ) : ℝ := (evenShellTest f D - f 0) / (D ^ 2 + h ^ 2)
  have he : Continuous (evenShellTest f) := (hf.add (hf.comp continuous_neg)).div_const 2
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (μ := volume) (F := g) (f := shellFinitePartTest f) (fun D => ‖shellFinitePartTest f D‖)
    ?_ ?_ (shell_finite_part_test_integrable hf hC hM).norm ?_
  · apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hK := opposite_shell_kernel_integrable hh'
    have hprod : Integrable (fun D => oppositeShellKernel h D * f D) := by
      simpa only [mul_comm] using hK.bdd_mul hf.aestronglyMeasurable ⟨C, hC⟩
    have hprod' : Integrable (fun D => oppositeShellKernel h D * f (-D)) := by
      simpa only [mul_comm] using hK.bdd_mul
        (hf.comp continuous_neg).aestronglyMeasurable ⟨C, fun D => hC (-D)⟩
    have hsym : (∫ D : ℝ, oppositeShellKernel h D * f (-D)) =
        ∫ D : ℝ, oppositeShellKernel h D * f D := by
      have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (MeasurableEquiv.neg ℝ).measurableEmbedding (fun D => oppositeShellKernel h D * f D)
      simpa [oppositeShellKernel, neg_sq, Function.comp_def] using hneg
    have hterm : (∫ D : ℝ, g h D) =
        ∫ D : ℝ, (oppositeShellKernel h D * f D + oppositeShellKernel h D * f (-D)) / 2 -
          oppositeShellKernel h D * f 0 := by
      apply integral_congr_ae
      refine Eventually.of_forall fun D => ?_
      dsimp [g, evenShellTest, oppositeShellKernel]
      ring
    have hadd : Integrable (fun D => (oppositeShellKernel h D * f D +
        oppositeShellKernel h D * f (-D)) / 2) := by
      simpa only [Pi.add_apply] using (hprod.add hprod').div_const 2
    rw [hterm, integral_sub hadd (hK.mul_const (f 0)),
      integral_div, integral_add hprod hprod', hsym, integral_mul_const,
      opposite_shell_kernel_mass hh']
    ring
  · exact Eventually.of_forall fun h =>
      (((he.sub continuous_const).measurable).div
        ((measurable_id.pow_const 2).add measurable_const)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    refine Eventually.of_forall fun D => ?_
    by_cases hD : D = 0
    · simp [hD, g, shellFinitePartTest, evenShellTest, add_div]
    · dsimp [g, shellFinitePartTest]
      rw [abs_div, abs_div, abs_of_nonneg (by positivity : 0 ≤ D ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ D ^ 2 + h ^ 2)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_ne_zero hD)
        (le_add_of_nonneg_right (sq_nonneg _))
  · refine Eventually.of_forall fun D => ?_
    by_cases hD : D = 0
    · simp [hD, g, evenShellTest, shellFinitePartTest, add_div]
    · have hg : ContinuousAt (fun h => g h D) 0 := by
        exact continuousAt_const.div
          ((continuous_const.add (continuous_id.pow 2)).continuousAt) (by
            simpa using (sq_pos_of_ne_zero hD).ne')
      simpa [g, shellFinitePartTest] using hg.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

section Diamond

variable {E : Type*} [NormedAddCommGroup E]

/-- The opposite quotient resolvents have the same geometric pole unit
and height. Only their evolution signs differ. -/
theorem Plane.opposite_pole_product (diamond : Plane E) (height : Height) (D : ℝ) :
    diamond.poleInverse .ascending height D * diamond.poleInverse .descending height D =
      directed (oppositeShellKernel (height : ℝ) D : ℂ) := by
  have hη : diamond.eta .descending = -diamond.eta .ascending := by
    simp [Plane.eta, evolutionSign]
  let t : ℝ := (height : ℝ)
  let u : ℝ := diamond.eta .ascending
  have hu : (u : ℂ) ^ 2 = 1 := by
    exact_mod_cast diamond.eta_sq .ascending
  rw [diamond.pole_inverse_complex, diamond.pole_inverse_complex, ← directed_mul,
    ← mul_inv, hη]
  unfold oppositeShellKernel
  push_cast
  congr 2
  change ((D : ℂ) + Complex.I * (u * t)) * ((D : ℂ) + Complex.I * (-u * t)) =
    (D : ℂ) ^ 2 + (t : ℂ) ^ 2
  calc
    _ = (D : ℂ) ^ 2 - Complex.I ^ 2 * (u : ℂ) ^ 2 * (t : ℂ) ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq, hu]; ring

/-- Exact finite-height canonical scalar convention. The directed
coefficient differs from the tagged running numerator on the virtual line. -/
theorem Plane.canonical_pole_split (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    directed (Complex.I * (diamond.eta ε : ℂ)) * diamond.poleInverse ε height D =
      directed ((polePoisson (height : ℝ) D : ℂ) +
        Complex.I * ((diamond.eta ε * polePV (height : ℝ) D : ℝ) : ℂ)) := by
  let t : ℝ := (height : ℝ)
  let u : ℝ := diamond.eta ε
  have hu : (u : ℂ) ^ 2 = 1 := by exact_mod_cast diamond.eta_sq ε
  rw [Plane.poleInverse, ← directed_mul]
  unfold polePoisson polePV
  push_cast
  congr 1
  change Complex.I * (u : ℂ) * (((D : ℂ) - Complex.I * ((u : ℂ) * t)) /
      ((D : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
    (t : ℂ) / ((D : ℂ) ^ 2 + (t : ℂ) ^ 2) +
      Complex.I * ((u : ℂ) * ((D : ℂ) / ((D : ℂ) ^ 2 + (t : ℂ) ^ 2)))
  have he : Complex.I * (u : ℂ) * ((D : ℂ) - Complex.I * ((u : ℂ) * t)) =
      (t : ℂ) + Complex.I * (u : ℂ) * D := by
    calc
      _ = Complex.I * (u : ℂ) * D - Complex.I ^ 2 * (u : ℂ) ^ 2 * t := by ring
      _ = _ := by rw [Complex.I_sq, hu]; ring
  rw [← mul_div_assoc, he]
  ring

theorem Plane.canonical_pole_test_limits (diamond : Plane E) (ε : Evolution)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hi : Integrable f)
    (C : ℝ) (hC : ∀ D, ‖f D‖ ≤ C) :
    Tendsto (fun h : ℝ => (∫ D, polePoisson h D * f D,
      diamond.eta ε * ∫ D, polePV h D * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * f 0,
        diamond.eta ε * ∫ D in Ioi (0 : ℝ), symmetricTest f D)) :=
  (pole_poisson_test_limit hf.continuous C hC).prodMk_nhds
    ((pole_pv_test_limit hf hi).const_mul (diamond.eta ε))

theorem Plane.inverse_pole_split (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.poleInverse ε height D = directed ((polePV (height : ℝ) D : ℂ) -
      Complex.I * ((diamond.eta ε * polePoisson (height : ℝ) D : ℝ) : ℂ)) := by
  unfold Plane.poleInverse polePV polePoisson
  push_cast
  congr 1
  ring

theorem Plane.inverse_pole_test_limits (diamond : Plane E) (ε : Evolution)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hi : Integrable f)
    (C : ℝ) (hC : ∀ D, ‖f D‖ ≤ C) :
    Tendsto (fun h : ℝ => (∫ D, polePV h D * f D,
      -diamond.eta ε * ∫ D, polePoisson h D * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 ((∫ D in Ioi (0 : ℝ), symmetricTest f D),
        -diamond.eta ε * (Real.pi * f 0))) :=
  (pole_pv_test_limit hf hi).prodMk_nhds
    ((pole_poisson_test_limit hf.continuous C hC).const_mul (-diamond.eta ε))

end Diamond

/-- A tested opposite-side numerator with its first two height coefficients
and a uniform little-o remainder. A nonzero zeroth shell coefficient
precludes a finite limit, and its vanishing leaves the stated contact term. -/
theorem opposite_shell_height_expansion {f₀ f₁ : ℝ → ℝ} {rem : ℝ → ℝ → ℝ}
    {err : ℝ → ℝ} (h₀ : Continuous f₀) (h₁ : Continuous f₁)
    {C₀ C₁ M : ℝ} (hC₀ : ∀ D, ‖f₀ D‖ ≤ C₀) (hC₁ : ∀ D, ‖f₁ D‖ ≤ C₁)
    (hM : ∀ D, |D| ≤ 1 → ‖evenShellTest f₀ D - f₀ 0‖ ≤ M * D ^ 2)
    (hrem : ∀ h > 0, Measurable (rem h))
    (hunif : ∀ h > 0, ∀ D, ‖rem h D‖ ≤ h * err h)
    (herr : Tendsto err (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    let T (h : ℝ) := ∫ D : ℝ, oppositeShellKernel h D * (f₀ D + h * f₁ D + rem h D)
    Tendsto (fun h => T h - Real.pi / h * f₀ 0)
      (𝓝[>] (0 : ℝ)) (𝓝 ((∫ D, shellFinitePartTest f₀ D) + Real.pi * f₁ 0)) ∧
      (f₀ 0 ≠ 0 → ∀ L : ℝ, ¬ Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 L)) := by
  let T (h : ℝ) := ∫ D : ℝ, oppositeShellKernel h D * (f₀ D + h * f₁ D + rem h D)
  let U (h : ℝ) := ∫ D : ℝ, oppositeShellKernel h D * rem h D
  let K := (∫ D, shellFinitePartTest f₀ D) + Real.pi * f₁ 0
  have U₀ : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (by simpa using herr.const_mul Real.pi)
      (Eventually.of_forall fun _ => norm_nonneg _)
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hK := opposite_shell_kernel_integrable hh'
    have hb : ‖U h‖ ≤ ∫ D, (h * err h) * oppositeShellKernel h D :=
      norm_integral_le_of_norm_le (hK.const_mul (h * err h))
      (Eventually.of_forall fun D => by
        have hk : 0 ≤ oppositeShellKernel h D := by unfold oppositeShellKernel; positivity
        rw [norm_mul, Real.norm_of_nonneg hk, mul_comm (h * err h)]
        exact mul_le_mul_of_nonneg_left (hunif h hh' D) hk)
    rw [integral_const_mul, opposite_shell_kernel_mass hh'] at hb
    rwa [show h * err h * (Real.pi / h) = Real.pi * err h by field_simp] at hb
  have heq : (fun h : ℝ => T h - Real.pi / h * f₀ 0) =ᶠ[𝓝[>] 0]
      (fun h : ℝ =>
        ((∫ D, oppositeShellKernel h D * f₀ D) - Real.pi / h * f₀ 0) +
          (∫ D, polePoisson h D * f₁ D) + U h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hK := opposite_shell_kernel_integrable hh'
    have hb {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ D, ‖f D‖ ≤ C) :
        Integrable (fun D => oppositeShellKernel h D * f D) := by
      simpa only [mul_comm] using hK.bdd_mul hm.aestronglyMeasurable ⟨C, hC⟩
    have hf₀ := hb h₀.measurable hC₀
    have hf₁ := hb (f := fun D => h * f₁ D)
      (continuous_const.mul h₁).measurable (C := h * C₁) (fun D => by
      rw [norm_mul, Real.norm_of_nonneg hh'.le]
      exact mul_le_mul_of_nonneg_left (hC₁ D) hh'.le)
    have hR := hb (hrem h hh') (hunif h hh')
    have hT : (∫ D, oppositeShellKernel h D * (f₀ D + h * f₁ D + rem h D)) =
        (∫ D, oppositeShellKernel h D * f₀ D) +
        (∫ D, oppositeShellKernel h D * (h * f₁ D)) +
        (∫ D, oppositeShellKernel h D * rem h D) := by
      simp_rw [mul_add]
      rw [integral_add _ hR, integral_add hf₀ hf₁]
      simpa only [Pi.add_apply] using hf₀.add hf₁
    have hP : (∫ D, oppositeShellKernel h D * (h * f₁ D)) =
        ∫ D, polePoisson h D * f₁ D := by
      apply integral_congr_ae
      exact Eventually.of_forall fun D => by unfold oppositeShellKernel polePoisson; ring
    dsimp [T, U]
    rw [hT, hP]
    ring
  have hlim := ((opposite_shell_finite_part_limit h₀ hC₀ hM).add
    (pole_poisson_test_limit h₁ C₁ hC₁)).add U₀
  rw [add_zero] at hlim
  have hlim' : Tendsto (fun h => T h - Real.pi / h * f₀ 0) (𝓝[>] 0) (𝓝 K) :=
    hlim.congr' heq.symm
  refine ⟨hlim', fun hn L hL => ?_⟩
  have hh₀ : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hdist : Tendsto (fun h => h * (T h - Real.pi / h * f₀ 0))
      (𝓝[>] 0) (𝓝 0) := by simpa using hh₀.mul hlim'
  have hp : Tendsto (fun h : ℝ => Real.pi * f₀ 0) (𝓝[>] 0) (𝓝 0) := by
    have hL₀ : Tendsto (fun h => h * T h) (𝓝[>] 0) (𝓝 0) := by simpa using hh₀.mul hL
    have hz := hL₀.sub hdist
    rw [sub_zero] at hz
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    change h * T h - h * (T h - Real.pi / h * f₀ 0) = Real.pi * f₀ 0
    field_simp [hh'.ne']; ring
  exact (mul_ne_zero Real.pi_ne_zero hn) (tendsto_nhds_unique hp tendsto_const_nhds).symm

end UV.SectorPlane
