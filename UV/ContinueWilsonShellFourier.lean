import UV.ContinueWilsonFourierHeat

/-! Angular-frequency estimates for the actual projected mark. Gaussian
windows and positivity give an L² estimate for every bounded marked
single-shell amplitude and an L¹ estimate for a two-mark product. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Real
open scoped Topology ENNReal RealInnerProductSpace ComplexConjugate

namespace UV

def wilsonMarkedTransform (μ : Measure OSFourSpace) (f : OSFourSpace → ℂ) (p : OSFourSpace) : ℂ :=
  ∫ x, thinPlaneWave p x * f x ∂μ

theorem wilson_wave_norm (p x : OSFourSpace) : ‖thinPlaneWave p x‖ = 1 := by
  simp [thinPlaneWave,Complex.norm_exp,Complex.mul_re]

theorem wilson_wave_difference (p x y : OSFourSpace) :
    thinPlaneWave p (x-y) = thinPlaneWave p x * conj (thinPlaneWave p y) := by
  simp only [thinPlaneWave,inner_sub_right,Complex.ofReal_sub,←Complex.exp_conj,←Complex.exp_add,
    map_mul,Complex.conj_I,Complex.conj_ofReal]
  congr 1
  ring

theorem wilson_marked_transform_measurable (μ : Measure OSFourSpace) [SFinite μ]
    {f : OSFourSpace → ℂ} (hf : Measurable f) : Measurable (wilsonMarkedTransform μ f) := by
  have hm : Measurable (fun z : OSFourSpace × OSFourSpace => thinPlaneWave z.1 z.2 * f z.2) :=
    (show Continuous (fun z : OSFourSpace × OSFourSpace => thinPlaneWave z.1 z.2) by unfold thinPlaneWave; fun_prop).measurable.mul
      (hf.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem wilson_marked_transform_bound (μ : Measure OSFourSpace) [IsProbabilityMeasure μ]
    {f : OSFourSpace → ℂ} {B : ℝ} (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) (p : OSFourSpace) :
    ‖wilsonMarkedTransform μ f p‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const B) ?_).trans_eq (by simp)
  simpa only [norm_mul,wilson_wave_norm,one_mul] using hb

theorem wilson_marked_transform_square (μ : Measure OSFourSpace) (f : OSFourSpace → ℂ) (p : OSFourSpace) [SFinite μ] :
    ((‖wilsonMarkedTransform μ f p‖^2:ℝ):ℂ) =
      ∫ z : OSFourSpace × OSFourSpace, thinPlaneWave p (z.1-z.2) * (f z.1*conj (f z.2)) ∂μ.prod μ := by
  rw [←Complex.normSq_eq_norm_sq,←Complex.mul_conj,wilsonMarkedTransform,←integral_conj,←integral_prod_mul]
  congr 1
  funext z
  rw [wilson_wave_difference,map_mul]
  ring

private theorem wilson_heat_pair_fubini (μ : Measure OSFourSpace) [IsProbabilityMeasure μ]
    {f : OSFourSpace → ℂ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : OSFourSpace × (OSFourSpace × OSFourSpace) => (wilsonHeatWindow t v.1:ℂ) *
      thinPlaneWave v.1 (v.2.1-v.2.2) * (f v.2.1*conj (f v.2.2))) (volume.prod (μ.prod μ)) := by
  have hc : Continuous (fun v : OSFourSpace × (OSFourSpace × OSFourSpace) =>
      (wilsonHeatWindow t v.1:ℂ)*thinPlaneWave v.1 (v.2.1-v.2.2)) := by unfold wilsonHeatWindow thinPlaneWave; fun_prop
  have hm := hc.measurable.mul ((hf.comp (measurable_fst.comp measurable_snd)).mul
    (Complex.continuous_conj.measurable.comp (hf.comp (measurable_snd.comp measurable_snd))))
  have hz : ∀ᵐ z ∂μ.prod μ, ‖f z.1‖ ≤ B ∧ ‖f z.2‖ ≤ B :=
    ((quasiMeasurePreserving_fst (ν := μ)).ae hb).and ((quasiMeasurePreserving_snd (μ := μ)).ae hb)
  apply ((wilson_heat_window_integrable ht).mul_prod (integrable_const (μ := μ.prod μ) (B^2))).mono' hm.aestronglyMeasurable
  filter_upwards [(quasiMeasurePreserving_snd (μ := (volume : Measure OSFourSpace))).ae hz] with v hv
  change ‖(wilsonHeatWindow t v.1:ℂ)*thinPlaneWave v.1 (v.2.1-v.2.2)*(f v.2.1*conj (f v.2.2))‖ ≤ wilsonHeatWindow t v.1*B^2
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (wilson_heat_window_pos t v.1).le,
    wilson_wave_norm,mul_one,Complex.norm_conj,pow_two]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hv.1 hv.2 (norm_nonneg _) hB) (Real.exp_pos _).le

private theorem wilson_heat_transform_identity (μ : Measure OSFourSpace) [IsProbabilityMeasure μ]
    {f : OSFourSpace → ℂ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B)
    {t : ℝ} (ht : 0 < t) :
    ((∫ p, wilsonHeatWindow t p * ‖wilsonMarkedTransform μ f p‖^2 : ℝ):ℂ) =
      ∫ z : OSFourSpace × OSFourSpace, (wilsonHeatKernel t (z.1-z.2):ℂ)*(f z.1*conj (f z.2)) ∂μ.prod μ := by
  rw [←integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul,wilson_marked_transform_square,←integral_const_mul]
  calc
    _ = ∫ z : OSFourSpace × OSFourSpace, ∫ p, (wilsonHeatWindow t p:ℂ) *
        thinPlaneWave p (z.1-z.2) * (f z.1*conj (f z.2)) ∂volume ∂μ.prod μ := by
      simp_rw [mul_assoc]
      apply integral_integral_swap
      simpa only [Function.uncurry,mul_assoc] using wilson_heat_pair_fubini μ hf hB hb ht
    _ = _ := by
      congr 1
      funext z
      rw [integral_mul_const,wilson_heat_fourier ht]

theorem wilson_heat_transform_bound (μ : Measure OSFourSpace) [IsProbabilityMeasure μ]
    {C : ℝ≥0∞} (hμ : μ ≤ C • volume) (hC : C ≠ ⊤)
    {f : OSFourSpace → ℂ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (∫ p, wilsonHeatWindow t p * ‖wilsonMarkedTransform μ f p‖^2) ≤ B^2*(C.toReal*(2*π)^4) := by
  let ν := (μ.prod μ).map (fun z : OSFourSpace × OSFourSpace => z.1-z.2)
  have hν : ν ≤ C • volume := by
    have h := wilson_translated_density_bound (F := id) (G := fun y : OSFourSpace => -y)
      (μ := μ) (ν := μ) measurable_id measurable_neg (by simpa only [Measure.map_id] using hμ)
    simpa only [ν,id_eq,sub_eq_add_neg] using h
  have hm : Measurable (fun z : OSFourSpace × OSFourSpace => z.1-z.2) := measurable_fst.sub measurable_snd
  have hc : Continuous (wilsonHeatKernel t) := by unfold wilsonHeatKernel wilsonHeatWindow; fun_prop
  have hi : Integrable (wilsonHeatKernel t) ν := ((wilson_heat_kernel_integrable ht).smul_measure hC).mono_measure hν
  have hai := (integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable).mp hi
  have hx := (quasiMeasurePreserving_fst (ν := μ)).ae hb
  have hy := (quasiMeasurePreserving_snd (μ := μ)).ae hb
  calc
    _ = ‖((∫ p, wilsonHeatWindow t p*‖wilsonMarkedTransform μ f p‖^2 : ℝ):ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_of_nonneg (integral_nonneg fun p => mul_nonneg (wilson_heat_window_pos t p).le (sq_nonneg ‖wilsonMarkedTransform μ f p‖))]
    _ ≤ ∫ z : OSFourSpace × OSFourSpace, ‖(wilsonHeatKernel t (z.1-z.2):ℂ)*(f z.1*conj (f z.2))‖ ∂μ.prod μ := by
      rw [wilson_heat_transform_identity μ hf hB hb ht]
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ z : OSFourSpace × OSFourSpace, B^2*wilsonHeatKernel t (z.1-z.2) ∂μ.prod μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hai.const_mul _)
      filter_upwards [hx,hy] with z hz hy'
      rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg (wilson_heat_kernel_pos ht _).le,mul_comm (B^2),pow_two]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hz hy' (norm_nonneg _) hB) (wilson_heat_kernel_pos ht _).le
    _ ≤ _ := by
      rw [integral_const_mul,←integral_map hm.aemeasurable hc.aestronglyMeasurable]
      exact mul_le_mul_of_nonneg_left (wilson_heat_kernel_measure_bound hν hC ht) (sq_nonneg _)

/-- Removing the Gaussian momentum window gives an absolutely integrable
squared transform for every bounded mark of a volume-dominated probability. -/
theorem wilson_marked_transform_square_integrable (μ : Measure OSFourSpace) [IsProbabilityMeasure μ]
    {C : ℝ≥0∞} (hμ : μ ≤ C • volume) (hC : C ≠ ⊤)
    {f : OSFourSpace → ℂ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    Integrable (fun p => ‖wilsonMarkedTransform μ f p‖^2) := by
  let g := fun p => ‖wilsonMarkedTransform μ f p‖^2
  let t := fun n : ℕ => 1/((n:ℝ)+1)
  let F := fun n p => wilsonHeatWindow (t n) p * g p
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hg : Measurable g := (wilson_marked_transform_measurable μ hf).norm.pow_const 2
  have hpos (n : ℕ) (p : OSFourSpace) : 0 ≤ F n p := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hmeas (n : ℕ) : Measurable (F n) :=
    (show Continuous (wilsonHeatWindow (t n)) by unfold wilsonHeatWindow; fun_prop).measurable.mul hg
  have hi (n : ℕ) : Integrable (F n) := by
    apply ((wilson_heat_window_integrable (ht n)).mul_const (B^2)).mono' (hmeas n).aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    rw [Real.norm_of_nonneg (hpos n p)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (wilson_marked_transform_bound μ hb p)
  have htend (p : OSFourSpace) : Tendsto (fun n => ENNReal.ofReal (F n p)) atTop (𝓝 (ENNReal.ofReal (g p))) := by
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.neg.mul_const (‖p‖^2)).rexp).mul_const (g p)
    simpa only [F,t,wilsonHeatWindow,neg_zero,zero_mul,Real.exp_zero,one_mul] using h
  apply (lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable (Eventually.of_forall fun _ => sq_nonneg _)).mp
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  calc
    _ = ∫⁻ p, liminf (fun n => ENNReal.ofReal (F n p)) atTop := lintegral_congr (fun p => (htend p).liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le (fun n => (hmeas n).ennreal_ofReal)
    _ ≤ ENNReal.ofReal (B^2*(C.toReal*(2*π)^4)) := by
      apply liminf_le_of_frequently_le'
      apply Frequently.of_forall
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hpos n))]
      exact ENNReal.ofReal_le_ofReal (wilson_heat_transform_bound μ hμ hC hf hB hb (ht n))

end UV
