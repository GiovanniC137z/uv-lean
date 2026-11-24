import UV.ContinueSewnFlagDisplacementAtoms

/-! A surviving displacement atom obstructs absolute ultraviolet
convergence under the manuscript's lower hard-channel weight. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology
namespace UV.SewnFlags

private theorem hard_cube_integrable_tail {f : ScalarMomentum → ℝ} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ k in hardCube R, f k) atTop (𝓝 0) := by
  let F := fun R : ℝ => (hardCube R).indicator f
  have hm (R : ℝ) : AEStronglyMeasurable (F R) volume :=
    hf.aestronglyMeasurable.indicator (hardCube_measurable R)
  have hb (R : ℝ) (k : ScalarMomentum) : ‖F R k‖ ≤ ‖f k‖ := by
    by_cases hk : k ∈ hardCube R <;> simp [F,hk]
  have hl (k : ScalarMomentum) : Tendsto (fun R => F R k) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact (hardCube_eventually_excludes k).mono fun R hk => (indicator_of_notMem hk f).symm
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (F := F)
    (f := fun _ => (0:ℝ)) (fun k => ‖f k‖)
    (Eventually.of_forall hm) (Eventually.of_forall fun R => ae_of_all _ (hb R)) hf.norm (ae_of_all _ hl)
  simpa only [F,integral_indicator (hardCube_measurable _),integral_zero] using h

private theorem hard_weight_scale {p R : ℝ} (hp : p ≤ 4) (hR : 1 ≤ R)
    {k : ScalarMomentum} (hk : k ∈ hardCube R) :
    ((4:ℝ)^4)⁻¹*(R^4)⁻¹ ≤ ‖k‖^(-p) := by
  have hR₀ : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hl,hu⟩ := hardCube_norm_bounds hR₀.le hk
  calc
    _ = (4*R)^(-4:ℝ) := by
      rw [rpow_neg (by positivity : 0 ≤ 4*R),show (4*R)^(4:ℝ) = (4*R)^4 by norm_num, mul_pow, mul_inv]
    _ ≤ ‖k‖^(-4:ℝ) := rpow_le_rpow_of_nonpos (hR₀.trans_le hl) hu (by norm_num)
    _ ≤ _ := rpow_le_rpow_of_exponent_le (hR.trans hl) (neg_le_neg hp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem marked_atom_forces_bare_divergence_bounded (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1)
    {d : ScalarMomentum} (hd : (μ.withDensityᵥ h) {d} ≠ 0)
    (W : ScalarMomentum → ℝ) (hW : Measurable W) (hW₀ : ∀ k, 0 ≤ W k)
    {p c R₀ : ℝ} (hp : p ≤ 4) (hc : 0 < c)
    (hLower : ∀ R ≥ R₀, ∀ k ∈ hardCube R, c*‖k‖^(-p) ≤ W k) :
    (∫⁻ k, ENNReal.ofReal (W k * ‖markedAmplitude μ h k‖^2)) = ⊤ := by
  let A := fun k => ‖markedAmplitude μ h k‖^2
  let f := fun k => W k * A k
  let C := c / (4:ℝ)^4
  let δ := ∑' e, ‖(μ.withDensityᵥ h) {e}‖^2
  have hC : 0 < C := by unfold C; positivity
  have hδ : 0 < δ := marked_atomic_sum_positive μ h hm h₁ hd
  have hA : StronglyMeasurable A := (markedAmplitude_stronglyMeasurable μ h hm).norm.pow 2
  have hf : StronglyMeasurable f := hW.stronglyMeasurable.mul hA
  have hf₀ (k : ScalarMomentum) : 0 ≤ f k := mul_nonneg (hW₀ k) (sq_nonneg _)
  have hM : Tendsto (fun R : ℝ => (R^4)⁻¹ * ∫ k in hardCube R, A k) atTop (𝓝 δ) :=
    marked_hard_cube_atomic_limit μ h hm.aestronglyMeasurable (ae_of_all _ h₁)
  have ha : ∀ᶠ R : ℝ in atTop, δ/2 < (R^4)⁻¹ * ∫ k in hardCube R, A k :=
    hM.eventually_const_lt (half_lt_self hδ)
  by_contra hfin
  have hi : Integrable f :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable (ae_of_all _ hf₀)).mp hfin
  have ht := (hard_cube_integrable_tail hi).eventually_lt_const (mul_pos hC (half_pos hδ))
  have hfalse : ∀ᶠ _ : ℝ in atTop, False := by
    filter_upwards [eventually_ge_atTop (max R₀ 1),ha,ht] with R hR hAv hTail
    have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR₁ : 1 ≤ R := (le_max_right _ _).trans hR
    haveI : IsFiniteMeasure (volume.restrict (hardCube R)) :=
      ⟨by rw [Measure.restrict_apply_univ,hardCube_volume _ (zero_le_one.trans hR₁)]; exact ENNReal.ofReal_lt_top⟩
    have hAi : IntegrableOn A (hardCube R) := by
      apply Integrable.of_bound hA.aestronglyMeasurable ((μ.real univ)^2)
      filter_upwards with k
      unfold A
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) ENNReal.toReal_nonneg).mpr (markedAmplitude_norm_le μ h h₁ k)
    have hL (k : ScalarMomentum) (hk : k ∈ hardCube R) : (C*(R^4)⁻¹)*A k ≤ f k := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply le_trans _ (hLower R hR₀ k hk)
      unfold C
      rw [div_eq_mul_inv,mul_assoc]
      exact mul_le_mul_of_nonneg_left (hard_weight_scale hp hR₁ hk) hc.le
    have hI := setIntegral_mono_on (hAi.const_mul (C*(R^4)⁻¹)) hi.integrableOn (hardCube_measurable R) hL
    rw [integral_const_mul,mul_assoc] at hI
    exact (not_lt_of_ge ((mul_lt_mul_of_pos_left hAv hC).le.trans hI)) hTail
  exact hfalse.exists.choose_spec

/-- A nonzero atom forces infinite positive bare energy when the
sewing factor has the stated lower bound on all sufficiently large hard cubes. -/
theorem marked_atom_forces_bare_divergence (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : AEStronglyMeasurable h μ) (h₁ : ∀ᵐ d ∂μ, ‖h d‖ ≤ 1)
    {d : ScalarMomentum} (hd : (μ.withDensityᵥ h) {d} ≠ 0)
    (W : ScalarMomentum → ℝ) (hW : Measurable W) (hW₀ : ∀ k, 0 ≤ W k)
    {p c R₀ : ℝ} (hp : p ≤ 4) (hc : 0 < c)
    (hLower : ∀ R ≥ R₀, ∀ k ∈ hardCube R, c*‖k‖^(-p) ≤ W k) :
    (∫⁻ k, ENNReal.ofReal (W k * ‖markedAmplitude μ h k‖^2)) = ⊤ := by
  obtain ⟨g,hg,hg₁,ha,hv⟩ := marked_bounded_density_version μ h hm h₁
  rw [hv] at hd
  simp_rw [ha]
  exact marked_atom_forces_bare_divergence_bounded μ g hg hg₁ hd W hW hW₀ hp hc hLower

end UV.SewnFlags
