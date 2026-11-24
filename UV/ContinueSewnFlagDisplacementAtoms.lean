import UV.ContinueSewnFlagHardCube
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The positive sewn hard-channel test for Hilbert-valued marked
amplitudes. Four-dimensional cube averages retain exactly the squared
masses of displacement atoms. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace ComplexConjugate
namespace UV.SewnFlags

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]

def markedAmplitude (μ : Measure ScalarMomentum) (h : ScalarMomentum → E) (k : ScalarMomentum) : E :=
  ∫ d, stableFourierPhase d k • h d ∂μ

theorem marked_bounded_density_version (μ : Measure ScalarMomentum) (h : ScalarMomentum → E)
    (hm : AEStronglyMeasurable h μ) (h₁ : ∀ᵐ d ∂μ, ‖h d‖ ≤ 1) :
    ∃ g : ScalarMomentum → E, StronglyMeasurable g ∧ (∀ d, ‖g d‖ ≤ 1) ∧
      markedAmplitude μ h = markedAmplitude μ g ∧ μ.withDensityᵥ h = μ.withDensityᵥ g := by
  let v := hm.mk h
  let S := {d | ‖v d‖ ≤ 1}
  let g := S.indicator v
  have hS : MeasurableSet S := measurableSet_le hm.stronglyMeasurable_mk.norm.measurable measurable_const
  have heg : h =ᵐ[μ] g := by
    filter_upwards [hm.ae_eq_mk,h₁] with d hd hd₁
    change h d = v d at hd
    change h d = S.indicator v d
    have hmem : d ∈ S := by change ‖v d‖ ≤ 1; rw [← hd]; exact hd₁
    rwa [indicator_of_mem hmem]
  refine ⟨g,hm.stronglyMeasurable_mk.indicator hS,?_,?_,WithDensityᵥEq.congr_ae heg⟩
  · intro d
    change ‖S.indicator v d‖ ≤ 1
    by_cases hd : d ∈ S
    · rw [indicator_of_mem hd]
      exact hd
    · rw [indicator_of_notMem hd,norm_zero]
      exact zero_le_one
  · funext k
    unfold markedAmplitude
    apply integral_congr_ae
    exact heg.mono fun d hd => congrArg (fun w : E => stableFourierPhase d k • w) hd

private theorem polarizationPhase (d e k : ScalarMomentum) :
    conj (stableFourierPhase d k) * stableFourierPhase e k = stableFourierPhase (e-d) k := by
  unfold stableFourierPhase
  rw [← Complex.exp_conj,← Complex.exp_add,inner_sub_left]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

private theorem phase_comp {X : Type*} [TopologicalSpace X] (a b : X → ScalarMomentum)
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => stableFourierPhase (a x) (b x)) := by
  unfold stableFourierPhase
  fun_prop

omit [NormedSpace ℝ E] in
private theorem marked_inner_kernel_bound (h : ScalarMomentum → E) (h₁ : ∀ d, ‖h d‖ ≤ 1)
    (d e : ScalarMomentum) : ‖⟪h d,h e⟫_ℂ‖ ≤ 1 :=
  (norm_inner_le_norm _ _).trans (mul_le_one₀ (h₁ _) (norm_nonneg _) (h₁ _))

omit [NormedSpace ℝ E] in
theorem marked_phase_integrable (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) (k : ScalarMomentum) :
    Integrable (fun d => stableFourierPhase d k • h d) μ := by
  have hφ : Measurable (fun d => stableFourierPhase d k) :=
    (phase_comp id (fun _ => k) continuous_id continuous_const).measurable
  have hh : StronglyMeasurable (fun d => stableFourierPhase d k • h d) := hφ.stronglyMeasurable.smul hm
  apply Integrable.of_bound hh.aestronglyMeasurable 1
  filter_upwards with d
  rw [norm_smul,stableFourierPhase_norm,one_mul]
  exact h₁ d

theorem markedAmplitude_stronglyMeasurable (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) : StronglyMeasurable (markedAmplitude μ h) := by
  have hφ : Continuous (fun q : ScalarMomentum × ScalarMomentum => stableFourierPhase q.2 q.1) :=
    phase_comp Prod.snd Prod.fst continuous_snd continuous_fst
  have ha : StronglyMeasurable (fun q : ScalarMomentum × ScalarMomentum => stableFourierPhase q.2 q.1 • h q.2) :=
    hφ.measurable.stronglyMeasurable.smul (hm.comp_measurable measurable_snd)
  exact ha.integral_prod_right'

theorem markedAmplitude_norm_le (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (h₁ : ∀ d, ‖h d‖ ≤ 1) (k : ScalarMomentum) :
    ‖markedAmplitude μ h k‖ ≤ μ.real univ := by
  unfold markedAmplitude
  have hB (d : ScalarMomentum) : ‖stableFourierPhase d k • h d‖ ≤ 1 := by
    rw [norm_smul,stableFourierPhase_norm,one_mul]
    exact h₁ d
  simpa only [one_mul] using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hB)

variable [CompleteSpace E]

private theorem marked_norm_fourier_pairing (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) (k : ScalarMomentum) :
    (‖markedAmplitude μ h k‖^2 : ℝ) =
      (∫ p, stableFourierPhase (p.2-p.1) k * ⟪h p.1,h p.2⟫_ℂ ∂μ.prod μ).re := by
  let F := fun d => stableFourierPhase d k • h d
  let A := markedAmplitude μ h k
  have hF : Integrable F μ := marked_phase_integrable μ h hm h₁ k
  have hLeft (x : E) : (∫ d, ⟪F d,x⟫_ℂ ∂μ) = ⟪A,x⟫_ℂ := by
    have hh (d : ScalarMomentum) : ⟪F d,x⟫_ℂ = conj ⟪x,F d⟫_ℂ := (inner_conj_symm _ _).symm
    simp_rw [hh]
    rw [integral_conj,integral_inner hF]
    exact inner_conj_symm _ _
  let G := fun p : ScalarMomentum × ScalarMomentum =>
    stableFourierPhase (p.2-p.1) k * ⟪h p.1,h p.2⟫_ℂ
  have hG : Integrable G (μ.prod μ) := by
    have hd : Continuous (fun p : ScalarMomentum × ScalarMomentum => p.2-p.1) := continuous_snd.sub continuous_fst
    have hφ : Continuous (fun p : ScalarMomentum × ScalarMomentum => stableFourierPhase (p.2-p.1) k) :=
      phase_comp _ (fun _ => k) hd continuous_const
    have hm' : StronglyMeasurable (fun p : ScalarMomentum × ScalarMomentum => ⟪h p.1,h p.2⟫_ℂ) :=
      (hm.comp_measurable measurable_fst).inner (hm.comp_measurable measurable_snd)
    have hi : StronglyMeasurable G := hφ.measurable.stronglyMeasurable.mul hm'
    apply Integrable.of_bound hi.aestronglyMeasurable 1
    filter_upwards with p
    dsimp only [G]
    rw [norm_mul,stableFourierPhase_norm,one_mul]
    exact marked_inner_kernel_bound h h₁ p.1 p.2
  change ‖A‖^2 = (∫ p, G p ∂μ.prod μ).re
  rw [MeasureTheory.integral_prod G hG]
  have hP (d e : ScalarMomentum) : G (d,e) = ⟪F d,F e⟫_ℂ := by
    dsimp only [G,F]
    rw [inner_smul_left,inner_smul_right,← mul_assoc,polarizationPhase]
  simp_rw [hP,integral_inner hF,hLeft]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) A)

private theorem marked_cube_pairing (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1)
    {R : ℝ} (hR : 0 < R) :
    (∫ k, ‖markedAmplitude μ h k‖^2 ∂hardCubeMeasure R) =
      ∫ p, (hardCubePhaseMean R (p.2-p.1) * ⟪h p.1,h p.2⟫_ℂ).re ∂μ.prod μ := by
  let P := ScalarMomentum × ScalarMomentum
  let τ := hardCubeMeasure R
  letI : IsFiniteMeasure τ := ⟨by change hardCubeMeasure R univ < ⊤; rw [hardCubeMeasure_univ hR]; exact ENNReal.one_lt_top⟩
  let G := fun (q : ScalarMomentum × P) =>
    stableFourierPhase (q.2.2-q.2.1) q.1 * ⟪h q.2.1,h q.2.2⟫_ℂ
  have hG : Integrable G (τ.prod (μ.prod μ)) := by
    have hφ : Continuous (fun q : ScalarMomentum × P => stableFourierPhase (q.2.2-q.2.1) q.1) := by
      have hE : Continuous (Prod.snd : P → ScalarMomentum) := continuous_snd
      have hD : Continuous (Prod.fst : P → ScalarMomentum) := continuous_fst
      exact phase_comp (fun q : ScalarMomentum × P => q.2.2-q.2.1) Prod.fst
        ((hE.comp continuous_snd).sub (hD.comp continuous_snd)) continuous_fst
    have hm' : StronglyMeasurable (fun q : ScalarMomentum × P => ⟪h q.2.1,h q.2.2⟫_ℂ) :=
      (hm.comp_measurable (measurable_fst.comp measurable_snd)).inner
        (hm.comp_measurable (measurable_snd.comp measurable_snd))
    have hi : StronglyMeasurable G := hφ.measurable.stronglyMeasurable.mul hm'
    apply Integrable.of_bound hi.aestronglyMeasurable 1
    filter_upwards with p
    dsimp only [G]
    rw [norm_mul,stableFourierPhase_norm,one_mul]
    exact marked_inner_kernel_bound h h₁ p.2.1 p.2.2
  have hL (k : ScalarMomentum) : ‖markedAmplitude μ h k‖^2 = (∫ p, G (k,p) ∂μ.prod μ).re :=
    marked_norm_fourier_pairing μ h hm h₁ k
  have hR' (p : P) : (∫ k, G (k,p) ∂τ) = hardCubePhaseMean R (p.2-p.1) * ⟪h p.1,h p.2⟫_ℂ := by
    dsimp only [G,hardCubePhaseMean]
    rw [integral_mul_const]
  simp_rw [hL]
  change (∫ k, RCLike.re (∫ p, G (k,p) ∂μ.prod μ) ∂τ) = _
  rw [integral_re hG.integral_prod_left,integral_integral_swap (f := fun k p => G (k,p)) hG]
  rw [← integral_re hG.integral_prod_right]
  simp_rw [hR']
  rfl

private theorem marked_cube_pairing_diagonal (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) :
    Tendsto (fun R : ℝ => ∫ k, ‖markedAmplitude μ h k‖^2 ∂hardCubeMeasure R) atTop
      (𝓝 (∫ d, μ.real {d} * ‖h d‖^2 ∂μ)) := by
  classical
  let P := ScalarMomentum × ScalarMomentum
  let F := fun (R : ℝ) (p : P) => (hardCubePhaseMean R (p.2-p.1) * ⟪h p.1,h p.2⟫_ℂ).re
  let g := fun p : P => if p.1 = p.2 then ‖h p.1‖^2 else 0
  have hFm (R : ℝ) : StronglyMeasurable (F R) := by
    apply Complex.continuous_re.comp_stronglyMeasurable
    exact ((hardCubePhaseMean_measurable R).comp (measurable_snd.sub measurable_fst)).stronglyMeasurable.mul
      ((hm.comp_measurable measurable_fst).inner (hm.comp_measurable measurable_snd))
  have hF1 {R : ℝ} (hR : 0 < R) (p : P) : ‖F R p‖ ≤ 1 := by
    unfold F
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_one₀ (hardCubePhaseMean_bound hR _) (norm_nonneg _) (marked_inner_kernel_bound h h₁ _ _)
  have hf (p : P) : Tendsto (fun R => F R p) atTop (𝓝 (g p)) := by
    have h' := Complex.continuous_re.continuousAt.tendsto.comp
      ((hardCubePhaseMean_limit (p.2-p.1)).mul_const ⟪h p.1,h p.2⟫_ℂ)
    by_cases he : p.1 = p.2
    · simpa [F,g,he,Function.comp_def,inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h'
    · simpa [F,g,he,Function.comp_def,sub_eq_zero,Ne.symm he] using h'
  have hLim := tendsto_integral_filter_of_dominated_convergence (μ := μ.prod μ) (F := F) (f := g) (fun _ => 1)
    (Eventually.of_forall fun R => (hFm R).aestronglyMeasurable)
    ((eventually_gt_atTop (0:ℝ)).mono fun _ hR => ae_of_all _ (hF1 hR)) (integrable_const _) (ae_of_all _ hf)
  have hg : Integrable g (μ.prod μ) := by
    have hd : MeasurableSet {p : P | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
    have hm' : StronglyMeasurable g := by
      have he : {p : P | p.1 = p.2}.indicator (fun p => ‖h p.1‖^2) = g := by
        funext p
        by_cases hp : p.1 = p.2 <;> simp [g,hp]
      rw [← he]
      exact ((hm.comp_measurable measurable_fst).norm.pow 2).indicator hd
    apply Integrable.of_bound hm'.aestronglyMeasurable 1
    filter_upwards with p
    by_cases he : p.1 = p.2
    · simp only [g,if_pos he,Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [mul_le_mul_of_nonneg_left (h₁ p.1) (norm_nonneg (h p.1))]
    · simp [g,he]
  have he (d : ScalarMomentum) : (∫ e, g (d,e) ∂μ) = μ.real {d} * ‖h d‖^2 := by
    have hs : (fun e => g (d,e)) = ({d} : Set ScalarMomentum).indicator (fun _ => ‖h d‖^2) := by
      funext e
      simp only [g,indicator_apply,mem_singleton_iff,eq_comm]
    rw [hs,integral_indicator_const _ (measurableSet_singleton d),smul_eq_mul]
  rw [integral_prod g hg] at hLim
  simp_rw [he] at hLim
  apply hLim.congr'
  exact (eventually_gt_atTop (0:ℝ)).mono fun _ hR => (marked_cube_pairing μ h hm h₁ hR).symm

omit [InnerProductSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem marked_diagonal_integrable (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) :
    Integrable (fun d => μ.real {d} * ‖h d‖^2) μ := by
  have hmS : Measurable (fun d => μ.real {d}) := by
    have h' : Measurable (fun d => μ (Prod.mk d ⁻¹' {p : ScalarMomentum × ScalarMomentum | p.1 = p.2})) :=
      measurable_measure_prodMk_left (measurableSet_eq_fun measurable_fst measurable_snd)
    have he (d : ScalarMomentum) : Prod.mk d ⁻¹' {p : ScalarMomentum × ScalarMomentum | p.1 = p.2} = {d} := by
      ext e
      exact eq_comm
    simpa only [he,Measure.real] using h'.ennreal_toReal
  apply Integrable.of_bound (hmS.stronglyMeasurable.mul (hm.norm.pow 2)).aestronglyMeasurable (μ.real univ)
  filter_upwards with d
  change ‖μ.real {d} * ‖h d‖^2‖ ≤ μ.real univ
  have hnonneg : 0 ≤ μ.real {d} * ‖h d‖^2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  have hd : μ.real {d} ≤ μ.real univ := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))
  exact (mul_le_mul_of_nonneg_right hd (sq_nonneg _)).trans (mul_le_of_le_one_right ENNReal.toReal_nonneg
    (by nlinarith [mul_le_mul_of_nonneg_left (h₁ d) (norm_nonneg (h d))]))

omit [InnerProductSpace ℂ E] in
private theorem marked_atom_eq (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) (d : ScalarMomentum) :
    (μ.withDensityᵥ h) {d} = μ.real {d} • h d := by
  have hi : Integrable h μ := Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ h₁)
  rw [withDensityᵥ_apply hi (measurableSet_singleton d),integral_singleton h d]

omit [InnerProductSpace ℂ E] in
private theorem marked_diagonal_eq_atomic_sum (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) :
    (∫ d, μ.real {d} * ‖h d‖^2 ∂μ) = ∑' d, ‖(μ.withDensityᵥ h) {d}‖^2 := by
  classical
  let S := {d : ScalarMomentum | 0 < μ {d}}
  have hS : S.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (fun d => measurableSet_singleton d) (fun _ _ hne => disjoint_singleton.mpr hne)
  let f := fun d : ScalarMomentum => μ.real {d} * ‖h d‖^2
  have hf : Integrable f μ := marked_diagonal_integrable μ h hm h₁
  have hzero (d : ScalarMomentum) (hd : d ∉ S) : μ {d} = 0 := by
    exact nonpos_iff_eq_zero.mp (not_lt.mp hd)
  have hF : S.indicator f = f := by
    funext d
    by_cases hd : d ∈ S
    · rw [indicator_of_mem hd]
    · rw [indicator_of_notMem hd]
      simp [f,Measure.real,hzero d hd]
  have ha := marked_atom_eq μ h hm h₁
  change (∫ d, f d ∂μ) = _
  rw [← hF, integral_indicator hS.measurableSet,integral_countable f hS hf.integrableOn]
  calc
    _ = ∑' d : S, ‖(μ.withDensityᵥ h) {(d:ScalarMomentum)}‖^2 := by
      apply tsum_congr
      intro d
      rw [ha,norm_smul,Real.norm_of_nonneg (show 0 ≤ μ.real {(d:ScalarMomentum)} from ENNReal.toReal_nonneg)]
      unfold f
      rw [smul_eq_mul,mul_pow]
      ring
    _ = _ := by
      apply tsum_subtype_eq_of_support_subset (f := fun d : ScalarMomentum => ‖(μ.withDensityᵥ h) {d}‖^2)
      intro d hd
      by_contra hn
      exact hd (by simp [ha,Measure.real,hzero d hn])

omit [InnerProductSpace ℂ E] in
theorem marked_atomic_sum_positive (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1)
    {d : ScalarMomentum} (hd : (μ.withDensityᵥ h) {d} ≠ 0) :
    0 < ∑' d, ‖(μ.withDensityᵥ h) {d}‖^2 := by
  rw [← marked_diagonal_eq_atomic_sum μ h hm h₁]
  rw [marked_atom_eq μ h hm h₁] at hd
  have hμ : 0 < μ.real {d} := lt_of_le_of_ne ENNReal.toReal_nonneg
    (fun hz => hd (by rw [← hz,zero_smul]))
  have hh : 0 < ‖h d‖ := norm_pos_iff.mpr (fun hz => hd (by rw [hz,smul_zero]))
  have hnonneg (q : ScalarMomentum) : 0 ≤ μ.real {q} * ‖h q‖^2 :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  calc
    _ < ∫ q in ({d} : Set ScalarMomentum), μ.real {q} * ‖h q‖^2 ∂μ := by
      rw [integral_singleton,smul_eq_mul]
      positivity
    _ ≤ _ := setIntegral_le_integral (marked_diagonal_integrable μ h hm h₁) (ae_of_all _ hnonneg)

private theorem marked_hard_cube_atomic_limit_bounded (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : StronglyMeasurable h) (h₁ : ∀ d, ‖h d‖ ≤ 1) :
    Tendsto (fun R : ℝ => (R^4)⁻¹ * ∫ k in hardCube R, ‖markedAmplitude μ h k‖^2) atTop
      (𝓝 (∑' d, ‖(μ.withDensityᵥ h) {d}‖^2)) := by
  have hc := marked_cube_pairing_diagonal μ h hm h₁
  rw [marked_diagonal_eq_atomic_sum μ h hm h₁] at hc
  apply hc.congr'
  apply Eventually.of_forall
  intro R
  dsimp only [hardCubeMeasure]
  have h₄ : 0 ≤ (R^4)⁻¹ := inv_nonneg.mpr (by positivity)
  rw [integral_smul_measure,ENNReal.toReal_ofReal h₄,smul_eq_mul]

/-- The original cube average of the positive Hilbert-channel
amplitude tends to the squared atomic masses of its vector measure. -/
theorem marked_hard_cube_atomic_limit (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (h : ScalarMomentum → E) (hm : AEStronglyMeasurable h μ) (h₁ : ∀ᵐ d ∂μ, ‖h d‖ ≤ 1) :
    Tendsto (fun R : ℝ => (R^4)⁻¹ * ∫ k in hardCube R, ‖markedAmplitude μ h k‖^2) atTop
      (𝓝 (∑' d, ‖(μ.withDensityᵥ h) {d}‖^2)) := by
  obtain ⟨g,hg,hg₁,ha,hv⟩ := marked_bounded_density_version μ h hm h₁
  simp_rw [ha,hv]
  exact marked_hard_cube_atomic_limit_bounded μ g hg hg₁

end UV.SewnFlags
