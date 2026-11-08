import UV.Convergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Positive-depth scalar comparison results. Definitions use the normalized
square-root kernel literally. Source: prop:OQED-depth-stability,
prop:OQED-bubble-depth-monotone and eq:OQED-subtraction-difference-square.
The complex continuation and asymptotic constants require additional proofs. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace UV

theorem kernel_iteratedDeriv_depth (n : ℕ) (M u a : ℝ) :
    iteratedDeriv n (fun b => kernel b M u) a =
      (-depthProfile M u) ^ n * kernel a M u := by
  have hf : (fun b => kernel b M u) =
      (fun b => Real.exp ((-depthProfile M u) * b)) := by
    funext b
    unfold kernel
    congr 1
    ring
  rw [hf, iteratedDeriv_exp_const_mul]
  change (-depthProfile M u) ^ n * Real.exp ((-depthProfile M u) * a) =
    (-depthProfile M u) ^ n * Real.exp (-a * depthProfile M u)
  rw [show (-depthProfile M u) * a = -a * depthProfile M u by ring]

theorem kernel_depth_derivative_bound {a amin amax M Mmax u : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hamax : a ≤ amax)
    (hM : 0 ≤ M) (hMmax : M ≤ Mmax) (hu : 0 ≤ u) (n : ℕ) :
    |iteratedDeriv n (fun b => kernel b M u) a| ≤
      Real.exp (amax * Mmax) * (Real.sqrt u) ^ n *
        Real.exp (-(amin * Real.sqrt u)) := by
  rw [kernel_iteratedDeriv_depth, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (depthProfile_nonneg hM hu), abs_of_pos (kernel_pos _ _ _)]
  have ha0 : 0 ≤ a := hmin.le.trans ha
  have hmax0 : 0 ≤ amax := ha0.trans hamax
  have hpow := pow_le_pow_left₀ (depthProfile_nonneg hM hu)
    (depthProfile_le_sqrt hM hu) n
  have hker := kernel_upper (M := M) ha0 hu
  have hker0 : 0 ≤ kernel a M u := (kernel_pos _ _ _).le
  have hexp : Real.exp (a * M) ≤ Real.exp (amax * Mmax) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul hamax hMmax hM hmax0
  have hdec : Real.exp (-a * Real.sqrt u) ≤ Real.exp (-(amin * Real.sqrt u)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg u]
  calc
    _ ≤ (Real.sqrt u) ^ n *
        (Real.exp (a * M) * Real.exp (-a * Real.sqrt u)) := by gcongr
    _ ≤ (Real.sqrt u) ^ n *
        (Real.exp (amax * Mmax) * Real.exp (-(amin * Real.sqrt u))) := by gcongr
    _ = _ := by ring

theorem kernel_zero_depth_error {a M u : ℝ}
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hu : 0 ≤ u) :
    0 ≤ 1 - kernel a M u ∧ 1 - kernel a M u ≤ a * Real.sqrt u := by
  constructor
  · exact sub_nonneg.mpr (kernel_le_one ha hM hu)
  · have he := Real.add_one_le_exp (-a * depthProfile M u)
    have hd := mul_le_mul_of_nonneg_left (depthProfile_le_sqrt hM hu) ha
    dsimp [kernel]
    linarith

theorem kernel_tendsto_zero_depth (M u : ℝ) :
    Tendsto (fun a => kernel a M u) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun a => kernel a M u) := by unfold kernel; fun_prop
  simpa [kernel] using hc.tendsto 0

abbrev ScalarMomentum := EuclideanSpace ℝ (Fin 4)

def scalarCovariance (a M m : ℝ) (q : ScalarMomentum) : ℝ :=
  kernel a M (‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)

def scalarBubbleIntegrand (a M m : ℝ) (P q : ScalarMomentum) : ℝ :=
  scalarCovariance a M m q * scalarCovariance a M m (q + P)

def scalarBubble (a M m : ℝ) (P : ScalarMomentum) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) * ∫ q, scalarBubbleIntegrand a M m P q

theorem scalarCovariance_nonneg {a M m : ℝ} (q : ScalarMomentum) :
    0 ≤ scalarCovariance a M m q := by
  unfold scalarCovariance
  exact div_nonneg (kernel_pos _ _ _).le (by positivity)

theorem scalarCovariance_continuous {a M m : ℝ} (hm : 0 < m) :
    Continuous (scalarCovariance a M m) := by
  unfold scalarCovariance kernel depthProfile
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro q
    positivity

theorem scalarCovariance_le_mass_bound {a M m : ℝ}
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hm : 0 < m) (q : ScalarMomentum) :
    scalarCovariance a M m q ≤ (m ^ 2)⁻¹ := by
  unfold scalarCovariance
  calc
    kernel a M (‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)
        ≤ 1 / (‖q‖ ^ 2 + m ^ 2) := by
      apply div_le_div_of_nonneg_right (kernel_le_one ha hM (sq_nonneg _))
      positivity
    _ ≤ 1 / (m ^ 2) := by
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      nlinarith [sq_nonneg ‖q‖]
    _ = _ := one_div _

theorem scalarCovariance_exponential_bound {a M m : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (q : ScalarMomentum) :
    scalarCovariance a M m q ≤
      (m ^ 2)⁻¹ * Real.exp (a * M) * Real.exp (-(a * ‖q‖)) := by
  unfold scalarCovariance
  have hk := kernel_upper (M := M) ha (sq_nonneg ‖q‖)
  rw [Real.sqrt_sq (norm_nonneg q), neg_mul] at hk
  calc
    _ ≤ (Real.exp (a * M) * Real.exp (-(a * ‖q‖))) /
        (‖q‖ ^ 2 + m ^ 2) := by gcongr
    _ ≤ (Real.exp (a * M) * Real.exp (-(a * ‖q‖))) / (m ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg ‖q‖]
    _ = _ := by ring

theorem scalarBubbleIntegrand_integrable {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (scalarBubbleIntegrand a M m P) := by
  have he : Integrable (fun q : ScalarMomentum => Real.exp (-(a * ‖q‖))) := by
    simpa using (integrable_norm_pow_exp (μ := volume) ha 0)
  apply (he.const_mul ((m ^ 2)⁻¹ * Real.exp (a * M) * (m ^ 2)⁻¹)).mono'
  · exact ((scalarCovariance_continuous hm).mul
      ((scalarCovariance_continuous hm).comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · filter_upwards with q
    unfold scalarBubbleIntegrand
    rw [Real.norm_of_nonneg (mul_nonneg (scalarCovariance_nonneg q)
      (scalarCovariance_nonneg (q + P)))]
    calc
      _ ≤ ((m ^ 2)⁻¹ * Real.exp (a * M) * Real.exp (-(a * ‖q‖))) *
          (m ^ 2)⁻¹ := by
        exact mul_le_mul (scalarCovariance_exponential_bound ha.le hm q)
          (scalarCovariance_le_mass_bound ha.le hM hm (q + P))
          (scalarCovariance_nonneg _) (by positivity)
      _ = _ := by ring

theorem scalarBubble_nonneg (a M m : ℝ) (P : ScalarMomentum) :
    0 ≤ scalarBubble a M m P := by
  unfold scalarBubble scalarBubbleIntegrand
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro q
  exact mul_nonneg (scalarCovariance_nonneg q) (scalarCovariance_nonneg (q + P))

theorem scalarBubble_antitone_depth {a b M m : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    scalarBubble b M m P ≤ scalarBubble a M m P := by
  unfold scalarBubble
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (scalarBubbleIntegrand_integrable (ha.trans_le hab) hM hm P)
    (scalarBubbleIntegrand_integrable ha hM hm P)
  intro q
  unfold scalarBubbleIntegrand scalarCovariance
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (kernel_antitone_depth hab hM (sq_nonneg _)) (by positivity)
  · exact div_le_div_of_nonneg_right (kernel_antitone_depth hab hM (sq_nonneg _)) (by positivity)
  · exact div_nonneg (kernel_pos _ _ _).le (by positivity)
  · exact div_nonneg (kernel_pos _ _ _).le (by positivity)

theorem scalarCovariance_sq_integrable {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) :
    Integrable (fun q : ScalarMomentum => scalarCovariance a M m q ^ 2) := by
  have h := scalarBubbleIntegrand_integrable ha hM hm (0 : ScalarMomentum)
  unfold scalarBubbleIntegrand at h
  simpa only [add_zero, pow_two] using h

def scalarSubtractedBubble (a M m : ℝ) (P : ScalarMomentum) : ℝ :=
  scalarBubble a M m 0 - scalarBubble a M m P

theorem scalarBubble_difference_square {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    scalarSubtractedBubble a M m P =
      (2 * Real.pi) ^ (-4 : ℤ) / 2 *
        ∫ q, (scalarCovariance a M m q - scalarCovariance a M m (q + P)) ^ 2 := by
  let C := scalarCovariance a M m
  have hc : Integrable (fun q => C q ^ 2) := scalarCovariance_sq_integrable ha hM hm
  have hs : Integrable (fun q => C (q + P) ^ 2) :=
    (measurePreserving_add_right volume P).integrable_comp_of_integrable hc
  have hp : Integrable (fun q => C q * C (q + P)) :=
    scalarBubbleIntegrand_integrable ha hM hm P
  have htranslate : (∫ q, C (q + P) ^ 2) = ∫ q, C q ^ 2 :=
    integral_add_right_eq_self (fun q => C q ^ 2) P
  have hidentity : (∫ q, (C q - C (q + P)) ^ 2) =
      2 * ((∫ q, C q ^ 2) - ∫ q, C q * C (q + P)) := by
    calc
      _ = ∫ q, (C q ^ 2 + C (q + P) ^ 2) - 2 * (C q * C (q + P)) := by
        apply integral_congr_ae
        filter_upwards with q
        ring
      _ = _ := by
        rw [integral_sub (f := fun q => C q ^ 2 + C (q + P) ^ 2)
          (g := fun q => 2 * (C q * C (q + P))) (hc.add hs) (hp.const_mul 2),
          integral_add hc hs,
          integral_const_mul, htranslate]
        ring
  unfold scalarSubtractedBubble scalarBubble
  simp only [scalarBubbleIntegrand, add_zero]
  change (2 * Real.pi) ^ (-4 : ℤ) * (∫ q, C q * C q) -
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ q, C q * C (q + P)) = _
  simp_rw [← pow_two]
  rw [hidentity]
  ring

theorem scalarSubtractedBubble_nonneg {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    0 ≤ scalarSubtractedBubble a M m P := by
  rw [scalarBubble_difference_square ha hM hm P]
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem scalarBubble_le_zero_transfer {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    scalarBubble a M m P ≤ scalarBubble a M m 0 := by
  have h := scalarSubtractedBubble_nonneg ha hM hm P
  exact sub_nonneg.mp h

def scalarDepthSum (M : ℝ) (P q : ScalarMomentum) : ℝ :=
  depthProfile M (‖q‖ ^ 2) + depthProfile M (‖q + P‖ ^ 2)

theorem scalarDepthSum_nonneg {M : ℝ} (hM : 0 ≤ M) (P q : ScalarMomentum) :
    0 ≤ scalarDepthSum M P q :=
  add_nonneg (depthProfile_nonneg hM (sq_nonneg _)) (depthProfile_nonneg hM (sq_nonneg _))

theorem scalarDepthSum_continuous (M : ℝ) (P : ScalarMomentum) :
    Continuous (scalarDepthSum M P) := by
  unfold scalarDepthSum depthProfile
  fun_prop

theorem scalarBubbleIntegrand_exponential (a M m : ℝ) (P q : ScalarMomentum) :
    scalarBubbleIntegrand a M m P q = Real.exp (-(a * scalarDepthSum M P q)) /
      ((‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2)) := by
  unfold scalarBubbleIntegrand scalarCovariance kernel scalarDepthSum
  rw [div_mul_div_comm, ← Real.exp_add]
  congr 2
  ring

def scalarDepthWeighted (n : ℕ) (a M m : ℝ) (P q : ScalarMomentum) : ℝ :=
  scalarDepthSum M P q ^ n * scalarBubbleIntegrand a M m P q

def scalarBubbleMoment (n : ℕ) (a M m : ℝ) (P : ScalarMomentum) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) * ∫ q, scalarDepthWeighted n a M m P q

theorem scalarDepthWeighted_nonneg {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (a m : ℝ) (P q : ScalarMomentum) :
    0 ≤ scalarDepthWeighted n a M m P q := by
  unfold scalarDepthWeighted scalarBubbleIntegrand
  exact mul_nonneg (pow_nonneg (scalarDepthSum_nonneg hM P q) _)
    (mul_nonneg (scalarCovariance_nonneg _) (scalarCovariance_nonneg _))

theorem scalarDepthWeighted_continuous (n : ℕ) (a M : ℝ) {m : ℝ}
    (hm : 0 < m) (P : ScalarMomentum) : Continuous (scalarDepthWeighted n a M m P) := by
  unfold scalarDepthWeighted scalarBubbleIntegrand
  exact ((scalarDepthSum_continuous M P).pow n).mul
    ((scalarCovariance_continuous hm).mul
      ((scalarCovariance_continuous hm).comp (continuous_id.add continuous_const)))

theorem scalarDepthWeighted_split (n : ℕ) (a b M m : ℝ) (P q : ScalarMomentum) :
    scalarDepthWeighted n a M m P q =
      (scalarDepthSum M P q ^ n * Real.exp (-((a - b) * scalarDepthSum M P q))) *
        scalarBubbleIntegrand b M m P q := by
  have he : Real.exp (-(a * scalarDepthSum M P q)) =
      Real.exp (-((a - b) * scalarDepthSum M P q)) *
        Real.exp (-(b * scalarDepthSum M P q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [scalarDepthWeighted, scalarBubbleIntegrand_exponential, he]
  ring

theorem scalarDepthWeighted_uniform_bound {a amin M : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hM : 0 ≤ M)
    (n : ℕ) (m : ℝ) (P q : ScalarMomentum) :
    scalarDepthWeighted n a M m P q ≤
      ((n.factorial : ℝ) / (amin / 2) ^ n) * scalarBubbleIntegrand (amin / 2) M m P q := by
  rw [scalarDepthWeighted_split n a (amin / 2)]
  have hH := scalarDepthSum_nonneg hM P q
  have he : Real.exp (-((a - amin / 2) * scalarDepthSum M P q)) ≤
      Real.exp (-((amin / 2) * scalarDepthSum M P q)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (scalarCovariance_nonneg _) (scalarCovariance_nonneg _))
  calc
    _ ≤ scalarDepthSum M P q ^ n *
        Real.exp (-((amin / 2) * scalarDepthSum M P q)) := by gcongr
    _ ≤ _ := pow_mul_exp_neg_le (by linarith) hH n

theorem scalarDepthWeighted_integrable {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    Integrable (scalarDepthWeighted n a M m P) := by
  apply ((scalarBubbleIntegrand_integrable (by linarith : 0 < a / 2) hM hm P).const_mul
    ((n.factorial : ℝ) / (a / 2) ^ n)).mono'
  · exact (scalarDepthWeighted_continuous n a M hm P).aestronglyMeasurable
  · filter_upwards with q
    rw [Real.norm_of_nonneg (scalarDepthWeighted_nonneg hM n a m P q)]
    exact scalarDepthWeighted_uniform_bound ha le_rfl hM n m P q

theorem scalarDepthWeighted_hasDerivAt (n : ℕ) (a M m : ℝ) (P q : ScalarMomentum) :
    HasDerivAt (fun b => scalarDepthWeighted n b M m P q)
      (-scalarDepthWeighted (n + 1) a M m P q) a := by
  let H := scalarDepthSum M P q
  let D := (‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2)
  have he := (((hasDerivAt_id a).mul_const H).neg.exp.const_mul (H ^ n)).div_const D
  convert he using 1
  · funext b
    simp only [scalarDepthWeighted, scalarBubbleIntegrand_exponential]
    dsimp [H, D]
    ring
  · simp only [scalarDepthWeighted, scalarBubbleIntegrand_exponential, pow_succ]
    dsimp [H, D]
    ring

theorem scalarBubbleMoment_hasDerivAt {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    HasDerivAt (fun b => scalarBubbleMoment n b M m P)
      (-scalarBubbleMoment (n + 1) a M m P) a := by
  have hbound : Integrable (fun q =>
      (((n + 1).factorial : ℝ) / ((a / 2) / 2) ^ (n + 1)) *
        scalarBubbleIntegrand ((a / 2) / 2) M m P q) :=
    (scalarBubbleIntegrand_integrable (by linarith : 0 < (a / 2) / 2) hM hm P).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b q => scalarDepthWeighted n b M m P q)
    (F' := fun b q => -scalarDepthWeighted (n + 1) b M m P q)
    (x₀ := a) (ε := a / 2) (μ := volume)
    (bound := fun q => (((n + 1).factorial : ℝ) / ((a / 2) / 2) ^ (n + 1)) *
      scalarBubbleIntegrand ((a / 2) / 2) M m P q)
    (by linarith)
    (Filter.Eventually.of_forall (fun b =>
      (scalarDepthWeighted_continuous n b M hm P).aestronglyMeasurable))
    (scalarDepthWeighted_integrable ha hM hm n P)
    ((scalarDepthWeighted_continuous (n + 1) a M hm P).neg.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun q b hb => by
      rw [norm_neg, Real.norm_of_nonneg (scalarDepthWeighted_nonneg hM _ _ _ _ _)]
      apply scalarDepthWeighted_uniform_bound (by linarith : 0 < a / 2) _ hM
      have hd : |b - a| < a / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
      have hh := (abs_lt.mp hd).1
      linarith)) hbound
    (Filter.Eventually.of_forall (fun q b _ => scalarDepthWeighted_hasDerivAt n b M m P q))
  convert hd.2.const_mul ((2 * Real.pi) ^ (-4 : ℤ)) using 1
  simp only [scalarBubbleMoment, integral_neg]
  ring

theorem scalarBubble_iteratedDeriv {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    iteratedDeriv n (fun b => scalarBubble b M m P) a =
      (-1 : ℝ) ^ n * scalarBubbleMoment n a M m P := by
  induction n generalizing a with
  | zero => simp [scalarBubbleMoment, scalarDepthWeighted, scalarBubble]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun b => scalarBubble b M m P) =ᶠ[𝓝 a]
        (fun b => (-1 : ℝ) ^ n * scalarBubbleMoment n b M m P) := by
      filter_upwards [eventually_gt_nhds ha] with b hb
      exact ih hb
    rw [heq.deriv_eq]
    rw [((scalarBubbleMoment_hasDerivAt ha hM hm n P).const_mul ((-1 : ℝ) ^ n)).deriv]
    ring

theorem scalarBubbleMoment_pos {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    0 < scalarBubbleMoment n a M m P := by
  obtain ⟨q, hq⟩ := exists_ne (0 : ScalarMomentum)
  have hdepth : 0 < depthProfile M (‖q‖ ^ 2) := by
    unfold depthProfile
    apply sub_pos.mpr
    apply (Real.lt_sqrt hM).mpr
    have hnorm := sq_pos_of_pos (norm_pos_iff.mpr hq)
    linarith
  have hH : 0 < scalarDepthSum M P q :=
    add_pos_of_pos_of_nonneg hdepth (depthProfile_nonneg hM (sq_nonneg _))
  have hw : 0 < scalarDepthWeighted n a M m P q := by
    unfold scalarDepthWeighted scalarBubbleIntegrand scalarCovariance
    exact mul_pos (pow_pos hH _) (mul_pos
      (div_pos (kernel_pos _ _ _) (by positivity))
      (div_pos (kernel_pos _ _ _) (by positivity)))
  unfold scalarBubbleMoment
  apply mul_pos (by positivity)
  exact integral_pos_of_integrable_nonneg_nonzero
    (scalarDepthWeighted_continuous n a M hm P)
    (scalarDepthWeighted_integrable ha hM hm n P)
    (fun q => scalarDepthWeighted_nonneg hM n a m P q) hw.ne'

/-- Strict complete monotonicity of the literal four-dimensional comparison bubble. -/
theorem scalarBubble_strict_complete_monotonicity {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (fun b => scalarBubble b M m P) a := by
  rw [scalarBubble_iteratedDeriv ha hM hm n P]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hs, one_mul]
  exact scalarBubbleMoment_pos ha hM hm n P

/-- An explicit uniform derivative budget, using a factorial bound for the exponential. -/
theorem scalarBubbleMoment_uniform_bound {a amin M m : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hM : 0 ≤ M) (hm : 0 < m)
    (n : ℕ) (P : ScalarMomentum) :
    scalarBubbleMoment n a M m P ≤
      ((n.factorial : ℝ) / (amin / 2) ^ n) * scalarBubble (amin / 2) M m P := by
  have hi : (∫ q, scalarDepthWeighted n a M m P q) ≤
      ((n.factorial : ℝ) / (amin / 2) ^ n) *
        ∫ q, scalarBubbleIntegrand (amin / 2) M m P q := by
    rw [← integral_const_mul]
    apply integral_mono (scalarDepthWeighted_integrable (hmin.trans_le ha) hM hm n P)
      ((scalarBubbleIntegrand_integrable (by linarith : 0 < amin / 2) hM hm P).const_mul _)
    intro q
    exact scalarDepthWeighted_uniform_bound hmin ha hM n m P q
  unfold scalarBubbleMoment scalarBubble
  calc
    _ ≤ (2 * Real.pi) ^ (-4 : ℤ) *
        (((n.factorial : ℝ) / (amin / 2) ^ n) *
          ∫ q, scalarBubbleIntegrand (amin / 2) M m P q) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

end UV
