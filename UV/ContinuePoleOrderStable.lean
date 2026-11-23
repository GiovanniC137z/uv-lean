import UV.ContinuePoleOrderMoving
import UV.SectorPlaneStableSquareChart

/-! Stable-half numerators of arbitrary same-side massive pole powers.
The smooth comparison is confined to a timelike shell collar. The
original branch and any running-sign power remain in the complementary
off-shell integral. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set Metric UV.Carrier
open scoped Topology ContDiff

set_option maxHeartbeats 1200000

variable {E : Type*} [NormedAddCommGroup E]

def poleOrderShellBump {m : ℝ} (hm : 0 < m) : ContDiffBump (m^2) :=
  ⟨m^2/4, m^2/2, by positivity, by nlinarith [sq_pos_of_pos hm]⟩

def Plane.stablePoleOrderWeight (diamond : Plane E) (ε : Evolution) (a : ℝ)
    (c : ℕ) (h : Height) (q : MassiveMomentum) : ℂ :=
  (axialSign q.1 : ℂ)^c * diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h

def stablePoleOrderBoundaryWeight (η a : ℝ) (c : ℕ) (q : MassiveMomentum) : ℂ :=
  (axialSign q.1 : ℂ)^c * stableSideValue η a (shellSquare q.1 q.2)

def Plane.stablePoleOrderCollar (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    (a : ℝ) (c : ℕ) (t : ℝ) (q : MassiveMomentum) : ℂ :=
  (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ) *
    (if 0 < q.1 then 1 else (-1 : ℂ)^c) *
      Complex.exp ((Complex.I * ((diamond.eta ε * a : ℝ) : ℂ)) *
        principalSqrt ((shellSquare q.1 q.2 : ℂ) + Complex.I * ((diamond.eta ε*t : ℝ) : ℂ)))

theorem Plane.stable_pole_order_collar_smooth (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    (a : ℝ) (c : ℕ) : ContDiff ℝ ∞ (Function.uncurry (diamond.stablePoleOrderCollar ε hm a c)) := by
  let w (x : ℝ × MassiveMomentum) := shellSquare x.2.1 x.2.2
  let Z (x : ℝ × MassiveMomentum) :=
    (w x : ℂ) + Complex.I * ((diamond.eta ε * x.1 : ℝ) : ℂ)
  have hw : ContDiff ℝ ∞ w :=
    ((contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)).comp contDiff_snd
  have hz : ContDiff ℝ ∞ Z :=
    (Complex.ofRealCLM.contDiff.comp hw).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  have hβ : ContDiff ℝ ∞ (fun x => (poleOrderShellBump hm (w x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((poleOrderShellBump hm).contDiff.comp hw)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < w x
  · have hxre : 0 < (Z x).re := by simpa [Z] using hx
    have hr : ContDiffAt ℝ ∞ (fun y => principalSqrt (Z y)) x :=
      ((principalSqrt_analyticOnNhd_rightHalfPlane (Z x) hxre).contDiffAt.restrict_scalars ℝ).comp x hz.contDiffAt
    have he : ContDiffAt ℝ ∞ (fun y => Complex.exp
        ((Complex.I * ((diamond.eta ε * a : ℝ) : ℂ)) * principalSqrt (Z y))) x :=
      (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).contDiffAt.comp x (contDiffAt_const.mul hr)
    have ht : x.2.1 ≠ 0 := by
      intro h
      simp [w, shellSquare, h, not_lt_of_ge (sq_nonneg ‖x.2.2‖)] at hx
    have H (b : ℂ) : ContDiffAt ℝ ∞ (fun y => (poleOrderShellBump hm (w y) : ℂ) * b *
        Complex.exp ((Complex.I * ((diamond.eta ε * a : ℝ) : ℂ)) * principalSqrt (Z y))) x :=
      (hβ.contDiffAt.mul contDiffAt_const).mul he
    rcases lt_or_gt_of_ne ht with hn | hp
    · apply (H ((-1 : ℂ)^c)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).mem_nhds hn] with y hy
      have hy' : y.2.1 < 0 := hy
      simp only [Function.uncurry, Plane.stablePoleOrderCollar, if_neg hy'.not_gt, w, Z]
    · apply (H 1).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hp] with y hy
      have hy' : 0 < y.2.1 := hy
      simp only [Function.uncurry, Plane.stablePoleOrderCollar, if_pos hy', w, Z]
  · have hlt : w x < m^2/2 := lt_of_le_of_lt (le_of_not_gt hx) (by positivity)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hw.continuous continuous_const).mem_nhds hlt] with y hy
    have hy' : w y < m^2/2 := hy
    have hβ0 : poleOrderShellBump hm (w y) = 0 := by
      apply (poleOrderShellBump hm).zero_of_le_dist
      rw [Real.dist_eq, abs_of_neg (by linarith [sq_pos_of_pos hm] : w y - m^2 < 0)]
      change m^2/2 ≤ _
      linarith
    simp only [Function.uncurry, Plane.stablePoleOrderCollar, ← show w y = shellSquare y.2.1 y.2.2 from rfl,
      hβ0, Complex.ofReal_zero, zero_mul]

theorem Plane.stable_pole_order_collar_eq (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    (a : ℝ) (c : ℕ) (h : Height) (q : MassiveMomentum) :
    diamond.stablePoleOrderCollar ε hm a c h q =
      (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ) * diamond.stablePoleOrderWeight ε a c h q := by
  unfold Plane.stablePoleOrderCollar Plane.stablePoleOrderWeight
  rw [diamond.stable_half_analytic_form, Plane.shiftedShellCoefficient]
  by_cases ht : q.1 = 0
  · have hβ0 : poleOrderShellBump hm (shellSquare q.1 q.2) = 0 := by
      apply (poleOrderShellBump hm).zero_of_le_dist
      rw [Real.dist_eq, shellSquare, ht, zero_pow (by decide : (2:ℕ) ≠ 0), zero_sub,
        abs_of_nonpos (by nlinarith [sq_nonneg ‖q.2‖, sq_nonneg m])]
      change m^2/2 ≤ _
      nlinarith [sq_nonneg ‖q.2‖, sq_nonneg m]
    simp only [hβ0, Complex.ofReal_zero, zero_mul]
  · rcases lt_or_gt_of_ne ht with hn | hp
    · simp only [axialSign, if_neg hn.not_gt, if_pos hn, Complex.ofReal_neg, Complex.ofReal_one, mul_assoc]
    · simp only [axialSign, if_pos hp, Complex.ofReal_one, one_pow, one_mul, mul_one]

private theorem Plane.stable_pole_order_weight_bound (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) (c : ℕ) (h : Height) (q : MassiveMomentum) :
    ‖diamond.stablePoleOrderWeight ε a c h q‖ ≤ 1 := by
  rw [Plane.stablePoleOrderWeight, norm_mul, norm_pow, Complex.norm_real]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (massive_running_axial_sign_norm_le_one _))
    (norm_nonneg _) (diamond.stable_half_coefficient_norm_le_one ε ha h.property)

private theorem Plane.stable_pole_order_weight_limit (diamond : Plane E) (ε : Evolution)
    (a : ℝ) (c : ℕ) (q : MassiveMomentum) :
    Tendsto (fun h : Height => diamond.stablePoleOrderWeight ε a c h q)
      poleBoundaryHeights (𝓝 (stablePoleOrderBoundaryWeight (diamond.eta ε) a c q)) := by
  have h := Complex.continuous_exp.continuousAt.tendsto.comp
    ((diamond.stable_shell_root_tendsto ε (shellSquare q.1 q.2)).const_mul (-(a : ℂ)))
  apply (h.const_mul ((axialSign q.1 : ℂ)^c)).congr
  intro h
  simp only [Plane.stablePoleOrderWeight, Plane.stableHalfCoefficient, dif_pos h.property,
    diamond.stable_half_numerator_characters, Function.comp_apply, Plane.stableShellRoot]


def Plane.stablePoleOrderExterior (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    (a : ℝ) (n c : ℕ) (f : MassiveMomentum → ℂ) (h : Height) (q : MassiveMomentum) : ℂ :=
  let B := (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ)
  f q * ((1 - B) * diamond.stablePoleOrderWeight ε a c h q *
    (diamond.poleCoefficient ε h (massiveD m q))^(n+1))

private theorem Plane.stable_pole_order_exterior_bound (diamond : Plane E) (ε : Evolution)
    {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (n c : ℕ) (f : MassiveMomentum → ℂ)
    (h : Height) (q : MassiveMomentum) : ‖diamond.stablePoleOrderExterior ε hm a n c f h q‖ ≤
      ‖f q‖ * ((m^2/4)⁻¹)^(n+1) := by
  let δ : ℝ := m^2/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_cases hq : |shellSquare q.1 q.2 - m^2| ≤ δ
  · have H : poleOrderShellBump hm (shellSquare q.1 q.2) = 1 :=
      (poleOrderShellBump hm).one_of_mem_closedBall
        (by simpa only [mem_closedBall, Real.dist_eq] using hq)
    simp only [Plane.stablePoleOrderExterior, H, Complex.ofReal_one, sub_self, zero_mul, mul_zero, norm_zero]
    positivity
  · have he : δ ≤ |massiveD m q| := (lt_of_not_ge hq).le
    have hn : massiveD m q ≠ 0 := by
      intro hh
      rw [hh,abs_zero] at he
      exact hδ.not_ge he
    have hp : ‖diamond.poleCoefficient ε h (massiveD m q)‖ ≤ δ⁻¹ :=
      (diamond.pole_coefficient_off_shell_bound ε h hn).trans (inv_anti₀ hδ he)
    have hBq : ‖1 - (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (poleOrderShellBump hm).le_one)]
      linarith [(poleOrderShellBump hm).nonneg (x := shellSquare q.1 q.2)]
    rw [Plane.stablePoleOrderExterior, norm_mul, norm_mul, norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (mul_le_mul (mul_le_one₀ hBq (norm_nonneg _) (diamond.stable_pole_order_weight_bound ε ha c h q))
      (pow_le_pow_left₀ (norm_nonneg _) hp _) (by positivity) zero_le_one).trans_eq (one_mul _)

private theorem Plane.stable_pole_order_exterior_integrable (diamond : Plane E) (ε : Evolution)
    {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (n c : ℕ)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (h : Height) : Integrable (diamond.stablePoleOrderExterior ε hm a n c f h) := by
  have hB : Continuous (fun q : MassiveMomentum =>
      (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ)) :=
    Complex.continuous_ofReal.comp ((poleOrderShellBump hm).continuous.comp shellSquare_continuous)
  have hP : Continuous (fun q : MassiveMomentum => diamond.poleCoefficient ε h (massiveD m q)) :=
    (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hW : Measurable (diamond.stablePoleOrderWeight ε a c h) :=
    ((Complex.continuous_ofReal.measurable.comp (massive_axial_sign_measurable.comp measurable_fst)).pow_const c).mul
      (((diamond.stable_half_coefficient_continuous ε a h).comp shellSquare_continuous).measurable)
  refine ((hf.integrable_of_hasCompactSupport hs).norm.mul_const (((m^2/4)⁻¹)^(n+1))).mono' ?_
    (Eventually.of_forall (diamond.stable_pole_order_exterior_bound ε hm ha n c f h))
  exact (hf.measurable.mul (((measurable_const.sub hB.measurable).mul hW).mul
    (hP.measurable.pow_const _))).aestronglyMeasurable

def Plane.stablePoleOrderExteriorLimit (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (a : ℝ) (n c : ℕ) (f : MassiveMomentum → ℂ) : ℂ :=
  ∫ q, f q * ((1 - (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ)) *
    stablePoleOrderBoundaryWeight (diamond.eta ε) a c q * ((massiveD m q : ℂ)⁻¹)^(n+1))

private theorem Plane.stable_pole_order_exterior_limit (diamond : Plane E) (ε : Evolution)
    {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (n c : ℕ)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, diamond.stablePoleOrderExterior ε hm a n c f h q)
      poleBoundaryHeights (𝓝 (diamond.stablePoleOrderExteriorLimit ε hm a n c f)) := by
  unfold Plane.stablePoleOrderExteriorLimit
  apply tendsto_integral_filter_of_dominated_convergence (fun (q : MassiveMomentum) => ‖f q‖ * ((m^2/4)⁻¹)^(n+1))
    (Eventually.of_forall (fun h => (diamond.stable_pole_order_exterior_integrable ε hm ha n c hf hs h).aestronglyMeasurable))
    (Eventually.of_forall (fun h => Eventually.of_forall (diamond.stable_pole_order_exterior_bound ε hm ha n c f h)))
    ((hf.integrable_of_hasCompactSupport hs).norm.mul_const _)
  exact (massiveD_nonzero_ae m).mono fun q hq =>
    ((((diamond.stable_pole_order_weight_limit ε a c q).const_mul (1 - (poleOrderShellBump hm (shellSquare q.1 q.2) : ℂ))).mul
      ((diamond.pole_coefficient_off_shell_limit ε hq).pow (n+1))).const_mul (f q))

/-- The exact boundary consists of a smooth-shell Euler term and the
ordinary integral of the complementary original branch. -/
def Plane.stablePoleOrderLimit (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    (a : ℝ) (n c : ℕ) (f : MassiveMomentum → ℂ) : ℂ :=
  let U := diamond.stablePoleOrderCollar ε hm a c
  bareComplexShellBoundary (diamond.eta ε) m (poleOrderEulerTest n (fun q => f q * U 0 q)) /
    ((m ^ 2 : ℝ) : ℂ) ^ n + diamond.stablePoleOrderExteriorLimit ε hm a n c f

/-- The stable-half multiplier and any finite running-sign power have
a common-height boundary at positive mass. Only the ordinary,
nonsingular complement uses the original nonsmooth axial readout. -/
theorem Plane.massive_stable_pole_order_boundary (diamond : Plane E) (ε : Evolution)
    {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (n c : ℕ)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ ((n : WithTop ℕ∞)+2) f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * (diamond.stablePoleOrderWeight ε a c h q *
      (diamond.poleCoefficient ε h (massiveD m q))^(n+1))) poleBoundaryHeights
      (𝓝 (diamond.stablePoleOrderLimit ε hm a n c f)) := by
  let U := diamond.stablePoleOrderCollar ε hm a c
  let F (t : ℝ) (q : MassiveMomentum) := f q * U t q
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  let W := diamond.stablePoleOrderWeight ε a c
  have hU : ContDiff ℝ ∞ (Function.uncurry U) := diamond.stable_pole_order_collar_smooth ε hm a c
  have horder : (n : WithTop ℕ∞) + 2 ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) + 2 ≤ ⊤)
  have hF : ContDiff ℝ ((n : WithTop ℕ∞)+2) (Function.uncurry F) :=
    (hf.comp contDiff_snd).mul (hU.of_le horder)
  let K : TopologicalSpace.Compacts MassiveMomentum := ⟨tsupport f, hs⟩
  have hFs (t : ℝ) (q : MassiveMomentum) (hq : q ∉ K) : F t q = 0 := by
    dsimp only [F]
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
  have hcollar := diamond.massive_same_side_pole_order_moving_boundary ε hm n K (F := F) hF hFs
  have hfc : Continuous f := hf.continuous
  have hrest : Tendsto (fun h : Height => ∫ q, diamond.stablePoleOrderExterior ε hm a n c f h q)
      poleBoundaryHeights (𝓝 (diamond.stablePoleOrderExteriorLimit ε hm a n c f)) :=
    diamond.stable_pole_order_exterior_limit ε hm ha n c hfc hs
  have hFjoint : Continuous (Function.uncurry F) := hF.continuous
  have hFcont (h : Height) : Continuous (F h) := by
    change Continuous (Function.uncurry F ∘ (fun q : MassiveMomentum => ((h : ℝ), q)))
    exact hFjoint.comp (continuous_const.prodMk continuous_id)
  have hP (h : Height) : Continuous (P h) :=
    (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hsum : Tendsto (fun h : Height =>
      (∫ q, F h q * P h q ^ (n+1)) + (∫ q, diamond.stablePoleOrderExterior ε hm a n c f h q))
      poleBoundaryHeights (𝓝 (diamond.stablePoleOrderLimit ε hm a n c f)) := hcollar.add hrest
  refine hsum.congr fun h => ?_
  have hiF : Integrable (fun q => F h q * P h q ^ (n+1)) :=
    ((hFcont h).mul ((hP h).pow _)).integrable_of_hasCompactSupport
      (hs.mul_right.mul_right)
  change (∫ q, F h q * P h q ^ (n+1)) + (∫ q, diamond.stablePoleOrderExterior ε hm a n c f h q) = _
  rw [← integral_add hiF (diamond.stable_pole_order_exterior_integrable ε hm ha n c (f := f) hfc hs h)]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only [F, P, U, W, Plane.stablePoleOrderExterior]
  rw [diamond.stable_pole_order_collar_eq]
  ring

end UV.SectorPlane
