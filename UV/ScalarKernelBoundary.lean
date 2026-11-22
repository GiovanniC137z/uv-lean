import UV.MassiveRunningPole
import UV.ExtendRunningAngularBoundary

/-! A single-line boundary theorem for an actual same-height numerator.
The hypotheses control the subtracted numerator on bounded shell intervals.
The running sign is always inside the four-momentum integral. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

theorem pole_boundary_heights_neBot : poleBoundaryHeights.NeBot := by
  apply Filter.comap_neBot
  intro U hU
  obtain ⟨x, hx, hx'⟩ := Filter.nonempty_of_mem (inter_mem hU
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))
  exact ⟨⟨x, hx'⟩, hx⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- Local estimates on the kernel in the extracted character. The
subtraction always uses the value at the shell at the very same height. -/
structure Plane.ShellKernelBounds (diamond : Plane E) (ε : Evolution) (s : ℝ)
    (K : Height → ℝ → ℂ) (F : ℝ → ℂ) : Prop where
  continuous_heights : ∀ h, Continuous (K h)
  measurable_boundary : Measurable F
  boundary : ∀ w, Tendsto (fun h => K h w) poleBoundaryHeights (𝓝 (F w))
  local_bound : ∀ R : ℝ, ∃ C ≥ (0 : ℝ), ∀ᶠ h in poleBoundaryHeights, ∀ w, |w| ≤ R →
    ‖(K h w - K h s) * diamond.poleCoefficient ε h (w - s)‖ ≤ C

def Plane.runningKernelPair (diamond : Plane E) (ε : Evolution) (h : Height) (m : ℝ)
    (K : Height → ℝ → ℂ) (f : MassiveMomentum → ℂ) : ℂ :=
  ∫ q : MassiveMomentum, runningAxialTest f q *
    (K h (shellSquare q.1 q.2) * diamond.poleCoefficient ε h (massiveD m q))

def runningKernelRemainder (m : ℝ) (F : ℝ → ℂ) (f : MassiveMomentum → ℂ) (q : MassiveMomentum) : ℂ :=
  runningAxialTest f q * ((F (shellSquare q.1 q.2) - F (m ^ 2)) * (massiveD m q : ℂ)⁻¹)

private theorem integrable_running_continuous_product {f A : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (hA : Continuous A) :
    Integrable (fun q => runningAxialTest f q * A q) := by
  simpa only [runningAxialTest, mul_assoc] using integrable_runningAxialSign_mul measurable_fst
    ((hf.mul hA).integrable_of_hasCompactSupport (μ := volume) hs.mul_right)

theorem Plane.running_kernel_pair_integrable (diamond : Plane E) (ε : Evolution)
    (h : Height) (m : ℝ) {K : Height → ℝ → ℂ} (hK : Continuous (K h))
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q : MassiveMomentum => runningAxialTest f q *
      (K h (shellSquare q.1 q.2) * diamond.poleCoefficient ε h (massiveD m q))) :=
  integrable_running_continuous_product hf hs ((hK.comp shellSquare_continuous).mul
    ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)))

/-- The boundary remainder is an ordinary absolutely integrable function,
including when the support meets the shell or the axial sign edge. -/
theorem Plane.shell_kernel_remainder_limit (diamond : Plane E) (ε : Evolution) (m : ℝ)
    {K : Height → ℝ → ℂ} {F : ℝ → ℂ} (H : diamond.ShellKernelBounds ε (m ^ 2) K F)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (runningKernelRemainder m F f) ∧
    Tendsto (fun h : Height => ∫ q : MassiveMomentum, runningAxialTest f q *
      ((K h (shellSquare q.1 q.2) - K h (m ^ 2)) * diamond.poleCoefficient ε h (massiveD m q)))
      poleBoundaryHeights (𝓝 (∫ q, runningKernelRemainder m F f q)) := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn shellSquare_continuous.continuousOn
  obtain ⟨C, hC, hB⟩ := H.local_bound R
  let A (h : Height) (q : MassiveMomentum) := runningAxialTest f q *
    ((K h (shellSquare q.1 q.2) - K h (m ^ 2)) * diamond.poleCoefficient ε h (massiveD m q))
  have hM : Integrable (fun q => C * ‖f q‖) :=
    (hf.integrable_of_hasCompactSupport hs).norm.const_mul C
  have hb : ∀ᶠ h in poleBoundaryHeights, ∀ q, ‖A h q‖ ≤ C * ‖f q‖ := by
    filter_upwards [hB] with h hB q
    by_cases hq : f q = 0
    · simp [A, runningAxialTest, hq]
    · dsimp only [A]
      rw [norm_mul, mul_comm C]
      exact mul_le_mul (running_axial_test_norm_le f q)
        (hB _ (hR q (subset_tsupport f hq))) (norm_nonneg _) (norm_nonneg _)
  have hp (q : MassiveMomentum) (hn : massiveD m q ≠ 0) :
      Tendsto (fun h => A h q) poleBoundaryHeights (𝓝 (runningKernelRemainder m F f q)) :=
    (((H.boundary _).sub (H.boundary (m ^ 2))).mul
      (diamond.pole_coefficient_off_shell_limit ε hn)).const_mul _
  have hAi (h : Height) : Integrable (A h) :=
    integrable_running_continuous_product hf hs
      ((((H.continuous_heights h).comp shellSquare_continuous).sub continuous_const).mul
        ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)))
  constructor
  · apply hM.mono'
    · exact ((running_axial_test_measurable hf.measurable).mul
        (((H.measurable_boundary.comp shellSquare_continuous.measurable).sub measurable_const).mul
          (Complex.continuous_ofReal.measurable.comp (massiveD_continuous m).measurable).inv)).aestronglyMeasurable
    · filter_upwards [massiveD_nonzero_ae m] with q hn
      exact le_of_tendsto (hp q hn).norm (hb.mono fun h hB => hB q)
  · exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall
      fun h => (hAi h).aestronglyMeasurable) (hb.mono fun h hB => Eventually.of_forall hB)
      hM ((massiveD_nonzero_ae m).mono fun q hn => hp q hn)

/-- Transfer of a bare running-pole pairing through a same-height
kernel. The massive and massless bare limits use different shell charts. -/
theorem Plane.running_kernel_limit (diamond : Plane E) (ε : Evolution) (m : ℝ)
    {K : Height → ℝ → ℂ} {F : ℝ → ℂ} (H : diamond.ShellKernelBounds ε (m ^ 2) K F)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {P : ℂ} (hP : Tendsto (fun h : Height => ∫ q : MassiveMomentum,
      runningAxialTest f q * diamond.poleCoefficient ε h (massiveD m q)) poleBoundaryHeights (𝓝 P)) :
    Tendsto (fun h => diamond.runningKernelPair ε h m K f) poleBoundaryHeights
      (𝓝 (F (m ^ 2) * P + ∫ q, runningKernelRemainder m F f q)) := by
  refine (((H.boundary (m ^ 2)).mul hP).add
    (diamond.shell_kernel_remainder_limit ε m H hf hs).2).congr fun h => ?_
  let P (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hPc : Continuous P := (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have h₁ := (integrable_running_continuous_product hf hs hPc).const_mul (K h (m ^ 2))
  have h₂ : Integrable (fun q : MassiveMomentum => runningAxialTest f q *
      ((K h (shellSquare q.1 q.2) - K h (m ^ 2)) * P q)) := integrable_running_continuous_product hf hs
    ((((H.continuous_heights h).comp shellSquare_continuous).sub
      (continuous_const (y := K h (m ^ 2)))).mul hPc)
  rw [← integral_const_mul, ← integral_add h₁ h₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by dsimp only; ring

theorem Plane.massive_running_kernel_limit (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {K : Height → ℝ → ℂ} {F : ℝ → ℂ}
    (H : diamond.ShellKernelBounds ε (m ^ 2) K F) {f : MassiveMomentum → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.runningKernelPair ε h m K f) poleBoundaryHeights
      (𝓝 (F (m ^ 2) * massiveComplexSignedPoleBoundary (diamond.eta ε) m f +
        ∫ q, runningKernelRemainder m F f q)) :=
  diamond.running_kernel_limit ε m H hf.continuous hs (diamond.massive_signed_pole_complex_limit ε hm hf hs)

theorem Plane.massless_running_kernel_limit (diamond : Plane E) (ε : Evolution)
    {K : Height → ℝ → ℂ} {F : ℝ → ℂ} (H : diamond.ShellKernelBounds ε 0 K F)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ R > (0 : ℝ), Tendsto (fun h => diamond.runningKernelPair ε h 0 K f) poleBoundaryHeights
      (𝓝 (F 0 * ((2 * Real.pi ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
        coneAngularSingleBoundary (diamond.eta ε) (coneRunningAngularAmplitude f r)) +
        ∫ q, runningKernelRemainder 0 F f q)) := by
  obtain ⟨R, hR, hp⟩ := diamond.cone_running_smooth_single_limit ε hf hs
  refine ⟨R, hR, ?_⟩
  have H' : diamond.ShellKernelBounds ε ((0 : ℝ) ^ 2) K F := by simpa using H
  have hB := diamond.running_kernel_limit ε 0 H' hf.continuous hs (P := _) (by
    simpa only [massiveD, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, Complex.real_smul,
      runningAxialTest, mul_assoc] using hp)
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hB

end UV.SectorPlane
