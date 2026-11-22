import UV.VerifyRunningLongitudinal
import UV.VerifyMassiveRunningJump

/-! The massless stable-half scalar, ghost, and Maxwell templates on
one sector plane. The real axial sign enters the numerator alone. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def Plane.runningStableGhostPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (g : ℝ × Spatial → ℂ) : ℂ :=
  (Complex.I * (diamond.eta ε : ℂ)) * diamond.masslessRunningStableSinglePair ε h a g

def Plane.runningStableGaugePair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a ζ : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) : ℂ :=
  -(Complex.I * (diamond.eta ε : ℂ)) *
    ((coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ) *
      diamond.masslessRunningStableSinglePair ε h a g -
      (1 - (ζ : ℂ)) * diamond.masslessRunningStableLongitudinalPair ε h a u v g)

/-- The ghost's scalar factor is literally the oriented scalar line with
the stable-half kernel at zero mass and the same positive height. -/
theorem Plane.massless_running_stable_scalar_line (diamond : Plane E) (ε : Evolution)
    (h : Height) {a : ℝ} (ha : 0 ≤ a) (q : ℝ × Spatial) (hq : q.1 ≠ 0) :
    directed (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ) *
      (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
        diamond.poleCoefficient ε h (shellSquare q.1 q.2))) =
      diamond.scalarLine ε h (fun z => Complex.exp (-principalSqrt z)) a 0 q.1 q.2 hq := by
  have H := diamond.massive_stable_running_integrand_scalarLine ε h ha 0 q hq
  simpa only [Plane.massiveStableRunningIntegrand, Plane.massiveStableFactor, h.property,
    dite_true, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using H

theorem Plane.massless_running_stable_scalar_line_ae (diamond : Plane E) (ε : Evolution)
    (h : Height) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ q : ℝ × Spatial ∂volume,
      directed (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ) *
        (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
          diamond.poleCoefficient ε h (shellSquare q.1 q.2))) =
        if hq : q.1 ≠ 0 then
          diamond.scalarLine ε h (fun z => Complex.exp (-principalSqrt z)) a 0 q.1 q.2 hq
        else 0 := by
  filter_upwards [real_axial_nonzero_ae] with q hq
  rw [dif_pos hq, diamond.massless_running_stable_scalar_line ε h ha q hq]

theorem Plane.massless_running_stable_ghost_pair_integral (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (g : ℝ × Spatial → ℂ) :
    diamond.runningStableGhostPair ε h a g = ∫ q : ℝ × Spatial,
      let w := shellSquare q.1 q.2
      g q * (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ) *
        (diamond.stableHalfCoefficient ε a w h * diamond.poleCoefficient ε h w)) := by
  rw [Plane.runningStableGhostPair, Plane.masslessRunningStableSinglePair, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  simp only [runningAxialTest, Complex.ofReal_mul]
  ring

private theorem directed_sub_complex (z w : ℂ) : directed (z - w) = directed z - directed w := by
  apply quotientCharacterEquiv.injective
  simp [directed]

/-- Componentwise resolved Maxwell template in the actual directed
carrier, contracted against the given unit axes on the same plane. -/
theorem Plane.massless_running_stable_gauge_integrand (diamond : Plane E) (ε : Evolution)
    (h : Height) {a : ℝ} (ha : 0 ≤ a) (ζ : ℝ)
    (u v : ConeUnitDirection) (q : ℝ × Spatial) :
    let w := shellSquare q.1 q.2
    let N := Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)
    let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
    let B := (1 - (ζ : ℂ)) * (coneCovector (WithLp.ofLp u.val) q : ℂ) *
      (coneCovector (WithLp.ofLp v.val) q : ℂ)
    let K := diamond.stableHalfCoefficient ε a w h
    let P := diamond.poleCoefficient ε h w
    directed (-N * (G * (K * P) - B * (K * P ^ 2))) =
      -directed N * directed (Complex.exp (-principalSqrt
        (-(a : ℂ) ^ 2 * diamond.shiftedShellCoefficient ε h w))) *
        (directed G * diamond.poleInverse ε h w -
          directed B * (diamond.poleInverse ε h w) ^ 2) := by
  dsimp only
  rw [← diamond.stable_half_numerator_scalar_argument ε h ha,
    directed_mul, directed_neg, directed_sub_complex]
  have hP (w : ℝ) : directed (diamond.poleCoefficient ε h w) =
      diamond.poleInverse ε h w := by
    simp [diamond.pole_coefficient_eq_inv, diamond.pole_inverse_complex,
      Plane.shiftedShellCoefficient]
  have hK (w : ℝ) : directed (diamond.stableHalfCoefficient ε a w h) =
      diamond.stableHalfNumerator ε h a w := by
    simp [Plane.stableHalfCoefficient, h.property, Plane.stableHalfNumerator, directed]
  simp only [directed_mul, pow_two, hP, hK]
  ring

private theorem Plane.running_stable_pair_integrable (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (n : ℕ) {f : ℝ × Spatial → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q : ℝ × Spatial => runningAxialTest f q *
      (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
        (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ n)) := by
  have hK := (diamond.stable_half_coefficient_continuous ε a h).comp shellSquare_continuous
  have hP := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
  have H := (hf.mul (hK.mul (hP.pow n))).integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  simpa only [runningAxialTest, mul_assoc] using integrable_runningAxialSign_mul measurable_fst H

theorem Plane.massless_running_stable_gauge_pair_integral (diamond : Plane E) (ε : Evolution)
    (h : Height) (a ζ : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : Continuous g) (hs : HasCompactSupport g) :
    diamond.runningStableGaugePair ε h a ζ u v g = ∫ q : ℝ × Spatial,
      let w := shellSquare q.1 q.2
      let N := Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)
      let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
      let B := (1 - (ζ : ℂ)) * (coneCovector (WithLp.ofLp u.val) q : ℂ) *
        (coneCovector (WithLp.ofLp v.val) q : ℂ)
      let K := diamond.stableHalfCoefficient ε a w h
      let P := diamond.poleCoefficient ε h w
      g q * (-N * (G * (K * P) - B * (K * P ^ 2))) := by
  let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
  let Z := 1 - (ζ : ℂ)
  have hS := diamond.running_stable_pair_integrable ε h a 1 hg hs
  have hT := diamond.running_stable_pair_integrable ε h a 2 (cone_tensor_test_continuous u v hg)
    (cone_tensor_test_compact u v hs)
  simp only [pow_one] at hS
  unfold Plane.runningStableGaugePair Plane.masslessRunningStableSinglePair
    Plane.masslessRunningStableLongitudinalPair
  simp only [← integral_const_mul]
  rw [← integral_sub (hS.const_mul G) (hT.const_mul Z), ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  simp only [runningAxialTest, coneTensorTest, coneLinearTest, Complex.ofReal_mul]
  ring

theorem Plane.massless_running_stable_ghost_limit (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ L : ℂ,
      Tendsto (fun h : Height => diamond.runningStableGhostPair ε h a g)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 L) ∧
      Tendsto (fun h : Height => directed (diamond.runningStableGhostPair ε h a g))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (directed L)) := by
  obtain ⟨_, _, hP⟩ := diamond.massless_running_stable_single_limit ε ha hg hs
  have H := hP.const_mul (Complex.I * (diamond.eta ε : ℂ))
  exact ⟨_, H, directed_shell_readout_continuous.continuousAt.tendsto.comp H⟩

theorem Plane.massless_running_stable_gauge_limit (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) (ζ : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ L : ℂ,
      Tendsto (fun h : Height => diamond.runningStableGaugePair ε h a ζ u v g)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 L) ∧
      Tendsto (fun h : Height => directed (diamond.runningStableGaugePair ε h a ζ u v g))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (directed L)) := by
  obtain ⟨_, _, hP⟩ := diamond.massless_running_stable_single_limit ε ha hg hs
  obtain ⟨_, hL, _⟩ := diamond.massless_running_stable_longitudinal_limit ε ha u v hg hs
  have H := ((hP.const_mul (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)).sub
    (hL.const_mul (1 - (ζ : ℂ)))).const_mul (-(Complex.I * (diamond.eta ε : ℂ)))
  exact ⟨_, H, directed_shell_readout_continuous.continuousAt.tendsto.comp H⟩

end UV.SectorPlane
