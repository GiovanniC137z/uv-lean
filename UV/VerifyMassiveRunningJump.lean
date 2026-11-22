import UV.VerifyMassiveRunningBoundary
import UV.VerifyMassiveRunningChart
import UV.VerifyMassiveRunningScale

/-! Full-line stable-half discontinuity with the actual normalized running
unit on a fixed massive sector plane. The sign-edge correction is tested
in the original four-momentum measure, uniformly away from the pole. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]

def massiveRunningRealCorrection (a m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  ∫ q : MassiveMomentum, (stableBoundaryReal a (shellSquare q.1 q.2) / massiveD m q *
    massiveRunningCorrection m q) * f q

/-- The real boundary multiplier times the running sign and the massive
PV. The correction restores the literal sign off the shell. -/
def massiveRunningRealPV (a m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  stableMassiveRealPV (m ^ 2 / 4) a m (massiveRunningTest m f) +
    massiveRunningRealCorrection a m f

private theorem Plane.massive_stable_factor_test_integrable (diamond : Plane E) (ε : Evolution)
    (a m : ℝ) (h : Height) {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q : MassiveMomentum =>
      diamond.massiveStableFactor ε a m (shellSquare q.1 q.2) h * (f q : ℂ)) := by
  have hc := (diamond.massive_stable_factor_continuous ε a m h).comp shellSquare_continuous
  exact (hc.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
    ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left (f := _))

private theorem Plane.massive_stable_correction_test_sum_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : MassiveMomentum,
      (diamond.massiveStableFactor εPos a m (shellSquare q.1 q.2) h +
        diamond.massiveStableFactor εNeg a m (shellSquare q.1 q.2) h) *
          (massiveRunningCorrection m q : ℂ) * (f q : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (massiveRunningRealCorrection a m f : ℂ))) := by
  let B : ℝ := (m ^ 2 / 2)⁻¹
  have hmeas := Complex.continuous_ofReal.measurable.comp
    (massive_running_correction_measurable hm)
  unfold massiveRunningRealCorrection
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (fun q : MassiveMomentum => (4 * B) * ‖f q‖) ?_ ?_
    ((hf.integrable_of_hasCompactSupport hs).norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hc (ε : Evolution) := (diamond.massive_stable_factor_continuous ε a m ⟨h, hh'⟩).comp
      shellSquare_continuous
    exact ((((hc εPos).add (hc εNeg)).measurable.mul hmeas).mul
      (Complex.continuous_ofReal.comp hf).measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    refine Eventually.of_forall fun q => ?_
    by_cases hq : massiveRunningCorrection m q = 0
    · simp [hq, B]
      positivity
    · have hgap := massive_running_correction_gap hm hq
      have hb : 0 < m ^ 2 / 2 := by positivity
      have hnon : massiveD m q ≠ 0 := fun h => by rw [h, abs_zero] at hgap; linarith
      have hp := (diamond.massive_stable_factor_norm_bound εPos ha hh' hnon).trans
        (inv_anti₀ hb hgap)
      have hn := (diamond.massive_stable_factor_norm_bound εNeg ha hh' hnon).trans
        (inv_anti₀ hb hgap)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ (B + B) * 2 := mul_le_mul ((norm_add_le _ _).trans (add_le_add hp hn))
          (massive_running_correction_norm_le m q) (norm_nonneg _) (by positivity)
        _ = _ := by ring
  · filter_upwards [massless_shell_nonzero_ae, massiveD_nonzero_ae m] with q hq hd
    have h := ((diamond.massive_stable_factor_sum_pointwise εPos εNeg hPos hNeg a m hq hd).mul_const
      (massiveRunningCorrection m q : ℂ)).mul_const (f q : ℂ)
    convert h using 2
    unfold massiveD
    push_cast
    ring

/-- At finite positive height the full coefficient has the running
unit only in its numerator. The stable branch and pole keep the
same fixed-plane η and positive height. -/
def Plane.massiveStableRunningIntegrand (diamond : Plane E) (ε : Evolution)
    (a m : ℝ) (q : MassiveMomentum) (h : ℝ) : ℂ :=
  Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ) *
    diamond.massiveStableFactor ε a m (shellSquare q.1 q.2) h

theorem Plane.massive_stable_running_integrand_directed (diamond : Plane E) (ε : Evolution)
    (h : Height) (a m : ℝ) (q : MassiveMomentum) :
    directed (diamond.massiveStableRunningIntegrand ε a m q h) =
      directed (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)) *
        diamond.stableHalfNumerator ε h a (shellSquare q.1 q.2) *
          diamond.poleInverse ε h (massiveD m q) := by
  rw [Plane.massiveStableRunningIntegrand, Plane.massiveStableFactor, dif_pos h.property,
    directed_mul]
  change directed (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)) *
      directed (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
        diamond.poleCoefficient ε h (massiveD m q)) = _
  rw [diamond.massive_stable_integrand_directed, mul_assoc]

theorem Plane.massive_stable_running_integrand_scalarLine (diamond : Plane E) (ε : Evolution)
    (h : Height) {a : ℝ} (ha : 0 ≤ a) (m : ℝ) (q : MassiveMomentum) (hq : q.1 ≠ 0) :
    directed (diamond.massiveStableRunningIntegrand ε a m q h) =
      diamond.scalarLine ε h (fun z => Complex.exp (-principalSqrt z)) a m q.1 q.2 hq := by
  rw [diamond.massive_stable_running_integrand_directed,
    diamond.stable_half_numerator_scalar_argument ε h ha]
  rfl

def Plane.massiveStableRunningPairing (diamond : Plane E) (ε : Evolution) (a m : ℝ)
    (f : MassiveMomentum → ℝ) (h : ℝ) : ℂ :=
  ∫ q : MassiveMomentum, diamond.massiveStableRunningIntegrand ε a m q h * (f q : ℂ)

private theorem Plane.massive_stable_running_jump_split (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {h : ℝ} (hh : 0 < h) :
    diamond.massiveStableRunningPairing εPos a m f h -
        diamond.massiveStableRunningPairing εNeg a m f h =
      Complex.I * (diamond.massiveStablePairing εPos a m (massiveRunningTest m f) h +
        diamond.massiveStablePairing εNeg a m (massiveRunningTest m f) h +
          ∫ q : MassiveMomentum, (diamond.massiveStableFactor εPos a m (shellSquare q.1 q.2) h +
            diamond.massiveStableFactor εNeg a m (shellSquare q.1 q.2) h) *
              (massiveRunningCorrection m q : ℂ) * (f q : ℂ)) := by
  let F (ε : Evolution) (q : MassiveMomentum) :=
    diamond.massiveStableFactor ε a m (shellSquare q.1 q.2) h
  let W (q : MassiveMomentum) := (axialSign q.1 : ℂ)
  let V (q : MassiveMomentum) := (massiveRunningClip m q.1 : ℂ)
  let U (q : MassiveMomentum) := (massiveRunningCorrection m q : ℂ)
  have ht (ε : Evolution) : Integrable (fun q => F ε q * (f q : ℂ)) :=
    diamond.massive_stable_factor_test_integrable ε a m ⟨h, hh⟩ hf hs
  have hi (ε : Evolution) (H : MassiveMomentum → ℂ)
      (hmH : Measurable H) (hb : ∃ C, ∀ q, ‖H q‖ ≤ C) :
      Integrable (fun q => F ε q * H q * (f q : ℂ)) := by
    have H0 := (ht ε).bdd_mul hmH.aestronglyMeasurable hb
    convert H0 using 1
    funext q
    ring
  have hwMeas : Measurable W :=
    Complex.continuous_ofReal.measurable.comp (massive_axial_sign_measurable.comp measurable_fst)
  have hw ε := hi ε W hwMeas ⟨1, fun q => by
    simpa only [W, Complex.norm_real] using (massive_running_axial_sign_norm_le_one q.1)⟩
  have hv ε := hi ε V (Complex.continuous_ofReal.measurable.comp
    (((massive_running_clip_lipschitz hm).continuous.comp continuous_fst).measurable))
    ⟨1, fun q => by
      simpa only [V, Complex.norm_real] using (massive_running_clip_norm_le_one m q.1)⟩
  have hu ε := hi ε U (Complex.continuous_ofReal.measurable.comp
    (massive_running_correction_measurable hm))
    ⟨2, fun q => by simpa only [U, Complex.norm_real] using massive_running_correction_norm_le m q⟩
  change (∫ q, diamond.massiveStableRunningIntegrand εPos a m q h * (f q : ℂ)) -
      (∫ q, diamond.massiveStableRunningIntegrand εNeg a m q h * (f q : ℂ)) = _
  rw [Plane.massiveStablePairing, Plane.massiveStablePairing, dif_pos hh, dif_pos hh]
  have e₁ : (fun q => diamond.massiveStableRunningIntegrand εPos a m q h * (f q : ℂ)) =
      fun q => Complex.I * (F εPos q * W q * (f q : ℂ)) := by
    funext q
    simp only [Plane.massiveStableRunningIntegrand, hPos, one_mul, F, W]
    ring
  have e₂ : (fun q => diamond.massiveStableRunningIntegrand εNeg a m q h * (f q : ℂ)) =
      fun q => -Complex.I * (F εNeg q * W q * (f q : ℂ)) := by
    funext q
    simp only [Plane.massiveStableRunningIntegrand, hNeg, neg_one_mul, Complex.ofReal_neg, F, W]
    ring
  rw [e₁, e₂, ← integral_sub ((hw εPos).const_mul _) ((hw εNeg).const_mul _)]
  have er (ε : Evolution) :
      (fun q : MassiveMomentum =>
        (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
          diamond.poleCoefficient ε ⟨h, hh⟩ (massiveD m q)) * (massiveRunningTest m f q : ℂ)) =
        fun q => F ε q * V q * (f q : ℂ) := by
    funext q
    simp only [F, V, Plane.massiveStableFactor, dif_pos hh, massiveD, massiveRunningTest,
      Complex.ofReal_mul, mul_assoc]
  rw [er εPos, er εNeg]
  have eU : (fun q => (F εPos q + F εNeg q) * U q * (f q : ℂ)) =
      fun q => (F εPos q * U q * (f q : ℂ)) + (F εNeg q * U q * (f q : ℂ)) := by
    funext q
    ring
  change _ = Complex.I * ((∫ q, F εPos q * V q * (f q : ℂ)) +
    (∫ q, F εNeg q * V q * (f q : ℂ)) + ∫ q : MassiveMomentum, (F εPos q + F εNeg q) * U q * (f q : ℂ))
  have hcombine := integral_add ((hv εPos).add (hv εNeg)) ((hu εPos).add (hu εNeg))
  simp only [Pi.add_apply] at hcombine
  rw [eU, ← integral_add (hv εPos) (hv εNeg), ← hcombine, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only [Pi.add_apply]
  have hWV : W q = V q + U q := by
    simp only [W, V, U, massiveRunningCorrection, Complex.ofReal_sub]
    ring
  rw [hWV]
  ring

/-- The full stable-half line with the running numerator has the signed
real-weighted PV and the signed two-sheet sine residue. -/
theorem Plane.massive_stable_running_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.massiveStableRunningPairing εPos a m f h -
      diamond.massiveStableRunningPairing εNeg a m f h) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Complex.I * (massiveRunningRealPV a m f : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (Real.sin (a * m) : ℂ) * (massiveSignedShellTest m f : ℂ))) := by
  obtain ⟨K, hK⟩ := massive_running_test_lipschitz hm hf hs
  have H := diamond.massive_stable_pairing_sum_limit εPos εNeg hPos hNeg ha
    (b := m ^ 2 / 4) (by positivity) (by nlinarith [sq_nonneg m]) hm hK
    (massive_running_test_hasCompactSupport m hs)
  rw [massive_running_test_fullShellTest hm] at H
  have hR := diamond.massive_stable_correction_test_sum_limit εPos εNeg hPos hNeg ha hm hf.continuous hs
  have H := (H.add hR).const_mul Complex.I
  have he :
      Complex.I * ((2 * (stableMassiveRealPV (m ^ 2 / 4) a m (massiveRunningTest m f) : ℂ) +
        2 * (Real.pi : ℂ) * (Real.sin (a * m) : ℂ) * (massiveSignedShellTest m f : ℂ)) +
          2 * (massiveRunningRealCorrection a m f : ℂ)) =
      2 * Complex.I * (massiveRunningRealPV a m f : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (Real.sin (a * m) : ℂ) * (massiveSignedShellTest m f : ℂ) := by
    rw [massiveRunningRealPV, Complex.ofReal_add]
    ring
  rw [he] at H
  refine H.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (diamond.massive_stable_running_jump_split εPos εNeg hPos hNeg hm hf.continuous hs hh).symm

theorem Plane.massive_stable_running_directed_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => directed (diamond.massiveStableRunningPairing εPos a m f h -
      diamond.massiveStableRunningPairing εNeg a m f h)) (𝓝[>] (0 : ℝ))
      (𝓝 (directed (2 * Complex.I * (massiveRunningRealPV a m f : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (Real.sin (a * m) : ℂ) * (massiveSignedShellTest m f : ℂ)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.massive_stable_running_jump εPos εNeg hPos hNeg ha hm hf hs)

end UV.SectorPlane
