import UV.ContinueStableMassivePV
import UV.ContinueStableMassiveRemainder

/-! The literal positive-mass stable-half jump on compact intrinsic
four-momentum tests, including the spacelike and timelike sides of
the branch edge. The shell distribution retains both axial sheets. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

theorem massiveD_nonzero_ae (m : ℝ) : ∀ᵐ q : MassiveMomentum ∂volume, massiveD m q ≠ 0 := by
  have hm : MeasurableSet {q : MassiveMomentum | massiveD m q ≠ 0} :=
    (measurableSet_eq_fun (massiveD_continuous m).measurable measurable_const).compl
  change ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure Spatial)), massiveD m q ≠ 0
  rw [Measure.ae_prod_iff_ae_ae hm, Measure.ae_ae_comm hm]
  refine Eventually.of_forall fun p => ?_
  have hp : ∀ᵐ t : ℝ ∂volume, t ≠ shellFrequency m p := by rw [ae_iff]; simp
  have hn : ∀ᵐ t : ℝ ∂volume, t ≠ -shellFrequency m p := by rw [ae_iff]; simp
  filter_upwards [hp, hn] with t ht ht'
  intro h
  have hsq : t ^ 2 = shellFrequency m p ^ 2 := by
    dsimp [massiveD, shellSquare] at h
    rw [shell_frequency_square]
    linarith
  exact (eq_or_eq_neg_of_sq_eq_sq t (shellFrequency m p) hsq).elim ht ht'

/-- Timelike sine multiplier in the boundary coefficient jump. -/
def stableTimelikeSine (a w : ℝ) : ℝ :=
  if 0 < w then Real.sin (a * Real.sqrt w) else 0

/-- Massive weighted principal value. The sine multiplier is smooth at
the massive shell. Its value at the shell multiplies the bare PV; the
remaining difference is tested with the ordinary inverse. -/
def stableMassiveSinePV (b a m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  Real.sin (a * m) * massiveShellPV b m f +
    ∫ q : MassiveMomentum, ((stableTimelikeSine a (shellSquare q.1 q.2) -
      Real.sin (a * m)) / massiveD m q) * f q

variable {E : Type*} [NormedAddCommGroup E]

private def stableBoundaryPhase (a η w : ℝ) : ℂ :=
  if 0 < w then Complex.exp (((η * a * Real.sqrt w : ℝ) : ℂ) * Complex.I)
  else Complex.exp ((-(a * Real.sqrt (-w)) : ℝ) : ℂ)

private theorem Plane.stable_half_coefficient_boundary (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    Tendsto (diamond.stableHalfCoefficient ε a w) (𝓝[>] (0 : ℝ))
      (𝓝 (stableBoundaryPhase a (diamond.eta ε) w)) := by
  rcases lt_or_gt_of_ne hw with h | h
  · simpa only [stableBoundaryPhase, if_neg h.not_gt] using
      diamond.stable_half_spacelike_coefficient_limit ε a h
  · simpa only [stableBoundaryPhase, if_pos h] using
      diamond.stable_half_timed_coefficient_limit ε a h

private theorem stable_boundary_difference {a w : ℝ} {s t : ℝ}
    (hs : s = 1) (ht : t = -1) :
    stableBoundaryPhase a s w - stableBoundaryPhase a t w =
      2 * Complex.I * (stableTimelikeSine a w : ℂ) := by
  by_cases h : 0 < w
  · simp only [stableBoundaryPhase, stableTimelikeSine, if_pos h, hs, ht, one_mul, neg_mul]
    exact stable_half_boundary_phase_difference a w
  · simp [stableBoundaryPhase, stableTimelikeSine, h]

private theorem Plane.massive_stable_remainder_pointwise_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (a : ℝ) {m w : ℝ} (hm : 0 < m) (hw : w ≠ 0) (hD : w - m ^ 2 ≠ 0) :
    Tendsto (fun h => diamond.massiveStableRemainder εPos a m w h -
      diamond.massiveStableRemainder εNeg a m w h) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Complex.I * (((stableTimelikeSine a w - Real.sin (a * m)) / (w - m ^ 2) : ℝ) : ℂ))) := by
  let P (ε : Evolution) (h : ℝ) :=
    ((((w - m ^ 2 : ℝ) : ℂ)) + Complex.I * ((diamond.eta ε * h : ℝ) : ℂ))⁻¹
  have hP (ε : Evolution) : Tendsto (P ε) (𝓝[>] (0 : ℝ)) (𝓝 (((w - m ^ 2 : ℝ) : ℂ))⁻¹) := by
    have hc : Continuous (fun h : ℝ => ((w - m ^ 2 : ℝ) : ℂ) +
        Complex.I * ((diamond.eta ε * h : ℝ) : ℂ)) := by fun_prop
    have hn : ((w - m ^ 2 : ℝ) : ℂ) + Complex.I * ((diamond.eta ε * (0 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      simpa only [mul_zero, Complex.ofReal_zero, add_zero, ne_eq, Complex.ofReal_eq_zero] using hD
    have hi := hc.continuousAt (x := (0 : ℝ)) |>.inv₀ hn
    simpa [P] using hi.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hc (ε : Evolution) := diamond.stable_half_coefficient_boundary ε a
    (w := m ^ 2) (sq_pos_of_pos hm).ne'
  have h (ε : Evolution) := ((diamond.stable_half_coefficient_boundary ε a hw).sub
    (hc ε)).mul (hP ε)
  have H (ε : Evolution) := (h ε).congr' (show _ =ᶠ[𝓝[>] 0]
      diamond.massiveStableRemainder ε a m w by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [Plane.massiveStableRemainder, dif_pos hh', diamond.pole_coefficient_eq_inv]
    rfl)
  have ht := (H εPos).sub (H εNeg)
  convert ht using 2
  change _ = (_ - _) * _ - (_ - _) * _
  have hdiff := stable_boundary_difference (a := a) (w := w) hPos hNeg
  have hmass := stable_boundary_difference (a := a) (w := m ^ 2) hPos hNeg
  rw [stableTimelikeSine, if_pos (sq_pos_of_pos hm), Real.sqrt_sq hm.le] at hmass
  rw [← sub_mul, sub_sub_sub_comm, hdiff, hmass]
  push_cast
  ring

/-- The remainder limit is dominated in the actual four-momentum measure,
including through the branch edge. -/
theorem Plane.massive_stable_remainder_test_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : MassiveMomentum,
      (diamond.massiveStableRemainder εPos a m (shellSquare q.1 q.2) h -
        diamond.massiveStableRemainder εNeg a m (shellSquare q.1 q.2) h) * (f q : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Complex.I * ((∫ q : MassiveMomentum,
        ((stableTimelikeSine a (shellSquare q.1 q.2) - Real.sin (a * m)) /
          massiveD m q) * f q : ℝ) : ℂ))) := by
  let B := max (a / (2 * Real.sqrt b)) (2 / b)
  have hB : 0 ≤ B := le_trans (by positivity) (le_max_left _ _)
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (fun q : MassiveMomentum => (2 * B) * ‖f q‖) ?_ ?_
    ((hf.integrable_of_hasCompactSupport hs).norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hc (ε : Evolution) : Continuous (fun q : MassiveMomentum =>
        diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h) := by
      simp only [Plane.massiveStableRemainder, dif_pos hh']
      exact (((diamond.stable_half_coefficient_continuous ε a ⟨h, hh'⟩).comp
        shellSquare_continuous).sub continuous_const).mul
        ((diamond.pole_coefficient_continuous ε ⟨h, hh'⟩).comp (massiveD_continuous m))
    exact (((hc εPos).sub (hc εNeg)).mul (Complex.continuous_ofReal.comp hf)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    refine Eventually.of_forall fun q => ?_
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h₁ := diamond.massive_stable_remainder_norm_bound εPos ha hb hmb hh' (shellSquare q.1 q.2)
    have h₂ := diamond.massive_stable_remainder_norm_bound εNeg ha hb hmb hh' (shellSquare q.1 q.2)
    exact ((norm_sub_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)
  · filter_upwards [massless_shell_nonzero_ae, massiveD_nonzero_ae m] with q hq hd
    have h := (diamond.massive_stable_remainder_pointwise_jump εPos εNeg hPos hNeg a hm hq hd).mul_const
      (f q : ℂ)
    convert h using 2
    unfold massiveD
    push_cast
    ring

def Plane.bareMassivePairing (diamond : Plane E) (ε : Evolution) (m : ℝ)
    (f : MassiveMomentum → ℝ) (h : ℝ) : ℂ :=
  if hh : 0 < h then ∫ q : MassiveMomentum, diamond.poleCoefficient ε ⟨h, hh⟩ (massiveD m q) *
    (f q : ℂ) else 0

theorem Plane.bare_massive_pairing_limit (diamond : Plane E) (ε : Evolution)
    {b m : ℝ} (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (diamond.bareMassivePairing ε m f) (𝓝[>] (0 : ℝ))
      (𝓝 ((massiveShellPV b m f : ℂ) - Complex.I * (diamond.eta ε : ℂ) *
        ((Real.pi * fullShellTest m f : ℝ) : ℂ))) := by
  have hPV := pole_pv_full_massive_shell_limit hb hmb hf hs
  have hP := pole_poisson_full_shell_limit m hf.continuous hs
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hPV).sub
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hP).const_mul
      (Complex.I * (diamond.eta ε : ℂ)))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hfC : Continuous (fun q : MassiveMomentum => (f q : ℂ)) := Complex.continuous_ofReal.comp hf.continuous
  have hfS : HasCompactSupport (fun q : MassiveMomentum => (f q : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi {u : MassiveMomentum → ℂ} (hu : Continuous u) :
      Integrable (fun q => u q * (f q : ℂ)) :=
    (hu.mul hfC).integrable_of_hasCompactSupport (hfS.mul_left (f := u))
  have hPVc : Continuous (polePV h) := continuous_iff_continuousAt.mpr
    fun D => (polePV_hasDerivAt hh' D).continuousAt
  have hPc : Continuous (polePoisson h) := continuous_iff_continuousAt.mpr
    fun D => (polePoisson_hasDerivAt hh' D).continuousAt
  have hi₁ : Integrable (fun q : MassiveMomentum => (polePV h (massiveD m q) : ℂ) * (f q : ℂ)) :=
    hi (Complex.continuous_ofReal.comp (hPVc.comp (massiveD_continuous m)))
  have hi₂ : Integrable (fun q : MassiveMomentum =>
      (polePoisson h (shellSquare q.1 q.2 - m ^ 2) : ℂ) * (f q : ℂ)) :=
    hi (Complex.continuous_ofReal.comp (hPc.comp (massiveD_continuous m)))
  dsimp only [Function.comp_apply]
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]
  rw [← integral_const_mul, ← integral_sub hi₁ (hi₂.const_mul _)]
  simp only [Plane.bareMassivePairing, dif_pos hh']
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only
  rw [diamond.pole_coefficient_split]
  unfold massiveD
  push_cast
  ring

theorem Plane.massive_stable_integrand_directed (diamond : Plane E) (ε : Evolution)
    (h : Height) (a m : ℝ) (q : MassiveMomentum) :
    directed (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      diamond.poleCoefficient ε h (massiveD m q)) =
      diamond.stableHalfNumerator ε h a (shellSquare q.1 q.2) *
        diamond.poleInverse ε h (massiveD m q) := by
  rw [directed_mul, Plane.stableHalfCoefficient, dif_pos h.property,
    diamond.stable_half_numerator_characters, Plane.stableHalfNumerator,
    diamond.pole_coefficient_eq_inv, diamond.pole_inverse_complex]
  rfl

/-- Literal stable-half numerator times the same finite-height massive
pole; the coefficient is extracted only in the declared character. -/
def Plane.massiveStablePairing (diamond : Plane E) (ε : Evolution) (a m : ℝ)
    (f : MassiveMomentum → ℝ) (h : ℝ) : ℂ :=
  if hh : 0 < h then
    ∫ q : MassiveMomentum, (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      diamond.poleCoefficient ε ⟨h, hh⟩ (massiveD m q)) * (f q : ℂ)
  else 0

private theorem Plane.massive_stable_pairing_split (diamond : Plane E) (ε : Evolution)
    (a m : ℝ) {h : ℝ} (hh : 0 < h) {f : MassiveMomentum → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    diamond.massiveStablePairing ε a m f h =
      diamond.stableHalfCoefficient ε a (m ^ 2) h * diamond.bareMassivePairing ε m f h +
      ∫ q : MassiveMomentum, diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h * (f q : ℂ) := by
  let F (q : MassiveMomentum) := diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h
  let K := diamond.stableHalfCoefficient ε a (m ^ 2) h
  let R (q : MassiveMomentum) := diamond.poleCoefficient ε ⟨h, hh⟩ (massiveD m q)
  have hFc : Continuous F :=
    (diamond.stable_half_coefficient_continuous ε a ⟨h, hh⟩).comp shellSquare_continuous
  have hRc : Continuous R :=
    (diamond.pole_coefficient_continuous ε ⟨h, hh⟩).comp (massiveD_continuous m)
  have hfC : Continuous (fun q : MassiveMomentum => (f q : ℂ)) := Complex.continuous_ofReal.comp hf
  have hfS : HasCompactSupport (fun q : MassiveMomentum => (f q : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi {u : MassiveMomentum → ℂ} (hu : Continuous u) :
      Integrable (fun q => u q * (f q : ℂ)) :=
    (hu.mul hfC).integrable_of_hasCompactSupport (hfS.mul_left (f := u))
  have h₁ : Integrable (fun q => K * (R q * (f q : ℂ))) := (hi hRc).const_mul _
  have h₂ := hi ((hFc.sub (continuous_const (y := K))).mul hRc)
  simp only [Plane.massiveStablePairing, Plane.bareMassivePairing, Plane.massiveStableRemainder, dif_pos hh]
  change (∫ q : MassiveMomentum, (F q * R q) * (f q : ℂ)) =
    K * (∫ q : MassiveMomentum, R q * (f q : ℂ)) +
    ∫ q : MassiveMomentum, ((F q - K) * R q) * (f q : ℂ)
  rw [← integral_const_mul, ← integral_add h₁ h₂]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  ring

private theorem stable_massive_phase_combine {a m : ℝ} (hm : 0 ≤ m) (P M Q : ℂ) :
    Complex.exp (((a * m : ℝ) : ℂ) * Complex.I) * (P - Complex.I * (Real.pi : ℂ) * M) -
      Complex.exp (((-(a * m) : ℝ) : ℂ) * Complex.I) * (P + Complex.I * (Real.pi : ℂ) * M) +
      2 * Complex.I * Q =
    2 * Complex.I * ((Real.sin (a * m) : ℂ) * P + Q) -
      2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * M := by
  have hd := stable_half_boundary_phase_difference a (m ^ 2)
  rw [Real.sqrt_sq hm] at hd
  have hs := stable_half_boundary_phase_sum a m hm
  rw [Real.sqrt_sq hm] at hs
  linear_combination P * hd - Complex.I * (Real.pi : ℂ) * M * hs

/-- The complete coefficient jump on the fixed massive sector plane,
with compact tests crossing the branch edge. No sign selector is
introduced into the two-sheet delta. -/
theorem Plane.massive_stable_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.massiveStablePairing εPos a m f h - diamond.massiveStablePairing εNeg a m f h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Complex.I * (stableMassiveSinePV b a m f : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * (fullShellTest m f : ℂ))) := by
  have ha₁ := diamond.stable_half_timed_coefficient_limit εPos a (sq_pos_of_pos hm)
  have ha₂ := diamond.stable_half_timed_coefficient_limit εNeg a (sq_pos_of_pos hm)
  rw [hPos, one_mul, Real.sqrt_sq hm.le] at ha₁
  rw [hNeg, neg_one_mul, neg_mul, Real.sqrt_sq hm.le] at ha₂
  have h₁ := ha₁.mul (diamond.bare_massive_pairing_limit εPos hb hmb hf hs)
  have h₂ := ha₂.mul (diamond.bare_massive_pairing_limit εNeg hb hmb hf hs)
  rw [hPos] at h₁
  rw [hNeg] at h₂
  have hR := diamond.massive_stable_remainder_test_limit εPos εNeg hPos hNeg ha hb hmb hm hf.continuous hs
  let P : ℂ := (massiveShellPV b m f : ℂ)
  let M : ℂ := (fullShellTest m f : ℂ)
  let Q : ℂ := ((∫ q : MassiveMomentum,
        ((stableTimelikeSine a (shellSquare q.1 q.2) - Real.sin (a * m)) /
          massiveD m q) * f q : ℝ) : ℂ)
  have hsum := (h₁.sub h₂).add hR
  simp only [Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_mul, mul_one, mul_neg,
    neg_mul, sub_neg_eq_add, ← mul_assoc] at hsum
  have hlim := stable_massive_phase_combine (a := a) hm.le P M Q
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, neg_mul] at hlim
  rw [hlim] at hsum
  rw [stableMassiveSinePV, Complex.ofReal_add, Complex.ofReal_mul]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  rw [diamond.massive_stable_pairing_split εPos a m hh' hf.continuous hs,
    diamond.massive_stable_pairing_split εNeg a m hh' hf.continuous hs]
  have hi (ε : Evolution) : Integrable (fun q : MassiveMomentum =>
      diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h * (f q : ℂ)) := by
    have hC : Continuous (fun q : MassiveMomentum =>
        diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h) := by
      simp only [Plane.massiveStableRemainder, dif_pos hh']
      exact (((diamond.stable_half_coefficient_continuous ε a ⟨h, hh'⟩).comp
        shellSquare_continuous).sub continuous_const).mul
        ((diamond.pole_coefficient_continuous ε ⟨h, hh'⟩).comp (massiveD_continuous m))
    exact (hC.mul (Complex.continuous_ofReal.comp hf.continuous)).integrable_of_hasCompactSupport
      ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left (f := _))
  have he :
      (∫ q : MassiveMomentum, (diamond.massiveStableRemainder εPos a m (shellSquare q.1 q.2) h -
          diamond.massiveStableRemainder εNeg a m (shellSquare q.1 q.2) h) * (f q : ℂ)) =
      (∫ q : MassiveMomentum, diamond.massiveStableRemainder εPos a m (shellSquare q.1 q.2) h * (f q : ℂ)) -
      (∫ q : MassiveMomentum, diamond.massiveStableRemainder εNeg a m (shellSquare q.1 q.2) h * (f q : ℂ)) := by
    simp_rw [sub_mul]
    rw [integral_sub (hi εPos) (hi εNeg)]
  rw [he]
  ring

theorem Plane.massive_stable_directed_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => directed (diamond.massiveStablePairing εPos a m f h - diamond.massiveStablePairing εNeg a m f h))
      (𝓝[>] (0 : ℝ)) (𝓝 (directed (2 * Complex.I * (stableMassiveSinePV b a m f : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * (fullShellTest m f : ℂ)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.massive_stable_jump εPos εNeg hPos hNeg ha hb hmb hm hf hs)

theorem massive_shell_pv_cutoff_independent {b c m : ℝ}
    (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hc : 0 < c) (hmc : 2 * c ≤ m ^ 2)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    massiveShellPV b m f = massiveShellPV c m f :=
  tendsto_nhds_unique (pole_pv_full_massive_shell_limit hb hmb hf hs)
    (pole_pv_full_massive_shell_limit hc hmc hf hs)

/-- The weighted distribution is intrinsic. Changing the auxiliary
width of the normal coarea chart leaves the pairing unchanged. -/
theorem stable_massive_sine_pv_cutoff_independent {a b c m : ℝ}
    (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hc : 0 < c) (hmc : 2 * c ≤ m ^ 2)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    stableMassiveSinePV b a m f = stableMassiveSinePV c a m f := by
  rw [stableMassiveSinePV, stableMassiveSinePV, massive_shell_pv_cutoff_independent hb hmb hc hmc hf hs]

/-- The full four-momentum coefficient jump with the canonical normal
chart radius m²/4, so only the positive mass is required as chart data. -/
theorem Plane.massive_stable_jump_canonical (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.massiveStablePairing εPos a m f h - diamond.massiveStablePairing εNeg a m f h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Complex.I * (stableMassiveSinePV (m ^ 2 / 4) a m f : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * (fullShellTest m f : ℂ))) :=
  diamond.massive_stable_jump εPos εNeg hPos hNeg ha
    (by positivity) (by nlinarith [sq_nonneg m]) hm hf hs

theorem Plane.massive_stable_directed_jump_canonical (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => directed (diamond.massiveStablePairing εPos a m f h - diamond.massiveStablePairing εNeg a m f h))
      (𝓝[>] (0 : ℝ)) (𝓝 (directed (2 * Complex.I * (stableMassiveSinePV (m ^ 2 / 4) a m f : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * (fullShellTest m f : ℂ)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.massive_stable_jump_canonical εPos εNeg hPos hNeg ha hm hf hs)

end UV.SectorPlane
