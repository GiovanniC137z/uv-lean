import UV.ContinueStableMassiveJump

/-! The sum of the two literal stable-half boundary coefficients. The
running unit changes sign between the two evolutions, so its full
line jump uses this sum. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- The real part common to the two stable-half boundary values. -/
def stableBoundaryReal (a w : ℝ) : ℝ :=
  if 0 < w then Real.cos (a * Real.sqrt w) else Real.exp (-(a * Real.sqrt (-w)))

def stableMassiveRealPV (b a m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  Real.cos (a * m) * massiveShellPV b m f +
    ∫ q : MassiveMomentum, ((stableBoundaryReal a (shellSquare q.1 q.2) - Real.cos (a * m)) /
      massiveD m q) * f q

private def stableBoundaryValue (a η w : ℝ) : ℂ :=
  if 0 < w then Complex.exp (((η * a * Real.sqrt w : ℝ) : ℂ) * Complex.I)
  else Complex.exp ((-(a * Real.sqrt (-w)) : ℝ) : ℂ)

private theorem Plane.stable_half_coefficient_full_boundary (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    Tendsto (diamond.stableHalfCoefficient ε a w) (𝓝[>] (0 : ℝ))
      (𝓝 (stableBoundaryValue a (diamond.eta ε) w)) := by
  rcases lt_or_gt_of_ne hw with h | h
  · simpa only [stableBoundaryValue, if_neg h.not_gt] using
      diamond.stable_half_spacelike_coefficient_limit ε a h
  · simpa only [stableBoundaryValue, if_pos h] using
      diamond.stable_half_timed_coefficient_limit ε a h

private theorem stable_boundary_value_sum {a w : ℝ} {s t : ℝ}
    (hs : s = 1) (ht : t = -1) :
    stableBoundaryValue a s w + stableBoundaryValue a t w = 2 * (stableBoundaryReal a w : ℂ) := by
  by_cases h : 0 < w
  · simp only [stableBoundaryValue, stableBoundaryReal, if_pos h, hs, ht, one_mul, neg_mul]
    have H := stable_half_boundary_phase_sum a (Real.sqrt w) (Real.sqrt_nonneg w)
    rwa [Real.sq_sqrt h.le] at H
  · simp only [stableBoundaryValue, stableBoundaryReal, if_neg h, Complex.ofReal_exp]
    ring

def Plane.massiveStableFactor (diamond : Plane E) (ε : Evolution) (a m w h : ℝ) : ℂ :=
  if hh : 0 < h then diamond.stableHalfCoefficient ε a w h *
    diamond.poleCoefficient ε ⟨h, hh⟩ (w - m ^ 2) else 0

theorem Plane.massive_stable_factor_continuous (diamond : Plane E) (ε : Evolution) (a m : ℝ)
    (h : Height) : Continuous (fun w => diamond.massiveStableFactor ε a m w h) := by
  simp only [Plane.massiveStableFactor, dif_pos h.property]
  exact (diamond.stable_half_coefficient_continuous ε a h).mul
    ((diamond.pole_coefficient_continuous ε h).comp (continuous_id.sub continuous_const))

private theorem Plane.massive_pole_off_shell_limit (diamond : Plane E) (ε : Evolution)
    {D : ℝ} (hD : D ≠ 0) :
    Tendsto (fun h : ℝ => (((D : ℂ) + Complex.I * ((diamond.eta ε * h : ℝ) : ℂ)))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (D : ℂ)⁻¹) := by
  have hc : Continuous (fun h : ℝ => (D : ℂ) + Complex.I *
      ((diamond.eta ε * h : ℝ) : ℂ)) := by fun_prop
  have hn : (D : ℂ) + Complex.I * ((diamond.eta ε * (0 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa only [mul_zero, Complex.ofReal_zero, add_zero, ne_eq, Complex.ofReal_eq_zero] using hD
  have hi := hc.continuousAt (x := (0 : ℝ)) |>.inv₀ hn
  simpa using hi.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

theorem Plane.massive_stable_factor_sum_pointwise (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (a m : ℝ) {w : ℝ} (hw : w ≠ 0) (hD : w - m ^ 2 ≠ 0) :
    Tendsto (fun h => diamond.massiveStableFactor εPos a m w h +
      diamond.massiveStableFactor εNeg a m w h) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * ((stableBoundaryReal a w / (w - m ^ 2) : ℝ) : ℂ))) := by
  have h (ε : Evolution) := (diamond.stable_half_coefficient_full_boundary ε a hw).mul
    (diamond.massive_pole_off_shell_limit ε hD)
  have H (ε : Evolution) := (h ε).congr' (show _ =ᶠ[𝓝[>] 0]
      diamond.massiveStableFactor ε a m w by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [Plane.massiveStableFactor, dif_pos hh', diamond.pole_coefficient_eq_inv]
    rfl)
  have ht := (H εPos).add (H εNeg)
  convert ht using 2
  change _ = _ * _ + _ * _
  rw [← add_mul, stable_boundary_value_sum hPos hNeg]
  push_cast
  ring

theorem Plane.massive_stable_factor_norm_bound (diamond : Plane E) (ε : Evolution)
    {a m w h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (hD : w - m ^ 2 ≠ 0) :
    ‖diamond.massiveStableFactor ε a m w h‖ ≤ |w - m ^ 2|⁻¹ := by
  let D := w - m ^ 2
  let z := diamond.shiftedShellCoefficient ε ⟨h, hh⟩ D
  have hz : |D| ≤ ‖z‖ := by
    simpa [z, Plane.shiftedShellCoefficient] using Complex.abs_re_le_norm z
  rw [Plane.massiveStableFactor, dif_pos hh, diamond.pole_coefficient_eq_inv, norm_mul, norm_inv]
  apply (mul_le_mul_of_nonneg_right (diamond.stable_half_coefficient_norm_le_one ε ha hh)
    (inv_nonneg.mpr (norm_nonneg z))).trans
  rw [one_mul]
  exact inv_anti₀ (abs_pos.mpr hD) hz

private theorem Plane.massive_stable_remainder_pointwise_sum (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (a : ℝ) {m w : ℝ} (hm : 0 < m) (hw : w ≠ 0) (hD : w - m ^ 2 ≠ 0) :
    Tendsto (fun h => diamond.massiveStableRemainder εPos a m w h +
      diamond.massiveStableRemainder εNeg a m w h) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * (((stableBoundaryReal a w - Real.cos (a * m)) / (w - m ^ 2) : ℝ) : ℂ))) := by
  have hc (ε : Evolution) := diamond.stable_half_coefficient_full_boundary ε a
    (w := m ^ 2) (sq_pos_of_pos hm).ne'
  have h (ε : Evolution) := ((diamond.stable_half_coefficient_full_boundary ε a hw).sub
    (hc ε)).mul (diamond.massive_pole_off_shell_limit ε hD)
  have H (ε : Evolution) := (h ε).congr' (show _ =ᶠ[𝓝[>] 0]
      diamond.massiveStableRemainder ε a m w by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [Plane.massiveStableRemainder, dif_pos hh', diamond.pole_coefficient_eq_inv]
    rfl)
  have ht := (H εPos).add (H εNeg)
  convert ht using 2
  change _ = (_ - _) * _ + (_ - _) * _
  have hmass := stable_boundary_value_sum (a := a) (w := m ^ 2) hPos hNeg
  rw [stableBoundaryReal, if_pos (sq_pos_of_pos hm), Real.sqrt_sq hm.le] at hmass
  rw [← add_mul, sub_add_sub_comm, stable_boundary_value_sum hPos hNeg, hmass]
  push_cast
  ring

theorem Plane.massive_stable_remainder_integrable (diamond : Plane E) (ε : Evolution)
    (a m : ℝ) (h : Height) {f : MassiveMomentum → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : Integrable (fun q : MassiveMomentum =>
      diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h * (f q : ℂ)) := by
  have hc : Continuous (fun q : MassiveMomentum =>
      diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h) := by
    simp only [Plane.massiveStableRemainder, dif_pos h.property]
    exact (((diamond.stable_half_coefficient_continuous ε a h).comp
      shellSquare_continuous).sub continuous_const).mul
      ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m))
  exact (hc.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
    ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left (f := _))

theorem Plane.massive_stable_remainder_test_sum_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : MassiveMomentum,
      (diamond.massiveStableRemainder εPos a m (shellSquare q.1 q.2) h +
        diamond.massiveStableRemainder εNeg a m (shellSquare q.1 q.2) h) * (f q : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * ((∫ q : MassiveMomentum,
        ((stableBoundaryReal a (shellSquare q.1 q.2) - Real.cos (a * m)) /
          massiveD m q) * f q : ℝ) : ℂ))) := by
  let B := max (a / (2 * Real.sqrt b)) (2 / b)
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (fun q : MassiveMomentum => (2 * B) * ‖f q‖) ?_ ?_
    ((hf.integrable_of_hasCompactSupport hs).norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    simp_rw [add_mul]
    exact ((diamond.massive_stable_remainder_integrable εPos a m ⟨h, hh'⟩ hf hs).add
      (diamond.massive_stable_remainder_integrable εNeg a m ⟨h, hh'⟩ hf hs)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    refine Eventually.of_forall fun q => ?_
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h₁ := diamond.massive_stable_remainder_norm_bound εPos ha hb hmb hh' (shellSquare q.1 q.2)
    have h₂ := diamond.massive_stable_remainder_norm_bound εNeg ha hb hmb hh' (shellSquare q.1 q.2)
    exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)
  · filter_upwards [massless_shell_nonzero_ae, massiveD_nonzero_ae m] with q hq hd
    have h := (diamond.massive_stable_remainder_pointwise_sum εPos εNeg hPos hNeg a hm hq hd).mul_const
      (f q : ℂ)
    convert h using 2
    unfold massiveD
    push_cast
    ring


private theorem Plane.massive_stable_pairing_decompose (diamond : Plane E) (ε : Evolution)
    (a m : ℝ) {h : ℝ} (hh : 0 < h) {f : MassiveMomentum → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    diamond.massiveStablePairing ε a m f h =
      diamond.stableHalfCoefficient ε a (m ^ 2) h * diamond.bareMassivePairing ε m f h +
      ∫ q : MassiveMomentum, diamond.massiveStableRemainder ε a m (shellSquare q.1 q.2) h * (f q : ℂ) := by
  let F (q : MassiveMomentum) := diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h
  let K := diamond.stableHalfCoefficient ε a (m ^ 2) h
  let R (q : MassiveMomentum) := diamond.poleCoefficient ε ⟨h, hh⟩ (massiveD m q)
  have hRc : Continuous R :=
    (diamond.pole_coefficient_continuous ε ⟨h, hh⟩).comp (massiveD_continuous m)
  have hfC : Continuous (fun q : MassiveMomentum => (f q : ℂ)) := Complex.continuous_ofReal.comp hf
  have hfS : HasCompactSupport (fun q : MassiveMomentum => (f q : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h₁ : Integrable (fun q => K * (R q * (f q : ℂ))) :=
    ((hRc.mul hfC).integrable_of_hasCompactSupport (hfS.mul_left (f := R))).const_mul _
  have h₂ : Integrable (fun q => ((F q - K) * R q) * (f q : ℂ)) :=
    diamond.massive_stable_remainder_integrable ε a m ⟨h, hh⟩ hf hs |>.congr (by
      filter_upwards with q
      simp only [Plane.massiveStableRemainder, dif_pos hh, F, K, R, massiveD])
  simp only [Plane.massiveStablePairing, Plane.bareMassivePairing, Plane.massiveStableRemainder, dif_pos hh]
  change (∫ q : MassiveMomentum, (F q * R q) * (f q : ℂ)) =
    K * (∫ q : MassiveMomentum, R q * (f q : ℂ)) +
    ∫ q : MassiveMomentum, ((F q - K) * R q) * (f q : ℂ)
  rw [← integral_const_mul, ← integral_add h₁ h₂]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  ring

private theorem stable_massive_phase_combine_sum {a m : ℝ} (hm : 0 ≤ m) (P M Q : ℂ) :
    Complex.exp (((a * m : ℝ) : ℂ) * Complex.I) * (P - Complex.I * (Real.pi : ℂ) * M) +
      Complex.exp (((-(a * m) : ℝ) : ℂ) * Complex.I) * (P + Complex.I * (Real.pi : ℂ) * M) +
      2 * Q =
    2 * ((Real.cos (a * m) : ℂ) * P + Q) +
      2 * (Real.pi : ℂ) * (Real.sin (a * m) : ℂ) * M := by
  have hd := stable_half_boundary_phase_difference a (m ^ 2)
  rw [Real.sqrt_sq hm] at hd
  have hs := stable_half_boundary_phase_sum a m hm
  rw [Real.sqrt_sq hm] at hs
  linear_combination (norm := ring_nf) P * hs - Complex.I * (Real.pi : ℂ) * M * hd
  rw [Complex.I_sq]
  ring

/-- The two sector-side stable factors add to twice the real boundary
weight times the full principal value, plus the sine shell residue. -/
theorem Plane.massive_stable_pairing_sum_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmb : 2 * b ≤ m ^ 2) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.massiveStablePairing εPos a m f h + diamond.massiveStablePairing εNeg a m f h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (stableMassiveRealPV b a m f : ℂ) +
        2 * (Real.pi : ℂ) * (Real.sin (a * m) : ℂ) * (fullShellTest m f : ℂ))) := by
  have ha₁ := diamond.stable_half_timed_coefficient_limit εPos a (sq_pos_of_pos hm)
  have ha₂ := diamond.stable_half_timed_coefficient_limit εNeg a (sq_pos_of_pos hm)
  rw [hPos, one_mul, Real.sqrt_sq hm.le] at ha₁
  rw [hNeg, neg_one_mul, neg_mul, Real.sqrt_sq hm.le] at ha₂
  have h₁ := ha₁.mul (diamond.bare_massive_pairing_limit εPos hb hmb hf hs)
  have h₂ := ha₂.mul (diamond.bare_massive_pairing_limit εNeg hb hmb hf hs)
  rw [hPos] at h₁
  rw [hNeg] at h₂
  have hR := diamond.massive_stable_remainder_test_sum_limit εPos εNeg hPos hNeg ha hb hmb hm hf.continuous hs
  let P : ℂ := (massiveShellPV b m f : ℂ)
  let M : ℂ := (fullShellTest m f : ℂ)
  let Q : ℂ := ((∫ q : MassiveMomentum,
        ((stableBoundaryReal a (shellSquare q.1 q.2) - Real.cos (a * m)) /
          massiveD m q) * f q : ℝ) : ℂ)
  have hsum := (h₁.add h₂).add hR
  simp only [Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_mul, mul_one, mul_neg,
    neg_mul, sub_neg_eq_add, ← mul_assoc] at hsum
  have hlim := stable_massive_phase_combine_sum (a := a) hm.le P M Q
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, neg_mul] at hlim
  rw [hlim] at hsum
  rw [stableMassiveRealPV, Complex.ofReal_add, Complex.ofReal_mul]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  rw [diamond.massive_stable_pairing_decompose εPos a m hh' hf.continuous hs,
    diamond.massive_stable_pairing_decompose εNeg a m hh' hf.continuous hs]
  simp_rw [add_mul]
  rw [integral_add (diamond.massive_stable_remainder_integrable εPos a m
    ⟨h, hh'⟩ hf.continuous hs) (diamond.massive_stable_remainder_integrable εNeg a m
    ⟨h, hh'⟩ hf.continuous hs)]
  ring

end UV.SectorPlane
