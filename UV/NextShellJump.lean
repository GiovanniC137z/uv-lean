import UV.FurtherCoincidentShell

/-! Analytic numerator discontinuities on a regular sector-plane shell
chart. The chart density and the test are included in the tested complex
numerators. The plus and minus sides are read out of the actual carrier
quotient on the same fixed plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

def complexShellPV (g : ℝ → ℂ) : ℂ :=
  (↑(∫ D in Ioi (0 : ℝ), symmetricTest (fun D => (g D).re) D) : ℂ) +
    (↑(∫ D in Ioi (0 : ℝ), symmetricTest (fun D => (g D).im) D) : ℂ) * Complex.I

theorem shell_re_lipschitz {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    LipschitzWith L (fun D => (g D).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro D D'
  rw [dist_eq_norm, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm (g D - g D')).trans (hg.norm_sub_le D D')

theorem shell_im_lipschitz {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    LipschitzWith L (fun D => (g D).im) := by
  apply LipschitzWith.of_dist_le_mul
  intro D D'
  rw [dist_eq_norm, ← Complex.sub_im]
  exact (Complex.abs_im_le_norm (g D - g D')).trans (hg.norm_sub_le D D')

theorem complex_shell_pv_sub {g k : ℝ → ℂ} {L K : ℝ≥0}
    (hg : LipschitzWith L g) (hk : LipschitzWith K k)
    (hgi : Integrable g) (hki : Integrable k) :
    complexShellPV (fun D => g D - k D) = complexShellPV g - complexShellPV k := by
  have hpoint (a b : ℝ → ℝ) (D : ℝ) :
      symmetricTest (fun x => a x - b x) D = symmetricTest a D - symmetricTest b D := by
    unfold symmetricTest; ring
  unfold complexShellPV
  simp_rw [Complex.sub_re, Complex.sub_im, hpoint]
  rw [integral_sub (symmetric_test_integrable (shell_re_lipschitz hg) hgi.re)
      (symmetric_test_integrable (shell_re_lipschitz hk) hki.re),
    integral_sub (symmetric_test_integrable (shell_im_lipschitz hg) hgi.im)
      (symmetric_test_integrable (shell_im_lipschitz hk) hki.im)]
  push_cast
  ring

theorem complex_shell_integral_split {p : ℝ → ℝ} {g : ℝ → ℂ}
    (hi : Integrable (fun D => p D • g D)) :
    (∫ D, p D • g D) =
      (↑(∫ D, p D * (g D).re) : ℂ) + (↑(∫ D, p D * (g D).im) : ℂ) * Complex.I := by
  symm
  have hc := integral_re_add_im hi
  change (↑(∫ D, (p D • g D).re) : ℂ) + (↑(∫ D, (p D • g D).im) : ℂ) * Complex.I =
    (∫ D, p D • g D) at hc
  simpa only [Complex.smul_re, Complex.smul_im, smul_eq_mul] using hc

theorem complex_shell_pv_limit {g : ℝ → ℂ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : HasCompactSupport g) :
    Tendsto (fun h : ℝ => ∫ D, polePV h D • g D)
      (𝓝[>] (0 : ℝ)) (𝓝 (complexShellPV g)) := by
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hs
  have hr := pole_pv_test_limit (shell_re_lipschitz hg) hgi.re
  have hi := pole_pv_test_limit (shell_im_lipschitz hg) hgi.im
  have hf := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul_const Complex.I)
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  have hc : Continuous (polePV h) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  exact (complex_shell_integral_split
    ((hc.smul hg.continuous).integrable_of_hasCompactSupport (hs.smul_left (f := polePV h)))).symm

theorem complex_shell_poisson_limit {g : ℝ → ℂ}
    (hg : Continuous g) (hs : HasCompactSupport g) :
    Tendsto (fun h : ℝ => ∫ D, polePoisson h D • g D)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ) * g 0)) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hs
  have hr := pole_poisson_test_limit (Complex.continuous_re.comp hg) C
    (fun D => (Complex.abs_re_le_norm (g D)).trans (hC D))
  have hi := pole_poisson_test_limit (Complex.continuous_im.comp hg) C
    (fun D => (Complex.abs_im_le_norm (g D)).trans (hC D))
  have hf := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul_const Complex.I)
  have h0 : (↑(Real.pi * (g 0).re) : ℂ) + (↑(Real.pi * (g 0).im) : ℂ) * Complex.I =
      (Real.pi : ℂ) * g 0 := by
    push_cast
    rw [mul_assoc, ← mul_add, Complex.re_add_im]
  simp only [Function.comp_apply] at hf
  rw [h0] at hf
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  have hc : Continuous (polePoisson h) :=
    continuous_const.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  exact (complex_shell_integral_split
    ((hc.smul hg).integrable_of_hasCompactSupport (hs.smul_left (f := polePoisson h)))).symm

variable {E : Type*} [NormedAddCommGroup E]

/-- Extract the first character after evaluating the actual vectorial inverse
at positive height. The second character is its conjugate. -/
def Plane.poleCoefficient (diamond : Plane E) (ε : Evolution) (height : Height) (D : ℝ) : ℂ :=
  (quotientCharacterEquiv (diamond.poleInverse ε height D)).1

theorem Plane.pole_coefficient_split (diamond : Plane E) (ε : Evolution)
    (h : Height) (D : ℝ) :
    diamond.poleCoefficient ε h D = (polePV (h : ℝ) D : ℂ) -
      Complex.I * ((diamond.eta ε * polePoisson (h : ℝ) D : ℝ) : ℂ) := by
  simp [Plane.poleCoefficient, diamond.inverse_pole_split ε h, directed]

theorem Plane.pole_coefficient_continuous (diamond : Plane E) (ε : Evolution) (h : Height) :
    Continuous (diamond.poleCoefficient ε h) := by
  rw [show diamond.poleCoefficient ε h =
    (fun D => (polePV (h : ℝ) D : ℂ) -
      Complex.I * ((diamond.eta ε * polePoisson (h : ℝ) D : ℝ) : ℂ)) from
    funext (diamond.pole_coefficient_split ε h)]
  have hp : Continuous (polePV (h : ℝ)) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const)
      (fun D => (add_pos_of_nonneg_of_pos (sq_nonneg D) (sq_pos_of_pos h.property)).ne')
  have hq : Continuous (polePoisson (h : ℝ)) :=
    continuous_const.div ((continuous_id.pow 2).add continuous_const)
      (fun D => (add_pos_of_nonneg_of_pos (sq_nonneg D) (sq_pos_of_pos h.property)).ne')
  exact (Complex.continuous_ofReal.comp hp).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul hq)))

/-- The limits of the tested coefficient family keep the declared eta
side. Lean's total real height parameter is used only on its positive ray. -/
theorem Plane.tested_pole_coefficient_limit (diamond : Plane E) (ε : Evolution)
    {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g) (hs : HasCompactSupport g) :
    Tendsto (fun h : ℝ => if hh : 0 < h then
      ∫ D, diamond.poleCoefficient ε ⟨h, hh⟩ D * g D else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (complexShellPV g -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * g 0))) := by
  have hpv := complex_shell_pv_limit hg hs
  have hpo := complex_shell_poisson_limit hg.continuous hs
  apply (hpv.sub (hpo.const_mul (Complex.I * (diamond.eta ε : ℂ)))).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  have hpc : Continuous (polePV h) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  have hqc : Continuous (polePoisson h) :=
    continuous_const.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  have hp : Integrable (fun D => polePV h D • g D) :=
    (hpc.smul hg.continuous).integrable_of_hasCompactSupport
    (hs.smul_left (f := polePV h))
  have hq : Integrable (fun D => polePoisson h D • g D) :=
    (hqc.smul hg.continuous).integrable_of_hasCompactSupport
    (hs.smul_left (f := polePoisson h))
  rw [dif_pos hpos, ← integral_const_mul, ← integral_sub hp (hq.const_mul _)]
  apply integral_congr_ae
  refine Eventually.of_forall fun D => ?_
  dsimp only
  rw [diamond.pole_coefficient_split]
  push_cast
  simp only [Complex.real_smul]
  ring

/-- The jump of the two tested boundary coefficients. Both sides belong
to the same fixed plane. Their positive and negative signs select the
auxiliary resolvent sides only. -/
theorem Plane.tested_pole_coefficient_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {gPos gNeg : ℝ → ℂ} {LPos LNeg : ℝ≥0}
    (hfPos : LipschitzWith LPos gPos) (hfNeg : LipschitzWith LNeg gNeg)
    (hsPos : HasCompactSupport gPos) (hsNeg : HasCompactSupport gNeg) :
    Tendsto (fun h : ℝ => if hh : 0 < h then
      (∫ D, diamond.poleCoefficient εPos ⟨h, hh⟩ D * gPos D) -
      (∫ D, diamond.poleCoefficient εNeg ⟨h, hh⟩ D * gNeg D) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (complexShellPV (fun D => gPos D - gNeg D) -
        Complex.I * (Real.pi : ℂ) * (gPos 0 + gNeg 0))) := by
  have h := (diamond.tested_pole_coefficient_limit εPos hfPos hsPos).sub
    (diamond.tested_pole_coefficient_limit εNeg hfNeg hsNeg)
  rw [hPos, hNeg] at h
  rw [complex_shell_pv_sub hfPos hfNeg
    (hfPos.continuous.integrable_of_hasCompactSupport hsPos)
    (hfNeg.continuous.integrable_of_hasCompactSupport hsNeg)]
  convert h using 1
  · funext h
    by_cases hh : 0 < h <;> simp [hh]
  · push_cast
    ring_nf

theorem Plane.common_numerator_pole_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g) (hs : HasCompactSupport g) :
    Tendsto (fun h : ℝ => if hh : 0 < h then
      (∫ D, diamond.poleCoefficient εPos ⟨h, hh⟩ D * g D) -
      (∫ D, diamond.poleCoefficient εNeg ⟨h, hh⟩ D * g D) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (Real.pi : ℂ) * Complex.I * g 0))) := by
  have h := diamond.tested_pole_coefficient_jump εPos εNeg hPos hNeg hg hg hs hs
  have hz : (complexShellPV fun D => g D - g D) = 0 := by
    simp [complexShellPV, symmetricTest]
  rw [hz, zero_sub] at h
  convert h using 2
  ring

theorem directed_shell_readout_continuous : Continuous (directed : ℂ → QuotientCarrier) :=
  quotientCharacterIsometry.symm.continuous.comp (continuous_id.prodMk continuous_star)

theorem Plane.directed_tested_pole_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {gPos gNeg : ℝ → ℂ} {LPos LNeg : ℝ≥0}
    (hfPos : LipschitzWith LPos gPos) (hfNeg : LipschitzWith LNeg gNeg)
    (hsPos : HasCompactSupport gPos) (hsNeg : HasCompactSupport gNeg) :
    Tendsto (fun h : ℝ => directed (if hh : 0 < h then
      (∫ D, diamond.poleCoefficient εPos ⟨h, hh⟩ D * gPos D) -
      (∫ D, diamond.poleCoefficient εNeg ⟨h, hh⟩ D * gNeg D) else 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (directed (complexShellPV (fun D => gPos D - gNeg D) -
        Complex.I * (Real.pi : ℂ) * (gPos 0 + gNeg 0)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.tested_pole_coefficient_jump εPos εNeg hPos hNeg hfPos hfNeg hsPos hsNeg)

end UV.SectorPlane
