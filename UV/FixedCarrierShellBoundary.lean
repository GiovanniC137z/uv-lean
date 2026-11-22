import UV.ScalarLineSide
import UV.AdvanceConeAngularSmooth

/-! Fixed virtual-carrier benchmark of `eq:carrier-pv-delta` on actual
four-momentum tests. The Poisson and conjugate Poisson regularizations use
one positive height. Both axial sheets contribute to the shell delta. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

/-- PV in the vectorial prescription, defined from the real conjugate Poisson
kernel. The limit is proved below, also at the vertex of the massless cone. -/
def regularizedShellPV (m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  limUnder poleBoundaryHeights (fun h : Height => ∫ q, polePV h (massiveD m q) * f q)

variable {E : Type*} [NormedAddCommGroup E]

private theorem Plane.bare_shell_real_part (diamond : Plane E) (ε : Evolution) (h : Height) (m : ℝ)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q, (f q : ℂ) * diamond.poleCoefficient ε h (massiveD m q)).re = ∫ q, polePV h (massiveD m q) * f q := by
  have hc := Complex.continuous_ofReal.comp hf
  have hsc := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi : Integrable (fun q => (f q : ℂ) * diamond.poleCoefficient ε h (massiveD m q)) := (hc.mul ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m))).integrable_of_hasCompactSupport
    (μ := volume) hsc.mul_right
  rw [← RCLike.re_eq_complex_re, ← integral_re hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by simp [diamond.pole_coefficient_split, mul_comm]

/-- The PV at the tip also has the explicit subtracted angular formula. In particular
it is determined by the compact Cartesian test and is independent of the pole side. -/
theorem Plane.massless_shell_pv_angular (diamond : Plane E) (ε : Evolution)
    {f : MassiveMomentum → ℝ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ R > (0 : ℝ), let Z := (2 * Real.pi ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
        coneAngularSingleBoundary (diamond.eta ε) (coneAngularAmplitude (fun q => (f q : ℂ)) r)
      Tendsto (fun h : Height => ∫ q, polePV h (massiveD 0 q) * f q) poleBoundaryHeights (𝓝 Z.re) ∧
        regularizedShellPV 0 f = Z.re := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have hc : ContDiff ℝ 2 (fun q => (f q : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsc := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  obtain ⟨R, hR, hoff⟩ := cone_radial_cutoff_of_compact hsc
  obtain ⟨C, hC, hjet⟩ := cone_smooth_single_normal_jet hc R
  have H := diamond.cone_nonradial_single_limit ε hc.continuous hsc hR hoff hC hjet
  have h := Complex.continuous_re.continuousAt.tendsto.comp H
  have h' := h.congr (f₂ := fun h : Height => ∫ q, polePV h (massiveD 0 q) * f q) fun h => by
    simpa only [Function.comp_apply, massiveD, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
      diamond.bare_shell_real_part ε h 0 hf.continuous hs
  exact ⟨R, hR, h', h'.limUnder_eq⟩

theorem massive_regularized_shell_pv {m b : ℝ} (hb : 0 < b) (hbm : 2*b ≤ m^2)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    regularizedShellPV m f = massiveShellPV b m f := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  exact ((pole_pv_full_massive_shell_limit hb hbm hf hs).comp (tendsto_comap (f := (fun h : Height => (h:ℝ))))).limUnder_eq

/-- Both signs in the fixed-carrier boundary act on the same four-dimensional
test. The scalar coefficient is reconstructed in the original quotient. -/
theorem Plane.fixed_carrier_shell_limit (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 ≤ m)
    {f : MassiveMomentum → ℝ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, directed (f q : ℂ) *
      (directed (Complex.I * (evolutionSign ε : ℂ)) * diamond.poleInverse ε h (massiveD m q)))
      poleBoundaryHeights (𝓝 (directed (((sectorSign diamond.s * (Real.pi * fullShellTest m f) : ℝ) : ℂ) +
        Complex.I * ((evolutionSign ε * regularizedShellPV m f : ℝ) : ℂ)))) := by
  have hPV : Tendsto (fun h : Height => ∫ q, polePV h (massiveD m q) * f q) poleBoundaryHeights (𝓝 (regularizedShellPV m f)) := by
    rcases hm.eq_or_lt with h | h
    · subst m
      obtain ⟨_, _, h, he⟩ := diamond.massless_shell_pv_angular ε hf hs
      rwa [he]
    · obtain ⟨_, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by norm_num)
      have hb : 0 < m^2/4 := by positivity
      have hbm : 2*(m^2/4) ≤ m^2 := by linarith [sq_nonneg m]
      rw [massive_regularized_shell_pv hb hbm hL hs]
      exact (pole_pv_full_massive_shell_limit hb hbm hL hs).comp tendsto_comap
  have hδ := (pole_poisson_full_shell_limit m hf.continuous hs).comp (tendsto_comap (f := fun h : Height => (h:ℝ)))
  have H := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hδ.const_mul (sectorSign diamond.s))).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hPV.const_mul (evolutionSign ε))).const_mul Complex.I)
  apply (directed_shell_readout_continuous.continuousAt.tendsto.comp H).congr
  intro h
  let d := massiveD m
  have hpv : Continuous (polePV (h:ℝ)) := continuous_iff_continuousAt.mpr (fun D => (polePV_hasDerivAt h.property D).continuousAt)
  have hpc : Continuous (polePoisson (h:ℝ)) := continuous_iff_continuousAt.mpr (fun D => (polePoisson_hasDerivAt h.property D).continuousAt)
  let F (q : MassiveMomentum) := sectorSign diamond.s * (polePoisson h (d q) * f q)
  let G (q : MassiveMomentum) := evolutionSign ε * (polePV h (d q) * f q)
  have hF : Integrable F := (((hpc.comp (massiveD_continuous m)).mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left).const_mul _
  have hG : Integrable G := (((hpv.comp (massiveD_continuous m)).mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left).const_mul _
  change directed (((sectorSign diamond.s * ∫ q, polePoisson h (d q) * f q : ℝ) : ℂ) + Complex.I *
    ((evolutionSign ε * ∫ q, polePV h (d q) * f q : ℝ) : ℂ)) = _
  rw [← integral_const_mul, ← integral_const_mul]
  change directed (((∫ q, F q : ℝ) : ℂ) + Complex.I * ((∫ q, G q : ℝ) : ℂ)) = _
  have hi : Integrable (fun q => (F q : ℂ) + Complex.I * (G q : ℂ)) := hF.ofReal.add (hG.ofReal.const_mul _)
  rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
    ← integral_add hF.ofReal (hG.ofReal.const_mul _), ← directed_integral hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [diamond.fixed_pole_components, ← directed_mul]
    congr 1
    simp only [F, G, polePoisson, polePV, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow]
    ring

end UV.SectorPlane
