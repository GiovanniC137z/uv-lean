import UV.FixedCarrierShellBoundary
import UV.SectorPlaneGaugeMultiplier

/-! Products with the same routed four-momentum on one locked sector plane.
For distinct mass shells the common-height resolvent identity isolates each
simple pole. For coincident shells the branch choices matter. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- The fixed-denominator coefficient on a real four-momentum test. -/
def bareShellBoundary (η m : ℝ) (f : MassiveMomentum → ℝ) : ℂ :=
  (regularizedShellPV m f : ℂ) - Complex.I * (η * (Real.pi * fullShellTest m f) : ℝ)

def bareComplexShellBoundary (η m : ℝ) (f : MassiveMomentum → ℂ) : ℂ :=
  bareShellBoundary η m (fun q => (f q).re) + Complex.I * bareShellBoundary η m (fun q => (f q).im)

theorem Plane.bare_real_shell_boundary (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 ≤ m)
    {f : MassiveMomentum → ℝ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, (f q : ℂ) * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareShellBoundary (diamond.eta ε) m f)) := by
  have hPV : Tendsto (fun h : Height => ∫ q, polePV h (massiveD m q) * f q) poleBoundaryHeights
      (𝓝 (regularizedShellPV m f)) := by
    rcases hm.eq_or_lt with h | h
    · subst m
      obtain ⟨_, _, h, eq⟩ := diamond.massless_shell_pv_angular ε hf hs
      rwa [eq]
    · obtain ⟨_, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by norm_num)
      have hbm : 2*(m^2/4) ≤ m^2 := by nlinarith [sq_nonneg m]
      have hb : 0 < m^2/4 := by positivity
      rw [massive_regularized_shell_pv hb hbm hL hs]
      exact (pole_pv_full_massive_shell_limit hb hbm hL hs).comp tendsto_comap
  have hδ := (pole_poisson_full_shell_limit m hf.continuous hs).comp (tendsto_comap (f := fun h : Height => (h:ℝ)))
  apply ((Complex.continuous_ofReal.continuousAt.tendsto.comp hPV).sub
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hδ.const_mul (diamond.eta ε))).const_mul Complex.I)).congr
  intro h
  let P q := polePV h (massiveD m q) * f q
  let D q := polePoisson h (massiveD m q) * f q
  have hp : Continuous (polePV (h:ℝ)) := continuous_iff_continuousAt.mpr (fun x => (polePV_hasDerivAt h.property x).continuousAt)
  have hd : Continuous (polePoisson (h:ℝ)) := continuous_iff_continuousAt.mpr (fun x => (polePoisson_hasDerivAt h.property x).continuousAt)
  have hP : Integrable P := ((hp.comp (massiveD_continuous m)).mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left
  have hD : Integrable D := ((hd.comp (massiveD_continuous m)).mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left
  change ((∫ q, P q : ℝ) : ℂ) - Complex.I * ((diamond.eta ε * ∫ q, D q : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, ← mul_assoc, ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
    ← integral_sub hP.ofReal (hD.ofReal.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    simp only [P, D, diamond.pole_coefficient_split, Complex.ofReal_mul]; ring

theorem Plane.bare_complex_shell_boundary_of_parts (diamond : Plane E) (ε : Evolution) (m : ℝ)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hr : Tendsto (fun h : Height => ∫ q, ((f q).re : ℂ) * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareShellBoundary (diamond.eta ε) m (fun q => (f q).re))))
    (hi : Tendsto (fun h : Height => ∫ q, ((f q).im : ℂ) * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareShellBoundary (diamond.eta ε) m (fun q => (f q).im)))) :
    Tendsto (fun h : Height => ∫ q, f q * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m f)) := by
  apply (hr.add (hi.const_mul Complex.I)).congr
  intro h
  let P q := diamond.poleCoefficient ε h (massiveD m q)
  have hP : Continuous P := (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hint (p : ℂ → ℝ) (hp : Continuous p) (hz : p 0 = 0) :
      Integrable (fun q => (p (f q) : ℂ) * P q) :=
    ((Complex.continuous_ofReal.comp (hp.comp hf)).mul hP).integrable_of_hasCompactSupport
      ((hs.comp_left hz).comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right
  change (∫ q, ((f q).re : ℂ) * P q) + Complex.I * (∫ q, ((f q).im : ℂ) * P q) = _
  rw [← integral_const_mul, ← integral_add (hint _ Complex.continuous_re Complex.zero_re)
    ((hint _ Complex.continuous_im Complex.zero_im).const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    calc
      _ = ((f q).re + (f q).im * Complex.I) * P q := by ring
      _ = _ := by rw [Complex.re_add_im]

theorem Plane.bare_complex_shell_boundary (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 ≤ m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m f)) := by
  exact diamond.bare_complex_shell_boundary_of_parts ε m hf.continuous hs
    (diamond.bare_real_shell_boundary ε hm (Complex.reCLM.contDiff.comp hf) (hs.comp_left Complex.zero_re))
    (diamond.bare_real_shell_boundary ε hm (Complex.imCLM.contDiff.comp hf) (hs.comp_left Complex.zero_im))

theorem Plane.bare_massive_complex_c1 (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m f)) := by
  have H {g : MassiveMomentum → ℝ} (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g) :
      Tendsto (fun h : Height => ∫ q, (g q : ℂ) * diamond.poleCoefficient ε h (massiveD m q))
        poleBoundaryHeights (𝓝 (bareShellBoundary (diamond.eta ε) m g)) := by
    obtain ⟨_,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgs hg le_rfl
    have hb : 0 < m^2/4 := by positivity
    have hbm : 2*(m^2/4) ≤ m^2 := by nlinarith [sq_nonneg m]
    have hh := (diamond.bare_massive_pairing_limit ε hb hbm hL hgs).comp
      (tendsto_comap (f := fun h : Height => (h:ℝ)))
    rw [bareShellBoundary,massive_regularized_shell_pv hb hbm hL hgs,Complex.ofReal_mul,← mul_assoc]
    exact hh.congr (fun h => by simp only [Function.comp_apply,Plane.bareMassivePairing,dif_pos h.property]; simp [mul_comm])
  exact diamond.bare_complex_shell_boundary_of_parts ε m hf.continuous hs
    (H (Complex.reCLM.contDiff.comp hf) (hs.comp_left Complex.zero_re))
    (H (Complex.imCLM.contDiff.comp hf) (hs.comp_left Complex.zero_im))

/-- Difference of the two denominators. The two positive heights are the
same number, even when the evolution orders select opposite sides. -/
def Plane.poleSeparation (diamond : Plane E) (ε₁ ε₂ : Evolution) (m₁ m₂ h : ℝ) : ℂ :=
  ((m₁^2-m₂^2 : ℝ) : ℂ) + Complex.I * (((diamond.eta ε₂ - diamond.eta ε₁) * h : ℝ) : ℂ)

theorem Plane.pole_product_difference (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height) (w m₁ m₂ : ℝ) :
    diamond.poleSeparation ε₁ ε₂ m₁ m₂ h * (diamond.poleCoefficient ε₁ h (w-m₁^2) *
        diamond.poleCoefficient ε₂ h (w-m₂^2)) =
      diamond.poleCoefficient ε₁ h (w-m₁^2) - diamond.poleCoefficient ε₂ h (w-m₂^2) := by
  let Z₁ := diamond.shiftedShellCoefficient ε₁ h (w-m₁^2)
  let Z₂ := diamond.shiftedShellCoefficient ε₂ h (w-m₂^2)
  have h₁ : Z₁ ≠ 0 := diamond.shifted_denominator_ne_zero ε₁ h _
  have h₂ : Z₂ ≠ 0 := diamond.shifted_denominator_ne_zero ε₂ h _
  have hz : diamond.poleSeparation ε₁ ε₂ m₁ m₂ h = Z₂-Z₁ := by
    simp only [Plane.poleSeparation,Z₁,Z₂,Plane.shiftedShellCoefficient,Complex.ofReal_sub,Complex.ofReal_mul]; ring
  simp only [diamond.pole_coefficient_eq_inv]
  change _ * (Z₁⁻¹ * Z₂⁻¹) = Z₁⁻¹ - Z₂⁻¹
  rw [hz]; field_simp

/-- A moving numerator can be partially fractioned at the common positive
height once its two individual simple-pole pairings have limits. -/
theorem Plane.weighted_pole_product_limit (diamond : Plane E) (ε₁ ε₂ : Evolution) {m₁ m₂ : ℝ}
    (hne : m₁^2 ≠ m₂^2) (G : Height → MassiveMomentum → ℂ) {z₁ z₂ : ℂ}
    (hI : ∀ h ε m, Integrable (fun q => G h q * diamond.poleCoefficient ε h (massiveD m q)))
    (h₁ : Tendsto (fun h => ∫ q, G h q * diamond.poleCoefficient ε₁ h (massiveD m₁ q)) poleBoundaryHeights (𝓝 z₁))
    (h₂ : Tendsto (fun h => ∫ q, G h q * diamond.poleCoefficient ε₂ h (massiveD m₂ q)) poleBoundaryHeights (𝓝 z₂)) :
    Tendsto (fun h : Height => ∫ q, G h q * (diamond.poleCoefficient ε₁ h (massiveD m₁ q) *
      diamond.poleCoefficient ε₂ h (massiveD m₂ q))) poleBoundaryHeights (𝓝 ((z₁-z₂) / ((m₁^2-m₂^2 : ℝ) : ℂ))) := by
  have hz : ((m₁^2-m₂^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  have hc : Continuous (diamond.poleSeparation ε₁ ε₂ m₁ m₂) := by unfold Plane.poleSeparation; fun_prop
  have hh := hc.continuousAt.tendsto.comp pole_height_tendsto_zero
  have hlim := (h₁.sub h₂).div (by simpa [Plane.poleSeparation] using hh) hz
  apply hlim.congr
  intro h
  let P (ε : Evolution) (m : ℝ) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hn : diamond.poleSeparation ε₁ ε₂ m₁ m₂ h ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Plane.poleSeparation, Complex.add_re, Complex.I_mul_re, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.zero_re] at he'
    exact hne (sub_eq_zero.mp he')
  change ((∫ q, G h q * P ε₁ m₁ q) - (∫ q, G h q * P ε₂ m₂ q)) / diamond.poleSeparation ε₁ ε₂ m₁ m₂ h = _
  rw [← integral_sub (hI h _ _) (hI h _ _), ← integral_div]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => (div_eq_iff hn).mpr ?_
  have he := diamond.pole_product_difference ε₁ ε₂ h (shellSquare q.1 q.2) m₁ m₂
  change G h q * P ε₁ m₁ q - G h q * P ε₂ m₂ q = G h q * (P ε₁ m₁ q * P ε₂ m₂ q) * _
  change diamond.poleSeparation ε₁ ε₂ m₁ m₂ h * (P ε₁ m₁ q * P ε₂ m₂ q) = P ε₁ m₁ q - P ε₂ m₂ q at he
  linear_combination (G h q) * he.symm

/-- Distributional partial fractions at a common height, including a zero
mass on either line and any choice of the two prescribed sides. -/
theorem Plane.distinct_shell_product_limit (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m₁ m₂ : ℝ} (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (hne : m₁^2 ≠ m₂^2)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * (diamond.poleCoefficient ε₁ h (massiveD m₁ q) *
      diamond.poleCoefficient ε₂ h (massiveD m₂ q))) poleBoundaryHeights
      (𝓝 ((bareComplexShellBoundary (diamond.eta ε₁) m₁ f -
           bareComplexShellBoundary (diamond.eta ε₂) m₂ f) / ((m₁^2-m₂^2 : ℝ) : ℂ))) := by
  exact diamond.weighted_pole_product_limit ε₁ ε₂ hne (fun _ q => f q)
    (fun h ε m => (hf.continuous.mul ((diamond.pole_coefficient_continuous ε h).comp
      (massiveD_continuous m))).integrable_of_hasCompactSupport hs.mul_right)
    (diamond.bare_complex_shell_boundary ε₁ h₁ hf hs) (diamond.bare_complex_shell_boundary ε₂ h₂ hf hs)

end UV.SectorPlane
