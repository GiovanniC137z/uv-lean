import UV.SectorPlaneEuler
import UV.SectorPlaneScalarProduct

/-! Two equal positive-mass poles on the same prescribed side. Dilation
integration by parts in all four momenta gives their boundary value without
a choice of normal chart, using only the simple-pole distribution. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def Plane.squareMassShift (diamond : Plane E) (ε : Evolution) (m t : ℝ) : ℂ :=
  ((m^2 : ℝ) : ℂ) - Complex.I * ((diamond.eta ε*t : ℝ) : ℂ)

def squareEulerTest (f : MassiveMomentum → ℂ) (q : MassiveMomentum) : ℂ :=
  f q + momentumEuler f q / 2

theorem Plane.massive_square_parts (diamond : Plane E) (ε : Evolution) (h : Height) (m : ℝ)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    diamond.squareMassShift ε m h * (∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^2) =
      ∫ q, squareEulerTest f q * diamond.poleCoefficient ε h (massiveD m q) := by
  let Z (q : MassiveMomentum) := diamond.shiftedShellCoefficient ε h (massiveD m q)
  let P (q : MassiveMomentum) := (Z q)⁻¹
  have hNZ (q) : Z q ≠ 0 := diamond.shifted_denominator_ne_zero ε h _
  have hw : ContDiff ℝ 1 (fun q : MassiveMomentum => shellSquare q.1 q.2) :=
    (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  have hZ : ContDiff ℝ 1 Z := (Complex.ofRealCLM.contDiff.comp (hw.sub contDiff_const)).add contDiff_const
  have hP : ContDiff ℝ 1 P := hZ.inv hNZ
  have hPf : ContDiff ℝ 1 (fun q => f q * P q) := hf.mul hP
  have hsource : HasCompactSupport (fun q => f q * P q) := hs.mul_right
  have dP (q) : momentumEuler P q = -2 * (shellSquare q.1 q.2 : ℂ) * P q ^ 2 := by
    have hz := ((Complex.ofRealCLM.hasFDerivAt.comp q ((shell_square_hasFDerivAt q).sub_const (m^2))).add_const
      (Complex.I * ((diamond.eta ε*(h:ℝ):ℝ):ℂ)))
    have hd := ((hasFDerivAt_inv (hNZ q)).restrictScalars ℝ).comp q hz
    change fderiv ℝ ((fun z : ℂ => z⁻¹) ∘ Z) q q = _
    rw [hd.fderiv]
    simp [P,coneCovector_apply,real_inner_self_eq_norm_sq,shellSquare,inv_pow]
    ring
  have dF (q) : momentumEuler (fun p => f p * P p) q =
      momentumEuler f q * P q - 2 * (shellSquare q.1 q.2 : ℂ) * f q * P q ^ 2 := by
    have hprod := ((hf.differentiable le_rfl q).hasFDerivAt.mul ((hP.differentiable le_rfl q).hasFDerivAt)).fderiv
    change fderiv ℝ (f * P) q q = _
    rw [hprod]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    change _ * momentumEuler P q + _ * momentumEuler f q = _
    rw [dP]; ring
  have he (q) : diamond.squareMassShift ε m h * (f q * P q^2) - squareEulerTest f q * P q =
      -2*(f q*P q) - momentumEuler (fun p => f p*P p) q / 2 := by
    have hi : Z q * P q = 1 := mul_inv_cancel₀ (hNZ q)
    have hz : (shellSquare q.1 q.2 : ℂ) - diamond.squareMassShift ε m h = Z q := by
      simp only [Plane.squareMassShift,Z,Plane.shiftedShellCoefficient,massiveD,Complex.ofReal_sub]; ring
    rw [dF]
    unfold squareEulerTest
    have hrel : ((shellSquare q.1 q.2 : ℂ) - diamond.squareMassShift ε m h) * P q = 1 := by rwa [hz]
    linear_combination -(f q * P q) * hrel
  have hEc := momentum_euler_continuous hPf
  have hEs := momentum_euler_compact hsource
  have htc : Continuous (squareEulerTest f) := hf.continuous.add ((momentum_euler_continuous hf).div_const _)
  have hts : HasCompactSupport (squareEulerTest f) := by
    simpa only [squareEulerTest,div_eq_mul_inv] using hs.add ((momentum_euler_compact hs).mul_right (f' := fun _ => (2:ℂ)⁻¹))
  have hi := (hf.continuous.mul (hP.continuous.pow 2)).integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  have hj := (htc.mul hP.continuous).integrable_of_hasCompactSupport (μ := volume) hts.mul_right
  have hiF := hPf.continuous.integrable_of_hasCompactSupport (μ := volume) hsource
  have hiE := hEc.integrable_of_hasCompactSupport (μ := volume) hEs
  simp only [diamond.pole_coefficient_eq_inv]
  change _ * (∫ q, f q * P q^2) = ∫ q, squareEulerTest f q * P q
  rw [← sub_eq_zero,← integral_const_mul,← integral_sub (hi.const_mul _) hj]
  simp_rw [he]
  rw [integral_sub (hiF.const_mul _) (hiE.div_const _),integral_const_mul,integral_div,integral_momentum_euler hPf hsource]
  ring

/-- Full four-momentum limit of the same-side square at positive mass.
The test may cross either sheet and the axial hyperplane. -/
theorem Plane.massive_same_side_square_boundary (diamond : Plane E) (ε : Evolution) {m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^2)
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m (squareEulerTest f) / (m^2 : ℝ))) := by
  have ht : ContDiff ℝ 1 (squareEulerTest f) := (hf.of_le (by norm_num)).add ((momentum_euler_c1 hf).div_const _)
  have hts : HasCompactSupport (squareEulerTest f) := by
    simpa only [squareEulerTest,div_eq_mul_inv] using hs.add ((momentum_euler_compact hs).mul_right (f' := fun _ => (2:ℂ)⁻¹))
  have hc : Continuous (diamond.squareMassShift ε m) := by unfold Plane.squareMassShift; fun_prop
  have hcl : Tendsto (fun h : Height => diamond.squareMassShift ε m h) poleBoundaryHeights (𝓝 ((m^2:ℝ):ℂ)) := by
    have he : diamond.squareMassShift ε m 0 = ((m^2:ℝ):ℂ) := by simp [Plane.squareMassShift]
    rw [← he]; exact (hc.continuousAt (x := 0)).tendsto.comp pole_height_tendsto_zero
  have hn : ((m^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (sq_pos_of_pos hm).ne'
  apply ((diamond.bare_massive_complex_c1 ε hm ht hts).div hcl hn).congr
  intro h
  have hz : diamond.squareMassShift ε m h ≠ 0 := by
    intro hx
    have H := congrArg Complex.re hx
    simp only [Plane.squareMassShift,Complex.sub_re,Complex.ofReal_re,Complex.I_mul_re,Complex.ofReal_im,neg_zero,sub_zero,Complex.zero_re] at H
    exact (sq_pos_of_pos hm).ne' H
  apply (div_eq_iff hz).mpr
  dsimp only
  rw [← diamond.massive_square_parts ε h m (hf.of_le (by norm_num)) hs, mul_comm]

theorem Plane.massive_same_side_scalar_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {m : ℝ} (hm : 0 < m) (a₁ a₂ : ℝ)
    {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε ε h φ₁ φ₂ a₁ a₂ m m f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  apply diamond.smooth_two_line_distribution_of_bare ε ε K m m a₁ a₂ hφ₁ hφ₂
  intro f
  exact ⟨_, by simpa only [sq] using diamond.massive_same_side_square_boundary ε hm f.contDiff f.compact_support⟩

end UV.SectorPlane
