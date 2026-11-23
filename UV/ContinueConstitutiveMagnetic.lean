import UV.NextOpticalBandGeometry
import UV.ContinuationVectorialPole
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The normal Dirichlet energy of the three independent magnetic curvature
components on a locked copy, and the resulting free transverse oscillator. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace UV
open SectorPlane NextOpticalRadial Carrier

/-- The three independent Fourier curvature components are (01), (02), (12)
in zero-based spatial indexing. The common factor i drops out of their energy. -/
def normalMagneticSquare (p A : Spatial) : ℝ :=
  (p 0 * A 1 - p 1 * A 0)^2 + (p 0 * A 2 - p 2 * A 0)^2 + (p 1 * A 2 - p 2 * A 1)^2

theorem normalMagneticSquare_gram (p A : Spatial) :
    normalMagneticSquare p A = ‖p‖^2 * ‖A‖^2 - ⟪p,A⟫^2 := by
  simp [normalMagneticSquare, EuclideanSpace.norm_sq_eq, PiLp.inner_apply,
    Fin.sum_univ_three, Real.norm_eq_abs, RCLike.inner_apply]
  ring

theorem normalMagneticSquare_transverse (n : UnitVector Spatial) (k : ℝ) (A : Spatial) :
    normalMagneticSquare (k • n.val) A = k^2 * ‖transverseMomentum n A‖^2 := by
  rw [normalMagneticSquare_gram, transverseMomentum_sq, norm_smul, n.property, mul_one,
    Real.norm_eq_abs, sq_abs, real_inner_smul_left, real_inner_comm n.val A]
  ring

def constitutiveExtension (k : ℝ) (z : ℂ) (y : ℝ) : ℂ := (Real.exp (-k*y) : ℂ) * z

@[simp] theorem constitutiveExtension_trace (k : ℝ) (z : ℂ) : constitutiveExtension k z 0 = z := by
  simp [constitutiveExtension]

theorem constitutiveExtension_sew (k a b : ℝ) (z : ℂ) :
    constitutiveExtension k (constitutiveExtension k z a) b = constitutiveExtension k z (a+b) := by
  unfold constitutiveExtension
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  ring

theorem constitutiveExtension_derivative (k : ℝ) (z : ℂ) (y : ℝ) :
    HasDerivAt (constitutiveExtension k z) ((-k : ℂ) * constitutiveExtension k z y) y := by
  have he := ((hasDerivAt_id y).const_mul (-k)).exp
  have hc := he.ofReal_comp.mul_const z
  convert hc using 1
  simp [constitutiveExtension]
  ring

/-- Exact half-line energy for a complex Fourier component, including both
real quadratures. -/
theorem constitutiveExtension_energy {k : ℝ} (hk : 0 < k) (z : ℂ) :
    (∫ y in Ioi 0, ‖deriv (constitutiveExtension k z) y‖^2 +
      k^2 * ‖constitutiveExtension k z y‖^2) = k * ‖z‖^2 := by
  have he (y : ℝ) : ‖deriv (constitutiveExtension k z) y‖^2 +
      k^2 * ‖constitutiveExtension k z y‖^2 = (2*k^2*‖z‖^2)*Real.exp ((-(2*k))*y) := by
    rw [(constitutiveExtension_derivative k z y).deriv]
    simp only [constitutiveExtension, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hk.le, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
    rw [show (2:ℕ) * (-k * y) = -(2*k)*y by push_cast; ring]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(2*k) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

def constitutiveFrequencySq (L k : ℝ) : ℝ := k^2 + L * k^3

theorem constitutiveMagnetic_action (L k ν : ℝ) (n : UnitVector Spatial) (A : Spatial)
    (hA : ⟪A,n.val⟫ = 0) :
    (ν^2 + k^2) * ‖A‖^2 / 2 + L / 2 * k * normalMagneticSquare (k • n.val) A =
      (ν^2 + constitutiveFrequencySq L k) * ‖A‖^2 / 2 := by
  rw [normalMagneticSquare_transverse, transverseMomentum_sq, hA]
  unfold constitutiveFrequencySq
  ring

/-- The real and imaginary spatial amplitudes give the magnetic energy of
a complex transverse polarization on the harmonic graph. -/
theorem constitutiveMagnetic_complex_action {k : ℝ} (hk : 0 < k) (L ν : ℝ) (n : UnitVector Spatial)
    (A B : Spatial) (hA : ⟪A,n.val⟫ = 0) (hB : ⟪B,n.val⟫ = 0) :
    let p := k • n.val
    let F := fun i j : Fin 3 => (p i * A j - p j * A i : ℝ) +
      (Complex.I : ℂ) * (p i * B j - p j * B i : ℝ)
    let energy := fun z : ℂ => ∫ y in Ioi 0, ‖deriv (constitutiveExtension k z) y‖^2 +
      k^2 * ‖constitutiveExtension k z y‖^2
    (ν^2+k^2)*(‖A‖^2+‖B‖^2)/2 + L/2*(energy (F 0 1) + energy (F 0 2) + energy (F 1 2)) =
      (ν^2+constitutiveFrequencySq L k)*(‖A‖^2+‖B‖^2)/2 := by
  intro p F energy
  have he (z : ℂ) : energy z = k*‖z‖^2 := constitutiveExtension_energy hk z
  have hnorm (i j : Fin 3) : ‖F i j‖^2 =
      (p i*A j-p j*A i)^2 + (p i*B j-p j*B i)^2 := by
    simp [F, Complex.sq_norm, Complex.normSq_apply, Complex.mul_im, Complex.mul_re]
    ring
  have ha := constitutiveMagnetic_action L k ν n A hA
  have hb := constitutiveMagnetic_action L k ν n B hB
  change _ + L/2*k*normalMagneticSquare p A = _ at ha
  change _ + L/2*k*normalMagneticSquare p B = _ at hb
  simp only [he, hnorm]
  unfold normalMagneticSquare at ha hb
  linarith only [ha, hb]

/-- Covariance on an arbitrary source in the three spatial coordinates.
The projector is computed from the actual unit direction of the mode. -/
def constitutiveCovariance (n : UnitVector Spatial) (L k ν : ℝ) (J : Spatial) : Spatial :=
  (ν^2 + constitutiveFrequencySq L k)⁻¹ • transverseMomentum n J

theorem constitutiveCovariance_inverse (n : UnitVector Spatial) {L k : ℝ} (hL : 0 ≤ L)
    (hk : 0 < k) (ν : ℝ) (J : Spatial) :
    (ν^2 + constitutiveFrequencySq L k) • constitutiveCovariance n L k ν J = transverseMomentum n J ∧
      ⟪constitutiveCovariance n L k ν J, n.val⟫ = 0 := by
  have hden : 0 < ν^2 + constitutiveFrequencySq L k := by unfold constitutiveFrequencySq; positivity
  constructor
  · rw [constitutiveCovariance, smul_smul, mul_inv_cancel₀ hden.ne', one_smul]
  · simp [constitutiveCovariance, transverseMomentum, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, n.property]

theorem constitutiveFrequency_ir (L : ℝ) :
    Tendsto (fun k : ℝ => constitutiveFrequencySq L k / k^2) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun k : ℝ => 1 + L*k) (𝓝[>] 0) (𝓝 (1+L*0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul nhdsWithin_le_nhds)
  apply (show Tendsto (fun k : ℝ => 1 + L*k) (𝓝[>] 0) (𝓝 1) by simpa using h).congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with k hk
  have hn : k ≠ 0 := (show 0 < k from hk).ne'
  unfold constitutiveFrequencySq
  field_simp

/-- The full continuous Euclidean frequency integral, for the ordinary
Maxwell law at L=0 and for every nonnegative magnetic coefficient. -/
theorem constitutive_frequency_integral {L k : ℝ} (hL : 0 ≤ L) (hk : 0 < k) :
    Integrable (fun ν : ℝ => (ν^2 + constitutiveFrequencySq L k)⁻¹) ∧
    (∫ ν : ℝ, (ν^2 + constitutiveFrequencySq L k)⁻¹) = Real.pi / Real.sqrt (constitutiveFrequencySq L k) ∧
    (∫ ν : ℝ, (ν^2 + constitutiveFrequencySq L k)⁻¹) ≤ Real.pi / k := by
  let b := Real.sqrt (constitutiveFrequencySq L k)
  have hb2 : 0 < constitutiveFrequencySq L k := by unfold constitutiveFrequencySq; positivity
  have hb : 0 < b := Real.sqrt_pos.mpr hb2
  have hs : b^2 = constitutiveFrequencySq L k := Real.sq_sqrt hb2.le
  let F := fun ν : ℝ => (1+ν^2)⁻¹
  have he (ν : ℝ) : (ν^2 + constitutiveFrequencySq L k)⁻¹ = (b^2)⁻¹ * F (b⁻¹*ν) := by
    rw [← hs]
    dsimp [F]
    field_simp [hb.ne']
    ring
  have hi := (integrable_comp_mul_left_iff F (inv_ne_zero hb.ne')).2 integrable_inv_one_add_sq
  have hev : (∫ ν : ℝ, (ν^2 + constitutiveFrequencySq L k)⁻¹) = Real.pi/b := by
    have scale : (∫ ν : ℝ, F (b⁻¹*ν)) = b * Real.pi := by
      simpa only [inv_inv, abs_of_pos hb, smul_eq_mul, F, integral_univ_inv_one_add_sq] using
        Measure.integral_comp_mul_left F b⁻¹
    simp only [he, integral_const_mul, scale]
    field_simp
  refine ⟨(hi.const_mul _).congr (Eventually.of_forall fun ν => (he ν).symm), hev, ?_⟩
  rw [hev]
  apply div_le_div_of_nonneg_left Real.pi_pos.le hk
  apply (Real.le_sqrt hk.le hb2.le).mpr
  exact le_add_of_nonneg_right (mul_nonneg hL (pow_nonneg hk.le _))

/-- If the free oscillator is continued with the framework's vectorial
prescription, the scalar invariant in the quotient is ω² minus the actual
constitutive squared frequency. -/
theorem SectorPlane.Plane.constitutive_vectorial_pole {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) (h : Height) (L k ω : ℝ) :
    diamond.poleDenominator ε h (ω^2 - constitutiveFrequencySq L k) =
      algebraMap ℂ QuotientCarrier ((ω^2 - constitutiveFrequencySq L k : ℝ) : ℂ) +
        algebraMap ℂ QuotientCarrier (Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)) * poleRoot :=
  diamond.pole_denominator_literal ε h _

end UV
