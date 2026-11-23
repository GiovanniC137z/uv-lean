import UV.ContinueNormalCircleModes
import UV.ContinueNormalZeroLoop
import UV.ContinueNormalPhotonEnvelope

/-! The zero winding is the holonomy average of the actual circle-mode
trace at fixed routed carrier momenta. The frequency remains continuous
after averaging, including when the carrier lies on a reciprocal lattice. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

/-- The periodic Dirac symbol, with the additional spacelike gamma-five
term, in the fixed Euclidean chart. -/
def normalDiracSymbol (m : ℝ) (p : OSFourSpace) (ξ : ℝ) : DiracMatrix :=
  (m:ℂ) • 1 + Complex.I • normalFiveSlash p ξ

theorem normal_dirac_two_sided_inverse {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    normalDiracSymbol m p ξ * normalDiracFrequency m p ξ = 1 ∧
    normalDiracFrequency m p ξ * normalDiracSymbol m p ξ = 1 := by
  let A := normalFiveSlash p ξ
  let P := (m:ℂ) • (1:DiracMatrix) + Complex.I • A
  let N := (m:ℂ) • (1:DiracMatrix) + (-Complex.I) • A
  let d := ((normalFiveDenom m p ξ:ℝ):ℂ)
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold normalFiveDenom; positivity)
  have hN : freeDiracNumerator m p + (-Complex.I*(ξ:ℂ)) • normalCoverGamma5 = N := by
    simp only [N,A,normalFiveSlash,freeDiracNumerator,smul_add,smul_smul]; abel
  have hpn : P*N = d • (1:DiracMatrix) ∧ N*P = d • (1:DiracMatrix) := by
    constructor <;>
      simp only [P,N,A,d,add_mul,mul_add,smul_mul_smul,one_mul,mul_one,mul_neg,neg_mul,
        Complex.I_mul_I,neg_neg,normal_five_slash_square,smul_smul,normalFiveDenom,Complex.ofReal_add,Complex.ofReal_pow] <;> module
  change P*(d⁻¹ • _) = 1 ∧ (d⁻¹ • _)*P = 1
  rw [hN,mul_smul_comm,smul_mul_assoc,hpn.1,hpn.2,smul_smul,inv_mul_cancel₀ hd,one_smul]
  exact ⟨rfl,rfl⟩

theorem SectorPlane.Plane.normal_circle_mode_inverse {E : Type*} [Norm E] (diamond : Plane E)
    {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) (n : ℤ) :
    let k := diamond.osOrientedChart p
    let ξ := (2*Real.pi*(n:ℝ)+θ)/L
    let G := L • (∫ t in Ioc (0:ℝ) 1, normalAngularPhase (2*Real.pi*(n:ℝ)) t • normalCircleKernel m L θ k t)
    normalDiracSymbol m k ξ * G = 1 ∧ G * normalDiracSymbol m k ξ = 1 := by
  dsimp only
  rw [normal_circle_fourier_mode hm hL]
  exact normal_dirac_two_sided_inverse hm _ _

theorem normal_fixed_carrier_weight {m : ℝ} (hm : 0 < m) {r : ℕ} (hr : 1 < r) (p : OSFourSpace) :
    Integrable (fun ξ : ℝ => normalLoopWeight m (p,ξ)^r) := by
  let b := min m 1
  have hb : 0 < b := lt_min hm zero_lt_one
  have hi := (normal_photon_weight_integrable volume (E := ℝ) (by rwa [Module.finrank_self] : Module.finrank ℝ ℝ < r)).const_mul ((2/b)^r)
  apply hi.mono' (Measurable.aestronglyMeasurable (by dsimp [normalLoopWeight,normalFiveDenom]; fun_prop))
  refine Eventually.of_forall fun ξ => ?_
  let d := Real.sqrt (normalFiveDenom m p ξ)
  have hD : 0 < normalFiveDenom m p ξ := by dsimp [normalFiveDenom]; positivity
  have hd : 0 < d := Real.sqrt_pos.mpr hD
  have hsq : d^2=m^2+‖p‖^2+ξ^2 := Real.sq_sqrt hD.le
  have h1 : b ≤ d := (min_le_left _ _).trans (by nlinarith [sq_nonneg ‖p‖,sq_nonneg ξ])
  have h2 : |ξ| ≤ d := by nlinarith [sq_nonneg ‖p‖,sq_nonneg m,sq_abs ξ,abs_nonneg ξ]
  have hrel : b*(1+|ξ|) ≤ 2*d := by nlinarith [mul_le_mul_of_nonneg_right (min_le_right m 1) (abs_nonneg ξ)]
  have he : d⁻¹ ≤ (2/b)*(1+|ξ|)⁻¹ := by
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),le_div_iff₀ hb,inv_mul_eq_div,div_mul_eq_mul_div,div_le_iff₀ hd]
    linarith
  change ‖d⁻¹^r‖ ≤ (2/b)^r * normalPhotonWeight r ξ
  rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hd.le) _)]
  simpa only [normalPhotonWeight,Real.norm_eq_abs,mul_pow,inv_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hd.le) he r

def normalFrequencyTrace {r : ℕ} (m : ℝ) (u : Fin r → UnitVector OSFourSpace) (p : Fin r → OSFourSpace) (ξ : ℝ) : ℂ :=
  (List.ofFn (fun j => normalDiracFrequency m (p j) ξ * diracSlash (u j).val)).prod.trace

theorem normal_frequency_trace_integrable {r : ℕ} {m : ℝ} (hm : 0 < m) (hr : 1 < r)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin r → OSFourSpace) : Integrable (normalFrequencyTrace m u p) := by
  have hπ : (2:ℝ)*Real.pi ≠ 0 := by positivity
  have he : normalFrequencyTrace m u p = normalZeroTrace m (2*Real.pi) u p := by
    ext ξ; simp only [normalFrequencyTrace,normalZeroTrace,div_self hπ,Complex.ofReal_one,one_mul]
  rw [he]
  have hmF := normal_zero_trace_measurable m (2*Real.pi) u (p := fun _ : ℝ => p) (fun _ => measurable_const) measurable_id
  have hi := (integrable_finset_sum Finset.univ (fun j _ => normal_fixed_carrier_weight hm hr (p j))).const_mul
    (((2*Real.pi)/(2*Real.pi)*4)*(r:ℝ)⁻¹)
  apply hi.mono' hmF.aestronglyMeasurable
  refine Eventually.of_forall fun ξ => ?_
  simpa only [mul_assoc] using normal_zero_trace_bound hm (by positivity : 0 < 2*Real.pi) (by omega : 0 < r) u p ξ

/-- Averaging the compact circle trace in normalized holonomy picks the
zero winding. The physical frequency integral acquires exactly L/(2π). -/
theorem normal_zero_from_circle_trace {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (hr : 1 < r)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin r → OSFourSpace) :
    (∫ α in Ioc (0:ℝ) 1, ∑' j : ℤ, normalFrequencyTrace m u p ((2*Real.pi*(j:ℝ)+2*Real.pi*α)/L)) =
      ∫ ξ, normalZeroTrace m L u p ξ := by
  let a := (2*Real.pi)/L
  have ha : 0 < a := by dsimp [a]; positivity
  have hf := (normal_frequency_trace_integrable hm hr u p).comp_mul_left' ha.ne'
  have he (α : ℝ) (j : ℤ) : (2*Real.pi*(j:ℝ)+2*Real.pi*α)/L = a*(α+(j:ℝ)) := by dsimp [a]; ring
  simp_rw [he]
  rw [normal_cell_integral_tsum hf,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr ha)]
  simp only [normalZeroTrace,normalFrequencyTrace,integral_const_mul,Complex.real_smul,a,inv_div]

end UV
