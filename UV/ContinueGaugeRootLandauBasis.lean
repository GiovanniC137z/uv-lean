import UV.ContinueGaugeRootWeight
import UV.ContinueGaugeRootHermiteBasis
import UV.ContinueGaugeRootLandau

/-! Completeness and normalization of the actual Hermite–Gaussian
modes of a Landau fibre on the spatial line. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal NNReal
namespace UV.RootMagnetic

def rootLandauEnvelope (b x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (2*b) / Real.sqrt (2*Real.pi)) * Real.exp (-b*x^2/2)

theorem root_landau_envelope_pos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 < rootLandauEnvelope b x := by
  unfold rootLandauEnvelope
  positivity

private theorem landauEnvelope_square {b : ℝ} (hb : 0 < b) (x : ℝ) :
    rootLandauEnvelope b x ^ 2 = Real.sqrt (2*b) * gaussianPDFReal 0 1 (Real.sqrt (2*b)*x) := by
  have h : 0 < Real.sqrt (2*b) := by positivity
  unfold rootLandauEnvelope gaussianPDFReal
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  simp only [NNReal.coe_one, mul_one, sub_zero, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*b)]
  ring_nf

private theorem landau_scale_preserves {b : ℝ} (hb : 0 < b) :
    MeasurePreserving (fun x : ℝ => Real.sqrt (2*b)*x)
      (squaredWeightLaw (rootLandauEnvelope b)) openingGaussianLaw := by
  let c := Real.sqrt (2*b)
  have hc : 0 < c := by dsimp [c]; positivity
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm : openingGaussianLaw.map e.symm = squaredWeightLaw (rootLandauEnvelope b) := by
    ext s hs
    have hder (x : ℝ) : HasDerivAt e c x := by
      simpa [e] using (hasDerivAt_id x).const_mul c
    rw [e.gaussianReal_map_symm_apply (by norm_num : (1:ℝ≥0) ≠ 0) hder hs,
      squaredWeightLaw, withDensity_apply _ hs]
    have hfun (x : ℝ) : |c| * gaussianPDFReal 0 1 (e x) = rootLandauEnvelope b x ^ 2 := by
      rw [abs_of_pos hc, landauEnvelope_square hb]
      rfl
    simp_rw [hfun]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · have hi : Integrable (fun x => c * gaussianPDFReal 0 1 (c*x)) := by
        exact ((integrable_comp_mul_left_iff (gaussianPDFReal 0 1) hc.ne').2 (integrable_gaussianPDFReal 0 1)).const_mul c
      simpa only [landauEnvelope_square hb] using hi.restrict (s := s)
    · exact Eventually.of_forall fun x => sq_nonneg _
  exact MeasurePreserving.symm e.symm ⟨e.symm.measurable, hm⟩

theorem root_landau_fiber_unitary {b : ℝ} (hb : 0 < b) :
    ∃ U : OpeningGaussianCarrier ≃ₗᵢ[ℂ] LebesgueFiber, ∀ f,
      ⇑(U f) =ᵐ[volume] fun x => (rootLandauEnvelope b x : ℂ) * f (Real.sqrt (2*b)*x) := by
  let c := Real.sqrt (2*b)
  have hc : 0 < c := by dsimp [c]; positivity
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ c hc.ne'
  have he : MeasurePreserving e (squaredWeightLaw (rootLandauEnvelope b)) openingGaussianLaw :=
    landau_scale_preserves hb
  let C := Lp.compMeasurePreservingₗᵢ ℂ e he (E := ℂ) (p := 2)
  have hC : Function.Surjective C := by
    intro g
    let f := Lp.compMeasurePreserving e.symm (he.symm e) g
    refine ⟨f, Lp.ext ?_⟩
    have hf := Lp.coeFn_compMeasurePreserving g (he.symm e)
    filter_upwards [Lp.coeFn_compMeasurePreserving f he, he.quasiMeasurePreserving.ae_eq_comp hf] with x hx hy
    calc _ = f (e x) := hx
         _ = g (e.symm (e x)) := hy
         _ = _ := by rw [e.symm_apply_apply]
  have hw : Measurable (rootLandauEnvelope b) := by unfold rootLandauEnvelope; fun_prop
  obtain ⟨W,hW⟩ := squared_weight_unitary hw (root_landau_envelope_pos hb)
  refine ⟨(LinearIsometryEquiv.ofSurjective C hC).trans W, fun f => ?_⟩
  have h₁ := Lp.coeFn_compMeasurePreserving f he
  have h₂ : (volume : Measure ℝ) ≪ squaredWeightLaw (rootLandauEnvelope b) :=
    withDensity_absolutelyContinuous' ((hw.pow_const 2).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (root_landau_envelope_pos hb x) _))
  filter_upwards [hW (C f), h₂.ae_le h₁] with x hx hy
  change W (C f) x = _
  rw [hx]
  exact congrArg ((rootLandauEnvelope b x : ℂ) * ·) hy

def normalizedLandauMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (Real.sqrt (2*b) / Real.sqrt (2*Real.pi)) / factorialRoot n) * rootFiberMode b n x : ℝ)

theorem root_landau_basis {b : ℝ} (hb : 0 < b) :
    ∃ μ : HilbertBasis ℕ ℂ LebesgueFiber, ∀ n, ⇑(μ n) =ᵐ[volume] normalizedLandauMode b n := by
  obtain ⟨B,hB⟩ := root_gaussian_basis_exists
  obtain ⟨U,hU⟩ := root_landau_fiber_unitary hb
  let V : HilbertBasis ℕ ℂ LebesgueFiber := HilbertBasis.ofRepr (U.symm.trans B.repr)
  refine ⟨V, fun n => ?_⟩
  have hv : V n = U (B n) := by
    rw [← V.repr_symm_single, ← B.repr_symm_single]
    rfl
  rw [hv]
  have hs := (landau_scale_preserves hb).quasiMeasurePreserving.ae_eq_comp (hB n)
  have hw : Measurable (rootLandauEnvelope b) := by unfold rootLandauEnvelope; fun_prop
  have ha : (volume : Measure ℝ) ≪ squaredWeightLaw (rootLandauEnvelope b) :=
    withDensity_absolutelyContinuous' ((hw.pow_const 2).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (root_landau_envelope_pos hb x) _))
  filter_upwards [hU (B n), ha.ae_le hs] with x hx hy
  have hnn := Complex.ofReal_ne_zero.mpr (factorialRoot_pos n).ne'
  have hz : B n (Real.sqrt (2*b)*x) = ((rootHermite n).eval (Real.sqrt (2*b)*x) : ℝ) / (factorialRoot n : ℂ) := by
    apply (eq_div_iff hnn).2
    rw [mul_comm]
    exact hy
  rw [hx, hz]
  change (rootLandauEnvelope b x : ℂ) * _ =
    (((Real.sqrt (Real.sqrt (2*b) / Real.sqrt (2*Real.pi)) / factorialRoot n) *
      ((rootHermite n).eval (Real.sqrt (2*b)*x) * Real.exp (-b*x^2/2)) : ℝ) : ℂ)
  simp only [rootLandauEnvelope, Complex.ofReal_mul, Complex.ofReal_div]
  ring

theorem root_landau_mode_norm {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∫ x, ‖normalizedLandauMode b n x‖^2 = 1 := by
  obtain ⟨B,hB⟩ := root_landau_basis hb
  have h : (∫ x, ‖normalizedLandauMode b n x‖^2) = ∫ x, ‖B n x‖ ^ 2 := by
    exact integral_congr_ae ((hB n).symm.mono fun x hx => congrArg (fun z : ℂ => ‖z‖^2) hx)
  rw [h, integral_norm_sq_lp, B.orthonormal.norm_eq_one, one_pow]

end UV.RootMagnetic
