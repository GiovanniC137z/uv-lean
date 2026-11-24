import UV.ContinueTwoBandFourierTorus

/-! The kernels of the one-sided onsite propagation followed by the
periodized hopping or its adjoint on a finite symmetric slab. The
temporal transport is taken at the same spatial position as the onsite
inverse. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

namespace UV.SectorPlane

private def onsitePrimitive (φ : TwoBandPoint → ℝ) (t : ℝ) (x : Spatial) : ℝ :=
  ∫ τ in (0:ℝ)..t, φ (τ,x)

private theorem onsite_primitive_continuous {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) :
    Continuous (fun p : TwoBandPoint => onsitePrimitive φ p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_fst
  change Continuous (fun p : TwoBandPoint × ℝ => φ (p.2,p.1.2))
  fun_prop

def twoBandOnsiteTransport (φ : TwoBandPoint → ℝ) (q : ℝ) (t s : ℝ) (x : Spatial) : ℂ :=
  Complex.exp (-Complex.I * (q:ℂ) * (onsitePrimitive φ t x - onsitePrimitive φ s x : ℝ))

theorem twoBand_onsite_transport_integral {φ : TwoBandPoint → ℝ} (hφ : Continuous φ)
    (q t s : ℝ) (x : Spatial) :
    twoBandOnsiteTransport φ q t s x = Complex.exp (-Complex.I*(q:ℂ)*(∫ τ in s..t, φ (τ,x) : ℝ)) := by
  have hc : Continuous (fun τ => φ (τ,x)) := hφ.comp (continuous_id.prodMk continuous_const)
  have h := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) 0 t) (hc.intervalIntegrable (μ := volume) 0 s)
  unfold twoBandOnsiteTransport onsitePrimitive
  rw [h]

theorem twoBand_onsite_transport_unit (φ : TwoBandPoint → ℝ) (q t s : ℝ) (x : Spatial) :
    ‖twoBandOnsiteTransport φ q t s x‖ = 1 := by
  simp [twoBandOnsiteTransport,Complex.norm_exp,Complex.mul_re]

private def bandOrientation (upper : Bool) (t s : ℝ) : ℝ :=
  if upper then (if s ≤ t then 1 else 0) else (if t < s then -1 else 0)

private theorem orientation_measurable (upper : Bool) :
    Measurable (fun p : ℝ × ℝ => bandOrientation upper p.1 p.2) := by
  cases upper <;> simp only [bandOrientation,Bool.false_eq_true,if_false,if_true]
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const measurable_const

private theorem orientation_le (upper : Bool) (t s : ℝ) : |bandOrientation upper t s| ≤ 1 := by
  unfold bandOrientation
  split_ifs <;> norm_num

def twoBandDirectedSlabHop (upper : Bool) (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (φ : TwoBandPoint → ℝ) (m q g σ L₁ L₂ L₃ : ℝ) (x y : TwoBandPoint) : ℂ :=
  (bandOrientation upper x.1 y.1 * Real.exp (-m*|x.1-y.1|) : ℝ) *
    twoBandOnsiteTransport φ q x.1 y.1 x.2 *
    (if upper then twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 x.2 y.2
      else conj (twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 y.2 x.2))

/-- The slab kernel, extended by zero outside the position cell. The
symmetric time interval is carried by the slab integration measure. -/
def twoBandSlabHopKernel (upper : Bool) (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (φ : TwoBandPoint → ℝ) (m q g σ L₁ L₂ L₃ : ℝ) (x y : TwoBandPoint) : ℂ := by
  classical
  exact if x.2 ∈ twoBandTorusCell L₁ L₂ L₃ ∧ y.2 ∈ twoBandTorusCell L₁ L₂ L₃ then
    twoBandDirectedSlabHop upper A φ m q g σ L₁ L₂ L₃ x y else 0

set_option maxHeartbeats 1200000 in
theorem twoBand_slab_hop_measurable (upper : Bool)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) (m q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    Measurable (fun p : TwoBandPoint × TwoBandPoint => twoBandSlabHopKernel upper A φ m q g σ L₁ L₂ L₃ p.1 p.2) := by
  have hc := twoBand_torus_cell_measurable L₁ L₂ L₃
  apply Measurable.ite ((hc.preimage (measurable_snd.comp measurable_fst)).inter
    (hc.preimage (measurable_snd.comp measurable_snd))) _ measurable_const
  have ht := twoBand_periodized_hop_measurable hA q g hσ h₁ h₂ h₃
  have h0 := onsite_primitive_continuous hφ
  have hphase : Continuous (fun p : TwoBandPoint × TwoBandPoint =>
      twoBandOnsiteTransport φ q p.1.1 p.2.1 p.1.2) := by
    have h1 := h0.comp (show Continuous (fun p : TwoBandPoint × TwoBandPoint => (p.2.1,p.1.2)) by fun_prop)
    have h2 := h0.comp (continuous_fst : Continuous (Prod.fst : TwoBandPoint × TwoBandPoint → TwoBandPoint))
    unfold twoBandOnsiteTransport
    exact Complex.continuous_exp.comp (continuous_const.mul <| Complex.continuous_ofReal.comp (h2.sub h1))
  have ho := (orientation_measurable upper).comp
    (show Measurable (fun p : TwoBandPoint × TwoBandPoint => (p.1.1,p.2.1)) by fun_prop)
  have he : Measurable (fun p : TwoBandPoint × TwoBandPoint => Real.exp (-m*|p.1.1-p.2.1|)) := by fun_prop
  let back : TwoBandPoint × TwoBandPoint → ℝ × Spatial × Spatial := fun p => (p.2.1,p.2.2,p.1.2)
  let forward : TwoBandPoint × TwoBandPoint → ℝ × Spatial × Spatial := fun p => (p.2.1,p.1.2,p.2.2)
  have hback : Measurable back := by unfold back; fun_prop
  have hforward : Measurable forward := by unfold forward; fun_prop
  have hB := Complex.continuous_conj.measurable.comp (ht.comp hback)
  have hF := ht.comp hforward
  have hf : Measurable (fun p : TwoBandPoint × TwoBandPoint =>
      if upper then twoBandPeriodizedHop A q g σ L₁ L₂ L₃ p.2.1 p.1.2 p.2.2
        else conj (twoBandPeriodizedHop A q g σ L₁ L₂ L₃ p.2.1 p.2.2 p.1.2)) := by
    cases upper
    · exact hB
    · exact hF
  exact ((Complex.continuous_ofReal.measurable.comp (ho.mul he)).mul hphase.measurable).mul hf

theorem twoBand_slab_hop_bound (upper : Bool) (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (φ : TwoBandPoint → ℝ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖twoBandSlabHopKernel upper A φ m q g σ L₁ L₂ L₃ x y‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := twoBand_periodized_hop_bounded A q g hσ h₁ h₂ h₃
  refine ⟨C,hC,?_⟩
  intro x y
  unfold twoBandSlabHopKernel
  split_ifs with hxy
  · have hhop :
        ‖if upper then twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 x.2 y.2
            else conj (twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 y.2 x.2)‖ ≤ C := by
      cases upper
      · simpa using (hB y.1 y.2 x.2 hxy.2 hxy.1).2
      · exact (hB y.1 x.2 y.2 hxy.1 hxy.2).2
    have he : Real.exp (-m*|x.1-y.1|) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) (abs_nonneg _))
    unfold twoBandDirectedSlabHop
    rw [norm_mul,norm_mul,twoBand_onsite_transport_unit,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (orientation_le upper _ _)
      (Real.exp_pos _).le he)).trans hhop
  · simpa using hC

/-- Both one-sided onsite/hopping kernels have finite squared integral
on the product of two copies of the actual symmetric slab. -/
theorem twoBand_slab_hop_squared_integrable (upper : Bool) (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    let μ := twoBandSlabMeasure T L₁ L₂ L₃
    Integrable (fun p : TwoBandPoint × TwoBandPoint =>
      ‖twoBandSlabHopKernel upper A φ m q g σ L₁ L₂ L₃ p.1 p.2‖^2) (μ.prod μ) := by
  obtain ⟨C,_,hC⟩ := twoBand_slab_hop_bound upper A φ hm q g hσ h₁ h₂ h₃
  exact (MemLp.of_bound (p := (2:ℕ)) (twoBand_slab_hop_measurable upper hA hφ m q g hσ h₁ h₂ h₃).aestronglyMeasurable
    C (ae_of_all _ fun p => hC p.1 p.2)).integrable_norm_pow (by norm_num)

end UV.SectorPlane
