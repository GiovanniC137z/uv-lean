import UV.ResumeOpticalResolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Removing one common conserved-momentum variable from the packet optical
identity. A decomposable measured amplitude acts on each localized incoming
packet by its own fibre. No product of momentum delta distributions occurs. -/

noncomputable section
namespace UV.SectorPlane
open MeasureTheory Filter Set
open scoped ComplexConjugate InnerProductSpace InnerProduct ENNReal

variable {E F K : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [MeasurableSpace K] {μ : Measure K}

omit [CompleteSpace F] in
private theorem optical_fibre_packet_square (w : Lp F 2 μ) :
    ‖w‖^2 = ∫ k, ‖w k‖^2 ∂μ := by
  have hi := L2.integrable_inner (𝕜 := ℂ) w w
  have he := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) w w)
  rw [←integral_re hi] at he
  simpa only [←norm_sq_eq_re_inner] using he

/-- The concrete momentum-diagonal matrix element on all characteristic
packets of finite measure. The data can retain the whole positive outgoing
channel space in each momentum fibre. -/
def Plane.HasConservedPacketRow (diamond : Plane E) (T : Plane E → Lp F 2 μ →L[ℂ] Lp F 2 μ)
    (v : F) (a : K → F) : Prop :=
  ∀ (s : Set K) (hs : MeasurableSet s) (hfin : μ s < ∞),
    (T diamond (indicatorConstLp 2 hs hfin.ne v) : Lp F 2 μ) =ᵐ[μ] s.indicator a

theorem Plane.physical_optical_fibre [SigmaFinite μ] (diamond : Plane E)
    (T : Plane E → Lp F 2 μ →L[ℂ] Lp F 2 μ) (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (v : F) (a : K → F) (hrow : diamond.HasConservedPacketRow T v a) :
    ∀ᵐ k ∂μ, 2*(inner ℂ v (a k)).im = ‖a k‖^2 := by
  have hloc (s : Set K) (hs : MeasurableSet s) (hfin : μ s < ∞) :
      IntegrableOn (fun k => 2*(inner ℂ v (a k)).im) s μ ∧ IntegrableOn (fun k => ‖a k‖^2) s μ ∧
      (∫ k in s, 2*(inner ℂ v (a k)).im ∂μ) = ∫ k in s, ‖a k‖^2 ∂μ := by
    let i := indicatorConstLp 2 hs hfin.ne v
    let w := T diamond i
    have hw : (w : K → F) =ᵐ[μ] s.indicator a := hrow s hs hfin
    have ha : (fun k => inner ℂ (i k) (w k)) =ᵐ[μ.restrict s] fun k => inner ℂ v (a k) := by
      filter_upwards [ae_restrict_of_ae (s := s) hw,ae_restrict_of_ae (s := s) (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := v)),ae_restrict_mem hs] with k hk hi hks
      change inner ℂ ((indicatorConstLp 2 hs hfin.ne v : Lp F 2 μ) k) (w k) = _
      simp only [hk,hi,indicator_of_mem hks]
    have hf : IntegrableOn (fun k => inner ℂ v (a k)) s μ := (L2.integrable_inner (𝕜 := ℂ) i w).integrableOn.congr ha
    have hb : (fun k => ‖w k‖^2) =ᵐ[μ] s.indicator (fun k => ‖a k‖^2) := by
      filter_upwards [hw] with k hk
      by_cases h : k ∈ s <;> simp [hk,h]
    have hg := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)).congr hb
    refine ⟨hf.im.const_mul _, (integrable_indicator_iff hs).mp hg, ?_⟩
    have hi := diamond.physical_optical_packet T hS i
    change 2*(inner ℂ i w).im = ‖w‖^2 at hi
    have hinner : inner ℂ i w = ∫ k in s, inner ℂ v (a k) ∂μ := by
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (s := s) hw,ae_restrict_mem hs] with k hk hks
      simp [hk,hks]
    rw [hinner,optical_fibre_packet_square,integral_congr_ae hb,integral_indicator hs] at hi
    rw [integral_const_mul]
    change 2 * ∫ k in s, RCLike.im (inner ℂ v (a k)) ∂μ = _
    rw [integral_im hf]
    exact hi
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s hs h => (hloc s hs h).1)
    (fun s hs h => (hloc s hs h).2.1) (fun s hs h => (hloc s hs h).2.2)

theorem Plane.physical_optical_fibre_channels [SigmaFinite μ] (diamond : Plane E)
    (T : Plane E → Lp F 2 μ →L[ℂ] Lp F 2 μ) (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (v : F) (a : K → F) (hrow : diamond.HasConservedPacketRow T v a)
    {N : Type*} {X : N → Type*} [∀ n, MeasurableSpace (X n)]
    (phase : K → Plane E → (n : N) → Measure (X n))
    (U : (k : K) → F ≃ₗᵢ[ℂ] Lp ℂ 2 (diamond.physicalIntermediateMeasure (phase k))) :
    ∀ᵐ k ∂μ, let f := U k (a k)
      (∀ n, Integrable (fun x : X n => ‖f (Sigma.mk n x)‖^2) (phase k diamond n)) ∧
      HasSum (fun n => ∫ x, ‖f (Sigma.mk n x)‖^2 ∂phase k diamond n) (2*(inner ℂ v (a k)).im) := by
  filter_upwards [diamond.physical_optical_fibre T hS v a hrow] with k hk
  let f := U k (a k)
  let mass := fun n => ∫⁻ x, ENNReal.ofReal (‖f (Sigma.mk n x)‖^2) ∂phase k diamond n
  have htotal : (∑' n, mass n) = ENNReal.ofReal (‖a k‖^2) := by
    unfold mass
    rw [← diamond.lintegral_physical_intermediate_measure (phase k) (fun x => ENNReal.ofReal (‖f x‖^2))
      (((Lp.stronglyMeasurable f).measurable.norm.pow_const 2).ennreal_ofReal),←physical_packet_norm_sq_eq_lintegral]
    rw [show ‖f‖ = ‖a k‖ from (U k).norm_map _]
  have htot : (∑' n, mass n) ≠ ∞ := htotal.trans_ne ENNReal.ofReal_ne_top
  have hfin (n : N) := ENNReal.ne_top_of_tsum_ne_top htot n
  have hmeas (n : N) : AEStronglyMeasurable (fun x : X n => ‖f (Sigma.mk n x)‖^2) (phase k diamond n) := by
    have hm : Measurable (Sigma.mk n : X n → Σ n,X n) :=
      measurable_iff_le_map.mpr (iInf_le (fun i => (inferInstance : MeasurableSpace (X i)).map (Sigma.mk i)) n)
    exact (((Lp.stronglyMeasurable f).measurable.comp hm).norm.pow_const 2).aestronglyMeasurable
  have he (n : N) : (∫ x, ‖f (Sigma.mk n x)‖^2 ∂phase k diamond n) = (mass n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) (hmeas n)
  refine ⟨fun n => (lintegral_ofReal_ne_top_iff_integrable (hmeas n) (Eventually.of_forall fun _ => sq_nonneg _)).mp (hfin n),?_⟩
  change HasSum (fun n => ∫ x, ‖f (Sigma.mk n x)‖^2 ∂phase k diamond n) _
  simp_rw [he]
  have hh : (∑' n, mass n).toReal = 2*(inner ℂ v (a k)).im := by rw [htotal,ENNReal.toReal_ofReal (sq_nonneg _),hk]
  rw [←hh,ENNReal.tsum_toReal_eq hfin]
  exact ENNReal.hasSum_toReal htot

theorem Plane.physical_optical_continuous_fibre [SigmaFinite μ] [TopologicalSpace K] [μ.IsOpenPosMeasure]
    (diamond : Plane E) (T : Plane E → Lp F 2 μ →L[ℂ] Lp F 2 μ)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (v : F) (a : K → F) (hrow : diamond.HasConservedPacketRow T v a) (ha : Continuous a) (k : K) :
    2*(inner ℂ v (a k)).im = ‖a k‖^2 := by
  exact congrFun (Measure.eq_of_ae_eq (μ := μ) (diamond.physical_optical_fibre T hS v a hrow)
    (continuous_const.mul (Complex.continuous_im.comp (continuous_const.inner ha))) (ha.norm.pow 2)) k

end UV.SectorPlane
