import UV.ContinueHeatMaxwellLoopDeriv
import UV.ContinueHeatMaxwellNativeTrace

/-! The literal shifted covariances and two native chord marks,
together with their first two derivatives in the external direction. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

local instance continueHeatMaxwellLoopInputsMeasurableSpace : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance continueHeatMaxwellLoopInputsBorelSpace : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩
private abbrev K := EuclideanPlaneMomentum

private def heatAveragedCurve {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    (a : ι→ℝ) (ha : Measurable a) (hb : ∀ᵐ z ∂μ, |a z|≤1)
    (y w : K→K) (hy : Continuous y) (hw : Continuous w)
    {C : ℝ} (hC : 0≤C) (hbound : ∀ k, ‖y k‖≤C*(1+‖k‖)^3 ∧ ‖w k‖≤C*(1+‖k‖)^3) : HeatLoopCurve K := by
  let M := fun k => heatAffineMark k (y k) (w k)
  let F := fun k => heatAffineFirst k (y k) (w k)
  let D := fun k => heatAffineSecond k (y k) (w k)
  have mf : Continuous (fun p : K×ℝ => M p.1 p.2) := by dsimp only [M,heatAffineMark,heatShiftGaussian,heatShiftFactor];fun_prop
  have ff : Continuous (fun p : K×ℝ => F p.1 p.2) := by dsimp only [F,heatAffineFirst,heatShiftGaussian,heatShiftFactor];fun_prop
  have df : Continuous (fun p : K×ℝ => D p.1 p.2) := by dsimp only [D,heatAffineSecond,heatShiftGaussian,heatShiftFactor];fun_prop
  have hm (V : K → ℝ → K) (hV : Continuous (fun p : K×ℝ => V p.1 p.2)) (n : ℕ) (t : ℝ) :
      AEStronglyMeasurable (fun k => heatChordMoment μ a n (V k) t) := by
    have hza : Measurable (fun p : K×ι => a p.2) := ha.comp measurable_snd
    have hu : Measurable (fun p : K×ι => ((a p.2)^n) • V p.1 (a p.2*t)) :=
      (hza.pow_const _).smul (hV.measurable.comp (measurable_fst.prodMk (hza.mul_const t)))
    exact hu.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  refine {
    value := fun t k => heatChordMoment μ a 0 (M k) t
    first := fun t k => heatChordMoment μ a 1 (F k) t
    second := fun t k => heatChordMoment μ a 2 (D k) t
    deriv_value := fun t k => heat_chord_moment_hasDerivAt ha hb (ff.comp (continuous_const.prodMk continuous_id))
      (fun s => (heat_affine_derivatives k (y k) (w k) s).1) 0 t
    deriv_first := fun t k => heat_chord_moment_hasDerivAt ha hb (df.comp (continuous_const.prodMk continuous_id))
      (fun s => (heat_affine_derivatives k (y k) (w k) s).2) 1 t
    measurable_value := hm M mf 0
    measurable_first := hm F ff 1
    measurable_second := hm D df 2
    gaussian_bound := ?_ }
  let A := 24*C*Real.exp 2*Real.exp 25
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨A*μ.real univ,mul_nonneg hA ENNReal.toReal_nonneg,?_⟩
  intro t k ht
  have he (n : ℕ) (f : ℝ → K) (hf : ∀ s, |s|≤1 → ‖f s‖≤A*heatLoopMajorant k) :
      ‖heatChordMoment μ a n f t‖ ≤ A*μ.real univ*heatLoopMajorant k := by
    have hmajor : ∀ᵐ z ∂μ, ‖(a z)^n • f (a z*t)‖ ≤ A*heatLoopMajorant k := by
      filter_upwards [hb] with z hz
      have hs : |a z*t|≤1 := by rw [abs_mul];exact (mul_le_mul hz ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      rw [norm_smul,norm_pow,Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)).trans (hf _ hs)
    exact (norm_integral_le_of_norm_le_const hmajor).trans_eq (by ring)
  have hu (s : ℝ) (hs : |s|≤1) := heat_affine_uniform k (y k) (w k) hC (hbound k).1 (hbound k).2 hs
  exact ⟨he 0 (M k) (fun s hs => (hu s hs).1),he 1 (F k) (fun s hs => (hu s hs).2.1),he 2 (D k) (fun s hs => (hu s hs).2.2)⟩

private def heatShiftCurve (c : ℝ) (hc : |c|≤1) : HeatLoopCurve K :=
  heatAveragedCurve (Measure.dirac (0:ℝ)) (fun _ => c) measurable_const (Eventually.of_forall fun _ => hc)
    id (fun _ => softLongitudinal.val) continuous_id continuous_const (C:=1) (by norm_num) fun k => by
      simp only [id_eq,one_mul,softLongitudinal.property]
      constructor <;> nlinarith [norm_nonneg k,sq_nonneg ‖k‖,pow_nonneg (norm_nonneg k) 3]

private theorem heat_shift_curve_val (c : ℝ) (hc : |c|≤1) (k : K) (t : ℝ) :
    (heatShiftCurve c hc).value t k = heatSymbol (k+(c*t) • softLongitudinal.val) := by
  change heatChordMoment (Measure.dirac (0:ℝ)) (fun _ => c) 0 (heatAffineMark k k softLongitudinal.val) t = _
  simp only [heatChordMoment,integral_const,measureReal_univ_eq_one,one_smul,pow_zero,heatAffineMark,heatShiftGaussian]
  have he := heatSymbol_two_unit_shifts k (c*t) 0
  simpa only [zero_smul,add_zero,heatShiftFactor_at_zero,mul_one] using he.symm

private def heatFirstY (k : K) : K := (-2*⟪k,softTransverse.val⟫) • k+softTransverse.val
private def heatFirstW (k : K) : K := (-2*⟪k,softTransverse.val⟫) • softLongitudinal.val
private def heatContactY (k : K) : K :=
  (4*⟪k,softTransverse.val⟫^2-2) • k+(-4*⟪k,softTransverse.val⟫) • softTransverse.val
private def heatContactW (k : K) : K := (4*⟪k,softTransverse.val⟫^2-2) • softLongitudinal.val

private theorem heat_seed_bounds (k : K) :
    (‖heatFirstY k‖≤10*(1+‖k‖)^3 ∧ ‖heatFirstW k‖≤10*(1+‖k‖)^3) ∧
    (‖heatContactY k‖≤10*(1+‖k‖)^3 ∧ ‖heatContactW k‖≤10*(1+‖k‖)^3) := by
  let j := ⟪k,softTransverse.val⟫
  let r := ‖k‖
  have hj : |j|≤r := by simpa only [j,r,softTransverse.property,mul_one] using abs_real_inner_le_norm k softTransverse.val
  have hr : 0≤r := norm_nonneg _
  have hj2 : j^2≤r^2 := sq_le_sq.mpr (hj.trans_eq (abs_of_nonneg hr).symm)
  have h4 : |4*j^2-2|≤4*r^2+2 := abs_le.mpr ⟨by nlinarith [sq_nonneg j,sq_nonneg r],by linarith⟩
  have h1 := mul_le_mul_of_nonneg_right hj hr
  have h2 := mul_le_mul_of_nonneg_right h4 hr
  have h3 := pow_nonneg hr 3
  simp only [heatFirstY,heatFirstW,heatContactY,heatContactW,norm_smul,Real.norm_eq_abs,abs_mul,
    softLongitudinal.property,mul_one]
  have hy1 := norm_add_le ((-2*j) • k) softTransverse.val
  have hy2 := norm_add_le ((4*j^2-2) • k) ((-4*j) • softTransverse.val)
  simp only [norm_smul,Real.norm_eq_abs,abs_mul,softTransverse.property,mul_one] at hy1 hy2
  norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_nonneg (by norm_num : (0:ℝ)≤4)] at *
  constructor <;> constructor <;> dsimp only [j,r] at * <;> nlinarith [sq_nonneg ‖k‖]

private def heatFirstCurve : HeatLoopCurve K :=
  heatAveragedCurve heatCenteredLaw id measurable_id heat_centered_bound heatFirstY heatFirstW
    (by unfold heatFirstY;fun_prop) (by unfold heatFirstW;fun_prop) (C:=10) (by norm_num) (fun k => (heat_seed_bounds k).1)

private def heatContactCurve : HeatLoopCurve K :=
  heatAveragedCurve heatContactLaw (fun z : ℝ×ℝ => z.1-z.2) (measurable_fst.sub measurable_snd) heat_contact_bound
    heatContactY heatContactW (by unfold heatContactY;fun_prop) (by unfold heatContactW;fun_prop)
    (C:=10) (by norm_num) (fun k => (heat_seed_bounds k).2)

private theorem heat_first_curve_val (k : K) (t : ℝ) : heatFirstCurve.value t k = heatFirstChord k t := by
  change heatChordMoment _ _ _ (heatAffineMark k (heatFirstY k) (heatFirstW k)) _ =
    heatChordMoment _ _ _ (heatFirstLocal k) _
  congr 1
  funext s
  rw [heatFirstLocal,(heatSymbol_transverse_derivatives k s).1]
  dsimp [heatAffineMark,heatShiftGaussian,heatFirstY,heatFirstW]
  module

private theorem heat_contact_curve_val (k : K) (t : ℝ) : heatContactCurve.value t k = heatContactChord k t := by
  change heatChordMoment _ _ _ (heatAffineMark k (heatContactY k) (heatContactW k)) _ =
    heatChordMoment _ _ _ (heatContactLocal k) _
  congr 1
  funext s
  rw [heatContactLocal,(heatSymbol_transverse_derivatives k s).2]
  dsimp [heatAffineMark,heatShiftGaussian,heatContactY,heatContactW]
  module

private abbrev HeatResponseSlots := K × K × K × K × K
private def heatSlots : HeatLoopCurve HeatResponseSlots :=
  (heatShiftCurve (-1/2) (by norm_num)).pair ((heatShiftCurve (1/2) (by norm_num)).pair
    ((heatShiftCurve 0 (by norm_num)).pair (heatFirstCurve.pair heatContactCurve)))

private def heatContract (m : ℝ) (x : HeatResponseSlots) : ℝ :=
  let p := x.1
  let q := x.2.1
  let h := x.2.2.1
  let v := x.2.2.2.1
  let w := x.2.2.2.2
  (2*⟪p,v⟫*⟪q,v⟫-(m^2+⟪p,q⟫)*‖v‖^2)/((‖p‖^2+m^2)*(‖q‖^2+m^2))-⟪h,w⟫/(‖h‖^2+m^2)

attribute [local fun_prop] ContDiff.inner Continuous.inner

private theorem heat_contract_smooth {m : ℝ} (hm : 0<m) : ContDiff ℝ 2 (heatContract m) := by
  unfold heatContract
  dsimp only
  simp_rw [←real_inner_self_eq_norm_sq]
  apply ContDiff.sub
  · apply ContDiff.div
    · fun_prop
    · fun_prop
    · intro x
      simp only [real_inner_self_eq_norm_sq]
      positivity
  · apply ContDiff.div
    · fun_prop
    · fun_prop
    · intro x
      simp only [real_inner_self_eq_norm_sq]
      positivity

private theorem heat_contract_zero (m : ℝ) : heatContract m 0=0 := by simp [heatContract]

def heatNativeCurve {m : ℝ} (hm : 0<m) : HeatLoopCurve ℝ :=
  heatSlots.compose (heat_contract_smooth hm) (heat_contract_zero m)

theorem heat_native_curve_value {m : ℝ} (hm : 0<m) (t : ℝ) (k : K) :
    (heatNativeCurve hm).value t k = heatNativeResponse m k t := by
  change heatContract m (heatSlots.value t k) = _
  simp only [heatContract,heatSlots,HeatLoopCurve.pair,heat_shift_curve_val,heat_first_curve_val,
    heat_contact_curve_val,heatNativeResponse,zero_mul,zero_smul,add_zero]
  congr 3 <;> ring_nf

/-- The four-dimensional momentum integral of the original native bubble
and direct contact has the integrated pointwise second derivative. -/
theorem heat_native_response_integral_second {m : ℝ} (hm : 0<m) :
    deriv (deriv (fun t => ∫ k, heatNativeResponse m k t)) 0 =
    ∫ k, deriv (deriv (heatNativeResponse m k)) 0 := by
  let a := heatNativeCurve hm
  have he : (fun t k => heatNativeResponse m k t) = a.value := funext fun t => funext fun k => (heat_native_curve_value hm t k).symm
  have hp (k : K) : deriv (deriv (heatNativeResponse m k)) 0 = a.second 0 k := by
    have hd : deriv (heatNativeResponse m k) = fun t => a.first t k := by
      funext t
      have h0 : heatNativeResponse m k = fun s => a.value s k := funext fun s => (heat_native_curve_value hm s k).symm
      rw [h0,(a.deriv_value t k).deriv]
    rw [hd,(a.deriv_first 0 k).deriv]
  simp_rw [hp]
  exact (congrArg (fun f : ℝ→K→ℝ => deriv (deriv (fun t => ∫ k, f t k)) 0) he).trans (heat_loop_integral_second a)

theorem heat_native_second_integrable {m : ℝ} (hm : 0<m) :
    Integrable (fun k : EuclideanPlaneMomentum => deriv (deriv (heatNativeResponse m k)) 0) := by
  let a := heatNativeCurve hm
  have he (k : K) : heatNativeResponse m k = fun t => a.value t k :=
    funext fun t => (heat_native_curve_value hm t k).symm
  have hd (k : K) : deriv (heatNativeResponse m k) = fun t => a.first t k := by
    rw [he]
    exact funext fun t => (a.deriv_value t k).deriv
  simp_rw [hd,fun k => (a.deriv_first 0 k).deriv]
  obtain ⟨C,_,hc⟩ := a.gaussian_bound
  exact (heat_loop_majorant_integrable.const_mul C).mono' (a.measurable_second 0) (Eventually.of_forall fun k => (hc 0 k (by norm_num)).2.2)

theorem heat_first_chord_integrable {t : ℝ} (ht : |t|≤1) :
    Integrable (fun k : EuclideanPlaneMomentum => heatFirstChord k t) := by
  simp_rw [←heat_first_curve_val]
  obtain ⟨C,_,h⟩ := heatFirstCurve.gaussian_bound
  exact (heat_loop_majorant_integrable.const_mul C).mono' (heatFirstCurve.measurable_value t)
    (Eventually.of_forall fun k => (h t k ht).1)

theorem heat_native_response_integrable {m t : ℝ} (hm : 0<m) (ht : |t|≤1) :
    Integrable (fun k : EuclideanPlaneMomentum => heatNativeResponse m k t) := by
  simp_rw [←heat_native_curve_value hm t]
  obtain ⟨C,_,h⟩ := (heatNativeCurve hm).gaussian_bound
  exact (heat_loop_majorant_integrable.const_mul C).mono' ((heatNativeCurve hm).measurable_value t)
    (Eventually.of_forall fun k => (h t k ht).1)

end UV.HeatMaxwell
