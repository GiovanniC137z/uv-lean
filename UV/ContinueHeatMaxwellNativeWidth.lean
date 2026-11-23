import UV.ContinueHeatMaxwellLoopInputs
import UV.ContinueRelativeSoftTrace
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Width scaling of the actual Gaussian symbol, the one-chord
contact, and the four-dimensional continuum spin kernel. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.SectorPlane UV.RelativeSoft MeasureTheory
open scoped RealInnerProductSpace Topology

local instance continueHeatMaxwellNativeWidthMeasurableSpace : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance continueHeatMaxwellNativeWidthBorelSpace : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

private abbrev K := EuclideanPlaneMomentum

def heatWidthSymbol (a : ℝ) (k : K) : K := Real.exp (-(a^2*‖k‖^2)) • k

theorem heat_width_symbol {a : ℝ} (ha : 0<a) (k : K) : heatWidthSymbol a k=a⁻¹ • heatSymbol (a • k) := by
  simp only [heatWidthSymbol,heatSymbol,norm_smul,Real.norm_eq_abs,abs_of_pos ha,mul_pow,smul_smul]
  congr 1
  field_simp

def heatWidthLocal (a : ℝ) (n : ℕ) (k : K) (r : ℝ) : K :=
  iteratedDeriv n (fun θ : ℝ => heatWidthSymbol a (k+r • softLongitudinal.val+θ • softTransverse.val)) 0

theorem heat_width_local {a : ℝ} (ha : 0<a) (n : ℕ) (k : K) (r : ℝ) :
    heatWidthLocal a n k r = (a⁻¹*a^n) • iteratedDeriv n (fun θ : ℝ =>
      heatSymbol (a • k+(a*r) • softLongitudinal.val+θ • softTransverse.val)) 0 := by
  let f := fun θ : ℝ => heatSymbol (a • k+(a*r) • softLongitudinal.val+θ • softTransverse.val)
  have hf : ContDiff ℝ n f := by
    have H : f = fun θ => (Real.exp (-‖a • k‖^2)*heatShiftFactor ⟪a • k,softLongitudinal.val⟫ (a*r) *
      heatShiftFactor ⟪a • k,softTransverse.val⟫ θ) • (a • k+(a*r) • softLongitudinal.val+θ • softTransverse.val) :=
      funext (heatSymbol_two_unit_shifts (a • k) (a*r))
    rw [H];unfold heatShiftFactor;fun_prop
  have hfc : ContDiff ℝ n (fun t : ℝ => f (a*t)) := hf.comp (contDiff_const.mul contDiff_id)
  have he : (fun θ : ℝ => heatWidthSymbol a (k+r • softLongitudinal.val+θ • softTransverse.val)) =
      a⁻¹ • (fun θ : ℝ => f (a*θ)) := by
    funext θ
    rw [heat_width_symbol ha]
    simp only [Pi.smul_apply,f,smul_add,smul_smul]
  change iteratedDeriv n _ 0=(a⁻¹*a^n) • iteratedDeriv n f 0
  rw [he,iteratedDeriv_const_smul hfc.contDiffAt,iteratedDeriv_comp_const_smul hf a]
  simp [smul_smul]

def heatWidthFirstChord (a : ℝ) (k : K) := heatChordMoment heatCenteredLaw id 0 (heatWidthLocal a 1 k)
def heatWidthContactChord (a : ℝ) (k : K) := heatChordMoment heatContactLaw
  (fun z : ℝ×ℝ => z.1-z.2) 0 (heatWidthLocal a 2 k)

theorem heat_width_first_chord {a : ℝ} (ha : 0<a) (k : K) (t : ℝ) :
    heatWidthFirstChord a k t=heatFirstChord (a • k) (a*t) := by
  simp only [heatWidthFirstChord,heatFirstChord,heatChordMoment,heat_width_local ha,heatFirstLocal,
    pow_one,inv_mul_cancel₀ ha.ne',one_smul,iteratedDeriv_one,pow_zero]
  congr 1
  funext s
  rw [mul_left_comm a (id s) t]

theorem heat_width_contact_chord {a : ℝ} (ha : 0<a) (k : K) (t : ℝ) :
    heatWidthContactChord a k t=a • heatContactChord (a • k) (a*t) := by
  have hc : a⁻¹*a^2=a := by field_simp
  simp only [heatWidthContactChord,heatContactChord,heatChordMoment,heat_width_local ha,heatContactLocal,hc,
    iteratedDeriv_succ,iteratedDeriv_zero,pow_zero,one_smul,←integral_smul]
  congr 1
  funext s
  rw [mul_left_comm a (s.1-s.2) t]

def heatWidthNativeResponse (m a : ℝ) (k : K) (t : ℝ) : ℝ :=
  let p := heatWidthSymbol a (k+(-t/2) • softLongitudinal.val)
  let q := heatWidthSymbol a (k+(t/2) • softLongitudinal.val)
  let h := heatWidthSymbol a k
  let v := heatWidthFirstChord a k t
  let w := heatWidthContactChord a k t
  (2*⟪p,v⟫*⟪q,v⟫-(m^2+⟪p,q⟫)*‖v‖^2)/((‖p‖^2+m^2)*(‖q‖^2+m^2))-⟪h,w⟫/(‖h‖^2+m^2)

theorem heat_width_native_response {m a : ℝ} (hm : 0<m) (ha : 0<a) (k : K) (t : ℝ) :
    heatWidthNativeResponse m a k t = a^2*heatNativeResponse (m*a) (a • k) (a*t) := by
  have hd (p : K) : ‖a⁻¹ • p‖^2+m^2=(‖p‖^2+(m*a)^2)/a^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    field_simp
  have hp : ∀ p : K, 0<‖p‖^2+(m*a)^2 := fun _ => by positivity
  simp only [heatWidthNativeResponse,heatNativeResponse,heat_width_symbol ha,heat_width_first_chord ha,heat_width_contact_chord ha,smul_add,smul_smul,
    show a*(-t/2)=-(a*t)/2 by ring,show a*(t/2)=a*t/2 by ring,hd,real_inner_smul_left,real_inner_smul_right]
  field_simp [ha.ne',fun p => (hp p).ne']

/-- Both the momentum measure and the original chord operators are
scaled before integrating out the Euclidean sector momentum. -/
theorem heat_width_native_integral {m a : ℝ} (hm : 0<m) (ha : 0<a) (t : ℝ) :
    (∫ k, heatWidthNativeResponse m a k t) =
      (a^2)⁻¹*(∫ k, heatNativeResponse (m*a) k (a*t)) := by
  simp_rw [heat_width_native_response hm ha,integral_const_mul]
  rw [show (∫ k : K, heatNativeResponse (m*a) (a • k) (a*t)) =
    ((a^4)⁻¹) • ∫ k, heatNativeResponse (m*a) k (a*t) by
      simpa only [soft_momentum_finrank] using
        (Measure.integral_comp_smul_of_nonneg (volume : Measure K) (fun k => heatNativeResponse (m*a) k (a*t)) a (hR:=ha.le))]
  simp only [smul_eq_mul]
  field_simp [ha.ne']

end UV.HeatMaxwell
