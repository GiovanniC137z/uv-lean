import UV.ContinueNormalFrequency
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.MeanInequalities

/-! Five-dimensional zero-winding power counting for the actual
normal-circle Dirac multiplier with independently shifted carriers. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

abbrev NormalLoopFrequency := OSFourSpace × ℝ

local instance normalFrequencyHaar : (volume : Measure NormalLoopFrequency).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod OSFourSpace ℝ]
  infer_instance

def normalLoopWeight (m : ℝ) (x : NormalLoopFrequency) : ℝ :=
  (Real.sqrt (normalFiveDenom m x.1 x.2))⁻¹

theorem normal_weight_power_integrable {m : ℝ} (hm : 0 < m) {r : ℕ} (hr : 5 < r) :
    Integrable (fun x : NormalLoopFrequency => normalLoopWeight m x ^ r) := by
  let b := min 1 m
  have hb : 0 < b := lt_min zero_lt_one hm
  have hdim : (Module.finrank ℝ NormalLoopFrequency : ℝ) < (r:ℝ) := by
    rw [Module.finrank_prod,finrank_euclideanSpace_fin,Module.finrank_self]
    exact_mod_cast hr
  have hI := (integrable_one_add_norm (μ := (volume : Measure NormalLoopFrequency)) hdim).const_mul ((2/b)^r)
  apply hI.mono' (Measurable.aestronglyMeasurable (by unfold normalLoopWeight normalFiveDenom; fun_prop))
  apply Eventually.of_forall fun x => ?_
  let d := Real.sqrt (normalFiveDenom m x.1 x.2)
  have hD : 0 < normalFiveDenom m x.1 x.2 := by unfold normalFiveDenom; positivity
  have hd : 0 < d := Real.sqrt_pos.mpr hD
  have hsq := Real.sq_sqrt hD.le
  change d^2 = m^2+‖x.1‖^2+x.2^2 at hsq
  have hmd : m ≤ d := by nlinarith [sq_nonneg ‖x.1‖,sq_nonneg x.2]
  have hnd : ‖x‖ ≤ d := by
    rw [Prod.norm_def,Real.norm_eq_abs,max_le_iff]
    constructor <;> nlinarith [sq_nonneg m,sq_nonneg ‖x.1‖,sq_nonneg x.2,sq_abs x.2,abs_nonneg x.2,norm_nonneg x.1]
  have hmin : b*(1+‖x‖) ≤ 2*d := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 m) (norm_nonneg x)
    have h2 := (min_le_right 1 m).trans hmd
    dsimp [b] at *
    nlinarith
  have ht : d⁻¹ ≤ (2/b)*(1+‖x‖)⁻¹ := by
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity : 0 < 1+‖x‖),le_div_iff₀ hb,inv_mul_eq_div,
      div_mul_eq_mul_div,div_le_iff₀ hd]
    linarith
  change ‖d⁻¹^r‖ ≤ (2/b)^r * (1+‖x‖)^(-(r:ℝ))
  rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hd.le) _)]
  simpa only [Real.rpow_neg (by positivity : 0 ≤ 1+‖x‖),Real.rpow_natCast,mul_pow,inv_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hd.le) ht r

theorem normal_weight_power_shift {m : ℝ} (hm : 0 < m) {r : ℕ} (hr : 5 < r) (s : OSFourSpace) :
    let f := fun x : NormalLoopFrequency => normalLoopWeight m (x.1+s,x.2)^r
    Integrable f ∧ (∫ x, f x) = ∫ x : NormalLoopFrequency, normalLoopWeight m x^r := by
  let t : NormalLoopFrequency := (s,0)
  have h (x : NormalLoopFrequency) : x+t = (x.1+s,x.2) := Prod.ext rfl (add_zero _)
  have hi := (measurePreserving_add_right volume t).integrable_comp_of_integrable (normal_weight_power_integrable hm hr)
  have he := integral_add_right_eq_self (μ := (volume : Measure NormalLoopFrequency)) (fun x => normalLoopWeight m x ^ r) t
  exact ⟨hi.congr (Eventually.of_forall (fun x => by simp only [Function.comp_apply,h])),by simpa only [h] using he⟩

theorem normal_product_le_mean_power {r : ℕ} (hr : 0 < r) (f : Fin r → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∏ j, f j ≤ (r:ℝ)⁻¹ * ∑ j, f j ^ r := by
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin r => (r:ℝ)⁻¹) (fun j => f j^r)
    (fun _ _ => by positivity) (by simp [hr']) (fun j _ => pow_nonneg (hf j) _)
  have he (i : Fin r) : (f i ^ r) ^ ((r:ℝ)⁻¹) = f i := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (hf i),mul_inv_cancel₀ hr',Real.rpow_one]
  simpa only [he,Finset.mul_sum] using h

def normalZeroTrace {r : ℕ} (m L : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin r → OSFourSpace) (ξ : ℝ) : ℂ :=
  ((L/(2*Real.pi):ℝ):ℂ) * (List.ofFn (fun j => normalDiracFrequency m (p j) ξ * diracSlash (u j).val)).prod.trace

theorem normal_zero_trace_bound {m L : ℝ} (hm : 0 < m) (hL : 0 < L) {r : ℕ} (hr : 0 < r)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin r → OSFourSpace) (ξ : ℝ) :
    ‖normalZeroTrace m L u p ξ‖ ≤ (L/(2*Real.pi)*4) * ((r:ℝ)⁻¹ * ∑ j, normalLoopWeight m (p j,ξ)^r) := by
  let A := fun j => normalDiracFrequency m (p j) ξ * diracSlash (u j).val
  have hA j : ‖A j‖ ≤ normalLoopWeight m (p j,ξ) := by
    apply (norm_mul_le _ _).trans_eq
    rw [wilson_slash_opnorm,(u j).property,mul_one,normal_dirac_frequency_norm hm]; rfl
  have h := (List.norm_prod_le (List.ofFn A))
  rw [List.map_ofFn,List.prod_ofFn] at h
  have hp := (h.trans (Finset.prod_le_prod (fun j _ => norm_nonneg (A j)) (fun j _ => hA j))).trans
    (normal_product_le_mean_power hr _ (fun j => inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hden : 0 < L/(2*Real.pi) := by positivity
  rw [normalZeroTrace,norm_mul,Complex.norm_real,Real.norm_of_nonneg hden.le,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((wilson_trace_le_opnorm _).trans (mul_le_mul_of_nonneg_left hp (by norm_num))) hden.le

local instance normalFrequencyMatrixSpace : MeasurableSpace DiracMatrix := borel _
local instance normalFrequencyMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_zero_trace_measurable {r : ℕ} {Z : Type*} [MeasurableSpace Z] (m L : ℝ)
    (u : Fin r → UnitVector OSFourSpace) {p : Z → Fin r → OSFourSpace} (hp : ∀ j, Measurable (p · j))
    {ξ : Z → ℝ} (hξ : Measurable ξ) : Measurable (fun z => normalZeroTrace m L u (p z) (ξ z)) := by
  have hN : Continuous (freeDiracNumerator m) := by
    unfold freeDiracNumerator diracSlash
    apply Continuous.add _ continuous_const
    apply continuous_const.smul
    apply continuous_finset_sum
    intro j _
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous).smul continuous_const
  let A := fun j z => normalDiracFrequency m (p z j) (ξ z) * diracSlash (u j).val
  have hA (j) : Measurable (A j) := by
    have h := hN.measurable.comp (hp j)
    unfold A normalDiracFrequency normalFiveDenom
    fun_prop
  have hl (l : List (Fin r)) : Measurable (fun z => (l.map (fun j => A j z)).prod) := by
    induction l with
    | nil => exact measurable_const
    | cons j l ih => exact (hA j).mul ih
  have hP := hl (List.ofFn (fun i : Fin r => i))
  simp only [List.map_ofFn,Function.comp_def] at hP
  exact measurable_const.mul ((Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp hP)

/-- Uniform product estimate on five-dimensional frequency variables. The
same proof applies to counting carrier modes with continuous normal frequency. -/
theorem normal_zero_trace_integral {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (hr : 5 < r)
    (u : Fin r → UnitVector OSFourSpace) (s : Fin r → OSFourSpace) (σ : Measure OSFourSpace) [SFinite σ]
    (B : ℝ) (hB : ∀ y : OSFourSpace, let g := fun x : NormalLoopFrequency => normalLoopWeight m (x.1+y,x.2)^r
      Integrable g (σ.prod volume) ∧ (∫ x, g x ∂σ.prod volume) ≤ B) :
    let F := fun x : NormalLoopFrequency => normalZeroTrace m L u (fun j => x.1+s j) x.2
    Integrable F (σ.prod volume) ∧ (∫ x, ‖F x‖ ∂σ.prod volume) ≤ (L/(2*Real.pi)*4)*B := by
  let K := (L/(2*Real.pi)*4)*(r:ℝ)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let f := fun (j : Fin r) (x : NormalLoopFrequency) => normalLoopWeight m (x.1+s j,x.2)^r
  let F := fun x : NormalLoopFrequency => normalZeroTrace m L u (fun j => x.1+s j) x.2
  have hi := (integrable_finset_sum Finset.univ (fun j _ => (hB (s j)).1)).const_mul K
  have hF : Measurable F := normal_zero_trace_measurable m L u (fun j => measurable_fst.add_const (s j)) measurable_snd
  have hle (x) : ‖F x‖ ≤ K * ∑ j, f j x := by
    simpa only [K,f,mul_assoc] using normal_zero_trace_bound hm hL (by omega : 0 < r) u (fun j => x.1+s j) x.2
  have hI := hi.mono' hF.aestronglyMeasurable (Eventually.of_forall hle)
  refine ⟨hI,(integral_mono hI.norm hi hle).trans ?_⟩
  rw [integral_const_mul,integral_finset_sum _ (fun j _ => (hB (s j)).1)]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
    (fun j _ => (hB (s j)).2)) hK).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,K]
  field_simp [show (r:ℝ) ≠ 0 by positivity]

theorem normal_zero_winding_six {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (hr : 5 < r)
    (u : Fin r → UnitVector OSFourSpace) (s : Fin r → OSFourSpace) :
    let F := fun x : NormalLoopFrequency => normalZeroTrace m L u (fun j => x.1+s j) x.2
    Integrable F ∧ (∫ x, ‖F x‖) ≤ (L/(2*Real.pi)*4) * ∫ x : NormalLoopFrequency, normalLoopWeight m x^r :=
  normal_zero_trace_integral hm hL hr u s volume _ (fun y =>
    ⟨(normal_weight_power_shift hm hr y).1,(normal_weight_power_shift hm hr y).2.le⟩)

end UV
