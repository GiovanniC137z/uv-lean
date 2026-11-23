import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The bounded two-history reflection test for a complete positive tilt on
conditionally independent reflected half histories. -/

noncomputable section
open MeasureTheory Set

namespace UV

def reflectedHistoryWitness {Ω : Type*} (A B : Set Ω) (u : Ω) : ℝ :=
  A.indicator (fun _ => 1) u - B.indicator (fun _ => 1) u

theorem reflected_history_witness_bound {Ω : Type*} (A B : Set Ω) (u : Ω) :
    |reflectedHistoryWitness A B u| ≤ 1 := by
  classical
  by_cases ha : u ∈ A <;> by_cases hb : u ∈ B <;> simp [reflectedHistoryWitness,ha,hb]

theorem reflected_history_expansion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : Ω × Ω → ℝ} (hi : Integrable K (μ.prod μ)) {A B : Set Ω} (ha : MeasurableSet A)
    (hb : MeasurableSet B) :
    (∫ p, K p*reflectedHistoryWitness A B p.1*reflectedHistoryWitness A B p.2 ∂(μ.prod μ)) =
      (∫ p in A ×ˢ A, K p ∂(μ.prod μ)) + (∫ p in B ×ˢ B, K p ∂(μ.prod μ)) -
        (∫ p in A ×ˢ B, K p ∂(μ.prod μ)) - (∫ p in B ×ˢ A, K p ∂(μ.prod μ)) := by
  have he (p : Ω × Ω) : K p*reflectedHistoryWitness A B p.1*reflectedHistoryWitness A B p.2 =
      (A ×ˢ A).indicator K p + (B ×ˢ B).indicator K p - (A ×ˢ B).indicator K p - (B ×ˢ A).indicator K p := by
    classical
    by_cases h₁ : p.1 ∈ A <;> by_cases h₂ : p.1 ∈ B <;> by_cases h₃ : p.2 ∈ A <;> by_cases h₄ : p.2 ∈ B <;>
      simp [reflectedHistoryWitness,Set.indicator,Set.mem_prod,h₁,h₂,h₃,h₄]
  simp_rw [he]
  change (∫ p, (((A ×ˢ A).indicator K + (B ×ˢ B).indicator K - (A ×ˢ B).indicator K - (B ×ˢ A).indicator K) p) ∂(μ.prod μ)) = _
  rw [integral_sub' (((hi.indicator (ha.prod ha)).add (hi.indicator (hb.prod hb))).sub
      (hi.indicator (ha.prod hb))) (hi.indicator (hb.prod ha)),
    integral_sub' ((hi.indicator (ha.prod ha)).add (hi.indicator (hb.prod hb))) (hi.indicator (ha.prod hb)),
    integral_add' (hi.indicator (ha.prod ha)) (hi.indicator (hb.prod hb)),
    integral_indicator (ha.prod ha),integral_indicator (hb.prod hb),integral_indicator (ha.prod hb),integral_indicator (hb.prod ha)]

theorem reflected_history_negative {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {K : Ω × Ω → ℝ} (hi : Integrable K (μ.prod μ)) {A B : Set Ω} (ha : MeasurableSet A)
    (hb : MeasurableSet B) (hm : μ.real B=μ.real A) (hp : 0<μ.real A) {d o : ℝ} (hgap : d<o)
    (hdA : ∀ p ∈ A ×ˢ A, K p≤d) (hdB : ∀ p ∈ B ×ˢ B, K p≤d)
    (hoAB : ∀ p ∈ A ×ˢ B, o≤K p) (hoBA : ∀ p ∈ B ×ˢ A, o≤K p) :
    (∫ p, K p*reflectedHistoryWitness A B p.1*reflectedHistoryWitness A B p.2 ∂(μ.prod μ)) < 0 := by
  rw [reflected_history_expansion μ hi ha hb]
  have up {S T : Set Ω} (hs : MeasurableSet S) (ht : MeasurableSet T) (h : ∀ p ∈ S ×ˢ T, K p≤d) :
      (∫ p in S ×ˢ T, K p ∂(μ.prod μ)) ≤ μ.real S*μ.real T*d := by
    simpa using setIntegral_mono_on hi.integrableOn integrableOn_const (hs.prod ht) h
  have lo {S T : Set Ω} (hs : MeasurableSet S) (ht : MeasurableSet T) (h : ∀ p ∈ S ×ˢ T, o≤K p) :
      μ.real S*μ.real T*o ≤ (∫ p in S ×ˢ T, K p ∂(μ.prod μ)) := by
    simpa using setIntegral_mono_on integrableOn_const hi.integrableOn (hs.prod ht) h
  have h₁ := up ha ha hdA
  have h₂ := up hb hb hdB
  have h₃ := lo ha hb hoAB
  have h₄ := lo hb ha hoBA
  rw [hm] at h₂ h₃ h₄
  linarith only [h₁,h₂,h₃,h₄,mul_lt_mul_of_pos_left hgap (mul_pos hp hp)]

theorem reflected_history_quartic_gap (a b : ℝ) :
    (a+b)^4-(a-b)^4=8*a*b*(a^2+b^2) := by ring

theorem reflected_history_quartic_integral_gap {E : Type*} [TopologicalSpace E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] {χ v w : E → ℝ} (hc : Continuous χ) (hs : HasCompactSupport χ)
    (hv : Continuous v) (hw : Continuous w) (hn : 0 ≤ χ) (hpos : ∃ x, 0<χ x)
    (hvpos : ∀ x, 0<v x) (hwpos : ∀ x, 0<w x) :
    (∫ x, χ x*(v x-w x)^4 ∂μ) < (∫ x, χ x*(v x+w x)^4 ∂μ) := by
  let Vp := fun x => χ x*(v x+w x)^4
  let Vm := fun x => χ x*(v x-w x)^4
  have hcp : Continuous Vp := hc.mul ((hv.add hw).pow 4)
  have hcm : Continuous Vm := hc.mul ((hv.sub hw).pow 4)
  have hsp : HasCompactSupport Vp := hs.mul_right
  have hsm : HasCompactSupport Vm := hs.mul_right
  have hpoint (x : E) : Vp x-Vm x = χ x*(8*v x*w x*((v x)^2+(w x)^2)) := by
    dsimp [Vp,Vm]; rw [←mul_sub,reflected_history_quartic_gap]
  obtain ⟨x,hx⟩ := hpos
  have hi := (hcp.sub hcm).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (hsp.sub hsm)
    (fun y => by change 0≤Vp y-Vm y; rw [hpoint]; exact mul_nonneg (hn y) (by have := hvpos y; have := hwpos y; positivity))
    (x := x) (by rw [hpoint]; have := hvpos x; have := hwpos x; positivity)
  rw [integral_sub (hcp.integrable_of_hasCompactSupport hsp) (hcm.integrable_of_hasCompactSupport hsm)] at hi
  exact sub_pos.mp hi

theorem reflected_history_normalized_tilt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Ω × Ω → ℝ} (hV : Measurable V) (hVn : ∀ p, 0≤V p) {coupling : ℝ} (hc : 0<coupling)
    {A B : Set Ω} (ha : MeasurableSet A) (hb : MeasurableSet B) (hm : μ.real B=μ.real A) (hp : 0<μ.real A)
    {vd vo : ℝ} (hgap : vo < vd)
    (hdA : ∀ p ∈ A ×ˢ A, vd≤V p) (hdB : ∀ p ∈ B ×ˢ B, vd≤V p)
    (hoAB : ∀ p ∈ A ×ˢ B, V p≤vo) (hoBA : ∀ p ∈ B ×ˢ A, V p≤vo) :
    (∫ p, Real.exp (-coupling*V p)*reflectedHistoryWitness A B p.1*reflectedHistoryWitness A B p.2 ∂(μ.prod μ)) /
      (∫ p, Real.exp (-coupling*V p) ∂(μ.prod μ)) < 0 := by
  let K := fun p => Real.exp (-coupling*V p)
  have hi : Integrable K (μ.prod μ) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) ((measurable_const.mul hV).exp.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hVn p))
  have hn := reflected_history_negative μ hi ha hb hm hp
    (d := Real.exp (-coupling*vd)) (o := Real.exp (-coupling*vo))
    (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hgap (neg_lt_zero.mpr hc)))
    (fun p h => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hdA p h) (by linarith)))
    (fun p h => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hdB p h) (by linarith)))
    (fun p h => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hoAB p h) (by linarith)))
    (fun p h => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hoBA p h) (by linarith)))
  have hZ : 0 < ∫ p, K p ∂(μ.prod μ) := by
    apply (integral_pos_iff_support_of_nonneg (fun p => (Real.exp_pos _).le) hi).2
    simp [Function.support]
  exact div_neg_of_neg_of_pos hn hZ

end UV
