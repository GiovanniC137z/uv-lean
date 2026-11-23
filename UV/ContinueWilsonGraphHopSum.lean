import UV.ContinueWilsonJointTraces
import UV.ContinueWilsonHardPhoton

/-! Joint bounds for the hard Wilson graph at fixed electromagnetic order.
Path fractions, external transfers and chord transfers can enter every hop
shift. Hopping lengths and placements vary independently at each vertex. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped BigOperators

namespace UV

variable {ι V Z : Type*} [Fintype ι] [Fintype V] [MeasurableSpace Z]

def wilsonTraceBudget {a : ℕ} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) : ℝ := 4 * wilsonHeadIntegralBudget L T u * (max 1 (2*L))^a

theorem wilson_trace_budget_nonneg {a : ℕ} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) : 0 ≤ wilsonTraceBudget L T u :=
  mul_nonneg (mul_nonneg (by norm_num) (wilson_head_budget_nonneg L T u)) (pow_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)) _)

abbrev WilsonMarkAllocation (a n : V → ℕ) := (v : V) → Fin (a v) → Fin (n v+1)

def wilsonGraphWord (w : Z → ℂ) (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {a n : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace) (f : WilsonMarkAllocation a n)
    (q : (v : V) → Z → Fin (n v+1) → OSFourSpace) : Z × (V → OSFourSpace) → ℂ :=
  wilsonJointTraces w (fun v z => wilsonAllocatedTrace L T (u v) (f v) (q v z))

theorem wilson_graph_words_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {a n : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace) (f : WilsonMarkAllocation a n)
    {q : (v : V) → Z → Fin (n v+1) → OSFourSpace} (hq : ∀ v j, Measurable (q v · j))
    (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w) (hw : Integrable w μ) :
    let ν := Measure.pi (fun _ : V => (volume : Measure OSFourSpace))
    Integrable (wilsonGraphWord w L T u f q) (μ.prod ν) ∧
      (∫ t, ‖wilsonGraphWord w L T u f q t‖ ∂μ.prod ν) ≤
        (∫ z, ‖w z‖ ∂μ) * ∏ v, wilsonTraceBudget L T (u v) * 2^(n v) := by
  apply wilson_joint_traces_bound μ hmw hw
  · intro v
    exact wilson_allocated_trace_measurable _ _ _ _ (fun j => (hq v j).comp measurable_fst) measurable_snd
  · intro v z
    exact (wilson_charged_trace_absolute_bound hL T (wilsonAssignedHop (u v) (f v) (q v z) 0)
      (wilsonAssignedTail (u v) (f v) (q v z))).1
  · exact fun v z => wilson_allocated_trace_bound hL T (u v) (f v) (q v z)

private theorem wilson_summable_independent_lengths {g : V → ℕ → ℝ} (hg : ∀ v k, 0 ≤ g v k)
    (hs : ∀ v, Summable (g v)) : Summable (fun n : V → ℕ => ∏ v, g v (n v)) := by
  classical
  have he : Measure.pi (fun _ : V => (Measure.count : Measure ℕ)) = Measure.count := by
    apply Measure.ext_of_singleton
    intro n
    rw [←Set.univ_pi_singleton n,Measure.pi_pi,Set.univ_pi_singleton]
    simp
  have hi (v : V) : Integrable (g v) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (hg v _)] using hs v
  have h := Integrable.fintype_prod hi
  rw [he,integrable_count_iff] at h
  simpa only [Real.norm_of_nonneg (Finset.prod_nonneg fun v _ => hg v _)] using h

/-- The sum over every positive length at each charged component and every
placement of its labelled marks, after integrating all charged and outer
variables together. No factorization of their momentum shifts is assumed. -/
theorem wilson_graph_all_lengths_summable [DecidableEq V] {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {a : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace)
    (q : (n : V → ℕ) → WilsonMarkAllocation a n → (v : V) → Z → Fin (n v+1) → OSFourSpace)
    (hq : ∀ n f v j, Measurable (q n f v · j)) (μ : Measure Z) [SFinite μ] {w : Z → ℂ}
    (hmw : Measurable w) (hw : Integrable w μ) :
    Summable (fun n : V → ℕ => (∏ v, lam^(n v+1)) * ∑ f : WilsonMarkAllocation a n,
      ∫ t, ‖wilsonGraphWord w L T u f (q n f) t‖ ∂μ.prod (Measure.pi (fun _ : V => volume))) := by
  classical
  let D := fun v => wilsonTraceBudget L T (u v)
  let g := fun v (k : ℕ) => (lam * D v) * ((2*lam)^k * (1+(k:ℝ))^(a v))
  have hg (v k) : 0 ≤ g v k := by
    have hd := wilson_trace_budget_nonneg L T (u v)
    dsimp [g,D]; positivity
  have hs (v) : Summable (g v) := (wilson_marked_hop_summable (a v) hlam hl).mul_left (lam*D v)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg hlam _)
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)) _
    ((wilson_summable_independent_lengths hg hs).mul_left (∫ z, ‖w z‖ ∂μ))
  intro n
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (WilsonMarkAllocation a n)))
    (fun f _ => (wilson_graph_words_bound hL T u f (hq n f) μ hmw hw).2)
  apply (mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg fun _ _ => pow_nonneg hlam _)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,WilsonMarkAllocation,Fintype.card_pi,
    Finset.prod_const,Fintype.card_fin,Nat.cast_prod,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  calc
    _ = (∫ z, ‖w z‖ ∂μ) * ((∏ v, lam^(n v+1)) * (∏ v, ((n v:ℝ)+1)^(a v)) *
            ∏ v, D v*2^(n v)) := by dsimp only [D]; ring
    _ = _ := by
      rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro v _
      dsimp [g]
      rw [pow_succ,mul_pow]
      ring

end UV
