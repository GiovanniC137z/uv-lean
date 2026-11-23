import UV.ContinueWilsonTimeSpin
import UV.ContinuationSectorPlane
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Prod

/-! The actual pair of independent A4 ball marks, projected onto a
specified unit carrier direction and scaled by the hop length. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Metric Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace UV

variable {ι : Type*} [Fintype ι]

abbrev WilsonBallSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def wilsonBallMeasure (ι : Type*) [Fintype ι] : Measure (WilsonBallSpace ι) :=
  ProbabilityTheory.cond volume (ball 0 1)

instance wilsonBallProbability : IsProbabilityMeasure (wilsonBallMeasure ι) :=
  cond_isProbabilityMeasure_of_finite (measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_ne_top

def wilsonTimeDisplacement (L : ℝ) (u : SectorPlane.UnitVector (WilsonBallSpace ι))
    (y : WilsonBallSpace ι × WilsonBallSpace ι) : ℝ := L * ⟪u.val,y.1+y.2⟫

theorem wilsonTimeDisplacement_continuous (L : ℝ) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) :
    Continuous (wilsonTimeDisplacement L u) := by unfold wilsonTimeDisplacement; fun_prop

def wilsonTimeMarginal (L : ℝ) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) : Measure ℝ :=
  ((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)).map (wilsonTimeDisplacement L u)

theorem wilson_ball_isometry (e : WilsonBallSpace ι ≃ₗᵢ[ℝ] WilsonBallSpace ι) :
    MeasurePreserving e (wilsonBallMeasure ι) (wilsonBallMeasure ι) := by
  refine ⟨e.continuous.measurable,?_⟩
  ext S hS
  rw [Measure.map_apply e.continuous.measurable hS,wilsonBallMeasure,
    cond_apply' (e.continuous.measurable hS),cond_apply' hS]
  have he : e ⁻¹' (ball 0 1 ∩ S) = ball 0 1 ∩ (e ⁻¹' S) := by
    ext x
    simp only [mem_preimage,mem_inter_iff,mem_ball,dist_zero_right,e.norm_map]
  rw [← he,e.measurePreserving.measure_preimage (measurableSet_ball.inter hS).nullMeasurableSet]

theorem wilson_marginal_symmetric (L : ℝ) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) :
    MeasurePreserving (fun s : ℝ => -s) (wilsonTimeMarginal L u) (wilsonTimeMarginal L u) := by
  let e : WilsonBallSpace ι ≃ₗᵢ[ℝ] WilsonBallSpace ι := LinearIsometryEquiv.neg ℝ
  have hp := (wilson_ball_isometry e).prod (wilson_ball_isometry e)
  have hc := (wilsonTimeDisplacement_continuous L u).measurable
  refine ⟨measurable_neg,?_⟩
  rw [wilsonTimeMarginal, Measure.map_map measurable_neg hc]
  have he : (fun s : ℝ => -s) ∘ wilsonTimeDisplacement L u =
      wilsonTimeDisplacement L u ∘ Prod.map e e := by
    funext y
    simp [e,wilsonTimeDisplacement,Function.comp_apply,inner_add_right]
    ring
  rw [he,← Measure.map_map hc hp.measurable,hp.map_eq]

theorem wilson_marginal_band {L : ℝ} (hL : 0 < L) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) :
    ∀ᵐ s ∂wilsonTimeMarginal L u, |s| ≤ 2*L := by
  unfold wilsonTimeMarginal
  apply (ae_map_iff (wilsonTimeDisplacement_continuous L u).measurable.aemeasurable
    (measurableSet_le measurable_abs measurable_const)).mpr
  have hb : ∀ᵐ y ∂wilsonBallMeasure ι, y ∈ ball (0:WilsonBallSpace ι) 1 := ae_cond_mem measurableSet_ball
  filter_upwards [(quasiMeasurePreserving_fst (ν := wilsonBallMeasure ι)).ae hb,
    (quasiMeasurePreserving_snd (μ := wilsonBallMeasure ι)).ae hb] with y hy hy'
  have h₁ : ‖y.1‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy
  have h₂ : ‖y.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy'
  rw [wilsonTimeDisplacement,abs_mul,abs_of_pos hL]
  have hi := abs_real_inner_le_norm u.val (y.1+y.2)
  rw [u.property,one_mul] at hi
  nlinarith [hi.trans (norm_add_le y.1 y.2)]

/-- Every open frequency interval containing an interior displacement
has positive probability. Both marks vary independently on open sets. -/
theorem wilson_marginal_interval_pos {L t c d : ℝ} (hL : 0 < L)
    (u : SectorPlane.UnitVector (WilsonBallSpace ι)) (ht : |t| < 2*L) (hc : c < t) (hd : t < d) :
    0 < wilsonTimeMarginal L u (Ioo c d) := by
  let probe := fun y : WilsonBallSpace ι => 2*L*⟪u.val,y⟫
  let V := ball (0:WilsonBallSpace ι) 1 ∩ probe ⁻¹' Ioo c d
  have hp : Continuous probe := by dsimp [probe]; fun_prop
  have hV : IsOpen V := isOpen_ball.inter (isOpen_Ioo.preimage hp)
  let y := (t/(2*L)) • u.val
  have hyy : y ∈ ball (0:WilsonBallSpace ι) 1 := by
    simp only [y,mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,u.property,mul_one,abs_div,
      abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hL)]
    exact (div_lt_one (by positivity)).mpr ht
  have hpy : probe y = t := by
    simp [probe,y,real_inner_smul_right,real_inner_self_eq_norm_sq,u.property]
    field_simp
  have hv : V.Nonempty := ⟨y,hyy,(show probe y ∈ Ioo c d by rw [hpy]; exact ⟨hc,hd⟩)⟩
  have hmass : 0 < wilsonBallMeasure ι V := by
    rw [wilsonBallMeasure,cond_apply' hV.measurableSet,
      inter_eq_right.mpr (show V ⊆ ball 0 1 from inter_subset_left)]
    exact (mul_ne_zero (ENNReal.inv_ne_zero.mpr measure_ball_ne_top) (hV.measure_pos volume hv).ne').bot_lt
  rw [wilsonTimeMarginal,Measure.map_apply (wilsonTimeDisplacement_continuous L u).measurable measurableSet_Ioo]
  apply (show 0 < ((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)) (V ×ˢ V) by
    rw [Measure.prod_prod]; exact (mul_ne_zero hmass.ne' hmass.ne').bot_lt).trans_le (measure_mono _)
  intro z hz
  change c < L*⟪u.val,z.1+z.2⟫ ∧ L*⟪u.val,z.1+z.2⟫ < d
  rw [inner_add_right,mul_add]
  obtain ⟨⟨_,h₁⟩,⟨_,h₂⟩⟩ := hz
  change c < 2*L*⟪u.val,z.1⟫ ∧ 2*L*⟪u.val,z.1⟫ < d at h₁
  change c < 2*L*⟪u.val,z.2⟫ ∧ 2*L*⟪u.val,z.2⟫ < d at h₂
  constructor <;> linarith

private theorem wilson_unit_projection_quasi (u : SectorPlane.UnitVector (WilsonBallSpace ι)) :
    QuasiMeasurePreserving (fun y : WilsonBallSpace ι => ⟪u.val,y⟫) volume volume := by
  classical
  let v : Set (WilsonBallSpace ι) := {u.val}
  have hv : Orthonormal ℝ (fun x : v => x.val) := by
    constructor
    · intro x
      change ‖x.val‖ = 1
      rw [show x.val = u.val from x.property]
      exact u.property
    · intro x y h
      have hx : x.val = u.val := x.property
      have hy : y.val = u.val := y.property
      exact (h (Subtype.ext (hx.trans hy.symm))).elim
  obtain ⟨s,b,hs,he⟩ := hv.exists_orthonormalBasis_extension
  let i : s := ⟨u.val, hs (by simp [v])⟩
  have hbi : b i = u.val := congrFun he i
  have h := ((Measure.quasiMeasurePreserving_eval (fun _ : s => (volume : Measure ℝ)) i).comp
    (EuclideanSpace.volume_preserving_measurableEquiv s).quasiMeasurePreserving).comp b.measurePreserving_repr.quasiMeasurePreserving
  change QuasiMeasurePreserving (fun y => b.repr y i) volume volume at h
  simpa only [b.repr_apply_apply,hbi] using h

theorem wilson_marginal_absolutely_continuous {L : ℝ} (hL : 0 < L) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) :
    wilsonTimeMarginal L u ≪ volume := by
  have hβ : wilsonBallMeasure ι ≪ volume := cond_absolutelyContinuous
  have hup := wilson_unit_projection_quasi u
  have hs := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hL.ne').comp
    (hup.comp (quasiMeasurePreserving_add (volume : Measure (WilsonBallSpace ι)) volume))
  exact (hs.mono_left (hβ.prod hβ)).absolutelyContinuous

def wilsonShellRestLaw {L : ℝ} (hL : 0 < L) (u : SectorPlane.UnitVector (WilsonBallSpace ι)) : WilsonRestLaw L where
  law := wilsonTimeMarginal L u
  probability := Measure.isProbabilityMeasure_map (wilsonTimeDisplacement_continuous L u).measurable.aemeasurable
  length_pos := hL
  band := wilson_marginal_band hL u
  symmetric := wilson_marginal_symmetric L u
  interior_mass := wilson_marginal_interval_pos (t := 3*L/4) hL u
    (by rw [abs_of_pos (by positivity)]; linarith) (by linarith) (by linarith)

end UV
