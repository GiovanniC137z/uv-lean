import UV.ContinueGaugeRootLandauBasis
import UV.UnboundedSourceTransport
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! The full Landau fibre has an actual self-adjoint diagonal generator
on its graph domain, with one normalized state at every oscillator level. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace lp
namespace UV.RootMagnetic

abbrev LandauCountL2 := Lp ℂ 2 (Measure.count : Measure ℕ)

private theorem lpTwo_count_iff (f : ℕ → ℂ) :
    Memℓp f 2 ↔ MemLp f 2 (Measure.count : Measure ℕ) := by
  have hM : StronglyMeasurable f := measurable_of_countable f |>.stronglyMeasurable
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal), memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable]
  have hm : AEStronglyMeasurable (fun n => ‖f n‖^2) (Measure.count : Measure ℕ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have h : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  simp only [h, Real.rpow_two, Integrable, hm, true_and, HasFiniteIntegral,
    Real.enorm_eq_ofReal (sq_nonneg _), lintegral_count]
  refine ⟨fun hs => hs.tsum_ofReal_lt_top, fun ht => ?_⟩
  have hh := ENNReal.summable_toReal ht.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh

private def numberToL2 (f : OpeningFock) : LandauCountL2 :=
  ((lpTwo_count_iff f).mp f.property).toLp f

private theorem numberToL2_apply (f : OpeningFock) (n : ℕ) : numberToL2 f n = f n :=
  Measure.ae_count_iff.mp (MemLp.coeFn_toLp _) n

theorem number_count_unitary :
    ∃ U : OpeningFock ≃ₗᵢ[ℂ] LandauCountL2, ∀ f n, U f n = f n := by
  let L : OpeningFock →ₗᵢ[ℂ] LandauCountL2 := {
    toFun := numberToL2
    map_add' := fun f g => by
      apply Lp.ext
      filter_upwards [Lp.coeFn_add (numberToL2 f) (numberToL2 g)] with x hx
      rw [hx, Pi.add_apply, numberToL2_apply, numberToL2_apply, numberToL2_apply]
      rfl
    map_smul' := fun c f => by
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul c (numberToL2 f)] with x hx
      change numberToL2 (c • f) x = (c • numberToL2 f) x
      rw [hx, Pi.smul_apply, numberToL2_apply, numberToL2_apply]
      rfl
    norm_map' := fun f => by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖numberToL2 f‖^2 = ‖f‖^2
      rw [← integral_norm_sq_lp (numberToL2 f)]
      simp_rw [numberToL2_apply]
      have h := memLp_two_iff_integrable_sq_norm (μ := (Measure.count : Measure ℕ))
        (measurable_of_countable (⇑f)).aestronglyMeasurable |>.mp ((lpTwo_count_iff f).mp f.property)
      rw [integral_countable' h]
      have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
      simpa [Measure.real] using hnorm.symm }
  have hsurj : Function.Surjective L := by
    intro f
    let x : OpeningFock := ⟨⇑f, (lpTwo_count_iff f).mpr (Lp.memLp f)⟩
    refine ⟨x, Lp.ext (Eventually.of_forall fun n => ?_)⟩
    exact numberToL2_apply x n
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, numberToL2_apply⟩

def landauLevel (b : ℝ) (n : ℕ) := (2 * (n : ℝ) + 1) * b

theorem magnetic_fiber_spectral_graph {b : ℝ} (hb : 0 < b) :
    ∃ (B : HilbertBasis ℕ ℂ LebesgueFiber) (H : LebesgueFiber →ₗ.[ℂ] LebesgueFiber),
      IsSelfAdjoint H ∧ (∀ n, ⇑(B n) =ᵐ[volume] normalizedLandauMode b n) ∧
      ∀ f g : LebesgueFiber, (f, g) ∈ H.graph ↔
        ∀ n, ⟪B n, g⟫_ℂ = (landauLevel b n : ℂ) * ⟪B n, f⟫_ℂ := by
  obtain ⟨B, hB⟩ := root_landau_basis hb
  obtain ⟨U, hU⟩ := number_count_unitary
  let V := B.repr.trans U
  let w (n : ℕ) : ℝ := landauLevel b n
  have hw : Measurable w := measurable_of_countable _
  let K := sourceL2Multiplier (Measure.count : Measure ℕ) (fun n => (w n : ℂ))
  let H := sourceUnitaryRealMultiplier (Measure.count : Measure ℕ) V w
  refine ⟨B,H,sourceUnitaryRealMultiplier_selfAdjoint _ V w hw,hB,fun f g => ?_⟩
  have hcomp (v : LebesgueFiber) (n : ℕ) : V v n = ⟪B n,v⟫_ℂ := by
    change U (B.repr v) n = _
    rw [hU, B.repr_apply_apply]
  simp_rw [← hcomp]
  rw [show H = sourceUnitaryConjugate V K from rfl, sourceUnitaryConjugate_graph_mem_iff V K]
  constructor
  · rintro hp n
    obtain ⟨d,hd,hg⟩ := K.mem_graph_iff.mp hp
    change (d : LandauCountL2) = V f at hd
    change K d = V g at hg
    rw [← hg, ← hd]
    exact Measure.ae_count_iff.mp (sourceL2Multiplier_coe _ _ d) n
  · intro hg
    have he : (fun n => (w n : ℂ) * V f n) =ᵐ[Measure.count] ⇑(V g) :=
      Eventually.of_forall (fun n => (hg n).symm)
    have hd : V f ∈ K.domain := (memLp_congr_ae he).mpr (Lp.memLp _)
    refine K.mem_graph_iff.mpr ⟨⟨V f, hd⟩, rfl, Lp.ext ?_⟩
    exact (sourceL2Multiplier_coe _ _ _).trans he

end UV.RootMagnetic
