import UV.ContinueNormalLatticeCells
import UV.ContinuationPoleBoundary

/-! Three observed and one unobserved real momentum coordinate.
The hard Maxwell denominator provides decay along the remaining direction
both in Lebesgue measure and on arbitrarily oriented reciprocal lattices. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped ENNReal

namespace UV

abbrev NormalPhotonChart := OSFourSpace ≃L[ℝ] Spatial × ℝ

def normalPhotonWeight {E : Type*} [Norm E] (r : ℕ) (p : E) : ℝ := ((1+‖p‖)^r)⁻¹

theorem normal_photon_weight_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {r : ℕ} (hr : Module.finrank ℝ E < r) : Integrable (normalPhotonWeight (E := E) r) μ := by
  have hd : (Module.finrank ℝ E : ℝ) < (r:ℝ) := by exact_mod_cast hr
  apply (integrable_one_add_norm (μ := μ) hd).congr
  refine Eventually.of_forall fun x => ?_
  change (1+‖x‖)^(-(r:ℝ)) = ((1+‖x‖)^r)⁻¹
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast]

theorem normal_photon_weight_cell {E : Type*} [SeminormedAddCommGroup E] {R : ℝ} (hR : 0 ≤ R)
    (p x : E) (hx : ‖x‖ ≤ R) (r : ℕ) :
    normalPhotonWeight r p ≤ (1+R)^r * normalPhotonWeight r (p+x) := by
  have hn : 1+‖p+x‖ ≤ (1+R)*(1+‖p‖) := by nlinarith [norm_add_le p x,mul_nonneg hR (norm_nonneg p)]
  dsimp only [normalPhotonWeight]
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),inv_mul_eq_div,div_le_iff₀ (by positivity),←mul_pow]
  exact pow_le_pow_left₀ (by positivity) hn r

def normalPhotonEnvelope (U : NormalPhotonChart) (p : OSFourSpace) : ℝ :=
  normalPhotonWeight 4 (U p).1 * normalPhotonWeight 2 (U p).2

theorem normal_photon_envelope_integrable (U : NormalPhotonChart) : Integrable (normalPhotonEnvelope U) := by
  let μ := (volume : Measure Spatial).prod (volume : Measure ℝ)
  let g := fun t : Spatial × ℝ => normalPhotonWeight 4 t.1 * normalPhotonWeight 2 t.2
  have hg : Measurable g := by dsimp [g,normalPhotonWeight]; fun_prop
  have hi : Integrable g μ :=
    (normal_photon_weight_integrable volume (by rw [finrank_euclideanSpace_fin]; decide : Module.finrank ℝ Spatial < 4)).mul_prod
    (normal_photon_weight_integrable volume (by rw [Module.finrank_self]; decide : Module.finrank ℝ ℝ < 2))
  haveI : IsAddHaarMeasure (volume.map U) := U.isAddHaarMeasure_map volume
  have he := isAddLeftInvariant_eq_smul (volume.map U) μ
  apply (integrable_map_measure hg.aestronglyMeasurable U.continuous.aemeasurable).mp
  rw [he]
  exact hi.smul_measure ENNReal.coe_ne_top

theorem normal_lattice_photon_envelope_integrable (b : NormalReciprocalBasis) (U : NormalPhotonChart) :
    Integrable (normalPhotonEnvelope U) (normalLatticeMeasure b) := by
  obtain ⟨R,hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  let D := ‖U.toContinuousLinearMap‖*max R 0
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) (le_max_right _ _)
  let C := (1+D)^6
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let g := normalPhotonEnvelope U
  have hg : Measurable g := by
    change Measurable (fun p : OSFourSpace => ((1+‖(U p).1‖)^4)⁻¹*((1+‖(U p).2‖)^2)⁻¹)
    fun_prop
  have hn (x) : 0 ≤ g x := by dsimp [g,normalPhotonEnvelope,normalPhotonWeight]; positivity
  have hc (k : NormalReciprocalLattice b) (x) (hx : x ∈ ZSpan.fundamentalDomain b) :
      g k ≤ C*g ((k:OSFourSpace)+x) := by
    have hUx : ‖U x‖ ≤ D := (U.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left ((hR x hx).trans (le_max_left R 0)) (norm_nonneg _))
    have hq := normal_photon_weight_cell hD (U k).1 (U x).1 ((norm_fst_le _).trans hUx) 4
    have ht := normal_photon_weight_cell hD (U k).2 (U x).2 ((norm_snd_le _).trans hUx) 2
    have h := mul_le_mul hq ht (by dsimp [normalPhotonWeight]; positivity) (by dsimp [normalPhotonWeight]; positivity)
    dsimp only [g,normalPhotonEnvelope,C]
    rw [map_add,Prod.fst_add,Prod.snd_add]
    exact h.trans_eq (by ring)
  exact (normal_integral_from_cell_bound (normalLatticeMeasure b) volume hg hn (normal_photon_envelope_integrable U)
    _ (normal_cell_factor_finite b C) (normal_lattice_cell_lintegral b C _ (ENNReal.measurable_ofReal.comp hg)
    (fun k x hx => by rw [←ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal (hc k x hx)))).1

/-- Exact integral of the unobserved direction at nonzero seen momentum. -/
theorem normal_rank_three_maxwell_slice (q : Spatial) (hq : q ≠ 0) :
    (∫ ω : ℝ, (‖q‖^2+ω^2)⁻¹) = Real.pi / ‖q‖ := by
  have hpos := norm_pos_iff.mpr hq
  have h := pole_poisson_scaling (fun _ => 1) hpos
  simp only [mul_one,polePoisson,div_eq_mul_inv] at h
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at h
  simp_rw [add_comm (‖q‖^2)]
  apply (eq_div_iff hpos.ne').mpr
  simpa only [mul_comm] using h

theorem normal_lattice_mode_gap (b : NormalReciprocalBasis) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : NormalReciprocalLattice b, k ≠ 0 → ρ ≤ ‖(k:OSFourSpace)‖ := by
  have ho : IsOpen ({0} : Set (NormalReciprocalLattice b)) := isOpen_discrete _
  obtain ⟨ρ,hρ,hB⟩ := Metric.isOpen_iff.mp ho 0 (by simp)
  refine ⟨ρ,hρ,fun k hk => ?_⟩
  by_contra! hh
  exact hk (hB (show k ∈ Metric.ball 0 ρ by simpa using hh))

end UV
