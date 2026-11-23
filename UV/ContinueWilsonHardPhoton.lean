import UV.ContinueWilsonRoutedPhoton
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Absolute photon majorants for the unclosed momentum-space Wilson
graph. Chords use the ordinary massless covariance even near zero. The
tree estimate uses the fixed infrared convention only on dependent edges. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

/-- The ordinary Euclidean transverse projector evaluated on two unit
polarizations. The formula at nonzero momentum uses its actual direction. -/
def wilsonTransverseEntry (u v : UnitVector OSFourSpace) (p : OSFourSpace) : ℝ :=
  ⟪u.val,(ℝ ∙ p)ᗮ.starProjection v.val⟫

theorem wilson_transverse_entry_bound (u v : UnitVector OSFourSpace) (p : OSFourSpace) :
    |wilsonTransverseEntry u v p| ≤ 1 := by
  apply (abs_real_inner_le_norm _ _).trans
  rw [u.property,one_mul]
  exact ((ℝ ∙ p)ᗮ.norm_starProjection_apply_le v.val).trans_eq v.property

theorem wilson_transverse_entry_measurable (u v : UnitVector OSFourSpace) : Measurable (wilsonTransverseEntry u v) := by
  change Measurable (fun p => wilsonTransverseEntry u v p)
  simp only [wilsonTransverseEntry,Submodule.starProjection_orthogonal_val,Submodule.starProjection_singleton]
  fun_prop

def wilsonPhotonDensity (χ : OSFourSpace → ℂ) (p : OSFourSpace) : ℝ := ‖χ p‖^2 / ‖p‖^2

theorem wilson_photon_density_nonneg (χ : OSFourSpace → ℂ) (p : OSFourSpace) : 0 ≤ wilsonPhotonDensity χ p :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem wilson_local_maxwell_integrable :
    IntegrableOn (fun p : OSFourSpace => (‖p‖^2)⁻¹) (closedBall 0 1) := by
  rw [←integrable_indicator_iff isClosed_closedBall.measurableSet]
  let f := (Iic (1:ℝ)).indicator (fun r : ℝ => (r^2)⁻¹)
  have he : (closedBall (0:OSFourSpace) 1).indicator (fun p => (‖p‖^2)⁻¹) = fun p => f ‖p‖ := by
    funext p
    by_cases hp : ‖p‖ ≤ 1 <;> simp [f,hp]
  rw [he]
  apply (integrable_fun_norm_addHaar (E := OSFourSpace) volume).mpr
  rw [finrank_euclideanSpace,Fintype.card_fin]
  have hh : (fun r : ℝ => r^(4-1) • f r) =ᵐ[volume.restrict (Ioi (0:ℝ))] (Iic (1:ℝ)).indicator id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hp : r ≠ 0 := (show 0 < r from hr).ne'
    by_cases hb : r ≤ 1
    · simp [f,hb,show (4-1:ℕ)=3 by decide,smul_eq_mul]; field_simp
    · simp [f,hb]
  apply (integrable_congr hh).mpr
  rw [integrable_indicator_iff measurableSet_Iic,IntegrableOn,restrict_restrict measurableSet_Iic]
  exact (continuous_id.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set (fun r hr => ⟨hr.2.le,hr.1⟩)

theorem wilson_actual_maxwell_integrable {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : Integrable (wilsonPhotonDensity (wilsonShellPhotonForm L T)) := by
  let χ := wilsonShellPhotonForm L T
  have hm : Measurable (wilsonPhotonDensity χ) := (wilson_shell_form_continuous L T).norm.measurable.pow_const 2 |>.div (measurable_norm.pow_const 2)
  have hpos (p) := wilson_photon_density_nonneg χ p
  have h₁ : IntegrableOn (wilsonPhotonDensity χ) (closedBall 0 1) := by
    apply wilson_local_maxwell_integrable.mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    rw [Real.norm_of_nonneg (hpos _),wilsonPhotonDensity,div_eq_mul_inv]
    apply mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _))
    simpa using pow_le_pow_left₀ (norm_nonneg _) (wilson_shell_form_le_one L T p) 2
  have h₂ : IntegrableOn (wilsonPhotonDensity χ) (closedBall 0 1)ᶜ := by
    apply (wilson_actual_shell_square_integrable hL T).integrableOn.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with p hp
    have hn : 1 < ‖p‖ := by simpa using hp
    rw [Real.norm_of_nonneg (hpos _),wilsonPhotonDensity]
    exact div_le_self (sq_nonneg _) (one_le_pow₀ hn.le)
  exact (integrableOn_univ.mp (by simpa only [union_compl_self] using h₁.union h₂))

structure WilsonPhotonPolarizations where
  incoming : UnitVector OSFourSpace
  outgoing : UnitVector OSFourSpace

def WilsonPhotonPolarizations.maxwell (e : WilsonPhotonPolarizations) (χ : OSFourSpace → ℂ) (p : OSFourSpace) : ℝ :=
  wilsonTransverseEntry e.incoming e.outgoing p * wilsonPhotonDensity χ p

theorem WilsonPhotonPolarizations.maxwell_measurable (e : WilsonPhotonPolarizations) {χ : OSFourSpace → ℂ} (hχ : Continuous χ) :
    Measurable (e.maxwell χ) :=
  (wilson_transverse_entry_measurable _ _).mul ((hχ.norm.measurable.pow_const 2).div (measurable_norm.pow_const 2))

theorem WilsonPhotonPolarizations.maxwell_bound (e : WilsonPhotonPolarizations) (χ : OSFourSpace → ℂ) (p : OSFourSpace) :
    ‖e.maxwell χ p‖ ≤ wilsonPhotonDensity χ p := by
  rw [maxwell,norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (wilson_photon_density_nonneg _ _)]
  exact mul_le_of_le_one_left (wilson_photon_density_nonneg _ _) (wilson_transverse_entry_bound _ _ _)

def WilsonPhotonPolarizations.hard (e : WilsonPhotonPolarizations) (ρ : ℝ) (χ : OSFourSpace → ℂ) (p : OSFourSpace) : ℝ :=
  if ρ ≤ ‖p‖ then e.maxwell χ p else 0

theorem WilsonPhotonPolarizations.hard_measurable (e : WilsonPhotonPolarizations) (ρ : ℝ)
    {χ : OSFourSpace → ℂ} (hχ : Continuous χ) : Measurable (e.hard ρ χ) :=
  Measurable.ite (measurableSet_le measurable_const measurable_norm) (e.maxwell_measurable hχ) measurable_const

theorem WilsonPhotonPolarizations.hard_bound (e : WilsonPhotonPolarizations) {ρ : ℝ} (hρ : 0 < ρ)
    {χ : OSFourSpace → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) (p : OSFourSpace) : ‖e.hard ρ χ p‖ ≤ (ρ^2)⁻¹ := by
  by_cases hp : ρ ≤ ‖p‖
  · rw [hard,if_pos hp]
    apply (e.maxwell_bound χ p).trans
    rw [wilsonPhotonDensity,div_eq_mul_inv]
    apply (mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (show ‖χ p‖^2 ≤ 1 by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hχ p) 2)).trans
    exact inv_anti₀ (sq_pos_of_pos hρ) (pow_le_pow_left₀ hρ.le hp 2)
  · simp [hard,hp,sq_nonneg]

variable {C D : Type*} [Fintype C] [Fintype D]

/-- Ordinary transverse chord factors and tree factors with the fixed
infrared exclusion. All tree momenta may depend on all independent chords. -/
def wilsonHardPhotonProduct (ρ : ℝ) (χ : OSFourSpace → ℂ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (q : C → OSFourSpace) : ℝ :=
  (∏ i, (chord i).maxwell χ (q i)) * ∏ e, (tree e).hard ρ χ (route q e)

theorem wilson_hard_product_measurable (ρ : ℝ) {χ : OSFourSpace → ℂ} (hχ : Continuous χ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    {route : (C → OSFourSpace) → D → OSFourSpace} (hr : ∀ e, Measurable (route · e)) :
    Measurable (wilsonHardPhotonProduct ρ χ chord tree route) :=
  (Finset.measurable_prod _ (fun i _ => ((chord i).maxwell_measurable hχ).comp (measurable_pi_apply i))).mul
    (Finset.measurable_prod _ (fun e _ => ((tree e).hard_measurable ρ hχ).comp (hr e)))

theorem wilson_hard_product_bound {ρ : ℝ} (hρ : 0 < ρ) {χ : OSFourSpace → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (q : C → OSFourSpace) :
    ‖wilsonHardPhotonProduct ρ χ chord tree route q‖ ≤
      (∏ i, wilsonPhotonDensity χ (q i)) * (ρ^2)⁻¹ ^ Fintype.card D := by
  rw [wilsonHardPhotonProduct,norm_mul,norm_prod,norm_prod]
  apply mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (chord i).maxwell_bound χ _)) _
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (Finset.prod_nonneg (fun _ _ => wilson_photon_density_nonneg _ _))
  simpa only [Finset.prod_const,Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ) (fun e _ => norm_nonneg _) (fun e _ => (tree e).hard_bound hρ hχ (route q e))

theorem wilson_hard_product_integrable {ι : Type*} [Fintype ι] {L ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (chord : C → WilsonPhotonPolarizations)
    (tree : D → WilsonPhotonPolarizations) {route : (C → OSFourSpace) → D → OSFourSpace}
    (hr : ∀ e, Measurable (route · e)) :
    Integrable (wilsonHardPhotonProduct ρ (wilsonShellPhotonForm L T) chord tree route) (Measure.pi (fun _ => volume)) :=
  ((Integrable.fintype_prod (fun _ : C => wilson_actual_maxwell_integrable hL T)).mul_const _).mono'
    (wilson_hard_product_measurable ρ (wilson_shell_form_continuous L T) chord tree hr).aestronglyMeasurable
    (Eventually.of_forall (wilson_hard_product_bound hρ (wilson_shell_form_le_one L T) chord tree route))

end UV
