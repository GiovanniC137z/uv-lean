import UV.ContinueVisitNormalPolar
import Mathlib.Analysis.Asymptotics.Defs

/-! A nonzero homogeneous leading normal Taylor profile determines
the exact local inverse-moment threshold, with no assumption that the
profile stays nonzero in every direction. -/

noncomputable section

open MeasureTheory Set Filter Metric Asymptotics Real
open scoped ENNReal Topology

namespace UV.ContinueVisitTaylorDensity

open UV.VerifyVisitCodimension UV.ContinueVisitNormalPolar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def normalTaylorWeight (n : ℕ) (ψ : NormalCoordinates n → F)
    (x : NormalCoordinates n) : ℝ :=
  ‖ψ x‖ ^ (2 : ℕ) / ‖x‖ ^ (2 * (n + 1))

omit [NormedSpace ℝ F] in
private theorem normal_taylor_weight_nonneg (n : ℕ) (ψ : NormalCoordinates n → F)
    (x : NormalCoordinates n) : 0 ≤ normalTaylorWeight n ψ x := by
  unfold normalTaylorWeight
  positivity

private theorem norm_radius_smul_normal_unit {n : ℕ} (u : NormalUnit n)
    (r : PositiveRadius) : ‖(r : ℝ) • (u : NormalCoordinates n)‖ = (r : ℝ) := by
  rw [norm_smul, mem_sphere_zero_iff_norm.mp u.property,
    Real.norm_of_nonneg r.property.le, mul_one]

private theorem taylor_radial_factor (n j : ℕ) (r : PositiveRadius) (c : ℝ) :
    (c * (r : ℝ) ^ j) ^ (2 : ℕ) / (r : ℝ) ^ (2 * (n + 1)) =
      c ^ (2 : ℕ) * (r : ℝ) ^ (2 * (j : ℝ) - 2 * ((n : ℝ) + 1)) := by
  have he : 2 * (j : ℝ) - 2 * ((n : ℝ) + 1) =
      ((j * 2 : ℕ) : ℝ) - ((2 * (n + 1) : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_sub r.property, Real.rpow_natCast, Real.rpow_natCast, pow_mul,
    mul_pow, mul_div_assoc]
  rw [pow_mul]

omit [NormedSpace ℝ F] in
theorem normal_taylor_angular_coefficient_pos (n : ℕ) {P : NormalCoordinates n → F}
    (hP : Continuous P) (hnz : ∃ u : NormalUnit n, P u ≠ 0) :
    0 < ∫ u : NormalUnit n, ‖P u‖ ^ (2 : ℕ) ∂normalSphereMeasure n := by
  let H := fun u : NormalUnit n => ‖P u‖ ^ (2 : ℕ)
  have hc : Continuous H := ((hP.comp continuous_subtype_val).norm.pow _)
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : NormalCoordinates n) 1).bddAbove_image
    ((hP.norm.pow 2).continuousOn)
  have hI : Integrable H (normalSphereMeasure n) :=
    (integrable_const M).mono' hc.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg ‖P u‖)]
      exact hM ⟨u.val, u.property, rfl⟩)
  have hS : IsOpen (Function.support H) := isOpen_ne_fun hc continuous_const
  have hs : (Function.support H).Nonempty := by
    obtain ⟨u, hu⟩ := hnz
    exact ⟨u, pow_ne_zero _ (norm_ne_zero_iff.mpr hu)⟩
  exact (integral_pos_iff_support_of_nonneg (fun u : NormalUnit n => sq_nonneg ‖P u‖) hI).mpr
    (normal_sphere_open_ne_zero n hS hs).bot_lt

/-- If the leading normal Taylor term has positive homogeneous degree
j (or is a nonzero constant at degree zero), the squared-state inverse
moment in every sufficiently small ball exists exactly when 2j>b. -/
theorem normal_taylor_inverse_moment_iff (n j : ℕ) {ψ P : NormalCoordinates n → F}
    (hψ : Continuous ψ) (hP : Continuous P)
    (hhom : ∀ (t : ℝ), 0 < t → ∀ x, P (t • x) = t ^ j • P x)
    (hnz : ∃ u : NormalUnit n, P u ≠ 0)
    (hrem : (fun x => ψ x - P x) =o[𝓝 0] (fun x => ‖x‖ ^ j)) :
    ∃ R > 0, ∀ ρ, 0 < ρ → ρ ≤ R →
      (IntegrableOn (normalTaylorWeight n ψ) (ball 0 ρ) ↔ n + 1 < 2 * j) := by
  obtain ⟨u₀, hu₀⟩ := hnz
  let k := ‖P u₀‖ / 3
  have hk : 0 < k := div_pos (norm_pos_iff.mpr hu₀) (by norm_num)
  have hsmall : ∀ᶠ x in 𝓝 (0 : NormalCoordinates n), ‖ψ x - P x‖ ≤ k * ‖x‖ ^ j := by
    filter_upwards [hrem.bound hk] with x hx
    simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) j)] using hx
  obtain ⟨R, hR, hremR⟩ := Metric.eventually_nhds_iff_ball.mp hsmall
  refine ⟨R, hR, ?_⟩
  intro ρ hρ hρR
  let α : ℝ := 2 * (j : ℝ) - 2 * ((n : ℝ) + 1)
  let f := normalTaylorWeight n ψ
  let g : NormalUnit n × PositiveRadius → ℝ := fun p =>
    if (p.2 : ℝ) < ρ then f ((p.2 : ℝ) • (p.1 : NormalCoordinates n)) else 0
  let U : Set (NormalUnit n) := {u | 2 * k < ‖P u‖}
  have hU : IsOpen U := isOpen_lt continuous_const (hP.comp continuous_subtype_val).norm
  have hUne : U.Nonempty := ⟨u₀, by
    change 2 * (‖P u₀‖ / 3) < ‖P u₀‖
    linarith [norm_pos_iff.mpr hu₀]⟩
  have hμU := normal_sphere_open_ne_zero n hU hUne
  have hgm : Measurable g := by
    unfold g f normalTaylorWeight
    exact Measurable.ite
      (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const)
      (by fun_prop) measurable_const
  have hgn (p : NormalUnit n × PositiveRadius) : 0 ≤ g p := by
    unfold g
    split
    · exact normal_taylor_weight_nonneg n ψ _
    · exact le_rfl
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : NormalCoordinates n) 1).bddAbove_image
    hP.norm.continuousOn
  let C := max M 0 + k
  have hMp (u : NormalUnit n) : ‖P u‖ ≤ max M 0 :=
    (hM ⟨u.val, u.property, rfl⟩).trans (le_max_left _ _)
  have hsub (u : NormalUnit n) (r : PositiveRadius) (hr : (r : ℝ) < ρ) :
      ‖ψ ((r : ℝ) • (u : NormalCoordinates n)) - P ((r : ℝ) • (u : NormalCoordinates n))‖ ≤
        k * (r : ℝ) ^ j := by
    have hb : (r : ℝ) • (u : NormalCoordinates n) ∈ ball (0 : NormalCoordinates n) R := by
      rw [mem_ball, dist_zero_right, norm_radius_smul_normal_unit]
      exact hr.trans_le hρR
    simpa only [norm_radius_smul_normal_unit] using hremR _ hb
  have hPu (u : NormalUnit n) (r : PositiveRadius) :
      ‖P ((r : ℝ) • (u : NormalCoordinates n))‖ = (r : ℝ) ^ j * ‖P u‖ := by
    rw [hhom _ r.property, norm_smul, Real.norm_of_nonneg (pow_nonneg r.property.le _)]
  have hhi (p : NormalUnit n × PositiveRadius) :
      g p ≤ C ^ (2 : ℕ) * radialPower ρ α p.2 := by
    by_cases hp : (p.2 : ℝ) < ρ
    · have ht : ‖ψ ((p.2 : ℝ) • (p.1 : NormalCoordinates n))‖ ≤ C * (p.2 : ℝ) ^ j := by
        calc
          _ = ‖(ψ ((p.2 : ℝ) • (p.1 : NormalCoordinates n)) -
              P ((p.2 : ℝ) • (p.1 : NormalCoordinates n))) +
              P ((p.2 : ℝ) • (p.1 : NormalCoordinates n))‖ := by rw [sub_add_cancel]
          _ ≤ _ + _ := norm_add_le _ _
          _ ≤ k * (p.2 : ℝ) ^ j + (p.2 : ℝ) ^ j * max M 0 :=
            add_le_add (hsub p.1 p.2 hp) (by
              rw [hPu]
              exact mul_le_mul_of_nonneg_left (hMp p.1) (pow_nonneg p.2.property.le _))
          _ = _ := by unfold C; ring
      simp only [g, radialPower, hp, if_true, f, normalTaylorWeight,
        norm_radius_smul_normal_unit]
      rw [← taylor_radial_factor n j p.2 C]
      have hden : 0 ≤ (p.2 : ℝ) ^ (2 * (n + 1)) := pow_nonneg p.2.property.le _
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht _) hden
    · simp [g, radialPower, hp]
  have hlo (u : NormalUnit n) (hu : u ∈ U) (r : PositiveRadius) :
      k ^ (2 : ℕ) * radialPower ρ α r ≤ g (u, r) := by
    by_cases hr : (r : ℝ) < ρ
    · let x := (r : ℝ) • (u : NormalCoordinates n)
      have ht' : ‖P x‖ ≤ ‖ψ x - P x‖ + ‖ψ x‖ := by
        calc
          _ = ‖(P x - ψ x) + ψ x‖ := by rw [sub_add_cancel]
          _ ≤ ‖P x - ψ x‖ + ‖ψ x‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev]
      have ht0 : 2 * k * (r : ℝ) ^ j ≤ ‖P x‖ := by
        rw [hPu, mul_comm ((r : ℝ) ^ j)]
        exact mul_le_mul_of_nonneg_right hu.le (pow_nonneg r.property.le _)
      have ht : k * (r : ℝ) ^ j ≤ ‖ψ x‖ := by
        have hb := hsub u r hr
        change ‖ψ x - P x‖ ≤ _ at hb
        linarith
      simp only [g, radialPower, hr, if_true, f, normalTaylorWeight,
        norm_radius_smul_normal_unit]
      rw [← taylor_radial_factor n j r k]
      have hden : 0 ≤ (r : ℝ) ^ (2 * (n + 1)) := pow_nonneg r.property.le _
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hk.le (pow_nonneg r.property.le _)) ht _) hden
    · simp [g, radialPower, hr]
  rw [normal_polar_integrable_iff]
  change Integrable g _ ↔ _
  have hriff : Integrable (radialPower ρ α) (Measure.volumeIoiPow n) ↔ n + 1 < 2 * j := by
    rw [radial_power_integrable_iff n hρ]
    have hreal : ((n + 1 : ℕ) : ℝ) < ((2 * j : ℕ) : ℝ) ↔ n + 1 < 2 * j := by
      exact_mod_cast (Iff.rfl : n + 1 < 2 * j ↔ n + 1 < 2 * j)
    rw [← hreal]
    push_cast
    unfold α
    constructor <;> intro h <;> linarith
  constructor
  · intro hgi
    have ha := hgi.prod_right_ae
    obtain ⟨u, hu, huI⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμU
      (ae_restrict_of_ae ha)
    apply hriff.mp
    have hki : Integrable (fun r => k ^ (2 : ℕ) * radialPower ρ α r) (Measure.volumeIoiPow n) :=
      huI.mono' ((radial_power_measurable ρ α).const_mul _).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg k) (radial_power_nonneg ρ α r))]
          exact hlo u hu r)
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hk.ne')) _).mp hki
  · intro hJ
    have hI := ((hriff.mpr hJ).const_mul (C ^ (2 : ℕ))).comp_snd (normalSphereMeasure n)
    exact hI.mono' hgm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_of_nonneg (hgn p)]; exact hhi p)

end UV.ContinueVisitTaylorDensity
