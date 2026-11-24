import UV.ContinueTwoBandDensityTrace
import UV.ContinueTwoBandRelativeWord

/-! The independently hard Coulomb frequency of the literal two-density
word. The frequency shift in the original routing is retained. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.SectorPlane

theorem twoBand_coulomb_frequency_not_integrable {m w η : ℝ}
    (hm : 0 < m) (hw : w ≠ 0) (hη : 0 < η) (v : ℝ) :
    ¬ Integrable (fun ξ : ℝ => twoBandRelativeBubble m v w ξ η) := by
  intro hi
  let C := 2*η*w^2/((η^2+m^2)*(η^2+m^2+w^2))
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (mul_pos (by norm_num) hη) (sq_pos_of_ne_zero hw)) (by positivity)
  have hD : 0 < C/2 := half_pos hC
  have ht := (twoBand_coulomb_scaled_limit hm v w η).1
  obtain ⟨R,hR⟩ := eventually_atTop.mp (ht (Ioi_mem_nhds (half_lt_self hC)))
  let a := max R 1
  have hI : IntegrableOn (fun ξ : ℝ => (C/2)⁻¹ * |twoBandRelativeBubble m v w ξ η|) (Ioi a) := by
    simpa only [Real.norm_eq_abs] using (hi.norm.const_mul (C/2)⁻¹).integrableOn
  apply not_IntegrableOn_Ioi_inv (a := a)
  apply hI.mono' measurable_inv.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hx : 0 < ξ := (zero_lt_one.trans_le (le_max_right R 1)).trans hξ
  have hLower : C/2 ≤ ξ * |twoBandRelativeBubble m v w ξ η| :=
    (hR ξ ((le_max_left R 1).trans hξ.le)).le.trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) hx.le)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), ← one_div,
    show (C/2)⁻¹ * |twoBandRelativeBubble m v w ξ η| =
      |twoBandRelativeBubble m v w ξ η| / (C/2) by ring]
  exact (div_le_div_iff₀ hx hD).mpr (by simpa only [one_mul,mul_comm] using hLower)

def twoBandCoulombMultiplier (charge a : ℝ) (p : Spatial) : ℝ :=
  charge^2 * Real.exp (-(2*a*‖p‖)) / ‖p‖^2

theorem twoBand_coulomb_multiplier_pos {charge a : ℝ} (hq : charge ≠ 0) {p : Spatial} (hp : p ≠ 0) :
    0 < twoBandCoulombMultiplier charge a p := by
  unfold twoBandCoulombMultiplier
  exact div_pos (mul_pos (sq_pos_of_ne_zero hq) (Real.exp_pos _)) (sq_pos_of_pos (norm_pos_iff.mpr hp))

def twoBandCoulombIntegrand (m g σ charge a : ℝ) (Ω η : ℝ) (k p : Spatial) : ℝ :=
  twoBandCoulombMultiplier charge a p *
    twoBandRelativeBubble m (twoBandSpatialHop g σ (k+p)) (twoBandSpatialHop g σ k) (Ω+η) η

/-- At each strictly positive fixed charged frequency and each nonzero
spatial transfer, the literal Coulomb-frequency section has a divergent
absolute integral. The statement also applies to discrete spatial momenta. -/
theorem twoBand_coulomb_section_not_integrable {m g σ charge a : ℝ}
    (hm : 0 < m) (hg : g ≠ 0) (hq : charge ≠ 0) {η : ℝ} (hη : 0 < η)
    (k : Spatial) {p : Spatial} (hp : p ≠ 0) :
    ¬ Integrable (fun Ω : ℝ => twoBandCoulombIntegrand m g σ charge a Ω η k p) := by
  intro hi
  let C := twoBandCoulombMultiplier charge a p
  have hC : 0 < C := twoBand_coulomb_multiplier_pos hq hp
  have ht : twoBandSpatialHop g σ k ≠ 0 :=
    mul_ne_zero hg (Real.exp_pos _).ne'
  apply twoBand_coulomb_frequency_not_integrable hm ht hη (twoBandSpatialHop g σ (k+p))
  apply ((measurePreserving_add_right (volume : Measure ℝ) η).integrable_comp_emb
    (Homeomorph.addRight η).measurableEmbedding).1
  have he (Ω : ℝ) : C⁻¹ * twoBandCoulombIntegrand m g σ charge a Ω η k p =
      twoBandRelativeBubble m (twoBandSpatialHop g σ (k+p)) (twoBandSpatialHop g σ k) (Ω+η) η := by
    change C⁻¹ * (C * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  exact (hi.const_mul C⁻¹).congr (ae_of_all _ he)

/-- The four-momentum routing that adds the instantaneous Coulomb line
to the completed density bubble fails absolute integrability even with
positive spatial damping. -/
theorem twoBand_coulomb_routing_not_integrable {m g σ charge a : ℝ}
    (hm : 0 < m) (hg : g ≠ 0) (hq : charge ≠ 0) :
    ¬ Integrable (fun u : ℝ × (ℝ × (Spatial × Spatial)) =>
      twoBandCoulombIntegrand m g σ charge a u.1 u.2.1 u.2.2.1 u.2.2.2) := by
  intro hi
  let U : Set (ℝ × (Spatial × Spatial)) := Ioi 0 ×ˢ (univ ×ˢ ({(0:Spatial)}ᶜ))
  let p := EuclideanSpace.single (0 : Fin 3) (1:ℝ)
  have hp : p ≠ 0 := by
    have hn : ‖p‖ = 1 := by simp [p]
    intro h
    simp [h] at hn
  have hPos : 0 < volume U := by
    change 0 < ((volume : Measure ℝ).prod ((volume : Measure Spatial).prod volume)) U
    unfold U
    rw [Measure.prod_prod, Measure.prod_prod]
    exact ENNReal.mul_pos_iff.mpr ⟨isOpen_Ioi.measure_pos volume ⟨(1:ℝ), mem_Ioi.mpr zero_lt_one⟩,
      ENNReal.mul_pos_iff.mpr ⟨isOpen_univ.measure_pos volume ⟨(0:Spatial), mem_univ _⟩,
        isClosed_singleton.isOpen_compl.measure_pos volume ⟨p, hp⟩⟩⟩
  have hAE : ∀ᵐ r : ℝ × (Spatial × Spatial) ∂volume, r ∉ U := by
    filter_upwards [hi.prod_left_ae] with r hSection hr
    have hη : 0 < r.1 := hr.1
    have hp : r.2.2 ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hr.2.2
    exact twoBand_coulomb_section_not_integrable hm hg hq hη r.2.1 hp hSection
  have hZero : volume U = 0 := by simpa only [ae_iff, not_not, setOf_mem_eq] using hAE
  exact hPos.ne' hZero

end UV.SectorPlane
