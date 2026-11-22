import UV.ContinueNetworkNormalization
import UV.ContinueNetworkTonelli

/-! The manuscript's exact integrated marked-network criterion for independent
visit probes, with the physical coherent vertex integral performed first. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace UV

def networkIndependentCost {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ s : E → ℝ, ∫⁻ q : NetworkVisitSpace n,
    ENNReal.ofReal ((1 / (2 * Real.pi) ^ (4 * n)) *
      ‖networkSharedFourier src dst m z s q‖)
    ∂volume ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))

theorem networkIndependent_momentum_cost {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    (∫⁻ q : NetworkVisitSpace n, ENNReal.ofReal ((1 / (2 * Real.pi) ^ (4 * n)) *
      ‖networkSharedFourier src dst m z s q‖)) = ENNReal.ofReal (networkSharedPrefactor m z s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((networkSharedFourier_momentum_integrable G src dst m z s hG hcover hs).const_mul
      (1 / (2 * Real.pi) ^ (4 * n))) (by exact Filter.Eventually.of_forall (fun q => by positivity)),
    integral_const_mul, networkSharedFourier_momentum_integral G src dst m z s hG hcover hs]

theorem networkIndependentCost_eq_duration {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    networkIndependentCost src dst m z = networkDurationCost m z := by
  unfold networkIndependentCost networkDurationCost
  apply lintegral_congr_ae
  have ha : ∀ᵐ s : E → ℝ ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ))),
      ∀ e, 0 < s e := by
    apply ae_all_iff.mpr
    intro e
    exact (Measure.quasiMeasurePreserving_eval _ e).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ha] with s hs
  exact networkIndependent_momentum_cost G src dst m z s hG hcover hs

/-- Exact source formula, including infinite factors at zero marks. -/
theorem integrated_marked_normal_network {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 ≤ z e) :
    networkIndependentCost src dst m z = ∏ e, networkExtendedGreen (m e) (z e) := by
  rw [networkIndependentCost_eq_duration G src dst m z hG hcover,
    networkDurationCost_extended m z hm hz]

theorem integrated_marked_normal_network_positive {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 < z e) :
    networkIndependentCost src dst m z = ENNReal.ofReal (∏ e,
      ((1 + m e * z e) * Real.exp (-(m e * z e))) / (8 * Real.pi ^ 2 * z e ^ 3)) := by
  rw [networkIndependentCost_eq_duration G src dst m z hG hcover,
    networkDurationCost_positive m z hm hz]
  rfl

theorem integrated_marked_normal_network_zero {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 ≤ z e) (e : E) (he : z e = 0) :
    networkIndependentCost src dst m z = ⊤ := by
  rw [networkIndependentCost_eq_duration G src dst m z hG hcover]
  exact networkDurationCost_zero_mark m z hm hz e he

def networkPositionMarks {E : Type*} {n : ℕ} (src dst : E → Option (Fin n))
    (y : Option (Fin n) → ℝ) : E → ℝ := fun e => |y (dst e) - y (src e)|

theorem integrated_marked_normal_network_common_law {E X : Type*} [Fintype E]
    [MeasurableSpace X] {n : ℕ} (μ : Measure X)
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m : E → ℝ)
    (y : X → Option (Fin n) → ℝ) (hG : G.Connected)
    (hcover : NetworkOrientationCovers G src dst) (hm : ∀ e, 0 < m e) :
    (∫⁻ x, networkIndependentCost src dst m (networkPositionMarks src dst (y x)) ∂μ) =
      ∫⁻ x, ∏ e, networkExtendedGreen (m e) (networkPositionMarks src dst (y x) e) ∂μ := by
  apply lintegral_congr
  intro x
  exact integrated_marked_normal_network G src dst m _ hG hcover hm (fun e => abs_nonneg _)

/-- The exact finiteness test uses one common law for all visit positions. -/
theorem integrated_marked_normal_network_common_law_finite_iff {E X : Type*} [Fintype E]
    [MeasurableSpace X] {n : ℕ} (μ : Measure X)
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m : E → ℝ)
    (y : X → Option (Fin n) → ℝ) (hG : G.Connected)
    (hcover : NetworkOrientationCovers G src dst) (hm : ∀ e, 0 < m e) :
    (∫⁻ x, networkIndependentCost src dst m (networkPositionMarks src dst (y x)) ∂μ) < ⊤ ↔
      (∫⁻ x, ∏ e, networkExtendedGreen (m e) (networkPositionMarks src dst (y x) e) ∂μ) < ⊤ := by
  rw [integrated_marked_normal_network_common_law μ G src dst m y hG hcover hm]

theorem integrated_marked_normal_network_inverse_moment_iff {E : Type*} [Fintype E] {n : ℕ}
    (μ : Measure ℝ) (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (m : E → ℝ) (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (hm : ∀ e, 0 < m e) (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkIndependentCost src dst m (fun _ => r) ∂μ) < ⊤ ↔
      inverseMoment μ ((3 * Fintype.card E : ℕ) : ℝ) < ⊤ := by
  simp_rw [networkIndependentCost_eq_duration G src dst m _ hG hcover]
  exact networkDurationCost_inverse_moment_iff μ m hm hr

/-- Transport the literal alternating closed polygon to any rooted visit
chart. Its position marks are actual differences of those vertex positions. -/
theorem integrated_alternating_polygon_inverse_moment_iff (N : ℕ) {n : ℕ}
    (chart : (Fin (N + 1) × Bool) ≃ Option (Fin n)) (μ : Measure ℝ)
    (G : SimpleGraph (Option (Fin n))) (m : (Fin (N + 1) × Bool) → ℝ)
    (hG : G.Connected)
    (hcover : NetworkOrientationCovers G chart (fun e => chart (alternatingNetworkNext e)))
    (hm : ∀ e, 0 < m e) (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkIndependentCost chart (fun e => chart (alternatingNetworkNext e)) m
      (networkPositionMarks chart (fun e => chart (alternatingNetworkNext e))
        (fun v => alternatingNetworkHeight r (chart.symm v))) ∂μ) < ⊤ ↔
      inverseMoment μ ((6 * (N + 1) : ℕ) : ℝ) < ⊤ := by
  simp_rw [networkIndependentCost_eq_duration G chart
    (fun e => chart (alternatingNetworkNext e)) m _ hG hcover]
  have hmarks (r : ℝ) : networkPositionMarks chart (fun e => chart (alternatingNetworkNext e))
      (fun v => alternatingNetworkHeight r (chart.symm v)) =
        fun v => |alternatingNetworkDisplacement r v| := by
    funext v
    simp [networkPositionMarks, alternatingNetworkDisplacement]
  simp_rw [hmarks]
  exact alternatingNetwork_inverse_moment_iff N μ m hm hr

end UV
