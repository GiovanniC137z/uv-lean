import UV.ContinueCarrierConeIsotropy
import UV.ContinueConeTensorLimit

/-! The individual spatial and mixed components of the unweighted
quadratic pole square on compact radial four-momentum tests. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter Real
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.cone_spatial_components (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0) (i j : Fin 3) :
    (∫ q : ℝ × Spatial, (q.2 i * q.2 j) • (φ (coneEuclideanRadius q) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2)) =
      if i = j then diamond.coneQuadraticPairing ε h 0 (1 / 3) φ else 0 := by
  let G (q : ℝ × ℝ) := φ (sqrt (q.1 ^ 2 + q.2 ^ 2)) •
    (diamond.poleCoefficient ε h (q.1 ^ 2 - q.2 ^ 2)) ^ 2
  have hIso := cone_compact_spatial_tensor (G := G)
    (diamond.cone_square_integrand_continuous ε h hc)
    (diamond.cone_square_integrand_compactSupport ε h hs) i j
  change (∫ q : ℝ × Spatial, (q.2 i * q.2 j) • G (q.1, ‖q.2‖)) = _
  rw [hIso]
  by_cases hij : i = j
  · simp only [if_pos hij, Plane.coneQuadraticPairing, zero_mul, zero_add]
    rw [← integral_smul]
    apply integral_congr_ae
    refine Eventually.of_forall fun q => ?_
    simp only [G, coneEuclideanRadius, shellSquare, smul_smul]
    congr 1
    ring
  · simp only [if_neg hij]

theorem Plane.cone_mixed_components (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0) (j : Fin 3) :
    (∫ q : ℝ × Spatial, (q.1 * q.2 j) • (φ (coneEuclideanRadius q) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2)) = 0 := by
  let G (q : ℝ × ℝ) := φ (sqrt (q.1 ^ 2 + q.2 ^ 2)) •
    (diamond.poleCoefficient ε h (q.1 ^ 2 - q.2 ^ 2)) ^ 2
  exact cone_compact_time_spatial (G := G)
    (diamond.cone_square_integrand_continuous ε h hc)
    (diamond.cone_square_integrand_compactSupport ε h hs) j

theorem Plane.cone_spatial_components_limit (diamond : Plane E) (ε : Evolution)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R) (hs : ∀ r > R, φ r = 0)
    (i j : Fin 3) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, (q.2 i * q.2 j) •
      (φ (coneEuclideanRadius q) • (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (if i = j then (2 * π ^ 2 : ℝ) • ((∫ r in Ioi (0 : ℝ), r * φ r) •
        ((1 + 2 * Complex.I * (diamond.eta ε : ℂ)) / 6)) else 0)) := by
  by_cases hij : i = j
  · simp only [if_pos hij]
    refine (diamond.cone_one_third_spatial_radial_limit ε hc hR hs).congr fun h => ?_
    rw [diamond.cone_spatial_components ε h hc hs i j, if_pos hij]
  · simp only [if_neg hij]
    refine tendsto_const_nhds.congr fun h => ?_
    rw [diamond.cone_spatial_components ε h hc hs i j, if_neg hij]

end UV.SectorPlane
