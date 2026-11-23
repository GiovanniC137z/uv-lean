import UV.SectorPlaneMassiveSquare
import UV.SectorPlaneStableSquareChart

/-! The two original stable-half lines on the same positive-mass shell
and on the same prescribed side. The smooth chart is used near the shell
and the branch difference is integrated on the rest of momentum space. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.massive_same_side_stable_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε ε h φ φ a b m m f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  obtain ⟨v,U,hv,he,hU,hmatch⟩ := diamond.stable_pair_massive_chart ε ε a b hm
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  let W (h : Height) (q : MassiveMomentum) := P h q ^ 2
  have hW (h : Height) : Continuous (W h) := ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)).pow 2
  have hbare (f : CompactMomentumTest K) : ∃ z, Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z) :=
    ⟨_,diamond.massive_same_side_square_boundary ε hm f.contDiff f.compact_support⟩
  obtain ⟨_,hchart⟩ := compact_momentum_multiplier_distribution K W
    (fun h => (hW h).continuousOn.integrableOn_compact K.isCompact) hbare U hU
  apply diamond.stable_scalar_distribution_of_weighted ε ε K ha hb m m
  intro f
  have hrest := diamond.stable_square_chart_remainder ε ha hb hm v hv.continuous he f.contDiff.continuous f.compact_support
  refine ⟨_, ((hchart f).add hrest).congr fun h => ?_⟩
  let S := diamond.stablePairWeight ε ε a b h
  let w := fun q : MassiveMomentum => shellSquare q.1 q.2
  have hc := diamond.stable_pair_weight_continuous ε ε a b h
  have hU' : Continuous (U (h:ℝ)) := hU.continuous.comp ((continuous_const (y := (h:ℝ))).prodMk continuous_id)
  have hi : Integrable (fun q => f.value q * (U h q * W h q)) :=
    (f.contDiff.continuous.mul (hU'.mul (hW h))).integrable_of_hasCompactSupport f.compact_support.mul_right
  have hj : Integrable (fun q => f.value q * ((S (w q)-S (v (w q))) * W h q)) :=
    (f.contDiff.continuous.mul (((hc.comp shellSquare_continuous).sub (hc.comp (hv.continuous.comp shellSquare_continuous))).mul
      (hW h))).integrable_of_hasCompactSupport f.compact_support.mul_right
  change (∫ q, f.value q * (U h q * W h q)) + (∫ q, f.value q * ((S (w q)-S (v (w q))) * W h q)) = _
  rw [← integral_add hi hj]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only [W,P,S,w]
  rw [hmatch]
  ring

end UV.SectorPlane
