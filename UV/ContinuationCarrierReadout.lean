import UV.ContinuationSectorPlane
import Mathlib.Topology.Order.DenselyOrdered

/-! Tests of the carrier readout on a locked sector plane. Spatial
readout directions are unit vectors in the intrinsic three-space. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Plane.branchActionUnit (diamond : Plane E) (ε : Evolution) : UnitVector E :=
  ⟨evolutionSign ε • (diamond.Ghat : E), by
    simp [norm_smul, Real.norm_eq_abs, diamond.Ghat.property]⟩

/-- The running direction has two different one-sided limits. Its value
on the zero-coordinate set cannot supply a continuous normalized unit. -/
theorem Plane.no_continuous_running_unit (diamond : Plane E) (f : ℝ → E)
    (hpos : ∀ t > 0, f t = (diamond.poleUnit : E))
    (hneg : ∀ t < 0, f t = -(diamond.poleUnit : E)) :
    ¬ ContinuousAt f (0 : ℝ) := by
  intro hc
  have hp : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (diamond.poleUnit : E)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpos t ht).symm
  have hn : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 (-(diamond.poleUnit : E))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hneg t ht).symm
  have he := (tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hp).symm.trans
    (tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hn)
  have hz : (diamond.poleUnit : E) = 0 := by
    exact (neg_eq_self ℝ E).mp he.symm
  have h := diamond.poleUnit.property
  rw [hz, norm_zero] at h
  norm_num at h

/-- The standard intrinsic boost of the time component along a specified
unit spatial direction in the carrier-adapted Minkowski readout. -/
def boostFrequency (n : UnitVector Spatial) (v kParallel : ℝ) (k : Spatial) : ℝ :=
  (kParallel - v * ⟪(n : Spatial), k⟫) / Real.sqrt (1 - v ^ 2)

theorem boost_readout_causal_positive (n : UnitVector Spatial) {v kParallel : ℝ}
    (hv : |v| < 1) (hk : 0 < kParallel) (k : Spatial) (hcausal : ‖k‖ ≤ kParallel) :
    0 < boostFrequency n v kParallel k := by
  have hv2 : v ^ 2 < 1 := by
    have h : |v| < |(1 : ℝ)| := by simpa only [abs_one] using hv
    simpa only [one_pow] using (sq_lt_sq).mpr h
  have hdot : |⟪(n : Spatial), k⟫| ≤ ‖k‖ := by
    simpa only [n.property, one_mul] using abs_real_inner_le_norm (n : Spatial) k
  have hmul : v * ⟪(n : Spatial), k⟫ < kParallel := by
    calc
      _ ≤ |v * ⟪(n : Spatial), k⟫| := le_abs_self _
      _ = |v| * |⟪(n : Spatial), k⟫| := abs_mul _ _
      _ ≤ |v| * kParallel := mul_le_mul_of_nonneg_left (hdot.trans hcausal) (abs_nonneg _)
      _ < 1 * kParallel := mul_lt_mul_of_pos_right hv hk
      _ = _ := one_mul _
  exact div_pos (sub_pos.mpr hmul) (Real.sqrt_pos.mpr (sub_pos.mpr hv2))

theorem boost_readout_spacelike_can_reverse (n : UnitVector Spatial)
    {kParallel : ℝ} (k : Spatial) (hk : 0 < kParallel)
    (hdir : kParallel < ⟪(n : Spatial), k⟫) :
    ∃ v : ℝ, 0 < v ∧ v < 1 ∧ boostFrequency n v kParallel k < 0 := by
  let k₁ := ⟪(n : Spatial), k⟫
  have hk₁ : 0 < k₁ := hk.trans hdir
  have hr : kParallel / k₁ < 1 := (div_lt_one hk₁).2 hdir
  let v := (1 + kParallel / k₁) / 2
  have hv : 0 < v := by dsimp [v]; positivity
  have hvl : v < 1 := by dsimp [v]; linarith
  have hl : kParallel < v * k₁ := (div_lt_iff₀ hk₁).1 (by dsimp [v]; linarith)
  have hv2 : v ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hv.le (show 0 ≤ (1 : ℝ) by norm_num)).mpr hvl
  exact ⟨v, hv, hvl, div_neg_of_neg_of_pos (sub_neg.mpr hl)
    (Real.sqrt_pos.mpr (sub_pos.mpr hv2))⟩

end UV.SectorPlane
