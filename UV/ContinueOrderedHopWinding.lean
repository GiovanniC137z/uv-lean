import UV.ContinueOrderedHopSlab
import UV.ContinueNormalHolonomyTheta
import UV.ExtendNativeHolonomyDeterminant
import UV.ContinueWilsonGraphHopSum

/-! Spatial windings of a two-band path on the periodic cube of side L.
These are windings of its physical three-space. The scalar Gaussian theta
bound is applied independently to the three Euclidean coordinates. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace UV.SectorPlane

abbrev OrderedHopWinding := Fin 3 → ℤ

def orderedHopLattice (L : ℝ) (w : OrderedHopWinding) : Spatial :=
  WithLp.toLp 2 (fun j => L*(w j:ℝ))

def orderedHopWindingGaussian (c L : ℝ) (y : Spatial) (w : OrderedHopWinding) : ℝ :=
  Real.exp (-c*‖orderedHopLattice L w - y‖^2)

private theorem scalar_winding_summable {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (y : ℝ) :
    Summable (fun j : ℤ => Real.exp (-c*(L*(j:ℝ)-y)^2)) := by
  have h := (UV.ExtendNativeHolonomy.normalWinding_gaussian_summable
    (show 0 < c*L^2/2 by positivity)).mul_left (Real.exp (c*y^2))
  apply h.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro j
  rw [← Real.exp_add,Real.exp_le_exp]
  nlinarith [mul_nonneg (sq_nonneg (L*(j:ℝ)-2*y)) hc.le]

private theorem scalar_winding_uniform {c L : ℝ} (hc : 0 < c) (hL : 1 ≤ L) (y : ℝ) :
    (∑' j : ℤ, Real.exp (-c*(L*(j:ℝ)-y)^2)) ≤ UV.ContinueNormalHolonomy.normalTheta c 0 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let C := c*L^2
  have hC : 0 < C := by unfold C; positivity
  have he (j : ℤ) : -c*(L*(j:ℝ)-y)^2 = -C*((j:ℝ)-y/L)^2 := by unfold C; field_simp
  simp_rw [he]
  change UV.ContinueNormalHolonomy.normalTheta C (y/L) ≤ _
  have ha : UV.ContinueNormalHolonomy.normalTheta C (y/L) ≤ UV.ContinueNormalHolonomy.normalTheta C 0 :=
    sub_nonneg.mp (UV.ContinueNormalHolonomy.relativeNormalTheta_nonnegative hC (y/L))
  apply ha.trans
  unfold UV.ContinueNormalHolonomy.normalTheta
  simp only [sub_zero]
  have hs (c : ℝ) (hc : 0 < c) : Summable (fun j : ℤ => Real.exp (-c*(j:ℝ)^2)) := by
    simpa only [neg_mul] using UV.ExtendNativeHolonomy.normalWinding_gaussian_summable hc
  apply (hs C hC).tsum_le_tsum _ (hs c hc)
  intro j
  apply Real.exp_le_exp.mpr
  have hCL : c ≤ C := by unfold C; nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L+1 by linarith))]
  exact mul_le_mul_of_nonneg_right (neg_le_neg hCL) (sq_nonneg _)

private theorem winding_product (c L : ℝ) (y : Spatial) (w : OrderedHopWinding) :
    orderedHopWindingGaussian c L y w = ∏ j, Real.exp (-c*(L*(w j:ℝ)-y j)^2) := by
  rw [orderedHopWindingGaussian,EuclideanSpace.norm_sq_eq,Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  simp [orderedHopLattice,Real.norm_eq_abs]

theorem orderedHop_winding_summable {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (y : Spatial) :
    Summable (orderedHopWindingGaussian c L y) := by
  change Summable (fun w => orderedHopWindingGaussian c L y w)
  simpa only [winding_product] using UV.wilson_summable_product (V := Fin 3)
    (fun j (k : ℤ) => (Real.exp_pos (-c*(L*(k:ℝ)-y j)^2)).le)
    (fun j => scalar_winding_summable hc hL (y j))

def orderedHopWindingBudget (c : ℝ) : ℝ := (UV.ContinueNormalHolonomy.normalTheta c 0)^3

theorem orderedHop_winding_budget_nonneg (c : ℝ) : 0 ≤ orderedHopWindingBudget c := by
  unfold orderedHopWindingBudget UV.ContinueNormalHolonomy.normalTheta
  exact pow_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le) _

theorem orderedHop_winding_uniform {c L : ℝ} (hc : 0 < c) (hL : 1 ≤ L) (y : Spatial) :
    (∑' w, orderedHopWindingGaussian c L y w) ≤ orderedHopWindingBudget c := by
  classical
  let f := fun (j : Fin 3) (k : ℤ) => Real.exp (-c*(L*(k:ℝ)-y j)^2)
  have hpos : 0 < L := zero_lt_one.trans_le hL
  have hi (j : Fin 3) : Integrable (f j) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [f,Real.norm_of_nonneg (Real.exp_pos _).le] using scalar_winding_summable hc hpos (y j)
  have hpi : Measure.pi (fun _ : Fin 3 => (Measure.count : Measure ℤ)) = Measure.count := by
    apply Measure.ext_of_singleton
    intro w
    rw [← Set.univ_pi_singleton w,Measure.pi_pi,Set.univ_pi_singleton]
    simp
  have hprod := Integrable.fintype_prod hi
  rw [hpi] at hprod
  calc
    _ = ∫ w : OrderedHopWinding, ∏ j, f j (w j) ∂Measure.count := by
      simp_rw [winding_product]; simpa [Measure.real,f] using (integral_countable' hprod).symm
    _ = ∏ j, ∫ k, f j k ∂Measure.count := by rw [← hpi,integral_fintype_prod_eq_prod]
    _ ≤ ∏ _j : Fin 3, UV.ContinueNormalHolonomy.normalTheta c 0 := by
      apply Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (Real.exp_pos _).le)
      intro j _
      rw [integral_countable' (hi j)]
      simpa [Measure.real,f] using scalar_winding_uniform hc hL (y j)
    _ = _ := by simp [orderedHopWindingBudget]

theorem orderedHop_lattice_gap {L : ℝ} (hL : 0 ≤ L) {w : OrderedHopWinding} (hw : w ≠ 0) :
    L ≤ ‖orderedHopLattice L w‖ := by
  have hex : ∃ j, w j ≠ 0 := by
    by_contra! h; exact hw (funext h)
  obtain ⟨j,hj⟩ := hex
  have hz : (1:ℝ) ≤ |(w j:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |w j| from abs_pos.mpr hj)
  have h := PiLp.norm_apply_le (orderedHopLattice L w) j
  change ‖L*(w j:ℝ)‖ ≤ _ at h
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hL] at h
  exact (le_mul_of_one_le_right hL hz).trans h

/-- The sum of all nonzero spatial winding envelopes goes to zero at each
fixed net free displacement, uniformly summable at every large volume. -/
theorem orderedHop_winding_nonzero_tendsto {c : ℝ} (hc : 0 < c) (y : Spatial) :
    Tendsto (fun L : ℝ => ∑' w : OrderedHopWinding, if w=0 then 0 else orderedHopWindingGaussian c L y w)
      atTop (𝓝 0) := by
  let D := orderedHopWindingBudget (c/2)
  have hhalf : 0 < c/2 := by positivity
  have hlim : Tendsto (fun L : ℝ => Real.exp (-(c/2)*(L-‖y‖)^2)*D) atTop (𝓝 0) := by
    have hX : Tendsto (fun L : ℝ => c/2*(L-‖y‖)^2) atTop atTop :=
      (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0) |>.comp (show Tendsto (fun x : ℝ => x-‖y‖) atTop atTop by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-‖y‖) tendsto_id)).const_mul_atTop hhalf
    simpa only [neg_mul,zero_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hX).mul_const D
  apply squeeze_zero' (Eventually.of_forall fun L => tsum_nonneg fun w => by split <;> first | exact le_rfl | exact (Real.exp_pos _).le) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ‖y‖] with L hL hY
  let K := Real.exp (-(c/2)*(L-‖y‖)^2)
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hG := orderedHop_winding_summable hhalf (zero_lt_one.trans_le hL) y
  have hb (w : OrderedHopWinding) : (if w=0 then 0 else orderedHopWindingGaussian c L y w) ≤ K*orderedHopWindingGaussian (c/2) L y w := by
    split
    · exact mul_nonneg hK (Real.exp_pos _).le
    · rename_i hw
      have hgap : L-‖y‖ ≤ ‖orderedHopLattice L w-y‖ := by
        linarith [orderedHop_lattice_gap (zero_le_one.trans hL) hw, norm_sub_norm_le (orderedHopLattice L w) y]
      have hr := pow_le_pow_left₀ (sub_nonneg.mpr hY) hgap 2
      dsimp only [K,orderedHopWindingGaussian]
      rw [←Real.exp_add,Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left hr hhalf.le]
  have hN (w : OrderedHopWinding) : 0 ≤ (if w=0 then 0 else orderedHopWindingGaussian c L y w) := by
    split <;> first | exact le_rfl | exact (Real.exp_pos _).le
  apply ((hG.mul_left K).of_nonneg_of_le hN hb).tsum_le_tsum hb (hG.mul_left K) |>.trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (orderedHop_winding_uniform hhalf hL y) hK

end UV.SectorPlane
