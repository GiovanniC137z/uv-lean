import UV.ContinueOrderedHopWinding

/-! Nonzero physical spatial windings disappear in the density limit,
even with any fixed polynomial cost in count and true lifted path length.
The closing step is kept in that length and in the product density. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace UV.SectorPlane

variable {n : ℕ}

def orderedHopWindClose (L : ℝ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) : OrderedHopStep :=
  ((orderedHopClosingStep d).1, orderedHopLattice L w + (orderedHopClosingStep d).2)

def orderedHopWindLength (L : ℝ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) : ℝ :=
  orderedHopLength (orderedHopWindClose L w d) + ∑ j, orderedHopLength (d j)

def orderedHopWindCost (m σ g L : ℝ) (a b : ℕ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) : ℝ :=
  |g|^(n+1)*(1+(n:ℝ))^a*(1+orderedHopWindLength L w d)^b *
    (orderedHopDensity m σ (orderedHopWindClose L w d) * ∏ j, orderedHopDensity m σ (d j))

theorem orderedHop_wind_zero (L : ℝ) (d : Fin n → OrderedHopStep) :
    orderedHopWindClose L 0 d = orderedHopClosingStep d := by
  have h : orderedHopLattice L 0 = 0 := by ext j; simp [orderedHopLattice]
  simp [orderedHopWindClose,h]

theorem orderedHop_zero_winding_density (m σ g L : ℝ) (a b : ℕ) (d : Fin n → OrderedHopStep) :
    orderedHopWindCost m σ g L a b 0 d = orderedHopPathEnvelope m σ g a b d := by
  simp only [orderedHopWindCost,orderedHopWindLength,orderedHop_wind_zero,orderedHopPathEnvelope,
    orderedHopReturnDensity,orderedHopPathLength]
  ring

theorem orderedHop_wind_length_nonneg (L : ℝ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) :
    0 ≤ orderedHopWindLength L w d := add_nonneg (orderedHop_length_nonneg _)
      (Finset.sum_nonneg fun _ _ => orderedHop_length_nonneg _)

theorem orderedHop_wind_cost_nonneg {σ : ℝ} (hσ : 0 < σ) (m g L : ℝ) (a b : ℕ)
    (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) : 0 ≤ orderedHopWindCost m σ g L a b w d := by
  have hlen := orderedHop_wind_length_nonneg L w d
  have hcl := orderedHop_density_nonneg hσ m (orderedHopWindClose L w d)
  have hp : 0 ≤ ∏ j, orderedHopDensity m σ (d j) := Finset.prod_nonneg fun _ _ => orderedHop_density_nonneg hσ _ _
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg g) _)
    (pow_nonneg (by positivity) _)) (pow_nonneg (by linarith) _)) (mul_nonneg hcl hp)

@[fun_prop] theorem orderedHop_wind_close_cont (L : ℝ) (w : OrderedHopWinding) :
    Continuous (orderedHopWindClose (n := n) L w) := by unfold orderedHopWindClose; fun_prop

@[fun_prop] theorem orderedHop_wind_length_cont (L : ℝ) (w : OrderedHopWinding) :
    Continuous (orderedHopWindLength (n := n) L w) := by unfold orderedHopWindLength; fun_prop

@[fun_prop] theorem orderedHop_wind_cost_cont (m σ g L : ℝ) (a b : ℕ) (w : OrderedHopWinding) :
    Continuous (orderedHopWindCost (n := n) m σ g L a b w) := by unfold orderedHopWindCost; fun_prop

theorem orderedHop_wind_length_gap {L : ℝ} (hL : 0 ≤ L) {w : OrderedHopWinding} (hw : w ≠ 0)
    (d : Fin n → OrderedHopStep) : L ≤ orderedHopWindLength L w d := by
  let z := ∑ j, (d j).2
  have he : (orderedHopWindClose L w d).2 + z = orderedHopLattice L w := by
    simp [orderedHopWindClose,orderedHopClosingStep,z,Prod.snd_sum]
  have hz : ‖z‖ ≤ ∑ j, orderedHopLength (d j) := (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (abs_nonneg (d j).1))
  apply (orderedHop_lattice_gap hL hw).trans
  rw [← he]
  exact (norm_add_le _ _).trans (add_le_add (le_add_of_nonneg_left (abs_nonneg _)) hz)

private def freeTilt (m σ g η : ℝ) (a : ℕ) (d : Fin n → OrderedHopStep) : ℝ :=
  |g|^(n+1)*(1+(n:ℝ))^a * ∏ j, orderedHopTiltMajorant m σ η (d j)

private theorem free_nonneg {σ : ℝ} (hσ : 0 < σ) (m g η : ℝ) (a : ℕ) (d : Fin n → OrderedHopStep) :
    0 ≤ freeTilt m σ g η a d := by
  have hp := Finset.prod_nonneg (s := Finset.univ) (fun j _ => orderedHop_tilt_majorant_nonneg hσ m η (d j))
  unfold freeTilt; positivity

private theorem free_integrable {m σ η : ℝ} (hσ : 0 < σ) (hm : η < m) (ha : η < orderedHopPrecision σ)
    (g : ℝ) (a n : ℕ) : Integrable (freeTilt (n := n) m σ g η a) := by
  rw [volume_pi]
  exact (Integrable.fintype_prod (fun _ : Fin n => orderedHop_tilt_majorant_integrable hσ hm ha)).const_mul _

private theorem free_summable {m σ g η : ℝ} (hσ : 0 < σ) (hm : η < m) (ha : η < orderedHopPrecision σ)
    (hsmall : |g| * orderedHopTiltMass m σ η < 1) (a : ℕ) :
    Summable (fun n : ℕ => ∫ d, freeTilt (n := n) m σ g η a d) := by
  let r := |g| * orderedHopTiltMass m σ η
  have hM : 0 ≤ orderedHopTiltMass m σ η := by
    unfold orderedHopTiltMass
    exact mul_nonneg (div_nonneg (by norm_num) (sub_pos.mpr hm).le)
      (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) (orderedHop_gaussian_mass_pos (sub_pos.mpr ha)).le)
  have hr : 0 ≤ r := mul_nonneg (abs_nonneg _) hM
  have hs := UV.wilson_marked_hop_summable a (show 0 ≤ r/2 by positivity) (show 2*(r/2)<1 by linarith)
  rw [show 2*(r/2) = r by ring] at hs
  apply (hs.mul_left |g|).congr
  intro n
  unfold freeTilt
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow,Fintype.card_fin,orderedHop_tilt_majorant_integral hm ha]
  unfold r
  rw [mul_pow,pow_succ]
  ring

private theorem winding_tilt_bound {m σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hm : η < m)
    (L : ℝ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) :
    (orderedHopDensity m σ (orderedHopWindClose L w d) * ∏ j, orderedHopDensity m σ (d j)) *
      Real.exp (η*orderedHopWindLength L w d) ≤
      orderedHopTiltPeak σ η * orderedHopWindingGaussian (orderedHopPrecision σ-η) L (-(orderedHopClosingStep d).2) w *
        ∏ j, orderedHopTiltMajorant m σ η (d j) := by
  let cl := orderedHopWindClose L w d
  have hc := orderedHop_tilt_le_majorant hσ hη.le m cl
  have htime : Real.exp (-(m-η)*|cl.1|) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sub_nonneg.mpr hm.le)) (abs_nonneg _))
  let G := orderedHopWindingGaussian (orderedHopPrecision σ-η) L (-(orderedHopClosingStep d).2) w
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hC : orderedHopTiltMajorant m σ η cl ≤ orderedHopTiltPeak σ η * G := by
    unfold orderedHopTiltMajorant
    have he : Real.exp (-(orderedHopPrecision σ-η)*‖cl.2‖^2) = G := by
      simp [G,cl,orderedHopWindingGaussian,orderedHopWindClose]
    rw [he]
    exact mul_le_of_le_one_left (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) hG) htime
  unfold orderedHopWindLength
  rw [mul_add,Real.exp_add,Finset.mul_sum,Real.exp_sum]
  calc
    _ = (orderedHopDensity m σ cl * Real.exp (η*orderedHopLength cl)) *
      ∏ j, (orderedHopDensity m σ (d j) * Real.exp (η*orderedHopLength (d j))) := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ _ := mul_le_mul (hc.trans hC)
      (Finset.prod_le_prod (fun j _ => mul_nonneg (orderedHop_density_nonneg hσ _ _) (Real.exp_pos _).le)
        (fun j _ => orderedHop_tilt_le_majorant hσ hη.le m _))
      (Finset.prod_nonneg fun j _ => mul_nonneg (orderedHop_density_nonneg hσ _ _) (Real.exp_pos _).le)
      (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) hG)

private theorem marked_winding_bound {m σ g η L : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hm : η < m)
    (hL : 0 ≤ L) (a b : ℕ) {w : OrderedHopWinding} (hw : w ≠ 0) (d : Fin n → OrderedHopStep) :
    orderedHopWindCost m σ g L a b w d ≤
      (Real.exp (-(η/2)*L) * (orderedHopMomentConstant (η/2) b * orderedHopTiltPeak σ η) * freeTilt m σ g η a d) *
        orderedHopWindingGaussian (orderedHopPrecision σ-η) L (-(orderedHopClosingStep d).2) w := by
  let len := orderedHopWindLength L w d
  let c := orderedHopMomentConstant (η/2) b
  let p := orderedHopDensity m σ (orderedHopWindClose L w d) * ∏ j, orderedHopDensity m σ (d j)
  let N := |g|^(n+1)*(1+(n:ℝ))^a
  have hN : 0 ≤ N := by unfold N; positivity
  have hp : 0 ≤ p := mul_nonneg (orderedHop_density_nonneg hσ _ _) (Finset.prod_nonneg fun _ _ => orderedHop_density_nonneg hσ _ _)
  have hc : 0 ≤ c := by unfold c orderedHopMomentConstant; positivity
  have hlen : L ≤ len := orderedHop_wind_length_gap hL hw d
  have hpoly := orderedHop_nonneg_power_bound (show 0 < η/2 by positivity) (orderedHop_wind_length_nonneg L w d) b
  have he : Real.exp (η/2*len) ≤ Real.exp (-(η/2)*L)*Real.exp (η*len) := by
    rw [←Real.exp_add,Real.exp_le_exp]; nlinarith [mul_le_mul_of_nonneg_left hlen hη.le]
  calc
    _ = N*((1+len)^b*p) := by unfold orderedHopWindCost N p len; ring
    _ ≤ N*((c*(Real.exp (-(η/2)*L)*Real.exp (η*len)))*p) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hpoly.trans (mul_le_mul_of_nonneg_left he hc)) hp) hN
    _ = (N*c*Real.exp (-(η/2)*L))*(p*Real.exp (η*len)) := by ring
    _ ≤ _ := by
      apply (mul_le_mul_of_nonneg_left (winding_tilt_bound hσ hη hm L w d)
        (show 0 ≤ N*c*Real.exp (-(η/2)*L) by positivity)).trans_eq
      unfold N c freeTilt
      ring

def orderedHopWindRemainder (m σ g L : ℝ) (a b : ℕ) (d : Fin n → OrderedHopStep) : ℝ :=
  ∑' w : OrderedHopWinding, if w=0 then 0 else orderedHopWindCost m σ g L a b w d

private theorem winding_remainder_nonneg {σ : ℝ} (hσ : 0 < σ) (m g L : ℝ) (a b : ℕ)
    (d : Fin n → OrderedHopStep) : 0 ≤ orderedHopWindRemainder m σ g L a b d :=
  tsum_nonneg fun w => by split <;> first | exact le_rfl | exact orderedHop_wind_cost_nonneg hσ _ _ _ _ _ _ _

private theorem winding_remainder_measurable {σ : ℝ} (hσ : 0 < σ) (m g L : ℝ) (a b n : ℕ) :
    Measurable (orderedHopWindRemainder (n := n) m σ g L a b) := by
  let f := fun (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) => if w=0 then 0 else orderedHopWindCost m σ g L a b w d
  have h (w) : Measurable (f w) := by
    by_cases hw : w=0
    · simp only [f,hw,↓reduceIte]; exact measurable_const
    · simp only [f,hw,↓reduceIte]; exact (orderedHop_wind_cost_cont _ _ _ _ _ _ _).measurable
  have hn (w d) : 0 ≤ f w d := by dsimp only [f]; split <;> first | exact le_rfl | exact orderedHop_wind_cost_nonneg hσ _ _ _ _ _ _ _
  have ht := (Measurable.nnreal_tsum (fun w => (h w).real_toNNReal)).coe_nnreal_real
  convert ht using 1
  ext d
  simp only [NNReal.coe_tsum,Real.coe_toNNReal _ (hn _ _)]
  rfl

private theorem winding_remainder_bound {m σ g η L : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hm : η < m)
    (ha : η < orderedHopPrecision σ) (hL : 1 ≤ L) (a b : ℕ) (d : Fin n → OrderedHopStep) :
    Summable (fun w : OrderedHopWinding => if w=0 then 0 else orderedHopWindCost m σ g L a b w d) ∧
    orderedHopWindRemainder m σ g L a b d ≤ Real.exp (-(η/2)*L) *
      (orderedHopMomentConstant (η/2) b * orderedHopTiltPeak σ η * orderedHopWindingBudget (orderedHopPrecision σ-η)) *
      freeTilt m σ g η a d := by
  let K := Real.exp (-(η/2)*L) * (orderedHopMomentConstant (η/2) b * orderedHopTiltPeak σ η) * freeTilt m σ g η a d
  have hM : 0 ≤ orderedHopMomentConstant (η/2) b := by unfold orderedHopMomentConstant; positivity
  have hP := orderedHop_tilt_peak_nonneg hσ η
  have hF := free_nonneg hσ m g η a d
  have hK : 0 ≤ K := by unfold K; positivity
  let G := orderedHopWindingGaussian (orderedHopPrecision σ-η) L (-(orderedHopClosingStep d).2)
  have hG : Summable G := orderedHop_winding_summable (sub_pos.mpr ha) (zero_lt_one.trans_le hL) _
  have hle (w : OrderedHopWinding) : (if w=0 then 0 else orderedHopWindCost m σ g L a b w d) ≤ K*G w := by
    split
    · exact mul_nonneg hK (Real.exp_pos _).le
    · exact marked_winding_bound hσ hη hm (zero_le_one.trans hL) a b (by assumption) d
  have hN (w : OrderedHopWinding) : 0 ≤ (if w=0 then 0 else orderedHopWindCost m σ g L a b w d) := by
    split <;> first | exact le_rfl | exact orderedHop_wind_cost_nonneg hσ _ _ _ _ _ _ _
  refine ⟨(hG.mul_left K).of_nonneg_of_le hN hle,?_⟩
  unfold orderedHopWindRemainder
  apply (((hG.mul_left K).of_nonneg_of_le hN hle).tsum_le_tsum hle (hG.mul_left K)).trans
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left (orderedHop_winding_uniform (sub_pos.mpr ha) hL _) hK).trans_eq
  unfold K
  ring

theorem orderedHop_nonzero_cost_summable {m σ g L : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (hL : 1 ≤ L)
    (a b : ℕ) (d : Fin n → OrderedHopStep) :
    Summable (fun w : OrderedHopWinding => if w=0 then 0 else orderedHopWindCost m σ g L a b w d) := by
  obtain ⟨η,hη,hm,ha,_⟩ := orderedHop_has_summable_tilt hσ hg
  exact (winding_remainder_bound hσ hη hm ha hL a b d).1

/-- The absolute sum of all lifted nonzero-winding polynomially marked
return densities has an exponential finite-volume error, with a constant
independent of the torus side and with no cutoff in the hop count. -/
theorem orderedHop_all_winding_error {m σ g : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (a b : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∀ n, Integrable (orderedHopWindRemainder (n := n) m σ g L a b)) ∧
      Summable (fun n : ℕ => ∫ d, orderedHopWindRemainder (n := n) m σ g L a b d) ∧
      (∑' n : ℕ, ∫ d, orderedHopWindRemainder (n := n) m σ g L a b d) ≤ Real.exp (-δ*L)*C := by
  obtain ⟨η,hη,hm,ha,hsmall⟩ := orderedHop_has_summable_tilt hσ hg
  let U := orderedHopMomentConstant (η/2) b * orderedHopTiltPeak σ η * orderedHopWindingBudget (orderedHopPrecision σ-η)
  let K := fun n : ℕ => ∫ d, freeTilt (n := n) m σ g η a d
  have hM : 0 ≤ orderedHopMomentConstant (η/2) b := by unfold orderedHopMomentConstant; positivity
  have hU : 0 ≤ U := mul_nonneg (mul_nonneg hM (orderedHop_tilt_peak_nonneg hσ η)) (orderedHop_winding_budget_nonneg _)
  have hK (n : ℕ) : 0 ≤ K n := integral_nonneg fun _ => free_nonneg hσ _ _ _ _ _
  have hS : Summable K := free_summable hσ hm ha hsmall a
  refine ⟨η/2,U*(∑' n, K n),by positivity,mul_nonneg hU (tsum_nonneg hK),?_⟩
  intro L hL
  let C := Real.exp (-(η/2)*L)*U
  have hF := free_integrable hσ hm ha g a
  have hB (n : ℕ) (d : Fin n → OrderedHopStep) := (winding_remainder_bound (g := g) hσ hη hm ha hL a b d).2
  have hI (n : ℕ) := ((hF n).const_mul C).mono' (winding_remainder_measurable hσ m g L a b n).aestronglyMeasurable
    (Eventually.of_forall fun d => (Real.norm_of_nonneg (winding_remainder_nonneg hσ m g L a b d)).le.trans (hB n d))
  have hb (n : ℕ) : (∫ d, orderedHopWindRemainder (n := n) m σ g L a b d) ≤ C*K n := by
    simpa only [K,integral_const_mul] using integral_mono (hI n) ((hF n).const_mul C) (hB n)
  have hs := (hS.mul_left C).of_nonneg_of_le (fun n => integral_nonneg fun _ => winding_remainder_nonneg hσ m g L a b _) hb
  refine ⟨hI,hs,(hs.tsum_le_tsum hb (hS.mul_left C)).trans_eq ?_⟩
  rw [tsum_mul_left]
  unfold C
  ring

end UV.SectorPlane
