import UV.ContinueSourceReviewInvariantPair
import UV.FurtherOpticalProjector
import UV.RevisionPairThreshold
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Two obligatory band changes in every nonempty ordered matter loop of
the on-shell current. This file estimates the actual invariant of the
shifted massive spatial momenta, with all normal-interval factors retained. -/

noncomputable section
open MeasureTheory Filter Set UV.FurtherOptical UV.SectorPlane
open scoped Topology BigOperators

namespace UV

/-- The earliest and latest vertices of a nonempty cyclic ordered word
are distinct band changes. `σ` sends a vertex to the next vertex. -/
theorem sea_ordered_cycle_changes {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : Equiv.Perm ι) (t : ι → ℝ) (band : ι → Bool)
    (ordered : ∀ i, if band i then t i < t (σ i) else t (σ i) < t i) :
    ∃ i j, i ≠ j ∧ band (σ.symm i) ≠ band i ∧ band (σ.symm j) ≠ band j := by
  obtain ⟨lo,_,hlo⟩ := Finset.exists_min_image Finset.univ t Finset.univ_nonempty
  obtain ⟨hi,_,hhi⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
  have h1 : band lo = true := by
    cases h : band lo <;> try rfl
    exact False.elim ((not_lt_of_ge (hlo _ (Finset.mem_univ _))) (by simpa [h] using ordered lo))
  have h2 : band (σ.symm lo) = false := by
    cases h : band (σ.symm lo) <;> try rfl
    exact False.elim ((not_lt_of_ge (hlo _ (Finset.mem_univ _))) (by simpa [h] using ordered (σ.symm lo)))
  have h3 : band hi = false := by
    cases h : band hi <;> try rfl
    exact False.elim ((not_lt_of_ge (hhi _ (Finset.mem_univ _))) (by simpa [h] using ordered hi))
  have h4 : band (σ.symm hi) = true := by
    cases h : band (σ.symm hi) <;> try rfl
    exact False.elim ((not_lt_of_ge (hhi _ (Finset.mem_univ _))) (by simpa [h] using ordered (σ.symm hi)))
  refine ⟨lo,hi,fun h => ?_,by simp [h1,h2],by simp [h3,h4]⟩
  subst hi; simp_all

def seaTransferSq (changeBand : Bool) (m : ℝ) (v w : Spatial) : ℝ :=
  (if changeBand then energy m v + energy m w else energy m v - energy m w)^2 - ‖v-w‖^2

theorem sea_transfer_kinematics (m : ℝ) (v w : Spatial) :
    seaTransferSq false m v w ≤ 0 ∧ (2*m)^2 ≤ seaTransferSq true m v w := by
  let V := WithLp.toLp 2 (v,m)
  let W := WithLp.toLp 2 (w,m)
  let W' := WithLp.toLp 2 (-w,m)
  have eV : ‖V‖ = energy m v := by simp [V,energy,WithLp.prod_norm_eq_of_L2,add_comm]
  have eW : ‖W‖ = energy m w := by simp [W,energy,WithLp.prod_norm_eq_of_L2,add_comm]
  have eW' : ‖W'‖ = energy m w := by simp [W',energy,WithLp.prod_norm_eq_of_L2,add_comm]
  have hn : ‖V-W‖ = ‖v-w‖ := by
    simp [V,W,WithLp.prod_norm_eq_of_L2,WithLp.sub_fst,WithLp.sub_snd]
  have hplus : ‖V+W'‖^2 = ‖v-w‖^2+(2*m)^2 := by
    rw [WithLp.prod_norm_eq_of_L2,Real.sq_sqrt (by positivity)]
    simp [V,W',WithLp.add_fst,WithLp.add_snd,sub_eq_add_neg,two_mul]
  have h1 := abs_norm_sub_norm_le V W
  rw [eV,eW,hn] at h1
  have h2 := norm_add_le V W'
  rw [eV,eW'] at h2
  constructor
  · dsimp [seaTransferSq]
    nlinarith [(sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 h1,sq_abs (energy m v-energy m w)]
  · dsimp [seaTransferSq]
    nlinarith [(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _ |>.trans h2)).2 h2]

/-- Denominator of the absolute normal-interval readout. Its common numerator
is `(1+2ℓm)^N` per vertex. -/
def seaMarkDen (b : Bool) (m ℓ : ℝ) (v w : Spatial) : ℝ :=
  if b then Real.sqrt (1+ℓ^2*(seaTransferSq true m v w-(2*m)^2))
  else 1+ℓ*Real.sqrt ((2*m)^2-seaTransferSq false m v w)

theorem sea_mark_den_ge_one (b : Bool) (m : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (v w : Spatial) :
    1 ≤ seaMarkDen b m ℓ v w := by
  cases b
  · dsimp [seaMarkDen]; exact le_add_of_nonneg_right (mul_nonneg hℓ.le (Real.sqrt_nonneg _))
  · dsimp [seaMarkDen]
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (sq_nonneg ℓ) (sub_nonneg.mpr (sea_transfer_kinematics m v w).2)]

/-- A band-changing mark controls the circulating momentum with only a
linear loss in the norms of the routed external offsets. -/
theorem sea_mark_hard_budget {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (a b k : Spatial) :
    1+‖k‖ ≤ (5+ℓ⁻¹)*(1+m+‖a‖+‖b‖)*seaMarkDen true m ℓ (k+a) (k+b) := by
  let S := 1+m+‖a‖+‖b‖
  let r := ‖k‖
  let D := seaMarkDen true m ℓ (k+a) (k+b)
  have hD : 1 ≤ D := sea_mark_den_ge_one _ _ hℓ _ _
  have hS : 1 ≤ S := by dsimp [S]; linarith [norm_nonneg a,norm_nonneg b]
  have hi := inv_pos.mpr hℓ
  change 1+r ≤ (5+ℓ⁻¹)*S*D
  by_cases h : r ≤ 4*S
  · nlinarith [mul_nonneg (sub_nonneg.mpr hD) (by positivity : 0 ≤ (5+ℓ⁻¹)*S),
      mul_nonneg hi.le (show 0 ≤ S by linarith)]
  · push_neg at h
    have e (w : Spatial) : ‖w‖ ≤ energy m w := by nlinarith [energy_sq m w,energy_pos hm w,norm_nonneg w,sq_nonneg m]
    have ha := norm_sub_le (k+a) a
    have hb := norm_sub_le (k+b) b
    rw [add_sub_cancel_right] at ha hb
    have ht : ‖(k+a)-(k+b)‖ ≤ ‖a‖+‖b‖ := by rw [add_sub_add_left_eq_sub]; exact norm_sub_le _ _
    have hm' : 2*m ≤ r/2 := by dsimp [S,r] at *; linarith [norm_nonneg a,norm_nonneg b]
    have ht' : ‖(k+a)-(k+b)‖ ≤ r/2 := by dsimp [S,r] at *; linarith [norm_nonneg a,norm_nonneg b]
    have he : 3*r/2 ≤ energy m (k+a)+energy m (k+b) := by
      dsimp [S,r] at *; linarith [e (k+a),e (k+b)]
    have hsq : r^2 ≤ seaTransferSq true m (k+a) (k+b)-(2*m)^2 := by
      dsimp [seaTransferSq]
      nlinarith [(sq_le_sq₀ (by positivity) (by positivity)).2 hm',
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 ht',
        (sq_le_sq₀ (by dsimp [r]; positivity) (add_nonneg (energy_pos hm _).le (energy_pos hm _).le)).2 he]
    have hsd : ℓ*r ≤ D := by
      dsimp only [D,seaMarkDen,if_true]
      apply (Real.le_sqrt (by dsimp [r]; positivity) (by
        nlinarith [mul_nonneg (sq_nonneg ℓ) (le_trans (sq_nonneg r) hsq)])).2
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ℓ)]
    have hrd : r ≤ ℓ⁻¹*D := by
      calc r = ℓ⁻¹*(ℓ*r) := by field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_left hsd hi.le
    have hα : 1+ℓ⁻¹ ≤ (5+ℓ⁻¹)*S := by nlinarith [mul_nonneg (sub_nonneg.mpr hS) (by positivity : 0 ≤ 5+ℓ⁻¹)]
    nlinarith [mul_le_mul_of_nonneg_right hα (show 0 ≤ D by linarith)]

def seaLoopRoutingCost {ι : Type*} [Fintype ι] (m ℓ : ℝ) (a : ι → Spatial) :=
  (5+ℓ⁻¹)*(1+m+2*∑ i, ‖a i‖)

def seaClassicalLoopReadout {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (band : ι → Bool)
    (a : ι → Spatial) (m ℓ : ℝ) (N : ℕ) (k : Spatial) :=
  ∏ i, ((1+ℓ*(2*m))/seaMarkDen (band (σ.symm i) != band i) m ℓ
      (k+a (σ.symm i)) (k+a i))^N

/-- The two distinct changes in an actual ordered full cycle give two
separate inverse powers. The displayed cost is polynomial in all routed
external momentum offsets and independent of the ordered times. -/
theorem sea_classical_loop_budget {ι : Type*} [Fintype ι] [Nonempty ι] (σ : Equiv.Perm ι)
    (t : ι → ℝ) (band : ι → Bool)
    (ordered : ∀ i, if band i then t i < t (σ i) else t (σ i) < t i)
    (a : ι → Spatial) {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ) (k : Spatial) :
    seaClassicalLoopReadout σ band a m ℓ N k ≤
      ((1+ℓ*(2*m))^(Fintype.card ι)*seaLoopRoutingCost m ℓ a^2)^N / (1+‖k‖)^(2*N) := by
  classical
  let D i := seaMarkDen (band (σ.symm i) != band i) m ℓ (k+a (σ.symm i)) (k+a i)
  let H := seaLoopRoutingCost m ℓ a
  let C := 1+ℓ*(2*m)
  let Y := 1+‖k‖
  have h1 (i : ι) : 1 ≤ D i := sea_mark_den_ge_one _ _ hℓ _ _
  have hH : 0 ≤ H := by dsimp [H,seaLoopRoutingCost]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hbnd (i : ι) (hc : band (σ.symm i) ≠ band i) : Y ≤ H*D i := by
    have h := sea_mark_hard_budget hm hℓ (a (σ.symm i)) (a i) k
    dsimp only [H,seaLoopRoutingCost,D,Y]
    rw [bne_iff_ne.mpr hc]
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (sea_mark_den_ge_one true _ hℓ _ _))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hle (l : ι) : ‖a l‖ ≤ ∑ i, ‖a i‖ := Finset.single_le_sum (fun i _ => norm_nonneg (a i)) (Finset.mem_univ l)
    linarith [hle (σ.symm i), hle i]
  obtain ⟨i,j,hij,hi,hj⟩ := sea_ordered_cycle_changes σ t band ordered
  have hprod : D i * D j ≤ ∏ l, D l := by
    rw [←Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i),
      ←Finset.mul_prod_erase (Finset.univ.erase i) D (Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ j⟩)]
    have hrest : 1 ≤ ∏ l ∈ (Finset.univ.erase i).erase j, D l := by
      simpa only [Finset.prod_const_one] using (Finset.prod_le_prod (s := (Finset.univ.erase i).erase j)
        (f := fun _ => (1:ℝ)) (g := D) (fun _ _ => zero_le_one) (fun l _ => h1 l))
    nlinarith [mul_nonneg (mul_nonneg (zero_le_one.trans (h1 i)) (zero_le_one.trans (h1 j))) (sub_nonneg.mpr hrest)]
  have hlow : Y^2 ≤ H^2 * ∏ l, D l := by
    calc Y^2 ≤ (H*D i)*(H*D j) := by rw [sq]; exact mul_le_mul (hbnd i hi) (hbnd j hj) hY.le (mul_nonneg hH (zero_le_one.trans (h1 i)))
         _ = H^2*(D i*D j) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg H)
  change (∏ i, (C/D i)^N) ≤ (C^Fintype.card ι*H^2)^N/Y^(2*N)
  rw [Finset.prod_pow,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,pow_mul,←div_pow]
  apply pow_le_pow_left₀ (div_nonneg (pow_nonneg hC.le _) (Finset.prod_nonneg (fun i _ => zero_le_one.trans (h1 i)))) _ N
  apply (div_le_div_iff₀ (Finset.prod_pos (fun l _ => zero_lt_one.trans_le (h1 l))) (sq_pos_of_pos hY)).2
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlow (pow_nonneg hC.le _)

theorem sea_classical_loop_integrable {ι : Type*} [Fintype ι] [Nonempty ι] (σ : Equiv.Perm ι)
    (t : ι → ℝ) (band : ι → Bool)
    (ordered : ∀ i, if band i then t i < t (σ i) else t (σ i) < t i)
    (a : ι → Spatial) {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (seaClassicalLoopReadout σ band a m ℓ N) := by
  have hi : Integrable (fun k : Spatial => (1+‖k‖)^(-((2*N:ℕ):ℝ))) volume :=
    integrable_one_add_norm (by simpa using (show (3:ℝ) < (2*N:ℕ) by exact_mod_cast (show 3 < 2*N by omega)))
  let C := ((1+ℓ*(2*m))^Fintype.card ι*seaLoopRoutingCost m ℓ a^2)^N
  have hn (k : Spatial) : 0 ≤ seaClassicalLoopReadout σ band a m ℓ N k := by
    unfold seaClassicalLoopReadout
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (div_nonneg (by positivity) (zero_le_one.trans (sea_mark_den_ge_one _ _ hℓ _ _))) _
  apply (hi.const_mul C).mono'
  · apply Measurable.aestronglyMeasurable
    unfold seaClassicalLoopReadout
    apply Finset.measurable_prod
    intro i _
    apply Measurable.pow_const
    apply measurable_const.div
    cases (band (σ.symm i) != band i) <;> simp [seaMarkDen,seaTransferSq,energy] <;> fun_prop
  · apply Eventually.of_forall
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg (hn k),Real.rpow_neg (by positivity),Real.rpow_natCast,←div_eq_mul_inv]
    exact sea_classical_loop_budget σ t band ordered a hm hℓ N k

end UV
