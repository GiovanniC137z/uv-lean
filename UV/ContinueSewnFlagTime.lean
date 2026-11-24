import UV.ContinueSewnFlagShortCost
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Massive tails on the full positive Schwinger chamber. The cap
dilates the whole chamber, leaving its ordering and all the projected
displacement moment tests intact. -/

noncomputable section
open Real MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal Matrix
namespace UV.SewnFlags

def orderedPositiveDurations (N : ℕ) : Set (Fin N → ℝ) :=
  {t | StrictMono t ∧ ∀ i, 0 < t i}

theorem orderedPositiveDurations_measurable (N : ℕ) : MeasurableSet (orderedPositiveDurations N) := by
  have he : orderedPositiveDurations N =
      (⋂ i : Fin N, {t | 0 < t i}) ∩
      ⋂ i : Fin N, ⋂ j : Fin N, ⋂ _h : i < j, {t | t i < t j} := by
    ext t
    simp [orderedPositiveDurations,StrictMono,and_comm]
  rw [he]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))

def routedMassSchwingerWeight {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν m t : Fin N → ℝ) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  exp (-(∑ i, (m i)^2*t i)) * routedSchwingerWeight C ν t d

theorem routedSchwingerWeight_nonneg {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν t : Fin N → ℝ) (ht : ∀ i, 0 ≤ t i) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    0 ≤ routedSchwingerWeight C ν t d := by
  unfold routedSchwingerWeight
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => rpow_nonneg (ht i) _)
    (inv_nonneg.mpr (sq_nonneg _))) (exp_pos _).le

private theorem dilated_ordered_lintegral {N : ℕ} {T : ℝ} (hT : 0 < T)
    (f : (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ t in (fun u : Fin N → ℝ => T • u) '' directionalOrderedSet N, f t) =
      ENNReal.ofReal (T^N) * (∫⁻ u in directionalOrderedSet N, f (T • u)) := by
  let A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := T • ContinuousLinearMap.id ℝ _
  have hd (u : Fin N → ℝ) (_hu : u ∈ directionalOrderedSet N) :
      HasFDerivWithinAt (fun v : Fin N → ℝ => T • v) A (directionalOrderedSet N) u :=
    ((hasFDerivAt_id u).const_smul T).hasFDerivWithinAt
  have hinj : Set.InjOn (fun v : Fin N → ℝ => T • v) (directionalOrderedSet N) := by
    intro x _ y _ h
    exact (smul_right_injective _ hT.ne') h
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (directionalOrderedSet_open N).measurableSet hd hinj]
  have hdet : A.det = T^N := by
    change LinearMap.det (T • (1 : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) = _
    rw [LinearMap.det_smul,show LinearMap.det (1 : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) = 1 from
      LinearMap.det_id,mul_one,Module.finrank_pi,Fintype.card_fin]
  simp only [hdet,abs_of_pos (pow_pos hT _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private def orderedDurationShell (N n : ℕ) : Set (Fin N → ℝ) :=
  {t ∈ orderedPositiveDurations N | ∑ i, t i ∈ Ico (n:ℝ) ((n:ℝ)+1)}

private theorem orderedDurationShell_cap {N n : ℕ} :
    orderedDurationShell N n ⊆ (fun u : Fin N → ℝ => ((n:ℝ)+1) • u) '' directionalOrderedSet N := by
  intro t ht
  let T := (n:ℝ)+1
  have hT : 0 < T := by dsimp [T]; positivity
  let u : Fin N → ℝ := T⁻¹ • t
  refine ⟨u, (directionalOrderedSet_mem_iff u).2 ⟨?_,?_⟩, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (ht.1.1 hij) (inv_pos.mpr hT)
  · intro i
    have hsum : t i ≤ ∑ j, t j :=
      Finset.single_le_sum (fun j _ => (ht.1.2 j).le) (Finset.mem_univ i)
    have hi : t i < T := hsum.trans_lt ht.2.2
    change T⁻¹*t i ∈ Ioo (0:ℝ) 1
    exact ⟨mul_pos (inv_pos.mpr hT) (ht.1.2 i), (inv_mul_lt_one₀ hT).2 hi⟩
  · change T • (T⁻¹ • t) = t
    rw [smul_smul,mul_inv_cancel₀ hT.ne',one_smul]

private theorem orderedDurationShell_cover (N : ℕ) :
    orderedPositiveDurations N ⊆ ⋃ n, orderedDurationShell N n := by
  intro t ht
  let s := ∑ i, t i
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => (ht.2 i).le
  exact mem_iUnion.mpr ⟨⌊s⌋₊,ht,Nat.floor_le hs,Nat.lt_floor_add_one _⟩

/-- With positive edge masses, the same moment condition controls
every duration on the ordered positive chamber. The countable cap
decomposition is summable because the volume costs grow polynomially. -/
theorem massive_ordered_flag_cost_finite {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν m : Fin N → ℝ)
    {η : ℝ} (hη : 0 < η) (hm : ∀ i, η ≤ (m i)^2)
    (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    (hJoint : (∫⁻ d, ∏ i, displacementCost (routingFaceExcess C ν i)
      (projectedDisplacement C (routingShortPrefix i) d) ∂μ) < ⊤) :
    (∫⁻ d, (∫⁻ t in orderedPositiveDurations N, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ∂μ) < ⊤ := by
  obtain ⟨K,hK,hcap⟩ := scaled_routed_flag_cost_le C hC ν
  let D := (∑ i, (ν i-1)) + ∑ i, max 1 (-routingFaceExcess C ν i)
  let p := ⌈(N:ℝ)+D⌉₊
  let W := fun n : ℕ => (K*exp η) * ((((n:ℝ)+1)^p)*exp (-(η*((n:ℝ)+1))))
  have hW : Summable W := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hη)
    simpa only [W,Nat.cast_add,Nat.cast_one,neg_mul] using h.mul_left (K*exp η)
  let J := fun d => ∏ i, displacementCost (routingFaceExcess C ν i)
    (projectedDisplacement C (routingShortPrefix i) d)
  have hW₀ (n : ℕ) : 0 ≤ W n := by unfold W; positivity
  have hshell (n : ℕ) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
      (∫⁻ t in orderedDurationShell N n, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ≤
        ENNReal.ofReal (W n) * J d := by
    let T := (n:ℝ)+1
    have hT : 1 ≤ T := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hT' : 0 < T := zero_lt_one.trans_le hT
    have hf (t : Fin N → ℝ) (ht : t ∈ orderedDurationShell N n) :
        ENNReal.ofReal (routedMassSchwingerWeight C ν m t d) ≤
          ENNReal.ofReal (exp (-(η*n))) * ENNReal.ofReal (routedSchwingerWeight C ν t d) := by
      unfold routedMassSchwingerWeight
      rw [← ENNReal.ofReal_mul (exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (routedSchwingerWeight_nonneg C ν t (fun i => (ht.1.2 i).le) d)
      rw [exp_le_exp,neg_le_neg_iff]
      calc
        η*n ≤ η*∑ i, t i := mul_le_mul_of_nonneg_left ht.2.1 hη.le
        _ ≤ _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hm i) (ht.1.2 i).le)
    have hb :
        (∫⁻ t in orderedDurationShell N n, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ≤
          ENNReal.ofReal (exp (-(η*n))) *
            (∫⁻ t in (fun u : Fin N → ℝ => T • u) '' directionalOrderedSet N,
              ENNReal.ofReal (routedSchwingerWeight C ν t d)) := by
      let S := orderedDurationShell N n
      have hs : MeasurableSet S := (orderedPositiveDurations_measurable N).inter
        (measurableSet_Ico.preimage (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (lintegral_mono_ae ((ae_restrict_mem hs).mono hf)).trans
        (lintegral_mono_set (orderedDurationShell_cap (N := N) (n := n)))
    rw [dilated_ordered_lintegral hT'] at hb
    apply hb.trans
    refine (mul_le_mul_left' (mul_le_mul_left' (hcap T hT d) _) _).trans ?_
    have hp : T^((N:ℝ)+D) ≤ T^p := by
      rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_le hT (Nat.le_ceil _)
    have he : exp (-(η*n)) = exp η * exp (-(η*T)) := by
      rw [← exp_add]
      congr 1
      dsimp [T]
      ring
    simp only [← mul_assoc,← ENNReal.ofReal_mul (show 0 ≤ exp (-(η*n)) by positivity),
      ← ENNReal.ofReal_mul (show 0 ≤ exp (-(η*n))*T^N by positivity)]
    refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
    change exp (-(η*n))*T^N*K*T^D ≤ W n
    rw [he,← rpow_natCast,
      show exp η*exp (-(η*T))*T^(N:ℝ)*K*T^D = (K*exp η)*(T^((N:ℝ)+D)*exp (-(η*T))) by
        rw [rpow_add hT' (N:ℝ) D]; ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (exp_pos _).le) (by positivity)
  have h (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
      (∫⁻ t in orderedPositiveDurations N, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ≤
        ENNReal.ofReal (∑' n, W n) * J d := by
    calc
      _ ≤ ∑' n, ∫⁻ t in orderedDurationShell N n,
          ENNReal.ofReal (routedMassSchwingerWeight C ν m t d) :=
        (lintegral_mono_set (orderedDurationShell_cover N)).trans (lintegral_iUnion_le _ _)
      _ ≤ ∑' n, ENNReal.ofReal (W n) * J d := ENNReal.tsum_le_tsum fun n => hshell n d
      _ = _ := by rw [ENNReal.tsum_mul_right,← ENNReal.ofReal_tsum_of_nonneg hW₀ hW]
  apply (lintegral_mono h).trans_lt
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJoint

end UV.SewnFlags
