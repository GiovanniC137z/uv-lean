import UV.ContinueSewnFlagDeterminant
import UV.ContinueSewnFlagOrdered

/-! The literal short-time Schwinger weight, including its inverse
determinant, is integrable against the joint displacement law under
the manuscript's projected prefix moments. -/

noncomputable section
open Real MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal Matrix
namespace UV.SewnFlags

def routingFaceExcess {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (ν : Fin N → ℝ) (j : Fin N) :=
  directionalOrderedPrefix ν j - 2 * (Module.finrank ℝ (routingFace C (routingShortPrefix j)) : ℝ)

def routedSchwingerWeight {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (ν t : Fin N → ℝ)
    (d : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  (∏ i, t i ^ (ν i-1)) * ((residualGram C t).det^2)⁻¹ * exp (-(routedInverseWeight C t d)/4)

private def minorShiftedExponents {N L : ℕ} (ν : Fin N → ℝ) (b : Fin L ↪ Fin N) (i : Fin N) :=
  ν i - 2 * (if i ∈ Finset.univ.map b then 1 else 0)

private theorem minorShiftedExponents_prefix {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν : Fin N → ℝ) (b : Fin L ↪ Fin N)
    (hcount : ∀ j : Fin N, Fintype.card {i : Fin L // b i ≤ j} =
      Module.finrank ℝ (routingFace C (routingShortPrefix j))) (j : Fin N) :
    directionalOrderedPrefix (minorShiftedExponents ν b) j = routingFaceExcess C ν j := by
  let B := Finset.univ.map b
  have h₁ (i : Fin N) :
      (if i ≤ j then minorShiftedExponents ν b i else 0) =
      (if i ≤ j then ν i else 0) - 2 * (if i ∈ B then if i ≤ j then (1:ℝ) else 0 else 0) := by
    by_cases h : i ≤ j <;> by_cases hB : i ∈ B <;> simp [minorShiftedExponents,h,hB,B] at *
  have hB : Finset.univ.filter (fun i => i ∈ B) = B := by ext; simp
  have hnum :
      (∑ i : Fin N, if i ∈ B then if i ≤ j then (1:ℝ) else 0 else 0) =
      (Fintype.card {i : Fin L // b i ≤ j} : ℝ) := by
    rw [← Finset.sum_filter,hB]
    unfold B
    rw [Finset.sum_map]
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Fintype.card_subtype]
  unfold directionalOrderedPrefix routingFaceExcess
  simp_rw [h₁]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hnum,hcount]
  rfl

private theorem minorShiftedExponents_product {N L : ℕ} (ν t : Fin N → ℝ)
    (ht : ∀ i, 0 < t i) (b : Fin L ↪ Fin N) :
    (∏ i, t i^(minorShiftedExponents ν b i-1)) =
      (∏ i, t i^(ν i-1)) * ((∏ i, t (b i))^2)⁻¹ := by
  let B := Finset.univ.map b
  have h₁ (i : Fin N) : t i^(minorShiftedExponents ν b i-1) =
      t i^(ν i-1) * (if i ∈ B then (t i^2)⁻¹ else 1) := by
    by_cases hi : i ∈ B
    · have he : minorShiftedExponents ν b i-1 = (ν i-1)-(2:ℕ) := by
        simp [minorShiftedExponents,show i ∈ Finset.univ.map b from hi]
        ring
      rw [he,rpow_sub_natCast (ht i).ne',if_pos hi,div_eq_mul_inv]
    · simp [minorShiftedExponents,show i ∉ Finset.univ.map b from hi,hi]
  have hB : Finset.univ.filter (fun i => i ∈ B) = B := by ext; simp
  simp_rw [h₁]
  rw [Finset.prod_mul_distrib,← Finset.prod_filter,hB]
  unfold B
  rw [Finset.prod_map,Finset.prod_inv_distrib,Finset.prod_pow]

/-- Exact short-region conclusion for a routed graph after its positive
Schwinger and Gaussian integrations, without any independent-displacement
hypothesis. Both the determinant and the inverse form are the routed matrices. -/
theorem short_routed_flag_cost_finite {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν : Fin N → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    (hJoint : (∫⁻ d, ∏ i, displacementCost (routingFaceExcess C ν i)
      (projectedDisplacement C (routingShortPrefix i) d) ∂μ) < ⊤) :
    (∫⁻ d, (∫⁻ t in directionalOrderedSet N, ENNReal.ofReal (routedSchwingerWeight C ν t d)) ∂μ) < ⊤ := by
  obtain ⟨b,hb,hcount⟩ := reverse_greedy_routed_minor C hC
  let a := minorShiftedExponents ν b
  let x := fun i => projectedDisplacement C (routingShortPrefix i)
  let c := fun i => flagRatioCoefficient C (routingShortPrefix i) N
  let K := ((selectedRows C b).det^2)^2
  have hK : 0 < K := sq_pos_of_pos (sq_pos_of_ne_zero hb)
  have hcost := ordered_joint_flag_moments μ a c x (fun i => flagRatioCoefficient_pos C (routingShortPrefix i) N)
    (fun i => projectedDisplacement_nonneg C (routingShortPrefix i))
    (fun i => projectedDisplacement_measurable C (routingShortPrefix i))
    (by simpa only [a,minorShiftedExponents_prefix C ν b hcount] using hJoint)
  let J := fun d => directionalWeightedSector a (fun i r => ENNReal.ofReal (exp (-(c i*(x i d)^2)/r)))
  refine lt_of_le_of_lt (lintegral_mono (g := fun d => ENNReal.ofReal K⁻¹ * J d) ?_) ?_
  · intro d
    change (∫⁻ t in directionalOrderedSet N, ENNReal.ofReal (routedSchwingerWeight C ν t d)) ≤
      ENNReal.ofReal K⁻¹ * J d
    unfold J directionalWeightedSector
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (directionalOrderedSet_open N).measurableSet] with t ht
    have hp (i : Fin N) : 0 < t i := ((directionalOrderedSet_mem_iff t).1 ht).2 i |>.1
    have hT (i e : Fin N) (he : e ∈ routingShortPrefix i) : t e ≤ t i :=
      ((directionalOrderedSet_mem_iff t).1 ht).1.monotone
        ((Finset.mem_filter.mp he).2)
    have hM : (residualGram C t).PosDef := by
      have he : residualGram C t = Cᴴ * diagonal t * C := by
        rw [residualGram,conjTranspose_eq_transpose_of_trivial]
        congr!
      rw [he]
      exact (Matrix.PosDef.diagonal hp).conjTranspose_mul_mul_same hC
    have hG := ordered_routed_inverse_weight C routingShortPrefix t t ht (fun i => (hp i).le) hT hM d
    have hd := routed_gram_dominates_selected_minor C t hp b hb
    let T := ∏ i, t (b i)
    have hT₀ : 0 < T := Finset.prod_pos fun i _ => hp (b i)
    have hd₀ : 0 < (selectedRows C b).det^2*T := mul_pos (sq_pos_of_ne_zero hb) hT₀
    have hI : ((residualGram C t).det^2)⁻¹ ≤ K⁻¹*(T^2)⁻¹ := by
      rw [← mul_inv,show K*T^2=((selectedRows C b).det^2*T)^2 by unfold K; ring]
      exact inv_anti₀ (sq_pos_of_pos hd₀) (pow_le_pow_left₀ hd₀.le hd 2)
    let H := fun i => exp (-(c i*(x i d)^2)/directionalOrderedRatios t i)
    have hJ : (∏ i, t i^(a i-1)) = (∏ i, t i^(ν i-1)) * (T^2)⁻¹ :=
      minorShiftedExponents_product ν t hp b
    change ENNReal.ofReal (routedSchwingerWeight C ν t d) ≤
      ENNReal.ofReal K⁻¹ * (directionalOrderedDensity a t * ∏ i, ENNReal.ofReal (H i))
    rw [directionalOrderedDensity,
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => rpow_nonneg (hp i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => rpow_nonneg (hp i).le _),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hK.le),hJ]
    apply ENNReal.ofReal_le_ofReal
    unfold routedSchwingerWeight
    calc
      _ ≤ ((∏ i, t i^(ν i-1)) * (K⁻¹*(T^2)⁻¹)) * (∏ i, H i) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hI (Finset.prod_nonneg fun i _ => rpow_nonneg (hp i).le _)
        · exact hG
        · positivity
        · exact mul_nonneg (Finset.prod_nonneg fun i _ => rpow_nonneg (hp i).le _)
            (mul_nonneg (inv_nonneg.mpr hK.le) (inv_nonneg.2 (sq_nonneg _)))
      _ = _ := by ring
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal K⁻¹ * (∫⁻ d, J d ∂μ) < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcost

end UV.SewnFlags
