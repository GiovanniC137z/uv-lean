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

/-- The ordered chamber bound is polynomial in a common time cap.
This permits a single family of dilated chambers to cover long and short
times simultaneously, while the same displacement is used at every face. -/
theorem scaled_routed_flag_cost_le {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν : Fin N → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℝ), 1 ≤ T → ∀ d : EuclideanSpace ℝ (Fin L × Fin 4),
      (∫⁻ u in directionalOrderedSet N, ENNReal.ofReal (routedSchwingerWeight C ν (T • u) d)) ≤
        ENNReal.ofReal (K*T^((∑ i, (ν i-1)) + ∑ i, max 1 (-routingFaceExcess C ν i))) *
        ∏ i, displacementCost (routingFaceExcess C ν i) (projectedDisplacement C (routingShortPrefix i) d) := by
  obtain ⟨b,hb,hcount⟩ := reverse_greedy_routed_minor C hC
  let a := minorShiftedExponents ν b
  let δ := routingFaceExcess C ν
  let c := fun i => flagRatioCoefficient C (routingShortPrefix i) N
  let K := ((selectedRows C b).det^2)^2
  have hK : 0 < K := sq_pos_of_pos (sq_pos_of_ne_zero hb)
  have hc (i : Fin N) : 0 < c i := flagRatioCoefficient_pos C _ _
  let K' := ∏ i, ratioCostConstant (δ i) (c i)
  have hK' : 0 < K' := Finset.prod_pos fun i _ => ratioCostConstant_pos _ (hc i)
  refine ⟨K⁻¹*K',mul_pos (inv_pos.mpr hK) hK',?_⟩
  intro T hT d
  have hT' : 0 < T := zero_lt_one.trans_le hT
  let x := fun i => projectedDisplacement C (routingShortPrefix i) d
  let D := ∑ i, (ν i-1)
  let J := directionalWeightedSector a (fun i r => ENNReal.ofReal (exp (-((c i/T)*(x i)^2)/r)))
  have hmajor :
      (∫⁻ u in directionalOrderedSet N, ENNReal.ofReal (routedSchwingerWeight C ν (T • u) d)) ≤
        ENNReal.ofReal (T^D*K⁻¹) * J := by
    unfold J directionalWeightedSector
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (directionalOrderedSet_open N).measurableSet] with u hu
    let t := T • u
    have hu' (i : Fin N) : 0 < u i := ((directionalOrderedSet_mem_iff u).1 hu).2 i |>.1
    have hp (i : Fin N) : 0 < t i := mul_pos hT' (hu' i)
    have hut (i : Fin N) : u i ≤ t i := le_mul_of_one_le_left (hu' i).le hT
    have hcap (i e : Fin N) (he : e ∈ routingShortPrefix i) : t e ≤ T*u i :=
      mul_le_mul_of_nonneg_left (((directionalOrderedSet_mem_iff u).1 hu).1.monotone
        ((Finset.mem_filter.mp he).2)) hT'.le
    have hM : (residualGram C t).PosDef := by
      have he : residualGram C t = Cᴴ * diagonal t * C := by
        rw [residualGram,conjTranspose_eq_transpose_of_trivial]
        congr!
      rw [he]
      exact (Matrix.PosDef.diagonal hp).conjTranspose_mul_mul_same hC
    have hG := ordered_routed_inverse_weight_scaled C routingShortPrefix t u hu hT'
      (fun i => (hp i).le) hcap hM d
    let U := ∏ i, u (b i)
    have hd : (selectedRows C b).det^2*U ≤ (residualGram C t).det :=
      (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => (hu' (b i)).le)
        (fun i _ => hut (b i))) (sq_nonneg _)).trans (routed_gram_dominates_selected_minor C t hp b hb)
    have hU : 0 < U := Finset.prod_pos fun i _ => hu' (b i)
    have hd₀ : 0 < (selectedRows C b).det^2*U := mul_pos (sq_pos_of_ne_zero hb) hU
    have hI : ((residualGram C t).det^2)⁻¹ ≤ K⁻¹*(U^2)⁻¹ := by
      rw [← mul_inv,show K*U^2=((selectedRows C b).det^2*U)^2 by unfold K; ring]
      exact inv_anti₀ (sq_pos_of_pos hd₀) (pow_le_pow_left₀ hd₀.le hd 2)
    let H := fun i => exp (-((c i/T)*(x i)^2)/directionalOrderedRatios u i)
    have hJ : (∏ i, u i^(a i-1)) = (∏ i, u i^(ν i-1)) * (U^2)⁻¹ :=
      minorShiftedExponents_product ν u hu' b
    have hD : (∏ i, t i^(ν i-1)) = T^D * ∏ i, u i^(ν i-1) := by
      change (∏ i, (T*u i)^(ν i-1)) = _
      simp_rw [mul_rpow hT'.le (hu' _).le]
      rw [Finset.prod_mul_distrib,← rpow_sum_of_pos hT']
    change ENNReal.ofReal (routedSchwingerWeight C ν t d) ≤
      ENNReal.ofReal (T^D*K⁻¹) * (directionalOrderedDensity a u * ∏ i, ENNReal.ofReal (H i))
    rw [directionalOrderedDensity,
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => rpow_nonneg (hu' i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => rpow_nonneg (hu' i).le _),
      ← ENNReal.ofReal_mul (by positivity),hJ]
    apply ENNReal.ofReal_le_ofReal
    unfold routedSchwingerWeight
    rw [hD]
    calc
      _ ≤ ((T^D*∏ i, u i^(ν i-1)) * (K⁻¹*(U^2)⁻¹)) * (∏ i, H i) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hI (mul_nonneg (rpow_nonneg hT'.le _)
            (Finset.prod_nonneg fun i _ => rpow_nonneg (hu' i).le _))
        · exact hG
        · positivity
        · exact mul_nonneg (mul_nonneg (rpow_nonneg hT'.le _)
            (Finset.prod_nonneg fun i _ => rpow_nonneg (hu' i).le _)) (by positivity)
      _ = _ := by ring
  have hJ := ordered_flag_cost_le a (fun i => c i/T) x
    (fun i => div_pos (hc i) hT') (fun i => projectedDisplacement_nonneg C _ _)
  simp only [a,minorShiftedExponents_prefix C ν b hcount] at hJ
  let A := ∑ i, max 1 (-δ i)
  have hconst :
      (∏ i, ENNReal.ofReal (ratioCostConstant (δ i) (c i/T))) ≤ ENNReal.ofReal (K'*T^A) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (ratioCostConstant_pos _ (div_pos (hc i) hT')).le)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∏ i, ratioCostConstant (δ i) (c i)*T^max 1 (-δ i) :=
        Finset.prod_le_prod (fun i _ => (ratioCostConstant_pos _ (div_pos (hc i) hT')).le)
          (fun i _ => ratioCostConstant_div_le _ (hc i) hT)
      _ = _ := by rw [Finset.prod_mul_distrib,← rpow_sum_of_pos hT']
  calc
    _ ≤ ENNReal.ofReal (T^D*K⁻¹) * J := hmajor
    _ ≤ ENNReal.ofReal (T^D*K⁻¹) * (ENNReal.ofReal (K'*T^A) *
          ∏ i, displacementCost (δ i) (x i)) :=
      mul_le_mul_left' (hJ.trans (mul_le_mul_right' hconst _)) _
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [rpow_add hT']
      ring

/-- Exact short-region conclusion for the same routed integral. -/
theorem short_routed_flag_cost_finite {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν : Fin N → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    (hJoint : (∫⁻ d, ∏ i, displacementCost (routingFaceExcess C ν i)
      (projectedDisplacement C (routingShortPrefix i) d) ∂μ) < ⊤) :
    (∫⁻ d, (∫⁻ t in directionalOrderedSet N, ENNReal.ofReal (routedSchwingerWeight C ν t d)) ∂μ) < ⊤ := by
  obtain ⟨K,_,hK⟩ := scaled_routed_flag_cost_le C hC ν
  have h (d : EuclideanSpace ℝ (Fin L × Fin 4)) := hK 1 le_rfl d
  simp only [one_smul,one_rpow,mul_one] at h
  apply (lintegral_mono h).trans_lt
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJoint

end UV.SewnFlags
