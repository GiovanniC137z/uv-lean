import UV.ContinueOrderedTorusGaussian
import UV.ContinueTwoBandFourierTorus

/-! At common depth the same rectangular lattice estimate bounds both the
straight-link contact averages and the position-space periodized hopping
kernel. The link averages retain the spatial unit vectors. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal ContDiff
namespace UV.SectorPlane

/-- An arbitrary probability law for shifts, including affine shifts by
the continuous straight-link parameters, preserves the uniform trace bound. -/
theorem ordered_torus_averaged_marks {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {κ : ℝ}
    (hκ : 0 < κ) (g : ℝ) (n : ℕ) {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (u : Fin n → UnitVector Spatial) (shift : S → Spatial), Measurable shift →
      (∑' k, ‖twoBandGaussianMarkAverage μ g (sqrt (κ*r)) u shift (orderedTorusMomentum δ k)‖ₑ) ≤
        ENNReal.ofReal (B*(sqrt (κ*r))^n*(sqrt r)⁻¹^3) := by
  obtain ⟨B,hB,h⟩ := ordered_torus_gaussian_marked_sum hδ hκ g n
  refine ⟨B,hB,?_⟩
  intro r hr hr₁ u shift hs
  let σ := sqrt (κ*r)
  let Φ := fun x : Spatial => iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x (fun j => (u j).val)
  have hSmooth : ContDiff ℝ n (twoBandSpatialHop g σ) :=
    (twoBand_gaussian_hop_smooth g σ).of_le (by exact_mod_cast le_top)
  have hΦ : Continuous Φ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Spatial) ℝ (fun j => (u j).val)).continuous.comp
      hSmooth.continuous_iteratedFDeriv'
  let f (k : OrderedHopWinding) (s : S) := Φ (orderedTorusMomentum δ k+shift s)
  have hf (k) : Measurable (f k) := hΦ.measurable.comp (measurable_const.add hs)
  calc
    _ ≤ ∑' k, ∫⁻ s, ‖f k s‖ₑ ∂μ := ENNReal.tsum_le_tsum fun k => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ s, ∑' k, ‖f k s‖ₑ ∂μ := (lintegral_tsum fun k => (hf k).enorm.aemeasurable).symm
    _ ≤ ∫⁻ _s, ENNReal.ofReal (B*σ^n*(sqrt r)⁻¹^3) ∂μ := by
      apply lintegral_mono; intro s
      obtain ⟨hsum,hsum_le⟩ := h r hr hr₁ u (shift s)
      simp_rw [← ofReal_norm_eq_enorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum]
      exact ENNReal.ofReal_le_ofReal hsum_le
    _ = _ := by simp [σ]

private def windingTuple : OrderedHopWinding ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0,k 1,k 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨x,y,z⟩; rfl

private theorem momentumTuple (L : Fin 3 → ℝ) (k : OrderedHopWinding) :
    orderedTorusMomentum L k = repairTorusMomentum (L 0) (L 1) (L 2) (windingTuple k) := by
  ext i; fin_cases i <;> rfl

set_option maxHeartbeats 1000000 in
/-- The entire winding sum is absolutely bounded uniformly in both
endpoints, the potential and the time. The real charge and real connection
enter only through the unitary spatial Wilson transport on each lift. -/
theorem ordered_torus_periodized_hop_depth (L : Fin 3 → ℝ) (hL : ∀ i, 0 < L i)
    {κ : ℝ} (hκ : 0 < κ) (g : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (q t : ℝ) (x y : Spatial),
      let H := twoBandWindingHop A q g (sqrt (κ*r)) (L 0) (L 1) (L 2) t x y
      Summable (fun k => ‖H k‖) ∧
      (∑' k, ‖H k‖) ≤ B*(sqrt r)⁻¹^3 ∧
      ‖twoBandPeriodizedHop A q g (sqrt (κ*r)) (L 0) (L 1) (L 2) t x y‖ ≤ B*(sqrt r)⁻¹^3 := by
  let a := (4*κ)⁻¹
  let c := ((4*Real.pi*κ)^(3/2:ℝ))⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨B,hB,htrace⟩ := ordered_torus_gaussian_shift hL ha
  refine ⟨|g| *c*B,by positivity,?_⟩
  intro r hr hr₁ A q t x y H
  let σ := sqrt (κ*r)
  have hs : σ^2 = κ*r := sq_sqrt (mul_pos hκ hr).le
  let C := |g| *c*(sqrt r)⁻¹^3
  let F (k : ℤ × ℤ × ℤ) := exp (-(a*‖repairTorusMomentum (L 0) (L 1) (L 2) k+(y-x)‖^2))
  have hwidth : ((4*Real.pi*σ^2)^(3/2:ℝ))⁻¹ = c*(sqrt r)⁻¹^3 := by
    rw [hs,← mul_assoc (4*Real.pi) κ r,Real.mul_rpow (by positivity) hr.le,Real.rpow_div_two_eq_sqrt 3 hr.le]
    norm_num [c,mul_comm]
  obtain ⟨hf,ht⟩ := htrace 1 zero_lt_one le_rfl (y-x)
  have he (k : OrderedHopWinding) : exp (-(a*1)*‖orderedTorusMomentum L k+(y-x)‖^2) =
      F (windingTuple k) := by simp [F,momentumTuple,neg_mul]
  simp_rw [he] at hf ht
  have hF : Summable F := windingTuple.summable_iff.mp hf
  have hT : (∑' k, F k) ≤ B := by rw [windingTuple.tsum_eq F] at ht; simpa using ht
  have hcomp (k) : ‖H k‖ ≤ C*F k := by
    change ‖twoBandWindingHop A q g σ (L 0) (L 1) (L 2) t x y k‖ ≤ _
    unfold twoBandWindingHop
    rw [norm_mul,twoBand_spatial_wilson_unit,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_real, Real.norm_of_nonneg (by unfold twoBandDisplacementDensity; positivity),
      twoBandDisplacementDensity,hwidth,← mul_assoc]
    dsimp only [C,F,a]
    rw [←mul_assoc,hs,add_comm (y-x)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr; apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hκ.le hr₁) (by norm_num))
  have hCF := hF.mul_left C
  have hsum := hCF.of_nonneg_of_le (fun k => norm_nonneg (H k)) hcomp
  have hbudget : (∑' k, ‖H k‖) ≤ |g| *c*B*(sqrt r)⁻¹^3 := by
    apply (hsum.tsum_le_tsum hcomp hCF).trans
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hT (by dsimp [C]; positivity)).trans_eq (by dsimp [C]; ring)
  exact ⟨hsum,hbudget,(norm_tsum_le_tsum_norm hsum).trans hbudget⟩

end UV.SectorPlane
