import UV.ContinueOrderedTorusShell
import UV.ContinueTwoBandGaussianMarks

/-! Width-uniform translated Gaussian sums on the actual rectangular
reciprocal lattice, including all fixed-order spatial Wilson derivatives. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal ContDiff
namespace UV.SectorPlane

private theorem integer_gaussian_summable {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (y : ℝ) :
    Summable (fun k : ℤ => exp (-a*(δ*(k:ℝ)+y)^2)) := by
  have hs := (UV.ExtendNativeHolonomy.normalWinding_gaussian_summable
    (show 0 < a*δ^2/2 by positivity)).mul_left (exp (a*y^2))
  apply hs.of_nonneg_of_le (fun _ => (exp_pos _).le)
  intro k
  rw [← exp_add,exp_le_exp]
  nlinarith [mul_nonneg ha.le (sq_nonneg (δ*(k:ℝ)+2*y))]

private theorem shifted_integer_gaussian_budget {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y : ℝ,
      (∑' k : ℤ, exp (-(a*r)*(δ*(k:ℝ)+y)^2)) ≤ B/(sqrt r) := by
  let v := a*δ^2
  have hv : 0 < v := by dsimp [v]; positivity
  let T := ∑' k : ℤ, exp (-(π^2/v*(k:ℝ)^2))
  have hT : 0 ≤ T := tsum_nonneg fun _ => (exp_pos _).le
  refine ⟨sqrt (π/v) * T, mul_nonneg (sqrt_nonneg _) hT,?_⟩
  intro r hr hr₁ y
  let V := v*r
  have hV : 0 < V := mul_pos hv hr
  have he (k : ℤ) : -(a*r)*(δ*(k:ℝ)+y)^2 = -V*((k:ℝ)-(-y/δ))^2 := by dsimp [V,v]; field_simp; ring
  simp_rw [he]
  change UV.ContinueNormalHolonomy.normalTheta V (-y/δ) ≤ _
  apply (sub_nonneg.mp (UV.ContinueNormalHolonomy.relativeNormalTheta_nonnegative hV (-y/δ))).trans
  rw [UV.ContinueNormalHolonomy.normalTheta_poisson hV]
  simp only [mul_zero,cos_zero,mul_one]
  have hs (c : ℝ) (hc : 0 < c) := UV.ExtendNativeHolonomy.normalWinding_gaussian_summable hc
  have hsum : (∑' k : ℤ, exp (-π^2/V*(k:ℝ)^2)) ≤ T := by
    simp_rw [neg_div,neg_mul]
    apply (hs _ (by positivity)).tsum_le_tsum _ (hs _ (by positivity))
    intro k
    apply exp_le_exp.mpr; apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact div_le_div_of_nonneg_left (sq_nonneg _) hV (mul_le_of_le_one_right hv.le hr₁)
  apply (mul_le_mul_of_nonneg_left hsum (sqrt_nonneg _)).trans_eq
  have he' : π/V = (π/v)/r := by dsimp [V]; ring
  rw [he',sqrt_div (div_nonneg pi_pos.le hv.le)]
  ring

/-- Uniform in arbitrary real shifts (hence also in marks on a segment or
integer bridge offsets), with all reciprocal lattice sites retained. -/
theorem ordered_torus_gaussian_shift {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y : Spatial,
      Summable (fun k => exp (-(a*r)*‖orderedTorusMomentum δ k+y‖^2)) ∧
      (∑' k, exp (-(a*r)*‖orderedTorusMomentum δ k+y‖^2)) ≤ B*(sqrt r)⁻¹^3 := by
  classical
  choose B hB hbudget using fun i => shifted_integer_gaussian_budget ha (hδ i)
  refine ⟨∏ i, B i, Finset.prod_nonneg (fun i _ => hB i),?_⟩
  intro r hr hr₁ y
  let f (i : Fin 3) (k : ℤ) := exp (-(a*r)*(δ i*(k:ℝ)+y i)^2)
  have hprod (k : OrderedHopWinding) : exp (-(a*r)*‖orderedTorusMomentum δ k+y‖^2) =
      ∏ i, f i (k i) := by
    simp only [EuclideanSpace.norm_sq_eq,Finset.mul_sum,exp_sum]
    apply Finset.prod_congr rfl; intro i _
    simp [f,orderedTorusMomentum,Real.norm_eq_abs]
  have hs (i) : Summable (f i) := integer_gaussian_summable (mul_pos ha hr) (hδ i) (y i)
  have hi (i) : Integrable (f i) Measure.count := integrable_count_iff.mpr
    (by simpa only [f,Real.norm_of_nonneg (exp_pos _).le] using hs i)
  have hpi : Measure.pi (fun _ : Fin 3 => (Measure.count : Measure ℤ)) = Measure.count := by
    apply Measure.ext_of_singleton; intro k
    rw [← Set.univ_pi_singleton k,Measure.pi_pi,Set.univ_pi_singleton]; simp
  have hi' := Integrable.fintype_prod hi
  rw [hpi] at hi'
  constructor
  · simpa only [hprod] using UV.wilson_summable_product (V := Fin 3)
      (fun i (k : ℤ) => (exp_pos (-(a*r)*(δ i*(k:ℝ)+y i)^2)).le) hs
  calc
    _ = ∫ k : OrderedHopWinding, ∏ i, f i (k i) ∂Measure.count := by
      simp_rw [hprod]; simpa [Measure.real] using (integral_countable' hi').symm
    _ = ∏ i, ∫ k, f i k ∂Measure.count := by rw [← hpi,integral_fintype_prod_eq_prod]
    _ ≤ ∏ i, B i /sqrt r := by
      apply Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (exp_pos _).le)
      intro i _; rw [integral_countable' (hi i)]; simpa [Measure.real,f] using hbudget i r hr hr₁ (y i)
    _ = _ := by simp [div_eq_mul_inv, Finset.prod_mul_distrib]

/-- Scaling the spatial unit-width symbol contributes exactly one factor of
`σ` per derivative in a retained unit direction. -/
theorem ordered_torus_gaussian_derivative_scale (g σ : ℝ) {n : ℕ}
    (u : Fin n → UnitVector Spatial) (x : Spatial) :
    iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x (fun j => (u j).val) =
      σ^n * iteratedFDeriv ℝ n (twoBandSpatialHop g 1) (σ • x) (fun j => (u j).val) := by
  let A := σ • ContinuousLinearMap.id ℝ Spatial
  have he : twoBandSpatialHop g σ = (twoBandSpatialHop g 1) ∘ A := by
    funext t; simp [A,twoBandSpatialHop,norm_smul,Real.norm_eq_abs,mul_pow]
  have hF : ContDiff ℝ n (twoBandSpatialHop g 1) := (twoBand_gaussian_hop_smooth g 1).of_le (by exact_mod_cast le_top)
  rw [he,A.iteratedFDeriv_comp_right hF x le_rfl]
  change (iteratedFDeriv ℝ n (twoBandSpatialHop g 1) (σ • x)) (fun i => σ • (u i).val) = _
  rw [ContinuousMultilinearMap.map_smul_univ]; simp

/-- Every fixed spatial mark order has the same `r⁻³ᐟ²` reciprocal trace
cost, uniformly in translated momenta and the unit vectors of the marks. -/
theorem ordered_torus_gaussian_marked_sum {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {κ : ℝ}
    (hκ : 0 < κ) (g : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (u : Fin n → UnitVector Spatial) (y : Spatial),
      let F (k : OrderedHopWinding) := ‖iteratedFDeriv ℝ n (twoBandSpatialHop g (sqrt (κ*r)))
        (orderedTorusMomentum δ k+y) (fun j => (u j).val)‖
      Summable F ∧ (∑' k, F k) ≤ B*(sqrt (κ*r))^n*(sqrt r)⁻¹^3 := by
  obtain ⟨D,hD,hmark⟩ := twoBand_gaussian_mark_envelope g zero_lt_one n
  obtain ⟨B,hB,hgauss⟩ := ordered_torus_gaussian_shift hδ (a := κ/2) (by positivity)
  refine ⟨D*B,mul_nonneg hD hB,?_⟩
  intro r hr hr₁ u y F
  let σ := sqrt (κ*r)
  have hσ : 0 ≤ σ := sqrt_nonneg _
  have hσsq : σ^2 = κ*r := sq_sqrt (mul_pos hκ hr).le
  let K (k : OrderedHopWinding) := exp (-(κ/2*r)*‖orderedTorusMomentum δ k+y‖^2)
  obtain ⟨hs,hint⟩ := hgauss r hr hr₁ y
  have hf (k) : F k ≤ (σ^n*D)*K k := by
    dsimp only [F]
    rw [ordered_torus_gaussian_derivative_scale,norm_mul,Real.norm_of_nonneg (pow_nonneg hσ _)]
    apply (mul_le_mul_of_nonneg_left (hmark u (σ • (orderedTorusMomentum δ k+y))) (pow_nonneg hσ n)).trans_eq
    dsimp [K]; rw [mul_assoc,norm_smul,Real.norm_of_nonneg hσ,mul_pow,hσsq]; congr 3; ring
  have hS : Summable (fun k => (σ^n*D)*K k) := hs.mul_left _
  have hf' := hS.of_nonneg_of_le (fun k => show 0 ≤ F k from norm_nonneg _) hf
  refine ⟨hf', (hf'.tsum_le_tsum hf hS).trans ?_⟩
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left hint (mul_nonneg (pow_nonneg hσ _) hD)).trans_eq
  dsimp [σ]; ring

end UV.SectorPlane
