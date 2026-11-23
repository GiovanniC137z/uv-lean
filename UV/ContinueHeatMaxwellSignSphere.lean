import UV.ContinueHeatMaxwellSignAngular
import UV.ContinuationStablePolar

/-! The actual normalized four-dimensional angular moments used by the heat-link jet. -/

noncomputable section

namespace UV.HeatMaxwell

open MeasureTheory Set Metric Real UV.SectorPlane UV.RelativeSoft
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

private def heatSectorBasis : OrthonormalBasis (Fin 1 ⊕ Fin 3) ℝ EuclideanPlaneMomentum :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).prod (EuclideanSpace.basisFun (Fin 3) ℝ)

def heatSectorCoordinates : EuclideanPlaneMomentum ≃ₗᵢ[ℝ] UV.ScalarMomentum :=
  heatSectorBasis.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

theorem heatSectorCoordinates_longitudinal (k : EuclideanPlaneMomentum) :
    heatSectorCoordinates k 1 = ⟪k, softLongitudinal.val⟫ := by
  change ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)
    (heatSectorBasis.repr k)) (finSumFinEquiv (Sum.inr 0)) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  change heatSectorBasis.repr k (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr 0))) = _
  rw [Equiv.symm_apply_apply, OrthonormalBasis.repr_apply_apply, real_inner_comm]
  simp [heatSectorBasis, OrthonormalBasis.prod_apply, softLongitudinal,
    EuclideanSpace.basisFun_apply]

theorem heatSectorCoordinates_transverse (k : EuclideanPlaneMomentum) :
    heatSectorCoordinates k 2 = ⟪k, softTransverse.val⟫ := by
  change ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)
    (heatSectorBasis.repr k)) (finSumFinEquiv (Sum.inr 1)) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  change heatSectorBasis.repr k (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr 1))) = _
  rw [Equiv.symm_apply_apply, OrthonormalBasis.repr_apply_apply, real_inner_comm]
  simp [heatSectorBasis, OrthonormalBasis.prod_apply, softTransverse,
    EuclideanSpace.basisFun_apply]

abbrev HeatUnitSphere := sphere (0 : UV.ScalarMomentum) 1

def heatSphereMoment (i j : ℕ) : ℝ :=
  ∫ n : HeatUnitSphere, (n.1 1) ^ i * (n.1 2) ^ j ∂(volume : Measure UV.ScalarMomentum).toSphere

/-- Polar integration of powers of the two orthogonal marked coordinates. -/
theorem heat_weighted_polar (i j : ℕ) (g : ℝ → ℝ) :
    (∫ x : UV.ScalarMomentum, (x 1) ^ i * (x 2) ^ j * g ‖x‖) =
      heatSphereMoment i j * ∫ r in Ioi (0 : ℝ), r ^ (i + j + 3) * g r := by
  let μ : Measure UV.ScalarMomentum := volume
  let e := (homeomorphUnitSphereProd UV.ScalarMomentum).toMeasurableEquiv
  let f := fun x : UV.ScalarMomentum => (x 1) ^ i * (x 2) ^ j * g ‖x‖
  have hp : MeasurePreserving e (μ.comap Subtype.val)
      (μ.toSphere.prod (Measure.volumeIoiPow 3)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      μ.measurePreserving_homeomorphUnitSphereProd
  have h := (MeasurePreserving.symm e hp).integral_comp e.symm.measurableEmbedding
    (fun x : ({(0 : UV.ScalarMomentum)}ᶜ : Set UV.ScalarMomentum) => f x.1)
  rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton] at h
  change (∫ x, f x ∂μ) = _
  rw [← h]
  have hpolar : (fun p : HeatUnitSphere × Ioi (0 : ℝ) => f (e.symm p).1) =
      fun p => ((p.1.1 1)^i * (p.1.1 2)^j) * (p.2.1 ^ (i + j) * g p.2.1) := by
    funext p
    change f (((homeomorphUnitSphereProd UV.ScalarMomentum).symm p).1) = _
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    have hn : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    unfold f
    simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg p.2.2.le,
      hn, mul_one, mul_pow, pow_add]
    ring
  rw [hpolar, integral_prod_mul
    (fun n : HeatUnitSphere => (n.1 1) ^ i * (n.1 2) ^ j)
    (fun r : Ioi (0 : ℝ) => r.1 ^ (i + j) * g r.1)]
  congr 1
  unfold Measure.volumeIoiPow
  have hmeas : Measurable (fun r : Ioi (0 : ℝ) => Real.toNNReal (r.1 ^ 3)) :=
    (measurable_subtype_coe.pow_const _).real_toNNReal
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul hmeas,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r ^ 3) • (r ^ (i + j) * g r))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul, pow_add]
  ring

private theorem heatGaussianLine_zero :
    (∫ t : ℝ, Real.exp (-(t ^ 2))) = Real.sqrt Real.pi := by
  have hh := integral_gaussian (1 : ℝ)
  simpa only [neg_one_mul, div_one] using hh

private theorem heatGaussianLine_two :
    (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
  have hh := UV.centered_gaussian_half_recurrence 0
  norm_num at hh
  rw [UV.centered_gaussian_even_integral 1, hh, UV.gaussianEvenMoment_zero_zero]
  ring

private theorem heatGaussianFour (i j : ℕ) :
    (∫ x : UV.ScalarMomentum, (x 1) ^ i * (x 2) ^ j * Real.exp (-(‖x‖ ^ 2))) =
      Real.pi * (∫ t : ℝ, t ^ i * Real.exp (-(t ^ 2))) *
        (∫ t : ℝ, t ^ j * Real.exp (-(t ^ 2))) := by
  let f : Fin 4 → ℝ → ℝ := fun a t =>
    (if a = 1 then t ^ i else if a = 2 then t ^ j else 1) * Real.exp (-(t ^ 2))
  have hp := (PiLp.volume_preserving_ofLp (Fin 4)).integral_comp
    (EuclideanSpace.measurableEquiv (Fin 4)).measurableEmbedding
    (fun x : Fin 4 → ℝ => ∏ a, f a (x a))
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  have he : (fun x : UV.ScalarMomentum => ∏ a, f a (x a)) =
      fun x => (x 1) ^ i * (x 2) ^ j * Real.exp (-(‖x‖ ^ 2)) := by
    funext x
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [Real.norm_eq_abs, sq_abs]
    simp [f, Fin.prod_univ_four, h02, h21, h31, h32]
    ring
  change (∫ x : UV.ScalarMomentum, ∏ a, f a (x a)) = ∫ x : Fin 4 → ℝ, ∏ a, f a (x a) at hp
  rw [← he, hp]
  change (∫ x : Fin 4 → ℝ, ∏ a, f a (x a) ∂Measure.pi (fun _ => volume)) = _
  rw [integral_fintype_prod_eq_prod f, Fin.prod_univ_four]
  simp [f, h02, h21, h31, h32, heatGaussianLine_zero]
  have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_nonneg
  calc
    _ = (Real.sqrt Real.pi) ^ 2 * (∫ t : ℝ, t ^ i * Real.exp (-(t ^ 2))) *
      (∫ t : ℝ, t ^ j * Real.exp (-(t ^ 2))) := by ring
    _ = _ := by rw [hpi]

private theorem heatGaussianRadial (n : ℕ) :
    (∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-(r ^ 2))) = (n.factorial : ℝ) / 2 := by
  have hs : (-1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    linarith [Nat.cast_nonneg (α := ℝ) (2 * n + 1)]
  have he := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 * n + 1 : ℕ)) (b := 1)
    (by norm_num) hs (by norm_num)
  have harg : ((↑(2 * n + 1 : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 := by push_cast; ring
  rw [harg, Real.Gamma_nat_eq_factorial] at he
  rw [show (1 : ℝ) ^ (-((↑(2 * n + 1 : ℕ) : ℝ) + 1) / 2) = 1 from Real.one_rpow _,
    one_mul] at he
  simpa only [Real.rpow_two, Real.rpow_natCast, neg_one_mul, div_eq_mul_inv, one_mul,
    mul_comm ((2 : ℝ)⁻¹) _] using he

theorem heatSphereMoment_zero :
    heatSphereMoment 0 0 = 2 * Real.pi ^ 2 := by
  have h := heat_weighted_polar 0 0 (fun r => Real.exp (-(r ^ 2)))
  have hc := heatGaussianFour 0 0
  simp only [pow_zero, one_mul, heatGaussianLine_zero] at hc
  have hR := heatGaussianRadial 1
  norm_num at hR
  norm_num at h
  rw [hc, hR] at h
  have hs := Real.sq_sqrt Real.pi_nonneg
  nlinarith

theorem heatSphereMoment_left :
    heatSphereMoment 2 0 = Real.pi ^ 2 / 2 := by
  have h := heat_weighted_polar 2 0 (fun r => Real.exp (-(r ^ 2)))
  have hc := heatGaussianFour 2 0
  simp only [pow_zero, one_mul, mul_one, heatGaussianLine_zero, heatGaussianLine_two] at hc
  have hR := heatGaussianRadial 2
  norm_num at hR
  norm_num at h
  rw [hc, hR] at h
  have hs := Real.sq_sqrt Real.pi_nonneg
  nlinarith

theorem heatSphereMoment_right :
    heatSphereMoment 0 2 = Real.pi ^ 2 / 2 := by
  have h := heat_weighted_polar 0 2 (fun r => Real.exp (-(r ^ 2)))
  have hc := heatGaussianFour 0 2
  simp only [pow_zero, one_mul, heatGaussianLine_zero, heatGaussianLine_two] at hc
  have hR := heatGaussianRadial 2
  norm_num at hR
  norm_num at h
  rw [hc, hR] at h
  have hs := Real.sq_sqrt Real.pi_nonneg
  nlinarith

theorem heatSphereMoment_cross :
    heatSphereMoment 2 2 = Real.pi ^ 2 / 12 := by
  have h := heat_weighted_polar 2 2 (fun r => Real.exp (-(r ^ 2)))
  have hc := heatGaussianFour 2 2
  simp only [heatGaussianLine_two] at hc
  have hR := heatGaussianRadial 3
  norm_num at hR
  norm_num at h
  rw [hc, hR] at h
  have hs := Real.sq_sqrt Real.pi_nonneg
  nlinarith

private theorem heatUnitSphere_mon_integrable (i j : ℕ) :
    Integrable (fun n : HeatUnitSphere => (n.1 1) ^ i * (n.1 2) ^ j)
      (volume : Measure UV.ScalarMomentum).toSphere := by
  have hc (a : Fin 4) : Continuous (fun n : HeatUnitSphere => n.1 a) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) a).comp continuous_subtype_val
  have h := ((hc 1).pow i).mul ((hc 2).pow j)
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The normalized angular average of the actual midpoint/contact quadratic
jet on the four-dimensional sphere at squared radius u. -/
theorem heatTwoMarkQuadratic_sphere_mean {u : ℝ} (hu : 0 ≤ u) (q : ℝ) :
    (∫ n : HeatUnitSphere, heatTwoMarkQuadratic u (Real.sqrt u * n.1 1)
      (Real.sqrt u * n.1 2) q ∂(volume : Measure UV.ScalarMomentum).toSphere) =
      2 * Real.pi ^ 2 * heatAngularMean u q := by
  let g (i j : ℕ) (c : ℝ) (n : HeatUnitSphere) := c * ((n.1 1) ^ i * (n.1 2) ^ j)
  let a := heatAngle00 u q
  let b := heatAngle10 u q * u
  let c := heatAngle01 u q * u
  let d := heatAngle11 u q * u ^ 2
  have h (n : HeatUnitSphere) :
      heatTwoMarkQuadratic u (Real.sqrt u * n.1 1) (Real.sqrt u * n.1 2) q =
        g 0 0 a n + g 2 0 b n + g 0 2 c n + g 2 2 d n := by
    rw [heatTwoMarkQuadratic_expand, mul_pow, mul_pow, Real.sq_sqrt hu]
    simp [g, a, b, c, d]
    ring
  simp_rw [h]
  have hi (i j : ℕ) (c : ℝ) :
      Integrable (g i j c) (volume : Measure UV.ScalarMomentum).toSphere :=
    (heatUnitSphere_mon_integrable i j).const_mul c
  have h₁ := (hi 0 0 a).add (hi 2 0 b)
  have h₂ := h₁.add (hi 0 2 c)
  have hsum := integral_add h₂ (hi 2 2 d)
  have hsum₂ := integral_add h₁ (hi 0 2 c)
  simp only [Pi.add_apply] at hsum hsum₂
  rw [hsum, hsum₂, integral_add (hi 0 0 a) (hi 2 0 b)]
  have hg (i j : ℕ) (c : ℝ) :
      (∫ n : HeatUnitSphere, g i j c n ∂(volume : Measure UV.ScalarMomentum).toSphere) =
        c * heatSphereMoment i j := integral_const_mul _ _
  rw [hg, hg, hg, hg, heatSphereMoment_zero, heatSphereMoment_left, heatSphereMoment_right,
    heatSphereMoment_cross]
  unfold heatAngularMean
  dsimp only [a, b, c, d]
  ring

end UV.HeatMaxwell
