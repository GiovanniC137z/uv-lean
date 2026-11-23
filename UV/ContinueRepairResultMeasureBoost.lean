import UV.ContinueRepairResultProjector

/-! A bounded equal-time charge marginal rules out a nonzero positive
Lorentz-vector spectral measure by boosting compact sets. This argument
uses the transformation law of integrals of the tensor over sets and
requires no disintegration over the timelike mass parameter. The spatial
coordinates are those of the locked intrinsic orthonormal frame. -/

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped ENNReal Matrix ComplexOrder

namespace UV.ContinuationBoostSpectrum

/-- A uniform bound with no constant-rank assumption. -/
theorem canonicalDensity_variable_rank_bounded {E : Type*} [Norm E] {d : ℕ} (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀))) (p : ChargeSpatialMomentum) :
    canonicalDensity (P diamond) p ≤ 3*spatialMeasureFactor * ∫ k, chargeInclusiveSquare (P diamond k-P₀) := by
  let F := fun k => P diamond k-P₀
  let q := fun k => chargeInclusiveSquare (F k)
  let b := fun k => matrixOverlap (F (k+p)) (F k)
  have hp := measurePreserving_add_right (volume : Measure ChargeSpatialMomentum) p
  have hq : Integrable q := hL
  have hs : Integrable (fun k => q (k+p)) := hp.integrable_comp_of_integrable hq
  have hab : ‖∫ k, b k‖ ≤ ∫ k, q (k+p)+q k := by
    apply norm_integral_le_of_norm_le (hs.add hq)
    apply Eventually.of_forall
    intro k
    simpa only [Real.norm_eq_abs,inv_one,one_mul] using (matrixOverlap_abs_bound (F (k+p)) (F k) zero_lt_one)
  rw [integral_add hs hq,hp.integral_comp (Homeomorph.addRight p).measurableEmbedding q, Real.norm_eq_abs] at hab
  rw [canonicalDensity_variable_rank_identity diamond P P₀ h₀ h₀₀ hm ha hi hL]
  change spatialMeasureFactor*((∫ k, q k)-∫ k, b k) ≤ 3*spatialMeasureFactor*(∫ k, q k)
  nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hab).1 spatialMeasureFactor_nonneg]

abbrev CurrentMomentum := ℝ × ChargeSpatialMomentum

def boostGamma (b : ℝ) := Real.sqrt (1+b^2)

/-- A boost in an orthonormal spatial coordinate direction, parametrized
by the hyperbolic sine of the rapidity. The locked pole unit is the time
coordinate of this chart. -/
def currentBoost (i : Fin 3) (b : ℝ) (k : CurrentMomentum) : CurrentMomentum :=
  (boostGamma b*k.1 + b*k.2 i,
   WithLp.toLp 2 (Function.update (fun j => k.2 j) i (b*k.1+boostGamma b*k.2 i)))

private theorem boostGamma_sq (b : ℝ) : boostGamma b ^ 2 = 1+b^2 := Real.sq_sqrt (by positivity)

theorem currentBoost_preserves_mass (i : Fin 3) (b : ℝ) (k : CurrentMomentum) :
    (currentBoost i b k).1^2 - ‖(currentBoost i b k).2‖^2 = k.1^2 - ‖k.2‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  let z := b*k.1+boostGamma b*k.2 i
  change (boostGamma b*k.1+b*k.2 i)^2-(∑ j, (Function.update (fun j => k.2 j) i z j)^2) = _
  rw [Fintype.sum_eq_add_sum_compl i (fun j => (Function.update (fun j => k.2 j) i z j)^2),
    Fintype.sum_eq_add_sum_compl i (fun j => (k.2 j)^2), Function.update_self]
  have he : (∑ j ∈ ({i}ᶜ : Finset (Fin 3)), (Function.update (fun j => k.2 j) i z j)^2) =
      ∑ j ∈ ({i}ᶜ : Finset (Fin 3)), (k.2 j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (by simpa using hj : j ≠ i)]
  rw [he]
  dsimp only [z]
  linear_combination (norm := ring) (k.1^2-(k.2 i)^2) * boostGamma_sq b

def boostBox (i : Fin 3) (R L : ℝ) : Set ChargeSpatialMomentum :=
  let r := fun j => if j=i then L else R
  EuclideanSpace.measurableEquiv (Fin 3) ⁻¹' Icc (fun j => -r j) r

theorem boostBox_measurable (i : Fin 3) (R L : ℝ) : MeasurableSet (boostBox i R L) :=
  (EuclideanSpace.measurableEquiv (Fin 3)).measurable measurableSet_Icc

theorem boostBox_volume (i : Fin 3) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    volume (boostBox i R L) = ENNReal.ofReal (8*R^2*L) := by
  unfold boostBox
  rw [(EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi,Fin.prod_univ_three]
  fin_cases i
  · change ENNReal.ofReal (L- -L)*ENNReal.ofReal (R- -R)*ENNReal.ofReal (R- -R) = _
    rw [←ENNReal.ofReal_mul (by linarith),←ENNReal.ofReal_mul (mul_nonneg (by linarith) (by linarith))]
    congr 1; ring
  · change ENNReal.ofReal (R- -R)*ENNReal.ofReal (L- -L)*ENNReal.ofReal (R- -R) = _
    rw [←ENNReal.ofReal_mul (by linarith),←ENNReal.ofReal_mul (mul_nonneg (by linarith) (by linarith))]
    congr 1; ring
  · change ENNReal.ofReal (R- -R)*ENNReal.ofReal (R- -R)*ENNReal.ofReal (L- -L) = _
    rw [←ENNReal.ofReal_mul (by linarith),←ENNReal.ofReal_mul (mul_nonneg (by linarith) (by linarith))]
    congr 1; ring

theorem currentBoost_spatial_containment (i : Fin 3) (b : ℝ) {R : ℝ}
    (K : Set CurrentMomentum) (hK : ∀ k ∈ K, |k.1| ≤ R ∧ ∀ j, |k.2 j| ≤ R) :
    currentBoost i b '' K ⊆ Prod.snd ⁻¹' boostBox i R ((1+2*|b|)*R) := by
  rintro _ ⟨k,hk,rfl⟩
  have hγ : 0 ≤ boostGamma b := Real.sqrt_nonneg _
  have hab : boostGamma b ≤ 1+|b| := by
    have h := boostGamma_sq b
    nlinarith [sq_abs b, abs_nonneg b, show 0 ≤ boostGamma b from hγ]
  have hbig : |b*k.1+boostGamma b*k.2 i| ≤ (1+2*|b|)*R := by
    calc
      _ ≤ |b*k.1|+|boostGamma b*k.2 i| := abs_add_le _ _
      _ ≤ |b| * R + (1+|b|)*R := by
        rw [abs_mul,abs_mul,abs_of_nonneg hγ]
        exact add_le_add (mul_le_mul_of_nonneg_left (hK k hk).1 (abs_nonneg _))
          (mul_le_mul hab ((hK k hk).2 i) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  change (∀ j, -(if j=i then (1+2*|b|)*R else R) ≤ Function.update (fun j => k.2 j) i _ j) ∧
    ∀ j, Function.update (fun j => k.2 j) i _ j ≤ (if j=i then (1+2*|b|)*R else R)
  constructor <;> intro j <;> by_cases he : j=i
  all_goals first
    | subst j; simpa only [if_pos rfl,Function.update_self] using (abs_le.mp hbig).1
    | subst j; simpa only [if_pos rfl,Function.update_self] using (abs_le.mp hbig).2
    | simpa only [if_neg he,Function.update_of_ne he] using (abs_le.mp ((hK k hk).2 j)).1
    | simpa only [if_neg he,Function.update_of_ne he] using (abs_le.mp ((hK k hk).2 j)).2

/-- In a fixed intrinsic chart let the spectral time marginal be bounded
by a constant multiple of spatial volume. For any bounded set of
momenta the Lorentz congruence in the two rapidity directions forces
both the integrated time and longitudinal diagonal coefficients to
vanish. The mixed entry is unrestricted. -/
theorem bounded_time_marginal_kills_boost_diagonals (i : Fin 3) (μ : Measure CurrentMomentum)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (K : Set CurrentMomentum)
    (hK : ∀ k ∈ K, |k.1| ≤ R ∧ ∀ j, |k.2 j| ≤ R)
    (hMarg : Measure.map Prod.snd μ ≤ ENNReal.ofReal C • volume)
    (a t z : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hCov : ∀ b : ℝ, μ.real (currentBoost i b '' K) = boostGamma b^2*a+b^2*t+boostGamma b*b*z) :
    a=0 ∧ t=0 := by
  have upper (b : ℝ) : μ.real (currentBoost i b '' K) ≤ C*(8*R^2*((1+2*|b|)*R)) := by
    let L := (1+2*|b|)*R
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hbox := boostBox_measurable i R L
    have hm : μ (currentBoost i b '' K) ≤ ENNReal.ofReal (C*(8*R^2*L)) := by
      calc
        _ ≤ μ (Prod.snd ⁻¹' boostBox i R L) := measure_mono (currentBoost_spatial_containment i b K hK)
        _ = Measure.map Prod.snd μ (boostBox i R L) := (Measure.map_apply measurable_snd hbox).symm
        _ ≤ (ENNReal.ofReal C • (volume : Measure ChargeSpatialMomentum)) (boostBox i R L) := hMarg _
        _ = _ := by rw [Measure.smul_apply,smul_eq_mul,boostBox_volume i hR hL,ENNReal.ofReal_mul hC]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm) ENNReal.ofReal_ne_top).mpr hm |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC (by positivity)))
  have hamb (b : ℝ) (hb : 1 ≤ b) : b^2*(a+t) ≤ 24*C*R^3*b := by
    have hp := upper b
    have hn := upper (-b)
    rw [hCov] at hp hn
    rw [show boostGamma (-b) = boostGamma b by simp [boostGamma],abs_neg] at hn
    rw [abs_of_nonneg (by linarith : 0 ≤ b)] at hp hn
    nlinarith [boostGamma_sq b, mul_nonneg (show 0 ≤ 8*C*R^3 by positivity) (by linarith : 0 ≤ b-1)]
  by_contra! h
  have hs : 0 < a+t := by by_contra! h'; exact (h (by linarith)) (by linarith)
  let b := max 1 (24*C*R^3/(a+t)) + 1
  have hb : 1 ≤ b := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hlarge : 24*C*R^3/(a+t) < b := (le_max_right _ _).trans_lt (lt_add_one _)
  have := (div_lt_iff₀ hs).mp hlarge
  have := mul_lt_mul_of_pos_left this (show 0 < b by linarith)
  nlinarith [hamb b hb]

/-- The time row of the same intrinsic Lorentz boost, acting on
contravariant current components. -/
def boostTimeRow (i : Fin 3) (b : ℝ) : Fin 4 → ℂ :=
  Pi.single 0 ((boostGamma b : ℝ):ℂ) + Pi.single i.succ (b:ℂ)

theorem boostTimeRow_congruence (T : DiracMatrix) (i : Fin 3) (b : ℝ) :
    ((boostTimeRow i b) ⬝ᵥ (T *ᵥ boostTimeRow i b)).re =
      boostGamma b^2*(T 0 0).re + b^2*(T i.succ i.succ).re +
        boostGamma b*b*((T 0 i.succ).re + (T i.succ 0).re) := by
  have hop (a z : ℂ) : MulOpposite.op a • z = z*a := rfl
  simp only [boostTimeRow,add_dotProduct,Matrix.mulVec_add,single_dotProduct,Pi.add_apply,
    Matrix.mulVec_single,Pi.smul_apply,Matrix.col_apply,hop,
    Complex.add_re,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re]
  ring

/-- On each compact set the tensor of *any* positive Lorentz-vector
spectral measure with bounded spatial time marginal must vanish. The
covariance assumption is precisely its integrated 00 congruence for
the three standard axial boosts. -/
theorem compact_positive_lorentz_tensor_vanishes (μ : Measure CurrentMomentum)
    {C : ℝ} (hC : 0 ≤ C) (hMarg : Measure.map Prod.snd μ ≤ ENNReal.ofReal C • volume)
    {K : Set CurrentMomentum} (hK : IsCompact K) (T : DiracMatrix) (hT : T.PosSemidef)
    (hCov : ∀ i b, μ.real (currentBoost i b '' K) = (boostTimeRow i b ⬝ᵥ (T *ᵥ boostTimeRow i b)).re) :
    T=0 := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  have hBound (k : CurrentMomentum) (hk : k ∈ K) : |k.1| ≤ max R 0 ∧ ∀ j, |k.2 j| ≤ max R 0 := by
    have h := (hR k hk).trans (le_max_left R 0)
    exact ⟨(norm_fst_le k).trans h,fun j => (PiLp.norm_apply_le k.2 j).trans ((norm_snd_le k).trans h)⟩
  have hdiag (j : Fin 4) : 0 ≤ T j j := by
    simpa only [Matrix.mulVec_single_one,←Pi.single_star,star_one,single_dotProduct,one_mul,Matrix.col_apply] using
      hT.2 (Pi.single j (1:ℂ))
  have hz (i : Fin 3) := bounded_time_marginal_kills_boost_diagonals i μ hC (le_max_right R 0) K
    hBound hMarg _ _ _ (Complex.nonneg_iff.mp (hdiag 0)).1 (Complex.nonneg_iff.mp (hdiag i.succ)).1
    (fun b => (hCov i b).trans (boostTimeRow_congruence T i b))
  apply hT.trace_eq_zero_iff.mp
  change ∑ j, T j j = 0
  apply Finset.sum_eq_zero
  intro j _
  apply Complex.ext
  · refine Fin.cases (hz 0).1 (fun i => (hz i).2) j
  · exact (Complex.nonneg_iff.mp (hdiag j)).2.symm

/-- Suppose a candidate vector vacuum measure matches the actual
canonical density as its 00 spatial marginal. Every positive spectral
tensor integrated over a compact momentum set is then zero, even for
an occupied sea of variable rank. -/
theorem finite_slot_lorentz_spectral_tensor_vanishes {E : Type*} [Norm E] {d : ℕ} (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀)))
    (μ : Measure CurrentMomentum)
    (hMarg : Measure.map Prod.snd μ =
      volume.withDensity (fun p => ENNReal.ofReal (canonicalDensity (P diamond) p)))
    {K : Set CurrentMomentum} (hK : IsCompact K) (T : DiracMatrix) (hT : T.PosSemidef)
    (hCov : ∀ i b, μ.real (currentBoost i b '' K) = (boostTimeRow i b ⬝ᵥ (T *ᵥ boostTimeRow i b)).re) :
    T=0 := by
  let C := 3*spatialMeasureFactor*∫ k, chargeInclusiveSquare (P diamond k-P₀)
  have hC : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg (by norm_num) spatialMeasureFactor_nonneg) (integral_nonneg fun k => ?_)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  apply compact_positive_lorentz_tensor_vanishes μ hC _ hK T hT hCov
  rw [hMarg,←withDensity_const]
  apply withDensity_mono
  exact Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal
    (canonicalDensity_variable_rank_bounded diamond P P₀ h₀ h₀₀ hm ha hi hL p)

end UV.ContinuationBoostSpectrum
