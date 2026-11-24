import UV.ContinueOrderedCurrentInstantaneous
import UV.ContinueOrderedEnvelopeGraph
import UV.ContinueOSGaussianExtension

/-! The Gaussian scalar field seen by the complete closed charged paths.
Its covariance is the Coulomb quadratic form in time, equal to the
normalized four-momentum sewing. Self-contractions are part of the form. -/

noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ComplexConjugate

namespace UV.SectorPlane.OrderedTwoBandPath

def coulombWeight (a : ℝ) (p : Spatial) : ℝ :=
  Real.exp (-(2*a*‖p‖))/‖p‖^2

def timeGram (P R : OrderedTwoBandPath) (p : Spatial) (u : ℝ) : ℝ :=
  (P.timeDensity u p*conj (R.timeDensity u p)).re

theorem timeGram_integrable (P R : OrderedTwoBandPath) (p : Spatial) :
    Integrable (timeGram P R p) := by
  simpa only [timeGram,R.time_density_opposite] using (P.time_density_pair R p).1.re

private theorem re_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := (integral_re hf).symm

private theorem entry_slice (P R : OrderedTwoBandPath) (a : ℝ) (p : Spatial) :
    (2*Real.pi)⁻¹ * (∫ ω, OrderedPhotonKind.coulomb.sewn a P R (ω,p)).re =
      coulombWeight a p * ∫ u, timeGram P R p u := by
  have h : (((2*Real.pi:ℝ)⁻¹:ℝ):ℂ) * (∫ ω, OrderedPhotonKind.coulomb.sewn a P R (ω,p)) =
      (coulombWeight a p:ℂ) * (∫ u, P.timeDensity u p*R.timeDensity u (-p)) := by
    simp only [OrderedPhotonKind.sewn,integral_const_mul,coulombWeight,Complex.ofReal_inv]
    rw [mul_left_comm,(P.time_density_pair R p).2]
  have he := congrArg Complex.re h
  rw [Complex.re_ofReal_mul,Complex.re_ofReal_mul,re_integral (P.time_density_pair R p).1] at he
  simpa only [timeGram,R.time_density_opposite] using he

private theorem sewn_integrable (P R : OrderedTwoBandPath) {a : ℝ} (ha : 0 < a) :
    Integrable (OrderedPhotonKind.coulomb.sewn a P R) := by
  apply ((ordered_envelopes_integrable ha).2.const_mul
      (OrderedPhotonKind.coulomb.pathCost P*OrderedPhotonKind.coulomb.pathCost R)).mono'
    (OrderedPhotonKind.coulomb.measurable_sewn a P R).aestronglyMeasurable
  apply ae_of_all
  intro p
  have h := OrderedPhotonKind.coulomb.sewn_bound a P R (orderedPhotonChart.symm p)
  simpa only [OrderedPhotonKind.envelope,orderedPhotonChart.apply_symm_apply] using h

theorem weightedGram_integrable (P R : OrderedTwoBandPath) {a : ℝ} (ha : 0 < a) :
    Integrable (fun p => coulombWeight a p * ∫ u, timeGram P R p u) := by
  have hi : Integrable (OrderedPhotonKind.coulomb.sewn a P R) ((volume : Measure ℝ).prod volume) :=
    P.sewn_integrable R ha
  simpa only [←entry_slice] using hi.integral_prod_right.re.const_mul (2*Real.pi)⁻¹

/-- The actual instantaneous Coulomb energy pairing on two closed paths. -/
def coulombCovariance (a : ℝ) (P R : OrderedTwoBandPath) : ℝ :=
  (2*Real.pi)^(-3:ℤ) * ∫ p, coulombWeight a p * ∫ u, timeGram P R p u

theorem coulomb_frequency_covariance (P R : OrderedTwoBandPath) {a : ℝ} (ha : 0 < a) :
    coulombCovariance a P R = (2*Real.pi)^(-4:ℤ) * (∫ z, OrderedPhotonKind.coulomb.sewn a P R z).re := by
  have hi : Integrable (OrderedPhotonKind.coulomb.sewn a P R) ((volume : Measure ℝ).prod volume) :=
    P.sewn_integrable R ha
  rw [coulombCovariance,Measure.volume_eq_prod,integral_prod_symm _ hi,re_integral hi.integral_prod_right]
  simp only [←entry_slice,integral_const_mul]
  rw [←mul_assoc]
  congr 1
  norm_num [_root_.zpow_neg,zpow_ofNat]
  ring

private theorem timeGram_symm (P R : OrderedTwoBandPath) (p : Spatial) (u : ℝ) :
    timeGram P R p u = timeGram R P p u := by
  simp [timeGram,Complex.mul_re,mul_comm]

theorem timeGram_energy {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    (c : ι → ℝ) (p : Spatial) (u : ℝ) :
    (∑ i, ∑ j, c i*c j*timeGram (P i) (P j) p u) =
      Complex.normSq (∑ i, (c i:ℂ)*(P i).timeDensity u p) := by
  let z := fun i => (c i:ℂ)*(P i).timeDensity u p
  have he : (∑ i, ∑ j, (((c i*c j:ℝ):ℂ) * ((P i).timeDensity u p*conj ((P j).timeDensity u p)))) =
      (∑ i, z i)*conj (∑ i, z i) := by
    rw [map_sum,sum_mul]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [z,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  have h := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.re_ofReal_mul,timeGram,Complex.mul_conj,Complex.ofReal_re,z] using h

/-- At every finite list (with repetitions permitted), the quadratic form is
the spatially smeared integral of the squared total signed time density. -/
theorem coulomb_quadratic_form {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    (c : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    c ⬝ᵥ ((fun i j => coulombCovariance a (P i) (P j)) *ᵥ c) =
      (2*Real.pi)^(-3:ℤ) * ∫ p, coulombWeight a p *
        ∫ u, Complex.normSq (∑ i, (c i:ℂ)*(P i).timeDensity u p) := by
  let K := fun i j (p : Spatial) => coulombWeight a p * ∫ u, timeGram (P i) (P j) p u
  have hK (i j : ι) : Integrable (fun p => (c i*c j)*K i j p) :=
    ((P i).weightedGram_integrable (P j) ha).const_mul _
  have hb (i j : ι) : c i*(coulombCovariance a (P i) (P j)*c j) =
      (2*Real.pi)^(-3:ℤ) * ∫ p, (c i*c j)*K i j p := by
    simp only [coulombCovariance,K,integral_const_mul]; ring
  change (∑ i, c i * ∑ j, coulombCovariance a (P i) (P j)*c j) = _
  simp_rw [Finset.mul_sum,hb]
  simp_rw [←Finset.mul_sum]
  congr 1
  simp_rw [←integral_finset_sum univ (fun j _ => hK _ j)]
  rw [←integral_finset_sum _ (fun i _ => integrable_finset_sum univ (fun j _ => hK i j))]
  apply integral_congr_ae
  filter_upwards with p
  change (∑ i, ∑ j, (c i*c j)*K i j p) = _
  simp_rw [←timeGram_energy P c]
  simp only [K]
  have htime (i j : ι) : Integrable (fun u => c i*c j*timeGram (P i) (P j) p u) :=
    ((P i).timeGram_integrable (P j) p).const_mul _
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum univ (fun j _ => htime i j))]
  simp_rw [integral_finset_sum univ (fun j _ => htime _ j),integral_const_mul,Finset.mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem coulomb_posSemidef {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    {a : ℝ} (ha : 0 < a) : Matrix.PosSemidef (R := ℝ) (fun i j => coulombCovariance a (P i) (P j)) := by
  refine ⟨Matrix.IsHermitian.ext (fun i j => ?_),fun c => ?_⟩
  · change coulombCovariance a (P j) (P i) = coulombCovariance a (P i) (P j)
    simp only [coulombCovariance,timeGram_symm (P j) (P i)]
  · rw [star_trivial,coulomb_quadratic_form P c ha]
    exact mul_nonneg (by positivity) (integral_nonneg fun p => mul_nonneg
      (by unfold coulombWeight; positivity) (integral_nonneg fun _ => Complex.normSq_nonneg _))

/-- One positive Gaussian kernel indexed by closed paths of the fixed plane. -/
def coulombGaussianKernel {a : ℝ} (ha : 0 < a) : OSPositiveCovariance OrderedTwoBandPath where
  entry := coulombCovariance a
  pos := fun paths => coulomb_posSemidef paths ha

theorem coulomb_gaussian_law {a : ℝ} (ha : 0 < a) :
    ∃! μ : Measure (OrderedTwoBandPath → ℝ), IsProjectiveLimit (α := fun _ => ℝ) μ (coulombGaussianKernel ha).family := by
  letI : Inhabited OrderedTwoBandPath := ⟨⟨0, 0, 0, rfl, rfl⟩⟩
  exact osPositiveGaussianProcess _

theorem coulomb_gaussian_sewing {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → OrderedTwoBandPath) (c : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    MarkedPhoton.photonCharacteristic ((coulombGaussianKernel ha).law P) c =
      Complex.exp (-(((2*Real.pi)^(-3:ℤ) * ∫ p, coulombWeight a p *
        ∫ u, Complex.normSq (∑ i, (c i:ℂ)*(P i).timeDensity u p) : ℝ):ℂ)/2) := by
  exact (MarkedPhoton.projectionLaw_characteristic _ (coulomb_posSemidef P ha) c).trans
    (by rw [coulomb_quadratic_form P c ha])

/-- The same formula on one common probability space for all complete paths;
the list may contain repeated paths and the quadratic form includes the diagonal. -/
theorem coulomb_gaussian_process_sewing {ι : Type} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 < a) (μ : Measure (OrderedTwoBandPath → ℝ))
    (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (coulombGaussianKernel ha).family)
    (P : ι → OrderedTwoBandPath) (c : ι → ℝ) :
    (∫ x, Complex.exp (((∑ i, c i*x (P i):ℝ):ℂ)*Complex.I) ∂μ) =
      Complex.exp (-(((2*Real.pi)^(-3:ℤ) * ∫ p, coulombWeight a p *
        ∫ u, Complex.normSq (∑ i, (c i:ℂ)*(P i).timeDensity u p) : ℝ):ℂ)/2) := by
  have hproj := osPositiveGaussian_projection (coulombGaussianKernel ha) μ hμ P
  have h := coulomb_gaussian_sewing P c ha
  rw [←hproj,MarkedPhoton.photonCharacteristic,integral_map] at h
  · exact h
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply (P i))).aemeasurable
  · fun_prop

end UV.SectorPlane.OrderedTwoBandPath
