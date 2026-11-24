import UV.ContinueOrderedCurrentCoulomb
import UV.ContinueWilsonPhotonSewing

/-! The integrated transverse Coulomb-gauge photon line is the covariance of
a positive Gaussian path field. Its spatial numerator is the exact three-by-three
orthogonal projector evaluated on the real and imaginary path currents. -/

noncomputable section

open MeasureTheory Matrix Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace UV.SectorPlane.OrderedTwoBandPath

private theorem neg_chart (ω : ℝ) (p : Spatial) : thinSpatialPoint (-ω) (-p) = -thinSpatialPoint ω p := by
  ext j
  cases j using Fin.cases <;> simp [thinSpatialPoint]

theorem spatial_current_opposite (P : OrderedTwoBandPath) (ω : ℝ) (p v : Spatial) :
    P.spatialCurrent (-ω) (-p) v = conj (P.spatialCurrent ω p v) := by
  simp only [spatialCurrent,hopWave,neg_chart,wilson_edge_conjugate,map_sum,map_mul,Complex.conj_ofReal]

def cartesianCurrent (P : OrderedTwoBandPath) (z : ℝ × Spatial) (part : ℂ →L[ℝ] ℝ) : Spatial :=
  ∑ i : Fin 3, part (P.spatialCurrent z.1 z.2 (spectralMarkSpatialUnit i).val) • (spectralMarkSpatialUnit i).val

private def projectorPair (p x y : Spatial) : ℝ := ⟪x,(ℝ ∙ p)ᗮ.starProjection y⟫

private theorem projector_coordinates (p : Spatial) (v w : Fin 3 → ℝ) :
    projectorPair p (∑ i, v i • (spectralMarkSpatialUnit i).val) (∑ i, w i • (spectralMarkSpatialUnit i).val) =
      ∑ ij : Fin 3 × Fin 3, orderedSpatialProjector ij.1 ij.2 p * (v ij.1*w ij.2) := by
  simp only [projectorPair,map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    Fintype.sum_prod_type,orderedSpatialProjector]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

private theorem projector_symm (p x y : Spatial) : projectorPair p x y = projectorPair p y x := by
  rw [projectorPair,←Submodule.inner_starProjection_left_eq_right,real_inner_comm]; rfl

private theorem projector_nonneg (p x : Spatial) : 0 ≤ projectorPair p x x := by
  rw [projectorPair,real_inner_comm]
  exact (ℝ ∙ p)ᗮ.re_inner_starProjection_nonneg x

def transverseGram (P R : OrderedTwoBandPath) (z : ℝ × Spatial) : ℝ :=
  projectorPair z.2 (P.cartesianCurrent z Complex.reCLM) (R.cartesianCurrent z Complex.reCLM) +
  projectorPair z.2 (P.cartesianCurrent z Complex.imCLM) (R.cartesianCurrent z Complex.imCLM)

theorem transverse_gram_numerator (P R : OrderedTwoBandPath) (z : ℝ × Spatial) :
    (orderedTransverseNumerator P R z.1 z.2).re = transverseGram P R z := by
  simp only [orderedTransverseNumerator,Complex.re_sum,Complex.re_ofReal_mul,R.spatial_current_opposite,
    transverseGram,cartesianCurrent,projector_coordinates,←sum_add_distrib,Complex.reCLM_apply,Complex.imCLM_apply]
  apply sum_congr rfl
  intro ij _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

def transverseWeight (a : ℝ) (z : ℝ × Spatial) : ℝ := Real.exp (-(2*a*‖z.2‖))/(z.1^2+‖z.2‖^2)

theorem transverse_gram_sewn (P R : OrderedTwoBandPath) (a : ℝ) (z : ℝ × Spatial) :
    (OrderedPhotonKind.transverse.sewn a P R z).re = transverseWeight a z * transverseGram P R z := by
  change (↑(transverseWeight a z)*orderedTransverseNumerator P R z.1 z.2).re = _
  rw [Complex.re_ofReal_mul,P.transverse_gram_numerator]

theorem transverse_sewn_integrable (P R : OrderedTwoBandPath) {a : ℝ} (ha : 0 < a) :
    Integrable (OrderedPhotonKind.transverse.sewn a P R) := by
  apply ((ordered_envelopes_integrable ha).1.const_mul
      (OrderedPhotonKind.transverse.pathCost P*OrderedPhotonKind.transverse.pathCost R)).mono'
    (OrderedPhotonKind.transverse.measurable_sewn a P R).aestronglyMeasurable
  apply ae_of_all
  intro p
  have h := OrderedPhotonKind.transverse.sewn_bound a P R (orderedPhotonChart.symm p)
  simpa only [OrderedPhotonKind.envelope,orderedPhotonChart.apply_symm_apply] using h

theorem transverse_weighted_integrable (P R : OrderedTwoBandPath) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z => transverseWeight a z * transverseGram P R z) := by
  simpa only [←transverse_gram_sewn] using (P.transverse_sewn_integrable R ha).re

def transverseCovariance (a : ℝ) (P R : OrderedTwoBandPath) : ℝ :=
  (2*Real.pi)^(-4:ℤ)*∫ z, (OrderedPhotonKind.transverse.sewn a P R z).re

private theorem projector_linear_combination {ι : Type*} [Fintype ι] (p : Spatial) (v : ι → Spatial) (c : ι → ℝ) :
    (∑ i, ∑ j, (c i*c j)*projectorPair p (v i) (v j)) = projectorPair p (∑ i, c i • v i) (∑ i, c i • v i) := by
  simp only [projectorPair,map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem transverse_covariance_posSemidef {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    {a : ℝ} (ha : 0 < a) : Matrix.PosSemidef (R := ℝ) (fun i j => transverseCovariance a (P i) (P j)) := by
  refine ⟨Matrix.IsHermitian.ext (fun i j => ?_),fun c => ?_⟩
  · change transverseCovariance a (P j) (P i) = transverseCovariance a (P i) (P j)
    simp only [transverseCovariance,transverse_gram_sewn,transverseGram,
      projector_symm _ ((P j).cartesianCurrent _ Complex.reCLM) ((P i).cartesianCurrent _ Complex.reCLM),
      projector_symm _ ((P j).cartesianCurrent _ Complex.imCLM) ((P i).cartesianCurrent _ Complex.imCLM)]
  · rw [star_trivial]
    let K := fun i j (z : ℝ × Spatial) => transverseWeight a z * transverseGram (P i) (P j) z
    have hK (i j : ι) : Integrable (fun z => c i*c j*K i j z) :=
      ((P i).transverse_weighted_integrable (P j) ha).const_mul _
    have hb (i j : ι) : c i*(transverseCovariance a (P i) (P j)*c j) =
        (2*Real.pi)^(-4:ℤ) * ∫ z, c i*c j*K i j z := by
      simp only [transverseCovariance,transverse_gram_sewn,K,integral_const_mul]; ring
    change 0 ≤ ∑ i, c i * ∑ j, transverseCovariance a (P i) (P j)*c j
    simp_rw [Finset.mul_sum,hb]
    simp_rw [←Finset.mul_sum]
    apply mul_nonneg (by positivity)
    simp_rw [←integral_finset_sum univ (fun j _ => hK _ j)]
    rw [←integral_finset_sum univ (fun i _ => integrable_finset_sum univ (fun j _ => hK i j))]
    apply integral_nonneg
    intro z
    simp only [K,mul_left_comm (c _*c _) (transverseWeight a z),←Finset.mul_sum]
    apply mul_nonneg (by unfold transverseWeight; positivity)
    simp only [transverseGram,mul_add,sum_add_distrib,projector_linear_combination]
    exact add_nonneg (projector_nonneg _ _) (projector_nonneg _ _)

def transverseGaussianKernel {a : ℝ} (ha : 0 < a) : OSPositiveCovariance OrderedTwoBandPath where
  entry := transverseCovariance a
  pos := fun paths => transverse_covariance_posSemidef paths ha

end UV.SectorPlane.OrderedTwoBandPath
