import UV.ContinueOrderedEnvelopeRouting
import UV.ContinueOrderedCurrentWard
import UV.ContinueRelativeSpectralMark

/-! Exact Coulomb-gauge sewing of two ordered paths. The spatial numerator
sums all entries of the orthogonal projector onto the plane perpendicular to
the spatial photon momentum. The scalar numerator retains both time pulses. -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace UV.SectorPlane

def orderedSpatialProjector (i j : Fin 3) (p : Spatial) : ℝ :=
  ⟪(spectralMarkSpatialUnit i).val,(ℝ ∙ p)ᗮ.starProjection (spectralMarkSpatialUnit j).val⟫

theorem ordered_spatial_projector_bound (i j : Fin 3) (p : Spatial) :
    |orderedSpatialProjector i j p| ≤ 1 := by
  apply (abs_real_inner_le_norm _ _).trans
  rw [(spectralMarkSpatialUnit i).property,one_mul]
  exact ((ℝ ∙ p)ᗮ.norm_starProjection_apply_le _).trans_eq (spectralMarkSpatialUnit j).property

theorem measurable_orderedSpatialProjector (i j : Fin 3) : Measurable (orderedSpatialProjector i j) := by
  change Measurable fun p => orderedSpatialProjector i j p
  simp only [orderedSpatialProjector,Submodule.starProjection_orthogonal_val,Submodule.starProjection_singleton]
  fun_prop

def orderedTransverseNumerator (P R : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) : ℂ :=
  ∑ ij : Fin 3 × Fin 3, (orderedSpatialProjector ij.1 ij.2 p : ℂ) *
    (P.spatialCurrent ω p (spectralMarkSpatialUnit ij.1).val *
      R.spatialCurrent (-ω) (-p) (spectralMarkSpatialUnit ij.2).val)

/-- A positive path cost for one end of each polarization channel.
There are nine Cartesian entries of the transverse projector. -/
def OrderedPhotonKind.pathCost (kind : OrderedPhotonKind) (P : OrderedTwoBandPath) : ℝ :=
  match kind with
  | .transverse => 9*(1+P.length)^2
  | .coulomb => 8*P.hops*(1+P.length)^2

theorem OrderedPhotonKind.pathCost_nonneg (kind : OrderedPhotonKind) (P : OrderedTwoBandPath) :
    0 ≤ kind.pathCost P := by
  cases kind <;> unfold pathCost <;> positivity

theorem ordered_transverse_numerator_bound (P R : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) :
    ‖orderedTransverseNumerator P R ω p‖ ≤
    (OrderedPhotonKind.transverse.pathCost P * OrderedPhotonKind.transverse.pathCost R) *
      (min 1 (Real.sqrt (ω^2+‖p‖^2)))^2 := by
  let S := min 1 (Real.sqrt (ω^2+‖p‖^2))
  have hS : 0 ≤ S := le_min zero_le_one (Real.sqrt_nonneg _)
  let A := 3*(1+P.length)^2
  let B := 3*(1+R.length)^2
  have hb (ij : Fin 3 × Fin 3) :
      ‖(orderedSpatialProjector ij.1 ij.2 p : ℂ) *
       (P.spatialCurrent ω p (spectralMarkSpatialUnit ij.1).val *
        R.spatialCurrent (-ω) (-p) (spectralMarkSpatialUnit ij.2).val)‖ ≤ A*S*(B*S) := by
    have hR := R.polarized_bound (-ω) (-p) (spectralMarkSpatialUnit ij.2)
    simp only [neg_sq, norm_neg] at hR
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (norm_nonneg _) (ordered_spatial_projector_bound _ _ _)).trans
    rw [norm_mul]
    exact mul_le_mul (P.polarized_bound ω p _) hR (norm_nonneg _) (mul_nonneg (by dsimp [A]; positivity) hS)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun ij _ => hb ij)).trans
  simp only [Finset.sum_const, Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
  unfold A B S OrderedPhotonKind.pathCost
  push_cast
  ring_nf
  rfl

/-- Each denominator is the Euclidean covariance appropriate to its line.
The waves at its two incident paths have opposite momenta. -/
def OrderedPhotonKind.sewn (kind : OrderedPhotonKind) (a : ℝ) (P R : OrderedTwoBandPath)
    (s : ℝ × Spatial) : ℂ :=
  match kind with
  | .transverse => ((Real.exp (-(2*a*‖s.2‖)) / (s.1^2+‖s.2‖^2) : ℝ) : ℂ) *
      orderedTransverseNumerator P R s.1 s.2
  | .coulomb => ((Real.exp (-(2*a*‖s.2‖)) / ‖s.2‖^2 : ℝ) : ℂ) *
      (P.density s.1 s.2 * R.density (-s.1) (-s.2))

theorem OrderedPhotonKind.sewn_bound (kind : OrderedPhotonKind) (a : ℝ)
    (P R : OrderedTwoBandPath) (q : OSFourSpace) :
    ‖kind.sewn a P R (orderedPhotonChart q)‖ ≤
      (kind.pathCost P * kind.pathCost R) * kind.envelope a q := by
  let s := orderedPhotonChart q
  have hE := Real.exp_nonneg (-(2*a*‖s.2‖))
  cases kind with
  | transverse =>
    change ‖((Real.exp (-(2*a*‖s.2‖)) / (s.1^2+‖s.2‖^2) : ℝ) : ℂ) *
      orderedTransverseNumerator P R s.1 s.2‖ ≤ _ * orderedTransverseEnvelope a s
    rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(2*a*‖s.2‖))/(s.1^2+‖s.2‖^2))]
    apply (mul_le_mul_of_nonneg_left (ordered_transverse_numerator_bound P R s.1 s.2) (by positivity)).trans_eq
    unfold orderedTransverseEnvelope
    ring
  | coulomb =>
    change ‖((Real.exp (-(2*a*‖s.2‖)) / ‖s.2‖^2 : ℝ) : ℂ) *
      (P.density s.1 s.2 * R.density (-s.1) (-s.2))‖ ≤ _ * orderedCoulombEnvelope a s
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(2*a*‖s.2‖))/‖s.2‖^2),norm_mul]
    have hR := R.density_bound (-s.1) (-s.2)
    simp only [norm_neg,abs_neg] at hR
    apply (mul_le_mul_of_nonneg_left (mul_le_mul (P.density_bound s.1 s.2) hR (norm_nonneg _)
      (div_nonneg (mul_nonneg (OrderedPhotonKind.coulomb.pathCost_nonneg P) (le_min zero_le_one (norm_nonneg _))) (by positivity))) (by positivity)).trans_eq
    unfold orderedCoulombEnvelope pathCost
    simp only [div_eq_mul_inv,mul_inv_rev,pow_two]
    ring

end UV.SectorPlane
