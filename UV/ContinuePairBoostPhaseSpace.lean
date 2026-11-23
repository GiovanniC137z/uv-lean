import UV.ContinuePairBoostLongitudinal
import UV.ContinueCompressedModesPairWard
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The moving-frame phase-space pushforward in the actual spatial
sector with a unit boost axis and its two orthogonal directions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace BigOperators
namespace UV.PairCurvature

open UV.FurtherOptical

abbrev PairTransverseCoordinates := Fin 2 → ℝ
abbrev PairSpatialFrame := OrthonormalBasis (Fin 3) ℝ ChargeSpatialMomentum

def pairSpatialCoordinates (b : PairSpatialFrame) :
    ChargeSpatialMomentum ≃ᵐ ℝ × PairTransverseCoordinates :=
  (b.measurableEquiv.trans (EuclideanSpace.measurableEquiv (Fin 3))).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

theorem pairSpatialCoordinates_preserving (b : PairSpatialFrame) :
    MeasurePreserving (pairSpatialCoordinates b) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
    ((EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).comp b.measurePreserving_measurableEquiv)

def pairSpatialVector (b : PairSpatialFrame) (x : ℝ) (v : PairTransverseCoordinates) :
    ChargeSpatialMomentum := b.repr.symm (WithLp.toLp 2 (Fin.cons x v))

theorem pairSpatialVector_eq (b : PairSpatialFrame) (x : ℝ) (v : PairTransverseCoordinates) :
    (pairSpatialCoordinates b).symm (x,v) = pairSpatialVector b x v := by
  change b.repr.symm (WithLp.toLp 2 ((0 : Fin 3).insertNth x v)) =
    b.repr.symm (WithLp.toLp 2 (Fin.cons x v))
  rw [Fin.insertNth_zero']

theorem pair_frame_axis_is_unit (b : PairSpatialFrame) : ‖b 0‖ = 1 := b.orthonormal.norm_eq_one _

def pairTransverseEnergySq (m : ℝ) (v : PairTransverseCoordinates) :=
  m^2 + ∑ i, (v i)^2

theorem pairTransverseEnergySq_pos {m : ℝ} (hm : 0 < m) (v : PairTransverseCoordinates) :
    0 < pairTransverseEnergySq m v :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos hm) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem pair_axis_energy (b : PairSpatialFrame) (m p x : ℝ) (v : PairTransverseCoordinates) :
    energy m (pairSpatialVector b x v) = oneParticleAxialEnergy (pairTransverseEnergySq m v) x ∧
    energy m (p • b 0 - pairSpatialVector b x v) = oneParticleAxialEnergy (pairTransverseEnergySq m v) (p-x) := by
  have hnorm₁ : ‖pairSpatialVector b x v‖^2 = x^2 + ∑ i, (v i)^2 := by
    rw [pairSpatialVector,b.repr.symm.norm_map,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ]
    simp only [PiLp.toLp_apply, Fin.cons_zero,Fin.cons_succ,Real.norm_eq_abs,sq_abs]
  have hcoord : b.repr (p • b 0 - pairSpatialVector b x v) =
      WithLp.toLp 2 (Fin.cons (p-x) (-v)) := by
    rw [map_sub,map_smul,b.repr_self,pairSpatialVector,b.repr.apply_symm_apply]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hnorm₂ : ‖p • b 0 - pairSpatialVector b x v‖^2 = (p-x)^2 + ∑ i, (v i)^2 := by
    rw [← b.repr.norm_map,hcoord,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ]
    simp only [PiLp.toLp_apply,Fin.cons_zero,Fin.cons_succ,Pi.neg_apply,
      Real.norm_eq_abs,sq_abs,neg_sq]
  constructor <;> simp only [energy,oneParticleAxialEnergy, restEnergySq,pairTransverseEnergySq,hnorm₁,hnorm₂] <;>
    congr 1 <;> ring

def pairBoostedRelative (b : PairSpatialFrame) (m p y : ℝ) (v : PairTransverseCoordinates) :
    ChargeSpatialMomentum :=
  pairSpatialVector b (longitudinalPairMomentum (pairTransverseEnergySq m v) p y) v

/-- The full Lebesgue product on the spatial plane has the exact
two-particle phase-space measure after the moving-frame substitution.
The input test may depend on the individual momenta as well as their sum. -/
theorem pair_boosted_spatial_phase_space (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m)
    (p : ℝ) (F : ChargeSpatialMomentum → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k, F k * ENNReal.ofReal ((4*energy m k*energy m (p • b 0-k))⁻¹)) =
      ∫⁻ v : PairTransverseCoordinates, ∫⁻ y : ℝ,
        F (pairBoostedRelative b m p y v) * ENNReal.ofReal
          ((4*longitudinalLorentzFactor (pairTransverseEnergySq m v) p y *
            restEnergySq (pairTransverseEnergySq m v) y)⁻¹) := by
  let e := pairSpatialCoordinates b
  have h := (pairSpatialCoordinates_preserving b).symm e
  let f := fun k => F k * ENNReal.ofReal ((4*energy m k*energy m (p • b 0-k))⁻¹)
  have hf : Measurable f := by
    unfold f energy
    fun_prop
  have hfe : Measurable (f ∘ e.symm) := hf.comp e.symm.measurable
  rw [← h.lintegral_comp_emb e.symm.measurableEmbedding f]
  change (∫⁻ q : ℝ × PairTransverseCoordinates, (f ∘ e.symm) q
    ∂(volume : Measure ℝ).prod (volume : Measure PairTransverseCoordinates)) = _
  rw [lintegral_prod_symm' _ hfe]
  apply lintegral_congr
  intro v
  have hline (x : ℝ) : (f ∘ e.symm) (x,v) =
      F (pairSpatialVector b x v) * ENNReal.ofReal
        ((4*oneParticleAxialEnergy (pairTransverseEnergySq m v) x *
          oneParticleAxialEnergy (pairTransverseEnergySq m v) (p-x))⁻¹) := by
    change f ((pairSpatialCoordinates b).symm (x,v)) = _
    rw [pairSpatialVector_eq]
    unfold f
    obtain ⟨h₁,h₂⟩ := pair_axis_energy b m p x v
    rw [h₁,h₂]
  simp_rw [hline]
  exact longitudinal_pair_measure (pairTransverseEnergySq_pos hm v) p (fun x => F (pairSpatialVector b x v))

/-- The original invariant mass, evaluated on the transformed spatial
momenta, equals four times the rest energy squared at each point. -/
theorem pair_boosted_invariant_mass (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m)
    (p y : ℝ) (v : PairTransverseCoordinates) :
    invariantMassSq m (p • b 0) (pairBoostedRelative b m p y v) =
      4*restEnergySq (pairTransverseEnergySq m v) y := by
  unfold invariantMassSq relativeEnergy pairBoostedRelative
  obtain ⟨h₁,h₂⟩ := pair_axis_energy b m p (longitudinalPairMomentum (pairTransverseEnergySq m v) p y) v
  rw [norm_smul,pair_frame_axis_is_unit,mul_one,Real.norm_eq_abs,sq_abs]
  rw [h₁,h₂]
  exact (longitudinal_pair_mass_and_energy (pairTransverseEnergySq_pos hm v) p y).2

end UV.PairCurvature
