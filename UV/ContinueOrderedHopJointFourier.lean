import UV.ContinueOrderedHopSpatialFourier
import UV.ContinueOrderedHopCarrierFourier
import UV.ContinueFourierHoppingSpatial

/-! For each placement term of a complete two-band loop, keep one actual
charged four-momentum with Lebesgue measure. Its normalized integral equals
the path integral after eliminating precisely one temporal and one spatial
displacement. All marks and the possible soft derivatives remain in their
original slots. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

namespace UV.SectorPlane

def HoppingSpatialSlot.positionDensity (s : HoppingSpatialSlot) (σ : ℝ) : Spatial → ℂ :=
  twoBandFourierLinkKernel 1 σ s.direction s.shift s.marks 0

/-- Fourier closure identity on one locked Euclidean sector plane for two
or more complete hops. The carrier sign is allowed to vary from slot to
slot, including the alternating signs of the determinant. -/
theorem orderedHop_joint_fourier_closure {n : ℕ} {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (T : Fin (n+1+1) → HoppingCarrierSlot) (S : Fin (n+1+1) → HoppingSpatialSlot)
    (hMass : ∀ i, |(T i).signedMass| = m) :
    ((2*Real.pi)^4)⁻¹ • (∫ p : OrderedHopStep, ∏ j, ((T j).value p.1 * ((S j).value σ p.2:ℂ))) =
      ∫ d : Fin (n+1) → OrderedHopStep, ∏ j,
        ((T j).positionDensity (orderedHopStepAt d j).1 * (S j).positionDensity σ (orderedHopStepAt d j).2) := by
  let t := fun (x : Fin (n+1) → ℝ) => (T 0).positionDensity (-(∑ j, x j)) *
      ∏ j, (T j.succ).positionDensity (x j)
  let s := fun (z : Fin (n+1) → Spatial) => ∏ j, (S j).positionDensity σ (orderedHopSpatialIncrements 0 z j)
  let P := fun (ξ : ℝ) => ∏ j, (T j).value ξ
  let K := fun (k : Spatial) => ∏ j, ((S j).value σ k : ℂ)
  have hT : (2*Real.pi)⁻¹ • (∫ ξ, P ξ) = ∫ x, t x := orderedHop_carrier_closure hm T hMass
  have hS : ((2*Real.pi)^3)⁻¹ • (∫ k, K k) = ∫ z, s z :=
    orderedHop_spatial_closure 1 hσ (fun j => (S j).degree) (fun j => (S j).direction)
      (fun j => (S j).shift) (fun j => (S j).marks)
  have hmoment : (∫ p : OrderedHopStep, ∏ j, ((T j).value p.1 * ((S j).value σ p.2:ℂ))) =
      (∫ ξ, P ξ)*(∫ k, K k) := by
    simp_rw [Finset.prod_mul_distrib]
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul P K
  rw [hmoment]
  have hpair : ((2*Real.pi)^4)⁻¹ • ((∫ ξ, P ξ)*(∫ k, K k)) = (∫ x, t x)*(∫ z, s z) := by
    rw [← hT,← hS,smul_mul_smul]
    congr 1
    field_simp
  rw [hpair,←integral_prod_mul t s]
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ Spatial (Fin (n+1))
  have he := volume_measurePreserving_arrowProdEquivProdArrow ℝ Spatial (Fin (n+1))
  rw [←Measure.volume_eq_prod,←he.integral_comp e.measurableEmbedding (fun p => t p.1*s p.2)]
  apply integral_congr_ae (ae_of_all _ fun d => ?_)
  rw [Finset.prod_mul_distrib]
  change t (fun i => (d i).1) * s (fun i => (d i).2) = _
  congr 1
  · simp only [t,Fin.prod_univ_succ,orderedHopStepAt,Fin.cons_zero,Fin.cons_succ,
      orderedHopClosingStep,Prod.fst_neg,Prod.fst_sum]
  · simp only [s,Fin.prod_univ_succ,orderedHopSpatialIncrements,orderedHopStepAt,Fin.cons_zero,Fin.cons_succ,
      orderedHopClosingStep,Prod.snd_neg,Prod.snd_sum,zero_sub]

/-- A phase on one spatial displacement translates its Gaussian Fourier symbol. -/
theorem HoppingSpatialSlot.position_translate (S : HoppingSpatialSlot) (σ : ℝ) (a z : Spatial) :
    ({ S with shift := S.shift+a } : HoppingSpatialSlot).positionDensity σ z =
      twoBandDisplacementWave a z * S.positionDensity σ z := by
  unfold positionDensity twoBandFourierLinkKernel twoBandDisplacementWave
  simp only [zero_add,inner_add_right,Complex.ofReal_add,add_mul,Complex.exp_add]
  ring

/-- Add one straight-link mode in the given genuine unit direction. At zero
incident momentum it is a Gaussian directional derivative. -/
def HoppingSpatialSlot.withMark (S : HoppingSpatialSlot) (v : UnitVector Spatial) (p : Spatial) :
    HoppingSpatialSlot := ⟨S.degree+1,Fin.cons v S.direction,S.shift,Fin.cons p S.marks⟩

theorem HoppingSpatialSlot.position_with_mark (S : HoppingSpatialSlot) (σ : ℝ)
    (v : UnitVector Spatial) (p z : Spatial) :
    (S.withMark v p).positionDensity σ z = twoBandLineMode v p z * S.positionDensity σ z := by
  unfold withMark positionDensity twoBandFourierLinkKernel
  simp only [twoBand_link_variations_eval,List.prod_ofFn,Complex.exp_zero,mul_one,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

end UV.SectorPlane
