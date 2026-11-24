import UV.ContinueCompressedModesPairCurrent
import UV.ContinueSourceReviewClassicalPacket
import UV.RevisionPairThreshold
import UV.RealDegree

/-! A direct test in the original relative three-momentum, before the
invariant-mass spectral integration. Both physical spin projections are
present, and the form factor depends on the actual two-particle mass. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator

namespace UV.PairCurvature

def relativeEnergy (m : ℝ) (P k : ChargeSpatialMomentum) :=
  FurtherOptical.energy m k + FurtherOptical.energy m (P-k)

def invariantMassSq (m : ℝ) (P k : ChargeSpatialMomentum) :=
  (relativeEnergy m P k)^2-‖P‖^2

theorem invariantMassSq_threshold {m : ℝ} (hm : 0<m) (P k : ChargeSpatialMomentum) :
    4*m^2 ≤ invariantMassSq m P k := by
  let K : Fin 2 → ChargeSpatialMomentum := ![k,P-k]
  have h := RevisionPairThreshold.blocked_pair_threshold (Finset.univ : Finset (Fin 2)) K hm.le (by simp)
  simp [Fin.sum_univ_two,K,RevisionPairThreshold.massiveEnergy,add_comm (‖_‖^2) (m^2)] at h
  have hE := sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr h
  rw [Real.sq_sqrt (by positivity)] at hE
  dsimp [invariantMassSq,relativeEnergy,FurtherOptical.energy]
  linarith

@[fun_prop] theorem continuous_relativeEnergy (m : ℝ) (P : ChargeSpatialMomentum) :
    Continuous (relativeEnergy m P) := by unfold relativeEnergy FurtherOptical.energy; fun_prop

@[fun_prop] theorem continuous_invariantMassSq (m : ℝ) (P : ChargeSpatialMomentum) :
    Continuous (invariantMassSq m P) := by unfold invariantMassSq; fun_prop

theorem relative_gaussian_bound {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) (P k : ChargeSpatialMomentum) :
    Real.exp (-(2*ℓ^4)*invariantMassSq m P k^2) ≤
    Real.exp (2*ℓ^4*(1+‖P‖^2))*Real.exp (-(2*ℓ^4*‖k‖^2)) := by
  have hk := FurtherOptical.energy_sq m k
  have hD := FurtherOptical.energy_pos hm k
  have hD' := FurtherOptical.energy_pos hm (P-k)
  have hs := sq_nonneg (invariantMassSq m P k-1/2)
  have hE : ‖k‖^2 ≤ invariantMassSq m P k+‖P‖^2 := by
    dsimp [invariantMassSq,relativeEnergy]
    nlinarith [mul_nonneg hD.le hD'.le,sq_nonneg m,sq_nonneg (FurtherOptical.energy m (P-k))]
  rw [←Real.exp_add,Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left (show ‖k‖^2 ≤ invariantMassSq m P k^2+1+‖P‖^2 by linarith) (show 0≤2*ℓ^4 by positivity)]

/-- The exact scalar pair form factor controls every fixed polynomial
numerator before any cancellation between relative momentum routes. -/
theorem relative_invariant_gaussian_integrable {m ℓ d : ℝ} (hm : 0<m) (hℓ : 0<ℓ)
    (hd : 0≤d) (P : ChargeSpatialMomentum) :
    Integrable (fun k => (1+‖k‖^d)*Real.exp (-(2*ℓ^4)*invariantMassSq m P k^2)) := by
  have hi := (integrable_real_degree_gaussian (μ := (volume : Measure ChargeSpatialMomentum)) (show 0<2*ℓ^4 by positivity) hd).const_mul
    (Real.exp (2*ℓ^4*(1+‖P‖^2)))
  refine hi.mono' (by fun_prop (disch := exact hd)) (ae_of_all _ fun k => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (relative_gaussian_bound hm hℓ P k)
    (show 0≤1+‖k‖^d by positivity)
  convert h using 1
  ring

def currentGamma (i : Fin 4) : DiracMatrix :=
  if i=0 then 1 else diracSlash (osAxis i).val

def currentBlock (m : ℝ) (P k : ChargeSpatialMomentum) (i : Fin 4) :=
  seaEnergyBand true m k * currentGamma i * seaEnergyBand false m (k-P)

private theorem currentBlock_contracts {m : ℝ} (hm : 0<m) (P k : ChargeSpatialMomentum) (i : Fin 4) :
    ‖currentBlock m P k i‖≤1 := by
  have hΓ : ‖currentGamma i‖≤1 := by
    dsimp [currentGamma]; split_ifs <;> simp [wilson_slash_opnorm,(osAxis i).property]
  simpa only [currentBlock,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_smul] using
    sea_spin_slot_bound k (k-P) true false hm (le_refl (0:ℝ)) (currentGamma i) hΓ

def totalComponent (m : ℝ) (P k : ChargeSpatialMomentum) (i : Fin 4) : ℝ :=
  Fin.cases (relativeEnergy m P k) (fun j => P j) i

def spinTensor (m : ℝ) (P k : ChargeSpatialMomentum) (i j : Fin 4) : DiracMatrix :=
  ((invariantMassSq m P k)⁻¹:ℂ) •
   (((totalComponent m P k i:ℂ) • currentBlock m P k j)-
    ((totalComponent m P k j:ℂ) • currentBlock m P k i))

private theorem spinTensor_uniform {m : ℝ} (hm : 0<m) (P k : ChargeSpatialMomentum) (i j : Fin 4) :
    ‖spinTensor m P k i j‖ ≤ 2*(1+(1+‖P‖^2)/(4*m^2)) := by
  let D := relativeEnergy m P k
  let s := invariantMassSq m P k
  have hD : 0<D := add_pos (FurtherOptical.energy_pos hm _) (FurtherOptical.energy_pos hm _)
  have hs : 4*m^2≤s := invariantMassSq_threshold hm P k
  have hd : 0<4*m^2 := by positivity
  have hs' : 0<s := hd.trans_le hs
  have hp : ‖P‖ ≤ D := by dsimp [s,invariantMassSq] at hs; nlinarith [norm_nonneg P,sq_nonneg m]
  have hT (j : Fin 4) : |totalComponent m P k j|≤D := by
    refine Fin.cases (by change |D|≤D;rw [abs_of_pos hD]) (fun j => ?_) j
    exact (PiLp.norm_apply_le P j).trans hp
  have hg (i j : Fin 4) : ‖(totalComponent m P k i:ℂ) • currentBlock m P k j‖≤D := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (hT i) (currentBlock_contracts hm P k j) (norm_nonneg _) hD.le).trans_eq (mul_one _)
  rw [spinTensor,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs'.le]
  have h := norm_sub_le ((totalComponent m P k i:ℂ) • currentBlock m P k j)
    ((totalComponent m P k j:ℂ) • currentBlock m P k i)
  calc _ ≤ s⁻¹*(D+D) := mul_le_mul_of_nonneg_left (h.trans (add_le_add (hg i j) (hg j i))) (inv_nonneg.mpr hs'.le)
    _ ≤ 2*(1+(1+‖P‖^2)/s) := by
      have he : D^2=s+‖P‖^2 := by dsimp [s,invariantMassSq,D]; ring
      field_simp
      nlinarith [sq_nonneg (D-1/2)]
    _ ≤ _ := by gcongr

/-- A component of the actual time-ordered two-source transfer before
relative momentum is integrated. The conjugate-transpose product is the
sum over the two free spin slots at each on-shell endpoint. -/
def rawTransfer (m ℓ ω : ℝ) (P k : ChargeSpatialMomentum) (i j l h : Fin 4) : ℂ :=
  ((Real.exp (-(2*ℓ^4)*invariantMassSq m P k^2):ℝ):ℂ) *
  ((spinTensor m P k i j).conjTranspose*spinTensor m P k l h).trace /
  ((relativeEnergy m P k:ℂ)+Complex.I*(ω:ℂ))

local instance : MeasurableSpace DiracMatrix := borel _
local instance : BorelSpace DiracMatrix := ⟨rfl⟩

private theorem measurable_spinTensor {m : ℝ} (hm : 0<m) (P : ChargeSpatialMomentum) (i j : Fin 4) :
    Measurable (fun k => spinTensor m P k i j) := by
  have hband (b:Bool) : Measurable (seaEnergyBand b m) := by
    have hcoeff := (FurtherOptical.coefficients_continuous (τ:=0) hm).measurable
    have hslash : Measurable diracSlash := by unfold diracSlash; fun_prop
    unfold seaEnergyBand FurtherOptical.projector
    cases b <;> simp <;> fun_prop (disch := exact hslash.comp hcoeff)
  have hj (h : Fin 4) : Measurable (fun k => currentBlock m P k h) := by
    unfold currentBlock
    exact ((hband true).mul_const _).mul ((hband false).comp (measurable_id.sub_const P))
  have hc (h : Fin 4) : Measurable (fun k => totalComponent m P k h) := by
    refine Fin.cases (continuous_relativeEnergy m P).measurable (fun _ => measurable_const) h
  unfold spinTensor
  exact (continuous_invariantMassSq m P).measurable.complex_ofReal.inv.smul
    (((hc i).complex_ofReal.smul (hj j)).sub ((hc j).complex_ofReal.smul (hj i)))

private def pairSpinTransferBound (m R : ℝ) := 2*(1+(1+R^2)/(4*m^2))

private theorem rawTransfer_norm_bound {m : ℝ} (hm : 0<m) (ℓ ω : ℝ)
    (P k : ChargeSpatialMomentum) (i j l h : Fin 4) :
    ‖rawTransfer m ℓ ω P k i j l h‖ ≤
      Real.exp (-(2*ℓ^4)*invariantMassSq m P k^2)*(4*(pairSpinTransferBound m ‖P‖)^2/(2*m)) := by
  let C := pairSpinTransferBound m ‖P‖
  have hC : 0≤C := by dsimp [C,pairSpinTransferBound]; positivity
  let D := relativeEnergy m P k
  have hD : 0<D := add_pos (FurtherOptical.energy_pos hm _) (FurtherOptical.energy_pos hm _)
  have hs := invariantMassSq_threshold hm P k
  have hmD : 2*m≤D := by change 4*m^2≤D^2-‖P‖^2 at hs; nlinarith [sq_nonneg ‖P‖]
  have hω : D ≤ ‖(D:ℂ)+Complex.I*(ω:ℂ)‖ := by simpa using Complex.re_le_norm ((D:ℂ)+Complex.I*(ω:ℂ))
  have ht : ‖((spinTensor m P k i j).conjTranspose*spinTensor m P k l h).trace‖≤4*C^2 := by
    apply (wilson_trace_le_opnorm _).trans
    gcongr
    apply (norm_mul_le _ _).trans
    rw [Matrix.l2_opNorm_conjTranspose,pow_two]
    exact mul_le_mul (spinTensor_uniform hm P k i j) (spinTensor_uniform hm P k l h) (norm_nonneg _) hC
  rw [rawTransfer,norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbound := div_le_div₀ (show 0≤4*C^2 by positivity) ht (show 0<2*m by positivity) (hmD.trans hω)
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

theorem rawTransfer_integrable {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ)
    (ω : ℝ) (P : ChargeSpatialMomentum) (i j l h : Fin 4) :
    Integrable (fun k => rawTransfer m ℓ ω P k i j l h) := by
  let C := pairSpinTransferBound m ‖P‖
  have hi := (relative_invariant_gaussian_integrable hm hℓ (show (0:ℝ)≤0 by rfl) P).mul_const (4*C^2/(2*m))
  have htrace : Measurable (fun k => ((spinTensor m P k i j).conjTranspose*spinTensor m P k l h).trace) := by
    apply (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp
    exact (continuous_star.measurable.comp (measurable_spinTensor hm P i j)).mul (measurable_spinTensor hm P l h)
  have hf : Measurable (fun k => rawTransfer m ℓ ω P k i j l h) := by
    unfold rawTransfer
    fun_prop (disch := exact htrace)
  refine hi.mono' hf.aestronglyMeasurable (ae_of_all _ fun k => ?_)
  apply (rawTransfer_norm_bound hm ℓ ω P k i j l h).trans
  simp only [Real.rpow_zero]
  nlinarith [mul_nonneg (Real.exp_pos (-(2*ℓ^4)*invariantMassSq m P k^2)).le
    (show 0≤4*C^2/(2*m) by positivity)]

/-- The original relative-momentum integral of every spin-tensor entry
is uniformly absolutely bounded on a compact spatial-transfer ball,
simultaneously for both carrier-frequency orderings. -/
theorem rawTransfer_absolute_uniform {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (P : ChargeSpatialMomentum), ‖P‖ ≤ R → ∀ (ω : ℝ) (i j l h : Fin 4),
      (∫ k, ‖rawTransfer m ℓ ω P k i j l h‖) ≤ B := by
  let C := 4*(pairSpinTransferBound m R)^2/(2*m)
  let G := fun k : ChargeSpatialMomentum =>
    Real.exp (2*ℓ^4*(1+R^2)) * Real.exp (-(2*ℓ^4*‖k‖^2)) * C
  have hi : Integrable G := by
    have h := integrable_real_degree_gaussian (μ := (volume : Measure ChargeSpatialMomentum))
      (show 0<2*ℓ^4 by positivity) (show (0:ℝ)≤0 by rfl)
    convert (h.const_mul (Real.exp (2*ℓ^4*(1+R^2))/2)).mul_const C using 1
    funext k
    simp only [G,Real.rpow_zero]
    ring
  refine ⟨∫ k, G k, integral_nonneg (fun k => by unfold G C; positivity),?_⟩
  intro P hP ω i j l h
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hi
  refine ae_of_all _ (fun k => (rawTransfer_norm_bound hm ℓ ω P k i j l h).trans ?_)
  have hN : ‖P‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg P) hR).2 hP
  have hC : 4*(pairSpinTransferBound m ‖P‖)^2/(2*m) ≤ C := by
    unfold C pairSpinTransferBound
    gcongr
  have hExp : Real.exp (2*ℓ^4*(1+‖P‖^2)) ≤ Real.exp (2*ℓ^4*(1+R^2)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  unfold G
  refine mul_le_mul ?_ hC (by positivity) (by positivity)
  exact (relative_gaussian_bound hm hℓ P k).trans
    (mul_le_mul_of_nonneg_right hExp (Real.exp_pos _).le)

end UV.PairCurvature
