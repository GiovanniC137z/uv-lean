import UV.ContinueCompressedModesPairRelative

/-! Ward contraction in the underlying massive particle and occupied
antiparticle spin spaces at their distinct momenta, on a fixed carrier
plane. No longitudinally averaged spin tensor is used here. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace UV.PairCurvature

def massiveCarrier (m : ℝ) (k : ChargeSpatialMomentum) : DiracMomentum :=
  WithLp.toLp 2 (Fin.cons m (fun j:Fin 3 => k j))

private theorem hamiltonian_polar {m : ℝ} (hm : 0<m) (k : ChargeSpatialMomentum) :
    diracSlash (massiveCarrier m k) =
      (FurtherOptical.energy m k:ℂ) • diracSlash (FurtherOptical.coefficients m 0 k) := by
  have hn := (FurtherOptical.energy_pos hm k).ne'
  have hdiag : FurtherOptical.diagonal m 0 k = m := by
    simp [FurtherOptical.diagonal,FurtherOptical.energy_sq,FurtherOptical.attenuation,Real.sqrt_sq hm.le]
  rw [←diracSlash_real_smul]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change m=FurtherOptical.energy m k*(FurtherOptical.diagonal m 0 k/FurtherOptical.energy m k)
    rw [hdiag]
    field_simp
  · change k j=FurtherOptical.energy m k*(FurtherOptical.attenuation 0 k*k j/FurtherOptical.energy m k)
    simp [FurtherOptical.attenuation]
    field_simp

private theorem band_eigenvalues {m : ℝ} (hm : 0<m) (k : ChargeSpatialMomentum) :
    seaEnergyBand true m k*diracSlash (massiveCarrier m k) =
      (FurtherOptical.energy m k:ℂ) • seaEnergyBand true m k ∧
    diracSlash (massiveCarrier m k)*seaEnergyBand false m k =
      -(FurtherOptical.energy m k:ℂ) • seaEnergyBand false m k := by
  let v := FurtherOptical.coefficients m 0 k
  have hsq : diracSlash v*diracSlash v = 1 := by
    rw [diracSlash_sq,FurtherOptical.coefficients_norm_sq hm (le_refl (0:ℝ)),Complex.ofReal_one,one_smul]
  have he : (1-FurtherOptical.projector v)*diracSlash v=1-FurtherOptical.projector v ∧
      diracSlash v*FurtherOptical.projector v= -FurtherOptical.projector v := by
    unfold FurtherOptical.projector
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hsq]
    constructor <;> module
  rw [hamiltonian_polar hm]
  change (1-FurtherOptical.projector v)*(_ • diracSlash v) = _ ∧ (_ • diracSlash v)*FurtherOptical.projector v=_
  simp only [mul_smul_comm,smul_mul_assoc,he.1,he.2,smul_neg,neg_smul,seaEnergyBand,if_true,Bool.false_eq_true,if_false,v,true_and]

theorem free_current_ward {m : ℝ} (hm : 0<m) (P k : ChargeSpatialMomentum) :
    (relativeEnergy m P k:ℂ) • currentBlock m P k 0 =
    ∑ j : Fin 3, (P j:ℂ) • currentBlock m P k j.succ := by
  let A := seaEnergyBand true m k
  let B := seaEnergyBand false m (k-P)
  let H := fun k => diracSlash (massiveCarrier m k)
  have hγ (j:Fin 3) : currentGamma j.succ=euclideanGamma j.succ := by
    rw [currentGamma,if_neg (Fin.succ_ne_zero _)]
    exact diracSlash_single _
  have hH : H k-H (k-P) = ∑ j:Fin 3, (P j:ℂ) • currentGamma j.succ := by
    rw [show H k-H (k-P) = diracSlash (massiveCarrier m k-massiveCarrier m (k-P)) from (FurtherOptical.slash_sub _ _).symm]
    unfold diracSlash
    rw [Fin.sum_univ_succ]
    simp only [PiLp.sub_apply,hγ]
    change ((m-m:ℝ):ℂ) • _ + ∑j:Fin 3, ((k j-(k j-P j):ℝ):ℂ) • _ = _
    simp
  have he : FurtherOptical.energy m (k-P)=FurtherOptical.energy m (P-k) := by
    unfold FurtherOptical.energy
    rw [norm_sub_rev]
  calc _ = ((FurtherOptical.energy m k:ℂ)+(FurtherOptical.energy m (k-P):ℂ)) • (A*B) := by
          simp [relativeEnergy,currentBlock,currentGamma,he,A,B]
    _ = (A*H k)*B - A*(H (k-P)*B) := by
      rw [(band_eigenvalues hm k).1,(band_eigenvalues hm (k-P)).2,smul_mul_assoc,mul_smul_comm,neg_smul,sub_neg_eq_add,add_smul]
    _ = A*(H k-H (k-P))*B := by noncomm_ring
    _ = _ := by simp only [hH,Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm,A,B,currentBlock]

def physicalPairTensor (m ℓ : ℝ) (P k : ChargeSpatialMomentum) (i j : Fin 4) : DiracMatrix :=
  (-Complex.I * (Real.exp (-(ℓ^4)*invariantMassSq m P k^2):ℂ)) • spinTensor m P k i j

/-- The factor iP from the first background variation cancels the −i
in the specified pair tensor. Its time and spatial components retain
the exact Dirac current with the single invariant-mass form factor. -/
theorem physical_pair_current {m : ℝ} (hm : 0<m) (ℓ : ℝ) (P k : ChargeSpatialMomentum) (j : Fin 4) :
    Complex.I • (∑ i : Fin 4, ((metricSign i*totalComponent m P k i:ℝ):ℂ) • physicalPairTensor m ℓ P k i j) =
    (Real.exp (-(ℓ^4)*invariantMassSq m P k^2):ℂ) • currentBlock m P k j := by
  let T := totalComponent m P k
  let J := currentBlock m P k
  let s := invariantMassSq m P k
  have hs : s≠0 := ne_of_gt ((show 0<4*m^2 by positivity).trans_le (invariantMassSq_threshold hm P k))
  have ward : (∑ i : Fin 4, ((metricSign i*T i:ℝ):ℂ) • J i)=0 := by
    have h := free_current_ward hm P k
    rw [Fin.sum_univ_succ]
    simp [metricSign,T,totalComponent,J,Fin.succ_ne_zero,h]
  have mass : (∑ i : Fin 4, ((metricSign i*T i*T i:ℝ):ℂ)) = (s:ℂ) := by
    rw [←Complex.ofReal_sum]
    congr 1
    dsimp only [s,invariantMassSq]
    rw [Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq]
    simp [T,totalComponent,metricSign,Fin.succ_ne_zero,Real.norm_eq_abs,pow_two,sub_eq_add_neg]
  let f : ℂ := Real.exp (-(ℓ^4)*s^2)
  have term (i : Fin 4) : ((metricSign i*T i:ℝ):ℂ) • physicalPairTensor m ℓ P k i j =
      (-Complex.I*f*(s:ℂ)⁻¹) •
      (((metricSign i*T i*T i:ℝ):ℂ) • J j -
      (T j:ℂ) • (((metricSign i*T i:ℝ):ℂ) • J i)) := by
    dsimp only [physicalPairTensor,spinTensor,T,J,s,f]
    push_cast
    module
  change Complex.I • (∑ i : Fin 4, ((metricSign i*T i:ℝ):ℂ) • physicalPairTensor m ℓ P k i j)= f • J j
  simp_rw [term]
  rw [←Finset.smul_sum,Finset.sum_sub_distrib,←Finset.sum_smul,←Finset.smul_sum,mass,ward,smul_zero,sub_zero,smul_smul,smul_smul]
  congr 1
  field_simp [hs]
  ring_nf
  simp [Complex.I_sq]

theorem spectral_tail_and_threshold {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) :
    (∀ s < 4*m^2, massDensity m ℓ s=0) ∧
    (∀ s > 4*m^2, 0<massDensity m ℓ s) ∧
    MeasureTheory.IntegrableOn (fun s => massDensity m ℓ s/s) (Set.Ioi (4*m^2)) := by
  refine ⟨fun s hs => if_neg (not_le.mpr hs),fun s hs => massDensity_pos hm hs ℓ,?_⟩
  have hd : 0<4*m^2 := by positivity
  apply ((massDensity_integrable m hℓ).div_const (4*m^2)).integrableOn.mono'
  · exact ((measurable_massDensity m ℓ).div measurable_id).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0<s := hd.trans hs
    rw [Real.norm_of_nonneg (div_nonneg (massDensity_nonneg ..) hs'.le)]
    exact div_le_div_of_nonneg_left (massDensity_nonneg ..) hd hs.le

/-- Positive and negative external frequency give the two one-sided
time orderings used by the Euclidean two-source transfer. -/
theorem ordered_pair_frequency {D : ℝ} (hD : 0<D) (ω : ℝ) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp ((-((D:ℂ)+Complex.I*(ω:ℂ)))*(t:ℂ))) =
      ((D:ℂ)+Complex.I*(ω:ℂ))⁻¹ := by
  have h : (-((D:ℂ)+Complex.I*(ω:ℂ))).re<0 := by simpa using hD
  rw [integral_exp_mul_complex_Ioi h]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq,one_div]

end UV.PairCurvature
