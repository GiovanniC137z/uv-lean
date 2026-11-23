import UV.ContinueSourceReviewLocality
import UV.ContinueRelativeCharge

/-! The beginning of the instantaneous locality test at zero electric coupling:
the actual spatial derivative of a lifted Gaussian and the occupied-to-empty
mass block on the four-component spin space. -/

noncomputable section
open MeasureTheory Filter Set UV.SectorPlane Matrix
open scoped Topology RealInnerProductSpace Matrix

namespace UV

def seaSpatialHeat (τ : ℝ) (z : Spatial) : ℝ :=
  (4*Real.pi*τ)^(-(3:ℝ)/2)*Real.exp (-‖z‖^2/(4*τ))

/-- Directional derivative of the normalized three-dimensional Gaussian in
the `j`th unit spatial direction on the sector plane. -/
theorem sea_spatial_heat_deriv (τ : ℝ) (z : Spatial) (j : Fin 3) :
    HasDerivAt (fun t : ℝ => seaSpatialHeat τ (z+t • EuclideanSpace.single j 1))
      (-z j/(2*τ)*seaSpatialHeat τ z) 0 := by
  let v : Spatial := EuclideanSpace.single j 1
  have hf : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
    simpa only [id_eq,one_smul,zero_add,Pi.add_def] using (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have h := ((((hf.norm_sq.neg).div_const (4*τ)).exp).const_mul ((4*Real.pi*τ)^(-(3:ℝ)/2)))
  convert h using 1
  simp [seaSpatialHeat,v,EuclideanSpace.inner_single_right]
  ring

def seaHeatPairBlock (τ ν : ℝ) (z : Spatial) : DiracMatrix :=
  (-Complex.I*(ν:ℂ)) • ∑ j : Fin 3, ((-z j/(2*τ)*seaSpatialHeat τ z:ℝ):ℂ) •
    (chordRestProjector * euclideanGamma j.succ * (1-chordRestProjector))

private theorem sea_mass_pair_gamma_entry (j : Fin 3) :
    (chordRestProjector*euclideanGamma j.succ*(1-chordRestProjector)) 0 0 =
      if j=0 then Complex.I/2 else 0 := by
  have row (i : Fin 4) : chordRestProjector 0 i = ![1/2,0,1/2,0] i := by
    fin_cases i
    · change (1/2:ℂ)*(1+0)=1/2; ring
    · change (1/2:ℂ)*(0+0)=0; ring
    · change (1/2:ℂ)*(0+1)=1/2; ring
    · change (1/2:ℂ)*(0+0)=0; ring
  have col (i : Fin 4) : ((1:DiracMatrix)-chordRestProjector) i 0 = ![1/2,0,-1/2,0] i := by
    fin_cases i
    · change 1-(1/2:ℂ)*(1+0)=1/2; ring
    · change 0-(1/2:ℂ)*(0+0)=0; ring
    · change 0-(1/2:ℂ)*(0+1) = -1/2; ring
    · change 0-(1/2:ℂ)*(0+0)=0; ring
  have hentry (C : DiracMatrix) : (chordRestProjector*C*(1-chordRestProjector)) 0 0 =
      (C 0 0-C 0 2+C 2 0-C 2 2)/4 := by
    simp only [Matrix.mul_apply,row,col,Fin.sum_univ_succ]
    simp
    ring
  rw [hentry]
  fin_cases j
  · change (0-(-Complex.I)+Complex.I-0)/4=Complex.I/2; ring
  · change (0-0+0-0 : ℂ)/4=0; ring
  · change (0-0+0-0 : ℂ)/4=0; ring

/-- An exact matrix entry of the creation kernel at a separated displacement. -/
theorem sea_heat_pair_entry (τ ν : ℝ) (z : Spatial) :
    seaHeatPairBlock τ ν z 0 0 = ((-ν*z 0/(4*τ)*seaSpatialHeat τ z : ℝ):ℂ) := by
  rw [seaHeatPairBlock,Matrix.smul_apply,Matrix.sum_apply]
  simp_rw [Matrix.smul_apply,sea_mass_pair_gamma_entry]
  simp only [smul_eq_mul,Fin.sum_univ_three,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat]
  norm_num [show (2:Fin 3) ≠ 0 by decide]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem sea_heat_pair_entry_ne_zero {τ ν : ℝ} (hτ : 0 < τ) (hν : ν ≠ 0)
    {z : Spatial} (hz : z 0 ≠ 0) : seaHeatPairBlock τ ν z 0 0 ≠ 0 := by
  rw [sea_heat_pair_entry,Complex.ofReal_ne_zero]
  apply mul_ne_zero (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hν) hz) (by positivity))
  unfold seaSpatialHeat
  positivity

/-- Nonzero first axial Fourier mode of the heat-spin hopping in a periodic
box. Here `q` is the magnitude of the first reciprocal spatial vector. -/
theorem sea_heat_pair_axial_symbol {ν q : ℝ} (hν : ν ≠ 0) (hq : 0 < q) (τ : ℝ) :
    let A := ((ν*q*Real.exp (-τ*q^2):ℝ):ℂ) •
      (chordRestProjector*euclideanGamma 1*(1-chordRestProjector))
    A 0 0 ≠ 0 := by
  have h := sea_mass_pair_gamma_entry 0
  dsimp at h
  change ((ν*q*Real.exp (-τ*q^2):ℝ):ℂ) * _ ≠ 0
  rw [h]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero hν hq.ne') (Real.exp_ne_zero _)))
    (div_ne_zero Complex.I_ne_zero (by norm_num))

/-- A square-integrable spatial kernel with a nonzero Fourier matrix element
cannot be concentrated on coincident particle and hole positions. The
statement applies to continuum charts and periodic coordinates with atomless
spatial volume. -/
theorem sea_fourier_pair_separated {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [SFinite μ] [NoAtoms μ] (K χ : X × X → ℂ)
    (hdiag : MeasurableSet {a : X × X | a.1 = a.2})
    (hFourier : ∫ a, χ a*K a ∂μ.prod μ ≠ 0) :
    ¬ ∀ᵐ a ∂μ.prod μ, a.1 ≠ a.2 → K a = 0 := by
  have hd : ∀ᵐ a ∂μ.prod μ, a.1 ≠ a.2 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun a : X×X => a.1 ≠ a.2) hdiag.compl).2
    apply Eventually.of_forall
    intro x
    rw [ae_iff]
    simp
  intro hall
  apply hFourier
  rw [integral_congr_ae (g := fun _ => 0) (by
    filter_upwards [hd,hall] with a ha hK
    simp [hK ha]),integral_zero]

end UV
