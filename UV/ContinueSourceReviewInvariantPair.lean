import UV.ContinuationSectorPlane
import UV.ContinueFiveBallPortalSpin
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Timelike cut weights and contact costs for the on-shell classical-current
model at expanded manuscript lines 24100–24167. The coefficient of its cut
is evaluated on a fixed locked sector plane; the oriented pole unit is the
one carried by that plane. -/

noncomputable section
open MeasureTheory Filter Set Asymptotics UV.SectorPlane
open scoped Topology Asymptotics

namespace UV

/-- Squared modulus of the on-shell normal readout extracted on either rim.
The square root on the cut has imaginary coefficient of the appropriate
signed magnitude, and the signed magnitude drops out of this norm square. -/
theorem sea_timelike_readout_square {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε : Evolution) (ℓ m s : ℝ) (N : ℕ) (hs : (2*m)^2 ≤ s) :
    Complex.normSq ((((1+ℓ*(2*m):ℝ):ℂ) /
      (1+Complex.I*((diamond.eta ε * ℓ * Real.sqrt (s-(2*m)^2) : ℝ):ℂ)))^N) =
      (1+ℓ*(2*m))^(2*N)/(1+ℓ^2*(s-(2*m)^2))^N := by
  let x := diamond.eta ε * ℓ * Real.sqrt (s-(2*m)^2)
  have h : Complex.normSq (1+Complex.I*(x:ℂ)) = 1+ℓ^2*(s-(2*m)^2) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,one_mul,sub_zero,add_zero,zero_add,one_mul,mul_zero]
    dsimp only [x]
    nlinarith [diamond.eta_sq ε,Real.sq_sqrt (sub_nonneg.mpr hs),
      congrArg (fun t : ℝ => t*ℓ^2*(Real.sqrt (s-(2*m)^2))^2) (diamond.eta_sq ε),
      congrArg (fun t : ℝ => ℓ^2*t) (Real.sq_sqrt (sub_nonneg.mpr hs))]
  rw [map_pow,Complex.normSq_div,h,Complex.normSq_ofReal,div_pow,pow_mul]
  ring

/-- Formula on the physical two-particle half-line `s ≥ (2m)²`. -/
def seaInvariantPairDensity (e m ℓ : ℝ) (N : ℕ) (s : ℝ) :=
  e^2/(12*Real.pi^2)*Real.sqrt (1-(2*m)^2/s)*(1+2*m^2/s)*
    (1+ℓ*(2*m))^(2*N)/(1+ℓ^2*(s-(2*m)^2))^N

def seaInvariantPairTail (e m ℓ : ℝ) (N : ℕ) :=
  e^2/(12*Real.pi^2)*(1+ℓ*(2*m))^(2*N)/(ℓ^2)^N

theorem sea_invariant_pair_tail (e m : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    Tendsto (fun s : ℝ => s^N*seaInvariantPairDensity e m ℓ N s) atTop
      (𝓝 (seaInvariantPairTail e m ℓ N)) := by
  let G (t : ℝ) := e^2/(12*Real.pi^2)*Real.sqrt (1-(2*m)^2*t)*(1+2*m^2*t)*
    (1+ℓ*(2*m))^(2*N)/(ℓ^2+(1-ℓ^2*(2*m)^2)*t)^N
  have hc : ContinuousAt G 0 := by dsimp only [G]; fun_prop (disch := simp [hℓ.ne'])
  have h := hc.tendsto.comp (tendsto_inv_atTop_zero : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  have h0 : G 0 = seaInvariantPairTail e m ℓ N := by simp [G,seaInvariantPairTail]
  rw [← h0]
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  have heq : 1+ℓ^2*(s-(2*m)^2)=s*(ℓ^2+(1-ℓ^2*(2*m)^2)*s⁻¹) := by field_simp; ring
  dsimp only [Function.comp_apply,G,seaInvariantPairDensity]
  rw [heq,mul_pow s _ N]
  rw [←mul_div_assoc,mul_div_mul_left _ _ (pow_ne_zero N hs.ne')]
  simp only [div_eq_mul_inv]

private theorem sea_density_continuousOn {e m ℓ : ℝ} (hm : 0 < m) (N : ℕ) :
    ContinuousOn (seaInvariantPairDensity e m ℓ N) (Ici ((2*m)^2)) := by
  intro s hs
  have hs' : 0 < s := (sq_pos_of_pos (by positivity : 0 < 2*m)).trans_le hs
  have hd : 0 < 1+ℓ^2*(s-(2*m)^2) := by nlinarith [mul_nonneg (sq_nonneg ℓ) (sub_nonneg.mpr hs)]
  apply ContinuousAt.continuousWithinAt
  unfold seaInvariantPairDensity
  fun_prop (disch := first | exact hs'.ne' | exact pow_ne_zero _ hd.ne')

private theorem sea_pair_orders {e m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ)
    (he : e ≠ 0) :
    seaInvariantPairDensity e m ℓ N =O[atTop] (fun s : ℝ => s^(-(N:ℝ))) ∧
      (fun s : ℝ => s^(-(N:ℝ))) =O[atTop] seaInvariantPairDensity e m ℓ N := by
  let f := seaInvariantPairDensity e m ℓ N
  let g (s : ℝ) := s^(-(N:ℝ))
  let C := seaInvariantPairTail e m ℓ N
  have hC : 0 < C := by dsimp [C,seaInvariantPairTail]; positivity
  have h : Tendsto (f/g) atTop (𝓝 C) := by
    refine (sea_invariant_pair_tail e m hℓ N).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    simp only [Pi.div_apply,g,Real.rpow_neg hs.le,Real.rpow_natCast,div_inv_eq_mul]
    exact mul_comm _ _
  have hg : ∀ᶠ s in atTop, g s ≠ 0 := (eventually_gt_atTop (0:ℝ)).mono fun s hs => (Real.rpow_pos_of_pos hs _).ne'
  have hf : ∀ᶠ s in atTop, f s ≠ 0 := by
    filter_upwards [h.eventually_ne hC.ne'] with s hs using fun hz => hs (by simp [Pi.div_apply,hz])
  refine ⟨isBigO_of_div_tendsto_nhds (hg.mono fun _ h' hz => (h' hz).elim) C h,?_⟩
  apply isBigO_of_div_tendsto_nhds (hf.mono fun _ h' hz => (h' hz).elim) C⁻¹
  simpa only [Pi.inv_def,Pi.div_apply,inv_div] using h.inv₀ hC.ne'

/-- Sharp contact-cost criterion on the whole timelike ray. In particular
one interval has infinite contact cost at nonzero coupling, while the
zero-charge density vanishes at every order. -/
theorem sea_invariant_contact_iff {e m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ) :
    IntegrableOn (seaInvariantPairDensity e m ℓ N) (Ici ((2*m)^2)) ↔ e=0 ∨ 2 ≤ N := by
  by_cases he : e=0
  · subst e
    have hz : seaInvariantPairDensity 0 m ℓ N = 0 := by ext s; simp [seaInvariantPairDensity]
    simp only [hz,true_or,iff_true]
    exact integrable_zero _ _ _
  have h := sea_pair_orders hm hℓ N he
  have hc : LocallyIntegrableOn (seaInvariantPairDensity e m ℓ N) (Ici ((2*m)^2)) volume := (sea_density_continuousOn (e:=e) (ℓ:=ℓ) hm N).locallyIntegrableOn measurableSet_Ici
  constructor
  · intro hi
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => s^(-(N:ℝ))) atTop volume := by
      have hgm : Measurable (fun s : ℝ => s^(-(N:ℝ))) := by fun_prop
      exact ⟨univ,univ_mem,hgm.aestronglyMeasurable⟩
    have hg := h.2.integrableAtFilter hmeas (integrableOn_Ici_iff_integrableAtFilter_atTop.mp hi).1
    have hn := integrableAtFilter_rpow_atTop_iff.mp hg
    right
    by_contra! hN
    have : (N:ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by omega)
    linarith
  · rintro (hz|hN)
    · contradiction
    · apply hc.integrableOn_of_isBigO_atTop h.1
      exact integrableAtFilter_rpow_atTop_iff.mpr (by exact_mod_cast (show -(N:ℤ)< -1 by omega))

/-- The unsubtracted scalar dispersion integral already converges at one
normal interval, even if the separate contact has infinite mass. -/
theorem sea_invariant_scalar_dispersion {e m ℓ x : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ)
    (hx : 0 ≤ x) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun s => seaInvariantPairDensity e m ℓ N s/(s+x)) (Ici ((2*m)^2)) := by
  let f := seaInvariantPairDensity e m ℓ N
  let g (s : ℝ) := s^(-((N+1:ℕ):ℝ))
  have hlim : Tendsto ((fun s => f s/(s+x))/g) atTop (𝓝 (seaInvariantPairTail e m ℓ N)) := by
    have hdiv : Tendsto (fun s : ℝ => (1+x*s⁻¹)⁻¹) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_inv_atTop_zero.const_mul x)).inv₀ (by simp)
    have h := (sea_invariant_pair_tail e m hℓ N).mul hdiv
    rw [mul_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    simp only [f,g,Pi.div_apply,Real.rpow_neg hs.le,Real.rpow_natCast,div_inv_eq_mul,pow_succ]
    field_simp [hs.ne',(add_pos_of_pos_of_nonneg hs hx).ne']
  have hg : ∀ᶠ s in atTop, g s ≠ 0 := (eventually_gt_atTop (0:ℝ)).mono fun _ hs => (Real.rpow_pos_of_pos hs _).ne'
  have hB := isBigO_of_div_tendsto_nhds (hg.mono fun _ h' hz => (h' hz).elim) _ hlim
  have hc : ContinuousOn (fun s => f s/(s+x)) (Ici ((2*m)^2)) := by
    apply (sea_density_continuousOn hm _).div (continuous_id.add continuous_const).continuousOn
    intro s hs
    exact (add_pos_of_pos_of_nonneg ((sq_pos_of_pos (by positivity : 0 < 2*m)).trans_le hs) hx).ne'
  apply (hc.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hB
  exact integrableAtFilter_rpow_atTop_iff.mpr (by push_cast; linarith [show 1 ≤ (N:ℝ) by exact_mod_cast hN])

/-- Exact contact-minus-dispersion identity for two or more intervals,
with both integrals finite in the original spectral variable. -/
theorem sea_invariant_current_transform {e m ℓ x : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ)
    (hx : 0 ≤ x) {N : ℕ} (hN : 2 ≤ N) :
    let f := seaInvariantPairDensity e m ℓ N
    IntegrableOn (fun s => s*f s/(s+x)) (Ici ((2*m)^2)) ∧
      (∫ s in Ici ((2*m)^2), s*f s/(s+x)) =
        (∫ s in Ici ((2*m)^2), f s) - x*(∫ s in Ici ((2*m)^2), f s/(s+x)) := by
  let f := seaInvariantPairDensity e m ℓ N
  have hc := (sea_invariant_contact_iff (e:=e) hm hℓ N).2 (Or.inr hN)
  have hd := sea_invariant_scalar_dispersion (e:=e) hm hℓ hx (show 1 ≤ N by omega)
  have hEq : (fun s => s*f s/(s+x)) =ᵐ[volume.restrict (Ici ((2*m)^2))] fun s => f s-x*(f s/(s+x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hs' := (sq_pos_of_pos (by positivity : 0 < 2*m)).trans_le hs
    field_simp [(add_pos_of_pos_of_nonneg hs' hx).ne']; ring
  refine ⟨(hc.sub (hd.const_mul x)).congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq,integral_sub hc (hd.const_mul x),integral_const_mul]

/-- The cut density is obtained directly from the four-slot occupied and
empty Dirac energy projectors, rest-frame phase space and the squared
normal readout on either oriented timelike rim. -/
theorem sea_invariant_cut_from_spin {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε : Evolution) (e ℓ : ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (k : ChargeSpatialMomentum) (hk : k ≠ 0) :
    let y := 2*FurtherOptical.energy m k
    let spin := (∑ i : Fin 3, (portalPairTrace (FurtherOptical.coefficients m 0 k) i).re)/3
    (4*Real.pi/(2*Real.pi)^3)*‖k‖^2*(y/(4*‖k‖))*spin/y^2 *
      (e^2*Complex.normSq ((((1+ℓ*(2*m):ℝ):ℂ) /
        (1+Complex.I*((diamond.eta ε * ℓ * Real.sqrt (y^2-(2*m)^2):ℝ):ℂ)))^N)) =
      seaInvariantPairDensity e m ℓ N (y^2) := by
  let y := 2*FurtherOptical.energy m k
  have hy : 0 < y := mul_pos (by norm_num) (FurtherOptical.energy_pos hm _)
  have hs : 4*m^2 ≤ y^2 := by dsimp only [y]; nlinarith [FurtherOptical.energy_sq m k,sq_nonneg ‖k‖]
  have h := portal_cut_from_spin (b := y^2/2) hm k hk
  dsimp only
  change _ = seaInvariantPairDensity e m ℓ N (y^2)
  change _*((y^2/2)^2/(y^2-y^2/2)^2) = portalPairCut m (y^2/2) (y^2) at h
  rw [portalPairCut,if_pos hs,show (y^2/2)^2/(y^2-y^2/2)^2=1 by field_simp; ring,mul_one,one_mul,
    openingWeight_eq_of_nonneg (by positivity)] at h
  rw [sea_timelike_readout_square diamond ε ℓ m _ N (by nlinarith),h,seaInvariantPairDensity]
  rw [show (2*m)^2=4*m^2 by ring,show 4*m^2/y^2/2=2*m^2/y^2 by ring]
  ring

end UV
