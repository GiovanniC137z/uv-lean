import UV.ContinueSourceReviewClassicalLoop
import UV.ContinueNormalCircleWord
import UV.ContinueWilsonSpinNorm
import UV.NextOpticalRadial
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual free-spinor slot estimates and joint packet, loop and finite-slab
integrability for the on-shell current with independent normal intervals. -/

noncomputable section
open MeasureTheory Filter Set Matrix UV.FurtherOptical UV.SectorPlane
open scoped Topology BigOperators Matrix.Norms.L2Operator SchwartzMap

namespace UV

def seaEnergyBand (b : Bool) (m : ℝ) (k : Spatial) : DiracMatrix :=
  if b then 1-projector (coefficients m 0 k) else projector (coefficients m 0 k)

theorem sea_energy_band_contraction (b : Bool) {m : ℝ} (hm : 0 < m) (k : Spatial) :
    ‖seaEnergyBand b m k‖ ≤ 1 := by
  let v := coefficients m 0 k
  have h1 : ‖v‖=1 := by nlinarith [coefficients_norm_sq hm le_rfl k,norm_nonneg v]
  have hhalf : ‖(1/2:ℂ)‖=1/2 := by norm_num
  cases b
  · change ‖(1/2:ℂ) • (1-diracSlash v)‖ ≤ 1
    rw [norm_smul,hhalf]
    have h := norm_sub_le (1:DiracMatrix) (diracSlash v)
    rw [norm_one,wilson_slash_opnorm,h1] at h
    linarith
  · change ‖1-(1/2:ℂ) • (1-diracSlash v)‖ ≤ 1
    rw [show (1:DiracMatrix)-(1/2:ℂ) • (1-diracSlash v)=(1/2:ℂ) • (1+diracSlash v) by module,norm_smul,hhalf]
    have h := norm_add_le (1:DiracMatrix) (diracSlash v)
    rw [norm_one,wilson_slash_opnorm,h1] at h
    linarith

/-- The density vertex and the spatial current polarized along a genuine
unit spatial vector have operator norm one in the four-component spinor. -/
theorem sea_physical_slot_current_norm (n : UnitVector Spatial) :
    ‖(1 : DiracMatrix)‖ = 1 ∧ ‖diracSlash (NextOpticalRadial.spinCoefficients 0 1 n)‖ = 1 := by
  refine ⟨norm_one, ?_⟩
  rw [wilson_slash_opnorm]
  nlinarith [NextOpticalRadial.spinCoefficients_norm_sq 0 1 n,
    norm_nonneg (NextOpticalRadial.spinCoefficients 0 1 n)]

/-- A free current insertion, including its two energy projections, unit
spatial polarization (or scalar density), and intervening Euclidean propagation.
The time separation is nonnegative along the selected band. -/
theorem sea_spin_slot_bound (v w : Spatial) (a b : Bool) {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t)
    (J : DiracMatrix) (hJ : ‖J‖ ≤ 1) :
    ‖((Real.exp (-t*energy m w):ℝ):ℂ) • (seaEnergyBand a m v*J*seaEnergyBand b m w)‖ ≤ 1 := by
  have hmat : ‖seaEnergyBand a m v*J*seaEnergyBand b m w‖ ≤ 1 := by
    calc _ ≤ ‖seaEnergyBand a m v*J‖ * ‖seaEnergyBand b m w‖ := norm_mul_le _ _
         _ ≤ (‖seaEnergyBand a m v‖*‖J‖)*‖seaEnergyBand b m w‖ := by gcongr; exact norm_mul_le _ _
         _ ≤ (1*1)*1 := by gcongr <;> exact sea_energy_band_contraction _ hm _
         _ = 1 := by norm_num
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hx := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (energy_pos hm w).le)
  calc _ ≤ 1*1 := mul_le_mul hx hmat (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

theorem sea_spin_word_trace_bound {n : ℕ} (A : Fin n → DiracMatrix) (hA : ∀ i, ‖A i‖ ≤ 1) :
    ‖(normalOrderedWord A).trace‖ ≤ 4 := by
  apply (wilson_trace_le_opnorm _).trans
  suffices h : ‖normalOrderedWord A‖ ≤ 1 by linarith
  apply ((List.ofFn A).norm_prod_le).trans
  rw [List.map_ofFn,List.prod_ofFn]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hA i)

/-- A Schwartz packet absorbs any fixed power of the external momentum. -/
theorem sea_packet_integrable {d : ℕ} (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ)) (n : ℕ) :
    Integrable (fun q => (1+‖q‖)^n*‖χ q‖) := by
  have hi := ((χ.integrable (μ := volume)).norm.add (χ.integrable_pow_mul volume n)).const_mul (2^n:ℝ)
  apply hi.mono' (by fun_prop)
  apply Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  by_cases h : ‖q‖ ≤ 1
  · have h1 : (1+‖q‖)^n ≤ 2^n := pow_le_pow_left₀ (by positivity) (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (χ q)),
      mul_nonneg (show 0 ≤ (2:ℝ)^n by positivity) (mul_nonneg (pow_nonneg (norm_nonneg q) n) (norm_nonneg (χ q)))]
  · have h1 : (1+‖q‖)^n ≤ (2*‖q‖)^n := pow_le_pow_left₀ (by positivity) (by linarith) _
    rw [mul_pow] at h1
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (χ q)),
      mul_nonneg (show 0 ≤ (2:ℝ)^n by positivity) (norm_nonneg (χ q))]

/-- Joint integration over arbitrary finitely many independently circulating
three-momenta, a common Schwartz external test, and the ordered slab times.
The measure `μ` is any finite restriction on the time variables, in
particular Lebesgue measure on their ordered finite-slab simplex. -/
theorem sea_tested_cycle_integrability {d n h : ℕ} {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ] (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ))
    {N : ℕ} (hN : 2 ≤ N) (C : ℝ) (F : T × (EuclideanSpace ℝ (Fin d) × (Fin h → Spatial)) → ℂ)
    (hF : AEStronglyMeasurable F (μ.prod (volume.prod volume)))
    (hbound : ∀ z, ‖F z‖ ≤ C * ((1+‖z.2.1‖)^n*‖χ z.2.1‖) *
      ∏ j, (1+‖z.2.2 j‖)^(-((2*N:ℕ):ℝ))) :
    Integrable F (μ.prod (volume.prod volume)) := by
  have hloop : Integrable (fun k : Spatial => (1+‖k‖)^(-((2*N:ℕ):ℝ))) volume :=
    integrable_one_add_norm (by simpa using (show (3:ℝ) < (2*N:ℕ) by exact_mod_cast (show 3 < 2*N by omega)))
  have hprod := Integrable.fintype_prod (ι := Fin h) (fun _ => hloop)
  have hq := (sea_packet_integrable χ n).const_mul C
  have htime : Integrable (fun _ : T => (1:ℝ)) μ := integrable_const _
  have hall := htime.mul_prod (hq.mul_prod hprod)
  apply hall.mono' hF
  apply Eventually.of_forall
  intro z
  simpa only [one_mul] using hbound z

/-- Affine momentum routes make the loss in each loop estimate a polynomial
in the external packet coordinate, including nonzero fixed offsets. -/
theorem sea_affine_loop_cost {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Spatial) (L : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] Spatial)
    {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin d)) :
    seaLoopRoutingCost m ℓ (fun i => a i + L i q) ≤
      ((5+ℓ⁻¹)*(1+m+2*∑ i, (‖a i‖+‖L i‖)))*(1+‖q‖) := by
  have hs : (∑ i, ‖a i+L i q‖) ≤ (∑ i, (‖a i‖+‖L i‖))*(1+‖q‖) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hl := (L i).le_opNorm q
    linarith [norm_add_le (a i) (L i q),mul_nonneg (norm_nonneg (a i)) (norm_nonneg q),norm_nonneg (L i)]
  unfold seaLoopRoutingCost
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hm.le (norm_nonneg q),norm_nonneg q]

/-- Explicit bound for independent circulating momenta when each cycle
uses its own permutation of ordered source vertices and affine routes. -/
theorem sea_joint_classical_loop_bound {d h : ℕ} {ι : Fin h → Type*}
    [∀ j,Fintype (ι j)] [∀ j,Nonempty (ι j)]
    (σ : ∀ j, Equiv.Perm (ι j)) (t : ∀ j, ι j → ℝ) (band : ∀ j, ι j → Bool)
    (ordered : ∀ j i, if band j i then t j i < t j (σ j i) else t j (σ j i) < t j i)
    (a : ∀ j, ι j → Spatial) (L : ∀ j, ι j → EuclideanSpace ℝ (Fin d) →L[ℝ] Spatial)
    {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ) (q : EuclideanSpace ℝ (Fin d))
    (k : Fin h → Spatial) :
    let B j := (5+ℓ⁻¹)*(1+m+2*∑ i, (‖a j i‖+‖L j i‖))
    (∏ j, seaClassicalLoopReadout (σ j) (band j) (fun i => a j i+L j i q) m ℓ N (k j)) ≤
      (∏ j, ((1+ℓ*(2*m))^(Fintype.card (ι j))*(B j)^2)^N) *
      (1+‖q‖)^(2*N*h) * ∏ j, (1+‖k j‖)^(-((2*N:ℕ):ℝ)) := by
  let B j := (5+ℓ⁻¹)*(1+m+2*∑ i, (‖a j i‖+‖L j i‖))
  let C j := ((1+ℓ*(2*m))^(Fintype.card (ι j))*(B j)^2)^N
  let W (j : Fin h) := (1+‖k j‖)^(-((2*N:ℕ):ℝ))
  have hpos j : 0 ≤ seaLoopRoutingCost m ℓ (fun i => a j i+L j i q) := by
    dsimp [seaLoopRoutingCost]; positivity
  have hbound j := sea_classical_loop_budget (σ j) (t j) (band j) (ordered j)
    (fun i => a j i+L j i q) hm hℓ N (k j)
  have hsingle j : seaClassicalLoopReadout (σ j) (band j) (fun i => a j i+L j i q) m ℓ N (k j)
      ≤ C j*(1+‖q‖)^(2*N)*W j := by
    apply (hbound j).trans
    calc _ ≤ ((1+ℓ*(2*m))^(Fintype.card (ι j))*(B j*(1+‖q‖))^2)^N / (1+‖k j‖)^(2*N) := by
           gcongr <;> first | exact hpos j | exact sea_affine_loop_cost (a j) (L j) hm hℓ q
         _ = _ := by
           dsimp only [C,W]
           rw [Real.rpow_neg (by positivity),Real.rpow_natCast,mul_pow (B j),←mul_assoc,mul_pow,←pow_mul,div_eq_mul_inv]
  apply (Finset.prod_le_prod (fun j _ => ?_) (fun j _ => hsingle j)).trans_eq
  · rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
  · unfold seaClassicalLoopReadout
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (div_nonneg (by positivity) (zero_le_one.trans (sea_mark_den_ge_one _ _ hℓ _ _))) _

/-- The two rims at a timelike transfer on the fixed plane are conjugates.
The complex mark uses the square root approached from below for the
positive signed energy transfer in `F(s+i0 sgn q⁰)`. For elastic
transfer the square root is real. -/
def seaRimMark {E : Type*} [NormedAddCommGroup E] (diamond : Plane E) (ε : Evolution)
    (b : Bool) (m ℓ : ℝ) (N : ℕ) (v w : Spatial) : ℂ :=
  if b then
    let s := seaTransferSq true m v w
    (((1+ℓ*(2*m):ℝ):ℂ) /
      (1-Complex.I*((diamond.eta ε * ℓ * Real.sqrt (s-(2*m)^2):ℝ):ℂ)))^N
  else (((1+ℓ*(2*m))/seaMarkDen false m ℓ v w:ℝ):ℂ)^N

theorem sea_rim_mark_norm {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε : Evolution) (b : Bool) {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ)
    (v w : Spatial) : ‖seaRimMark diamond ε b m ℓ N v w‖ =
      ((1+ℓ*(2*m))/seaMarkDen b m ℓ v w)^N := by
  let C := 1+ℓ*(2*m)
  have hC : 0 < C := by dsimp only [C]; positivity
  cases b
  · rw [seaRimMark,if_neg (by decide),norm_pow, Complex.norm_real,Real.norm_of_nonneg]
    exact div_nonneg hC.le (zero_le_one.trans (sea_mark_den_ge_one _ _ hℓ _ _))
  · let s := seaTransferSq true m v w
    let x := diamond.eta ε * ℓ * Real.sqrt (s-(2*m)^2)
    have hs : (2*m)^2 ≤ s := (sea_transfer_kinematics _ _ _).2
    have hx : x^2 = ℓ^2*(s-(2*m)^2) := by
      dsimp only [x]
      rw [mul_pow,mul_pow,diamond.eta_sq,one_mul,Real.sq_sqrt (sub_nonneg.mpr hs)]
    have hd : ‖1-Complex.I*(x:ℂ)‖=Real.sqrt (1+ℓ^2*(s-(2*m)^2)) := by
      rw [Complex.norm_def,Complex.normSq_apply]
      congr 1
      simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.mul_re,
        Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,one_mul,mul_zero,sub_zero,zero_add,zero_sub,neg_mul_neg]
      nlinarith [hx]
    change ‖((C:ℂ)/(1-Complex.I*(x:ℂ)))^N‖ = _
    rw [norm_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hC.le,hd]
    rfl

/-- Oriented, complex-valued product of the on-shell normal amplitudes
in one matter cycle with its own routing and oriented transfer labels. -/
def seaComplexLoopReadout {E ι : Type*} [NormedAddCommGroup E] [Fintype ι] (diamond : Plane E)
    (ε : ι → Evolution) (σ : Equiv.Perm ι) (band : ι → Bool)
    (a : ι → Spatial) (m ℓ : ℝ) (N : ℕ) (k : Spatial) : ℂ :=
  ∏ i, seaRimMark diamond (ε i) (band (σ.symm i) != band i) m ℓ N
    (k+a (σ.symm i)) (k+a i)

theorem sea_complex_loop_readout_norm {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    (diamond : Plane E) (ε : ι → Evolution) (σ : Equiv.Perm ι) (band : ι → Bool)
    (a : ι → Spatial) {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (N : ℕ) (k : Spatial) :
    ‖seaComplexLoopReadout diamond ε σ band a m ℓ N k‖ = seaClassicalLoopReadout σ band a m ℓ N k := by
  unfold seaComplexLoopReadout seaClassicalLoopReadout
  rw [norm_prod]
  exact Finset.prod_congr rfl (fun i _ => sea_rim_mark_norm diamond (ε i) _ hm hℓ _ _ _)

/-- Complete finite products of ordered classical-source matter loops. This
uses the literal shifted readouts, the independent circulating momenta and
the actual traces of all retained spin and transfer matrices. A finite
time measure represents the ordered slab, and `χ` is the external packet.
The measurability of the supplied spin and routing realization is stated
as measurability of the displayed integrand. -/
theorem sea_ordered_packet_graph_integrable {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    {d h : ℕ} (n : Fin h → ℕ) (ε : ∀ j, Fin (n j) → Evolution)
    [∀ j,Nonempty (Fin (n j))] {T : Type*} [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ]
    (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ)) (σ : ∀ j, Equiv.Perm (Fin (n j)))
    (t : T → ∀ j, Fin (n j) → ℝ) (band : ∀ j, Fin (n j) → Bool)
    (ordered : ∀ u j i, if band j i then t u j i < t u j (σ j i) else t u j (σ j i) < t u j i)
    (a : ∀ j, Fin (n j) → Spatial)
    (L : ∀ j, Fin (n j) → EuclideanSpace ℝ (Fin d) →L[ℝ] Spatial)
    (spin : T × (EuclideanSpace ℝ (Fin d) × (Fin h → Spatial)) → ∀ j, Fin (n j) → DiracMatrix)
    (hspin : ∀ z j i, ‖spin z j i‖ ≤ 1)
    {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) {N : ℕ} (hN : 2 ≤ N) :
    let weight (q : EuclideanSpace ℝ (Fin d)) (k : Fin h → Spatial) (j : Fin h) :=
      seaComplexLoopReadout diamond (ε j) (σ j) (band j) (fun i => a j i+L j i q) m ℓ N (k j)
    let F z := χ z.2.1 * ∏ j, ((normalOrderedWord (spin z j)).trace * weight z.2.1 z.2.2 j)
    AEStronglyMeasurable F (μ.prod (volume.prod volume)) → Integrable F (μ.prod (volume.prod volume)) := by
  dsimp only
  intro hF
  let B j := (5+ℓ⁻¹)*(1+m+2*∑ i, (‖a j i‖+‖L j i‖))
  let C := ∏ j, ((1+ℓ*(2*m))^(Fintype.card (Fin (n j)))*(B j)^2)^N
  apply sea_tested_cycle_integrability μ χ hN (n := 2*N*h) (C*4^h) _ hF
  intro z
  let W j := seaClassicalLoopReadout (σ j) (band j) (fun i => a j i+L j i z.2.1) m ℓ N (z.2.2 j)
  have hw j : 0 ≤ W j := by
    unfold W seaClassicalLoopReadout
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (div_nonneg (by positivity) (zero_le_one.trans (sea_mark_den_ge_one _ _ hℓ _ _))) _
  have hs := sea_joint_classical_loop_bound σ (t z.1) band (ordered z.1) a L hm hℓ N z.2.1 z.2.2
  change (∏ j, W j) ≤ C*_ * _ at hs
  rw [norm_mul,norm_prod]
  let U j := seaComplexLoopReadout diamond (ε j) (σ j) (band j) (fun i => a j i+L j i z.2.1) m ℓ N (z.2.2 j)
  have hprod : (∏ j, ‖(normalOrderedWord (spin z j)).trace * U j‖) ≤ (4^h:ℝ) * ∏ j, W j := by
    calc _ ≤ ∏ j, 4*W j := by
           apply Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => ?_)
           rw [norm_mul,show ‖U j‖ = W j from sea_complex_loop_readout_norm diamond (ε j) _ _ _ hm hℓ _ _]
           exact mul_le_mul_of_nonneg_right (sea_spin_word_trace_bound _ (hspin z j)) (hw j)
         _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc _ ≤ ‖χ z.2.1‖*(4^h* ∏ j, W j) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
       _ ≤ ‖χ z.2.1‖*(4^h*(C*_ * _)) := by gcongr
       _ = _ := by ring

/-- For fixed spatial momentum the additional spatial tensor numerator is
a fixed multiple of the scalar dispersion integral. This includes each
unsubtracted spatial Fourier component on the locked plane. -/
theorem sea_fixed_spatial_tensor_integrable {e m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ)
    {N : ℕ} (hN : 2 ≤ N) (q : Spatial) (ω a b : ℝ) :
    IntegrableOn (fun s => (a*s+b)*seaInvariantPairDensity e m ℓ N s /
      (s+(‖q‖^2+ω^2))) (Ici ((2*m)^2)) := by
  have hx : 0 ≤ ‖q‖^2+ω^2 := by positivity
  have h₁ := (sea_invariant_current_transform (e := e) hm hℓ hx hN).1
  have h₂ := sea_invariant_scalar_dispersion (e := e) hm hℓ hx (show 1 ≤ N by omega)
  apply ((h₁.const_mul a).add (h₂.const_mul b)).congr
  exact Eventually.of_forall fun s => by dsimp; ring

end UV
