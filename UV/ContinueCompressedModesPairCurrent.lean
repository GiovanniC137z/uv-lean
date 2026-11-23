import UV.ContinueCompressedModesPairHamiltonian

/-! The curvature-pair current and its complete two-insertion Euclidean
spectral coefficient. The electric field strengths carry the Fourier
transfer; the two time orderings retain their own massive denominators. -/

noncomputable section
open MeasureTheory Set UV.SectorPlane

namespace UV.PairCurvature

def wedge (P j : Fin 4 → ℝ) (s : ℝ) (a b : Fin 4) := (P a*j b-P b*j a)/s

/-- The pair tensor is the covariant exterior product. This identity
in particular applies to every locked Lorentz change of frame. -/
theorem wedge_transform (Λ : Matrix (Fin 4) (Fin 4) ℝ) (P j : Fin 4 → ℝ)
    (s : ℝ) (a b : Fin 4) :
    wedge (Λ.mulVec P) (Λ.mulVec j) s a b =
    (Λ * Matrix.of (wedge P j s) * Λ.transpose) a b := by
  simp only [wedge,Matrix.mulVec,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,dotProduct,Fin.sum_univ_four]
  ring

theorem current_conserved (p s : ℝ) (a : Fin 3) :
    ∑ i : Fin 4, metricSign i*pairMomentum p s i*current p s a i=0 := by
  fin_cases a <;> simp (config := {decide:=true}) [Fin.sum_univ_four,metricSign,pairMomentum,current]
  ring

theorem pair_current_derivative (p : ℝ) {s : ℝ} (hs : 0<s) (a : Fin 3) (j : Fin 4) :
    ∑ i : Fin 4, metricSign i*pairMomentum p s i*pairTensor p s a i j=current p s a j := by
  have hd : (pairEnergy p s)^2=p^2+s := Real.sq_sqrt (by positivity)
  have h := current_conserved p s a
  have hn : (∑i:Fin 4, metricSign i*pairMomentum p s i*pairMomentum p s i)=s := by
    simp (config:={decide:=true}) [Fin.sum_univ_four,metricSign,pairMomentum]
    nlinarith
  have hterm (i:Fin 4) : metricSign i*pairMomentum p s i*pairTensor p s a i j =
      (metricSign i*pairMomentum p s i*pairMomentum p s i*current p s a j-
       metricSign i*pairMomentum p s i*current p s a i*pairMomentum p s j)/s := by
    unfold pairTensor
    ring
  simp_rw [hterm]
  rw [←Finset.sum_div,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.sum_mul,hn,h]
  field_simp
  ring

private theorem abs_diff (x y : ℝ) : |x-y| ≤ |x|+|y| := by simpa only [Real.norm_eq_abs] using norm_sub_le x y

private theorem pairTensor_bound {p s d R : ℝ} (hp : 0≤p) (hpR : p≤R)
    (hd : 0<d) (hs : d≤s) (a : Fin 3) (i j : Fin 4) :
    |pairTensor p s a i j| ≤ 2*(1+R^2/d) := by
  let D := pairEnergy p s
  have hs' : 0<s := hd.trans_le hs
  have hD : 0<D := Real.sqrt_pos.mpr (by positivity)
  have hE : D^2=p^2+s := Real.sq_sqrt (by positivity)
  have hRD : p≤D := by nlinarith
  have hsD : Real.sqrt s ≤D := by nlinarith [Real.sq_sqrt hs'.le,Real.sqrt_nonneg s]
  have hm (l : Fin 4) : |pairMomentum p s l|≤D := by
    unfold pairMomentum; split_ifs <;> simp [abs_of_nonneg hD.le,abs_of_nonneg hp,D] <;> linarith
  have hc (l : Fin 4) : |current p s a l|≤D := by
    unfold current; split_ifs <;> simp [abs_of_nonneg hD.le,abs_of_nonneg hp,abs_of_nonneg (Real.sqrt_nonneg _),D] <;> linarith
  have hr := (sq_le_sq₀ hp (hp.trans hpR)).mpr hpR
  rw [pairTensor,abs_div,abs_of_pos hs']
  apply (div_le_div_of_nonneg_right (abs_diff _ _) hs'.le).trans
  rw [abs_mul,abs_mul]
  have hi := mul_le_mul (hm i) (hc j) (abs_nonneg _) hD.le
  have hj := mul_le_mul (hm j) (hc i) (abs_nonneg _) hD.le
  calc _ ≤ 2*D^2/s := (div_le_div_iff_of_pos_right hs').mpr (by nlinarith)
    _ = 2*(1+p^2/s) := by rw [hE]; field_simp; ring
    _ ≤ _ := by gcongr

/-- Plane polarization is a unit vector. The coefficient φ allows the
unit Wick-rotation factors on electric tensor components. -/
def curvatureMark (φ : Fin 4 → Fin 4 → ℂ) (Q : DiracMomentum) (u : UnitVector DiracMomentum)
    (p s : ℝ) (a : Fin 3) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, φ i j * (((Q i * u.val j-Q j*u.val i)/2*pairTensor p s a i j : ℝ):ℂ)

private theorem curvatureMark_bound (φ : Fin 4 → Fin 4 → ℂ) (hφ : ∀i j, ‖φ i j‖≤1)
    (Q : DiracMomentum) (u : UnitVector DiracMomentum) {p s R d : ℝ}
    (hp : 0≤p) (hR : p≤R) (hd : 0<d) (hs : d≤s) (a : Fin 3) :
    ‖curvatureMark φ Q u p s a‖≤16*(2*(1+R^2/d))*‖Q‖ := by
  have hq (i:Fin 4) : |Q i|≤‖Q‖ := PiLp.norm_apply_le Q i
  have hu (i:Fin 4) : |u.val i|≤1 := by simpa only [←Real.norm_eq_abs,u.property] using PiLp.norm_apply_le u.val i
  have hF (i j : Fin 4) : |(Q i*u.val j-Q j*u.val i)/2|≤‖Q‖ := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num)).mpr
    apply (abs_diff _ _).trans
    simp_rw [abs_mul]
    nlinarith [mul_le_mul (hq i) (hu j) (abs_nonneg _) (norm_nonneg _),
               mul_le_mul (hq j) (hu i) (abs_nonneg _) (norm_nonneg _)]
  have hb (i j:Fin 4) :
      ‖φ i j * (((Q i*u.val j-Q j*u.val i)/2*pairTensor p s a i j : ℝ):ℂ)‖ ≤ ‖Q‖*(2*(1+R^2/d)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    calc _ ≤ 1*(‖Q‖*(2*(1+R^2/d))) := by gcongr; exacts [hφ i j,hF i j,pairTensor_bound hp hR hd hs a i j]
      _ = _ := one_mul _
  unfold curvatureMark
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _ : Fin 4, ∑ _ : Fin 4, ‖Q‖*(2*(1+R^2/d)) :=
    Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb i j)))
    _ = _ := by simp; ring

private def orderedPair (D ω : ℝ) (x y : ℂ) := x*star y / ((D:ℂ)+Complex.I*(ω:ℂ))

private theorem orderedPair_bound {D : ℝ} (hD : 0<D) (ω : ℝ) (x y : ℂ) :
    ‖orderedPair D ω x y‖ ≤ ‖x‖*‖y‖/D := by
  have hr := Complex.re_le_norm ((D:ℂ)+Complex.I*(ω:ℂ))
  simp at hr
  rw [orderedPair,norm_div,norm_mul,norm_star]
  exact div_le_div_of_nonneg_left (by positivity) hD hr

/-- Both time orderings of the pair transfer, with its invariant measure
factor 1/(2D). The common charge squared multiplies the full answer. -/
def vacuumTransfer (φ : Fin 4 → Fin 4 → ℂ) (Q : DiracMomentum)
    (u v : UnitVector DiracMomentum) (p s : ℝ) : ℂ :=
  ∑ a : Fin 3, (orderedPair (pairEnergy p s) (Q 0) (curvatureMark φ Q u p s a) (curvatureMark φ Q v p s a)+
    orderedPair (pairEnergy p s) (-(Q 0)) (curvatureMark φ Q v p s a) (curvatureMark φ Q u p s a)) /
    ((2*pairEnergy p s:ℝ):ℂ)

private theorem vacuumTransfer_bound (φ : Fin 4 → Fin 4 → ℂ) (hφ : ∀i j, ‖φ i j‖≤1)
    (Q : DiracMomentum) (u v : UnitVector DiracMomentum) {p s R d : ℝ}
    (hp : 0≤p) (hR : p≤R) (hd : 0<d) (hs : d≤s) :
    ‖vacuumTransfer φ Q u v p s‖ ≤ (3*(16*(2*(1+R^2/d)))^2/d)*‖Q‖^2 := by
  let D := pairEnergy p s
  let C := 16*(2*(1+R^2/d))
  have hD : 0<D := Real.sqrt_pos.mpr (by linarith [sq_nonneg p])
  have hsq : D^2=p^2+s := Real.sq_sqrt (by linarith [sq_nonneg p])
  have hc : 0≤C*‖Q‖ := by dsimp [C]; positivity
  have bound (a : Fin 3) (w z : UnitVector DiracMomentum) (ω : ℝ) :
      ‖orderedPair D ω (curvatureMark φ Q w p s a) (curvatureMark φ Q z p s a)‖≤(C*‖Q‖)^2/D := by
    refine (orderedPair_bound hD _ _ _).trans ((div_le_div_iff_of_pos_right hD).mpr ?_)
    rw [pow_two]
    exact mul_le_mul (curvatureMark_bound φ hφ Q w hp hR hd hs a)
      (curvatureMark_bound φ hφ Q z hp hR hd hs a) (norm_nonneg _) hc
  unfold vacuumTransfer
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _ : Fin 3, (C*‖Q‖)^2/d := by
          apply Finset.sum_le_sum
          intro a _
          rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<2*pairEnergy p s by linarith)]
          apply (div_le_div_of_nonneg_right (norm_add_le _ _) (show 0≤2*D by linarith)).trans
          calc _ ≤ ((C*‖Q‖)^2/D+(C*‖Q‖)^2/D)/(2*D) := by gcongr; exacts [bound a u v _,bound a v u _]
            _ = (C*‖Q‖)^2/D^2 := by field_simp; ring
            _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hd (by linarith [sq_nonneg p])
    _ = _ := by simp [C]; ring

private theorem measurable_transfer (φ : Fin 4 → Fin 4 → ℂ) (Q : DiracMomentum)
    (u v : UnitVector DiracMomentum) (p : ℝ) : Measurable (vacuumTransfer φ Q u v p) := by
  have hP (i : Fin 4) : Measurable (fun s => pairMomentum p s i) := by
    unfold pairMomentum pairEnergy; split_ifs <;> fun_prop
  have hj (a : Fin 3) (i : Fin 4) : Measurable (fun s => current p s a i) := by
    unfold current pairEnergy; split_ifs <;> fun_prop
  have hB (a : Fin 3) (i j : Fin 4) : Measurable (fun s => pairTensor p s a i j) :=
    (((hP i).mul (hj a j)).sub ((hP j).mul (hj a i))).div measurable_id
  have hV (w : UnitVector DiracMomentum) (a : Fin 3) :
      Measurable (fun s => curvatureMark φ Q w p s a) := by
    unfold curvatureMark
    fun_prop (disch := exact hB ..)
  unfold vacuumTransfer orderedPair pairEnergy
  fun_prop (disch := exact hV ..)

/-- The actual spectral density, opposite Euclidean time poles and both
external field strengths give absolute convergence and a uniform quadratic
soft bound on every bounded set of spatial transfers. -/
theorem complete_pair_two_source (φ : Fin 4 → Fin 4 → ℂ) (hφ : ∀i j, ‖φ i j‖≤1)
    {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) (R : ℝ) :
    ∃ C:ℝ, 0≤C ∧ ∀ (Q : DiracMomentum) (u v : UnitVector DiracMomentum) (p : ℝ), 0≤p → p≤R →
      let f := fun s => (massDensity m ℓ s:ℂ)*vacuumTransfer φ Q u v p s
      IntegrableOn f (Ioi (4*m^2)) ∧ ‖∫ s in Ioi (4*m^2), f s‖≤C*‖Q‖^2 := by
  let d := 4*m^2
  let B := 3*(16*(2*(1+R^2/d)))^2/d
  have hd : 0<d := by dsimp [d]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨(∫ s in Ioi d, massDensity m ℓ s)*B,
    mul_nonneg (integral_nonneg (fun s => massDensity_nonneg ..)) hB,?_⟩
  intro Q u v p hp hR
  let f := fun s => (massDensity m ℓ s:ℂ)*vacuumTransfer φ Q u v p s
  let μ := (volume : Measure ℝ).restrict (Ioi d)
  have hm' : Measurable f := Complex.measurable_ofReal.comp (measurable_massDensity m ℓ) |>.mul (measurable_transfer φ Q u v p)
  have hmaj : Integrable (fun s => massDensity m ℓ s*(B*‖Q‖^2)) μ := ((massDensity_integrable m hℓ).mul_const _).integrableOn
  have hbound : ∀ᵐ s ∂μ, ‖f s‖≤massDensity m ℓ s*(B*‖Q‖^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (massDensity_nonneg ..)]
    exact mul_le_mul_of_nonneg_left (vacuumTransfer_bound φ hφ Q u v hp hR hd hs.le) (massDensity_nonneg ..)
  have hf := hmaj.mono' hm'.aestronglyMeasurable hbound
  refine ⟨hf,(norm_integral_le_integral_norm f).trans ((integral_mono_ae hf.norm hmaj hbound).trans_eq ?_)⟩
  rw [integral_mul_const]
  ring

end UV.PairCurvature
