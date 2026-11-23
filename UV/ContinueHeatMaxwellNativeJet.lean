import UV.ContinueHeatMaxwellTaylorInputs
import UV.ContinueHeatMaxwellSignPrimitive

/-! Identification of the actual quadratic coefficient of the massive
Dirac determinant Hessian with its angular and radial sign polynomial. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane
open scoped RealInnerProductSpace

private abbrev K := EuclideanPlaneMomentum

private def nativeScalarForm (u q : ℝ) (p l h v w : K) : ℝ :=
  let b := 1-q*u
  let vv := ⟪v,v⟫
  let den := (q*⟪p,p⟫+b)*(q*⟪l,l⟫+b)
  (q^2*(2*(⟪p,v⟫*⟪l,v⟫)-⟪p,l⟫*vv)-(q*b)*vv)*den⁻¹-q*⟪h,w⟫

private theorem heat_normalized_scalar_form {m : ℝ} (hm : 0<m) (k p l h v w : K)
    (hh : ‖h‖^2=Real.exp (-‖k‖^2)^2*‖k‖^2) :
    let c := Real.exp (-‖k‖^2)
    let q := heatNormalizedGaussian (m^2) (‖k‖^2)
    nativeScalarForm (‖k‖^2) q (c⁻¹ • p) (c⁻¹ • l) (c⁻¹ • h) (c⁻¹ • v) (c⁻¹ • w) =
    (2*⟪p,v⟫*⟪l,v⟫-(m^2+⟪p,l⟫)*‖v‖^2)/((‖p‖^2+m^2)*(‖l‖^2+m^2))-⟪h,w⟫/(‖h‖^2+m^2) := by
  let u := ‖k‖^2
  let c := Real.exp (-u)
  let N := m^2+c^2*u
  let q := c^2/N
  have hc : c≠0 := Real.exp_ne_zero _
  have hN : N≠0 := by dsimp [N,u];positivity
  have hq : heatNormalizedGaussian (m^2) u=q := by
    simp only [heatNormalizedGaussian,heatRadius,q,N,c]
    rw [show Real.exp (-2*u)=Real.exp (-u)^2 from by rw [←Real.exp_nat_mul];congr 1;push_cast;ring,mul_comm u]
  have hb : 1-q*u=m^2/N := by dsimp only [q];field_simp;dsimp only [N];ring
  have hd (z : K) : q*⟪c⁻¹ • z,c⁻¹ • z⟫+(1-q*u)=(‖z‖^2+m^2)/N := by
    rw [hb,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq]
    dsimp only [q];field_simp
  have hp : ‖p‖^2+m^2≠0 := by positivity
  have hl : ‖l‖^2+m^2≠0 := by positivity
  change nativeScalarForm u (heatNormalizedGaussian (m^2) u) (c⁻¹ • p) (c⁻¹ • l) (c⁻¹ • h) (c⁻¹ • v) (c⁻¹ • w)=_
  rw [hq]
  unfold nativeScalarForm
  dsimp only
  rw [hd,hd,hb]
  change ‖h‖^2=c^2*u at hh
  rw [hh,show c^2*u+m^2=N from add_comm _ _]
  simp only [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (show 0<c from Real.exp_pos _),q]
  field_simp
  ring

private def heatMarkNormalized (k : K) (a : ℝ) : ℝ→K :=
  heatNormalizedMotion k (fun t => heatSymbol (k+(a*t) • softLongitudinal.val))

private theorem heat_actual_native_form (m : ℝ) (hm : 0<m) (k : K) (t : ℝ) :
    nativeScalarForm (‖k‖^2) (heatNormalizedGaussian (m^2) (‖k‖^2))
      (heatMarkNormalized k (-1/2) t) (heatMarkNormalized k (1/2) t) k
      (heatNormalizedMotion k (heatFirstChord k) t) (heatNormalizedMotion k (heatContactChord k) t) =
      heatNativeResponse m k t := by
  have H := heat_normalized_scalar_form hm k (heatSymbol (k+(-t/2) • softLongitudinal.val))
    (heatSymbol (k+(t/2) • softLongitudinal.val)) (heatSymbol k)
    (heatFirstChord k t) (heatContactChord k t) (by simp [heatSymbol,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow])
  have he : (Real.exp (-‖k‖^2))⁻¹ • heatSymbol k=k := by
    rw [heatSymbol,smul_smul,inv_mul_cancel₀ (Real.exp_ne_zero _),one_smul]
  dsimp only at H
  rw [he] at H
  simpa only [heatMarkNormalized,heatNormalizedMotion,heatNativeResponse,show (-1/2:ℝ)*t= -t/2 by ring,
    show (1/2:ℝ)*t=t/2 by ring] using H

theorem heat_native_scalar_germ {m : ℝ} (hm : 0<m) (k : K) :
    ScalarGerm (heatNativeResponse m k) (heatBubbleContactJet (‖k‖^2)
       ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫ (heatNormalizedGaussian (m^2) (‖k‖^2))) := by
  let u := ‖k‖^2
  let j := ⟪k,softLongitudinal.val⟫
  let b := ⟪k,softTransverse.val⟫
  let q := heatNormalizedGaussian (m^2) u
  let dot := heatGram u j b
  let P : VectorJet := ⟨heatK,vectorScale (-1/2) (heatH₁ j),vectorScale (1/8) (heatH₁₁ j)⟩
  let Q : VectorJet := ⟨heatK,vectorScale (1/2) (heatH₁ j),vectorScale (1/8) (heatH₁₁ j)⟩
  let V : VectorJet := ⟨heatH₂ b,vectorZero,vectorScale (1/24) (heatH₁₁₂ j b)⟩
  let W : VectorJet := ⟨heatContactBase b,vectorZero,vectorScale (1/12) (heatH₁₁₂₂ j b)⟩
  let p := heatMarkNormalized k (-1/2)
  let l := heatMarkNormalized k (1/2)
  let v := heatNormalizedMotion k (heatFirstChord k)
  let w := heatNormalizedMotion k (heatContactChord k)
  have hp : VectorGerm k p P := by
    convert heat_shifted_germ k (-1/2) using 1
    norm_num [P,j]
  have hl : VectorGerm k l Q := by
    convert heat_shifted_germ k (1/2) using 1
    norm_num [Q,j]
  have hv : VectorGerm k v V := heat_first_germ k
  have hw : VectorGerm k w W := heat_contact_germ k
  have hk : VectorGerm k (fun _ => k) ⟨heatK,vectorZero,vectorZero⟩ := by
    unfold VectorGerm
    simpa only [heat_carrier_k,heat_carrier_zero] using HeatJetGerm.const k
  let den (x : ℝ→K) := fun t => q*⟪x t,x t⟫+(1-q*u)
  have hd {x : ℝ→K} {X : VectorJet} (hx : VectorGerm k x X) :
      ScalarGerm (den x) (normalizedDenominator q u dot X) :=
    ((heat_dot_germ hx hx).scale q).add (ScalarGerm.const _)
  have hd0 : ((normalizedDenominator q u dot P).mul (normalizedDenominator q u dot Q)).constant=1 := by
    simp only [normalizedDenominator,HeatScalarJet.add,HeatScalarJet.scale,HeatScalarJet.mul,dotJet,P,Q,dot,heatGram,heatK]
    ring
  have hden (x : K) : 0<q*⟪x,x⟫+(1-q*u) := by
    have he : Real.exp (-2*u)>0 := Real.exp_pos _
    have hu : 0≤u := sq_nonneg _
    have hy : 0<m^2+u*Real.exp (-2*u) := by positivity
    have hq : 0≤q := by dsimp [q,heatNormalizedGaussian,heatRadius];positivity
    have hx : 1-q*u=m^2/(m^2+u*Real.exp (-2*u)) := by
      dsimp [q,heatNormalizedGaussian,heatRadius];field_simp;ring
    rw [hx,real_inner_self_eq_norm_sq];positivity
  have hdi := ((hd hp).mul (hd hl)).unitInverse hd0 (fun t => mul_ne_zero (hden (p t)).ne' (hden (l t)).ne')
  have hVV := heat_dot_germ hv hv
  have hB := (((((heat_dot_germ hp hv).mul (heat_dot_germ hl hv)).scale 2).sub
    ((heat_dot_germ hp hl).mul hVV)).scale (q^2)).sub (hVV.scale (q*(1-q*u)))
  have hg : ScalarGerm (fun t => nativeScalarForm u q (p t) (l t) k (v t) (w t)) (heatBubbleContactJet u j b q) :=
    (hB.mul hdi).sub ((heat_dot_germ hk hw).scale q)
  have he : (fun t => nativeScalarForm u q (p t) (l t) k (v t) (w t))=heatNativeResponse m k :=
    funext (heat_actual_native_form m hm k)
  rw [he] at hg
  exact hg

theorem heat_native_pointwise_first {m : ℝ} (hm : 0<m) (k : K) : deriv (heatNativeResponse m k) 0=0 := by
  obtain ⟨_,d,hd,hv,_⟩ := heat_native_scalar_germ hm k
  rw [(hd 0).deriv,hv]
  simp only [heatBubbleContactJet,normalizedDenominator,dotJet,HeatScalarJet.add,HeatScalarJet.scale,
    HeatScalarJet.sub,HeatScalarJet.mul,HeatScalarJet.unitInverse,vectorScale,vectorZero,heatGram,heatK,
    heatH₁,heatH₁₁,heatH₂,heatH₁₁₂,heatH₁₁₂₂]
  ring

/-- The pointwise second derivative is twice the coefficient entering
the spherical average, with the longitudinal unit ray fixed. -/
theorem heat_native_pointwise_second {m : ℝ} (hm : 0<m) (k : K) :
    deriv (deriv (heatNativeResponse m k)) 0=2*heatTwoMarkQuadratic (‖k‖^2)
       ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫ (heatNormalizedGaussian (m^2) (‖k‖^2)) := by
  simpa only [heatBubbleContactJet_quadratic,smul_eq_mul] using HeatJetGerm.second (heat_native_scalar_germ hm k)

end UV.HeatMaxwell
