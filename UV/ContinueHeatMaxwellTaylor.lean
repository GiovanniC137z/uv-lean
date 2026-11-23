import UV.ContinueHeatMaxwellSignJet
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual differentiable germs realizing the normalized Taylor jets
used in the Wilson bubble and contact computation. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.SectorPlane
open scoped RealInnerProductSpace

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def HeatJetGerm (f : ℝ→E) (x v w : E) : Prop :=
  f 0=x ∧ ∃ d : ℝ→E, (∀ t, HasDerivAt f (d t) t) ∧ d 0=v ∧ HasDerivAt d ((2:ℝ) • w) 0

theorem HeatJetGerm.second {f : ℝ→E} {x v w : E} (h : HeatJetGerm f x v w) :
    deriv (deriv f) 0 = (2:ℝ) • w := by
  obtain ⟨_,d,hd,_,h2⟩ := h
  rw [show deriv f=d from funext fun t => (hd t).deriv,h2.deriv]

theorem HeatJetGerm.of_derivatives {f : ℝ→E} {x v w : E}
    (hd : Differentiable ℝ f) (hdd : DifferentiableAt ℝ (deriv f) 0)
    (hx : f 0=x) (hv : deriv f 0=v) (hw : deriv (deriv f) 0=(2:ℝ) • w) : HeatJetGerm f x v w :=
  ⟨hx,deriv f,fun t => (hd t).hasDerivAt,hv,hw ▸ hdd.hasDerivAt⟩

theorem HeatJetGerm.const (x : E) : HeatJetGerm (fun _ => x) x 0 0 := by
  exact ⟨rfl,fun _ => 0,fun t => hasDerivAt_const t _,rfl,by simpa using hasDerivAt_const (0:ℝ) (0:E)⟩

theorem HeatJetGerm.add {f g : ℝ→E} {x v w X V W : E}
    (a : HeatJetGerm f x v w) (b : HeatJetGerm g X V W) :
    HeatJetGerm (fun t => f t+g t) (x+X) (v+V) (w+W) := by
  obtain ⟨hx,d,hd,hv,hw⟩ := a
  obtain ⟨hX,e,he,hV,hW⟩ := b
  exact ⟨congrArg₂ (·+·) hx hX,fun t => d t+e t,fun t => (hd t).add (he t),
    congrArg₂ (·+·) hv hV,by simpa only [smul_add] using hw.add hW⟩

theorem HeatJetGerm.scale {f : ℝ→E} {x v w : E} (a : HeatJetGerm f x v w) (c : ℝ) :
    HeatJetGerm (fun t => c • f t) (c • x) (c • v) (c • w) := by
  obtain ⟨hx,d,hd,hv,hw⟩ := a
  exact ⟨congrArg (c • ·) hx,fun t => c • d t,fun t => (hd t).const_smul c,congrArg (c • ·) hv,
    by simpa only [smul_comm c (2:ℝ)] using hw.const_smul c⟩

theorem HeatJetGerm.reparam {f : ℝ→E} {x v w : E} (a : HeatJetGerm f x v w) (c : ℝ) :
    HeatJetGerm (fun t => f (c*t)) x (c • v) (c^2 • w) := by
  obtain ⟨hx,d,hd,hv,hw⟩ := a
  have ht (t:ℝ) : HasDerivAt (fun s => c*s) c t := by simpa using (hasDerivAt_id t).const_mul c
  refine ⟨by simpa using hx,fun t => c • d (c*t),fun t => (hd _).scomp t (ht t),by simp [hv],?_⟩
  have hw' : HasDerivAt d ((2:ℝ) • w) (c*0) := by simpa using hw
  convert (hw'.scomp 0 (ht 0)).const_smul c using 1
  module

theorem HeatJetGerm.bilinear (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ→E} {g : ℝ→F} {x v w : E} {X V W : F}
    (a : HeatJetGerm f x v w) (b : HeatJetGerm g X V W) :
    HeatJetGerm (fun t => L (f t) (g t)) (L x X) (L x V+L v X) (L x W+L v V+L w X) := by
  obtain ⟨hx,d,hd,hv,hw⟩ := a
  obtain ⟨hX,e,he,hV,hW⟩ := b
  refine ⟨by simp only [hx,hX],fun t => L (d t) (g t)+L (f t) (e t),fun t =>
    (L.hasFDerivAt.comp_hasDerivAt t (hd t)).clm_apply (he t),by simp only [hv,hX,hx,hV,add_comm],?_⟩
  have H := ((L.hasFDerivAt.comp_hasDerivAt 0 hw).clm_apply (he 0)).add
    ((L.hasFDerivAt.comp_hasDerivAt 0 (hd 0)).clm_apply hW)
  convert H using 1
  simp only [Function.comp_apply,hv,hV,hx,hX,map_smul,ContinuousLinearMap.smul_apply]
  module

abbrev ScalarGerm (f : ℝ→ℝ) (a : HeatScalarJet) := HeatJetGerm f a.constant a.linear a.quadratic

theorem ScalarGerm.const (a : ℝ) : ScalarGerm (fun _ => a) ⟨a,0,0⟩ := HeatJetGerm.const a
theorem ScalarGerm.add {f g : ℝ→ℝ} {a b : HeatScalarJet} (ha : ScalarGerm f a) (hb : ScalarGerm g b) :
    ScalarGerm (fun t => f t+g t) (a.add b) := HeatJetGerm.add ha hb
theorem ScalarGerm.scale {f : ℝ→ℝ} {a : HeatScalarJet} (ha : ScalarGerm f a) (c : ℝ) :
    ScalarGerm (fun t => c*f t) (a.scale c) := HeatJetGerm.scale ha c
theorem ScalarGerm.sub {f g : ℝ→ℝ} {a b : HeatScalarJet} (ha : ScalarGerm f a) (hb : ScalarGerm g b) :
    ScalarGerm (fun t => f t-g t) (a.sub b) := by
  simpa only [neg_one_mul,←sub_eq_add_neg] using ha.add (hb.scale (-1))
theorem ScalarGerm.mul {f g : ℝ→ℝ} {a b : HeatScalarJet} (ha : ScalarGerm f a) (hb : ScalarGerm g b) :
    ScalarGerm (fun t => f t*g t) (a.mul b) := HeatJetGerm.bilinear (ContinuousLinearMap.mul ℝ ℝ) ha hb

theorem ScalarGerm.unitInverse {f : ℝ→ℝ} {a : HeatScalarJet} (ha : ScalarGerm f a) (h0 : a.constant=1)
    (hne : ∀ t, f t≠0) : ScalarGerm (fun t => (f t)⁻¹) a.unitInverse := by
  obtain ⟨hx,d,hd,hv,hw⟩ := ha
  rw [h0] at hx
  refine ⟨by simp [hx,HeatScalarJet.unitInverse],fun t => -(d t)/(f t)^2,fun t => (hd t).inv (hne t),
    by simp [hx,hv,HeatScalarJet.unitInverse],?_⟩
  have H := hw.neg.div ((hd 0).pow 2) (pow_ne_zero 2 (hne 0))
  convert H using 1
  simp only [HeatScalarJet.unitInverse,Pi.pow_apply,Pi.neg_apply,hx,hv,one_pow,smul_eq_mul,Nat.cast_ofNat]
  ring

abbrev VectorGerm (k : EuclideanPlaneMomentum) (f : ℝ→EuclideanPlaneMomentum) (a : VectorJet) :=
  HeatJetGerm f (heatCarrierVector k a.constant) (heatCarrierVector k a.linear) (heatCarrierVector k a.quadratic)

theorem heat_dot_germ {k : EuclideanPlaneMomentum} {f g : ℝ→EuclideanPlaneMomentum} {a b : VectorJet}
    (ha : VectorGerm k f a) (hb : VectorGerm k g b) :
    ScalarGerm (fun t => ⟪f t,g t⟫) (dotJet (heatGram (‖k‖^2) ⟪k,UV.RelativeSoft.softLongitudinal.val⟫
      ⟪k,UV.RelativeSoft.softTransverse.val⟫) a b) := by
  have h := HeatJetGerm.bilinear (innerSL ℝ (E:=EuclideanPlaneMomentum)) ha hb
  unfold ScalarGerm dotJet
  simp only [←heatGram_eq_inner]
  exact h

end UV.HeatMaxwell
