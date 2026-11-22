import UV.ContinueSpectrumLayers

/-! Exact layer--layer spectral Green blocks, including the Dirichlet noise
from the same positive continuum as the boundary pole. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def continueDirichletDensity (β M₂ r r' s : ℝ) : ℝ :=
  Real.sin (Real.sqrt (s-M₂)*r)*Real.sin (Real.sqrt (s-M₂)*r') /
    (Real.pi*β*Real.sqrt (s-M₂))

def continueLayerDensity (β b M₂ r r' s : ℝ) : ℝ :=
  bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) *
    normalMode β (Real.sqrt (s-M₂)) (b-s) r *
    normalMode β (Real.sqrt (s-M₂)) (b-s) r'

def continueBulkLayerGreen (β b M₂ x r r' : ℝ) : ℝ :=
  Real.exp (-(r+r')*Real.sqrt (x+M₂))/(x+b+β*Real.sqrt (x+M₂)) +
    (Real.exp (-|r-r'| *Real.sqrt (x+M₂)) -
      Real.exp (-(r+r')*Real.sqrt (x+M₂)))/(2*β*Real.sqrt (x+M₂))

theorem continue_sqrt_stieltjes_integrable {M₂ x : ℝ} (hM : 0<M₂) (hx : 0<x) :
    IntegrableOn (fun s : ℝ => (Real.sqrt (s-M₂)*(x+s))⁻¹) (Ioi M₂) := by
  let w := Real.sqrt (x+M₂)
  have hw : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by positivity)
  have hder : ∀ k ∈ Ioi (0:ℝ), HasDerivWithinAt (fun k : ℝ => k^2+M₂) (2*k) (Ioi 0) k := by
    intro k _
    exact (by simpa using (((hasDerivAt_id k).pow 2).add_const M₂).hasDerivWithinAt)
  have hinj : InjOn (fun k : ℝ => k^2+M₂) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro r hr k hk h
    exact add_lt_add_right ((sq_lt_sq₀ hr.le hk.le).mpr h) M₂
  have himage : (fun k : ℝ => k^2+M₂) '' Ioi 0 = Ioi M₂ := by
    ext s
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact (show M₂<k^2+M₂ by linarith [sq_pos_of_pos (mem_Ioi.mp hk)])
    · intro hs
      have h : 0<s-M₂ := sub_pos.mpr hs
      exact ⟨Real.sqrt (s-M₂),Real.sqrt_pos.mpr h, by
        change Real.sqrt (s-M₂)^2+M₂=s
        rw [Real.sq_sqrt h.le]
        ring⟩

  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj
    (fun s : ℝ => (Real.sqrt (s-M₂)*(x+s))⁻¹)
  rw [himage] at hi
  apply hi.mpr
  have hW : IntegrableOn (fun k : ℝ => 2*(k^2+w^2)⁻¹) (Ioi 0) :=
    (resumeCauchy_integrable w hw).const_mul 2
  apply hW.congr_fun _ measurableSet_Ioi
  intro k hk
  change 0<k at hk
  dsimp only [smul_eq_mul]
  rw [abs_of_pos (by positivity : 0<2*k),show k^2+M₂-M₂=k^2 by ring,Real.sqrt_sq hk.le]
  rw [show x+(k^2+M₂)=k^2+w^2 by linarith]
  have hden : k^2+w^2≠0 := by positivity
  field_simp

theorem continue_dirichlet_integrable {β M₂ x : ℝ} (hβ : 0<β) (hM : 0<M₂) (hx : 0<x)
    (r r' : ℝ) :
    IntegrableOn (fun s : ℝ => continueDirichletDensity β M₂ r r' s/(x+s)) (Ioi M₂) := by
  apply ((continue_sqrt_stieltjes_integrable hM hx).const_mul (1/(Real.pi*β))).mono'
  · exact (by unfold continueDirichletDensity; fun_prop :
      Measurable (fun s : ℝ => continueDirichletDensity β M₂ r r' s/(x+s))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsM : M₂<s := hs
    have hs₀ : 0<s := hM.trans hsM
    have hk : 0<Real.sqrt (s-M₂) := Real.sqrt_pos.mpr (sub_pos.mpr hsM)
    have hprod : |Real.sin (Real.sqrt (s-M₂)*r)*Real.sin (Real.sqrt (s-M₂)*r')|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [Real.norm_eq_abs,continueDirichletDensity,abs_div,abs_div,
      abs_of_pos (by positivity : 0<Real.pi*β*Real.sqrt (s-M₂)),abs_of_pos (add_pos hx hs₀)]
    calc
      _ ≤ (1/(Real.pi*β*Real.sqrt (s-M₂)))/(x+s) := by gcongr
      _ = _ := by
        have hd : x+s≠0 := by positivity
        field_simp

theorem continue_dirichlet_stieltjes {β M₂ x r r' : ℝ}
    (hβ : 0<β) (hM : 0<M₂) (hx : 0<x) (hr : 0≤r) (hr' : 0≤r') :
    (∫ s : ℝ in Ioi M₂,continueDirichletDensity β M₂ r r' s/(x+s)) =
      (Real.exp (-|r-r'| *Real.sqrt (x+M₂)) -
        Real.exp (-(r+r')*Real.sqrt (x+M₂)))/(2*β*Real.sqrt (x+M₂)) := by
  let w := Real.sqrt (x+M₂)
  have hw : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by positivity)
  rw [resume_bulk_spectral_substitution]
  have he : (∫ k : ℝ in Ioi 0,(2*k)*(continueDirichletDensity β M₂ r r' (k^2+M₂)/(x+(k^2+M₂)))) =
      (1/(Real.pi*β))*(∫ k : ℝ in Ioi 0,
        Real.cos ((r-r')*k)*(k^2+w^2)⁻¹-Real.cos ((r+r')*k)*(k^2+w^2)⁻¹) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro k hk
    change 0<k at hk
    dsimp only
    unfold continueDirichletDensity
    rw [show k^2+M₂-M₂=k^2 by ring,Real.sqrt_sq hk.le,
      show x+(k^2+M₂)=k^2+w^2 by linarith]
    have htrig : Real.cos ((r-r')*k)-Real.cos ((r+r')*k)=2*Real.sin (k*r)*Real.sin (k*r') := by
      rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
      simp only [mul_comm k]
      ring
    have hden : k^2+w^2≠0 := by positivity
    rw [← sub_mul, htrig]
    field_simp
  have h₁ : IntegrableOn (fun k : ℝ => Real.cos ((r-r')*k)*(k^2+w^2)⁻¹) (Ioi 0) := by
    simpa only [mul_comm] using (continueCauchyCos_integrable hw (r-r')).integrableOn (s:=Ioi 0)
  have h₂ : IntegrableOn (fun k : ℝ => Real.cos ((r+r')*k)*(k^2+w^2)⁻¹) (Ioi 0) := by
    simpa only [mul_comm] using (continueCauchyCos_integrable hw (r+r')).integrableOn (s:=Ioi 0)
  have hv₁ : (∫ k : ℝ in Ioi 0,Real.cos ((r-r')*k)*(k^2+w^2)⁻¹)=
      Real.pi/(2*w)*Real.exp (-w*|r-r'|) := by
    simpa only [mul_comm] using continueCauchyCos_integral hw (r-r')
  have hv₂ : (∫ k : ℝ in Ioi 0,Real.cos ((r+r')*k)*(k^2+w^2)⁻¹)=
      Real.pi/(2*w)*Real.exp (-w*|r+r'|) := by
    simpa only [mul_comm] using continueCauchyCos_integral hw (r+r')
  rw [he,integral_sub h₁ h₂,hv₁,hv₂,abs_of_nonneg (add_nonneg hr hr')]
  change (1/(Real.pi*β))*(Real.pi/(2*w)*Real.exp (-w*|r-r'|)-Real.pi/(2*w)*Real.exp (-w*(r+r'))) = _
  change _ = (Real.exp (-|r-r'| *w)-Real.exp (-(r+r')*w))/(2*β*w)
  simp_rw [mul_comm (-w)]
  field_simp

theorem continue_layer_density_identity {β k : ℝ} (hβ : 0<β) (hk : 0<k) (t r r' : ℝ) :
    bulkBoundaryDensity β k t*normalMode β k t r*normalMode β k t r' =
      bulkBoundaryDensity β k t*normalMode β k t (r+r')+
        Real.sin (k*r)*Real.sin (k*r')/(Real.pi*β*k) := by
  unfold bulkBoundaryDensity normalMode
  rw [show k*(r+r')=k*r+k*r' by ring,Real.cos_add,Real.sin_add]
  have hden : t^2+(β*k)^2≠0 := by positivity
  field_simp
  ring

theorem continue_layer_integrable {β b M₂ x r r' : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) (hr' : 0≤r') :
    IntegrableOn (fun s : ℝ => continueLayerDensity β b M₂ r r' s/(x+s)) (Ioi M₂) := by
  have hI : IntegrableOn (fun s : ℝ => continueBoundaryLayerDensity β b M₂ (r+r') s/(x+s)+
      continueDirichletDensity β M₂ r r' s/(x+s)) (Ioi M₂) :=
    (continue_boundary_layer_integrable hβ hb₀ hb hx (add_nonneg hr hr')).add
      (continue_dirichlet_integrable hβ (hb₀.trans hb) hx r r')
  apply hI.congr_fun _ measurableSet_Ioi
  intro s hs
  have hk : 0<Real.sqrt (s-M₂) := Real.sqrt_pos.mpr (sub_pos.mpr hs)
  dsimp only [Pi.add_apply]
  rw [continueLayerDensity,continue_layer_density_identity hβ hk,add_div]
  rfl

/-- Every literal layer block has the same displayed positive atom and
continuum as the boundary block; the second term is the retained Dirichlet
noise, derived from the same spectral measure. -/
theorem continue_bulk_layer_stieltjes {β b M₂ x r r' : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) (hr' : 0≤r') :
    IntegrableOn (fun s : ℝ => continueLayerDensity β b M₂ r r' s/(x+s)) (Ioi M₂) ∧
    bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂)*Real.exp (-r'*bulkKappa β b M₂)/(x+bulkPole β b M₂)+
      (∫ s : ℝ in Ioi M₂,continueLayerDensity β b M₂ r r' s/(x+s)) =
      continueBulkLayerGreen β b M₂ x r r' := by
  refine ⟨continue_layer_integrable hβ hb₀ hb hx hr hr',?_⟩
  have h₁ := continue_boundary_layer_integrable hβ hb₀ hb hx (add_nonneg hr hr')
  have h₂ := continue_dirichlet_integrable hβ (hb₀.trans hb) hx r r'
  have he : (∫ s : ℝ in Ioi M₂,continueLayerDensity β b M₂ r r' s/(x+s)) =
      (∫ s : ℝ in Ioi M₂,continueBoundaryLayerDensity β b M₂ (r+r') s/(x+s))+
      (∫ s : ℝ in Ioi M₂,continueDirichletDensity β M₂ r r' s/(x+s)) := by
    rw [← integral_add h₁ h₂]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hk : 0<Real.sqrt (s-M₂) := Real.sqrt_pos.mpr (sub_pos.mpr hs)
    dsimp only
    rw [continueLayerDensity,continue_layer_density_identity hβ hk,add_div]
    rfl
  have hAtom : Real.exp (-r*bulkKappa β b M₂)*Real.exp (-r'*bulkKappa β b M₂)=
      Real.exp (-(r+r')*bulkKappa β b M₂) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,show bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂)*Real.exp (-r'*bulkKappa β b M₂)=
    bulkResidue β b M₂*Real.exp (-(r+r')*bulkKappa β b M₂) by rw [mul_assoc,hAtom],← add_assoc,
    (continue_boundary_layer_stieltjes hβ hb₀ hb hx (add_nonneg hr hr')).2,
    continue_dirichlet_stieltjes hβ (hb₀.trans hb) hx hr hr']
  rfl

end UV.RevisionSpectrum
