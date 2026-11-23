import UV.ContinueCompressedModesPairTail

/-! Vacuum perturbation of the Maxwell-coupled pair. At a fixed (p,s) the
one-photon intermediate energy is D+p in every contributing polarization,
so only the normalized linear combination coupled to the vacuum is active. -/

noncomputable section
open Filter Matrix
open scoped Matrix Topology

namespace UV.PairCurvature

def contactCoefficient (complete : Bool) (p s : ℝ) :=
  (electricContact p s + if complete then magneticContact p s else 0)/(4*pairEnergy p s)

def emissionCoefficient (p s : ℝ) :=
  emittedSquare p s/(4*pairEnergy p s*p)

/-- Finite vacuum/bright-state Hamiltonian with actual contact and photon
normalization; orthogonal intermediate channels have the same free energy. -/
def vacuumHamiltonian (complete : Bool) (p s x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x^2*contactCoefficient complete p s, x*Real.sqrt (emissionCoefficient p s);
     x*Real.sqrt (emissionCoefficient p s), pairEnergy p s+p]

private def lowRoot (c b w x : ℝ) :=
  (b+x^2*c-Real.sqrt ((b-x^2*c)^2+4*x^2*w))/2

def vacuumEnergy (complete : Bool) (p s x : ℝ) :=
  lowRoot (contactCoefficient complete p s) (pairEnergy p s+p) (emissionCoefficient p s) x

private theorem emissionCoefficient_nonneg {p s : ℝ} (hp : 0<p) (hs : 0<s) :
    0≤emissionCoefficient p s := by
  have h := (polarization_contacts p hs).2.2
  rw [emissionCoefficient,h]
  unfold pairEnergy
  positivity

theorem vacuumEnergy_spectral (complete : Bool) {p s : ℝ} (hp : 0<p) (hs : 0<s) (x : ℝ) :
    (vacuumHamiltonian complete p s x - Matrix.scalar (Fin 2) (vacuumEnergy complete p s x)).det=0 ∧
     vacuumEnergy complete p s x ≤ (pairEnergy p s+p+x^2*contactCoefficient complete p s)/2 := by
  set c := contactCoefficient complete p s with hc
  set b := pairEnergy p s+p with hb
  set w := emissionCoefficient p s with he
  have hw := emissionCoefficient_nonneg hp hs
  have hw' : 0≤w := hw
  have hq := Real.sq_sqrt (show 0≤(b-x^2*c)^2+4*x^2*w by positivity)
  have ht := Real.sq_sqrt hw'
  change _ ∧ lowRoot c b w x ≤ _
  constructor
  · rw [Matrix.det_fin_two]
    simp [vacuumHamiltonian,vacuumEnergy,lowRoot,Matrix.scalar_apply,←hc,←hb,←he]
    linear_combination (1/4:ℝ)*hq - x^2*ht
  · unfold lowRoot
    linarith [Real.sqrt_nonneg ((b-x^2*c)^2+4*x^2*w)]

private theorem lowRoot_quadratic {b w : ℝ} (hb : 0<b) (hw : 0≤w) (c : ℝ) :
    Tendsto (fun x:ℝ => lowRoot c b w x/x^2) (𝓝[≠] 0) (𝓝 (c-w/b)) := by
  let Q := fun x:ℝ => Real.sqrt ((b-x^2*c)^2+4*x^2*w)
  let den := fun x:ℝ => b+x^2*c+Q x
  have h0 : den 0=2*b := by simp [den,Q,Real.sqrt_sq hb.le]; ring
  have hc : Continuous den := by dsimp [den,Q]; fun_prop
  have hd : den 0≠0 := by rw [h0]; positivity
  have hd' : ∀ᶠ x in 𝓝[≠] (0:ℝ),den x≠0 :=
    (hc.continuousAt.eventually_ne hd).filter_mono nhdsWithin_le_nhds
  have h := ((tendsto_const_nhds (x:=2*(b*c-w))).div (hc.tendsto 0) hd).mono_left
    (nhdsWithin_le_nhds (s:={0}ᶜ))
  have hh : 2*(b*c-w)/den 0=c-w/b := by rw [h0]; field_simp
  rw [hh] at h
  apply h.congr'
  filter_upwards [hd',self_mem_nhdsWithin] with x hx hx0
  have hx' : x≠0 := hx0
  have hq : (Q x)^2 = (b-x^2*c)^2+4*x^2*w := Real.sq_sqrt (by positivity)
  dsimp [lowRoot]
  change _= (b+x^2*c-Q x)/2/x^2
  field_simp [hx,hx']
  dsimp [den]
  linear_combination hq

/-- The second-order vacuum energy of the physical emission Hamiltonian
has exactly the contact-minus-exchange coefficient used in the mass integral. -/
theorem vacuumHamiltonian_coefficient (complete : Bool) {p s : ℝ} (hp : 0<p) (hs : 0<s) :
    Tendsto (fun x:ℝ => vacuumEnergy complete p s x/x^2) (𝓝[≠] 0)
      (𝓝 (sewnWeight complete 1 p s)) := by
  have hd : 0<pairEnergy p s := Real.sqrt_pos.mpr (by positivity)
  have h := lowRoot_quadratic (add_pos hd hp) (emissionCoefficient_nonneg hp hs) (contactCoefficient complete p s)
  change Tendsto _ _ _ at h
  convert h using 2
  unfold sewnWeight contactCoefficient emissionCoefficient
  field_simp [hd.ne',hp.ne',(add_pos hd hp).ne']

/-- With the original three independent carrier-momentum components
and spatial Fourier normalization, neither Hamiltonian has an absolutely
integrable vacuum coefficient. -/
theorem vacuum_spatial_not_integrable (complete : Bool) {e m ℓ : ℝ}
    (he : e≠0) (hm : 0<m) (hℓ : 0<ℓ) :
    ¬MeasureTheory.Integrable (fun P : ChargeSpatialMomentum =>
      massResponse complete e m ℓ ‖P‖ / (2*Real.pi)^3) := by
  intro hi
  have h := hi.const_mul ((2*Real.pi)^3)
  have hf : MeasureTheory.Integrable (fun P : ChargeSpatialMomentum => massResponse complete e m ℓ ‖P‖) := by
    apply h.congr
    filter_upwards with P
    field_simp
  have hr := (MeasureTheory.integrable_fun_norm_addHaar (E := ChargeSpatialMomentum) MeasureTheory.volume
    (f := massResponse complete e m ℓ)).mp hf
  apply vacuum_radial_not_integrable complete he hm hℓ 0
  simpa [ChargeSpatialMomentum,smul_eq_mul] using hr

end UV.PairCurvature
