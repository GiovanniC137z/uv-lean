import UV.ContinueFiveBallPortalSpin
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Maxwell sewing of the massive pair-curvature vertex, in an orthonormal
carrier rest/boost chart on a fixed sector plane. The 0 component is timelike.
The two emitted photon polarizations are the first two spatial unit axes. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Matrix Topology

namespace UV.PairCurvature

def pairEnergy (p s : ℝ) := Real.sqrt (p^2+s)

def pairMomentum (p s : ℝ) : Fin 4 → ℝ := fun i => if i=0 then pairEnergy p s else if i=3 then p else 0

def metricSign : Fin 4 → ℝ := fun i => if i=0 then 1 else -1

/-- Three columns square to the Lorentz current tensor PᵘPᵛ−ηᵘᵛs. -/
def current (p s : ℝ) : Fin 3 → Fin 4 → ℝ :=
  fun a i => if a=0 then (if i=1 then Real.sqrt s else 0) else if a=1 then (if i=2 then Real.sqrt s else 0) else if i=0 then p else if i=3 then pairEnergy p s else 0

theorem current_tensor (p : ℝ) {s : ℝ} (hs : 0 < s) (i j : Fin 4) :
    ∑ a : Fin 3, current p s a i * current p s a j =
      pairMomentum p s i * pairMomentum p s j - (if i=j then metricSign i*s else 0) := by
  have h := Real.sq_sqrt (show 0 ≤ p^2+s by positivity)
  have hs' := Real.sq_sqrt hs.le
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Fin.sum_univ_three,current,pairMomentum,metricSign,pairEnergy] <;> nlinarith

/-- The common phase −i drops out of every squared matrix element. -/
def pairTensor (p s : ℝ) (a : Fin 3) (i j : Fin 4) : ℝ :=
  (pairMomentum p s i * current p s a j - pairMomentum p s j * current p s a i)/s

/-- q=(p,0,0,−p). Lowering its spatial index gives the plus sign. -/
def emission (p s : ℝ) (a : Fin 3) (i : Fin 2) :=
  p*pairTensor p s a 0 i.castSucc.succ+p*pairTensor p s a 3 i.castSucc.succ

def electricContact (p s : ℝ) := ∑ a : Fin 3, ∑ i : Fin 3, (pairTensor p s a 0 i.succ)^2

def magneticContact (p s : ℝ) := ∑ a : Fin 3, ((pairTensor p s a 1 2)^2+
  (pairTensor p s a 2 3)^2+(pairTensor p s a 3 1)^2)

def emittedSquare (p s : ℝ) := ∑ a : Fin 3, ∑ i : Fin 2, (emission p s a i)^2

theorem polarization_contacts (p : ℝ) {s : ℝ} (hs : 0 < s) :
    electricContact p s = 1+2*(pairEnergy p s)^2/s ∧
    magneticContact p s = 2*p^2/s ∧
    emittedSquare p s = 2*p^2*(pairEnergy p s+p)^2/s := by
  have hd : (pairEnergy p s)^2=p^2+s := Real.sq_sqrt (by positivity)
  have ht := Real.sq_sqrt hs.le
  simp only [electricContact,magneticContact,emittedSquare,emission,pairTensor,
    current,pairMomentum,Fin.sum_univ_three,Fin.sum_univ_two]
  simp (config := {decide := true})
  field_simp [hs.ne']
  constructor
  · linear_combination (-(pairEnergy p s)^2+p^2-s)*(-hd) + 2*(pairEnergy p s)^2*ht
  constructor <;> nlinarith [congrArg (· * p^2) ht,
    congrArg (· * (p^2*(pairEnergy p s+p)^2)) ht]

/-- Maxwell Legendre and Coulomb contacts, physical intermediate pair and
photon, and optional magnetic contact, with the common mass spectral weight. -/
def sewnWeight (complete : Bool) (e p s : ℝ) :=
  let D := pairEnergy p s
  e^2/(4*D)*(electricContact p s + (if complete then magneticContact p s else 0) -
    emittedSquare p s/(p*(D+p)))

theorem sewn_weight (e : ℝ) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    sewnWeight false e p s = e^2/4*(3/pairEnergy p s-2*p/s) ∧
    sewnWeight true e p s = e^2/(4*pairEnergy p s)*(3-2*p/(pairEnergy p s+p)) := by
  have hd : 0<pairEnergy p s := Real.sqrt_pos.mpr (by positivity)
  have he : (pairEnergy p s)^2=p^2+s := Real.sq_sqrt (by positivity)
  obtain ⟨h₁,h₂,h₃⟩ := polarization_contacts p hs
  simp only [sewnWeight,h₁,h₂,h₃,Bool.false_eq_true,if_false,add_zero,if_true]
  constructor <;> field_simp [hd.ne',hs.ne',hp.ne',(add_pos hd hp).ne']
  · linear_combination 2*e^2*he
  · nlinarith [congrArg (· * (2*e^2*(pairEnergy p s+p))) he]

def massDensity (m ℓ s : ℝ) : ℝ := if 4*m^2≤s then
  openingWeight (4*m^2/s)/(12*Real.pi^2)*Real.exp (-(2*ℓ^4)*s^2) else 0

theorem massDensity_nonneg (m ℓ s : ℝ) : 0 ≤ massDensity m ℓ s := by
  unfold massDensity
  split_ifs
  · exact mul_nonneg (div_nonneg (openingWeight_nonneg _) (by positivity)) (Real.exp_pos _).le
  · rfl

theorem massDensity_integrable (m : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : Integrable (massDensity m ℓ) := by
  have h := (integrable_exp_neg_mul_sq (show 0 < 2*ℓ^4 by positivity)).const_mul ((3/2)/(12*Real.pi^2))
  have hmeas : Measurable (massDensity m ℓ) := by
    unfold massDensity openingWeight
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  refine h.mono' hmeas.aestronglyMeasurable ?_
  refine ae_of_all _ fun s => ?_
  rw [Real.norm_of_nonneg (massDensity_nonneg ..)]
  unfold massDensity
  split_ifs
  · gcongr; exact openingWeight_le _
  · positivity

/-- The invariant density comes from the ordinary Dirac occupied/empty spin
projectors and the rest-frame radial phase-space Jacobian, with the square
of the specified entire pair form factor. -/
theorem massDensity_from_spin {m : ℝ} (hm : 0<m) (ℓ : ℝ)
    (k : ChargeSpatialMomentum) (hk : k≠0) :
    let y := 2*FurtherOptical.energy m k
    let spin := (∑ i : Fin 3, (portalPairTrace (FurtherOptical.coefficients m 0 k) i).re)/3
    (4*Real.pi/(2*Real.pi)^3)*‖k‖^2*(y/(4*‖k‖))*spin/y^2*
      (Real.exp (-(ℓ^4)*(y^2)^2))^2 = massDensity m ℓ (y^2) := by
  let y := 2*FurtherOptical.energy m k
  have hy : 0<y := mul_pos (by norm_num) (FurtherOptical.energy_pos hm _)
  have hd : 4*m^2 ≤ y^2 := by
    dsimp [y]
    nlinarith [FurtherOptical.energy_sq m k,sq_nonneg ‖k‖]
  have h := portal_cut_from_spin (b := y^2/2) hm k hk
  dsimp only at h ⊢
  change _ = massDensity m ℓ (y^2)
  change _*( (y^2/2)^2/(y^2-y^2/2)^2 )=portalPairCut m (y^2/2) (y^2) at h
  rw [portalPairCut,if_pos hd,show (y^2/2)^2/(y^2-y^2/2)^2=1 by field_simp; ring,mul_one,one_mul] at h
  rw [massDensity,if_pos hd,←h,←Real.exp_nat_mul]
  congr 2
  dsimp [y]
  ring

end UV.PairCurvature
