import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The two-particle mass-shell change of variables at a fixed spatial
transfer. The transverse directions are held fixed and the longitudinal
direction is a unit axis of the spatial orthonormal frame. -/

noncomputable section
open Real MeasureTheory Filter Set
open scoped ENNReal Topology
namespace UV.PairCurvature

def restEnergySq (s y : ℝ) := s + y^2
def longitudinalLorentzFactor (s p y : ℝ) := sqrt (1 + p^2/(4 * restEnergySq s y))
def longitudinalPairMomentum (s p y : ℝ) := p/2 + longitudinalLorentzFactor s p y*y

def oneParticleAxialEnergy (s y : ℝ) := sqrt (restEnergySq s y)

theorem restEnergySq_pos {s : ℝ} (hs : 0 < s) (y : ℝ) : 0 < restEnergySq s y := by
  unfold restEnergySq
  positivity

theorem longitudinalLorentzFactor_sq {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    longitudinalLorentzFactor s p y ^ 2 = 1 + p^2/(4 * restEnergySq s y) :=
  Real.sq_sqrt (add_nonneg zero_le_one (div_nonneg (sq_nonneg p) (mul_nonneg (by norm_num) (restEnergySq_pos hs y).le)))

theorem longitudinalLorentzFactor_ge_one {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    1 ≤ longitudinalLorentzFactor s p y := by
  unfold longitudinalLorentzFactor
  have h : 1 ≤ 1 + p^2/(4 * restEnergySq s y) := le_add_of_nonneg_right
    (div_nonneg (sq_nonneg p) (mul_nonneg (by norm_num) (restEnergySq_pos hs y).le))
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h

private theorem longitudinal_energy_formula {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    oneParticleAxialEnergy s (longitudinalPairMomentum s p y) =
      longitudinalLorentzFactor s p y * oneParticleAxialEnergy s y + p*y/(2 * oneParticleAxialEnergy s y) := by
  let R := restEnergySq s y
  let E₀ := oneParticleAxialEnergy s y
  let γ := longitudinalLorentzFactor s p y
  have hR : 0 < R := restEnergySq_pos hs y
  have hE : 0 < E₀ := sqrt_pos.2 hR
  have hE₂ : E₀^2 = R := sq_sqrt hR.le
  have hγ₀ : 0 < γ := zero_lt_one.trans_le (longitudinalLorentzFactor_ge_one hs p y)
  have hγ₂ : γ^2 = 1+p^2/(4*R) := longitudinalLorentzFactor_sq hs p y
  have he : (γ*E₀ + p*y/(2*E₀))^2 = s + (p/2+γ*y)^2 := by
    have hrel : 4*R*γ^2 = 4*R+p^2 := by
      rw [hγ₂]
      field_simp
    calc
      _ = γ^2*R + γ*p*y + p^2*y^2/(4*R) := by
        rw [← hE₂]
        field_simp
        ring
      _ = _ := by
        field_simp
        dsimp only [R, restEnergySq] at *
        linear_combination (4*s)*hrel
  have hbound : |p*y/(2*E₀)| < γ * E₀ := by
    apply (sq_lt_sq₀ (abs_nonneg _) (mul_nonneg hγ₀.le hE.le)).1
    simp only [sq_abs,div_pow,mul_pow,hE₂,hγ₂]
    have hY : y^2 ≤ R := by dsimp only [R, restEnergySq]; linarith
    have h₁ : p^2*y^2/(4*R) ≤ p^2/4 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hR)).2
      have h := mul_le_mul_of_nonneg_left hY (sq_nonneg p)
      linarith
    have h₂ : (1+p^2/(4*R))*R = R+p^2/4 := by field_simp
    rw [h₂]
    nlinarith [h₁, hR]
  have hplus : 0 ≤ γ * E₀ + p*y/(2*E₀) := by linarith [neg_abs_le (p*y/(2*E₀))]
  change sqrt (s + (p/2+γ*y)^2) = γ*E₀ + p*y/(2*E₀)
  exact (Real.sqrt_eq_iff_eq_sq (add_nonneg hs.le (sq_nonneg _)) hplus).2 he.symm

theorem longitudinal_pair_mass_and_energy {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    let k := longitudinalPairMomentum s p y
    let D := oneParticleAxialEnergy s k + oneParticleAxialEnergy s (p-k)
    let R := restEnergySq s y
    let γ := longitudinalLorentzFactor s p y
    D = 2*γ*oneParticleAxialEnergy s y ∧ D^2-p^2 = 4*R := by
  have hk : p-longitudinalPairMomentum s p y = longitudinalPairMomentum s p (-y) := by
    simp only [longitudinalPairMomentum,longitudinalLorentzFactor,restEnergySq,neg_sq]
    ring
  dsimp only
  rw [hk,longitudinal_energy_formula hs p y,longitudinal_energy_formula hs p (-y)]
  simp only [longitudinalLorentzFactor,oneParticleAxialEnergy,restEnergySq,neg_sq]
  constructor
  · ring
  · have hR := restEnergySq_pos hs y
    change (_ : ℝ) = _
    have hE := sq_sqrt hR.le
    have hγ := longitudinalLorentzFactor_sq hs p y
    change sqrt (1+p^2/(4*(s+y^2)))^2 = _ at hγ
    rw [show sqrt (1+p^2/(4*(s+y^2))) * sqrt (s+y^2) + p*y/(2*sqrt (s+y^2)) +
      (sqrt (1+p^2/(4*(s+y^2))) * sqrt (s+y^2) + p*(-y)/(2*sqrt (s+y^2))) =
        2*sqrt (1+p^2/(4*(s+y^2)))*sqrt (s+y^2) by ring, mul_pow,mul_pow,hγ]
    change sqrt (s+y^2)^2 = s+y^2 at hE
    rw [hE]
    simp only [restEnergySq] at hR ⊢
    field_simp [hR.ne']
    ring

def longitudinalPairJacobian (s p y : ℝ) :=
  let k := longitudinalPairMomentum s p y
  oneParticleAxialEnergy s k * oneParticleAxialEnergy s (p-k) /
    (longitudinalLorentzFactor s p y * restEnergySq s y)

theorem longitudinalPairJacobian_pos {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    0 < longitudinalPairJacobian s p y := by
  unfold longitudinalPairJacobian oneParticleAxialEnergy
  exact div_pos (mul_pos (sqrt_pos.2 (restEnergySq_pos hs _)) (sqrt_pos.2 (restEnergySq_pos hs _)))
    (mul_pos (zero_lt_one.trans_le (longitudinalLorentzFactor_ge_one hs p y)) (restEnergySq_pos hs y))

theorem longitudinal_pair_hasDerivAt {s : ℝ} (hs : 0 < s) (p y : ℝ) :
    HasDerivAt (longitudinalPairMomentum s p) (longitudinalPairJacobian s p y) y := by
  let R := restEnergySq s y
  let E₀ := oneParticleAxialEnergy s y
  let γ := longitudinalLorentzFactor s p y
  have hR := restEnergySq_pos hs y
  have hE : 0 < E₀ := sqrt_pos.2 hR
  have hE₂ : E₀^2=R := sq_sqrt hR.le
  have hγ : 0 < γ := zero_lt_one.trans_le (longitudinalLorentzFactor_ge_one hs p y)
  have hRD : HasDerivAt (restEnergySq s) (2*y) y := by
    convert (hasDerivAt_pow 2 y).const_add s using 1
    ring
  have hi := (hRD.const_mul 4).inv (show 4*R≠0 by positivity)
  have hi' := (hi.const_mul (p^2)).const_add 1
  have hg := hi'.sqrt (show 1+p^2*(4*R)⁻¹ ≠ 0 by positivity)
  have hD : HasDerivAt (longitudinalLorentzFactor s p) (-(p^2*y)/(4*γ*R^2)) y := by
    convert hg using 1
    change -(p^2*y)/(4*γ*R^2) = (p^2 * (-(4*(2*y))/(4*R)^2)) /
      (2*sqrt (1+p^2*(4*R)⁻¹))
    rw [show sqrt (1+p^2*(4*R)⁻¹) = γ by dsimp [γ,R,longitudinalLorentzFactor]; rfl]
    field_simp
  have hk : p-longitudinalPairMomentum s p y = longitudinalPairMomentum s p (-y) := by
    simp only [longitudinalPairMomentum,longitudinalLorentzFactor,restEnergySq,neg_sq]
    ring
  have he : longitudinalPairJacobian s p y = (-(p^2*y)/(4*γ*R^2))*y+γ := by
    unfold longitudinalPairJacobian
    dsimp only
    rw [hk,longitudinal_energy_formula hs p y,longitudinal_energy_formula hs p (-y)]
    have hg' : longitudinalLorentzFactor s p (-y)=γ := by simp [γ,longitudinalLorentzFactor,restEnergySq]
    have he' : oneParticleAxialEnergy s (-y)=E₀ := by simp [E₀,oneParticleAxialEnergy,restEnergySq]
    rw [hg',he']
    change ((γ*E₀ + p*y/(2*E₀)) * (γ*E₀ + p*(-y)/(2*E₀))) / (γ*R) = _
    rw [← hE₂]
    field_simp [hE.ne']
    ring
  rw [he]
  convert ((hD.mul (hasDerivAt_id y)).const_add (p/2)) using 1
  simp [γ]

theorem longitudinal_pair_strictMono {s : ℝ} (hs : 0 < s) (p : ℝ) :
    StrictMono (longitudinalPairMomentum s p) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(longitudinal_pair_hasDerivAt hs p y).deriv]
  exact longitudinalPairJacobian_pos hs p y

theorem longitudinal_pair_surjective {s : ℝ} (hs : 0 < s) (p : ℝ) :
    Function.Surjective (longitudinalPairMomentum s p) := by
  intro k
  let R := |k-p/2| + 1
  have hp : 0 < R := by dsimp [R]; positivity
  have hC : Continuous (longitudinalPairMomentum s p) :=
    continuous_iff_continuousAt.mpr (fun y => (longitudinal_pair_hasDerivAt hs p y).continuousAt)
  have h : k ∈ Icc (longitudinalPairMomentum s p (-R)) (longitudinalPairMomentum s p R) := by
    have hl := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (longitudinalLorentzFactor_ge_one hs p (-R))) (neg_nonpos.mpr hp.le)
    have hr := mul_nonneg (sub_nonneg.mpr (longitudinalLorentzFactor_ge_one hs p R)) hp.le
    unfold longitudinalPairMomentum
    exact ⟨by nlinarith [neg_abs_le (k-p/2)], by nlinarith [le_abs_self (k-p/2)]⟩
  obtain ⟨y,_,hy⟩ := intermediate_value_Icc (show -R ≤ R by linarith) hC.continuousOn h
  exact ⟨y,hy⟩

/-- At fixed total spatial momentum the product of the two one-particle
normalization factors absorbs the full axial Jacobian. The surviving
factor is 1/γ times the rest-frame product. -/
theorem longitudinal_pair_measure {s : ℝ} (hs : 0 < s) (p : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ k, F k * ENNReal.ofReal ((4*oneParticleAxialEnergy s k*oneParticleAxialEnergy s (p-k))⁻¹)) =
      ∫⁻ y, F (longitudinalPairMomentum s p y) *
        ENNReal.ofReal ((4*longitudinalLorentzFactor s p y * restEnergySq s y)⁻¹) := by
  let k := longitudinalPairMomentum s p
  have hS : k '' (univ : Set ℝ) = univ := by
    rw [image_univ, range_eq_univ]
    exact longitudinal_pair_surjective hs p
  have hD (x : ℝ) (_hx : x ∈ univ) :
      HasDerivWithinAt k (longitudinalPairJacobian s p x) univ x :=
    (longitudinal_pair_hasDerivAt hs p x).hasDerivWithinAt
  have hEq := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hD
    (longitudinal_pair_strictMono hs p).injective.injOn (fun x =>
      F x * ENNReal.ofReal ((4*oneParticleAxialEnergy s x*oneParticleAxialEnergy s (p-x))⁻¹))
  rw [hS, Measure.restrict_univ] at hEq
  rw [hEq]
  apply lintegral_congr
  intro y
  rw [abs_of_pos (longitudinalPairJacobian_pos hs p y), mul_left_comm,
    ← ENNReal.ofReal_mul (longitudinalPairJacobian_pos hs p y).le]
  congr 2
  unfold longitudinalPairJacobian
  dsimp only [k]
  have h₁ : oneParticleAxialEnergy s (longitudinalPairMomentum s p y) ≠ 0 :=
    (sqrt_pos.2 (restEnergySq_pos hs _)).ne'
  have h₂ : oneParticleAxialEnergy s (p-longitudinalPairMomentum s p y) ≠ 0 :=
    (sqrt_pos.2 (restEnergySq_pos hs _)).ne'
  field_simp [h₁,h₂]

end UV.PairCurvature
