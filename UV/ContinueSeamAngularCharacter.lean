import UV.ContinueSeamAngularMetric

/-! The Dirichlet form is evaluated on the actual normalized Gauss-neutral
Fourier character of the two period-2π angles. -/

noncomputable section

namespace UV.SeamAngular

open Real Matrix MeasureTheory Set
open scoped ComplexConjugate BigOperators

theorem seam_character_real_lift (q : ℤ) (x y : ℝ) :
    seamCharacter q (-q) (x:SeamCircle) (y:SeamCircle) =
      Complex.exp (Complex.I*(((q:ℝ)*(x-y):ℝ):ℂ)) := by
  rw [seamCharacter,fourier_coe_apply,fourier_coe_apply,← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem seam_character_directional_derivative (q : ℤ) (x v : AngularCoordinates) :
    HasDerivAt (fun t : ℝ => seamCharacter q (-q) ((x 0+t*v 0 : ℝ):SeamCircle)
        ((x 1+t*v 1 : ℝ):SeamCircle))
      (Complex.I*(((q:ℝ)*(v 0-v 1):ℝ):ℂ)*seamCharacter q (-q) (x 0:SeamCircle) (x 1:SeamCircle)) 0 := by
  simp_rw [seam_character_real_lift]
  have hd : HasDerivAt (fun t : ℝ => (q:ℝ)*((x 0+t*v 0)-(x 1+t*v 1))) ((q:ℝ)*(v 0-v 1)) 0 := by
    simpa only [id_eq,one_mul] using ((((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (x 0)).sub
      (((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (x 1))).const_mul (q:ℝ)
  simpa only [zero_mul,add_zero,mul_comm] using (hd.ofReal_comp.const_mul Complex.I).cexp

def seamCharacterSlope (q : ℤ) (x : AngularCoordinates) (i : Fin 2) : ℂ :=
  let v : AngularCoordinates := Pi.single i 1
  deriv (fun t : ℝ => seamCharacter q (-q) ((x 0+t*v 0 : ℝ):SeamCircle)
    ((x 1+t*v 1 : ℝ):SeamCircle)) 0

theorem seam_character_slope (q : ℤ) (x : AngularCoordinates) (i : Fin 2) :
    seamCharacterSlope q x i = Complex.I * (((q:ℝ)*seamDifference i:ℝ):ℂ) *
      seamCharacter q (-q) (x 0:SeamCircle) (x 1:SeamCircle) := by
  rw [seamCharacterSlope,(seam_character_directional_derivative q x (Pi.single i 1)).deriv]
  fin_cases i <;> norm_num [Pi.single_apply,seamDifference]

theorem seam_character_dirichlet_energy (M : AngularMatrix) (q : ℤ) (x : AngularCoordinates) :
    (∑ i, ∑ j, conj (seamCharacterSlope q x i) * ((M⁻¹ i j:ℝ):ℂ) * seamCharacterSlope q x j) =
      (((q:ℝ)^2 * seamForm M seamOrbit / M.det : ℝ):ℂ) := by
  let z := seamCharacter q (-q) (x 0:SeamCircle) (x 1:SeamCircle)
  let w := (q:ℝ) • seamDifference
  have hnorm : ‖z‖ = 1 := by simp [z,seam_character_real_lift,Complex.norm_exp,Complex.mul_re]
  have hz : conj z*z = 1 := by rw [mul_comm,Complex.mul_conj',hnorm]; norm_num
  have he (i j : Fin 2) :
      conj (seamCharacterSlope q x i) * ((M⁻¹ i j:ℝ):ℂ) * seamCharacterSlope q x j =
      ((w i*(M⁻¹ i j*w j):ℝ):ℂ) := by
    rw [seam_character_slope,seam_character_slope]
    change conj (Complex.I*(w i:ℂ)*z)*((M⁻¹ i j:ℝ):ℂ)*(Complex.I*(w j:ℂ)*z) = _
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_mul]
    calc
      _ = ((w i:ℂ)*((M⁻¹ i j:ℝ):ℂ)*(w j:ℂ))*(-(Complex.I^2))*(conj z*z) := by ring
      _ = _ := by rw [hz,Complex.I_sq]; ring
  simp_rw [he]
  rw [← seam_selection_identity]
  simp [seamForm,dotProduct,mulVec,Fin.sum_univ_two,w,Pi.smul_apply,smul_eq_mul]
  ring

end UV.SeamAngular
