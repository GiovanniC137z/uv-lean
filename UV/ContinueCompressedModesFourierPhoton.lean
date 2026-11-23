import UV.ContinueCompressedModesMaxwell

/-! Reality of the complex Fourier photon. Each independent nonzero
mode pair ±Q uses two real Gaussian coordinate families. Equal signs
have vanishing bilinear covariance and opposite signs give the
ordinary transverse Maxwell covariance. -/

noncomputable section
open MeasureTheory UV.SectorPlane UV.NextCurvatureLaw
namespace UV

private theorem compressed_gaussian_linear_cov {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (s : α → ModeSlot n) (t : β → ModeSlot n) (a : α → ℂ) (b : β → ℂ) :
    (∫ X, (∑ i, a i*(X (s i):ℂ))*(∑ j, b j*(X (t j):ℂ)) ∂commonGaussian n) =
      ∑ i, ∑ j, (a i*b j)*(if s i=t j then (1/2:ℂ) else 0) := by
  let f (i : α) (j : β) (X : ModeSlot n → ℝ) : ℂ := (a i*b j)*((X (s i)*X (t j):ℝ):ℂ)
  have hi (i j) : Integrable (f i j) (commonGaussian n) := by
    apply Integrable.const_mul
    apply Integrable.ofReal
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using
      (VerifyCurvaturePairings.coordinate_list_wick [s i,t j] 1 (by simp)).1
  have hv (X : ModeSlot n → ℝ) :
      (∑ i, a i*(X (s i):ℂ))*(∑ j, b j*(X (t j):ℂ)) = ∑ i, ∑ j, f i j X := by
    simp only [Fintype.sum_mul_sum,f,Complex.ofReal_mul,mul_mul_mul_comm]
  simp_rw [hv]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∫ X, f i j X ∂commonGaussian n) = (a i*b j)*(∫ X : ModeSlot n → ℝ, ((X (s i)*X (t j):ℝ):ℂ) ∂commonGaussian n) from integral_const_mul _ _,
    integral_complex_ofReal,AdvanceCurvatureWick.baseCoord_pair_integral]
  split <;> norm_num

def compressedFourierPhase (positive imag : Bool) : ℂ :=
  if imag then (if positive then Complex.I else -Complex.I) else 1

def compressedFourierPhoton {n : ℕ} (k : MeanZeroMode) (slot : Fin 4 → Fin n) (pos : Bool)
    (χ : OSFourSpace → ℂ) (p : OSFourSpace) (u : UnitVector OSFourSpace) (X : ModeSlot n → ℝ) : ℂ :=
  ∑ a : Bool × Fin 4, compressedFourierPhase pos a.1 * (compressedMaxwellWeight χ p u a.2:ℂ) *
    (X (k,((if a.1 then 1 else 0):Fin 2),slot a.2):ℂ)

theorem compressed_fourier_reality {n : ℕ} (k : MeanZeroMode) (slot : Fin 4 → Fin n)
    (χ : OSFourSpace → ℂ) (p : OSFourSpace) (u : UnitVector OSFourSpace) (X : ModeSlot n → ℝ) :
    compressedFourierPhoton k slot false χ p u X = star (compressedFourierPhoton k slot true χ p u X) := by
  simp only [compressedFourierPhoton,star_sum]
  apply Finset.sum_congr rfl
  rintro ⟨b,i⟩ _
  cases b <;> simp [compressedFourierPhase,mul_assoc]

theorem compressed_fourier_maxwell_covariance {n : ℕ} (k l : MeanZeroMode) (slot : Fin 4 → Fin n)
    (hs : Function.Injective slot) (pos pos' : Bool) (χ : OSFourSpace → ℂ) (p : OSFourSpace)
    (u v : UnitVector OSFourSpace) :
    (∫ X, compressedFourierPhoton k slot pos χ p u X * compressedFourierPhoton l slot pos' χ p v X ∂commonGaussian n) =
      if k=l ∧ pos ≠ pos' then ((WilsonPhotonPolarizations.mk u v).maxwell χ p:ℂ) else 0 := by
  let S (k : MeanZeroMode) (a : Bool × Fin 4) : ModeSlot n := (k,(if a.1 then 1 else 0),slot a.2)
  have hslot (a b : Bool × Fin 4) : S k a = S l b ↔ k=l ∧ a=b := by
    rcases a with ⟨x,i⟩
    rcases b with ⟨y,j⟩
    cases x <;> cases y <;> simp [S,hs.eq_iff]
  simp only [compressedFourierPhoton]
  rw [compressed_gaussian_linear_cov]
  change (∑ a : Bool × Fin 4, ∑ b : Bool × Fin 4, _ * (if S k a = S l b then _ else 0)) = _
  simp_rw [hslot]
  by_cases hkl : k=l
  · simp only [hkl,true_and,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [←compressed_maxwell_gram χ p u v,Complex.ofReal_sum,Fintype.sum_prod_type,Fintype.sum_bool]
    cases pos <;> cases pos' <;> simp only [compressedFourierPhase,if_true,if_false,Bool.true_eq_false,Bool.false_eq_true,
      ne_eq,not_true_eq_false,not_false_eq_true,Complex.ofReal_mul,one_mul,←Finset.sum_add_distrib]
    all_goals first | apply Finset.sum_congr rfl; intro i _ | apply Finset.sum_eq_zero; intro i _
    all_goals ring_nf
    all_goals simp [Complex.I_sq] <;> ring
  · simp [hkl]

end UV
