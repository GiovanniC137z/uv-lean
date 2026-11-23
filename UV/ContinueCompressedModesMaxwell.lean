import UV.ContinueCompressedModesWick

/-! The endpoint Gram matrix of the projected real Gaussian Maxwell
coordinates equals the actual transverse photon edge used in the graph
bounds. -/

noncomputable section
open MeasureTheory UV.SectorPlane UV.NextCurvatureLaw
open scoped RealInnerProductSpace
namespace UV

def compressedMaxwellWeight (χ : OSFourSpace → ℂ) (p : OSFourSpace)
    (u : UnitVector OSFourSpace) (a : Fin 4) : ℝ :=
  ‖χ p‖/‖p‖ * ((ℝ ∙ p)ᗮ.starProjection u.val) a

theorem compressed_maxwell_gram (χ : OSFourSpace → ℂ) (p : OSFourSpace) (u v : UnitVector OSFourSpace) :
    (∑ a, compressedMaxwellWeight χ p u a*compressedMaxwellWeight χ p v a) =
      (WilsonPhotonPolarizations.mk u v).maxwell χ p := by
  let K := (ℝ ∙ p)ᗮ
  have he : ∑ a, (K.starProjection u.val) a*(K.starProjection v.val) a =
      wilsonTransverseEntry u v p := by
    have hi := K.inner_starProjection_left_eq_right u.val (K.starProjection v.val)
    rw [K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v.val)] at hi
    change _ = ⟪u.val,K.starProjection v.val⟫
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm] using hi
  calc
    _ = (‖χ p‖/‖p‖)^2 * ∑ a, (K.starProjection u.val) a*(K.starProjection v.val) a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [compressedMaxwellWeight,K]
      ring
    _ = _ := by rw [he,div_pow,WilsonPhotonPolarizations.maxwell,wilsonPhotonDensity,mul_comm]

def compressedGaussianPhoton {n : ℕ} (slot : Fin 4 → ModeSlot n) (χ : OSFourSpace → ℂ) (p : OSFourSpace)
    (u : UnitVector OSFourSpace) (X : ModeSlot n → ℝ) : ℝ :=
  ∑ a, (Real.sqrt 2 * compressedMaxwellWeight χ p u a) * X (slot a)

theorem compressed_gaussian_photon_covariance {n : ℕ} (slot : Fin 4 → ModeSlot n) (hs : Function.Injective slot)
    (χ : OSFourSpace → ℂ) (p : OSFourSpace) (u v : UnitVector OSFourSpace) :
    (∫ X, compressedGaussianPhoton slot χ p u X * compressedGaussianPhoton slot χ p v X ∂commonGaussian n) =
      (WilsonPhotonPolarizations.mk u v).maxwell χ p := by
  let a (i : Fin 4) := Real.sqrt 2*compressedMaxwellWeight χ p u i
  let b (i : Fin 4) := Real.sqrt 2*compressedMaxwellWeight χ p v i
  let f (i j : Fin 4) (X : ModeSlot n → ℝ) := (a i*b j)*(X (slot i)*X (slot j))
  have hpair (i j : Fin 4) : Integrable (fun X : ModeSlot n → ℝ => X (slot i)*X (slot j)) (commonGaussian n) := by
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using
      (VerifyCurvaturePairings.coordinate_list_wick [slot i,slot j] 1 (by simp)).1
  have hi (i j : Fin 4) : Integrable (f i j) (commonGaussian n) := (hpair i j).const_mul _
  have hp (X) : compressedGaussianPhoton slot χ p u X * compressedGaussianPhoton slot χ p v X = ∑ i, ∑ j, f i j X := by
    simp only [compressedGaussianPhoton,Fintype.sum_mul_sum,f,a,b]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j)]
  have hm (i j) : (∫ X, f i j X ∂commonGaussian n) = (a i*b j)*(if i=j then 1/2 else 0) := by
    rw [show (∫ X, f i j X ∂commonGaussian n) = (a i*b j)*(∫ X : ModeSlot n → ℝ, X (slot i)*X (slot j) ∂commonGaussian n) from integral_const_mul _ _,
      AdvanceCurvatureWick.baseCoord_pair_integral]
    simp only [hs.eq_iff]
  suffices hh : ∀ i, (a i*b i)*(1/2) = compressedMaxwellWeight χ p u i*compressedMaxwellWeight χ p v i by
    simpa only [hm,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,hh] using compressed_maxwell_gram χ p u v
  intro i
  dsimp only [a,b]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

end UV
