import UV.ContinueWilsonShellRotation
import UV.ContinueWilsonPolygonMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Orthogonal covariance of the actual Euclidean Wilson spin matrices.
A unit Clifford normal implements a hyperplane reflection together with
the chirality involution. Cartan--Dieudonné then covers the full
orthogonal group, including the oriented GT chart reflection. -/

noncomputable section

open UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

private def wilsonChirality : DiracMatrix := Matrix.diagonal (![1,-1,-1,1] : Fin 4 → ℂ)

private theorem wilson_chirality_sq : wilsonChirality*wilsonChirality = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [wilsonChirality,Matrix.diagonal_apply,Matrix.one_apply]

private theorem wilson_chirality_gamma (k : Fin 4) :
    wilsonChirality * euclideanGamma k = -(euclideanGamma k * wilsonChirality) := by
  ext i j
  simp only [wilsonChirality,Matrix.diagonal_mul,Matrix.neg_apply,Matrix.mul_diagonal]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [euclideanGamma]

private theorem wilson_chirality_slash (x : OSFourSpace) : wilsonChirality*diracSlash x = -(diracSlash x*wilsonChirality) := by
  simp only [diracSlash,Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm,
    wilson_chirality_gamma,smul_neg,Finset.sum_neg_distrib]

theorem wilson_slash_anticommutator (u v : OSFourSpace) :
    diracSlash u * diracSlash v + diracSlash v * diracSlash u = ((2*⟪u,v⟫ : ℝ):ℂ) • (1 : DiracMatrix) := by
  have h := diracSlash_sq (u+v)
  rw [diracSlash_add,add_mul,mul_add,mul_add,diracSlash_sq,diracSlash_sq,norm_add_sq_real] at h
  simp only [Complex.ofReal_add,add_smul] at h
  linear_combination (norm := abel) h

private def WilsonSpinIntertwines (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) : Prop :=
  ∃ A B : DiracMatrix, A*B=1 ∧ B*A=1 ∧ ∀ x, diracSlash (R x)*A=A*diracSlash x

private theorem wilson_unit_reflection_spin (u : UnitVector OSFourSpace) :
    WilsonSpinIntertwines (ℝ ∙ u.val)ᗮ.reflection := by
  let N := diracSlash u.val
  let J := wilsonChirality
  have hN : N*N=1 := by simpa only [N,u.property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq u.val
  have hJ : J*J=1 := wilson_chirality_sq
  refine ⟨N*J,J*N,?_,?_,?_⟩
  · calc N*J*(J*N) = N*(J*J)*N := by noncomm_ring
         _ = 1 := by rw [hJ,mul_one,hN]
  · calc J*N*(N*J) = J*(N*N)*J := by noncomm_ring
         _ = 1 := by rw [hN,mul_one,hJ]
  · intro v
    let c := 2*⟪u.val,v⟫
    have hr : (ℝ ∙ u.val)ᗮ.reflection v = v + (-c) • u.val := by
      rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
      change -(2 • (⟪u.val,v⟫ / ‖u.val‖^2) • u.val - v) = _
      rw [u.property,one_pow,div_one]
      simp [two_smul,c,two_mul,neg_smul,add_smul,sub_eq_add_neg]
    have ha : diracSlash v * N + N * diracSlash v = (c:ℂ) • 1 := by
      simpa only [N,c,add_comm] using wilson_slash_anticommutator u.val v
    have hmatch : diracSlash ((ℝ ∙ u.val)ᗮ.reflection v)*N = -(N*diracSlash v) := by
      rw [hr,diracSlash_add,diracSlash_real_smul,add_mul,smul_mul_assoc,show diracSlash u.val = N from rfl,hN,
        Complex.ofReal_neg,neg_smul]
      linear_combination (norm := abel) ha
    calc diracSlash ((ℝ ∙ u.val)ᗮ.reflection v)*(N*J) = -(N*diracSlash v)*J := by rw [←mul_assoc,hmatch]
         _ = N * (-(diracSlash v*J)) := by noncomm_ring
         _ = N*J*diracSlash v := by rw [←wilson_chirality_slash]; exact (mul_assoc ..).symm

private theorem wilson_reflection_spin (v : OSFourSpace) : WilsonSpinIntertwines (ℝ ∙ v)ᗮ.reflection := by
  by_cases h : v = 0
  · subst v
    refine ⟨1,1,by simp,by simp,fun x => ?_⟩
    simp only [Submodule.span_zero_singleton,Submodule.bot_orthogonal_eq_top,mul_one,one_mul]
    rw [Submodule.reflection_mem_subspace_eq_self (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ OSFourSpace))]
  · let u : UnitVector OSFourSpace := ⟨‖v‖⁻¹ • v,by simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),h]⟩
    have hs : (ℝ ∙ u.val) = ℝ ∙ v := Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr h))) v
    let refl := fun K : Submodule ℝ OSFourSpace => Kᗮ.reflection
    change WilsonSpinIntertwines (refl (ℝ ∙ v))
    rw [←hs]
    exact wilson_unit_reflection_spin u

theorem wilson_spin_orthogonal_implementation (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) :
    ∃ A B : DiracMatrix, A*B=1 ∧ B*A=1 ∧ ∀ x, diracSlash (R x)*A=A*diracSlash x := by
  obtain ⟨l,hl,rfl⟩ := R.reflections_generate_dim
  clear hl
  change WilsonSpinIntertwines _
  induction l with
  | nil => exact ⟨1,1,by simp,by simp,fun x => by simp⟩
  | cons v l ih =>
    obtain ⟨A,B,hAB,hBA,hA⟩ := wilson_reflection_spin v
    obtain ⟨C,D,hCD,hDC,hC⟩ := ih
    refine ⟨A*C,D*B,?_,?_,?_⟩
    · calc A*C*(D*B) = A*(C*D)*B := by noncomm_ring
           _ = 1 := by rw [hCD,mul_one,hAB]
    · calc D*B*(A*C) = D*(B*A)*C := by noncomm_ring
           _ = 1 := by rw [hBA,mul_one,hDC]
    · intro x
      rw [List.map_cons,List.prod_cons,LinearIsometryEquiv.coe_mul,Function.comp_apply,←mul_assoc,hA,mul_assoc,hC,mul_assoc]

theorem wilson_spin_trace_orthogonal (L : ℝ) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) (d : List OSFourSpace) :
    (d.map (fun x => wilsonSpinWeight L (R x))).prod.trace = (d.map (wilsonSpinWeight L)).prod.trace := by
  obtain ⟨A,B,hAB,hBA,hA⟩ := wilson_spin_orthogonal_implementation R
  have hw (x) : wilsonSpinWeight L (R x)*A=A*wilsonSpinWeight L x := by
    simp only [wilsonSpinWeight,sub_mul,mul_sub,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,hA]
  have hp (l : List OSFourSpace) :
      (l.map (fun x => wilsonSpinWeight L (R x))).prod*A=A*(l.map (wilsonSpinWeight L)).prod := by
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons,List.prod_cons,mul_assoc,ih,←mul_assoc (wilsonSpinWeight L (R x)) A,hw]
  calc _ = ((d.map (fun x => wilsonSpinWeight L (R x))).prod * A * B).trace := by rw [mul_assoc,hAB,mul_one]
       _ = _ := by rw [hp,Matrix.trace_mul_cycle,hBA,one_mul]

end UV
