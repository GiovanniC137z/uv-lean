import UV.ContinueCollarWirtinger

/-! Assemble Dirichlet trial spaces from the orthonormality of the
individual modes and the actual bilinear weak eigenfunction equations. -/

noncomputable section

open MeasureTheory Set Real

namespace UV.CollarEigenmode

private def trialMap {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) : (ι → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun c r := ∑ i,c i*f i r
  map_add' c d := by ext r; simp [add_mul,Finset.sum_add_distrib]
  map_smul' k c := by ext r; simp [Finset.mul_sum,mul_assoc]

private def gram {ι : Type*} [Fintype ι] (F : ι → ι → ℝ → ℝ) (c : ι → ℝ) (r : ℝ) :=
  ∑ i,∑ j,(c i*c j)*F i j r

private theorem interval_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (h : ∀ i,IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun x => ∑ i,f i x) volume 0 1 := by
  convert IntervalIntegrable.sum (f := f) Finset.univ (fun i _ => h i) using 1
  ext x
  simp only [Finset.sum_apply]

private theorem integral_gram {ι : Type*} [Fintype ι] (F : ι → ι → ℝ → ℝ) (c : ι → ℝ)
    (h : ∀ i j,IntervalIntegrable (F i j) volume 0 1) :
    IntervalIntegrable (gram F c) volume 0 1 ∧
    (∫ x in (0:ℝ)..1,gram F c x)= ∑ i,∑ j,(c i*c j)*(∫ x in (0:ℝ)..1,F i j x) := by
  have hi i j := (h i j).const_mul (c i*c j)
  have hrow i := interval_sum (fun j x => (c i*c j)*F i j x) (hi i)
  refine ⟨interval_sum _ hrow,?_⟩
  unfold gram
  rw [intervalIntegral.integral_finset_sum fun i _ => hrow i]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finset_sum fun j _ => hi i j]
  simp only [intervalIntegral.integral_const_mul]

private theorem gram_sq {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (c : ι → ℝ) :
    gram (fun i j r => f i r * f j r) c = fun r => (trialMap f c r)^2 := by
  ext r
  simp only [gram,trialMap,LinearMap.coe_mk,AddHom.coe_mk,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem gram_form {ι : Type*} [Fintype ι] (f g : ι → ℝ → ℝ) (V : ℝ → ℝ) (c : ι → ℝ) :
    gram (fun i j r => g i r*g j r+V r*(f i r*f j r)) c =
      fun r => (trialMap g c r)^2+V r*(trialMap f c r)^2 := by
  ext r
  rw [← congrFun (gram_sq g c) r,← congrFun (gram_sq f c) r]
  simp only [gram,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- On the first n+1 orthonormal modes the true weak eigenfunction
equations for the quadratic form with any nonnegative potential yield
the sharp lower bound. The energies may have multiplicities. -/
theorem dirichlet_eigenfamily_energy_lower (n : ℕ) (V : ℝ → ℝ)
    (f g : Fin (n+1) → ℝ → ℝ) (E : Fin (n+1) → ℝ)
    (hV : ∀ r ∈ Icc 0 1,0 ≤ V r) (hE : ∀ i,E i ≤ E (Fin.last n))
    (hC : ∀ i,ContinuousOn (f i) (Icc 0 1)) (hu : ∀ i x,x ∈ Ioo 0 1 → HasDerivAt (f i) (g i x) x)
    (h₀ : ∀ i,f i 0=0) (h₁ : ∀ i,f i 1=0)
    (hg : ∀ i,IntervalIntegrable (g i) volume 0 1)
    (hgg : ∀ i j,IntervalIntegrable (fun r => g i r*g j r) volume 0 1)
    (hfull : ∀ i j,IntervalIntegrable (fun r => g i r*g j r+V r*(f i r*f j r)) volume 0 1)
    (horth : ∀ i j,(∫ r in (0:ℝ)..1,f i r*f j r)=if i=j then 1 else 0)
    (hweak : ∀ i j,(∫ r in (0:ℝ)..1,g i r*g j r+V r*(f i r*f j r))=if i=j then E i else 0) :
    π^2*((n:ℝ)+1)^2 ≤ E (Fin.last n) := by
  classical
  have hmass (c : Fin (n+1) → ℝ) : (∫ r in (0:ℝ)..1,(trialMap f c r)^2)=∑ i,c i^2 := by
    have h := (integral_gram (fun i j r => f i r*f j r) c (fun i j => ((hC i).mul (hC j)).intervalIntegrable_of_Icc zero_le_one)).2
    rw [gram_sq] at h
    simpa [horth,pow_two] using h
  have hkin (c : Fin (n+1) → ℝ) := (integral_gram (fun i j r => g i r*g j r) c hgg).1
  have hRay (c : Fin (n+1) → ℝ) : (∫ r in (0:ℝ)..1,(trialMap g c r)^2) ≤ E (Fin.last n)*(∫ r in (0:ℝ)..1,(trialMap f c r)^2) := by
    have H := integral_gram (fun i j r => g i r*g j r+V r*(f i r*f j r)) c hfull
    rw [gram_form] at H
    have hk := hkin c
    rw [gram_sq] at hk
    calc
      _ ≤ ∫ r in (0:ℝ)..1,(trialMap g c r)^2+V r*(trialMap f c r)^2 :=
        intervalIntegral.integral_mono_on zero_le_one hk H.1 (fun r hr => le_add_of_nonneg_right (mul_nonneg (hV r hr) (sq_nonneg _)))
      _ = ∑ i,c i^2*E i := by simpa [hweak,pow_two] using H.2
      _ ≤ _ := by
        rw [hmass,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        simpa only [mul_comm (E _)] using mul_le_mul_of_nonneg_left (hE i) (sq_nonneg (c i))
  apply dirichlet_mesh_eigenvalue_lower n (trialMap f) (fun c => trialMap g c) _
  · intro c
    exact continuousOn_finset_sum Finset.univ fun i _ => (continuousOn_const (c := c i)).mul (hC i)
  · intro c x hx
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hu i x hx).const_mul (c i)
  · intro c; simp [trialMap,h₀]
  · intro c; simp [trialMap,h₁]
  · intro c; exact interval_sum (fun i r => c i*g i r) fun i => (hg i).const_mul _
  · intro c; simpa only [gram_sq] using hkin c
  · intro c hc
    rw [hmass]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hc
    exact Finset.sum_pos' (fun j _ => sq_nonneg (c j)) ⟨i,Finset.mem_univ i,sq_pos_of_ne_zero hi⟩
  · exact hRay

end UV.CollarEigenmode
