import UV.ContinueFourierHoppingSpatial
import UV.ContinueTwoBandSpectralLoop

/-! The complete translated charged four-momentum word keeps one independent
frequency and three-momentum per hopping loop. The number N+2 counts the
actual Gaussian hops and carrier intervals, at least two in a closed word. -/

noncomputable section

open MeasureTheory

namespace UV.SectorPlane

structure HoppingFourierLoop (N : ℕ) where
  time : Fin (N+2) → HoppingCarrierSlot
  space : Fin (N+2) → HoppingSpatialSlot

def HoppingFourierLoop.valid {N : ℕ} (L : HoppingFourierLoop N) (m : ℝ) (M : ℕ) : Prop :=
  (∀ j, |(L.time j).signedMass|=m) ∧ (∑ j, (L.time j).degree) ≤ M ∧ (∑ j, (L.space j).degree) ≤ M

def HoppingFourierLoop.weight {N : ℕ} (L : HoppingFourierLoop N) : ℝ := ∏ j, (L.time j).weight

theorem HoppingFourierLoop.weight_nonneg {N : ℕ} (L : HoppingFourierLoop N) : 0 ≤ L.weight :=
  Finset.prod_nonneg fun _ _ => hopping_weight_nonneg _

def HoppingFourierLoop.word {N : ℕ} (L : HoppingFourierLoop N) (g σ : ℝ) (x : ℝ × Spatial) : ℂ :=
  (g : ℂ)^(N+2) * ((∏ j, (L.time j).value x.1) * ((∏ j, (L.space j).value σ x.2 : ℝ) : ℂ))

def hoppingFourierBudget (m g : ℝ) {σ : ℝ} (hσ : 0 < σ) (M : ℕ) : ℝ :=
  |g|^2 * (Real.pi/m) * (hoppingOrderConstant m M)^(M+2) * (hoppingSpatialBudget hσ M)^(M+1)

theorem hopping_fourier_budget_nonneg {m σ : ℝ} (hm : 0<m) (g : ℝ) (hσ : 0<σ) (M : ℕ) :
    0 ≤ hoppingFourierBudget m g hσ M := by
  have h₁ := zero_le_one.trans (hopping_order_constant_one m M)
  have h₂ := zero_le_one.trans (hopping_spatial_budget_one hσ M)
  unfold hoppingFourierBudget
  positivity

theorem HoppingFourierLoop.carrier_cost {N : ℕ} (L : HoppingFourierLoop N) {m : ℝ} (hm : 0<m)
    {M : ℕ} (hL : L.valid m M) :
    let F := fun x : ℝ => ∏ j, (L.time j).value x
    Integrable F ∧ (∫ x, ‖F x‖) ≤ (Real.pi/m)*m⁻¹^N*(hoppingOrderConstant m M)^(M+2)*L.weight := by
  intro G
  let T := List.ofFn (fun j : Fin N => L.time j.succ.succ)
  let F := fun x : ℝ => ∏ j, (L.time j).value x
  have hT : ∀ y ∈ T, |HoppingCarrierSlot.signedMass y|=m := by
    simp only [T,List.mem_ofFn]
    rintro y ⟨j,rfl⟩
    exact hL.1 _
  have ht := hL.2.1
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at ht
  have htD : (L.time 0).degree + (L.time 1).degree + hoppingLoopDegree T ≤ M := by
    simpa only [T,hoppingLoopDegree,List.map_ofFn,List.sum_ofFn,Function.comp_def,add_assoc] using ht
  have hF := hopping_charged_loop_frequency hm (L.time 0) (L.time 1) T (hL.1 0) (hL.1 1) hT htD
  have eqF : hoppingLoopValue (L.time 0::L.time 1::T) = F := by
    funext x
    simp only [F,Fin.prod_univ_succ,hoppingLoopValue,T,List.map_cons,List.prod_cons,List.map_ofFn,
      Function.comp_def,List.prod_ofFn]
    rfl
  have eqW : hoppingLoopWeight (L.time 0::L.time 1::T) = L.weight := by
    simp only [weight,Fin.prod_univ_succ,hoppingLoopWeight,T,List.map_cons,List.prod_cons,List.map_ofFn,
      Function.comp_def,List.prod_ofFn]
    rfl
  rw [eqF,eqW,show T.length=N by simp [T]] at hF
  exact hF

/-- One temporal Lebesgue variable and a spatial momentum variable with
any measure having a finite absolute integral for the translated heat word. -/
theorem HoppingFourierLoop.cost_for {N : ℕ} (L : HoppingFourierLoop N) {m : ℝ} (hm : 0<m)
    (g σ : ℝ) {M : ℕ} (hL : L.valid m M) {S : Type*} [MeasurableSpace S] (μ : Measure S) [SFinite μ]
    (k : S → Spatial) (D : ℝ)
    (hH : let H := fun z => ∏ j, (L.space j).value σ (k z)
      Integrable H μ ∧ (∫ z, ‖H z‖ ∂μ) ≤ D) :
    let F := fun x : ℝ × S => L.word g σ (x.1, k x.2)
    Integrable F (volume.prod μ) ∧ (∫ x, ‖F x‖ ∂volume.prod μ) ≤
      ((|g|^2*(Real.pi/m)*(hoppingOrderConstant m M)^(M+2)*D) * (|g|/m)^N)*L.weight := by
  intro G
  let F := fun x : ℝ => ∏ j, (L.time j).value x
  let H := fun z => ∏ j, (L.space j).value σ (k z)
  have hF := L.carrier_cost hm hL
  have hi : Integrable G (volume.prod μ) := (hF.1.mul_prod hH.1.ofReal).const_mul ((g:ℂ)^(N+2))
  refine ⟨hi,?_⟩
  have he (x : ℝ × S) : ‖G x‖ = |g|^(N+2)*(‖F x.1‖*‖H x.2‖) := by
    simp only [G,word,F,H,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun x => ‖F x‖) (fun z => ‖H z‖)]
  have hFpos := (integral_nonneg fun x => norm_nonneg (F x)).trans hF.2
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hF.2 hH.2 (integral_nonneg fun z => norm_nonneg _) hFpos)
    (pow_nonneg (abs_nonneg _) _)).trans_eq
  rw [div_pow,pow_add]
  ring

/-- All n+2 spatial and temporal factors at their actual shifted momenta,
with |g| for each hop. The fixed-order constant is independent of n. -/
theorem HoppingFourierLoop.absolute_cost {N : ℕ} (L : HoppingFourierLoop N) {m σ : ℝ} (hm : 0<m) (hσ : 0<σ)
    (g : ℝ) {M : ℕ} (hL : L.valid m M) :
    Integrable (L.word g σ) ∧
    (∫ x, ‖L.word g σ x‖) ≤ (hoppingFourierBudget m g hσ M * (|g|/m)^N)*L.weight := by
  let S := List.ofFn (fun j : Fin (N+1) => L.space j.succ)
  have hs := hL.2.2
  rw [Fin.sum_univ_succ] at hs
  have hsD : (L.space 0).degree + hoppingSpatialDegree S ≤ M := by
    simpa only [S,hoppingSpatialDegree,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hs
  have hH := hopping_charged_loop_spatial hσ (L.space 0) S hsD
  have eqH : hoppingSpatialProduct σ (L.space 0::S) = fun k => ∏ j, (L.space j).value σ k := by
    funext k
    simp only [Fin.prod_univ_succ,hoppingSpatialProduct,S,List.map_cons,List.prod_cons,List.map_ofFn,
      Function.comp_def,List.prod_ofFn]
  rw [eqH] at hH
  exact L.cost_for hm g σ hL volume id _ hH

end UV.SectorPlane
