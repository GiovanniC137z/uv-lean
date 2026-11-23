import UV.ContinueAngularMassCompact

/-! Attainment and the eigenvector equation for the dimensionless
zonal Jacobi operator on the unit-speed sector plane. -/

noncomputable section
open Finset Set Filter
open scoped Topology
namespace UV

def angularJacobiRow (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => angularJacobiEdge 0*z 1
  | j+1 => angularJacobiEdge j*z j+angularJacobiEdge (j+1)*z (j+2)

private theorem ball_energy {z : ℕ → ℝ} (hz : z ∈ angularUnitBall) :
    Summable (fun j => (z j)^2) ∧ (∑' j, (z j)^2) ≤ 1 := by
  have h : ∀ n, (∑ j ∈ range n, (z j)^2) ≤ 1 := by
    intro n
    cases n with
    | zero => simp
    | succ n => exact hz n
  have hs := summable_of_sum_range_le (fun j => sq_nonneg (z j)) h
  exact ⟨hs,le_of_tendsto' hs.hasSum.tendsto_sum_nat h⟩

private theorem variational_bound {z : ℕ → ℝ}
    (hmax : ∀ y ∈ angularUnitBall, angularInfiniteForm y ≤ angularInfiniteForm z)
    (y : ℕ → ℝ) (hy : Summable (fun j => (y j)^2)) :
    angularInfiniteForm y ≤ angularInfiniteForm z*(∑' j,(y j)^2) := by
  let S := ∑' j,(y j)^2
  have hn (n) : angularFiniteNorm n y ≤ S :=
    hy.sum_le_tsum _ fun j _ => sq_nonneg _
  have hS : 0 ≤ S := tsum_nonneg (fun _ => sq_nonneg _)
  by_cases hpos : 0 < S
  · let c := (Real.sqrt S)⁻¹
    have hC : c^2 * S = 1 := by
      dsimp only [c]; rw [inv_pow, Real.sq_sqrt hS, inv_mul_cancel₀ hpos.ne']
    have he : (fun j => c*y j) ∈ angularUnitBall := by
      intro n
      unfold angularFiniteNorm
      simp_rw [mul_pow, ← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (hn n) (sq_nonneg c)).trans_eq hC
    have hf := hmax _ he
    have hscale : angularInfiniteForm (fun j => c*y j) = c^2*angularInfiniteForm y := by
      unfold angularInfiniteForm
      rw [←tsum_mul_left]
      apply tsum_congr
      intro j; ring
    rw [hscale] at hf
    have h := mul_le_mul_of_nonneg_right hf hS
    change _ ≤ angularInfiniteForm z*S
    calc _ = (c^2*angularInfiniteForm y)*S := by rw [mul_right_comm,hC,one_mul]
         _ ≤ _ := h
  · have he : y = 0 := by
      funext j
      have hj : (y j)^2 ≤ S := hy.le_tsum j (fun _ _ => sq_nonneg _)
      change y j=0
      nlinarith
    subst y
    simp [angularInfiniteForm]

private def cutState (n : ℕ) (y : ℕ → ℝ) (j : ℕ) := if j ≤ n then y j else 0

private theorem cut_energy (n : ℕ) (y : ℕ → ℝ) :
    HasSum (fun j => (cutState n y j)^2) (angularFiniteNorm n y) := by
  have h : HasSum (fun j => (cutState n y j)^2) (∑ j ∈ range (n+1), (cutState n y j)^2) := hasSum_sum_of_ne_finset_zero (s := range (n+1)) (f := fun j => (cutState n y j)^2)
    (fun j hj => by simp [cutState, show ¬ j ≤ n by simpa [Nat.lt_succ_iff] using hj])
  convert h using 1
  unfold angularFiniteNorm
  exact Finset.sum_congr rfl fun j hj => by simp [cutState,Nat.le_of_lt_succ (mem_range.mp hj)]

private theorem cut_form (n : ℕ) (y : ℕ → ℝ) :
    angularInfiniteForm (cutState n y) = angularFiniteForm n y := by
  unfold angularInfiniteForm angularFiniteForm
  rw [tsum_eq_sum (s := range n)]
  · apply Finset.sum_congr rfl
    intro j hj
    have h := mem_range.mp hj
    simp [cutState,h.le,Nat.succ_le_of_lt h]
  · intro j hj
    have h : ¬ j+1 ≤ n := by simp at hj; omega
    simp [cutState,h]

private theorem maximum_eq_edge {z : ℕ → ℝ} (hz : z ∈ angularUnitBall)
    (hmax : ∀ y ∈ angularUnitBall, angularInfiniteForm y ≤ angularInfiniteForm z) :
    angularInfiniteForm z = angularZonalEdge ∧ (∑' j,(z j)^2)=1 := by
  let M := angularInfiniteForm z
  let R := {r : ℝ | ∃ (n : ℕ) (v : ℕ → ℝ), 0 < angularFiniteNorm n v ∧ r=angularFiniteForm n v/angularFiniteNorm n v}
  have hnon : (0:ℝ)∈R := by
    refine ⟨0,fun _ => 1,by norm_num [angularFiniteNorm],?_⟩
    simp [angularFiniteForm]
  have hfinite (x : ℝ) (hx : x∈R) : x ≤ M := by
    obtain ⟨n,v,hv,rfl⟩ := hx
    have h := variational_bound hmax (cutState n v) (cut_energy n v).summable
    rw [cut_form,(cut_energy n v).tsum_eq] at h
    exact (div_le_iff₀ hv).mpr h
  have hsup : angularZonalEdge ≤ M := csSup_le ⟨_,hnon⟩ hfinite
  have he : 0 < angularZonalEdge := by
    have h := angular_zonal_mass_bracket.1
    by_contra! h'
    exact (not_lt_of_ge (div_nonpos_of_nonneg_of_nonpos zero_le_one h')) (lt_trans (by norm_num : (0:ℝ)<3.78984) h)
  have hM := he.trans_le hsup
  obtain ⟨hs,h1⟩ := ball_energy hz
  have hb n : angularFiniteForm n z ≤ angularZonalEdge*angularFiniteNorm n z := by
    have hn := Finset.sum_nonneg (s := range (n+1)) (fun i _ => sq_nonneg (z i))
    change 0 ≤ angularFiniteNorm n z at hn
    by_cases h : 0 < angularFiniteNorm n z
    · exact (div_le_iff₀ h).mp (le_csSup ⟨_,hfinite⟩ (show _∈R from ⟨n,z,h,rfl⟩))
    · have hz' := le_antisymm (le_of_not_gt h) hn
      simpa [hz'] using angular_finite_rayleigh_upper n z
  have hp := le_of_tendsto_of_tendsto' (angular_infinite_form_summable hs).hasSum.tendsto_sum_nat
    (tendsto_const_nhds.mul (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))) hb
  change M ≤ angularZonalEdge * (∑' j,(z j)^2) at hp
  have hle := hp.trans ((mul_le_mul_of_nonneg_left h1 he.le).trans_eq (mul_one _))
  have hEq := hle.antisymm hsup
  exact ⟨hEq,h1.antisymm (by rw [hEq] at hp; nlinarith)⟩

private def bumpState (z : ℕ → ℝ) (j : ℕ) (t : ℝ) (k : ℕ) :=
  if k=j then z k+t else z k

private theorem bump_norm {z : ℕ → ℝ} (hz : Summable (fun k => (z k)^2)) (j : ℕ) (t : ℝ) :
    HasSum (fun k => (bumpState z j t k)^2) ((∑' k, (z k)^2)+(2*z j*t+t^2)) := by
  convert hz.hasSum.add (hasSum_ite_eq j (2*z j*t+t^2)) using 1
  funext k
  by_cases h : k=j <;> simp [bumpState,h]
  ring

private theorem bump_form {z : ℕ → ℝ} (hz : Summable (fun k => (z k)^2)) (j : ℕ) (t : ℝ) :
    angularInfiniteForm (bumpState z j t) = angularInfiniteForm z+2*t*angularJacobiRow z j := by
  have h := (angular_infinite_form_summable hz).hasSum
  cases j with
  | zero =>
    let a := 2*t*angularJacobiRow z 0
    have hh := h.add (hasSum_ite_eq 0 a)
    apply HasSum.tsum_eq
    convert hh using 1
    funext k
    by_cases hk : k=0 <;> simp [bumpState,hk,a,angularJacobiRow]
    ring
  | succ j =>
    let a := 2*t*angularJacobiEdge j*z j
    let b := 2*t*angularJacobiEdge (j+1)*z (j+2)
    have hh := (h.add (hasSum_ite_eq j a)).add (hasSum_ite_eq (j+1) b)
    apply HasSum.tsum_eq
    convert hh using 1
    · funext k
      by_cases h₀ : k = j
      · subst k; simp [bumpState,a,b]; ring
      by_cases h₁ : k = j+1
      · subst k; simp [bumpState,a,b]; ring
      · simp [bumpState,h₀,h₁]
    · change angularInfiniteForm z+2*t*angularJacobiRow z (j+1)=angularInfiniteForm z+a+b
      dsimp only [angularJacobiRow,a,b]; ring

/-- Coordinate variation of the actual maximizing state yields every
Jacobi row, including the one-sided zeroth row. -/
theorem angular_maximum_eigenvector :
    ∃ z : ℕ → ℝ, Summable (fun j => (z j)^2) ∧ (∑' j, (z j)^2)=1 ∧
      z 0 ≠ 0 ∧ 0 < angularZonalEdge ∧
      (∀ j, angularJacobiRow z j = angularZonalEdge*z j) ∧
      (∀ y : ℕ → ℝ, Summable (fun j => (y j)^2) →
          angularInfiniteForm y ≤ angularZonalEdge*(∑' j,(y j)^2)) ∧
      3.78984 < 1/angularZonalEdge ∧ 1/angularZonalEdge < 3.78985 := by
  obtain ⟨z,hz,hmax⟩ := angular_form_has_maximum
  obtain ⟨hval,hn⟩ := maximum_eq_edge hz hmax
  have hpos : 0 < angularZonalEdge := by
    by_contra! h
    have hb := angular_zonal_mass_bracket.1
    linarith [div_nonpos_of_nonneg_of_nonpos zero_le_one h]
  have hS := (ball_energy hz).1
  have hbound (y : ℕ → ℝ) (hs : Summable (fun j => (y j)^2)) :
      angularInfiniteForm y ≤ angularZonalEdge*(∑' j,(y j)^2) := by
    rw [←hval]; exact variational_bound hmax y hs
  have hrow j : angularJacobiRow z j = angularZonalEdge*z j := by
    let s := angularJacobiRow z j-angularZonalEdge*z j
    let t := s/angularZonalEdge
    have ht : t*angularZonalEdge=s := div_mul_cancel₀ s hpos.ne'
    have he := hbound _ (bump_norm hS j t).summable
    rw [bump_form hS,(bump_norm hS j t).tsum_eq,hn,hval] at he
    have hts : t*s ≤ 0 := by
      dsimp only [s] at ht ⊢
      nlinarith only [he,congrArg (fun u : ℝ => t*u) ht]
    have hss := mul_nonpos_of_nonpos_of_nonneg hts hpos.le
    have hz' : s*s ≤ 0 := by nlinarith only [hss,congrArg (fun u : ℝ => u*s) ht]
    have hz'' : s=0 := by nlinarith [sq_nonneg s]
    exact sub_eq_zero.mp hz''
  have hcoord : z 0 ≠ 0 := by
    intro hz₀
    have hz₁ : z 1=0 := by
      have h := hrow 0
      rw [angularJacobiRow,hz₀,mul_zero] at h
      rcases mul_eq_zero.mp h with he|h₁
      · norm_num [angularJacobiEdge] at he
      · exact h₁
    have hi (j : ℕ) : z j=0 ∧ z (j+1)=0 := by
      induction j with
      | zero => exact ⟨hz₀,hz₁⟩
      | succ j ih =>
        refine ⟨ih.2,?_⟩
        have h := hrow (j+1)
        rw [angularJacobiRow,ih.1,ih.2,mul_zero,mul_zero,zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left (by unfold angularJacobiEdge; positivity)
    have hzero : z=0 := funext fun j => (hi j).1
    simp [hzero] at hn
  exact ⟨z,hS,hn,hcoord,hpos,hrow,hbound,angular_zonal_mass_bracket⟩

/-- The actual infinite quadratic form is the row-by-row Hilbert pairing
with the Jacobi action, with absolute convergence at square-summable input. -/
theorem angular_jacobi_pairing {z : ℕ → ℝ} (hz : Summable (fun k => (z k)^2)) :
    HasSum (fun j => z j*angularJacobiRow z j) (angularInfiniteForm z) := by
  let u (j : ℕ) := angularJacobiEdge j*z j*z (j+1)
  have hs : Summable u := by
    convert (angular_infinite_form_summable hz).mul_left (1/2:ℝ) using 1
    funext j; dsimp [u]; ring
  let p : ℕ → ℝ := fun j => match j with | 0 => 0 | n+1 => u n
  have hp : Summable p := (summable_nat_add_iff 1).mp hs
  have heq : (∑' j, p j) = ∑' j, u j := by
    rw [hp.tsum_eq_zero_add]; exact zero_add _
  have hh := hp.hasSum.add hs.hasSum
  convert hh using 1
  · funext j
    cases j with
    | zero => dsimp [p,u,angularJacobiRow]; ring
    | succ j => dsimp [p,u,angularJacobiRow]; ring
  · rw [heq,←two_mul,←tsum_mul_left]
    apply tsum_congr
    intro j; dsimp only [u]; ring

/-- Every eigenvalue on the real zonal ℓ² space is bounded above by the
attained eigenvalue. The endpoint at coordinate zero sees that eigenvalue. -/
theorem angular_largest_eigenvalue :
    (∃ z : ℕ → ℝ, Summable (fun j => (z j)^2) ∧ (∑' j, (z j)^2)=1 ∧ z 0 ≠ 0 ∧
       ∀ j, angularJacobiRow z j=angularZonalEdge*z j) ∧
      (∀ (r : ℝ) (y : ℕ → ℝ), y ≠ 0 → Summable (fun j => (y j)^2) →
        (∀ j, angularJacobiRow y j=r*y j) → r ≤ angularZonalEdge) ∧
      3.78984 < 1/angularZonalEdge ∧ 1/angularZonalEdge < 3.78985 := by
  obtain ⟨z,hs,hn,hz,_,hrow,hbound,hbr⟩ := angular_maximum_eigenvector
  refine ⟨⟨z,hs,hn,hz,hrow⟩,?_,hbr⟩
  intro r y hy hys hry
  have hsum : angularInfiniteForm y = r*(∑' j,(y j)^2) := by
    rw [←(angular_jacobi_pairing hys).tsum_eq, ←tsum_mul_left]
    exact tsum_congr fun j => by rw [hry]; ring
  have hi := hbound y hys
  rw [hsum] at hi
  have hn' : 0 < ∑' j,(y j)^2 := by
    obtain ⟨i,hi⟩ : ∃ i, y i ≠ 0 := by
      contrapose! hy
      exact funext hy
    exact (sq_pos_of_ne_zero hi).trans_le (hys.le_tsum i fun _ _ => sq_nonneg _)
  exact le_of_mul_le_mul_right hi hn'

/-- Complexification of the same zero-diagonal real Jacobi matrix. -/
def angularComplexJacobiRow (z : ℕ → ℂ) : ℕ → ℂ
  | 0 => (angularJacobiEdge 0:ℂ)*z 1
  | j+1 => (angularJacobiEdge j:ℂ)*z j + (angularJacobiEdge (j+1):ℂ)*z (j+2)

private theorem angular_edge_pos (j : ℕ) : 0 < angularJacobiEdge j := by
  unfold angularJacobiEdge; positivity

private theorem angular_row_norm_upper (z : ℕ → ℂ) (j : ℕ) :
    ‖angularComplexJacobiRow z j‖ ≤ angularJacobiRow (fun k => ‖z k‖) j := by
  cases j with
  | zero => simp [angularComplexJacobiRow,angularJacobiRow,Real.norm_of_nonneg (angular_edge_pos _).le]
  | succ j =>
    apply (norm_add_le _ _).trans_eq
    simp [angularJacobiRow,Real.norm_of_nonneg (angular_edge_pos _).le]

/-- Every complex square-summable eigenvector has spectral modulus no
larger than the actual positive maximum. Positivity of the true Jacobi
edges controls both real and complex phases. -/
theorem angular_complex_eigenvalue_bound (r : ℂ) {z : ℕ → ℂ}
    (hz : z ≠ 0) (hs : Summable (fun j => ‖z j‖^2))
    (he : ∀ j, angularComplexJacobiRow z j=r*z j) : ‖r‖ ≤ angularZonalEdge := by
  let y (j : ℕ) := ‖z j‖
  have h (j : ℕ) : ‖r‖*y j ≤ angularJacobiRow y j := by
    have h := angular_row_norm_upper z j
    rwa [he,norm_mul] at h
  obtain ⟨_,_,_,_,_,_,hbound,_⟩ := angular_maximum_eigenvector
  have hcmp := hasSum_le (f := fun j => ‖r‖*(y j)^2) (g := fun j => y j*angularJacobiRow y j)
    (fun j => by have hh := mul_le_mul_of_nonneg_left (h j) (norm_nonneg (z j)); nlinarith only [hh])
    (hs.hasSum.mul_left ‖r‖) (angular_jacobi_pairing (z:=y) hs)
  have hn : 0 < ∑' j,(y j)^2 := by
    obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
      contrapose! hz
      exact funext hz
    exact (sq_pos_of_pos (norm_pos_iff.mpr hi)).trans_le (hs.le_tsum i fun _ _ => sq_nonneg _)
  exact le_of_mul_le_mul_right (hcmp.trans (hbound y hs)) hn

/-- Positive off-diagonals make every eigensolution uniquely determined
by its constant endpoint, with no square-summability assumption needed
for the recursion. -/
theorem angular_complex_eigenvector_unique (r : ℂ) {u v : ℕ → ℂ}
    (hu : ∀ j, angularComplexJacobiRow u j = r*u j)
    (hv : ∀ j, angularComplexJacobiRow v j = r*v j) (h₀ : u 0=v 0) : u=v := by
  have edge (j : ℕ) : (angularJacobiEdge j : ℂ) ≠ 0 := by exact_mod_cast (angular_edge_pos j).ne'
  have hh (j : ℕ) : u j = v j ∧ u (j+1) = v (j+1) := by
    induction j with
    | zero =>
      refine ⟨h₀,mul_left_cancel₀ (edge 0) ?_⟩
      exact (hu 0).trans ((congrArg (fun x : ℂ => r*x) h₀).trans (hv 0).symm)
    | succ j ih =>
      refine ⟨ih.2,mul_left_cancel₀ (edge (j+1)) ?_⟩
      have h := (hu (j+1)).trans ((congrArg (fun x : ℂ => r*x) ih.2).trans (hv (j+1)).symm)
      simp only [angularComplexJacobiRow,ih.1,add_right_inj] at h
      exact h
  exact funext fun j => (hh j).1

theorem angular_complex_eigenspace_line (r : ℂ) {u v : ℕ → ℂ}
    (hu : ∀ j, angularComplexJacobiRow u j = r*u j)
    (hv : ∀ j, angularComplexJacobiRow v j = r*v j) (h₀ : u 0 ≠ 0) :
    v = fun j => (v 0/u 0)*u j := by
  apply angular_complex_eigenvector_unique r hv
  · intro j
    have hh := hu j
    cases j <;> dsimp only [angularComplexJacobiRow] at hh ⊢ <;> linear_combination (norm:=ring) (v 0/u 0)*hh
  · exact (div_mul_cancel₀ _ h₀).symm

end UV
