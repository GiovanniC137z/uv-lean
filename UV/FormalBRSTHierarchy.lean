import UV.FormalBRST
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! The loop hierarchy is the actual Cauchy convolution of a bilinear
antibracket on a genuine formal loop series. Exponential degree is not used
as a surrogate for loop degree. -/

noncomputable section
open scoped BigOperators

namespace UV

variable {A : Type*} [Ring A] [Algebra ℚ A]

def formalBilinear (bracket : A →ₗ[ℚ] A →ₗ[ℚ] A)
    (F G : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => ∑ p ∈ Finset.antidiagonal n,
    bracket (PowerSeries.coeff p.1 F) (PowerSeries.coeff p.2 G))

@[simp] theorem formalBilinear_coeff (bracket : A →ₗ[ℚ] A →ₗ[ℚ] A)
    (F G : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (formalBilinear bracket F G) =
      ∑ p ∈ Finset.antidiagonal n,
        bracket (PowerSeries.coeff p.1 F) (PowerSeries.coeff p.2 G) := by
  simp [formalBilinear]

theorem formalBilinear_coeff_range (bracket : A →ₗ[ℚ] A →ₗ[ℚ] A)
    (F G : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (formalBilinear bracket F G) =
      ∑ k ∈ Finset.range (n+1), bracket (PowerSeries.coeff k F) (PowerSeries.coeff (n-k) G) := by
  rw [formalBilinear_coeff]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ n

def formalMasterSeries (bracket : A →ₗ[ℚ] A →ₗ[ℚ] A)
    (Γ : PowerSeries A) : PowerSeries A := (1/2 : ℚ) • formalBilinear bracket Γ Γ

theorem formal_master_iff (bracket : A →ₗ[ℚ] A →ₗ[ℚ] A) (Γ : PowerSeries A) :
    formalMasterSeries bracket Γ = 0 ↔
      ∀ n, (1/2 : ℚ) • ∑ k ∈ Finset.range (n+1),
        bracket (PowerSeries.coeff k Γ) (PowerSeries.coeff (n-k) Γ) = 0 := by
  rw [← PowerSeries.forall_coeff_eq_zero]
  simp only [formalMasterSeries, PowerSeries.coeff_smul, formalBilinear_coeff_range]

theorem formal_master_convolution_zero {bracket : A →ₗ[ℚ] A →ₗ[ℚ] A}
    {Γ : PowerSeries A} (hmaster : formalMasterSeries bracket Γ = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), bracket (PowerSeries.coeff k Γ) (PowerSeries.coeff (n-k) Γ) = 0 := by
  have h := (formal_master_iff bracket Γ).mp hmaster n
  have hh := congrArg (fun x : A => (2 : ℚ) • x) h
  simpa only [smul_smul, show (2:ℚ)*(1/2)=1 by norm_num, one_smul, smul_zero] using hh

/-- The tree coefficient satisfies the classical master equation as the
actual zeroth coefficient of the formal quantum master equation. -/
theorem formal_master_tree {bracket : A →ₗ[ℚ] A →ₗ[ℚ] A}
    {Γ : PowerSeries A} {S : A} (hmaster : formalMasterSeries bracket Γ = 0)
    (htree : PowerSeries.coeff 0 Γ = S) : bracket S S = 0 := by
  simpa [htree] using formal_master_convolution_zero hmaster 0

/-- The exact source loop hierarchy, with ℓ=n+1. Symmetry is required only
on the actual even effective-action coefficients; it is a structural
antibracket law, not any order of the desired hierarchy. -/
theorem formal_loop_slavnov_taylor {bracket : A →ₗ[ℚ] A →ₗ[ℚ] A}
    {Γ : PowerSeries A} {S : A} (hmaster : formalMasterSeries bracket Γ = 0)
    (htree : PowerSeries.coeff 0 Γ = S)
    (hsymm : ∀ k l, bracket (PowerSeries.coeff k Γ) (PowerSeries.coeff l Γ) =
      bracket (PowerSeries.coeff l Γ) (PowerSeries.coeff k Γ)) (n : ℕ) :
    bracket S (PowerSeries.coeff (n+1) Γ) =
      -(1/2 : ℚ) • ∑ k ∈ Finset.range n,
        bracket (PowerSeries.coeff (k+1) Γ) (PowerSeries.coeff (n-k) Γ) := by
  have h := formal_master_convolution_zero hmaster (n+1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
  simp only [Nat.sub_self, Nat.sub_zero, Nat.add_sub_add_right] at h
  rw [hsymm (n+1) 0] at h
  have hh : (2 : ℚ) • bracket (PowerSeries.coeff 0 Γ) (PowerSeries.coeff (n+1) Γ) =
      -(∑ k ∈ Finset.range n,
        bracket (PowerSeries.coeff (k+1) Γ) (PowerSeries.coeff (n-k) Γ)) := by
    rw [two_smul ℚ]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_assoc, add_comm, add_left_comm] using h)
  have hhalf := congrArg (fun x : A => (1/2 : ℚ) • x) hh
  simpa only [smul_smul, show (1/2:ℚ)*2=1 by norm_num, one_smul,
    htree, smul_neg, neg_smul] using hhalf

end UV
