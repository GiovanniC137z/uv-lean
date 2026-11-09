import UV.ContinuumLegendre

/-! The continuum Ward contraction is an actual integral of the canonical
graded derivatives. Its derivative laws are proved from integral calculus. -/

noncomputable section
open MeasureTheory

namespace UV

variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedSpace ℝ B] [Algebra ℚ B] [CompleteSpace B]
  [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
theorem continuumJacobianIntegral_homogeneous (μ : Measure X)
    {σ : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σ (ε x))
    {δ : Bool} (v : X → B)
    (hv : ∀ x, σ.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (P : B →L[ℝ] B) (hP : ∀ f, P f = σ.parity f)
    (hI : ∀ f, Integrable (fun x => v x * (dcoord x).d f) μ) (f : B) :
    continuumJacobianIntegral μ dcoord (AlgHom.id ℚ B) v (σ.parity f) =
      koszulSign δ • σ.parity (continuumJacobianIntegral μ dcoord (AlgHom.id ℚ B) v f) := by
  have he (x : X) : v x * (dcoord x).d (σ.parity f) =
      koszulSign δ • σ.parity (v x * (dcoord x).d f) := by
    rw [(dcoord x).homogeneous, map_mul, hv x]
    have hsign (q p : Bool) (a b : B) : a * koszulSign p • b =
        koszulSign q • (koszulSign (Bool.xor q p) • a * b) := by
      cases q <;> cases p <;> simp [koszulSign]
    exact hsign δ (ε x) _ _
  unfold continuumJacobianIntegral
  simp only [AlgHom.id_apply]
  simp_rw [he]
  have hcomm : (∫ x, σ.parity (v x * (dcoord x).d f) ∂μ) =
      σ.parity (∫ x, v x * (dcoord x).d f ∂μ) := by
    simpa only [hP] using P.integral_comp_comm (hI f)
  cases δ
  · simpa only [koszulSign, Bool.false_eq_true, ite_false, one_smul] using hcomm
  · simpa only [koszulSign, ite_true, neg_one_smul, integral_neg] using congrArg Neg.neg hcomm

/-- The integral operator is ℚ-linear, and its graded product/parity laws
follow from the actual continuum contractions. In particular it may be used
as the Ward derivative in a coefficientwise formal perturbation series. -/
def continuumGradedDerivative (μ : Measure X)
    {σ : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σ (ε x))
    (hB : SupercommutativeGrading σ) {δ : Bool} (v : X → B)
    (hv : ∀ x, σ.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (P : B →L[ℝ] B) (hP : ∀ f, P f = σ.parity f)
    (hI : ∀ f, Integrable (fun x => v x * (dcoord x).d f) μ) : GradedDerivative σ δ where
  d :=
    { toFun := continuumJacobianIntegral μ dcoord (AlgHom.id ℚ B) v
      map_add' f g := continuumJacobianIntegral_add μ dcoord (AlgHom.id ℚ B) v f g (hI f) (hI g)
      map_smul' r f := by
        have hm := continuumJacobianIntegral_leibniz μ dcoord hB (AlgHom.id ℚ B)
          (fun _ => rfl) v hv (algebraMap ℚ B r) f (hI _) (hI _)
        simpa only [AlgHom.id_apply, continuumJacobianIntegral_algebraMap, zero_mul,
          zero_add, σ.parity.commutes r, ite_self, Algebra.smul_def, RingHom.id_apply] using hm }
  leibniz f g := continuumJacobianIntegral_leibniz μ dcoord hB (AlgHom.id ℚ B)
    (fun _ => rfl) v hv f g (hI f) (hI g)
  homogeneous f := continuumJacobianIntegral_homogeneous μ dcoord v hv P hP hI f

/-- The source continuum Ward operator has odd degree: multiplying the
antifield derivative of parity not ε by its inert source of parity ε
produces precisely the odd operator, with no finite coordinate sum. -/
def continuumSourceWardDerivative (μ : Measure X)
    {σ : GradingInvolution B} (ε : X → Bool)
    (afD : ∀ x, GradedDerivative σ (!(ε x)))
    (hB : SupercommutativeGrading σ) (J : X → B)
    (hJ : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (P : B →L[ℝ] B) (hP : ∀ f, P f = σ.parity f)
    (hI : ∀ f, Integrable (fun x => J x * (afD x).d f) μ) : GradedDerivative σ true :=
  continuumGradedDerivative μ afD hB J
    (fun x => by simpa only [Bool.true_xor, Bool.not_not] using hJ x) P hP hI

theorem continuumSourceWardDerivative_apply (μ : Measure X)
    {σ : GradingInvolution B} (ε : X → Bool)
    (afD : ∀ x, GradedDerivative σ (!(ε x)))
    (hB : SupercommutativeGrading σ) (J : X → B)
    (hJ : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (P : B →L[ℝ] B) (hP : ∀ f, P f = σ.parity f)
    (hI : ∀ f, Integrable (fun x => J x * (afD x).d f) μ) (f : B) :
    (continuumSourceWardDerivative μ ε afD hB J hJ P hP hI).d f =
      ∫ x, J x * (afD x).d f ∂μ := rfl

end UV
