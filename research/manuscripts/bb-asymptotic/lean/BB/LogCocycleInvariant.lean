import BB.Cocycle
import BB.CoboundaryMeasure
import BB.Asymptotics
import BB.Cemetery

/-!
# Invariant logarithmic averages from actual product envelopes

Finite products are integrated by a direct induction using invariance. No
pointwise ergodic theorem, empirical-measure compactness, or integrable
transfer function is assumed. The real logarithm is used only when the
multiplier is positive almost everywhere and its logarithm is integrable.
-/

noncomputable section
namespace BB
open MeasureTheory Filter
open scoped Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma log_prefix_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (r : X → ℝ)
    (hr : ∀ᵐ x ∂μ, 0 < r x) (hf : Integrable (fun x => Real.log (r x)) μ) (n : ℕ) :
    (∀ᵐ x ∂μ, 0 < prefixProduct r T n x) ∧
    Integrable (fun x => Real.log (prefixProduct r T n x)) μ ∧
    (∫ x, Real.log (prefixProduct r T n x) ∂μ) = (n:ℝ)*(∫ x, Real.log (r x) ∂μ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hposT := hT.quasiMeasurePreserving.ae ih.1
    have hlog : (fun x => Real.log (prefixProduct r T (n+1) x)) =ᵐ[μ]
        (fun x => Real.log (r x)+Real.log (prefixProduct r T n (T x))) := by
      filter_upwards [hr,hposT] with x hxr hxp
      exact Real.log_mul hxr.ne' hxp.ne'
    have hIntT : Integrable (fun x => Real.log (prefixProduct r T n (T x))) μ :=
      (hT.integrable_comp ih.2.1.aestronglyMeasurable).mpr ih.2.1
    refine ⟨?_,(hf.add hIntT).congr hlog.symm,?_⟩
    · filter_upwards [hr,hposT] with x hxr hxp
      exact mul_pos hxr hxp
    · rw [integral_congr_ae hlog, integral_add hf hIntT,
        invariant_integral_comp μ T hT _ ih.2.1.aestronglyMeasurable, ih.2.2]
      push_cast
      ring

lemma invariant_log_integral_le_of_envelope (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (r : X → ℝ)
    (hr : ∀ᵐ x ∂μ, 0 < r x) (hf : Integrable (fun x => Real.log (r x)) μ)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (henv : ∀ n x, prefixProduct r T n x ≤ C*γ^n) :
    (∫ x, Real.log (r x) ∂μ) ≤ Real.log γ := by
  have hbound : ∀ n : ℕ, (n:ℝ)*(∫ x, Real.log (r x) ∂μ) ≤ Real.log C+(n:ℝ)*Real.log γ := by
    intro n
    obtain ⟨hpos,hi,heq⟩ := log_prefix_integral μ T hT r hr hf n
    rw [← heq]
    have hle : ∀ᵐ x ∂μ, Real.log (prefixProduct r T n x) ≤ Real.log C+(n:ℝ)*Real.log γ := by
      filter_upwards [hpos] with x hx
      have h := Real.log_le_log hx (henv n x)
      rwa [Real.log_mul hC.ne' (pow_pos hγ n).ne', Real.log_pow] at h
    simpa using integral_mono_ae hi (integrable_const (Real.log C+(n:ℝ)*Real.log γ)) hle
  by_contra h
  have hd : 0 < (∫ x, Real.log (r x) ∂μ)-Real.log γ := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.log C/((∫ x, Real.log (r x) ∂μ)-Real.log γ))
  have hmul := (div_lt_iff hd).mp hn
  linarith [hbound n]

lemma invariant_log_integral_le_of_all_envelopes (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (r : X → ℝ)
    (hr : ∀ᵐ x ∂μ, 0 < r x) (hf : Integrable (fun x => Real.log (r x)) μ)
    (c : ℝ) (hc : 0 < c)
    (henv : ∀ γ : ℝ, c < γ → ∃ C : ℝ, 0 < C ∧ ∀ n x, prefixProduct r T n x ≤ C*γ^n) :
    (∫ x, Real.log (r x) ∂μ) ≤ Real.log c := by
  have he : Real.exp (∫ x, Real.log (r x) ∂μ) ≤ c := by
    apply le_of_forall_strict_upper_bound
    intro γ hγ
    obtain ⟨C,hC,hbound⟩ := henv γ hγ
    have hi := invariant_log_integral_le_of_envelope μ T hT r hr hf C γ hC (hc.trans hγ) hbound
    simpa only [Real.exp_log (hc.trans hγ)] using Real.exp_le_exp.mpr hi
  exact Real.exp_le_exp.mp (by simpa only [Real.exp_log hc] using he)

/-- The exact pointwise logarithmic identity on every regular finite segment. -/
lemma prefix_positive_and_log_sum (r : X → ℝ) (T : X → X) (n : ℕ) (x : X)
    (hreg : ∀ j < n, 0 < r (T^[j] x)) :
    0 < prefixProduct r T n x ∧
      Real.log (prefixProduct r T n x) = ∑ j in Finset.range n, Real.log (r (T^[j] x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hp,hs⟩ := ih (fun j hj => hreg j (by omega))
    have hc := hreg n (by omega)
    have hid : prefixProduct r T (n+1) x = prefixProduct r T n x*r (T^[n] x) := by
      rw [prefix_product_cocycle r T n 1 x]
      simp only [prefix_product_succ,prefix_product_zero,mul_one]
    refine ⟨by rw [hid]; exact mul_pos hp hc,?_⟩
    rw [hid,Real.log_mul hp.ne' hc.ne',hs,Finset.sum_range_succ]

/-- A family of actual multiplicative envelopes yields the manuscript's
additive semiuniform conclusion on every nonterminal segment. -/
lemma semiuniform_log_sum_of_all_envelopes (r : X → ℝ) (T : X → X) (c : ℝ) (hc : 0 < c)
    (henv : ∀ γ : ℝ, c < γ → ∃ C : ℝ, 0 < C ∧ ∀ n x, prefixProduct r T n x ≤ C*γ^n)
    (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x, (∀ j < n, 0 < r (T^[j] x)) →
      (∑ j in Finset.range n, Real.log (r (T^[j] x))) ≤ (n:ℝ)*(Real.log c+η)+B := by
  let γ := c*Real.exp η
  have hγpos : 0 < γ := mul_pos hc (Real.exp_pos _)
  have hγc : c < γ := by dsimp [γ]; nlinarith [Real.one_lt_exp_iff.mpr hη]
  obtain ⟨C,hC,hbound⟩ := henv γ hγc
  refine ⟨max 0 (Real.log C),le_max_left _ _,?_⟩
  intro n x hreg
  obtain ⟨hp,hs⟩ := prefix_positive_and_log_sum r T n x hreg
  rw [← hs]
  have hi := Real.log_le_log hp (hbound n x)
  rw [Real.log_mul hC.ne' (pow_pos hγpos n).ne',Real.log_pow] at hi
  have hlogγ : Real.log γ = Real.log c+η := by
    dsimp [γ]; rw [Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp]
  rw [hlogγ] at hi
  linarith [le_max_right 0 (Real.log C)]

/-- The extended invariant average also covers terminal mass and a divergent
negative part. There is no integrability premise in this theorem. -/
lemma invariant_extended_log_le_of_all_envelopes (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (r : X → ℝ) (hr : Measurable r)
    (D : ℝ) (hD : ∀ x, 0 < r x → Real.log (r x) ≤ D)
    (c : ℝ) (hc : 0 < c)
    (henv : ∀ γ : ℝ, c < γ → ∃ C : ℝ, 0 < C ∧ ∀ n x, prefixProduct r T n x ≤ C*γ^n) :
    extendedLogIntegral r D μ ≤ (Real.log c : EReal) := by
  rcases extendedLogIntegral_dichotomy r hr D hD μ with hbot | ⟨hpos,hf,heq⟩
  · rw [hbot]; exact bot_le
  · rw [heq]
    exact_mod_cast invariant_log_integral_le_of_all_envelopes μ T hT r hpos hf c hc henv

lemma killed_prefix_from_base (T : X → X) (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
    (n : ℕ) (x : X) :
    prefixProduct (killedMultiplier r) (killedMap T r) n (Sum.inl x) = prefixProduct r T n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [prefix_product_succ,prefix_product_succ]
    change r x * prefixProduct (killedMultiplier r) (killedMap T r) n (killedMap T r (Sum.inl x)) = _
    by_cases hx : 0 < r x
    · rw [killedMap_regular T r x hx,ih]
    · have hz : r x = 0 := le_antisymm (le_of_not_gt hx) (hr x)
      rw [hz,zero_mul,zero_mul]

lemma killed_prefix_at_point (T : X → X) (r : X → ℝ) (n : ℕ) :
    prefixProduct (killedMultiplier r) (killedMap T r) (n+1) cemeteryPoint = 0 := by
  exact prefix_product_terminal _ _ _ (killedMultiplier_point r) n

lemma killed_prefix_envelope (T : X → X) (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
    (C γ : ℝ) (hγ : 0 ≤ γ) (henv : ∀ n x, prefixProduct r T n x ≤ C*γ^n) :
    ∀ n x, prefixProduct (killedMultiplier r) (killedMap T r) n x ≤ (max 1 C)*γ^n := by
  intro n x
  cases x with
  | inl x =>
    rw [killed_prefix_from_base T r hr]
    exact (henv n x).trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hγ n))
  | inr u =>
    cases u
    cases n with
    | zero => simpa only [prefix_product_zero,pow_zero,mul_one] using le_max_left 1 C
    | succ n =>
      change prefixProduct (killedMultiplier r) (killedMap T r) (n+1) cemeteryPoint ≤ _
      rw [killed_prefix_at_point]
      exact mul_nonneg (zero_le_one.trans (le_max_left 1 C)) (pow_nonneg hγ _)

lemma killed_all_prefix_envelopes (T : X → X) (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
    (c : ℝ) (hc : 0 ≤ c)
    (henv : ∀ γ : ℝ, c < γ → ∃ C : ℝ, 0 < C ∧ ∀ n x, prefixProduct r T n x ≤ C*γ^n) :
    ∀ γ : ℝ, c < γ → ∃ C : ℝ, 0 < C ∧ ∀ n x,
      prefixProduct (killedMultiplier r) (killedMap T r) n x ≤ C*γ^n := by
  intro γ hγ
  obtain ⟨C,_hC,hbound⟩ := henv γ hγ
  exact ⟨max 1 C,zero_lt_one.trans_le (le_max_left 1 C),
    killed_prefix_envelope T r hr C γ (hc.trans hγ.le) hbound⟩

end BB
