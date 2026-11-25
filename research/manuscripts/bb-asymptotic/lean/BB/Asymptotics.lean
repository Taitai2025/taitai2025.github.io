import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Asymptotic tools for BB convergence factors

The definitions use real `limsup`, so the comparison and shift results explicitly
assume eventual upper boundedness of the root sequences. The exponential-envelope
result itself does not need this assumption: it derives the needed upper bound.
-/

namespace BB

open Filter
open scoped Topology

lemma le_of_forall_strict_upper_bound {x y : ℝ}
    (h : ∀ z : ℝ, y < z → x ≤ z) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hyz, hzx⟩ := exists_between (lt_of_not_ge hxy)
  exact (not_le_of_gt hzx) (h z hyz)

noncomputable def rootTerm (u : ℕ → ℝ) (n : ℕ) : ℝ := u n ^ ((n : ℝ)⁻¹)

noncomputable def rootFactor (u : ℕ → ℝ) : ℝ :=
  Filter.limsup (rootTerm u) Filter.atTop

def ExponentialEnvelope (u : ℕ → ℝ) (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, u n ≤ C * γ ^ n

lemma rootTerm_nonneg (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    0 ≤ rootTerm u n := Real.rpow_nonneg (hu n) _

lemma rootTerm_cobounded (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    atTop.IsCoboundedUnder (· ≤ ·) (rootTerm u) := by
  have hb : atTop.IsBoundedUnder (· ≥ ·) (rootTerm u) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ rootTerm u n
    exact Filter.eventually_of_forall (rootTerm_nonneg u hu)
  exact hb.isCobounded_flip

lemma tendsto_constant_root (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  simpa using (tendsto_const_nhds.rpow tendsto_inverse_atTop_nhds_zero_nat
    (Or.inl (ne_of_gt hC)) :
    Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 (C ^ (0 : ℝ))))

lemma rootTerm_geometric (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (n : ℕ) (hn : n ≠ 0) :
    rootTerm (fun k => C * γ ^ k) n = C ^ ((n : ℝ)⁻¹) * γ := by
  unfold rootTerm
  rw [Real.mul_rpow hC (pow_nonneg hγ n), Real.pow_rpow_inv_natCast hγ hn]

lemma rootFactor_le_of_eventual_envelope (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 ≤ γ)
    (h : ∀ᶠ n in atTop, u n ≤ C * γ ^ n) : rootFactor u ≤ γ := by
  have ht : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹) * γ) atTop (𝓝 γ) := by
    simpa using (tendsto_constant_root C hC).mul_const γ
  have he : ∀ᶠ n in atTop,
      rootTerm u n ≤ C ^ ((n : ℝ)⁻¹) * γ := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    calc
      rootTerm u n ≤ rootTerm (fun k => C * γ ^ k) n :=
        Real.rpow_le_rpow (hu n) hn (by positivity)
      _ = C ^ ((n : ℝ)⁻¹) * γ :=
        rootTerm_geometric C γ hC.le hγ n (by omega)
  calc
    rootFactor u ≤ Filter.limsup (fun n : ℕ => C ^ ((n : ℝ)⁻¹) * γ) atTop :=
      Filter.limsup_le_limsup he (rootTerm_cobounded u hu) ht.isBoundedUnder_le
    _ = γ := ht.limsup_eq

lemma rootFactor_le_of_envelope (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ExponentialEnvelope u γ) : rootFactor u ≤ γ := by
  obtain ⟨C, hC, h⟩ := h
  exact rootFactor_le_of_eventual_envelope u hu C γ hC hγ
    (Filter.eventually_of_forall h)

lemma rootFactor_le_of_all_envelopes (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ γ : ℝ, c < γ → ExponentialEnvelope u γ) : rootFactor u ≤ c := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  exact rootFactor_le_of_envelope u hu γ (hc.trans hγ.le) (h γ hγ)

lemma rootFactor_nonneg (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u)) : 0 ≤ rootFactor u := by
  exact Filter.le_limsup_of_frequently_le
    (Filter.Eventually.frequently (Filter.eventually_of_forall (rootTerm_nonneg u hu))) hb

lemma eventual_geometric_of_rootFactor_lt (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (γ : ℝ) (hγ : 0 < γ) (h : rootFactor u < γ) :
    ∀ᶠ n in atTop, u n ≤ γ ^ n := by
  have he := Filter.eventually_lt_of_limsup_lt h hb
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : u n < γ ^ (n : ℝ) :=
    (Real.rpow_inv_lt_iff_of_pos (hu n) hγ.le hnpos).mp hn
  simpa only [Real.rpow_natCast] using hh.le

lemma envelope_of_rootFactor_lt (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (γ : ℝ) (hγ : 0 < γ) (h : rootFactor u < γ) : ExponentialEnvelope u γ := by
  have he := eventual_geometric_of_rootFactor_lt u hu hub γ hγ h
  have hquot : atTop.IsBoundedUnder (· ≤ ·) (fun n => u n / γ ^ n) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n in atTop, u n / γ ^ n ≤ 1
    filter_upwards [he] with n hn
    exact (div_le_one (pow_pos hγ n)).mpr hn
  obtain ⟨C, hC⟩ := hquot.bddAbove_range
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro n
  apply (div_le_iff (pow_pos hγ n)).mp
  exact (hC (Set.mem_range_self n)).trans (le_max_left C 1)

lemma rootFactor_le_of_rates_below_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ γ : ℝ, c < γ → γ < 1 → ExponentialEnvelope u γ) : rootFactor u ≤ c := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  obtain ⟨δ, hcδ, hδ⟩ := exists_between (lt_min hγ hc1)
  have hδγ : δ < γ := hδ.trans_le (min_le_left γ 1)
  have hδ1 : δ < 1 := hδ.trans_le (min_le_right γ 1)
  exact (rootFactor_le_of_envelope u hu δ (hc.trans hcδ.le) (h δ hcδ hδ1)).trans hδγ.le

lemma rootFactor_le_of_comparison (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v))
    (C : ℝ) (hC : 0 < C) (h : ∀ᶠ n in atTop, u n ≤ C * v n) :
    rootFactor u ≤ rootFactor v := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  have hγpos : 0 < γ := (rootFactor_nonneg v hv hvb).trans_lt hγ
  apply rootFactor_le_of_eventual_envelope u hu C γ hC hγpos.le
  filter_upwards [h, eventual_geometric_of_rootFactor_lt v hv hvb γ hγpos hγ]
    with n hn hvn
  exact hn.trans (mul_le_mul_of_nonneg_left hvn hC.le)

lemma rootFactor_eq_of_two_sided_comparison (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v))
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (huv : ∀ᶠ n in atTop, u n ≤ C * v n)
    (hvu : ∀ᶠ n in atTop, v n ≤ D * u n) : rootFactor u = rootFactor v := by
  exact le_antisymm (rootFactor_le_of_comparison u v hu hv hvb C hC huv)
    (rootFactor_le_of_comparison v u hv hu hub D hD hvu)

/-- A finite-termination sequence has root factor zero. -/
lemma rootFactor_eq_zero_of_eventually_zero (u : ℕ → ℝ)
    (h : ∀ᶠ n in atTop, u n = 0) : rootFactor u = 0 := by
  have he : rootTerm u =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    unfold rootTerm
    rw [hn, Real.zero_rpow]
    positivity
  exact (Filter.limsup_congr he).trans (by simp)

/-- Exact geometric trajectories have the advertised root factor. -/
lemma rootFactor_geometric (C γ : ℝ) (hC : 0 < C) (hγ : 0 ≤ γ) :
    rootFactor (fun n => C * γ ^ n) = γ := by
  have he : rootTerm (fun n => C * γ ^ n) =ᶠ[atTop]
      fun n : ℕ => C ^ ((n : ℝ)⁻¹) * γ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact rootTerm_geometric C γ hC.le hγ n (by omega)
  have ht : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹) * γ) atTop (𝓝 γ) := by
    simpa using (tendsto_constant_root C hC).mul_const γ
  exact (Filter.limsup_congr he).trans ht.limsup_eq

lemma no_smaller_envelope_for_geometric (C ρ γ : ℝ)
    (hC : 0 < C) (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hlt : γ < ρ) :
    ¬ ExponentialEnvelope (fun n => C * ρ ^ n) γ := by
  intro he
  have hb := rootFactor_le_of_envelope (fun n => C * ρ ^ n)
    (fun n => mul_nonneg hC.le (pow_nonneg hρ n)) γ hγ he
  rw [rootFactor_geometric C ρ hC hρ] at hb
  exact (not_le_of_gt hlt) hb

/-- An eventual geometric estimate also gives the boundedness needed for real `limsup`. -/
lemma rootTerm_bounded_of_eventual_envelope (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 ≤ γ)
    (h : ∀ᶠ n in atTop, u n ≤ C * γ ^ n) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm u) := by
  have ht : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹) * γ) atTop (𝓝 γ) := by
    simpa using (tendsto_constant_root C hC).mul_const γ
  apply ht.isBoundedUnder_le.mono_le
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  calc
    rootTerm u n ≤ rootTerm (fun k => C * γ ^ k) n :=
      Real.rpow_le_rpow (hu n) hn (by positivity)
    _ = C ^ ((n : ℝ)⁻¹) * γ :=
      rootTerm_geometric C γ hC.le hγ n (by omega)

lemma rootTerm_bounded_of_comparison (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v))
    (C : ℝ) (hC : 0 < C) (h : ∀ᶠ n in atTop, u n ≤ C * v n) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm u) := by
  let γ := rootFactor v + 1
  have hγ : 0 < γ := by dsimp [γ]; linarith [rootFactor_nonneg v hv hvb]
  apply rootTerm_bounded_of_eventual_envelope u hu C γ hC hγ.le
  filter_upwards [h, eventual_geometric_of_rootFactor_lt v hv hvb γ hγ (by dsimp [γ]; linarith)]
    with n hn hvn
  exact hn.trans (mul_le_mul_of_nonneg_left hvn hC.le)

lemma rootFactor_eq_of_comparable (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v))
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (huv : ∀ᶠ n in atTop, u n ≤ C * v n)
    (hvu : ∀ᶠ n in atTop, v n ≤ D * u n) : rootFactor u = rootFactor v := by
  exact rootFactor_eq_of_two_sided_comparison u v hu hv
    (rootTerm_bounded_of_comparison u v hu hv hvb C hC huv) hvb C D hC hD huv hvu

lemma rootFactor_mul_const (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (C : ℝ) (hC : 0 < C) : rootFactor (fun n => C * u n) = rootFactor u := by
  apply rootFactor_eq_of_comparable (fun n => C * u n) u
    (fun n => mul_nonneg hC.le (hu n)) hu hub C C⁻¹ hC (inv_pos.mpr hC)
  · exact Filter.eventually_of_forall fun _ => le_rfl
  · apply Filter.eventually_of_forall
    intro n
    rw [← mul_assoc, inv_mul_cancel hC.ne', one_mul]

lemma rootFactor_div_const (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (C : ℝ) (hC : 0 < C) : rootFactor (fun n => u n / C) = rootFactor u := by
  simpa only [div_eq_mul_inv, mul_comm] using rootFactor_mul_const u hu hub C⁻¹ (inv_pos.mpr hC)

lemma rootFactor_shift_le (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u)) (m : ℕ) :
    rootFactor (fun n => u (n + m)) ≤ rootFactor u := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  have hγpos : 0 < γ := (rootFactor_nonneg u hu hub).trans_lt hγ
  apply rootFactor_le_of_eventual_envelope (fun n => u (n + m))
    (fun n => hu (n + m)) (γ ^ m) γ (pow_pos hγpos m) hγpos.le
  have he := (tendsto_add_atTop_nat m).eventually
    (eventual_geometric_of_rootFactor_lt u hu hub γ hγpos hγ)
  filter_upwards [he] with n hn
  simpa only [pow_add, mul_comm] using hn

lemma rootFactor_le_shift (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (m : ℕ)
    (hsb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u (n + m)))) :
    rootFactor u ≤ rootFactor (fun n => u (n + m)) := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  have hγpos : 0 < γ :=
    (rootFactor_nonneg (fun n => u (n + m)) (fun n => hu (n + m)) hsb).trans_lt hγ
  have he := eventual_geometric_of_rootFactor_lt (fun n => u (n + m))
    (fun n => hu (n + m)) hsb γ hγpos hγ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  apply rootFactor_le_of_eventual_envelope u hu (γ ^ m)⁻¹ γ
    (inv_pos.mpr (pow_pos hγpos m)) hγpos.le
  apply Filter.eventually_atTop.mpr
  refine ⟨N + m, ?_⟩
  intro n hn
  have hmn : m ≤ n := by omega
  have hNm : N ≤ n - m := by omega
  have hh := hN (n - m) hNm
  dsimp only at hh
  rw [Nat.sub_add_cancel hmn] at hh
  calc
    u n ≤ γ ^ (n - m) := hh
    _ = (γ ^ m)⁻¹ * γ ^ n := by
      rw [← Nat.sub_add_cancel hmn, pow_add]
      field_simp

lemma rootFactor_shift_eq (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u)) (m : ℕ) :
    rootFactor (fun n => u (n + m)) = rootFactor u := by
  let γ := rootFactor u + 1
  have hγ : 0 < γ := by dsimp [γ]; linarith [rootFactor_nonneg u hu hub]
  have hs : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u (n + m))) := by
    apply rootTerm_bounded_of_eventual_envelope (fun n => u (n + m))
      (fun n => hu (n + m)) (γ ^ m) γ (pow_pos hγ m) hγ.le
    have he := (tendsto_add_atTop_nat m).eventually
      (eventual_geometric_of_rootFactor_lt u hu hub γ hγ (by dsimp [γ]; linarith))
    filter_upwards [he] with n hn
    simpa only [pow_add, mul_comm] using hn
  exact le_antisymm (rootFactor_shift_le u hu hub m) (rootFactor_le_shift u hu m hs)

lemma rootTerm_pow (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (m n : ℕ) :
    rootTerm (fun k => u k ^ m) n = rootTerm u n ^ m := by
  change (u n ^ m) ^ ((n : ℝ)⁻¹) = (u n ^ ((n : ℝ)⁻¹)) ^ m
  rw [← Real.rpow_natCast (u n) m, ← Real.rpow_mul (hu n), mul_comm,
    Real.rpow_mul (hu n), Real.rpow_natCast]

lemma rootTerm_pow_bounded (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u)) (m : ℕ) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u n ^ m)) := by
  obtain ⟨B, hB⟩ := hub
  refine ⟨(max B 0) ^ m, ?_⟩
  change ∀ᶠ n in atTop, rootTerm (fun n => u n ^ m) n ≤ (max B 0) ^ m
  change ∀ᶠ n in atTop, rootTerm u n ≤ B at hB
  filter_upwards [hB] with n hn
  rw [rootTerm_pow u hu m n]
  exact pow_le_pow_left (rootTerm_nonneg u hu n) (hn.trans (le_max_left B 0)) m

/-- In particular an objective gap comparable to the squared error has squared root factor. -/
lemma rootFactor_pow (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u)) (m : ℕ) :
    rootFactor (fun n => u n ^ m) = rootFactor u ^ m := by
  let f : ℝ → ℝ := fun x => (max x 0) ^ m
  have hf : Monotone f := by
    intro x y hxy
    exact pow_le_pow_left (le_max_right x 0) (max_le_max hxy le_rfl) m
  have hc : Continuous f := (continuous_id.max continuous_const).pow m
  have hl : atTop.IsBoundedUnder (· ≥ ·) (rootTerm u) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ rootTerm u n
    exact Filter.eventually_of_forall (rootTerm_nonneg u hu)
  have hm := hf.map_limsup_of_continuousAt (rootTerm u) hc.continuousAt hub hl
  calc
    rootFactor (fun n => u n ^ m) = Filter.limsup (f ∘ rootTerm u) atTop := by
      apply Filter.limsup_congr
      apply Filter.eventually_of_forall
      intro n
      rw [rootTerm_pow u hu m n]
      dsimp only [Function.comp_def, f]
      rw [max_eq_left (rootTerm_nonneg u hu n)]
    _ = f (rootFactor u) := hm.symm
    _ = rootFactor u ^ m := by
      dsimp only [f]
      rw [max_eq_left (rootFactor_nonneg u hu hub)]

lemma rootTerm_bounded_of_square (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hs : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u n ^ 2))) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm u) := by
  obtain ⟨B, hB⟩ := hs
  refine ⟨max B 1, ?_⟩
  change ∀ᶠ n in atTop, rootTerm u n ≤ max B 1
  change ∀ᶠ n in atTop, rootTerm (fun n => u n ^ 2) n ≤ B at hB
  filter_upwards [hB] with n hn
  rw [rootTerm_pow u hu 2 n] at hn
  have hr := rootTerm_nonneg u hu n
  rcases le_or_lt (rootTerm u n) 1 with h | h
  · exact h.trans (le_max_right B 1)
  · have : rootTerm u n ≤ B := by nlinarith
    exact this.trans (le_max_left B 1)

lemma rootTerm_add_bounded (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v)) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u n + v n)) := by
  let γ := max (rootFactor u) (rootFactor v) + 1
  have huγ : rootFactor u < γ := by dsimp [γ]; linarith [le_max_left (rootFactor u) (rootFactor v)]
  have hvγ : rootFactor v < γ := by dsimp [γ]; linarith [le_max_right (rootFactor u) (rootFactor v)]
  have hγ : 0 < γ := (rootFactor_nonneg u hu hub).trans_lt huγ
  apply rootTerm_bounded_of_eventual_envelope (fun n => u n + v n)
    (fun n => add_nonneg (hu n) (hv n)) 2 γ (by norm_num) hγ.le
  filter_upwards [eventual_geometric_of_rootFactor_lt u hu hub γ hγ huγ,
    eventual_geometric_of_rootFactor_lt v hv hvb γ hγ hvγ] with n hun hvn
  linarith

lemma rootFactor_add (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hub : atTop.IsBoundedUnder (· ≤ ·) (rootTerm u))
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v)) :
    rootFactor (fun n => u n + v n) = max (rootFactor u) (rootFactor v) := by
  apply le_antisymm
  · apply le_of_forall_strict_upper_bound
    intro γ hγ
    have huγ := (le_max_left (rootFactor u) (rootFactor v)).trans_lt hγ
    have hvγ := (le_max_right (rootFactor u) (rootFactor v)).trans_lt hγ
    have hγpos := (rootFactor_nonneg u hu hub).trans_lt huγ
    apply rootFactor_le_of_eventual_envelope (fun n => u n + v n)
      (fun n => add_nonneg (hu n) (hv n)) 2 γ (by norm_num) hγpos.le
    filter_upwards [eventual_geometric_of_rootFactor_lt u hu hub γ hγpos huγ,
      eventual_geometric_of_rootFactor_lt v hv hvb γ hγpos hvγ] with n hun hvn
    linarith
  · apply max_le
    · apply rootFactor_le_of_comparison u (fun n => u n + v n) hu
        (fun n => add_nonneg (hu n) (hv n)) (rootTerm_add_bounded u v hu hv hub hvb)
        1 zero_lt_one
      exact Filter.eventually_of_forall fun n => by nlinarith [hv n]
    · apply rootFactor_le_of_comparison v (fun n => u n + v n) hv
        (fun n => add_nonneg (hu n) (hv n)) (rootTerm_add_bounded u v hu hv hub hvb)
        1 zero_lt_one
      exact Filter.eventually_of_forall fun n => by nlinarith [hu n]

/-- The positive-definite quadratic form for `z[k+2] = z[k+1] - 2 z[k]`. -/
def recurrenceEnergy (x y : ℝ) : ℝ := x ^ 2 - x * y + 2 * y ^ 2

lemma recurrenceEnergy_nonneg (x y : ℝ) : 0 ≤ recurrenceEnergy x y := by
  unfold recurrenceEnergy
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

lemma recurrenceEnergy_eq_zero_iff (x y : ℝ) :
    recurrenceEnergy x y = 0 ↔ x = 0 ∧ y = 0 := by
  unfold recurrenceEnergy
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    ring

lemma recurrenceEnergy_step (x y : ℝ) :
    recurrenceEnergy (x - 2 * y) x = 2 * recurrenceEnergy x y := by
  unfold recurrenceEnergy
  ring

lemma recurrenceEnergy_trajectory (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n) (n : ℕ) :
    recurrenceEnergy (z (n + 1)) (z n) = 2 ^ n * recurrenceEnergy (z 1) (z 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, hz n, recurrenceEnergy_step, ih]
    ring

lemma recurrenceEnergy_bounds (x y : ℝ) :
    (x ^ 2 + y ^ 2) / 2 ≤ recurrenceEnergy x y ∧
      recurrenceEnergy x y ≤ 3 * (x ^ 2 + y ^ 2) := by
  unfold recurrenceEnergy
  constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]

lemma recurrenceEnergy_tendsto_atTop (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n)
    (hne : ¬ (z 0 = 0 ∧ z 1 = 0)) :
    Tendsto (fun n => recurrenceEnergy (z (n + 1)) (z n)) atTop atTop := by
  have hE : 0 < recurrenceEnergy (z 1) (z 0) := by
    have hn := recurrenceEnergy_nonneg (z 1) (z 0)
    have hnot : recurrenceEnergy (z 1) (z 0) ≠ 0 := by
      intro h
      exact hne ((recurrenceEnergy_eq_zero_iff (z 1) (z 0)).mp h).symm
    exact lt_of_le_of_ne hn hnot.symm
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hE
  exact ht.congr (fun n => (recurrenceEnergy_trajectory z hz n).symm)

/-- A returning pair in the linear logarithmic recurrence must be the origin. -/
lemma recurrence_periodic_pair_zero (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n)
    (p : ℕ) (hp : 0 < p) (h0 : z p = z 0) (h1 : z (p + 1) = z 1) :
    z 0 = 0 ∧ z 1 = 0 := by
  have he := recurrenceEnergy_trajectory z hz p
  rw [h0, h1] at he
  have hpow : (1 : ℝ) < 2 ^ p := one_lt_pow (by norm_num) (by omega)
  have hn := recurrenceEnergy_nonneg (z 1) (z 0)
  have hz0 : recurrenceEnergy (z 1) (z 0) = 0 := by nlinarith
  exact (recurrenceEnergy_eq_zero_iff (z 1) (z 0)).mp hz0 |>.symm

/-- The sharp logarithmic growth claimed in Proposition 3.2, for arbitrary nonzero initial pairs. -/
lemma recurrence_rootFactor_abs (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n)
    (hne : ¬ (z 0 = 0 ∧ z 1 = 0)) :
    rootFactor (fun n => |z n|) = Real.sqrt 2 := by
  let E := recurrenceEnergy (z 1) (z 0)
  have hE : 0 < E := by
    have hn := recurrenceEnergy_nonneg (z 1) (z 0)
    have hnot : E ≠ 0 := by
      intro h
      exact hne ((recurrenceEnergy_eq_zero_iff (z 1) (z 0)).mp h).symm
    exact lt_of_le_of_ne hn hnot.symm
  let u : ℕ → ℝ := fun n => |z n|
  have hu : ∀ n, 0 ≤ u n := fun n => abs_nonneg _
  have hsqenv : ∀ n, u n ^ 2 ≤ (2 * E) * 2 ^ n := by
    intro n
    have hb := (recurrenceEnergy_bounds (z (n + 1)) (z n)).1
    rw [recurrenceEnergy_trajectory z hz n] at hb
    dsimp only [u]
    rw [sq_abs]
    dsimp only [E]
    nlinarith [sq_nonneg (z (n + 1))]
  have hsqb := rootTerm_bounded_of_eventual_envelope (fun n => u n ^ 2)
    (fun n => sq_nonneg _) (2 * E) 2 (by positivity) (by norm_num)
    (Filter.eventually_of_forall hsqenv)
  have hub := rootTerm_bounded_of_square u hu hsqb
  have hshift : rootFactor (fun n => u (n + 1)) = rootFactor u := rootFactor_shift_eq u hu hub 1
  have hshiftb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => u (n + 1))) := by
    have he := eventual_geometric_of_rootFactor_lt u hu hub (rootFactor u + 1)
      (by linarith [rootFactor_nonneg u hu hub]) (by linarith)
    apply rootTerm_bounded_of_eventual_envelope (fun n => u (n + 1))
      (fun n => hu (n + 1)) (rootFactor u + 1) (rootFactor u + 1)
      (by linarith [rootFactor_nonneg u hu hub]) (by linarith [rootFactor_nonneg u hu hub])
    have hes := (tendsto_add_atTop_nat 1).eventually he
    filter_upwards [hes] with n hn
    simpa only [pow_succ, mul_comm] using hn
  let w : ℕ → ℝ := fun n => u (n + 1) ^ 2 + u n ^ 2
  have hw : ∀ n, 0 ≤ w n := fun n => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hwb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm w) :=
    rootTerm_add_bounded (fun n => u (n + 1) ^ 2) (fun n => u n ^ 2)
      (fun n => sq_nonneg _) (fun n => sq_nonneg _)
      (rootTerm_pow_bounded (fun n => u (n + 1)) (fun n => hu (n + 1)) hshiftb 2) hsqb
  have hwrate : rootFactor w = rootFactor u ^ 2 := by
    rw [rootFactor_add (fun n => u (n + 1) ^ 2) (fun n => u n ^ 2)
      (fun n => sq_nonneg _) (fun n => sq_nonneg _)
      (rootTerm_pow_bounded (fun n => u (n + 1)) (fun n => hu (n + 1)) hshiftb 2) hsqb,
      rootFactor_pow (fun n => u (n + 1)) (fun n => hu (n + 1)) hshiftb 2,
      rootFactor_pow u hu hub 2, hshift, max_self]
  let q : ℕ → ℝ := fun n => recurrenceEnergy (z (n + 1)) (z n)
  have hq : ∀ n, 0 ≤ q n := fun n => recurrenceEnergy_nonneg _ _
  have hqwrate : rootFactor q = rootFactor w := by
    apply rootFactor_eq_of_comparable q w hq hw hwb 3 2 (by norm_num) (by norm_num)
    · apply Filter.eventually_of_forall
      intro n
      dsimp only [q, w, u]
      simp only [sq_abs]
      exact (recurrenceEnergy_bounds (z (n + 1)) (z n)).2
    · apply Filter.eventually_of_forall
      intro n
      dsimp only [q, w, u]
      simp only [sq_abs]
      have hh := (recurrenceEnergy_bounds (z (n + 1)) (z n)).1
      linarith
  have hqrate : rootFactor q = 2 := by
    have hqe : q = (fun n => E * 2 ^ n) := by
      funext n
      exact (recurrenceEnergy_trajectory z hz n).trans (mul_comm _ _)
    rw [hqe]
    exact rootFactor_geometric E 2 hE (by norm_num)
  have hsq : rootFactor u ^ 2 = 2 := hwrate.symm.trans (hqwrate.symm.trans hqrate)
  have hr := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (rootFactor_nonneg u hu hub)] at hr
  exact hr

lemma recurrence_bounded_initial_zero (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n)
    (M : ℝ) (hM : ∀ n, |z n| ≤ M) : z 0 = 0 ∧ z 1 = 0 := by
  by_contra hne
  have hr := recurrence_rootFactor_abs z hz hne
  have he : ExponentialEnvelope (fun n => |z n|) 1 := by
    refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right M 1), ?_⟩
    intro n
    simpa using (hM n).trans (le_max_left M 1)
  have hb := rootFactor_le_of_envelope (fun n => |z n|) (fun n => abs_nonneg _) 1 (by norm_num) he
  rw [hr] at hb
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

lemma recurrence_zero_of_initial_zero (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 2) = z (n + 1) - 2 * z n)
    (h0 : z 0 = 0) (h1 : z 1 = 0) : ∀ n, z n = 0 := by
  exact Nat.twoStepInduction h0 h1 (fun n hn hn1 => by rw [hz n, hn, hn1]; ring)

end BB
