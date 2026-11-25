import BB.Asymptotics
import BB.Cocycle
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# Compactness and variable-length contraction

These are abstract lemmas. Instantiating their pointwise-contraction and cocycle
hypotheses for the full BB state space is a separate obligation.
-/

namespace BB

open Filter Set
open scoped Topology

/-- Compactness makes a pointwise strictly contracting prefix uniform in both
its length and its contraction amount. No continuity of the state map is assumed. -/
lemma compact_uniform_prefix {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (R : ℕ → X → ℝ) (hcont : ∀ n, Continuous (R n))
    (hpos : ∀ n x, 0 ≤ R n x)
    (hprefix : ∀ x, ∃ n : ℕ, 0 < n ∧ R n x < 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ x, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ R j x ≤ q := by
  classical
  choose n hn hRn using hprefix
  let c : X → ℝ := fun x => (1 + R (n x) x) / 2
  have hcpos : ∀ x, 0 < c x := by
    intro x
    dsimp only [c]
    linarith [hpos (n x) x]
  have hclt : ∀ x, c x < 1 := by
    intro x
    dsimp only [c]
    linarith [hRn x]
  let U : X → Set X := fun x => {y | R (n x) y < c x}
  have hUopen : ∀ x, IsOpen (U x) := fun x => isOpen_lt (hcont (n x)) continuous_const
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _hx
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    dsimp only [U, Set.mem_setOf_eq, c]
    linarith [hRn x]
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨x1, hx1s, _hx1⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x0))
  have hsne : s.Nonempty := ⟨x1, hx1s⟩
  let N := s.sup n
  let q := s.sup' hsne c
  have hN : 0 < N := (hn x1).trans_le (Finset.le_sup hx1s)
  have hq : 0 < q := (hcpos x1).trans_le (Finset.le_sup' c hx1s)
  have hq1 : q < 1 := (Finset.sup'_lt_iff hsne).mpr (fun x _hx => hclt x)
  refine ⟨N, hN, q, hq, hq1, ?_⟩
  intro x
  obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine ⟨n y, hn y, Finset.le_sup hys, ?_⟩
  change R (n y) x < c y at hxy
  exact hxy.le.trans (Finset.le_sup' c hys)

lemma cocycle_bound_of_one_step {X : Type*} (T : X → X) (R : ℕ → X → ℝ)
    (hzero : ∀ x, R 0 x = 1) (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (M : ℝ) (hM : 0 ≤ M) (hstep : ∀ x, R 1 x ≤ M) :
    ∀ n x, R n x ≤ M ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [hzero]
  | succ n ih =>
    intro x
    calc
      R (n + 1) x = R 1 x * R n (T^[1] x) := by
        rw [Nat.add_comm n 1, hcocycle 1 n x]
      _ ≤ M * M ^ n := mul_le_mul (hstep x) (ih _) (hpos n _) hM
      _ = M ^ (n + 1) := by rw [pow_succ]; ring

/-- A bounded-length contraction criterion gives a uniform geometric bound.
The explicit prefactor is `(M/γ)^N`. -/
lemma envelope_of_uniform_prefix {X : Type*} (T : X → X) (R : ℕ → X → ℝ)
    (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (M γ : ℝ) (hM : 1 ≤ M) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hbound : ∀ n x, R n x ≤ M ^ n)
    (N : ℕ) (q : ℝ) (hq : q ≤ γ ^ N)
    (hprefix : ∀ x, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ R j x ≤ q) :
    ∀ n x, R n x ≤ (M / γ) ^ N * γ ^ n := by
  have hratio : 1 ≤ M / γ := (le_div_iff hγ).mpr (by linarith)
  have hC : 0 < (M / γ) ^ N := pow_pos (div_pos (by linarith) hγ) N
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    by_cases hn : n < N
    · have hp : (M / γ) ^ n ≤ (M / γ) ^ N := pow_le_pow_right hratio hn.le
      have hr : R n x / γ ^ n ≤ (M / γ) ^ n := by
        rw [div_pow]
        exact div_le_div_of_nonneg_right (hbound n x) (pow_nonneg hγ.le n)
      exact (div_le_iff (pow_pos hγ n)).mp (hr.trans hp)
    · obtain ⟨j, hj, hjN, hjq⟩ := hprefix x
      have hjn : j ≤ n := by omega
      have hsub : n - j < n := by omega
      have hjγ : q ≤ γ ^ j := hq.trans (pow_le_pow_of_le_one hγ.le hγ1 hjN)
      calc
        R n x = R j x * R (n - j) (T^[j] x) := by
          rw [← hcocycle j (n - j) x]
          congr 1
          omega
        _ ≤ q * ((M / γ) ^ N * γ ^ (n - j)) :=
          mul_le_mul hjq (ih (n - j) hsub _) (hpos (n - j) _)
            (le_trans (hpos j x) hjq)
        _ ≤ γ ^ j * ((M / γ) ^ N * γ ^ (n - j)) :=
          mul_le_mul_of_nonneg_right hjγ (mul_nonneg hC.le (pow_nonneg hγ.le _))
        _ = (M / γ) ^ N * γ ^ n := by
          have hsum : j + (n - j) = n := by omega
          calc
            γ ^ j * ((M / γ) ^ N * γ ^ (n - j)) =
                (M / γ) ^ N * (γ ^ j * γ ^ (n - j)) := by ring
            _ = (M / γ) ^ N * γ ^ (j + (n - j)) := by rw [pow_add]
            _ = (M / γ) ^ N * γ ^ n := by rw [hsum]

/-- A compact continuous cocycle with a contracting prefix at every state
admits a single exponential envelope for all states and all times. -/
lemma compact_cocycle_uniform_envelope {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (T : X → X) (R : ℕ → X → ℝ)
    (hzero : ∀ x, R 0 x = 1) (hcont : ∀ n, Continuous (R n))
    (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (hprefix : ∀ x, ∃ n : ℕ, 0 < n ∧ R n x < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      ∀ n x, R n x ≤ C * γ ^ n := by
  classical
  obtain ⟨N, hN, q, hq, hq1, hpref⟩ := compact_uniform_prefix R hcont hpos hprefix
  obtain ⟨M0, hM0⟩ := (isCompact_univ.image (hcont 1)).bddAbove
  let M := max M0 1
  have hM : 1 ≤ M := le_max_right _ _
  have hstep : ∀ x, R 1 x ≤ M := by
    intro x
    exact (hM0 (Set.mem_image_of_mem (R 1) (Set.mem_univ x))).trans (le_max_left M0 1)
  let γ := q ^ ((N : ℝ)⁻¹)
  have hγ : 0 < γ := Real.rpow_pos_of_pos hq _
  have hγ1 : γ < 1 := Real.rpow_lt_one hq.le hq1 (by positivity)
  have hγN : γ ^ N = q := Real.rpow_inv_natCast_pow hq.le (by omega)
  refine ⟨(M / γ) ^ N, pow_pos (div_pos (by linarith) hγ) N, γ, hγ, hγ1, ?_⟩
  exact envelope_of_uniform_prefix T R hpos hcocycle M γ hM hγ hγ1.le
    (cocycle_bound_of_one_step T R hzero hpos hcocycle M (by linarith) hstep)
    N q hγN.ge hpref

/-- Relative contraction on every sufficiently late tail is incompatible with a
positive lower bound. This proof uses the infimum of the tail values. -/
lemma tail_relative_contraction_contradiction (p : ℕ → ℝ) (N : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hbelow : ∀ n, 1 ≤ p n)
    (hcontract : ∀ n, N ≤ n → ∃ m : ℕ, N ≤ m ∧ p m ≤ q * p n) : False := by
  let S : Set ℝ := {y | ∃ n : ℕ, N ≤ n ∧ p n = y}
  have hS : S.Nonempty := ⟨p N, N, le_rfl, rfl⟩
  have hSb : BddBelow S := ⟨1, by
    rintro y ⟨n, _hn, rfl⟩
    exact hbelow n⟩
  let μ := sInf S
  have hμ : 1 ≤ μ := le_csInf hS (by
    rintro y ⟨n, _hn, rfl⟩
    exact hbelow n)
  have hlt : μ < μ / q := (lt_div_iff hq).mpr (by nlinarith)
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hS hlt
  obtain ⟨n, hn, rfl⟩ := hy
  obtain ⟨m, hm, hpm⟩ := hcontract n hn
  have hμm : μ ≤ p m := csInf_le hSb ⟨m, hm, rfl⟩
  have hsmall : q * p n < μ := by
    have hh := (lt_div_iff hq).mp hylt
    nlinarith
  linarith

/-- On a compact space, a nonnegative continuous function tending to zero
forces a sequence into every open neighborhood of its zero set. -/
lemma eventually_mem_zero_neighborhood {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (V : X → ℝ) (hV : Continuous V) (hVpos : ∀ x, 0 ≤ V x)
    (U : Set X) (hU : IsOpen U) (hzero : ∀ x, V x = 0 → x ∈ U)
    (x : ℕ → X) (hx : Tendsto (fun n => V (x n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, x n ∈ U := by
  have hpositive : ∀ y ∈ Uᶜ, 0 < V y := by
    intro y hy
    have hne : V y ≠ 0 := fun h => hy (hzero y h)
    exact lt_of_le_of_ne (hVpos y) hne.symm
  obtain ⟨δ, hδ, hmin⟩ := hU.isClosed_compl.isCompact.exists_forall_le'
    hV.continuousOn hpositive
  have he : ∀ᶠ n in atTop, V (x n) < δ := hx.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with n hn
  by_contra hnot
  exact (not_le_of_gt hn) (hmin (x n) hnot)

/-- Contracting prefixes on the zero set extend, with a common margin, to an
open neighborhood of that set. -/
lemma zero_set_prefix_neighborhood {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (R : ℕ → X → ℝ) (hcont : ∀ n, Continuous (R n)) (hpos : ∀ n x, 0 ≤ R n x)
    (V : X → ℝ) (hV : Continuous V)
    (hboundary : ∀ x, V x = 0 → ∃ n : ℕ, 0 < n ∧ R n x < 1) :
    ∃ U : Set X, IsOpen U ∧ (∀ x, V x = 0 → x ∈ U) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
        ∀ x ∈ U, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ R j x ≤ q := by
  classical
  let Z := {x : X // V x = 0}
  by_cases hz : Nonempty Z
  · letI : Nonempty Z := hz
    have hclosed : IsClosed {x : X | V x = 0} := isClosed_eq hV continuous_const
    letI : CompactSpace Z := isCompact_iff_compactSpace.mp hclosed.isCompact
    obtain ⟨N, hN, q, hq, hq1, hpref⟩ := compact_uniform_prefix
      (fun n (z : Z) => R n z.val)
      (fun n => (hcont n).comp continuous_subtype_val)
      (fun n z => hpos n z.val) (fun z => hboundary z.val z.property)
    let q' := (q + 1) / 2
    have hqq' : q < q' := by dsimp [q']; linarith
    have hq' : 0 < q' := hq.trans hqq'
    have hq'1 : q' < 1 := by dsimp [q']; linarith
    let U : Set X := ⋃ j : {j : ℕ // 0 < j ∧ j ≤ N}, {x | R j.val x < q'}
    refine ⟨U, isOpen_iUnion (fun j => isOpen_lt (hcont j.val) continuous_const), ?_,
      N, hN, q', hq', hq'1, ?_⟩
    · intro x hx
      obtain ⟨j, hj, hjN, hjq⟩ := hpref ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hj, hjN⟩, hjq.trans_lt hqq'⟩
    · intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      change R j.val x < q' at hj
      exact ⟨j.val, j.property.1, j.property.2, hj.le⟩
  · refine ⟨∅, isOpen_empty, ?_, 1, by norm_num, 1 / 2, by norm_num, by norm_num, ?_⟩
    · intro x hx
      exact (hz ⟨⟨x, hx⟩⟩).elim
    · intro x hx
      exact hx.elim

/-- A continuous Lyapunov certificate contracts every state once its zero-set
boundary is known to have contracting prefixes. The state map need not be
continuous at terminal states. -/
lemma contracting_prefix_of_boundary_lyapunov {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (T : X → X) (R : ℕ → X → ℝ)
    (hzero : ∀ x, R 0 x = 1) (hcont : ∀ n, Continuous (R n))
    (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (V : X → ℝ) (hV : Continuous V) (hVpos : ∀ x, 0 ≤ V x)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlyap : ∀ n x, R n x ^ 2 * V (T^[n] x) ≤ θ ^ n * V x)
    (hboundary : ∀ x, V x = 0 → ∃ n : ℕ, 0 < n ∧ R n x < 1) :
    ∀ x, ∃ n : ℕ, 0 < n ∧ R n x < 1 := by
  intro x
  by_contra hnot
  have hge : ∀ n, 1 ≤ R n x := by
    intro n
    by_cases hn : n = 0
    · rw [hn, hzero x]
    · exact le_of_not_gt (fun hlt => hnot ⟨n, Nat.pos_of_ne_zero hn, hlt⟩)
  have hsmall : ∀ n, V (T^[n] x) ≤ θ ^ n * V x := by
    intro n
    have hs : (1 : ℝ) ≤ R n x ^ 2 := by nlinarith [hge n]
    have hh := mul_le_mul_of_nonneg_right hs (hVpos (T^[n] x))
    have hh' : V (T^[n] x) ≤ R n x ^ 2 * V (T^[n] x) := by
      simpa only [one_mul] using hh
    exact hh'.trans (hlyap n x)
  have hlimit : Tendsto (fun n => V (T^[n] x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hVpos (T^[n] x)) hsmall
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const (V x)
  obtain ⟨U, hU, hZU, N, _hN, q, hq, hq1, hUprefix⟩ :=
    zero_set_prefix_neighborhood R hcont hpos V hV hboundary
  have heU := eventually_mem_zero_neighborhood V hV hVpos U hU hZU
    (fun n => T^[n] x) hlimit
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp heU
  apply tail_relative_contraction_contradiction (fun n => R n x) N0 q hq hq1 hge
  intro n hn
  obtain ⟨j, hj, _hjN, hjq⟩ := hUprefix (T^[n] x) (hN0 n hn)
  refine ⟨n + j, by omega, ?_⟩
  change R (n + j) x ≤ q * R n x
  rw [hcocycle n j x]
  nlinarith [mul_le_mul_of_nonneg_left hjq (hpos n x)]

lemma compact_boundary_lyapunov_uniform_envelope {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (T : X → X) (R : ℕ → X → ℝ)
    (hzero : ∀ x, R 0 x = 1) (hcont : ∀ n, Continuous (R n))
    (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (V : X → ℝ) (hV : Continuous V) (hVpos : ∀ x, 0 ≤ V x)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlyap : ∀ n x, R n x ^ 2 * V (T^[n] x) ≤ θ ^ n * V x)
    (hboundary : ∀ x, V x = 0 → ∃ n : ℕ, 0 < n ∧ R n x < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      ∀ n x, R n x ≤ C * γ ^ n :=
  compact_cocycle_uniform_envelope T R hzero hcont hpos hcocycle
    (contracting_prefix_of_boundary_lyapunov T R hzero hcont hpos hcocycle
      V hV hVpos θ hθ hθ1 hlyap hboundary)

/-- Rescaling the cocycle turns a strict boundary rate and a Lyapunov rate below
`γ` into a uniform rate strictly below `γ`. The finite-dimensional face-induction
step can apply this lemma separately at each requested comparison factor. -/
lemma compact_boundary_lyapunov_improved_rate {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (T : X → X) (R : ℕ → X → ℝ)
    (hzero : ∀ x, R 0 x = 1) (hcont : ∀ n, Continuous (R n))
    (hpos : ∀ n x, 0 ≤ R n x)
    (hcocycle : ∀ m n x, R (m + n) x = R m x * R n (T^[m] x))
    (V : X → ℝ) (hV : Continuous V) (hVpos : ∀ x, 0 ≤ V x)
    (θ γ : ℝ) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hθγ : θ < γ ^ 2)
    (hlyap : ∀ n x, R n x ^ 2 * V (T^[n] x) ≤ θ ^ n * V x)
    (hboundary : ∀ x, V x = 0 → ∃ n : ℕ, 0 < n ∧ R n x < γ ^ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < γ ∧
      ∀ n x, R n x ≤ C * ρ ^ n := by
  let S : ℕ → X → ℝ := fun n x => R n x / γ ^ n
  have hSzero : ∀ x, S 0 x = 1 := by intro x; simp [S, hzero]
  have hScont : ∀ n, Continuous (S n) := by
    intro n
    exact (hcont n).div_const (γ ^ n)
  have hSpos : ∀ n x, 0 ≤ S n x := fun n x => div_nonneg (hpos n x) (pow_nonneg hγ.le n)
  have hScocycle : ∀ m n x, S (m + n) x = S m x * S n (T^[m] x) := by
    intro m n x
    dsimp only [S]
    rw [hcocycle, pow_add, div_mul_div_comm]
  have hθS : 0 ≤ θ / γ ^ 2 := div_nonneg hθ (sq_nonneg γ)
  have hθS1 : θ / γ ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hγ)).mpr hθγ
  have hSlyap : ∀ n x, S n x ^ 2 * V (T^[n] x) ≤ (θ / γ ^ 2) ^ n * V x := by
    intro n x
    have hden : (γ ^ n) ^ 2 = (γ ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    calc
      S n x ^ 2 * V (T^[n] x) = (R n x ^ 2 * V (T^[n] x)) / (γ ^ 2) ^ n := by
        dsimp only [S]
        rw [div_pow, div_mul_eq_mul_div, hden]
      _ ≤ (θ ^ n * V x) / (γ ^ 2) ^ n :=
        div_le_div_of_nonneg_right (hlyap n x) (pow_nonneg (sq_nonneg γ) n)
      _ = (θ / γ ^ 2) ^ n * V x := by rw [div_pow]; ring
  have hSboundary : ∀ x, V x = 0 → ∃ n : ℕ, 0 < n ∧ S n x < 1 := by
    intro x hx
    obtain ⟨n, hn, hRn⟩ := hboundary x hx
    exact ⟨n, hn, (div_lt_one (pow_pos hγ n)).mpr hRn⟩
  obtain ⟨C, hC, η, hη, hη1, henv⟩ :=
    compact_boundary_lyapunov_uniform_envelope T S hSzero hScont hSpos hScocycle
      V hV hVpos (θ / γ ^ 2) hθS hθS1 hSlyap hSboundary
  refine ⟨C, hC, γ * η, mul_pos hγ hη, ?_, ?_⟩
  · nlinarith
  · intro n x
    have hh : R n x ≤ (C * η ^ n) * γ ^ n :=
      (div_le_iff (pow_pos hγ n)).mp (henv n x)
    simpa only [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hh

/-- A finite first multiplier followed by a tail rate strictly below `γ`
produces a finite prefix contracting relative to `γ`. -/
lemma strict_prefix_of_tail_envelope {X : Type*} (r : X → ℝ) (T : X → X)
    (x : X) (hr : 0 ≤ r x) (C ρ γ : ℝ) (hρ : 0 ≤ ρ)
    (hγ : 0 < γ) (hργ : ρ < γ)
    (htail : ∀ n, prefixProduct r T n (T x) ≤ C * ρ ^ n) :
    ∃ n : ℕ, 0 < n ∧ prefixProduct r T n x < γ ^ n := by
  have hq0 : 0 ≤ ρ / γ := div_nonneg hρ hγ.le
  have hq1 : ρ / γ < 1 := (div_lt_one hγ).mpr hργ
  have hlim : Tendsto (fun n : ℕ => r x * C * (ρ / γ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (r x * C)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hγ)).exists
  have hdiv : (r x * C * ρ ^ n) / γ ^ n < γ := by
    simpa only [div_pow, mul_div_assoc] using hn
  have hlt := (div_lt_iff (pow_pos hγ n)).mp hdiv
  refine ⟨n + 1, by omega, ?_⟩
  rw [prefix_product_succ]
  calc
    r x * prefixProduct r T n (T x) ≤ r x * (C * ρ ^ n) :=
      mul_le_mul_of_nonneg_left (htail n) hr
    _ < γ ^ (n + 1) := by simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hlt

end BB
