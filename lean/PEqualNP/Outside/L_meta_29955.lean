import Mathlib
import PEqualNP.Defs

/- The harmonic loss decomposition and point-mask compiler are adapted from
   lean/PEqualNP/Outside/L_meta_29934.lean at f8f579373fe16a8f1b7ff705930503e9add28b9f. -/

namespace PEqualNP.Outside.L_meta_29955_aux

private def step {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (c : Fin s → Bool) (x : Option (Fin s)) : Option (Fin s) :=
  x.bind (fun j => n j (c j))

private def Stops {s : ℕ} (n : Fin s → Bool → Option (Fin s)) : Prop :=
  ∃ c, ∀ i, (step n c)^[s] (some i) = none

private def Harm {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (a : Fin s → Bool → ℝ) (v : Fin s → ℝ) : Prop :=
  ∀ i, 2 * v i = ∑ bit, (n i bit).elim (a i bit) v

private theorem harm_cmp {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    (hn : Stops n) {a b : Fin s → Bool → ℝ} {v w : Fin s → ℝ}
    (hv : Harm n a v) (hw : Harm n b w) (hab : ∀ i e, a i e ≤ b i e) (i : Fin s) :
    v i ≤ w i := by
  classical
  obtain ⟨c, hc⟩ := hn
  by_contra! hi
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun k => v k - w k)
    ⟨i, Finset.mem_univ i⟩
  let M := v j - w j
  have hM : 0 < M := (sub_pos.mpr hi).trans_le (hj i (Finset.mem_univ i))
  have hdiff : ∀ k, v k - w k ≤ M := fun k => hj k (Finset.mem_univ k)
  have hnext : ∀ k, v k - w k = M →
      ∃ l, n k (c k) = some l ∧ v l - w l = M := by
    intro k hk
    let A := fun e => (n k e).elim (a k e) v - (n k e).elim (b k e) w
    have hA : ∀ e, A e ≤ M := by
      intro e
      simp only [A]
      cases he : n k e with
      | none => exact (sub_nonpos.mpr (hab k e)).trans hM.le
      | some l => exact hdiff l
    have heq : A false + A true = 2 * M := by
      have hp := hv k
      have hq := hw k
      rw [Fintype.sum_bool] at hp hq
      dsimp [A]
      linarith
    have hsel : A (c k) = M := by
      have hF := hA false
      have hT := hA true
      cases c k <;> linarith
    cases hl : n k (c k) with
    | none =>
      simp only [A, hl, Option.elim_none] at hsel
      linarith [hab k (c k)]
    | some l => exact ⟨l, rfl, by simpa only [A, hl, Option.elim_some] using hsel⟩
  have hz (r : ℕ) : ∃ k, (step n c)^[r] (some j) = some k ∧ v k - w k = M := by
    induction r with
    | zero => exact ⟨j, rfl, rfl⟩
    | succ r ih =>
      obtain ⟨k, hk, hk'⟩ := ih
      obtain ⟨l, hl, hl'⟩ := hnext k hk'
      exact ⟨l, by rw [Function.iterate_succ_apply', hk]; exact hl, hl'⟩
  obtain ⟨k, hk, -⟩ := hz s
  rw [hc j] at hk
  contradiction

private theorem harm_const {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (a : ℝ) :
    Harm n (fun _ _ => a) (fun _ => a) := by
  intro i
  have h : ∀ e, (n i e).elim a (fun _ => a) = a := by
    intro e
    cases n i e <;> rfl
  rw [Fintype.sum_bool, h, h]
  ring

private theorem harm_sub {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {a b : Fin s → Bool → ℝ} {v w : Fin s → ℝ}
    (hv : Harm n a v) (hw : Harm n b w) :
    Harm n (fun i e => a i e - b i e) (fun i => v i - w i) := by
  intro i
  have h : ∀ e, (n i e).elim (a i e - b i e) (fun k => v k - w k) =
    (n i e).elim (a i e) v - (n i e).elim (b i e) w := by
    intro e
    cases n i e <;> rfl
  rw [Fintype.sum_bool, h, h]
  have hv' := hv i
  have hw' := hw i
  rw [Fintype.sum_bool] at hv' hw'
  linarith

private theorem harm_scale {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {a : Fin s → Bool → ℝ} {v : Fin s → ℝ} (hv : Harm n a v) (r : ℝ) :
    Harm n (fun i e => r * a i e) (fun i => r * v i) := by
  intro i
  have h : ∀ e, (n i e).elim (r * a i e) (fun k => r * v k) =
    r * (n i e).elim (a i e) v := by
    intro e
    cases n i e <;> rfl
  rw [Fintype.sum_bool, h, h]
  have hv' := hv i
  rw [Fintype.sum_bool] at hv'
  linear_combination r * hv'

private theorem harm_sum {s : ℕ} {n : Fin s → Bool → Option (Fin s)} {α : Type*}
    (D : Finset α) {a : α → Fin s → Bool → ℝ} {v : α → Fin s → ℝ}
    (hv : ∀ j ∈ D, Harm n (a j) (v j)) :
    Harm n (fun i e => ∑ j ∈ D, a j i e) (fun i => ∑ j ∈ D, v j i) := by
  intro i
  have h : ∀ e, (n i e).elim (∑ j ∈ D, a j i e) (fun k => ∑ j ∈ D, v j k) =
    ∑ j ∈ D, (n i e).elim (a j i e) (v j) := by
    intro e
    cases n i e <;> rfl
  rw [Fintype.sum_bool, h, h, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => by
    simpa only [Fintype.sum_bool] using hv j hj i

private theorem harm_unique {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    (hn : Stops n) {a : Fin s → Bool → ℝ} {v w : Fin s → ℝ}
    (hv : Harm n a v) (hw : Harm n a w) (i : Fin s) : v i = w i :=
  le_antisymm (harm_cmp hn hv hw (fun _ _ => le_rfl) i)
    (harm_cmp hn hw hv (fun _ _ => le_rfl) i)


private def edits {N : ℕ} (base H : Fin N → Fin N → Bool) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun z => H z.1 z.2 ≠ base z.1 z.2)

private def graph {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (j : Fin q) :
    Finset (Fin N × Fin N) :=
  Finset.univ.image (fun x => (x, f j x))

private theorem mem_graph {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (j : Fin q)
    (z : Fin N × Fin N) : z ∈ graph f j ↔ f j z.1 = z.2 := by
  simp only [graph, Finset.mem_image, Finset.mem_univ, true_and, Prod.eq_iff_fst_eq_snd_eq]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · exact fun h => ⟨z.1, rfl, h⟩

private theorem graph_disjoint {N q : ℕ} {f : Fin q → Equiv.Perm (Fin N)}
    (hf : ∀ x, Function.Injective (fun j => f j x)) {j k : Fin q} (hjk : j ≠ k) :
    Disjoint (graph f j) (graph f k) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hjk (hf z.1 ((mem_graph _ _ _).mp hz |>.trans ((mem_graph _ _ _).mp hz').symm))

private def flips {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (D : Finset (Fin q)) :
    Finset (Fin N × Fin N) := D.biUnion (graph f)

private theorem mem_flips {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (D : Finset (Fin q)) (z : Fin N × Fin N) :
    z ∈ flips f D ↔ z.2 ∈ D.image (fun j => f j z.1) := by
  simp only [flips, Finset.mem_biUnion, Finset.mem_image, mem_graph]

private theorem flips_card {N q : ℕ} {f : Fin q → Equiv.Perm (Fin N)}
    (hf : ∀ x, Function.Injective (fun j => f j x)) (D : Finset (Fin q)) :
    (flips f D).card = D.card * N := by
  rw [flips, Finset.card_biUnion (fun j _ k _ h => graph_disjoint hf h)]
  have h (j : Fin q) : (graph f j).card = N := by
    rw [graph, Finset.card_image_of_injective]
    · simp
    · intro x y hxy
      exact congrArg Prod.fst hxy
  simp [h]

private theorem inter_flips_card {N q : ℕ} {f : Fin q → Equiv.Perm (Fin N)}
    (hf : ∀ x, Function.Injective (fun j => f j x)) (D : Finset (Fin q))
    (A : Finset (Fin N × Fin N)) :
    (A ∩ flips f D).card = ∑ j ∈ D, (A ∩ graph f j).card := by
  rw [flips, Finset.inter_biUnion, Finset.card_biUnion]
  intro j _ k _ hjk
  exact (graph_disjoint hf hjk).mono Finset.inter_subset_right Finset.inter_subset_right

private def score {N q : ℕ} (base : Fin N → Fin N → Bool)
    (f : Fin q → Equiv.Perm (Fin N)) (H : Fin N → Fin N → Bool)
    (D : Finset (Fin q)) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠
    xor (base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card

private theorem score_decomp {N q : ℕ} {f : Fin q → Equiv.Perm (Fin N)}
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (base H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :
    (score base f H D : ℝ) =
      (D.card : ℝ) * N + (edits base H).card -
        2 * ∑ j ∈ D, ((edits base H ∩ graph f j).card : ℝ) := by
  let A := edits base H
  let B := flips f D
  have hfilter : (Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
    xor (base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))) = symmDiff A B := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff, A, B, edits,
      mem_flips]
    by_cases hb : z.2 ∈ D.image (fun j => f j z.1)
    all_goals cases H z.1 z.2 <;> cases base z.1 z.2 <;> simp [hb]
  have hAB : (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at h2
    have hd : Disjoint (A \ B) (B \ A) := by
      simp only [Finset.disjoint_left, Finset.mem_sdiff]
      tauto
    change ((A \ B) ∪ (B \ A)).card + _ = _
    rw [Finset.card_union_of_disjoint hd]
    omega
  have hab := congrArg (fun n : ℕ => (n : ℝ)) hAB
  push_cast at hab
  rw [show score base f H D = (symmDiff A B).card from congrArg Finset.card hfilter]
  rw [show B.card = D.card * N from flips_card hf D,
    show (A ∩ B).card = ∑ j ∈ D, (A ∩ graph f j).card from inter_flips_card hf D A] at hab
  push_cast at hab
  linarith

private theorem score_empty {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (base H : Fin N → Fin N → Bool) :
    score base f H ∅ = (edits base H).card := by
  simp [score, edits]

-- The cyclic averaging identity is adapted from
-- e93061bdf8cf33267c6155ab2dc1be6528a5e618:lean/PEqualNP/Outside/L_meta_26025.lean.
private theorem orbit_sum {q : ℕ} [NeZero q] (D : Finset (Fin q)) (F : Fin q → ℝ) :
    ∑ k : Fin q, ∑ j ∈ D.image (fun j => j + k), F j = (D.card : ℝ) * ∑ j, F j := by
  have h' : ∀ k : Fin q,
      ∑ j ∈ D.image (fun j => j + k), F j = ∑ j ∈ D, F (j + k) := fun k =>
    Finset.sum_image (fun x _ y _ he => add_right_cancel he)
  simp_rw [h']
  rw [Finset.sum_comm]
  have h : ∀ j : Fin q, ∑ k : Fin q, F (j + k) = ∑ k, F k := fun j =>
    Equiv.sum_comp (Equiv.addLeft j) F
  simp_rw [h]
  simp [nsmul_eq_mul]

private theorem uniform_of_optimal {q E t : ℕ} [NeZero q] (ht : t < q)
    (htq : q < 2*t) (A : Fin q → ℝ) (V : ℝ)
    (hV : V ≤ E) (hA : (∑ j, A j) ≤ V)
    (hO : ∀ D : Finset (Fin q), D.card = t →
      V - 2 * ∑ j ∈ D, A j ≤ (1 - 2*(t : ℝ)/q)*E) :
    V = E ∧ ∀ j, A j = (E : ℝ)/q := by
  classical
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ht₀ : 0 < t := by omega
  have htreal : 0 < (t : ℝ) := by exact_mod_cast ht₀
  have hgap : 0 < 2*(t : ℝ) - q := by
    apply sub_pos.mpr
    exact_mod_cast htq
  let Sum := ∑ j, A j
  let M := (1 - 2*(t : ℝ)/q)*E
  let T := fun (D : Finset (Fin q)) => V - 2*∑ j ∈ D, A j
  have hcard (D : Finset (Fin q)) (k : Fin q) :
      (D.image (fun j => j + k)).card = D.card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  have horbit (D : Finset (Fin q)) (hD : D.card = t) :
      ∑ k : Fin q, T (D.image (fun j => j + k)) = q*V - 2*t*Sum := by
    simp only [T, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, orbit_sum, hD, Sum]
    ring
  obtain ⟨D₀, -, hD₀⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin q))) (n := t) (by simpa using ht.le)
  have havg : q*V - 2*t*Sum ≤ q*M := by
    rw [← horbit D₀ hD₀]
    calc
      _ ≤ ∑ _ : Fin q, M := Finset.sum_le_sum fun k _ =>
        hO (D₀.image (fun j => j + k)) ((hcard D₀ k).trans hD₀)
      _ = _ := by simp [nsmul_eq_mul]
  have hM : (q : ℝ)*M = (q - 2*t)*E := by
    dsimp [M]
    field_simp
  rw [hM] at havg
  change Sum ≤ V at hA
  have hVE : V = E := by
    by_contra hne
    have hstrict := mul_pos hgap (sub_pos.mpr (lt_of_le_of_ne hV hne))
    nlinarith [mul_nonneg htreal.le (sub_nonneg.mpr hA)]
  have hSE : Sum = E := by
    rw [hVE] at hA havg
    nlinarith [mul_nonneg htreal.le (sub_nonneg.mpr hA)]
  have htight (D : Finset (Fin q)) (hD : D.card = t) : T D = M := by
    have hS : ∑ k : Fin q, T (D.image (fun j => j + k)) = ∑ _ : Fin q, M := by
      rw [horbit D hD, hVE, hSE, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hM]
      ring
    have heach := (Finset.sum_eq_sum_iff_of_le
      (fun (k : Fin q) (_ : k ∈ Finset.univ) =>
        hO (D.image (fun j => j + k)) ((hcard D k).trans hD))).mp hS
    have := heach 0 (Finset.mem_univ _)
    simpa using this
  have hequal (j k : Fin q) : A j = A k := by
    by_cases he : j = k
    · rw [he]
    let S := ((Finset.univ : Finset (Fin q)).erase j).erase k
    have hkj : k ∈ (Finset.univ : Finset (Fin q)).erase j := by simp [Ne.symm he]
    have hS : S.card = q - 2 := by
      simp [S, Finset.card_erase_of_mem hkj, Finset.card_erase_of_mem (Finset.mem_univ j)]
      omega
    obtain ⟨U, hUS, hU⟩ := Finset.exists_subset_card_eq (s := S) (n := t-1) (by omega)
    have hjU : j ∉ U := fun hj => by simpa [S] using hUS hj
    have hkU : k ∉ U := fun hk => by simpa [S] using hUS hk
    have h1 := htight (insert j U) (by rw [Finset.card_insert_of_notMem hjU, hU]; omega)
    have h2 := htight (insert k U) (by rw [Finset.card_insert_of_notMem hkU, hU]; omega)
    simp only [T, Finset.sum_insert hjU, Finset.sum_insert hkU] at h1 h2
    linarith
  refine ⟨hVE, fun j => (eq_div_iff (ne_of_gt hq)).2 ?_⟩
  have h := hSE
  simp only [Sum, hequal _ j, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  linarith

private theorem harm_add {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {a b : Fin s → Bool → ℝ} {v w : Fin s → ℝ}
    (hv : Harm n a v) (hw : Harm n b w) :
    Harm n (fun i e => a i e + b i e) (fun i => v i + w i) := by
  simpa [sub_eq_add_neg] using harm_sub hv (harm_scale hw (-1))

private theorem ideal_eq {q N t E : ℕ} (hq : 0 < q) (ht : t < q)
    (htq : q ≤ 2*t) (hN : q ≤ N) (hE : E < q) :
    (((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) =
      (N : ℝ)*t + (1-2*(t : ℝ)/q)*E := by
  have hle : (2*t-q)*E ≤ q*N*t := calc
    _ ≤ t * E := Nat.mul_le_mul_right _ (by omega)
    _ ≤ t * N := Nat.mul_le_mul_left _ (hE.le.trans hN)
    _ = 1 * (N*t) := by ring
    _ ≤ q * (N*t) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_mul, Nat.cast_sub htq, Nat.cast_ofNat]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

private theorem optimal_harm {N q E t s : ℕ} [NeZero q]
    {f : Fin q → Equiv.Perm (Fin N)} (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Fin N → Fin N → Bool) (H : Fin s → Bool → Fin N → Fin N → Bool)
    (L : Fin s → Finset (Fin q) → ℝ) {n : Fin s → Bool → Option (Fin s)}
    (z : Fin s) (hn : Stops n)
    (hl : ∀ D, Harm n (fun i e => (score base f (H i e) D : ℝ)) (fun i => L i D))
    (hE : ∀ i e, score base f (H i e) ∅ ≤ E)
    (ht : t < q) (htq : q < 2*t) (hO : ∀ D : Finset (Fin q), D.card = t →
      L z D ≤ (N : ℝ)*t + (1 - 2*(t : ℝ)/q)*E) :
    ∃ A : Fin q → Fin s → ℝ,
      (∀ j, Harm n (fun i e => ((edits base (H i e) ∩ graph f j).card : ℝ)) (A j)) ∧
      (∀ j i, 0 ≤ A j i) ∧ (∀ i, (∑ j, A j i) ≤ E) ∧
      ∀ j, A j z = (E : ℝ)/q := by
  let T := fun i e => edits base (H i e)
  let B := fun (j : Fin q) i e => ((T i e ∩ graph f j).card : ℝ)
  let A := fun (j : Fin q) i => (N + L i ∅ - L i {j})/2
  let V := fun i => L i ∅
  have hv : Harm n (fun i e => ((T i e).card : ℝ)) V := by
    simpa only [T, V, score_empty] using hl ∅
  have hterm : ∀ i e, (T i e).card ≤ E := fun i e => by
    simpa only [T, score_empty] using hE i e
  have ha (j : Fin q) : Harm n (B j) (A j) := by
    have hh := harm_scale (harm_sub (harm_add (harm_const n (N : ℝ)) hv) (hl {j})) (1/2)
    convert hh using 1
    · funext i e
      rw [score_decomp hf]
      simp only [Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton]
      simp only [B, T]
      ring
    · funext i
      dsimp [A, V]
      ring
  have hsum (D : Finset (Fin q)) :
      Harm n (fun i e => ∑ j ∈ D, B j i e) (fun i => ∑ j ∈ D, A j i) :=
    harm_sum D (fun j _ => ha j)
  have hL (i : Fin s) (D : Finset (Fin q)) :
      L i D = (D.card : ℝ)*N + V i - 2*∑ j ∈ D, A j i := by
    have hh := harm_sub (harm_add (harm_const n ((D.card : ℝ)*N)) hv) (harm_scale (hsum D) 2)
    have hh' : Harm n (fun i e => (score base f (H i e) D : ℝ))
        (fun i => (D.card : ℝ)*N + V i - 2*∑ j ∈ D, A j i) := by
      convert hh using 1
      funext i e
      exact score_decomp hf _ _ _
    exact harm_unique hn (hl D) hh' i
  have hV (i : Fin s) : V i ≤ E :=
    harm_cmp hn hv (harm_const n E) (fun j e => by exact_mod_cast hterm j e) i
  have hA (i : Fin s) : (∑ j, A j i) ≤ V i := by
    apply harm_cmp hn (hsum Finset.univ) hv _ i
    intro j e
    have hh := inter_flips_card hf Finset.univ (T j e)
    simp only [B]
    have hs₀ : (T j e ∩ flips f Finset.univ).card ≤ (T j e).card :=
      Finset.card_le_card Finset.inter_subset_left
    rw [hh] at hs₀
    exact_mod_cast hs₀
  have ho (D : Finset (Fin q)) (hD : D.card = t) :
      V z - 2*∑ j ∈ D, A j z ≤ (1 - 2*(t : ℝ)/q)*E := by
    have hh := hO D hD
    rw [hL, hD] at hh
    linarith
  have hnon (j : Fin q) (i : Fin s) : 0 ≤ A j i := by
    apply harm_cmp hn (harm_const n 0) (ha j) _ i
    intro k e
    exact Nat.cast_nonneg _
  refine ⟨A, ha, hnon, fun i => (hA i).trans (hV i), ?_⟩
  exact (uniform_of_optimal ht htq (fun j => A j z) (V z) (hV z) (hA z) ho).2


private theorem hist_edits {N q E : ℕ} {f : Fin q → Equiv.Perm (Fin N)}
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (a : Fin q → ℕ) (ha : ∑ j, a j = E) (hEN : E ≤ N) :
    ∃ T : Finset (Fin N × Fin N), T.card = E ∧
      ∀ j, (T ∩ graph f j).card = a j := by
  classical
  have hcap (j : Fin q) : a j ≤ N :=
    (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (ha.le.trans hEN)
  let e (j : Fin q) : Fin (a j) ↪ (Fin N × Fin N) :=
    ⟨fun x => (Fin.castLE (hcap j) x, f j (Fin.castLE (hcap j) x)),
      fun x y he => Fin.ext (congrArg (fun z : Fin N × Fin N => z.1.val) he)⟩
  let S (j : Fin q) : Finset (Fin N × Fin N) := Finset.univ.map (e j)
  let T := Finset.univ.biUnion S
  have hsub (j : Fin q) : S j ⊆ graph f j := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
    exact (mem_graph _ _ _).mpr rfl
  have hcard (j : Fin q) : (S j).card = a j := by simp [S]
  have hpart (j : Fin q) : T ∩ graph f j = S j := by
    ext z
    constructor
    · intro hz
      obtain ⟨hT, hj⟩ := Finset.mem_inter.mp hz
      obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hT
      have hkj : k = j := by
        by_contra hn
        exact Finset.disjoint_left.mp (graph_disjoint hf hn) (hsub k hk) hj
      rwa [hkj] at hk
    · intro hz
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hz⟩,
        hsub j hz⟩
  refine ⟨T, ?_, fun j => by rw [hpart j, hcard j]⟩
  rw [show T = Finset.univ.biUnion S from rfl, Finset.card_biUnion]
  · simpa only [hcard] using ha
  · intro i _ j _ hij
    exact (graph_disjoint hf hij).mono (hsub i) (hsub j)

private theorem edits_mask {N : ℕ} (base H : Fin N → Fin N → Bool)
    (S : Finset (Fin N × Fin N))
    (h : ∀ x y, H x y = xor (base x y) (decide ((x,y) ∈ S))) :
    edits base H = S := by
  ext z
  rw [edits, Finset.mem_filter, h z.1 z.2]
  have hu : z ∈ (Finset.univ : Finset (Fin N × Fin N)) := Finset.mem_univ _
  by_cases hz : z ∈ S <;> cases base z.1 z.2 <;> simp [hz, hu]

private theorem optimum_from_hist {N q E t s : ℕ} (_hq : 0 < q)
    {f : Fin q → Equiv.Perm (Fin N)} (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Fin N → Fin N → Bool) (H : Fin s → Bool → Fin N → Fin N → Bool)
    (a : Fin q → Fin s → Bool → ℕ) (v : Fin q → Fin s → ℝ)
    {n : Fin s → Bool → Option (Fin s)} (z : Fin s)
    (hcard : ∀ i e, (edits base (H i e)).card = E)
    (hpart : ∀ j i e, (edits base (H i e) ∩ graph f j).card = a j i e)
    (hh : ∀ j, Harm n (fun i e => (a j i e : ℝ)) (v j))
    (hroot : ∀ j, v j z = (E : ℝ)/q) :
    ∃ L : Fin s → Finset (Fin q) → ℝ,
      (∀ D, Harm n (fun i e => (score base f (H i e) D : ℝ)) (fun i => L i D)) ∧
      ∀ D, D.card = t → L z D = (N : ℝ)*t + (1-2*(t : ℝ)/q)*E := by
  let L := fun i (D : Finset (Fin q)) => (D.card : ℝ)*N + E - 2*∑ j ∈ D, v j i
  refine ⟨L, ?_, ?_⟩
  · intro D
    have hv := harm_sum D (fun j _ => hh j)
    have hh' := harm_sub (harm_const n ((D.card : ℝ)*N + E)) (harm_scale hv 2)
    convert hh' using 1
    funext i e
    simp only [score_decomp hf, hcard, hpart]
  · intro D hD
    simp only [L, hroot, Finset.sum_const, hD, nsmul_eq_mul]
    ring

private theorem harm_exists {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    (hn : Stops n) (a : Fin s → Bool → ℝ) : ∃ v, Harm n a v := by
  let g (v : Fin s → ℝ) (i : Fin s) (e : Bool) := (n i e).elim 0 v
  have hadd (u v : Fin s → ℝ) (i : Fin s) (e : Bool) :
      g (u + v) i e = g u i e + g v i e := by
    cases he : n i e <;> simp [g, he]
  have hsmul (r : ℝ) (u : Fin s → ℝ) (i : Fin s) (e : Bool) :
      g (r • u) i e = r*g u i e := by
    cases he : n i e <;> simp [g, he]
  let F : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    { toFun := fun v i => 2 * v i - (g v i true + g v i false)
      map_add' := by
        intro u v
        ext i
        simp only [Pi.add_apply, hadd]
        ring
      map_smul' := by
        intro r u
        ext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, hsmul]
        ring }
  have hF (u : Fin s → ℝ) (i : Fin s) :
      F u i = 2 * u i - (g u i true + g u i false) := rfl
  have hker : ∀ u, F u = 0 → u = 0 := by
    intro u hu
    have hH : Harm n (fun _ _ => 0) u := by
      intro i
      have h := congrFun hu i
      rw [hF, Pi.zero_apply] at h
      rw [Fintype.sum_bool]
      exact sub_eq_zero.mp h
    funext i
    exact harm_unique hn hH (harm_const n 0) i
  have hFj : Function.Injective F := by
    intro u v he
    apply sub_eq_zero.mp
    exact hker (u-v) (by rw [map_sub, he, sub_self])
  let exit (i : Fin s) (e : Bool) : ℝ := (n i e).elim (a i e) (fun _ => 0)
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hFj) (fun i => exit i true + exit i false)
  refine ⟨v, fun i => ?_⟩
  have h := congrFun hv i
  rw [hF] at h
  have hp (e : Bool) : (n i e).elim (a i e) v = exit i e + g v i e := by
    cases he : n i e <;> simp [exit, g, he]
  rw [Fintype.sum_bool, hp, hp]
  linarith

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev MaskLegal (n : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧ C.output < n + C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

abbrev MaskTable {N : ℕ} (C : Circuit) (x y : Fin N) : Bool :=
  C.eval (PEqualNP.Represents.oneEach x y)

private def maskStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem maskFold_length (gs : List Gate) (z : List Bool) :
    (gs.foldl maskStep z).length = z.length + gs.length := by
  induction gs generalizing z with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons, ih, maskStep, List.length_append, List.length_cons,
        List.length_nil] <;> omega

private theorem maskFold_prefix (gs : List Gate) (z : List Bool) :
    z <+: gs.foldl maskStep z := by
  induction gs generalizing z with
  | nil => exact List.prefix_rfl
  | cons g gs ih =>
      rw [List.foldl_cons]
      exact (show z <+: maskStep z g from List.prefix_append _ _).trans (ih _)

private theorem maskGetD_prefix {a b : List Bool} (h : a <+: b) {i : ℕ}
    (hi : i < a.length) : b.getD i false = a.getD i false := by
  obtain ⟨tail, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

private theorem maskPrefix_wire {n : ℕ} {C D : Circuit} (hp : C.gates <+: D.gates)
    {z : List Bool} (hz : z.length = n) {i : ℕ} (hi : i < n + C.size) :
    (D.wires z).getD i false = (C.wires z).getD i false := by
  apply maskGetD_prefix
  · obtain ⟨tail, ht⟩ := hp
    change C.gates.foldl maskStep z <+: D.gates.foldl maskStep z
    rw [← ht, List.foldl_append]
    exact maskFold_prefix _ _
  · change i < (C.gates.foldl maskStep z).length
    rw [maskFold_length, hz]
    exact hi

private theorem maskPrefix_bound {n i : ℕ} {C D : Circuit}
    (hp : C.gates <+: D.gates) (hi : i < n + C.size) : i < n + D.size :=
  lt_of_lt_of_le hi (Nat.add_le_add_left hp.length_le n)

private theorem maskEmit_gate {n : ℕ} {C : Circuit} (hC : MaskLegal n C) (g : Gate)
    (hg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hread : ∀ i ∈ g.inputs, i < n + C.size) :
    ∃ D : Circuit, MaskLegal n D ∧ C.gates <+: D.gates ∧ D.size = C.size + 1 ∧
      ∀ z : List Bool, z.length = n →
        D.eval z = g.op.eval (g.inputs.map fun i => (C.wires z).getD i false) := by
  let D : Circuit := ⟨C.gates ++ [g], n + C.size⟩
  have hs : D.size = C.size + 1 := by simp [D, Circuit.size]
  refine ⟨D, ⟨?_, ?_, ?_⟩, List.prefix_append _ _, hs, ?_⟩
  · intro j hj i hi
    change j < (C.gates ++ [g]).length at hj
    change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hC.1 j hj' i hi
    · have heq : j = C.gates.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp at hi
      exact hread i hi
  · change n + C.size < n + D.size
    omega
  · intro a ha
    change a ∈ C.gates ++ [g] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hC.2.2 a ha
    · have he : a = g := List.mem_singleton.mp ha
      subst a
      exact hg
  · intro z hz
    have hl : (C.wires z).length = n + C.size := by
      change (C.gates.foldl maskStep z).length = _
      simp only [maskFold_length, hz, Circuit.size]
    have hw : D.wires z = maskStep (C.wires z) g := by
      change (C.gates ++ [g]).foldl maskStep z = maskStep (C.gates.foldl maskStep z) g
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (D.wires z).getD (n + C.size) false = _
    rw [hw, maskStep, ← hl, List.getD_append_right _ _ _ _ le_rfl] <;> simp

private theorem maskBinary_reads {k a b : ℕ} (ha : a < k) (hb : b < k) :
    ∀ i ∈ [a, b], i < k := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ha
  · exact hb

private theorem maskEmit_and {n a b : ℕ} {C : Circuit}
    (hC : MaskLegal n C) (ha : a < n + C.size) (hb : b < n + C.size) :
    ∃ D : Circuit, MaskLegal n D ∧ C.gates <+: D.gates ∧ D.size = C.size + 1 ∧
      ∀ z : List Bool, z.length = n →
        D.eval z = ((C.wires z).getD a false && (C.wires z).getD b false) := by
  obtain ⟨D, hD, hp, hs, he⟩ :=
    maskEmit_gate hC ⟨.and, [a, b]⟩ (by simp) (maskBinary_reads ha hb)
  exact ⟨D, hD, hp, hs, fun z hz => by simpa [GateOp.eval] using he z hz⟩

private theorem maskEmit_or {n a b : ℕ} {C : Circuit}
    (hC : MaskLegal n C) (ha : a < n + C.size) (hb : b < n + C.size) :
    ∃ D : Circuit, MaskLegal n D ∧ C.gates <+: D.gates ∧ D.size = C.size + 1 ∧
      ∀ z : List Bool, z.length = n →
        D.eval z = ((C.wires z).getD a false || (C.wires z).getD b false) := by
  obtain ⟨D, hD, hp, hs, he⟩ :=
    maskEmit_gate hC ⟨.or, [a, b]⟩ (by simp) (maskBinary_reads ha hb)
  exact ⟨D, hD, hp, hs, fun z hz => by simpa [GateOp.eval] using he z hz⟩

private theorem maskEmit_not {n a : ℕ} {C : Circuit}
    (hC : MaskLegal n C) (ha : a < n + C.size) :
    ∃ D : Circuit, MaskLegal n D ∧ C.gates <+: D.gates ∧ D.size = C.size + 1 ∧
      ∀ z : List Bool, z.length = n → D.eval z = !((C.wires z).getD a false) := by
  have hr : ∀ i ∈ [a], i < n + C.size := by
    intro i hi
    simpa [List.mem_singleton.mp hi] using ha
  obtain ⟨D, hD, hp, hs, he⟩ := maskEmit_gate hC ⟨.not, [a]⟩ (by simp) hr
  exact ⟨D, hD, hp, hs, fun z hz => by simpa [GateOp.eval] using he z hz⟩

private theorem maskEmit_xor {n a b : ℕ} {C : Circuit}
    (hC : MaskLegal n C) (ha : a < n + C.size) (hb : b < n + C.size) :
    ∃ D : Circuit, MaskLegal n D ∧ C.gates <+: D.gates ∧ D.size = C.size + 4 ∧
      ∀ z : List Bool, z.length = n →
        D.eval z = xor ((C.wires z).getD a false) ((C.wires z).getD b false) := by
  obtain ⟨A, hA, hCA, hsA, heA⟩ := maskEmit_and hC ha hb
  obtain ⟨B, hB, hAB, hsB, heB⟩ := maskEmit_not hA hA.2.1
  have hCB := hCA.trans hAB
  obtain ⟨O, hO, hBO, hsO, heO⟩ :=
    maskEmit_or hB (maskPrefix_bound hCB ha) (maskPrefix_bound hCB hb)
  obtain ⟨D, hD, hOD, hsD, heD⟩ := maskEmit_and hO (maskPrefix_bound hBO hB.2.1) hO.2.1
  refine ⟨D, hD, hCB.trans (hBO.trans hOD), by omega, ?_⟩
  intro z hz
  rw [heD z hz, maskPrefix_wire hBO hz hB.2.1]
  change (B.eval z && O.eval z) = _
  rw [heB z hz, heO z hz, maskPrefix_wire hCB hz ha, maskPrefix_wire hCB hz hb]
  change (!(A.eval z) && ((C.wires z).getD a false || (C.wires z).getD b false)) = _
  rw [heA z hz]
  cases (C.wires z).getD a false <;> cases (C.wires z).getD b false <;> rfl

private theorem maskOneEach_length {N : ℕ} (x y : Fin N) :
    (PEqualNP.Represents.oneEach x y).length = N + N := by
  simp [PEqualNP.Represents.oneEach]

private theorem maskOneEach_left {N : ℕ} (C : Circuit) (x y a : Fin N) :
    (C.wires (PEqualNP.Represents.oneEach x y)).getD a.val false = decide (a = x) := by
  rw [maskGetD_prefix (show PEqualNP.Represents.oneEach x y <+:
      C.wires (PEqualNP.Represents.oneEach x y) from maskFold_prefix _ _)
      (by rw [maskOneEach_length]; exact a.isLt.trans_le (Nat.le_add_right _ _))]
  rw [PEqualNP.Represents.oneEach, List.getD_append _ _ _ _ (by simpa using a.isLt),
    List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp only [List.getElem_ofFn]

private theorem maskOneEach_right {N : ℕ} (C : Circuit) (x y b : Fin N) :
    (C.wires (PEqualNP.Represents.oneEach x y)).getD (N + b.val) false = decide (b = y) := by
  rw [maskGetD_prefix (show PEqualNP.Represents.oneEach x y <+:
      C.wires (PEqualNP.Represents.oneEach x y) from maskFold_prefix _ _)
      (by rw [maskOneEach_length]; exact Nat.add_lt_add_left b.isLt _)]
  rw [PEqualNP.Represents.oneEach, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using b.isLt)]
  simp only [List.getElem_ofFn]

private theorem maskEmit_point {N : ℕ} {C : Circuit} (hC : MaskLegal (N + N) C)
    (p : Fin N × Fin N) :
    ∃ D : Circuit, MaskLegal (N + N) D ∧ C.gates <+: D.gates ∧ D.size = C.size + 1 ∧
      ∀ x y, MaskTable D x y = decide ((x, y) = p) := by
  have ha : p.1.val < N + N + C.size := by have := p.1.isLt; omega
  have hb : N + p.2.val < N + N + C.size := by have := p.2.isLt; omega
  obtain ⟨D, hD, hp, hs, he⟩ := maskEmit_and hC ha hb
  refine ⟨D, hD, hp, hs, fun x y => ?_⟩
  change D.eval (PEqualNP.Represents.oneEach x y) = _
  rw [he _ (maskOneEach_length x y), maskOneEach_left, maskOneEach_right]
  cases p
  simp [Prod.ext_iff, eq_comm]

private theorem maskEmit_points {N : ℕ} {base : Circuit} (hbase : MaskLegal (N + N) base)
    (S : Finset (Fin N × Fin N)) (hS : S.Nonempty) :
    ∃ M : Circuit, MaskLegal (N + N) M ∧ base.gates <+: M.gates ∧
      M.size + 1 = base.size + 2 * S.card ∧
      ∀ x y, MaskTable M x y = decide ((x, y) ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert p S hp ih =>
      by_cases h0 : S = ∅
      · subst S
        obtain ⟨D, hD, hpre, hs, he⟩ := maskEmit_point hbase p
        refine ⟨D, hD, hpre, by simp [hs, Nat.add_assoc], ?_⟩
        intro x y
        simpa only [Finset.insert_empty, Finset.mem_singleton] using he x y
      · obtain ⟨C, hC, hpre, hs, he⟩ := ih (Finset.nonempty_iff_ne_empty.mpr h0)
        obtain ⟨D, hD, hCD, hsD, heD⟩ := maskEmit_point hC p
        obtain ⟨F, hF, hDF, hsF, heF⟩ :=
          maskEmit_or hD hD.2.1 (maskPrefix_bound hCD hC.2.1)
        refine ⟨F, hF, hpre.trans (hCD.trans hDF), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hp]
          omega
        · intro x y
          let z := PEqualNP.Represents.oneEach x y
          have hz : z.length = N + N := maskOneEach_length x y
          have h := heF z hz
          rw [maskPrefix_wire hCD hz hC.2.1] at h
          change MaskTable F x y = (MaskTable D x y || MaskTable C x y) at h
          rw [h, heD x y, he x y]
          by_cases hEq : (x, y) = p <;> by_cases hMem : (x, y) ∈ S <;>
            simp [Finset.mem_insert, hEq, hMem]

/-- Append a membership mask and XOR it with the original circuit's output. -/
theorem compilePointMask {N : ℕ} (base : Circuit) (hbase : MaskLegal (N + N) base)
    (S : Finset (Fin N × Fin N)) (hS : S.Nonempty) :
    ∃ C : Circuit, MaskLegal (N + N) C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size + 2 * S.card + 3 ∧
      ∀ x y, MaskTable C x y = xor (MaskTable base x y) (decide ((x, y) ∈ S)) := by
  obtain ⟨M, hM, hpre, hs, he⟩ := maskEmit_points hbase S hS
  obtain ⟨C, hC, hMC, hsC, heC⟩ :=
    maskEmit_xor hM (maskPrefix_bound hpre hbase.2.1) hM.2.1
  refine ⟨C, hC, ?_, by omega, ?_⟩
  · obtain ⟨tail, ht⟩ := hpre.trans hMC
    rw [← ht]
    exact List.take_left
  · intro x y
    let z := PEqualNP.Represents.oneEach x y
    have hz : z.length = N + N := maskOneEach_length x y
    have h := heC z hz
    rw [maskPrefix_wire hpre hz hbase.2.1] at h
    change MaskTable C x y = xor (MaskTable base x y) (MaskTable M x y) at h
    rwa [he x y] at h

private theorem realize_from_machine {N q E t s : ℕ} (hq : 0 < q) (hE : 0 < E)
    (hEq : E < q) (hN : q ≤ N) (ht : t < q) (htq : q < 2*t)
    (base : PEqualNP.CircuitLowerBounds.Circuit) (hbase : MaskLegal (N+N) base)
    {f : Fin q → Equiv.Perm (Fin N)} (hf : ∀ x, Function.Injective (fun j => f j x))
    {z : Fin s} {n : Fin s → Bool → Option (Fin s)} (hn : Stops n)
    (a : Fin q → Fin s → Bool → ℕ) (v : Fin q → Fin s → ℝ)
    (ha : ∀ i e, ∑ j, a j i e = E)
    (hh : ∀ j, Harm n (fun i e => (a j i e : ℝ)) (v j))
    (hroot : ∀ j, v j z = (E : ℝ)/q) :
    ∃ (C : Fin s → Bool → PEqualNP.CircuitLowerBounds.Circuit) (L : Fin s → Finset (Fin q) → ℝ),
      (∀ D, Harm n (fun i e => (score (MaskTable base) f (MaskTable (C i e)) D : ℝ))
        (fun i => L i D)) ∧
      (∀ i bit, MaskLegal (N+N) (C i bit) ∧ (C i bit).gates.take base.size = base.gates ∧
        (C i bit).size ≤ base.size+2*E+3 ∧ score (MaskTable base) f (MaskTable (C i bit)) ∅ ≤ E) ∧
      (∀ U : Finset (Fin q), U.card = t →
        L z U = ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) := by
  classical
  have he (i : Fin s) (e : Bool) := hist_edits hf (fun j => a j i e) (ha i e) (hEq.le.trans hN)
  choose T hT hpart using he
  have hne (i : Fin s) (e : Bool) : (T i e).Nonempty :=
    Finset.card_pos.mp ((hT i e).symm ▸ hE)
  have hC (i : Fin s) (e : Bool) := compilePointMask base hbase (T i e) (hne i e)
  choose C hleg hpre hsize htable using hC
  have hmask (i : Fin s) (e : Bool) : edits (MaskTable base) (MaskTable (C i e)) = T i e :=
    edits_mask _ _ _ (htable i e)
  obtain ⟨L, hL, hO⟩ := optimum_from_hist hq hf (MaskTable base) (fun i e => MaskTable (C i e))
    a v z (fun i e => (congrArg Finset.card (hmask i e)).trans (hT i e))
    (fun j i e => by rw [hmask]; exact hpart i e j) hh hroot
  refine ⟨C, L, hL, ?_, ?_⟩
  · intro i e
    refine ⟨hleg i e, hpre i e, ?_, ?_⟩
    · simpa only [hT i e] using hsize i e
    · rw [score_empty, hmask, hT i e]
  · intro U hU
    rw [hO U hU, ideal_eq hq ht htq.le hN hEq]

open scoped BigOperators


private def runWord {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (x : Option (Fin s)) (w : List Bool) : Option (Fin s) :=
  w.foldl (fun x bit => x.bind (fun i => n i bit)) x

private def Reach {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (z i : Fin s) : Prop := ∃ w : List Bool, runWord n (some z) w = some i

private theorem reach_next {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {z i k : Fin s} {bit : Bool} (hi : Reach n z i) (hk : n i bit = some k) :
    Reach n z k := by
  obtain ⟨w, hw⟩ := hi
  refine ⟨w ++ [bit], ?_⟩
  unfold runWord at hw ⊢
  simp [List.foldl_append, hw, hk]

private noncomputable def exits {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (z : Fin s) : Finset (Fin s × Bool) := by
  classical
  exact Finset.univ.filter (fun e => Reach n z e.1 ∧ n e.1 e.2 = none)

private theorem mem_exits {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {z : Fin s} {e : Fin s × Bool} :
    e ∈ exits n z ↔ Reach n z e.1 ∧ n e.1 e.2 = none := by
  classical
  simp [exits]

-- The maximum principle only needs an inequality on exits visible from the root.
private theorem harm_cmp_reachable {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    (z : Fin s) (hn : Stops n) {a b : Fin s → Bool → ℝ} {v w : Fin s → ℝ}
    (hv : Harm n a v) (hw : Harm n b w)
    (hle : ∀ i e, (i,e) ∈ exits n z → a i e ≤ b i e) : v z ≤ w z := by
  classical
  obtain ⟨c, hc⟩ := hn
  by_contra! hz
  let K := Finset.univ.filter (Reach n z)
  have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ z, ⟨[], rfl⟩⟩
  obtain ⟨j, hjK, hj⟩ := Finset.exists_max_image K (fun k => v k - w k) ⟨z, hzK⟩
  let M := v j - w j
  have hM : 0 < M := (sub_pos.mpr hz).trans_le (hj z hzK)
  have hdiff (k : Fin s) (hk : Reach n z k) : v k - w k ≤ M :=
    hj k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
  have hnext (k : Fin s) (hk : Reach n z k) (hV : v k - w k = M) :
      ∃ l, n k (c k) = some l ∧ Reach n z l ∧ v l - w l = M := by
    let A := fun e => (n k e).elim (a k e) v - (n k e).elim (b k e) w
    have hA (e : Bool) : A e ≤ M := by
      dsimp [A]
      cases he : n k e with
      | none => exact (sub_nonpos.mpr (hle k e (mem_exits.mpr ⟨hk, he⟩))).trans hM.le
      | some l => exact hdiff l (reach_next hk he)
    have heq : A false + A true = 2 * M := by
      have hp := hv k
      have hq := hw k
      rw [Fintype.sum_bool] at hp hq
      dsimp [A]
      linarith
    have hsel : A (c k) = M := by
      have hF := hA false
      have hT := hA true
      cases c k <;> linarith
    cases hl : n k (c k) with
    | none =>
      simp only [A, hl, Option.elim_none] at hsel
      linarith [hle k (c k) (mem_exits.mpr ⟨hk, hl⟩)]
    | some l => exact ⟨l, rfl, reach_next hk hl, by simpa only [A, hl, Option.elim_some] using hsel⟩
  have hpath (r : ℕ) :
      ∃ k, (step n c)^[r] (some j) = some k ∧ Reach n z k ∧ v k - w k = M := by
    induction r with
    | zero => exact ⟨j, rfl, (Finset.mem_filter.mp hjK).2, rfl⟩
    | succ r ih =>
      obtain ⟨k, hk, hkR, hk'⟩ := ih
      obtain ⟨l, hl, hlR, hl'⟩ := hnext k hkR hk'
      exact ⟨l, by rw [Function.iterate_succ_apply', hk]; exact hl, hlR, hl'⟩
  obtain ⟨k, hk, -, -⟩ := hpath s
  rw [hc j] at hk
  contradiction

-- Count the integral matching mass in reachable terminal slots. At equality every
-- matching contributes one unit in exactly one slot, and no slot has unused capacity.
private theorem terminal_balance {s m E : ℕ} (hE : 0 < E) (hm : 0 < m)
    {n : Fin s → Bool → Option (Fin s)} (z : Fin s) (hn : Stops n)
    (a : Fin (m*E) → Fin s → Bool → ℕ) (v : Fin (m*E) → Fin s → ℝ)
    (ha : ∀ i bit, (∑ j, a j i bit) ≤ E)
    (hv : ∀ j, Harm n (fun i bit => (a j i bit : ℝ)) (v j))
    (hroot : ∀ j, v j z = (E : ℝ)/((m*E : ℕ) : ℝ)) :
    m ≤ (exits n z).card ∧
      ((exits n z).card = m → ∀ e ∈ exits n z, ∃ w : Fin s → ℝ,
        Harm n (fun i bit => if (i,bit) = e then 1 else 0) w ∧
        w z = 1/(m : ℝ)) := by
  classical
  let T := exits n z
  let A (j : Fin (m*E)) (e : Fin s × Bool) := a j e.1 e.2
  let S (j : Fin (m*E)) := ∑ e ∈ T, A j e
  have hpos : 0 < (E : ℝ)/((m*E : ℕ) : ℝ) := by
    exact div_pos (by exact_mod_cast hE) (by exact_mod_cast Nat.mul_pos hm hE)
  have hS (j : Fin (m*E)) : 1 ≤ S j := by
    by_contra! hj
    have hz : S j = 0 := by omega
    have hzA (e : Fin s × Bool) (he : e ∈ T) : A j e = 0 :=
      Nat.eq_zero_of_le_zero (hz ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) he)
    have hc := harm_cmp_reachable z hn (hv j) (harm_const n 0)
      (fun i bit he => (by simpa [A] using hzA (i,bit) he : (a j i bit : ℝ) ≤ 0))
    rw [hroot] at hc
    exact (not_le_of_gt hpos) hc
  have hL : m*E ≤ ∑ j, S j := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hS j))
  have hU : (∑ j, S j) ≤ T.card*E := by
    unfold S
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _e ∈ T, E := Finset.sum_le_sum (fun e _ => ha e.1 e.2)
      _ = _ := by simp
  refine ⟨(Nat.le_of_mul_le_mul_right (hL.trans hU) hE), ?_⟩
  intro ht e he
  change T.card = m at ht
  have hJ (j : Fin (m*E)) : S j = 1 := by
    by_contra hj
    have hj' : 1 < S j := lt_of_le_of_ne (hS j) (Ne.symm hj)
    have hlt : (∑ _ : Fin (m*E), 1) < ∑ k, S k :=
      Finset.sum_lt_sum (fun k _ => hS k) ⟨j, Finset.mem_univ _, hj'⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
    exact (not_lt_of_ge (by simpa only [ht] using hU : (∑ k, S k) ≤ m*E)) hlt
  have htight : (∑ j, A j e) = E := by
    have hu : (∑ j, A j e) ≤ E := ha e.1 e.2
    by_contra hn'
    have he' : (∑ j, A j e) < E := lt_of_le_of_ne hu hn'
    have hlt : (∑ x ∈ T, ∑ j, A j x) < ∑ _x ∈ T, E :=
      Finset.sum_lt_sum (fun x _ => (show (∑ j, A j x) ≤ E from ha x.1 x.2)) ⟨e, he, he'⟩
    simp only [Finset.sum_const, nsmul_eq_mul, ht] at hlt
    rw [← Finset.sum_comm] at hlt
    exact (not_lt_of_ge hL) hlt
  have hp : ∃ j, 0 < A j e := by
    by_contra! hzero
    have hz : (∑ j, A j e) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact Nat.eq_zero_of_le_zero (hzero j)
    exact hE.ne' (htight.symm.trans hz)
  obtain ⟨j,hj⟩ := hp
  have hE1 : A j e = 1 := by
    have hh := Finset.single_le_sum (f := A j) (fun _ _ => Nat.zero_le _) (show e ∈ T from he)
    change A j e ≤ S j at hh
    rw [hJ] at hh
    omega
  have hOther (x : Fin s × Bool) (hx : x ∈ T) (hne : x ≠ e) : A j x = 0 := by
    have hh : A j x + A j e ≤ S j := by
      have hsub : ({x,e} : Finset (Fin s × Bool)) ⊆ T := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · rw [Finset.mem_singleton] at hy
          exact hy.symm ▸ he
      simpa [hne] using (Finset.sum_le_sum_of_subset_of_nonneg (f := A j) hsub
        (fun _ _ _ => Nat.zero_le _))
    rw [hJ, hE1] at hh
    omega
  let B (i : Fin s) (bit : Bool) : ℝ := if (i,bit) = e then 1 else 0
  obtain ⟨w,hw⟩ := harm_exists hn B
  have hEq (i : Fin s) (bit : Bool) (hmem : (i,bit) ∈ T) :
      (a j i bit : ℝ) = B i bit := by
    dsimp [B]
    by_cases heq : (i,bit) = e
    · subst e
      simpa [A] using (Nat.cast_eq_one.mpr hE1 : (A j (i,bit) : ℝ) = 1)
    · have hh := hOther (i,bit) hmem heq
      simpa [A, heq] using (Nat.cast_eq_zero.mpr hh : (A j (i,bit) : ℝ) = 0)
  have hwz := le_antisymm
    (harm_cmp_reachable z hn hw (hv j) (fun i e he => (hEq i e he).ge))
    (harm_cmp_reachable z hn (hv j) hw (fun i e he => (hEq i e he).le))
  refine ⟨w, hw, ?_⟩
  rw [hwz, hroot, Nat.cast_mul]
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

private theorem labels_to_matching {s m E : ℕ} (hm : 0 < m) (hE : 0 < E)
    {n : Fin s → Bool → Option (Fin s)} (z : Fin s)
    (label : Fin s → Bool → Fin m) (v : Fin m → Fin s → ℝ)
    (hv : ∀ k, Harm n (fun i bit => if label i bit = k then 1 else 0) (v k))
    (hroot : ∀ k, v k z = 1/(m : ℝ)) :
    ∃ (a : Fin (m*E) → Fin s → Bool → ℕ) (A : Fin (m*E) → Fin s → ℝ),
      (∀ i bit, ∑ j, a j i bit = E) ∧
      (∀ j, Harm n (fun i bit => (a j i bit : ℝ)) (A j)) ∧
      (∀ j, A j z = (E : ℝ)/((m*E : ℕ) : ℝ)) := by
  classical
  let e : Fin m × Fin E ≃ Fin (m*E) := finProdFinEquiv
  let a (j : Fin (m*E)) (i : Fin s) (bit : Bool) : ℕ :=
    if label i bit = (e.symm j).1 then 1 else 0
  refine ⟨a, fun j => v (e.symm j).1, ?_, ?_, ?_⟩
  · intro i bit
    rw [← e.sum_comp (fun j => a j i bit), Fintype.sum_prod_type]
    simp [a, eq_comm]
  · intro j
    convert hv (e.symm j).1 using 1
    funext i bit
    by_cases heq : label i bit = (e.symm j).1 <;> simp [a, heq]
  · intro j
    change v (e.symm j).1 z = _
    rw [hroot, Nat.cast_mul]
    have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

namespace L29955Lower

variable {s : ℕ}

def runWord (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (w : List Bool) : Option (Fin s) :=
  w.foldl (fun x bit => x.bind (fun i => n i bit)) x

def Reach (n : Fin s → Bool → Option (Fin s)) (z i : Fin s) : Prop :=
  ∃ w : List Bool, runWord n (some z) w = some i

noncomputable def exits (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Finset (Fin s × Bool) := by
  classical
  exact Finset.univ.filter (fun e => Reach n z e.1 ∧ n e.1 e.2 = none)

private theorem run_append (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (u v : List Bool) : runWord n x (u ++ v) = runWord n (runWord n x u) v := by
  simp [runWord, List.foldl_append]

private theorem run_none (n : Fin s → Bool → Option (Fin s)) (w : List Bool) :
    runWord n none w = none := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem reach_root (n : Fin s → Bool → Option (Fin s)) (z : Fin s) : Reach n z z :=
  ⟨[], rfl⟩

private theorem reach_next {n : Fin s → Bool → Option (Fin s)} {z i j : Fin s} {b : Bool}
    (hi : Reach n z i) (hij : n i b = some j) : Reach n z j := by
  obtain ⟨w, hw⟩ := hi
  refine ⟨w ++ [b], ?_⟩
  rw [run_append, hw]
  exact hij

private noncomputable def depth (n : Fin s → Bool → Option (Fin s)) (z i : Fin s) : ℕ := by
  classical
  exact if hi : Reach n z i then
    Nat.find (show ∃ k, ∃ w : List Bool, w.length = k ∧ runWord n (some z) w = some i by
      obtain ⟨w, hw⟩ := hi
      exact ⟨w.length, w, rfl, hw⟩)
  else 0

private theorem depth_spec {n : Fin s → Bool → Option (Fin s)} {z i : Fin s}
    (hi : Reach n z i) : ∃ w : List Bool, w.length = depth n z i ∧ runWord n (some z) w = some i := by
  classical
  unfold depth
  rw [dite_eq_left hi]
  exact Nat.find_spec (H := show ∃ k, ∃ w : List Bool,
    w.length = k ∧ runWord n (some z) w = some i by
      obtain ⟨w, hw⟩ := hi
      exact ⟨w.length, w, rfl, hw⟩)

private theorem depth_le {n : Fin s → Bool → Option (Fin s)} {z i : Fin s}
    {w : List Bool} (hw : runWord n (some z) w = some i) : depth n z i ≤ w.length := by
  classical
  unfold depth
  rw [dite_eq_left (show Reach n z i from ⟨w, hw⟩)]
  exact Nat.find_min' _ ⟨w, rfl, hw⟩

private theorem depth_root (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    depth n z z = 0 := Nat.le_zero.mp (depth_le (w := []) rfl)

private theorem depth_next {n : Fin s → Bool → Option (Fin s)} {z i j : Fin s} {b : Bool}
    (hi : Reach n z i) (hij : n i b = some j) : depth n z j ≤ depth n z i + 1 := by
  obtain ⟨w, hd, hw⟩ := depth_spec hi
  have h : runWord n (some z) (w ++ [b]) = some j := by
    rw [run_append, hw]
    exact hij
  simpa [hd] using depth_le h

private theorem parent_exists {n : Fin s → Bool → Option (Fin s)} {z i : Fin s}
    (hi : Reach n z i) (hiz : i ≠ z) : ∃ e : Fin s × Bool,
    Reach n z e.1 ∧ n e.1 e.2 = some i ∧ depth n z e.1 + 1 = depth n z i := by
  obtain ⟨w, hd, hw⟩ := depth_spec hi
  induction w using List.reverseRecOn with
  | nil => exact (hiz (Option.some.inj hw).symm).elim
  | append_singleton u b _ =>
    rw [run_append] at hw
    cases hu : runWord n (some z) u with
    | none => simp [hu, run_none] at hw
    | some j =>
      rw [hu] at hw
      change n j b = some i at hw
      have hj : Reach n z j := ⟨u, hu⟩
      have h1 := depth_le hu
      have h2 := depth_next hj hw
      exact ⟨(j,b), hj, hw, by change depth n z j + 1 = depth n z i; simp at hd; omega⟩

private noncomputable def vertices (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Finset (Fin s) := by
  classical
  exact Finset.univ.filter (Reach n z)

private theorem mem_vertices {n : Fin s → Bool → Option (Fin s)} {z i : Fin s} :
    i ∈ vertices n z ↔ Reach n z i := by
  classical
  simp [vertices]

private noncomputable def parent (n : Fin s → Bool → Option (Fin s)) (z i : Fin s) : Fin s × Bool := by
  classical
  exact if hi : Reach n z i ∧ i ≠ z then Classical.choose (parent_exists hi.1 hi.2) else (z,false)

private theorem parent_spec {n : Fin s → Bool → Option (Fin s)} {z i : Fin s}
    (hi : Reach n z i) (hz : i ≠ z) : Reach n z (parent n z i).1 ∧
    n (parent n z i).1 (parent n z i).2 = some i ∧
    depth n z (parent n z i).1 + 1 = depth n z i := by
  unfold parent
  rw [dite_eq_left (And.intro hi hz)]
  exact Classical.choose_spec (parent_exists hi hz)

private noncomputable def parents (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Finset (Fin s × Bool) := by
  classical
  exact ((vertices n z).erase z).image (parent n z)

private noncomputable def extra (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Finset (Fin s × Bool) := by
  classical
  exact ((vertices n z).product Finset.univ) \ (exits n z ∪ parents n z)

private theorem mem_exits {n : Fin s → Bool → Option (Fin s)} {z : Fin s} {e : Fin s × Bool} :
    e ∈ exits n z ↔ Reach n z e.1 ∧ n e.1 e.2 = none := by
  classical
  simp [exits]

private theorem mem_parents {n : Fin s → Bool → Option (Fin s)} {z : Fin s} {e : Fin s × Bool} :
    e ∈ parents n z ↔ ∃ i, Reach n z i ∧ i ≠ z ∧ parent n z i = e := by
  classical
  simp only [parents, Finset.mem_image, Finset.mem_erase, mem_vertices]
  exact ⟨fun ⟨i, h, hp⟩ => ⟨i, h.2, h.1, hp⟩,
    fun ⟨i, hi, hz, hp⟩ => ⟨i, ⟨hz, hi⟩, hp⟩⟩

private theorem parents_subset {n : Fin s → Bool → Option (Fin s)} {z : Fin s} :
    parents n z ⊆ (vertices n z).product Finset.univ := by
  intro e he
  obtain ⟨i, hi, hz, rfl⟩ := mem_parents.mp he
  simp [mem_vertices, (parent_spec hi hz).1]

private theorem exits_subset {n : Fin s → Bool → Option (Fin s)} {z : Fin s} :
    exits n z ⊆ (vertices n z).product Finset.univ := by
  intro e he
  simp [mem_vertices, (mem_exits.mp he).1]

private theorem exits_parents_disjoint (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Disjoint (exits n z) (parents n z) := by
  refine Finset.disjoint_left.mpr ?_
  intro e hE hP
  obtain ⟨i, hi, hz, rfl⟩ := mem_parents.mp hP
  have hn := (mem_exits.mp hE).2
  rw [(parent_spec hi hz).2.1] at hn
  contradiction

private theorem card_parents (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    (parents n z).card = (vertices n z).card - 1 := by
  classical
  rw [parents, Finset.card_image_of_injOn, Finset.card_erase_of_mem (mem_vertices.mpr (reach_root n z))]
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_erase, mem_vertices] at hi hj
  exact Option.some.inj ((parent_spec hi.2 hi.1).2.1.symm.trans
    (hij ▸ (parent_spec hj.2 hj.1).2.1))

private theorem card_balance (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    (extra n z).card + (exits n z).card = (vertices n z).card + 1 := by
  classical
  have hp : 0 < (vertices n z).card := Finset.card_pos.mpr ⟨z, mem_vertices.mpr (reach_root n z)⟩
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.union_subset exits_subset parents_subset : exits n z ∪ parents n z ⊆
      (vertices n z).product Finset.univ)
  change (extra n z).card + _ = ((vertices n z) ×ˢ (Finset.univ : Finset Bool)).card at h
  rw [Finset.card_union_of_disjoint (exits_parents_disjoint n z), card_parents,
    Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
  omega

theorem exit_bound (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    (exits n z).card ≤ s + 1 := by
  have h := card_balance n z
  have h' := Finset.card_le_univ (vertices n z)
  simp only [Fintype.card_fin] at h'
  omega

private noncomputable def tree (n : Fin s → Bool → Option (Fin s)) (z : Fin s) :
    Fin s → Bool → Option (Fin s) := by
  classical
  exact fun i b => if (i,b) ∈ parents n z then n i b else none

private theorem tree_some {n : Fin s → Bool → Option (Fin s)} {z i j : Fin s} {b : Bool} :
    tree n z i b = some j ↔ Reach n z j ∧ j ≠ z ∧ parent n z j = (i,b) := by
  classical
  unfold tree
  split
  · rename_i h
    obtain ⟨k, hk, hzk, hp⟩ := mem_parents.mp h
    have he := (parent_spec hk hzk).2.1
    rw [hp] at he
    change n i b = some k at he
    rw [he, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨hk, hzk, hp⟩
    · rintro ⟨hj, hzj, hp'⟩
      have he' := (parent_spec hj hzj).2.1
      rw [hp'] at he'
      exact Option.some.inj (he.symm.trans he')
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hj
    exact h (mem_parents.mpr ⟨j, hj⟩)

private theorem tree_depth {n : Fin s → Bool → Option (Fin s)} {z i j : Fin s} {w : List Bool}
    (hw : runWord (tree n z) (some i) w = some j) : depth n z j = depth n z i + w.length := by
  induction w generalizing i with
  | nil => simpa [runWord] using congrArg (fun x => (x.map (depth n z)).getD 0) hw.symm
  | cons b w ih =>
    change runWord (tree n z) (tree n z i b) w = some j at hw
    cases h : tree n z i b with
    | none => simp [h, run_none] at hw
    | some k =>
      rw [h] at hw
      obtain ⟨hk, hzk, hkp⟩ := tree_some.mp h
      have hd := (parent_spec hk hzk).2.2
      rw [hkp] at hd
      change depth n z i + 1 = depth n z k at hd
      simp only [List.length_cons, ih hw]
      omega

private theorem tree_pred {n : Fin s → Bool → Option (Fin s)} {z t j : Fin s}
    (h : Reach (tree n z) t j) (ht : j ≠ t) :
    Reach n z j ∧ j ≠ z ∧ Reach (tree n z) t (parent n z j).1 := by
  obtain ⟨w, hw⟩ := h
  induction w using List.reverseRecOn with
  | nil => exact (ht (Option.some.inj hw).symm).elim
  | append_singleton u b _ =>
    rw [run_append] at hw
    cases hu : runWord (tree n z) (some t) u with
    | none => simp [hu, run_none] at hw
    | some i =>
      rw [hu] at hw
      change tree n z i b = some j at hw
      obtain ⟨hj, hjz, hp⟩ := tree_some.mp hw
      exact ⟨hj, hjz, by rw [hp]; exact ⟨u, hu⟩⟩

private theorem root_tree_reach {n : Fin s → Bool → Option (Fin s)} {z j : Fin s}
    (h : Reach n z j) : Reach (tree n z) z j := by
  induction hd : depth n z j using Nat.strong_induction_on generalizing j with
  | ind d ih =>
    by_cases hj : j = z
    · subst j
      exact reach_root _ _
    · obtain ⟨hp, _, hdp⟩ := parent_spec h hj
      have ht := ih _ (by omega) hp rfl
      exact reach_next ht (tree_some.mpr ⟨h, hj, (Prod.eta _).symm⟩)

private theorem tree_edge_depth {n : Fin s → Bool → Option (Fin s)} {z t : Fin s}
    {e : Fin s × Bool} (h : Reach (tree n z) t e.1) :
    depth n z t ≤ depth n z e.1 := by
  obtain ⟨w, hw⟩ := h
  have hh := tree_depth hw
  omega

private theorem edge_split {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {e : Fin s × Bool} (he : Reach n z e.1) :
    e ∈ exits n z ∨ e ∈ parents n z ∨ e ∈ extra n z := by
  classical
  by_cases hx : e ∈ exits n z
  · exact Or.inl hx
  by_cases hp : e ∈ parents n z
  · exact Or.inr (Or.inl hp)
  exact Or.inr (Or.inr (by simp [extra, mem_vertices, he, hx, hp]))

private theorem extra_some {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {e : Fin s × Bool} (he : e ∈ extra n z) :
    ∃ j, n e.1 e.2 = some j ∧ Reach n z j := by
  classical
  have hh : Reach n z e.1 ∧ e ∉ exits n z ∧ e ∉ parents n z := by
    simpa [extra, mem_vertices] using he
  cases h : n e.1 e.2 with
  | none => exact (hh.2.1 (mem_exits.mpr ⟨hh.1, h⟩)).elim
  | some j => exact ⟨j, rfl, reach_next hh.1 h⟩

private noncomputable def descendants (n : Fin s → Bool → Option (Fin s)) (z t : Fin s) :
    Finset (Fin s) := by
  classical
  exact (vertices n z).filter (Reach (tree n z) t)

private theorem mem_descendants {n : Fin s → Bool → Option (Fin s)} {z t i : Fin s} :
    i ∈ descendants n z t ↔ Reach n z i ∧ Reach (tree n z) t i := by
  classical
  simp [descendants, mem_vertices]

private noncomputable def wt (d : ℕ) : ℝ := (1 / 2) ^ d

private theorem wt_step (d : ℕ) : 2 * wt (d+1) = wt d := by
  rw [wt, pow_succ, ← wt]
  ring

def Harm (n : Fin s → Bool → Option (Fin s)) (a : Fin s → Bool → ℝ) (v : Fin s → ℝ) : Prop :=
  ∀ i, 2 * v i = ∑ bit : Bool, (n i bit).elim (a i bit) v

private theorem harmonic_boundary {n : Fin s → Bool → Option (Fin s)} {z t : Fin s}
    {a : Fin s → Bool → ℝ} {v : Fin s → ℝ} (ht : Reach n z t) (hv : Harm n a v) :
    ∑ e ∈ ((descendants n z t).product Finset.univ) \ parents n z,
      wt (depth n z e.1 + 1) * (n e.1 e.2).elim (a e.1 e.2) v =
      wt (depth n z t) * v t := by
  classical
  let D := descendants n z t
  let B := D.product (Finset.univ : Finset Bool)
  let P := parents n z
  let g : Fin s × Bool → ℝ := fun e => wt (depth n z e.1 + 1) * (n e.1 e.2).elim (a e.1 e.2) v
  let f : Fin s → ℝ := fun i => wt (depth n z i) * v i
  change ∑ e ∈ B \ P, g e = f t
  have hD : t ∈ D := mem_descendants.mpr ⟨ht, reach_root _ _⟩
  have htotal : ∑ e ∈ B, g e = ∑ i ∈ D, f i := by
    change ∑ e ∈ (D ×ˢ (Finset.univ : Finset Bool)), g e = _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    change ∑ b : Bool, wt (depth n z i + 1) * (n i b).elim (a i b) v = f i
    rw [← Finset.mul_sum, ← hv i]
    dsimp [f]
    rw [← mul_assoc, mul_comm (wt _), wt_step]
  have hin : ∀ i ∈ D.erase t, parent n z i ∈ B ∩ P := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hir, hist⟩ := mem_descendants.mp hi
    obtain ⟨_, hiz, hpt⟩ := tree_pred hist hne
    exact Finset.mem_inter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_descendants.mpr ⟨(parent_spec hir hiz).1, hpt⟩, Finset.mem_univ _⟩,
      mem_parents.mpr ⟨i, hir, hiz, rfl⟩⟩
  have hselected : ∑ i ∈ D.erase t, f i = ∑ e ∈ B ∩ P, g e := by
    apply Finset.sum_bij (fun i _ => parent n z i) hin
    · intro i hi j hj heq
      have get : ∀ k ∈ D.erase t, n (parent n z k).1 (parent n z k).2 = some k := by
        intro k hk
        obtain ⟨hne, hk⟩ := Finset.mem_erase.mp hk
        obtain ⟨hkr, hkt⟩ := mem_descendants.mp hk
        exact (parent_spec hkr (tree_pred hkt hne).2.1).2.1
      exact Option.some.inj ((get i hi).symm.trans (heq ▸ get j hj))
    · intro e he
      obtain ⟨heb, hep⟩ := Finset.mem_inter.mp he
      obtain ⟨i, hir, hiz, rfl⟩ := mem_parents.mp hep
      have hist := (mem_descendants.mp (Finset.mem_product.mp heb).1).2
      have hd := (parent_spec hir hiz).2.2
      have hle := tree_edge_depth (e := parent n z i) hist
      have hne : i ≠ t := by
        intro hh
        subst i
        change depth n z (parent n z t).1 + 1 = depth n z t at hd
        omega
      have hr := reach_next hist (tree_some.mpr ⟨hir, hiz, (Prod.eta _).symm⟩)
      exact ⟨i, Finset.mem_erase.mpr ⟨hne, mem_descendants.mpr ⟨hir, hr⟩⟩, rfl⟩
    · intro i hi
      obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
      obtain ⟨hir, hist⟩ := mem_descendants.mp hi
      obtain ⟨_, hiz, _⟩ := tree_pred hist hne
      obtain ⟨_, hs, hd⟩ := parent_spec hir hiz
      simp only [g, f, hs, hd, Option.elim_some]
  have hparts : ∑ e ∈ B \ P, g e + ∑ e ∈ B ∩ P, g e = ∑ e ∈ B, g e := by
    rw [← Finset.sum_union (by exact Finset.disjoint_left.mpr (by
      intro e h₁ h₂
      exact (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).2))]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [htotal, ← hselected, Finset.sum_erase_add _ _ hD |>.symm] at hparts
  linarith

private theorem mem_extra {n : Fin s → Bool → Option (Fin s)} {z : Fin s} {e : Fin s × Bool} :
    e ∈ extra n z ↔ Reach n z e.1 ∧ e ∉ exits n z ∧ e ∉ parents n z := by
  classical
  simp [extra, mem_vertices]

private theorem harmonic_indicator {n : Fin s → Bool → Option (Fin s)} {z t : Fin s}
    {v : Fin s → ℝ} (ht : Reach n z t) {e : Fin s × Bool} (he : e ∈ exits n z)
    (hv : Harm n (fun i b => if (i,b) = e then 1 else 0) v) :
    (by
      classical
      exact (if Reach (tree n z) t e.1 then wt (depth n z e.1 + 1) else 0) +
        (∑ k ∈ (extra n z).filter (fun k => Reach (tree n z) t k.1),
          wt (depth n z k.1 + 1) * (n k.1 k.2).elim 0 v) =
        wt (depth n z t) * v t) := by
  classical
  have hh := harmonic_boundary (z := z) ht hv
  let E := (exits n z).filter (fun k => Reach (tree n z) t k.1)
  let F := (extra n z).filter (fun k => Reach (tree n z) t k.1)
  have hp : (descendants n z t ×ˢ (Finset.univ : Finset Bool)) \ parents n z = E ∪ F := by
    ext k
    simp only [E, F, Finset.mem_sdiff, Finset.mem_product, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, and_true, mem_descendants, mem_extra]
    have h1 := fun hk : k ∈ exits n z => (mem_exits.mp hk).1
    have h2 := fun hk : k ∈ exits n z => Finset.disjoint_left.mp
      (exits_parents_disjoint n z) hk
    tauto
  change ∑ k ∈ (descendants n z t ×ˢ (Finset.univ : Finset Bool)) \ parents n z, _ = _ at hh
  rw [hp, Finset.sum_union (Finset.disjoint_left.mpr (by
    intro k hkE hkF
    exact (mem_extra.mp (Finset.mem_filter.mp hkF).1).2.1 (Finset.mem_filter.mp hkE).1))] at hh
  have hE : (∑ k ∈ E, wt (depth n z k.1 + 1) *
      (n k.1 k.2).elim (if (k.1,k.2) = e then 1 else 0) v) =
      if Reach (tree n z) t e.1 then wt (depth n z e.1 + 1) else 0 := by
    calc
      _ = ∑ k ∈ E, if k = e then wt (depth n z k.1 + 1) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [(mem_exits.mp (Finset.mem_filter.mp hk).1).2]
        by_cases h : k = e <;> simp [h]
      _ = _ := by simp [E, he]
  have hF : (∑ k ∈ F, wt (depth n z k.1 + 1) *
      (n k.1 k.2).elim (if (k.1,k.2)=e then 1 else 0) v) =
      ∑ k ∈ F, wt (depth n z k.1 + 1) * (n k.1 k.2).elim 0 v := by
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨j, hj, _⟩ := extra_some (Finset.mem_filter.mp hk).1
    simp [hj]
  rw [hE, hF] at hh
  exact hh

private theorem eventually_exit {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    (P : Fin s → Prop) (seed : ∃ i, Reach n z i ∧ P i)
    (closed : ∀ i j b, Reach n z i → P i → tree n z i b = some j → P j)
    (noextra : ∀ i b, Reach n z i → P i → (i,b) ∉ extra n z) :
    ∃ e ∈ exits n z, P e.1 := by
  classical
  let F := (vertices n z).filter P
  have hn : F.Nonempty := by
    obtain ⟨i, hi, hP⟩ := seed
    exact ⟨i, Finset.mem_filter.mpr ⟨mem_vertices.mpr hi, hP⟩⟩
  obtain ⟨i, hi, hm⟩ := Finset.exists_max_image F (depth n z) hn
  obtain ⟨hir, hip⟩ := Finset.mem_filter.mp hi
  have hir := mem_vertices.mp hir
  rcases edge_split (e := (i,false)) hir with he | hp | hx
  · exact ⟨_, he, hip⟩
  · obtain ⟨j, hj, hjz, hpar⟩ := mem_parents.mp hp
    have hjp := closed i j false hir hip (tree_some.mpr ⟨hj, hjz, hpar⟩)
    have hd := (parent_spec hj hjz).2.2
    rw [hpar] at hd
    have hle := hm j (Finset.mem_filter.mpr ⟨mem_vertices.mpr hj, hjp⟩)
    change depth n z i + 1 = depth n z j at hd
    omega
  · exact (noextra i false hir hip hx).elim

private theorem exit_outside_cycle {n : Fin s → Bool → Option (Fin s)} {z t : Fin s}
    {k : Fin s × Bool} (ht : Reach n z t) (htz : t ≠ z) (hx : extra n z = {k})
    (hkt : Reach (tree n z) t k.1) :
    ∃ e ∈ exits n z, ¬ Reach (tree n z) t e.1 := by
  classical
  obtain ⟨hir, _, hdi⟩ := parent_spec ht htz
  let i := (parent n z t).1
  let b := !(parent n z t).2
  change depth n z i + 1 = depth n z t at hdi
  have hnot : ¬ Reach (tree n z) t i := by
    intro h
    have hd := tree_edge_depth (e := parent n z t) h
    change depth n z t ≤ depth n z i at hd
    omega
  rcases edge_split (e := (i,b)) hir with he | hp | he
  · exact ⟨_, he, hnot⟩
  · obtain ⟨j, hj, hjz, hp⟩ := mem_parents.mp hp
    have hjt : j ≠ t := by
      intro h
      subst j
      have hb := congrArg Prod.snd hp
      change (parent n z t).2 = !(parent n z t).2 at hb
      cases hh : (parent n z t).2 <;> simp [hh] at hb
    have hd := (parent_spec hj hjz).2.2
    rw [hp] at hd
    have hdesc : ¬ Reach (tree n z) t j := by
      intro hh
      have hh := (tree_pred hh hjt).2.2
      rw [hp] at hh
      exact hnot hh
    obtain ⟨e, he, hP⟩ := eventually_exit
      (fun u => depth n z t ≤ depth n z u ∧ ¬ Reach (tree n z) t u)
      ⟨j, hj, by change depth n z i + 1 = depth n z j at hd; omega, hdesc⟩
      (by
        intro u v c _ hu huv
        obtain ⟨hvr, hvz, hvp⟩ := tree_some.mp huv
        have hdu := (parent_spec hvr hvz).2.2
        rw [hvp] at hdu
        change depth n z u + 1 = depth n z v at hdu
        refine ⟨by have := hu.1; omega, ?_⟩
        intro hvt
        have hvne : v ≠ t := by
          intro hh
          subst v
          have := hu.1
          omega
        have hh := (tree_pred hvt hvne).2.2
        rw [hvp] at hh
        exact hu.2 hh)
      (by
        intro u c _ hu huc
        rw [hx, Finset.mem_singleton] at huc
        have hh : u = k.1 := congrArg Prod.fst huc
        exact hu.2 (hh ▸ hkt))
    exact ⟨e, he, hP.2⟩
  · rw [hx, Finset.mem_singleton] at he
    have hh : (i,b).1 = k.1 := congrArg Prod.fst he
    change i = k.1 at hh
    exact (hnot (hh ▸ hkt)).elim


private theorem wt_pos (k : ℕ) : 0 < wt k := by
  unfold wt
  positivity

private theorem wt_add (a b : ℕ) : wt (a+b) = wt a * wt b := by
  simp [wt, pow_add]

private theorem wt_inv (k : ℕ) : wt k = 1 / (2 : ℝ)^k := by
  simp [wt]

private theorem wt_injective : Function.Injective wt := by
  intro a b h
  have hh : (2:ℝ)^a = (2:ℝ)^b := by
    simp only [wt_inv, one_div, inv_inj] at h
    exact h
  exact (pow_right_strictMono₀ (show (1:ℝ) < 2 by norm_num)).injective hh

private def Den2 (x : ℝ) : Prop := ∃ d k : ℕ, x = (k : ℝ) * wt d

private theorem den_zero : Den2 0 := ⟨0, 0, by simp⟩

private theorem den_wt (d : ℕ) : Den2 (wt d) := ⟨d, 1, by simp⟩

private theorem den_mul {x y : ℝ} (hx : Den2 x) (hy : Den2 y) : Den2 (x*y) := by
  obtain ⟨a,k,rfl⟩ := hx
  obtain ⟨b,l,rfl⟩ := hy
  refine ⟨a+b,k*l,?_⟩
  rw [wt_add, Nat.cast_mul]
  ring

private theorem den_add {x y : ℝ} (hx : Den2 x) (hy : Den2 y) : Den2 (x+y) := by
  obtain ⟨a,k,rfl⟩ := hx
  obtain ⟨b,l,rfl⟩ := hy
  refine ⟨a+b,k*2^b+l*2^a,?_⟩
  rw [wt_add]
  push_cast
  rw [wt_inv a, wt_inv b]
  have ha : (2:ℝ)^a ≠ 0 := pow_ne_zero _ (by norm_num)
  have hb : (2:ℝ)^b ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

private theorem den_force {m : ℕ} (hm : 0 < m) (hd : Den2 (1 / (m:ℝ))) :
    ∃ h : ℕ, m = 2^h := by
  obtain ⟨d,k,hk⟩ := hd
  rw [wt_inv] at hk
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : (2:ℝ)^d ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (2:ℝ)^d = (m:ℝ)*(k:ℝ) := by
    field_simp at hk
    nlinarith
  have he' : (2:ℕ)^d = m*k := by exact_mod_cast he
  obtain ⟨h, _, hh⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨k,he'⟩
  exact ⟨h,hh⟩

private theorem narrow_exit_ge {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {k : Fin s × Bool} (hx : extra n z = {k}) : ∃ e ∈ exits n z,
    depth n z k.1 + 1 ≤ depth n z e.1 + 1 := by
  classical
  have hk : k ∈ extra n z := by simp [hx]
  have hkr := (mem_extra.mp hk).1
  have hne : (k.1, !k.2) ≠ k := by
    intro h
    have hb : (!k.2) = k.2 := congrArg Prod.snd h
    cases hh : k.2 <;> simp [hh] at hb
  rcases edge_split (e := (k.1,!k.2)) hkr with he | hp | he
  · exact ⟨_, he, Nat.le_refl _⟩
  · obtain ⟨j,hj,hjz,hp⟩ := mem_parents.mp hp
    have hd := (parent_spec hj hjz).2.2
    rw [hp] at hd
    change depth n z k.1 + 1 = depth n z j at hd
    obtain ⟨e,he,hde⟩ := eventually_exit (fun i => depth n z k.1 < depth n z i)
      ⟨j,hj,by omega⟩
      (by
        intro i j b _ hi hij
        obtain ⟨hj,hjz,hp⟩ := tree_some.mp hij
        have hd := (parent_spec hj hjz).2.2
        rw [hp] at hd
        change depth n z i + 1 = depth n z j at hd
        change depth n z k.1 < depth n z j
        omega)
      (by
        intro i b _ hi he
        rw [hx, Finset.mem_singleton] at he
        have hh : i = k.1 := congrArg Prod.fst he
        subst i
        exact (Nat.lt_irrefl _) hi)
    exact ⟨e,he,by omega⟩
  · exact (hne (by simpa [hx] using he)).elim

private theorem step_except {n : Fin s → Bool → Option (Fin s)} {z i j : Fin s}
    {b : Bool} (hi : Reach n z i) (hj : n i b = some j) (hx : (i,b) ∉ extra n z) :
    depth n z j = depth n z i + 1 := by
  rcases edge_split (e := (i,b)) hi with he | hp | he
  · have hn := (mem_exits.mp he).2
    rw [hj] at hn
    contradiction
  · obtain ⟨u,hu,huz,hp⟩ := mem_parents.mp hp
    obtain ⟨_,hn,hd⟩ := parent_spec hu huz
    rw [hp] at hn hd
    change n i b = some u at hn
    have hh := Option.some.inj (hj.symm.trans hn)
    subst u
    exact hd.symm
  · exact (hx he).elim

private theorem short_unique {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    (Rooted : ∀ e ∈ extra n z, n e.1 e.2 = some z)
    {i : Fin s} {u v : List Bool} (hu : runWord n (some z) u = some i)
    (hv : runWord n (some z) v = some i) (hdu : u.length = depth n z i)
    (hdv : v.length = depth n z i) : u = v := by
  induction u using List.reverseRecOn generalizing i v with
  | nil =>
    have hv0 : v.length = 0 := hdv.trans hdu.symm
    exact (List.length_eq_zero_iff.mp hv0).symm
  | append_singleton u b ih =>
    induction v using List.reverseRecOn with
    | nil => simp at hdu hdv; omega
    | append_singleton v c _ =>
      rw [run_append] at hu hv
      cases hru : runWord n (some z) u with
      | none => simp [hru, run_none] at hu
      | some x =>
        cases hrv : runWord n (some z) v with
        | none => simp [hrv, run_none] at hv
        | some y =>
          rw [hru] at hu
          rw [hrv] at hv
          change n x b = some i at hu
          change n y c = some i at hv
          simp only [List.length_append, List.length_singleton] at hdu hdv
          have hne : i ≠ z := by
            intro hh
            subst i
            rw [depth_root] at hdu
            omega
          have get : ∀ (x : Fin s) (b : Bool), Reach n z x →
              n x b = some i → parent n z i = (x,b) := by
            intro x b hxr hxi
            rcases edge_split (e := (x,b)) hxr with he | hp | he
            · have hh := (mem_exits.mp he).2
              rw [hxi] at hh
              contradiction
            · obtain ⟨j,hj,hjz,hp⟩ := mem_parents.mp hp
              have hh := (parent_spec hj hjz).2.1
              rw [hp] at hh
              change n x b = some j at hh
              rwa [Option.some.inj (hh.symm.trans hxi)] at hp
            · exact (hne (Option.some.inj (hxi.symm.trans (Rooted _ he)))).elim
          have hxu := get x b ⟨u,hru⟩ hu
          have hyv := get y c ⟨v,hrv⟩ hv
          have hxy : (x,b) = (y,c) := hxu.symm.trans hyv
          have hxy' := Prod.mk.inj hxy
          obtain ⟨rfl,rfl⟩ := hxy'
          have hh := (parent_spec (reach_next ⟨u,hru⟩ hu) hne).2.2
          rw [hxu] at hh
          change depth n z x + 1 = depth n z i at hh
          rw [ih hru hrv (by omega) (by omega)]

private theorem root_indicator {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {e : Fin s × Bool} (he : e ∈ exits n z) {v : Fin s → ℝ}
    (hv : Harm n (fun i b => if (i,b)=e then 1 else 0) v) :
    (by
      classical
      exact wt (depth n z e.1 + 1) +
        (∑ k ∈ extra n z, wt (depth n z k.1 + 1) * (n k.1 k.2).elim 0 v) = v z) := by
  classical
  have hh := harmonic_indicator (reach_root n z) he hv
  have hr : (extra n z).filter (fun k => Reach (tree n z) z k.1) = extra n z := by
    exact Finset.filter_eq_self.mpr (fun k hk => root_tree_reach (mem_extra.mp hk).1)
  simpa [root_tree_reach (mem_exits.mp he).1, hr, depth_root, wt] using hh

def Uniform (n : Fin s → Bool → Option (Fin s)) (z : Fin s) (m : ℕ) : Prop :=
  ∀ e ∈ exits n z, ∃ v : Fin s → ℝ,
    Harm n (fun i b => if (i,b)=e then 1 else 0) v ∧ v z = 1/(m:ℝ)

private theorem zero_extra_shape {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {m : ℕ} (hm : 2 ≤ m) (hc : m ≤ (exits n z).card) (hv : Uniform n z m)
    (hx : extra n z = ∅) : ∃ h : ℕ, m = 2^h ∧
    ∀ e ∈ exits n z, depth n z e.1 + 1 = h := by
  have calcExit : ∀ e ∈ exits n z, wt (depth n z e.1 + 1) = 1/(m:ℝ) := by
    intro e he
    obtain ⟨v,hv,hz⟩ := hv e he
    simpa [hx, hz] using root_indicator he hv
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (exits n z).card by omega)
  refine ⟨depth n z e.1 + 1, ?_, fun k hk => wt_injective ((calcExit k hk).trans (calcExit e he).symm)⟩
  have hh := calcExit e he
  rw [wt_inv, one_div, one_div, inv_inj] at hh
  exact_mod_cast hh.symm

private theorem restart_target {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {m : ℕ} (hm : 2 ≤ m) (hc : m ≤ (exits n z).card) (hv : Uniform n z m)
    (hnd : ¬ ∃ a : ℕ, m = 2^a) {k : Fin s × Bool} (hx : extra n z = {k})
    {t : Fin s} (ht : Reach n z t) (hk : n k.1 k.2 = some t) : t = z := by
  classical
  by_contra htz
  have hout : Den2 (1/(m:ℝ)) := by
    by_cases hp : Reach (tree n z) t k.1
    · obtain ⟨e,he,he'⟩ := exit_outside_cycle ht htz hx hp
      obtain ⟨v,hv,hz⟩ := hv e he
      have ht' := harmonic_indicator ht he hv
      have ht' : wt (depth n z k.1 + 1) * v t = wt (depth n z t) * v t := by
        simpa [he', hx, Finset.filter_singleton, hp, hk] using ht'
      have hv0 : v t = 0 := by
        by_contra hne
        have hh := wt_injective (mul_right_cancel₀ hne ht')
        have hd := tree_edge_depth (e := k) hp
        omega
      have hh : wt (depth n z e.1 + 1) = 1/(m:ℝ) := by
        simpa [hx,hk,hv0,hz] using root_indicator he hv
      rw [← hh]
      exact den_wt _
    · obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (exits n z).card by omega)
      obtain ⟨v,hv,hz⟩ := hv e he
      have ht' := harmonic_indicator ht he hv
      have hden : Den2 (v t) := by
        by_cases he' : Reach (tree n z) t e.1
        · have hd := tree_edge_depth (e := e) he'
          have hle : depth n z t ≤ depth n z e.1 + 1 := by omega
          have hh : wt (depth n z e.1 + 1) = wt (depth n z t) * v t := by
            simpa [he', hx, Finset.filter_singleton, hp] using ht'
          rw [← Nat.add_sub_of_le hle, wt_add] at hh
          rw [← mul_left_cancel₀ (wt_pos _).ne' hh]
          exact den_wt _
        · have hh : 0 = wt (depth n z t) * v t := by
            simpa [he', hx, Finset.filter_singleton, hp] using ht'
          have h0 : v t = 0 := (mul_eq_zero.mp hh.symm).resolve_left (wt_pos _).ne'
          rw [h0]
          exact den_zero
      have hh : wt (depth n z e.1 + 1) + wt (depth n z k.1 + 1) * v t =
          1/(m:ℝ) := by simpa [hx,hk,hz] using root_indicator he hv
      rw [← hh]
      exact den_add (den_wt _) (den_mul (den_wt _) hden)
  exact hnd (den_force (by omega) hout)

private theorem restart_numbers {m h p : ℕ} (hm : 0 < m) (hp : p ≤ h)
    (he : wt h + wt p * (1/(m:ℝ)) = 1/(m:ℝ)) :
    m = 2^h - 2^(h-p) ∧ m = 2^(h-p) * (2^p-1) := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow : (2:ℝ)^h = (2:ℝ)^(h-p) * (2:ℝ)^p := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  have hre : (m:ℝ) * wt h = 1 - wt p := by
    have he' := congrArg (fun x : ℝ => (m:ℝ)*x) he
    have hh : (m:ℝ)*(1/(m:ℝ)) = 1 := by field_simp
    have hrew : (m:ℝ) * (wt h + wt p * (1/(m:ℝ))) =
        (m:ℝ) * wt h + wt p * ((m:ℝ) * (1/(m:ℝ))) := by ring
    rw [hrew, hh, mul_one] at he'
    linarith
  have hcalc : (2:ℝ)^h * wt p = (2:ℝ)^(h-p) := by
    rw [hpow, wt_inv]
    have hn : (2:ℝ)^p ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hr : (m:ℝ) = (2:ℝ)^h - (2:ℝ)^(h-p) := by
    calc
      _ = (2:ℝ)^h * ((m:ℝ) * wt h) := by
        rw [wt_inv]
        have hn : (2:ℝ)^h ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
      _ = _ := by rw [hre, mul_sub, mul_one, hcalc]
  have hle : (2:ℕ)^(h-p) ≤ (2:ℕ)^h := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hr' : (m:ℝ) = ((2^h - 2^(h-p) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle]
    exact hr
  have he' : m = 2^h - 2^(h-p) := by exact_mod_cast hr'
  refine ⟨he', ?_⟩
  rw [he', Nat.mul_sub, Nat.mul_one, ← pow_add, Nat.sub_add_cancel hp]

private theorem restart_shape {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {m : ℕ} (hm : 2 ≤ m) (hc : m ≤ (exits n z).card) (hv : Uniform n z m)
    (hnd : ¬ ∃ a : ℕ, m = 2^a) {k : Fin s × Bool} (hx : extra n z = {k}) :
    ∃ h p : ℕ, 2 ≤ p ∧ p ≤ h ∧ m = 2^h - 2^(h-p) ∧
    m = 2^(h-p) * (2^p-1) ∧
    (∀ e ∈ exits n z, depth n z e.1 + 1 = h) ∧
    n k.1 k.2 = some z ∧ depth n z k.1 + 1 = p := by
  obtain ⟨t,ht,hr⟩ := extra_some (show k ∈ extra n z by simp [hx])
  have hh := restart_target hm hc hv hnd hx hr ht
  subst t
  let p := depth n z k.1 + 1
  have calcExit : ∀ e ∈ exits n z, wt (depth n z e.1 + 1) + wt p * (1/(m:ℝ)) =
      1/(m:ℝ) := by
    intro e he
    obtain ⟨v,hv,hz⟩ := hv e he
    simpa [hx,ht,hz,p] using root_indicator he hv
  obtain ⟨e,he,hpe⟩ := narrow_exit_ge hx
  let h := depth n z e.1 + 1
  have hph : p ≤ h := hpe
  obtain ⟨hm1,hm2⟩ := restart_numbers (show 0 < m by omega) hph (calcExit e he)
  have hp2 : 2 ≤ p := by
    by_contra h
    have hp1 : p = 1 := by dsimp [p] at *; omega
    exact hnd ⟨_, by simpa [hp1] using hm2⟩
  refine ⟨h,p,hp2,hph,hm1,hm2,?_,ht,rfl⟩
  intro f hf
  apply wt_injective
  have he' := calcExit e he
  have hf' := calcExit f hf
  change wt h + wt p * (1/(m:ℝ)) = 1/(m:ℝ) at he'
  linarith

def UniformEvent (n : Fin s → Bool → Option (Fin s)) (z : Fin s) (m : ℕ) : Prop :=
  ∃ (a : Fin s → Bool → ℕ) (v : Fin s → ℝ),
    Harm n (fun i b => (a i b : ℝ)) v ∧ v z = 1/(m:ℝ)

private theorem zero_extra_dyadic {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {m : ℕ} (hm : 2 ≤ m) (he : UniformEvent n z m) (hx : extra n z = ∅) :
    ∃ h : ℕ, m = 2^h := by
  classical
  obtain ⟨a,v,hv,hz⟩ := he
  have hh := harmonic_boundary (reach_root n z) hv
  have hset : (descendants n z z ×ˢ (Finset.univ : Finset Bool)) \ parents n z =
      exits n z := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_univ, and_true, mem_descendants]
    constructor
    · rintro ⟨⟨hr,_⟩,hn⟩
      rcases edge_split (e := e) hr with he | hp | he
      · exact he
      · exact (hn hp).elim
      · simp [hx] at he
    · intro he
      have hr := (mem_exits.mp he).1
      exact ⟨⟨hr,root_tree_reach hr⟩, Finset.disjoint_left.mp (exits_parents_disjoint n z) he⟩
  change ∑ e ∈ (descendants n z z ×ˢ (Finset.univ : Finset Bool)) \ parents n z, _ = _ at hh
  rw [hset, depth_root, hz] at hh
  simp only [wt, pow_zero, one_mul] at hh
  apply den_force (show 0 < m by omega)
  rw [← hh]
  have hs : ∀ f : Finset (Fin s × Bool), f ⊆ exits n z →
      Den2 (∑ e ∈ f, wt (depth n z e.1 + 1) * (n e.1 e.2).elim (a e.1 e.2 : ℝ) v) := by
    intro f
    induction f using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; intro _; exact den_zero
    | @insert e f hne ih =>
      intro hsub
      have hmem := hsub (Finset.mem_insert_self e f)
      rw [Finset.sum_insert hne]
      apply den_add _ (ih (fun k hk => hsub (Finset.mem_insert_of_mem hk)))
      rw [(mem_exits.mp hmem).2]
      exact den_mul (den_wt _) ⟨0, a e.1 e.2, by simp [wt]⟩
  simpa only [wt] using hs _ (fun _ h => h)

theorem classification (n : Fin s → Bool → Option (Fin s)) (z : Fin s) (m : ℕ)
    (hm : 2 ≤ m) (hx : m ≤ (exits n z).card)
    (hu : (exits n z).card = m → Uniform n z m)
    (hevent : UniformEvent n z m) :
    m ≤ s+1 ∧
    (s+1 = m → ∃ (d : Fin s → ℕ) (h : ℕ), m = 2^h ∧ d z = 0 ∧
      (∀ i b, Reach n z i → n i b = none → d i+1 = h) ∧
      (∀ i b j, Reach n z i → n i b = some j → d j = d i+1)) ∧
    ((¬ ∃ a : ℕ, m = 2^a) → s ≤ m → s = m ∧
      ∃ (d : Fin s → ℕ) (h p : ℕ) (k : Fin s × Bool), 2 ≤ p ∧ p ≤ h ∧
        m = 2^h - 2^(h-p) ∧ m = 2^(h-p) * (2^p-1) ∧ d z = 0 ∧
        (∀ i b, Reach n z i → n i b = none → d i+1 = h) ∧
        (∀ i b j, Reach n z i → n i b = some j → (i,b) ≠ k → d j = d i+1) ∧
        n k.1 k.2 = some z ∧ d k.1+1 = p ∧
        ∃ w : List Bool, w.length+1 = p ∧ runWord n (some z) w = some k.1 ∧
          ∀ u : List Bool, u.length+1 = p → runWord n (some z) u = some k.1 → u=w) := by
  classical
  have hb := exit_bound n z
  have ha := card_balance n z
  have hV := Finset.card_le_univ (vertices n z)
  simp only [Fintype.card_fin] at hV
  refine ⟨by omega, ?_, ?_⟩
  · intro hs
    have hzero : extra n z = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨h,hm',hh⟩ := zero_extra_shape hm hx (hu (by omega)) hzero
    refine ⟨depth n z,h,hm',depth_root n z,?_,?_⟩
    · intro i b hi hn
      exact hh (i,b) (mem_exits.mpr ⟨hi,hn⟩)
    · intro i b j hi hn
      exact step_except hi hn (by simp [hzero])
  · intro hnd hs
    have hne : (extra n z).card ≠ 0 := by
      intro hzero
      exact hnd (zero_extra_dyadic hm hevent (Finset.card_eq_zero.mp hzero))
    have hs' : s = m := by omega
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp (show (extra n z).card = 1 by omega)
    obtain ⟨h,p,hp,hph,hm1,hm2,hex,hback,hdep⟩ :=
      restart_shape hm hx (hu (by omega)) hnd hk
    refine ⟨hs',depth n z,h,p,k,hp,hph,hm1,hm2,depth_root n z,?_,?_,hback,hdep,?_⟩
    · intro i b hi hn
      exact hex (i,b) (mem_exits.mpr ⟨hi,hn⟩)
    · intro i b j hi hn hnk
      exact step_except hi hn (by simpa [hk] using hnk)
    · have hkr := (mem_extra.mp (show k ∈ extra n z by simp [hk])).1
      obtain ⟨w,hw,hr⟩ := depth_spec hkr
      refine ⟨w,by omega,hr,?_⟩
      intro u hu hur
      exact short_unique (fun e he => by rw [hk,Finset.mem_singleton] at he; subst e; exact hback)
        hur hr (by omega) hw

end L29955Lower

namespace L29955Live

private def runWord {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (x : Option (Fin s)) (w : List Bool) : Option (Fin s) :=
  w.foldl (fun x bit => x.bind (fun i => n i bit)) x

private def Reach {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (z i : Fin s) : Prop := ∃ w : List Bool, runWord n (some z) w = some i

private def Stops {s : ℕ} (n : Fin s → Bool → Option (Fin s)) : Prop :=
  ∃ c : Fin s → Bool, ∀ i : Fin s,
    (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none

private def live {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (z : Fin s)
    (b : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin b → Bool)).filter
    (fun w => (runWord n (some z) (List.ofFn w)).isSome)).card

private theorem run_append {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (x : Option (Fin s)) (u v : List Bool) :
    runWord n x (u ++ v) = runWord n (runWord n x u) v :=
  List.foldl_append

private theorem run_snoc {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (x : Option (Fin s)) (u : List Bool) (bit : Bool) :
    runWord n x (u ++ [bit]) = (runWord n x u).bind (fun i => n i bit) :=
  run_append n x u [bit]

private theorem none_run {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : List Bool) :
    runWord n none u = none := by
  induction u with
  | nil => rfl
  | cons b u ih => exact ih

private theorem next_reachable {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {z i j : Fin s} {bit : Bool} (hi : Reach n z i) (h : n i bit = some j) : Reach n z j := by
  obtain ⟨u, hu⟩ := hi
  exact ⟨u ++ [bit], by rw [run_snoc, hu]; exact h⟩

private theorem rank_lt {s : ℕ} {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    (d : Fin s → ℕ) (h : ℕ) (stop : Stops n)
    (advance : ∀ i, Reach n z i → h ≤ d i → ∀ bit,
      ∃ j, n i bit = some j ∧ h ≤ d j) :
    ∀ i, Reach n z i → d i < h := by
  obtain ⟨c,hc⟩ := stop
  intro i hi
  by_contra! hi'
  let f (x : Option (Fin s)) := x.bind (fun j => n j (c j))
  have inv (k : ℕ) : ∃ j, f^[k] (some i) = some j ∧ Reach n z j ∧ h ≤ d j := by
    induction k with
    | zero => exact ⟨i,rfl,hi,hi'⟩
    | succ k ih =>
      obtain ⟨j,hj,hjr,hjd⟩ := ih
      obtain ⟨l,hl,hld⟩ := advance j hjr hjd (c j)
      exact ⟨l, by rw [Function.iterate_succ_apply', hj]; exact hl, next_reachable hjr hl, hld⟩
  obtain ⟨j,hj,-,-⟩ := inv s
  have hh : f^[s] (some i) = none := hc i
  rw [hh] at hj
  contradiction

-- From any state that is beyond the restart source, the remaining life is the depth gap.
private theorem ordered_run {s : ℕ} {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    (d : Fin s → ℕ) (h a : ℕ)
    (hrank : ∀ i, Reach n z i → d i < h)
    (hexit : ∀ i bit, Reach n z i → n i bit = none → d i+1=h)
    (hstep : ∀ i bit j, Reach n z i → a ≤ d i → n i bit = some j → d j=d i+1)
    (w : List Bool) (i : Fin s) (hi : Reach n z i) (ha : a ≤ d i) :
    (runWord n (some i) w).isSome ↔ d i + w.length < h := by
  induction w generalizing i with
  | nil => simp [runWord, hrank i hi]
  | cons bit w ih =>
    change (runWord n (n i bit) w).isSome ↔ _
    cases hn : n i bit with
    | none =>
      rw [none_run]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, List.length_cons]
      have hh := hexit i bit hi hn
      omega
    | some j =>
      have hj := hstep i bit j hi ha hn
      rw [ih j (next_reachable hi hn) (by omega)]
      simp only [List.length_cons]
      omega

private theorem card_live_of_lt {s : ℕ} {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {h b : ℕ} (he : ∀ w : Fin b → Bool,
      (runWord n (some z) (List.ofFn w)).isSome ↔ b < h) :
    live n z b = if b < h then 2^b else 0 := by
  classical
  unfold live
  simp_rw [he]
  by_cases hb : b < h <;> simp [hb]

theorem tree_live {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (z : Fin s)
    (d : Fin s → ℕ) (h : ℕ) (hz : d z = 0) (stop : Stops n)
    (hexit : ∀ i bit, Reach n z i → n i bit = none → d i+1=h)
    (hstep : ∀ i bit j, Reach n z i → n i bit=some j → d j=d i+1) :
    ∀ b, live n z b = 2^b % 2^h := by
  have hR := rank_lt d h stop (z := z) (by
    intro i hi hid bit
    cases he : n i bit with
    | none => have := hexit i bit hi he; omega
    | some j => have := hstep i bit j hi he; exact ⟨j,rfl,by omega⟩)
  intro b
  rw [card_live_of_lt (h := h) (fun w => by
    simpa [hz] using (ordered_run d h 0 hR hexit (fun i bit j hi _ => hstep i bit j hi)
      (List.ofFn w) z ⟨[],rfl⟩ (Nat.zero_le _)))]
  split_ifs with hb
  · exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hb)).symm
  · exact (Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 (by omega))).symm

private theorem restart_count {s : ℕ} {n : Fin s → Bool → Option (Fin s)} {z : Fin s}
    {p b : ℕ} (r : List Bool) (hr : r.length = p)
    (hrun : ∀ (u : List Bool) (v : List Bool), u.length = p → v.length = b →
      ((runWord n (some z) (u ++ v)).isSome ↔ u = r ∧ (runWord n (some z) v).isSome)) :
    live n z (p+b) = live n z b := by
  classical
  let r' : Fin p → Bool := fun i => r.get (Fin.cast hr.symm i)
  have hr' : List.ofFn r' = r := by
    apply List.ext_get
    · simp [hr]
    · intro i hi hri
      simp [r']
  let L (w : Fin (p+b) → Bool) : Fin p → Bool := fun i => w (Fin.castAdd b i)
  let R (w : Fin (p+b) → Bool) : Fin b → Bool := fun i => w (Fin.natAdd p i)
  have hchar (w : Fin (p+b) → Bool) :
      (runWord n (some z) (List.ofFn w)).isSome ↔
      L w = r' ∧ (runWord n (some z) (List.ofFn (R w))).isSome := by
    have hc : List.ofFn w = List.ofFn (L w) ++ List.ofFn (R w) := by
      rw [List.ofFn_add]
      congr 2
    rw [hc]
    simpa only [← hr', List.ofFn_inj] using
      (hrun (List.ofFn (L w)) (List.ofFn (R w)) (by simp) (by simp))
  unfold live
  apply Finset.card_bij (fun w _ => R w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar w).mp (Finset.mem_filter.mp hw).2 |>.2⟩
  · intro w hw v hv he
    have hl := ((hchar w).mp (Finset.mem_filter.mp hw).2).1.trans
      ((hchar v).mp (Finset.mem_filter.mp hv).2).1.symm
    funext i
    refine Fin.addCases ?_ ?_ i
    · exact congrFun hl
    · exact congrFun he
  · intro w hw
    refine ⟨Fin.append r' w, ?_, by funext i; simp [R]⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar _).mpr ⟨?_, ?_⟩⟩
    · funext i
      simp [L]
    · have hwr : R (Fin.append r' w) = w := by funext i; simp [R]
      rw [hwr]
      exact (Finset.mem_filter.mp hw).2

theorem restart_live {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (z : Fin s)
    (d : Fin s → ℕ) (h p : ℕ) (i₀ : Fin s) (bit₀ : Bool)
    (hp : 2 ≤ p) (hph : p ≤ h) (hz : d z=0) (stop : Stops n)
    (hexit : ∀ i bit, Reach n z i → n i bit=none → d i+1=h)
    (hstep : ∀ i bit j, Reach n z i → n i bit=some j → (i,bit) ≠ (i₀,bit₀) → d j=d i+1)
    (back : n i₀ bit₀=some z) (depth : d i₀+1=p)
    (unique : ∃ w : List Bool, w.length+1=p ∧ runWord n (some z) w=some i₀ ∧
      ∀ u : List Bool, u.length+1=p → runWord n (some z) u=some i₀ → u=w) :
    ∀ b, live n z b = 2^b % (2^h - 2^(h-p)) := by
  have hrank := rank_lt d h stop (z := z) (by
    intro i hi hid bit
    cases he : n i bit with
    | none => have := hexit i bit hi he; omega
    | some j =>
      have hne : (i,bit) ≠ (i₀,bit₀) := by
        intro hh
        have hh' : d i = d i₀ := congrArg (fun q : Fin s × Bool => d q.1) hh
        omega
      have := hstep i bit j hi he hne
      exact ⟨j,rfl,by omega⟩)
  have hshort (w : List Bool) (hw : w.length < p) :
      ∃ j, runWord n (some z) w = some j ∧ d j=w.length := by
    induction w using List.reverseRecOn with
    | nil => exact ⟨z,rfl,hz⟩
    | append_singleton u bit ih =>
      simp only [List.length_append, List.length_singleton] at hw ⊢
      obtain ⟨i,hi,hi'⟩ := ih (by omega)
      rw [run_snoc, hi]
      cases he : n i bit with
      | none => have := hexit i bit ⟨u,hi⟩ he; omega
      | some j =>
        have hne : (i,bit) ≠ (i₀,bit₀) := by
          intro hh
          have hh' : d i = d i₀ := congrArg (fun q : Fin s × Bool => d q.1) hh
          omega
        exact ⟨j,he,hstep _ _ _ ⟨u,hi⟩ he hne |>.trans (by omega)⟩
  obtain ⟨w₀,hw₀,hreach,huniq⟩ := unique
  let r := w₀ ++ [bit₀]
  have hr : r.length = p := by simpa [r] using hw₀
  have rr : runWord n (some z) r = some z := by rw [show r = w₀ ++ [bit₀] from rfl, run_snoc, hreach]; exact back
  have hnon (u v : List Bool) (hu : u.length = p) (hne : u ≠ r) :
      (runWord n (some z) (u ++ v)).isSome ↔ p+v.length < h := by
    cases u using List.reverseRecOn with
    | nil => simp at hu; omega
    | append_singleton u bit =>
      simp only [List.length_append, List.length_singleton] at hu
      obtain ⟨i,hi,hi'⟩ := hshort u (by omega)
      have he' : (i,bit) ≠ (i₀,bit₀) := by
        intro he
        injection he with hei heb
        subst i bit
        exact hne (by rw [huniq _ hu hi])
      rw [run_append, run_snoc, hi]
      change (runWord n (n i bit) v).isSome ↔ _
      cases he : n i bit with
      | none =>
        rw [none_run]
        have hh := hexit i bit ⟨u,hi⟩ he
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        omega
      | some j =>
        have hj := hstep i bit j ⟨u,hi⟩ he he'
        have hjr := next_reachable (show Reach n z i from ⟨u,hi⟩) he
        have hordered := ordered_run d h p hrank hexit (fun i bit j hi hid he =>
          hstep i bit j hi he (by
            intro hh
            have hh' : d i = d i₀ := congrArg (fun q : Fin s × Bool => d q.1) hh
            omega)) v j hjr (by omega)
        simpa only [show d j = p by omega] using hordered
  have hsurvive (w : List Bool) (hw : w.length < h) :
      ∃ i, runWord n (some z) w = some i ∧ d i ≤ w.length := by
    induction w using List.reverseRecOn with
    | nil => exact ⟨z,rfl,hz.le⟩
    | append_singleton u bit ih =>
      simp only [List.length_append, List.length_singleton] at hw ⊢
      obtain ⟨i,hi,hi'⟩ := ih (by omega)
      rw [run_snoc, hi]
      cases he : n i bit with
      | none => have := hexit i bit ⟨u,hi⟩ he; omega
      | some j =>
        refine ⟨j,he,?_⟩
        by_cases heq : (i,bit) = (i₀,bit₀)
        · injection heq with hei heb
          subst i bit
          have hj : j = z := Option.some.inj (he.symm.trans back)
          subst j
          omega
        · have := hstep i bit j ⟨u,hi⟩ he heq
          omega
  have noexit (b : ℕ) (hb : b < h) : live n z b = 2^b := by
    have hc := card_live_of_lt (h := h) (n := n) (z := z) (b := b) (fun w => by
      obtain ⟨i,hi,-⟩ := hsurvive (List.ofFn w) (by simpa using hb)
      simp [hi, hb])
    simpa [hb] using hc
  have hsmall (b : ℕ) (hb : b < h) : 2^b < 2^h - 2^(h-p) := by
    have H : h = (h-1)+1 := by omega
    have hbig : 2^h = 2^(h-1)*2 := (congrArg (fun k : ℕ => 2^k) H).trans (pow_succ _ _)
    have h₁ : (2:ℕ)^(h-p) < 2^(h-1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have h₂ : (2:ℕ)^b ≤ 2^(h-1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hperiod (b : ℕ) (hb : h ≤ b) : live n z b = live n z (b-p) := by
    have heq : p+(b-p)=b := Nat.add_sub_of_le (hph.trans hb)
    conv_lhs => rw [← heq]
    apply restart_count r hr
    intro u v hu hv
    by_cases he : u = r
    · simp [he, run_append, rr]
    · have hh : ¬ p + v.length < h := by omega
      simp [he, (hnon u v hu he).trans (iff_false_intro hh)]
  have hmod (b : ℕ) (hb : h ≤ b) : 2^b % (2^h - 2^(h-p)) = 2^(b-p) % (2^h - 2^(h-p)) := by
    have hbig : (2:ℕ)^(b-h)*2^h = 2^b := by rw [← pow_add, Nat.sub_add_cancel hb]
    have hsmall : (2:ℕ)^(b-h)*2^(h-p) = 2^(b-p) := by
      rw [← pow_add]
      congr 1
      omega
    have hdiff : (2:ℕ)^b = 2^(b-p) + 2^(b-h)*(2^h - 2^(h-p)) := by
      rw [Nat.mul_sub_left_distrib, hbig, hsmall]
      have hle : (2:ℕ)^(b-p) ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    conv_lhs => rw [hdiff]
    simp
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    by_cases hb : b < h
    · rw [noexit b hb, Nat.mod_eq_of_lt (hsmall b hb)]
    · rw [hperiod b (by omega), hmod b (by omega), ih (b-p) (by omega)]

end L29955Live

namespace L29955Upper

/- The frontier is indexed from left to right. If a layer has a restart twig,
its last child (a true edge) resets; all other children either advance or exit. -/

/- The paired-child sum and word ordinal adapt the layer decompositions in
`lean/PEqualNP/Outside/L_meta_29934.lean` at commit
`f8f579373fe16a8f1b7ff705930503e9add28b9f` to this binary tree with restart. -/

private def cut (J : Finset ℕ) (t : ℕ) : ℕ := if t ∈ J then 1 else 0

private def w (h : ℕ) (J : Finset ℕ) : ℕ → ℕ
  | 0 => 1
  | d+1 => 2*w h J d - cut J (h-(d+1))

private theorem cut_le (J : Finset ℕ) (t : ℕ) : cut J t ≤ 1 := by
  classical
  unfold cut
  split <;> omega

private theorem w_pos (h : ℕ) (J : Finset ℕ) (d : ℕ) : 0 < w h J d := by
  induction d with
  | zero => exact Nat.one_pos
  | succ d ih =>
    have := cut_le J (h-(d+1))
    simp only [w]
    omega

private theorem w_step (h : ℕ) (J : Finset ℕ) (d : ℕ) :
    w h J (d+1) + cut J (h-(d+1)) = 2*w h J d := by
  have := w_pos h J d
  have := cut_le J (h-(d+1))
  simp only [w]
  omega

private def tail (J : Finset ℕ) (t : ℕ) : Finset ℕ := J.filter (fun j => j < t)

private theorem tail_step (J : Finset ℕ) (t : ℕ) :
    tail J (t+1) = if t ∈ J then insert t (tail J t) else tail J t := by
  classical
  by_cases hj : t ∈ J
  · rw [ite_eq_left hj]
    ext j
    simp only [tail, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨ha, hb⟩
      by_cases he : j = t
      · exact Or.inl he
      · exact Or.inr ⟨ha, by omega⟩
    · rintro (rfl | ⟨ha,hb⟩)
      · exact ⟨hj, by omega⟩
      · exact ⟨ha, by omega⟩
  · rw [ite_eq_right hj]
    ext j
    simp only [tail, Finset.mem_filter]
    constructor
    · rintro ⟨ha,hb⟩
      refine ⟨ha, ?_⟩
      have hne : j ≠ t := by rintro rfl; exact hj ha
      omega
    · exact fun ⟨ha,hb⟩ => ⟨ha, by omega⟩

private theorem tail_sum (J : Finset ℕ) (t : ℕ) :
    (∑ j ∈ tail J (t+1), 2^j) = (∑ j ∈ tail J t, 2^j) + cut J t * 2^t := by
  classical
  have hn : t ∉ tail J t := by simp [tail]
  rw [tail_step]
  by_cases hj : t ∈ J <;> simp [hj, cut, Finset.sum_insert hn, add_comm]

private theorem tail_card (J : Finset ℕ) (t : ℕ) :
    (tail J (t+1)).card = (tail J t).card + cut J t := by
  classical
  have hn : t ∉ tail J t := by simp [tail]
  rw [tail_step]
  by_cases hj : t ∈ J <;> simp [hj, cut, Finset.card_insert_of_notMem hn]

private theorem tail_eq (J : Finset ℕ) (h : ℕ) (hJ : ∀ j ∈ J, j < h) : tail J h = J := by
  classical
  exact Finset.filter_true_of_mem hJ

private theorem width_balance {m h : ℕ} {J : Finset ℕ} (hJ : ∀ j ∈ J, j < h)
    (hm : m + (∑ j ∈ J, 2^j) = 2^h) {d : ℕ} (hd : d ≤ h) :
    w h J d * 2^(h-d) = m + (∑ j ∈ tail J (h-d), 2^j) := by
  classical
  induction d with
  | zero => simpa [w, tail_eq J h hJ] using hm.symm
  | succ d ih =>
    have he : h-d = (h-(d+1))+1 := by omega
    have hi := ih (by omega)
    rw [he, tail_sum, pow_succ] at hi
    rw [show w h J d * (2^(h-(d+1)) * 2) = (2*w h J d)*2^(h-(d+1)) by ac_rfl,
      ← w_step h J d, Nat.add_mul] at hi
    omega

private theorem width_end {m h : ℕ} {J : Finset ℕ} (hJ : ∀ j ∈ J, j < h)
    (hm : m + (∑ j ∈ J, 2^j) = 2^h) : w h J h = m := by
  classical
  simpa [tail] using width_balance hJ hm (d := h) le_rfl

private def size (h : ℕ) (J : Finset ℕ) : ℕ := ∑ d ∈ Finset.range h, w h J d

private theorem size_formula {m h : ℕ} {J : Finset ℕ} (hJ : ∀ j ∈ J, j < h)
    (hm : m + (∑ j ∈ J, 2^j) = 2^h) : size h J = m + J.card - 1 := by
  classical
  have H (d : ℕ) (hd : d ≤ h) :
      (∑ e ∈ Finset.range d, w h J e) + 1 + (tail J (h-d)).card = w h J d + J.card := by
    induction d with
    | zero => simp [w, tail_eq J h hJ]
    | succ d ih =>
      have he : h-d = h-(d+1)+1 := by omega
      have hi := ih (by omega)
      rw [he, tail_card] at hi
      rw [Finset.sum_range_succ]
      have := w_step h J d
      omega
  have hi := H h le_rfl
  simp [width_end hJ hm, tail] at hi
  unfold size
  omega

private theorem depth_le_size (h : ℕ) (J : Finset ℕ) : h ≤ size h J := by
  classical
  calc
    h = ∑ _ ∈ Finset.range h, 1 := by simp
    _ ≤ size h J := Finset.sum_le_sum (fun d _ => w_pos h J d)

private def child (i : ℕ) (bit : Bool) : ℕ := 2*i + if bit then 1 else 0

@[simp] private theorem child_false (i : ℕ) : child i false = 2*i := by simp [child]
@[simp] private theorem child_true (i : ℕ) : child i true = 2*i+1 := rfl

private abbrev State (h : ℕ) (J : Finset ℕ) := Σ d : Fin h, Fin (w h J d.val)

private def node {h : ℕ} {J : Finset ℕ} (d c : ℕ) (hd : d < h) (hc : c < w h J d) : State h J :=
  ⟨⟨d,hd⟩, ⟨c,hc⟩⟩

private def root {h : ℕ} {J : Finset ℕ} (hh : 0 < h) : State h J :=
  node 0 0 hh Nat.one_pos

private def step {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (i : State h J) (bit : Bool) : Option (State h J) :=
  if hc : child i.2.val bit < w h J (i.1.val+1) then
    if hd : i.1.val+1 < h then some (node _ _ hd hc) else none
  else some (root hh)

private theorem step_node {h : ℕ} {J : Finset ℕ} (hh : 0 < h)
    (d c : ℕ) (hd : d < h) (hc : c < w h J d) (bit : Bool) :
    step hh (node d c hd hc) bit =
      if hc' : child c bit < w h J (d+1) then
        if hd' : d+1 < h then some (node _ _ hd' hc') else none
      else some (root hh) := rfl

private theorem false_child_lt {h : ℕ} {J : Finset ℕ} (i : State h J) :
    child i.2.val false < w h J (i.1.val+1) := by
  have := i.2.isLt
  have := w_step h J i.1.val
  have := cut_le J (h-(i.1.val+1))
  simp only [child_false]
  omega

private theorem stops_state {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (i : State h J) :
    (fun o : Option (State h J) => o.bind (fun j => step hh j false))^[size h J] (some i) = none := by
  classical
  let f := fun o : Option (State h J) => o.bind (fun j => step hh j false)
  have hr (b : ℕ) (j : State h J) (e : f^[b] (some i) = some j) : i.1.val+b ≤ j.1.val := by
    induction b generalizing j with
    | zero =>
      have ej : i = j := Option.some.inj e
      simp [← ej]
    | succ b ih =>
      rw [Function.iterate_succ_apply'] at e
      cases he : f^[b] (some i) with
      | none => simp [he, f] at e
      | some l =>
        have hl : step hh l false = some j := by simpa [he, f] using e
        simp only [step, dite_eq_left (false_child_lt l)] at hl
        split at hl
        · simp only [Option.some.injEq] at hl
          have he' := congrArg (fun a : State h J => a.1.val) hl
          change l.1.val+1 = j.1.val at he'
          have := ih l he
          omega
        · simp at hl
  change f^[size h J] (some i) = none
  cases e : f^[size h J] (some i) with
  | none => rfl
  | some j =>
    have := hr _ j e
    have := j.1.isLt
    have := depth_le_size h J
    omega

private def pay {m h : ℕ} {J : Finset ℕ} (hm : 0 < m) (i : State h J) (bit : Bool) : Fin m :=
  if hv : child i.2.val bit < m then ⟨child i.2.val bit, hv⟩ else ⟨0,hm⟩

private noncomputable def potential {m h : ℕ} (J : Finset ℕ) (k : Fin m) : ℕ → ℕ → ℝ
  | 0, i => if i = k.val then 1 else 0
  | t+1, i =>
    let val := fun c => if c < w h J (h-t) then potential (h := h) J k t c else 1/(m:ℝ)
    (val (child i true) + val (child i false)) / 2

private theorem sum_children (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (f (child i true) + f (child i false))) =
      ∑ i ∈ Finset.range (2*n), f i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      show 2*(n+1) = (2*n+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [child_false, child_true]
    ring

private noncomputable def layer {m h : ℕ} (J : Finset ℕ) (k : Fin m) (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (w h J d), potential (h := h) J k (h-d) i

private theorem layer_step {m h : ℕ} (J : Finset ℕ) (k : Fin m) {d : ℕ} (hd : d < h) :
    2 * layer (h := h) J k d =
      layer (h := h) J k (d+1) + ↑(cut J (h-(d+1))) * (1/(m:ℝ)) := by
  classical
  let f := fun c => if c < w h J (d+1) then potential (h := h) J k (h-(d+1)) c else 1/(m:ℝ)
  have hd' : h-d = (h-(d+1))+1 := by omega
  have hb : h-(h-(d+1)) = d+1 := by omega
  unfold layer
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range (w h J d), (f (child i true) + f (child i false)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hd', potential, hb]
      dsimp [f]
      ring
    _ = ∑ i ∈ Finset.range (w h J (d+1) + cut J (h-(d+1))), f i := by
      rw [sum_children, w_step]
    _ = _ := by
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [f, Finset.mem_range.mp hi]
      · calc
          _ = ∑ _i ∈ Finset.range (cut J (h-(d+1))), (1/(m:ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hn : ¬ w h J (d+1) + i < w h J (d+1) := by omega
            simp [f, hn]
          _ = _ := by simp [nsmul_eq_mul]

private theorem potential_root {m h : ℕ} {J : Finset ℕ} (hJ : ∀ j ∈ J, j < h)
    (hm : m + (∑ j ∈ J, 2^j) = 2^h) (k : Fin m) :
    potential (h := h) J k h 0 = 1/(m:ℝ) := by
  classical
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by have := k.isLt; omega)
  have hend : layer (h := h) J k h = 1 := by
    unfold layer
    rw [width_end hJ hm, Nat.sub_self]
    simp only [potential]
    rw [Finset.sum_eq_single k.val]
    · simp
    · intro j hj hn
      simp [hn]
    · simp [Finset.mem_range.mpr k.isLt]
  have H (t : ℕ) (ht : t ≤ h) :
      (2:ℝ)^t * layer (h := h) J k (h-t) = 1 + (↑(∑ j ∈ tail J t, 2^j : ℕ) : ℝ)/(m:ℝ) := by
    induction t with
    | zero => simp [tail, hend]
    | succ t ih =>
      have he : h-(t+1)+1 = h-t := by omega
      have hs := layer_step J k (h := h) (d := h-(t+1)) (by omega)
      rw [he, show h-(h-t) = t by omega] at hs
      have hi := ih (by omega)
      rw [tail_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        _ = 2^t * (2 * layer (h := h) J k (h-(t+1))) := by ring
        _ = _ := by
          rw [hs, mul_add, hi]
          ring
  have hf := H h le_rfl
  rw [Nat.sub_self, tail_eq J h hJ] at hf
  have he : (m:ℝ) + ↑(∑ j ∈ J, 2^j : ℕ) = (2:ℝ)^h := by exact_mod_cast hm
  have hp : (2:ℝ)^h ≠ 0 := by positivity
  have hl : layer (h := h) J k 0 = 1/(m:ℝ) := by
    apply (mul_left_cancel₀ hp)
    rw [hf, ← he]
    field_simp
  simpa [layer, w] using hl

private theorem law_state {m h : ℕ} {J : Finset ℕ} (hh : 0 < h) (hm0 : 0 < m)
    (hJ : ∀ j ∈ J, j < h) (hm : m + (∑ j ∈ J, 2^j) = 2^h)
    (k : Fin m) (i : State h J) :
    2 * potential (h := h) J k (h-i.1.val) i.2.val = ∑ bit : Bool,
      (step hh i bit).elim (if pay hm0 i bit = k then 1 else 0)
        (fun j => potential (h := h) J k (h-j.1.val) j.2.val) := by
  classical
  have hd := i.1.isLt
  have he : h-i.1.val = (h-(i.1.val+1))+1 := by omega
  have hb : h-(h-(i.1.val+1)) = i.1.val+1 := by omega
  have hedge (bit : Bool) :
      (step hh i bit).elim (if pay hm0 i bit = k then 1 else 0)
        (fun j => potential (h := h) J k (h-j.1.val) j.2.val) =
      if child i.2.val bit < w h J (i.1.val+1) then
        potential (h := h) J k (h-(i.1.val+1)) (child i.2.val bit)
      else 1/(m:ℝ) := by
    by_cases hc : child i.2.val bit < w h J (i.1.val+1)
    · by_cases ht : i.1.val+1 < h
      · simp [step, hc, ht, node]
      · have he' : i.1.val+1 = h := by omega
        have hm' : child i.2.val bit < m := by rwa [he', width_end hJ hm] at hc
        simp [step, he', width_end hJ hm, hm', pay, potential, Fin.ext_iff]
    · simp [step, hc, root, node, potential_root hJ hm]
  rw [Fintype.sum_bool, hedge, hedge, he, potential, hb]
  ring

private def run {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (l : List Bool)
    (o : Option (State h J)) : Option (State h J) :=
  l.foldl (fun x bit => x.bind (fun i => step hh i bit)) o

private theorem run_none {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (l : List Bool) :
    run (J := J) hh l none = none := by
  classical
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

private theorem run_short {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (l : List Bool)
    (i : State h J) (hi : i.1.val+l.length < h) :
    ∃ j, run hh l (some i) = some j ∧ j.1.val ≤ i.1.val+l.length := by
  classical
  induction l generalizing i with
  | nil => exact ⟨i, rfl, by simp⟩
  | cons bit l ih =>
    simp only [List.length_cons] at hi ⊢
    have hd : i.1.val+1 < h := by omega
    have H : ∃ j, step hh i bit = some j ∧ j.1.val ≤ i.1.val+1 := by
      unfold step
      split
      · exact ⟨_, rfl, le_rfl⟩
      · exact ⟨_, rfl, Nat.zero_le _⟩
    obtain ⟨j,hj,hj'⟩ := H
    obtain ⟨k,hk,hk'⟩ := ih j (by omega)
    refine ⟨k, ?_, by omega⟩
    simpa only [run, List.foldl_cons, Option.bind_some, hj] using hk

private theorem child_lt {h : ℕ} {J : Finset ℕ} (i : State h J) (bit : Bool) :
    child i.2.val bit < 2*w h J i.1.val := by
  have := i.2.isLt
  cases bit <;> simp only [child_false, child_true] <;> omega

private theorem run_long {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (l : List Bool)
    (i : State h J) (hi : h ≤ i.1.val+l.length)
    (hc : ∀ d, i.1.val ≤ d → d < h → cut J (h-(d+1)) = 0) :
    run hh l (some i) = none := by
  classical
  induction l generalizing i with
  | nil =>
    have := i.1.isLt
    simp only [List.length_nil] at hi
    omega
  | cons bit l ih =>
    have hid := i.1.isLt
    have hs := w_step h J i.1.val
    rw [hc _ le_rfl hid, Nat.add_zero] at hs
    have hnext : child i.2.val bit < w h J (i.1.val+1) := hs ▸ child_lt i bit
    change run hh l (step hh i bit) = none
    rw [step, dite_eq_left hnext]
    split
    · rename_i hd
      apply ih
      · change h ≤ i.1.val+1+l.length
        simp only [List.length_cons] at hi
        omega
      · intro d hle hlt
        exact hc d (by change i.1.val+1 ≤ d at hle; omega) hlt
    · exact run_none hh l

private def ordinal : (b : ℕ) → (Fin b → Bool) → ℕ
  | 0, _ => 0
  | b+1, x => child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b))

private theorem ordinal_lt (b : ℕ) (x : Fin b → Bool) : ordinal b x < 2^b := by
  classical
  induction b with
  | zero => exact Nat.one_pos
  | succ b ih =>
    rw [ordinal, pow_succ]
    have hi := ih (fun i => x i.castSucc)
    cases x (Fin.last b) <;> simp only [child_true, child_false] <;> omega

private theorem ordinal_max (b : ℕ) (x : Fin b → Bool) :
    ordinal b x + 1 = 2^b ↔ x = fun _ => true := by
  classical
  induction b with
  | zero =>
    have h : x = fun _ => true := funext (fun i => i.elim0)
    simp [ordinal, h]
  | succ b ih =>
    rw [ordinal, pow_succ]
    have hi := ordinal_lt b (fun i => x i.castSucc)
    have hbits : x = (fun _ => true) ↔
        (fun i : Fin b => x i.castSucc) = (fun _ => true) ∧ x (Fin.last b) = true := by
      constructor
      · rintro rfl
        exact ⟨rfl,rfl⟩
      · rintro ⟨he,hl⟩
        funext i
        exact Fin.lastCases hl (congrFun he) i
    rw [hbits, ← ih (fun i => x i.castSucc)]
    by_cases hb : x (Fin.last b) = true
    · rw [hb, child_true]
      simp only [and_true]
      omega
    · have hf : x (Fin.last b) = false := Bool.eq_false_of_not_eq_true hb
      rw [hf, child_false]
      simp only [Bool.false_eq_true, and_false, iff_false]
      omega

private theorem width_pow {h : ℕ} {J : Finset ℕ} (b : ℕ)
    (hc : ∀ d < b, cut J (h-(d+1)) = 0) : w h J b = 2^b := by
  classical
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ]
    have hs := w_step h J b
    rw [hc b (by omega), Nat.add_zero, ih (fun d hd => hc d (by omega)), Nat.mul_comm] at hs
    exact hs

private theorem run_nocut {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (b : ℕ) (hb : b < h)
    (hc : ∀ d < b, cut J (h-(d+1)) = 0) (x : Fin b → Bool) :
    run hh (List.ofFn x) (some (root hh)) =
      some (node (J := J) b (ordinal b x) hb (by rw [width_pow b hc]; exact ordinal_lt b x)) := by
  classical
  induction b with
  | zero => rw [List.ofFn_zero]; rfl
  | succ b ih =>
    have hc' : ∀ d < b, cut J (h-(d+1)) = 0 := fun d hd => hc d (by omega)
    have hr := ih (by omega) hc' (fun i => x i.castSucc)
    have hs : ordinal (b+1) x < w h J (b+1) := by
      rw [width_pow (b+1) hc]
      exact ordinal_lt _ x
    simp only [run] at hr ⊢
    rw [List.ofFn_succ_last, List.foldl_append, hr]
    simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
    have hs' : child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b)) < w h J (b+1) := hs
    rw [step_node, dite_eq_left hs', dite_eq_left hb]
    rfl

private theorem run_single_prefix {h j p : ℕ} (hh : 0 < h) (hp : 0 < p)
    (hph : p ≤ h) (hj : h-p = j) (x : Fin p → Bool) :
    if x = (fun _ => true) then
      run (J := {j}) hh (List.ofFn x) (some (root hh)) = some (root hh)
    else if hlt : p < h then
      ∃ i, run (J := {j}) hh (List.ofFn x) (some (root hh)) = some i ∧ i.1.val = p
    else run (J := {j}) hh (List.ofFn x) (some (root hh)) = none := by
  classical
  obtain ⟨b,rfl⟩ : ∃ b, p = b+1 := ⟨p-1, by omega⟩
  have hc : ∀ d < b, cut ({j} : Finset ℕ) (h-(d+1)) = 0 := by
    intro d hd
    have hn : h-(d+1) ≠ j := by omega
    simp [cut, hn]
  have hw := w_step h ({j} : Finset ℕ) b
  rw [hj, show cut ({j} : Finset ℕ) j = 1 by simp [cut], width_pow b hc] at hw
  have he : ordinal (b+1) x < w h ({j} : Finset ℕ) (b+1) ↔ x ≠ (fun _ => true) := by
    simp only [ne_eq, ← ordinal_max (b+1) x]
    have ho := ordinal_lt (b+1) x
    rw [pow_succ] at ho
    omega
  have hr := run_nocut hh b (by omega) hc (fun i => x i.castSucc)
  simp only [run] at hr ⊢
  rw [List.ofFn_succ_last, List.foldl_append, hr]
  simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
  have hChild : child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b)) = ordinal (b+1) x := rfl
  by_cases hx : x = (fun _ => true)
  · have hn : ¬ child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b)) < w h ({j} : Finset ℕ) (b+1) := by
      rw [hChild]
      exact fun ht => (he.mp ht) hx
    rw [ite_eq_left hx, step_node, dite_eq_right hn]
  · have ht : child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b)) < w h ({j} : Finset ℕ) (b+1) := by
      rw [hChild]
      exact he.mpr hx
    rw [ite_eq_right hx, step_node, dite_eq_left ht]
    by_cases hp' : b+1 < h
    · rw [dite_eq_left hp', dite_eq_left hp']
      exact ⟨node _ _ hp' ht, rfl, rfl⟩
    · rw [dite_eq_right hp', dite_eq_right hp']

private theorem run_single_long {h j p b : ℕ} (hh : 0 < h) (hp : 0 < p)
    (hj : h-p=j) (hb : h ≤ p+b) (hph : p ≤ h)
    (x : Fin p → Bool) (y : Fin b → Bool) :
    (run (J := {j}) hh (List.ofFn (Fin.append x y)) (some (root hh))).isSome = true ↔
      x = (fun _ => true) ∧ (run (J := {j}) hh (List.ofFn y) (some (root hh))).isSome = true := by
  classical
  rw [List.ofFn_fin_append]
  simp only [run, List.foldl_append]
  change (run hh (List.ofFn y) (run hh (List.ofFn x) (some (root hh)))).isSome = true ↔ _
  have hr := run_single_prefix hh hp hph hj x
  by_cases hx : x = (fun _ => true)
  · rw [ite_eq_left hx] at hr
    rw [hr]
    simp only [hx, true_and]
    rfl
  · rw [ite_eq_right hx] at hr
    have hn : run (J := {j}) hh (List.ofFn y) (run hh (List.ofFn x) (some (root hh))) = none := by
      by_cases ht : p < h
      · rw [dite_eq_left ht] at hr
        obtain ⟨i,hi,hi'⟩ := hr
        rw [hi]
        apply run_long
        · simpa only [List.length_ofFn, hi'] using hb
        · intro d hd hd'
          have hn : h-(d+1) ≠ j := by omega
          simp [cut, hn]
      · rw [dite_eq_right ht] at hr
        rw [hr, run_none]
    simp [hn, hx]

private theorem card_state (h : ℕ) (J : Finset ℕ) : Fintype.card (State h J) = size h J := by
  classical
  simp [State, size, Fin.sum_univ_eq_sum_range]

private noncomputable def encode (h : ℕ) (J : Finset ℕ) : State h J ≃ Fin (size h J) :=
  Fintype.equivFinOfCardEq (card_state h J)

private noncomputable def next {h : ℕ} {J : Finset ℕ} (hh : 0 < h)
    (i : Fin (size h J)) (bit : Bool) : Option (Fin (size h J)) :=
  (step hh ((encode h J).symm i) bit).map (encode h J)

private noncomputable def start {h : ℕ} {J : Finset ℕ} (hh : 0 < h) : Fin (size h J) :=
  encode h J (root hh)

private theorem step_map {h : ℕ} {J : Finset ℕ} (hh : 0 < h)
    (o : Option (State h J)) (bit : Bool) :
    (o.map (encode h J)).bind (fun i => next hh i bit) =
      (o.bind (fun j => step hh j bit)).map (encode h J) := by
  classical
  cases o <;> simp [next]

private theorem run_map {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (l : List Bool)
    (o : Option (State h J)) :
    l.foldl (fun (x : Option (Fin (size h J))) bit => x.bind (fun i => next hh i bit))
      (o.map (encode h J)) = (run hh l o).map (encode h J) := by
  classical
  induction l generalizing o with
  | nil => rfl
  | cons bit l ih =>
    simp only [List.foldl_cons, run]
    rw [step_map, ih]
    rfl

private theorem stops_fin {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (i : Fin (size h J)) :
    (fun o : Option (Fin (size h J)) => o.bind (fun j => next hh j false))^[size h J]
      (some i) = none := by
  classical
  let e := encode h J
  let f := fun o : Option (Fin (size h J)) => o.bind (fun j => next hh j false)
  let g := fun o : Option (State h J) => o.bind (fun j => step hh j false)
  have H (b : ℕ) : f^[b] (some i) = (g^[b] (some (e.symm i))).map e := by
    induction b with
    | zero => simp [e]
    | succ b ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact step_map hh _ false
  change f^[size h J] (some i) = none
  rw [H, stops_state hh]
  rfl

private def alive {h : ℕ} (J : Finset ℕ) (hh : 0 < h) (b : ℕ) (x : Fin b → Bool) : Prop :=
  (run (J := J) hh (List.ofFn x) (some (root hh))).isSome = true

private noncomputable def liveCount {h : ℕ} (J : Finset ℕ) (hh : 0 < h) (b : ℕ) : ℕ := by
  classical
  exact Fintype.card (Subtype (alive J hh b))

private theorem live_eq {h : ℕ} {J : Finset ℕ} (hh : 0 < h) (b : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter (fun x =>
      ((List.ofFn x).foldl (fun (o : Option (Fin (size h J))) bit =>
        o.bind (fun i => next hh i bit)) (some (start hh))).isSome)).card =
    liveCount J hh b := by
  classical
  rw [liveCount, Fintype.card_subtype]
  congr 1
  apply Finset.ext
  intro x
  rw [Finset.mem_filter_univ, Finset.mem_filter_univ]
  unfold alive
  have he : some (start (J := J) hh) = (some (root (J := J) hh)).map (encode h J) := rfl
  rw [he, run_map]
  cases run (J := J) hh (List.ofFn x) (some (root hh)) <;> rfl

private theorem live_short {h b : ℕ} (J : Finset ℕ) (hh : 0 < h) (hb : b < h) :
    liveCount J hh b = 2^b := by
  classical
  have H (x : Fin b → Bool) : alive J hh b x := by
    obtain ⟨i,hi,_⟩ := run_short hh (List.ofFn x) (root (J := J) hh) (by simpa [root,node] using hb)
    simp [alive, hi]
  rw [liveCount, Fintype.card_subtype, Finset.filter_true_of_mem (fun x _ => H x)]
  simp

private theorem live_empty {h : ℕ} (hh : 0 < h) (b : ℕ) (hb : h ≤ b) :
    liveCount ∅ hh b = 0 := by
  classical
  have H (x : Fin b → Bool) : ¬ alive ∅ hh b x := by
    have hn := run_long hh (List.ofFn x) (root (J := (∅ : Finset ℕ)) hh)
      (by simpa [root,node] using hb) (by simp [cut])
    simp [alive, hn]
  rw [liveCount, Fintype.card_subtype, Finset.filter_false_of_mem (fun x _ => H x)]
  rfl

private theorem live_single_step {h j p b : ℕ} (hh : 0 < h) (hp : 0 < p)
    (hph : p ≤ h) (hj : h-p=j) (hb : h ≤ p+b) :
    liveCount {j} hh (p+b) = liveCount {j} hh b := by
  classical
  let pref := fun x : Fin (p+b) → Bool => fun i : Fin p => x (Fin.castAdd b i)
  let suff := fun x : Fin (p+b) → Bool => fun i : Fin b => x (Fin.natAdd p i)
  have H (x : Fin (p+b) → Bool) :
      alive {j} hh (p+b) x ↔ pref x = (fun _ => true) ∧ alive {j} hh b (suff x) := by
    have he : Fin.append (pref x) (suff x) = x := Fin.append_castAdd_natAdd
    simpa only [alive, he] using run_single_long hh hp hj hb hph (pref x) (suff x)
  let e : Subtype (alive {j} hh (p+b)) ≃ Subtype (alive {j} hh b) :=
    { toFun := fun x => ⟨suff x.val, ((H x.val).mp x.property).2⟩
      invFun := fun y => ⟨Fin.append (fun _ => true) y.val,
        (run_single_long hh hp hj hb hph (fun _ => true) y.val).mpr ⟨rfl,y.property⟩⟩
      left_inv := fun x => Subtype.ext (by
        change Fin.append (fun _ => true) (suff x.val) = x.val
        rw [← ((H x.val).mp x.property).1]
        exact Fin.append_castAdd_natAdd)
      right_inv := fun y => Subtype.ext (by
        funext i
        change Fin.append (fun _ : Fin p => true) y.val (Fin.natAdd p i) = y.val i
        exact Fin.append_right _ _ _) }
  exact Fintype.card_congr e

/-- A binary machine with a uniform exit label and, when requested, the remainder live count. -/
def Realize (m s : ℕ) (sharp : Bool) : Prop :=
  ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (label : Fin s → Bool → Fin m) (v : Fin m → Fin s → ℝ),
    (∃ c : Fin s → Bool, ∀ i : Fin s,
      (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none) ∧
    (∀ k : Fin m, ∀ i : Fin s, 2*v k i = ∑ bit : Bool,
      (n i bit).elim (if label i bit = k then 1 else 0) (v k)) ∧
    (∀ k, v k z = 1/(m:ℝ)) ∧
    (sharp = true → ∀ b : ℕ,
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun x =>
        ((List.ofFn x).foldl (fun (o : Option (Fin s)) bit => o.bind (fun i => n i bit))
            (some z)).isSome)).card = 2^b % m)

private theorem construct {m h : ℕ} {J : Finset ℕ} (hh : 0 < h) (hm0 : 0 < m)
    (hJ : ∀ j ∈ J, j < h) (hm : m + (∑ j ∈ J, 2^j) = 2^h) (sharp : Bool)
    (hs : sharp = true → ∀ b, liveCount J hh b = 2^b % m) : Realize m (m+J.card-1) sharp := by
  classical
  rw [← size_formula hJ hm]
  let v : Fin m → Fin (size h J) → ℝ := fun k i =>
    let j := (encode h J).symm i
    potential (h := h) J k (h-j.1.val) j.2.val
  refine ⟨start hh, next hh, (fun i bit => pay hm0 ((encode h J).symm i) bit), v,
    ⟨fun _ => false, stops_fin hh⟩, ?_, ?_, ?_⟩
  · intro k i
    have H (bit : Bool) :
        (next hh i bit).elim (if pay hm0 ((encode h J).symm i) bit = k then 1 else 0) (v k) =
        (step hh ((encode h J).symm i) bit).elim
          (if pay hm0 ((encode h J).symm i) bit = k then 1 else 0)
          (fun j => potential (h := h) J k (h-j.1.val) j.2.val) := by
      unfold next
      cases step hh ((encode h J).symm i) bit with
      | none => rfl
      | some j =>
        change v k (encode h J j) = _
        unfold v
        rw [Equiv.symm_apply_apply]
        rfl
    simpa only [H, v] using law_state hh hm0 hJ hm k ((encode h J).symm i)
  · intro k
    unfold v start
    rw [Equiv.symm_apply_apply]
    exact potential_root hJ hm k
  · intro hs' b
    rw [live_eq, hs hs']

theorem missingPowers (m : ℕ) (hm : 2 ≤ m) (h : ℕ) (J : Finset ℕ) (hJ : ∀ j ∈ J, j < h)
    (he : m + (∑ j ∈ J, 2^j) = 2^h) : Realize m (m+J.card-1) false := by
  classical
  have hh : 0 < h := by
    by_contra! hn
    have hh : h = 0 := by omega
    simp [hh] at he
    omega
  exact construct hh (by omega) hJ he false (by simp)

theorem dyadic (m : ℕ) (hm : 2 ≤ m) (hm' : ∃ a : ℕ, m = 2^a) : Realize m (m-1) true := by
  classical
  obtain ⟨h,rfl⟩ := hm'
  have hh : 0 < h := by
    by_contra! hn
    have hh : h = 0 := by omega
    simp [hh] at hm
  have hs (b : ℕ) : liveCount ∅ hh b = 2^b % 2^h := by
    by_cases hb : b < h
    · rw [live_short ∅ hh hb, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb)]
    · rw [live_empty hh b (by omega), Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 (by omega))]
  simpa using construct (J := ∅) (m := 2^h) hh (by omega) (by simp) (by simp) true (fun _ => hs)

private theorem block_mass (a p : ℕ) :
    2^a * (2^p-1) + 2^a = 2^(a+p) := by
  classical
  have h1 : 1 ≤ 2^p := (pow_pos Nat.two_pos _)
  calc
    _ = 2^a*((2^p-1)+1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel h1, pow_add]

private theorem block_count (a p : ℕ) (hp : 2 ≤ p) (hh : 0 < a+p) (b : ℕ) :
    liveCount {a} hh b = 2^b % (2^a*(2^p-1)) := by
  classical
  let m := 2^a*(2^p-1)
  have hm : m+2^a = 2^(a+p) := block_mass a p
  change liveCount {a} hh b = 2^b % m
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases hb : b < a+p
    · have h₁ : 2^a < 2^(a+p-1) := Nat.pow_lt_pow_right (by decide) (by omega)
      have h₂ : 2^b ≤ 2^(a+p-1) := Nat.pow_le_pow_right (by decide) (by omega)
      have h₃ : 2^(a+p) = 2^(a+p-1)*2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h₃] at hm
      rw [live_short {a} hh hb, Nat.mod_eq_of_lt (by omega)]
    · have hb' : b = p+(b-p) := by omega
      have hs := live_single_step (j := a) (p := p) (b := b-p) hh (by omega)
        (by omega) (by omega) (by omega)
      rw [← hb', ih (b-p) (by omega)] at hs
      rw [hs]
      obtain ⟨d, hd⟩ : ∃ d, b-p = a+d := ⟨b-p-a, by omega⟩
      have he : 2^b = m*2^d+2^(b-p) := by
        have hbd : b = (a+p)+d := by omega
        have hf : 2^b = 2^(a+p)*2^d := by rw [hbd, pow_add]
        have hg : 2^(b-p) = 2^a*2^d := by rw [hd, pow_add]
        rw [hf, hg, ← hm, Nat.add_mul]
      conv_rhs => rw [he, Nat.mul_add_mod]

theorem block (m : ℕ) (hm : 2 ≤ m) (hm' : ∃ a p : ℕ, 2 ≤ p ∧ m = 2^a*(2^p-1)) :
    Realize m m true := by
  classical
  obtain ⟨a,p,hp,rfl⟩ := hm'
  have hh : 0 < a+p := by omega
  have H := construct (J := {a}) (m := 2^a*(2^p-1)) hh (by omega)
    (by simpa using (show a < a+p by omega)) (by simpa using block_mass a p) true
    (fun _ => block_count a p hp hh)
  simpa using H

end L29955Upper

end PEqualNP.Outside.L_meta_29955_aux

open PEqualNP.Outside.L_meta_29955_aux

theorem PEqualNP.Outside.L_meta_29955 :
∀ (m E : ℕ), 2 ≤ m → 0 < E →
  let q := m*E
  ∀ (N t : ℕ), q ≤ N → q < 2*t → t < q →
  let X := Fin N
  let I := Fin q
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun C : Circ =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  ∀ (base : Circ), legal base → ∀ f : I → Equiv.Perm X,
    (∀ x : X, Function.Injective (fun j => f j x)) →
    let loss := fun (H : X → X → Bool) (D : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 ≠
        xor (table base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card
    let fits := fun C : Circ => legal C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size+2*E+3 ∧ loss (table C) ∅ ≤ E
    let ideal := ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)
    let run := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (b : ℕ) (w : Fin b → Bool) =>
      (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) =>
        x.bind (fun i => n i bit)) (some z)
    let live := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ) =>
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (run s z n b w).isSome)).card
    let law := fun (s : ℕ) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ) =>
      (∃ c : Fin s → Bool, ∀ i : Fin s,
        (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none) ∧
      ∀ i D, 2*L i D = ∑ bit : Bool, (n i bit).elim (loss (H i bit) D : ℝ) (fun j => L j D)
    let dyadic := ∃ a : ℕ, m = 2^a
    let block := ∃ a p : ℕ, 2 ≤ p ∧ m = 2^a*(2^p-1)
    let realize := fun (s : ℕ) (sharp : Bool) =>
      ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (C : Fin s → Bool → Circ)
          (L : Fin s → Finset I → ℝ),
        law s n (fun i bit => table (C i bit)) L ∧ (∀ i bit, fits (C i bit)) ∧
        (∀ U : Finset I, U.card = t → L z U = ideal) ∧
        (sharp = true → ∀ b : ℕ, live s z n b = 2^b % m)
    (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ),
      law s n H L → (∀ i bit, loss (H i bit) ∅ ≤ E) →
      (∀ U : Finset I, U.card = t → L z U ≤ ideal) →
      m ≤ s+1 ∧ (s+1 = m → dyadic ∧ ∀ b : ℕ, live s z n b = 2^b % m) ∧
      (¬ dyadic → s ≤ m → s = m ∧ block ∧ ∀ b : ℕ, live s z n b = 2^b % m)) ∧
    (dyadic → realize (m-1) true) ∧ (block → realize m true) ∧
    ∀ (h : ℕ) (J : Finset ℕ), (∀ j ∈ J, j < h) →
      m + (∑ j ∈ J, 2^j) = 2^h → realize (m+J.card-1) false
:= by
  classical
  intro m E hm hE q N t hN htq ht X I Circ legal table base hbase f hf loss fits ideal run live law
    dyadic block realize
  have hm' : 0 < m := by omega
  have hq : 0 < q := Nat.mul_pos hm' hE
  have hEq : E < q := by
    simpa only [q, one_mul] using Nat.mul_lt_mul_of_pos_right (show 1 < m by omega) hE
  letI : NeZero q := ⟨hq.ne'⟩
  have hLower (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ)
      (hLaw : law s n H L) (hLoss : ∀ i bit, loss (H i bit) ∅ ≤ E)
      (hOpt : ∀ U : Finset I, U.card = t → L z U ≤ ideal) :
      m ≤ s+1 ∧ (s+1 = m → dyadic ∧ ∀ b : ℕ, live s z n b = 2^b % m) ∧
      (¬ dyadic → s ≤ m → s = m ∧ block ∧ ∀ b : ℕ, live s z n b = 2^b % m) := by
    have hO (D : Finset I) (hD : D.card = t) : L z D ≤ (N : ℝ)*t+(1-2*(t : ℝ)/q)*E :=
      (hOpt D hD).trans_eq (ideal_eq hq ht htq.le hN hEq)
    obtain ⟨A,hA,-,-,hroot⟩ := optimal_harm hf (table base) H L z hLaw.1
      (fun D i => hLaw.2 i D) hLoss ht htq hO
    let a (j : I) (i : Fin s) (bit : Bool) := (edits (table base) (H i bit) ∩ graph f j).card
    have hcap (i : Fin s) (bit : Bool) : (∑ j, a j i bit) ≤ E := by
      have hT : (edits (table base) (H i bit)).card ≤ E := by
        simpa only [score_empty] using (show score (table base) f (H i bit) ∅ ≤ E from hLoss i bit)
      change (∑ j, (edits (table base) (H i bit) ∩ graph f j).card) ≤ E
      rw [← inter_flips_card hf]
      exact (Finset.card_le_card Finset.inter_subset_left).trans hT
    obtain ⟨hExit,hU⟩ := terminal_balance hE hm' z hLaw.1 a A hcap hA hroot
    have hEvent : ∃ (u : Fin s → Bool → ℕ) (v : Fin s → ℝ),
        Harm n (fun i bit => (u i bit : ℝ)) v ∧ v z = 1/(m : ℝ) := by
      let j : I := ⟨0,hq⟩
      refine ⟨a j, A j, hA j, ?_⟩
      rw [hroot]
      change (E : ℝ)/((m*E : ℕ) : ℝ) = _
      rw [Nat.cast_mul]
      have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
      have hm'' : (m : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
      field_simp
    obtain ⟨hb,hTree,hRestart⟩ := L29955Lower.classification n z m hm hExit hU hEvent
    refine ⟨hb, ?_, ?_⟩
    · intro hs
      obtain ⟨d,h,hmh,hz,he,hd⟩ := hTree hs
      refine ⟨⟨h,hmh⟩, ?_⟩
      intro b
      have hl := L29955Live.tree_live n z d h hz hLaw.1 he hd b
      exact hmh.symm ▸ hl
    · intro hn hs
      obtain ⟨hsm,d,h,p,k,hp,hph,hmh,hmBlock,hz,he,hd,hback,hdepth,hunique⟩ :=
        hRestart hn hs
      refine ⟨hsm, ⟨h-p,p,hp,hmBlock⟩, ?_⟩
      intro b
      have hl := L29955Live.restart_live n z d h p k.1 k.2 hp hph hz hLaw.1 he hd
        hback hdepth hunique b
      exact hmh.symm ▸ hl
  have hReal (s : ℕ) (sharp : Bool) (hr : L29955Upper.Realize m s sharp) :
      realize s sharp := by
    obtain ⟨z,n,label,v,hstop,harm,hroot,hLive⟩ := hr
    obtain ⟨a,A,ha,hA,hrootA⟩ := labels_to_matching hm' hE z label v harm hroot
    obtain ⟨C,L,hL,hC,hO⟩ := realize_from_machine hq hE hEq hN ht htq base hbase hf
      (z := z) hstop a A ha hA hrootA
    exact ⟨z,n,C,L,⟨hstop,fun i D => hL D i⟩,hC,hO,hLive⟩
  exact ⟨hLower, fun h => hReal _ _ (L29955Upper.dyadic m hm h),
    fun h => hReal _ _ (L29955Upper.block m hm h),
    fun h J hJ heq => hReal _ _ (L29955Upper.missingPowers m hm h J hJ heq)⟩

