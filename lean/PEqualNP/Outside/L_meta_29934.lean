import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29934_aux

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

private def outcome {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    (Fin s ⊕ (Fin s × Bool)) → Bool → (Fin s ⊕ (Fin s × Bool))
  | .inl i, e => (n i e).elim (.inr (i, e)) .inl
  | .inr t, _ => .inr t

private def path {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (z : Fin s)
    {b : ℕ} (w : Fin b → Bool) : Fin s ⊕ (Fin s × Bool) :=
  (List.ofFn w).foldl (outcome n) (.inl z)

private def mass {s : ℕ} (a : Fin s → Bool → ℝ) (v : Fin s → ℝ) :
    (Fin s ⊕ (Fin s × Bool)) → ℝ
  | .inl i => v i
  | .inr t => a t.1 t.2

private theorem path_sum {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {a : Fin s → Bool → ℝ} {v : Fin s → ℝ} (hv : Harm n a v) (b : ℕ) (z : Fin s) :
    ∑ w : Fin b → Bool, mass a v (path n z w) = 2 ^ b * v z := by
  classical
  induction b generalizing z with
  | zero => simp [path, mass, List.ofFn_zero]
  | succ b ih =>
    let ec : Bool × (Fin b → Bool) ≃ (Fin (b + 1) → Bool) := Fin.consEquiv (fun _ => Bool)
    rw [← Equiv.sum_comp ec, Fintype.sum_prod_type, Fintype.sum_bool]
    have hs (e : Bool) :
        (∑ w : Fin b → Bool, mass a v (path n z (ec (e,w)))) =
          2 ^ b * (n z e).elim (a z e) v := by
      have hec (w : Fin b → Bool) : ec (e,w) = Fin.cons e w := rfl
      have htail (l : List Bool) (t : Fin s × Bool) :
          l.foldl (outcome n) (.inr t) = .inr t := by
        induction l with
        | nil => rfl
        | cons _ _ h => exact h
      simp only [hec, path, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.foldl_cons, outcome]
      cases hn : n z e with
      | none => simp [htail, mass]
      | some j => exact ih j
    have hv' := hv z
    rw [Fintype.sum_bool] at hv'
    rw [hs false, hs true, ← mul_add, ← hv', pow_succ]
    ring

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

private def active {s : ℕ} : (Fin s ⊕ (Fin s × Bool)) → Option (Fin s)
  | .inl i => some i
  | .inr _ => none

private theorem active_fold {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (l : List Bool)
    (x : Fin s ⊕ (Fin s × Bool)) :
    active (l.foldl (outcome n) x) =
      l.foldl (fun x e => x.bind (fun y => n y e)) (active x) := by
  induction l generalizing x with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    cases x with
    | inr p => rfl
    | inl i => cases h : n i e <;> simp [active, outcome, h]

private def liveCount {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (b : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin b → Bool => (active (path n z w)).isSome)).card

private theorem sharp_lower {s q E : ℕ} (hq : 0 < q) (hE : 0 < E)
    {n : Fin s → Bool → Option (Fin s)} (z : Fin s)
    (a : Fin q → Fin s → Bool → ℕ) (v : Fin q → Fin s → ℝ)
    (hh : ∀ j, Harm n (fun i e => (a j i e : ℝ)) (v j))
    (hn : ∀ j i, 0 ≤ v j i) (hcap : ∀ i, (∑ j, v j i) ≤ E)
    (hroot : ∀ j, v j z = (E : ℝ)/q) (b : ℕ) :
    ((2^b*E % q)+E-1)/E ≤ liveCount z n b := by
  classical
  let P := path n z (b := b)
  let W := (Finset.univ : Finset (Fin b → Bool))
  let A := W.filter (fun w => (active (P w)).isSome)
  let St := fun (j : Fin q) w => (P w).elim (fun _ => 0) (fun p => a j p.1 p.2)
  let Rem := fun (j : Fin q) w => (P w).elim (v j) (fun _ => 0)
  let K := 2^b * E
  have hk (j : Fin q) :
      (∑ w ∈ W, (St j w : ℝ)) + ∑ w ∈ W, Rem j w = (K : ℝ)/q := by
    rw [← Finset.sum_add_distrib]
    have hp := path_sum (hh j) b z
    rw [hroot j] at hp
    have hpiece (w : Fin b → Bool) :
        (St j w : ℝ) + Rem j w = mass (fun i e => (a j i e : ℝ)) (v j) (P w) := by
      cases he : P w <;> simp [St, Rem, he, mass]
    simpa only [hpiece, K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using hp
  have hcast (j : Fin q) : (∑ w ∈ W, (St j w : ℝ)) ≤ ((K/q : ℕ) : ℝ) := by
    have hnon : 0 ≤ ∑ w ∈ W, Rem j w := by
      apply Finset.sum_nonneg
      intro w _
      cases he : P w <;> simp [Rem, he, hn]
    have hr : (∑ w ∈ W, (St j w : ℝ)) ≤ (K : ℝ)/q := by linarith [hk j]
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    have hs : (∑ w ∈ W, St j w) * q ≤ K := by
      exact_mod_cast (le_div_iff₀ hq').mp hr
    exact_mod_cast (Nat.le_div_iff_mul_le hq).2 hs
  have htail : (∑ j, ∑ w ∈ W, Rem j w) ≤ (A.card : ℝ)*E := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ w ∈ W, if (active (P w)).isSome then (E : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro w _
        cases he : P w <;> simp [Rem, he, active, hcap]
      _ = _ := by rw [← Finset.sum_filter]; simp [A, nsmul_eq_mul]
  have heq := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin q)) = Finset.univ)
    (fun j _ => hk j)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hq.ne' : (q : ℝ) ≠ 0)] at heq
  have hs : (∑ j : Fin q, ∑ w ∈ W, (St j w : ℝ)) ≤ (q : ℝ)*(K/q : ℕ) := by
    calc
      _ ≤ ∑ _ : Fin q, ((K/q : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hcast j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hh₀ : (K : ℝ) ≤ (q : ℝ)*(K/q : ℕ) + (A.card : ℝ)*E := by linarith
  have hh : K ≤ q*(K/q) + A.card*E := by exact_mod_cast hh₀
  have hr := Nat.mod_add_div K q
  have hle : K%q ≤ A.card*E := by omega
  change (K%q+E-1)/E ≤ A.card
  apply (Nat.div_le_iff_le_mul_add_pred hE).2
  have hm : K%q ≤ E*A.card := by simpa only [Nat.mul_comm E A.card] using hle
  omega

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

private def batchR (q E b : ℕ) := 2 ^ b * E % q
private def batchBeta (q E b : ℕ) := (2 * batchR q E b) / q
private def batchWidth (q E b : ℕ) := (batchR q E b + E - 1) / E
private def batchCap (q E b : ℕ) := E * batchWidth q E b - batchR q E b
private def batchLeaves (q E b : ℕ) := 2 * batchWidth q E b - batchWidth q E (b + 1)

private theorem batchR_mod (q E b : ℕ) :
    batchR q E (b + 1) = (2 * batchR q E b) % q := by
  unfold batchR
  rw [show 2 ^ (b + 1) * E = 2 * (2 ^ b * E) by rw [pow_succ]; ring]
  rw [← Nat.mul_mod_mod]

private theorem batchR_succ (q E b : ℕ) :
    batchR q E (b + 1) + q * batchBeta q E b = 2 * batchR q E b := by
  rw [batchR_mod]
  exact Nat.mod_add_div _ _

private theorem batchBeta_le_one {q E : ℕ} (hq : 0 < q) (b : ℕ) :
    batchBeta q E b ≤ 1 := by
  have hr := Nat.mod_lt (2 ^ b * E) hq
  change batchR q E b < q at hr
  have hh : (2 * batchR q E b) / q < 2 :=
    (Nat.div_lt_iff_lt_mul hq).2 (by omega)
  change (2 * batchR q E b) / q ≤ 1
  omega

private theorem batchCeil_spec {E : ℕ} (he : 0 < E) (r : ℕ) :
    r ≤ E * ((r + E - 1) / E) ∧ E * ((r + E - 1) / E) < r + E := by
  let w := (r + E - 1) / E
  have hlo : w * E ≤ r + E - 1 := (Nat.le_div_iff_mul_le he).1 (le_refl w)
  have hhi : r + E - 1 < (w + 1) * E :=
    (Nat.div_lt_iff_lt_mul he).1 (show w < w + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hhi
  rw [Nat.mul_comm w E] at hlo hhi
  change r ≤ E * w ∧ E * w < r + E
  omega

private theorem batchCeil_le {E r n : ℕ} (he : 0 < E) (hr : r ≤ E * n) :
    (r + E - 1) / E ≤ n := by
  have h : (r + E - 1) / E < n + 1 := (Nat.div_lt_iff_lt_mul he).2 (by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n E]
    omega)
  omega

private theorem batchCover {q E : ℕ} (he : 0 < E) (b : ℕ) :
    batchR q E b + batchCap q E b = E * batchWidth q E b := by
  have hs := (batchCeil_spec he (batchR q E b)).1
  unfold batchCap
  change batchR q E b ≤ E * batchWidth q E b at hs
  omega

private theorem batchCap_lt {q E : ℕ} (he : 0 < E) (b : ℕ) : batchCap q E b < E := by
  have hs := (batchCeil_spec he (batchR q E b)).2
  change E * batchWidth q E b < batchR q E b + E at hs
  unfold batchCap
  omega

private theorem batchWidth_zero {q E : ℕ} (he : 0 < E) (hlt : E < q) :
    batchWidth q E 0 = 1 := by
  have hr : batchR q E 0 = E := by simp [batchR, Nat.mod_eq_of_lt hlt]
  have hlo := (batchCeil_spec he E).1
  have hhi := batchCeil_le he (show E ≤ E * 1 by simp)
  have hp : 0 < (E + E - 1) / E := by
    by_contra! hz
    have hz' : (E + E - 1) / E = 0 := Nat.eq_zero_of_le_zero hz
    rw [hz', Nat.mul_zero] at hlo
    exact (not_le_of_gt he) hlo
  unfold batchWidth
  rw [hr]
  omega

private theorem batchCap_zero {q E : ℕ} (he : 0 < E) (hlt : E < q) :
    batchCap q E 0 = 0 := by
  simp [batchCap, batchWidth_zero he hlt, batchR, Nat.mod_eq_of_lt hlt]

private theorem batchWidth_succ_le {q E : ℕ} (he : 0 < E) (b : ℕ) :
    batchWidth q E (b + 1) ≤ 2 * batchWidth q E b := by
  apply batchCeil_le he
  rw [show E * (2 * batchWidth q E b) = 2 * (E * batchWidth q E b) by ring]
  have hc := batchCover (q := q) he b
  have hr := batchR_succ q E b
  omega

private theorem batchCap_step {q E : ℕ} (he : 0 < E) (b : ℕ) :
    2 * batchCap q E b + q * batchBeta q E b =
      batchCap q E (b + 1) + E * batchLeaves q E b := by
  have hw := batchWidth_succ_le (q := q) he b
  have ht : batchWidth q E (b + 1) + batchLeaves q E b = 2 * batchWidth q E b := by
    unfold batchLeaves
    omega
  have ht' : E * batchWidth q E (b + 1) + E * batchLeaves q E b =
      2 * (E * batchWidth q E b) := calc
    _ = E * (batchWidth q E (b + 1) + batchLeaves q E b) := by ring
    _ = E * (2 * batchWidth q E b) := by rw [ht]
    _ = _ := by ring
  have hr := batchR_succ q E b
  have hb := batchCover (q := q) he b
  have hb' := batchCover (q := q) he (b + 1)
  omega

private def batchDeficit (K β : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | b + 1, k => min (K (b + 1)) (2 * batchDeficit K β b k + k * β b)

private theorem batchDeficit_zero (K β : ℕ → ℕ) (b : ℕ) :
    batchDeficit K β b 0 = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [batchDeficit, ih]

private theorem batchDeficit_mono (K β : ℕ → ℕ) (b : ℕ) :
    Monotone (batchDeficit K β b) := by
  induction b with
  | zero => intro i j hij; exact le_rfl
  | succ b ih =>
      intro i j hij
      exact min_le_min le_rfl
        (Nat.add_le_add (Nat.mul_le_mul_left 2 (ih hij)) (Nat.mul_le_mul_right _ hij))

private theorem batchDeficit_le (K β : ℕ → ℕ) (b k : ℕ) :
    batchDeficit K β b k ≤ K b := by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b => exact min_le_left _ _

private theorem batchDeficit_end {q E : ℕ} (he : 0 < E) (hlt : E < q) (b : ℕ) :
    batchDeficit (batchCap q E) (batchBeta q E) b q = batchCap q E b := by
  induction b with
  | zero => exact (batchCap_zero he hlt).symm
  | succ b ih =>
      rw [batchDeficit, ih]
      have hs := batchCap_step (q := q) he b
      exact min_eq_left (by omega)

private def batchPrefix (q E b k : ℕ) :=
  2 * batchDeficit (batchCap q E) (batchBeta q E) b k + k * batchBeta q E b -
    batchCap q E (b + 1)

private theorem batchPrefix_zero (q E b : ℕ) : batchPrefix q E b 0 = 0 := by
  simp [batchPrefix, batchDeficit_zero]

private theorem batchPrefix_mono (q E b : ℕ) : Monotone (batchPrefix q E b) := by
  intro i j hij
  exact Nat.sub_le_sub_right
    (Nat.add_le_add (Nat.mul_le_mul_left 2 (batchDeficit_mono _ _ b hij))
      (Nat.mul_le_mul_right _ hij)) _

private theorem batchPrefix_end {q E : ℕ} (he : 0 < E) (hlt : E < q) (b : ℕ) :
    batchPrefix q E b q = E * batchLeaves q E b := by
  unfold batchPrefix
  rw [batchDeficit_end he hlt]
  have hs := batchCap_step (q := q) he b
  omega

private theorem batchPrefix_conserve (q E b k : ℕ) :
    batchPrefix q E b k + batchDeficit (batchCap q E) (batchBeta q E) (b + 1) k =
      2 * batchDeficit (batchCap q E) (batchBeta q E) b k + k * batchBeta q E b := by
  unfold batchPrefix
  rw [batchDeficit]
  generalize batchCap q E (b + 1) = c
  generalize 2 * batchDeficit (batchCap q E) (batchBeta q E) b k + k * batchBeta q E b = a
  by_cases h : c ≤ a
  · rw [min_eq_left h]; omega
  · rw [min_eq_right (show a ≤ c by omega)]; omega

private def batchHist (q E b i : ℕ) := batchPrefix q E b (i + 1) - batchPrefix q E b i
private def batchDelta (q E b i : ℕ) :=
  batchDeficit (batchCap q E) (batchBeta q E) b (i + 1) -
    batchDeficit (batchCap q E) (batchBeta q E) b i

private theorem batchHist_conserve (q E b i : ℕ) :
    batchHist q E b i + batchDelta q E (b + 1) i =
      batchBeta q E b + 2 * batchDelta q E b i := by
  have h₀ := batchPrefix_conserve q E b i
  have h₁ := batchPrefix_conserve q E b (i + 1)
  have hp := batchPrefix_mono q E b (show i ≤ i + 1 by omega)
  have hd := batchDeficit_mono (batchCap q E) (batchBeta q E) b (show i ≤ i + 1 by omega)
  have hd' := batchDeficit_mono (batchCap q E) (batchBeta q E) (b + 1) (show i ≤ i + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at h₁
  unfold batchHist batchDelta
  omega

private theorem batchDelta_lt {q E : ℕ} (he : 0 < E) (b i : ℕ) :
    batchDelta q E b i < E :=
  (Nat.sub_le _ _).trans_lt ((batchDeficit_le _ _ _ _).trans_lt (batchCap_lt he b))

private def batchTerminalPrefix (q E b t k : ℕ) := min E (batchPrefix q E b k - E * t)

private def batchTerminalHist (q E b t i : ℕ) :=
  batchTerminalPrefix q E b t (i + 1) - batchTerminalPrefix q E b t i

private theorem batchTerminalPrefix_mono (q E b t : ℕ) :
    Monotone (batchTerminalPrefix q E b t) := by
  intro i j hij
  exact min_le_min le_rfl (Nat.sub_le_sub_right (batchPrefix_mono q E b hij) _)

/-- Every terminating edge emits a histogram of exactly `E` slots. -/
private theorem batchTerminalHist_mass {q E b t : ℕ} (he : 0 < E) (hlt : E < q)
    (ht : t < batchLeaves q E b) : (∑ i ∈ Finset.range q, batchTerminalHist q E b t i) = E := by
  unfold batchTerminalHist
  rw [Finset.sum_range_tsub (batchTerminalPrefix_mono q E b t)]
  unfold batchTerminalPrefix
  rw [batchPrefix_zero, batchPrefix_end he hlt]
  have hm := Nat.mul_le_mul_left E (show t + 1 ≤ batchLeaves q E b by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  simp [min_eq_left (show E ≤ E * batchLeaves q E b - E * t by omega)]

private theorem batchSplit_total (E a n : ℕ) :
    (∑ t ∈ Finset.range n, min E (a - E * t)) = min a (E * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_add, Nat.mul_one]
      by_cases h : a ≤ E * n
      · simp [min_eq_left h, Nat.sub_eq_zero_of_le h,
          min_eq_left (show a ≤ E * n + E by omega)]
      · rw [min_eq_right (show E * n ≤ a by omega)]
        by_cases ha : a ≤ E * n + E
        · rw [min_eq_right (show a - E * n ≤ E by omega), min_eq_left ha]
          omega
        · rw [min_eq_left (show E ≤ a - E * n by omega),
            min_eq_right (show E * n + E ≤ a by omega)]

/-- Summing a label's multiplicity over all terminating edges recovers the forward
cumulative difference used in the dyadic count recurrence. -/
private theorem batchTerminalHist_aggregate {q E b i : ℕ} (he : 0 < E) (hlt : E < q)
    (hi : i < q) : (∑ t ∈ Finset.range (batchLeaves q E b), batchTerminalHist q E b t i) =
      batchHist q E b i := by
  have h₀ := batchPrefix_mono q E b (show i ≤ q by omega)
  have h₁ := batchPrefix_mono q E b (show i + 1 ≤ q by omega)
  rw [batchPrefix_end he hlt] at h₀ h₁
  unfold batchTerminalHist
  rw [Finset.sum_tsub_distrib _ (fun t _ => batchTerminalPrefix_mono q E b t (Nat.le_succ i))]
  unfold batchTerminalPrefix batchHist
  rw [batchSplit_total, batchSplit_total, min_eq_left h₀, min_eq_left h₁]

private def batchDigits (β : ℕ → ℕ) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * batchDigits β b n + β (b + n)

private def batchWalk (K β : ℕ → ℕ) (k b : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => min (K (b + n + 1)) (2 * batchWalk K β k b n x + k * β (b + n))

private theorem batchWalk_deficit (K β : ℕ → ℕ) (k b n : ℕ) :
    batchWalk K β k b n (batchDeficit K β b k) = batchDeficit K β (b + n) k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [batchWalk, ih]
    conv_rhs => rw [Nat.add_succ, batchDeficit]

private theorem batchClip_comp (A z c K : ℕ) :
    min K (2 * min A z + c) = min (min K (2 * A + c)) (2 * z + c) := by
  by_cases h : A ≤ z
  · rw [min_eq_left h, min_eq_left ((min_le_right K _).trans (show 2 * A + c ≤ 2 * z + c by omega))]
  · rw [min_eq_right (show z ≤ A by omega), min_assoc,
      min_eq_right (show 2 * z + c ≤ 2 * A + c by omega)]

private theorem batchWalk_affine (K β : ℕ → ℕ) (k b n : ℕ) :
    ∃ A ≤ K (b + (n + 1)), ∀ x,
      batchWalk K β k b (n + 1) x = min A (2 ^ (n + 1) * x + k * batchDigits β b (n + 1)) := by
  induction n with
  | zero =>
      exact ⟨K (b + 1), le_rfl, fun x => by simp [batchWalk, batchDigits]⟩
  | succ n ih =>
      obtain ⟨A, _, hA⟩ := ih
      refine ⟨min (K (b + (n + 1) + 1)) (2 * A + k * β (b + (n + 1))),
        min_le_left _ _, ?_⟩
      intro x
      rw [batchWalk, hA, batchClip_comp, pow_succ (2 : ℕ) (n + 1)]
      rw [show batchDigits β b (n+1+1) = 2*batchDigits β b (n+1) + β (b+(n+1)) from rfl]
      congr 1
      ring

private theorem batchDigits_eq (q E b n : ℕ) :
    batchR q E (b + n) + q * batchDigits (batchBeta q E) b n = 2 ^ n * batchR q E b := by
  induction n with
  | zero => simp [batchDigits]
  | succ n ih =>
      have hs : batchR q E (b+n).succ + q*batchBeta q E (b+n) = 2*batchR q E (b+n) :=
        batchR_succ q E (b + n)
      rw [Nat.add_succ, batchDigits, pow_succ]
      rw [show (2 ^ n * 2) * batchR q E b = 2 * (2 ^ n * batchR q E b) by ring, ← ih]
      rw [Nat.mul_add, Nat.mul_left_comm q 2, Nat.mul_add]
      omega

private theorem batchDigits_pos {q E b p : ℕ} (hp : 0 < p) (hr : 0 < batchR q E b)
    (hperiod : batchR q E (b + p) = batchR q E b) :
    0 < batchDigits (batchBeta q E) b p := by
  have hpow : 1 < (2 : ℕ) ^ p := Nat.one_lt_pow (by omega) (by decide)
  have hh := Nat.mul_lt_mul_of_pos_right hpow hr
  have heq := batchDigits_eq q E b p
  rw [hperiod] at heq
  by_contra! hn
  rw [show batchDigits (batchBeta q E) b p = 0 by omega, Nat.mul_zero, Nat.add_zero] at heq
  simp only [Nat.one_mul] at hh
  omega

private theorem batchClip_fixed {A M C : ℕ} (hM : 0 < M) (hC : 0 < C)
    (v : ℕ → ℕ) (hv : ∀ u, v (u + 1) = min A (M * v u + C)) :
    ∀ u, A ≤ M ^ u → v (u + 1) = A ∧ v (u + 2) = A := by
  have lower : ∀ n, min A (M ^ n) ≤ v (n + 1) := by
    intro n
    induction n with
    | zero => rw [hv, pow_zero]; exact min_le_min le_rfl (by omega)
    | succ n ih =>
        rw [hv]
        refine le_min (min_le_left _ _) ?_
        by_cases ht : A ≤ M ^ n
        · rw [min_eq_left ht] at ih
          exact le_trans (min_le_left _ _) (by have hh := Nat.le_mul_of_pos_left (v (n + 1)) hM; omega)
        · rw [min_eq_right (show M ^ n ≤ A by omega)] at ih
          have hh := Nat.mul_le_mul_left M ih
          rw [pow_succ, Nat.mul_comm (M ^ n) M]
          exact (min_le_right _ _).trans (by omega)
  intro u hu
  have h₀ := lower u
  rw [min_eq_left hu] at h₀
  have he : v (u + 1) = A := le_antisymm (by rw [hv]; exact min_le_left _ _) h₀
  refine ⟨he, ?_⟩
  rw [show u + 2 = (u + 1) + 1 by omega, hv, he]
  exact min_eq_left (by have hh := Nat.le_mul_of_pos_left A hM; omega)

private theorem batchWalk_period (K β : ℕ → ℕ) (p h : ℕ)
    (hK : ∀ b, h ≤ b → K (b + p) = K b) (hβ : ∀ b, h ≤ b → β (b + p) = β b)
    (k b n x : ℕ) (hb : h ≤ b) : batchWalk K β k (b + p) n x = batchWalk K β k b n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [batchWalk, batchWalk, ih]
      rw [show b + p + n + 1 = (b + n + 1) + p by omega, hK (b + n + 1) (by omega)]
      rw [show b + p + n = (b + n) + p by omega, hβ (b + n) (by omega)]

private theorem batchDeficit_period {K β : ℕ → ℕ} {p h u E : ℕ} (hp : 0 < p)
    (hE : E ≤ 2 ^ (p * u)) (hbound : ∀ b, K b < E)
    (hK : ∀ b, h ≤ b → K (b + p) = K b) (hβ : ∀ b, h ≤ b → β (b + p) = β b)
    (hpos : 0 < batchDigits β h p) (b k : ℕ) (hb : h + p * (u + 1) ≤ b) :
    batchDeficit K β (b + p) k = batchDeficit K β b k := by
  by_cases hk : k = 0
  · simp [hk, batchDeficit_zero]
  have haf : ∃ A ≤ K (h + p), ∀ x,
      batchWalk K β k h p x = min A (2 ^ p * x + k * batchDigits β h p) := by
    cases p with
    | zero => omega
    | succ n => exact batchWalk_affine K β k h n
  obtain ⟨A, hA, hf⟩ := haf
  have hblocks (n x : ℕ) : batchWalk K β k (h + p * n) p x = batchWalk K β k h p x := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc,
          batchWalk_period K β p h hK hβ k (h + p * n) p x (by omega), ih]
  let v : ℕ → ℕ := fun n => batchDeficit K β (h + p * n) k
  have hv n : v (n + 1) = min A (2 ^ p * v n + k * batchDigits β h p) := by
    dsimp [v]
    rw [Nat.mul_succ, ← Nat.add_assoc, ← batchWalk_deficit K β k (h + p * n) p, hblocks, hf]
  have hAu : A ≤ (2 ^ p) ^ u := by rw [← pow_mul]; exact hA.trans ((hbound _).le.trans hE)
  have fixed := batchClip_fixed (A := A) (M := 2 ^ p) (C := k * batchDigits β h p)
    (by positivity) (Nat.mul_pos (by omega) hpos) v hv u hAu
  let B := h + p * (u + 1)
  have atB : batchDeficit K β (B + p) k = batchDeficit K β B k := by
    have hindex : B + p = h + p * (u + 2) := by dsimp [B]; ring
    rw [hindex]
    exact fixed.2.trans fixed.1.symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show B ≤ b from hb)
  induction n with
  | zero => simpa using atB
  | succ n ih =>
      rw [show B + (n + 1) + p = (B + n + p) + 1 by omega, Nat.add_succ B n]
      rw [batchDeficit, batchDeficit, ih (by dsimp [B]; omega),
        show B + n + p + 1 = B + n + 1 + p by omega,
        hK (B + n + 1) (by dsimp [B]; omega), hβ (B + n) (by dsimp [B]; omega)]

private theorem batchR_period {h d g e p b : ℕ} (hp : d ∣ 2 ^ p - 1) (hb : h ≤ b) :
    batchR (g * (2 ^ h * d)) (g * e) (b + p) = batchR (g * (2 ^ h * d)) (g * e) b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨c, hc⟩ := hp
  have hp' : (2 : ℕ) ^ p = 1 + d * c := by
    have hpow : 0 < (2 : ℕ) ^ p := by positivity
    omega
  unfold batchR
  have harg : 2 ^ (h + n + p) * (g * e) =
      2 ^ (h + n) * (g * e) + (g * (2 ^ h * d)) * (2 ^ n * e * c) := by
    rw [pow_add _ (h + n) p, hp', pow_add _ h n]
    ring
  rw [harg, Nat.add_mul_mod_self_left]

private theorem batchR_h {h d g e : ℕ} :
    batchR (g * (2 ^ h * d)) (g * e) h = (g * 2 ^ h) * (e % d) := by
  unfold batchR
  rw [show (2 : ℕ) ^ h * (g * e) = (g * 2 ^ h) * e by ring,
    ← Nat.mul_assoc, Nat.mul_mod_mul_left]

private theorem batchR_h_pos {h d g e : ℕ} (hg : 0 < g) (hd : 1 < d)
    (hc : Nat.Coprime e (2 ^ h * d)) : 0 < batchR (g * (2 ^ h * d)) (g * e) h := by
  have hc' : Nat.Coprime d e := (hc.coprime_dvd_right (Nat.dvd_mul_left d (2 ^ h))).symm
  have hr : 0 < e % d := by
    by_contra! hz
    have hd' : d ∣ e := Nat.dvd_of_mod_eq_zero (by omega)
    have hd1 : d = 1 := (Nat.gcd_eq_left hd').symm.trans hc'
    omega
  rw [batchR_h]
  exact Nat.mul_pos (Nat.mul_pos hg (by positivity)) hr

private theorem batchR_dyadic (h g e b : ℕ) (hb : h ≤ b) :
    batchR (g * (2 ^ h * 1)) (g * e) b = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  unfold batchR
  rw [pow_add, show (2 : ℕ) ^ h * 2 ^ n * (g * e) = (g * (2 ^ h * 1)) * (2 ^ n * e) by ring]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)

private theorem batchWidth_dyadic {h g e b : ℕ} (hE : 0 < g * e) (hb : h ≤ b) :
    batchWidth (g * (2 ^ h * 1)) (g * e) b = 0 := by
  unfold batchWidth
  rw [batchR_dyadic h g e b hb]
  exact Nat.eq_zero_of_le_zero (batchCeil_le hE (show 0 ≤ (g * e) * 0 by simp))

/-- The exact finite fold used at the posted checkpoint; the dyadic case has no live layers
at or after `h`, and the non-dyadic case saturates the identical period map. -/
private theorem batchArithmetic_period {h d g e p u : ℕ} (hd : 0 < d) (hg : 0 < g)
    (he : 0 < e) (hc : Nat.Coprime e (2 ^ h * d)) (hp : 0 < p) (hp' : d ∣ 2 ^ p - 1)
    (hE : g * e ≤ 2 ^ (p * u)) (b : ℕ) (hb : h + p * (u + 1) ≤ b) :
    let q := g * (2 ^ h * d)
    let E := g * e
    batchWidth q E (b + p) = batchWidth q E b ∧
    ∀ k, batchPrefix q E (b + p) k = batchPrefix q E b k := by
  dsimp only
  let q := g * (2 ^ h * d)
  let E := g * e
  change batchWidth q E (b + p) = batchWidth q E b ∧ ∀ k, batchPrefix q E (b + p) k = batchPrefix q E b k
  have hr n (hn : h ≤ n) : batchR q E (n + p) = batchR q E n := batchR_period hp' hn
  have hwidth n (hn : h ≤ n) : batchWidth q E (n + p) = batchWidth q E n := by
    unfold batchWidth; rw [hr n hn]
  have hcap n (hn : h ≤ n) : batchCap q E (n + p) = batchCap q E n := by
    unfold batchCap; rw [hr n hn, hwidth n hn]
  have hbeta n (hn : h ≤ n) : batchBeta q E (n + p) = batchBeta q E n := by
    unfold batchBeta; rw [hr n hn]
  have hD n k (hn : h + p * (u + 1) ≤ n) :
      batchDeficit (batchCap q E) (batchBeta q E) (n + p) k =
        batchDeficit (batchCap q E) (batchBeta q E) n k := by
    by_cases hd1 : d = 1
    · have hzero m (hm : h ≤ m) : batchCap q E m = 0 := by
        have hr' : batchR q E m = 0 := by
          simpa only [q, E, hd1] using batchR_dyadic h g e m hm
        have hw' : batchWidth q E m = 0 := by
          simpa only [q, E, hd1] using batchWidth_dyadic (Nat.mul_pos hg he) hm
        simp [batchCap, hr', hw']
      have hn₁ := batchDeficit_le (batchCap q E) (batchBeta q E) n k
      have hn₂ := batchDeficit_le (batchCap q E) (batchBeta q E) (n + p) k
      rw [hzero n (by omega)] at hn₁
      rw [hzero (n + p) (by omega)] at hn₂
      omega
    · exact batchDeficit_period hp hE (batchCap_lt (q := q) (Nat.mul_pos hg he)) hcap hbeta
        (batchDigits_pos hp (batchR_h_pos hg (by omega) hc) (hr h le_rfl)) n k hn
  refine ⟨hwidth b (by omega), fun k => ?_⟩
  unfold batchPrefix
  rw [hD b k hb, hbeta b (by omega), show b + p + 1 = (b + 1) + p by omega, hcap _ (by omega)]

open scoped BigOperators

namespace L29934Layer

private def bitNat (bit : Bool) : ℕ := if bit then 1 else 0

private theorem bitNat_lt (bit : Bool) : bitNat bit < 2 := by
  cases bit <;> decide

private theorem bitNat_injective : Function.Injective bitNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitNat]

def child (i : ℕ) (bit : Bool) : ℕ := 2 * i + bitNat bit

@[simp] theorem child_false (i : ℕ) : child i false = 2 * i := by simp [child, bitNat]

@[simp] theorem child_true (i : ℕ) : child i true = 2 * i + 1 := rfl

private def ordinal : (b : ℕ) → (Fin b → Bool) → ℕ
  | 0, _ => 0
  | b + 1, x => child (ordinal b (fun i => x i.castSucc)) (x (Fin.last b))

private theorem ordinal_inj (b : ℕ) : Function.Injective (ordinal b) := by
  induction b with
  | zero =>
    intro x y _
    funext i
    exact Fin.elim0 i
  | succ b ih =>
    intro x y h
    change 2 * ordinal b (fun i => x i.castSucc) + bitNat (x (Fin.last b)) =
      2 * ordinal b (fun i => y i.castSucc) + bitNat (y (Fin.last b)) at h
    have hx := bitNat_lt (x (Fin.last b))
    have hy := bitNat_lt (y (Fin.last b))
    have hpre : (fun i : Fin b => x i.castSucc) = fun i : Fin b => y i.castSucc :=
      ih (by omega)
    funext i
    refine Fin.lastCases ?_ (fun j => congrFun hpre j) i
    exact bitNat_injective (by omega)

private theorem ordinal_onto (b n : ℕ) (hn : n < 2 ^ b) :
    ∃ x : Fin b → Bool, ordinal b x = n := by
  induction b generalizing n with
  | zero =>
    refine ⟨fun _ => false, ?_⟩
    change 0 = n
    simp only [pow_zero] at hn
    omega
  | succ b ih =>
    rw [pow_succ] at hn
    have hd : n / 2 < 2 ^ b := by omega
    obtain ⟨x, hx⟩ := ih (n / 2) hd
    let bit := decide (n % 2 = 1)
    have hb : bitNat bit = n % 2 := by
      by_cases h : n % 2 = 1
      · simp [bit, bitNat, h]
      · have h0 : n % 2 = 0 := by omega
        simp [bit, bitNat, h0]
    refine ⟨Fin.snoc x bit, ?_⟩
    change 2 * ordinal b (fun i => Fin.snoc (α := fun _ => Bool) x bit i.castSucc) +
      bitNat (Fin.snoc (α := fun _ => Bool) x bit (Fin.last b)) = n
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hx, hb]
    omega

def phase (B p : ℕ) (hp : 0 < p) (b : ℕ) : Fin (B + p) :=
  if h : b < B then ⟨b, by omega⟩ else ⟨B + (b - B) % p, by
    have := Nat.mod_lt (b - B) hp
    omega⟩

private theorem phase_val_of_lt {B p : ℕ} (hp : 0 < p) {b : ℕ} (h : b < B + p) :
    (phase B p hp b).val = b := by
  by_cases hB : b < B
  · simp [phase, hB]
  · simp [phase, hB, Nat.mod_eq_of_lt (show b - B < p by omega),
      Nat.add_sub_of_le (show B ≤ b by omega)]

private theorem phase_next {B p : ℕ} (hp : 0 < p) (b : ℕ) :
    phase B p hp ((phase B p hp b).val + 1) = phase B p hp (b + 1) := by
  by_cases hB : b < B
  · rw [phase_val_of_lt hp (show b < B + p by omega)]
  · apply Fin.ext
    have hb : (phase B p hp b).val = B + (b - B) % p := by simp [phase, hB]
    rw [hb]
    have hn₁ : ¬ B + (b - B) % p + 1 < B := by omega
    have hn₂ : ¬ b + 1 < B := by omega
    simp only [phase, dif_neg hn₁, dif_neg hn₂]
    rw [show B + (b - B) % p + 1 - B = (b - B) % p + 1 by omega,
      show b + 1 - B = (b - B) + 1 by omega, Nat.mod_add_mod]

private def widthValid (B p : ℕ) (w : ℕ → ℕ) : Prop :=
  w 0 = 1 ∧ (∀ b, w (b+1) ≤ 2*w b) ∧ (∀ b, B ≤ b → w (b+p) = w b)

def Widths (B p : ℕ) : Type := Subtype (widthValid B p)

namespace Widths

def mk {B p : ℕ} (w : ℕ → ℕ) (hr : w 0 = 1)
    (hs : ∀ b, w (b+1) ≤ 2*w b) (ht : ∀ b, B ≤ b → w (b+p) = w b) :
    Widths B p := (⟨w,hr,hs,ht⟩ : Subtype (widthValid B p))

def width {B p : ℕ} (W : Widths B p) : ℕ → ℕ :=
  (show Subtype (widthValid B p) from W).val

private theorem valid {B p : ℕ} (W : Widths B p) : widthValid B p W.width :=
  (show Subtype (widthValid B p) from W).property

theorem root {B p : ℕ} (W : Widths B p) : W.width 0 = 1 := W.valid.1

theorem step {B p : ℕ} (W : Widths B p) (b : ℕ) : W.width (b+1) ≤ 2*W.width b :=
  W.valid.2.1 b

theorem tail {B p : ℕ} (W : Widths B p) (b : ℕ) (hb : B ≤ b) : W.width (b+p) = W.width b :=
  W.valid.2.2 b hb

variable {B p : ℕ} (W : Widths B p) (hp : 0 < p)

private theorem width_phase (b : ℕ) : W.width (phase B p hp b).val = W.width b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases h : b < B + p
    · rw [phase_val_of_lt hp h]
    have hB : B ≤ b - p := by omega
    have hφ : phase B p hp b = phase B p hp (b - p) := by
      apply Fin.ext
      have hn₁ : ¬ b < B := by omega
      have hn₂ : ¬ b - p < B := by omega
      simp only [phase, dif_neg hn₁, dif_neg hn₂]
      rw [show b - B = (b - p - B) + p by omega, Nat.add_mod_right]
    rw [hφ, ih (b - p) (by omega)]
    simpa only [Nat.sub_add_cancel (show p ≤ b by omega)] using (W.tail (b - p) hB).symm

private theorem width_le_pow (b : ℕ) : W.width b ≤ 2 ^ b := by
  induction b with
  | zero => simp [W.root]
  | succ b ih =>
    rw [pow_succ]
    have hh := W.step b
    omega

abbrev State := Σ a : Fin (B + p), Fin (W.width a.val)

def count : ℕ := ∑ b ∈ Finset.range (B + p), W.width b

private theorem card_state : Fintype.card W.State = W.count := by
  simp [State, count, Fin.sum_univ_eq_sum_range]

noncomputable def encode : W.State ≃ Fin W.count :=
  Fintype.equivFinOfCardEq W.card_state

private def embedLayer (b : ℕ) (i : Fin (W.width b)) : W.State :=
  ⟨phase B p hp b, ⟨i.val, by rw [W.width_phase hp]; exact i.isLt⟩⟩

noncomputable def atDepth (b : ℕ) (i : Fin (W.width b)) : Fin W.count :=
  W.encode (W.embedLayer hp b i)

noncomputable def start : Fin W.count :=
  W.atDepth hp 0 ⟨0, by simpa only [W.root] using Nat.zero_lt_one⟩

private def nextPhase (a : Fin (B + p)) : Fin (B + p) := phase B p hp (a.val + 1)

private def nextState (i : W.State) (bit : Bool) : Option W.State :=
  if h : child i.2.val bit < W.width (nextPhase hp i.1).val then
    some ⟨nextPhase hp i.1, ⟨child i.2.val bit, h⟩⟩
  else none

noncomputable def next (i : Fin W.count) (bit : Bool) : Option (Fin W.count) :=
  (W.nextState hp (W.encode.symm i) bit).map W.encode

private theorem nextPhase_embedLayer (b : ℕ) (i : Fin (W.width b)) :
    nextPhase hp (W.embedLayer hp b i).1 = phase B p hp (b + 1) := phase_next hp b

private theorem nextPhase_width (b : ℕ) (i : Fin (W.width b)) :
    W.width (nextPhase hp (W.embedLayer hp b i).1).val = W.width (b + 1) := by
  rw [W.nextPhase_embedLayer hp, W.width_phase hp]

private theorem fin_heq {n m : ℕ} (h : n = m) {i : Fin n} {j : Fin m}
    (hv : i.val = j.val) : HEq i j := by
  subst m
  exact heq_of_eq (Fin.ext hv)

theorem next_atDepth (b : ℕ) (i : Fin (W.width b)) (bit : Bool) :
    W.next hp (W.atDepth hp b i) bit =
      if h : child i.val bit < W.width (b + 1) then
        some (W.atDepth hp (b + 1) ⟨child i.val bit, h⟩)
      else none := by
  unfold next atDepth
  rw [Equiv.symm_apply_apply]
  unfold nextState
  have hw := W.nextPhase_width hp b i
  by_cases h : child i.val bit < W.width (b + 1)
  · have hh : child (W.embedLayer hp b i).2.val bit <
        W.width (nextPhase hp (W.embedLayer hp b i).1).val := by
      rw [hw]
      exact h
    simp only [dif_pos h, dif_pos hh, Option.map_some]
    apply congrArg (fun j : W.State => some (W.encode j))
    apply Sigma.ext
    · exact W.nextPhase_embedLayer hp b i
    · have hwidth := congrArg (fun a : Fin (B+p) => W.width a.val) (W.nextPhase_embedLayer hp b i)
      exact fin_heq hwidth (i := ⟨_,hh⟩) (j := (W.embedLayer hp (b+1) ⟨_,h⟩).2) rfl
  · have hh : ¬ child (W.embedLayer hp b i).2.val bit <
        W.width (nextPhase hp (W.embedLayer hp b i).1).val := by
      rw [hw]
      exact h
    simp [h, hh]

private noncomputable def result (b j : ℕ) : Option (Fin W.count) :=
  if h : j < W.width b then some (W.atDepth hp b ⟨j, h⟩) else none

private theorem result_bind (b j : ℕ) (bit : Bool) :
    (W.result hp b j).bind (fun i => W.next hp i bit) = W.result hp (b + 1) (child j bit) := by
  by_cases h : j < W.width b
  · simp only [result, dif_pos h, Option.bind_some, next_atDepth]
  · have h' : ¬ child j bit < W.width (b + 1) := by
      have hs := W.step b
      have hb := bitNat_lt bit
      change ¬ 2*j+bitNat bit < W.width (b+1)
      omega
    simp only [result, dite_eq_right h, dite_eq_right h', Option.bind_none]

private theorem run_eq_result (b : ℕ) (x : Fin b → Bool) :
    (List.ofFn x).foldl (fun (o : Option (Fin W.count)) bit =>
        o.bind (fun i => W.next hp i bit)) (some (W.start hp)) =
      W.result hp b (ordinal b x) := by
  induction b with
  | zero =>
    change (List.ofFn x).foldl _ (some (W.start hp)) = W.result hp 0 0
    have h0 : 0 < W.width 0 := W.root.symm ▸ Nat.one_pos
    rw [List.ofFn_zero, List.foldl_nil, result, dite_eq_left h0]
    rfl
  | succ b ih =>
    rw [List.ofFn_succ_last, List.foldl_append, ih]
    simpa only [List.foldl_cons, List.foldl_nil, ordinal] using
      W.result_bind hp b (ordinal b (fun i => x i.castSucc)) (x (Fin.last b))

private theorem isSome_run_iff (b : ℕ) (x : Fin b → Bool) :
    ((List.ofFn x).foldl (fun (o : Option (Fin W.count)) bit =>
        o.bind (fun i => W.next hp i bit)) (some (W.start hp))).isSome = true ↔
      ordinal b x < W.width b := by
  rw [W.run_eq_result hp]
  by_cases h : ordinal b x < W.width b
  · rw [result, dite_eq_left h, Option.isSome_some]
    exact iff_of_true rfl h
  · rw [result, dite_eq_right h, Option.isSome_none]
    exact iff_of_false (by decide) h
theorem live (b : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter (fun x =>
      ((List.ofFn x).foldl (fun (o : Option (Fin W.count)) bit =>
        o.bind (fun i => W.next hp i bit)) (some (W.start hp))).isSome)).card = W.width b := by
  classical
  let liveWord := fun x : Fin b → Bool =>
      ((List.ofFn x).foldl (fun (o : Option (Fin W.count)) bit =>
        o.bind (fun i => W.next hp i bit)) (some (W.start hp))).isSome = true
  let f : Subtype liveWord → Fin (W.width b) := fun x =>
    ⟨ordinal b x.val, (W.isSome_run_iff hp b x.val).mp x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact ordinal_inj b (congrArg Fin.val h)
    · intro i
      obtain ⟨x, hx⟩ := ordinal_onto b i.val (lt_of_lt_of_le i.isLt (W.width_le_pow b))
      have hlt : ordinal b x < W.width b := by rw [hx]; exact i.isLt
      exact ⟨⟨x, (W.isSome_run_iff hp b x).mpr hlt⟩, Fin.ext hx⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_subtype, Fintype.card_fin, liveWord] using hcard

private noncomputable def rank (i : Fin W.count) : ℕ := (W.encode.symm i).2.val

private theorem rank_lt (i : Fin W.count) : W.rank i < W.count := by
  let j := W.encode.symm i
  have hw : W.width j.1.val ≤ W.count := by
    unfold count
    exact Finset.single_le_sum (f := W.width) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr j.1.isLt)
  exact lt_of_lt_of_le j.2.isLt hw

private theorem rank_true {i j : Fin W.count}
    (h : W.next hp i true = some j) : W.rank i < W.rank j := by
  unfold next nextState at h
  split at h
  · rename_i ht
    simp only [Option.map_some, Option.some.injEq] at h
    subst j
    unfold rank
    rw [W.encode.symm_apply_apply]
    change (W.encode.symm i).2.val < 2 * (W.encode.symm i).2.val + 1
    omega
  · simp at h

theorem terminate (i : Fin W.count) :
    (fun o : Option (Fin W.count) => o.bind (fun j => W.next hp j true))^[W.count]
      (some i) = none := by
  let f := fun o : Option (Fin W.count) => o.bind (fun j => W.next hp j true)
  have hr : ∀ k j, (f^[k]) (some i) = some j → W.rank i + k ≤ W.rank j := by
    intro k
    induction k with
    | zero =>
      intro j h
      change some i = some j at h
      have he := Option.some.inj h
      simp [← he]
    | succ k ih =>
      intro j h
      rw [Function.iterate_succ_apply'] at h
      cases h' : (f^[k]) (some i) with
      | none => simp [h', f] at h
      | some l =>
        have hl : W.next hp l true = some j := by simpa only [h', f, Option.bind_some] using h
        have hli := ih l h'
        have hlj := W.rank_true hp hl
        omega
  change (f^[W.count]) (some i) = none
  cases h : (f^[W.count]) (some i) with
  | none => rfl
  | some j =>
    have he := hr W.count j h
    have hh := W.rank_lt j
    omega

def slots (b : ℕ) : ℕ := 2 * W.width b - W.width (b + 1)

theorem slots_phase (b : ℕ) : W.slots (phase B p hp b).val = W.slots b := by
  unfold slots
  rw [W.width_phase hp b, ← W.width_phase hp ((phase B p hp b).val + 1),
    phase_next hp b, W.width_phase hp (b + 1)]

noncomputable def exitSlot (i : Fin W.count) (bit : Bool) : ℕ :=
  let j := W.encode.symm i
  child j.2.val bit - W.width (nextPhase hp j.1).val

theorem exitSlot_lt (i : Fin W.count) (bit : Bool) (hn : W.next hp i bit = none) :
    W.exitSlot hp i bit < W.slots (W.encode.symm i).1.val := by
  let j := W.encode.symm i
  have hw : W.width (nextPhase hp j.1).val = W.width (j.1.val + 1) :=
    W.width_phase hp (j.1.val + 1)
  have hlo : W.width (nextPhase hp j.1).val ≤ child j.2.val bit := by
    by_contra! h
    simpa [next, nextState, j, h] using hn
  have hhi := j.2.isLt
  have hb := bitNat_lt bit
  change child j.2.val bit - W.width (nextPhase hp j.1).val <
    2 * W.width j.1.val - W.width (j.1.val + 1)
  unfold child at *
  omega

noncomputable def exitValue (H : Fin (B + p) → ℕ → ℝ)
    (i : Fin W.count) (bit : Bool) : ℝ :=
  H (W.encode.symm i).1 (W.exitSlot hp i bit)

noncomputable def layerValue (L : Fin W.count → ℝ) (b : ℕ) : ℝ :=
  ∑ i : Fin (W.width b), L (W.atDepth hp b i)

private theorem sum_children (m : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, (f (2 * i + 1) + f (2 * i))) =
      ∑ k ∈ Finset.range (2 * m), f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- The branch law sums to a conservation equation at each depth. -/
theorem layer_recurrence (H : Fin (B + p) → ℕ → ℝ) (L : Fin W.count → ℝ)
    (law : ∀ i, 2 * L i = ∑ bit : Bool, (W.next hp i bit).elim (W.exitValue hp H i bit) L)
    (b : ℕ) :
    2 * W.layerValue hp L b = W.layerValue hp L (b + 1) +
      ∑ k ∈ Finset.range (W.slots b), H (phase B p hp b) k := by
  let f := fun k : ℕ => if h : k < W.width (b + 1) then
    L (W.atDepth hp (b + 1) ⟨k, h⟩)
    else H (phase B p hp b) (k - W.width (b + 1))
  have hEdge (i : Fin (W.width b)) (bit : Bool) :
      (W.next hp (W.atDepth hp b i) bit).elim (W.exitValue hp H (W.atDepth hp b i) bit) L =
        f (child i.val bit) := by
    rw [W.next_atDepth hp]
    have hw := W.nextPhase_width hp b i
    by_cases h : child i.val bit < W.width (b + 1)
    · simp [h, f]
    · rw [dite_eq_right h]
      simp only [f, dite_eq_right h, Option.elim_none]
      unfold exitValue exitSlot atDepth
      rw [W.encode.symm_apply_apply]
      dsimp only
      rw [hw]
      rfl
  calc
    2 * W.layerValue hp L b =
        ∑ i : Fin (W.width b), 2 * L (W.atDepth hp b i) := by simp [layerValue, Finset.mul_sum]
    _ = ∑ i : Fin (W.width b), (f (2 * i.val + 1) + f (2 * i.val)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [law, Fintype.sum_bool, hEdge, hEdge] <;> rfl
    _ = ∑ k ∈ Finset.range (2 * W.width b), f k := by
      rw [Fin.sum_univ_eq_sum_range (fun i => f (2 * i + 1) + f (2 * i)), sum_children]
    _ = ∑ k ∈ Finset.range (W.width (b + 1) + W.slots b), f k := by
      rw [slots, Nat.add_sub_of_le (W.step b)]
    _ = W.layerValue hp L (b + 1) +
        ∑ k ∈ Finset.range (W.slots b), H (phase B p hp b) k := by
      rw [Finset.sum_range_add, ← Fin.sum_univ_eq_sum_range f]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => by simp [f, i.isLt, layerValue])
      · exact Finset.sum_congr rfl (fun i _ => by
          have h : ¬ W.width (b + 1) + i < W.width (b + 1) := by omega
          simp [f, h])

private theorem layer_bounded (L : Fin W.count → ℝ) :
    ∃ M : ℝ, ∀ b, |W.layerValue hp L b| ≤ M := by
  let M : ℝ := ∑ i : Fin W.count, |L i|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg (L i))
  refine ⟨W.count * M, fun b => ?_⟩
  have hw : W.width b ≤ W.count := by
    rw [← W.width_phase hp b]
    exact Finset.single_le_sum (f := W.width) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (phase B p hp b).isLt)
  calc
    |W.layerValue hp L b| ≤ ∑ i : Fin (W.width b), |L (W.atDepth hp b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (W.width b), M := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact Finset.single_le_sum (f := fun j => |L j|) (fun j _ => abs_nonneg (L j))
        (Finset.mem_univ (W.atDepth hp b i))
    _ = W.width b * M := by simp [nsmul_eq_mul]
    _ ≤ W.count * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hw) hM

private theorem bounded_doubling_zero (d : ℕ → ℝ) (K : ℝ)
    (hd : ∀ b, d (b + 1) = 2 * d b) (hb : ∀ b, |d b| ≤ K) : d 0 = 0 := by
  by_contra h0
  have ha : 0 < |d 0| := abs_pos.mpr h0
  have hlin (n : ℕ) : ((n : ℝ) + 1) * |d 0| ≤ |d n| := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hd n, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Nat.cast_add, Nat.cast_one]
      have hnonneg : 0 ≤ (n : ℝ) * |d 0| := mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |d 0|)
  have hh := (div_lt_iff₀ ha).mp hn
  linarith [hlin n, hb n]

private theorem layer_root (L : Fin W.count → ℝ) : W.layerValue hp L 0 = L (W.start hp) := by
  let j : Fin (W.width 0) := ⟨0, by rw [W.root]; decide⟩
  change (∑ i : Fin (W.width 0), L (W.atDepth hp 0 i)) = L (W.atDepth hp 0 j)
  apply Finset.sum_eq_single j
  · intro i hi hne
    exfalso
    apply hne
    apply Fin.ext
    have hi' : i.val < 1 := i.isLt.trans_le W.root.le
    change i.val = 0
    omega
  · simp

/-- A bounded target with the same layer recurrence has the correct root potential. -/
theorem root_of_recurrence (H : Fin (B + p) → ℕ → ℝ) (L : Fin W.count → ℝ)
    (law : ∀ i, 2 * L i = ∑ bit : Bool, (W.next hp i bit).elim (W.exitValue hp H i bit) L)
    (T : ℕ → ℝ) (K : ℝ) (hK : ∀ b, |T b| ≤ K)
    (hT : ∀ b, 2 * T b = T (b + 1) + ∑ k ∈ Finset.range (W.slots b), H (phase B p hp b) k) :
    L (W.start hp) = T 0 := by
  obtain ⟨M, hM⟩ := W.layer_bounded hp L
  let D := fun b => W.layerValue hp L b - T b
  have hD (b : ℕ) : D (b + 1) = 2 * D b := by
    dsimp [D]
    linarith [W.layer_recurrence hp H L law b, hT b]
  have hDb (b : ℕ) : |D b| ≤ M + K :=
    (abs_sub _ _).trans (add_le_add (hM b) (hK b))
  have he := bounded_doubling_zero D (M + K) hD hDb
  change W.layerValue hp L 0 - T 0 = 0 at he
  rw [W.layer_root hp] at he
  linarith

/-- Coordinate-wise floor-balance interface; `δ` is the bounded integer carry. -/
theorem root_of_floor_balance (H : Fin (B + p) → ℕ → ℝ) (L : Fin W.count → ℝ)
    (law : ∀ i, 2 * L i = ∑ bit : Bool, (W.next hp i bit).elim (W.exitValue hp H i bit) L)
    (q E : ℕ) (hE : E < q) (δ : ℕ → ℤ) (hδ₀ : δ 0 = 0)
    (K : ℝ) (hK : ∀ b, |(δ b : ℝ)| ≤ K)
    (hist : ∀ b, let r := 2 ^ b * E % q
      (∑ k ∈ Finset.range (W.slots b), H (phase B p hp b) k) =
        (((2 * r) / q : ℕ) : ℝ) + 2 * (δ b : ℝ) - (δ (b + 1) : ℝ)) :
    L (W.start hp) = (E : ℝ) / (q : ℝ) := by
  have hq : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let r := fun b : ℕ => 2 ^ b * E % q
  let T := fun b : ℕ => (r b : ℝ) / (q : ℝ) + (δ b : ℝ)
  have hT₀ : T 0 = (E : ℝ) / (q : ℝ) := by
    simp [T, r, hδ₀, Nat.mod_eq_of_lt hE]
  rw [← hT₀]
  apply W.root_of_recurrence hp H L law T (1 + K)
  · intro b
    have hr₀ : (0 : ℝ) ≤ r b := Nat.cast_nonneg _
    have hr₁ : (r b : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt (2 ^ b * E) hq).le
    have hr₂ : |(r b : ℝ) / (q : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hr₀ hqR.le)]
      exact (div_le_one hqR).mpr hr₁
    exact (abs_add_le _ _).trans (add_le_add hr₂ (hK b))
  · intro b
    have hmod : r (b + 1) = (2 * r b) % q := by
      change (2 ^ (b + 1) * E) % q = (2 * ((2 ^ b * E) % q)) % q
      rw [Nat.mul_mod_mod, pow_succ, show 2 ^ b * 2 * E = 2 * (2 ^ b * E) by ring]
    have hdiv := Nat.mod_add_div (2 * r b) q
    rw [← hmod] at hdiv
    have hcast : (r (b + 1) : ℝ) + (q : ℝ) * (((2 * r b) / q : ℕ) : ℝ) =
        2 * (r b : ℝ) := by exact_mod_cast hdiv
    have hrem : (r (b + 1) : ℝ) / (q : ℝ) + (((2 * r b) / q : ℕ) : ℝ) =
        2 * ((r b : ℝ) / (q : ℝ)) := by
      field_simp [ne_of_gt hqR]
      linarith
    dsimp [T]
    rw [hist b]
    linarith

def skinny (h p : ℕ) : Widths h p :=
  mk (fun _ => 1) rfl (fun _ => by norm_num) (fun _ _ => rfl)

theorem skinny_count (h p : ℕ) : (skinny h p).count = h + p := by
  simp [count, skinny, width, mk]


end Widths

end L29934Layer

open L29934Layer

private def SharpMachine (q E : ℕ) (width : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (a : Fin q → Fin s → Bool → ℕ) (v : Fin q → Fin s → ℝ),
    Stops n ∧ (∀ b, liveCount z n b = width b) ∧
    (∀ i e, ∑ j, a j i e = E) ∧
    (∀ j, Harm n (fun i e => (a j i e : ℝ)) (v j)) ∧ ∀ j, v j z = (E : ℝ)/q

private theorem from_layer {B p q E : ℕ} (W : Widths B p) (hp : 0 < p) (hq : 0 < q)
    (H : Fin q → Fin (B+p) → ℕ → ℕ)
    (hH : ∀ a k, k < W.slots a.val → ∑ j, H j a k = E)
    (hroot : ∀ j v, Harm (W.next hp) (W.exitValue hp (fun a k => H j a k)) v →
      v (W.start hp) = (E : ℝ)/q) : SharpMachine q E W.width W.count := by
  classical
  let z := W.start hp
  let n := W.next hp
  let reward := fun (j : Fin q) (i : Fin W.count) (e : Bool) =>
    if n i e = none then
      H j (W.encode.symm i).1 (W.exitSlot hp i e)
    else if j = ⟨0,hq⟩ then E else 0
  have hn : Stops n := ⟨fun _ => true, W.terminate hp⟩
  have hr (j : Fin q) : ∃ v, Harm n (fun i e => (reward j i e : ℝ)) v := harm_exists hn _
  choose v hv using hr
  have hterm (j : Fin q) : Harm n (W.exitValue hp (fun a k => H j a k)) (v j) := by
    intro i
    rw [Fintype.sum_bool]
    have hi := hv j i
    rw [Fintype.sum_bool] at hi
    have hpiece (e : Bool) : (n i e).elim (W.exitValue hp (fun a k => H j a k) i e) (v j) =
        (n i e).elim (↑(reward j i e)) (v j) := by
      cases he : n i e <;> simp [reward, Widths.exitValue, he]
    rwa [hpiece, hpiece]
  refine ⟨z,n,reward,v,hn,fun b => ?_,fun i e => ?_,hv,fun j => hroot j (v j) (hterm j)⟩
  · unfold liveCount path
    simp_rw [active_fold]
    exact W.live hp b
  · by_cases h : n i e = none
    · simpa only [reward, if_pos h] using hH _ _ (W.exitSlot_lt hp i e h)
    · simp [reward,h]

private theorem phase_preserves {B p : ℕ} {α : Type*} (hp : 0 < p) (F : ℕ → α)
    (hF : ∀ b, B ≤ b → F (b+p) = F b) (b : ℕ) :
    F (phase B p hp b).val = F b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases h : b < B+p
    · rw [L29934Layer.phase_val_of_lt hp h]
    have hB : B ≤ b-p := by omega
    have hφ : phase B p hp b = phase B p hp (b-p) := by
      apply Fin.ext
      simp only [phase, dif_neg (show ¬ b < B by omega), dif_neg (show ¬ b-p < B by omega)]
      rw [show b-B = (b-p-B)+p by omega, Nat.add_mod_right]
    rw [hφ, ih (b-p) (by omega), ← hF (b-p) hB, Nat.sub_add_cancel (by omega)]

private theorem batch_machine {h d g e p u : ℕ} (hd : 0 < d) (hg : 0 < g)
    (he : 0 < e) (heq : e < 2^h*d) (hc : Nat.Coprime e (2^h*d))
    (hp : 0 < p) (hp' : d ∣ 2^p-1) (hu : g*e ≤ 2^(p*u)) :
    let q := g*(2^h*d)
    let E := g*e
    let B := h+p*(u+1)
    SharpMachine q E (batchWidth q E) (∑ b ∈ Finset.range (B+p), batchWidth q E b) := by
  intro q E B
  have hE : 0 < E := Nat.mul_pos hg he
  have hEq : E < q := Nat.mul_lt_mul_of_pos_left heq hg
  have hper (b : ℕ) (hb : B ≤ b) := batchArithmetic_period hd hg he hc hp hp' hu b hb
  let W : Widths B p := Widths.mk (batchWidth q E) (batchWidth_zero hE hEq)
    (batchWidth_succ_le hE) (fun b hb => (hper b hb).1)
  change SharpMachine q E W.width W.count
  let H (j : Fin q) (a : Fin (B+p)) (k : ℕ) := batchTerminalHist q E a.val k j.val
  apply from_layer W hp (hE.trans hEq) H
  · intro a k hk
    rw [Fin.sum_univ_eq_sum_range]
    exact batchTerminalHist_mass hE hEq hk
  · intro j v hv
    let δ (b : ℕ) : ℤ := batchDelta q E b j.val
    have hδ₀ : δ 0 = 0 := by simp [δ,batchDelta,batchDeficit]
    have hδ (b : ℕ) : |(δ b : ℝ)| ≤ E := by
      rw [show (δ b : ℝ) = (batchDelta q E b j.val : ℝ) by simp [δ], abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (batchDelta_lt hE b j.val).le
    apply W.root_of_floor_balance hp (fun a k => H j a k) v hv q E hEq δ hδ₀ E hδ
    intro b
    have hphase (k : ℕ) : H j (phase B p hp b) k = batchTerminalHist q E b k j.val := by
      apply phase_preserves hp (fun b => batchTerminalHist q E b k j.val) _ b
      intro c hcb
      have hh (k : ℕ) : batchPrefix q E (c+p) k = batchPrefix q E c k := (hper c hcb).2 k
      simp only [batchTerminalHist, batchTerminalPrefix, hh]
    have hagg := batchTerminalHist_aggregate hE hEq j.isLt (b := b)
    change (∑ k ∈ Finset.range (batchLeaves q E b), (H j (phase B p hp b) k : ℝ)) =
      (batchBeta q E b : ℝ) + 2*(δ b : ℝ) - (δ (b+1) : ℝ)
    simp only [hphase]
    rw [← Nat.cast_sum, hagg]
    have hcons := congrArg (fun n : ℕ => (n : ℝ)) (batchHist_conserve q E b j.val)
    push_cast at hcons
    simp only [δ, Int.cast_natCast]
    linarith

private theorem skinnyR_scale (den e g b : ℕ) :
    2^b*(g*e) % (g*den) = g*(2^b*e%den) := by
  rw [show 2^b*(g*e) = g*(2^b*e) by ring, Nat.mul_mod_mul_left]

private theorem skinny_width {den e g : ℕ} (he : 0 < e) (hg : 0 < g)
    (hep : e+1=den) (hc : Nat.Coprime e den) (b : ℕ) :
    (2^b*(g*e) % (g*den) + g*e-1)/(g*e) = if den ∣ 2^b then 0 else 1 := by
  have hden : 0 < den := by omega
  have hE : 0 < g*e := Nat.mul_pos hg he
  have hzero : 2^b*e%den = 0 ↔ den ∣ 2^b := by
    rw [← Nat.dvd_iff_mod_eq_zero, hc.symm.dvd_mul_right]
  have hcap := Nat.mod_lt (2^b*e) hden
  have hcap' : g*(2^b*e%den) ≤ g*e := Nat.mul_le_mul_left g (by omega)
  rw [skinnyR_scale]
  by_cases h : den ∣ 2^b
  · rw [if_pos h, hzero.mpr h, Nat.mul_zero, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · rw [if_neg h]
    have hpos : 0 < g*(2^b*e%den) := Nat.mul_pos hg (Nat.pos_of_ne_zero (mt hzero.mp h))
    apply le_antisymm
    · apply (Nat.div_le_iff_le_mul_add_pred hE).mpr
      rw [Nat.mul_one]; omega
    · apply (Nat.le_div_iff_mul_le hE).mpr
      rw [Nat.one_mul]; omega

private theorem skinnyDvd {h d b : ℕ} (ho : d % 2 = 1) :
    2^h*d ∣ 2^b ↔ d = 1 ∧ h ≤ b := by
  constructor
  · intro hd
    have hd' : d ∣ 2^b := (dvd_mul_left _ _).trans hd
    have hc : d.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ho)
    have hd1 : d = 1 := Nat.dvd_one.mp ((hc.pow_right b).dvd_of_dvd_mul_right
      (by simpa using hd' : d ∣ 1 * 2^b))
    refine ⟨hd1, ?_⟩
    simpa [hd1, Nat.pow_dvd_pow_iff_le_right] using hd
  · rintro ⟨rfl, hb⟩
    simpa using Nat.pow_dvd_pow 2 hb

private theorem skinny_tau_period {h d p b : ℕ} (hP : d ∣ 2^p-1) (hb : h ≤ b) :
    2^(b+p) % (2^h*d) = 2^b % (2^h*d) := by
  simpa [batchR] using
    (batchR_period (g := 1) (e := 1) (p := p) (h := h) (d := d) (b := b) hP hb)

private theorem skinny_tau_succ (den b : ℕ) :
    2^(b+1) % den + den*((2*(2^b%den))/den) = 2*(2^b%den) := by
  simpa [batchR, batchBeta] using batchR_succ den 1 b

private theorem skinny_digit_le_one {den : ℕ} (hd : 0 < den) (b : ℕ) :
    (2*(2^b%den))/den ≤ 1 := by
  simpa [batchR, batchBeta] using batchBeta_le_one (E := 1) hd b

open L29934Layer

private theorem skinny_layer {den e g B p : ℕ} (he : 0 < e) (hg : 0 < g) (heq : e+1=den)
    (W : Widths B p) (hp : 0 < p)
    (hw : ∀ b, W.width b = if den ∣ 2^b then 0 else 1)
    (hperiod : ∀ b, B ≤ b → 2^(b+p)%den = 2^b%den) :
    SharpMachine (g*den) (g*e) W.width W.count := by
  classical
  let q := g*den
  let E := g*e
  have hd : 1 < den := by omega
  have hq : 0 < q := Nat.mul_pos hg (by omega)
  have hdecomp : q = g + E := by dsimp [q,E]; rw [← heq, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  obtain ⟨S, hSS, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin q))) (n := g) (by simp; omega)
  let P (j : Fin q) := if j∈S then e else 0
  let Q (j : Fin q) := if j∈S then 0 else 1
  have hP : ∑ j, P j = E := by
    simp only [P, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, hS, nsmul_eq_mul, E]
    rfl
  have hQ : ∑ j, Q j = E := by
    have hs := Finset.card_sdiff_of_subset hSS
    rw [Finset.card_univ, Fintype.card_fin, hS] at hs
    have hq' : q-g=E := by omega
    rw [hq'] at hs
    have hQpoint (j : Fin q) : Q j = if j∉S then 1 else 0 := by
      by_cases hj : j∈S <;> simp [Q,hj]
    simp_rw [hQpoint]
    rw [← Finset.sum_filter, ← Finset.sdiff_eq_filter]
    simpa using hs
  let r (b : ℕ) := 2^b%den
  let β (b : ℕ) := (2*r b)/den
  let G (j : Fin q) (b k : ℕ) :=
    if k+W.width (b+1)=1 ∧ β b=1 then P j else Q j
  let H (j : Fin q) (a : Fin (B+p)) (k : ℕ) := G j a.val k
  apply from_layer W hp hq H
  · intro a k _
    dsimp only [H,G]
    split <;> assumption
  · intro j v hv
    let T (b : ℕ) : ℝ := (Q j : ℝ)*W.width b + ((P j : ℝ)-Q j)*(r b / (den : ℝ))
    have hden : 0 < (den : ℝ) := by exact_mod_cast (show 0 < den by omega)
    have hwle (b : ℕ) : W.width b ≤ 1 := by rw [hw]; split <;> omega
    have hrange (b : ℕ) : |(r b : ℝ)/den| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hden.le)]
      exact (div_le_one hden).2 (by exact_mod_cast (Nat.mod_lt (2^b) (by omega : 0<den)).le)
    apply (show v (W.start hp) = T 0 → _ from fun h => h.trans ?_)
    · apply W.root_of_recurrence hp (fun a k => H j a k) v hv T (|(Q j : ℝ)| + |(P j : ℝ)-Q j|)
      · intro b
        apply (abs_add_le _ _).trans
        have hcast : |(W.width b : ℝ)| = (W.width b : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        rw [abs_mul, abs_mul, hcast]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (by exact_mod_cast hwle b))
          (mul_le_of_le_one_right (abs_nonneg _) (hrange b))
      · intro b
        have hphase (k : ℕ) : H j (phase B p hp b) k = G j b k := by
          apply phase_preserves hp (fun b => G j b k) _ b
          intro c hc
          have hww : W.width (c+p+1) = W.width (c+1) := by
            rw [show c+p+1=c+1+p by omega, W.tail (c+1) (by omega)]
          simp only [G, β, r, hperiod c hc, hww]
        have hβ (b : ℕ) : β b ≤ 1 := skinny_digit_le_one (by omega) b
        have hzero : W.width b = 0 → β b = 0 := by
          intro hz
          rw [hw b] at hz
          split at hz
          · rename_i h
            simp [β,r,Nat.mod_eq_zero_of_dvd h]
          · contradiction
        have hsum : (∑ k ∈ Finset.range (W.slots b), (H j (phase B p hp b) k : ℝ)) =
            (Q j : ℝ)*W.slots b + ((P j : ℝ)-Q j)*β b := by
          simp only [hphase]
          rcases (show W.width b = 0 ∨ W.width b = 1 by have := hwle b; omega) with hw0 | hw1
          · have hwn : W.width (b+1) = 0 := by have := W.step b; omega
            simp [Widths.slots, hw0, hwn, hzero hw0]
          · rcases (show W.width (b+1) = 0 ∨ W.width (b+1) = 1 by have := hwle (b+1); omega) with hw0 | hwn
            · rcases (show β b = 0 ∨ β b = 1 by have := hβ b; omega) with hb' | hb' <;>
                simp [Widths.slots, G, hw1, hw0, hb', Finset.sum_range_succ] <;> ring
            · rcases (show β b = 0 ∨ β b = 1 by have := hβ b; omega) with hb' | hb' <;>
                simp [Widths.slots, G, hw1, hwn, hb'] <;> ring
        have hwint : W.width (b+1) + W.slots b = 2*W.width b :=
          Nat.add_sub_of_le (W.step b)
        have hwreal : (W.width (b+1) : ℝ) + W.slots b = 2*W.width b := by exact_mod_cast hwint
        have hrint : r (b+1) + den*β b = 2*r b := skinny_tau_succ den b
        have hrreal : ((r (b+1) : ℝ)/den) + β b = 2*((r b : ℝ)/den) := by
          have hrc : (r (b+1) : ℝ) + (den : ℝ)*β b = 2*r b := by exact_mod_cast hrint
          field_simp
          linarith
        rw [hsum]
        dsimp [T]
        linear_combination -(Q j : ℝ)*hwreal - ((P j : ℝ)-Q j)*hrreal
    · have hr0 : r 0 = 1 := by simp [r,Nat.mod_eq_of_lt hd]
      have hrat : (E : ℝ)/q = (e : ℝ)/den := by
        have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
        simpa [E,q,Nat.cast_mul] using mul_div_mul_left (e : ℝ) (den : ℝ) hg'
      rw [hrat, show T 0 = (Q j : ℝ) + ((P j : ℝ)-Q j)/(den : ℝ) by
        simp [T, W.root, hr0, div_eq_mul_inv]]
      have hc : (e : ℝ)+1 = den := by exact_mod_cast heq
      by_cases hj : j∈S <;> simp [P,Q,hj] <;> field_simp <;> linarith

private theorem skinny_machine {h d e g p : ℕ} (ho : d%2=1) (he : 0<e) (hg : 0<g)
    (heq : e+1=2^h*d) (hc : Nat.Coprime e (2^h*d)) (hp : 0<p) (hp' : d∣2^p-1) :
    SharpMachine (g*(2^h*d)) (g*e) (batchWidth (g*(2^h*d)) (g*e))
      (h+(if d=1 then 0 else p)) := by
  let q := g*(2^h*d)
  let E := g*e
  have hw (b : ℕ) : batchWidth q E b = if 2^h*d ∣ 2^b then 0 else 1 :=
    skinny_width he hg heq hc b
  have hE : 0 < E := Nat.mul_pos hg he
  have hEq : E < q := Nat.mul_lt_mul_of_pos_left (by omega) hg
  by_cases hd : d=1
  · let W : Widths h 1 := Widths.mk (batchWidth q E) (batchWidth_zero hE hEq) (batchWidth_succ_le hE) (by
      intro b hb
      rw [hw (b+1), hw b, if_pos ((skinnyDvd ho).2 ⟨hd,hb.trans (Nat.le_succ b)⟩),
        if_pos ((skinnyDvd ho).2 ⟨hd,hb⟩)])
    have hperiod (b : ℕ) (hb : h≤b) : 2^(b+1)%(2^h*d) = 2^b%(2^h*d) := by
      rw [Nat.mod_eq_zero_of_dvd ((skinnyDvd ho).2 ⟨hd,hb.trans (Nat.le_succ b)⟩),
        Nat.mod_eq_zero_of_dvd ((skinnyDvd ho).2 ⟨hd,hb⟩)]
    have hcount : W.count = h := by
      unfold Widths.count
      rw [Finset.sum_range_succ]
      have hs : ∑ b ∈ Finset.range h, W.width b = ∑ _b ∈ Finset.range h, 1 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact (hw b).trans (if_neg (fun H => (Nat.not_le_of_gt (Finset.mem_range.mp hb)) ((skinnyDvd ho).1 H).2))
      rw [hs]
      have hh : W.width h = 0 := (hw h).trans (if_pos ((skinnyDvd ho).mpr ⟨hd,le_rfl⟩))
      simp [hh]
    change SharpMachine q E (batchWidth q E) (h+(if d=1 then 0 else p))
    rw [if_pos hd,Nat.add_zero]
    have hh := skinny_layer he hg heq W Nat.one_pos hw hperiod
    exact (congrArg (fun k => SharpMachine q E (batchWidth q E) k) hcount).mp hh
  · let W := Widths.skinny h p
    have hW (b : ℕ) : W.width b = if 2^h*d ∣ 2^b then 0 else 1 :=
      (if_neg (fun H => hd ((skinnyDvd ho).1 H).1)).symm
    have hhead := skinny_layer he hg heq W hp hW (fun b hb => skinny_tau_period hp' hb)
    have hfun : W.width = batchWidth q E := funext (fun b => (hW b).trans (hw b).symm)
    have hcount : W.count = h+p := Widths.skinny_count h p
    rw [hfun,hcount] at hhead
    simpa only [hd, if_false] using hhead

open scoped BigOperators

namespace NarrowDenominator

private def IsInteger (x : ℝ) : Prop := ∃ j : ℤ, x = (j : ℝ)

private theorem IsInteger.add {x y : ℝ} (hx : IsInteger x) (hy : IsInteger y) :
    IsInteger (x + y) := by
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  exact ⟨j + k, (Int.cast_add j k).symm⟩

private theorem IsInteger.mul {x y : ℝ} (hx : IsInteger x) (hy : IsInteger y) :
    IsInteger (x * y) := by
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  exact ⟨j * k, (Int.cast_mul j k).symm⟩

private theorem nat_integer (j : ℕ) : IsInteger (j : ℝ) :=
  ⟨(j : ℤ), by simp⟩

private theorem pow_two_integer (r : ℕ) : IsInteger ((2 : ℝ) ^ r) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_integer (2 ^ r)

private def payoff {α : Type*} (n : α → Bool → Option α) (a : α → Bool → ℤ)
    (v : α → ℝ) (i : α) (b : Bool) : ℝ := (n i b).elim (a i b : ℝ) v

private theorem sum_bool_chosen (f : Bool → ℝ) (b : Bool) :
    (∑ c : Bool, f c) = f b + f (!b) := by
  cases b
  · exact (Fintype.sum_bool f).trans (add_comm _ _)
  · exact Fintype.sum_bool f

/-- Each edge off the boundary consumes at most one dyadic factor. A zero rank is
reserved for the boundary; a non-boundary state whose edges both stop can have rank one. -/
private theorem integer_at_depth {α : Type*} (n : α → Bool → Option α)
    (a : α → Bool → ℤ) (v : α → ℝ) (Q : ℕ) (active boundary : α → Prop)
    (rank : α → ℕ)
    (law : ∀ i, 2 * v i = ∑ b : Bool, payoff n a v i b)
    (base : ∀ i, active i → boundary i → IsInteger ((Q : ℝ) * v i))
    (step : ∀ i, active i → ¬ boundary i → 0 < rank i ∧
      ∀ b j, n i b = some j → active j ∧ rank j < rank i) :
    ∀ r i, active i → rank i ≤ r → IsInteger (((2 : ℝ) ^ r * Q) * v i) := by
  intro r
  induction r with
  | zero =>
      intro i hi hr
      by_cases hb : boundary i
      · simpa using base i hi hb
      · exact False.elim (by have := (step i hi hb).1; omega)
  | succ r ih =>
      intro i hi hr
      by_cases hb : boundary i
      · rw [mul_assoc]
        exact (pow_two_integer _).mul (base i hi hb)
      · have child (b : Bool) : IsInteger (((2 : ℝ) ^ r * Q) * payoff n a v i b) := by
          cases hj : n i b with
          | none =>
              rw [payoff, hj]
              exact ((pow_two_integer r).mul (nat_integer Q)).mul ⟨a i b, rfl⟩
          | some j =>
              obtain ⟨hja, hjr⟩ := (step i hi hb).2 b j hj
              simpa [payoff, hj] using ih j hja (by omega)
        convert (child true).add (child false) using 1
        calc
          ((2 : ℝ) ^ (r + 1) * Q) * v i = ((2 : ℝ) ^ r * Q) * (2 * v i) := by
            rw [pow_succ]; ring
          _ = ((2 : ℝ) ^ r * Q) * (payoff n a v i true + payoff n a v i false) := by
            rw [law i, Fintype.sum_bool]
          _ = _ := mul_add _ _ _

/-- Clear one odd cycle factor without spending a dyadic factor per traversal. -/
private theorem integer_at_cycle (l : ℕ) (f : ℕ → ℝ) (D : ℝ)
    (hclose : f l = f 0)
    (hexit : ∀ k < l, IsInteger (D * (2 * f k - f (k + 1)))) :
    IsInteger (((2 ^ l - 1 : ℕ) : ℝ) * (D * f 0)) := by
  have hspan : ∀ k ≤ l, IsInteger (D * ((2 : ℝ) ^ k * f 0 - f k)) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨0, by simp⟩
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hn := hexit k (by omega)
        convert ((nat_integer 2).mul hprev).add hn using 1
        push_cast
        rw [pow_succ]
        ring
  have hspan' := hspan l le_rfl
  convert hspan' using 1
  rw [hclose, Nat.cast_sub (Nat.one_le_pow l 2 (by decide))]
  push_cast
  ring

private theorem odd_cycle_lcm {m : ℕ} (l : Fin m → ℕ) (hl : ∀ j, 0 < l j) :
    Odd ((Finset.univ : Finset (Fin m)).lcm fun j => 2 ^ l j - 1) := by
  have hx (j : Fin m) : ¬ 2 ∣ 2 ^ l j - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hj := hl j
    cases h : l j with
    | zero => omega
    | succ k =>
        rw [pow_succ]
        have hp : 0 < (2 : ℕ) ^ k := by positivity
        omega
  have hnot (S : Finset (Fin m)) : ¬ 2 ∣ S.lcm (fun j => 2 ^ l j - 1) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
        rw [Finset.lcm_insert, lcm_eq_nat_lcm]
        exact Nat.prime_two.not_dvd_lcm (hx j) ih
  by_contra hn
  exact hnot Finset.univ (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hn))

private theorem reduced_denominator {e h d r Q : ℕ} {x : ℝ} (hd : 0 < d)
    (hdodd : Odd d) (hQodd : Odd Q) (hcop : Nat.Coprime e (2 ^ h * d))
    (hx : x = (e : ℝ) / ((2 ^ h * d : ℕ) : ℝ))
    (hint : IsInteger (((2 : ℝ) ^ r * Q) * x)) : h ≤ r ∧ d ∣ Q := by
  let D : ℕ := 2 ^ h * d
  let W : ℕ := 2 ^ r * Q
  have hD : (D : ℝ) ≠ 0 := by
    have hDp : 0 < D := by dsimp [D]; positivity
    exact_mod_cast (Nat.ne_of_gt hDp)
  obtain ⟨j, hj⟩ := hint
  have hscale : (W : ℝ) * ((e : ℝ) / (D : ℝ)) = (j : ℝ) := by
    rw [← hx]
    simpa only [W, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hj
  have hclear : (W : ℝ) * (e : ℝ) = (D : ℝ) * (j : ℝ) := by
    rw [← mul_div_assoc] at hscale
    exact ((div_eq_iff hD).mp hscale).trans (mul_comm _ _)
  have hnat : D ∣ W * e := by
    apply Int.natCast_dvd_natCast.mp
    refine ⟨j, Int.cast_injective (α := ℝ) ?_⟩
    simpa only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul] using hclear
  have hdiv : D ∣ W := hcop.symm.dvd_of_dvd_mul_right hnat
  have hp : 2 ^ h ∣ W := (dvd_mul_right (2 ^ h) d).trans hdiv
  have hodd : d ∣ W := (dvd_mul_left d (2 ^ h)).trans hdiv
  exact ⟨(Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp
      (((Nat.coprime_two_left.mpr hQodd).pow_left h).dvd_of_dvd_mul_right hp),
    ((Nat.coprime_two_right.mpr hdodd).pow_right r).dvd_of_dvd_mul_left hodd⟩

/-- Exact arithmetic interface to the graph argument. The two rank budgets count disjoint
classes of states: mortal states (which cannot reach any cycle), and reachable states
which are neither mortal nor on a cycle. Cycle edges may exit into mortal states. -/
theorem of_partition {s m h d e r t K : ℕ} (z : Fin s)
    (n : Fin s → Bool → Option (Fin s)) (a : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (l : Fin m → ℕ) (P M C : Fin s → Prop) (rankM rankT : Fin s → ℕ)
    (law : ∀ i, 2 * v i = ∑ b : Bool, (n i b).elim (a i b : ℝ) v)
    (hz : P z) (hd : 0 < d) (hdodd : d % 2 = 1) (hcop : Nat.Coprime e (2 ^ h * d))
    (hv : v z = (e : ℝ) / ((2 ^ h * d : ℕ) : ℝ))
    (hm : m ≤ K) (hl : ∀ c, 0 < l c) (hbudget : r + t + (∑ c, l c) ≤ s)
    (hMbound : ∀ i, M i → rankM i ≤ r)
    (hMstep : ∀ i, M i → 0 < rankM i ∧
      ∀ b j, n i b = some j → M j ∧ rankM j < rankM i)
    (hTbound : ∀ i, P i → rankT i ≤ t)
    (hTstep : ∀ i, P i → ¬ (M i ∨ C i) → 0 < rankT i ∧
      ∀ b j, n i b = some j → P j ∧ rankT j < rankT i)
    (hcycle : ∀ i, C i → ∃ (c : Fin m) (path : ℕ → Fin s) (bit : ℕ → Bool),
      path 0 = i ∧ path (l c) = i ∧ ∀ k < l c,
        n (path k) (bit k) = some (path (k + 1)) ∧
        ∀ j, n (path k) (!(bit k)) = some j → M j) :
    ∃ (m' : ℕ) (l' : Fin m' → ℕ), m' ≤ K ∧ (∀ c, 0 < l' c) ∧
      h + (∑ c, l' c) ≤ s ∧ d ∣ (Finset.univ : Finset (Fin m')).lcm (fun c => 2 ^ l' c - 1) := by
  let Q := (Finset.univ : Finset (Fin m)).lcm fun c => 2 ^ l c - 1
  have hM : ∀ i, M i → IsInteger ((2 : ℝ) ^ r * v i) := by
    intro i hi
    simpa using integer_at_depth n a v 1 M (fun _ => False) rankM law
      (fun _ _ h => h.elim) (fun j hj _ => hMstep j hj) r i hi (hMbound i hi)
  have hC : ∀ i, C i → IsInteger (((2 : ℝ) ^ r * Q) * v i) := by
    intro i hi
    obtain ⟨c, path, bit, hstart, hend, hpath⟩ := hcycle i hi
    have hclose : v (path (l c)) = v (path 0) := by rw [hend, hstart]
    have hs (k : ℕ) (hk : k < l c) :
        IsInteger ((2 : ℝ) ^ r * (2 * v (path k) - v (path (k + 1)))) := by
      obtain ⟨hnext, hmortal⟩ := hpath k hk
      have hsum : 2 * v (path k) = v (path (k + 1)) + payoff n a v (path k) (!(bit k)) := by
        rw [law (path k)]
        change (∑ b : Bool, payoff n a v (path k) b) = _
        have hpay : payoff n a v (path k) (bit k) = v (path (k + 1)) := by
          simp [payoff, hnext]
        rw [sum_bool_chosen _ (bit k), hpay]
      rw [hsum, add_sub_cancel_left]
      cases hj : n (path k) (!(bit k)) with
      | none =>
          rw [payoff, hj]
          exact (pow_two_integer r).mul ⟨a (path k) (!(bit k)), rfl⟩
      | some j =>
          simpa [payoff, hj] using hM j (hmortal j hj)
    have hlocal := integer_at_cycle (l c) (fun k => v (path k)) ((2 : ℝ) ^ r) hclose hs
    change IsInteger (((2 ^ l c - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ r * v (path 0))) at hlocal
    rw [hstart] at hlocal
    have hdiv : (2 ^ l c - 1 : ℕ) ∣ Q := Finset.dvd_lcm (Finset.mem_univ c)
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, Nat.cast_mul]
    convert (nat_integer q).mul hlocal using 1 <;> ring
  have hbase : ∀ i, P i → M i ∨ C i → IsInteger (((Q * 2 ^ r : ℕ) : ℝ) * v i) := by
    intro i _ hi
    have hint : IsInteger (((2 : ℝ) ^ r * Q) * v i) := by
      rcases hi with hmortal | hcyclic
      · rw [mul_comm ((2 : ℝ) ^ r), mul_assoc]
        exact (nat_integer Q).mul (hM i hmortal)
      · exact hC i hcyclic
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm (Q : ℝ)] using hint
  have hT := integer_at_depth n a v (Q * 2 ^ r) P (fun i => M i ∨ C i) rankT law
    hbase hTstep t z hz (hTbound z hz)
  have hzint : IsInteger (((2 : ℝ) ^ (r + t) * Q) * v z) := by
    convert hT using 1
    push_cast
    rw [pow_add]
    ring
  obtain ⟨hhr, hdiv⟩ := reduced_denominator hd (Nat.odd_iff.mpr hdodd)
    (odd_cycle_lcm l hl) hcop hv hzint
  exact ⟨m, l, hm, hl, by omega, hdiv⟩

def Edge {α : Type*} (n : α → Bool → Option α) (i j : α) : Prop :=
  ∃ b, n i b = some j

def ReachesCycle {α : Type*} (n : α → Bool → Option α) (i : α) : Prop :=
  ∃ j, Relation.ReflTransGen (Edge n) i j ∧ Relation.TransGen (Edge n) j j

noncomputable def cycleStates {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) :
    Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun i =>
    Relation.ReflTransGen (Edge n) z i ∧ Relation.TransGen (Edge n) i i

/-- Count the states in the same region still reachable from the current state. The
region need not be forward-closed: its complement receives rank zero. -/
private theorem rank_acyclic {α : Type*} (edge : α → α → Prop) (U : Finset α)
    (hU : ∀ i ∈ U, ¬ Relation.TransGen edge i i) :
    ∃ rank : α → ℕ, (∀ i, rank i ≤ U.card) ∧
      ∀ i ∈ U, 0 < rank i ∧ ∀ j, edge i j → rank j < rank i := by
  classical
  let reach (i : α) : Finset α :=
    if i ∈ U then U.filter (Relation.ReflTransGen edge i) else ∅
  have hmem (i x : α) :
      x ∈ reach i ↔ i ∈ U ∧ x ∈ U ∧ Relation.ReflTransGen edge i x := by
    by_cases hi : i ∈ U <;> simp [reach, hi]
  refine ⟨fun i => (reach i).card, ?_, ?_⟩
  · intro i
    exact Finset.card_le_card fun x hx => ((hmem i x).mp hx).2.1
  · intro i hi
    have hself : i ∈ reach i := (hmem i i).mpr ⟨hi, hi, .refl⟩
    refine ⟨Finset.card_pos.mpr ⟨i, hself⟩, ?_⟩
    intro j hij
    have hsub : reach j ⊆ reach i := by
      intro x hx
      obtain ⟨_, hxU, hjx⟩ := (hmem j x).mp hx
      exact (hmem i x).mpr ⟨hi, hxU, Relation.ReflTransGen.head hij hjx⟩
    apply Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ?_)
    refine ⟨i, hself, fun hback => hU i hi ?_⟩
    exact Relation.TransGen.head' hij ((hmem j i).mp hback).2.2

/-- Only the recurrent-narrow graph cover remains: cover all reachable cyclic
vertices by the enumerated disjoint cycles, and show that each non-cycle edge
from such a vertex either stops or cannot reach a cycle. -/
theorem of_cycle_cover {s m h d e K : ℕ} (z : Fin s)
    (n : Fin s → Bool → Option (Fin s)) (a : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (l : Fin m → ℕ)
    (law : ∀ i, 2 * v i = ∑ b : Bool, (n i b).elim (a i b : ℝ) v)
    (hd : 0 < d) (hdodd : d % 2 = 1) (hcop : Nat.Coprime e (2 ^ h * d))
    (hv : v z = (e : ℝ) / ((2 ^ h * d : ℕ) : ℝ))
    (hm : m ≤ K) (hl : ∀ c, 0 < l c)
    (hcard : (∑ c, l c) ≤ (cycleStates z n).card)
    (hcover : ∀ i ∈ cycleStates z n,
      ∃ (c : Fin m) (path : ℕ → Fin s) (bit : ℕ → Bool),
        path 0 = i ∧ path (l c) = i ∧ ∀ k < l c,
          n (path k) (bit k) = some (path (k + 1)) ∧
          ∀ j, n (path k) (!(bit k)) = some j → ¬ ReachesCycle n j) :
    ∃ (m' : ℕ) (l' : Fin m' → ℕ), m' ≤ K ∧ (∀ c, 0 < l' c) ∧
      h + (∑ c, l' c) ≤ s ∧ d ∣ (Finset.univ : Finset (Fin m')).lcm (fun c => 2 ^ l' c - 1) := by
  classical
  let P := Relation.ReflTransGen (Edge n) z
  let M : Fin s → Prop := fun i => P i ∧ ¬ ReachesCycle n i
  let C : Fin s → Prop := fun i => i ∈ cycleStates z n
  let S : Finset (Fin s) := Finset.univ.filter M
  let T : Finset (Fin s) := Finset.univ.filter fun i => P i ∧ ¬ (M i ∨ C i)
  have hC (i) : C i ↔ P i ∧ Relation.TransGen (Edge n) i i := by
    simp only [C, cycleStates, Finset.mem_filter, Finset.mem_univ, true_and, P]
  have hS (i) : i ∈ S ↔ M i := by simp [S]
  have hT (i) : i ∈ T ↔ P i ∧ ¬ (M i ∨ C i) := by simp [T]
  have hP {i j : Fin s} (hi : P i) (hij : Edge n i j) : P j :=
    Relation.ReflTransGen.tail hi hij
  have hSacyc (i) (hi : i ∈ S) : ¬ Relation.TransGen (Edge n) i i :=
    fun hloop => ((hS i).mp hi).2 ⟨i, .refl, hloop⟩
  have hTacyc (i) (hi : i ∈ T) : ¬ Relation.TransGen (Edge n) i i :=
    fun hloop => ((hT i).mp hi).2 (Or.inr ((hC i).mpr ⟨((hT i).mp hi).1, hloop⟩))
  obtain ⟨rankM, hMb, hMs⟩ := rank_acyclic (Edge n) S hSacyc
  obtain ⟨rankT, hTb, hTs⟩ := rank_acyclic (Edge n) T hTacyc
  have hSc : Disjoint S (cycleStates z n) := by
    rw [Finset.disjoint_left]
    intro i hi hc
    exact hSacyc i hi ((hC i).mp hc).2
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hi ht
    exact ((hT i).mp ht).2 (Or.inl ((hS i).mp hi))
  have hTc : Disjoint T (cycleStates z n) := by
    rw [Finset.disjoint_left]
    intro i hi hc
    exact ((hT i).mp hi).2 (Or.inr hc)
  have hbudget : S.card + T.card + (∑ c, l c) ≤ s := by
    have hu : ((S ∪ T) ∪ cycleStates z n).card ≤ s := by
      simpa using Finset.card_le_univ ((S ∪ T) ∪ cycleStates z n)
    rw [Finset.card_union_of_disjoint (disjoint_sup_left.mpr ⟨hSc, hTc⟩),
      Finset.card_union_of_disjoint hST] at hu
    omega
  refine of_partition z n a v l P M C rankM rankT law .refl hd hdodd hcop hv hm hl hbudget
    (fun i _ => hMb i) ?_ (fun i _ => hTb i) ?_ ?_
  · intro i hi
    obtain ⟨hpos, hdec⟩ := hMs i ((hS i).mpr hi)
    refine ⟨hpos, fun b j hj => ⟨⟨hP hi.1 ⟨b, hj⟩, ?_⟩, hdec j ⟨b, hj⟩⟩⟩
    rintro ⟨k, hjk, hloop⟩
    exact hi.2 ⟨k, Relation.ReflTransGen.head ⟨b, hj⟩ hjk, hloop⟩
  · intro i hi hnb
    obtain ⟨hpos, hdec⟩ := hTs i ((hT i).mpr ⟨hi, hnb⟩)
    exact ⟨hpos, fun b j hj => ⟨hP hi ⟨b, hj⟩, hdec j ⟨b, hj⟩⟩⟩
  · intro i hi
    obtain ⟨c, path, bit, hs, he, hpath⟩ := hcover i hi
    have hreach : ∀ k ≤ l c, P (path k) := by
      intro k
      induction k with
      | zero => intro _; simpa only [hs] using ((hC i).mp hi).1
      | succ k ih =>
          intro hk
          exact hP (ih (by omega)) ⟨bit k, (hpath k (by omega)).1⟩
    exact ⟨c, path, bit, hs, he, fun k hk => ⟨(hpath k hk).1,
      fun j hj => ⟨hP (hreach k hk.le) ⟨!(bit k), hj⟩, (hpath k hk).2 j hj⟩⟩⟩

def runWord {α : Type*} (n : α → Bool → Option α) (x : Option α) (w : List Bool) :
    Option α := w.foldl (fun y b => y.bind fun i => n i b) x

theorem runWord_append {α : Type*} (n : α → Bool → Option α) (x : Option α)
    (u w : List Bool) : runWord n x (u ++ w) = runWord n (runWord n x u) w :=
  List.foldl_append

private theorem reachable_word {α : Type*} {n : α → Bool → Option α} {i j : α}
    (h : Relation.ReflTransGen (Edge n) i j) :
    ∃ w : List Bool, runWord n (some i) w = some j := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hj ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨b, hb⟩ := hj
      exact ⟨w ++ [b], by rw [runWord_append, hw]; exact hb⟩

private theorem cyclic_word {α : Type*} {n : α → Bool → Option α} {i j : α}
    (h : Relation.TransGen (Edge n) i j) :
    ∃ w : List Bool, 0 < w.length ∧ runWord n (some i) w = some j := by
  induction h with
  | single h =>
      obtain ⟨b, hb⟩ := h
      exact ⟨[b], by simp, hb⟩
  | tail _ hj ih =>
      obtain ⟨w, hwpos, hw⟩ := ih
      obtain ⟨b, hb⟩ := hj
      exact ⟨w ++ [b], by simp, by rw [runWord_append, hw]; exact hb⟩

noncomputable def liveWords {α : Type*} (n : α → Bool → Option α) (z : α) (b : ℕ) :
    Finset (Fin b → Bool) :=
  Finset.univ.filter fun w => (runWord n (some z) (List.ofFn w)).isSome

noncomputable def immortalWords {α : Type*} (n : α → Bool → Option α) (z : α) (b : ℕ) :
    Finset (Fin b → Bool) := by
  classical
  exact Finset.univ.filter fun w =>
    ∃ i, runWord n (some z) (List.ofFn w) = some i ∧ ReachesCycle n i

private theorem mem_immortalWords {α : Type*} {n : α → Bool → Option α} {z : α}
    {b : ℕ} {w : Fin b → Bool} :
    w ∈ immortalWords n z b ↔
      ∃ i, runWord n (some z) (List.ofFn w) = some i ∧ ReachesCycle n i := by
  classical
  simp [immortalWords]

private theorem immortal_subset_live {α : Type*} (n : α → Bool → Option α) (z : α) (b : ℕ) :
    immortalWords n z b ⊆ liveWords n z b := by
  intro w hw
  obtain ⟨i, hi, _⟩ := mem_immortalWords.mp hw
  simp [liveWords, hi]

private theorem immortal_succ {α : Type*} {n : α → Bool → Option α} {i : α}
    (h : ReachesCycle n i) : ∃ b j, n i b = some j ∧ ReachesCycle n j := by
  obtain ⟨k, hik, hkk⟩ := h
  rcases hik.cases_head with he | ⟨j, ⟨b, hb⟩, hjk⟩
  · subst k
    obtain ⟨j, ⟨b, hb⟩, hjk⟩ := Relation.TransGen.head'_iff.mp hkk
    exact ⟨b, j, hb, i, hjk, hkk⟩
  · exact ⟨b, j, hb, k, hjk, hkk⟩

private theorem runWord_snoc {α : Type*} (n : α → Bool → Option α) (z : α)
    {b : ℕ} (w : Fin b → Bool) (x : Bool) :
    runWord n (some z) (List.ofFn (Fin.snoc w x)) =
      (runWord n (some z) (List.ofFn w)).bind (fun i => n i x) := by
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, runWord_append] <;> rfl

private theorem immortal_card_step {α : Type*} (n : α → Bool → Option α) (z : α)
    (b : ℕ) :
    (immortalWords n z b).card ≤ (immortalWords n z (b + 1)).card ∧
    ((∃ w : Fin b → Bool, w ∈ immortalWords n z b ∧
        ∀ x : Bool, Fin.snoc w x ∈ immortalWords n z (b + 1)) →
      (immortalWords n z b).card < (immortalWords n z (b + 1)).card) := by
  classical
  let S := immortalWords n z b
  let T := immortalWords n z (b + 1)
  have next (w : Fin b → Bool) (hw : w ∈ S) : ∃ x : Bool, Fin.snoc w x ∈ T := by
    obtain ⟨i, hi, hcyc⟩ := mem_immortalWords.mp hw
    obtain ⟨x, j, hx, hj⟩ := immortal_succ hcyc
    exact ⟨x, mem_immortalWords.mpr ⟨j, by rw [runWord_snoc, hi]; exact hx, hj⟩⟩
  let pick (w : Fin b → Bool) : Bool := if hw : w ∈ S then (next w hw).choose else false
  let f (w : Fin b → Bool) : Fin (b+1) → Bool := Fin.snoc w (pick w)
  have hinj : Function.Injective f := by
    intro u w h
    funext i
    simpa only [f, Fin.snoc_castSucc] using congrFun h i.castSucc
  have himage : S.image f ⊆ T := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    simpa only [f, pick, dif_pos hu] using (next u hu).choose_spec
  have hcard := Finset.card_image_of_injective S hinj
  refine ⟨hcard ▸ Finset.card_le_card himage, ?_⟩
  rintro ⟨w, _, hboth⟩
  have hout : Fin.snoc w (!(pick w)) ∉ S.image f := by
    intro hx
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
    have huw : u = w := by
      funext i
      simpa only [f, Fin.snoc_castSucc] using congrFun hu i.castSucc
    subst u
    have heq : pick w = !(pick w) := by
      simpa only [f, Fin.snoc_last] using congrFun hu (Fin.last b)
    cases hb : pick w <;> simp [hb] at heq
  have hstrict := (Finset.ssubset_iff_of_subset himage).mpr ⟨_, hboth _, hout⟩
  exact hcard ▸ Finset.card_lt_card hstrict

private theorem long_cyclic_prefix {α : Type*} {n : α → Bool → Option α} {z i : α}
    (hzi : Relation.ReflTransGen (Edge n) z i) (hii : Relation.TransGen (Edge n) i i) (a : ℕ) :
    ∃ b ≥ a, ∃ w : Fin b → Bool, runWord n (some z) (List.ofFn w) = some i := by
  obtain ⟨p, hp⟩ := reachable_word hzi
  obtain ⟨q, hqpos, hq⟩ := cyclic_word hii
  have hrep : ∀ r : ℕ, ∃ w : List Bool, r ≤ w.length ∧ runWord n (some i) w = some i := by
    intro r
    induction r with
    | zero => exact ⟨[], by simp, rfl⟩
    | succ r ih =>
        obtain ⟨w, hl, hw⟩ := ih
        refine ⟨q ++ w, ?_, by rw [runWord_append, hq, hw]⟩
        simp only [List.length_append]
        omega
  obtain ⟨w, hwlen, hwrun⟩ := hrep a
  refine ⟨(p ++ w).length, by simp only [List.length_append]; omega,
    fun k => (p ++ w)[k.val], ?_⟩
  rw [List.ofFn_getElem, runWord_append, hp, hwrun]

/-- Narrow levels rule out two different immortal bits at a reachable cyclic state. -/
theorem cycle_exit_mortal {α : Type*} (n : α → Bool → Option α) (z : α) (K : ℕ)
    (hwidth : ∀ a, ∃ b ≥ a, (liveWords n z b).card ≤ K)
    {i j k : α} (hzi : Relation.ReflTransGen (Edge n) z i)
    (hii : Relation.TransGen (Edge n) i i) {x : Bool}
    (hx : n i x = some j) (hj : ReachesCycle n j)
    (hy : n i (!x) = some k) : ¬ ReachesCycle n k := by
  intro hk
  let F (b : ℕ) := (immortalWords n z b).card
  have hmono : Monotone F := monotone_nat_of_le_succ fun b => (immortal_card_step n z b).1
  have hbound (b : ℕ) : F b ≤ K := by
    obtain ⟨c, hbc, hc⟩ := hwidth b
    exact (hmono hbc).trans ((Finset.card_le_card (immortal_subset_live n z c)).trans hc)
  have hgrow (a : ℕ) : ∃ c, F a < F c := by
    obtain ⟨b, hab, w, hw⟩ := long_cyclic_prefix hzi hii a
    have hmem : w ∈ immortalWords n z b :=
      mem_immortalWords.mpr ⟨i, hw, i, .refl, hii⟩
    have htwo (y : Bool) : Fin.snoc w y ∈ immortalWords n z (b + 1) := by
      apply mem_immortalWords.mpr
      rw [runWord_snoc, hw]
      by_cases heq : y = x
      · exact ⟨j, by simpa [heq] using hx, hj⟩
      · have hneq : y = !x := by cases y <;> cases x <;> simp_all
        exact ⟨k, by simpa [hneq] using hy, hk⟩
    exact ⟨b + 1, (hmono hab).trans_lt ((immortal_card_step n z b).2 ⟨w, hmem, htwo⟩)⟩
  have hunbounded (r : ℕ) : ∃ c, r ≤ F c := by
    induction r with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ r ih =>
        obtain ⟨a, ha⟩ := ih
        obtain ⟨c, hc⟩ := hgrow a
        exact ⟨c, Nat.succ_le_of_lt (ha.trans_lt hc)⟩
  obtain ⟨c, hc⟩ := hunbounded (K + 1)
  have hle := hc.trans (hbound c)
  omega

/-- At a common narrow level, end one word in each cycle to obtain distinct words. -/
private theorem cycle_count_le {α : Type*} {m K : ℕ} (n : α → Bool → Option α)
    (z : α) (hwidth : ∀ a, ∃ b ≥ a, (liveWords n z b).card ≤ K)
    (part : Fin m → α → Prop)
    (entry : ∀ c, ∃ i, Relation.ReflTransGen (Edge n) z i ∧ part c i)
    (step : ∀ c i, part c i → ∃ b j, n i b = some j ∧ part c j)
    (disj : ∀ c d i, part c i → part d i → c = d) : m ≤ K := by
  classical
  choose root hroot hp using entry
  choose pref hpref using fun c => reachable_word (hroot c)
  let B := (Finset.univ : Finset (Fin m)).sup fun c => (pref c).length
  obtain ⟨b, hB, hb⟩ := hwidth B
  have extend (c : Fin m) :
      ∀ (k : ℕ) (i : α), part c i → ∃ (w : List Bool) (j : α),
        w.length = k ∧ runWord n (some i) w = some j ∧ part c j := by
    intro k
    induction k with
    | zero => exact fun i hi => ⟨[], i, rfl, rfl, hi⟩
    | succ k ih =>
        intro i hi
        obtain ⟨x, j, hx, hj⟩ := step c i hi
        obtain ⟨w, l, hlen, hw, hl⟩ := ih j hj
        refine ⟨x :: w, l, by simpa only [List.length_cons, hlen], ?_, hl⟩
        change runWord n (n i x) w = some l
        rwa [hx]
  have words (c : Fin m) : ∃ (w : Fin b → Bool) (i : α),
      runWord n (some z) (List.ofFn w) = some i ∧ part c i := by
    have hle : (pref c).length ≤ b :=
      (Finset.le_sup (f := fun c => (pref c).length) (Finset.mem_univ c)).trans hB
    obtain ⟨w, i, hwlen, hw, hi⟩ := extend c (b - (pref c).length) (root c) (hp c)
    have hlen : (pref c ++ w).length = b := by
      simp only [List.length_append, hwlen]
      omega
    rw [← hlen]
    refine ⟨fun k => (pref c ++ w)[k.val], i, ?_, hi⟩
    rw [List.ofFn_getElem, runWord_append, hpref c, hw]
  choose word dst hrun hd using words
  let F : Fin m → ↥(liveWords n z b) := fun c =>
    ⟨word c, by simp [liveWords, hrun c]⟩
  have hF : Function.Injective F := by
    intro c d he
    have hwords : word c = word d := congrArg Subtype.val he
    have hdst : dst c = dst d := by
      apply Option.some.inj
      rw [← hrun c, ← hrun d, hwords]
    exact disj c d (dst c) (hd c) (hdst.symm ▸ hd d)
  have hc : m ≤ (liveWords n z b).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hF
  exact hc.trans hb

/-- Recurrent-narrow denominator bound. Finite stopping is not needed in this
graph-and-arithmetic step once the harmonic value at `z` has been identified. -/
theorem recurrent_narrow {s h d e K : ℕ} (z : Fin s)
    (n : Fin s → Bool → Option (Fin s)) (a : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (law : ∀ i, 2 * v i = ∑ b : Bool, (n i b).elim (a i b : ℝ) v)
    (hd : 0 < d) (hdodd : d % 2 = 1) (hcop : Nat.Coprime e (2 ^ h * d))
    (hv : v z = (e : ℝ) / ((2 ^ h * d : ℕ) : ℝ))
    (hwidth : ∀ a, ∃ b ≥ a, (liveWords n z b).card ≤ K) :
    ∃ (m : ℕ) (l : Fin m → ℕ), m ≤ K ∧ (∀ c, 0 < l c) ∧
      h + (∑ c, l c) ≤ s ∧ d ∣ (Finset.univ : Finset (Fin m)).lcm (fun c => 2 ^ l c - 1) := by
  classical
  let U := ↥(cycleStates z n)
  have memC (i : Fin s) :
      i ∈ cycleStates z n ↔
        Relation.ReflTransGen (Edge n) z i ∧ Relation.TransGen (Edge n) i i := by
    simp [cycleStates]
  have reach (i : U) : Relation.ReflTransGen (Edge n) z i.val := ((memC i.val).mp i.property).1
  have cyclic (i : U) : Relation.TransGen (Edge n) i.val i.val := ((memC i.val).mp i.property).2
  have immortal (i : U) : ReachesCycle n i.val := ⟨i.val, .refl, cyclic i⟩
  have choose_edge (i : U) : ∃ (b : Bool) (j : U), n i.val b = some j.val := by
    obtain ⟨j, ⟨b, hb⟩, hbwd⟩ := Relation.TransGen.head'_iff.mp (cyclic i)
    have hj : j ∈ cycleStates z n :=
      (memC j).mpr ⟨(reach i).tail ⟨b, hb⟩, Relation.TransGen.tail' hbwd ⟨b, hb⟩⟩
    exact ⟨b, ⟨j, hj⟩, hb⟩
  choose bit f hf using choose_edge
  have hexit (i : U) (j : Fin s) (hj : n i.val (!(bit i)) = some j) :
      ¬ ReachesCycle n j :=
    cycle_exit_mortal n z K hwidth (reach i) (cyclic i) (hf i) (immortal (f i)) hj
  have force (i j : U) (b : Bool) (hb : n i.val b = some j.val) : f i = j := by
    have hbit : b = bit i := by
      by_contra hn
      have hn' : b = !(bit i) := by cases hh : bit i <;> cases b <;> simp_all
      exact hexit i j.val (by simpa only [← hn'] using hb) (immortal j)
    apply Subtype.ext
    exact Option.some.inj ((hf i).symm.trans (by simpa only [hbit] using hb))
  have hsurj : Function.Surjective f := by
    intro i
    obtain ⟨j, hforw, ⟨b, hb⟩⟩ := Relation.TransGen.tail'_iff.mp (cyclic i)
    have hj : j ∈ cycleStates z n :=
      (memC j).mpr ⟨(reach i).trans hforw, Relation.TransGen.head' ⟨b, hb⟩ hforw⟩
    exact ⟨⟨j, hj⟩, force ⟨j, hj⟩ i b hb⟩
  have hper (i : U) : i ∈ Function.periodicPts f :=
    ((Finite.injective_iff_surjective).mpr hsurj).mem_periodicPts i
  let O := (Finset.univ : Finset U).image (Function.periodicOrbit f)
  let m := Fintype.card ↥O
  let cls : Fin m ≃ ↥O := (Fintype.equivFin ↥O).symm
  have repr_exists (c : Fin m) : ∃ i : U, Function.periodicOrbit f i = (cls c).val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (cls c).property
    exact ⟨i, hi⟩
  choose repr hrepr using repr_exists
  let l (c : Fin m) := Function.minimalPeriod f (repr c)
  have hl (c : Fin m) : 0 < l c := Function.minimalPeriod_pos_of_mem_periodicPts (hper (repr c))
  let part (c : Fin m) (i : Fin s) :=
    ∃ x : U, x.val = i ∧ Function.periodicOrbit f x = (cls c).val
  have hentry (c : Fin m) : ∃ i, Relation.ReflTransGen (Edge n) z i ∧ part c i :=
    ⟨(repr c).val, reach (repr c), repr c, rfl, hrepr c⟩
  have hstep (c : Fin m) (i : Fin s) (hi : part c i) :
      ∃ b j, n i b = some j ∧ part c j := by
    obtain ⟨x, rfl, hx⟩ := hi
    exact ⟨bit x, (f x).val, hf x, f x, rfl,
      (Function.periodicOrbit_apply_eq (hper x)).trans hx⟩
  have hdisj (c d : Fin m) (i : Fin s) (hc : part c i) (hd : part d i) : c = d := by
    obtain ⟨x, hx, hc'⟩ := hc
    obtain ⟨y, hy, hd'⟩ := hd
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    have hcls : Function.periodicOrbit f x = (cls d).val := by simpa only [hxy] using hd'
    exact cls.injective (Subtype.ext (hc'.symm.trans hcls))
  have hm := cycle_count_le n z hwidth part hentry hstep hdisj
  let index (p : Σ c : Fin m, Fin (l c)) : U := f^[p.2.val] (repr p.1)
  have labels (c : Fin m) (j : Fin (l c)) :
      Function.periodicOrbit f (index ⟨c, j⟩) = (cls c).val :=
    (Function.periodicOrbit_apply_iterate_eq (hper (repr c)) j.val).trans (hrepr c)
  have hinj : Function.Injective index := by
    rintro ⟨c, j⟩ ⟨d, k⟩ he
    have hc : c = d := cls.injective (Subtype.ext
      ((labels c j).symm.trans ((congrArg (Function.periodicOrbit f) he).trans (labels d k))))
    subst d
    have hj : j = k := Fin.ext
      ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := f) (x := repr c)
        j.isLt k.isLt).mp he)
    subst k
    rfl
  have hcard : (∑ c, l c) ≤ (cycleStates z n).card := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_coe, U] using
      Fintype.card_le_of_injective index hinj
  refine of_cycle_cover z n a v l law hd hdodd hcop hv hm hl hcard ?_
  intro i hi
  let x : U := ⟨i, hi⟩
  have hx : Function.periodicOrbit f x ∈ O := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  let c := cls.symm ⟨Function.periodicOrbit f x, hx⟩
  have hc : (cls c).val = Function.periodicOrbit f x := by simp [c]
  have hlen : l c = Function.minimalPeriod f x := by
    simpa only [l, Function.periodicOrbit_length] using
      congrArg Cycle.length ((hrepr c).trans hc)
  refine ⟨c, fun k => (f^[k] x).val, fun k => bit (f^[k] x), ?_, ?_, ?_⟩
  · simp [x]
  · change (f^[l c] x).val = i
    rw [hlen, Function.iterate_minimalPeriod]
  · intro k _
    change n (f^[k] x).val (bit (f^[k] x)) = some (f^[k + 1] x).val ∧
      ∀ j, n (f^[k] x).val (!(bit (f^[k] x))) = some j → ¬ ReachesCycle n j
    rw [Function.iterate_succ_apply']
    exact ⟨hf _, hexit _⟩

end NarrowDenominator

end PEqualNP.Outside.L_meta_29934_aux

open PEqualNP.Outside.L_meta_29934_aux in
theorem PEqualNP.Outside.L_meta_29934 :
∀ (h d e g p u : ℕ), 0 < d → d % 2 = 1 → 0 < g →
  let den := 2^h*d
  0 < e → e < den → Nat.Coprime e den → 0 < p → d ∣ 2^p-1 →
  (∀ a, 0 < a → a < p → ¬ d ∣ 2^a-1) →
  let q := g*den
  let E := g*e
  E ≤ 2^(p*u) →
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
    let R := fun b : ℕ => ((2^b*E % q)+E-1)/E
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
    let realize := fun (s : ℕ) =>
      ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (C : Fin s → Bool → Circ)
          (L : Fin s → Finset I → ℝ),
        law s n (fun i bit => table (C i bit)) L ∧ (∀ i bit, fits (C i bit)) ∧
        (∀ U : Finset I, U.card = t → L z U = ideal) ∧ ∀ b, live s z n b = R b
    let B := h+p*(u+1)
    let small := h+(if d=1 then 0 else p)
    (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ),
      law s n H L → (∀ i bit, loss (H i bit) ∅ ≤ E) →
      (∀ U : Finset I, U.card = t → L z U ≤ ideal) →
      (∀ b, R b ≤ live s z n b) ∧ ((∀ b, live s z n b = R b) →
        (e+1 = den → small ≤ s) ∧ ∀ K : ℕ, (∀ a : ℕ, ∃ b ≥ a, R b ≤ K) →
        ∃ (m : ℕ) (l : Fin m → ℕ), m ≤ K ∧ (∀ i, 0 < l i) ∧
          h+(∑ i, l i) ≤ s ∧ d ∣ (Finset.univ : Finset (Fin m)).lcm (fun i => 2^(l i)-1))) ∧
    realize (∑ b ∈ Finset.range (B+p), R b) ∧ (e+1 = den → realize small)
:= by
  classical
  intro h d e g p u hd ho hg den he heq hc hp hpDiv hpMin q E hEbig N t hN htq ht
    X I Circ legal table base hbase f hf loss fits ideal R run live law realize B small
  have hE : 0 < E := Nat.mul_pos hg he
  have hEq : E < q := Nat.mul_lt_mul_of_pos_left heq hg
  have hq : 0 < q := hE.trans hEq
  letI : NeZero q := ⟨hq.ne'⟩
  have hlive {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ) :
      live s z n b = liveCount z n b := by
    unfold live run liveCount path
    simp_rw [active_fold]
    rfl
  have hReal (s : ℕ) (hm : SharpMachine q E R s) : realize s := by
    obtain ⟨z,n,a,v,hstop,hw,ha,harm,hroot⟩ := hm
    obtain ⟨C,L,hL,hC,hO⟩ := realize_from_machine hq hE hEq hN ht htq base hbase hf
      (z := z) hstop a v ha harm hroot
    exact ⟨z,n,C,L,⟨hstop,fun i D => hL D i⟩,hC,hO,fun b => (hlive z n b).trans (hw b)⟩
  refine ⟨?_,hReal _ (batch_machine hd hg he heq hc hp hpDiv hEbig),fun hsmall =>
    hReal _ (skinny_machine ho he hg hsmall hc hp hpDiv)⟩
  intro s z n H L hLaw hEmpty hOpt
  have hO (D : Finset I) (hD : D.card = t) : L z D ≤ (N : ℝ)*t + (1-2*(t : ℝ)/q)*E :=
    (hOpt D hD).trans_eq (ideal_eq hq ht htq.le hN hEq)
  obtain ⟨A,hA,hpos,hcap,hroot⟩ := optimal_harm hf (table base) H L z hLaw.1
    (fun D i => hLaw.2 i D) hEmpty ht htq hO
  refine ⟨fun b => ?_,fun hequal => ?_⟩
  · rw [hlive]
    exact sharp_lower hq hE z (fun j i e => (edits (table base) (H i e) ∩ graph f j).card)
      A hA hpos hcap hroot b
  have hcycles (K : ℕ) (hK : ∀ a : ℕ, ∃ b ≥ a, R b ≤ K) :
      ∃ (m : ℕ) (l : Fin m → ℕ), m ≤ K ∧ (∀ i, 0 < l i) ∧
        h+(∑ i, l i) ≤ s ∧ d ∣ (Finset.univ : Finset (Fin m)).lcm (fun i => 2^(l i)-1) := by
    let j : Fin q := ⟨0,hq⟩
    let a (i : Fin s) (bit : Bool) : ℕ := (edits (table base) (H i bit) ∩ graph f j).card
    have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hroot' : A j z = (e : ℝ)/((2^h*d : ℕ) : ℝ) := by
      rw [hroot]
      change ((g*e : ℕ) : ℝ)/((g*(2^h*d) : ℕ) : ℝ) = _
      simp only [Nat.cast_mul]
      exact mul_div_mul_left _ _ hg'
    apply NarrowDenominator.recurrent_narrow z n (fun i bit => (a i bit : ℤ)) (A j)
      (fun i => by simpa only [Int.cast_natCast] using hA j i) hd ho hc hroot'
    intro b₀
    obtain ⟨b,hb,hKb⟩ := hK b₀
    refine ⟨b,hb,?_⟩
    exact (hequal b).le.trans hKb
  refine ⟨fun hsmall => ?_,hcycles⟩
  have hK : ∀ a : ℕ, ∃ b ≥ a, R b ≤ 1 := by
    intro a
    exact ⟨a,le_rfl,by
      change batchWidth q E a ≤ 1
      rw [show batchWidth q E a = (if den ∣ 2^a then 0 else 1) from skinny_width he hg hsmall hc a]
      split <;> omega⟩
  obtain ⟨m,l,hm,hLpos,hLsum,hdiv⟩ := hcycles 1 hK
  by_cases hd1 : d = 1
  · simpa only [small,hd1,if_true,Nat.add_zero] using (Nat.le_add_right h (∑ i, l i)).trans hLsum
  have hm1 : m = 1 := by
    by_contra hn
    have hm0 : m = 0 := by omega
    subst m
    have hdvd : d ∣ 1 := by simpa using hdiv
    exact hd1 (Nat.dvd_one.mp hdvd)
  subst m
  have hu : (Finset.univ : Finset (Fin 1)) = {0} := by ext j; simp [Fin.eq_zero j]
  have hdiv' : d ∣ 2^(l 0)-1 := by simpa [hu] using hdiv
  have hl : p ≤ l 0 := by
    by_contra! hn
    exact hpMin (l 0) (hLpos 0) hn hdiv'
  have hsum : h+l 0 ≤ s := by simpa [Fin.sum_univ_one] using hLsum
  simpa only [small,hd1,if_false] using (Nat.add_le_add_left hl h).trans hsum
