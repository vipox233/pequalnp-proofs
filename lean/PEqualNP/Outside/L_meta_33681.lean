import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33681_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def depthsStep (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_concat_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [getD_append_right l [a] l.length d (le_refl _)]
  simp

lemma wires_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl wiresStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma depths_fold_length (gs : List Gate) (ds : List ℕ) :
    (gs.foldl depthsStep ds).length = ds.length + gs.length := by
  induction gs generalizing ds with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, depthsStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_fold_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wiresStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 : i < (wiresStep x g).length := by
      simp only [wiresStep, List.length_append, List.length_singleton]
      omega
    rw [ih (wiresStep x g) h1, wiresStep, getD_append_left x _ i false hi]

lemma depths_fold_getD_prefix (gs : List Gate) (ds : List ℕ) (i : ℕ) (hi : i < ds.length) :
    (gs.foldl depthsStep ds).getD i 0 = ds.getD i 0 := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 : i < (depthsStep ds g).length := by
      simp only [depthsStep, List.length_append, List.length_singleton]
      omega
    rw [ih (depthsStep ds g) h1, depthsStep, getD_append_left ds _ i 0 hi]

lemma foldl_take_append_drop {α β : Type} (f : β → α → β) (init : β) (l : List α) (j : ℕ)
    (hj : j < l.length) :
    l.foldl f init = (l.drop (j + 1)).foldl f (f ((l.take j).foldl f init) l[j]) := by
  have hsplit : l = l.take j ++ [l[j]] ++ l.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j l]
    rw [List.append_assoc, List.cons_append, List.nil_append]
    congr 1
    exact (List.getElem_cons_drop hj).symm
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wiresStep x := rfl

lemma depths_eq_foldl (w : ℕ) (C : Circuit) :
    depths w C = C.gates.foldl depthsStep (List.replicate w 0) := rfl

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  wires_fold_getD_prefix C.gates x i hi

lemma depths_getD_input (w : ℕ) (C : Circuit) (i : ℕ) (hi : i < w) :
    (depths w C).getD i 0 = 0 := by
  rw [depths_eq_foldl, depths_fold_getD_prefix]
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [hi]

lemma wires_getD_gate (w : ℕ) (C : Circuit) (hRB : ReadsBack w C) (x : List Bool)
    (hx : x.length = w) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (w + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  set pref := (C.gates.take j).foldl wiresStep x
  have hplen : pref.length = w + j := by
    rw [wires_fold_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : C.wires x = (C.gates.drop (j + 1)).foldl wiresStep (wiresStep pref C.gates[j]) := by
    rw [wires_eq_foldl, foldl_take_append_drop wiresStep x C.gates j hj]
  have hlt : w + j < (wiresStep pref C.gates[j]).length := by
    simp only [wiresStep, List.length_append, List.length_singleton, hplen]
    omega
  have hlhs : (C.wires x).getD (w + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    rw [hfold, wires_fold_getD_prefix _ _ _ hlt, wiresStep, ← hplen, getD_concat_last]
  rw [hlhs, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < w + j := by
    have h1 := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at h1
    exact h1 hi
  have hlt2 : i < (wiresStep pref C.gates[j]).length := by
    simp only [wiresStep, List.length_append, List.length_singleton, hplen]
    omega
  rw [hfold, wires_fold_getD_prefix _ _ _ hlt2, wiresStep, getD_append_left pref _ i false (by omega)]

lemma depths_getD_gate (w : ℕ) (C : Circuit) (hRB : ReadsBack w C) (j : ℕ) (hj : j < C.gates.length) :
    (depths w C).getD (w + j) 0 =
      ((gateAt C j).inputs.map fun i => (depths w C).getD i 0).foldr max 0 +
        (nonlinear (gateAt C j)).toNat := by
  set pref := (C.gates.take j).foldl depthsStep (List.replicate w 0)
  have hplen : pref.length = w + j := by
    rw [depths_fold_length, List.length_replicate, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : depths w C = (C.gates.drop (j + 1)).foldl depthsStep (depthsStep pref C.gates[j]) := by
    rw [depths_eq_foldl, foldl_take_append_drop depthsStep (List.replicate w 0) C.gates j hj]
  have hlt : w + j < (depthsStep pref C.gates[j]).length := by
    simp only [depthsStep, List.length_append, List.length_singleton, hplen]
    omega
  have hlhs : (depths w C).getD (w + j) 0 =
      (C.gates[j].inputs.map fun i => pref.getD i 0).foldr max 0 + (nonlinear C.gates[j]).toNat := by
    rw [hfold, depths_fold_getD_prefix _ _ _ hlt, depthsStep, ← hplen, getD_concat_last]
  rw [hlhs, gateAt_eq_getElem C j hj]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < w + j := by
    have h1 := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at h1
    exact h1 hi
  have hlt2 : i < (depthsStep pref C.gates[j]).length := by
    simp only [depthsStep, List.length_append, List.length_singleton, hplen]
    omega
  rw [hfold, depths_fold_getD_prefix _ _ _ hlt2, depthsStep, getD_append_left pref _ i 0 (by omega)]

lemma foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

lemma getD_le_foldr_max (l : List ℕ) (w : ℕ) : l.getD w 0 ≤ l.foldr max 0 := by
  by_cases hlt : w < l.length
  · have hmem : l.getD w 0 ∈ l := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem hlt
    exact (foldr_max_le_iff l _).mp (le_refl _) _ hmem
  · have hnone : l[w]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    exact Nat.zero_le _

lemma oneEach_length {N : ℕ} (x y : Fin N) :
    (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_left {N : ℕ} (x y : Fin N) (i : ℕ) (hi : i < N) :
    (oneEach x y).getD i false = decide (⟨i, hi⟩ = x) := by
  simp only [oneEach]
  rw [getD_append_left _ _ i false (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma oneEach_getD_right {N : ℕ} (x y : Fin N) (j : ℕ) (hj : j < N) :
    (oneEach x y).getD (N + j) false = decide (⟨j, hj⟩ = y) := by
  simp only [oneEach]
  rw [getD_append_right _ _ (N + j) false (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma f2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma f2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma f2_mul_self (a : ZMod 2) : a * a = a := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma gate_eval_linear (g : Gate) (hFan : g.inputs.length ≤ 2) (hLin : nonlinear g = false) :
    (g.inputs = [] ∧ ∃ c : ZMod 2, b2f (g.op.eval []) = c) ∨
    (∃ a, g.inputs = [a] ∧ ∃ c0 c1 : ZMod 2, ∀ u : Bool,
      b2f (g.op.eval [u]) = c0 + c1 * b2f u) ∨
    (∃ a b, g.inputs = [a, b] ∧ ∃ c0 c1 c2 : ZMod 2, ∀ u v : Bool,
      b2f (g.op.eval [u, v]) = c0 + c1 * b2f u + c2 * b2f v) := by
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · left
    exact ⟨rfl, b2f (g.op.eval []), rfl⟩
  · right; left
    refine ⟨a, rfl, b2f (g.op.eval [false]), b2f (g.op.eval [true]) + b2f (g.op.eval [false]), ?_⟩
    intro u
    cases u <;> cases h0 : g.op.eval [false] <;> cases h1 : g.op.eval [true] <;> decide
  · right; right
    refine ⟨a, b, rfl, b2f (g.op.eval [false, false]),
      b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false]), ?_⟩
    have hnl : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
      simp only [nonlinear, h, List.length_cons, List.length_nil, beq_self_eq_true,
        Bool.true_and] at hLin
      exact hLin
    intro u v
    cases h00 : g.op.eval [false, false] <;> cases h01 : g.op.eval [false, true] <;>
      cases h10 : g.op.eval [true, false] <;> cases h11 : g.op.eval [true, true] <;>
      simp only [h00, h01, h10, h11] at hnl <;>
      try (cases hnl) <;>
      cases u <;> cases v <;> simp only [h00, h01, h10, h11] <;> decide
  · simp [h] at hFan

lemma gate_eval_nonlinear (g : Gate) (hNL : nonlinear g = true) :
    ∃ a b, g.inputs = [a, b] ∧ ∃ α β γ : ZMod 2, ∀ u v : Bool,
      b2f (g.op.eval [u, v]) = (b2f u + β) * (b2f v + α) + γ := by
  have hlen : g.inputs.length = 2 := by
    simp only [nonlinear, Bool.and_eq_true, beq_iff_eq] at hNL
    exact hNL.1
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · have hnl : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      simp only [nonlinear, h, List.length_cons, List.length_nil, beq_self_eq_true,
        Bool.true_and] at hNL
      exact hNL
    refine ⟨a, b, rfl,
      b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, false]) +
        (b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false])) *
        (b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false])), ?_⟩
    intro u v
    cases h00 : g.op.eval [false, false] <;> cases h01 : g.op.eval [false, true] <;>
      cases h10 : g.op.eval [true, false] <;> cases h11 : g.op.eval [true, true] <;>
      simp only [h00, h01, h10, h11] at hnl <;>
      try (cases hnl) <;>
      cases u <;> cases v <;> simp only [h00, h01, h10, h11] <;> decide
  · simp [h] at hlen

def HasRankLe {N : ℕ} (M : Fin N → Fin N → ZMod 2) (r : ℕ) : Prop :=
  ∃ (u v : Fin r → Fin N → ZMod 2), ∀ x y, M x y = ∑ i : Fin r, u i x * v i y

lemma hasRankLe_one {N : ℕ} (a b : Fin N → ZMod 2) :
    HasRankLe (fun x y => a x * b y) 1 :=
  ⟨fun _ => a, fun _ => b, fun x y => by simp⟩

lemma hasRankLe_add {N r1 r2 : ℕ} {M1 M2 : Fin N → Fin N → ZMod 2}
    (h1 : HasRankLe M1 r1) (h2 : HasRankLe M2 r2) :
    HasRankLe (fun x y => M1 x y + M2 x y) (r1 + r2) := by
  rcases h1 with ⟨u1, v1, hM1⟩
  rcases h2 with ⟨u2, v2, hM2⟩
  refine ⟨Fin.append u1 u2, Fin.append v1 v2, fun x y => ?_⟩
  dsimp only
  rw [Fin.sum_univ_add, hM1 x y, hM2 x y]
  simp [Fin.append_left, Fin.append_right]

lemma hasRankLe_sum {N : ℕ} {ι : Type} (S : Finset ι) (f g : ι → Fin N → ZMod 2) :
    HasRankLe (fun x y => ∑ i ∈ S, f i x * g i y) S.card := by
  classical
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  refine ⟨fun i => f (e i).val, fun i => g (e i).val, fun x y => ?_⟩
  dsimp only
  rw [← Finset.sum_attach S]
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma hasRankLe_sum_univ {N : ℕ} {ι : Type} [Fintype ι] (f g : ι → Fin N → ZMod 2) :
    HasRankLe (fun x y => ∑ i : ι, f i x * g i y) (Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨fun i => f (e i), fun i => g (e i), fun x y => ?_⟩
  dsimp only
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma hasRankLe_id_le {N r : ℕ}
    (h : HasRankLe (fun x y : Fin N => if x = y then (1 : ZMod 2) else 0) r) :
    N ≤ r := by
  rcases h with ⟨u, v, hM⟩
  let L : (Fin N → ZMod 2) → (Fin r → ZMod 2) := fun z i => ∑ y : Fin N, v i y * z y
  have hLinj : Function.Injective L := by
    intro z1 z2 hz
    funext x
    have h1 : ∀ z : Fin N → ZMod 2, z x = ∑ i : Fin r, u i x * L z i := by
      intro z
      calc z x = ∑ y : Fin N, (if x = y then (1 : ZMod 2) else 0) * z y := by simp
        _ = ∑ y : Fin N, (∑ i : Fin r, u i x * v i y) * z y := by
            refine Finset.sum_congr rfl fun y _ => ?_
            have hxy : (if x = y then (1 : ZMod 2) else 0) = ∑ i : Fin r, u i x * v i y := hM x y
            rw [hxy]
        _ = ∑ y : Fin N, ∑ i : Fin r, u i x * (v i y * z y) := by
            refine Finset.sum_congr rfl fun y _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i : Fin r, ∑ y : Fin N, u i x * (v i y * z y) := Finset.sum_comm
        _ = ∑ i : Fin r, u i x * L z i := by
            refine Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]
    rw [h1 z1, h1 z2, hz]
  have hcard := Fintype.card_le_of_injective L hLinj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

lemma symplectic_clique_free {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq P]
    (μ ν : Q → P → ZMod 2) (S : Finset P)
    (hClique : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' →
      ∑ q : Q, (μ q p * ν q p' + ν q p * μ q p') = 1) :
    S.card ≤ 2 * Fintype.card Q + 1 := by
  classical
  by_contra hgt
  have hge : 2 * Fintype.card Q + 2 ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hge
  let W : P → P → ZMod 2 := fun p p' => ∑ q : Q, (μ q p * ν q p' + ν q p * μ q p')
  have hWdiag : ∀ p : P, W p p = 0 := by
    intro p
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [mul_comm (ν q p)]
    exact f2_add_self _
  let L : (T → ZMod 2) → (Q × Bool → ZMod 2) := fun z qb =>
    if qb.2 then ∑ p : T, ν qb.1 p.val * z p else ∑ p : T, μ qb.1 p.val * z p
  have hLinj : Function.Injective L := by
    intro z1 z2 hz
    set z : T → ZMod 2 := fun p => z1 p + z2 p
    have hdiff : ∀ qb, L z qb = 0 := by
      intro qb
      have h1 : L z1 qb = L z2 qb := congrFun hz qb
      cases hqb : qb.2
      · simp only [L, hqb, Bool.false_eq_true, ↓reduceIte, z] at h1 ⊢
        calc ∑ p : T, μ qb.1 p.val * (z1 p + z2 p)
            = ∑ p : T, (μ qb.1 p.val * z1 p + μ qb.1 p.val * z2 p) :=
                Finset.sum_congr rfl fun p _ => mul_add _ _ _
          _ = (∑ p : T, μ qb.1 p.val * z1 p) + (∑ p : T, μ qb.1 p.val * z2 p) :=
                Finset.sum_add_distrib
          _ = (∑ p : T, μ qb.1 p.val * z2 p) + (∑ p : T, μ qb.1 p.val * z2 p) := by rw [h1]
          _ = 0 := f2_add_self _
      · simp only [L, hqb, ↓reduceIte, z] at h1 ⊢
        calc ∑ p : T, ν qb.1 p.val * (z1 p + z2 p)
            = ∑ p : T, (ν qb.1 p.val * z1 p + ν qb.1 p.val * z2 p) :=
                Finset.sum_congr rfl fun p _ => mul_add _ _ _
          _ = (∑ p : T, ν qb.1 p.val * z1 p) + (∑ p : T, ν qb.1 p.val * z2 p) :=
                Finset.sum_add_distrib
          _ = (∑ p : T, ν qb.1 p.val * z2 p) + (∑ p : T, ν qb.1 p.val * z2 p) := by rw [h1]
          _ = 0 := f2_add_self _
    have hWz : ∀ p : T, ∑ p' : T, W p.val p'.val * z p' = 0 := by
      intro p
      calc ∑ p' : T, W p.val p'.val * z p'
          = ∑ p' : T, ∑ q : Q, (μ q p.val * (ν q p'.val * z p') + ν q p.val * (μ q p'.val * z p')) := by
              refine Finset.sum_congr rfl fun p' _ => ?_
              simp only [W, Finset.sum_mul]
              exact Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ q : Q, ∑ p' : T, (μ q p.val * (ν q p'.val * z p') + ν q p.val * (μ q p'.val * z p')) :=
              Finset.sum_comm
        _ = ∑ q : Q, (μ q p.val * L z (q, true) + ν q p.val * L z (q, false)) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              rfl
        _ = 0 := Finset.sum_eq_zero fun q _ => by rw [hdiff (q, true), hdiff (q, false)]; ring
    have hWz2 : ∀ p : T, (∑ p' : T, z p') + z p = 0 := by
      intro p
      have h0 := hWz p
      have hrew : ∑ p' : T, W p.val p'.val * z p' = ∑ p' : T, (z p' + (if p' = p then z p' else 0)) := by
        refine Finset.sum_congr rfl fun p' _ => ?_
        by_cases hpp : p' = p
        · subst hpp
          simp only [hWdiag, zero_mul, ↓reduceIte, f2_add_self]
        · have hne : p.val ≠ p'.val := fun heq => hpp (Subtype.ext heq.symm)
          have hW1 : W p.val p'.val = 1 := hClique p.val (hTS p.property) p'.val (hTS p'.property) hne
          simp only [hW1, one_mul, hpp, ↓reduceIte, add_zero]
      rw [hrew, Finset.sum_add_distrib] at h0
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
      exact h0
    have hsum0 : ∑ p' : T, z p' = 0 := by
      have htot : ∑ p : T, ((∑ p' : T, z p') + z p) = 0 :=
        Finset.sum_eq_zero fun p _ => hWz2 p
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hTcard] at htot
      have heven : ((2 * Fintype.card Q + 2 : ℕ) : ZMod 2) = 0 := by
        have h2 : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [h2]
        ring
      rw [nsmul_eq_mul, heven, zero_mul, zero_add] at htot
      exact htot
    funext p
    have hp := hWz2 p
    rw [hsum0, zero_add] at hp
    have hzz : z p + z2 p = z2 p := by rw [hp, zero_add]
    simp only [z, add_assoc, f2_add_self, add_zero] at hzz
    exact hzz
  have hcard := Fintype.card_le_of_injective L hLinj
  have hLcard : Fintype.card (T → ZMod 2) = 2 ^ (2 * Fintype.card Q + 2) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe, hTcard]
  have hRcard : Fintype.card (Q × Bool → ZMod 2) = 2 ^ (2 * Fintype.card Q) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_bool, mul_comm]
  rw [hLcard, hRcard] at hcard
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  omega

lemma filter_card_add_not {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hu : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hp : p x <;> simp [hp]
  have hd : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  rw [← Finset.card_union_of_disjoint hd, hu]

lemma turan_ordered_edges {α : Type} [DecidableEq α] (adj : α → α → Prop) [DecidableRel adj]
    (hSymm : ∀ a b, adj a b → adj b a) (hIrrefl : ∀ a, ¬ adj a a)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (V : Finset α),
      (∀ S ⊆ V, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → adj a b) → S.card ≤ m) →
      m * ((V ×ˢ V).filter (fun p => adj p.1 p.2)).card ≤ (m - 1) * V.card ^ 2 := by
  induction m with
  | zero => omega
  | succ m' ih =>
    intro V hFree
    by_cases hm' : m' = 0
    · subst hm'
      have hemp : (V ×ˢ V).filter (fun p => adj p.1 p.2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hadj
        have h1 : p.1 ∈ V := (Finset.mem_product.mp hp).1
        have h2 : p.2 ∈ V := (Finset.mem_product.mp hp).2
        have hne : p.1 ≠ p.2 := fun heq => hIrrefl p.1 (heq ▸ hadj)
        have hsub : ({p.1, p.2} : Finset α) ⊆ V := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hcl : ∀ a ∈ ({p.1, p.2} : Finset α), ∀ b ∈ ({p.1, p.2} : Finset α), a ≠ b → adj a b := by
          intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · exact hadj
          · exact hSymm _ _ hadj
          · exact absurd rfl hab
        have hc := hFree {p.1, p.2} hsub hcl
        rw [Finset.card_pair hne] at hc
        omega
      rw [hemp, Finset.card_empty]
      simp
    · have hm'_pos : 1 ≤ m' := by omega
      by_cases hV : V.Nonempty
      · let deg : α → ℕ := fun v => (V.filter (fun u => adj v u)).card
        obtain ⟨v0, hv0V, hv0max⟩ := Finset.exists_max_image V deg hV
        let A := V.filter (fun u => adj v0 u)
        let B := V.filter (fun u => ¬ adj v0 u)
        have hAsub : A ⊆ V := Finset.filter_subset _ _
        have hBsub : B ⊆ V := Finset.filter_subset _ _
        have hABcard : A.card + B.card = V.card := filter_card_add_not V (fun u => adj v0 u)
        have hAFree : ∀ S ⊆ A, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → adj a b) → S.card ≤ m' := by
          intro S hSA hScl
          have hv0notS : v0 ∉ S := fun hv0S => hIrrefl v0 (Finset.mem_filter.mp (hSA hv0S)).2
          have hins_sub : insert v0 S ⊆ V := Finset.insert_subset_iff.mpr ⟨hv0V, Finset.Subset.trans hSA hAsub⟩
          have hins_cl : ∀ a ∈ insert v0 S, ∀ b ∈ insert v0 S, a ≠ b → adj a b := by
            intro a ha b hb hab
            rcases Finset.mem_insert.mp ha with rfl | haS <;>
              rcases Finset.mem_insert.mp hb with rfl | hbS
            · exact absurd rfl hab
            · exact (Finset.mem_filter.mp (hSA hbS)).2
            · exact hSymm _ _ (Finset.mem_filter.mp (hSA haS)).2
            · exact hScl a haS b hbS hab
          have hc := hFree (insert v0 S) hins_sub hins_cl
          rw [Finset.card_insert_of_notMem hv0notS] at hc
          omega
        have hIH := ih hm'_pos A hAFree
        set E := ((V ×ˢ V).filter (fun p => adj p.1 p.2)).card
        set EA := ((A ×ˢ A).filter (fun p => adj p.1 p.2)).card
        have hE_eq : E = ∑ u ∈ V, deg u := by
          simp only [E, deg]
          rw [Finset.card_filter, Finset.sum_product]
          exact Finset.sum_congr rfl fun u _ => (Finset.card_filter _ _).symm
        have hEA_eq : EA = ∑ u ∈ A, (A.filter (fun w => adj u w)).card := by
          simp only [EA]
          rw [Finset.card_filter, Finset.sum_product]
          exact Finset.sum_congr rfl fun u _ => (Finset.card_filter _ _).symm
        have hCross : (∑ u ∈ A, (B.filter (fun w => adj u w)).card) =
            (∑ w ∈ B, (A.filter (fun u => adj w u)).card) := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
          by_cases h : adj u w
          · have h' := hSymm u w h
            simp only [h, h', ↓reduceIte]
          · have h' : ¬ adj w u := fun h2 => h (hSymm w u h2)
            simp only [h, h', ↓reduceIte]
        have hVsplit : ∀ f : α → ℕ, ∑ u ∈ V, f u = ∑ u ∈ A, f u + ∑ u ∈ B, f u := fun f =>
          (Finset.sum_filter_add_sum_filter_not V (fun u => adj v0 u) f).symm
        have hdeg_split : ∀ u : α, deg u = (A.filter (fun w => adj u w)).card + (B.filter (fun w => adj u w)).card := by
          intro u
          simp only [deg, A, B, Finset.card_filter]
          rw [← Finset.sum_filter_add_sum_filter_not V (fun w => adj v0 w) (fun w => if adj u w then 1 else 0)]
        have hE_le : E ≤ EA + 2 * (B.card * A.card) := by
          have h1 : E = EA + (∑ u ∈ A, (B.filter (fun w => adj u w)).card) + ∑ u ∈ B, deg u := by
            rw [hE_eq, hVsplit deg]
            have hA : ∑ u ∈ A, deg u = EA + ∑ u ∈ A, (B.filter (fun w => adj u w)).card := by
              rw [hEA_eq, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun u _ => hdeg_split u
            omega
          have h2 : ∑ u ∈ B, deg u ≤ B.card * A.card := by
            calc ∑ u ∈ B, deg u ≤ ∑ _u ∈ B, deg v0 := Finset.sum_le_sum fun u hu => hv0max u (hBsub hu)
              _ = B.card * A.card := by simp [deg, A]
          have h3 : ∑ w ∈ B, (A.filter (fun u => adj w u)).card ≤ B.card * A.card := by
            calc ∑ w ∈ B, (A.filter (fun u => adj w u)).card ≤ ∑ w ∈ B, deg w := by
                  refine Finset.sum_le_sum fun w _ => Finset.card_le_card ?_
                  intro u hu
                  exact Finset.mem_filter.mpr ⟨hAsub (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
              _ ≤ B.card * A.card := h2
          rw [h1, hCross]
          omega
        have hZ : ((m' + 1) * E : ℤ) ≤ (m' * V.card ^ 2 : ℤ) := by
          have hIHZ : (m' : ℤ) * (EA : ℤ) ≤ ((m' : ℤ) - 1) * (A.card : ℤ) ^ 2 := by
            have := Nat.cast_le (α := ℤ).mpr hIH
            push_cast [Nat.cast_sub hm'_pos] at this
            exact this
          have hEZ : (E : ℤ) ≤ (EA : ℤ) + 2 * ((B.card : ℤ) * (A.card : ℤ)) := by exact_mod_cast hE_le
          have hABZ : (A.card : ℤ) + (B.card : ℤ) = (V.card : ℤ) := by exact_mod_cast hABcard
          have hm'Z : (1 : ℤ) ≤ (m' : ℤ) := by exact_mod_cast hm'_pos
          have hmE : (m' : ℤ) * (E : ℤ) ≤ (m' : ℤ) * (EA : ℤ) + 2 * (m' : ℤ) * ((B.card : ℤ) * (A.card : ℤ)) := by
            nlinarith only [hEZ, hm'Z]
          have h1 : (m' : ℤ) * ((m' : ℤ) + 1) * (E : ℤ) ≤
              ((m' : ℤ) + 1) * (((m' : ℤ) - 1) * (A.card : ℤ) ^ 2 + 2 * (m' : ℤ) * ((B.card : ℤ) * (A.card : ℤ))) := by
            nlinarith only [hIHZ, hmE, hm'Z]
          have hid : ((m' : ℤ) + 1) * (((m' : ℤ) - 1) * (A.card : ℤ) ^ 2 + 2 * (m' : ℤ) * ((B.card : ℤ) * (A.card : ℤ))) =
              (m' : ℤ) ^ 2 * (V.card : ℤ) ^ 2 - ((m' : ℤ) * (V.card : ℤ) - ((m' : ℤ) + 1) * (A.card : ℤ)) ^ 2 := by
            rw [← hABZ]; ring
          have hsq : (0 : ℤ) ≤ ((m' : ℤ) * (V.card : ℤ) - ((m' : ℤ) + 1) * (A.card : ℤ)) ^ 2 := sq_nonneg _
          have hstep : (m' : ℤ) * (((m' : ℤ) + 1) * (E : ℤ)) ≤ (m' : ℤ) * ((m' : ℤ) * (V.card : ℤ) ^ 2) := by
            linarith only [h1, hid, hsq]
          nlinarith only [hstep, hm'Z]
        have hN : (m' + 1) * E ≤ m' * V.card ^ 2 := by exact_mod_cast hZ
        simpa [Nat.add_sub_cancel] using hN
      · rw [Finset.not_nonempty_iff_eq_empty] at hV
        subst hV
        simp

lemma two_phase_rank_cap (N : ℕ) {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq P]
    (pVal : P → ℕ) (hpInj : Function.Injective pVal)
    (pa pa' pb pb' : P → Fin N → ZMod 2)
    (Aout Bout : Fin N → ZMod 2) (cout : P → ZMod 2) (lam : Q → ZMod 2)
    (Uq Uq' Vq Vq' : Q → Fin N → ZMod 2) (μq νq : Q → P → ZMod 2) (γq : Q → ZMod 2)
    (hId : ∀ x y : Fin N, (if x = y then (1 : ZMod 2) else 0) =
      Aout x + Bout y +
      (∑ p : P, cout p * (pa p x * pb' p y + pa' p x * pb p y)) +
      ∑ q : Q, lam q *
        ((Uq q x + Vq q y + ∑ p : P, μq q p * (pa p x * pb' p y + pa' p x * pb p y)) *
         (Uq' q x + Vq' q y + ∑ p : P, νq q p * (pa p x * pb' p y + pa' p x * pb p y)) + γq q)) :
    ∃ E : ℕ, N ≤ 2 + 2 * Fintype.card Q + 4 * Fintype.card P + 4 * E ∧
      (2 * Fintype.card Q + 1) * (2 * E) ≤ 2 * Fintype.card Q * Fintype.card P ^ 2 := by
  classical
  let h : P → Fin N → Fin N → ZMod 2 := fun p x y => pa p x * pb' p y + pa' p x * pb p y
  let μ' : Q → P → ZMod 2 := fun q p => lam q * μq q p
  let ν' : Q → P → ZMod 2 := fun q p => lam q * νq q p
  let W : P → P → ZMod 2 := fun p p' => ∑ q : Q, (μ' q p * ν' q p' + ν' q p * μ' q p')
  let adj : P → P → Prop := fun p p' => W p p' = 1
  have hWsymm : ∀ p p', W p p' = W p' p := fun p p' =>
    Finset.sum_congr rfl fun q _ => by ring
  have hWirrefl : ∀ p, ¬ adj p p := by
    intro p hadj
    dsimp only [adj] at hadj
    have h0 : W p p = 0 := Finset.sum_eq_zero fun q _ => by
      rw [mul_comm (ν' q p)]; exact f2_add_self _
    rw [h0] at hadj
    exact absurd hadj (by decide)
  have hTuran := turan_ordered_edges adj (fun a b h1 => by dsimp only [adj] at h1 ⊢; rw [← hWsymm]; exact h1) hWirrefl
    (2 * Fintype.card Q + 1) (by omega) Finset.univ (fun S _ hcl => symplectic_clique_free μ' ν' S hcl)
  let U : Finset (P × P) := (Finset.univ : Finset P) ×ˢ (Finset.univ : Finset P)
  let Eset : Finset (P × P) := U.filter (fun pp => pVal pp.1 < pVal pp.2 ∧ W pp.1 pp.2 = 1)
  have hEord : 2 * Eset.card = (U.filter (fun pp => adj pp.1 pp.2)).card := by
    let Egt : Finset (P × P) := U.filter (fun pp => pVal pp.2 < pVal pp.1 ∧ W pp.1 pp.2 = 1)
    have hcard_eq : Egt.card = Eset.card := by
      refine Finset.card_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_
      · intro pp hpp
        have h1 := (Finset.mem_filter.mp hpp).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          h1.1, by rw [hWsymm]; exact h1.2⟩
      · intro pp1 _ pp2 _ heq; ext <;> simp_all
      · intro pp hpp
        have h1 := (Finset.mem_filter.mp hpp).2
        refine ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          h1.1, by rw [hWsymm]; exact h1.2⟩, by ext <;> rfl⟩
    have hunion : U.filter (fun pp => adj pp.1 pp.2) = Eset ∪ Egt := by
      ext pp
      simp only [U, Eset, Egt, adj, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and]
      constructor
      · intro hadj
        have hne : pVal pp.1 ≠ pVal pp.2 := fun heq => hWirrefl pp.1 ((hpInj heq) ▸ hadj)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨hlt, hadj⟩
        · exact Or.inr ⟨hgt, hadj⟩
      · rintro (⟨_, h1⟩ | ⟨_, h1⟩) <;> exact h1
    have hdisj : Disjoint Eset Egt := by
      rw [Finset.disjoint_left]
      intro pp h1 h2
      have := (Finset.mem_filter.mp h1).2.1
      have := (Finset.mem_filter.mp h2).2.1
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj, hcard_eq]
    omega
  have hTuran2 : (2 * Fintype.card Q + 1) * (2 * Eset.card) ≤ 2 * Fintype.card Q * Fintype.card P ^ 2 := by
    rw [hEord]
    simpa [U, Finset.card_univ] using hTuran
  let M0 : Fin N → Fin N → ZMod 2 := fun x y =>
    (Aout x + ∑ q : Q, lam q * (Uq q x * Uq' q x + γq q)) * 1 +
    1 * (Bout y + ∑ q : Q, lam q * (Vq q y * Vq' q y))
  let M1 : Fin N → Fin N → ZMod 2 := fun x y =>
    (∑ q : Q, (lam q * Uq q x) * Vq' q y) + (∑ q : Q, (lam q * Uq' q x) * Vq q y)
  let Xp : P → Fin N → ZMod 2 := fun p x =>
    cout p + ∑ q : Q, lam q * (μq q p * νq q p + Uq q x * νq q p + Uq' q x * μq q p)
  let Yp : P → Fin N → ZMod 2 := fun p y =>
    ∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)
  let M2 : Fin N → Fin N → ZMod 2 := fun x y =>
    ((∑ p : P, (Xp p x * pa p x) * pb' p y) + (∑ p : P, (Xp p x * pa' p x) * pb p y)) +
    ((∑ p : P, pa p x * (Yp p y * pb' p y)) + (∑ p : P, pa' p x * (Yp p y * pb p y)))
  let M3 : Fin N → Fin N → ZMod 2 := fun x y =>
    ((∑ pp ∈ Eset, (pa pp.1 x * pa pp.2 x) * (pb' pp.1 y * pb' pp.2 y)) +
     (∑ pp ∈ Eset, (pa pp.1 x * pa' pp.2 x) * (pb' pp.1 y * pb pp.2 y))) +
    ((∑ pp ∈ Eset, (pa' pp.1 x * pa pp.2 x) * (pb pp.1 y * pb' pp.2 y)) +
     (∑ pp ∈ Eset, (pa' pp.1 x * pa' pp.2 x) * (pb pp.1 y * pb pp.2 y)))
  have hMsum : ∀ x y, (if x = y then (1 : ZMod 2) else 0) = ((M0 x y + M1 x y) + M2 x y) + M3 x y := by
    intro x y
    rw [hId x y]
    have hQuad : ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) =
        (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) + M3 x y := by
      have h1 : ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) =
          ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) := by
        calc ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y))
            = ∑ q : Q, ∑ p : P, ∑ p' : P, lam q * (μq q p * νq q p') * (h p x y * h p' x y) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun p' _ => by ring
          _ = ∑ p : P, ∑ q : Q, ∑ p' : P, lam q * (μq q p * νq q p') * (h p x y * h p' x y) :=
                Finset.sum_comm
          _ = ∑ p : P, ∑ p' : P, ∑ q : Q, lam q * (μq q p * νq q p') * (h p x y * h p' x y) :=
                Finset.sum_congr rfl fun p _ => Finset.sum_comm
          _ = ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) :=
                Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ =>
                  (Finset.sum_mul _ _ _).symm
      rw [h1]
      let D : Finset (P × P) := U.filter (fun pp => pp.1 = pp.2)
      let LT : Finset (P × P) := U.filter (fun pp => pVal pp.1 < pVal pp.2)
      let GT : Finset (P × P) := U.filter (fun pp => pVal pp.2 < pVal pp.1)
      have hpart : U = D ∪ (LT ∪ GT) := by
        ext pp
        simp only [U, D, LT, GT, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_univ, true_and]
        constructor
        · intro _
          rcases lt_trichotomy (pVal pp.1) (pVal pp.2) with hlt | heq | hgt
          · exact Or.inr (Or.inl hlt)
          · exact Or.inl (hpInj heq)
          · exact Or.inr (Or.inr hgt)
        · intro _; trivial
      have hd1 : Disjoint D (LT ∪ GT) := by
        rw [Finset.disjoint_left]
        intro pp hD hLG
        have heq := (Finset.mem_filter.mp hD).2
        rcases Finset.mem_union.mp hLG with hL | hG
        · have := (Finset.mem_filter.mp hL).2; rw [heq] at this; omega
        · have := (Finset.mem_filter.mp hG).2; rw [heq] at this; omega
      have hd2 : Disjoint LT GT := by
        rw [Finset.disjoint_left]
        intro pp hL hG
        have := (Finset.mem_filter.mp hL).2
        have := (Finset.mem_filter.mp hG).2
        omega
      have hsplit : ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) =
          (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) +
          ∑ pp ∈ LT, W pp.1 pp.2 * (h pp.1 x y * h pp.2 x y) := by
        have hprod : ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) =
            ∑ pp ∈ U, (∑ q : Q, lam q * (μq q pp.1 * νq q pp.2)) * (h pp.1 x y * h pp.2 x y) :=
          (Finset.sum_product' _ _ _).symm
        rw [hprod, hpart, Finset.sum_union hd1, Finset.sum_union hd2]
        congr 1
        · refine Finset.sum_bij (fun pp _ => pp.1) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro pp1 h1 pp2 h2 heq
            have e1 := (Finset.mem_filter.mp h1).2
            have e2 := (Finset.mem_filter.mp h2).2
            exact Prod.ext heq (by rw [← e1, ← e2, heq])
          · intro p _
            exact ⟨(p, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, rfl⟩
          · intro pp hpp
            have heq := (Finset.mem_filter.mp hpp).2
            rw [← heq, f2_mul_self]
        · have hGT : ∑ pp ∈ GT, (∑ q : Q, lam q * (μq q pp.1 * νq q pp.2)) * (h pp.1 x y * h pp.2 x y) =
              ∑ pp ∈ LT, (∑ q : Q, lam q * (μq q pp.2 * νq q pp.1)) * (h pp.1 x y * h pp.2 x y) := by
            refine Finset.sum_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_ ?_
            · intro pp hpp
              exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
                (Finset.mem_filter.mp hpp).2⟩
            · intro pp1 _ pp2 _ heq; ext <;> simp_all
            · intro pp hpp
              exact ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
                (Finset.mem_filter.mp hpp).2⟩, by ext <;> rfl⟩
            · intro pp _
              simp only [mul_comm (h pp.1 x y)]
          rw [hGT, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun pp _ => ?_
          rw [← add_mul]
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [μ', ν']
          have hlam2 : lam q * lam q = lam q := f2_mul_self (lam q)
          calc lam q * (μq q pp.1 * νq q pp.2) + lam q * (μq q pp.2 * νq q pp.1)
              = (lam q * lam q) * (μq q pp.1 * νq q pp.2) + (lam q * lam q) * (νq q pp.1 * μq q pp.2) := by
                  rw [hlam2]; ring
            _ = lam q * μq q pp.1 * (lam q * νq q pp.2) + lam q * νq q pp.1 * (lam q * μq q pp.2) := by ring
      rw [hsplit]
      congr 1
      have hfilt : ∑ pp ∈ LT, W pp.1 pp.2 * (h pp.1 x y * h pp.2 x y) = ∑ pp ∈ Eset, h pp.1 x y * h pp.2 x y := by
        have hsub : Eset = LT.filter (fun pp => W pp.1 pp.2 = 1) := by
          ext pp; simp [Eset, LT, and_assoc]
        symm
        rw [hsub, Finset.sum_filter]
        refine Finset.sum_congr rfl fun pp _ => ?_
        rcases f2_cases (W pp.1 pp.2) with h0 | h1
        · simp only [h0, zero_mul, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
        · simp only [h1, one_mul, ↓reduceIte]
      rw [hfilt]
      simp only [M3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pp _ => ?_
      simp only [h]
      ring
    have hExpQ : ∑ q : Q, lam q * ((Uq q x + Vq q y + ∑ p : P, μq q p * h p x y) *
          (Uq' q x + Vq' q y + ∑ p : P, νq q p * h p x y) + γq q) =
        (∑ q : Q, lam q * (Uq q x * Uq' q x + γq q)) +
        (∑ q : Q, lam q * (Vq q y * Vq' q y)) +
        M1 x y +
        (∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y) +
        ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) := by
      have hlinX : ∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y =
          ∑ q : Q, lam q * (Uq q x * (∑ p : P, νq q p * h p x y) + Uq' q x * (∑ p : P, μq q p * h p x y)) := by
        calc ∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y
            = ∑ p : P, ∑ q : Q, lam q * (Uq q x * (νq q p * h p x y) + Uq' q x * (μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun q _ => by ring
          _ = ∑ q : Q, ∑ p : P, lam q * (Uq q x * (νq q p * h p x y) + Uq' q x * (μq q p * h p x y)) :=
                Finset.sum_comm
          _ = ∑ q : Q, lam q * (Uq q x * (∑ p : P, νq q p * h p x y) + Uq' q x * (∑ p : P, μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hlinY : ∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y =
          ∑ q : Q, lam q * (Vq q y * (∑ p : P, νq q p * h p x y) + Vq' q y * (∑ p : P, μq q p * h p x y)) := by
        calc ∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y
            = ∑ p : P, ∑ q : Q, lam q * (Vq q y * (νq q p * h p x y) + Vq' q y * (μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun q _ => by ring
          _ = ∑ q : Q, ∑ p : P, lam q * (Vq q y * (νq q p * h p x y) + Vq' q y * (μq q p * h p x y)) :=
                Finset.sum_comm
          _ = ∑ q : Q, lam q * (Vq q y * (∑ p : P, νq q p * h p x y) + Vq' q y * (∑ p : P, μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hlinX, hlinY]
      simp only [M1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    change _ = _
    rw [hExpQ, hQuad]
    have hM2eq : M2 x y = (∑ p : P, Xp p x * h p x y) + (∑ p : P, Yp p y * h p x y) := by
      simp only [M2, h, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hXsum : ∑ p : P, Xp p x * h p x y =
        (∑ p : P, cout p * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y) := by
      simp only [Xp, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      have : ∑ q : Q, lam q * (μq q p * νq q p + Uq q x * νq q p + Uq' q x * μq q p) =
          (∑ q : Q, lam q * (μq q p * νq q p)) +
          (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      rw [this]
      ring
    rw [hM2eq, hXsum]
    simp only [M0, Yp]
    ring
  have hR0 : HasRankLe M0 2 := hasRankLe_add (hasRankLe_one _ _) (hasRankLe_one _ _)
  have hR1 : HasRankLe M1 (2 * Fintype.card Q) := by
    have h1 := hasRankLe_add
      (hasRankLe_sum_univ (fun q x => lam q * Uq q x) (fun q y => Vq' q y))
      (hasRankLe_sum_univ (fun q x => lam q * Uq' q x) (fun q y => Vq q y))
    have heq : Fintype.card Q + Fintype.card Q = 2 * Fintype.card Q := by omega
    rw [heq] at h1
    exact h1
  have hR2 : HasRankLe M2 (4 * Fintype.card P) := by
    have ha := hasRankLe_add
      (hasRankLe_sum_univ (fun p x => Xp p x * pa p x) (fun p y => pb' p y))
      (hasRankLe_sum_univ (fun p x => Xp p x * pa' p x) (fun p y => pb p y))
    have hb := hasRankLe_add
      (hasRankLe_sum_univ (fun p x => pa p x) (fun p y => Yp p y * pb' p y))
      (hasRankLe_sum_univ (fun p x => pa' p x) (fun p y => Yp p y * pb p y))
    have hab := hasRankLe_add ha hb
    have h4 : Fintype.card P + Fintype.card P + (Fintype.card P + Fintype.card P) = 4 * Fintype.card P := by omega
    rw [h4] at hab
    exact hab
  have hR3 : HasRankLe M3 (4 * Eset.card) := by
    have ha := hasRankLe_add
      (hasRankLe_sum Eset (fun pp x => pa pp.1 x * pa pp.2 x) (fun pp y => pb' pp.1 y * pb' pp.2 y))
      (hasRankLe_sum Eset (fun pp x => pa pp.1 x * pa' pp.2 x) (fun pp y => pb' pp.1 y * pb pp.2 y))
    have hb := hasRankLe_add
      (hasRankLe_sum Eset (fun pp x => pa' pp.1 x * pa pp.2 x) (fun pp y => pb pp.1 y * pb' pp.2 y))
      (hasRankLe_sum Eset (fun pp x => pa' pp.1 x * pa' pp.2 x) (fun pp y => pb pp.1 y * pb pp.2 y))
    have hab := hasRankLe_add ha hb
    have h4 : Eset.card + Eset.card + (Eset.card + Eset.card) = 4 * Eset.card := by omega
    rw [h4] at hab
    exact hab
  have hAll := hasRankLe_add (hasRankLe_add (hasRankLe_add hR0 hR1) hR2) hR3
  have hRank_id : HasRankLe (fun x y : Fin N => if x = y then (1 : ZMod 2) else 0)
      (2 + 2 * Fintype.card Q + 4 * Fintype.card P + 4 * Eset.card) := by
    convert hAll using 1
    funext x y
    exact hMsum x y
  exact ⟨Eset.card, hasRankLe_id_le hRank_id, hTuran2⟩

lemma circuit_two_phase_bound (N t : ℕ) (hN : 0 < N) (C : Circuit)
    (hRB : ReadsBack (N + N) C) (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hCount : C.gates.countP nonlinear ≤ t)
    (hDepth : (depths (N + N) C).getD C.output 0 ≤ 2)
    (hRep : Represents (fun (x y : Fin N) => decide (x = y)) C) :
    ∃ s k E : ℕ, s + k ≤ t ∧ N ≤ 2 + 2 * k + 4 * s + 4 * E ∧
      (2 * k + 1) * (2 * E) ≤ 2 * k * s ^ 2 := by
  classical
  let w := N + N
  let f : ℕ → Fin N → Fin N → ZMod 2 := fun wire x y =>
    b2f ((C.wires (oneEach x y)).getD wire false)
  let d : ℕ → ℕ := fun wire => (depths w C).getD wire 0
  have hOut_lt : C.output < w + C.gates.length := by
    by_contra hge
    have hlen : (C.wires (oneEach ⟨0, hN⟩ ⟨0, hN⟩)).length = w + C.gates.length := by
      rw [wires_eq_foldl, wires_fold_length, oneEach_length]
    have hev : C.eval (oneEach ⟨0, hN⟩ ⟨0, hN⟩) = false := by
      simp only [Circuit.eval, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hrep0 := hRep ⟨0, hN⟩ ⟨0, hN⟩
    simp [hev] at hrep0
  let P : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => nonlinear (gateAt C j) = true ∧ d (w + j) = 1)
  let Q : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => nonlinear (gateAt C j) = true ∧ d (w + j) = 2)
  have hPQ_disj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro j hjP hjQ
    have h1 := (Finset.mem_filter.mp hjP).2.2
    have h2 := (Finset.mem_filter.mp hjQ).2.2
    omega
  have hPQ_card : P.card + Q.card ≤ t := by
    have hunion : (P ∪ Q).card ≤ ((Finset.range C.gates.length).filter
        (fun j => nonlinear (gateAt C j) = true)).card := by
      apply Finset.card_le_card
      intro j hj
      rcases Finset.mem_union.mp hj with hjP | hjQ
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjP).1, (Finset.mem_filter.mp hjP).2.1⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjQ).1, (Finset.mem_filter.mp hjQ).2.1⟩
    have hcnt : ((Finset.range C.gates.length).filter
        (fun j => nonlinear (gateAt C j) = true)).card = C.gates.countP nonlinear := by
      rw [List.countP_eq_length_filter]
      have : ∀ (l : List Gate), ((Finset.range l.length).filter
          (fun j => nonlinear (l.getD j ⟨GateOp.or, []⟩) = true)).card =
          (l.filter nonlinear).length := by
        intro l
        induction l using List.reverseRecOn with
        | nil => simp
        | append_singleton xs g ih =>
          rw [List.length_append, List.length_singleton, Finset.range_add_one,
            Finset.filter_insert, List.filter_append, List.length_append]
          have hprev : (Finset.range xs.length).filter
              (fun j => nonlinear ((xs ++ [g]).getD j ⟨GateOp.or, []⟩) = true) =
              (Finset.range xs.length).filter
              (fun j => nonlinear (xs.getD j ⟨GateOp.or, []⟩) = true) := by
            refine Finset.filter_congr fun j hj => ?_
            rw [getD_append_left xs [g] j _ (Finset.mem_range.mp hj)]
          rw [hprev, getD_concat_last]
          by_cases hg : nonlinear g = true
          · rw [if_pos hg, Finset.card_insert_of_notMem (by simp), ih]
            simp [hg]
          · rw [if_neg hg, ih]
            have hgf : nonlinear g = false := Bool.eq_false_iff.mpr hg
            simp [hgf]
      exact this C.gates
    rw [← Finset.card_union_of_disjoint hPQ_disj]
    omega
  have hDepth0 : ∀ wire < w + C.gates.length, d wire = 0 →
      ∃ A B : Fin N → ZMod 2, ∀ x y, f wire x y = A x + B y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd0
      by_cases hw : wire < w
      · by_cases hN1 : wire < N
        · refine ⟨fun x => b2f (decide (⟨wire, hN1⟩ = x)), fun _ => 0, fun x y => ?_⟩
          simp only [f, add_zero]
          rw [wires_getD_input C (oneEach x y) wire (by rw [oneEach_length]; exact hw)]
          rw [oneEach_getD_left x y wire hN1]
        · have hN2 : wire - N < N := by omega
          refine ⟨fun _ => 0, fun y => b2f (decide (⟨wire - N, hN2⟩ = y)), fun x y => ?_⟩
          simp only [f, zero_add]
          rw [wires_getD_input C (oneEach x y) wire (by rw [oneEach_length]; exact hw)]
          have heq : wire = N + (wire - N) := by omega
          have hr := oneEach_getD_right x y (wire - N) hN2
          rw [← heq] at hr
          rw [hr]
      · set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd0 ⊢
        have hdg := depths_getD_gate w C hRB j hj
        change d (w + j) = ((gateAt C j).inputs.map fun i => d i).foldr max 0 + (nonlinear (gateAt C j)).toNat at hdg
        rw [hd0] at hdg
        have hnl : nonlinear (gateAt C j) = false := by
          cases h : nonlinear (gateAt C j)
          · rfl
          · simp [h] at hdg
        have hmax0 : ((gateAt C j).inputs.map fun i => d i).foldr max 0 = 0 := by
          simp [hnl] at hdg
          omega
        have hinp0 : ∀ a ∈ (gateAt C j).inputs, d a = 0 := by
          intro a ha
          have hle := (foldr_max_le_iff _ 0).mp (le_of_eq hmax0) (d a) (List.mem_map_of_mem ha)
          omega
        have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
          rw [gateAt_eq_getElem C j hj]
          exact hFan _ (List.getElem_mem hj)
        rcases gate_eval_linear (gateAt C j) hFan_j hnl with
          ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
        · refine ⟨fun _ => c, fun _ => 0, fun x y => ?_⟩
          simp only [f, add_zero]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
          exact hc
        · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
          have ha0 : d a = 0 := hinp0 a (by simp [h1])
          obtain ⟨Aa, Ba, hfa⟩ := ih a (by omega) (by omega) ha0
          refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y, fun x y => ?_⟩
          simp only [f]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
          simp only [List.map_cons, List.map_nil]
          rw [hc]
          change c0 + c1 * f a x y = _
          rw [hfa x y]
          ring
        · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
          have hb_lt : b < w + j := hRB j hj b (by simp [h2])
          obtain ⟨Aa, Ba, hfa⟩ := ih a (by omega) (by omega) (hinp0 a (by simp [h2]))
          obtain ⟨Ab, Bb, hfb⟩ := ih b (by omega) (by omega) (hinp0 b (by simp [h2]))
          refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y, fun x y => ?_⟩
          simp only [f]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
          simp only [List.map_cons, List.map_nil]
          rw [hc]
          change c0 + c1 * f a x y + c2 * f b x y = _
          rw [hfa x y, hfb x y]
          ring
  have hPrepSpec : ∀ p : P, ∃ (a a' b b' α β : Fin N → ZMod 2), ∀ x y,
      f (w + p.val) x y = a x * b' y + a' x * b y + α x + β y := by
    intro p
    have hp := Finset.mem_filter.mp p.property
    have hj : p.val < C.gates.length := Finset.mem_range.mp hp.1
    have hnl : nonlinear (gateAt C p.val) = true := hp.2.1
    have hd1 : d (w + p.val) = 1 := hp.2.2
    obtain ⟨u, v, huv, α0, β0, γ0, hgv⟩ := gate_eval_nonlinear (gateAt C p.val) hnl
    have hdg := depths_getD_gate w C hRB p.val hj
    change d (w + p.val) = ((gateAt C p.val).inputs.map fun i => d i).foldr max 0 + (nonlinear (gateAt C p.val)).toNat at hdg
    rw [hd1, hnl, Bool.toNat_true] at hdg
    have hmax0 : ((gateAt C p.val).inputs.map fun i => d i).foldr max 0 = 0 := by omega
    have hu_lt : u < w + p.val := hRB p.val hj u (by simp [huv])
    have hv_lt : v < w + p.val := hRB p.val hj v (by simp [huv])
    have hu0 : d u = 0 := by
      have := (foldr_max_le_iff _ 0).mp (le_of_eq hmax0) (d u) (List.mem_map_of_mem (by simp [huv]))
      omega
    have hv0 : d v = 0 := by
      have := (foldr_max_le_iff _ 0).mp (le_of_eq hmax0) (d v) (List.mem_map_of_mem (by simp [huv]))
      omega
    obtain ⟨Au, Bu, hfu⟩ := hDepth0 u (by omega) hu0
    obtain ⟨Av, Bv, hfv⟩ := hDepth0 v (by omega) hv0
    refine ⟨fun x => Au x + β0, fun x => Av x + α0, Bu, Bv,
      fun x => (Au x + β0) * (Av x + α0) + γ0, fun y => Bu y * Bv y, fun x y => ?_⟩
    simp only [f]
    rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) p.val hj, huv]
    simp only [List.map_cons, List.map_nil]
    rw [hgv]
    change (f u x y + β0) * (f v x y + α0) + γ0 = _
    rw [hfu x y, hfv x y]
    ring
  choose pa pa' pb pb' pα pβ hpEq using hPrepSpec
  let h : P → Fin N → Fin N → ZMod 2 := fun p x y => pa p x * pb' p y + pa' p x * pb p y
  have hDepth1 : ∀ wire < w + C.gates.length, d wire ≤ 1 →
      ∃ (A B : Fin N → ZMod 2) (c : P → ZMod 2), ∀ x y,
        f wire x y = A x + B y + ∑ p : P, c p * h p x y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd1
      by_cases hd0 : d wire = 0
      · obtain ⟨A, B, hAB⟩ := hDepth0 wire hlt hd0
        exact ⟨A, B, 0, fun x y => by simp [hAB x y]⟩
      · have hw : w ≤ wire := by
          by_contra hltw
          have := depths_getD_input w C wire (by omega)
          exact hd0 this
        set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd1 hd0 ⊢
        by_cases hnl : nonlinear (gateAt C j) = true
        · have hjP : j ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hnl, by omega⟩
          let pj : P := ⟨j, hjP⟩
          refine ⟨pα pj, pβ pj, fun p => if p = pj then 1 else 0, fun x y => ?_⟩
          rw [hpEq pj x y]
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, h]
          ring
        · have hnlf : nonlinear (gateAt C j) = false := Bool.eq_false_iff.mpr hnl
          have hdg := depths_getD_gate w C hRB j hj
          change d (w + j) = ((gateAt C j).inputs.map fun i => d i).foldr max 0 + (nonlinear (gateAt C j)).toNat at hdg
          have hmax1 : ((gateAt C j).inputs.map fun i => d i).foldr max 0 ≤ 1 := by
            simp [hnlf] at hdg
            omega
          have hinp1 : ∀ a ∈ (gateAt C j).inputs, d a ≤ 1 := by
            intro a ha
            exact (foldr_max_le_iff _ 1).mp hmax1 (d a) (List.mem_map_of_mem ha)
          have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
            rw [gateAt_eq_getElem C j hj]
            exact hFan _ (List.getElem_mem hj)
          rcases gate_eval_linear (gateAt C j) hFan_j hnlf with
            ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
          · refine ⟨fun _ => c, fun _ => 0, 0, fun x y => ?_⟩
            simp only [f, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
            exact hc
          · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
            obtain ⟨Aa, Ba, ca, hfa⟩ := ih a (by omega) (by omega) (hinp1 a (by simp [h1]))
            refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y, fun p => c1 * ca p, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y = _
            rw [hfa x y, mul_add, mul_add, Finset.mul_sum]
            have hsm : ∑ p : P, c1 * (ca p * h p x y) = ∑ p : P, c1 * ca p * h p x y :=
              Finset.sum_congr rfl fun p _ => by ring
            rw [hsm]
            ring
          · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
            have hb_lt : b < w + j := hRB j hj b (by simp [h2])
            obtain ⟨Aa, Ba, ca, hfa⟩ := ih a (by omega) (by omega) (hinp1 a (by simp [h2]))
            obtain ⟨Ab, Bb, cb, hfb⟩ := ih b (by omega) (by omega) (hinp1 b (by simp [h2]))
            refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y,
              fun p => c1 * ca p + c2 * cb p, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y + c2 * f b x y = _
            rw [hfa x y, hfb x y]
            have hsm : ∑ p : P, (c1 * ca p + c2 * cb p) * h p x y =
                c1 * (∑ p : P, ca p * h p x y) + c2 * (∑ p : P, cb p * h p x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun p _ => by ring
            rw [hsm]
            ring
  have hFinalSpec : ∀ q : Q, ∃ (Uq Uq' Vq Vq' : Fin N → ZMod 2) (μq νq : P → ZMod 2) (γq : ZMod 2),
      ∀ x y, f (w + q.val) x y =
        (Uq x + Vq y + ∑ p : P, μq p * h p x y) * (Uq' x + Vq' y + ∑ p : P, νq p * h p x y) + γq := by
    intro q
    have hq := Finset.mem_filter.mp q.property
    have hj : q.val < C.gates.length := Finset.mem_range.mp hq.1
    have hnl : nonlinear (gateAt C q.val) = true := hq.2.1
    have hd2 : d (w + q.val) = 2 := hq.2.2
    obtain ⟨u, v, huv, α0, β0, γ0, hgv⟩ := gate_eval_nonlinear (gateAt C q.val) hnl
    have hdg := depths_getD_gate w C hRB q.val hj
    change d (w + q.val) = ((gateAt C q.val).inputs.map fun i => d i).foldr max 0 + (nonlinear (gateAt C q.val)).toNat at hdg
    rw [hd2, hnl, Bool.toNat_true] at hdg
    have hmax1 : ((gateAt C q.val).inputs.map fun i => d i).foldr max 0 ≤ 1 := by omega
    have hu_lt : u < w + q.val := hRB q.val hj u (by simp [huv])
    have hv_lt : v < w + q.val := hRB q.val hj v (by simp [huv])
    have hu1 : d u ≤ 1 := (foldr_max_le_iff _ 1).mp hmax1 (d u) (List.mem_map_of_mem (by simp [huv]))
    have hv1 : d v ≤ 1 := (foldr_max_le_iff _ 1).mp hmax1 (d v) (List.mem_map_of_mem (by simp [huv]))
    obtain ⟨Au, Bu, cu, hfu⟩ := hDepth1 u (by omega) hu1
    obtain ⟨Av, Bv, cv, hfv⟩ := hDepth1 v (by omega) hv1
    refine ⟨fun x => Au x + β0, fun x => Av x + α0, Bu, Bv, cu, cv, γ0, fun x y => ?_⟩
    simp only [f]
    rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) q.val hj, huv]
    simp only [List.map_cons, List.map_nil]
    rw [hgv]
    change (f u x y + β0) * (f v x y + α0) + γ0 = _
    rw [hfu x y, hfv x y]
    ring
  choose Uq Uq' Vq Vq' μq νq γq hqEq using hFinalSpec
  have hDepth2 : ∀ wire < w + C.gates.length, d wire ≤ 2 →
      ∃ (A B : Fin N → ZMod 2) (c : P → ZMod 2) (lam : Q → ZMod 2), ∀ x y,
        f wire x y = A x + B y + ∑ p : P, c p * h p x y + ∑ q : Q, lam q * f (w + q.val) x y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd2
      by_cases hd1 : d wire ≤ 1
      · obtain ⟨A, B, c, h1⟩ := hDepth1 wire hlt hd1
        exact ⟨A, B, c, 0, fun x y => by simp [h1 x y]⟩
      · have hw : w ≤ wire := by
          by_contra hltw
          have h0 : d wire = 0 := depths_getD_input w C wire (by omega)
          omega
        set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd2 hd1 ⊢
        by_cases hnl : nonlinear (gateAt C j) = true
        · have hjQ : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hnl, by omega⟩
          let qj : Q := ⟨j, hjQ⟩
          refine ⟨0, 0, 0, fun q => if q = qj then 1 else 0, fun x y => ?_⟩
          simp [qj]
        · have hnlf : nonlinear (gateAt C j) = false := Bool.eq_false_iff.mpr hnl
          have hdg := depths_getD_gate w C hRB j hj
          change d (w + j) = ((gateAt C j).inputs.map fun i => d i).foldr max 0 + (nonlinear (gateAt C j)).toNat at hdg
          have hmax2 : ((gateAt C j).inputs.map fun i => d i).foldr max 0 ≤ 2 := by
            simp [hnlf] at hdg
            omega
          have hinp2 : ∀ a ∈ (gateAt C j).inputs, d a ≤ 2 := by
            intro a ha
            exact (foldr_max_le_iff _ 2).mp hmax2 (d a) (List.mem_map_of_mem ha)
          have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
            rw [gateAt_eq_getElem C j hj]
            exact hFan _ (List.getElem_mem hj)
          rcases gate_eval_linear (gateAt C j) hFan_j hnlf with
            ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
          · refine ⟨fun _ => c, fun _ => 0, 0, 0, fun x y => ?_⟩
            simp only [f, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
            exact hc
          · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
            obtain ⟨Aa, Ba, ca, la, hfa⟩ := ih a (by omega) (by omega) (hinp2 a (by simp [h1]))
            refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y,
              fun p => c1 * ca p, fun q => c1 * la q, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y = _
            rw [hfa x y]
            have h1s : ∑ p : P, c1 * ca p * h p x y = c1 * ∑ p : P, ca p * h p x y := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
            have h2s : ∑ q : Q, c1 * la q * f (w + q.val) x y = c1 * ∑ q : Q, la q * f (w + q.val) x y := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
            rw [h1s, h2s]
            ring
          · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
            have hb_lt : b < w + j := hRB j hj b (by simp [h2])
            obtain ⟨Aa, Ba, ca, la, hfa⟩ := ih a (by omega) (by omega) (hinp2 a (by simp [h2]))
            obtain ⟨Ab, Bb, cb, lb, hfb⟩ := ih b (by omega) (by omega) (hinp2 b (by simp [h2]))
            refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y,
              fun p => c1 * ca p + c2 * cb p, fun q => c1 * la q + c2 * lb q, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y + c2 * f b x y = _
            rw [hfa x y, hfb x y]
            have h1s : ∑ p : P, (c1 * ca p + c2 * cb p) * h p x y =
                c1 * (∑ p : P, ca p * h p x y) + c2 * (∑ p : P, cb p * h p x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun _ _ => by ring
            have h2s : ∑ q : Q, (c1 * la q + c2 * lb q) * f (w + q.val) x y =
                c1 * (∑ q : Q, la q * f (w + q.val) x y) + c2 * (∑ q : Q, lb q * f (w + q.val) x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun _ _ => by ring
            rw [h1s, h2s]
            ring
  obtain ⟨Aout, Bout, cout, lam, hout⟩ := hDepth2 C.output hOut_lt hDepth
  have hId : ∀ x y : Fin N, (if x = y then (1 : ZMod 2) else 0) =
      Aout x + Bout y + (∑ p : P, cout p * h p x y) +
      ∑ q : Q, lam q * ((Uq q x + Vq q y + ∑ p : P, μq q p * h p x y) *
        (Uq' q x + Vq' q y + ∑ p : P, νq q p * h p x y) + γq q) := by
    intro x y
    have hr := hRep x y
    have hfx : (if x = y then (1 : ZMod 2) else 0) = f C.output x y := by
      simp only [f, Circuit.eval] at hr ⊢
      rw [hr]
      by_cases hxy : x = y <;> simp [hxy, b2f]
    rw [hfx, hout x y]
    congr 1
    exact Finset.sum_congr rfl fun q _ => by rw [hqEq q x y]
  obtain ⟨E, hRank, hTuran⟩ := two_phase_rank_cap N Subtype.val Subtype.val_injective
    pa pa' pb pb' Aout Bout cout lam Uq Uq' Vq Vq' μq νq γq hId
  simp only [Fintype.card_coe] at hRank hTuran
  exact ⟨P.card, Q.card, E, hPQ_card, hRank, hTuran⟩

structure Builder (width : ℕ) where
  gates : List Gate
  hRB : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < width + j
  hFan : ∀ g ∈ gates, g.inputs.length ≤ 2

def Builder.empty (width : ℕ) : Builder width :=
  ⟨[], fun _ h => by simp at h, fun _ h => by simp at h⟩

def Builder.push {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    Builder width × ℕ :=
  (⟨B.gates ++ [g], by
      intro j hj i hi
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < B.gates.length
      · rw [getD_append_left B.gates [g] j _ hlt] at hi
        exact B.hRB j hlt i hi
      · have heq : j = B.gates.length := by omega
        subst heq
        rw [getD_concat_last] at hi
        exact hgRB i hi,
    by
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact B.hFan g' h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact hgFan⟩,
   width + B.gates.length)

def Builder.wires {width : ℕ} (B : Builder width) (x : List Bool) : List Bool :=
  B.gates.foldl wiresStep x

def Builder.depths {width : ℕ} (B : Builder width) : List ℕ :=
  B.gates.foldl depthsStep (List.replicate width 0)

def Builder.nlCount {width : ℕ} (B : Builder width) : ℕ :=
  B.gates.countP nonlinear

lemma builder_push_wires_old {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = width) (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.push g hgRB hgFan).1.wires x).getD w false = (B.wires x).getD w false := by
  simp only [Builder.push, Builder.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, wiresStep]
  rw [getD_append_left]
  rw [wires_fold_length, hx]
  exact hw

lemma builder_push_wires_new {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = width) :
    ((B.push g hgRB hgFan).1.wires x).getD (B.push g hgRB hgFan).2 false =
      g.op.eval (g.inputs.map fun i => (B.wires x).getD i false) := by
  simp only [Builder.push, Builder.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, wiresStep]
  have hlen : (B.gates.foldl wiresStep x).length = width + B.gates.length := by
    rw [wires_fold_length, hx]
  rw [← hlen, getD_concat_last]

lemma builder_push_depths_old {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.push g hgRB hgFan).1.depths).getD w 0 = (B.depths).getD w 0 := by
  simp only [Builder.push, Builder.depths, List.foldl_append, List.foldl_cons, List.foldl_nil, depthsStep]
  rw [getD_append_left]
  rw [depths_fold_length, List.length_replicate]
  exact hw

lemma builder_push_depths_new {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    ((B.push g hgRB hgFan).1.depths).getD (B.push g hgRB hgFan).2 0 =
      (g.inputs.map fun i => (B.depths).getD i 0).foldr max 0 + (nonlinear g).toNat := by
  simp only [Builder.push, Builder.depths, List.foldl_append, List.foldl_cons, List.foldl_nil, depthsStep]
  have hlen : (B.gates.foldl depthsStep (List.replicate width 0)).length = width + B.gates.length := by
    rw [depths_fold_length, List.length_replicate]
  rw [← hlen, getD_concat_last]

lemma builder_push_nlCount {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    (B.push g hgRB hgFan).1.nlCount = B.nlCount + (nonlinear g).toNat := by
  simp only [Builder.push, Builder.nlCount, List.countP_append, List.countP_singleton]
  cases nonlinear g <;> simp

lemma builder_push_len {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    (B.push g hgRB hgFan).1.gates.length = B.gates.length + 1 := by
  simp [Builder.push]

lemma nonlinear_or_nil : nonlinear ⟨GateOp.or, []⟩ = false := rfl
lemma nonlinear_not (w : ℕ) : nonlinear ⟨GateOp.not, [w]⟩ = false := rfl
lemma nonlinear_mod2 (a b : ℕ) : nonlinear ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
lemma nonlinear_and (a b : ℕ) : nonlinear ⟨GateOp.and, [a, b]⟩ = true := rfl

lemma eval_mod2_not (a b : Bool) :
    (!(GateOp.eval (GateOp.mod 2) [a, b])) = xor a b := by
  cases a <;> cases b <;> decide

def Builder.pushXor {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    Builder width × ℕ :=
  let p1 := B.push ⟨GateOp.mod 2, [a, b]⟩
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp)
  let p2 := p1.1.push ⟨GateOp.not, [p1.2]⟩
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; simp [p1, Builder.push])
    (by simp)
  p2

lemma pushXor_len {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).1.gates.length = B.gates.length + 2 := by
  simp [Builder.pushXor, Builder.push]

lemma pushXor_out_lt {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).2 < width + (B.pushXor a b ha hb).1.gates.length := by
  simp [Builder.pushXor, Builder.push]

lemma pushXor_nlCount {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).1.nlCount = B.nlCount := by
  simp only [Builder.pushXor, builder_push_nlCount, nonlinear_mod2, nonlinear_not]
  rfl

lemma pushXor_wires_old {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (x : List Bool) (hx : x.length = width) (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.wires x).getD w false = (B.wires x).getD w false := by
  simp only [Builder.pushXor]
  rw [builder_push_wires_old _ _ _ _ x hx w (by simp [Builder.push]; omega)]
  rw [builder_push_wires_old _ _ _ _ x hx w hw]

lemma pushXor_wires_new {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (x : List Bool) (hx : x.length = width) :
    ((B.pushXor a b ha hb).1.wires x).getD (B.pushXor a b ha hb).2 false =
      xor ((B.wires x).getD a false) ((B.wires x).getD b false) := by
  simp only [Builder.pushXor]
  rw [builder_push_wires_new _ _ _ _ x hx]
  simp only [List.map_cons, List.map_nil]
  rw [builder_push_wires_new _ _ _ _ x hx]
  simp only [List.map_cons, List.map_nil]
  have hnot : GateOp.eval GateOp.not [(GateOp.mod 2).eval [(B.wires x).getD a false, (B.wires x).getD b false]] =
      !((GateOp.mod 2).eval [(B.wires x).getD a false, (B.wires x).getD b false]) := rfl
  rw [hnot]
  exact eval_mod2_not _ _

lemma pushXor_depths_old {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.depths).getD w 0 = (B.depths).getD w 0 := by
  simp only [Builder.pushXor]
  rw [builder_push_depths_old _ _ _ _ w (by simp [Builder.push]; omega)]
  rw [builder_push_depths_old _ _ _ _ w hw]

lemma pushXor_depths_new {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.depths).getD (B.pushXor a b ha hb).2 0 =
      max ((B.depths).getD a 0) ((B.depths).getD b 0) := by
  simp only [Builder.pushXor]
  rw [builder_push_depths_new]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_not, Bool.toNat_false, add_zero]
  rw [builder_push_depths_new]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_mod2, Bool.toNat_false, add_zero]
  omega

def Builder.foldXor {width : ℕ} (B : Builder width) (acc : ℕ) (hacc : acc < width + B.gates.length)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < width + B.gates.length) : Builder width × ℕ :=
  match ws with
  | [] => (B, acc)
  | w :: rest =>
    let p := B.pushXor acc w hacc (hws w (by simp))
    have hlen : B.gates.length ≤ p.1.gates.length := by rw [pushXor_len]; omega
    p.1.foldXor p.2 (pushXor_out_lt B acc w hacc _) rest
      (fun u hu => lt_of_lt_of_le (hws u (by simp [hu])) (Nat.add_le_add_left hlen width))

lemma foldXor_spec {width : ℕ} (B : Builder width) (acc : ℕ) (hacc : acc < width + B.gates.length)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < width + B.gates.length) (D : ℕ)
    (hdAcc : (B.depths).getD acc 0 ≤ D) (hdWs : ∀ w ∈ ws, (B.depths).getD w 0 ≤ D) :
    let res := B.foldXor acc hacc ws hws
    B.gates.length ≤ res.1.gates.length ∧
    res.2 < width + res.1.gates.length ∧
    res.1.nlCount = B.nlCount ∧
    (res.1.depths).getD res.2 0 ≤ D ∧
    (∀ w < width + B.gates.length, (res.1.depths).getD w 0 = (B.depths).getD w 0) ∧
    (∀ (x : List Bool), x.length = width →
      (∀ w < width + B.gates.length, (res.1.wires x).getD w false = (B.wires x).getD w false) ∧
      (res.1.wires x).getD res.2 false =
        ws.foldl (fun b w => xor b ((B.wires x).getD w false)) ((B.wires x).getD acc false)) := by
  induction ws generalizing B acc with
  | nil =>
    refine ⟨le_refl _, hacc, rfl, hdAcc, fun _ _ => rfl, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
  | cons w rest ih =>
    simp only [Builder.foldXor]
    set p := B.pushXor acc w hacc (hws w (by simp))
    have hlen1 : B.gates.length ≤ p.1.gates.length := by rw [pushXor_len]; omega
    have hdP : (p.1.depths).getD p.2 0 ≤ D := by
      rw [pushXor_depths_new]
      exact max_le hdAcc (hdWs w (by simp))
    have hdRest : ∀ u ∈ rest, (p.1.depths).getD u 0 ≤ D := by
      intro u hu
      rw [pushXor_depths_old B acc w _ _ u (hws u (by simp [hu]))]
      exact hdWs u (by simp [hu])
    have hih := ih p.1 p.2 (pushXor_out_lt B acc w _ _)
      (fun u hu => lt_of_lt_of_le (hws u (by simp [hu])) (Nat.add_le_add_left hlen1 width))
      hdP hdRest
    rcases hih with ⟨hlen2, hout, hnl, hdOut, hdOld, hW⟩
    refine ⟨le_trans hlen1 hlen2, hout, by rw [hnl, pushXor_nlCount], hdOut, ?_, ?_⟩
    · intro u hu
      rw [hdOld u (by omega), pushXor_depths_old B acc w _ _ u hu]
    · intro x hx
      obtain ⟨hwOld, hwNew⟩ := hW x hx
      refine ⟨fun u hu => by rw [hwOld u (by omega), pushXor_wires_old B acc w _ _ x hx u hu], ?_⟩
      rw [hwNew, List.foldl_cons, pushXor_wires_new B acc w _ _ x hx]
      have hcongr : ∀ (b0 : Bool) (l : List ℕ), (∀ u ∈ l, u < width + B.gates.length) →
          l.foldl (fun b u => xor b ((p.1.wires x).getD u false)) b0 =
          l.foldl (fun b u => xor b ((B.wires x).getD u false)) b0 := by
        intro b0 l hl
        induction l generalizing b0 with
        | nil => rfl
        | cons u us ih2 =>
          simp only [List.foldl_cons]
          rw [pushXor_wires_old B acc w _ _ x hx u (hl u (by simp))]
          exact ih2 _ (fun v hv => hl v (by simp [hv]))
      exact hcongr _ rest (fun u hu => hws u (by simp [hu]))

def Builder.pushXorList {width : ℕ} (B : Builder width) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < width + B.gates.length) : Builder width × ℕ :=
  let p0 := B.push ⟨GateOp.or, []⟩ (by intro _ h; simp at h) (by simp)
  have hlen : B.gates.length ≤ p0.1.gates.length := by rw [builder_push_len]; omega
  p0.1.foldXor p0.2 (by simp [p0, Builder.push]) ws
    (fun u hu => lt_of_lt_of_le (hws u hu) (Nat.add_le_add_left hlen width))

lemma b2f_foldl_xor {α : Type} (l : List α) (f : α → Bool) (b0 : Bool) :
    b2f (l.foldl (fun b a => xor b (f a)) b0) = b2f b0 + (l.map fun a => b2f (f a)).sum := by
  induction l generalizing b0 with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, b2f_xor, add_assoc]

lemma pushXorList_spec {width : ℕ} (B : Builder width) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < width + B.gates.length) (D : ℕ)
    (hdWs : ∀ w ∈ ws, (B.depths).getD w 0 ≤ D) :
    let res := B.pushXorList ws hws
    B.gates.length ≤ res.1.gates.length ∧
    res.2 < width + res.1.gates.length ∧
    res.1.nlCount = B.nlCount ∧
    (res.1.depths).getD res.2 0 ≤ D ∧
    (∀ w < width + B.gates.length, (res.1.depths).getD w 0 = (B.depths).getD w 0) ∧
    (∀ (x : List Bool), x.length = width →
      (∀ w < width + B.gates.length, (res.1.wires x).getD w false = (B.wires x).getD w false) ∧
      b2f ((res.1.wires x).getD res.2 false) = (ws.map fun w => b2f ((B.wires x).getD w false)).sum) := by
  simp only [Builder.pushXorList]
  set p0 := B.push ⟨GateOp.or, []⟩ (by intro _ h; simp at h) (by simp)
  have hlen0 : B.gates.length ≤ p0.1.gates.length := by rw [builder_push_len]; omega
  have hd0 : (p0.1.depths).getD p0.2 0 ≤ D := by
    rw [builder_push_depths_new]
    simp [nonlinear_or_nil]
  have hdWs' : ∀ w ∈ ws, (p0.1.depths).getD w 0 ≤ D := by
    intro w hw
    rw [builder_push_depths_old B _ _ _ w (hws w hw)]
    exact hdWs w hw
  have hspec := foldXor_spec p0.1 p0.2 (by simp [p0, Builder.push]) ws
    (fun u hu => lt_of_lt_of_le (hws u hu) (Nat.add_le_add_left hlen0 width)) D hd0 hdWs'
  rcases hspec with ⟨hlen1, hout, hnl, hdOut, hdOld, hW⟩
  refine ⟨le_trans hlen0 hlen1, hout, ?_, hdOut, ?_, ?_⟩
  · rw [hnl, builder_push_nlCount, nonlinear_or_nil]; rfl
  · intro w hw
    rw [hdOld w (by omega), builder_push_depths_old B _ _ _ w hw]
  · intro x hx
    obtain ⟨hwOld, hwNew⟩ := hW x hx
    refine ⟨fun w hw => by rw [hwOld w (by omega), builder_push_wires_old B _ _ _ x hx w hw], ?_⟩
    rw [hwNew, b2f_foldl_xor, builder_push_wires_new B _ _ _ x hx]
    simp only [List.map_nil, GateOp.eval, List.any_nil, b2f, Bool.false_eq_true, ↓reduceIte, zero_add]
    congr 1
    apply List.map_congr_left
    intro w hw
    rw [builder_push_wires_old B _ _ _ x hx w (hws w hw)]

def pushManyXor {width : ℕ} (B : Builder width) (n : ℕ)
    (ws : Fin n → List ℕ) (hws : ∀ i w, w ∈ ws i → w < width + B.gates.length) :
    { p : Builder width × (Fin n → ℕ) //
      B.gates.length ≤ p.1.gates.length ∧
      (∀ i, p.2 i < width + p.1.gates.length) ∧
      p.1.nlCount = B.nlCount ∧
      (∀ D, (∀ i w, w ∈ ws i → (B.depths).getD w 0 ≤ D) → ∀ i, (p.1.depths).getD (p.2 i) 0 ≤ D) ∧
      (∀ w < width + B.gates.length, (p.1.depths).getD w 0 = (B.depths).getD w 0) ∧
      (∀ x : List Bool, x.length = width →
        (∀ w < width + B.gates.length, (p.1.wires x).getD w false = (B.wires x).getD w false) ∧
        ∀ i, b2f ((p.1.wires x).getD (p.2 i) false) = (ws i |>.map fun w => b2f ((B.wires x).getD w false)).sum) } := by
  induction n generalizing B with
  | zero =>
    exact ⟨(B, Fin.elim0), le_refl _, fun i => i.elim0, rfl, fun _ _ i => i.elim0,
      fun _ _ => rfl, fun _ _ => ⟨fun _ _ => rfl, fun i => i.elim0⟩⟩
  | succ n ih =>
    let p1 := B.pushXorList (ws 0) (hws 0)
    have hbase := pushXorList_spec B (ws 0) (hws 0) (B.depths.foldr max 0) (fun w _ => getD_le_foldr_max B.depths w)
    have hlen1 : B.gates.length ≤ p1.1.gates.length := hbase.1
    let ws' : Fin n → List ℕ := fun i => ws i.succ
    have hws' : ∀ i w, w ∈ ws' i → w < width + p1.1.gates.length := fun i w hw =>
      lt_of_lt_of_le (hws i.succ w hw) (Nat.add_le_add_left hlen1 width)
    let r2 := ih p1.1 ws' hws'
    refine ⟨(r2.val.1, Fin.cons p1.2 r2.val.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hlen1 r2.property.1
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        have h1 : p1.2 < width + p1.1.gates.length := hbase.2.1
        have h2 : p1.1.gates.length ≤ r2.val.1.gates.length := r2.property.1
        omega
      · intro j; simp only [Fin.cons_succ]; exact r2.property.2.1 j
    · rw [r2.property.2.2.1, hbase.2.2.1]
    · intro D hD i
      have hs1 := pushXorList_spec B (ws 0) (hws 0) D (hD 0)
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [r2.property.2.2.2.2.1 p1.2 hs1.2.1]
        exact hs1.2.2.2.1
      · intro j
        simp only [Fin.cons_succ]
        refine r2.property.2.2.2.1 D ?_ j
        intro k w hw
        rw [hs1.2.2.2.2.1 w (hws k.succ w hw)]
        exact hD k.succ w hw
    · intro w hw
      rw [r2.property.2.2.2.2.1 w (by omega), hbase.2.2.2.2.1 w hw]
    · intro x hx
      obtain ⟨hwOld1, hwNew1⟩ := hbase.2.2.2.2.2 x hx
      obtain ⟨hwOld2, hwNew2⟩ := r2.property.2.2.2.2.2 x hx
      refine ⟨fun w hw => by rw [hwOld2 w (by omega), hwOld1 w hw], fun i => ?_⟩
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [hwOld2 p1.2 hbase.2.1, hwNew1]
      · intro j
        simp only [Fin.cons_succ]
        rw [hwNew2 j]
        congr 1
        apply List.map_congr_left
        intro w hw
        rw [hwOld1 w (hws j.succ w hw)]

def pushManyAnd {width : ℕ} (B : Builder width) (n : ℕ)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < width + B.gates.length) (hb : ∀ i, b i < width + B.gates.length) :
    { p : Builder width × (Fin n → ℕ) //
      B.gates.length ≤ p.1.gates.length ∧
      (∀ i, p.2 i < width + p.1.gates.length) ∧
      p.1.nlCount = B.nlCount + n ∧
      (∀ D, (∀ i, (B.depths).getD (a i) 0 ≤ D) → (∀ i, (B.depths).getD (b i) 0 ≤ D) →
        ∀ i, (p.1.depths).getD (p.2 i) 0 ≤ D + 1) ∧
      (∀ w < width + B.gates.length, (p.1.depths).getD w 0 = (B.depths).getD w 0) ∧
      (∀ x : List Bool, x.length = width →
        (∀ w < width + B.gates.length, (p.1.wires x).getD w false = (B.wires x).getD w false) ∧
        ∀ i, b2f ((p.1.wires x).getD (p.2 i) false) =
          b2f ((B.wires x).getD (a i) false) * b2f ((B.wires x).getD (b i) false)) } := by
  induction n generalizing B with
  | zero =>
    exact ⟨(B, Fin.elim0), le_refl _, fun i => i.elim0, by simp, fun _ _ _ i => i.elim0,
      fun _ _ => rfl, fun _ _ => ⟨fun _ _ => rfl, fun i => i.elim0⟩⟩
  | succ n ih =>
    let p1 := B.push ⟨GateOp.and, [a 0, b 0]⟩ (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha 0
      · exact hb 0) (by simp)
    have hlen1 : B.gates.length ≤ p1.1.gates.length := by rw [builder_push_len]; omega
    have hout1 : p1.2 < width + p1.1.gates.length := by simp [p1, Builder.push]
    let r2 := ih p1.1 (fun i => a i.succ) (fun i => b i.succ)
      (fun i => lt_of_lt_of_le (ha i.succ) (Nat.add_le_add_left hlen1 width))
      (fun i => lt_of_lt_of_le (hb i.succ) (Nat.add_le_add_left hlen1 width))
    refine ⟨(r2.val.1, Fin.cons p1.2 r2.val.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hlen1 r2.property.1
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        have := r2.property.1
        omega
      · intro j; simp only [Fin.cons_succ]; exact r2.property.2.1 j
    · rw [r2.property.2.2.1, builder_push_nlCount, nonlinear_and]
      simp only [Bool.toNat_true]
      omega
    · intro D hDa hDb i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [r2.property.2.2.2.2.1 p1.2 hout1, builder_push_depths_new]
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_and, Bool.toNat_true]
        have := hDa 0
        have := hDb 0
        omega
      · intro j
        simp only [Fin.cons_succ]
        refine r2.property.2.2.2.1 D ?_ ?_ j
        · intro k; rw [builder_push_depths_old B _ _ _ _ (ha k.succ)]; exact hDa k.succ
        · intro k; rw [builder_push_depths_old B _ _ _ _ (hb k.succ)]; exact hDb k.succ
    · intro w hw
      rw [r2.property.2.2.2.2.1 w (by omega), builder_push_depths_old B _ _ _ w hw]
    · intro x hx
      obtain ⟨hwOld2, hwNew2⟩ := r2.property.2.2.2.2.2 x hx
      refine ⟨fun w hw => by rw [hwOld2 w (by omega), builder_push_wires_old B _ _ _ x hx w hw], fun i => ?_⟩
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [hwOld2 p1.2 hout1, builder_push_wires_new B _ _ _ x hx]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact b2f_and _ _
      · intro j
        simp only [Fin.cons_succ]
        rw [hwNew2 j, builder_push_wires_old B _ _ _ x hx _ (ha j.succ),
          builder_push_wires_old B _ _ _ x hx _ (hb j.succ)]

lemma list_sum_finRange_eq {n : ℕ} (f : Fin n → ZMod 2) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ]
    exact congrArg (f 0 + ·) (ih (fun i => f i.succ))

lemma list_sum_filter_finRange {n : ℕ} (p : Fin n → Bool) (f : Fin n → ZMod 2) :
    (((List.finRange n).filter p).map f).sum = ∑ i : Fin n, if p i then f i else 0 := by
  rw [← list_sum_finRange_eq]
  have : ∀ (l : List (Fin n)), ((l.filter p).map f).sum = (l.map fun i => if p i then f i else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      cases hp : p a <;> simp [ih]
  exact this (List.finRange n)

lemma upper_bound_naive (N : ℕ) :
    ∃ C : Circuit, ReadsBack (N + N) C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ N ∧ (depths (N + N) C).getD C.output 0 ≤ 2 ∧
      Represents (fun (x y : Fin N) => decide (x = y)) C := by
  let B0 := Builder.empty (N + N)
  let rAnd := pushManyAnd B0 N (fun i => i.val) (fun i => N + i.val)
    (fun i => by have := i.isLt; simp [B0, Builder.empty]; omega)
    (fun i => by simp [B0, Builder.empty])
  let ws := (List.finRange N).map rAnd.val.2
  have hws : ∀ w ∈ ws, w < N + N + rAnd.val.1.gates.length := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    exact rAnd.property.2.1 i
  let res := rAnd.val.1.pushXorList ws hws
  have hsp := pushXorList_spec rAnd.val.1 ws hws 1 (by
    intro w hw
    rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    refine rAnd.property.2.2.2.1 0 ?_ ?_ i
    · intro j; simp [B0, Builder.empty, Builder.depths, List.getD_eq_getElem?_getD, Nat.lt_add_right N j.isLt]
    · intro j; simp [B0, Builder.empty, Builder.depths, List.getD_eq_getElem?_getD])
  let C : Circuit := ⟨res.1.gates, res.2⟩
  refine ⟨C, res.1.hRB, res.1.hFan, ?_, ?_, ?_⟩
  · change res.1.nlCount ≤ N
    rw [hsp.2.2.1, rAnd.property.2.2.1]
    simp [B0, Builder.empty, Builder.nlCount]
  · change (res.1.depths).getD res.2 0 ≤ 2
    exact le_trans hsp.2.2.2.1 (by omega)
  · intro x y
    apply b2f_injective
    have hW := (hsp.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2
    have hAndW := (rAnd.property.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2
    change b2f ((res.1.wires (oneEach x y)).getD res.2 false) = b2f (decide (x = y))
    rw [hW]
    simp only [ws, List.map_map]
    rw [list_sum_finRange_eq]
    have hmap : ∑ i : Fin N, ((fun w => b2f ((rAnd.val.1.wires (oneEach x y)).getD w false)) ∘ rAnd.val.2) i =
        ∑ i : Fin N, b2f (decide (i = x)) * b2f (decide (i = y)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.comp_apply, hAndW i]
      simp only [B0, Builder.empty, Builder.wires, List.foldl_nil]
      rw [oneEach_getD_left x y i.val i.isLt, oneEach_getD_right x y i.val i.isLt]
    rw [hmap]
    have hterm : ∀ i : Fin N, b2f (decide (i = x)) * b2f (decide (i = y)) =
        if i = x then b2f (decide (x = y)) else 0 := by
      intro i
      by_cases hix : i = x
      · subst hix; simp [b2f]
      · simp [hix, b2f]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def sympU (k : ℕ) (c : Fin (2 * k + 1)) (j : Fin k) : Bool :=
  decide (c.val / 2 = j.val)

def sympV (k : ℕ) (c : Fin (2 * k + 1)) (j : Fin k) : Bool :=
  decide (2 * j.val < c.val)

lemma symp_omega_lt (k : ℕ) (c1 c2 : Fin (2 * k + 1)) (hlt : c1.val < c2.val) :
    ∑ j : Fin k, (b2f (sympU k c1 j) * b2f (sympV k c2 j) +
      b2f (sympV k c1 j) * b2f (sympU k c2 j)) = 1 := by
  rw [Finset.sum_add_distrib]
  have hj1 : c1.val / 2 < k := by omega
  have h1 : ∑ j : Fin k, b2f (sympU k c1 j) * b2f (sympV k c2 j) = 1 := by
    have hterm : ∀ j : Fin k, b2f (sympU k c1 j) * b2f (sympV k c2 j) =
        if j = ⟨c1.val / 2, hj1⟩ then 1 else 0 := by
      intro j
      by_cases hj : j = ⟨c1.val / 2, hj1⟩
      · subst hj
        have h2 : 2 * (c1.val / 2) < c2.val := by omega
        simp [sympU, sympV, h2, b2f]
      · have hne : c1.val / 2 ≠ j.val := fun heq => hj (Fin.ext heq.symm)
        simp [sympU, hne, hj, b2f]
    simp [hterm]
  have h2 : ∑ j : Fin k, b2f (sympV k c1 j) * b2f (sympU k c2 j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hju : c2.val / 2 = j.val
    · have hnot : ¬ (2 * j.val < c1.val) := by omega
      simp [sympV, hnot, b2f]
    · simp [sympU, hju, b2f]
  rw [h1, h2, add_zero]

lemma symp_omega_ne (k : ℕ) (c1 c2 : Fin (2 * k + 1)) (hne : c1 ≠ c2) :
    ∑ j : Fin k, (b2f (sympU k c1 j) * b2f (sympV k c2 j) +
      b2f (sympV k c1 j) * b2f (sympU k c2 j)) = 1 := by
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · exact symp_omega_lt k c1 c2 hlt
  · have := symp_omega_lt k c2 c1 hgt
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => by ring

def sympDiag (k : ℕ) (c : Fin (2 * k + 1)) : Bool :=
  decide (c.val % 2 = 1)

lemma symp_diag_eq (k : ℕ) (c : Fin (2 * k + 1)) :
    ∑ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) = b2f (sympDiag k c) := by
  by_cases hc : c.val < 2 * k
  · have hj0 : c.val / 2 < k := by omega
    have hterm : ∀ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) =
        if j = ⟨c.val / 2, hj0⟩ then b2f (sympDiag k c) else 0 := by
      intro j
      by_cases hj : j = ⟨c.val / 2, hj0⟩
      · subst hj
        have hiff : 2 * (c.val / 2) < c.val ↔ c.val % 2 = 1 := by omega
        simp [sympU, sympV, sympDiag, hiff, b2f]
      · have hne : c.val / 2 ≠ j.val := fun heq => hj (Fin.ext heq.symm)
        simp [sympU, hne, hj, b2f]
    simp [hterm]
  · have heq : c.val = 2 * k := by omega
    have hzero : ∀ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) = 0 := by
      intro j
      have hne : c.val / 2 ≠ j.val := by omega
      simp [sympU, hne, b2f]
    rw [Finset.sum_eq_zero fun j _ => hzero j]
    have hmod : c.val % 2 = 0 := by omega
    simp [sympDiag, hmod, b2f]

def turanPairs (s k : ℕ) : Finset (Fin s × Fin s) :=
  ((Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))).filter
    (fun pp => pp.1.val < pp.2.val ∧ pp.1.val % (2 * k + 1) ≠ pp.2.val % (2 * k + 1))

lemma turanPairs_card_bound (s k : ℕ) :
    4 * (2 * k) * s ^ 2 ≤ 2 * (2 * k + 1) * (4 * (turanPairs s k).card) + (2 * k + 1) ^ 2 := by
  set m := 2 * k + 1
  have hm : 0 < m := by omega
  let cls : Fin m → Finset (Fin s) := fun c => Finset.univ.filter (fun p : Fin s => p.val % m = c.val)
  let U : Finset (Fin s × Fin s) := (Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))
  have hord : 2 * (turanPairs s k).card + ∑ c : Fin m, (cls c).card ^ 2 = s ^ 2 := by
    let Same := U.filter (fun pp => pp.1.val % m = pp.2.val % m)
    let Diff := U.filter (fun pp => pp.1.val % m ≠ pp.2.val % m)
    have hSD : Diff.card + Same.card = s ^ 2 := by
      have h1 := filter_card_add_not U (fun pp => pp.1.val % m ≠ pp.2.val % m)
      have hSame : Same = U.filter (fun pp => ¬ pp.1.val % m ≠ pp.2.val % m) := by
        ext pp; simp [Same]
      rw [← hSame] at h1
      simpa [Diff, U, sq, Fintype.card_fin] using h1
    have hDiff : Diff.card = 2 * (turanPairs s k).card := by
      let GT := U.filter (fun pp => pp.2.val < pp.1.val ∧ pp.1.val % m ≠ pp.2.val % m)
      have hU : Diff = turanPairs s k ∪ GT := by
        ext pp
        simp only [Diff, turanPairs, GT, U, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_univ, true_and]
        constructor
        · intro hne
          have hne' : pp.1.val ≠ pp.2.val := fun heq => hne (by rw [heq])
          rcases lt_or_gt_of_ne hne' with hlt | hgt
          · exact Or.inl ⟨hlt, hne⟩
          · exact Or.inr ⟨hgt, hne⟩
        · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      have hD : Disjoint (turanPairs s k) GT := by
        rw [Finset.disjoint_left]
        intro pp h1 h2
        have := (Finset.mem_filter.mp h1).2.1
        have := (Finset.mem_filter.mp h2).2.1
        omega
      have hG : GT.card = (turanPairs s k).card := by
        refine Finset.card_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_
        · intro pp hpp
          have h1 := (Finset.mem_filter.mp hpp).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
            h1.1, h1.2.symm⟩
        · intro pp1 _ pp2 _ heq; ext <;> simp_all
        · intro pp hpp
          have h1 := (Finset.mem_filter.mp hpp).2
          exact ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
            h1.1, h1.2.symm⟩, by ext <;> rfl⟩
      rw [hU, Finset.card_union_of_disjoint hD, hG]
      omega
    have hSame_eq : Same.card = ∑ c : Fin m, (cls c).card ^ 2 := by
      have hbi : Same = Finset.univ.biUnion (fun c : Fin m => cls c ×ˢ cls c) := by
        ext pp
        simp only [Same, U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_filter, cls]
        constructor
        · intro h; exact ⟨⟨pp.1.val % m, Nat.mod_lt _ hm⟩, rfl, h.symm⟩
        · rintro ⟨c, h1, h2⟩; exact h1.trans h2.symm
      have hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (fun c => cls c ×ˢ cls c) := by
        intro c1 _ c2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro pp h1 h2
        have e1 := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        have e2 := (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2
        exact hne (Fin.ext (e1.symm.trans e2))
      rw [hbi, Finset.card_biUnion (fun c1 _ c2 _ hne => hdisj (Set.mem_univ c1) (Set.mem_univ c2) hne)]
      refine Finset.sum_congr rfl fun c _ => by rw [Finset.card_product, sq]
    rw [← hDiff, ← hSame_eq, hSD]
  set q := s / m
  set rem := s % m
  have hs_eq : s = m * q + rem := (Nat.div_add_mod s m).symm
  have hrem_lt : rem < m := Nat.mod_lt s hm
  have hcls_card : ∀ c : Fin m, (cls c).card = if c.val < rem then q + 1 else q := by
    intro c
    let n_c := if c.val < rem then q + 1 else q
    have hcard : (cls c).card = (Finset.range n_c).card := by
      refine Finset.card_bij (fun p _ => p.val / m) ?_ ?_ ?_
      · intro p hp
        have hmod := (Finset.mem_filter.mp hp).2
        have hlt := p.isLt
        have hdiv : m * (p.val / m) + c.val < m * q + rem := by
          rw [← hmod, Nat.div_add_mod]; omega
        rw [Finset.mem_range]
        dsimp only [n_c]
        split_ifs with hc
        · have h1 : m * (p.val / m) < m * (q + 1) := by
            have := c.isLt
            nlinarith
          exact Nat.lt_of_mul_lt_mul_left h1
        · have h1 : m * (p.val / m) < m * q := by linarith
          exact Nat.lt_of_mul_lt_mul_left h1
      · intro p1 h1 p2 h2 heq
        have m1 := (Finset.mem_filter.mp h1).2
        have m2 := (Finset.mem_filter.mp h2).2
        apply Fin.ext
        have e1 := Nat.div_add_mod p1.val m
        have e2 := Nat.div_add_mod p2.val m
        rw [← e1, ← e2, heq, m1, m2]
      · intro t ht
        rw [Finset.mem_range] at ht
        have hval : m * t + c.val < s := by
          dsimp only [n_c] at ht
          split_ifs at ht with hc
          · have : t ≤ q := by omega
            rcases Nat.eq_or_lt_of_le this with rfl | hlt
            · omega
            · have : m * (t + 1) ≤ m * q := Nat.mul_le_mul_left m hlt
              have := c.isLt
              nlinarith
          · have : m * (t + 1) ≤ m * q := Nat.mul_le_mul_left m ht
            have := c.isLt
            nlinarith
        refine ⟨⟨m * t + c.val, hval⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]
        · rw [Nat.mul_add_div hm, Nat.div_eq_of_lt c.isLt, add_zero]
    rw [hcard, Finset.card_range]
  have hsum_sq : ∑ c : Fin m, (cls c).card ^ 2 = m * q ^ 2 + 2 * rem * q + rem := by
    have h1 : ∑ c : Fin m, (cls c).card ^ 2 = ∑ c : Fin m, (q ^ 2 + if c.val < rem then 2 * q + 1 else 0) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hcls_card c]
      split_ifs <;> ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 : (∑ c : Fin m, if c.val < rem then 2 * q + 1 else 0) = rem * (2 * q + 1) := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      congr 1
      have hbij : (Finset.univ.filter (fun c : Fin m => c.val < rem)).card = (Finset.range rem).card := by
        refine Finset.card_bij (fun c _ => c.val) ?_ ?_ ?_
        · intro c hc; exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2
        · intro c1 _ c2 _ h; exact Fin.ext h
        · intro t ht
          exact ⟨⟨t, lt_trans (Finset.mem_range.mp ht) hrem_lt⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ht⟩, rfl⟩
      rw [hbij, Finset.card_range]
    rw [h2]
    ring
  have hZ : (4 * (2 * k) * s ^ 2 : ℤ) ≤ (2 * (2 * k + 1) * (4 * (turanPairs s k).card) + (2 * k + 1) ^ 2 : ℤ) := by
    have h1 : (2 * (turanPairs s k).card : ℤ) + ((m : ℤ) * (q : ℤ) ^ 2 + 2 * (rem : ℤ) * (q : ℤ) + (rem : ℤ)) = (s : ℤ) ^ 2 := by
      have := hord
      rw [hsum_sq] at this
      exact_mod_cast this
    have h2 : (s : ℤ) = (m : ℤ) * (q : ℤ) + (rem : ℤ) := by exact_mod_cast hs_eq
    have hm_eq : (m : ℤ) = 2 * (k : ℤ) + 1 := by omega
    have hsq : (0 : ℤ) ≤ ((m : ℤ) - 2 * (rem : ℤ)) ^ 2 := sq_nonneg _
    nlinarith only [h1, h2, hm_eq, hsq]
  exact_mod_cast hZ

lemma symp_quad_sum_eq (s k : ℕ) (col : Fin s → Fin (2 * k + 1)) (Pval : Fin s → ZMod 2) :
    (∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
      (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p')) +
    (∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p) =
    ∑ pp ∈ ((Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))).filter (fun pp => pp.1.val < pp.2.val),
      (∑ j : Fin k, (b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j) +
        b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j))) * (Pval pp.1 * Pval pp.2) := by
  let U : Finset (Fin s × Fin s) := (Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))
  let D : Finset (Fin s × Fin s) := U.filter (fun pp => pp.1 = pp.2)
  let LT : Finset (Fin s × Fin s) := U.filter (fun pp => pp.1.val < pp.2.val)
  let GT : Finset (Fin s × Fin s) := U.filter (fun pp => pp.2.val < pp.1.val)
  have h1 : ∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
      (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p') =
      ∑ pp ∈ U, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) * (Pval pp.1 * Pval pp.2) := by
    dsimp only [U]
    rw [Finset.sum_product]
    calc ∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
          (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p')
        = ∑ j : Fin k, ∑ p : Fin s, ∑ p' : Fin s,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p' _ => by ring
      _ = ∑ p : Fin s, ∑ j : Fin k, ∑ p' : Fin s,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') := Finset.sum_comm
      _ = ∑ p : Fin s, ∑ p' : Fin s, ∑ j : Fin k,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') :=
            Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ p : Fin s, ∑ p' : Fin s,
            (∑ j : Fin k, b2f (sympU k (col p) j) * b2f (sympV k (col p') j)) * (Pval p * Pval p') :=
            Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => (Finset.sum_mul _ _ _).symm
  have hpart : U = D ∪ (LT ∪ GT) := by
    ext pp
    simp only [U, D, LT, GT, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy pp.1.val pp.2.val with hlt | heq | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (Or.inr hgt)
    · intro _; trivial
  have hd1 : Disjoint D (LT ∪ GT) := by
    rw [Finset.disjoint_left]
    intro pp hD hLG
    have heq := (Finset.mem_filter.mp hD).2
    rcases Finset.mem_union.mp hLG with hL | hG
    · have := (Finset.mem_filter.mp hL).2; rw [heq] at this; omega
    · have := (Finset.mem_filter.mp hG).2; rw [heq] at this; omega
  have hd2 : Disjoint LT GT := by
    rw [Finset.disjoint_left]
    intro pp hL hG
    have := (Finset.mem_filter.mp hL).2
    have := (Finset.mem_filter.mp hG).2
    omega
  have hDsum : ∑ pp ∈ D, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) = ∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p := by
    refine Finset.sum_bij (fun pp _ => pp.1) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro pp1 h1 pp2 h2 heq
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      exact Prod.ext heq (by rw [← e1, ← e2, heq])
    · intro p _
      exact ⟨(p, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, rfl⟩
    · intro pp hpp
      have heq := (Finset.mem_filter.mp hpp).2
      rw [← heq, f2_mul_self, symp_diag_eq]
  have hGTsum : ∑ pp ∈ GT, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) =
      ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) := by
    refine Finset.sum_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_ ?_
    · intro pp hpp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hpp).2⟩
    · intro pp1 _ pp2 _ heq; ext <;> simp_all
    · intro pp hpp
      exact ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hpp).2⟩, by ext <;> rfl⟩
    · intro pp _
      rw [mul_comm (Pval pp.1)]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h1, hpart, Finset.sum_union hd1, Finset.sum_union hd2, hDsum, hGTsum]
  set Sdiag := ∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p
  set A := ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) * (Pval pp.1 * Pval pp.2)
  set B := ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j)) * (Pval pp.1 * Pval pp.2)
  have hcancel : Sdiag + (A + B) + Sdiag = A + B := by
    calc Sdiag + (A + B) + Sdiag = (Sdiag + Sdiag) + (A + B) := by ring
      _ = 0 + (A + B) := by rw [f2_add_self]
      _ = A + B := zero_add _
  rw [hcancel]
  simp only [A, B, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pp _ => ?_
  rw [← add_mul, ← Finset.sum_add_distrib]

lemma slot_pair_eval_eq (N s k : ℕ)
    (p1 p2 : Fin N → Fin s) (b1 b2 : Fin N → Bool)
    (hp_lt : ∀ x, (p1 x).val < (p2 x).val)
    (hp_col : ∀ x, (p1 x).val % (2 * k + 1) ≠ (p2 x).val % (2 * k + 1))
    (hinj : ∀ x y, p1 x = p1 y → p2 x = p2 y → b1 x = b1 y → b2 x = b2 y → x = y)
    (x y : Fin N) :
    let usesSlot : Fin N → Fin s → Bool → Bool := fun z p b =>
      (decide (p1 z = p) && decide (b1 z = b)) || (decide (p2 z = p) && decide (b2 z = b))
    let Pval : Fin s → ZMod 2 := fun p =>
      b2f (usesSlot x p false) * b2f (usesSlot y p false) +
      b2f (usesSlot x p true) * b2f (usesSlot y p true)
    let col : Fin s → Fin (2 * k + 1) := fun p => ⟨p.val % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
    ∑ pp ∈ ((Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))).filter (fun pp => pp.1.val < pp.2.val),
      (∑ j : Fin k, (b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j) +
        b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j))) * (Pval pp.1 * Pval pp.2) =
    b2f (decide (x = y)) := by
  intro usesSlot Pval col
  have hslot_disj : ∀ z p, b2f (usesSlot z p false) * b2f (usesSlot z p true) = 0 := by
    intro z p
    have hne : p1 z ≠ p2 z := fun heq => by have := hp_lt z; rw [heq] at this; omega
    by_cases h1 : p1 z = p
    · have h2 : p2 z ≠ p := fun heq => hne (h1.trans heq.symm)
      cases hb : b1 z <;> simp [usesSlot, h1, h2, hb, b2f]
    · by_cases h2 : p2 z = p
      · cases hb : b2 z <;> simp [usesSlot, h1, h2, hb, b2f]
      · simp [usesSlot, h1, h2, b2f]
  have hPval_iff : ∀ p : Fin s, Pval p = 1 ↔
      ((p = p1 x ∧ p = p1 y ∧ b1 x = b1 y) ∨
       (p = p1 x ∧ p = p2 y ∧ b1 x = b2 y) ∨
       (p = p2 x ∧ p = p1 y ∧ b2 x = b1 y) ∨
       (p = p2 x ∧ p = p2 y ∧ b2 x = b2 y)) := by
    intro p
    have hslot_eq : ∀ z b, usesSlot z p b = true ↔ (p1 z = p ∧ b1 z = b) ∨ (p2 z = p ∧ b2 z = b) := by
      intro z b; simp [usesSlot]
    have hP1 : Pval p = 1 ↔ (usesSlot x p false = true ∧ usesSlot y p false = true) ∨
        (usesSlot x p true = true ∧ usesSlot y p true = true) := by
      have hx0 := hslot_disj x p
      cases hxf : usesSlot x p false <;> cases hxt : usesSlot x p true <;>
        cases hyf : usesSlot y p false <;> cases hyt : usesSlot y p true <;>
        simp only [hxf, hxt, hyf, hyt, Pval, b2f] at hx0 ⊢ <;>
        first | exact absurd hx0 (by decide) | decide
    rw [hP1, hslot_eq x false, hslot_eq y false, hslot_eq x true, hslot_eq y true]
    constructor
    · rintro (⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩)
      · exact Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩
      · exact Or.inr (Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩))
      · exact Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩
      · exact Or.inr (Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1.1.symm, h2.1.symm, h1.2.trans h2.2.symm⟩))
    · rintro (⟨rfl, hpy, hb⟩ | ⟨rfl, hpy, hb⟩ | ⟨rfl, hpy, hb⟩ | ⟨rfl, hpy, hb⟩)
      · cases hb1 : b1 x
        · left; exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨hpy.symm, hb.symm.trans hb1⟩⟩
        · right; exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨hpy.symm, hb.symm.trans hb1⟩⟩
      · cases hb1 : b1 x
        · left; exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨hpy.symm, hb.symm.trans hb1⟩⟩
        · right; exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨hpy.symm, hb.symm.trans hb1⟩⟩
      · cases hb2 : b2 x
        · left; exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨hpy.symm, hb.symm.trans hb2⟩⟩
        · right; exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨hpy.symm, hb.symm.trans hb2⟩⟩
      · cases hb2 : b2 x
        · left; exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨hpy.symm, hb.symm.trans hb2⟩⟩
        · right; exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨hpy.symm, hb.symm.trans hb2⟩⟩
  have hProd : ∀ pp : Fin s × Fin s, pp.1.val < pp.2.val →
      (Pval pp.1 * Pval pp.2 = 1 ↔ x = y ∧ pp = (p1 x, p2 x)) := by
    intro pp hlt
    constructor
    · intro h1
      have hP1 : Pval pp.1 = 1 := by
        rcases f2_cases (Pval pp.1) with h0 | h1'
        · rw [h0, zero_mul] at h1; exact absurd h1 (by decide)
        · exact h1'
      have hP2 : Pval pp.2 = 1 := by
        rcases f2_cases (Pval pp.2) with h0 | h1'
        · rw [h0, mul_zero] at h1; exact absurd h1 (by decide)
        · exact h1'
      have c1 := (hPval_iff pp.1).mp hP1
      have c2 := (hPval_iff pp.2).mp hP2
      have hxlt := hp_lt x
      have hylt := hp_lt y
      have hpp1 : pp.1 = p1 x ∧ pp.1 = p1 y ∧ b1 x = b1 y := by
        rcases c1 with h | ⟨hp1, hpy, _⟩ | ⟨hp1, _, _⟩ | ⟨hp1, _, _⟩
        · exact h
        · exfalso
          rcases c2 with ⟨_, hpy2, _⟩ | ⟨_, hpy2, _⟩ | ⟨_, hpy2, _⟩ | ⟨_, hpy2, _⟩ <;>
            (rw [hpy, hpy2] at hlt; omega)
        · exfalso
          rcases c2 with ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ <;>
            (rw [hp1, hpx2] at hlt; omega)
        · exfalso
          rcases c2 with ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ <;>
            (rw [hp1, hpx2] at hlt; omega)
      have hpp2 : pp.2 = p2 x ∧ pp.2 = p2 y ∧ b2 x = b2 y := by
        rcases c2 with ⟨hpx2, _, _⟩ | ⟨hpx2, _, _⟩ | ⟨_, hpy2, _⟩ | h
        · exfalso; rw [hpp1.1, hpx2] at hlt; omega
        · exfalso; rw [hpp1.1, hpx2] at hlt; omega
        · exfalso; rw [hpp1.2.1, hpy2] at hlt; omega
        · exact h
      exact ⟨hinj x y (hpp1.1.symm.trans hpp1.2.1) (hpp2.1.symm.trans hpp2.2.1) hpp1.2.2 hpp2.2.2,
        Prod.ext hpp1.1 hpp2.1⟩
    · rintro ⟨rfl, rfl⟩
      have h1 : Pval (p1 x) = 1 := (hPval_iff (p1 x)).mpr (Or.inl ⟨rfl, rfl, rfl⟩)
      have h2 : Pval (p2 x) = 1 := (hPval_iff (p2 x)).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      rw [h1, h2, mul_one]
  by_cases hxy : x = y
  · subst hxy
    have hrhs : b2f (decide (x = x)) = 1 := by simp [b2f]
    rw [hrhs]
    have hmem : (p1 x, p2 x) ∈ ((Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))).filter
        (fun pp => pp.1.val < pp.2.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hp_lt x⟩
    rw [Finset.sum_eq_single (p1 x, p2 x)]
    · dsimp only
      have hprod1 : Pval (p1 x) * Pval (p2 x) = 1 := (hProd (p1 x, p2 x) (hp_lt x)).mpr ⟨rfl, rfl⟩
      have hcolne : col (p1 x) ≠ col (p2 x) := fun h => hp_col x (congrArg Fin.val h)
      rw [hprod1, mul_one, symp_omega_ne k (col (p1 x)) (col (p2 x)) hcolne]
    · intro pp hpp hne
      have hlt := (Finset.mem_filter.mp hpp).2
      have h0 : Pval pp.1 * Pval pp.2 = 0 := by
        rcases f2_cases (Pval pp.1 * Pval pp.2) with h0 | h1
        · exact h0
        · exfalso; exact hne ((hProd pp hlt).mp h1).2
      rw [h0, mul_zero]
    · intro hnot; exact absurd hmem hnot
  · simp only [hxy, decide_false, b2f, Bool.false_eq_true, ↓reduceIte]
    refine Finset.sum_eq_zero fun pp hpp => ?_
    have hlt := (Finset.mem_filter.mp hpp).2
    have h0 : Pval pp.1 * Pval pp.2 = 0 := by
      rcases f2_cases (Pval pp.1 * Pval pp.2) with h0 | h1
      · exact h0
      · exfalso; exact hxy ((hProd pp hlt).mp h1).1
    rw [h0, mul_zero]

lemma upper_bound_4T (N s k : ℕ) (hN : N ≤ 4 * (turanPairs s k).card) :
    ∃ C : Circuit, ReadsBack (N + N) C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ s + k ∧ (depths (N + N) C).getD C.output 0 ≤ 2 ∧
      Represents (fun (x y : Fin N) => decide (x = y)) C := by
  classical
  let EType := { pp : Fin s × Fin s // pp ∈ turanPairs s k }
  let LType := EType × Bool × Bool
  have hcardL : Fintype.card LType = 4 * (turanPairs s k).card := by
    simp only [LType, EType, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
    ring
  let eL : Fin (4 * (turanPairs s k).card) ≃ LType := (Fintype.equivFinOfCardEq hcardL).symm
  let lbl : Fin N → LType := fun x => eL ⟨x.val, lt_of_lt_of_le x.isLt hN⟩
  have hlbl_inj : Function.Injective lbl := by
    intro x1 x2 heq
    have h1 : (⟨x1.val, lt_of_lt_of_le x1.isLt hN⟩ : Fin (4 * (turanPairs s k).card)) =
        ⟨x2.val, lt_of_lt_of_le x2.isLt hN⟩ := eL.injective heq
    exact Fin.ext (Fin.mk.inj h1)
  let p1 : Fin N → Fin s := fun x => (lbl x).1.val.1
  let p2 : Fin N → Fin s := fun x => (lbl x).1.val.2
  let b1 : Fin N → Bool := fun x => (lbl x).2.1
  let b2 : Fin N → Bool := fun x => (lbl x).2.2
  have hp_lt : ∀ x : Fin N, (p1 x).val < (p2 x).val := fun x =>
    (Finset.mem_filter.mp (lbl x).1.property).2.1
  have hp_col : ∀ x : Fin N, (p1 x).val % (2 * k + 1) ≠ (p2 x).val % (2 * k + 1) := fun x =>
    (Finset.mem_filter.mp (lbl x).1.property).2.2
  have hpinj : ∀ x y, p1 x = p1 y → p2 x = p2 y → b1 x = b1 y → b2 x = b2 y → x = y := by
    intro x y h1 h2 h3 h4
    apply hlbl_inj
    exact Prod.ext (Subtype.ext (Prod.ext h1 h2)) (Prod.ext h3 h4)
  let usesSlot : Fin N → Fin s → Bool → Bool := fun x p b =>
    (decide (p1 x = p) && decide (b1 x = b)) || (decide (p2 x = p) && decide (b2 x = b))
  have hslot_disj : ∀ x p, b2f (usesSlot x p false) * b2f (usesSlot x p true) = 0 := by
    intro x p
    have hne : p1 x ≠ p2 x := fun heq => by have := hp_lt x; rw [heq] at this; omega
    by_cases h1 : p1 x = p
    · have h2 : p2 x ≠ p := fun heq => hne (h1.trans heq.symm)
      cases hb : b1 x <;> simp [usesSlot, h1, h2, hb, b2f]
    · by_cases h2 : p2 x = p
      · cases hb : b2 x <;> simp [usesSlot, h1, h2, hb, b2f]
      · simp [usesSlot, h1, h2, b2f]
  let w := N + N
  let B0 := Builder.empty w
  let wsL : Fin s → List ℕ := fun p =>
    ((List.finRange N).filter (fun x => usesSlot x p false)).map (fun x => x.val) ++
    ((List.finRange N).filter (fun y => usesSlot y p true)).map (fun y => N + y.val)
  let wsR : Fin s → List ℕ := fun p =>
    ((List.finRange N).filter (fun x => usesSlot x p true)).map (fun x => x.val) ++
    ((List.finRange N).filter (fun y => usesSlot y p false)).map (fun y => N + y.val)
  have hwsL : ∀ p i, i ∈ wsL p → i < w + B0.gates.length := by
    intro p i hi
    simp only [wsL, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩ <;> simp [B0, Builder.empty, w] <;> omega
  have hwsR : ∀ p i, i ∈ wsR p → i < w + B0.gates.length := by
    intro p i hi
    simp only [wsR, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩ <;> simp [B0, Builder.empty, w] <;> omega
  let rL := pushManyXor B0 s wsL hwsL
  let rR := pushManyXor rL.val.1 s wsR (fun p i hi =>
    lt_of_lt_of_le (hwsR p i hi) (Nat.add_le_add_left rL.property.1 w))
  let rP := pushManyAnd rR.val.1 s rL.val.2 rR.val.2
    (fun p => lt_of_lt_of_le (rL.property.2.1 p) (Nat.add_le_add_left rR.property.1 w))
    rR.property.2.1
  let col : Fin s → Fin (2 * k + 1) := fun p => ⟨p.val % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
  let wsU : Fin k → List ℕ := fun j =>
    ((List.finRange s).filter (fun p => sympU k (col p) j)).map rP.val.2
  let wsV : Fin k → List ℕ := fun j =>
    ((List.finRange s).filter (fun p => sympV k (col p) j)).map rP.val.2
  have hwsU : ∀ j i, i ∈ wsU j → i < w + rP.val.1.gates.length := by
    intro j i hi
    rcases List.mem_map.mp hi with ⟨p, _, rfl⟩
    exact rP.property.2.1 p
  have hwsV : ∀ j i, i ∈ wsV j → i < w + rP.val.1.gates.length := by
    intro j i hi
    rcases List.mem_map.mp hi with ⟨p, _, rfl⟩
    exact rP.property.2.1 p
  let rU := pushManyXor rP.val.1 k wsU hwsU
  let rV := pushManyXor rU.val.1 k wsV (fun j i hi =>
    lt_of_lt_of_le (hwsV j i hi) (Nat.add_le_add_left rU.property.1 w))
  let rQ := pushManyAnd rV.val.1 k rU.val.2 rV.val.2
    (fun j => lt_of_lt_of_le (rU.property.2.1 j) (Nat.add_le_add_left rV.property.1 w))
    rV.property.2.1
  let wsOut : List ℕ :=
    ((List.finRange k).map rQ.val.2) ++
    (((List.finRange s).filter (fun p => sympDiag k (col p))).map rP.val.2)
  have hP_lt_Q : ∀ p : Fin s, rP.val.2 p < w + rQ.val.1.gates.length := by
    intro p
    have h1 := rP.property.2.1 p
    have h2 := rU.property.1
    have h3 := rV.property.1
    have h4 := rQ.property.1
    omega
  have hwsOut : ∀ i ∈ wsOut, i < w + rQ.val.1.gates.length := by
    intro i hi
    simp only [wsOut, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨j, _, rfl⟩ | ⟨p, _, rfl⟩
    · exact rQ.property.2.1 j
    · exact hP_lt_Q p
  let rOut := rQ.val.1.pushXorList wsOut hwsOut
  have hdB0 : ∀ i < w, (B0.depths).getD i 0 ≤ 0 := by
    intro i hi
    simp [B0, Builder.empty, Builder.depths, List.getD_eq_getElem?_getD, hi]
  have hdL : ∀ p, (rL.val.1.depths).getD (rL.val.2 p) 0 ≤ 0 :=
    rL.property.2.2.2.1 0 (fun p i hi => hdB0 i (by have := hwsL p i hi; simp [B0, Builder.empty] at this; exact this))
  have hdR : ∀ p, (rR.val.1.depths).getD (rR.val.2 p) 0 ≤ 0 := by
    refine rR.property.2.2.2.1 0 (fun p i hi => ?_)
    have hi0 : i < w := by have := hwsR p i hi; simp [B0, Builder.empty] at this; exact this
    rw [rL.property.2.2.2.2.1 i (by simp [B0, Builder.empty]; exact hi0)]
    exact hdB0 i hi0
  have hdP : ∀ p, (rP.val.1.depths).getD (rP.val.2 p) 0 ≤ 1 := by
    refine rP.property.2.2.2.1 0 (fun p => ?_) hdR
    rw [rR.property.2.2.2.2.1 (rL.val.2 p) (rL.property.2.1 p)]
    exact hdL p
  have hdU : ∀ j, (rU.val.1.depths).getD (rU.val.2 j) 0 ≤ 1 := by
    refine rU.property.2.2.2.1 1 (fun j i hi => ?_)
    rcases List.mem_map.mp hi with ⟨p, _, rfl⟩
    exact hdP p
  have hdV : ∀ j, (rV.val.1.depths).getD (rV.val.2 j) 0 ≤ 1 := by
    refine rV.property.2.2.2.1 1 (fun j i hi => ?_)
    rcases List.mem_map.mp hi with ⟨p, _, rfl⟩
    rw [rU.property.2.2.2.2.1 (rP.val.2 p) (rP.property.2.1 p)]
    exact hdP p
  have hdQ : ∀ j, (rQ.val.1.depths).getD (rQ.val.2 j) 0 ≤ 2 := by
    refine rQ.property.2.2.2.1 1 (fun j => ?_) hdV
    rw [rV.property.2.2.2.2.1 (rU.val.2 j) (rU.property.2.1 j)]
    exact hdU j
  have hdP_in_Q : ∀ p, (rQ.val.1.depths).getD (rP.val.2 p) 0 ≤ 2 := by
    intro p
    have h1 := rP.property.2.1 p
    have h2 := rU.property.1
    have h3 := rV.property.1
    rw [rQ.property.2.2.2.2.1 (rP.val.2 p) (by omega),
      rV.property.2.2.2.2.1 (rP.val.2 p) (by omega),
      rU.property.2.2.2.2.1 (rP.val.2 p) h1]
    exact le_trans (hdP p) (by omega)
  have hspOut := pushXorList_spec rQ.val.1 wsOut hwsOut 2 (by
    intro i hi
    simp only [wsOut, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨j, _, rfl⟩ | ⟨p, _, rfl⟩
    · exact hdQ j
    · exact hdP_in_Q p)
  let C : Circuit := ⟨rOut.1.gates, rOut.2⟩
  refine ⟨C, rOut.1.hRB, rOut.1.hFan, ?_, hspOut.2.2.2.1, ?_⟩
  · change rOut.1.nlCount ≤ s + k
    rw [hspOut.2.2.1, rQ.property.2.2.1, rV.property.2.2.1, rU.property.2.2.1,
      rP.property.2.2.1, rR.property.2.2.1, rL.property.2.2.1]
    simp [B0, Builder.empty, Builder.nlCount]
  · intro x y
    apply b2f_injective
    have hxlen : (oneEach x y).length = w := oneEach_length x y
    have hB0L : ∀ i : Fin N, b2f ((B0.wires (oneEach x y)).getD i.val false) = b2f (decide (i = x)) := by
      intro i
      simp only [B0, Builder.empty, Builder.wires, List.foldl_nil]
      rw [oneEach_getD_left x y i.val i.isLt]
    have hB0R : ∀ j : Fin N, b2f ((B0.wires (oneEach x y)).getD (N + j.val) false) = b2f (decide (j = y)) := by
      intro j
      simp only [B0, Builder.empty, Builder.wires, List.foldl_nil]
      rw [oneEach_getD_right x y j.val j.isLt]
    have hLval : ∀ p : Fin s, b2f ((rL.val.1.wires (oneEach x y)).getD (rL.val.2 p) false) =
        b2f (usesSlot x p false) + b2f (usesSlot y p true) := by
      intro p
      rw [(rL.property.2.2.2.2.2 (oneEach x y) hxlen).2 p]
      simp only [wsL, List.map_append, List.sum_append, List.map_map]
      rw [list_sum_filter_finRange, list_sum_filter_finRange]
      have h1 : (∑ a : Fin N, if usesSlot a p false = true then
          ((fun w_1 => b2f ((B0.wires (oneEach x y)).getD w_1 false)) ∘ Fin.val) a else 0) =
          b2f (usesSlot x p false) := by
        have hcongr : ∀ a : Fin N, (if usesSlot a p false = true then
            ((fun w_1 => b2f ((B0.wires (oneEach x y)).getD w_1 false)) ∘ Fin.val) a else 0) =
            if a = x then b2f (usesSlot x p false) else 0 := by
          intro a
          simp only [Function.comp_apply, hB0L a]
          by_cases hax : a = x
          · subst hax; cases usesSlot a p false <;> simp [b2f]
          · cases usesSlot a p false <;> simp [hax, b2f]
        simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h2 : (∑ a : Fin N, if usesSlot a p true = true then
          ((fun w_1 => b2f ((B0.wires (oneEach x y)).getD w_1 false)) ∘ (fun y : Fin N => N + y.val)) a else 0) =
          b2f (usesSlot y p true) := by
        have hcongr : ∀ a : Fin N, (if usesSlot a p true = true then
            ((fun w_1 => b2f ((B0.wires (oneEach x y)).getD w_1 false)) ∘ (fun y : Fin N => N + y.val)) a else 0) =
            if a = y then b2f (usesSlot y p true) else 0 := by
          intro a
          simp only [Function.comp_apply, hB0R a]
          by_cases hay : a = y
          · subst hay; cases usesSlot a p true <;> simp [b2f]
          · cases usesSlot a p true <;> simp [hay, b2f]
        simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [h1, h2]
    have hRval : ∀ p : Fin s, b2f ((rR.val.1.wires (oneEach x y)).getD (rR.val.2 p) false) =
        b2f (usesSlot x p true) + b2f (usesSlot y p false) := by
      intro p
      rw [(rR.property.2.2.2.2.2 (oneEach x y) hxlen).2 p]
      have hOldL := (rL.property.2.2.2.2.2 (oneEach x y) hxlen).1
      simp only [wsR, List.map_append, List.sum_append, List.map_map]
      rw [list_sum_filter_finRange, list_sum_filter_finRange]
      have h1 : (∑ a : Fin N, if usesSlot a p true = true then
          ((fun w_1 => b2f ((rL.val.1.wires (oneEach x y)).getD w_1 false)) ∘ Fin.val) a else 0) =
          b2f (usesSlot x p true) := by
        have hcongr : ∀ a : Fin N, (if usesSlot a p true = true then
            ((fun w_1 => b2f ((rL.val.1.wires (oneEach x y)).getD w_1 false)) ∘ Fin.val) a else 0) =
            if a = x then b2f (usesSlot x p true) else 0 := by
          intro a
          simp only [Function.comp_apply]
          rw [hOldL a.val (by have := a.isLt; simp [B0, Builder.empty, w]; omega), hB0L a]
          by_cases hax : a = x
          · subst hax; cases usesSlot a p true <;> simp [b2f]
          · cases usesSlot a p true <;> simp [hax, b2f]
        simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h2 : (∑ a : Fin N, if usesSlot a p false = true then
          ((fun w_1 => b2f ((rL.val.1.wires (oneEach x y)).getD w_1 false)) ∘ (fun y : Fin N => N + y.val)) a else 0) =
          b2f (usesSlot y p false) := by
        have hcongr : ∀ a : Fin N, (if usesSlot a p false = true then
            ((fun w_1 => b2f ((rL.val.1.wires (oneEach x y)).getD w_1 false)) ∘ (fun y : Fin N => N + y.val)) a else 0) =
            if a = y then b2f (usesSlot y p false) else 0 := by
          intro a
          simp only [Function.comp_apply]
          rw [hOldL (N + a.val) (by simp [B0, Builder.empty, w]), hB0R a]
          by_cases hay : a = y
          · subst hay; cases usesSlot a p false <;> simp [b2f]
          · cases usesSlot a p false <;> simp [hay, b2f]
        simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [h1, h2]
    let Pval : Fin s → ZMod 2 := fun p =>
      b2f (usesSlot x p false) * b2f (usesSlot y p false) +
      b2f (usesSlot x p true) * b2f (usesSlot y p true)
    have hPval : ∀ p : Fin s, b2f ((rP.val.1.wires (oneEach x y)).getD (rP.val.2 p) false) = Pval p := by
      intro p
      rw [(rP.property.2.2.2.2.2 (oneEach x y) hxlen).2 p]
      rw [(rR.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rL.val.2 p) (rL.property.2.1 p)]
      rw [hLval p, hRval p]
      have hx0 := hslot_disj x p
      have hy0 := hslot_disj y p
      calc (b2f (usesSlot x p false) + b2f (usesSlot y p true)) *
            (b2f (usesSlot x p true) + b2f (usesSlot y p false))
          = b2f (usesSlot x p false) * b2f (usesSlot x p true) +
            b2f (usesSlot y p false) * b2f (usesSlot y p true) + Pval p := by simp only [Pval]; ring
        _ = 0 + 0 + Pval p := by rw [hx0, hy0]
        _ = Pval p := by ring
    have hUval : ∀ j : Fin k, b2f ((rU.val.1.wires (oneEach x y)).getD (rU.val.2 j) false) =
        ∑ p : Fin s, b2f (sympU k (col p) j) * Pval p := by
      intro j
      rw [(rU.property.2.2.2.2.2 (oneEach x y) hxlen).2 j]
      simp only [wsU, List.map_map]
      rw [list_sum_filter_finRange]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Function.comp_apply, hPval p]
      cases sympU k (col p) j <;> simp [b2f]
    have hVval : ∀ j : Fin k, b2f ((rV.val.1.wires (oneEach x y)).getD (rV.val.2 j) false) =
        ∑ p : Fin s, b2f (sympV k (col p) j) * Pval p := by
      intro j
      rw [(rV.property.2.2.2.2.2 (oneEach x y) hxlen).2 j]
      simp only [wsV, List.map_map]
      rw [list_sum_filter_finRange]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Function.comp_apply]
      rw [(rU.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rP.val.2 p) (rP.property.2.1 p), hPval p]
      cases sympV k (col p) j <;> simp [b2f]
    have hQval : ∀ j : Fin k, b2f ((rQ.val.1.wires (oneEach x y)).getD (rQ.val.2 j) false) =
        (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) * (∑ p : Fin s, b2f (sympV k (col p) j) * Pval p) := by
      intro j
      rw [(rQ.property.2.2.2.2.2 (oneEach x y) hxlen).2 j]
      rw [(rV.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rU.val.2 j) (rU.property.2.1 j)]
      rw [hUval j, hVval j]
    have hPval_in_Q : ∀ p : Fin s, b2f ((rQ.val.1.wires (oneEach x y)).getD (rP.val.2 p) false) = Pval p := by
      intro p
      have h1 := rP.property.2.1 p
      have h2 := rU.property.1
      have h3 := rV.property.1
      rw [(rQ.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rP.val.2 p) (by omega),
        (rV.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rP.val.2 p) (by omega),
        (rU.property.2.2.2.2.2 (oneEach x y) hxlen).1 (rP.val.2 p) h1, hPval p]
    have hOutVal : b2f (C.eval (oneEach x y)) =
        (∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
          (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p')) +
        (∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p) := by
      change b2f ((rOut.1.wires (oneEach x y)).getD rOut.2 false) = _
      rw [(hspOut.2.2.2.2.2 (oneEach x y) hxlen).2]
      simp only [wsOut, List.map_append, List.sum_append, List.map_map]
      congr 1
      · rw [list_sum_finRange_eq]
        exact Finset.sum_congr rfl fun j _ => hQval j
      · rw [list_sum_filter_finRange]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Function.comp_apply, hPval_in_Q p]
        cases sympDiag k (col p) <;> simp [b2f]
    rw [hOutVal, symp_quad_sum_eq s k col Pval]
    exact slot_pair_eval_eq N s k p1 p2 b1 b2 hp_lt hp_col hpinj x y

lemma lb_real_step (r sr u k : ℝ) (hr7 : 7 ≤ r) (hsr_sq : sr ^ 2 = r) (hsr_nn : 0 ≤ sr)
    (hk1 : 1 ≤ k) (hu_nn : 0 ≤ u)
    (hMain : (2 * k + 1) * r ^ 2 ≤ 2 * k * u ^ 2 + k * (2 * k + 1)) :
    r + sr - 8 ≤ u + k := by
  by_contra hlt
  have hsr2 : (2 : ℝ) ≤ sr := by nlinarith only [hr7, hsr_sq, hsr_nn]
  have hu_lt : u < r + sr - 8 - k := by linarith only [hlt]
  by_cases hkbig : 2 * sr ≤ k
  · have hu_le : u ≤ r - sr - 8 := by linarith only [hu_lt, hkbig]
    have hk_le : k ≤ r + sr - 8 := by linarith only [hu_lt, hu_nn]
    have hu_sq : u ^ 2 ≤ (r - sr - 8) ^ 2 := by nlinarith only [hu_nn, hu_le]
    have hdrop : (2 * k + 1) * r ^ 2 ≤ (2 * k + 1) * (u ^ 2 + k) := by nlinarith only [hMain, hu_nn]
    have hru : r ^ 2 ≤ u ^ 2 + k := by nlinarith only [hdrop, hk1]
    have hcontr : (r - sr - 8) ^ 2 + (r + sr - 8) < r ^ 2 := by
      have : r ^ 2 - ((r - sr - 8) ^ 2 + (r + sr - 8)) = (2 * sr + 15) * r - (r + 17 * sr + 56) := by
        nlinarith only [hsr_sq]
      nlinarith only [this, hr7, hsr2, hsr_sq]
    linarith only [hru, hu_sq, hk_le, hcontr]
  · set x : ℝ := sr - 3 - k
    have hux : u < r + x := by linarith only [hu_lt]
    have hu_sq : u ^ 2 < (r + x) ^ 2 := by nlinarith only [hu_nn, hux]
    have hstep : (2 * k + 1) * r ^ 2 < 2 * k * (r + x) ^ 2 + k * (2 * k + 1) := by
      nlinarith only [hMain, hu_sq, hk1]
    have hexp : 2 * k * (r + x) ^ 2 + k * (2 * k + 1) - (2 * k + 1) * r ^ 2 =
        - r * (sr - 2 * k) ^ 2 - 12 * k * r + 2 * k * x ^ 2 + 2 * k ^ 2 + k := by
      have hr2 : r ^ 2 = r * sr ^ 2 := by rw [hsr_sq]; ring
      have h1 : x = sr - 3 - k := rfl
      nlinarith only [hr2, h1]
    have hx_lo : -(sr + 3) ≤ x := by linarith only [hkbig]
    have hx_hi : x ≤ sr + 3 := by linarith only [hk1]
    have hx_sq : x ^ 2 ≤ r + 6 * sr + 9 := by nlinarith only [hx_lo, hx_hi, hsr_sq]
    have hsq_nn : 0 ≤ r * (sr - 2 * k) ^ 2 := mul_nonneg (by linarith only [hr7]) (sq_nonneg _)
    have h2kx : 2 * k * x ^ 2 ≤ 2 * k * (r + 6 * sr + 9) := by nlinarith only [hx_sq, hk1]
    have h2k2 : 2 * k ^ 2 ≤ 4 * k * sr := by nlinarith only [hkbig, hk1]
    have hsr_le : 5 * sr ≤ 2 * r := by nlinarith only [hr7, hsr_sq, hsr_nn]
    have htail : -10 * r + 16 * sr + 19 ≤ 0 := by linarith only [hr7, hsr_le]
    have hktail : k * (-10 * r + 16 * sr + 19) ≤ 0 := by nlinarith only [htail, hk1]
    linarith only [hstep, hexp, hsq_nn, h2kx, h2k2, hktail]

lemma lb_real (N s k E : ℕ) (hN : 0 < N)
    (hRank : N ≤ 2 + 2 * k + 4 * s + 4 * E)
    (hTuran : (2 * k + 1) * (2 * E) ≤ 2 * k * s ^ 2) :
    let r := Real.sqrt ((N : ℝ) / 2)
    r + Real.sqrt r - 10 ≤ ((s + k : ℕ) : ℝ) := by
  intro r
  have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
  have hsr_nn : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = (N : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hsr_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr_nn
  by_cases hr7 : r < 7
  · have hsr3 : Real.sqrt r < 3 := by nlinarith only [hr7, hsr_sq, hsr_nn]
    have hsk_nn : (0 : ℝ) ≤ ((s + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hr7, hsr3, hsk_nn]
  · have hr7' : 7 ≤ r := le_of_not_gt hr7
    have hRankR : (N : ℝ) ≤ 2 + 2 * (k : ℝ) + 4 * (s : ℝ) + 4 * (E : ℝ) := by exact_mod_cast hRank
    have hTuranR : (2 * (k : ℝ) + 1) * (2 * (E : ℝ)) ≤ 2 * (k : ℝ) * (s : ℝ) ^ 2 := by exact_mod_cast hTuran
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, add_zero] at hRankR hTuranR ⊢
      have hEnn : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg E
      have hE0 : (E : ℝ) = 0 := by linarith only [hTuranR, hEnn]
      have hsr_le : Real.sqrt r ≤ r / 2 := by nlinarith only [hr7', hsr_sq, hsr_nn]
      nlinarith only [hr_sq, hRankR, hE0, hr7', hsr_le]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0)
      have hs_nn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      set u : ℝ := (s : ℝ) + 2
      have hMain : (2 * (k : ℝ) + 1) * r ^ 2 ≤ 2 * (k : ℝ) * u ^ 2 + (k : ℝ) * (2 * (k : ℝ) + 1) := by
        have h1 : (2 * (k : ℝ) + 1) * (2 * r ^ 2) ≤
            (2 * (k : ℝ) + 1) * (2 + 2 * (k : ℝ) + 4 * (s : ℝ)) + 4 * (k : ℝ) * (s : ℝ) ^ 2 := by
          have hE4 : (2 * (k : ℝ) + 1) * (4 * (E : ℝ)) ≤ 4 * (k : ℝ) * (s : ℝ) ^ 2 := by linarith only [hTuranR]
          nlinarith only [hr_sq, hRankR, hE4, hk1]
        have h2 : (2 * (k : ℝ) + 1) * (2 + 4 * (s : ℝ)) ≤ 4 * (k : ℝ) * (4 * (s : ℝ) + 4) := by
          nlinarith only [hk1, hs_nn]
        have h3 : 4 * (k : ℝ) * u ^ 2 = 4 * (k : ℝ) * (s : ℝ) ^ 2 + 4 * (k : ℝ) * (4 * (s : ℝ) + 4) := by
          simp only [u]; ring
        linarith only [h1, h2, h3]
      have hstep := lb_real_step r (Real.sqrt r) u (k : ℝ) hr7' hsr_sq hsr_nn hk1 (by linarith only [hs_nn]) hMain
      push_cast
      linarith only [hstep]

lemma ub_real (N : ℕ) (hN : 0 < N) :
    let r := Real.sqrt ((N : ℝ) / 2)
    ∃ t : ℕ, (∃ C : Circuit, ReadsBack (N + N) C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ t ∧ (depths (N + N) C).getD C.output 0 ≤ 2 ∧
      Represents (fun (x y : Fin N) => decide (x = y)) C) ∧
      (t : ℝ) ≤ r + Real.sqrt r + 10 := by
  intro r
  have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
  have hsr_nn : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = (N : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hsr_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr_nn
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨1, upper_bound_naive 1, ?_⟩
    push_cast
    linarith only [hr_nn, hsr_nn]
  · have hN2 : 2 ≤ N := by omega
    have hNR2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hr1 : 1 ≤ r := by nlinarith only [hr_sq, hNR2, hr_nn]
    have hsr1 : 1 ≤ Real.sqrt r := by nlinarith only [hsr_sq, hr1, hsr_nn]
    have hsr_le_r : Real.sqrt r ≤ r := by nlinarith only [hsr_sq, hsr1]
    set k : ℕ := Nat.ceil (Real.sqrt r / 2)
    have hk_ge : Real.sqrt r / 2 ≤ (k : ℝ) := Nat.le_ceil _
    have hk_lt : (k : ℝ) < Real.sqrt r / 2 + 1 := Nat.ceil_lt_add_one (by linarith only [hsr_nn])
    have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith only [hk_ge, hsr1]
    have hdiv_nn : 0 ≤ r / (4 * (k : ℝ)) := div_nonneg hr_nn (by linarith only [hk_pos])
    set s : ℕ := Nat.ceil (r + r / (4 * (k : ℝ)) + 2)
    have hs_ge : r + r / (4 * (k : ℝ)) + 2 ≤ (s : ℝ) := Nat.le_ceil _
    have hs_lt : (s : ℝ) < r + r / (4 * (k : ℝ)) + 3 := by
      have h1 := Nat.ceil_lt_add_one (by linarith only [hr_nn, hdiv_nn] : 0 ≤ r + r / (4 * (k : ℝ)) + 2)
      linarith only [h1]
    have h4T_ge : N ≤ 4 * (turanPairs s k).card := by
      have hT := turanPairs_card_bound s k
      have hTR : (4 * (2 * (k : ℝ)) * (s : ℝ) ^ 2 : ℝ) ≤
          2 * (2 * (k : ℝ) + 1) * (4 * ((turanPairs s k).card : ℝ)) + (2 * (k : ℝ) + 1) ^ 2 := by
        exact_mod_cast hT
      have hs_sq : r ^ 2 + r ^ 2 / (2 * (k : ℝ)) + 4 * r + 4 ≤ (s : ℝ) ^ 2 := by
        have h1 : (r + r / (4 * (k : ℝ)) + 2) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith only [hs_ge, hr_nn, hdiv_nn]
        have h2 : (r + r / (4 * (k : ℝ)) + 2) ^ 2 =
            r ^ 2 + r ^ 2 / (2 * (k : ℝ)) + 4 * r + 4 + (r / (4 * (k : ℝ))) ^ 2 + r / (k : ℝ) := by
          field_simp
          ring
        have h3 : 0 ≤ (r / (4 * (k : ℝ))) ^ 2 := sq_nonneg _
        have h4 : 0 ≤ r / (k : ℝ) := div_nonneg hr_nn (le_of_lt hk_pos)
        linarith only [h1, h2, h3, h4]
      have h4k_mul : 4 * (k : ℝ) * (r ^ 2 / (2 * (k : ℝ))) = 2 * r ^ 2 := by
        field_simp
        ring
      have hLHS : 4 * (k : ℝ) * r ^ 2 + 2 * r ^ 2 + 16 * (k : ℝ) * r + 16 * (k : ℝ) ≤
          4 * (k : ℝ) * (s : ℝ) ^ 2 := by
        have h1 : 4 * (k : ℝ) * (r ^ 2 + r ^ 2 / (2 * (k : ℝ)) + 4 * r + 4) ≤ 4 * (k : ℝ) * (s : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hs_sq (by linarith only [hk_pos])
        linarith only [h1, h4k_mul]
      have hk_le : (k : ℝ) ≤ r + 1 := by linarith only [hk_lt, hsr_le_r, hsr_nn]
      have hk_half : (1 : ℝ) / 2 ≤ (k : ℝ) := by linarith only [hk_ge, hsr1]
      have h2k_sq : 2 * (k : ℝ) ^ 2 ≤ 2 * (k : ℝ) * (r + 1) := by nlinarith only [hk_le, hk_pos]
      have hNR : (N : ℝ) ≤ 4 * ((turanPairs s k).card : ℝ) := by
        have hN_eq : (N : ℝ) = 2 * r ^ 2 := by linarith only [hr_sq]
        have hneed : (2 * (k : ℝ) + 1) * (2 * (2 * r ^ 2)) + (2 * (k : ℝ) + 1) ^ 2 ≤
            4 * (2 * (k : ℝ)) * (s : ℝ) ^ 2 := by
          nlinarith only [hLHS, h2k_sq, hk_half, hr1]
        have hcmp : 2 * (2 * (k : ℝ) + 1) * (N : ℝ) ≤ 2 * (2 * (k : ℝ) + 1) * (4 * ((turanPairs s k).card : ℝ)) := by
          rw [hN_eq]
          linarith only [hTR, hneed]
        nlinarith only [hcmp, hk_pos]
      exact_mod_cast hNR
    have hsum_le : ((s + k : ℕ) : ℝ) ≤ r + Real.sqrt r + 10 := by
      have hrdiv : r / (4 * (k : ℝ)) ≤ Real.sqrt r / 2 := by
        rw [div_le_div_iff₀ (by linarith only [hk_pos]) (by norm_num)]
        nlinarith only [hk_ge, hsr_sq, hsr_nn]
      push_cast
      linarith only [hs_lt, hk_lt, hrdiv]
    exact ⟨s + k, upper_bound_4T N s k h4T_ge, hsum_le⟩

end PEqualNP.Outside.L_meta_33681_aux

theorem PEqualNP.Outside.L_meta_33681 :
    (let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    ∀ N : ℕ, 0 < N →
      let possible := fun t : ℕ => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
        (depths (N+N) C).getD C.output 0 ≤ 2 ∧
        PEqualNP.Represents.Represents (fun (x y : Fin N) => decide (x = y)) C
      let r := Real.sqrt ((N : ℝ) / 2)
      ∃ t : ℕ, IsLeast {u : ℕ | possible u} t ∧ |(t : ℝ) - (r + Real.sqrt r)| ≤ 10) := by
  classical
  dsimp only
  intro N hN
  set r := Real.sqrt ((N : ℝ) / 2)
  let possible : ℕ → Prop := fun t => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    C.gates.countP PEqualNP.Outside.L_meta_33681_aux.nonlinear ≤ t ∧
    (PEqualNP.Outside.L_meta_33681_aux.depths (N + N) C).getD C.output 0 ≤ 2 ∧
    PEqualNP.Represents.Represents (fun (x y : Fin N) => decide (x = y)) C
  obtain ⟨u0, hu0_pos, hu0_ub⟩ := PEqualNP.Outside.L_meta_33681_aux.ub_real N hN
  have hex : ∃ u : ℕ, possible u := ⟨u0, hu0_pos⟩
  let t := Nat.find hex
  have ht_pos : possible t := Nat.find_spec hex
  have ht_min : ∀ u : ℕ, possible u → t ≤ u := fun u hu => Nat.find_min' hex hu
  have ht_ub : (t : ℝ) ≤ r + Real.sqrt r + 10 := by
    have htu : (t : ℝ) ≤ (u0 : ℝ) := by exact_mod_cast ht_min u0 hu0_pos
    linarith only [htu, hu0_ub]
  have ht_lb : r + Real.sqrt r - 10 ≤ (t : ℝ) := by
    rcases ht_pos with ⟨C, hRB, hFan, hCount, hDepth, hRep⟩
    obtain ⟨s, k, E, hsk, hRank, hTuran⟩ :=
      PEqualNP.Outside.L_meta_33681_aux.circuit_two_phase_bound N t hN C hRB hFan hCount hDepth hRep
    have h1 := PEqualNP.Outside.L_meta_33681_aux.lb_real N s k E hN hRank hTuran
    have h2 : ((s + k : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hsk
    linarith only [h1, h2]
  refine ⟨t, ⟨ht_pos, fun u hu => ht_min u hu⟩, ?_⟩
  rw [abs_le]
  constructor <;> linarith only [ht_ub, ht_lb]
