import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_lib_1345

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run_nil]
  | cons g gs ih => intro w; rw [run_cons, ih]; simp; omega

theorem run_prefix (gs : List Gate) : ∀ w : List Bool, ∃ ext, run gs w = w ++ ext := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run_nil]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨e, he⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ e, by
      rw [run_cons, he, List.append_assoc]⟩

theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨e, he⟩ := run_prefix gs w
  rw [he, List.getD_append _ _ _ _ h]

theorem getD_snoc (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]; simp

theorem getD_snoc_ne (w : List Bool) (v : Bool) (k : ℕ) (h : k ≠ w.length) :
    (w ++ [v]).getD k false = w.getD k false := by
  rcases lt_or_gt_of_ne h with h | h
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def nots (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nots_append (a b : List Gate) : nots (a ++ b) = nots a + nots b := by
  simp [nots, PEqualNP.NotBracket.notCount, List.filter_append]

theorem rises (u : ℕ → Bool) (B : Finset ℕ) : ∀ m, (∀ i < m, i ∉ B → u i = true → u (i+1) = true) →
    ((Finset.range m).filter (fun i => u i = false ∧ u (i+1) = true)).card + (if u 0 = true then 1 else 0)
      ≤ ((Finset.range m).filter (fun i => i ∈ B)).card + (if u m = true then 1 else 0) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h m (by omega)
    rw [Finset.card_filter, Finset.card_filter] at h1 ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hB : m ∈ B
    · cases hm : u m <;> cases hm1 : u (m+1) <;> simp [hm, hm1, hB] at h1 ⊢ <;> omega
    · cases hm : u m <;> cases hm1 : u (m+1) <;> simp [hm, hm1, hB] at h1 h2 ⊢ <;> omega

theorem markov (m N : ℕ) (x : ℕ → List Bool) (hlen : ∀ i, (x i).length = N)
    (hx : ∀ i < m, ∀ k, (x i).getD k false = true → (x (i+1)).getD k false = true) (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    ∃ B : Finset ℕ, B.card + 1 ≤ 2 ^ nots gs ∧ ∀ i < m, i ∉ B → ∀ k,
      (run gs (x i)).getD k false = true → (run gs (x (i+1))).getD k false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact ⟨∅, by simp [nots, PEqualNP.NotBracket.notCount], fun i hi _ k => hx i hi k⟩
  | append_singleton gs g ih =>
    intro hops
    obtain ⟨B, hB, hmono⟩ := ih (fun g' hg' => hops g' (List.mem_append_left _ hg'))
    have hg := hops g (by simp)
    have hL : ∀ i, (run gs (x i)).length = N + gs.length := fun i => by rw [run_length, hlen]
    have hstep : ∀ i, run (gs ++ [g]) (x i) = run gs (x i) ++
        [g.op.eval (g.inputs.map fun j => (run gs (x i)).getD j false)] := fun i => by
      rw [run_append, run_cons, run_nil]
    have key : ∀ B' : Finset ℕ, B ⊆ B' → (∀ i < m, i ∉ B' →
          g.op.eval (g.inputs.map fun j => (run gs (x i)).getD j false) = true →
          g.op.eval (g.inputs.map fun j => (run gs (x (i+1))).getD j false) = true) →
        ∀ i < m, i ∉ B' → ∀ k, (run (gs ++ [g]) (x i)).getD k false = true →
          (run (gs ++ [g]) (x (i+1))).getD k false = true := by
      intro B' hsub hnew i hi hiB k
      rw [hstep, hstep]
      by_cases hk : k = N + gs.length
      · have e1 : k = (run gs (x i)).length := by rw [hL]; exact hk
        have e2 : k = (run gs (x (i+1))).length := by rw [hL]; exact hk
        intro h
        rw [e1, getD_snoc] at h
        rw [e2, getD_snoc]
        exact hnew i hi hiB h
      · rw [getD_snoc_ne _ _ _ (by rw [hL]; exact hk), getD_snoc_ne _ _ _ (by rw [hL]; exact hk)]
        exact hmono i hi (fun h => hiB (hsub h)) k
    rcases hg with hg | hg | hg
    · refine ⟨B, ?_, key B (Finset.Subset.refl _) ?_⟩
      · rw [nots_append]; simpa [nots, PEqualNP.NotBracket.notCount, hg] using hB
      · intro i hi hiB h
        simp only [hg, GateOp.eval, List.all_eq_true, List.mem_map] at h ⊢
        rintro b ⟨j, hj, rfl⟩
        exact hmono i hi hiB j (h _ ⟨j, hj, rfl⟩)
    · refine ⟨B, ?_, key B (Finset.Subset.refl _) ?_⟩
      · rw [nots_append]; simpa [nots, PEqualNP.NotBracket.notCount, hg] using hB
      · intro i hi hiB h
        simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map] at h ⊢
        obtain ⟨b, ⟨j, hj, rfl⟩, hb⟩ := h
        exact ⟨_, ⟨j, hj, rfl⟩, hmono i hi hiB j hb⟩
    · obtain ⟨u, hu⟩ : ∃ u : ℕ → Bool, u = fun i =>
          (g.inputs.map fun j => (run gs (x i)).getD j false).headD false := ⟨_, rfl⟩
      have humono : ∀ i < m, i ∉ B → u i = true → u (i+1) = true := by
        intro i hi hiB
        rw [hu]
        cases hin : g.inputs with
        | nil => simp
        | cons j t => simpa using hmono i hi hiB j
      refine ⟨B ∪ (Finset.range m).filter (fun i => u i = false ∧ u (i+1) = true), ?_,
        key _ Finset.subset_union_left ?_⟩
      · have h1 := rises u B m humono
        have h2 : ((Finset.range m).filter (fun i => i ∈ B)).card ≤ B.card :=
          Finset.card_le_card (fun i hi => (Finset.mem_filter.1 hi).2)
        have h3 := Finset.card_union_le B ((Finset.range m).filter (fun i => u i = false ∧ u (i+1) = true))
        have h4 : (if u m = true then 1 else 0) ≤ 1 := by split <;> omega
        have h5 : nots (gs ++ [g]) = nots gs + 1 := by rw [nots_append]; simp [nots, PEqualNP.NotBracket.notCount, hg]
        rw [h5, pow_succ]; omega
      · intro i hi hiB h
        have e : ∀ i, g.op.eval (g.inputs.map fun j => (run gs (x i)).getD j false) = !(u i) := by
          intro i; rw [hu, hg]; rfl
        rw [e] at h ⊢
        cases h1 : u (i+1)
        · rfl
        · exact absurd (Finset.mem_union_right B (Finset.mem_filter.2
            ⟨Finset.mem_range.2 hi, by simpa using h, h1⟩)) hiB

theorem falls (C : Circuit) (m N : ℕ) (x : ℕ → List Bool) (hlen : ∀ i, (x i).length = N)
    (hx : ∀ i < m, ∀ k, (x i).getD k false = true → (x (i+1)).getD k false = true)
    (hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (F : Finset ℕ) (hF : ∀ i ∈ F, i < m ∧ C.eval (x i) = true ∧ C.eval (x (i+1)) = false) :
    F.card + 1 ≤ 2 ^ nots C.gates := by
  obtain ⟨B, hB, hmono⟩ := markov m N x hlen hx C.gates hops
  have hsub : F ⊆ B := by
    intro i hi
    obtain ⟨him, h1, h2⟩ := hF i hi
    by_contra hiB
    have h3 : C.eval (x (i+1)) = true := hmono i him hiB C.output h1
    rw [h2] at h3
    exact Bool.false_ne_true h3
  have := Finset.card_le_card hsub
  omega

theorem cone (N : ℕ) (gs : List Gate) : (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ W : Finset ℕ,
    ∃ T : Finset ℕ, T.card ≤ W.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ t ∈ T, x.getD t false = y.getD t false) →
      ∀ k ∈ W, (run gs x).getD k false = (run gs y).getD k false := by
  induction gs using List.reverseRecOn with
  | nil => intro _ W; exact ⟨W, by simp, fun x y _ _ h k hk => h k hk⟩
  | append_singleton gs g ih =>
    intro hf W
    have ih' := ih (fun g' hg' => hf g' (List.mem_append_left _ hg'))
    have hg := hf g (by simp)
    have hstep : ∀ x, run (gs ++ [g]) x = run gs x ++
        [g.op.eval (g.inputs.map fun j => (run gs x).getD j false)] := fun x => by
      rw [run_append, run_cons, run_nil]
    by_cases hW : N + gs.length ∈ W
    · obtain ⟨T, hT, hag⟩ := ih' (W.erase (N + gs.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, ?_⟩
      · have h1 := Finset.card_union_le (W.erase (N + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one hW
        have h3 := g.inputs.toFinset_card_le
        simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy k hk
        have h := hag x y hx hy hxy
        have lx : (run gs x).length = N + gs.length := by rw [run_length, hx]
        have ly : (run gs y).length = N + gs.length := by rw [run_length, hy]
        rw [hstep, hstep]
        by_cases hkl : k = N + gs.length
        · have e1 : k = (run gs x).length := by omega
          have e2 : (run gs x).length = (run gs y).length := by omega
          have hin : (g.inputs.map fun j => (run gs x).getD j false) =
              (g.inputs.map fun j => (run gs y).getD j false) :=
            List.map_congr_left (fun j hj => h j (Finset.mem_union_right _ (List.mem_toFinset.2 hj)))
          rw [e1, getD_snoc, e2, getD_snoc, hin]
        · rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
          exact h k (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hkl, hk⟩))
    · obtain ⟨T, hT, hag⟩ := ih' W
      refine ⟨T, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · intro x y hx hy hxy k hk
        have hkl : k ≠ N + gs.length := fun h => hW (h ▸ hk)
        have lx : (run gs x).length = N + gs.length := by rw [run_length, hx]
        have ly : (run gs y).length = N + gs.length := by rw [run_length, hy]
        rw [hstep, hstep, getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
        exact hag x y hx hy hxy k hk

def Good : ℕ → List Gate → Prop
  | _, [] => True
  | L, g :: gs => ((g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧
      ∀ i ∈ g.inputs, i < L) ∧ Good (L+1) gs

theorem good_append : ∀ (a : List Gate) (L : ℕ) (b : List Gate), Good L a → Good (L + a.length) b →
    Good L (a ++ b)
  | [], L, b, _, hb => by simpa using hb
  | g :: a, L, b, ha, hb => ⟨ha.1, good_append a (L+1) b ha.2 (by
      have e : L + 1 + a.length = L + (g :: a).length := by simp; omega
      rw [e]; exact hb)⟩

theorem good_get : ∀ (gs : List Gate) (L : ℕ), Good L gs → ∀ j (h : j < gs.length),
    ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or ∨ (gs[j]).op = GateOp.not) ∧
      (gs[j]).inputs.length ≤ 2 ∧ ∀ i ∈ (gs[j]).inputs, i < L + j
  | [], _, _, j, h => by simp at h
  | g :: gs, L, hg, 0, _ => by simpa using hg.1
  | g :: gs, L, hg, j+1, h => by
    have := good_get gs (L+1) hg.2 j (by simpa using h)
    have e : L + (j+1) = L + 1 + j := by omega
    simpa only [List.getElem_cons_succ, e] using this

theorem good_mem (gs : List Gate) (L : ℕ) (h : Good L gs) (g : Gate) (hg : g ∈ gs) :
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact ⟨(good_get gs L h j hj).1, (good_get gs L h j hj).2.1⟩

def layer (n : ℕ) : ℕ → List (ℕ × ℕ) → List Gate
  | _, [] => []
  | L, p :: ps => ⟨GateOp.and, [p.1, n]⟩ :: ⟨GateOp.or, [L, p.2]⟩ :: layer n (L+2) ps

theorem layer_length (n : ℕ) : ∀ (ps : List (ℕ × ℕ)) (L : ℕ), (layer n L ps).length = 2 * ps.length
  | [], _ => rfl
  | p :: ps, L => by simp [layer, layer_length n ps]; omega

theorem layer_nots (n : ℕ) : ∀ (ps : List (ℕ × ℕ)) (L : ℕ), nots (layer n L ps) = 0
  | [], _ => rfl
  | p :: ps, L => by
    have := layer_nots n ps (L+2)
    simpa [layer, nots, PEqualNP.NotBracket.notCount] using this

theorem layer_good (n : ℕ) : ∀ (ps : List (ℕ × ℕ)) (L : ℕ), n < L → (∀ p ∈ ps, p.1 < L ∧ p.2 < L) →
    Good L (layer n L ps)
  | [], _, _, _ => trivial
  | p :: ps, L, hn, h => by
    have hp := h p (by simp)
    refine ⟨⟨Or.inl rfl, by simp, ?_⟩, ⟨Or.inr (Or.inl rfl), by simp, ?_⟩,
      layer_good n ps (L+2) (by omega) (fun q hq => ?_)⟩
    · intro i hi; simp at hi; omega
    · intro i hi; simp at hi; omega
    · have := h q (List.mem_cons_of_mem _ hq); omega

theorem layer_spec (n : ℕ) : ∀ (ps : List (ℕ × ℕ)) (w : List Bool), n < w.length →
    (∀ p ∈ ps, p.1 < w.length ∧ p.2 < w.length) → ∀ i (h : i < ps.length),
    (run (layer n w.length ps) w).getD (w.length + 2*i+1) false =
      ((w.getD (ps[i]).1 false && w.getD n false) || w.getD (ps[i]).2 false)
  | [], _, _, _, i, h => by simp at h
  | p :: ps, w, hn, hps, i, hi => by
    have hp := hps p (by simp)
    obtain ⟨a, ha⟩ : ∃ a, a = (w.getD p.1 false && w.getD n false) := ⟨_, rfl⟩
    obtain ⟨o, ho⟩ : ∃ o, o = (a || w.getD p.2 false) := ⟨_, rfl⟩
    have e : run (layer n w.length (p :: ps)) w
        = run (layer n (w ++ [a] ++ [o]).length ps) (w ++ [a] ++ [o]) := by
      have l2 : (w ++ [a] ++ [o]).length = w.length + 2 := by simp
      have e1 : GateOp.and.eval ([p.1, n].map fun i => w.getD i false) = a := by
        rw [ha]; simp [GateOp.eval]
      have e2 : GateOp.or.eval ([w.length, p.2].map fun i => (w ++ [a]).getD i false) = o := by
        rw [ho]; simp only [List.map_cons, List.map_nil]
        rw [getD_snoc, List.getD_append _ _ _ _ hp.2]; simp [GateOp.eval]
      rw [l2, layer, run_cons, e1, run_cons, e2]
    rw [e]
    cases i with
    | zero =>
      have l1 : w.length + 2*0+1 = (w ++ [a]).length := by simp
      rw [run_old _ _ _ (by simp), l1, getD_snoc, ho, ha]; rfl
    | succ i =>
      have l2 : w.length + 2*(i+1)+1 = (w ++ [a] ++ [o]).length + 2*i+1 := by simp; omega
      have hlt : ∀ k, k < w.length → (w ++ [a] ++ [o]).getD k false = w.getD k false := by
        intro k hk
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ hk]
      have hi' : i < ps.length := by simpa using hi
      rw [l2, layer_spec n ps (w ++ [a] ++ [o]) (by simp; omega)
        (fun q hq => by
          have := hps q (List.mem_cons_of_mem _ hq)
          simp; omega) i hi']
      have hq := hps (ps[i]) (List.mem_cons_of_mem _ (List.getElem_mem hi'))
      rw [hlt _ hq.1, hlt _ hq.2, hlt _ hn]
      simp

def pairs (k : ℕ) (t e : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range (2^k-1)).map (fun i => (t i, t (i+2^k))) ++ (List.range (2^k)).map (fun i => (e i, e (i+2^k)))

def dec : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ) → List Gate × ℕ
  | 0, _, _, e => ([], e 0)
  | k+1, L, t, e =>
    (⟨GateOp.not, [t (2^k-1)]⟩ :: (layer L (L+1) (pairs k t e) ++
        (dec k (L+1+2*(pairs k t e).length) (fun i => L+1+2*i+1) (fun i => L+1+2*(2^k-1+i)+1)).1),
      (dec k (L+1+2*(pairs k t e).length) (fun i => L+1+2*i+1) (fun i => L+1+2*(2^k-1+i)+1)).2)

theorem dec_spec : ∀ (r : ℕ) (w : List Bool) (t e : ℕ → ℕ) (P : ℕ) (c : Bool), P < 2^r →
    (∀ i < 2^r - 1, t i < w.length ∧ w.getD (t i) false = decide (i < P)) →
    (∀ i < 2^r, e i < w.length ∧ w.getD (e i) false = (decide (i < P) || (decide (i = P) && c))) →
    (run (dec r w.length t e).1 w).getD (dec r w.length t e).2 false = c ∧
      Good w.length (dec r w.length t e).1 ∧
      (dec r w.length t e).2 < w.length + (dec r w.length t e).1.length ∧
      nots (dec r w.length t e).1 = r ∧ (dec r w.length t e).1.length + 4 ≤ 4 * 2^r := by
  intro r
  induction r with
  | zero =>
    intro w t e P c hP _ he
    have hP0 : P = 0 := by simpa using hP
    have h := he 0 (by simp)
    refine ⟨?_, trivial, by simpa [dec] using h.1, rfl, by simp [dec]⟩
    show w.getD (e 0) false = c
    rw [h.2, hP0]; simp
  | succ k ih =>
    intro w t e P c hP ht he
    have h2 : 2^(k+1) = 2^k + 2^k := by rw [pow_succ]; omega
    have h1 : 1 ≤ 2^k := Nat.one_le_two_pow
    have hsel := ht (2^k-1) (by omega)
    obtain ⟨nb, hnb⟩ : ∃ nb, nb = !(w.getD (t (2^k-1)) false) := ⟨_, rfl⟩
    have hnb' : nb = decide (P < 2^k) := by
      rw [hnb, hsel.2, Bool.eq_iff_iff]; simp; omega
    have hlen : (pairs k t e).length = (2^k-1) + 2^k := by simp [pairs]
    have hmem : ∀ p ∈ pairs k t e, p.1 < (w ++ [nb]).length ∧ p.2 < (w ++ [nb]).length := by
      intro p hp
      simp only [pairs, List.mem_append, List.mem_map, List.mem_range] at hp
      rcases hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · have a := (ht i (by omega)).1
        have b := (ht (i+2^k) (by omega)).1
        simp; omega
      · have a := (he i (by omega)).1
        have b := (he (i+2^k) (by omega)).1
        simp; omega
    have l1 : (w ++ [nb]).length = w.length + 1 := by simp
    obtain ⟨w2, hw2⟩ : ∃ w2, w2 = run (layer w.length (w ++ [nb]).length (pairs k t e)) (w ++ [nb]) := ⟨_, rfl⟩
    have l2 : w2.length = w.length + 1 + 2 * (pairs k t e).length := by
      rw [hw2, run_length, layer_length, l1]
    have hspec := layer_spec w.length (pairs k t e) (w ++ [nb]) (by simp) hmem
    have hold : ∀ j, j < w.length → (w ++ [nb]).getD j false = w.getD j false :=
      fun j hj => List.getD_append _ _ _ _ hj
    obtain ⟨P', hP'⟩ : ∃ P', P' = if P < 2^k then P else P - 2^k := ⟨_, rfl⟩
    have hP'lt : P' < 2^k := by rw [hP']; split <;> omega
    have ht' : ∀ i < 2^k - 1, w.length+1+2*i+1 < w2.length ∧
        w2.getD (w.length+1+2*i+1) false = decide (i < P') := by
      intro i hi
      refine ⟨by omega, ?_⟩
      have hi' : i < (pairs k t e).length := by omega
      have hs := hspec i hi'
      have ep : (pairs k t e)[i] = (t i, t (i+2^k)) := by
        simp only [pairs]
        rw [List.getElem_append_left (by simpa using hi)]
        simp
      have a := ht i (by omega)
      have b := ht (i+2^k) (by omega)
      rw [ep] at hs
      simp only at hs
      rw [hold _ a.1, hold _ b.1, a.2, b.2, getD_snoc, ← hw2, l1] at hs
      rw [hs, hnb', hP', Bool.eq_iff_iff]
      by_cases hc : P < 2^k
      · simp [hc]; omega
      · simp [hc]; omega
    have he' : ∀ i < 2^k, w.length+1+2*(2^k-1+i)+1 < w2.length ∧
        w2.getD (w.length+1+2*(2^k-1+i)+1) false = (decide (i < P') || (decide (i = P') && c)) := by
      intro i hi
      refine ⟨by omega, ?_⟩
      have hi' : 2^k-1+i < (pairs k t e).length := by omega
      have hs := hspec _ hi'
      have ep : (pairs k t e)[2^k-1+i] = (e i, e (i+2^k)) := by
        simp only [pairs]
        rw [List.getElem_append_right (by simp)]
        simp
      have a := he i (by omega)
      have b := he (i+2^k) (by omega)
      rw [ep] at hs
      simp only at hs
      rw [hold _ a.1, hold _ b.1, a.2, b.2, getD_snoc, ← hw2, l1] at hs
      rw [hs, hnb', hP']
      by_cases hc : P < 2^k
      · have x1 : ¬ i + 2^k < P := by omega
        have x2 : ¬ i + 2^k = P := by omega
        simp [hc, x1, x2]
      · have x1 : (i + 2^k < P) = (i < P - 2^k) := propext (by omega)
        have x2 : (i + 2^k = P) = (i = P - 2^k) := propext (by omega)
        simp [hc, x1, x2]
    have R := ih w2 (fun i => w.length+1+2*i+1) (fun i => w.length+1+2*(2^k-1+i)+1) P' c hP'lt ht' he'
    rw [l2] at R
    obtain ⟨Rv, Rg, Ro, Rn, Rs⟩ := R
    have egate : GateOp.not.eval ([t (2^k-1)].map fun i => w.getD i false) = nb := by
      rw [hnb]; rfl
    have ll : (layer w.length (w.length+1) (pairs k t e)).length = 2 * (pairs k t e).length :=
      layer_length _ _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [dec]
      rw [run_cons, egate, run_append, ← l1, ← hw2, l1]
      exact Rv
    · simp only [dec]
      refine ⟨⟨Or.inr (Or.inr rfl), by simp, fun i hi => ?_⟩, ?_⟩
      · simp at hi; rw [hi]; exact hsel.1
      · refine good_append _ _ _ (layer_good _ _ _ (by omega) (fun p hp => ?_)) ?_
        · have := hmem p hp; rwa [l1] at this
        · rw [ll]; exact Rg
    · simp only [dec, List.length_cons, List.length_append, ll]; omega
    · simp only [dec]
      have : ∀ (a : List Gate), nots (⟨GateOp.not, [t (2^k-1)]⟩ :: a) = nots a + 1 := by
        intro a; simp [nots, PEqualNP.NotBracket.notCount]
      rw [this, nots_append, layer_nots, Rn]; omega
    · simp only [dec, List.length_cons, List.length_append, ll]; omega

theorem dec_spec' (r : ℕ) (w : List Bool) (t e : ℕ → ℕ) (P : ℕ) (c : Bool) (hP : P < 2^r)
    (ht : ∀ i < 2^r - 1, t i < w.length ∧ (w.getD (t i) false = true ↔ i < P))
    (he : ∀ i < 2^r, e i < w.length ∧ (w.getD (e i) false = true ↔ i < P ∨ (i = P ∧ c = true))) :
    (run (dec r w.length t e).1 w).getD (dec r w.length t e).2 false = c ∧
      Good w.length (dec r w.length t e).1 ∧
      (dec r w.length t e).2 < w.length + (dec r w.length t e).1.length ∧
      nots (dec r w.length t e).1 = r ∧ (dec r w.length t e).1.length + 4 ≤ 4 * 2^r :=
  dec_spec r w t e P c hP
    (fun i hi => ⟨(ht i hi).1, by rw [Bool.eq_iff_iff, (ht i hi).2, decide_eq_true_eq]⟩)
    (fun i hi => ⟨(he i hi).1, by rw [Bool.eq_iff_iff, (he i hi).2]; simp⟩)

theorem nots_or (l : List ℕ) : nots [⟨GateOp.or, l⟩] = 0 := by
  unfold nots PEqualNP.NotBracket.notCount; simp

theorem nots_not (l : List ℕ) : nots [⟨GateOp.not, l⟩] = 1 := by
  unfold nots PEqualNP.NotBracket.notCount; simp

def orchain : ℕ → ℕ → List ℕ → List Gate × ℕ
  | prev, _, [] => ([], prev)
  | prev, L, i :: is => (⟨GateOp.or, [prev, i]⟩ :: (orchain L (L+1) is).1, (orchain L (L+1) is).2)

theorem orchain_spec : ∀ (is : List ℕ) (w : List Bool) (prev : ℕ), prev < w.length →
    (∀ i ∈ is, i < w.length) →
    (run (orchain prev w.length is).1 w).getD (orchain prev w.length is).2 false
        = (w.getD prev false || is.any (fun i => w.getD i false)) ∧
      Good w.length (orchain prev w.length is).1 ∧
      (orchain prev w.length is).2 < w.length + (orchain prev w.length is).1.length ∧
      nots (orchain prev w.length is).1 = 0 ∧ (orchain prev w.length is).1.length = is.length
  | [], w, prev, hp, _ => ⟨by simp [orchain, run_nil], trivial, by simpa [orchain] using hp, rfl, rfl⟩
  | i :: is, w, prev, hp, h => by
    have hi := h i (by simp)
    obtain ⟨v, hv⟩ : ∃ v, v = (w.getD prev false || w.getD i false) := ⟨_, rfl⟩
    have l1 : (w ++ [v]).length = w.length + 1 := by simp
    have R := orchain_spec is (w ++ [v]) w.length (by simp)
      (fun j hj => by have := h j (List.mem_cons_of_mem _ hj); simp; omega)
    rw [l1] at R
    obtain ⟨Rv, Rg, Ro, Rn, Rs⟩ := R
    have eg : GateOp.or.eval ([prev, i].map fun j => w.getD j false) = v := by
      rw [hv]; simp [GateOp.eval]
    have hany : is.any (fun j => (w ++ [v]).getD j false) = is.any (fun j => w.getD j false) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨j, hj, hjv⟩
        exact ⟨j, hj, by rwa [List.getD_append _ _ _ _ (h j (List.mem_cons_of_mem _ hj))] at hjv⟩
      · rintro ⟨j, hj, hjv⟩
        exact ⟨j, hj, by rwa [List.getD_append _ _ _ _ (h j (List.mem_cons_of_mem _ hj))]⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [orchain]
      rw [run_cons, eg, Rv, getD_snoc, hany, hv, List.any_cons, Bool.or_assoc]
    · simp only [orchain]
      refine ⟨⟨Or.inr (Or.inl rfl), by simp, fun j hj => ?_⟩, Rg⟩
      simp at hj; omega
    · simp only [orchain, List.length_cons]; omega
    · simpa [orchain, nots, PEqualNP.NotBracket.notCount] using Rn
    · simp [orchain, Rs]

theorem pos_exists : ∀ (n : ℕ) (width : Fin n → ℕ), ∃ pos : (a : Fin n) → Fin (width a) → ℕ,
    (∀ a k, pos a k < ∑ a, width a) ∧ ∀ x : (a : Fin n) → Fin (width a) → Bool,
      ((List.ofFn fun a => List.ofFn (x a)).flatten).length = ∑ a, width a ∧
      ∀ a k, ((List.ofFn fun a => List.ofFn (x a)).flatten).getD (pos a k) false = x a k := by
  intro n
  induction n with
  | zero => intro width; exact ⟨fun a => a.elim0, fun a => a.elim0, fun x => ⟨by simp, fun a => a.elim0⟩⟩
  | succ n ih =>
    intro width
    obtain ⟨pos', hb, hx⟩ := ih (fun a => width a.succ)
    refine ⟨Fin.cases (motive := fun a => Fin (width a) → ℕ) (fun k => k.val)
      (fun i k => width 0 + pos' i k), ?_, fun x => ?_⟩
    · intro a
      rw [Fin.sum_univ_succ]
      induction a using Fin.cases with
      | zero => intro k; simp only [Fin.cases_zero]; omega
      | succ i =>
        intro k; simp only [Fin.cases_succ]
        have := hb i k; omega
    · obtain ⟨hl, hv⟩ := hx (fun a => x a.succ)
      rw [List.ofFn_succ, List.flatten_cons]
      refine ⟨by rw [List.length_append, hl, Fin.sum_univ_succ]; simp, fun a => ?_⟩
      induction a using Fin.cases with
      | zero =>
        intro k; simp only [Fin.cases_zero]
        rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
        simp
      | succ i =>
        intro k; simp only [Fin.cases_succ]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simpa using hv i k

end PEqualNP.Outside.L_lib_1345

theorem PEqualNP.Outside.L_lib_1345 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n r d : Nat) (w : Fin n → Nat) (E : Finset (Finset (Fin n))),
  let q := 2^r
  7*q+2 ≤ d →
  let width := fun a : Fin n => d * w a
  let N := Finset.univ.sum width + (2*q-1) + 2
  let raw := fun (x : (a : Fin n) → Fin (width a) → Bool) (j : Nat) =>
    (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++
    List.ofFn (fun g : Fin (2*q-1) => decide (g.val < j)) ++ [false,true]
  let ordinary := (Finset.Ico 1 (2*q)).image
    (fun j => (raw (fun _ _ => false) j, decide (j % 2 = 0)))
  let copies := fun M : Finset (Fin n) =>
    Finset.univ.image (fun f : (a : {a : Fin n // a ∈ M}) → Fin (width a.val) =>
      (raw (fun a k => if h : a ∈ M then decide (f ⟨a,h⟩ = k) else false) 0, true))
  let rows := ordinary ∪ E.biUnion copies
  let fits := fun (b s : Nat) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧
      C.output < N+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
      ∀ z ∈ rows, C.eval z.1 = z.2
  rows.card = (2*q-1) + E.sum (fun M => M.prod width) ∧
    (∀ k : Nat, fits r (d*k+7*q) ↔
      ∃ S : Finset (Fin n), S.sum w ≤ k ∧ ∀ M ∈ E, (M ∩ S).Nonempty) ∧
    (∀ b < r, ∀ s, ¬ fits b s) ∧ fits (r+1) (10*q)) := by
  intro n r d w E q hd width N raw ordinary copies rows fits
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  obtain ⟨pos, hpb, hpx⟩ := PEqualNP.Outside.L_lib_1345.pos_exists n width
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ a, width a := ⟨_, rfl⟩
  have hN : N = W + (2*q-1) + 2 := by rw [hW]
  obtain ⟨z, hz⟩ : ∃ z : (a : Fin n) → Fin (width a) → Bool, z = fun _ _ => false := ⟨_, rfl⟩
  have hflat : ∀ x : (a : Fin n) → Fin (width a) → Bool,
      ((List.ofFn fun a => List.ofFn (x a)).flatten).length = W := fun x => by rw [(hpx x).1, hW]
  have hlen : ∀ x j, (raw x j).length = N := by
    intro x j
    simp only [raw, List.length_append, hflat, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  have hbank : ∀ x j a k, (raw x j).getD (pos a k) false = x a k := by
    intro x j a k
    have h1 : pos a k < W := by rw [hW]; exact hpb a k
    simp only [raw]
    rw [List.getD_append _ _ _ _ (by rw [List.length_append, hflat]; omega),
      List.getD_append _ _ _ _ (by rw [hflat]; exact h1)]
    exact (hpx x).2 a k
  have hlev : ∀ x j i, i < 2*q-1 → ((raw x j).getD (W+i) false = true ↔ i < j) := by
    intro x j i hi
    simp only [raw]
    rw [List.getD_append _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn]; omega),
      List.getD_append_right _ _ _ _ (by rw [hflat]; omega), hflat,
      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega)]
    simp
  have hfalse : ∀ x j, (raw x j).getD (W+(2*q-1)) false = false := by
    intro x j
    simp only [raw]
    have hl : ((List.ofFn fun a => List.ofFn (x a)).flatten ++
        List.ofFn (fun g : Fin (2*q-1) => decide (g.val < j))).length = W+(2*q-1) := by
      rw [List.length_append, hflat, List.length_ofFn]
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn])]
    simp only [List.length_append, hflat, List.length_ofFn, Nat.sub_self]
    rfl
  have hord : ∀ j, 1 ≤ j → j < 2*q → ∃ b : Bool, (raw z j, b) ∈ rows ∧ (b = true ↔ j % 2 = 0) := by
    intro j h1 h2
    rw [hz]
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    refine ⟨decide (j % 2 = 0), Finset.mem_union_left _ (Finset.mem_image.2
      ⟨j, Finset.mem_Ico.2 ⟨h1, h2⟩, rfl⟩), by rw [decide_eq_true_eq]⟩
  have hcopy : ∀ M ∈ E, ∀ f : (a : {a : Fin n // a ∈ M}) → Fin (width a.val),
      ∃ x : (a : Fin n) → Fin (width a) → Bool, (raw x 0, true) ∈ rows ∧
        ∀ a k, (x a k = true ↔ ∃ h : a ∈ M, f ⟨a,h⟩ = k) := by
    intro M hM f
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    refine ⟨_, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨M, hM,
      Finset.mem_image.2 ⟨f, Finset.mem_univ _, rfl⟩⟩), ?_⟩
    intro a k
    by_cases h : a ∈ M <;> simp [h]
  have hOE : ∀ u ∈ ordinary, ∃ j, (1 ≤ j ∧ j < 2*q) ∧ u.1 = raw z j ∧ (u.2 = true ↔ j % 2 = 0) := by
    intro u hu
    rw [hz]
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨j, Finset.mem_Ico.1 hj, rfl, by rw [decide_eq_true_eq]⟩
  have hCE : ∀ M u, u ∈ copies M → ∃ f : (a : {a : Fin n // a ∈ M}) → Fin (width a.val),
      ∃ x : (a : Fin n) → Fin (width a) → Bool, u = (raw x 0, true) ∧
        ∀ a k, (x a k = true ↔ ∃ h : a ∈ M, f ⟨a,h⟩ = k) := by
    intro M u hu
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨f, _, rfl, ?_⟩
    intro a k
    by_cases h : a ∈ M <;> simp [h]
  have hRE : ∀ u ∈ rows, u ∈ ordinary ∨ ∃ M ∈ E, u ∈ copies M := by
    intro u hu
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    rcases Finset.mem_union.1 hu with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_biUnion.1 h)
  have hmono : ∀ j k, (raw z j).getD k false = true → (raw z (j+1)).getD k false = true := by
    intro j k h
    by_cases hk : W ≤ k ∧ k < W + (2*q-1)
    · obtain ⟨i, rfl⟩ : ∃ i, k = W + i := ⟨k - W, by omega⟩
      have hi : i < 2*q-1 := by omega
      rw [hlev z _ i hi] at h ⊢; omega
    · have same : (raw z (j+1)).getD k false = (raw z j).getD k false := by
        by_cases hk1 : k < W
        · simp only [raw]
          rw [List.getD_append _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn]; omega),
            List.getD_append _ _ _ _ (by rw [hflat]; omega),
            List.getD_append _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn]; omega),
            List.getD_append _ _ _ _ (by rw [hflat]; omega)]
        · simp only [raw]
          rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn]; omega),
            List.getD_append_right _ _ _ _ (by rw [List.length_append, hflat, List.length_ofFn]; omega)]
          simp only [List.length_append, List.length_ofFn]
      rw [same]; exact h
  have hops : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) := by
    intro C h
    exact ⟨fun g hg => by simpa using (h g hg).1, fun g hg => (h g hg).2⟩
  have hbuild : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o b s : ℕ),
      PEqualNP.Outside.L_lib_1345.Good N gs → o < N + gs.length →
      PEqualNP.Outside.L_lib_1345.nots gs ≤ b → gs.length ≤ s →
      (∀ u ∈ rows, (PEqualNP.Outside.L_lib_1345.run gs u.1).getD o false = u.2) → fits b s := by
    intro gs o b s hg ho hn hs hr
    refine ⟨⟨gs, o⟩, ?_, ?_, ho, hn, hs, hr⟩
    · intro g hgm
      have := PEqualNP.Outside.L_lib_1345.good_mem gs N hg g hgm
      exact ⟨by simpa using this.1, this.2⟩
    · intro j hj i hi
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] :=
        List.getD_eq_getElem _ _ hj
      rw [e] at hi
      exact (PEqualNP.Outside.L_lib_1345.good_get gs N hg j hj).2.2 i hi
  refine ⟨?_, fun k => ⟨?_, ?_⟩, ?_, ?_⟩
  · have d1 : ∀ u ∈ ordinary, ∀ M, u ∉ copies M := by
      intro u hu M hu'
      obtain ⟨j, hj, h1, _⟩ := hOE u hu
      obtain ⟨_, x, hx, _⟩ := hCE M u hu'
      have h0 : 0 < 2*q-1 := by omega
      have e : raw z j = raw x 0 := by rw [← h1, hx]
      have h := (hlev z j 0 h0).2 (by omega)
      rw [e, hlev _ _ 0 h0] at h
      omega
    have hinj : ∀ a b : ℕ, a ∈ Finset.Ico 1 (2*q) → b ∈ Finset.Ico 1 (2*q) →
        raw (fun _ _ => false) a = raw (fun _ _ => false) b → a = b := by
      intro a b ha hb hab
      have ha' := Finset.mem_Ico.1 ha
      have hb' := Finset.mem_Ico.1 hb
      have key : ∀ a b : ℕ, 1 ≤ a → a < 2*q → raw (fun _ _ => false) a = raw (fun _ _ => false) b → a ≤ b := by
        intro a b h1 h2 h
        have hi : a-1 < 2*q-1 := by omega
        have h3 := (hlev (fun _ _ => false) a (a-1) hi).2 (by omega)
        rw [h, hlev _ b (a-1) hi] at h3
        omega
      exact le_antisymm (key a b ha'.1 ha'.2 hab) (key b a hb'.1 hb'.2 hab.symm)
    have c1 : ordinary.card = (Finset.Ico 1 (2*q)).card := by
      letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb hab
      exact hinj a b ha hb (congrArg Prod.fst hab)
    have hsame : ∀ M M' : Finset (Fin n), ∀ u, u ∈ copies M → u ∈ copies M' → M ⊆ M' := by
      intro M M' u hu hu' a ha
      obtain ⟨f, x, hx, hxv⟩ := hCE M u hu
      obtain ⟨g, y, hy, hyv⟩ := hCE M' u hu'
      have e : raw x 0 = raw y 0 := congrArg Prod.fst (hx.symm.trans hy)
      have h1 : x a (f ⟨a,ha⟩) = true := (hxv _ _).2 ⟨ha, rfl⟩
      rw [← hbank x 0, e, hbank] at h1
      exact ((hyv _ _).1 h1).1
    have c2 : ∀ M, (copies M).card = M.prod width := by
      intro M
      letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      refine (Finset.card_image_of_injective _ ?_).trans ?_
      · intro f g hfg
        funext ⟨a, ha⟩
        have e := congrArg Prod.fst hfg
        have h := congrArg (fun l => l.getD (pos a (f ⟨a,ha⟩)) false) e
        simp only [hbank] at h
        simp [ha] at h
        exact h.symm
      · refine Finset.card_univ.trans (Fintype.card_pi.trans ?_)
        simp only [Fintype.card_fin]
        exact Finset.prod_coe_sort M width
    have c3 : rows.card = ordinary.card + ∑ M ∈ E, (copies M).card := by
      letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      have dj : Disjoint ordinary (E.biUnion copies) := by
        refine Finset.disjoint_left.2 (fun u hu hu' => ?_)
        obtain ⟨M, _, h⟩ := Finset.mem_biUnion.1 hu'
        exact d1 u hu M h
      refine (Finset.card_union_of_disjoint dj).trans (congrArg _ (Finset.card_biUnion ?_))
      intro M _ M' _ hne
      exact Finset.disjoint_left.2 (fun u hu hu' => hne
        (Finset.Subset.antisymm (hsame M M' u hu hu') (hsame M' M u hu' hu)))
    rw [c3, c1, Nat.card_Ico, Finset.sum_congr rfl (fun M _ => c2 M)]
    try omega
  · rintro ⟨C, hfan, _, _, hnot, hsize, hrows⟩
    obtain ⟨hop, hin⟩ := hops C hfan
    obtain ⟨T, hT, hag⟩ := PEqualNP.Outside.L_lib_1345.cone N C.gates hin {C.output}
    refine ⟨Finset.univ.filter (fun a => ∀ k : Fin (width a), pos a k ∈ T), ?_, ?_⟩
    · have inj : Function.Injective (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) := by
        rintro ⟨a, k1⟩ ⟨b, k2⟩ h
        simp only at h
        have h1 := hbank (fun c m => decide ((⟨c,m⟩ : (a : Fin n) × Fin (width a)) = ⟨a,k1⟩)) 0 a k1
        rw [h, hbank] at h1
        have h2 := h1.trans (decide_eq_true rfl)
        exact (of_decide_eq_true h2).symm
      obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.filter (fun a => ∀ k : Fin (width a), pos a k ∈ T) := ⟨_, rfl⟩
      rw [← hS]
      have sub : (S.sigma (fun a => (Finset.univ : Finset (Fin (width a))))).image
          (fun s => pos s.1 s.2) ⊆ T := by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
        have := (Finset.mem_sigma.1 hs).1
        rw [hS] at this
        exact (Finset.mem_filter.1 this).2 s.2
      have h1 := Finset.card_le_card sub
      rw [Finset.card_image_of_injective _ inj, Finset.card_sigma] at h1
      have h2 : ∑ a ∈ S, (Finset.univ : Finset (Fin (width a))).card = d * S.sum w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp [width]
      have h3 : T.card ≤ 1 + C.gates.length := by simpa using hT
      have h4 : C.gates.length ≤ d*k+7*q := hsize
      have h5 : d * S.sum w < d * (k+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      have := Nat.lt_of_mul_lt_mul_left h5
      omega
    · intro M hM
      by_contra hne
      have hun : ∀ a : {a : Fin n // a ∈ M}, ∃ k : Fin (width a.val), pos a.val k ∉ T := by
        rintro ⟨a, ha⟩
        by_contra hc
        refine hne ⟨a, ?_⟩
        simp only [Finset.mem_inter]
        refine ⟨ha, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => ?_⟩⟩
        by_contra h
        exact hc ⟨k, h⟩
      choose f hf using hun
      obtain ⟨x, hxrow, hxv⟩ := hcopy M hM f
      have surj : ∀ t < W, ∃ b l, pos b l = t := by
        intro t ht
        have inj : Function.Injective (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) := by
          rintro ⟨a, k1⟩ ⟨b, k2⟩ h
          simp only at h
          have h1 := hbank (fun c m => decide ((⟨c,m⟩ : (a : Fin n) × Fin (width a)) = ⟨a,k1⟩)) 0 a k1
          rw [h, hbank] at h1
          have h2 := h1.trans (decide_eq_true rfl)
          exact (of_decide_eq_true h2).symm
        have e : Finset.univ.image (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) = Finset.range W := by
          refine Finset.eq_of_subset_of_card_le (fun t ht => ?_) ?_
          · obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 ht
            rw [Finset.mem_range, hW]; exact hpb _ _
          · rw [Finset.card_image_of_injective _ inj, Finset.card_range, Finset.card_univ,
              Fintype.card_sigma, hW]
            simp
        have : t ∈ Finset.range W := Finset.mem_range.2 ht
        rw [← e] at this
        obtain ⟨s, _, hs⟩ := Finset.mem_image.1 this
        exact ⟨s.1, s.2, hs⟩
      have agree : ∀ t ∈ T, (raw x 0).getD t false = (raw z 0).getD t false := by
        intro t ht
        by_cases htW : t < W
        · obtain ⟨b, l, rfl⟩ := surj t htW
          rw [hbank, hbank, hz]
          cases hx : x b l
          · rfl
          · obtain ⟨hb, hfl⟩ := (hxv b l).1 hx
            exact absurd (hfl ▸ ht : pos b (f ⟨b,hb⟩) ∈ T) (hf ⟨b,hb⟩)
        · simp only [raw]
          rw [List.append_assoc, List.append_assoc,
            List.getD_append_right ((List.ofFn fun a => List.ofFn (x a)).flatten) _ _ _ (by rw [hflat]; omega),
            List.getD_append_right ((List.ofFn fun a => List.ofFn (z a)).flatten) _ _ _ (by rw [hflat]; omega),
            hflat, hflat]
      have h0 : C.eval (raw z 0) = true := by
        have e : C.eval (raw x 0) = C.eval (raw z 0) :=
          hag (raw x 0) (raw z 0) (hlen _ _) (hlen _ _) agree C.output (Finset.mem_singleton_self _)
        rw [← e]; exact hrows _ hxrow
      have hF := PEqualNP.Outside.L_lib_1345.falls C (2*q-1) N (fun i => raw z i) (fun i => hlen z i)
        (fun i _ => hmono i) hop ((Finset.range q).image (fun p => 2*p)) (by
          intro i hi
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          have hp' := Finset.mem_range.1 hp
          refine ⟨by omega, ?_, ?_⟩
          · rcases Nat.eq_zero_or_pos p with rfl | hp0
            · simpa using h0
            · obtain ⟨c, hc, hcv⟩ := hord (2*p) (by omega) (by omega)
              exact (hrows _ hc).trans (hcv.2 (by omega))
          · obtain ⟨c, hc, hcv⟩ := hord (2*p+1) (by omega) (by omega)
            refine (hrows _ hc).trans (Bool.eq_false_iff.2 (fun h => ?_))
            have := hcv.1 h
            omega)
      rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range] at hF
      have : 2 ^ PEqualNP.Outside.L_lib_1345.nots C.gates ≤ q := Nat.pow_le_pow_right (by omega) hnot
      omega
  · rintro ⟨S, hSk, hhit⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun i => W + (2*i+2) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, e = fun i => if 2*i+1 < 2*q-1 then W + (2*i+1) else W + (2*q-1) := ⟨_, rfl⟩
    obtain ⟨I, hI⟩ : ∃ I : List ℕ, I = (S.sigma (fun a => (Finset.univ : Finset (Fin (width a))))).toList.map
        (fun s => pos s.1 s.2) := ⟨_, rfl⟩
    have hIlen : I.length ≤ d*k := by
      have h2 : ∑ a ∈ S, (Finset.univ : Finset (Fin (width a))).card = d * S.sum w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp [width]
      rw [hI, List.length_map, Finset.length_toList, Finset.card_sigma, h2]
      exact Nat.mul_le_mul_left d hSk
    have hdec : ∀ j, 1 ≤ j → j < 2*q →
        (∀ i < 2^r - 1, t i < (raw z j).length ∧ ((raw z j).getD (t i) false = true ↔ i < (j-1)/2)) ∧
        (∀ i < 2^r, e i < (raw z j).length ∧ ((raw z j).getD (e i) false = true ↔
          i < (j-1)/2 ∨ (i = (j-1)/2 ∧ decide (j % 2 = 0) = true))) := by
      intro j h1 h2
      constructor
      · intro i hi
        have hi' : i < q - 1 := hi
        have a : 2*i+2 < 2*q-1 := by omega
        rw [hlen, ht]
        refine ⟨by simp only; omega, ?_⟩
        show (raw z j).getD (W + (2*i+2)) false = true ↔ _
        rw [hlev z j _ a]
        omega
      · intro i hi
        have hi' : i < q := hi
        rw [hlen, he]
        by_cases a : 2*i+1 < 2*q-1
        · simp only [if_pos a]
          refine ⟨by omega, ?_⟩
          rw [hlev z j _ a, decide_eq_true_eq]
          omega
        · simp only [if_neg a]
          refine ⟨by omega, ?_⟩
          rw [hfalse, decide_eq_true_eq]
          simp only [Bool.false_eq_true, false_iff]
          omega
    have spec : ∀ j, 1 ≤ j → j < 2*q → _ := fun j h1 h2 =>
      PEqualNP.Outside.L_lib_1345.dec_spec' r (raw z j) t e ((j-1)/2) (decide (j % 2 = 0))
        (show (j-1)/2 < q by omega) (hdec j h1 h2).1 (hdec j h1 h2).2
    obtain ⟨D, hD⟩ : ∃ D, D = PEqualNP.Outside.L_lib_1345.dec r N t e := ⟨_, rfl⟩
    have S1 := spec 1 le_rfl (by omega)
    rw [hlen, ← hD] at S1
    obtain ⟨_, Dg, Do, Dn, Ds⟩ := S1
    obtain ⟨O, hO⟩ : ∃ O, O = PEqualNP.Outside.L_lib_1345.orchain (W+(2*q-1)) (N + D.1.length) I := ⟨_, rfl⟩
    have hIlt : ∀ i ∈ I, i < N := by
      intro i hi
      rw [hI] at hi
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hi
      have := hpb s.1 s.2
      omega
    have run1 : ∀ u : List Bool, u.length = N →
        (PEqualNP.Outside.L_lib_1345.run D.1 u).length = N + D.1.length := fun u hu => by
      rw [PEqualNP.Outside.L_lib_1345.run_length, hu]
    have ospec : ∀ u : List Bool, u.length = N → _ := fun u hu =>
      PEqualNP.Outside.L_lib_1345.orchain_spec I (PEqualNP.Outside.L_lib_1345.run D.1 u) (W+(2*q-1))
        (by rw [run1 u hu]; omega) (fun i hi => by rw [run1 u hu]; have := hIlt i hi; omega)
    have O1 := ospec (raw z 1) (hlen _ _)
    rw [run1 _ (hlen _ _), ← hO] at O1
    obtain ⟨_, Og, Oo, On, Os⟩ := O1
    refine hbuild (D.1 ++ (O.1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [O.2, D.2]⟩]))
      (N + D.1.length + O.1.length) r (d*k+7*q) ?_ ?_ ?_ ?_ ?_
    · refine PEqualNP.Outside.L_lib_1345.good_append _ _ _ Dg
        (PEqualNP.Outside.L_lib_1345.good_append _ _ _ Og ?_)
      refine ⟨⟨Or.inr (Or.inl rfl), by simp, fun i hi => ?_⟩, trivial⟩
      simp at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [PEqualNP.Outside.L_lib_1345.nots_append, PEqualNP.Outside.L_lib_1345.nots_append, Dn, On,
        PEqualNP.Outside.L_lib_1345.nots_or]
      try omega
    · simp only [List.length_append, List.length_singleton]
      have : D.1.length + 4 ≤ 4 * q := Ds
      omega
    · intro u hu
      have value : ∀ v : List Bool, v.length = N →
          (PEqualNP.Outside.L_lib_1345.run
            (D.1 ++ (O.1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [O.2, D.2]⟩])) v).getD
              (N + D.1.length + O.1.length) false =
          ((v.getD (W+(2*q-1)) false || I.any (fun i => v.getD i false)) ||
            (PEqualNP.Outside.L_lib_1345.run D.1 v).getD D.2 false) := by
        intro v hv
        have Ov := (ospec v hv).1
        rw [run1 v hv, ← hO] at Ov
        have lO : (PEqualNP.Outside.L_lib_1345.run O.1 (PEqualNP.Outside.L_lib_1345.run D.1 v)).length
            = N + D.1.length + O.1.length := by
          rw [PEqualNP.Outside.L_lib_1345.run_length, run1 v hv]
        rw [PEqualNP.Outside.L_lib_1345.run_append, PEqualNP.Outside.L_lib_1345.run_append,
          PEqualNP.Outside.L_lib_1345.run_cons, PEqualNP.Outside.L_lib_1345.run_nil, ← lO,
          PEqualNP.Outside.L_lib_1345.getD_snoc]
        have keep : (PEqualNP.Outside.L_lib_1345.run O.1 (PEqualNP.Outside.L_lib_1345.run D.1 v)).getD D.2 false
            = (PEqualNP.Outside.L_lib_1345.run D.1 v).getD D.2 false :=
          PEqualNP.Outside.L_lib_1345.run_old _ _ _ (by rw [run1 v hv]; exact Do)
        have old : ∀ i, i < N → (PEqualNP.Outside.L_lib_1345.run D.1 v).getD i false = v.getD i false :=
          fun i hi => PEqualNP.Outside.L_lib_1345.run_old _ _ _ (by omega)
        have anyold : I.any (fun i => (PEqualNP.Outside.L_lib_1345.run D.1 v).getD i false)
            = I.any (fun i => v.getD i false) := by
          rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
          constructor
          · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rwa [old i (hIlt i hi)] at h⟩
          · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rwa [old i (hIlt i hi)]⟩
        simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
          List.any_cons, List.any_nil, Bool.or_false, id]
        rw [keep, Ov, anyold, old _ (by omega)]
      rcases hRE u hu with hu | ⟨M, hM, hu⟩
      · obtain ⟨j, hj', h1, h2⟩ := hOE u hu
        rw [h1]
        have Dv := (spec j hj'.1 hj'.2).1
        rw [hlen, ← hD] at Dv
        have noany : I.any (fun i => (raw z j).getD i false) = false := by
          rw [List.any_eq_false]
          intro i hi
          rw [hI] at hi
          obtain ⟨s, _, rfl⟩ := List.mem_map.1 hi
          rw [hbank, hz]; simp
        rw [value _ (hlen _ _), hfalse, noany, Dv, Bool.eq_iff_iff, h2]
        simp
      · obtain ⟨f, x, hx, hxv⟩ := hCE M u hu
        rw [hx]
        obtain ⟨a, ha⟩ := hhit M hM
        simp only [Finset.mem_inter] at ha
        have haM := ha.1
        have haS := ha.2
        have yes : I.any (fun i => (raw x 0).getD i false) = true := by
          rw [List.any_eq_true]
          refine ⟨pos a (f ⟨a,haM⟩), ?_, ?_⟩
          · rw [hI]
            exact List.mem_map.2 ⟨⟨a, f ⟨a,haM⟩⟩, Finset.mem_toList.2
              (Finset.mem_sigma.2 ⟨haS, Finset.mem_univ _⟩), rfl⟩
          · rw [hbank]; exact (hxv _ _).2 ⟨haM, rfl⟩
        show (PEqualNP.Outside.L_lib_1345.run _ (raw x 0)).getD _ false = true
        rw [value _ (hlen _ _), yes]
        simp
  · intro b hb s ⟨C, hfan, _, _, hnot, _, hrows⟩
    obtain ⟨hop, _⟩ := hops C hfan
    have hF := PEqualNP.Outside.L_lib_1345.falls C (2*q-2) N (fun i => raw z (i+1)) (fun i => hlen z _)
      (fun i _ => hmono (i+1)) hop ((Finset.range (q-1)).image (fun p => 2*p+1)) (by
        intro i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        have hp' := Finset.mem_range.1 hp
        refine ⟨by omega, ?_, ?_⟩
        · obtain ⟨c, hc, hcv⟩ := hord (2*p+1+1) (by omega) (by omega)
          exact (hrows _ hc).trans (hcv.2 (by omega))
        · obtain ⟨c, hc, hcv⟩ := hord (2*p+1+1+1) (by omega) (by omega)
          refine (hrows _ hc).trans (Bool.eq_false_iff.2 (fun h => ?_))
          have := hcv.1 h
          omega)
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range] at hF
    have h1 : 2 ^ PEqualNP.Outside.L_lib_1345.nots C.gates ≤ 2^b := Nat.pow_le_pow_right (by omega) hnot
    have h2 : 2^r ≤ 2^b := by
      have : q ≤ 2^b := by omega
      exact this
    have := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 h2
    omega
  · obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun i => W + (2*i+1) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, e = fun i => W + 2*i := ⟨_, rfl⟩
    have spec : ∀ x j, j < 2*q → _ := fun x j (hj : j < 2*q) =>
      PEqualNP.Outside.L_lib_1345.dec_spec' r (raw x j) t e (j/2) (decide (j % 2 = 1))
        (show j/2 < q by omega)
        (fun i (hi : i < q - 1) => by
          have a : 2*i+1 < 2*q-1 := by omega
          rw [hlen, ht]
          refine ⟨by simp only; omega, ?_⟩
          show (raw x j).getD (W + (2*i+1)) false = true ↔ _
          rw [hlev x j _ a]
          omega)
        (fun i (hi : i < q) => by
          have a : 2*i < 2*q-1 := by omega
          rw [hlen, he]
          refine ⟨by simp only; omega, ?_⟩
          show (raw x j).getD (W + 2*i) false = true ↔ _
          rw [hlev x j _ a, decide_eq_true_eq]
          omega)
    obtain ⟨D, hD⟩ : ∃ D, D = PEqualNP.Outside.L_lib_1345.dec r N t e := ⟨_, rfl⟩
    have S1 := spec z 0 (by omega)
    rw [hlen, ← hD] at S1
    obtain ⟨_, Dg, Do, Dn, Ds⟩ := S1
    refine hbuild (D.1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [D.2]⟩]) (N + D.1.length) (r+1) (10*q)
      ?_ ?_ ?_ ?_ ?_
    · refine PEqualNP.Outside.L_lib_1345.good_append _ _ _ Dg ?_
      refine ⟨⟨Or.inr (Or.inr rfl), by simp, fun i hi => ?_⟩, trivial⟩
      simp at hi; omega
    · simp
    · rw [PEqualNP.Outside.L_lib_1345.nots_append, Dn, PEqualNP.Outside.L_lib_1345.nots_not]
    · simp only [List.length_append, List.length_singleton]
      have : D.1.length + 4 ≤ 4 * q := Ds
      omega
    · intro u hu
      have value : ∀ x j, j < 2*q →
          (PEqualNP.Outside.L_lib_1345.run (D.1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [D.2]⟩])
            (raw x j)).getD (N + D.1.length) false = decide (j % 2 = 0) := by
        intro x j hj
        have Dv := (spec x j hj).1
        rw [hlen, ← hD] at Dv
        have l : (PEqualNP.Outside.L_lib_1345.run D.1 (raw x j)).length = N + D.1.length := by
          rw [PEqualNP.Outside.L_lib_1345.run_length, hlen]
        rw [PEqualNP.Outside.L_lib_1345.run_append, PEqualNP.Outside.L_lib_1345.run_cons,
          PEqualNP.Outside.L_lib_1345.run_nil, ← l, PEqualNP.Outside.L_lib_1345.getD_snoc]
        simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons]
        rw [Dv, Bool.eq_iff_iff]
        simp
      rcases hRE u hu with hu | ⟨M, hM, hu⟩
      · obtain ⟨j, hj', h1, h2⟩ := hOE u hu
        rw [h1]
        refine (value _ j hj'.2).trans ?_
        rw [Bool.eq_iff_iff, h2, decide_eq_true_eq]
      · obtain ⟨_, x, hx, _⟩ := hCE M u hu
        rw [hx]
        exact (value _ 0 (by omega)).trans (by simp)
