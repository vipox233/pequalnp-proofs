import Mathlib
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


-- Circuit helpers adapted from da8a4af6535bd5099ea39fa69ebe754d0698eee6,
-- lean/PEqualNP/Outside/L_lib_1345.lean (uniform bank widths here).
namespace PEqualNP.Outside.L_lib_1346_aux

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


open scoped BigOperators

private def loss {α : Type*} (E : Finset (Finset α)) (D : ℤ) (x : α → ℤ) : ℤ :=
  ∑ M ∈ E, ∏ a ∈ M, (D - x a)

private def shift {α : Type*} [DecidableEq α] (x : α → ℤ) (i j : α) (u : ℤ) (a : α) : ℤ :=
  if a = i then x a + u else if a = j then x a - u else x a

private theorem shift_sum {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℤ)
    {i j : α} (ij : i ≠ j) (u : ℤ) : ∑ a, shift x i j u a = ∑ a, x a := by
  have e (a : α) : shift x i j u a = x a + (if a = i then u else 0) - (if a = j then u else 0) := by
    by_cases ai : a = i
    · subst a; simp [shift, ij]
    · by_cases aj : a = j <;> simp [shift, ai, aj, ij.symm]
  simp [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem edge_shift {α : Type*} [DecidableEq α] (M : Finset α) (D : ℤ) (x : α → ℤ)
    {i j : α} (ij : i ≠ j) (u : ℤ) :
    (∏ a ∈ M, (D - shift x i j u a)) =
      (if i ∈ M then D-x i-u else 1) * (if j ∈ M then D-x j+u else 1) *
        ∏ a ∈ ((M.erase i).erase j), (D - x a) := by
  have tail : (∏ a ∈ ((M.erase i).erase j), (D - shift x i j u a)) =
      ∏ a ∈ ((M.erase i).erase j), (D - x a) := by
    apply Finset.prod_congr rfl
    intro a ha
    have aj := (Finset.mem_erase.1 ha).1
    have ai := (Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).1
    simp [shift, ai, aj]
  have ej : (∏ a ∈ M.erase i, (D - shift x i j u a)) =
      (if j ∈ M then D-x j+u else 1) * ∏ a ∈ ((M.erase i).erase j), (D - x a) := by
    by_cases hj : j ∈ M
    · have hm : j ∈ M.erase i := Finset.mem_erase.2 ⟨ij.symm,hj⟩
      rw [← Finset.mul_prod_erase _ _ hm, tail]
      simp only [shift, if_neg ij.symm, if_true, if_pos hj]
      congr 1
      ring
    · have hm : j ∉ M.erase i := fun h => hj (Finset.mem_erase.1 h).2
      simpa [hj, Finset.erase_eq_of_notMem hm] using tail
  by_cases hi : i ∈ M
  · rw [← Finset.mul_prod_erase _ _ hi, ej]
    simp [shift, hi, sub_add_eq_sub_sub, mul_assoc]
  · simpa [hi, Finset.erase_eq_of_notMem hi] using ej

private theorem exchange {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (D : ℤ) (x : α → ℤ) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ D)
    {i j : α} (ij : i ≠ j) (hi : 0 < x i ∧ x i < D) (hj : 0 < x j ∧ x j < D) :
    ∃ y : α → ℤ, (∀ a, 0 ≤ y a ∧ y a ≤ D) ∧ (∑ a, y a) = ∑ a, x a ∧
      loss E D y ≤ loss E D x ∧
      (Finset.univ.filter (fun a => 0 < y a ∧ y a < D)).card <
        (Finset.univ.filter (fun a => 0 < x a ∧ x a < D)).card := by
  let L := min (x i) (D - x j)
  let R := min (D - x i) (x j)
  have hL : 0 < L := lt_min hi.1 (by omega)
  have hR : 0 < R := lt_min (by omega) hj.1
  have bound {u : ℤ} (lo : -L ≤ u) (up : u ≤ R) : ∀ a, 0 ≤ shift x i j u a ∧ shift x i j u a ≤ D := by
    have ll : L ≤ x i := min_le_left ..
    have lr : L ≤ D - x j := min_le_right ..
    have rl : R ≤ D - x i := min_le_left ..
    have rr : R ≤ x j := min_le_right ..
    intro a
    by_cases ai : a = i
    · subst a; simp only [shift, if_pos rfl, if_neg ij]; omega
    · by_cases aj : a = j
      · subst a; simp only [shift, if_neg ij.symm, if_pos rfl]; omega
      · simpa [shift, ai, aj] using hx a
  have edge (M : Finset α) :
      R * (∏ a ∈ M, (D - shift x i j (-L) a)) + L * (∏ a ∈ M, (D - shift x i j R a)) ≤
      (R+L) * (∏ a ∈ M, (D - shift x i j 0 a)) := by
    rw [edge_shift M D x ij, edge_shift M D x ij, edge_shift M D x ij]
    let P := ∏ a ∈ ((M.erase i).erase j), (D - x a)
    have hp : 0 ≤ P := Finset.prod_nonneg (fun a _ => sub_nonneg.2 (hx a).2)
    by_cases hm : i ∈ M <;> by_cases hn : j ∈ M <;> simp only [hm, hn, if_true, if_false]
    · have H : 0 ≤ R*L*(R+L)*P := mul_nonneg
          (mul_nonneg (mul_nonneg hR.le hL.le) (by omega)) hp
      change R * ((D - x i - -L) * (D - x j + -L) * P) + L * ((D - x i - R) * (D - x j + R) * P) ≤ _
      linear_combination H
    all_goals apply le_of_eq; ring
  have conc : R * loss E D (shift x i j (-L)) + L * loss E D (shift x i j R) ≤ (R+L) * loss E D x := by
    have H := Finset.sum_le_sum (s := E) (fun M _ => edge M)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at H
    have e : shift x i j 0 = x := by funext a; simp [shift]
    rw [e] at H
    exact H
  have chooseSide : ∃ u, (u = -L ∨ u = R) ∧ loss E D (shift x i j u) ≤ loss E D x := by
    by_contra! h
    have h1 := mul_lt_mul_of_pos_left (h (-L) (Or.inl rfl)) hR
    have h2 := mul_lt_mul_of_pos_left (h R (Or.inr rfl)) hL
    have H := add_lt_add h1 h2
    rw [← add_mul] at H
    exact (not_lt_of_ge conc) H
  obtain ⟨u, hu, hlu⟩ := chooseSide
  refine ⟨shift x i j u, bound (by rcases hu with rfl | rfl <;> omega)
    (by rcases hu with rfl | rfl <;> omega), shift_sum x ij u, hlu, ?_⟩
  have sub : Finset.univ.filter (fun a => 0 < shift x i j u a ∧ shift x i j u a < D) ⊆
      Finset.univ.filter (fun a => 0 < x a ∧ x a < D) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    by_cases ai : a = i
    · rwa [ai]
    · by_cases aj : a = j
      · rwa [aj]
      · simpa [shift, ai, aj] using ha
  have endpoint : ∃ a, (0 < x a ∧ x a < D) ∧ ¬ (0 < shift x i j u a ∧ shift x i j u a < D) := by
    rcases hu with rfl | rfl
    · rcases min_choice (x i) (D - x j) with h | h
      · refine ⟨i, hi, ?_⟩
        simp [shift, show L = x i from h]
      · refine ⟨j, hj, ?_⟩
        simp [shift, ij.symm, show L = D-x j from h]
    · rcases min_choice (D - x i) (x j) with h | h
      · refine ⟨i, hi, ?_⟩
        simp [shift, show R = D-x i from h]
      · refine ⟨j, hj, ?_⟩
        simp [shift, ij.symm, show R = x j from h]
  obtain ⟨a, ha, ha'⟩ := endpoint
  apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨sub, ?_⟩)
  intro eq
  have : a ∈ Finset.univ.filter (fun a => 0 < x a ∧ x a < D) := by simp [ha]
  rw [← eq] at this
  exact ha' (Finset.mem_filter.1 this).2

private theorem almostIntegral {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (D : ℤ) (x : α → ℤ) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ D) :
    ∃ y : α → ℤ, (∀ a, 0 ≤ y a ∧ y a ≤ D) ∧ (∑ a, y a) = ∑ a, x a ∧
      loss E D y ≤ loss E D x ∧ (Finset.univ.filter (fun a => 0 < y a ∧ y a < D)).card ≤ 1 := by
  generalize hm : (Finset.univ.filter (fun a => 0 < x a ∧ x a < D)).card = m
  induction m using Nat.strong_induction_on generalizing x with
  | ind m ih =>
    by_cases H : m ≤ 1
    · exact ⟨x, hx, rfl, le_rfl, hm ▸ H⟩
    · have H' : 1 < (Finset.univ.filter (fun a => 0 < x a ∧ x a < D)).card := by omega
      obtain ⟨i, hi, j, hj, ij⟩ := Finset.one_lt_card.1 H'
      obtain ⟨z, hz, zs, zl, zm⟩ := exchange E D x hx ij (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2
      obtain ⟨y, hy, ys, yl, ym⟩ := ih _ (by omega) z hz rfl
      exact ⟨y, hy, ys.trans zs, yl.trans zl, ym⟩

private theorem round_finish {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (D : ℤ) (h deg k t b : ℕ)
    (hD : 0 < D) (hh : 0 < h) (hM : ∀ M ∈ E, M.card = h)
    (hdeg : ∀ a : α, (E.filter (fun M => a ∈ M)).card ≤ deg)
    (hb : (b : ℤ) * ((deg : ℤ)+1) < D)
    (y : α → ℤ) (hy : ∀ a, 0 ≤ y a ∧ y a ≤ D)
    (hs : ∑ a, y a ≤ D*k+b) (hl : loss E D y ≤ t*D^h)
    (hp : (Finset.univ.filter (fun a => 0 < y a ∧ y a < D)).card ≤ 1) :
    ∃ S : Finset α, S.card ≤ k ∧ (E.filter (fun M => Disjoint M S)).card ≤ t := by
  let S := Finset.univ.filter (fun a => y a = D)
  let P := Finset.univ.filter (fun a => 0 < y a)
  have sprop (a : α) : a ∈ S ↔ y a = D := by simp [S]
  have pprop (a : α) : a ∈ P ↔ 0 < y a := by simp [P]
  have ss : S ⊆ P := fun a ha => (pprop a).2 (by rw [(sprop a).1 ha]; exact hD)
  have sumS : ∑ a ∈ S, y a = D * S.card := by
    rw [Finset.sum_congr rfl (fun a ha => (sprop a).1 ha)]
    simp [mul_comm]
  have bdS : D * S.card ≤ D*k+b := by
    calc
      _ = ∑ a ∈ S, y a := sumS.symm
      _ ≤ ∑ a, y a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => (hy a).1)
      _ ≤ _ := hs
  have bg : (b : ℤ)*(deg : ℤ) < D := by
    have := Int.natCast_nonneg b
    rw [mul_add, mul_one] at hb
    omega
  have bD : (b : ℤ) < D := by
    have H := mul_nonneg (Int.natCast_nonneg b) (Int.natCast_nonneg deg)
    rw [mul_add, mul_one] at hb
    omega
  have cs : S.card ≤ k := by
    by_contra! H
    have hh' : (k : ℤ)+1 ≤ S.card := by exact_mod_cast H
    have H' := mul_le_mul_of_nonneg_left hh' hD.le
    rw [mul_add, mul_one] at H'
    omega
  have powPos : 0 < D^(h-1) := pow_pos hD _
  have powStep : D^h = D * D^(h-1) := by
    conv_lhs => rw [show h = (h-1)+1 by omega]
    rw [pow_succ, mul_comm]
  have finish (A : Finset α) (ha : A.card ≤ k)
      (H : ((E.filter (fun M => Disjoint M A)).card : ℤ)*D^h < (t+1 : ℤ)*D^h) :
      ∃ S : Finset α, S.card ≤ k ∧ (E.filter (fun M => Disjoint M S)).card ≤ t := by
    have e := lt_of_mul_lt_mul_right H (pow_nonneg hD.le h)
    exact ⟨A, ha, by omega⟩
  by_cases cp : P.card ≤ k
  · apply finish P cp
    have H : ((E.filter (fun M => Disjoint M P)).card : ℤ)*D^h ≤ loss E D y := by
      have edge (M : Finset α) (hME : M ∈ E) :
          (if Disjoint M P then D^h else 0) ≤ ∏ a ∈ M, (D-y a) := by
        split
        · rename_i hd
          have e (a : α) (ha : a ∈ M) : y a = 0 := by
            have hn : a ∉ P := fun haP => Finset.disjoint_left.1 hd ha haP
            have H := (hy a).1
            rw [pprop] at hn
            omega
          rw [Finset.prod_congr rfl (fun a ha => show D-y a = D by rw [e _ ha, sub_zero])]
          simp [hM M hME]
        · exact Finset.prod_nonneg (fun a _ => sub_nonneg.2 (hy a).2)
      have H := Finset.sum_le_sum edge
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at H
      exact H
    have H' := H.trans hl
    have hpow : 0 < D^h := pow_pos hD _
    rw [add_mul, one_mul]
    omega
  · have ne : P ≠ S := fun e => cp (e.symm ▸ cs)
    have np : ¬ P ⊆ S := fun h => ne (Finset.Subset.antisymm h ss)
    obtain ⟨a, haP, haS⟩ := Finset.not_subset.1 np
    have hap : 0 < y a ∧ y a < D := by
      have h1 := (pprop a).1 haP
      have h2 := (hy a).2
      rw [sprop] at haS
      omega
    have uni (c : α) (hc : 0 < y c ∧ y c < D) : c = a := by
      by_contra ne'
      have mem (c : α) (hc : 0 < y c ∧ y c < D) :
          c ∈ Finset.univ.filter (fun j => 0 < y j ∧ y j < D) := by simp [hc]
      have H := Finset.one_lt_card.2 ⟨c, mem c hc, a, mem a hap, ne'⟩
      omega
    have eP : P = insert a S := by
      ext c
      rw [Finset.mem_insert, pprop, sprop]
      constructor
      · intro H
        by_cases e : y c = D
        · exact Or.inr e
        · exact Or.inl (uni c ⟨H, lt_of_le_of_ne (hy c).2 e⟩)
      · rintro (rfl | h)
        · exact hap.1
        · rwa [h]
    have ck : S.card = k := by
      have he : P.card = S.card+1 := by rw [eP, Finset.card_insert_of_notMem haS]
      omega
    have ya : y a ≤ b := by
      have H : ∑ c ∈ P, y c ≤ D*k+b :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => (hy c).1)).trans hs
      rw [eP, Finset.sum_insert haS, sumS, ck] at H
      omega
    have zeroOutside (c : α) (hc : c ∉ S) (hc' : c ≠ a) : y c = 0 := by
      have H : c ∉ P := by rw [eP, Finset.mem_insert]; exact fun e => e.elim hc' hc
      rw [pprop] at H
      have := (hy c).1
      omega
    have edge (M : Finset α) (hME : M ∈ E) :
        (if Disjoint M S then D^h else 0) ≤
          (∏ c ∈ M, (D-y c)) + (if a ∈ M then (b : ℤ)*D^(h-1) else 0) := by
      by_cases hm : Disjoint M S
      · have cz (c : α) (hc : c ∈ M) (hne : c ≠ a) : y c = 0 :=
          zeroOutside c (fun hcS => Finset.disjoint_left.1 hm hc hcS) hne
        by_cases ha : a ∈ M
        · have er : (∏ c ∈ M.erase a, (D-y c)) = D^(h-1) := by
            rw [Finset.prod_congr rfl (fun c hc => show D-y c = D by
              rw [cz _ (Finset.mem_erase.1 hc).2 (Finset.mem_erase.1 hc).1, sub_zero])]
            simp [Finset.card_erase_of_mem ha, hM M hME]
          rw [if_pos hm, if_pos ha, ← Finset.mul_prod_erase _ _ ha, er, powStep, ← add_mul]
          exact mul_le_mul_of_nonneg_right (by omega) powPos.le
        · rw [if_pos hm, if_neg ha, add_zero,
            Finset.prod_congr rfl (fun c hc => show D-y c = D by
              rw [cz _ hc (fun eq => ha (eq ▸ hc)), sub_zero])]
          simp [hM M hME]
      · rw [if_neg hm]
        apply add_nonneg (Finset.prod_nonneg (fun c _ => sub_nonneg.2 (hy c).2))
        split
        · exact mul_nonneg (Int.natCast_nonneg b) powPos.le
        · exact le_rfl
    have H := Finset.sum_le_sum edge
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at H
    have hEdge : ((E.filter (fun M => a ∈ M)).card : ℤ) ≤ deg := by exact_mod_cast hdeg a
    have hErr : ((E.filter (fun M => a ∈ M)).card : ℤ) * ((b : ℤ)*D^(h-1)) < D^h := by
      rw [powStep, ← mul_assoc, mul_comm _ (b : ℤ)]
      exact mul_lt_mul_of_pos_right ((mul_le_mul_of_nonneg_left hEdge (Int.natCast_nonneg b)).trans_lt bg) powPos
    apply finish S cs
    change _ ≤ loss E D y + _ at H
    rw [add_mul, one_mul]
    omega

theorem rounding {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (d h deg k t b : ℕ) (hh : 0 < h)
    (hM : ∀ M ∈ E, M.card = h) (hdeg : ∀ a : α, (E.filter (fun M => a ∈ M)).card ≤ deg)
    (hb : b*(deg+1) < d) (x : α → ℕ) (hx : ∀ a, x a ≤ d)
    (hs : ∑ a, x a ≤ d*k+b) (hl : ∑ M ∈ E, ∏ a ∈ M, (d-x a) ≤ t*d^h) :
    ∃ S : Finset α, S.card ≤ k ∧ (E.filter (fun M => Disjoint M S)).card ≤ t := by
  let X (a : α) : ℤ := x a
  have hX (a : α) : 0 ≤ X a ∧ X a ≤ (d : ℤ) := ⟨Int.natCast_nonneg _, by
    dsimp [X]
    exact_mod_cast hx a⟩
  obtain ⟨y, hy, hys, hyl, hyp⟩ := almostIntegral E (d : ℤ) X hX
  have HD : (0 : ℤ) < d := by exact_mod_cast (Nat.zero_le _).trans_lt hb
  have HS : ∑ a, y a ≤ (d : ℤ)*k+b := by
    rw [hys]
    dsimp only [X]
    exact_mod_cast hs
  have HL : loss E (d : ℤ) X ≤ (t : ℤ)*(d : ℤ)^h := by
    have castProd (M : Finset α) :
        (∏ a ∈ M, ((d : ℤ)-X a)) = (↑(∏ a ∈ M, (d-x a)) : ℤ) := by
      push_cast
      exact Finset.prod_congr rfl (fun a _ => by rw [Nat.cast_sub (hx a)])
    unfold loss
    simp only [castProd, ← Nat.cast_sum]
    exact_mod_cast hl
  exact round_finish E d h deg k t b HD hh hM hdeg (by exact_mod_cast hb) y hy HS (hyl.trans HL) hyp

end PEqualNP.Outside.L_lib_1346_aux

open PEqualNP.Outside.L_lib_1346_aux

theorem PEqualNP.Outside.L_lib_1346 : (
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n h r d deg : Nat) (E : Finset (Finset (Fin n))),
  let q := 2^r
  0 < h → (∀ M ∈ E, M.card = h) →
  (∀ a : Fin n, (E.filter (fun M => a ∈ M)).card ≤ deg) →
  (7*q+1)*(deg+1) < d →
  let N := n*d + (2*q-1) + 2
  let raw := fun (x : Fin n → Fin d → Bool) (j : Nat) =>
    (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++
    List.ofFn (fun g : Fin (2*q-1) => decide (g.val < j)) ++ [false,true]
  let copies := fun M : Finset (Fin n) =>
    Finset.univ.image (fun f : {a : Fin n // a ∈ M} → Fin d =>
      raw (fun a k => if h' : a ∈ M then decide (f ⟨a,h'⟩ = k) else false) 0)
  let special := E.biUnion copies
  ∀ k t : Nat,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧
      C.output < N+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ d*k+7*q ∧
      (∀ j : Nat, 1 ≤ j → j < 2*q → C.eval (raw (fun _ _ => false) j) = decide (j % 2 = 0)) ∧
      (special.filter (fun x => C.eval x = false)).card ≤ t*d^h) ↔
    ∃ S : Finset (Fin n), S.card ≤ k ∧ (E.filter (fun M => Disjoint M S)).card ≤ t
) := by
  intro n h r d deg E q hh hMcard hdeg hd N raw copies special k miss
  classical
  let width : Fin n → Nat := fun _ => d
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  obtain ⟨pos, hpb, hpx⟩ := pos_exists n width
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ a, width a := ⟨_, rfl⟩
  have hWd : W = n*d := by simp [hW, width, Nat.mul_comm]
  have hN : N = W + (2*q-1) + 2 := by rw [hWd]
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
  let row (M : Finset (Fin n)) (f : {a : Fin n // a ∈ M} → Fin d) :=
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    raw (fun a l => if ha : a ∈ M then decide (f ⟨a,ha⟩ = l) else false) 0
  have rowbit : ∀ M f a l, (row M f).getD (pos a l) false = true ↔
      ∃ ha : a ∈ M, f ⟨a,ha⟩ = l := by
    intro M f a l
    simp only [row, hbank]
    by_cases ha : a ∈ M <;> simp [ha]
  have rowinj : ∀ {M P} {f : {a : Fin n // a ∈ M} → Fin d}
      {g : {a : Fin n // a ∈ P} → Fin d}, row M f = row P g → M = P := by
    intro M P f g e
    ext a
    constructor
    · intro ha
      have H := (rowbit M f a (f ⟨a,ha⟩)).2 ⟨ha, rfl⟩
      rw [e, rowbit] at H
      exact H.choose
    · intro ha
      have H := (rowbit P g a (g ⟨a,ha⟩)).2 ⟨ha, rfl⟩
      rw [← e, rowbit] at H
      exact H.choose
  have finj : ∀ M, Function.Injective (row M) := by
    intro M f g e
    funext a
    have H := (rowbit M f a (f a)).2 ⟨a.property, rfl⟩
    rw [e, rowbit] at H
    obtain ⟨_, he⟩ := H
    exact he.symm
  have copy_eq : ∀ M, copies M = (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      Finset.univ.image (row M)) := by intro M; rfl
  have copycard : ∀ M ∈ E, (copies M).card = d^h := by
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    intro M hME
    rw [copy_eq, Finset.card_image_of_injective _ (finj M), Finset.card_univ, Fintype.card_fun]
    simp [hMcard M hME]
  constructor
  · rintro ⟨C, hfan, _, _, hnot, hsize, hlevels, hmiss⟩
    obtain ⟨hop, hin⟩ := hops C hfan
    have h0 : C.eval (raw z 0) = false := by
      cases hval : C.eval (raw z 0)
      · rfl
      · exfalso
        have hF := falls C (2*q-1) N (fun i => raw z i) (fun i => hlen z i)
          (fun i _ => hmono i) hop ((Finset.range q).image (fun p => 2*p)) (by
            intro i hi
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
            have hp' := Finset.mem_range.1 hp
            refine ⟨by omega, ?_, ?_⟩
            · rcases Nat.eq_zero_or_pos p with rfl | hp0
              · simpa using hval
              · rw [hz, hlevels _ (by omega) (by omega)]
                simp
            · rw [hz, hlevels _ (by omega) (by omega)]
              simp)
        rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range] at hF
        have : 2 ^ nots C.gates ≤ q := Nat.pow_le_pow_right (by omega) hnot
        omega
    obtain ⟨T, hT, hag⟩ := cone N C.gates hin {C.output}
    have inj : Function.Injective (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) := by
      rintro ⟨a, k1⟩ ⟨b, k2⟩ e
      simp only at e
      have H := hbank (fun c m => decide ((⟨c,m⟩ : (a : Fin n) × Fin (width a)) = ⟨a,k1⟩)) 0 a k1
      rw [e, hbank] at H
      exact (of_decide_eq_true (H.trans (decide_eq_true rfl))).symm
    have surj : ∀ t < W, ∃ b l, pos b l = t := by
      intro t ht
      have e : Finset.univ.image (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) = Finset.range W := by
        refine Finset.eq_of_subset_of_card_le (fun t ht => ?_) ?_
        · obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 ht
          rw [Finset.mem_range, hW]; exact hpb _ _
        · rw [Finset.card_image_of_injective _ inj, Finset.card_range, Finset.card_univ,
            Fintype.card_sigma, hW]
          simp
      have ht' : t ∈ Finset.range W := Finset.mem_range.2 ht
      rw [← e] at ht'
      obtain ⟨s, _, hs⟩ := Finset.mem_image.1 ht'
      exact ⟨s.1, s.2, hs⟩
    let readBank (a : Fin n) := (Finset.univ : Finset (Fin d)).filter (fun l => pos a l ∈ T)
    let unread (a : Fin n) := (Finset.univ : Finset (Fin d)) \ readBank a
    let x (a : Fin n) := (readBank a).card
    have hx : ∀ a, x a ≤ d := fun a => by
      simpa [x] using Finset.card_le_card (Finset.subset_univ (readBank a))
    have unreadCard (a : Fin n) : (unread a).card = d - x a := by
      dsimp only [unread]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [x]
    have xsum : ∑ a, x a ≤ d*k+(7*q+1) := by
      have sub : (Finset.univ.sigma readBank).image
          (fun s : (a : Fin n) × Fin (width a) => pos s.1 s.2) ⊆ T := by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
        exact (Finset.mem_filter.1 (Finset.mem_sigma.1 hs).2).2
      have H := Finset.card_le_card sub
      rw [Finset.card_image_of_injective _ inj, Finset.card_sigma] at H
      have hT' : T.card ≤ 1 + C.size := by simpa [Circuit.size] using hT
      change ∑ a, x a ≤ T.card at H
      omega
    let missedCopies (M : Finset (Fin n)) :=
      (Finset.univ : Finset ((a : {a : Fin n // a ∈ M}) → {l // l ∈ unread a.val})).image
        (fun f => row M (fun a => (f a).val))
    have missedCard (M : Finset (Fin n)) : (missedCopies M).card = ∏ a ∈ M, (d-x a) := by
      have H : Function.Injective (fun f : (a : {a : Fin n // a ∈ M}) → {l // l ∈ unread a.val} =>
          row M (fun a => (f a).val)) := by
        intro f g e
        have e' := @finj M (fun a => (f a).val) (fun a => (g a).val) e
        funext a
        exact Subtype.ext (congrFun e' a)
      dsimp only [missedCopies]
      rw [Finset.card_image_of_injective _ H, Finset.card_univ, Fintype.card_pi]
      simp only [Fintype.card_coe, unreadCard]
      exact Finset.prod_attach M (fun a => d-x a)
    let misses := (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      special.filter (fun i => C.eval i = false))
    have missedSub : E.biUnion missedCopies ⊆ misses := by
      intro u hu
      obtain ⟨M, hME, hm⟩ := Finset.mem_biUnion.1 hu
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 hm
      have mem : row M (fun a => (f a).val) ∈ misses ↔
          row M (fun a => (f a).val) ∈ special ∧ C.eval (row M (fun a => (f a).val)) = false := by
        letI : ∀ P : Prop, Decidable P := Classical.propDecidable
        exact Finset.mem_filter
      apply mem.2
      refine ⟨?_, ?_⟩
      · letI : ∀ P : Prop, Decidable P := Classical.propDecidable
        refine Finset.mem_biUnion.2 ⟨M, hME, ?_⟩
        rw [copy_eq]
        exact Finset.mem_image.2 ⟨fun a => (f a).val, Finset.mem_univ _, rfl⟩
      let v (a : Fin n) (l : Fin d) :=
        letI : ∀ P : Prop, Decidable P := Classical.propDecidable
        if ha : a ∈ M then decide ((f ⟨a,ha⟩).val = l) else false
      change C.eval (raw v 0) = false
      have agree : ∀ t ∈ T, (raw v 0).getD t false = (raw z 0).getD t false := by
        intro t ht
        by_cases htW : t < W
        · obtain ⟨b, l, rfl⟩ := surj t htW
          rw [hbank, hbank, hz]
          by_cases hb : b ∈ M
          · simp only [v, dif_pos hb, decide_eq_false_iff_not]
            intro e
            have H := (Finset.mem_sdiff.1 (f ⟨b,hb⟩).property).2
            apply H
            rw [e]
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩
          · simp [v, hb]
        · simp only [raw]
          rw [List.append_assoc, List.append_assoc,
            List.getD_append_right ((List.ofFn fun a => List.ofFn (v a)).flatten) _ _ _ (by rw [hflat]; omega),
            List.getD_append_right ((List.ofFn fun a => List.ofFn (z a)).flatten) _ _ _ (by rw [hflat]; omega),
            hflat, hflat]
      have e : C.eval (raw v 0) = C.eval (raw z 0) :=
        hag (raw v 0) (raw z 0) (hlen _ _) (hlen _ _) agree C.output (Finset.mem_singleton_self _)
      exact e.trans h0
    have dis : (↑E : Set (Finset (Fin n))).PairwiseDisjoint missedCopies := by
      intro M hM P hP hne
      refine Finset.disjoint_left.2 (fun u hu hv => ?_)
      obtain ⟨f, _, ef⟩ := Finset.mem_image.1 hu
      obtain ⟨g, _, eg⟩ := Finset.mem_image.1 hv
      exact hne (rowinj (f := fun a => (f a).val) (g := fun a => (g a).val) (ef.trans eg.symm))
    have hF : ∑ M ∈ E, ∏ a ∈ M, (d-x a) ≤ miss*d^h := by
      have H := (Finset.card_le_card missedSub).trans hmiss
      rwa [Finset.card_biUnion dis, Finset.sum_congr rfl (fun M _ => missedCard M)] at H
    have hdg (a : Fin n) : (E.filter (fun M => a ∈ M)).card ≤ deg := by
      rw [← Finset.filter_congr_decidable E (fun M => a ∈ M) (fun _ => Classical.propDecidable _)]
      exact hdeg a
    obtain ⟨S, hS, hmissS⟩ := rounding E d h deg k miss (7*q+1)
      hh hMcard hdg hd x hx xsum hF
    refine ⟨S, hS, ?_⟩
    have e := Finset.filter_congr_decidable E (fun M => Disjoint M S) (fun _ => Classical.propDecidable _)
    simpa only [e] using hmissS
  · rintro ⟨S, hSk, hmiss⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun i => W + (2*i+2) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, e = fun i => if 2*i+1 < 2*q-1 then W + (2*i+1) else W + (2*q-1) := ⟨_, rfl⟩
    obtain ⟨I, hI⟩ : ∃ I : List ℕ, I = (S.sigma (fun a => (Finset.univ : Finset (Fin (width a))))).toList.map
        (fun s => pos s.1 s.2) := ⟨_, rfl⟩
    have hIlen : I.length ≤ d*k := by
      rw [hI, List.length_map, Finset.length_toList, Finset.card_sigma]
      simp [width, Nat.mul_comm, Nat.mul_le_mul_left d hSk]
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
      dec_spec' r (raw z j) t e ((j-1)/2) (decide (j % 2 = 0))
        (show (j-1)/2 < q by omega) (hdec j h1 h2).1 (hdec j h1 h2).2
    obtain ⟨D, hD⟩ : ∃ D, D = dec r N t e := ⟨_, rfl⟩
    have S1 := spec 1 le_rfl (by omega)
    rw [hlen, ← hD] at S1
    obtain ⟨_, Dg, Do, Dn, Ds⟩ := S1
    obtain ⟨O, hO⟩ : ∃ O, O = orchain (W+(2*q-1)) (N + D.1.length) I := ⟨_, rfl⟩
    have hIlt : ∀ i ∈ I, i < N := by
      intro i hi
      rw [hI] at hi
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hi
      have := hpb s.1 s.2
      omega
    have run1 : ∀ u : List Bool, u.length = N →
        (run D.1 u).length = N + D.1.length := fun u hu => by
      rw [run_length, hu]
    have ospec : ∀ u : List Bool, u.length = N → _ := fun u hu =>
      orchain_spec I (run D.1 u) (W+(2*q-1))
        (by rw [run1 u hu]; omega) (fun i hi => by rw [run1 u hu]; have := hIlt i hi; omega)
    have O1 := ospec (raw z 1) (hlen _ _)
    rw [run1 _ (hlen _ _), ← hO] at O1
    obtain ⟨_, Og, Oo, On, Os⟩ := O1
    let gs : List Gate := D.1 ++ (O.1 ++ [⟨GateOp.or, [O.2, D.2]⟩])
    let out := N + D.1.length + O.1.length
    have good : Good N gs := by
      refine good_append _ _ _ Dg (good_append _ _ _ Og ?_)
      refine ⟨⟨Or.inr (Or.inl rfl), by simp, fun i hi => ?_⟩, trivial⟩
      simp at hi
      rcases hi with rfl | rfl <;> omega
    have value : ∀ v : List Bool, v.length = N →
        (run
          (D.1 ++ (O.1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [O.2, D.2]⟩])) v).getD
            (N + D.1.length + O.1.length) false =
        ((v.getD (W+(2*q-1)) false || I.any (fun i => v.getD i false)) ||
          (run D.1 v).getD D.2 false) := by
      intro v hv
      have Ov := (ospec v hv).1
      rw [run1 v hv, ← hO] at Ov
      have lO : (run O.1 (run D.1 v)).length
          = N + D.1.length + O.1.length := by
        rw [run_length, run1 v hv]
      rw [run_append, run_append, run_cons, run_nil, ← lO, getD_snoc]
      have keep : (run O.1 (run D.1 v)).getD D.2 false = (run D.1 v).getD D.2 false :=
        run_old _ _ _ (by rw [run1 v hv]; exact Do)
      have old : ∀ i, i < N → (run D.1 v).getD i false = v.getD i false :=
        fun i hi => run_old _ _ _ (by omega)
      have anyold : I.any (fun i => (run D.1 v).getD i false)
          = I.any (fun i => v.getD i false) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        constructor
        · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rwa [old i (hIlt i hi)] at h⟩
        · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rwa [old i (hIlt i hi)]⟩
      simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.any_cons, List.any_nil, Bool.or_false, id]
      rw [keep, Ov, anyold, old _ (by omega)]
    let C : Circuit := ⟨gs,out⟩
    refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      have H := good_mem gs N good g hg
      exact ⟨by simpa using H.1, H.2⟩
    · intro j hj i hi
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = gs[j]'hj :=
        List.getD_eq_getElem _ _ hj
      rw [e] at hi
      exact (good_get gs N good j hj).2.2 i hi
    · change out < N + gs.length
      simp [out, gs]; omega
    · change nots gs ≤ r
      unfold gs
      rw [nots_append, nots_append, Dn, On, nots_or]
      omega
    · change gs.length ≤ d*k+7*q
      simp only [gs, List.length_append, List.length_singleton]
      have : D.1.length + 4 ≤ 4 * q := Ds
      omega
    · intro j hj hj'
      rw [← hz]
      change (run gs (raw z j)).getD out false = _
      have Dv := (spec j hj hj').1
      rw [hlen, ← hD] at Dv
      have noany : I.any (fun i => (raw z j).getD i false) = false := by
        rw [List.any_eq_false]
        intro i hi
        rw [hI] at hi
        obtain ⟨s, _, rfl⟩ := List.mem_map.1 hi
        rw [hbank, hz]
        simp
      rw [value _ (hlen _ _), hfalse, noany, Dv]
      simp
    · letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      let bad := E.filter (fun M => Disjoint M S)
      have sub : special.filter (fun x => C.eval x = false) ⊆ bad.biUnion copies := by
        intro u hu
        obtain ⟨hu, hv⟩ := Finset.mem_filter.1 hu
        obtain ⟨M, hME, hu⟩ := Finset.mem_biUnion.1 hu
        refine Finset.mem_biUnion.2 ⟨M, Finset.mem_filter.2 ⟨hME, ?_⟩, hu⟩
        by_contra H
        obtain ⟨a, haM, haS⟩ := Finset.not_disjoint_iff.1 H
        rw [copy_eq] at hu
        obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 hu
        have yes : I.any (fun i => (row M f).getD i false) = true := by
          rw [List.any_eq_true]
          refine ⟨pos a (f ⟨a,haM⟩), ?_, (rowbit _ _ _ _).2 ⟨haM,rfl⟩⟩
          rw [hI]
          exact List.mem_map.2 ⟨⟨a, f ⟨a,haM⟩⟩, Finset.mem_toList.2
            (Finset.mem_sigma.2 ⟨haS, Finset.mem_univ _⟩), rfl⟩
        change (run gs (row M f)).getD out false = false at hv
        rw [value _ (hlen _ _), yes] at hv
        simp at hv
      calc
        _ ≤ (bad.biUnion copies).card := Finset.card_le_card sub
        _ ≤ ∑ M ∈ bad, (copies M).card := Finset.card_biUnion_le
        _ = bad.card * d^h := by
          rw [Finset.sum_congr rfl (fun M hM => copycard M (Finset.mem_filter.1 hM).1)]
          simp only [Finset.sum_const, nsmul_eq_mul]
          rfl
        _ ≤ miss*d^h := Nat.mul_le_mul_right _ hmiss
