import Mathlib
import PEqualNP.Defs

open PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_270

section TreeHelpers

private def Tree {V : Type} [DecidableEq V] (leaf : Clause V → ℕ → Prop)
    (R : Clause V) (K : ℕ) : Prop :=
  ∃ (nodes inner : Finset (List Bool)) (line : List Bool → Clause V)
    (cost : List Bool → ℕ),
    [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = R ∧ (nodes \ inner).sum cost ≤ K ∧
    (∀ p ∈ nodes, p ∉ inner → leaf (line p) (cost p)) ∧
    (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
    ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

private def treePrefix (a : Bool) : List Bool ↪ List Bool :=
  ⟨List.cons a, fun _ _ h => (List.cons.inj h).2⟩

private theorem treePrefix_apply (a : Bool) (p : List Bool) :
    treePrefix a p = a :: p := rfl

private def treeFork (S : Bool → Finset (List Bool)) : Finset (List Bool) :=
  (S false).map (treePrefix false) ∪ (S true).map (treePrefix true)

private theorem treeFork_nil (S : Bool → Finset (List Bool)) : [] ∉ treeFork S := by
  simp [treeFork, Finset.mem_map, treePrefix_apply]

private theorem treeFork_cons (S : Bool → Finset (List Bool)) (a : Bool) (p : List Bool) :
    a :: p ∈ treeFork S ↔ p ∈ S a := by
  cases a <;> simp [treeFork, Finset.mem_map, treePrefix_apply]

private theorem treeFork_sum (S : Bool → Finset (List Bool)) (f : List Bool → ℕ) :
    (treeFork S).sum f = (S false).sum (fun p => f (false :: p)) +
      (S true).sum (fun p => f (true :: p)) := by
  have hd : Disjoint ((S false).map (treePrefix false)) ((S true).map (treePrefix true)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hp
    simp [Finset.mem_map, treePrefix_apply] at hq
  unfold treeFork
  rw [Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
  simp only [treePrefix_apply]

private noncomputable def treeBranch (s : Finset (List Bool)) (a : Bool) : Finset (List Bool) :=
  s.preimage (treePrefix a) (treePrefix a).injective.injOn

private theorem treeBranch_mem (s : Finset (List Bool)) (a : Bool) (p : List Bool) :
    p ∈ treeBranch s a ↔ a :: p ∈ s := by
  simp [treeBranch, treePrefix_apply]

private theorem treeBranch_card (s : Finset (List Bool)) (a : Bool) (h : [] ∈ s) :
    (treeBranch s a).card < s.card := by
  rw [← Finset.card_map (treePrefix a)]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    exact (treeBranch_mem s a q).mp hq
  · intro heq
    rw [← heq] at h
    simp [Finset.mem_map, treePrefix_apply] at h

variable {V : Type} [DecidableEq V] {leaf : Clause V → ℕ → Prop}
variable {C D R : Clause V} {c d : ℕ}

private theorem tree_single (h : leaf C c) : Tree leaf C c := by
  refine ⟨{[]}, ∅, fun _ => C, fun _ => c, by simp, by simp, rfl, by simp, ?_, ?_, ?_⟩
  · exact fun _ _ _ => h
  · intro p a hp
    simp at hp
  · simp

private theorem tree_join (hC : Tree leaf C c) (hD : Tree leaf D d)
    (hR : IsResolvent C D R) : Tree leaf R (c + d) := by
  classical
  have input : ∀ a : Bool, Tree leaf (if a then D else C) (if a then d else c) := by
    intro a
    cases a
    · exact hC
    · exact hD
  unfold Tree at input
  choose N I L W h using input
  let line : List Bool → Clause V := fun p => match p with
    | [] => R
    | a :: q => L a q
  let cost : List Bool → ℕ := fun p => match p with
    | [] => 0
    | a :: q => W a q
  let nodes := insert [] (treeFork N)
  let inner := insert [] (treeFork I)
  have memN (a : Bool) (p : List Bool) : a :: p ∈ nodes ↔ p ∈ N a := by
    simp [nodes, treeFork_cons]
  have memI (a : Bool) (p : List Bool) : a :: p ∈ inner ↔ p ∈ I a := by
    simp [inner, treeFork_cons]
  have rootN : [] ∈ nodes := by simp [nodes]
  have rootI : [] ∈ inner := by simp [inner]
  have leafSets : nodes \ inner = treeFork (fun a => N a \ I a) := by
    ext p
    cases p with
    | nil => simp [rootI, treeFork_nil]
    | cons a p => simp [Finset.mem_sdiff, memN, memI, treeFork_cons]
  refine ⟨nodes, inner, line, cost, rootN, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    cases p with
    | nil => exact rootN
    | cons a p => exact (memN a p).mpr ((h a).2.1 ((memI a p).mp hp))
  · rw [leafSets, treeFork_sum]
    exact Nat.add_le_add (h false).2.2.2.1 (h true).2.2.2.1
  · intro p hp hn
    cases p with
    | nil => exact (hn rootI).elim
    | cons a p =>
      exact (h a).2.2.2.2.1 p ((memN a p).mp hp)
        (fun hi => hn ((memI a p).mpr hi))
  · intro p a hp
    cases p with
    | nil => exact rootI
    | cons b p =>
      exact (memI b p).mpr ((h b).2.2.2.2.2.1 p a ((memN b (p ++ [a])).mp hp))
  · intro p hp
    cases p with
    | nil =>
      refine ⟨(memN false []).mpr (h false).1, (memN true []).mpr (h true).1, ?_⟩
      change IsResolvent (L false []) (L true []) R
      rw [(h false).2.2.1, (h true).2.2.1]
      exact hR
    | cons a p =>
      obtain ⟨hf, ht, hr⟩ := (h a).2.2.2.2.2.2 p ((memI a p).mp hp)
      exact ⟨(memN a _).mpr hf, (memN a _).mpr ht, hr⟩

private theorem tree_induct (P : Clause V → ℕ → Prop)
    (hLeaf : ∀ {A k}, leaf A k → P A k)
    (hResolve : ∀ {A B Q k l}, IsResolvent A B Q → P A k → P B l → P Q (k + l))
    (hMono : ∀ {A k l}, k ≤ l → P A k → P A l) : Tree leaf C c → P C c := by
  have go : ∀ n : ℕ, ∀ (nodes inner : Finset (List Bool))
      (line : List Bool → Clause V) (cost : List Bool → ℕ),
      nodes.card = n → [] ∈ nodes → inner ⊆ nodes →
      (∀ p ∈ nodes, p ∉ inner → leaf (line p) (cost p)) →
      (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) →
      (∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
        IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) →
      P (line []) ((nodes \ inner).sum cost) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro nodes inner line cost hn root sub leaves parent children
      by_cases hi : [] ∈ inner
      · obtain ⟨hf, ht, hr⟩ := children [] hi
        have child (a : Bool) (ha : [a] ∈ nodes) :
            P (line [a]) ((treeBranch nodes a \ treeBranch inner a).sum
              (fun p => cost (a :: p))) := by
          have hcard : (treeBranch nodes a).card < n := hn ▸ treeBranch_card nodes a root
          refine ih (treeBranch nodes a).card hcard
            (treeBranch nodes a) (treeBranch inner a) (fun p => line (a :: p))
            (fun p => cost (a :: p)) rfl ((treeBranch_mem nodes a []).mpr ha) ?_ ?_ ?_ ?_
          · intro p hp
            exact (treeBranch_mem nodes a p).mpr (sub ((treeBranch_mem inner a p).mp hp))
          · intro p hp hpi
            exact leaves _ ((treeBranch_mem nodes a p).mp hp)
              (fun h => hpi ((treeBranch_mem inner a p).mpr h))
          · intro p b hp
            exact (treeBranch_mem inner a p).mpr
              (parent (a :: p) b ((treeBranch_mem nodes a (p ++ [b])).mp hp))
          · intro p hp
            obtain ⟨hpf, hpt, hpr⟩ := children (a :: p) ((treeBranch_mem inner a p).mp hp)
            exact ⟨(treeBranch_mem nodes a _).mpr hpf, (treeBranch_mem nodes a _).mpr hpt, hpr⟩
        have split : nodes \ inner = treeFork (fun a => treeBranch nodes a \ treeBranch inner a) := by
          ext p
          cases p with
          | nil => simp [hi, treeFork_nil]
          | cons a p => simp [Finset.mem_sdiff, treeFork_cons, treeBranch_mem]
        rw [split, treeFork_sum]
        exact hResolve hr (child false hf) (child true ht)
      · have onlyRoot : ∀ p ∈ nodes, p = ([] : List Bool) := by
          intro p
          refine List.reverseRecOn (motive := fun q => q ∈ nodes → q = []) p (fun _ => rfl) ?_
          intro q a ihq hp
          have hq := parent q a hp
          have hnil := ihq (sub hq)
          rw [hnil] at hq
          exact (hi hq).elim
        have nodeSet : nodes = {[]} := by
          ext p
          simpa only [Finset.mem_singleton] using
            (show p ∈ nodes ↔ p = [] from ⟨onlyRoot p, fun e => e.symm ▸ root⟩)
        have leafSet : nodes \ inner = {[]} := by
          rw [nodeSet]
          ext p
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨And.left, fun e => ⟨e, e.symm ▸ hi⟩⟩
        rw [leafSet, Finset.sum_singleton]
        exact hLeaf (leaves [] root hi)
  rintro ⟨nodes, inner, line, cost, root, sub, eq, bound, leaves, parent, children⟩
  rw [← eq]
  exact hMono bound (go nodes.card nodes inner line cost rfl root sub leaves parent children)

end TreeHelpers

private theorem chain_tree {V : Type} [DecidableEq V]
    (P : Clause V → ℕ → Prop) (lit : ℕ → Literal V) (N : ℕ) (hN : 0 < N)
    (hpos : ∀ j, 0 < j → j < N → (lit j).2 = true)
    (hvar : ∀ i j, i < j → j ≤ N → (lit i).1 ≠ (lit j).1)
    (hstep : ∀ j, j < N → P {((lit j).1, !(lit j).2), lit (j + 1)} 1)
    (hres : ∀ {C D R c d}, IsResolvent C D R → P C c → P D d → P R (c + d)) :
    P {((lit 0).1, !(lit 0).2), lit N} N := by
  have hprefix : ∀ k, k + 1 ≤ N → P {((lit 0).1, !(lit 0).2), lit (k + 1)} (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact hstep 0 hN
    | succ j ih =>
      intro hj
      let a : Literal V := ((lit 0).1, !(lit 0).2)
      let b : Literal V := lit (j + 1 + 1)
      let v : V := (lit (j + 1)).1
      have hs : (lit (j + 1)).2 = true := hpos (j + 1) (by omega) (by omega)
      have hp : lit (j + 1) = (v, true) := Prod.ext rfl hs
      have hn : ((lit (j + 1)).1, !(lit (j + 1)).2) = (v, false) := by
        simp [v, hs]
      have ha : (v, true) ∉ ({a} : Clause V) := by
        intro h
        have he : (v,true) = a := Finset.mem_singleton.mp h
        have hv := congrArg (fun x : Literal V => x.1) he
        exact (hvar 0 (j + 1) (by omega) (by omega)).symm hv
      have hb : (v, false) ∉ ({b} : Clause V) := by
        intro h
        have he : (v,false) = b := Finset.mem_singleton.mp h
        have hv := congrArg (fun x : Literal V => x.1) he
        exact hvar (j + 1) (j + 1 + 1) (by omega) (by omega) hv
      have hr : IsResolvent ({a, lit (j + 1)} : Clause V)
          {((lit (j + 1)).1, !(lit (j + 1)).2), b} {a, b} := by
        rw [hn, hp]
        refine ⟨v, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.pair_comm a (v, true), Finset.erase_insert ha, Finset.erase_insert hb,
          Finset.singleton_union]
      exact hres hr (ih (by omega)) (hstep (j + 1) (by omega))
  have hk : N - 1 + 1 = N := by omega
  simpa only [hk] using hprefix (N - 1) (by omega)

private def Clean {V : Type} (C : Clause V) : Prop :=
  ∀ (v : V) (b : Bool), (v,b) ∈ C → (v,!b) ∉ C

private theorem clean_subset {V : Type} {C D : Clause V} (h : D ⊆ C) (hc : Clean C) :
    Clean D :=
  fun v b hl hn => hc v b (h hl) (h hn)

private theorem clean_insert {V : Type} [DecidableEq V] {A : Clause V} {w : V} {s : Bool}
    (hA : Clean A) (hnot : (w,!s) ∉ A) : Clean (insert (w,s) A) := by
  intro v b hp hq
  rcases Finset.mem_insert.mp hp with he | hpA <;>
    rcases Finset.mem_insert.mp hq with hf | hqA
  · cases b <;> cases s <;> simp_all
  · cases he
    exact hnot hqA
  · have hv := congrArg Prod.fst hf
    have hs := congrArg Prod.snd hf
    change v = w at hv
    change (!b) = s at hs
    subst v
    subst s
    exact hnot (by simpa using hpA)
  · exact hA v b hpA hqA

private def litMap {V W : Type} (f : V → Literal W) (l : Literal V) : Literal W :=
  ((f l.1).1, if l.2 then (f l.1).2 else !(f l.1).2)

private theorem litMap_neg {V W : Type} (f : V → Literal W) (l : Literal V) :
    litMap f (l.1,!l.2) = ((litMap f l).1, !(litMap f l).2) := by
  rcases l with ⟨v,b⟩
  cases b <;> simp [litMap]

private theorem merge_pruned {W : Type} [DecidableEq W] (P : Clause W → ℕ → Prop)
    (grow : ∀ {D a b}, P D a → a ≤ b → P D b)
    (join : ∀ {D E R a b}, IsResolvent D E R → P D a → P E b → P R (a+b))
    (A B : Clause W) (w : W) (s : Bool) (a b : ℕ) (hR : Clean (A ∪ B))
    (ihA : Clean (insert (w,s) A) → ∃ D ⊆ insert (w,s) A, P D a)
    (ihB : Clean (insert (w,!s) B) → ∃ D ⊆ insert (w,!s) B, P D b) :
    ∃ D ⊆ A ∪ B, P D (a+b) := by
  have subA : A ⊆ A ∪ B := Finset.subset_union_left
  have subB : B ⊆ A ∪ B := Finset.subset_union_right
  by_cases ht : (w,s) ∈ A ∪ B
  · have hx : insert (w,s) A ⊆ A ∪ B := Finset.insert_subset_iff.mpr ⟨ht,subA⟩
    obtain ⟨D,hD,hp⟩ := ihA (clean_subset hx hR)
    exact ⟨D,hD.trans hx,grow hp (by omega)⟩
  by_cases hf : (w,!s) ∈ A ∪ B
  · have hx : insert (w,!s) B ⊆ A ∪ B := Finset.insert_subset_iff.mpr ⟨hf,subB⟩
    obtain ⟨D,hD,hp⟩ := ihB (clean_subset hx hR)
    exact ⟨D,hD.trans hx,grow hp (by omega)⟩
  have hB : (w,!(!s)) ∉ B := by simpa using fun h => ht (subB h)
  obtain ⟨D,hD,hp⟩ := ihA (clean_insert (clean_subset subA hR) (fun h => hf (subA h)))
  obtain ⟨E,hE,hq⟩ := ihB (clean_insert (clean_subset subB hR) hB)
  have hDs : D.erase (w,s) ⊆ A ∪ B := by
    intro l hl
    rcases Finset.mem_erase.mp hl with ⟨hne,hm⟩
    exact subA ((Finset.mem_insert.mp (hD hm)).resolve_left hne)
  have hEs : E.erase (w,!s) ⊆ A ∪ B := by
    intro l hl
    rcases Finset.mem_erase.mp hl with ⟨hne,hm⟩
    exact subB ((Finset.mem_insert.mp (hE hm)).resolve_left hne)
  by_cases hd : (w,s) ∈ D
  · by_cases he : (w,!s) ∈ E
    · refine ⟨D.erase (w,s) ∪ E.erase (w,!s), Finset.union_subset hDs hEs, ?_⟩
      cases s with
      | false =>
        rw [Finset.union_comm, Nat.add_comm]
        exact join ⟨w,he,hd,rfl⟩ hq hp
      | true => exact join ⟨w,hd,he,rfl⟩ hp hq
    · rw [Finset.erase_eq_of_notMem he] at hEs
      exact ⟨E,hEs,grow hq (by omega)⟩
  · rw [Finset.erase_eq_of_notMem hd] at hDs
    exact ⟨D,hDs,grow hp (by omega)⟩

private theorem project_resolvent {V W : Type} [DecidableEq V] [DecidableEq W]
    (P : Clause W → ℕ → Prop)
    (grow : ∀ {D a b}, P D a → a ≤ b → P D b)
    (join : ∀ {D E R a b}, IsResolvent D E R → P D a → P E b → P R (a+b))
    (f : V → Literal W) {C D R : Clause V} {a b : ℕ} (h : IsResolvent C D R)
    (ihC : Clean (C.image (litMap f)) → ∃ E ⊆ C.image (litMap f), P E a)
    (ihD : Clean (D.image (litMap f)) → ∃ E ⊆ D.image (litMap f), P E b)
    (hR : Clean (R.image (litMap f))) : ∃ E ⊆ R.image (litMap f), P E (a+b) := by
  obtain ⟨v,hpos,hneg,rfl⟩ := h
  rw [Finset.image_union] at hR ⊢
  have eC : C.image (litMap f) = insert (f v) ((C.erase (v,true)).image (litMap f)) := by
    calc
      _ = (insert (v,true) (C.erase (v,true))).image (litMap f) := by rw [Finset.insert_erase hpos]
      _ = _ := by simp only [Finset.image_insert, litMap]; rfl
  have eD : D.image (litMap f) = insert ((f v).1, !(f v).2) ((D.erase (v,false)).image (litMap f)) := by
    calc
      _ = (insert (v,false) (D.erase (v,false))).image (litMap f) := by rw [Finset.insert_erase hneg]
      _ = _ := by simp only [Finset.image_insert, litMap]; rfl
  rw [eC] at ihC
  rw [eD] at ihD
  exact merge_pruned P grow join _ _ (f v).1 (f v).2 a b hR ihC ihD

private def reprice {E : Type} (len : E → ℕ) (cut : ∀ e, Fin (len e))
    (q : Σ e, Fin (len e)) : ℕ :=
  if q.2 = cut q.1 then len q.1 else 0

private theorem cutoff_budget {A E : Type} [Fintype A] [Fintype E] {len : E → ℕ}
    (hlen : ∀ e, 0 < len e) (tag : A → Σ e, Fin (len e)) :
    ∃ cut : ∀ e, Fin (len e), (∑ p, reprice len cut (tag p)) ≤ Fintype.card A := by
  classical
  let count (e : E) (j : Fin (len e)) : ℕ := ∑ p : A, if tag p = ⟨e,j⟩ then 1 else 0
  have hmin (e : E) : ∃ j, ∀ i, count e j ≤ count e i := by
    have : Nonempty (Fin (len e)) := ⟨⟨0,hlen e⟩⟩
    obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ (count e) Finset.univ_nonempty
    exact ⟨j,fun i => hj i (Finset.mem_univ _)⟩
  choose cut hcut using hmin
  refine ⟨cut,?_⟩
  have reprice_sum (q : Σ e, Fin (len e)) :
      reprice len cut q = ∑ e : E, if q = ⟨e,cut e⟩ then len e else 0 := by
    obtain ⟨e,j⟩ := q
    rw [Finset.sum_eq_single e]
    · simp [reprice]
    · intro x _ hxe
      have hne : (⟨e,j⟩ : Σ e, Fin (len e)) ≠ ⟨x,cut x⟩ :=
        fun h => hxe (congrArg Sigma.fst h).symm
      simp [hne]
    · simp
  calc
    (∑ p, reprice len cut (tag p)) = ∑ e : E, len e * count e (cut e) := by
      simp_rw [reprice_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp only [count, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : tag p = ⟨e,cut e⟩ <;> simp [h]
    _ ≤ ∑ e : E, ∑ j : Fin (len e), count e j := by
      apply Finset.sum_le_sum
      intro e _
      simpa [Nat.mul_comm] using
        (Finset.sum_le_sum fun (j : Fin (len e)) (_ : j ∈ Finset.univ) => hcut e j)
    _ = ∑ q : Σ e, Fin (len e), ∑ p : A, if tag p = q then 1 else 0 := by
      exact (Fintype.sum_sigma' count).symm
    _ = Fintype.card A := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ _ : A, 1 := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_eq_single (tag p)]
          · simp
          · intro q _ hq
            simp [Ne.symm hq]
          · simp
        _ = Fintype.card A := by simp

private abbrev ChainV (n m : ℕ) := Fin n ⊕ (Fin m × ℕ)

private def chainLit {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (j : ℕ) : Literal (ChainV n m) :=
  if j = 0 then (Sum.inl (src e).1, (src e).2)
  else if j = len e then (Sum.inl (dst e).1, (dst e).2)
  else (Sum.inr (e,j), true)

private def chainStep {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (j : ℕ) : Clause (ChainV n m) :=
  {((chainLit src dst len e j).1, !(chainLit src dst len e j).2), chainLit src dst len e (j+1)}

private def baseClause {n m : ℕ} (src dst : Fin m → Fin n × Bool) (e : Fin m) :
    Clause (ChainV n m) :=
  {(Sum.inl (src e).1, !(src e).2), (Sum.inl (dst e).1, (dst e).2)}

private def unitLeaf {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (C : Clause (ChainV n m)) (c : ℕ) : Prop :=
  (∃ e j, j < len e ∧ C = chainStep src dst len e j) ∧ c = 1

private def weightedLeaf {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (C : Clause (ChainV n m)) (c : ℕ) : Prop :=
  ∃ e, C = baseClause src dst e ∧ c = len e

private def cutLeaf {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (cut : ∀ e, Fin (len e)) (C : Clause (ChainV n m)) (c : ℕ) : Prop :=
  ∃ q : Σ e, Fin (len e), C = chainStep src dst len q.1 q.2 ∧ c = reprice len cut q

private theorem chainLit_distinct {n m : ℕ} {src dst : Fin m → Fin n × Bool}
    (len : Fin m → ℕ) (e : Fin m) (hne : (src e).1 ≠ (dst e).1)
    (i j : ℕ) (hij : i < j) (hj : j ≤ len e) :
    (chainLit src dst len e i).1 ≠ (chainLit src dst len e j).1 := by
  have hj0 : j ≠ 0 := by omega
  have hiN : i ≠ len e := by omega
  have hN0 : len e ≠ 0 := by omega
  by_cases hi : i = 0 <;> by_cases hjN : j = len e <;>
    simp [chainLit, hi, hjN, hiN, hj0, hN0, hne, ne_of_lt hij]

private def chainSub {n m : ℕ} (src dst : Fin m → Fin n × Bool) {len : Fin m → ℕ}
    (cut : ∀ e, Fin (len e)) : ChainV n m → Literal (ChainV n m)
  | .inl v => (.inl v, true)
  | .inr (e,j) =>
    if j ≤ (cut e).val then (.inl (src e).1, (src e).2) else (.inl (dst e).1, (dst e).2)

private theorem map_chainLit {n m : ℕ} (src dst : Fin m → Fin n × Bool) {len : Fin m → ℕ}
    (cut : ∀ e, Fin (len e)) (e : Fin m) (j : ℕ) :
    litMap (chainSub src dst cut) (chainLit src dst len e j) =
      if j ≤ (cut e).val then (Sum.inl (src e).1, (src e).2) else (Sum.inl (dst e).1, (dst e).2) := by
  by_cases hz : j = 0
  · subst j
    cases hs : (src e).2 <;> simp [chainLit, litMap, chainSub, hs]
  by_cases hl : j = len e
  · subst j
    have h := (cut e).isLt
    have hh : ¬ len e ≤ (cut e).val := by omega
    cases hs : (dst e).2 <;> simp [chainLit, litMap, chainSub, hz, hh, hs]
  simp [chainLit, litMap, chainSub, hz, hl]

private theorem clean_cutLeaf {n m : ℕ} (src dst : Fin m → Fin n × Bool) {len : Fin m → ℕ}
    (cut : ∀ e, Fin (len e)) {C : Clause (ChainV n m)} {c : ℕ}
    (h : cutLeaf src dst len cut C c) (hc : Clean (C.image (litMap (chainSub src dst cut)))) :
    weightedLeaf src dst len (C.image (litMap (chainSub src dst cut))) c := by
  classical
  obtain ⟨⟨e,j⟩, rfl, rfl⟩ := h
  simp only [chainStep, Finset.image_insert, Finset.image_singleton, litMap_neg, map_chainLit] at hc ⊢
  by_cases hl : (j : ℕ) < (cut e).val
  · have hleft : (j : ℕ) ≤ (cut e).val := by omega
    have hright : (j : ℕ) + 1 ≤ (cut e).val := by omega
    simp only [ite_eq_left hleft, ite_eq_left hright] at hc
    exact False.elim (hc (Sum.inl (src e).1) (src e).2 (by simp) (by simp))
  by_cases hr : (cut e).val < (j : ℕ)
  · have hleft : ¬ (j : ℕ) ≤ (cut e).val := by omega
    have hright : ¬ (j : ℕ) + 1 ≤ (cut e).val := by omega
    simp only [ite_eq_right hleft, ite_eq_right hright] at hc
    exact False.elim (hc (Sum.inl (dst e).1) (dst e).2 (by simp) (by simp))
  have h : j = cut e := Fin.ext (by omega)
  subst j
  exact ⟨e, by simp [baseClause], by simp [reprice]⟩

private theorem tree_grow {V : Type} [DecidableEq V] {leaf : Clause V → ℕ → Prop}
    {C : Clause V} {a b : ℕ} (h : Tree leaf C a) (hab : a ≤ b) : Tree leaf C b := by
  obtain ⟨nodes,inner,line,cost,hr,hi,he,hb,hl,hp,hs⟩ := h
  exact ⟨nodes,inner,line,cost,hr,hi,he,hb.trans hab,hl,hp,hs⟩

private theorem expand_tree {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (h : ∀ e, 0 < len e ∧ (src e).1 ≠ (dst e).1) {C : Clause (ChainV n m)} {K : ℕ} :
    Tree (weightedLeaf src dst len) C K → Tree (unitLeaf src dst len) C K := by
  apply tree_induct (Tree (unitLeaf src dst len))
  · intro R c hc
    obtain ⟨e,rfl,rfl⟩ := hc
    have chain := chain_tree (Tree (unitLeaf src dst len)) (chainLit src dst len e) (len e)
      (h e).1
      (fun j hj hN => by simp [chainLit, ne_of_gt hj, ne_of_lt hN])
      (chainLit_distinct len e (h e).2)
      (fun j hj => tree_single (show unitLeaf src dst len (chainStep src dst len e j) 1 from
        ⟨⟨e,j,hj,rfl⟩,rfl⟩))
      (fun hr hA hB => tree_join hA hB hr)
    simpa [chainLit, baseClause, ne_of_gt (h e).1] using chain
  · exact fun hr hA hB => tree_join hA hB hr
  · exact fun hab hA => tree_grow hA hab

private theorem reweight_tree {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (hlen : ∀ e, 0 < len e) {C : Clause (ChainV n m)} {K : ℕ}
    (h : Tree (unitLeaf src dst len) C K) :
    ∃ cut, Tree (cutLeaf src dst len cut) C K := by
  classical
  obtain ⟨nodes,inner,line,cost,hr,hi,he,hb,hl,hp,hs⟩ := h
  let S := nodes \ inner
  have tags : ∀ p : ↥S, ∃ q : Σ e, Fin (len e), line p = chainStep src dst len q.1 q.2 := by
    intro p
    have hm := Finset.mem_sdiff.mp p.property
    obtain ⟨⟨e,j,hj,hline⟩,_⟩ := hl p hm.1 hm.2
    exact ⟨⟨e,⟨j,hj⟩⟩,hline⟩
  choose tag htag using tags
  obtain ⟨cut,hcut⟩ := cutoff_budget hlen tag
  let price (p : List Bool) : ℕ := if hm : p ∈ S then reprice len cut (tag ⟨p,hm⟩) else 0
  refine ⟨cut,nodes,inner,line,price,hr,hi,he,?_,?_,hp,hs⟩
  · change S.sum price ≤ K
    calc
      S.sum price = ∑ p : ↥S, reprice len cut (tag p) := by
        change S.sum price = S.attach.sum (fun p => reprice len cut (tag p))
        rw [← Finset.sum_attach S price]
        apply Finset.sum_congr rfl
        intro p _
        simp [price, p.property]
      _ ≤ Fintype.card ↥S := hcut
      _ = S.sum cost := by
        rw [Fintype.card_coe]
        calc
          S.card = S.sum (fun _ => 1) := by simp
          _ = S.sum cost := by
            apply Finset.sum_congr rfl
            intro p hp'
            have hm := Finset.mem_sdiff.mp hp'
            exact (hl p hm.1 hm.2).2.symm
      _ ≤ K := hb
  · intro p hpn hpi
    have hm : p ∈ S := Finset.mem_sdiff.mpr ⟨hpn,hpi⟩
    exact ⟨tag ⟨p,hm⟩, htag ⟨p,hm⟩, by simp [price, hm]⟩

private theorem contract_tree {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (hlen : ∀ e, 0 < len e) {K : ℕ}
    (h : Tree (unitLeaf src dst len) ∅ K) : Tree (weightedLeaf src dst len) ∅ K := by
  obtain ⟨cut,ht⟩ := reweight_tree src dst len hlen h
  let image (C : Clause (ChainV n m)) := C.image (litMap (chainSub src dst cut))
  let P (C : Clause (ChainV n m)) (c : ℕ) :=
    Clean (image C) → ∃ D ⊆ image C, Tree (weightedLeaf src dst len) D c
  have hproj : P ∅ K := by
    refine tree_induct P ?_ ?_ ?_ ht
    · intro C c hleaf hc
      exact ⟨image C,Finset.Subset.rfl,tree_single (clean_cutLeaf src dst cut hleaf hc)⟩
    · intro A B R a b hr hA hB hc
      exact project_resolvent (Tree (weightedLeaf src dst len)) tree_grow
        (fun hr' hD hE => tree_join hD hE hr') (chainSub src dst cut) hr hA hB hc
    · intro C a b hab hA hc
      obtain ⟨D,hD,hP⟩ := hA hc
      exact ⟨D,hD,tree_grow hP hab⟩
  obtain ⟨D,hD,hP⟩ := hproj (by simp [Clean,image])
  have he : D = ∅ := by simpa [image] using hD
  simpa [he] using hP

private theorem answer (n m : ℕ) (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (h : ∀ e, 0 < len e ∧ (src e).1 ≠ (dst e).1) (K : ℕ) :
    Tree (unitLeaf src dst len) ∅ K ↔ Tree (weightedLeaf src dst len) ∅ K :=
  ⟨contract_tree src dst len (fun e => (h e).1), expand_tree src dst len h⟩

end PEqualNP.Outside.L_pcx_270

theorem PEqualNP.Outside.L_pcx_270 :
∀ (n m : ℕ) (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ),
  (∀ e, 0 < len e ∧ (src e).1 ≠ (dst e).1) →
  let V := Fin n ⊕ (Fin m × ℕ)
  let lit := fun (e : Fin m) (j : ℕ) =>
    if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
    else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
    else ((Sum.inr (e,j) : V), true)
  let step := fun (e : Fin m) (j : ℕ) =>
    ({((lit e j).1, !(lit e j).2), lit e (j+1)} : PEqualNP.ProofComplexity.Clause V)
  let big : Set (PEqualNP.ProofComplexity.Clause V) := {C | ∃ e j, j < len e ∧ C = step e j}
  let base := fun clauseIndex : Fin m =>
    ({((Sum.inl (src clauseIndex).1 : V), !(src clauseIndex).2), ((Sum.inl (dst clauseIndex).1 : V), (dst clauseIndex).2)} :
      PEqualNP.ProofComplexity.Clause V)
  Function.Injective base →
  let tree := fun (leaf : PEqualNP.ProofComplexity.Clause V → ℕ → Prop) (K : ℕ) =>
    ∃ (nodes inner : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause V)
      (cost : List Bool → ℕ), [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (nodes \ inner).sum cost ≤ K ∧
      (∀ p ∈ nodes, p ∉ inner → leaf (line p) (cost p)) ∧
      (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
      ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
        PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)
  ∀ K : ℕ,
    tree (fun C charge => C ∈ big ∧ charge = 1) K ↔
    tree (fun D price => ∃ idx, D = base idx ∧ price = len idx) K := by
  intro n m src dst len h V lit step big base _ tree K
  exact PEqualNP.Outside.L_pcx_270.answer n m src dst len h K
