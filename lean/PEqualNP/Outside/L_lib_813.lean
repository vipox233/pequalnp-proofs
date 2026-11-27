import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_813

private def join (a b : Nat) : Nat := if a = b then a+1 else max a b

private theorem join_add (a b c : Nat) :
    join (a+c) (b+c) = join a b + c := by
  unfold join
  split_ifs <;> omega

private theorem join_mono {a b a' b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    join a b ≤ join a' b' := by
  unfold join
  split_ifs <;> omega

private theorem cheaper (a b : Nat) : min a b + 1 ≤ join a b := by
  unfold join
  split_ifs <;> omega

private inductive Tree (V A : Type)
  | done (a : A)
  | ask (v : V) (left right : Tree V A)

private def Tree.rank {V A : Type} (fee : V → Nat) (pay : A → Nat) : Tree V A → Nat
  | .done a => pay a
  | .ask v l r => fee v + join (l.rank fee pay) (r.rank fee pay)

private def Tree.eval {V A : Type} (x : V → Bool) : Tree V A → A
  | .done a => a
  | .ask v l r => if x v then r.eval x else l.eval x

private def Tree.Valid {V A : Type} (len : V → Nat) (seen : List V) (H : Nat) :
    Tree V A → Prop
  | .done _ => True
  | .ask v l r => v ∉ seen ∧ len v ≤ H ∧
      l.Valid len (v :: seen) (H-len v) ∧ r.Valid len (v :: seen) (H-len v)

private def block {V A : Type} (l r : Tree V A) : List V → Tree V A
  | [] => l
  | v :: vs => .ask v (block l r vs) (block r l vs)
termination_by vs => vs.length

private theorem block_rank {V A : Type} (fee : V → ℕ) (pay : A → ℕ)
    (v : V) (vs : List V) (l r : Tree V A) :
    (block l r (v :: vs)).rank fee pay =
      ((v :: vs).map fee).sum + vs.length + join (l.rank fee pay) (r.rank fee pay) := by
  induction vs generalizing v l r with
  | nil => simp [block, Tree.rank]
  | cons w ws ih =>
    rw [block, Tree.rank, ih w l r, ih w r l]
    have h : join (r.rank fee pay) (l.rank fee pay) = join (l.rank fee pay) (r.rank fee pay) := by
      unfold join
      split_ifs <;> omega
    rw [h]
    simp [join, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem block_eval {V A : Type} (x : V → Bool) (vs : List V) (l r : Tree V A) :
    (block l r vs).eval x =
      if (vs.map x).foldr xor false then r.eval x else l.eval x := by
  induction vs generalizing l r with
  | nil => simp [block]
  | cons v vs ih =>
    rw [block, Tree.eval, ih r l, ih l r]
    cases h : x v <;> cases hh : (vs.map x).foldr xor false <;> simp [h, hh]

private theorem valid_transport {V A : Type} (len : V → Nat) (t : Tree V A)
    {xs ys : List V} {h k : Nat} (hs : ∀ v ∈ ys, v ∈ xs) (hk : h ≤ k)
    (ht : t.Valid len xs h) : t.Valid len ys k := by
  induction t generalizing xs ys h k with
  | done => trivial
  | ask v l r il ir =>
    obtain ⟨hv, hl, ha, hb⟩ := ht
    refine ⟨fun hh => hv (hs _ hh), le_trans hl hk, il ?_ (by omega) ha, ir ?_ (by omega) hb⟩ <;>
      intro y hy <;> rcases List.mem_cons.mp hy with h | h <;> simp_all

private theorem block_valid {V A : Type} (len : V → Nat) (vs seen : List V)
    (H : Nat) (l r : Tree V A) (hvs : vs.Nodup)
    (hs : ∀ v ∈ vs, v ∉ seen) (hh : (vs.map len).sum ≤ H)
    (hl : l.Valid len (vs ++ seen) (H - (vs.map len).sum))
    (hr : r.Valid len (vs ++ seen) (H - (vs.map len).sum)) :
    (block l r vs).Valid len seen H := by
  induction vs generalizing l r seen H with
  | nil => simpa [block] using hl
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hvs
    simp only [List.map_cons, List.sum_cons] at hh hl hr
    have dis : ∀ w ∈ vs, w ∉ v :: seen := by
      intro w hw hm
      rcases List.mem_cons.mp hm with he | he
      · exact hv (he ▸ hw)
      · exact hs w (by simp [hw]) he
    have incl : ∀ w ∈ vs ++ v :: seen, w ∈ (v :: vs) ++ seen := by
      simp only [List.mem_append, List.mem_cons]
      tauto
    have l' := valid_transport len l incl (show H - (len v + (vs.map len).sum) ≤ H - len v - (vs.map len).sum by omega) hl
    have r' := valid_transport len r incl (show H - (len v + (vs.map len).sum) ≤ H - len v - (vs.map len).sum by omega) hr
    rw [block, Tree.Valid]
    exact ⟨hs v (by simp), by omega, ih _ _ _ _ hvs dis (by omega) l' r',
      ih _ _ _ _ hvs dis (by omega) r' l'⟩

private abbrev Raw {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

private def bits {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : List (Raw w) :=
  List.ofFn (fun j : Fin (w i) => ⟨i,j⟩)

private def expand {n : ℕ} (w : Fin n → ℕ) {A : Type} : Tree (Fin n) A → Tree (Raw w) A
  | .done a => .done a
  | .ask i l r => block (expand w l) (expand w r) (bits w i)

private theorem bits_sum {n : ℕ} (w : Fin n → ℕ) (i : Fin n) (fee : Raw w → ℕ) :
    ((bits w i).map fee).sum = ∑ j : Fin (w i), fee ⟨i,j⟩ := by
  simp [bits, List.map_ofFn, List.sum_ofFn, Function.comp_def]

private theorem expand_rank {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    {A : Type} (fee : Raw w → ℕ) (pay : A → ℕ) (t : Tree (Fin n) A) :
    (expand w t).rank fee pay =
      t.rank (fun i => (∑ j : Fin (w i), fee ⟨i,j⟩) + (w i-1)) pay := by
  induction t with
  | done => rfl
  | ask i l r il ir =>
    simp only [expand, Tree.rank]
    have hs := bits_sum w i fee
    have hlen : (bits w i).length = w i := by simp [bits]
    cases he : bits w i with
    | nil => simp [he] at hlen; exact False.elim ((Nat.ne_of_gt (hw i)) hlen.symm)
    | cons v vs =>
      rw [block_rank, il, ir]
      rw [he] at hlen hs
      simp only [List.length_cons] at hlen
      rw [hs]
      congr 2
      omega

private theorem xor_count {V : Type} (x : V → Bool) (vs : List V) :
    (vs.map x).foldr xor false = decide (Odd (vs.countP x)) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases hx : x v <;> simp [hx, ih, Nat.odd_add_one] <;> by_cases h : Odd (vs.countP x) <;> simp_all

private theorem expand_eval {n : ℕ} (w : Fin n → ℕ) {A : Type} (x : Raw w → Bool)
    (t : Tree (Fin n) A) : (expand w t).eval x =
      t.eval (fun i => decide (Odd ((Finset.univ : Finset (Fin (w i))).filter
        (fun j => x ⟨i,j⟩ = true)).card)) := by
  induction t with
  | done => rfl
  | ask i l r il ir =>
    rw [expand, block_eval, il, ir, Tree.eval, xor_count]
    have hc := (List.nodup_finRange (w i)).card_eq_countP (P := fun j => x ⟨i,j⟩ = true)
    have hall : (List.finRange (w i)).toFinset = Finset.univ := by ext; simp
    rw [hall] at hc
    rw [hc]
    simp [bits, List.ofFn_eq_map, List.countP_map, Function.comp_def]


private theorem bits_mem {n : ℕ} {w : Fin n → ℕ} {i : Fin n} {z : Raw w} :
    z ∈ bits w i ↔ z.1 = i := by
  cases z with
  | mk k j =>
    simp only [bits, List.mem_ofFn]
    constructor
    · rintro ⟨a, h⟩
      exact (congrArg Sigma.fst h).symm
    · rintro rfl; exact ⟨j,rfl⟩

private theorem expand_valid {n : ℕ} (w : Fin n → ℕ) {A : Type} (len : Raw w → ℕ)
    (t : Tree (Fin n) A) (seen : List (Fin n)) (H : ℕ)
    (ht : t.Valid (fun i => ∑ j : Fin (w i), len ⟨i,j⟩) seen H) :
    (expand w t).Valid len (seen.flatMap (bits w)) H := by
  induction t generalizing seen H with
  | done => trivial
  | ask i l r il ir =>
    obtain ⟨hnew,hcost,hl,hr⟩ := ht
    rw [expand]
    apply block_valid
    · rw [bits, List.nodup_ofFn]
      intro u v h
      simpa using h
    · intro z hz hs
      obtain ⟨k, hk, hz'⟩ := List.mem_flatMap.mp hs
      rw [bits_mem] at hz hz'
      exact hnew (hz ▸ hz' ▸ hk)
    · simpa [bits_sum] using hcost
    · simpa [bits_sum] using il (i :: seen) _ hl
    · simpa [bits_sum] using ir (i :: seen) _ hr


private def Shape (N J : Finset (List Bool)) : Prop :=
    [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

private def Search {V A : Type} (len fee : V → ℕ) (pay : A → ℕ)
    (ok : (V → Bool) → A → Prop) (H s : ℕ) : Prop :=
    ∃ (N J : Finset (List Bool)) (q : List Bool → Option V)
      (out : List Bool → A) (r : List Bool → ℕ),
      Shape N J ∧ r [] ≤ s ∧
      (∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
        (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 len)).sum ≤ H) ∧
      (∀ p ∈ J, ∃ v, q p = some v ∧
        r p = fee v + join (r (p ++ [false])) (r (p ++ [true]))) ∧
      ∀ p ∈ N \ J, r p = pay (out p) ∧ ∀ x : V → Bool,
        (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p)

private def history {V : Type} (q : List Bool → Option V) (p : List Bool) : List (Option V) :=
  List.ofFn (fun j : Fin p.length => q (p.take j.val))

private def Consistent {V : Type} (q : List Bool → Option V) (p : List Bool) (x : V → Bool) :=
  ∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)

private theorem take_snoc {p : List Bool} {b : Bool} {i : Nat} (hi : i ≤ p.length) :
    (p ++ [b]).take i = p.take i := by simp [List.take_append, Nat.sub_eq_zero_of_le hi]

private theorem hist_snoc {V : Type} (q : List Bool → Option V) (p : List Bool) (b : Bool) :
    history q (p ++ [b]) = history q p ++ [q p] := by
  apply List.ext_getElem
  · simp [history]
  · intro i h₁ h₂
    by_cases h : i < p.length
    · rw [List.getElem_append_left (by simpa only [history, List.length_ofFn] using h)]
      simp only [history, List.getElem_ofFn, take_snoc (Nat.le_of_lt h)]
    · have hi : i = p.length := by simp [history] at h₁; omega
      subst i
      rw [List.getElem_append_right (by simp only [history,List.length_ofFn,le_refl])]
      simp only [history,List.getElem_ofFn,List.length_ofFn,Nat.sub_self,List.getElem_cons_zero,take_snoc (le_refl _),List.take_length]

private theorem consistent_snoc {V : Type} (q : List Bool → Option V) (p : List Bool)
    (b : Bool) (x : V → Bool) : Consistent q (p ++ [b]) x ↔
    Consistent q p x ∧ (q p).map x = some b := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [List.get_eq_getElem, take_snoc (Nat.le_of_lt i.isLt),
        List.getElem_append_left, i.isLt] using h ⟨i.val, by simp⟩
    · simpa [List.get_eq_getElem, take_snoc, List.getElem_append_right] using h ⟨p.length, by simp⟩
  · rintro ⟨h, hb⟩ j
    by_cases hj : j.val < p.length
    · simpa [List.get_eq_getElem, take_snoc (Nat.le_of_lt hj),
        List.getElem_append_left, hj] using h ⟨j.val,hj⟩
    · have hj' : j.val = p.length := by have := j.isLt; simp at this; omega
      simpa [List.get_eq_getElem, hj', take_snoc, List.getElem_append_right] using hb

private def HasTree {V A : Type} (len fee : V → ℕ) (pay : A → ℕ)
    (ok : (V → Bool) → A → Prop) (H s : ℕ) :=
    ∃ t : Tree V A, t.Valid len [] H ∧ t.rank fee pay ≤ s ∧ ∀ x, ok x (t.eval x)

private theorem search_tree {V A : Type} (len fee : V → ℕ) (pay : A → ℕ)
    (ok : (V → Bool) → A → Prop) (H s : ℕ) :
    Search len fee pay ok H s → HasTree len fee pay ok H s := by
  classical
  rintro ⟨N,J,q,out,r,hshape,hr0,hpaths,hinternal,hleaf⟩
  let bound := N.sup List.length
  have bounded {p : List Bool} (hp : p ∈ N) : p.length ≤ bound := Finset.le_sup hp
  have build : ∀ (fuel : ℕ) (p : List Bool) (xs : List V), p ∈ N →
      bound - p.length ≤ fuel → history q p = xs.map some →
      ∃ t : Tree V A, t.Valid len xs (H-(xs.map len).sum) ∧ t.rank fee pay = r p ∧
        ∀ x, Consistent q p x → ok x (t.eval x) := by
    intro fuel
    induction fuel with
    | zero =>
      intro p xs hp hf hh
      have hn : p ∉ J := by
        intro hj
        have hb := bounded (hshape.2.2.2 p hj).1
        simp at hb
        omega
      obtain ⟨hr,ho⟩ := hleaf p (Finset.mem_sdiff.mpr ⟨hp,hn⟩)
      exact ⟨.done (out p), trivial, hr.symm, ho⟩
    | succ fuel ih =>
      intro p xs hp hf hh
      by_cases hj : p ∈ J
      · obtain ⟨v,hq,hr⟩ := hinternal p hj
        have hc (b : Bool) : p ++ [b] ∈ N := by cases b <;> simp_all [hshape.2.2.2 p hj]
        have recurse (b : Bool) := ih (p ++ [b]) (xs ++ [v]) (hc b)
          (by have hb := bounded (hc b); simp at hb ⊢; omega)
          (by simp [hist_snoc, hh, hq])
        obtain ⟨l,hl,hkl,hol⟩ := recurse false
        obtain ⟨rr,hrr,hkr,hor⟩ := recurse true
        have path := hpaths (p ++ [false]) (hc false)
        change (history q (p ++ [false])).Nodup ∧ _ at path
        rw [hist_snoc, hh, hq] at path
        have hv : v ∉ xs := by
          intro hv
          have := List.disjoint_of_nodup_append path.1 (List.mem_map.mpr ⟨v,hv,rfl⟩)
          exact this (by simp)
        have hcost : (xs.map len).sum + len v ≤ H := by
          have hh' : (List.ofFn (fun j : Fin (p ++ [false]).length =>
              (q ((p ++ [false]).take j.val)).elim 0 len)) =
              (history q (p ++ [false])).map (fun z => z.elim 0 len) := by
                simp [history, List.map_ofFn, Function.comp_def]
          rw [hh',hist_snoc,hh,hq] at path
          simpa [List.map_map, Function.comp_def] using path.2
        refine ⟨.ask v l rr, ⟨hv,by omega,?_,?_⟩,?_,?_⟩
        · apply valid_transport len l (fun _ h => by simpa [or_comm] using h) _ hl
          simp; omega
        · apply valid_transport len rr (fun _ h => by simpa [or_comm] using h) _ hrr
          simp; omega
        · simpa [Tree.rank,hkl,hkr] using hr.symm
        · intro x hx
          cases h : x v
          · simpa [Tree.eval,h] using hol x ((consistent_snoc ..).mpr ⟨hx,by simp [hq,h]⟩)
          · simpa [Tree.eval,h] using hor x ((consistent_snoc ..).mpr ⟨hx,by simp [hq,h]⟩)
      · obtain ⟨hr,ho⟩ := hleaf p (Finset.mem_sdiff.mpr ⟨hp,hj⟩)
        exact ⟨.done (out p), trivial, hr.symm, ho⟩
  obtain ⟨t,ht,hr,ho⟩ := build bound [] [] hshape.1 (by simp) (by simp [history])
  exact ⟨t,by simpa using ht,hr.le.trans hr0,fun x => ho x (by intro j; exact Fin.elim0 j)⟩

private def follow {V A : Type} (t : Tree V A) : List Bool → Option (Tree V A)
  | [] => some t
  | b :: p => match t with
    | .done _ => none
    | .ask _ l r => follow (if b then r else l) p
termination_by p => p.length

private def label {V A : Type} : Tree V A → Option V
  | .done _ => none
  | .ask v _ _ => some v

private def query {V A : Type} (t : Tree V A) (p : List Bool) : Option V :=
  (follow t p).bind label

private theorem follow_append {V A : Type} (t : Tree V A) (p d : List Bool) :
    follow t (p ++ d) = (follow t p).bind (fun u => follow u d) := by
  induction p generalizing t with
  | nil => simp [follow]
  | cons b p ih => cases t <;> simp [follow,ih]

private def nodes {V A : Type} : Tree V A → Finset (List Bool)
  | .done _ => {[]}
  | .ask _ l r => insert [] ((nodes l).image (false :: ·) ∪ (nodes r).image (true :: ·))

private theorem nodes_spec {V A : Type} (t : Tree V A) (p : List Bool) :
    p ∈ nodes t ↔ (follow t p).isSome := by
  induction t generalizing p with
  | done a => cases p <;> simp [nodes, follow]
  | ask v l r il ir =>
    cases p with
    | nil => simp [nodes,follow]
    | cons b p => cases b <;> simp [nodes,follow,← il,← ir]

private theorem history_cons {V A : Type} (v : V) (l r : Tree V A) (b : Bool) (p : List Bool) :
    history (query (.ask v l r)) (b :: p) =
      some v :: history (query (if b then r else l)) p := by
  simp [history, List.ofFn_succ, query, label, follow]

private theorem consistent_cons {V A : Type} (v : V) (l r : Tree V A) (b : Bool) (p : List Bool)
    (x : V → Bool) : Consistent (query (.ask v l r)) (b :: p) x ↔
    x v = b ∧ Consistent (query (if b then r else l)) p x := by
  simp [Consistent, Fin.forall_fin_succ, query, label, follow]

private theorem leaf_outputs {V A : Type} {x : V → Bool} (t : Tree V A) (p : List Bool) (a : A)
    (hf : follow t p = some (.done a)) (hc : Consistent (query t) p x) :
    t.eval x = a := by
  induction p generalizing t with
  | nil => have he : t = .done a := by simpa [follow] using hf
           simp [he,Tree.eval]
  | cons b p ih =>
    cases t with
    | done => simp [follow] at hf
    | ask v l r =>
      obtain ⟨hv,hc⟩ := (consistent_cons ..).mp hc
      cases b <;> simpa [Tree.eval,hv] using ih _ (by simpa [follow] using hf) (by simpa using hc)

private theorem valid_path {V A : Type} (t : Tree V A) (len : V → ℕ) (seen : List V)
    (H : ℕ) (hv : t.Valid len seen H) (hn : seen.Nodup) (p : List Bool)
    (hp : p ∈ nodes t) : ∃ xs : List V, history (query t) p = xs.map some ∧
      (xs.reverse ++ seen).Nodup ∧ (xs.map len).sum ≤ H := by
  induction p generalizing t seen H with
  | nil => exact ⟨[],by simp [history],by simpa using hn,by simp⟩
  | cons b p ih =>
    cases t with
    | done => simp [nodes] at hp
    | ask v l r =>
      obtain ⟨hnew,hcost,hl,hr⟩ := hv
      have hc : (if b then r else l).Valid len (v :: seen) (H-len v) := by cases b <;> assumption
      have hs : p ∈ nodes (if b then r else l) := by
        rw [nodes_spec] at hp ⊢
        simpa [follow] using hp
      obtain ⟨xs,hist,hxs,hlen⟩ := ih _ _ _ hc (List.nodup_cons.mpr ⟨hnew,hn⟩) hs
      exact ⟨v :: xs,by simp [history_cons,hist],by simpa using hxs,by simp; omega⟩

private theorem tree_search {V A : Type} (len fee : V → ℕ) (pay : A → ℕ)
    (ok : (V → Bool) → A → Prop) (H s : ℕ) :
    HasTree len fee pay ok H s → Search len fee pay ok H s := by
  classical
  rintro ⟨t,ht,hs,hgood⟩
  let J := (nodes t).filter (fun p => (query t p).isSome)
  let out (p : List Bool) := ((follow t p).getD t).eval (fun _ => false)
  let r (p : List Bool) := ((follow t p).getD t).rank fee pay
  refine ⟨nodes t,J,query t,out,r,?_,?_,?_,?_,?_⟩
  · refine ⟨(nodes_spec ..).mpr (by simp [follow]), Finset.filter_subset ..,?_,?_⟩
    · intro p b hp
      rw [nodes_spec,follow_append] at hp
      obtain h | ⟨u,h⟩ := (follow t p).eq_none_or_eq_some
      · simp [h] at hp
      cases u with
      | done a => simp [h,follow] at hp
      | ask v l rr => exact Finset.mem_filter.mpr ⟨(nodes_spec ..).mpr (by simp [h]), by simp [query,h,label]⟩
    · intro p hp
      obtain ⟨hnode,hquery⟩ := Finset.mem_filter.mp hp
      obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((nodes_spec ..).mp hnode)
      cases u <;> simp_all [query,label,nodes_spec,follow_append,follow]
  · simpa [r,follow] using hs
  · intro p hp
    obtain ⟨xs,hh,hn,hcost⟩ := valid_path t len [] H ht (by simp) p hp
    change (history (query t) p).Nodup ∧ _
    rw [hh]
    constructor
    · exact (by simpa using hn : xs.Nodup).map (fun _ _ h => Option.some.inj h)
    · have hl : List.ofFn (fun j : Fin p.length => ((query t) (p.take j.val)).elim 0 len) =
          (history (query t) p).map (fun z => z.elim 0 len) := by
            simp [history,List.map_ofFn,Function.comp_def]
      simpa [hl,hh,List.map_map,Function.comp_def] using hcost
  · intro p hp
    obtain ⟨hnode,hquery⟩ := Finset.mem_filter.mp hp
    obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((nodes_spec ..).mp hnode)
    cases u with
    | done a => simp [query,label,hu] at hquery
    | ask v l rr => exact ⟨v,by simp [query,hu,label],by simp [r,hu,follow_append,follow,Tree.rank]⟩
  · intro p hp
    obtain ⟨hnode,hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((nodes_spec ..).mp hnode)
    cases u with
    | ask v l rr => exact False.elim (hnot (Finset.mem_filter.mpr ⟨hnode,by simp [query,hu,label]⟩))
    | done a =>
      refine ⟨by simp [r,out,hu,Tree.rank,Tree.eval],?_⟩
      intro x hx
      have hh := leaf_outputs t p a hu hx
      simpa [out,hu,Tree.eval,hh] using hgood x

private def full {n : ℕ} {w : Fin n → ℕ} (S : Finset (Raw w)) (i : Fin n) : Prop :=
  ∀ j : Fin (w i), (⟨i,j⟩ : Raw w) ∈ S

private instance {n : ℕ} {w : Fin n → ℕ} (S : Finset (Raw w)) (i : Fin n) : Decidable (full S i) :=
  inferInstanceAs (Decidable (∀ j : Fin (w i), (⟨i,j⟩ : Raw w) ∈ S))

private def localBank {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) (S : Finset (Raw w)) (i : Fin n) :=
  if full S i then 0 else ∑ j : Fin (w i), if (⟨i,j⟩ : Raw w) ∈ S then c ⟨i,j⟩ else 0

private def bank {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) (S : Finset (Raw w)) :=
  ∑ i : Fin n, localBank c S i

private theorem full_other {n : ℕ} {w : Fin n → ℕ} {S : Finset (Raw w)} {i k : Fin n}
    (j : Fin (w i)) (hk : k ≠ i) : full (insert ⟨i,j⟩ S) k ↔ full S k := by
  simp [full, Sigma.ext_iff, hk]

private theorem bank_update {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) (S : Finset (Raw w))
    (i : Fin n) (j : Fin (w i)) (hj : (⟨i,j⟩ : Raw w) ∉ S) :
    bank c S + c ⟨i,j⟩ = bank c (insert ⟨i,j⟩ S) +
      (if full (insert ⟨i,j⟩ S) i then ∑ k : Fin (w i), c ⟨i,k⟩ else 0) := by
  classical
  have hn : ¬ full S i := fun h => hj (h j)
  have hother (k : Fin n) (hk : k ≠ i) :
      localBank c S k = localBank c (insert ⟨i,j⟩ S) k := by
    simp [localBank, full_other j hk, Sigma.ext_iff, hk]
  have hsum :
      (∑ k : Fin (w i), if (⟨i,k⟩ : Raw w) ∈ S then c ⟨i,k⟩ else 0) + c ⟨i,j⟩ =
      ∑ k : Fin (w i), if (⟨i,k⟩ : Raw w) ∈ insert ⟨i,j⟩ S then c ⟨i,k⟩ else 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp only [if_neg hj,add_zero,Finset.mem_insert_self,if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    simp [hkj]
  unfold bank
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ k ∈ Finset.univ.erase i, localBank c S k) =
      ∑ k ∈ Finset.univ.erase i, localBank c (insert ⟨i,j⟩ S) k :=
    Finset.sum_congr rfl (fun k hk => hother k (Finset.mem_erase.mp hk).1)
  rw [he]
  by_cases hf : full (insert ⟨i,j⟩ S) i
  · have hlast (k : Fin (w i)) := hf k
    simp [localBank,hn,hf,hlast] at hsum ⊢
    omega
  · simp [localBank,hn,hf] at hsum ⊢
    omega


private def parity {n : ℕ} (w : Fin n → ℕ) (y : Raw w → Bool) (i : Fin n) :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)

private theorem par_congr {n : ℕ} {w : Fin n → ℕ} {a b : Raw w → Bool} (i : Fin n)
    (h : ∀ j : Fin (w i), a ⟨i,j⟩ = b ⟨i,j⟩) : parity w a i = parity w b i := by
  simp [parity,h]

private theorem par_write_other {n : ℕ} {w : Fin n → ℕ} (a : Raw w → Bool)
    (i : Fin n) (j : Fin (w i)) (b : Bool) {k : Fin n} (hk : k ≠ i) :
    parity w (Function.update a ⟨i,j⟩ b) k = parity w a k := by
  apply par_congr
  intro t
  rw [Function.update_of_ne (by simp [Sigma.ext_iff,hk])]

private theorem par_write_swap {n : ℕ} {w : Fin n → ℕ} (a : Raw w → Bool)
    (i : Fin n) (j : Fin (w i)) :
    parity w (Function.update a ⟨i,j⟩ true) i =
      !(parity w (Function.update a ⟨i,j⟩ false) i) := by
  classical
  let S := Finset.univ.filter (fun t : Fin (w i) => (Function.update a ⟨i,j⟩ false) ⟨i,t⟩ = true)
  have hj : j ∉ S := by simp [S]
  have he : Finset.univ.filter (fun t : Fin (w i) =>
        (Function.update a ⟨i,j⟩ true) ⟨i,t⟩ = true) = insert j S := by
    ext t
    by_cases h : t = j
    · subst t; simp
    · have hn : (⟨i,t⟩ : Raw w) ≠ ⟨i,j⟩ := by simpa using h
      simp [S,Function.update_of_ne hn,h]
  unfold parity
  rw [he,Finset.card_insert_of_notMem hj]
  change decide (Odd (S.card+1)) = !decide (Odd S.card)
  simp only [Nat.odd_add_one,decide_not]

private theorem par_choose {n : ℕ} {w : Fin n → ℕ} (a : Raw w → Bool)
    (i : Fin n) (j : Fin (w i)) (b : Bool) :
    ∃ d : Bool, parity w (Function.update a ⟨i,j⟩ d) i = b := by
  have h := par_write_swap a i j
  cases b <;> cases hh : parity w (Function.update a ⟨i,j⟩ false) i <;> simp_all

private def Compatible {n : ℕ} {w : Fin n → ℕ} (S : Finset (Raw w))
    (a : Raw w → Bool) (x : Fin n → Bool) := ∀ i, full S i → parity w a i = x i

private theorem complete_input {n : ℕ} {w : Fin n → ℕ} (S : Finset (Raw w))
    (a : Raw w → Bool) (x : Fin n → Bool) (hx : Compatible S a x) :
    ∃ y : Raw w → Bool, (∀ z ∈ S, y z = a z) ∧ parity w y = x := by
  classical
  have each (i : Fin n) : ∃ y : Raw w → Bool,
      (∀ z ∈ S, y z = a z) ∧ parity w y i = x i := by
    by_cases hf : full S i
    · exact ⟨a,by simp,hx i hf⟩
    · obtain ⟨j,hj⟩ : ∃ j : Fin (w i), (⟨i,j⟩ : Raw w) ∉ S := by simpa [full] using hf
      obtain ⟨d,hd⟩ := par_choose a i j (x i)
      exact ⟨Function.update a ⟨i,j⟩ d,fun z hz => Function.update_of_ne
        (show z ≠ (⟨i,j⟩ : Raw w) from fun he => hj (he ▸ hz)) ..,hd⟩
  choose y hy hp using each
  refine ⟨fun z => y z.1 z,fun z hz => hy _ _ hz,funext (fun i => ?_)⟩
  exact (par_congr i (fun _ => rfl)).trans (hp i)

private theorem compat_write {n : ℕ} {w : Fin n → ℕ} (S : Finset (Raw w))
    (a : Raw w → Bool) (i : Fin n) (j : Fin (w i)) (b : Bool) (x : Fin n → Bool)
    (hx : Compatible S a x)
    (h : full (insert ⟨i,j⟩ S) i → parity w (Function.update a ⟨i,j⟩ b) i = x i) :
    Compatible (insert ⟨i,j⟩ S) (Function.update a ⟨i,j⟩ b) x := by
  intro k hk
  by_cases he : k = i
  · subst k; exact h hk
  · rw [par_write_other a i j b he]
    exact hx k ((full_other j he).mp hk)


private def total {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) (i : Fin n) :=
  ∑ j : Fin (w i), c ⟨i,j⟩

private def toll {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) (i : Fin n) :=
  total c i + (w i - 1)

private theorem compress {n : ℕ} {w : Fin n → ℕ} {A : Type}
    (len fee : Raw w → ℕ) (pay : A → ℕ) (ok : (Fin n → Bool) → A → Prop)
    (t : Tree (Raw w) A) (seen : List (Raw w)) (outer : List (Fin n)) (H : ℕ)
    (a : Raw w → Bool) (hh : t.Valid len seen H)
    (ho : ∀ k ∈ outer, full seen.toFinset k)
    (hg : ∀ y : Raw w → Bool, (∀ z ∈ seen, y z = a z) → ok (parity w y) (t.eval y)) :
    ∃ u : Tree (Fin n) A, u.Valid (total len) outer (H + bank len seen.toFinset) ∧
      u.rank (toll fee) pay ≤ t.rank fee pay + bank (fun z => fee z + 1) seen.toFinset ∧
      ∀ x, Compatible seen.toFinset a x → ok x (u.eval x) := by
  classical
  induction t generalizing seen outer H a with
  | done ans =>
    refine ⟨.done ans,trivial,by simp [Tree.rank],?_⟩
    intro x hx
    obtain ⟨y,hy,he⟩ := complete_input _ _ _ hx
    simpa [Tree.eval,he] using hg y (fun z hz => hy z (by simpa using hz))
  | ask z l r il ir =>
    rcases z with ⟨i,j⟩
    let z : Raw w := ⟨i,j⟩
    let S := seen.toFinset
    let S' := insert z S
    let credit := fun z : Raw w => fee z + 1
    obtain ⟨hn,hcost,hl,hr⟩ := hh
    change len z ≤ H at hcost
    have hj : z ∉ S := by simpa [S,z] using hn
    have old {k : Fin n} (hk : full S k) : full S' k :=
      fun v => Finset.mem_insert_of_mem (hk v)
    have hlen := bank_update len S i j hj
    have hfee := bank_update credit S i j hj
    change bank len S + len z = bank len S' + (if full S' i then total len i else 0) at hlen
    change bank credit S + (fee z+1) = bank credit S' + (if full S' i then total credit i else 0) at hfee
    have sub (b : Bool) (outer' : List (Fin n)) (hout : ∀ k ∈ outer', full S' k) :
        ∃ u : Tree (Fin n) A, u.Valid (total len) outer' (H - len z + bank len S') ∧
          u.rank (toll fee) pay ≤ (if b then r else l).rank fee pay + bank credit S' ∧
          ∀ x, Compatible S' (Function.update a z b) x → ok x (u.eval x) := by
      have hy (y : Raw w → Bool) (hy : ∀ k ∈ z :: seen, y k = Function.update a z b k) :
          ok (parity w y) ((if b then r else l).eval y) := by
        have hzb : y z = b := by simpa using hy z (by simp)
        have hg' := hg y (fun k hk => (hy k (by simp [hk])).trans
          (Function.update_of_ne (show k ≠ z from fun he => hj (by simpa [S,← he] using hk)) ..))
        cases b <;> simpa [Tree.eval,show y ⟨i,j⟩ = _ from hzb] using hg'
      have hs' : (z :: seen).toFinset = S' := by simp [S',S]
      have hh' : ∀ k ∈ outer', full (z :: seen).toFinset k := by simpa [hs'] using hout
      cases b
      · simpa only [Bool.false_eq_true,ite_false,hs',credit] using
          il (z :: seen) outer' (H-len z) (Function.update a z false) hl hh' (by simpa using hy)
      · simpa only [ite_true,hs',credit] using
          ir (z :: seen) outer' (H-len z) (Function.update a z true) hr hh' (by simpa using hy)
    by_cases hf : full S' i
    · rw [if_pos hf] at hfee hlen
      have htc : total credit i = toll fee i + 1 := by
        have hwpos := j.isLt
        simp [total,toll,credit,Finset.sum_add_distrib]
        omega
      have hi : i ∉ outer := fun h => hj (ho i h j)
      have hout : ∀ k ∈ i :: outer, full S' k := by
        intro k hk
        rcases List.mem_cons.mp hk with h | h
        · exact h ▸ hf
        · exact old (ho _ h)
      obtain ⟨u0,hv0,hk0,hs0⟩ := sub false (i :: outer) hout
      obtain ⟨u1,hv1,hk1,hs1⟩ := sub true (i :: outer) hout
      simp only [Bool.false_eq_true,ite_false] at hk0
      simp only [ite_true] at hk1
      have hlen' : H + bank len S - total len i = H - len z + bank len S' := by omega
      have hv (l' r' : Tree (Fin n) A) (hl' : l'.Valid (total len) (i :: outer) (H - len z + bank len S'))
          (hr' : r'.Valid (total len) (i :: outer) (H - len z + bank len S')) :
          (Tree.ask i l' r').Valid (total len) outer (H + bank len S) :=
        ⟨hi,by omega,hlen'.symm ▸ hl',hlen'.symm ▸ hr'⟩
      have hjoin := join_mono hk0 hk1
      rw [join_add] at hjoin
      have hbound : toll fee i + join (u0.rank (toll fee) pay) (u1.rank (toll fee) pay) ≤
          fee z + join (l.rank fee pay) (r.rank fee pay) + bank credit S := by omega
      have hswap : parity w (Function.update a z true) i = !(parity w (Function.update a z false) i) := par_write_swap a i j
      cases h0 : parity w (Function.update a z false) i
      · refine ⟨.ask i u0 u1,hv _ _ hv0 hv1,hbound,?_⟩
        intro x hx
        cases hxv : x i
        · simpa [Tree.eval,hxv] using hs0 x (compat_write S a i j false x hx (fun _ => h0.trans hxv.symm))
        · simpa [Tree.eval,hxv] using hs1 x (compat_write S a i j true x hx (fun _ => by rw [h0] at hswap; simpa [hxv,z] using hswap))
      · have comm (a b : ℕ) : join a b = join b a := by unfold join; split_ifs <;> omega
        refine ⟨.ask i u1 u0,hv _ _ hv1 hv0,?_,?_⟩
        · simpa only [Tree.rank,comm (u1.rank ..) (u0.rank ..)] using hbound
        · intro x hx
          cases hxv : x i
          · simpa [Tree.eval,hxv] using hs1 x (compat_write S a i j true x hx (fun _ => by rw [h0] at hswap; simpa [hxv,z] using hswap))
          · simpa [Tree.eval,hxv] using hs0 x (compat_write S a i j false x hx (fun _ => h0.trans hxv.symm))
    · rw [if_neg hf] at hfee hlen
      have cheap : ∃ b : Bool, (if b then r else l).rank fee pay + 1 ≤
          join (l.rank fee pay) (r.rank fee pay) := by
        have h := cheaper (l.rank fee pay) (r.rank fee pay)
        by_cases he : l.rank fee pay ≤ r.rank fee pay
        · exact ⟨false,by simpa [min_eq_left he] using h⟩
        · exact ⟨true,by simpa [min_eq_right (by omega : r.rank fee pay ≤ l.rank fee pay)] using h⟩
      obtain ⟨b,hb⟩ := cheap
      obtain ⟨u,hv,hk,hs⟩ := sub b outer (fun k hk => old (ho k hk))
      refine ⟨u,?_,?_,fun x hx => hs x (compat_write S a i j b x hx (fun h => (hf h).elim))⟩
      · have he : H + bank len S = H-len z+bank len S' := by omega
        exact he.symm ▸ hv
      · change u.rank (toll fee) pay ≤ fee z + join (l.rank fee pay) (r.rank fee pay) + bank credit S
        omega

private theorem bank_empty {n : ℕ} {w : Fin n → ℕ} (c : Raw w → ℕ) :
    bank c ∅ = 0 := by simp [bank,localBank]

private theorem main {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    {A : Type} (ok : (Fin n → Bool) → A → Prop) (pay : A → ℕ)
    (len fee : Raw w → ℕ) (H s : ℕ) :
    Search len fee pay (fun y a => ok (parity w y) a) H s ↔
      Search (total len) (toll fee) pay ok H s := by
  constructor
  · intro hs
    obtain ⟨t,ht,hr,hg⟩ := search_tree _ _ _ _ _ _ hs
    obtain ⟨u,hu,hur,hug⟩ := compress len fee pay ok t [] [] H (fun _ => false) ht
      (by simp) (fun y _ => hg y)
    apply tree_search
    refine ⟨u, by simpa [bank_empty] using hu, ?_,?_⟩
    · exact (by simpa [bank_empty] using hur : u.rank (toll fee) pay ≤ t.rank fee pay).trans hr
    · intro x
      apply hug x
      intro i hi
      exact False.elim (by simpa using hi ⟨0,hw i⟩)
  · intro hs
    obtain ⟨t,ht,hr,hg⟩ := search_tree _ _ _ _ _ _ hs
    apply tree_search
    refine ⟨expand w t,?_,?_,?_⟩
    · simpa using expand_valid w len t [] H ht
    · rw [expand_rank w hw]
      exact hr
    · intro y
      rw [expand_eval]
      exact hg (parity w y)


end PEqualNP.Outside.L_lib_813


theorem PEqualNP.Outside.L_lib_813 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let search := fun {V Ans : Type} (len fee : V → ℕ) (pay : Ans → ℕ)
      (ok : (V → Bool) → Ans → Prop) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (q : List Bool → Option V)
      (out : List Bool → Ans) (r : List Bool → ℕ),
      shape N J ∧ r [] ≤ s ∧
      (∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
        (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 len)).sum ≤ H) ∧
      (∀ p ∈ J, ∃ v, q p = some v ∧
        r p = fee v + join (r (p ++ [false])) (r (p ++ [true]))) ∧
      ∀ p ∈ N \ J, r p = pay (out p) ∧ ∀ x : V → Bool,
        (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p)
  ∀ (Ans : Type) (ok : (Fin n → Bool) → Ans → Prop) (pay : Ans → ℕ) (lengthFee fee : Raw → ℕ) (H s : ℕ),
    search lengthFee fee pay (fun y a => ok (parity y) a) H s ↔
      search (fun i => (Finset.univ : Finset (Fin (w i))).sum (fun j => lengthFee ⟨i,j⟩))
        (fun i => ((Finset.univ : Finset (Fin (w i))).sum (fun j => fee ⟨i,j⟩)) + (w i-1))
        pay ok H s) := by
  intro n w hw
  exact fun A ok pay len fee H s => PEqualNP.Outside.L_lib_813.main w hw ok pay len fee H s
