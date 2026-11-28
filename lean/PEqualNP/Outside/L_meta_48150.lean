import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48150

abbrev Vert (n : Nat) := Finset (Fin n)

def Falls {n : Nat} (x : Vert n) (f : Vert n → Fin n → Bool) : Nat → Vert n → Prop :=
  Nat.rec (motive := fun _ => Vert n → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Vert n) (j : Fin n), j ∈ x ∧ prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      f u j = true ∧ f v j = false)

def Stable {n : Nat} (g : Fin n → Fin n → Bool) (z : Vert n) : Prop :=
  ∀ a ∈ z, ∀ b ∈ z, g a b = false

lemma extendBound {n r : Nat} {g : Fin n → Fin n → Bool} {u : Vert n} {a b : Fin n}
    (edge : g a b = true) (bound : ∀ z ⊆ u, Stable g z → z.card ≤ r) :
    ∀ z ⊆ insert a (insert b u), Stable g z → z.card ≤ r + 1 := by
  intro z hz hs
  have split : a ∉ z ∨ b ∉ z := by
    by_contra! bad
    have := hs a bad.1 b bad.2
    simp_all
  rcases split with ha | hb
  · have sub : z.erase b ⊆ u := by
      intro i hi
      obtain ⟨hne, him⟩ := Finset.mem_erase.mp hi
      simpa [Finset.mem_insert, hne, show i ≠ a from fun h => ha (h ▸ him)] using hz him
    have small := bound _ sub (fun i hi j hj => hs i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
    have := Finset.pred_card_le_card_erase (a := b) (s := z)
    omega
  · have sub : z.erase a ⊆ u := by
      intro i hi
      obtain ⟨hne, him⟩ := Finset.mem_erase.mp hi
      simpa [Finset.mem_insert, hne, show i ≠ b from fun h => hb (h ▸ him)] using hz him
    have small := bound _ sub (fun i hi j hj => hs i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
    have := Finset.pred_card_le_card_erase (a := a) (s := z)
    omega

lemma forceTwo {n r : Nat} {x u : Vert n} {f : Vert n → Fin n → Bool} {g : Fin n → Fin n → Bool}
    (free : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true)
    (hit : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (mono : ∀ s t, s ⊆ t → t ⊆ x → ∀ j ∈ x, f t j = true → f s j = true)
    (hu : u ⊆ x) (prev : Falls x f r u) {a b c : Fin n} (ha : a ∈ x) (hb : b ∈ x) (hc : c ∈ x)
    (fresh : ∀ j ∈ ({a,b,c} : Vert n), j ∉ u ∧ ∀ i ∈ u, g i j = false)
    (hac : a ≠ c) (nonedge : g a c = false) :
    Falls x f (r+2) (insert c (insert b u)) ∨ Falls x f (r+2) (insert b (insert a u)) := by
  classical
  have step {l : Nat} {s t : Vert n} {j : Fin n} (hs : Falls x f l s) (hst : s ⊆ t) (hj : j ∈ x)
      (on : f s j = true) (off : f t j = false) : Falls x f (l+1) t :=
    ⟨s, t, j, hj, hs, hst, Finset.Subset.rfl, on, off⟩
  have hbu : insert b u ⊆ x := Finset.insert_subset hb hu
  have hau : insert a u ⊆ x := Finset.insert_subset ha hu
  have hon (j) (hj : j ∈ ({a,b,c} : Vert n)) (hjx : j ∈ x) := free u hu j hjx (fresh j hj)
  cases he : f (insert b u) c with
  | true =>
    left
    exact step (step prev (Finset.subset_insert _ _) hb (hon b (by simp) hb)
      (hit _ hbu _ (by simp))) (Finset.subset_insert _ _) hc he
      (hit _ (Finset.insert_subset hc hbu) _ (by simp))
  | false =>
    right
    have hcold := fresh c (by simp)
    have hcon : f (insert a u) c = true := by
      apply free _ hau _ hc
      refine ⟨by simp [hac.symm, hcold.1], ?_⟩
      simpa [Finset.forall_mem_insert, nonedge] using hcold.2
    have hcoff : f (insert b (insert a u)) c = false := by
      cases he' : f (insert b (insert a u)) c with
      | false => rfl
      | true =>
        have := mono _ _ (Finset.insert_subset_insert _ (Finset.subset_insert a u))
          (Finset.insert_subset hb hau) c hc he'
        simp_all
    exact step (step prev (Finset.subset_insert _ _) ha (hon a (by simp) ha)
      (hit _ hau _ (by simp))) (Finset.subset_insert _ _) hc hcon hcoff

lemma manyFalls {n k : Nat} {x : Vert n} {f : Vert n → Fin n → Bool} {g : Fin n → Fin n → Bool}
    (free : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true)
    (hit : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (mono : ∀ s t, s ⊆ t → t ⊆ x → ∀ j ∈ x, f t j = true → f s j = true)
    (v : Fin k × Fin 3 → Fin n) (inj : Function.Injective v) (inside : ∀ a, v a ∈ x)
    (graph : ∀ a d, g (v a) (v d) = decide (a.1 = d.1 ∧ (a.2.val+1 = d.2.val ∨ d.2.val+1 = a.2.val))) :
    ∃ y ⊆ x, Falls x f (2*k) y ∧ ∀ z ⊆ y, Stable g z → z.card ≤ k := by
  classical
  have aux (r : Nat) (hr : r ≤ k) : ∃ y : Vert n,
      (∀ i ∈ y, ∃ d, d.1.val < r ∧ v d = i) ∧ Falls x f (2*r) y ∧
      ∀ z ⊆ y, Stable g z → z.card ≤ r := by
    induction r with
    | zero => exact ⟨∅, by simp, True.intro, by simp⟩
    | succ r ih =>
      obtain ⟨u, old, prev, bound⟩ := ih (by omega)
      let row : Fin k := ⟨r, by omega⟩
      let w := fun s : Fin 3 => v (row,s)
      have hu : u ⊆ x := by
        intro i hi
        obtain ⟨d, _, rfl⟩ := old i hi
        exact inside _
      have fresh (s : Fin 3) : w s ∉ u ∧ ∀ i ∈ u, g i (w s) = false := by
        constructor
        · intro h
          obtain ⟨d, hd, he⟩ := old _ h
          have hd' : d = (row,s) := inj he
          subst d
          exact (Nat.lt_irrefl r) hd
        · intro i hi
          obtain ⟨d, hd, rfl⟩ := old _ hi
          have hn : d.1 ≠ row := fun he => (Nat.ne_of_lt hd) (congrArg Fin.val he)
          simp [w, graph, hn]
      have rows (a b : Fin 3) : ∀ i ∈ insert (w a) (insert (w b) u), ∃ d, d.1.val < r+1 ∧ v d = i := by
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | rfl | hi
        · exact ⟨(row,a), by simp [row], rfl⟩
        · exact ⟨(row,b), by simp [row], rfl⟩
        · obtain ⟨d, hd, rfl⟩ := old _ hi
          exact ⟨d, by omega, rfl⟩
      have cases' := forceTwo free hit mono hu prev (inside (row,0)) (inside (row,1)) (inside (row,2))
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; intro j hj; rcases hj with rfl|rfl|rfl <;> apply fresh)
        (fun he => by have := congrArg Prod.snd (inj he); exact (by decide : (0 : Fin 3) ≠ 2) this)
        (by simp [graph])
      rw [Nat.mul_succ]
      rcases cases' with hc | ha
      · exact ⟨_, rows 2 1, hc, extendBound (a := w 2) (b := w 1) (by simp [w,graph]) bound⟩
      · exact ⟨_, rows 1 0, ha, extendBound (a := w 1) (b := w 0) (by simp [w,graph]) bound⟩
  obtain ⟨y, hy, falls, bound⟩ := aux k le_rfl
  refine ⟨y, ?_, falls, bound⟩
  intro i hi
  obtain ⟨d, _, rfl⟩ := hy i hi
  exact inside _

noncomputable def Alpha {n : Nat} (g : Fin n → Fin n → Bool) (y : Vert n) : Nat := by
  classical
  exact (y.powerset.filter (Stable g)).sup Finset.card

def Admits {n : Nat} (g : Fin n → Fin n → Bool) (x : Vert n) (e : Nat) : Prop :=
  ∃ f : Vert n → Fin n → Bool,
    (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true) ∧
    (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
    (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
    ∀ y l, y ⊆ x → Falls x f l y → l ≤ Alpha g y + e

def Copies {n : Nat} (g : Fin n → Fin n → Bool) (x : Vert n) (k : Nat) : Prop :=
  ∃ v : Fin k × Fin 3 → Fin n, Function.Injective v ∧ (∀ a, v a ∈ x) ∧
    ∀ a d, g (v a) (v d) = decide (a.1 = d.1 ∧ (a.2.val+1 = d.2.val ∨ d.2.val+1 = a.2.val))

lemma copiesLower {n k e : Nat} {g : Fin n → Fin n → Bool} {x : Vert n}
    (copies : Copies g x k) (adm : Admits g x e) : k ≤ e := by
  classical
  obtain ⟨v, inj, hsub, hgraph⟩ := copies
  obtain ⟨f, free, hit, mono, bound⟩ := adm
  obtain ⟨y, hy, falls, small⟩ := manyFalls free hit mono v inj hsub hgraph
  have lo := bound y _ hy falls
  have hi : Alpha g y ≤ k := by
    apply Finset.sup_le
    intro z hz
    obtain ⟨hsub', hs⟩ := Finset.mem_filter.mp hz
    exact small _ (Finset.mem_powerset.mp hsub') hs
  omega

lemma admitsMono {n e e' : Nat} {g : Fin n → Fin n → Bool} {x : Vert n}
    (h : Admits g x e) (he : e ≤ e') : Admits g x e' := by
  obtain ⟨f, hf, hh, hm, hb⟩ := h
  exact ⟨f, hf, hh, hm, fun y l hy hl => (hb y l hy hl).trans (Nat.add_le_add_left he _)⟩

lemma coloredAdmits {n : Nat} {g : Fin n → Fin n → Bool} {x : Vert n} {C : Type*}
    [DecidableEq C] (color : Fin n → C) (bad : Finset C)
    (loop : ∀ i, g i i = false)
    (clique : ∀ i ∈ x, ∀ j ∈ x, i ≠ j → color i = color j → g i j = true)
    (cluster : ∀ i ∈ x, ∀ j ∈ x, color i ∉ bad → color j ∉ bad → g i j = true → color i = color j) :
    Admits g x bad.card := by
  classical
  let f := fun (y : Vert n) (j : Fin n) => decide (color j ∉ y.image color)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro y hy j hj off
    simp only [f, decide_eq_true_eq]
    intro h
    obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp h
    have ed := clique _ (hy hi) _ hj (fun hh => off.1 (hh ▸ hi)) eq
    have := off.2 _ hi
    simp_all
  · intro y _ j hj
    simpa only [f, decide_eq_false_iff_not, not_not] using Finset.mem_image_of_mem color hj
  · intro u v huv _ j _
    simp only [f, decide_eq_true_eq]
    exact fun h hh => h (Finset.image_mono color huv hh)
  · intro y l hy hl
    have count (m : Nat) (s : Vert n) (hs : Falls x f m s) : m ≤ (s.image color).card := by
      induction m generalizing s with
      | zero => omega
      | succ m ih =>
        obtain ⟨u, v, j, _, hu, huv, hvs, on, off⟩ := hs
        simp only [f, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at on off
        have lt : u.image color ⊂ v.image color := Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.image_mono color huv, fun eq => on (eq ▸ off)⟩
        exact (Nat.succ_le_of_lt ((ih u hu).trans_lt (Finset.card_lt_card lt))).trans
          (Finset.card_le_card (Finset.image_mono color hvs))
    let good := y.filter (fun i => color i ∉ bad)
    obtain ⟨z, hsub, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
      (f := color) (↑good : Set (Fin n)) (good.image color) (by simp [Set.SurjOn])
    have zy : z ⊆ y := fun _ hi => (Finset.mem_filter.mp (hsub hi)).1
    have st : Stable g z := by
      intro i hi j hj
      by_cases he : g i j = true
      · have eq := cluster _ (hy (zy hi)) _ (hy (zy hj)) (Finset.mem_filter.mp (hsub hi)).2
            (Finset.mem_filter.mp (hsub hj)).2 he
        rw [hinj hi hj eq, loop]
      · simpa using he
    have al : z.card ≤ Alpha g y := Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr zy, st⟩)
    have spread : y.image color ⊆ good.image color ∪ bad := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      by_cases hb : color i ∈ bad
      · exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi,hb⟩))
    have bound := (count l y hl).trans <| (Finset.card_le_card spread).trans (Finset.card_union_le _ _)
    rw [← himg, Finset.card_image_iff.mpr hinj] at bound
    omega

def Hits {n t : Nat} (S : Fin n → Vert t) (g : Fin n → Fin n → Bool) (x : Vert n) (Q : Vert t) :=
  ∀ i ∈ x, ∀ j ∈ x, ∀ k ∈ x, i ≠ k → g i j = true → g j k = true → g i k = false →
    ∃ q ∈ Q, q ∈ S i ∨ q ∈ S j ∨ q ∈ S k

lemma coverUpper {n t b : Nat} {S : Fin n → Vert t} {g : Fin n → Fin n → Bool} {x : Vert n} {Q : Vert t}
    (loop : ∀ i, g i i = false) (symm : ∀ i j, g i j = g j i) (hits : Hits S g x Q)
    (cover : ∀ q : Fin t, ∃ colors : Fin b → Vert n,
      (∀ i, q ∈ S i → ∃ c, i ∈ colors c) ∧
      (∀ c, ∀ i ∈ colors c, ∀ j ∈ colors c, i ≠ j → g i j = true)) : Admits g x (b*Q.card) := by
  classical
  choose colors inside clique using cover
  let marks (i : Fin n) := ∃ p : Q × Fin b, i ∈ colors p.1.val p.2
  let Rel (i j : Fin n) := i = j ∨ g i j = true
  let good (i : Fin n) := x.filter (fun j => ¬ marks j ∧ Rel i j)
  let label (i : Fin n) : (Q × Fin b) ⊕ Vert n := if h : marks i then .inl h.choose else .inr (good i)
  let bad : Finset ((Q × Fin b) ⊕ Vert n) := Finset.univ.map Function.Embedding.inl
  have bs (i) : label i ∈ bad ↔ marks i := by
    by_cases h : marks i <;> simp [label, h, bad]
  have refl (i) (hi : i ∈ x) (hm : ¬marks i) : i ∈ good i := Finset.mem_filter.mpr ⟨hi, hm, Or.inl rfl⟩
  have trans (i j k) (hi : i ∈ x) (hj : j ∈ x) (hk : k ∈ x) (mi : ¬marks i) (mj : ¬marks j) (mk : ¬marks k)
      (hij : Rel i j) (hjk : Rel j k) : Rel i k := by
    rcases hij with rfl | hij
    · exact hjk
    rcases hjk with rfl | hjk
    · exact Or.inr hij
    by_contra! hn
    have hn' : i ≠ k ∧ g i k = false := by simpa [Rel] using hn
    obtain ⟨q, hq, hs⟩ := hits i hi j hj k hk hn'.1 hij hjk hn'.2
    have covered (a) (ha : q ∈ S a) : marks a := by
      obtain ⟨c,hc⟩ := inside q a ha
      exact ⟨(⟨q,hq⟩,c),hc⟩
    rcases hs with hs | hs | hs
    · exact mi (covered _ hs)
    · exact mj (covered _ hs)
    · exact mk (covered _ hs)
  have clique' (i) (hi : i ∈ x) (j) (hj : j ∈ x) (ne : i ≠ j) (eq : label i = label j) : g i j = true := by
    by_cases mi : marks i <;> by_cases mj : marks j
    · have same : mi.choose = mj.choose := by simpa [label, mi, mj] using eq
      apply clique _ _ i mi.choose_spec j _ ne
      simpa [same] using mj.choose_spec
    · simp [label, mi, mj] at eq
    · simp [label, mi, mj] at eq
    · have same : good i = good j := by simpa [label, mi, mj] using eq
      have hh : j ∈ good i := same ▸ refl _ hj mj
      exact (Finset.mem_filter.mp hh).2.2.resolve_left ne
  have cluster (i) (hi : i ∈ x) (j) (hj : j ∈ x) (ni : label i ∉ bad) (nj : label j ∉ bad)
      (ed : g i j = true) : label i = label j := by
    have mi := mt (bs i).mpr ni
    have mj := mt (bs j).mpr nj
    simp only [label, dif_neg mi, dif_neg mj, Sum.inr.injEq]
    ext k
    simp only [good, Finset.mem_filter]
    exact ⟨fun ⟨hk,mk,rel⟩ => ⟨hk,mk,trans j i k hj hi hk mj mi mk (Or.inr (symm i j ▸ ed)) rel⟩,
      fun ⟨hk,mk,rel⟩ => ⟨hk,mk,trans i j k hi hj hk mi mj mk (Or.inr ed) rel⟩⟩
  simpa [bad, Nat.mul_comm] using coloredAdmits label bad loop clique' cluster

lemma parentUnique {V : Type*} {T : SimpleGraph V} (tree : T.IsTree) (root u v w : V)
    (av : T.Adj u v) (aw : T.Adj u w) (dv : T.dist root v < T.dist root u)
    (dw : T.dist root w < T.dist root u) : v = w := by
  obtain ⟨pv, hpv⟩ := tree.connected.exists_walk_length_eq_dist v root
  obtain ⟨pw, hpw⟩ := tree.connected.exists_walk_length_eq_dist w root
  have best (j : V) (a : T.Adj u j) (hj : T.dist root j < T.dist root u)
      (p : T.Walk j root) (hp : p.length = T.dist j root) : (p.cons a).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    have := tree.dist_eq_dist_add_one_of_adj root a
    rw [T.dist_comm (u := j) (v := root)] at hp
    rw [SimpleGraph.Walk.length_cons, hp, T.dist_comm (u := u) (v := root)]
    omega
  have he := (tree.existsUnique_path u root).unique (best v av dv pv hpv) (best w aw dw pw hpw)
  simpa using congrArg (fun p : T.Walk u root => p.snd) he

lemma localParent {t : Nat} {T : SimpleGraph (Fin t)} (tree : T.IsTree) (root : Fin t)
    {A : Vert t} (conn : (T.induce (↑A : Set (Fin t))).Connected) {a : Fin t} (ha : a ∈ A)
    (least : ∀ i ∈ A, T.dist root a ≤ T.dist root i) {v : Fin t} (hv : v ∈ A) (hne : v ≠ a) :
    ∃ w ∈ A, T.Adj v w ∧ T.dist root w < T.dist root v := by
  classical
  let E (u w : A) := T.Adj u.val w.val ∧ T.dist root u.val < T.dist root w.val
  let top : A := ⟨a,ha⟩
  have all (z : A) : Relation.ReflTransGen E top z := by
    have path := ((T.induce (↑A : Set (Fin t))).reachable_iff_reflTransGen top z).mp (conn.preconnected top z)
    induction path with
    | refl => rfl
    | @tail i j _ edge ih =>
      change T.Adj i.val j.val at edge
      have gap := tree.dist_eq_dist_add_one_of_adj root edge
      by_cases up : T.dist root i.val < T.dist root j.val
      · exact ih.tail ⟨edge,up⟩
      · have down : T.dist root j.val < T.dist root i.val := by omega
        rcases ih.cases_tail with same | ⟨p, hp, last⟩
        · subst i
          exact (Nat.not_lt_of_le (least j.val j.property) down).elim
        · have equ := parentUnique tree root i.val p.val j.val last.1.symm edge last.2 down
          exact (Subtype.ext equ : p = j) ▸ hp
  rcases (all ⟨v,hv⟩).cases_tail with same | ⟨w,_,last⟩
  · exact (hne (congrArg Subtype.val same)).elim
  · exact ⟨w.val,w.property,last.1.symm,last.2⟩

lemma crossTop {t : Nat} {T : SimpleGraph (Fin t)} (tree : T.IsTree) (root : Fin t)
    {A B : Vert t} (ca : (T.induce (↑A : Set (Fin t))).Connected) (cb : (T.induce (↑B : Set (Fin t))).Connected)
    {a b : Fin t} (ha : a ∈ A) (hb : b ∈ B) (la : ∀ i ∈ A, T.dist root a ≤ T.dist root i)
    (lb : ∀ i ∈ B, T.dist root b ≤ T.dist root i) (deeper : T.dist root b ≤ T.dist root a)
    (meet : (A ∩ B).Nonempty) : a ∈ B := by
  classical
  obtain ⟨v, hv, low⟩ := (A ∩ B).exists_min_image (T.dist root) meet
  obtain ⟨hva,hvb⟩ := Finset.mem_inter.mp hv
  by_contra hn
  have na : v ≠ a := fun h => hn (h ▸ hvb)
  obtain ⟨p,hp,ap,dp⟩ := localParent tree root ca ha la hva na
  have nb : v ≠ b := by
    intro he
    subst v
    have := la p hp
    omega
  obtain ⟨q,hq,aq,dq⟩ := localParent tree root cb hb lb hvb nb
  have eq := parentUnique tree root v p q ap aq dp dq
  subst q
  exact (Nat.not_lt_of_le (low p (Finset.mem_inter.mpr ⟨hp,hq⟩))) dp

lemma treePacking {t : Nat} {I : Type*} [DecidableEq I] {T : SimpleGraph (Fin t)} (tree : T.IsTree)
    (A : I → Vert t) (fam : Finset I) (nonempty : ∀ i ∈ fam, (A i).Nonempty)
    (conn : ∀ i ∈ fam, (T.induce (↑(A i) : Set (Fin t))).Connected) :
    ∃ (Q : Vert t) (D : Finset I), D ⊆ fam ∧ Q.card ≤ D.card ∧
      (∀ i ∈ fam, (Q ∩ A i).Nonempty) ∧ (∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (A i) (A j)) := by
  classical
  let root := Classical.choice tree.connected.nonempty
  induction fam using Finset.strongInduction with
  | H fam ih =>
    by_cases empty : fam.Nonempty
    · have best (i : fam) := (A i.val).exists_min_image (T.dist root) (nonempty _ i.property)
      choose top ht hmin using best
      have un : (Finset.univ : Finset fam).Nonempty := by obtain ⟨i,hi⟩ := empty; exact ⟨⟨i,hi⟩,Finset.mem_univ _⟩
      obtain ⟨m,_,deep⟩ := Finset.univ.exists_max_image (fun i : fam => T.dist root (top i)) un
      let rem := fam.filter (fun i => top m ∉ A i)
      have sub : rem ⊆ fam := Finset.filter_subset _ _
      have notm : m.val ∉ rem := by simp [rem, ht]
      have proper : rem ⊂ fam := Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun h => notm (h.symm.subst (motive := fun s => m.val ∈ s) m.property)⟩
      obtain ⟨Q,D,hD,size,hit,dis⟩ := ih rem proper (fun i hi => nonempty i (sub hi)) (fun i hi => conn i (sub hi))
      have apart (i) (hi : i ∈ D) : Disjoint (A m.val) (A i) := by
        by_contra h
        have meet : (A m.val ∩ A i).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp h
        let j : fam := ⟨i, sub (hD hi)⟩
        have := crossTop tree root (conn _ m.property) (conn _ j.property) (ht m) (ht j) (hmin m) (hmin j)
          (deep j (Finset.mem_univ _)) meet
        exact (Finset.mem_filter.mp (hD hi)).2 this
      refine ⟨insert (top m) Q, insert m.val D, Finset.insert_subset m.property (hD.trans sub), ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun h => notm (hD h))]
        exact (Finset.card_insert_le _ _).trans (by omega)
      · intro i hi
        by_cases hm : top m ∈ A i
        · exact ⟨_,Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hm⟩⟩
        · obtain ⟨p,hp⟩ := hit _ (Finset.mem_filter.mpr ⟨hi,hm⟩)
          exact ⟨p,Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hp).1,(Finset.mem_inter.mp hp).2⟩⟩
      · intro i hi j hj ne
        rcases Finset.mem_insert.mp hi with rfl | hi <;> rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (ne rfl).elim
        · exact apart _ hj
        · exact (apart _ hi).symm
        · exact dis _ hi _ hj ne
    · rw [Finset.not_nonempty_iff_eq_empty.mp empty]
      exact ⟨∅,∅,by simp⟩

lemma pathCover {n t : Nat} {T : SimpleGraph (Fin t)} (tree : T.IsTree)
    {S : Fin n → Vert t} (bags : ∀ i, (S i).Nonempty ∧ (T.induce (↑(S i) : Set (Fin t))).Connected)
    {g : Fin n → Fin n → Bool} (loop : ∀ i, g i i = false) (symm : ∀ i j, g i j = g j i)
    (touch : ∀ i j, g i j = true → (S i ∩ S j).Nonempty) (x : Vert n) :
    ∃ (Q : Vert t) (k : Nat), Q.card ≤ k ∧ k ≤ n ∧ Copies g x k ∧ Hits S g x Q := by
  classical
  let valid (w : Fin 3 → Fin n) := Function.Injective w ∧ (∀ s, w s ∈ x) ∧
    ∀ s d, g (w s) (w d) = decide (s.val+1 = d.val ∨ d.val+1 = s.val)
  let fam := Finset.univ.filter valid
  let A (w : Fin 3 → Fin n) := (S (w 0) ∪ S (w 1)) ∪ S (w 2)
  have vf {w} (hw : w ∈ fam) : valid w := (Finset.mem_filter.mp hw).2
  have sub (w : Fin 3 → Fin n) (s : Fin 3) : S (w s) ⊆ A w := by
    intro q hq
    fin_cases s <;> simp_all [A]
  have nonempty (w) (_ : w ∈ fam) : (A w).Nonempty := (bags (w 0)).1.mono (sub w 0)
  have conn (w) (hw : w ∈ fam) : (T.induce (↑(A w) : Set (Fin t))).Connected := by
    have merge (a b : Vert t) (ca : (T.induce (↑a : Set (Fin t))).Connected)
        (cb : (T.induce (↑b : Set (Fin t))).Connected) (meet : (a ∩ b).Nonempty) :
        (T.induce (↑(a ∪ b) : Set (Fin t))).Connected := by
      rw [Finset.coe_union]
      obtain ⟨point, hp⟩ := meet
      exact T.induce_union_connected ca.preconnected cb.preconnected ⟨point,Finset.mem_inter.mp hp⟩
    have e01 : g (w 0) (w 1) = true := by simp [(vf hw).2.2]
    have e12 : g (w 1) (w 2) = true := by simp [(vf hw).2.2]
    apply merge _ _ (merge _ _ (bags _).2 (bags _).2 (touch _ _ e01)) (bags _).2
    obtain ⟨q,hq⟩ := touch _ _ e12
    exact ⟨q,Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hq).1,(Finset.mem_inter.mp hq).2⟩⟩
  obtain ⟨Q,D,hD,size,hit,dis⟩ := treePacking tree A fam nonempty conn
  let enum : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (by simp)).symm
  let row (r : Fin D.card) := (enum r).val
  let v (p : Fin D.card × Fin 3) := row p.1 p.2
  have rv (r) : valid (row r) := vf (hD (enum r).property)
  have sep (r s : Fin D.card) (ne : r ≠ s) : Disjoint (A (row r)) (A (row s)) :=
    dis _ (enum r).property _ (enum s).property (fun e => ne (enum.injective (Subtype.ext e)))
  have inj : Function.Injective v := by
    rintro ⟨r,a⟩ ⟨s,b⟩ he
    change row r a = row s b at he
    by_cases eq : r = s
    · subst s
      exact Prod.ext rfl ((rv r).1 he)
    · obtain ⟨q,hq⟩ := (bags (row r a)).1
      exact (Finset.disjoint_left.mp (sep _ _ eq) (sub _ a hq) (sub _ b (he ▸ hq))).elim
  have kn : D.card ≤ n := by
    have := Fintype.card_le_of_injective (fun r => v (r,0)) (fun i j he => congrArg Prod.fst (inj he))
    simpa using this
  refine ⟨Q, D.card, size, kn, ⟨v, inj, fun p => (rv p.1).2.1 p.2, ?_⟩, ?_⟩
  · rintro ⟨r,a⟩ ⟨s,b⟩
    by_cases eq : r = s
    · subst s
      simpa [v] using (rv r).2.2 a b
    · have no : g (row r a) (row s b) = false := by
        cases he : g (row r a) (row s b) with
        | false => rfl
        | true =>
          obtain ⟨q,hq⟩ := touch _ _ he
          exact (Finset.disjoint_left.mp (sep _ _ eq) (sub _ a (Finset.mem_inter.mp hq).1) (sub _ b (Finset.mem_inter.mp hq).2)).elim
      simpa [v,eq] using no
  · intro i hi j hj k hk ne e01 e12 e02
    let w : Fin 3 → Fin n := ![i,j,k]
    have ij : i ≠ j := by rintro rfl; simp [loop] at e01
    have jk : j ≠ k := by rintro rfl; simp [loop] at e12
    have ew : valid w := by
      refine ⟨?_, ?_, ?_⟩
      · intro a b h
        fin_cases a <;> fin_cases b <;> simp_all [w,ne.symm,ij.symm,jk.symm]
      · intro a
        fin_cases a <;> simp_all [w]
      · have e10 := (symm i j).symm.trans e01
        have e21 := (symm j k).symm.trans e12
        have e20 := (symm i k).symm.trans e02
        intro a b
        fin_cases a <;> fin_cases b <;> simp_all [w]
    obtain ⟨q,hq⟩ := hit w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ew⟩)
    exact ⟨q,(Finset.mem_inter.mp hq).1,by simpa [A,w,or_assoc] using (Finset.mem_inter.mp hq).2⟩

end PEqualNP.Outside.L_meta_48150

theorem PEqualNP.Outside.L_meta_48150 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n t : Nat) (T : SimpleGraph (Fin t)) (S : Fin n → Finset (Fin t)),
  T.IsTree → (∀ i, (S i).Nonempty ∧ (T.induce (↑(S i) : Set (Fin t))).Connected) →
  ∀ (g : Fin n → Fin n → Bool),
    (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
    (∀ i j, g i j = true → ((S i) ∩ (S j)).Nonempty) →
    let X := Finset (Fin n)
    let alpha := fun (y : X) =>
      (y.powerset.filter (fun z => ∀ a ∈ z, ∀ b ∈ z, g a b = false)).sup Finset.card
    let admits := fun (x : X) (e : Nat) =>
      ∃ f : X → Fin n → Bool,
        (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true) ∧
        (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
        (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
        let pack := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : X) (j : Fin n), j ∈ x ∧ prev u ∧ u ⊆ v ∧ v ⊆ y ∧
            f u j = true ∧ f v j = false)
        ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
    ∀ (b : Nat),
      (∀ q : Fin t, ∃ colors : Fin b → X,
        (∀ i, q ∈ S i → ∃ c, i ∈ colors c) ∧
        (∀ c, ∀ i ∈ colors c, ∀ j ∈ colors c, i ≠ j → g i j = true)) →
      ∀ x : X,
        let copies := fun (k : Nat) => ∃ v : Fin k × Fin 3 → Fin n,
          Function.Injective v ∧ (∀ a, v a ∈ x) ∧
          ∀ a d, g (v a) (v d) =
            decide (a.1 = d.1 ∧ (a.2.val+1 = d.2.val ∨ d.2.val+1 = a.2.val))
        let p := ((Finset.range (n+1)).filter copies).sup id
        (∃ Q : Finset (Fin t), Q.card ≤ p ∧ ∀ i ∈ x, ∀ j ∈ x, ∀ k ∈ x,
          i ≠ k → g i j = true → g j k = true → g i k = false →
          ∃ q ∈ Q, q ∈ S i ∨ q ∈ S j ∨ q ∈ S k) ∧
        (∀ e, admits x e → p ≤ e) ∧ admits x (b*p) ∧
        (b = 1 → ∀ e, admits x e ↔ p ≤ e)) := by
  classical
  intro n t T S tree bags g loop symm touch
  dsimp only
  intro b cover x
  let p := ((Finset.range (n+1)).filter (PEqualNP.Outside.L_meta_48150.Copies g x)).sup id
  suffices claim : (∃ Q : Finset (Fin t), Q.card ≤ p ∧ PEqualNP.Outside.L_meta_48150.Hits S g x Q) ∧
    (∀ e, PEqualNP.Outside.L_meta_48150.Admits g x e → p ≤ e) ∧ PEqualNP.Outside.L_meta_48150.Admits g x (b*p) ∧
    (b = 1 → ∀ e, PEqualNP.Outside.L_meta_48150.Admits g x e ↔ p ≤ e) by
    unfold PEqualNP.Outside.L_meta_48150.Admits PEqualNP.Outside.L_meta_48150.Alpha PEqualNP.Outside.L_meta_48150.Stable PEqualNP.Outside.L_meta_48150.Falls PEqualNP.Outside.L_meta_48150.Hits at claim
    dsimp only [p, PEqualNP.Outside.L_meta_48150.Copies] at claim
    convert! claim using 64 <;> unfold PEqualNP.Outside.L_meta_48150.Copies <;>
      apply exists_congr <;> intro v <;> apply and_congr_right <;> intro _ <;> apply and_congr_right <;> intro _ <;>
      apply forall_congr' <;> intro a <;> apply forall_congr' <;> intro d <;> cases g (v a) (v d) <;> simp
  have inst : (fun a b : Fin t => Classical.propDecidable (a = b)) = instDecidableEqFin t := Subsingleton.elim _ _
  rw [inst] at touch
  obtain ⟨Q,k,size,kn,copies,hits⟩ := PEqualNP.Outside.L_meta_48150.pathCover tree bags loop symm touch x
  have kp : k ≤ p := Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),copies⟩)
  have qp := size.trans kp
  have lower (e) (adm : PEqualNP.Outside.L_meta_48150.Admits g x e) : p ≤ e := by
    apply Finset.sup_le
    intro r hr
    exact PEqualNP.Outside.L_meta_48150.copiesLower (Finset.mem_filter.mp hr).2 adm
  have upper := PEqualNP.Outside.L_meta_48150.admitsMono (PEqualNP.Outside.L_meta_48150.coverUpper loop symm hits cover) (Nat.mul_le_mul_left b qp)
  refine ⟨⟨Q,qp,hits⟩,lower,upper,?_⟩
  rintro rfl e
  exact ⟨lower _, fun he => PEqualNP.Outside.L_meta_48150.admitsMono (by simpa using upper) he⟩
