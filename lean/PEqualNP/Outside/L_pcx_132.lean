import PEqualNP.Defs

/-
  Lower bound for Res(⊕) on BPHP 5 2: no refutation has at most 111 lines.
  The ShortestDag, Collision/sample geometry, and component-mass accounting
  machinery are adapted from the merged Apache-2.0 file
  PEqualNP/Outside/L_pcx_130.lean, extended here with non-tautology pruning,
  derived-root unrolling past reused input clauses, signed sub-assignment
  potentials, and H2/H1 incoming-edge charge accounting.
-/

namespace PEqualNP.Outside.L_pcx_132_aux

namespace Dag

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

inductive Rule (F : Set (LinClause V)) (pi : List (LinClause V)) (i : Fin pi.length) : Type
  | ax (inFormula : pi.get i ∈ F)
  | res (j k : Fin pi.length) (hj : i < j) (hk : i < k)
      (valid : IsLinResolvent (pi.get j) (pi.get k) (pi.get i))
  | weak (j : Fin pi.length) (hj : i < j)
      (valid : ∀ a, LinClauseSat a (pi.get j) → LinClauseSat a (pi.get i))

def Rule.parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length)
  | .ax _ => []
  | .res j k _ _ _ => [j, k]
  | .weak j _ _ => [j]

theorem Rule.lt_of_mem_parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i j : Fin pi.length} (r : Rule F pi i) (h : j ∈ r.parents) : i < j := by
  cases r with
  | ax _ => simp [parents] at h
  | res a b ha hb _ =>
    simp [parents] at h
    rcases h with rfl | rfl <;> assumption
  | weak a ha _ =>
    simp only [parents, List.mem_singleton] at h
    simpa [h] using ha

def Rule.cons {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (C : LinClause V) (r : Rule F pi i) :
    Rule F (C :: pi) i.succ := by
  cases r with
  | ax h => exact .ax (by simpa using h)
  | res j k hj hk h =>
    exact .res j.succ k.succ (by simpa using hj) (by simpa using hk) (by simpa using h)
  | weak j hj h =>
    exact .weak j.succ (by simpa using hj) (by simpa using h)

theorem line_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) : ∀ i, Nonempty (Rule F pi i) := by
  classical
  induction deriv with
  | nil => intro i; exact Fin.elim0 i
  | @ax pi C deriv hC ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨.ax (by simpa using hC)⟩
    · exact ⟨(Classical.choice (ih j)).cons C⟩
  | @res pi C D R deriv hC hD hr ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hD
      let j' : Fin pi.length := ⟨j, hj⟩
      let k' : Fin pi.length := ⟨k, hk⟩
      refine ⟨.res j'.succ k'.succ (Fin.succ_pos _) (Fin.succ_pos _) ?_⟩
      change IsLinResolvent (pi.get j') (pi.get k') R
      rwa [show pi.get j' = C from ej, show pi.get k' = D from ek]
    · exact ⟨(Classical.choice (ih j)).cons R⟩
  | @weak pi C D deriv hC hw ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      let j' : Fin pi.length := ⟨j, hj⟩
      refine ⟨.weak j'.succ (Fin.succ_pos _) ?_⟩
      change ∀ a, LinClauseSat a (pi.get j') → LinClauseSat a D
      rwa [show pi.get j' = C from ej]
    · exact ⟨(Classical.choice (ih j)).cons D⟩

noncomputable def choose_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (i : Fin pi.length) : Rule F pi i :=
  Classical.choice (line_rules deriv i)

theorem false_res {C D R : LinClause V} (h : IsLinResolvent C D R)
    (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)

theorem derivation_dedup {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) :
    ∃ rho, IsLinDerivation F rho ∧ rho.Nodup ∧ rho.Sublist pi ∧
      ∀ c, c ∈ pi ↔ c ∈ rho := by
  classical
  induction deriv with
  | nil => exact ⟨[], .nil, List.nodup_nil, .slnil, fun _ => Iff.rfl⟩
  | @ax pi C deriv hC ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : C ∈ rho
    · refine ⟨rho, hd, nd, sub.cons C, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨C :: rho, .ax hd hC, List.nodup_cons.mpr ⟨h, nd⟩,
        sub.cons_cons C, fun c => by simp [eq]⟩
  | @res pi C D R deriv hC hD hr ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : R ∈ rho
    · refine ⟨rho, hd, nd, sub.cons R, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨R :: rho, .res hd ((eq C).mp hC) ((eq D).mp hD) hr,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons R, fun c => by simp [eq]⟩
  | @weak pi C D deriv hC hw ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : D ∈ rho
    · refine ⟨rho, hd, nd, sub.cons D, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨D :: rho, .weak hd ((eq C).mp hC) hw,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons D, fun c => by simp [eq]⟩

def Useful (C : LinClause V) : Prop := ∃ a : V → Bool, ¬ LinClauseSat a C

theorem derivation_prune_taut {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) :
    ∃ rho, IsLinDerivation F rho ∧ rho.Sublist pi ∧
      (∀ c ∈ rho, Useful c) ∧ (∀ c ∈ pi, Useful c → c ∈ rho) := by
  classical
  induction deriv with
  | nil => exact ⟨[], .nil, .slnil, by simp, by simp⟩
  | @ax pi C deriv hC ih =>
    obtain ⟨rho, hd, sub, hu, hc⟩ := ih
    by_cases hU : Useful C
    · refine ⟨C :: rho, .ax hd hC, sub.cons_cons C, ?_, ?_⟩
      · intro c hm; rcases List.mem_cons.mp hm with rfl | hm; exact hU; exact hu c hm
      · intro c hm huc; rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem C (hc c hm huc)
    · refine ⟨rho, hd, sub.cons C, hu, ?_⟩
      intro c hm huc
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (hU huc).elim
      · exact hc c hm huc
  | @res pi C D R deriv hC hD hr ih =>
    obtain ⟨rho, hd, sub, hu, hc⟩ := ih
    by_cases hUR : Useful R
    · by_cases hUC : Useful C
      · by_cases hUD : Useful D
        · refine ⟨R :: rho, .res hd (hc C hC hUC) (hc D hD hUD) hr, sub.cons_cons R, ?_, ?_⟩
          · intro c hm; rcases List.mem_cons.mp hm with rfl | hm; exact hUR; exact hu c hm
          · intro c hm huc; rcases List.mem_cons.mp hm with rfl | hm
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem R (hc c hm huc)
        · have hw : ∀ a, LinClauseSat a C → LinClauseSat a R := by
            intro a hs
            by_contra hn
            rcases false_res hr a hn with h1 | h2
            · exact h1 hs
            · exact hUD ⟨a, h2⟩
          refine ⟨R :: rho, .weak hd (hc C hC hUC) hw, sub.cons_cons R, ?_, ?_⟩
          · intro c hm; rcases List.mem_cons.mp hm with rfl | hm; exact hUR; exact hu c hm
          · intro c hm huc; rcases List.mem_cons.mp hm with rfl | hm
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem R (hc c hm huc)
      · have hw : ∀ a, LinClauseSat a D → LinClauseSat a R := by
          intro a hs
          by_contra hn
          rcases false_res hr a hn with h1 | h2
          · exact hUC ⟨a, h1⟩
          · exact h2 hs
        have hUD : Useful D := by
          obtain ⟨a, ha⟩ := hUR
          exact ⟨a, fun hs => ha (hw a hs)⟩
        refine ⟨R :: rho, .weak hd (hc D hD hUD) hw, sub.cons_cons R, ?_, ?_⟩
        · intro c hm; rcases List.mem_cons.mp hm with rfl | hm; exact hUR; exact hu c hm
        · intro c hm huc; rcases List.mem_cons.mp hm with rfl | hm
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem R (hc c hm huc)
    · refine ⟨rho, hd, sub.cons R, hu, ?_⟩
      intro c hm huc
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (hUR huc).elim
      · exact hc c hm huc
  | @weak pi C D deriv hC hw ih =>
    obtain ⟨rho, hd, sub, hu, hc⟩ := ih
    by_cases hUD : Useful D
    · have hUC : Useful C := by
        obtain ⟨a, ha⟩ := hUD
        exact ⟨a, fun hs => ha (hw a hs)⟩
      refine ⟨D :: rho, .weak hd (hc C hC hUC) hw, sub.cons_cons D, ?_, ?_⟩
      · intro c hm; rcases List.mem_cons.mp hm with rfl | hm; exact hUD; exact hu c hm
      · intro c hm huc; rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem D (hc c hm huc)
    · refine ⟨rho, hd, sub.cons D, hu, ?_⟩
      intro c hm huc
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (hUD huc).elim
      · exact hc c hm huc

theorem derivation_trim {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (keep : List (Fin pi.length))
    (order : keep.Pairwise (· < ·))
    (closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep) :
    IsLinDerivation F (keep.map pi.get) := by
  induction keep with
  | nil => exact .nil
  | cons i keep ih =>
    obtain ⟨head, later⟩ := List.pairwise_cons.mp order
    have ht : ∀ j ∈ keep, ∀ k ∈ (rules j).parents, k ∈ keep := by
      intro j hj k hk
      have mem := closed j (List.mem_cons_of_mem i hj) k hk
      rcases List.mem_cons.mp mem with eq | hm
      · have hlt := (rules j).lt_of_mem_parents hk
        rw [eq] at hlt
        exact False.elim (not_lt_of_ge (head _ hj).le hlt)
      · exact hm
    have prev := ih later ht
    have hm : ∀ j ∈ (rules i).parents, j ∈ keep := by
      intro j hj
      have hlt := (rules i).lt_of_mem_parents hj
      have mem := closed i List.mem_cons_self j hj
      rcases List.mem_cons.mp mem with eq | mem
      · exact False.elim (hlt.ne eq.symm)
      · exact mem
    generalize eq : rules i = r at hm
    cases r with
    | ax h => exact .ax prev h
    | res j k _ _ h =>
      exact .res prev (List.mem_map_of_mem (hm j (by simp [Rule.parents])))
        (List.mem_map_of_mem (hm k (by simp [Rule.parents]))) h
    | weak j _ h =>
      exact .weak prev (List.mem_map_of_mem (hm j (by simp [Rule.parents]))) h

def Parent {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (i j : Fin pi.length) : Prop :=
  j ∈ (rules i).parents

abbrev Reaches {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) := Relation.ReflTransGen (Parent rules)

theorem reachable_of_shortest {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (root : Fin pi.length) (hroot : pi.get root = ∅)
    (shortest : ∀ rho, IsLinDerivation F rho → (∅ : LinClause V) ∈ rho → pi.length ≤ rho.length) :
    ∀ i, Reaches rules root i := by
  classical
  let keep := (List.finRange pi.length).filter (fun j => decide (Reaches rules root j))
  have order : keep.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have member (j : Fin pi.length) : j ∈ keep ↔ Reaches rules root j := by
    simp [keep, List.mem_finRange]
  have closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep := by
    intro i hi j hj
    exact (member j).mpr ((member i).mp hi |>.tail hj)
  have deriv := derivation_trim rules keep order closed
  have emptyMem : (∅ : LinClause V) ∈ keep.map pi.get := by
    rw [← hroot]
    exact List.mem_map_of_mem ((member root).mpr .refl)
  have lengthBound := shortest _ deriv emptyMem
  rw [List.length_map] at lengthBound
  have sub : keep.Sublist (List.finRange pi.length) := List.filter_sublist
  have same : keep = List.finRange pi.length :=
    sub.eq_of_length (by have := sub.length_le; simp at this; simp; omega)
  intro i
  exact (member i).mp (same.symm ▸ List.mem_finRange i)

structure ShortestDag (F : Set (LinClause V)) where
  pi : List (LinClause V)
  nodup : pi.Nodup
  root : Fin pi.length
  rootEmpty : pi.get root = ∅
  rules : ∀ i, Rule F pi i
  reachable : ∀ i, Reaches rules root i
  nonTaut : ∀ i, Useful (pi.get i)
  shortest : ∀ rho, IsLinDerivation F rho → (∅ : LinClause V) ∈ rho → pi.length ≤ rho.length

theorem shortest_dag {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (contains : (∅ : LinClause V) ∈ pi) :
    ∃ d : ShortestDag F, d.pi.length ≤ pi.length := by
  classical
  let P (n : Nat) := ∃ rho, IsLinDerivation F rho ∧ (∅ : LinClause V) ∈ rho ∧ rho.length = n
  have exist : ∃ n, P n := ⟨pi.length, pi, deriv, contains, rfl⟩
  obtain ⟨rho, hr, hempty, hlen⟩ := Nat.find_spec exist
  have shortest (tau : List (LinClause V)) (h : IsLinDerivation F tau)
      (he : (∅ : LinClause V) ∈ tau) : rho.length ≤ tau.length := by
    rw [hlen]
    exact Nat.find_min' exist ⟨tau, h, he, rfl⟩
  obtain ⟨delta, hd, nd, sub, eq⟩ := derivation_dedup hr
  have bdd := shortest delta hd ((eq ∅).mp hempty)
  have same : delta = rho := sub.eq_of_length (Nat.le_antisymm sub.length_le bdd)
  have noDup : rho.Nodup := same ▸ nd
  obtain ⟨tau, htd, tsub, thu, thc⟩ := derivation_prune_taut hr
  have emptyUseful : Useful (∅ : LinClause V) := ⟨fun _ => false, by simp [LinClauseSat]⟩
  have tbdd := shortest tau htd (thc ∅ hempty emptyUseful)
  have tsame : tau = rho := tsub.eq_of_length (Nat.le_antisymm tsub.length_le tbdd)
  have nonTaut : ∀ i : Fin rho.length, Useful (rho.get i) := by
    intro i
    exact thu (rho.get i) (tsame ▸ List.get_mem rho i)
  obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hempty
  let root : Fin rho.length := ⟨k, hk⟩
  have rootEmpty : rho.get root = ∅ := ek
  let rules := choose_rules hr
  exact ⟨⟨rho, noDup, root, rootEmpty, rules,
    reachable_of_shortest rules root rootEmpty shortest, nonTaut, shortest⟩,
    shortest pi deriv contains⟩

abbrev Test (V : Type) := Finset V × Bool

def testParity (a : V → Bool) (f : Finset V) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

noncomputable def Rule.labelled {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length × Option (Test V))
  | .ax _ => []
  | .weak j _ _ => [(j, none)]
  | .res j k _ _ hr =>
      let f := Classical.choose hr
      [(j, some (f, true)), (k, some (f, false))]

theorem Rule.labelled_map {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (r : Rule F pi i) : r.labelled.map Prod.fst = r.parents := by
  cases r <;> rfl

/-- Derived-cut local tree: unrolls past reused input clauses, stopping only at
    derived nodes with incoming degree ≥ 2. -/
inductive DTree (V I : Type)
  | axUniq (i : I)
  | axRep (i : I)
  | exitDer (j : I)
  | weak (i : I) (child : DTree V I)
  | res (i : I) (pivot : Finset V) (left right : DTree V I)

inductive DTree.Route {I : Type} : DTree V I → I → List (Option (Test V)) → Prop
  | axUniq (i : I) : Route (.axUniq i) i []
  | weak {i t j qs} (h : Route t j qs) : Route (.weak i t) j (none :: qs)
  | left {i f l r j qs} (h : Route l j qs) : Route (.res i f l r) j (some (f, true) :: qs)
  | right {i f l r j qs} (h : Route r j qs) : Route (.res i f l r) j (some (f, false) :: qs)

namespace ShortestDag

variable {F : Set (LinClause V)} (d : ShortestDag F)

def children (i : Fin d.pi.length) : List (Fin d.pi.length) := (d.rules i).parents

theorem children_lt (i j : Fin d.pi.length) (h : j ∈ d.children i) : i < j :=
  (d.rules i).lt_of_mem_parents h

theorem root_val_zero : d.root.val = 0 := by
  let z : Fin d.pi.length := ⟨0, Nat.zero_lt_of_lt d.root.isLt⟩
  have h := d.reachable z
  have le : ∀ v, Reaches d.rules d.root v → d.root ≤ v := by
    intro v hr
    induction hr with
    | refl => exact le_rfl
    | @tail v w _ hp ih => exact ih.trans (d.children_lt v w hp).le
  exact Nat.eq_zero_of_le_zero (le _ h)

theorem exists_parent (j : Fin d.pi.length) (hn : j.val ≠ 0) :
    ∃ i, j ∈ d.children i := by
  have h := d.reachable j
  induction h with
  | refl => exact (hn d.root_val_zero).elim
  | @tail v w _ hp _ => exact ⟨v, hp⟩

def incoming (j : Fin d.pi.length) : ℕ :=
  ∑ i : Fin d.pi.length, (d.children i).count j

theorem incoming_pos (j : Fin d.pi.length) (hn : j.val ≠ 0) : 0 < d.incoming j := by
  obtain ⟨i, hi⟩ := d.exists_parent j hn
  have hpos : 0 < (d.children i).count j := List.count_pos_iff.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun b _ => Nat.zero_le ((d.children b).count j))
    (Finset.mem_univ i))

theorem incoming_at_first : d.incoming d.root = 0 := by
  classical
  unfold incoming
  apply Finset.sum_eq_zero
  intro i _
  apply List.count_eq_zero_of_not_mem
  intro h
  have hp : i.val < d.root.val := d.children_lt i d.root h
  rw [d.root_val_zero] at hp
  omega

theorem children_length (i : Fin d.pi.length) : (d.children i).length ≤ 2 := by
  unfold children; cases d.rules i <;> simp [Rule.parents]

theorem axiom_of_no_children (i : Fin d.pi.length) (h : d.children i = []) :
    d.pi.get i ∈ F := by
  cases hr : d.rules i with
  | ax hf => exact hf
  | res => simp [children, hr, Rule.parents] at h
  | weak => simp [children, hr, Rule.parents] at h

def AxiomIndex := { i : Fin d.pi.length // d.children i = [] }

noncomputable abbrev labels (i : Fin d.pi.length) := (d.rules i).labelled

theorem label_child {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : (j, q) ∈ d.labels i) : j ∈ d.children i := by
  rw [children, ← (d.rules i).labelled_map]
  exact List.mem_map.mpr ⟨(j, q), h, rfl⟩

theorem labelled_of_child {i j : Fin d.pi.length} (h : j ∈ d.children i) :
    ∃ q, (j, q) ∈ d.labels i := by
  rw [children, ← (d.rules i).labelled_map] at h
  obtain ⟨⟨k, q⟩, hk, he⟩ := List.mem_map.mp h
  cases he; exact ⟨q, hk⟩

theorem res_children_ne {i j k : Fin d.pi.length} (hj : i < j)
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i)) : j ≠ k := by
  rintro rfl
  obtain ⟨f, _, _, he⟩ := hr
  have heq : (d.pi.get j).erase (f, false) ∪ (d.pi.get j).erase (f, true) = d.pi.get j := by
    ext q
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · exact fun h => h.elim And.right And.right
    · intro h
      by_cases hq : q = (f, false)
      · exact Or.inr ⟨by simp [hq], h⟩
      · exact Or.inl ⟨hq, h⟩
  exact (ne_of_lt hj) (d.nodup.injective_get (he.trans heq))

theorem labels_unique {i j : Fin d.pi.length} {q r : Option (Test V)}
    (hq : (j, q) ∈ d.labels i) (hr : (j, r) ∈ d.labels i) : q = r := by
  cases h : d.rules i with
  | ax => simp [labels, h, Rule.labelled] at hq
  | weak k hk hw => simp [labels, h, Rule.labelled] at hq hr; exact hq.2.trans hr.2.symm
  | res k l hk hl hv =>
    have hkl := d.res_children_ne hk hv
    simp [labels, h, Rule.labelled] at hq hr
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hr with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · rfl
    · exact (hkl he).elim
    · exact (hkl he.symm).elim
    · rfl

theorem parent_unique {i k j : Fin d.pi.length} (hin : d.incoming j = 1)
    (hi : j ∈ d.children i) (hk : j ∈ d.children k) : i = k := by
  classical
  by_contra h
  have hci := List.count_pos_iff.mpr hi
  have hck := List.count_pos_iff.mpr hk
  have subset : ({i, k} : Finset (Fin d.pi.length)) ⊆ Finset.univ := Finset.subset_univ _
  have lb := Finset.sum_le_sum_of_subset_of_nonneg subset (fun x _ _ =>
    Nat.zero_le ((d.children x).count j))
  rw [← incoming, hin] at lb
  simp [h] at lb
  omega

def Accepts (a : V → Bool) : Option (Test V) → Prop
  | none => True
  | some (f, b) => testParity a f = b

private theorem res_false_label {i j k : Fin d.pi.length}
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i))
    (a : V → Bool) (hf : ¬ LinClauseSat a (d.pi.get i)) :
    if testParity a (Classical.choose hr) then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k) := by
  let f := Classical.choose hr
  obtain ⟨_, _, he⟩ := Classical.choose_spec hr
  change (if testParity a f then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k))
  by_cases odd : Odd (f.filter (fun v => a v = true)).card
  · simp [testParity, odd]
    rintro ⟨q, hq, hqs⟩
    apply hf; refine ⟨q, ?_, hqs⟩; rw [he]
    refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl; exact Bool.noConfusion (hqs.1 odd)
  · simp [testParity, odd]
    rintro ⟨q, hq, hqs⟩
    apply hf; refine ⟨q, ?_, hqs⟩; rw [he]
    refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl; exact odd (hqs.2 rfl)

theorem false_label_or_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    d.children i = [] ∨ ∃ j q, (j, q) ∈ d.labels i ∧ Accepts a q ∧
      ¬ LinClauseSat a (d.pi.get j) := by
  cases h : d.rules i with
  | ax => left; simp [children, h, Rule.parents]
  | weak j hj hw =>
    exact Or.inr ⟨j, none, by simp [labels, h, Rule.labelled], trivial, fun hn => hf (hw a hn)⟩
  | res j k hj hk hr =>
    have hv := d.res_false_label hr a hf
    cases hp : testParity a (Classical.choose hr)
    · exact Or.inr ⟨k, some (Classical.choose hr, false), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩
    · exact Or.inr ⟨j, some (Classical.choose hr, true), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩

def ActiveStep (a : V → Bool) (i j : Fin d.pi.length) : Prop :=
  ∃ q, (j, q) ∈ d.labels i ∧ Accepts a q ∧
    ¬ LinClauseSat a (d.pi.get i) ∧ ¬ LinClauseSat a (d.pi.get j)

abbrev Active (a : V → Bool) := Relation.ReflTransGen (d.ActiveStep a)

theorem active_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
  have aux (k : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = k →
      ¬ LinClauseSat a (d.pi.get i) →
      ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hf
      rcases d.false_label_or_axiom a i hf with e | ⟨j, q, hj, ha, hn⟩
      · exact ⟨i, .refl, e, hf⟩
      · have edge : i.val < j.val := d.children_lt i j (d.label_child hj)
        have hb := j.isLt
        obtain ⟨w, hpath, he, hw⟩ := ih (d.pi.length - j.val) (by omega) j rfl hn
        exact ⟨w, hpath.head ⟨q, hj, ha, hf, hn⟩, he, hw⟩
  exact aux _ i rfl hf

theorem active_initial_clause (a : V → Bool) :
    ∃ j, d.Active a d.root j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) :=
  d.active_axiom a d.root (by rw [d.rootEmpty]; simp [LinClauseSat])

inductive LocalPath : Fin d.pi.length → Fin d.pi.length → List (Option (Test V)) → Prop
  | nil (i) : LocalPath i i []
  | cons {i j k q qs} (label : (j, q) ∈ d.labels i) (unique : d.incoming j = 1)
      (rest : LocalPath j k qs) : LocalPath i k (q :: qs)

theorem peel_active {a : V → Bool} {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : d.Active a d.root j) (he : (j, q) ∈ d.labels i) (hu : d.incoming j = 1) :
    d.Active a d.root i ∧ Accepts a q ∧ ¬ LinClauseSat a (d.pi.get i) := by
  cases h with
  | refl => have hz := d.incoming_at_first; omega
  | @tail k j hp hs =>
    obtain ⟨r, hr, ar, hnk, _⟩ := hs
    have eq := d.parent_unique hu (d.label_child hr) (d.label_child he)
    subst k
    have eqr := d.labels_unique hr he
    exact ⟨hp, eqr ▸ ar, hnk⟩

theorem local_path_active {a : V → Bool} {i j : Fin d.pi.length} {qs}
    (hp : d.LocalPath i j qs) (ha : d.Active a d.root j)
    (hf : ¬ LinClauseSat a (d.pi.get j)) :
    d.Active a d.root i ∧ ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  induction hp with
  | nil _ => exact ⟨ha, hf, by simp⟩
  | @cons i j k q qs he hu rest ih =>
    obtain ⟨haj, hfj, acc⟩ := ih ha hf
    obtain ⟨hai, aq, hfi⟩ := d.peel_active haj he hu
    exact ⟨hai, hfi, fun r hr => (List.mem_cons.mp hr).elim (fun e => e.symm ▸ aq) (acc r)⟩

/-- Unroll a node into a DTree, stopping only at derived nodes with incoming ≠ 1
    and classifying leaf input clauses by incoming = 1 (axUniq) vs incoming ≥ 2 (axRep). -/
noncomputable def dUnroll (i : Fin d.pi.length) : DTree V (Fin d.pi.length) :=
  match d.rules i with
  | .ax _ => if d.incoming i = 1 then .axUniq i else .axRep i
  | .weak j _hj _ =>
      .weak i (if d.children j = [] then (if d.incoming j = 1 then .axUniq j else .axRep j)
               else if d.incoming j = 1 then dUnroll j else .exitDer j)
  | .res j k _hj _hk h =>
      .res i (Classical.choose h)
        (if d.children j = [] then (if d.incoming j = 1 then .axUniq j else .axRep j)
         else if d.incoming j = 1 then dUnroll j else .exitDer j)
        (if d.children k = [] then (if d.incoming k = 1 then .axUniq k else .axRep k)
         else if d.incoming k = 1 then dUnroll k else .exitDer k)
termination_by d.pi.length - i.val
decreasing_by
  all_goals
    apply Nat.sub_lt_sub_left
    · exact i.isLt
    · first | exact _hj | exact _hk

noncomputable def dCutChild (j : Fin d.pi.length) : DTree V (Fin d.pi.length) :=
  if d.children j = [] then (if d.incoming j = 1 then .axUniq j else .axRep j)
  else if d.incoming j = 1 then d.dUnroll j else .exitDer j

theorem dUnroll_ax {i : Fin d.pi.length} {h} (hr : d.rules i = .ax h) :
    d.dUnroll i = (if d.incoming i = 1 then .axUniq i else .axRep i) := by
  rw [dUnroll, hr]

theorem dUnroll_weak {i j : Fin d.pi.length} {hj hw}
    (hr : d.rules i = .weak j hj hw) :
    d.dUnroll i = .weak i (d.dCutChild j) := by
  rw [dUnroll, hr]; rfl

theorem dUnroll_res {i j k : Fin d.pi.length} {hj hk hv}
    (hr : d.rules i = .res j k hj hk hv) :
    d.dUnroll i = .res i (Classical.choose hv) (d.dCutChild j) (d.dCutChild k) := by
  rw [dUnroll, hr]; rfl

theorem route_of_dUnroll {i j : Fin d.pi.length} {qs}
    (h : DTree.Route (d.dUnroll i) j qs) :
    d.LocalPath i j qs ∧ d.children j = [] ∧ d.incoming j = 1 := by
  have aux (n : ℕ) : ∀ (i : Fin d.pi.length) qs, d.pi.length - i.val = n →
      DTree.Route (d.dUnroll i) j qs →
      d.LocalPath i j qs ∧ d.children j = [] ∧ d.incoming j = 1 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i qs hn h
      have sub (k : Fin d.pi.length) (lt : i < k) {rs}
          (hk : DTree.Route (d.dCutChild k) j rs) :
          d.incoming k = 1 ∧ d.LocalPath k j rs ∧ d.children j = [] ∧ d.incoming j = 1 := by
        unfold dCutChild at hk
        by_cases hax : d.children k = []
        · rw [ite_eq_left hax] at hk
          by_cases hin : d.incoming k = 1
          · rw [ite_eq_left hin] at hk
            cases hk
            exact ⟨hin, .nil _, hax, hin⟩
          · rw [ite_eq_right hin] at hk; cases hk
        · rw [ite_eq_right hax] at hk
          by_cases hin : d.incoming k = 1
          · rw [ite_eq_left hin] at hk
            have hlt : i.val < k.val := lt
            have hb := k.isLt
            exact ⟨hin, ih _ (by omega) k rs rfl hk⟩
          · rw [ite_eq_right hin] at hk; cases hk
      cases hr : d.rules i with
      | ax ha =>
        rw [d.dUnroll_ax hr] at h
        by_cases hin : d.incoming i = 1
        · rw [ite_eq_left hin] at h; cases h
          exact ⟨.nil _, by simp [children, hr, Rule.parents], hin⟩
        · rw [ite_eq_right hin] at h; cases h
      | weak k hlt hv =>
        rw [d.dUnroll_weak hr] at h
        cases h with
        | weak h =>
          obtain ⟨h1, h2, h3, h4⟩ := sub k hlt h
          exact ⟨.cons (by simp [labels, hr, Rule.labelled]) h1 h2, h3, h4⟩
      | res k l hk hl hrule =>
        rw [d.dUnroll_res hr] at h
        cases h with
        | left h =>
          obtain ⟨h1, h2, h3, h4⟩ := sub k hk h
          exact ⟨.cons (by simp [labels, hr, Rule.labelled]) h1 h2, h3, h4⟩
        | right h =>
          obtain ⟨h1, h2, h3, h4⟩ := sub l hl h
          exact ⟨.cons (by simp [labels, hr, Rule.labelled]) h1 h2, h3, h4⟩
  exact aux _ i qs rfl h

theorem dUnroll_route_active (a : V → Bool) {i j : Fin d.pi.length} {qs}
    (h : DTree.Route (d.dUnroll i) j qs)
    (unique : ∀ C ∈ F, ¬ LinClauseSat a C → C = d.pi.get j) :
    ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  obtain ⟨k, hk, hax, hf⟩ := d.active_initial_clause a
  have heq := d.nodup.injective_get (unique _ (d.axiom_of_no_children k hax) hf)
  subst k
  exact (d.local_path_active (d.route_of_dUnroll h).1 hk hf).2

/-- A pure (weak-free) derived node cannot be subsumed by one of its unique leaf clauses. -/
theorem nonAx_not_subsumed_by_child_ax {i j : Fin d.pi.length}
    (hres : ∃ a b ha hb hr, d.rules i = .res a b ha hb hr)
    (hsub : ∀ a, LinClauseSat a (d.pi.get j) → LinClauseSat a (d.pi.get i))
    (hij : i < j)
    (hreach : ∃ c ∈ d.children i, d.incoming c = 1 ∧ c ≠ j) : False := by
  classical
  obtain ⟨c, hc, hinc, hcj⟩ := hreach
  let rules' : ∀ u, Rule F d.pi u := fun u =>
    if h : u = i then h ▸ .weak j hij hsub else d.rules u
  -- In rules', c has no parent at all (its only parent in d was i, whose new parent is j ≠ c).
  have hno_parent : ∀ u, c ∉ (rules' u).parents := by
    intro u hu
    by_cases hui : u = i
    · subst hui
      simp [rules', Rule.parents] at hu
      exact hcj hu
    · simp only [rules', dite_eq_right hui] at hu
      have eq := d.parent_unique hinc hc hu
      exact hui eq.symm
  have hnot_reach : ¬ Reaches rules' d.root c := by
    intro hr
    cases hr with
    | refl =>
      have hz := d.incoming_at_first
      omega
    | @tail u _ _ hp => exact hno_parent u hp
  let keep := (List.finRange d.pi.length).filter (fun u => decide (Reaches rules' d.root u))
  have order : keep.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have member (u : Fin d.pi.length) : u ∈ keep ↔ Reaches rules' d.root u := by
    simp [keep, List.mem_finRange]
  have closed : ∀ u ∈ keep, ∀ v ∈ (rules' u).parents, v ∈ keep := by
    intro u hu v hv
    exact (member v).mpr ((member u).mp hu |>.tail hv)
  have deriv := derivation_trim rules' keep order closed
  have emptyMem : (∅ : LinClause V) ∈ keep.map d.pi.get := by
    rw [← d.rootEmpty]
    exact List.mem_map_of_mem ((member d.root).mpr .refl)
  have lb := d.shortest _ deriv emptyMem
  rw [List.length_map] at lb
  have hcmem : c ∉ keep := fun h => hnot_reach ((member c).mp h)
  have hlt : keep.length < (List.finRange d.pi.length).length := by
    have hsubl : keep.Sublist (List.finRange d.pi.length) := List.filter_sublist
    have hne : keep ≠ List.finRange d.pi.length := fun e => hcmem (e ▸ List.mem_finRange c)
    have hle := hsubl.length_le
    by_contra hge
    exact hne (hsubl.eq_of_length (by omega))
  simp at hlt
  omega

end ShortestDag

end Dag

namespace BPHP

open PEqualNP.ProofComplexity

abbrev Variable := Fin 5 × Fin 2
abbrev Assignment := Variable → Bool

structure Collision where
  left : Fin 5
  right : Fin 5
  hole : Fin 4
  ordered : left < right
  deriving DecidableEq

def otherHoles (h : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter (· != h)

def otherRank (i j p : Fin 5) : ℕ :=
  ((List.finRange 5).filter (fun q => decide (q < p) && q != i && q != j)).length

def sampleHole (i j : Fin 5) (h : Fin 4) (phase : Fin 3) (p : Fin 5) : Fin 4 :=
  if p = i ∨ p = j then h else (otherHoles h).getD ((otherRank i j p + phase.val) % 3) h

def sample (c : Collision) (phase : Fin 3) : Assignment :=
  fun v => (sampleHole c.left c.right c.hole phase v.1).val.testBit v.2.val

def allIn (h : Fin 4) : Assignment := fun v => h.val.testBit v.2.val

theorem sample_hole_facts : ∀ (i j : Fin 5) (h : Fin 4) (r : Fin 3), i < j →
    sampleHole i j h r i = h ∧ sampleHole i j h r j = h ∧
    ∀ p q : Fin 5, p < q →
      (sampleHole i j h r p = sampleHole i j h r q ↔ p = i ∧ q = j) := by
  decide +kernel

theorem bit_geometry : ∀ (i j : Fin 5) (h : Fin 4) (p : Fin 5) (b : Fin 2), i < j →
    ((∀ r : Fin 3, (sampleHole i j h r p).val.testBit b.val = h.val.testBit b.val) ↔
      p = i ∨ p = j) ∧
    ((sampleHole i j h 0 p).val.testBit b.val ^^
      ((sampleHole i j h 1 p).val.testBit b.val ^^
        (sampleHole i j h 2 p).val.testBit b.val)) = h.val.testBit b.val := by
  decide +kernel

theorem sample_bits_xor (c : Collision) (v : Variable) :
    (sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole v :=
  (bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).2

def parity (f : Finset Variable) (a : Assignment) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

theorem parity_insert (a : Assignment) (f : Finset Variable) (v : Variable)
    (fresh : v ∉ f) : parity (insert v f) a = (a v ^^ parity f a) := by
  cases hv : a v
  · simp [parity, Finset.filter_insert, hv]
  · simp [parity, Finset.filter_insert, hv, Finset.card_insert_of_notMem,
      (show v ∉ f.filter (fun v => a v = true) from fun hm => fresh (Finset.mem_of_mem_filter v hm)),
      Nat.odd_add_one]
    let n := (f.filter (fun v => a v = true)).card
    change decide (Even n) = !decide (Odd n)
    by_cases ho : Odd n
    · have he : ¬ Even n := fun h => (Nat.not_odd_iff_even.mpr h) ho
      simp [ho, he]
    · have he : Even n := Nat.not_odd_iff_even.mp ho
      simp [ho, he]

theorem parity_xor (f : Finset Variable) (a b : Assignment) :
    parity f (fun v => a v ^^ b v) = (parity f a ^^ parity f b) := by
  classical
  induction f using Finset.induction_on with
  | empty => simp [parity]
  | insert v f fresh ih =>
    rw [parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, ih]
    cases a v <;> cases b v <;> cases parity f a <;> cases parity f b <;> rfl

theorem allIn_follows (c : Collision) (f : Finset Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, parity f (sample c r) = b) :
    parity f (allIn c.hole) = b := by
  have eq : (fun v => sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole :=
    funext (sample_bits_xor c)
  rw [← eq, parity_xor, parity_xor, agrees 0, agrees 1, agrees 2]
  cases b <;> rfl

theorem bit_constant (c : Collision) (v : Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, sample c r v = b) :
    (v.1 = c.left ∨ v.1 = c.right) ∧ b = allIn c.hole v := by
  have eq := sample_bits_xor c v
  rw [agrees 0, agrees 1, agrees 2] at eq
  have value : b = allIn c.hole v := by cases b <;> simpa using eq
  exact ⟨(bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).1.mp
    (fun r => (agrees r).trans value), value⟩

theorem parity_singleton (v : Variable) (a : Assignment) : parity {v} a = a v := by
  cases hv : a v <;> simp [parity, Finset.filter_singleton, hv]

def bits (h : Fin 4) : Fin 2 → Bool := fun b => h.val.testBit b.val

def holeOf (a : Fin 2 → Bool) : Fin 4 :=
  if a 1 then (if a 0 then 3 else 2) else (if a 0 then 1 else 0)

theorem bits_hole (a : Fin 2 → Bool) : bits (holeOf a) = a := by
  funext b
  cases h0 : a 0 <;> cases h1 : a 1 <;> fin_cases b <;> simp [holeOf, bits, h0, h1] <;> rfl

theorem hole_bits : ∀ h : Fin 4, holeOf (bits h) = h := by decide +kernel

theorem bits_injective : Function.Injective bits := by
  intro h k eq
  rw [← hole_bits h, ← hole_bits k, eq]

def pairClause (i j : Fin 5) (a : Fin 2 → Bool) : Clause Variable :=
  Finset.univ.image (fun b : Fin 2 => ((i, b), !a b)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j, b), !a b))

def Collision.clause (c : Collision) : LinClause Variable :=
  linOfClause (pairClause c.left c.right (bits c.hole))

abbrev Formula := (fun C => linOfClause C) '' BPHP 5 2

theorem Collision.mem_formula (c : Collision) : c.clause ∈ Formula :=
  ⟨pairClause c.left c.right (bits c.hole), ⟨c.left, c.right, bits c.hole, c.ordered.ne, rfl⟩, rfl⟩

theorem clause_key {D : LinClause Variable} (mem : D ∈ Formula) :
    ∃ c : Collision, D = c.clause := by
  obtain ⟨D0, ⟨i, j, a, hne, rfl⟩, rfl⟩ := mem
  rcases lt_or_gt_of_ne hne with forward | backward
  · exact ⟨⟨i, j, holeOf a, forward⟩, by simp [Collision.clause, pairClause, bits_hole]⟩
  · exact ⟨⟨j, i, holeOf a, backward⟩, by simp [Collision.clause, pairClause, bits_hole, Finset.union_comm]⟩

theorem singleton_iff (v : Variable) (s : Bool) (a : Assignment) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem falsifies_pair_iff (i j : Fin 5) (b : Fin 2 → Bool) (a : Assignment) :
    ¬ LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∀ q, a (i, q) = b q) ∧ (∀ q, a (j, q) = b q) := by
  have eval : LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∃ q, a (i, q) = !(b q)) ∨ (∃ q, a (j, q) = !(b q)) := by
    unfold LinClauseSat linOfClause pairClause
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨_, (⟨q, rfl⟩ | ⟨q, rfl⟩), rfl⟩, sat⟩
      · exact Or.inl ⟨q, (singleton_iff _ _ _).mp sat⟩
      · exact Or.inr ⟨q, (singleton_iff _ _ _).mp sat⟩
    · rintro (⟨q, e⟩ | ⟨q, e⟩)
      · exact ⟨_, ⟨_, Or.inl ⟨q, rfl⟩, rfl⟩, (singleton_iff _ _ _).mpr e⟩
      · exact ⟨_, ⟨_, Or.inr ⟨q, rfl⟩, rfl⟩, (singleton_iff _ _ _).mpr e⟩
  rw [eval]
  constructor
  · intro hn
    refine ⟨fun q => ?_, fun q => ?_⟩
    · have no : a (i, q) ≠ !(b q) := fun e => hn (Or.inl ⟨q, e⟩)
      cases hv : a (i, q) <;> cases hb : b q <;> simp_all
    · have no : a (j, q) ≠ !(b q) := fun e => hn (Or.inr ⟨q, e⟩)
      cases hv : a (j, q) <;> cases hb : b q <;> simp_all
  · rintro ⟨l, r⟩ (⟨q, e⟩ | ⟨q, e⟩)
    · have eq := l q; rw [eq] at e; cases h : b q <;> simp [h] at e
    · have eq := r q; rw [eq] at e; cases h : b q <;> simp [h] at e

theorem sample_falsifies (c : Collision) (r : Fin 3) :
    ¬ LinClauseSat (sample c r) c.clause := by
  have h := sample_hole_facts c.left c.right c.hole r c.ordered
  exact (falsifies_pair_iff _ _ _ _).mpr
    ⟨fun q => by simp [sample, bits, h.1], fun q => by simp [sample, bits, h.2.1]⟩

theorem unique_collision (c d : Collision) (r : Fin 3)
    (falsified : ¬ LinClauseSat (sample c r) d.clause) : c = d := by
  obtain ⟨l, r'⟩ := (falsifies_pair_iff _ _ _ _).mp falsified
  have lh : sampleHole c.left c.right c.hole r d.left = d.hole := bits_injective (funext l)
  have rh : sampleHole c.left c.right c.hole r d.right = d.hole := bits_injective (funext r')
  have samples := sample_hole_facts c.left c.right c.hole r c.ordered
  obtain ⟨leftEq, rightEq⟩ := (samples.2.2 d.left d.right d.ordered).mp (lh.trans rh.symm)
  have holeEq : c.hole = d.hole := by rw [leftEq, samples.1] at lh; exact lh
  cases c; cases d; simp_all

theorem sample_only_axiom (c : Collision) (r : Fin 3) {D : LinClause Variable}
    (mem : D ∈ Formula) (falsified : ¬ LinClauseSat (sample c r) D) : D = c.clause := by
  obtain ⟨d, rfl⟩ := clause_key mem
  rw [← unique_collision c d r falsified]

theorem clause_injective : Function.Injective Collision.clause := by
  intro c d same
  exact unique_collision c d 0 (same ▸ sample_falsifies c 0)

abbrev CollisionData := { t : Fin 5 × Fin 5 × Fin 4 // t.1 < t.2.1 }

def collisionEquiv : Collision ≃ CollisionData where
  toFun c := ⟨⟨c.left, c.right, c.hole⟩, c.ordered⟩
  invFun t := ⟨t.val.1, t.val.2.1, t.val.2.2, t.property⟩
  left_inv := by rintro ⟨i, j, h, p⟩; rfl
  right_inv := by rintro ⟨⟨i, j, h⟩, p⟩; rfl

instance : Fintype Collision := Fintype.ofEquiv CollisionData collisionEquiv.symm

theorem collision_count : Fintype.card Collision = 40 :=
  (Fintype.card_congr collisionEquiv).trans (by decide +kernel)

theorem Collision.mem_clause_bit (c : Collision) (b : Fin 2) :
    ({(c.left, b)}, !bits c.hole b) ∈ c.clause ∧
    ({(c.right, b)}, !bits c.hole b) ∈ c.clause := by
  constructor
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩

/-- Signed sub-assignment on the 10 variables of BPHP(5, 2). -/
abbrev State := Variable → Option Bool

def State.empty : State := fun _ => none

def State.Le (ρ₁ ρ₂ : State) : Prop :=
  ∀ v b, ρ₁ v = some b → ρ₂ v = some b

theorem State.Le.refl (ρ : State) : State.Le ρ ρ := fun _ _ h => h

theorem State.Le.trans {ρ₁ ρ₂ ρ₃ : State} (h1 : State.Le ρ₁ ρ₂) (h2 : State.Le ρ₂ ρ₃) :
    State.Le ρ₁ ρ₃ := fun v b hv => h2 v b (h1 v b hv)

def State.grant (ρ : State) (f : Finset Variable) (side : Bool) : State :=
  fun v => if f = {v} then some side else ρ v

def clauseState (C : LinClause Variable) : State :=
  fun v => if ({v}, false) ∈ C then some true
           else if ({v}, true) ∈ C then some false
           else none

theorem clauseState_empty : clauseState (∅ : LinClause Variable) = State.empty := by
  funext v; simp [clauseState, State.empty]

theorem nonTaut_not_both {C : LinClause Variable} (hU : Dag.Useful C) (v : Variable) :
    ¬ (({v}, false) ∈ C ∧ ({v}, true) ∈ C) := by
  rintro ⟨h0, h1⟩
  obtain ⟨a, ha⟩ := hU
  cases hv : a v
  · exact ha ⟨({v}, false), h0, (singleton_iff v false a).mpr hv⟩
  · exact ha ⟨({v}, true), h1, (singleton_iff v true a).mpr hv⟩

theorem clauseState_some_iff {C : LinClause Variable} (hU : Dag.Useful C) (v : Variable) (b : Bool) :
    clauseState C v = some b ↔ ({v}, !b) ∈ C := by
  have hnb := nonTaut_not_both hU v
  cases b <;> simp only [clauseState, Bool.not_false, Bool.not_true]
  · by_cases h0 : ({v}, false) ∈ C
    · simp only [ite_eq_left h0, Option.some.injEq, Bool.true_eq_false, false_iff]
      intro h1; exact hnb ⟨h0, h1⟩
    · by_cases h1 : ({v}, true) ∈ C <;> simp [h0, h1]
  · by_cases h0 : ({v}, false) ∈ C <;> simp [h0]

theorem carry_state {C D R : LinClause Variable} {f : Finset Variable} {ρ : State}
    (hUC : Dag.Useful C) (hUD : Dag.Useful D) (hUR : Dag.Useful R)
    (hres : (f, false) ∈ C ∧ (f, true) ∈ D ∧ R = C.erase (f, false) ∪ D.erase (f, true))
    (hR : State.Le (clauseState R) ρ) :
    State.Le (clauseState C) (State.grant ρ f true) ∧
    State.Le (clauseState D) (State.grant ρ f false) := by
  obtain ⟨hfC, hfD, rfl⟩ := hres
  constructor
  · intro v b hv
    have hm : ({v}, !b) ∈ C := (clauseState_some_iff hUC v b).mp hv
    unfold State.grant
    by_cases hfv : f = {v}
    · rw [ite_eq_left hfv]
      subst hfv
      cases b
      · exact False.elim (nonTaut_not_both hUC v ⟨hfC, hm⟩)
      · rfl
    · rw [ite_eq_right hfv]
      have hmR : ({v}, !b) ∈ C.erase (f, false) ∪ D.erase (f, true) :=
        Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hfv (congrArg Prod.fst e).symm, hm⟩)
      exact hR v b ((clauseState_some_iff hUR v b).mpr hmR)
  · intro v b hv
    have hm : ({v}, !b) ∈ D := (clauseState_some_iff hUD v b).mp hv
    unfold State.grant
    by_cases hfv : f = {v}
    · rw [ite_eq_left hfv]
      subst hfv
      cases b
      · rfl
      · exact False.elim (nonTaut_not_both hUD v ⟨hm, hfD⟩)
    · rw [ite_eq_right hfv]
      have hmR : ({v}, !b) ∈ C.erase (f, false) ∪ D.erase (f, true) :=
        Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => hfv (congrArg Prod.fst e).symm, hm⟩)
      exact hR v b ((clauseState_some_iff hUR v b).mpr hmR)

def SignedShared (cs : List Collision) (ρ : State) : Prop :=
  ∀ v b, ρ v = some b → ∀ c ∈ cs, ∀ r : Fin 3, sample c r v = b

theorem signedShared_of_clause {C : LinClause Variable} (hU : Dag.Useful C)
    (cs : List Collision) (bad : ∀ c ∈ cs, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) C) :
    SignedShared cs (clauseState C) := by
  intro v b hv c hc r
  have hm : ({v}, !b) ∈ C := (clauseState_some_iff hU v b).mp hv
  have hne : sample c r v ≠ !b := fun e => bad c hc r ⟨({v}, !b), hm, (singleton_iff v (!b) _).mpr e⟩
  cases hs : sample c r v <;> cases b <;> simp_all

theorem signedShared_grant {cs : List Collision} {ρ : State} {f : Finset Variable} {side : Bool}
    (hs : SignedShared cs ρ)
    (hroute : ∀ c ∈ cs, ∀ r : Fin 3, parity f (sample c r) = side) :
    SignedShared cs (State.grant ρ f side) := by
  intro v b hv c hc r
  unfold State.grant at hv
  by_cases hfv : f = {v}
  · rw [ite_eq_left hfv] at hv
    have hb : side = b := Option.some.inj hv
    subst hfv; subst hb
    exact (parity_singleton v (sample c r)).symm.trans (hroute c hc r)
  · rw [ite_eq_right hfv] at hv
    exact hs v b hv c hc r

theorem signedShared_mono {cs₁ cs₂ : List Collision} {ρ : State}
    (hs : SignedShared cs₂ ρ) (hsub : ∀ c ∈ cs₁, c ∈ cs₂) : SignedShared cs₁ ρ :=
  fun v b hv c hc r => hs v b hv c (hsub c hc) r

theorem three_holes_vary : ∀ (h k l : Fin 4) (d : Fin 2), h ≠ k → h ≠ l → k ≠ l →
    ¬ (bits h d = bits k d ∧ bits h d = bits l d) := by
  decide +kernel

theorem signedShared_const {c : Collision} {cs : List Collision} {ρ : State}
    (hs : SignedShared cs ρ) (hc : c ∈ cs) {v : Variable} {b : Bool} (hv : ρ v = some b) :
    (v.1 = c.left ∨ v.1 = c.right) ∧ b = bits c.hole v.2 :=
  bit_constant c v b (hs v b hv c hc)

theorem signedShared_three {cs : List Collision} {ρ : State}
    (nd : (cs.map Collision.hole).Nodup) (h3 : 3 ≤ cs.length)
    (hs : SignedShared cs ρ) : ρ = State.empty := by
  rcases cs with _ | ⟨c, _ | ⟨d, _ | ⟨g, rest⟩⟩⟩
  · simp at h3
  · simp at h3
  · simp at h3
  · funext v
    cases hv : ρ v with
    | none => rfl
    | some b =>
      have hc := signedShared_const (c := c) hs (by simp) hv
      have hd := signedShared_const (c := d) hs (by simp) hv
      have hg := signedShared_const (c := g) hs (by simp) hv
      have h1 := List.nodup_cons.mp nd
      have h2 := List.nodup_cons.mp h1.2
      exfalso
      apply three_holes_vary c.hole d.hole g.hole v.2
      · intro eq; exact h1.1 (by simp [eq])
      · intro eq; exact h1.1 (by simp [eq])
      · intro eq; exact h2.1 (by simp [eq])
      · exact ⟨hc.2.symm.trans hd.2, hc.2.symm.trans hg.2⟩

end BPHP

namespace Potential

open PEqualNP.ProofComplexity BPHP
open scoped Classical

def otherBit (b : Fin 2) : Fin 2 := 1 - b

theorem otherBit_facts : ∀ b : Fin 2,
    otherBit b ≠ b ∧ otherBit (otherBit b) = b ∧ ∀ x : Fin 2, x = b ∨ x = otherBit b := by
  decide +kernel

def flipBit (h : Fin 4) (b : Fin 2) : Fin 4 :=
  holeOf (fun q => if q = b then !bits h q else bits h q)

theorem flipBit_facts : ∀ (h : Fin 4) (b : Fin 2),
    flipBit h b ≠ h ∧
    bits (flipBit h b) b = !bits h b ∧
    bits (flipBit h b) (otherBit b) = bits h (otherBit b) ∧
    flipBit (flipBit h b) b = h := by
  decide +kernel

theorem other_hole_of_bit : ∀ (h₁ h₂ : Fin 4) (b : Fin 2),
    h₁ ≠ h₂ → bits h₁ b = bits h₂ b → h₂ = flipBit h₁ (otherBit b) := by
  decide +kernel

theorem holes_with_bit_card : ∀ (b : Fin 2) (val : Bool),
    (Finset.univ.filter (fun h : Fin 4 => bits h b = val)).card = 2 := by
  decide +kernel

theorem hole_eq_of_bits : ∀ (h₁ h₂ : Fin 4) (b : Fin 2),
    bits h₁ b = bits h₂ b → bits h₁ (otherBit b) = bits h₂ (otherBit b) → h₁ = h₂ := by
  decide +kernel

theorem exists_hole_of_bits : ∀ (b : Fin 2) (v₁ v₂ : Bool),
    ∃ h : Fin 4, bits h b = v₁ ∧ bits h (otherBit b) = v₂ := by
  decide +kernel

def pigeonHole (ρ : State) (p : Fin 5) (h : Fin 4) : Prop :=
  ρ (p, 0) = some (bits h 0) ∧ ρ (p, 1) = some (bits h 1)

theorem pigeonHole_bit {ρ : State} {p : Fin 5} {h : Fin 4}
    (hp : pigeonHole ρ p h) (b : Fin 2) : ρ (p, b) = some (bits h b) := by
  fin_cases b
  · exact hp.1
  · exact hp.2

theorem pigeonHole_of_bits {ρ : State} {p : Fin 5} {h : Fin 4} {b : Fin 2}
    (h1 : ρ (p, b) = some (bits h b)) (h2 : ρ (p, otherBit b) = some (bits h (otherBit b))) :
    pigeonHole ρ p h := by
  fin_cases b
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

theorem pigeonHole_unique {ρ : State} {p : Fin 5} {h₁ h₂ : Fin 4}
    (hp1 : pigeonHole ρ p h₁) (hp2 : pigeonHole ρ p h₂) : h₁ = h₂ := by
  apply bits_injective
  funext b
  have e1 := pigeonHole_bit hp1 b
  have e2 := pigeonHole_bit hp2 b
  exact Option.some.inj (e1.symm.trans e2)

def hasCollision (ρ : State) : Prop :=
  ∃ u v : Fin 5, u < v ∧ ∃ h : Fin 4, pigeonHole ρ u h ∧ pigeonHole ρ v h

def pigeonFixed (ρ : State) (p : Fin 5) : Prop :=
  ρ (p, 0) ≠ none ∨ ρ (p, 1) ≠ none

theorem pigeonFixed_of_some {ρ : State} {p : Fin 5} {b : Fin 2} {val : Bool}
    (h : ρ (p, b) = some val) : pigeonFixed ρ p := by
  fin_cases b
  · left; intro e; change ρ (p, (0 : Fin 2)) = some val at h; rw [e] at h; cases h
  · right; intro e; change ρ (p, (1 : Fin 2)) = some val at h; rw [e] at h; cases h

theorem pigeonFixed_of_hole {ρ : State} {p : Fin 5} {h : Fin 4}
    (hp : pigeonHole ρ p h) : pigeonFixed ρ p :=
  pigeonFixed_of_some hp.1

noncomputable def fixedPigeons (ρ : State) : ℕ :=
  (Finset.univ.filter (pigeonFixed ρ)).card

noncomputable def fixedBits (ρ : State) : ℕ :=
  (Finset.univ.filter (fun v : Variable => ρ v ≠ none)).card

theorem fixedBits_empty : fixedBits State.empty = 0 := by
  simp [fixedBits, State.empty]

theorem eq_empty_of_fixedBits_zero {ρ : State} (h : fixedBits ρ = 0) : ρ = State.empty := by
  funext v
  have hem : Finset.univ.filter (fun w : Variable => ρ w ≠ none) = ∅ :=
    Finset.card_eq_zero.mp h
  by_contra hne
  have hm : v ∈ Finset.univ.filter (fun w : Variable => ρ w ≠ none) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hne⟩
  rw [hem] at hm
  simp at hm

def sameBitPair (ρ : State) (u v : Fin 5) (b : Fin 2) (val : Bool) : Prop :=
  u < v ∧ ρ (u, b) = some val ∧ ρ (v, b) = some val

def pairHoles (u v : Fin 5) (b : Fin 2) (val : Bool) : Finset Collision :=
  Finset.univ.filter (fun c : Collision => c.left = u ∧ c.right = v ∧ bits c.hole b = val)

def DistinctHoles (ow : Finset Collision) : Prop :=
  ∀ c₁ ∈ ow, ∀ c₂ ∈ ow, c₁.hole = c₂.hole → c₁ = c₂

theorem distinctHoles_bit_card {ow : Finset Collision} (hd : DistinctHoles ow)
    (b : Fin 2) (val : Bool) :
    (ow.filter (fun c => bits c.hole b = val)).card ≤ 2 := by
  let S := ow.filter (fun c => bits c.hole b = val)
  have hinj : Set.InjOn Collision.hole (S : Set Collision) := by
    intro c₁ hc₁ c₂ hc₂ heq
    exact hd c₁ (Finset.mem_filter.mp hc₁).1 c₂ (Finset.mem_filter.mp hc₂).1 heq
  have hsub : S.image Collision.hole ⊆ Finset.univ.filter (fun h : Fin 4 => bits h b = val) := by
    intro h hh
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, holes_with_bit_card] at hcard
  exact hcard

def hasDoubleOneStep (ρ : State) : Prop :=
  ∃ p : Fin 5, ∃ b : Fin 2, ∃ val : Bool,
    ρ (p, b) = some val ∧ ρ (p, otherBit b) = none ∧
    ∀ h : Fin 4, bits h b = val → ∃ q : Fin 5, pigeonHole ρ q h

def hasDoublePartialMatch (ρ : State) : Prop :=
  ∃ p₁ p₂ q : Fin 5, ∃ b : Fin 2, ∃ val : Bool, ∃ h : Fin 4,
    p₁ ≠ p₂ ∧ bits h b = val ∧ pigeonHole ρ q h ∧
    ρ (p₁, b) = some val ∧ ρ (p₁, otherBit b) = none ∧
    ρ (p₂, b) = some val ∧ ρ (p₂, otherBit b) = none

noncomputable def leafWeight (ρ : State) (ow : Finset Collision) : ℕ :=
  if ∃ u v b val, sameBitPair ρ u v b val ∧ Disjoint (pairHoles u v b val) ow
  then 3
  else if ∃ u v b val, sameBitPair ρ u v b val ∧ (pairHoles u v b val ∩ ow).card ≤ 1
  then 4
  else 6

theorem leafWeight_ge_three (ρ : State) (ow : Finset Collision) : 3 ≤ leafWeight ρ ow := by
  unfold leafWeight
  split_ifs <;> omega

theorem leafWeight_le_six (ρ : State) (ow : Finset Collision) : leafWeight ρ ow ≤ 6 := by
  unfold leafWeight
  split_ifs <;> omega

theorem leafWeight_eq_three_of_disjoint {ρ : State} {ow : Finset Collision}
    {u v : Fin 5} {b : Fin 2} {val : Bool}
    (hs : sameBitPair ρ u v b val) (hd : Disjoint (pairHoles u v b val) ow) :
    leafWeight ρ ow = 3 := by
  unfold leafWeight
  rw [ite_eq_left ⟨u, v, b, val, hs, hd⟩]

theorem leafWeight_le_four_of_card_le_one {ρ : State} {ow : Finset Collision}
    {u v : Fin 5} {b : Fin 2} {val : Bool}
    (hs : sameBitPair ρ u v b val) (hc : (pairHoles u v b val ∩ ow).card ≤ 1) :
    leafWeight ρ ow ≤ 4 := by
  unfold leafWeight
  by_cases h3 : ∃ u' v' b' val',
      sameBitPair ρ u' v' b' val' ∧ Disjoint (pairHoles u' v' b' val') ow
  · rw [ite_eq_left h3]; omega
  · rw [ite_eq_right h3, ite_eq_left ⟨u, v, b, val, hs, hc⟩]

theorem three_pigeons_sameBit_leafWeight {ρ : State} {ow : Finset Collision}
    (hd : DistinctHoles ow) {p₁ p₂ p₃ : Fin 5} {b : Fin 2} {val : Bool}
    (h12 : p₁ < p₂) (h23 : p₂ < p₃)
    (hp1 : ρ (p₁, b) = some val) (hp2 : ρ (p₂, b) = some val) (hp3 : ρ (p₃, b) = some val) :
    leafWeight ρ ow = 3 := by
  have h13 : p₁ < p₃ := h12.trans h23
  let A := pairHoles p₁ p₂ b val ∩ ow
  let B := pairHoles p₁ p₃ b val ∩ ow
  let C := pairHoles p₂ p₃ b val ∩ ow
  let T := ow.filter (fun c => bits c.hole b = val)
  have hAT : A ⊆ T := by
    intro c hc; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hc
    exact Finset.mem_filter.mpr ⟨h2, (Finset.mem_filter.mp h1).2.2.2⟩
  have hBT : B ⊆ T := by
    intro c hc; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hc
    exact Finset.mem_filter.mpr ⟨h2, (Finset.mem_filter.mp h1).2.2.2⟩
  have hCT : C ⊆ T := by
    intro c hc; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hc
    exact Finset.mem_filter.mpr ⟨h2, (Finset.mem_filter.mp h1).2.2.2⟩
  have dAB : Disjoint A B := Finset.disjoint_left.mpr fun c ha hb => by
    have e1 := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2.2.1
    have e2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2.2.1
    exact h23.ne (e1.symm.trans e2)
  have dAC : Disjoint A C := Finset.disjoint_left.mpr fun c ha hc => by
    have e1 := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2.1
    have e2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2.1
    exact h12.ne (e1.symm.trans e2)
  have dBC : Disjoint B C := Finset.disjoint_left.mpr fun c hb hc => by
    have e1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2.1
    have e2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2.1
    exact h12.ne (e1.symm.trans e2)
  have hsum : A.card + B.card + C.card ≤ 2 := by
    have hsub : A ∪ B ∪ C ⊆ T := Finset.union_subset (Finset.union_subset hAT hBT) hCT
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dAC, dBC⟩),
        Finset.card_union_of_disjoint dAB] at hc
    exact hc.trans (distinctHoles_bit_card hd b val)
  have hor : A.card = 0 ∨ B.card = 0 ∨ C.card = 0 := by omega
  rcases hor with h0 | h0 | h0
  · exact leafWeight_eq_three_of_disjoint ⟨h12, hp1, hp2⟩
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0))
  · exact leafWeight_eq_three_of_disjoint ⟨h13, hp1, hp3⟩
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0))
  · exact leafWeight_eq_three_of_disjoint ⟨h23, hp2, hp3⟩
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0))

theorem three_distinct_sameBit_leafWeight {ρ : State} {ow : Finset Collision}
    (hd : DistinctHoles ow) {p₁ p₂ p₃ : Fin 5} {b : Fin 2} {val : Bool}
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hp1 : ρ (p₁, b) = some val) (hp2 : ρ (p₂, b) = some val) (hp3 : ρ (p₃, b) = some val) :
    leafWeight ρ ow = 3 := by
  rcases lt_or_gt_of_ne h12 with a12 | a21
  · rcases lt_or_gt_of_ne h23 with a23 | a32
    · exact three_pigeons_sameBit_leafWeight hd a12 a23 hp1 hp2 hp3
    · rcases lt_or_gt_of_ne h13 with a13 | a31
      · exact three_pigeons_sameBit_leafWeight hd a13 a32 hp1 hp3 hp2
      · exact three_pigeons_sameBit_leafWeight hd a31 a12 hp3 hp1 hp2
  · rcases lt_or_gt_of_ne h13 with a13 | a31
    · exact three_pigeons_sameBit_leafWeight hd a21 a13 hp2 hp1 hp3
    · rcases lt_or_gt_of_ne h23 with a23 | a32
      · exact three_pigeons_sameBit_leafWeight hd a23 a31 hp2 hp3 hp1
      · exact three_pigeons_sameBit_leafWeight hd a32 a21 hp3 hp2 hp1

noncomputable def b0 (ρ : State) (ow : Finset Collision) : ℕ :=
  if hasCollision ρ then 1
  else if hasDoubleOneStep ρ then 2
  else if 4 ≤ fixedPigeons ρ then min (leafWeight ρ ow) 3
  else if fixedPigeons ρ = 3 then min (leafWeight ρ ow) 4
  else leafWeight ρ ow

theorem b0_ge_one (ρ : State) (ow : Finset Collision) : 1 ≤ b0 ρ ow := by
  unfold b0
  have h3 := leafWeight_ge_three ρ ow
  split_ifs <;> omega

theorem b0_le_leafWeight (ρ : State) (ow : Finset Collision) : b0 ρ ow ≤ leafWeight ρ ow := by
  unfold b0
  have h3 := leafWeight_ge_three ρ ow
  split_ifs <;> omega

theorem b0_le_six (ρ : State) (ow : Finset Collision) : b0 ρ ow ≤ 6 :=
  (b0_le_leafWeight ρ ow).trans (leafWeight_le_six ρ ow)

theorem b0_of_hasCollision {ρ : State} {ow : Finset Collision} (h : hasCollision ρ) :
    b0 ρ ow = 1 := by
  unfold b0; rw [ite_eq_left h]

theorem b0_of_fp_le_two {ρ : State} {ow : Finset Collision}
    (hnc : ¬ hasCollision ρ) (hfp : fixedPigeons ρ ≤ 2) :
    b0 ρ ow = leafWeight ρ ow := by
  have hnd : ¬ hasDoubleOneStep ρ := by
    rintro ⟨p, b, val, hpb, hpo, hall⟩
    obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits b val false
    obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits b val true
    obtain ⟨q0, hq0⟩ := hall h0 hb0
    obtain ⟨q1, hq1⟩ := hall h1 hb1
    have hne_h : h0 ≠ h1 := fun e => by rw [e, ho1] at ho0; cases ho0
    have hq01 : q0 ≠ q1 := fun e => hne_h (pigeonHole_unique (e ▸ hq0) hq1)
    have hpq0 : p ≠ q0 := fun e => by
      have := pigeonHole_bit (e ▸ hq0) (otherBit b); rw [hpo] at this; cases this
    have hpq1 : p ≠ q1 := fun e => by
      have := pigeonHole_bit (e ▸ hq1) (otherBit b); rw [hpo] at this; cases this
    have hsub : ({p, q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl | rfl
      · exact pigeonFixed_of_some hpb
      · exact pigeonFixed_of_hole hq0
      · exact pigeonFixed_of_hole hq1
    have hc := Finset.card_le_card hsub
    simp [hpq0, hpq1, hq01] at hc
    change 3 ≤ fixedPigeons ρ at hc
    omega
  unfold b0
  rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem grant_eq_self {ρ : State} {v : Variable} {side : Bool} (hv : ρ v = some side) :
    State.grant ρ {v} side = ρ := by
  funext w
  unfold State.grant
  by_cases h : ({v} : Finset Variable) = {w}
  · rw [ite_eq_left h]
    have e : v = w := Finset.singleton_injective h
    subst e; exact hv.symm
  · rw [ite_eq_right h]

theorem grant_apply_self (ρ : State) (v : Variable) (side : Bool) :
    State.grant ρ {v} side v = some side := by
  simp [State.grant]

theorem grant_apply_ne (ρ : State) {v w : Variable} (hne : v ≠ w) (side : Bool) :
    State.grant ρ {v} side w = ρ w := by
  unfold State.grant
  rw [ite_eq_right (fun h => hne (Finset.singleton_injective h))]

theorem fixedBits_grant_none {ρ : State} {v : Variable} (hv : ρ v = none) (side : Bool) :
    fixedBits (State.grant ρ {v} side) = fixedBits ρ + 1 := by
  unfold fixedBits
  have eq : Finset.univ.filter (fun w : Variable => State.grant ρ {v} side w ≠ none) =
      insert v (Finset.univ.filter (fun w : Variable => ρ w ≠ none)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases h : w = v
    · subst h; simp [grant_apply_self]
    · simp [grant_apply_ne ρ (Ne.symm h), h]
  rw [eq, Finset.card_insert_of_notMem]
  simp [hv]

theorem fixedPigeons_grant_of_other_some {ρ : State} {p : Fin 5} {b : Fin 2}
    (ho : ρ (p, otherBit b) ≠ none) (side : Bool) :
    fixedPigeons (State.grant ρ {(p, b)} side) = fixedPigeons ρ := by
  unfold fixedPigeons
  congr 1; ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hqp : q = p
  · subst hqp
    have h1 : pigeonFixed (State.grant ρ {(q, b)} side) q :=
      pigeonFixed_of_some (grant_apply_self ρ (q, b) side)
    have h2 : pigeonFixed ρ q := by
      cases h : ρ (q, otherBit b) with
      | none => exact (ho h).elim
      | some val => exact pigeonFixed_of_some h
    exact iff_of_true h1 h2
  · have e0 : State.grant ρ {(p, b)} side (q, 0) = ρ (q, 0) :=
      grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm) side
    have e1 : State.grant ρ {(p, b)} side (q, 1) = ρ (q, 1) :=
      grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm) side
    simp [pigeonFixed, e0, e1]

theorem fixedPigeons_grant_of_both_none {ρ : State} {p : Fin 5} {b : Fin 2}
    (hb : ρ (p, b) = none) (ho : ρ (p, otherBit b) = none) (side : Bool) :
    fixedPigeons (State.grant ρ {(p, b)} side) = fixedPigeons ρ + 1 := by
  unfold fixedPigeons
  have eq : Finset.univ.filter (pigeonFixed (State.grant ρ {(p, b)} side)) =
      insert p (Finset.univ.filter (pigeonFixed ρ)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hqp : q = p
    · subst hqp
      simp [pigeonFixed_of_some (grant_apply_self ρ (q, b) side)]
    · have e0 : State.grant ρ {(p, b)} side (q, 0) = ρ (q, 0) :=
        grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm) side
      have e1 : State.grant ρ {(p, b)} side (q, 1) = ρ (q, 1) :=
        grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm) side
      simp [pigeonFixed, e0, e1, hqp]
  rw [eq, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pigeonFixed, not_or, not_not]
  fin_cases b
  · exact ⟨hb, ho⟩
  · exact ⟨ho, hb⟩

theorem pigeonHole_grant_ne {ρ : State} {p q : Fin 5} {b : Fin 2} {side : Bool} {h : Fin 4}
    (hq : q ≠ p) : pigeonHole (State.grant ρ {(p, b)} side) q h ↔ pigeonHole ρ q h := by
  have e0 : State.grant ρ {(p, b)} side (q, 0) = ρ (q, 0) :=
    grant_apply_ne ρ (fun e => hq (congrArg Prod.fst e).symm) side
  have e1 : State.grant ρ {(p, b)} side (q, 1) = ρ (q, 1) :=
    grant_apply_ne ρ (fun e => hq (congrArg Prod.fst e).symm) side
  simp [pigeonHole, e0, e1]

theorem hasCollision_grant_elim {ρ : State} {p : Fin 5} {b : Fin 2} {side : Bool}
    (hnc : ¬ hasCollision ρ) (hc : hasCollision (State.grant ρ {(p, b)} side)) :
    ∃ h : Fin 4, ∃ q : Fin 5, q ≠ p ∧
      bits h b = side ∧ ρ (p, otherBit b) = some (bits h (otherBit b)) ∧ pigeonHole ρ q h := by
  obtain ⟨u, v, huv, h, hu, hv⟩ := hc
  by_cases hup : u = p
  · subst hup
    have hvp : v ≠ u := huv.ne'
    have hv' : pigeonHole ρ v h := (pigeonHole_grant_ne hvp).mp hv
    have h1 := pigeonHole_bit hu b
    rw [grant_apply_self] at h1
    have h2 := pigeonHole_bit hu (otherBit b)
    rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm)] at h2
    exact ⟨h, v, hvp, (Option.some.inj h1).symm, h2, hv'⟩
  · by_cases hvp : v = p
    · subst hvp
      have hu' : pigeonHole ρ u h := (pigeonHole_grant_ne hup).mp hu
      have h1 := pigeonHole_bit hv b
      rw [grant_apply_self] at h1
      have h2 := pigeonHole_bit hv (otherBit b)
      rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm)] at h2
      exact ⟨h, u, hup, (Option.some.inj h1).symm, h2, hu'⟩
    · exact (hnc ⟨u, v, huv, h, (pigeonHole_grant_ne hup).mp hu, (pigeonHole_grant_ne hvp).mp hv⟩).elim

theorem b0_split {ρ : State} {ow : Finset Collision} (hd : DistinctHoles ow) (v : Variable) :
    b0 ρ ow ≤ b0 (State.grant ρ {v} false) ow + b0 (State.grant ρ {v} true) ow := by
  let ρ0 := State.grant ρ {v} false
  let ρ1 := State.grant ρ {v} true
  change b0 ρ ow ≤ b0 ρ0 ow + b0 ρ1 ow
  cases hv : ρ v with
  | some b =>
    cases b
    · rw [show ρ0 = ρ from grant_eq_self hv]; omega
    · rw [show ρ1 = ρ from grant_eq_self hv]; omega
  | none =>
    rcases v with ⟨p, b⟩
    have hge0 := b0_ge_one ρ0 ow
    have hge1 := b0_ge_one ρ1 ow
    by_cases hle2 : b0 ρ ow ≤ 2
    · omega
    have hnc : ¬ hasCollision ρ := fun hc => by rw [b0_of_hasCollision hc] at hle2; omega
    have hnd : ¬ hasDoubleOneStep ρ := fun hdb => by
      unfold b0 at hle2; rw [ite_eq_right hnc, ite_eq_left hdb] at hle2; omega
    -- Cannot have both ρ0 and ρ1 collide (that would give hasDoubleOneStep ρ).
    have hnot_both_coll : ¬ (hasCollision ρ0 ∧ hasCollision ρ1) := by
      rintro ⟨hc0, hc1⟩
      obtain ⟨h0, q0, _, hb0, ho0, hq0⟩ := hasCollision_grant_elim hnc hc0
      obtain ⟨h1, q1, _, hb1, ho1, hq1⟩ := hasCollision_grant_elim hnc hc1
      have hval : bits h0 (otherBit b) = bits h1 (otherBit b) := Option.some.inj (ho0.symm.trans ho1)
      apply hnd
      refine ⟨p, otherBit b, bits h0 (otherBit b), ho0, by rwa [(otherBit_facts b).2.1], ?_⟩
      intro h hh
      cases hhb : bits h b
      · have eh : h = h0 := hole_eq_of_bits h h0 b (hhb.trans hb0.symm) hh
        exact ⟨q0, eh ▸ hq0⟩
      · have eh : h = h1 := hole_eq_of_bits h h1 b (hhb.trans hb1.symm) (hh.trans hval)
        exact ⟨q1, eh ▸ hq1⟩
    by_cases h3 : b0 ρ ow = 3
    · have : ¬ (b0 ρ0 ow = 1 ∧ b0 ρ1 ow = 1) := by
        rintro ⟨e0, e1⟩
        have c0 : hasCollision ρ0 := by
          unfold b0 at e0; have := leafWeight_ge_three ρ0 ow; split_ifs at e0 <;> omega
        have c1 : hasCollision ρ1 := by
          unfold b0 at e1; have := leafWeight_ge_three ρ1 ow; split_ifs at e1 <;> omega
        exact hnot_both_coll ⟨c0, c1⟩
      omega
    -- Now b0 ρ ow ∈ {4, 6} (since leafWeight ∈ {3, 4, 6} and b0 ρ ow > 3).
    have hfp3 : fixedPigeons ρ ≤ 3 := by
      by_contra h4
      unfold b0 at hle2 h3
      rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_left (by omega)] at hle2 h3
      have := leafWeight_ge_three ρ ow
      omega
    have hlw4 : 4 ≤ leafWeight ρ ow := by
      have := b0_le_leafWeight ρ ow; omega
    -- Helper: if ρ_side collides and ρ_other hasDoubleOneStep, contradiction with b0 ρ ow ≥ 4!
    have hnot_coll_double : ∀ (s : Bool),
        hasCollision (State.grant ρ {(p, b)} s) →
        hasDoubleOneStep (State.grant ρ {(p, b)} (!s)) → False := by
      intro s hc hd'
      obtain ⟨h0, q0, hq0p, hb0, ho0, hq0⟩ := hasCollision_grant_elim hnc hc
      have hfp_eq : fixedPigeons (State.grant ρ {(p, b)} (!s)) = fixedPigeons ρ :=
        fixedPigeons_grant_of_other_some (by simp [ho0]) (!s)
      -- p is fixed to hole h1 = flipBit h0 b in ρ' = grant ρ {(p,b)} (!s)
      let h1 := flipBit h0 b
      have hp1 : pigeonHole (State.grant ρ {(p, b)} (!s)) p h1 := by
        apply pigeonHole_of_bits (b := b)
        · rw [grant_apply_self, (flipBit_facts h0 b).2.1, hb0]
        · rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm),
              (flipBit_facts h0 b).2.2.1, ho0]
      obtain ⟨r, br, valr, hrb, hro, hallr⟩ := hd'
      have hrp : r ≠ p := by
        intro e; subst e
        have := pigeonHole_bit hp1 (otherBit br); rw [hro] at this; cases this
      have hrb_orig : ρ (r, br) = some valr := by
        rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hrb
      have hro_orig : ρ (r, otherBit br) = none := by
        rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hro
      -- Since ¬ hasDoubleOneStep ρ, one of the 2 holes for (br, valr) has NO full pigeon in ρ,
      -- so it MUST be h1 (the only newly full pigeon is p at h1!).
      have hex_h1 : bits h1 br = valr := by
        by_contra hne
        apply hnd
        refine ⟨r, br, valr, hrb_orig, hro_orig, fun h hh => ?_⟩
        obtain ⟨q, hq⟩ := hallr h hh
        by_cases hqp : q = p
        · subst hqp
          have eh := pigeonHole_unique hq hp1
          exact (hne (eh ▸ hh)).elim
        · exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
      -- The OTHER hole h2 = flipBit h1 (otherBit br) has a full pigeon q2 ≠ p in ρ!
      let h2 := flipBit h1 (otherBit br)
      have hh2_br : bits h2 br = valr := by
        have := (flipBit_facts h1 (otherBit br)).2.2.1
        rwa [(otherBit_facts br).2.1, hex_h1] at this
      obtain ⟨q2, hq2'⟩ := hallr h2 hh2_br
      have hq2p : q2 ≠ p := by
        intro e; subst e
        exact (flipBit_facts h1 (otherBit br)).1 (pigeonHole_unique hq2' hp1)
      have hq2 : pigeonHole ρ q2 h2 := (pigeonHole_grant_ne hq2p).mp hq2'
      have hq2r : q2 ≠ r := by
        intro e; subst e
        have := pigeonHole_bit hq2 (otherBit br); rw [hro_orig] at this; cases this
      have hq0r : q0 ≠ r := by
        intro e; subst e
        have := pigeonHole_bit hq0 (otherBit br); rw [hro_orig] at this; cases this
      by_cases hq02 : q0 = q2
      · -- Then h0 = h2, so br = otherBit b and valr = bits h0 (otherBit b)!
        subst hq02
        have eh02 : h0 = h2 := pigeonHole_unique hq0 hq2
        have hbr_eq : br = otherBit b := by
          rcases (otherBit_facts b).2.2 br with hbr | hbr
          · exfalso
            have e1 : bits h2 b = bits h1 b := hbr ▸ (hh2_br.trans hex_h1.symm)
            rw [← eh02, (flipBit_facts h0 b).2.1] at e1
            cases bits h0 b <;> simp at e1
          · exact hbr
        subst br
        have hval_eq : valr = bits h0 (otherBit b) := by
          rw [← hex_h1, (flipBit_facts h0 b).2.2.1]
        -- Now q0, p, r are 3 distinct pigeons all having (otherBit b) = some valr!
        have hlw3 := three_distinct_sameBit_leafWeight hd hq0p hq0r hrp.symm
          (hval_eq ▸ pigeonHole_bit hq0 (otherBit b)) (hval_eq ▸ ho0) hrb_orig
        omega
      · -- q0, q2, p, r are 4 distinct fixed pigeons in ρ, contradicting hfp3!
        have hsub : ({q0, q2, p, r} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl
          · exact pigeonFixed_of_hole hq0
          · exact pigeonFixed_of_hole hq2
          · exact pigeonFixed_of_some ho0
          · exact pigeonFixed_of_some hrb_orig
        have hc4 := Finset.card_le_card hsub
        simp [hq02, hq0p, hq0r, hq2p, hq2r, hrp.symm] at hc4
        change 4 ≤ fixedPigeons ρ at hc4
        omega
    by_cases h4 : b0 ρ ow = 4
    · -- Need b0 ρ0 + b0 ρ1 ≥ 4! Only forbidden pairs are (1,1), (1,2), (2,1).
      have hnb12 : ¬ (b0 ρ0 ow = 1 ∧ b0 ρ1 ow ≤ 2) := by
        rintro ⟨e0, e1⟩
        have c0 : hasCollision ρ0 := by
          unfold b0 at e0; have := leafWeight_ge_three ρ0 ow; split_ifs at e0 <;> omega
        by_cases c1 : hasCollision ρ1
        · exact hnot_both_coll ⟨c0, c1⟩
        · have d1 : hasDoubleOneStep ρ1 := by
            unfold b0 at e1; have := leafWeight_ge_three ρ1 ow
            rw [ite_eq_right c1] at e1; split_ifs at e1 <;> omega
          exact hnot_coll_double false c0 d1
      have hnb21 : ¬ (b0 ρ0 ow ≤ 2 ∧ b0 ρ1 ow = 1) := by
        rintro ⟨e0, e1⟩
        have c1 : hasCollision ρ1 := by
          unfold b0 at e1; have := leafWeight_ge_three ρ1 ow; split_ifs at e1 <;> omega
        by_cases c0 : hasCollision ρ0
        · exact hnot_both_coll ⟨c0, c1⟩
        · have d0 : hasDoubleOneStep ρ0 := by
            unfold b0 at e0; have := leafWeight_ge_three ρ0 ow
            rw [ite_eq_right c0] at e0; split_ifs at e0 <;> omega
          exact hnot_coll_double true c1 d0
      omega
    -- Remaining case: b0 ρ ow = 6 (so fixedPigeons ρ ≤ 2 and leafWeight ρ ow = 6)!
    have h6 : b0 ρ ow = 6 := by
      unfold b0 at hle2 h3 h4 ⊢
      rw [ite_eq_right hnc, ite_eq_right hnd] at hle2 h3 h4 ⊢
      have hlw_cases : leafWeight ρ ow = 3 ∨ leafWeight ρ ow = 4 ∨ leafWeight ρ ow = 6 := by
        unfold leafWeight; split_ifs <;> omega
      split_ifs at hle2 h3 h4 ⊢ <;> omega
    have hfp2 : fixedPigeons ρ ≤ 2 := by
      by_contra h3'
      unfold b0 at h6
      rw [ite_eq_right hnc, ite_eq_right hnd] at h6
      split_ifs at h6 <;> omega
    have hlw6 : leafWeight ρ ow = 6 := by
      have := b0_of_fp_le_two (ow := ow) hnc hfp2; omega
    -- Split on whether p's other bit is already set in ρ!
    cases ho : ρ (p, otherBit b) with
    | some val' =>
      have hfp0 : fixedPigeons ρ0 ≤ 2 := by
        rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
      have hfp1 : fixedPigeons ρ1 ≤ 2 := by
        rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
      -- Helper: if ρ_s collides, then ρ_(!s) has b0 = 6!
      have hcoll_other6 : ∀ (s : Bool), hasCollision (State.grant ρ {(p, b)} s) →
          b0 (State.grant ρ {(p, b)} (!s)) ow = 6 := by
        intro s hc
        have hnc' : ¬ hasCollision (State.grant ρ {(p, b)} (!s)) := fun hc' => by
          cases s <;> exact hnot_both_coll (by first | exact ⟨hc, hc'⟩ | exact ⟨hc', hc⟩)
        have hfp' : fixedPigeons (State.grant ρ {(p, b)} (!s)) ≤ 2 := by
          rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
        rw [b0_of_fp_le_two hnc' hfp']
        obtain ⟨h0, q, hqp, hb0, ho0, hq⟩ := hasCollision_grant_elim hnc hc
        -- Every fixed pigeon in ρ' is p or q!
        have honly : ∀ x, pigeonFixed (State.grant ρ {(p, b)} (!s)) x → x = p ∨ x = q := by
          intro x hx
          have hsub : ({p, q} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rcases hy with rfl | rfl
            · exact pigeonFixed_of_some ho0
            · exact pigeonFixed_of_hole hq
          have hcard : ({p, q} : Finset (Fin 5)).card = 2 := by simp [hqp.symm]
          have heq : ({p, q} : Finset (Fin 5)) = Finset.univ.filter (pigeonFixed ρ) :=
            Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hfp2)
          have hxq : pigeonFixed ρ x := by
            by_cases hxp : x = p
            · subst hxp; exact pigeonFixed_of_some ho0
            · have e0 : State.grant ρ {(p, b)} (!s) (x, 0) = ρ (x, 0) :=
                grant_apply_ne ρ (fun e => hxp (congrArg Prod.fst e).symm) (!s)
              have e1 : State.grant ρ {(p, b)} (!s) (x, 1) = ρ (x, 1) :=
                grant_apply_ne ρ (fun e => hxp (congrArg Prod.fst e).symm) (!s)
              simpa [pigeonFixed, e0, e1] using hx
          have hm : x ∈ ({p, q} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxq⟩
          simpa using hm
        -- Any sameBitPair in ρ' must be on {p, q} and on bit (otherBit b), hence already in ρ!
        have hsame_imp : ∀ u v b' val', sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' →
            sameBitPair ρ u v b' val' := by
          intro u v b' val' ⟨huv, hu', hv'⟩
          have hu_pq := honly u (pigeonFixed_of_some hu')
          have hv_pq := honly v (pigeonFixed_of_some hv')
          have hpair : (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
            rcases hu_pq with rfl | rfl <;> rcases hv_pq with rfl | rfl
            · exact (huv.ne rfl).elim
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
            · exact (huv.ne rfl).elim
          have hb_ne : b' ≠ b := by
            intro eb; subst b'
            have hqb := pigeonHole_bit hq b
            rw [hb0] at hqb
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [grant_apply_self] at hu'
              rw [grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm), hqb] at hv'
              have e1 := Option.some.inj hu'
              have e2 := Option.some.inj hv'
              rw [← e1] at e2; cases s <;> cases e2
            · rw [grant_apply_self] at hv'
              rw [grant_apply_ne ρ (fun e => hqp (congrArg Prod.fst e).symm), hqb] at hu'
              have e1 := Option.some.inj hv'
              have e2 := Option.some.inj hu'
              rw [← e1] at e2; cases s <;> cases e2
          refine ⟨huv, ?_, ?_⟩
          · rwa [grant_apply_ne ρ (fun e => hb_ne (congrArg Prod.snd e).symm)] at hu'
          · rwa [grant_apply_ne ρ (fun e => hb_ne (congrArg Prod.snd e).symm)] at hv'
        unfold leafWeight at hlw6 ⊢
        by_cases h3' : ∃ u v b' val',
            sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
        · obtain ⟨u, v, b', val', hs', hdj⟩ := h3'
          have h3ρ : ∃ u v b' val', sameBitPair ρ u v b' val' ∧ Disjoint (pairHoles u v b' val') ow :=
            ⟨u, v, b', val', hsame_imp u v b' val' hs', hdj⟩
          rw [ite_eq_left h3ρ] at hlw6; omega
        · rw [ite_eq_right h3']
          by_cases h4' : ∃ u v b' val',
              sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' ∧ (pairHoles u v b' val' ∩ ow).card ≤ 1
          · obtain ⟨u, v, b', val', hs', hcd⟩ := h4'
            have h4ρ : ∃ u v b' val', sameBitPair ρ u v b' val' ∧ (pairHoles u v b' val' ∩ ow).card ≤ 1 :=
              ⟨u, v, b', val', hsame_imp u v b' val' hs', hcd⟩
            by_cases h3ρ : ∃ u v b' val', sameBitPair ρ u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
            · rw [ite_eq_left h3ρ] at hlw6; omega
            · rw [ite_eq_right h3ρ, ite_eq_left h4ρ] at hlw6; omega
          · rw [ite_eq_right h4']
      by_cases hc0 : hasCollision ρ0
      · have := hcoll_other6 false hc0; change b0 ρ1 ow = 6 at this; omega
      · by_cases hc1 : hasCollision ρ1
        · have := hcoll_other6 true hc1; change b0 ρ0 ow = 6 at this; omega
        · rw [b0_of_fp_le_two hc0 hfp0, b0_of_fp_le_two hc1 hfp1]
          have := leafWeight_ge_three ρ0 ow; have := leafWeight_ge_three ρ1 ow; omega
    | none =>
      -- Both bits of p are none in ρ, so neither ρ0 nor ρ1 can collide!
      have hnc0 : ¬ hasCollision ρ0 := fun hc => by
        obtain ⟨_, _, _, _, ho', _⟩ := hasCollision_grant_elim hnc hc; rw [ho] at ho'; cases ho'
      have hnc1 : ¬ hasCollision ρ1 := fun hc => by
        obtain ⟨_, _, _, _, ho', _⟩ := hasCollision_grant_elim hnc hc; rw [ho] at ho'; cases ho'
      have hfp0 : fixedPigeons ρ0 ≤ 3 := by
        rw [fixedPigeons_grant_of_both_none hv ho]; omega
      have hfp1 : fixedPigeons ρ1 ≤ 3 := by
        rw [fixedPigeons_grant_of_both_none hv ho]; omega
      -- Helper: if ρ_s hasDoubleOneStep, then ρ_(!s) has b0 = 4 (giving 2 + 4 = 6)!
      have hdouble_other4 : ∀ (s : Bool), hasDoubleOneStep (State.grant ρ {(p, b)} s) →
          4 ≤ b0 (State.grant ρ {(p, b)} (!s)) ow := by
        intro s hd'
        obtain ⟨r, br, valr, hrb, hro, hallr⟩ := hd'
        -- Since ¬ hasDoubleOneStep ρ and no new full pigeon was created (p only got 1 bit!),
        -- the half-fixed pigeon r MUST be p itself, with br = b and valr = s!
        have hrp : r = p := by
          by_contra hne
          apply hnd
          refine ⟨r, br, valr, ?_, ?_, fun h hh => ?_⟩
          · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hrb
          · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hro
          · obtain ⟨q, hq⟩ := hallr h hh
            have hqp : q ≠ p := by
              intro e; subst e
              have := pigeonHole_bit hq (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
              cases this
            exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
        subst r
        have hbr : br = b := by
          by_contra hne
          have hne' : (p, b) ≠ (p, br) := fun e => hne (congrArg Prod.snd e).symm
          rw [grant_apply_ne ρ hne'] at hrb
          have : br = otherBit b := (otherBit_facts b).2.2 br |>.resolve_left hne
          rw [this, ho] at hrb; cases hrb
        subst br
        have hvalr : valr = s := Option.some.inj (hrb.symm.trans (grant_apply_self ρ (p, b) s))
        subst valr
        -- So ρ already has 2 distinct full pigeons q0, q1 at the 2 holes with bit b = s!
        obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits b s false
        obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits b s true
        obtain ⟨q0, hq0'⟩ := hallr h0 hb0
        obtain ⟨q1, hq1'⟩ := hallr h1 hb1
        have hq0p : q0 ≠ p := by
          intro e; subst e
          have := pigeonHole_bit hq0' (otherBit b)
          rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
          cases this
        have hq1p : q1 ≠ p := by
          intro e; subst e
          have := pigeonHole_bit hq1' (otherBit b)
          rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
          cases this
        have hq0 : pigeonHole ρ q0 h0 := (pigeonHole_grant_ne hq0p).mp hq0'
        have hq1 : pigeonHole ρ q1 h1 := (pigeonHole_grant_ne hq1p).mp hq1'
        have hne_h : h0 ≠ h1 := fun e => by rw [e, ho1] at ho0; cases ho0
        have hq01 : q0 ≠ q1 := fun e => hne_h (pigeonHole_unique (e ▸ hq0) hq1)
        -- Every fixed pigeon in ρ is q0 or q1!
        have honly_ρ : ∀ x, pigeonFixed ρ x → x = q0 ∨ x = q1 := by
          intro x hx
          have hsub : ({q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rcases hy with rfl | rfl
            · exact pigeonFixed_of_hole hq0
            · exact pigeonFixed_of_hole hq1
          have heq : ({q0, q1} : Finset (Fin 5)) = Finset.univ.filter (pigeonFixed ρ) :=
            Finset.eq_of_subset_of_card_le hsub (by simp [hq01]; exact hfp2)
          have hm : x ∈ ({q0, q1} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
          simpa using hm
        -- Now examine ρ' = grant ρ {(p, b)} (!s)!
        let ρ' := State.grant ρ {(p, b)} (!s)
        have hnc' : ¬ hasCollision ρ' := by cases s <;> assumption
        have hfp' : fixedPigeons ρ' = 3 := by
          have hfp_eq2 : fixedPigeons ρ = 2 := by
            have hsub : ({q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hy with rfl | rfl
              · exact pigeonFixed_of_hole hq0
              · exact pigeonFixed_of_hole hq1
            have := Finset.card_le_card hsub; simp [hq01] at this; change 2 ≤ fixedPigeons ρ at this; omega
          rw [fixedPigeons_grant_of_both_none hv ho]; omega
        -- ρ' does NOT have hasDoubleOneStep (its only half-fixed pigeon is p with bit b = !s,
        -- while q0 and q1 both have bit b = s!).
        have hnd' : ¬ hasDoubleOneStep ρ' := by
          rintro ⟨x, bx, valx, hxb, hxo, hallx⟩
          have hxp : x = p := by
            by_contra hne
            have hxf : pigeonFixed ρ x := by
              have e : ρ' (x, bx) = ρ (x, bx) :=
                grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm) (!s)
              exact pigeonFixed_of_some (e ▸ hxb)
            rcases honly_ρ x hxf with rfl | rfl
            · have := pigeonHole_bit hq0 (otherBit bx)
              dsimp only [ρ'] at hxo
              rw [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hxo
              rw [this] at hxo; cases hxo
            · have := pigeonHole_bit hq1 (otherBit bx)
              dsimp only [ρ'] at hxo
              rw [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hxo
              rw [this] at hxo; cases hxo
          subst x
          have hbx : bx = b := by
            by_contra hne
            have : bx = otherBit b := (otherBit_facts b).2.2 bx |>.resolve_left hne
            dsimp only [ρ'] at hxb
            rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hxb
            cases hxb
          subst bx
          have hvx : valx = !s := Option.some.inj (hxb.symm.trans (grant_apply_self ρ (p, b) (!s)))
          subst valx
          obtain ⟨h2, hb2, _⟩ := exists_hole_of_bits b (!s) false
          obtain ⟨q2, hq2⟩ := hallx h2 hb2
          have hq2p : q2 ≠ p := by
            intro e; subst q2
            have := pigeonHole_bit hq2 (otherBit b)
            dsimp only [ρ'] at this
            rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
            cases this
          have hq2_orig : pigeonHole ρ q2 h2 := (pigeonHole_grant_ne hq2p).mp hq2
          rcases honly_ρ q2 (pigeonFixed_of_hole hq2_orig) with rfl | rfl
          · have e := pigeonHole_unique hq2_orig hq0
            rw [e, hb0] at hb2; cases s <;> simp at hb2
          · have e := pigeonHole_unique hq2_orig hq1
            rw [e, hb1] at hb2; cases s <;> simp at hb2
        -- Any sameBitPair in ρ' cannot involve p (p only has bit b = !s, while q0, q1 have bit b = s!),
        -- so it is already in ρ, hence leafWeight ρ' ow = 6!
        have hsame_imp : ∀ u v b' val', sameBitPair ρ' u v b' val' → sameBitPair ρ u v b' val' := by
          intro u v b' val' ⟨huv, hu', hv'⟩
          have not_p : ∀ x, ρ' (x, b') = some val' → x = p → ∀ y, y ≠ p → ρ' (y, b') = some val' → False := by
            intro x hx hxp y hyp hy
            subst x
            have hb' : b' = b := by
              by_contra hne
              have : b' = otherBit b := (otherBit_facts b).2.2 b' |>.resolve_left hne
              dsimp only [ρ'] at hx
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hx
              cases hx
            subst b'
            have hvs : val' = !s := Option.some.inj (hx.symm.trans (grant_apply_self ρ (p, b) (!s)))
            subst val'
            dsimp only [ρ'] at hy
            rw [grant_apply_ne ρ (fun e => hyp (congrArg Prod.fst e).symm)] at hy
            rcases honly_ρ y (pigeonFixed_of_some hy) with rfl | rfl
            · have := pigeonHole_bit hq0 b; rw [hb0] at this; rw [this] at hy
              have e := Option.some.inj hy; cases s <;> simp at e
            · have := pigeonHole_bit hq1 b; rw [hb1] at this; rw [this] at hy
              have e := Option.some.inj hy; cases s <;> simp at e
          have hup : u ≠ p := fun e => not_p u hu' e v (e ▸ huv.ne') hv'
          have hvp : v ≠ p := fun e => not_p v hv' e u (e ▸ huv.ne) hu'
          dsimp only [ρ'] at hu' hv'
          refine ⟨huv, ?_, ?_⟩
          · rwa [grant_apply_ne ρ (fun e => hup (congrArg Prod.fst e).symm)] at hu'
          · rwa [grant_apply_ne ρ (fun e => hvp (congrArg Prod.fst e).symm)] at hv'
        have hlw' : leafWeight ρ' ow = 6 := by
          unfold leafWeight at hlw6 ⊢
          by_cases h3' : ∃ u v b' val',
              sameBitPair ρ' u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
          · obtain ⟨u, v, b', val', hs', hdj⟩ := h3'
            rw [ite_eq_left ⟨u, v, b', val', hsame_imp u v b' val' hs', hdj⟩] at hlw6; omega
          · rw [ite_eq_right h3']
            by_cases h4' : ∃ u v b' val',
                sameBitPair ρ' u v b' val' ∧ (pairHoles u v b' val' ∩ ow).card ≤ 1
            · obtain ⟨u, v, b', val', hs', hcd⟩ := h4'
              by_cases h3ρ : ∃ u v b' val', sameBitPair ρ u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
              · rw [ite_eq_left h3ρ] at hlw6; omega
              · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, v, b', val', hsame_imp u v b' val' hs', hcd⟩] at hlw6; omega
            · rw [ite_eq_right h4']
        change 4 ≤ b0 ρ' ow
        unfold b0
        rw [ite_eq_right hnc', ite_eq_right hnd', ite_eq_right (by omega), ite_eq_left hfp', hlw']
        omega
      by_cases hd0 : hasDoubleOneStep ρ0
      · have := hdouble_other4 false hd0; change 4 ≤ b0 ρ1 ow at this
        have h20 : 2 ≤ b0 ρ0 ow := by unfold b0; rw [ite_eq_right hnc0, ite_eq_left hd0]
        omega
      · by_cases hd1 : hasDoubleOneStep ρ1
        · have := hdouble_other4 true hd1; change 4 ≤ b0 ρ0 ow at this
          have h21 : 2 ≤ b0 ρ1 ow := by unfold b0; rw [ite_eq_right hnc1, ite_eq_left hd1]
          omega
        · have h30 : 3 ≤ b0 ρ0 ow := by
            unfold b0; rw [ite_eq_right hnc0, ite_eq_right hd0]
            have := leafWeight_ge_three ρ0 ow; split_ifs <;> omega
          have h31 : 3 ≤ b0 ρ1 ow := by
            unfold b0; rw [ite_eq_right hnc1, ite_eq_right hd1]
            have := leafWeight_ge_three ρ1 ow; split_ifs <;> omega
          omega

/-- Auxiliary potential `b0_all4` for a pure subtree whose exit leaves ALL have weight 4
    and leafWeight ≤ 4 (used only for the k = 4, |S_r| = 4 boundary case). -/
noncomputable def b0_all4 (ρ : State) (ow : Finset Collision) : ℕ :=
  if hasCollision ρ then 1
  else if hasDoubleOneStep ρ then 2
  else if 4 ≤ fixedPigeons ρ then 3
  else if fixedPigeons ρ = 3 ∧ hasDoublePartialMatch ρ then 3
  else if leafWeight ρ ow ≤ 4 then 4
  else if fixedPigeons ρ = 3 then 5
  else 7

theorem b0_all4_ge_one (ρ : State) (ow : Finset Collision) : 1 ≤ b0_all4 ρ ow := by
  unfold b0_all4; split_ifs <;> omega

theorem b0_all4_le_four_of_lw4 {ρ : State} {ow : Finset Collision} (h : leafWeight ρ ow ≤ 4) :
    b0_all4 ρ ow ≤ 4 := by
  unfold b0_all4; split_ifs <;> omega

theorem b0_all4_split {ρ : State} {ow : Finset Collision} (hd : DistinctHoles ow) (v : Variable) :
    b0_all4 ρ ow ≤ b0_all4 (State.grant ρ {v} false) ow + b0_all4 (State.grant ρ {v} true) ow := by
  -- Note: for ρ with b0_all4 ≤ 2, trivial (1+1=2).
  -- For b0_all4 = 3: ¬ hasCollision ∧ ¬ hasDoubleOneStep ⇒ not both collide ⇒ 1+2=3!
  -- For b0_all4 = 4: ¬ hasCollision ∧ ¬ hasDoubleOneStep ∧ fp ≤ 3 ∧ ¬(fp=3 ∧ hasDoublePartialMatch)
  --   ⇒ cannot have (1, 2) or (2, 1)!
  -- For b0_all4 = 5 (fp = 3, lw = 6): cannot have (1, ≤3) or (2, 2) or (≤3, 1)!
  -- For b0_all4 = 7 (fp ≤ 2, lw = 6): split gives either (1, 7) or (2, 5) or (≥4, ≥4) or (≥3, ≥4)!
  let ρ0 := State.grant ρ {v} false
  let ρ1 := State.grant ρ {v} true
  change b0_all4 ρ ow ≤ b0_all4 ρ0 ow + b0_all4 ρ1 ow
  cases hv : ρ v with
  | some b =>
    cases b
    · rw [show ρ0 = ρ from grant_eq_self hv]; omega
    · rw [show ρ1 = ρ from grant_eq_self hv]; omega
  | none =>
    rcases v with ⟨p, b⟩
    have hge0 := b0_all4_ge_one ρ0 ow
    have hge1 := b0_all4_ge_one ρ1 ow
    by_cases hle2 : b0_all4 ρ ow ≤ 2
    · omega
    have hnc : ¬ hasCollision ρ := fun hc => by unfold b0_all4 at hle2; rw [ite_eq_left hc] at hle2; omega
    have hnd : ¬ hasDoubleOneStep ρ := fun hdb => by
      unfold b0_all4 at hle2; rw [ite_eq_right hnc, ite_eq_left hdb] at hle2; omega
    have hnot_both_coll : ¬ (hasCollision ρ0 ∧ hasCollision ρ1) := by
      rintro ⟨hc0, hc1⟩
      obtain ⟨h0, q0, _, hb0, ho0, hq0⟩ := hasCollision_grant_elim hnc hc0
      obtain ⟨h1, q1, _, hb1, ho1, hq1⟩ := hasCollision_grant_elim hnc hc1
      have hval : bits h0 (otherBit b) = bits h1 (otherBit b) := Option.some.inj (ho0.symm.trans ho1)
      apply hnd
      refine ⟨p, otherBit b, bits h0 (otherBit b), ho0, by rwa [(otherBit_facts b).2.1], ?_⟩
      intro h hh
      cases hhb : bits h b
      · exact ⟨q0, (hole_eq_of_bits h h0 b (hhb.trans hb0.symm) hh) ▸ hq0⟩
      · exact ⟨q1, (hole_eq_of_bits h h1 b (hhb.trans hb1.symm) (hh.trans hval)) ▸ hq1⟩
    by_cases h3 : b0_all4 ρ ow = 3
    · have : ¬ (b0_all4 ρ0 ow = 1 ∧ b0_all4 ρ1 ow = 1) := by
        rintro ⟨e0, e1⟩
        have c0 : hasCollision ρ0 := by unfold b0_all4 at e0; split_ifs at e0 <;> omega
        have c1 : hasCollision ρ1 := by unfold b0_all4 at e1; split_ifs at e1 <;> omega
        exact hnot_both_coll ⟨c0, c1⟩
      omega
    -- Now b0_all4 ρ ow ∈ {4, 5, 7}, so fp ≤ 3 and ¬(fp = 3 ∧ hasDoublePartialMatch ρ)!
    have hfp3 : fixedPigeons ρ ≤ 3 := by
      by_contra h4; unfold b0_all4 at hle2 h3
      rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_left (by omega)] at hle2 h3; omega
    have hndpm : ¬ (fixedPigeons ρ = 3 ∧ hasDoublePartialMatch ρ) := by
      intro h; unfold b0_all4 at hle2 h3
      rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_right (by omega), ite_eq_left h] at hle2 h3; omega
    -- Same (coll, double) impossibility as b0_split, now using hndpm instead of leafWeight ≥ 4!
    have hnot_coll_double : ∀ (s : Bool),
        hasCollision (State.grant ρ {(p, b)} s) →
        hasDoubleOneStep (State.grant ρ {(p, b)} (!s)) → False := by
      intro s hc hd'
      obtain ⟨h0, q0, hq0p, hb0, ho0, hq0⟩ := hasCollision_grant_elim hnc hc
      let h1 := flipBit h0 b
      have hp1 : pigeonHole (State.grant ρ {(p, b)} (!s)) p h1 := by
        apply pigeonHole_of_bits (b := b)
        · rw [grant_apply_self, (flipBit_facts h0 b).2.1, hb0]
        · rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm),
              (flipBit_facts h0 b).2.2.1, ho0]
      obtain ⟨r, br, valr, hrb, hro, hallr⟩ := hd'
      have hrp : r ≠ p := by
        intro e; subst e
        have := pigeonHole_bit hp1 (otherBit br); rw [hro] at this; cases this
      have hrb_orig : ρ (r, br) = some valr := by
        rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hrb
      have hro_orig : ρ (r, otherBit br) = none := by
        rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hro
      have hex_h1 : bits h1 br = valr := by
        by_contra hne
        apply hnd
        refine ⟨r, br, valr, hrb_orig, hro_orig, fun h hh => ?_⟩
        obtain ⟨q, hq⟩ := hallr h hh
        by_cases hqp : q = p
        · subst hqp; exact (hne ((pigeonHole_unique hq hp1) ▸ hh)).elim
        · exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
      let h2 := flipBit h1 (otherBit br)
      have hh2_br : bits h2 br = valr := by
        have := (flipBit_facts h1 (otherBit br)).2.2.1; rwa [(otherBit_facts br).2.1, hex_h1] at this
      obtain ⟨q2, hq2'⟩ := hallr h2 hh2_br
      have hq2p : q2 ≠ p := by
        intro e; subst e; exact (flipBit_facts h1 (otherBit br)).1 (pigeonHole_unique hq2' hp1)
      have hq2 : pigeonHole ρ q2 h2 := (pigeonHole_grant_ne hq2p).mp hq2'
      have hq2r : q2 ≠ r := by
        intro e; subst e; have := pigeonHole_bit hq2 (otherBit br); rw [hro_orig] at this; cases this
      have hq0r : q0 ≠ r := by
        intro e; subst e; have := pigeonHole_bit hq0 (otherBit br); rw [hro_orig] at this; cases this
      by_cases hq02 : q0 = q2
      · subst hq02
        have eh02 : h0 = h2 := pigeonHole_unique hq0 hq2
        have hbr_eq : br = otherBit b := by
          rcases (otherBit_facts b).2.2 br with hbr | hbr
          · exfalso
            have e1 : bits h2 b = bits h1 b := hbr ▸ (hh2_br.trans hex_h1.symm)
            rw [← eh02, (flipBit_facts h0 b).2.1] at e1
            cases bits h0 b <;> simp at e1
          · exact hbr
        subst br
        have hval_eq : valr = bits h0 (otherBit b) := by
          rw [← hex_h1, (flipBit_facts h0 b).2.2.1]
        have hsub3 : ({q0, p, r} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hx with rfl | rfl | rfl
          · exact pigeonFixed_of_hole hq0
          · exact pigeonFixed_of_some ho0
          · exact pigeonFixed_of_some hrb_orig
        have hc3 := Finset.card_le_card hsub3
        simp [hq0p, hq0r, hrp.symm] at hc3
        change 3 ≤ fixedPigeons ρ at hc3
        apply hndpm
        refine ⟨by omega, p, r, q0, otherBit b, valr, h0, hrp.symm, hval_eq.symm, hq0,
          hval_eq ▸ ho0, by rwa [(otherBit_facts b).2.1], hrb_orig, hro_orig⟩
      · have hsub4 : ({q0, q2, p, r} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl
          · exact pigeonFixed_of_hole hq0
          · exact pigeonFixed_of_hole hq2
          · exact pigeonFixed_of_some ho0
          · exact pigeonFixed_of_some hrb_orig
        have hc4 := Finset.card_le_card hsub4
        simp [hq02, hq0p, hq0r, hq2p, hq2r, hrp.symm] at hc4
        change 4 ≤ fixedPigeons ρ at hc4
        omega
    by_cases h4 : b0_all4 ρ ow = 4
    · have hnb12 : ¬ (b0_all4 ρ0 ow = 1 ∧ b0_all4 ρ1 ow ≤ 2) := by
        rintro ⟨e0, e1⟩
        have c0 : hasCollision ρ0 := by unfold b0_all4 at e0; split_ifs at e0 <;> omega
        by_cases c1 : hasCollision ρ1
        · exact hnot_both_coll ⟨c0, c1⟩
        · have d1 : hasDoubleOneStep ρ1 := by
            unfold b0_all4 at e1; rw [ite_eq_right c1] at e1; split_ifs at e1 <;> omega
          exact hnot_coll_double false c0 d1
      have hnb21 : ¬ (b0_all4 ρ0 ow ≤ 2 ∧ b0_all4 ρ1 ow = 1) := by
        rintro ⟨e0, e1⟩
        have c1 : hasCollision ρ1 := by unfold b0_all4 at e1; split_ifs at e1 <;> omega
        by_cases c0 : hasCollision ρ0
        · exact hnot_both_coll ⟨c0, c1⟩
        · have d0 : hasDoubleOneStep ρ0 := by
            unfold b0_all4 at e0; rw [ite_eq_right c0] at e0; split_ifs at e0 <;> omega
          exact hnot_coll_double true c1 d0
      omega
    -- Now b0_all4 ρ ow ∈ {5, 7}, so leafWeight ρ ow = 6 (i.e. ¬ leafWeight ≤ 4)!
    have hlw6 : leafWeight ρ ow = 6 := by
      have hgt4 : ¬ leafWeight ρ ow ≤ 4 := by
        intro h; unfold b0_all4 at hle2 h3 h4
        rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_right (by omega), ite_eq_right hndpm, ite_eq_left h] at hle2 h3 h4
        omega
      have : leafWeight ρ ow = 3 ∨ leafWeight ρ ow = 4 ∨ leafWeight ρ ow = 6 := by
        unfold leafWeight; split_ifs <;> omega
      omega
    by_cases h5 : b0_all4 ρ ow = 5
    · -- fp = 3 and lw = 6! Notice b0 ρ ow = 4!
      -- Could we get (1, 3) or (2, 2) or (3, 1)?
      -- Check: (1, 3) means ρ_s collides (so p's other bit is set, fp stays 3!) AND ρ_(!s) has fp = 3 ∧ hasDoublePartialMatch!
      -- Wait: if ρ_(!s) has hasDoublePartialMatch, the 2 half-fixed pigeons p1, p2 (with same bit b' = val') PLUS full pigeon q
      -- form 3 distinct pigeons sharing (b', val') -> by three_distinct_sameBit_leafWeight, leafWeight ρ_(!s) = 3!
      -- Wait: if ρ_s collides at q0, then p becomes full (h1), so the 2 half-fixed pigeons in ρ_(!s) are ALREADY half-fixed in ρ (neither is p!),
      -- AND their full pigeon q is either q0 (so already hasDoublePartialMatch in ρ -> contradicts hndpm!) OR p itself!
      -- If q = p (at h1): p, p1, p2 are 3 distinct pigeons in ρ ALL having bit b' = val' (since p only changed bit b -> if b' = otherBit b, already in ρ -> leafWeight ρ = 3, contradiction!;
      -- if b' = b, then h1 has bit b = !s, while p1, p2 have bit b = !s, wait: p had bit b = none and q0 had bit b = s, so {q0, p, p1, p2} are 4 fixed pigeons in ρ -> contradicts fp = 3!!)!
      have hnot_coll_dpm : ∀ (s : Bool),
          hasCollision (State.grant ρ {(p, b)} s) →
          hasDoublePartialMatch (State.grant ρ {(p, b)} (!s)) → False := by
        intro s hc hdpm
        obtain ⟨h0, q0, hq0p, hb0, ho0, hq0⟩ := hasCollision_grant_elim hnc hc
        let h1 := flipBit h0 b
        have hp1 : pigeonHole (State.grant ρ {(p, b)} (!s)) p h1 := by
          apply pigeonHole_of_bits (b := b)
          · rw [grant_apply_self, (flipBit_facts h0 b).2.1, hb0]
          · rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm),
                (flipBit_facts h0 b).2.2.1, ho0]
        obtain ⟨p1, p2, q, br, valr, hq, h12, hhb, hqh, hp1b, hp1o, hp2b, hp2o⟩ := hdpm
        have hp1p : p1 ≠ p := fun e => by
          subst e; have := pigeonHole_bit hp1 (otherBit br); rw [hp1o] at this; cases this
        have hp2p : p2 ≠ p := fun e => by
          subst e; have := pigeonHole_bit hp1 (otherBit br); rw [hp2o] at this; cases this
        have hp1b' : ρ (p1, br) = some valr := by
          rwa [grant_apply_ne ρ (fun e => hp1p (congrArg Prod.fst e).symm)] at hp1b
        have hp1o' : ρ (p1, otherBit br) = none := by
          rwa [grant_apply_ne ρ (fun e => hp1p (congrArg Prod.fst e).symm)] at hp1o
        have hp2b' : ρ (p2, br) = some valr := by
          rwa [grant_apply_ne ρ (fun e => hp2p (congrArg Prod.fst e).symm)] at hp2b
        have hp2o' : ρ (p2, otherBit br) = none := by
          rwa [grant_apply_ne ρ (fun e => hp2p (congrArg Prod.fst e).symm)] at hp2o
        -- Now q0, p, p1, p2 are fixed in ρ!
        have hq0p1 : q0 ≠ p1 := fun e => by
          subst e; have := pigeonHole_bit hq0 (otherBit br); rw [hp1o'] at this; cases this
        have hq0p2 : q0 ≠ p2 := fun e => by
          subst e; have := pigeonHole_bit hq0 (otherBit br); rw [hp2o'] at this; cases this
        have hsub4 : ({q0, p, p1, p2} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl
          · exact pigeonFixed_of_hole hq0
          · exact pigeonFixed_of_some ho0
          · exact pigeonFixed_of_some hp1b'
          · exact pigeonFixed_of_some hp2b'
        have hc4 := Finset.card_le_card hsub4
        simp [hq0p, hq0p1, hq0p2, hp1p.symm, hp2p.symm, h12] at hc4
        change 4 ≤ fixedPigeons ρ at hc4
        omega
      -- Also cannot have BOTH ρ0 and ρ1 have hasDoubleOneStep!
      have hnot_both_double : ¬ (hasDoubleOneStep ρ0 ∧ hasDoubleOneStep ρ1) := by
        rintro ⟨hd0, hd1⟩
        -- If both have hasDoubleOneStep while ¬ hasDoubleOneStep ρ:
        -- Case A: ρ (p, otherBit b) = none -> p must be the half-fixed pigeon in BOTH ->
        --   both (b, false) holes and both (b, true) holes have full pigeons in ρ -> 4 full pigeons in ρ, contradicting hfp3!
        -- Case B: ρ (p, otherBit b) = some val' -> p becomes full at h0 (in ρ0) and h1 (in ρ1),
        --   so in ρ0 some r0 ≠ p has 2 holes {h0, h0'} with h0' full in ρ; wait: could r0 = r1?!
        --   Even simpler: p is fixed, and in ρ0 there is a full pigeon q0 ≠ p and half-fixed r0 ≠ p;
        --   since fp = 3, {p, q0, r0} are ALL 3 fixed pigeons in ρ!
        --   Then in ρ1, the half-fixed pigeon MUST ALSO be r0 and the existing full pigeon MUST ALSO be q0!
        --   So r0's 2 holes are BOTH {h0, h_q0} AND {h1, h_q0} -> h0 = h1, impossible!
        cases ho : ρ (p, otherBit b) with
        | none =>
          have extract : ∀ s, hasDoubleOneStep (State.grant ρ {(p, b)} s) →
              ∀ h : Fin 4, bits h b = s → ∃ q : Fin 5, pigeonHole ρ q h := by
            intro s ⟨r, br, valr, hrb, hro, hallr⟩
            have hrp : r = p := by
              by_contra hne
              apply hnd
              refine ⟨r, br, valr, ?_, ?_, fun h hh => ?_⟩
              · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hrb
              · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hro
              · obtain ⟨q, hq⟩ := hallr h hh
                have hqp : q ≠ p := fun e => by
                  subst e; have := pigeonHole_bit hq (otherBit b)
                  rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
                  cases this
                exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
            subst r
            have hbr : br = b := by
              by_contra hne
              have : br = otherBit b := (otherBit_facts b).2.2 br |>.resolve_left hne
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hrb
              cases hrb
            subst br
            have hvs : valr = s := Option.some.inj (hrb.symm.trans (grant_apply_self ρ (p, b) s))
            subst valr
            intro h hh
            obtain ⟨q, hq⟩ := hallr h hh
            have hqp : q ≠ p := fun e => by
              subst q; have := pigeonHole_bit hq (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this
              cases this
            exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
          obtain ⟨q0, hq0⟩ := extract false hd0 0 (by fin_cases b <;> rfl)
          obtain ⟨q1, hq1⟩ := extract false hd0 (flipBit 0 (otherBit b)) (by
            have := (flipBit_facts 0 (otherBit b)).2.2.1; rw [(otherBit_facts b).2.1] at this; rw [this]; fin_cases b <;> rfl)
          obtain ⟨q2, hq2⟩ := extract true hd1 (flipBit 0 b) (by
            rw [(flipBit_facts 0 b).2.1]; fin_cases b <;> rfl)
          obtain ⟨q3, hq3⟩ := extract true hd1 (flipBit (flipBit 0 b) (otherBit b)) (by
            have := (flipBit_facts (flipBit 0 b) (otherBit b)).2.2.1; rw [(otherBit_facts b).2.1] at this
            rw [this, (flipBit_facts 0 b).2.1]; fin_cases b <;> rfl)
          have hdist : ∀ x y : Fin 4, ∀ px py : Fin 5, x ≠ y → pigeonHole ρ px x → pigeonHole ρ py y → px ≠ py :=
            fun _ _ _ _ hne hx hy e => hne (pigeonHole_unique (e ▸ hx) hy)
          have hd01 : (0 : Fin 4) ≠ flipBit 0 (otherBit b) := (flipBit_facts 0 (otherBit b)).1.symm
          have hd02 : (0 : Fin 4) ≠ flipBit 0 b := (flipBit_facts 0 b).1.symm
          have hd03 : (0 : Fin 4) ≠ flipBit (flipBit 0 b) (otherBit b) := by fin_cases b <;> decide
          have hd12 : flipBit 0 (otherBit b) ≠ flipBit 0 b := by fin_cases b <;> decide
          have hd13 : flipBit 0 (otherBit b) ≠ flipBit (flipBit 0 b) (otherBit b) := by fin_cases b <;> decide
          have hd23 : flipBit 0 b ≠ flipBit (flipBit 0 b) (otherBit b) := (flipBit_facts (flipBit 0 b) (otherBit b)).1.symm
          have hsub4 : ({q0, q1, q2, q3} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rcases hx with rfl | rfl | rfl | rfl
            · exact pigeonFixed_of_hole hq0
            · exact pigeonFixed_of_hole hq1
            · exact pigeonFixed_of_hole hq2
            · exact pigeonFixed_of_hole hq3
          have hc4 := Finset.card_le_card hsub4
          simp [hdist _ _ _ _ hd01 hq0 hq1, hdist _ _ _ _ hd02 hq0 hq2, hdist _ _ _ _ hd03 hq0 hq3,
                hdist _ _ _ _ hd12 hq1 hq2, hdist _ _ _ _ hd13 hq1 hq3, hdist _ _ _ _ hd23 hq2 hq3] at hc4
          change 4 ≤ fixedPigeons ρ at hc4
          omega
        | some val' =>
          obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits b false val'
          obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits b true val'
          have hne01 : h0 ≠ h1 := fun e => by rw [e, hb1] at hb0; cases hb0
          have extract2 : ∀ (s : Bool) (hs : Fin 4), bits hs b = s → bits hs (otherBit b) = val' →
              hasDoubleOneStep (State.grant ρ {(p, b)} s) →
              ∃ r q : Fin 5, ∃ br : Fin 2, r ≠ p ∧ q ≠ p ∧ q ≠ r ∧
                ρ (r, br) = some (bits hs br) ∧ ρ (r, otherBit br) = none ∧
                pigeonHole ρ q (flipBit hs (otherBit br)) := by
            intro s hs hsb hso ⟨r, br, valr, hrb, hro, hallr⟩
            have hps : pigeonHole (State.grant ρ {(p, b)} s) p hs :=
              pigeonHole_of_bits (b := b) (by rw [grant_apply_self, hsb])
                (by rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho, hso])
            have hrp : r ≠ p := fun e => by
              subst e; have := pigeonHole_bit hps (otherBit br); rw [hro] at this; cases this
            have hrb' : ρ (r, br) = some valr := by
              rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hrb
            have hro' : ρ (r, otherBit br) = none := by
              rwa [grant_apply_ne ρ (fun e => hrp (congrArg Prod.fst e).symm)] at hro
            have hhsb : bits hs br = valr := by
              by_contra hne
              apply hnd
              refine ⟨r, br, valr, hrb', hro', fun h hh => ?_⟩
              obtain ⟨q, hq⟩ := hallr h hh
              by_cases hqp : q = p
              · subst hqp; exact (hne ((pigeonHole_unique hq hps) ▸ hh)).elim
              · exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
            let h2 := flipBit hs (otherBit br)
            have hh2 : bits h2 br = valr := by
              have := (flipBit_facts hs (otherBit br)).2.2.1; rwa [(otherBit_facts br).2.1, hhsb] at this
            obtain ⟨q, hq'⟩ := hallr h2 hh2
            have hqp : q ≠ p := fun e => by
              subst q; exact (flipBit_facts hs (otherBit br)).1 (pigeonHole_unique hq' hps)
            have hq : pigeonHole ρ q h2 := (pigeonHole_grant_ne hqp).mp hq'
            have hqr : q ≠ r := fun e => by
              subst q; have := pigeonHole_bit hq (otherBit br); rw [hro'] at this; cases this
            exact ⟨r, q, br, hrp, hqp, hqr, hhsb ▸ hrb', hro', hq⟩
          obtain ⟨r0, q0, br0, hr0p, hq0p, hq0r0, hr0b, hr0o, hq0⟩ := extract2 false h0 hb0 ho0 hd0
          obtain ⟨r1, q1, br1, hr1p, hq1p, hq1r1, hr1b, hr1o, hq1⟩ := extract2 true h1 hb1 ho1 hd1
          -- {p, r0, q0} are 3 distinct fixed pigeons in ρ, so they are ALL fixed pigeons in ρ!
          have honly : ∀ x, pigeonFixed ρ x → x = p ∨ x = r0 ∨ x = q0 := by
            intro x hx
            have hsub : ({p, r0, q0} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hy with rfl | rfl | rfl
              · exact pigeonFixed_of_some ho
              · exact pigeonFixed_of_some hr0b
              · exact pigeonFixed_of_hole hq0
            have heq : ({p, r0, q0} : Finset (Fin 5)) = Finset.univ.filter (pigeonFixed ρ) :=
              Finset.eq_of_subset_of_card_le hsub (by simp [hr0p.symm, hq0p.symm, hq0r0.symm]; exact hfp3)
            have hm : x ∈ ({p, r0, q0} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            simpa using hm
          have hr1_eq : r1 = r0 := by
            rcases honly r1 (pigeonFixed_of_some hr1b) with h | h | h
            · exact (hr1p h).elim
            · exact h
            · subst r1; have := pigeonHole_bit hq0 (otherBit br1); rw [hr1o] at this; cases this
          have hq1_eq : q1 = q0 := by
            rcases honly q1 (pigeonFixed_of_hole hq1) with h | h | h
            · exact (hq1p h).elim
            · subst q1; have := pigeonHole_bit hq1 (otherBit br0); rw [hr0o] at this; cases this
            · exact h
          subst r1; subst q1
          have hbr_eq : br1 = br0 := by
            rcases (otherBit_facts br0).2.2 br1 with e | e
            · exact e
            · rw [e, (otherBit_facts br0).2.1] at hr1o; rw [hr1o] at hr0b; cases hr0b
          subst br1
          have heq_f : flipBit h0 (otherBit br0) = flipBit h1 (otherBit br0) := pigeonHole_unique hq0 hq1
          have heq01 : h0 = h1 := by
            have := congrArg (fun x => flipBit x (otherBit br0)) heq_f
            rwa [(flipBit_facts h0 (otherBit br0)).2.2.2, (flipBit_facts h1 (otherBit br0)).2.2.2] at this
          exact hne01 heq01
      -- Now for b0_all4 ρ ow = 5, finish by checking (1, ≤3), (≤3, 1), (2, 2)!
      have hnb13 : ∀ (s : Bool), b0_all4 (State.grant ρ {(p, b)} s) ow = 1 →
          4 ≤ b0_all4 (State.grant ρ {(p, b)} (!s)) ow := by
        intro s e1
        have hc : hasCollision (State.grant ρ {(p, b)} s) := by
          unfold b0_all4 at e1; split_ifs at e1 <;> omega
        have hnc' : ¬ hasCollision (State.grant ρ {(p, b)} (!s)) := fun hc' => by
          cases s <;> exact hnot_both_coll (by first | exact ⟨hc, hc'⟩ | exact ⟨hc', hc⟩)
        have hnd' : ¬ hasDoubleOneStep (State.grant ρ {(p, b)} (!s)) := hnot_coll_double s hc
        have hdpm' : ¬ hasDoublePartialMatch (State.grant ρ {(p, b)} (!s)) := hnot_coll_dpm s hc
        obtain ⟨_, _, _, _, ho0, _⟩ := hasCollision_grant_elim hnc hc
        have hfp' : fixedPigeons (State.grant ρ {(p, b)} (!s)) ≤ 3 := by
          rw [fixedPigeons_grant_of_other_some (by simp [ho0])]; exact hfp3
        unfold b0_all4
        rw [ite_eq_right hnc', ite_eq_right hnd', ite_eq_right (by omega), ite_eq_right (fun h => hdpm' h.2)]
        split_ifs <;> omega
      by_cases e0 : b0_all4 ρ0 ow = 1
      · have := hnb13 false e0; change 4 ≤ b0_all4 ρ1 ow at this; omega
      · by_cases e1 : b0_all4 ρ1 ow = 1
        · have := hnb13 true e1; change 4 ≤ b0_all4 ρ0 ow at this; omega
        · by_cases d0 : hasDoubleOneStep ρ0
          · have hnd1 : ¬ hasDoubleOneStep ρ1 := fun d1 => hnot_both_double ⟨d0, d1⟩
            have hnc1 : ¬ hasCollision ρ1 := fun c1 => by unfold b0_all4 at e1; rw [ite_eq_left c1] at e1; omega
            have h31 : 3 ≤ b0_all4 ρ1 ow := by
              unfold b0_all4; rw [ite_eq_right hnc1, ite_eq_right hnd1]; split_ifs <;> omega
            omega
          · have hnc0 : ¬ hasCollision ρ0 := fun c0 => by unfold b0_all4 at e0; rw [ite_eq_left c0] at e0; omega
            have h30 : 3 ≤ b0_all4 ρ0 ow := by
              unfold b0_all4; rw [ite_eq_right hnc0, ite_eq_right d0]; split_ifs <;> omega
            omega
    -- Final case: b0_all4 ρ ow = 7 (so fp ≤ 2 and lw = 6)!
    have h7 : b0_all4 ρ ow = 7 := by
      unfold b0_all4 at hle2 h3 h4 h5 ⊢
      rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_right (by omega), ite_eq_right hndpm,
          ite_eq_right (by omega)] at hle2 h3 h4 h5 ⊢
      split_ifs at hle2 h3 h4 h5 ⊢ <;> omega
    have hfp2 : fixedPigeons ρ ≤ 2 := by
      by_contra h3'; unfold b0_all4 at h7
      rw [ite_eq_right hnc, ite_eq_right hnd, ite_eq_right (by omega), ite_eq_right hndpm,
          ite_eq_right (by omega), ite_eq_left (by omega)] at h7; omega
    -- Reuse the exact same two cases (p's other bit some vs none) as in b0_split!
    cases ho : ρ (p, otherBit b) with
    | some val' =>
      have hfp0 : fixedPigeons ρ0 ≤ 2 := by
        rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
      have hfp1 : fixedPigeons ρ1 ≤ 2 := by
        rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
      have hnd_fp2 : ∀ ρ', fixedPigeons ρ' ≤ 2 → ¬ hasDoubleOneStep ρ' := fun ρ' hfp' hdb' => by
        obtain ⟨x, bx, valx, hxb, hxo, hallx⟩ := hdb'
        obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits bx valx false
        obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits bx valx true
        obtain ⟨q0, hq0⟩ := hallx h0 hb0
        obtain ⟨q1, hq1⟩ := hallx h1 hb1
        have hne : h0 ≠ h1 := fun e => by rw [e, ho1] at ho0; cases ho0
        have hq01 : q0 ≠ q1 := fun e => hne (pigeonHole_unique (e ▸ hq0) hq1)
        have hxq0 : x ≠ q0 := fun e => by have := pigeonHole_bit (e ▸ hq0) (otherBit bx); rw [hxo] at this; cases this
        have hxq1 : x ≠ q1 := fun e => by have := pigeonHole_bit (e ▸ hq1) (otherBit bx); rw [hxo] at this; cases this
        have hsub : ({x, q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ') := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hy with rfl | rfl | rfl
          · exact pigeonFixed_of_some hxb
          · exact pigeonFixed_of_hole hq0
          · exact pigeonFixed_of_hole hq1
        have hc := Finset.card_le_card hsub; simp [hxq0, hxq1, hq01] at hc
        change 3 ≤ fixedPigeons ρ' at hc; omega
      have hcoll_other7 : ∀ (s : Bool), hasCollision (State.grant ρ {(p, b)} s) →
          b0_all4 (State.grant ρ {(p, b)} (!s)) ow = 7 := by
        intro s hc
        let ρ' := State.grant ρ {(p, b)} (!s)
        have hnc' : ¬ hasCollision ρ' := fun hc' => by
          cases s <;> exact hnot_both_coll (by first | exact ⟨hc, hc'⟩ | exact ⟨hc', hc⟩)
        have hfp' : fixedPigeons ρ' ≤ 2 := by
          rw [fixedPigeons_grant_of_other_some (by simp [ho])]; exact hfp2
        have hnd' := hnd_fp2 ρ' hfp'
        -- By b0_split logic, b0 ρ' ow = 6 -> leafWeight ρ' ow = 6!
        have hb0_eq6 : b0 ρ ow = 6 := by rw [b0_of_fp_le_two hnc hfp2, hlw6]
        have hb0_s : b0 (State.grant ρ {(p, b)} s) ow = 1 := b0_of_hasCollision hc
        have hb0_sp := b0_split (ρ := ρ) hd (p, b)
        have hb0_ge5 : 5 ≤ b0 ρ' ow := by cases s <;> dsimp only [ρ'] <;> simp only [Bool.not_false, Bool.not_true] at * <;> omega
        rw [b0_of_fp_le_two hnc' hfp'] at hb0_ge5
        have hlw' : leafWeight ρ' ow = 6 := by
          have : leafWeight ρ' ow = 3 ∨ leafWeight ρ' ow = 4 ∨ leafWeight ρ' ow = 6 := by
            unfold leafWeight; split_ifs <;> omega
          omega
        change b0_all4 ρ' ow = 7
        unfold b0_all4
        rw [ite_eq_right hnc', ite_eq_right hnd', ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      by_cases hc0 : hasCollision ρ0
      · have := hcoll_other7 false hc0; change b0_all4 ρ1 ow = 7 at this; omega
      · by_cases hc1 : hasCollision ρ1
        · have := hcoll_other7 true hc1; change b0_all4 ρ0 ow = 7 at this; omega
        · have h40 : 4 ≤ b0_all4 ρ0 ow := by
            unfold b0_all4
            rw [ite_eq_right hc0, ite_eq_right (hnd_fp2 ρ0 hfp0), ite_eq_right (by omega), ite_eq_right (by omega)]
            split_ifs <;> omega
          have h41 : 4 ≤ b0_all4 ρ1 ow := by
            unfold b0_all4
            rw [ite_eq_right hc1, ite_eq_right (hnd_fp2 ρ1 hfp1), ite_eq_right (by omega), ite_eq_right (by omega)]
            split_ifs <;> omega
          omega
    | none =>
      have hnc0 : ¬ hasCollision ρ0 := fun hc => by
        obtain ⟨_, _, _, _, ho', _⟩ := hasCollision_grant_elim hnc hc; rw [ho] at ho'; cases ho'
      have hnc1 : ¬ hasCollision ρ1 := fun hc => by
        obtain ⟨_, _, _, _, ho', _⟩ := hasCollision_grant_elim hnc hc; rw [ho] at ho'; cases ho'
      have hfp0 : fixedPigeons ρ0 ≤ 3 := by rw [fixedPigeons_grant_of_both_none hv ho]; omega
      have hfp1 : fixedPigeons ρ1 ≤ 3 := by rw [fixedPigeons_grant_of_both_none hv ho]; omega
      -- Neither ρ0 nor ρ1 can have hasDoublePartialMatch (Wait: in ρ with fp ≤ 2 and lw = 6,
      -- if ρ_s has hasDoublePartialMatch, p must be one of the 2 half-fixed pigeons p1, p2;
      -- the OTHER half-fixed pigeon p2 and the full pigeon q are ALREADY in ρ, sharing (b, s) ->
      -- then (p2, q) is a sameBitPair in ρ, AND since lw = 6, BOTH holes of (b, s) on (p2, q) are in ow!
      -- AND on ρ_(!s), p has (b, !s) which disagrees with BOTH p2 and q, so ρ_(!s) has lw = 6 and ¬ hasDoublePartialMatch -> b0_all4 = 5!
      -- Wait: 3 + 5 = 8 ≥ 7!! So we ONLY need: if ρ_s has b0_all4 ≤ 3 (i.e. hasDoubleOneStep OR hasDoublePartialMatch),
      -- then ρ_(!s) has b0_all4 = 5 (giving 2 + 5 = 7)!!)!
      have hlow_other5 : ∀ (s : Bool), b0_all4 (State.grant ρ {(p, b)} s) ow ≤ 3 →
          5 ≤ b0_all4 (State.grant ρ {(p, b)} (!s)) ow := by
        intro s hle3
        have hncs : ¬ hasCollision (State.grant ρ {(p, b)} s) := by cases s <;> assumption
        have hnc' : ¬ hasCollision (State.grant ρ {(p, b)} (!s)) := by cases s <;> assumption
        have hfps : fixedPigeons (State.grant ρ {(p, b)} s) ≤ 3 := by cases s <;> assumption
        have hfp' : fixedPigeons (State.grant ρ {(p, b)} (!s)) ≤ 3 := by cases s <;> assumption
        have hcase : hasDoubleOneStep (State.grant ρ {(p, b)} s) ∨
            hasDoublePartialMatch (State.grant ρ {(p, b)} s) := by
          unfold b0_all4 at hle3
          rw [ite_eq_right hncs] at hle3
          by_cases hd' : hasDoubleOneStep (State.grant ρ {(p, b)} s)
          · exact Or.inl hd'
          · rw [ite_eq_right hd', ite_eq_right (by omega)] at hle3
            by_cases hm' : fixedPigeons (State.grant ρ {(p, b)} s) = 3 ∧
                hasDoublePartialMatch (State.grant ρ {(p, b)} s)
            · exact Or.inr hm'.2
            · rw [ite_eq_right hm'] at hle3; split_ifs at hle3 <;> omega
        have hall_s : ∀ x, pigeonFixed ρ x → ρ (x, b) = some s := by
          rcases hcase with ⟨r, br, valr, hrb, hro, hallr⟩ | ⟨p1, p2, q, br, valr, hq, h12, hhb, hqh, hp1b, hp1o, hp2b, hp2o⟩
          · have hrp : r = p := by
              by_contra hne
              apply hnd
              refine ⟨r, br, valr, ?_, ?_, fun h hh => ?_⟩
              · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hrb
              · rwa [grant_apply_ne ρ (fun e => hne (congrArg Prod.fst e).symm)] at hro
              · obtain ⟨q, hq⟩ := hallr h hh
                have hqp : q ≠ p := fun e => by
                  subst q; have := pigeonHole_bit hq (otherBit b)
                  rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
                exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
            subst r
            have hbr : br = b := by
              by_contra hne
              have : br = otherBit b := (otherBit_facts b).2.2 br |>.resolve_left hne
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hrb; cases hrb
            subst br
            have hvs : valr = s := Option.some.inj (hrb.symm.trans (grant_apply_self ρ (p, b) s))
            subst valr
            obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits b s false
            obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits b s true
            obtain ⟨q0, hq0'⟩ := hallr h0 hb0
            obtain ⟨q1, hq1'⟩ := hallr h1 hb1
            have hq0p : q0 ≠ p := fun e => by
              subst q0; have := pigeonHole_bit hq0' (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
            have hq1p : q1 ≠ p := fun e => by
              subst q1; have := pigeonHole_bit hq1' (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
            have hq0 := (pigeonHole_grant_ne hq0p).mp hq0'
            have hq1 := (pigeonHole_grant_ne hq1p).mp hq1'
            have hq01 : q0 ≠ q1 := fun e => by
              have eh := pigeonHole_unique (e ▸ hq0) hq1; rw [eh, ho1] at ho0; cases ho0
            have hsub : ({q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hy with rfl | rfl; exact pigeonFixed_of_hole hq0; exact pigeonFixed_of_hole hq1
            have heq := Finset.eq_of_subset_of_card_le hsub (by simp [hq01]; exact hfp2)
            intro x hx
            have hm : x ∈ ({q0, q1} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · rw [pigeonHole_bit hq0 b, hb0]
            · rw [pigeonHole_bit hq1 b, hb1]
          · have hqp : q ≠ p := fun e => by
              subst q; have := pigeonHole_bit hqh (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
            have hq_orig : pigeonHole ρ q hq := (pigeonHole_grant_ne hqp).mp hqh
            have hqp1 : q ≠ p1 := fun e => by
              subst q; have := pigeonHole_bit hqh (otherBit br); rw [hp1o] at this; cases this
            have hqp2 : q ≠ p2 := fun e => by
              subst q; have := pigeonHole_bit hqh (otherBit br); rw [hp2o] at this; cases this
            have hp_mem : p = p1 ∨ p = p2 := by
              by_contra hne; push Not at hne
              have hsub : ({q, p1, p2} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
                intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hy with rfl | rfl | rfl
                · exact pigeonFixed_of_hole hq_orig
                · exact pigeonFixed_of_some (by rwa [grant_apply_ne ρ (fun e => hne.1 (congrArg Prod.fst e))] at hp1b)
                · exact pigeonFixed_of_some (by rwa [grant_apply_ne ρ (fun e => hne.2 (congrArg Prod.fst e))] at hp2b)
              have hc := Finset.card_le_card hsub; simp [hqp1, hqp2, h12] at hc
              change 3 ≤ fixedPigeons ρ at hc; omega
            have hbr_eq : br = b := by
              have hp_eq : State.grant ρ {(p, b)} s (p, br) = some valr := by
                rcases hp_mem with h1 | h2
                · rw [← h1] at hp1b; exact hp1b
                · rw [← h2] at hp2b; exact hp2b
              by_contra hne
              have : br = otherBit b := (otherBit_facts b).2.2 br |>.resolve_left hne
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hp_eq
              cases hp_eq
            subst br
            have hval_eq : valr = s := by
              have hp_eq : State.grant ρ {(p, b)} s (p, b) = some valr := by
                rcases hp_mem with h1 | h2
                · rw [← h1] at hp1b; exact hp1b
                · rw [← h2] at hp2b; exact hp2b
              exact Option.some.inj (hp_eq.symm.trans (grant_apply_self ρ (p, b) s))
            rw [hval_eq] at hhb hp1b hp2b
            have hex_other : ∃ p' : Fin 5, p' ≠ q ∧ ρ (p', b) = some s := by
              rcases hp_mem with h1 | h2
              · subst p1; refine ⟨p2, hqp2.symm, ?_⟩
                rwa [grant_apply_ne ρ (fun e => h12 (congrArg Prod.fst e))] at hp2b
              · subst p2; refine ⟨p1, hqp1.symm, ?_⟩
                rwa [grant_apply_ne ρ (fun e => h12.symm (congrArg Prod.fst e))] at hp1b
            obtain ⟨p', hpq', hp'b⟩ := hex_other
            have hsub : ({q, p'} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hy with rfl | rfl
              · exact pigeonFixed_of_hole hq_orig
              · exact pigeonFixed_of_some hp'b
            have heq := Finset.eq_of_subset_of_card_le hsub (by simp [hpq'.symm]; exact hfp2)
            intro x hx
            have hm : x ∈ ({q, p'} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · rw [pigeonHole_bit hq_orig b, hhb]
            · exact hp'b
        have hnd' : ¬ hasDoubleOneStep (State.grant ρ {(p, b)} (!s)) := by
          rintro ⟨x, bx, valx, hxb, hxo, hallx⟩
          by_cases hxp : x = p
          · subst x
            have hbx : bx = b := by
              by_contra hne
              have : bx = otherBit b := (otherBit_facts b).2.2 bx |>.resolve_left hne
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hxb; cases hxb
            subst bx
            have hvx : valx = !s := Option.some.inj (hxb.symm.trans (grant_apply_self ρ (p, b) (!s)))
            subst valx
            obtain ⟨h2, hb2, _⟩ := exists_hole_of_bits b (!s) false
            obtain ⟨q2, hq2⟩ := hallx h2 hb2
            have hq2p : q2 ≠ p := fun e => by
              subst q2; have := pigeonHole_bit hq2 (otherBit b)
              rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
            have hq2_orig := (pigeonHole_grant_ne hq2p).mp hq2
            have hs_q2 := hall_s q2 (pigeonFixed_of_hole hq2_orig)
            rw [pigeonHole_bit hq2_orig b, hb2] at hs_q2
            have e := Option.some.inj hs_q2; cases s <;> simp at e
          · apply hnd
            refine ⟨x, bx, valx, ?_, ?_, fun h hh => ?_⟩
            · rwa [grant_apply_ne ρ (fun e => hxp (congrArg Prod.fst e).symm)] at hxb
            · rwa [grant_apply_ne ρ (fun e => hxp (congrArg Prod.fst e).symm)] at hxo
            · obtain ⟨q, hq⟩ := hallx h hh
              have hqp : q ≠ p := fun e => by
                subst q; have := pigeonHole_bit hq (otherBit b)
                rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
              exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
        have hndpm' : ¬ hasDoublePartialMatch (State.grant ρ {(p, b)} (!s)) := by
          rintro ⟨p1, p2, q, br, valr, hq, h12, hhb, hqh, hp1b, hp1o, hp2b, hp2o⟩
          have hqp : q ≠ p := fun e => by
            subst q; have := pigeonHole_bit hqh (otherBit b)
            rw [grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at this; cases this
          have hq_orig := (pigeonHole_grant_ne hqp).mp hqh
          have hqp1 : q ≠ p1 := fun e => by subst q; have := pigeonHole_bit hqh (otherBit br); rw [hp1o] at this; cases this
          have hqp2 : q ≠ p2 := fun e => by subst q; have := pigeonHole_bit hqh (otherBit br); rw [hp2o] at this; cases this
          have hp_mem : p = p1 ∨ p = p2 := by
            by_contra hne; push Not at hne
            have hsub : ({q, p1, p2} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed ρ) := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hy with rfl | rfl | rfl
              · exact pigeonFixed_of_hole hq_orig
              · exact pigeonFixed_of_some (by rwa [grant_apply_ne ρ (fun e => hne.1 (congrArg Prod.fst e))] at hp1b)
              · exact pigeonFixed_of_some (by rwa [grant_apply_ne ρ (fun e => hne.2 (congrArg Prod.fst e))] at hp2b)
            have hc := Finset.card_le_card hsub; simp [hqp1, hqp2, h12] at hc
            change 3 ≤ fixedPigeons ρ at hc; omega
          have hp_eq : State.grant ρ {(p, b)} (!s) (p, br) = some valr := by
            rcases hp_mem with h1 | h2
            · rw [← h1] at hp1b; exact hp1b
            · rw [← h2] at hp2b; exact hp2b
          have hbr : br = b := by
            by_contra hne
            have : br = otherBit b := (otherBit_facts b).2.2 br |>.resolve_left hne
            rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hp_eq; cases hp_eq
          subst br
          have hvs : valr = !s := Option.some.inj (hp_eq.symm.trans (grant_apply_self ρ (p, b) (!s)))
          rw [hvs] at hhb
          have hs_q := hall_s q (pigeonFixed_of_hole hq_orig)
          rw [pigeonHole_bit hq_orig b, hhb] at hs_q
          have e := Option.some.inj hs_q; cases s <;> simp at e
        have hsame_imp : ∀ u v b' val', sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' → sameBitPair ρ u v b' val' := by
          intro u v b' val' ⟨huv, hu', hv'⟩
          have not_p : ∀ x, State.grant ρ {(p, b)} (!s) (x, b') = some val' → x = p →
              ∀ y, y ≠ p → State.grant ρ {(p, b)} (!s) (y, b') = some val' → False := by
            intro x hx hxp y hyp hy; subst x
            have hb' : b' = b := by
              by_contra hne
              have : b' = otherBit b := (otherBit_facts b).2.2 b' |>.resolve_left hne
              rw [this, grant_apply_ne ρ (fun e => (otherBit_facts b).1 (congrArg Prod.snd e).symm), ho] at hx; cases hx
            subst b'
            have hvs : val' = !s := Option.some.inj (hx.symm.trans (grant_apply_self ρ (p, b) (!s)))
            subst val'
            rw [grant_apply_ne ρ (fun e => hyp (congrArg Prod.fst e).symm)] at hy
            have hsy := hall_s y (pigeonFixed_of_some hy)
            rw [hy] at hsy; have e := Option.some.inj hsy; cases s <;> simp at e
          have hup : u ≠ p := fun e => not_p u hu' e v (e ▸ huv.ne') hv'
          have hvp : v ≠ p := fun e => not_p v hv' e u (e ▸ huv.ne) hu'
          refine ⟨huv, ?_, ?_⟩
          · rwa [grant_apply_ne ρ (fun e => hup (congrArg Prod.fst e).symm)] at hu'
          · rwa [grant_apply_ne ρ (fun e => hvp (congrArg Prod.fst e).symm)] at hv'
        have hlw' : leafWeight (State.grant ρ {(p, b)} (!s)) ow = 6 := by
          unfold leafWeight at hlw6 ⊢
          by_cases h3' : ∃ u v b' val',
              sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
          · obtain ⟨u, v, b', val', hs', hdj⟩ := h3'
            rw [ite_eq_left ⟨u, v, b', val', hsame_imp u v b' val' hs', hdj⟩] at hlw6; omega
          · rw [ite_eq_right h3']
            by_cases h4' : ∃ u v b' val',
                sameBitPair (State.grant ρ {(p, b)} (!s)) u v b' val' ∧ (pairHoles u v b' val' ∩ ow).card ≤ 1
            · obtain ⟨u, v, b', val', hs', hcd⟩ := h4'
              by_cases h3ρ : ∃ u v b' val', sameBitPair ρ u v b' val' ∧ Disjoint (pairHoles u v b' val') ow
              · rw [ite_eq_left h3ρ] at hlw6; omega
              · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, v, b', val', hsame_imp u v b' val' hs', hcd⟩] at hlw6; omega
            · rw [ite_eq_right h4']
        unfold b0_all4
        rw [ite_eq_right hnc', ite_eq_right hnd', ite_eq_right (by omega),
            ite_eq_right (fun h => hndpm' h.2), ite_eq_right (by omega)]
        split_ifs <;> omega
      by_cases h0 : b0_all4 ρ0 ow ≤ 3
      · have h20 : 2 ≤ b0_all4 ρ0 ow := by unfold b0_all4; rw [ite_eq_right hnc0]; split_ifs <;> omega
        have := hlow_other5 false h0; change 5 ≤ b0_all4 ρ1 ow at this; omega
      · by_cases h1 : b0_all4 ρ1 ow ≤ 3
        · have h21 : 2 ≤ b0_all4 ρ1 ow := by unfold b0_all4; rw [ite_eq_right hnc1]; split_ifs <;> omega
          have := hlow_other5 true h1; change 5 ≤ b0_all4 ρ0 ow at this; omega
        · omega

/-- The 6-line inductive scalar potential requirement `req k ρ ow`. -/
noncomputable def req (k : ℕ) (ρ : State) (ow : Finset Collision) : ℕ :=
  match k with
  | 0 => b0 ρ ow
  | 1 => if hasCollision ρ then 0
         else if 3 ≤ fixedBits ρ then b0 ρ ow
         else min 10 (2 * b0 ρ ow)
  | 2 => if 2 ≤ fixedBits ρ then 12
         else if fixedBits ρ = 1 then 18
         else 20
  | 3 => 28
  | _ => 36

theorem req_weak_step (k : ℕ) (ρ ρ' : State) (ow : Finset Collision) :
    req k ρ ow ≤ 10 + req k ρ' ow := by
  have hb := b0_le_six ρ ow
  have hb' := b0_ge_one ρ' ow
  cases k with
  | zero => simp only [req]; omega
  | succ k =>
    cases k with
    | zero => simp only [req]; split_ifs <;> omega
    | succ k =>
      cases k with
      | zero => simp only [req]; split_ifs <;> omega
      | succ k =>
        cases k with
        | zero => simp only [req]; omega
        | succ k => simp only [req]; omega

theorem fixedPigeons_le_two_of_shared {c : Collision} {cs : List Collision} {ρ : State}
    (hs : SignedShared cs ρ) (hc : c ∈ cs) : fixedPigeons ρ ≤ 2 := by
  have hsub : Finset.univ.filter (pigeonFixed ρ) ⊆ ({c.left, c.right} : Finset (Fin 5)) := by
    intro p hp
    have hpf := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hpf with h0 | h1
    · cases hv : ρ (p, 0) with
      | none => exact (h0 hv).elim
      | some val => exact (signedShared_const hs hc hv).1
    · cases hv : ρ (p, 1) with
      | none => exact (h1 hv).elim
      | some val => exact (signedShared_const hs hc hv).1
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem fixedBits_le_four_of_shared {c : Collision} {cs : List Collision} {ρ : State}
    (hs : SignedShared cs ρ) (hc : c ∈ cs) : fixedBits ρ ≤ 4 := by
  have hsub : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆
      ({(c.left, 0), (c.left, 1), (c.right, 0), (c.right, 1)} : Finset Variable) := by
    intro v hv
    cases h : ρ v with
    | none => exact ((Finset.mem_filter.mp hv).2 h).elim
    | some val =>
      have h1 := (signedShared_const hs hc h).1
      rcases v with ⟨p, b⟩
      change p = c.left ∨ p = c.right at h1
      rcases h1 with rfl | rfl <;> fin_cases b <;> simp
  exact (Finset.card_le_card hsub).trans (by
    have h1 := Finset.card_insert_le (c.left, (0 : Fin 2)) {(c.left, 1), (c.right, 0), (c.right, 1)}
    have h2 := Finset.card_insert_le (c.left, (1 : Fin 2)) {(c.right, 0), (c.right, 1)}
    have h3 := Finset.card_le_two (a := (c.right, (0 : Fin 2))) (b := (c.right, (1 : Fin 2)))
    omega)

theorem hasCollision_of_fixedBits_four {c : Collision} {cs : List Collision} {ρ : State}
    (hs : SignedShared cs ρ) (hc : c ∈ cs) (h4 : 4 ≤ fixedBits ρ) : hasCollision ρ := by
  let S : Finset Variable := {(c.left, 0), (c.left, 1), (c.right, 0), (c.right, 1)}
  have hS : S.card = 4 := by
    have hne : c.left ≠ c.right := c.ordered.ne
    simp [S, hne]
  have hsub : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ S := by
    intro v hv
    cases h : ρ v with
    | none => exact ((Finset.mem_filter.mp hv).2 h).elim
    | some val =>
      have h1 := (signedShared_const hs hc h).1
      rcases v with ⟨p, b⟩; change p = c.left ∨ p = c.right at h1
      rcases h1 with rfl | rfl <;> fin_cases b <;> simp [S]
  have heq : Finset.univ.filter (fun v : Variable => ρ v ≠ none) = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hS]; exact h4)
  have getv : ∀ p b, (p = c.left ∨ p = c.right) → ρ (p, b) = some (bits c.hole b) := by
    intro p b hp
    have hm : (p, b) ∈ Finset.univ.filter (fun v : Variable => ρ v ≠ none) := by
      rw [heq]; rcases hp with rfl | rfl <;> fin_cases b <;> simp [S]
    have hne := (Finset.mem_filter.mp hm).2
    cases hv : ρ (p, b) with
    | none => exact (hne hv).elim
    | some val => rw [(signedShared_const hs hc hv).2]
  exact ⟨c.left, c.right, c.ordered, c.hole,
    ⟨getv c.left 0 (Or.inl rfl), getv c.left 1 (Or.inl rfl)⟩,
    ⟨getv c.right 0 (Or.inr rfl), getv c.right 1 (Or.inr rfl)⟩⟩

theorem shared_single_b0_ge_four {c : Collision} {cs : List Collision} {ρ : State} {ow : Finset Collision}
    (hs : SignedShared cs ρ) (hc : c ∈ cs) (how : c ∈ ow) (hnc : ¬ hasCollision ρ) :
    4 ≤ b0 ρ ow := by
  rw [b0_of_fp_le_two hnc (fixedPigeons_le_two_of_shared hs hc)]
  unfold leafWeight
  by_cases h3 : ∃ u v b val, sameBitPair ρ u v b val ∧ Disjoint (pairHoles u v b val) ow
  · exfalso
    obtain ⟨u, v, b, val, ⟨huv, hu, hv⟩, hdj⟩ := h3
    have hcu := signedShared_const hs hc hu
    have hcv := signedShared_const hs hc hv
    have heq_u : u = c.left ∧ v = c.right := by
      rcases hcu.1 with e1 | e1 <;> rcases hcv.1 with e2 | e2
      · exact (huv.ne (e1.trans e2.symm)).elim
      · exact ⟨e1, e2⟩
      · have : c.right < c.left := e1 ▸ e2 ▸ huv
        exact (not_lt_of_gt c.ordered this).elim
      · exact (huv.ne (e1.trans e2.symm)).elim
    have hcm : c ∈ pairHoles u v b val := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq_u.1.symm, heq_u.2.symm, hcu.2.symm⟩
    exact Finset.disjoint_left.mp hdj hcm how
  · rw [ite_eq_right h3]; split_ifs <;> omega

theorem shared_pair_structure {c₁ c₂ : Collision} {cs : List Collision} {ρ : State}
    (hs : SignedShared cs ρ) (hc1 : c₁ ∈ cs) (hc2 : c₂ ∈ cs) (hne : c₁.hole ≠ c₂.hole) :
    fixedBits ρ ≤ 2 ∧
    (fixedBits ρ = 2 →
      c₁.left = c₂.left ∧ c₁.right = c₂.right ∧
      ∃ b : Fin 2, bits c₁.hole b = bits c₂.hole b ∧
        ρ (c₁.left, b) = some (bits c₁.hole b) ∧ ρ (c₁.right, b) = some (bits c₁.hole b) ∧
        ρ (c₁.left, otherBit b) = none ∧ ρ (c₁.right, otherBit b) = none) := by
  have hbit_ne : ∃ b0 : Fin 2, bits c₁.hole b0 ≠ bits c₂.hole b0 := by
    by_contra hall; push Not at hall
    exact hne (bits_injective (funext hall))
  obtain ⟨b0, hb0ne⟩ := hbit_ne
  let b1 := otherBit b0
  -- No variable with snd = b0 can be fixed in ρ!
  have hno_b0 : ∀ p : Fin 5, ρ (p, b0) = none := by
    intro p
    cases hv : ρ (p, b0) with
    | none => rfl
    | some val =>
      have e1 := (signedShared_const hs hc1 hv).2
      have e2 := (signedShared_const hs hc2 hv).2
      exact (hb0ne (e1.symm.trans e2)).elim
  have hsub : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ ({(c₁.left, b1), (c₁.right, b1)} : Finset Variable) := by
    intro v hv
    cases h : ρ v with
    | none => exact ((Finset.mem_filter.mp hv).2 h).elim
    | some val =>
      rcases v with ⟨p, b⟩
      have hb : b = b1 := (otherBit_facts b0).2.2 b |>.resolve_left (fun eb => by rw [eb, hno_b0] at h; cases h)
      subst hb
      have hp : p = c₁.left ∨ p = c₁.right := (signedShared_const hs hc1 h).1
      rcases hp with rfl | rfl <;> simp
  have hle2 : fixedBits ρ ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
  refine ⟨hle2, fun h2 => ?_⟩
  have hne_lr : (c₁.left, b1) ≠ (c₁.right, b1) := fun e => c₁.ordered.ne (congrArg Prod.fst e)
  have heq : Finset.univ.filter (fun v : Variable => ρ v ≠ none) = {(c₁.left, b1), (c₁.right, b1)} :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hne_lr]; exact h2.symm.le)
  have hl_ne : ρ (c₁.left, b1) ≠ none := by
    have : (c₁.left, b1) ∈ Finset.univ.filter (fun v : Variable => ρ v ≠ none) := by rw [heq]; simp
    exact (Finset.mem_filter.mp this).2
  have hr_ne : ρ (c₁.right, b1) ≠ none := by
    have : (c₁.right, b1) ∈ Finset.univ.filter (fun v : Variable => ρ v ≠ none) := by rw [heq]; simp
    exact (Finset.mem_filter.mp this).2
  cases hl : ρ (c₁.left, b1) with
  | none => exact (hl_ne hl).elim
  | some vl =>
    cases hr : ρ (c₁.right, b1) with
    | none => exact (hr_ne hr).elim
    | some vr =>
      have h1l := signedShared_const hs hc1 hl
      have h2l := signedShared_const hs hc2 hl
      have h1r := signedShared_const hs hc1 hr
      have h2r := signedShared_const hs hc2 hr
      have hlr_eq : c₁.left = c₂.left ∧ c₁.right = c₂.right := by
        rcases h2l.1 with e1 | e1 <;> rcases h2r.1 with e2 | e2
        · exact (c₁.ordered.ne (e1.trans e2.symm)).elim
        · exact ⟨e1, e2⟩
        · have : c₂.right < c₂.left := e1 ▸ e2 ▸ c₁.ordered
          exact (not_lt_of_gt c₂.ordered this).elim
        · exact (c₁.ordered.ne (e1.trans e2.symm)).elim
      refine ⟨hlr_eq.1, hlr_eq.2, b1, h1l.2.symm.trans h2l.2, h1l.2 ▸ hl, h1r.2 ▸ hr, ?_, ?_⟩
      · change ρ (c₁.left, otherBit (otherBit b0)) = none; rw [(otherBit_facts b0).2.1]; exact hno_b0 _
      · change ρ (c₁.right, otherBit (otherBit b0)) = none; rw [(otherBit_facts b0).2.1]; exact hno_b0 _

theorem shared_pair_b0_six {c₁ c₂ : Collision} {cs : List Collision} {ρ : State} {ow : Finset Collision}
    (hs : SignedShared cs ρ) (hc1 : c₁ ∈ cs) (hc2 : c₂ ∈ cs) (hne : c₁.hole ≠ c₂.hole)
    (how1 : c₁ ∈ ow) (how2 : c₂ ∈ ow) : b0 ρ ow = 6 := by
  have hfp := fixedPigeons_le_two_of_shared hs hc1
  have hnc : ¬ hasCollision ρ := fun ⟨u, v, huv, h, hu, hv⟩ => by
    have h1 := (signedShared_const hs hc1 hu.1).2
    have h2 := (signedShared_const hs hc1 hu.2).2
    have h3 := (signedShared_const hs hc2 hu.1).2
    have h4 := (signedShared_const hs hc2 hu.2).2
    exact hne (bits_injective (funext fun b => by fin_cases b; exact h1.symm.trans h3; exact h2.symm.trans h4))
  rw [b0_of_fp_le_two hnc hfp]
  -- Any sameBitPair in ρ must be on (c₁.left, c₁.right, b, val) with BOTH c₁, c₂ in pairHoles ∩ ow!
  have hcard2 : ∀ u v b val, sameBitPair ρ u v b val →
      2 ≤ (pairHoles u v b val ∩ ow).card := by
    intro u v b val ⟨huv, hu, hv⟩
    have h1u := signedShared_const hs hc1 hu
    have h1v := signedShared_const hs hc1 hv
    have h2u := signedShared_const hs hc2 hu
    have h2v := signedShared_const hs hc2 hv
    have heq1 : u = c₁.left ∧ v = c₁.right := by
      rcases h1u.1 with e1 | e1 <;> rcases h1v.1 with e2 | e2
      · exact (huv.ne (e1.trans e2.symm)).elim
      · exact ⟨e1, e2⟩
      · exact (not_lt_of_gt c₁.ordered (e1 ▸ e2 ▸ huv)).elim
      · exact (huv.ne (e1.trans e2.symm)).elim
    have heq2 : u = c₂.left ∧ v = c₂.right := by
      rcases h2u.1 with e1 | e1 <;> rcases h2v.1 with e2 | e2
      · exact (huv.ne (e1.trans e2.symm)).elim
      · exact ⟨e1, e2⟩
      · exact (not_lt_of_gt c₂.ordered (e1 ▸ e2 ▸ huv)).elim
      · exact (huv.ne (e1.trans e2.symm)).elim
    have hm1 : c₁ ∈ pairHoles u v b val ∩ ow :=
      Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq1.1.symm, heq1.2.symm, h1u.2.symm⟩, how1⟩
    have hm2 : c₂ ∈ pairHoles u v b val ∩ ow :=
      Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq2.1.symm, heq2.2.symm, h2u.2.symm⟩, how2⟩
    have hcne : c₁ ≠ c₂ := fun e => hne (congrArg Collision.hole e)
    have hsub : ({c₁, c₂} : Finset Collision) ⊆ pairHoles u v b val ∩ ow := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub; simp [hcne] at this; exact this
  unfold leafWeight
  by_cases h3 : ∃ u v b val, sameBitPair ρ u v b val ∧ Disjoint (pairHoles u v b val) ow
  · obtain ⟨u, v, b, val, hsp, hdj⟩ := h3
    have h2 := hcard2 u v b val hsp
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdj] at h2; simp at h2
  · rw [ite_eq_right h3]
    by_cases h4 : ∃ u v b val, sameBitPair ρ u v b val ∧ (pairHoles u v b val ∩ ow).card ≤ 1
    · obtain ⟨u, v, b, val, hsp, h1⟩ := h4
      have h2 := hcard2 u v b val hsp; omega
    · rw [ite_eq_right h4]

theorem b0_eq_six_of_no_sameBitPair {ρ : State} {ow : Finset Collision}
    (hnc : ¬ hasCollision ρ) (hfp : fixedPigeons ρ ≤ 2)
    (hno : ∀ u v b val, ¬ sameBitPair ρ u v b val) : b0 ρ ow = 6 := by
  rw [b0_of_fp_le_two hnc hfp]
  unfold leafWeight
  rw [ite_eq_right (fun ⟨u, v, b, val, h, _⟩ => hno u v b val h),
      ite_eq_right (fun ⟨u, v, b, val, h, _⟩ => hno u v b val h)]

theorem b0_eq_six_of_fixedBits_le_one {ρ : State} {ow : Finset Collision}
    (h1 : fixedBits ρ ≤ 1) : b0 ρ ow = 6 := by
  have hno : ∀ u v b val, ¬ sameBitPair ρ u v b val := by
    rintro u v b val ⟨huv, hu, hv⟩
    have hsub : ({(u, b), (v, b)} : Finset Variable) ⊆ Finset.univ.filter (fun w => ρ w ≠ none) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl <;> simp [hu, hv]
    have hne : (u, b) ≠ (v, b) := fun e => huv.ne (congrArg Prod.fst e)
    have hc := Finset.card_le_card hsub; simp [hne] at hc
    change 2 ≤ fixedBits ρ at hc; omega
  have hnc : ¬ hasCollision ρ := fun ⟨u, v, huv, h, hu, hv⟩ =>
    hno u v 0 (bits h 0) ⟨huv, hu.1, hv.1⟩
  have hfp : fixedPigeons ρ ≤ 2 := by
    have hle : fixedPigeons ρ ≤ fixedBits ρ := by
      let f : Fin 5 → Variable := fun p => if ρ (p, 0) ≠ none then (p, 0) else (p, 1)
      have hinj : Set.InjOn f (Finset.univ.filter (pigeonFixed ρ) : Set (Fin 5)) := by
        intro p _ q _ heq
        have hp : (f p).1 = p := by unfold f; split_ifs <;> rfl
        have hq : (f q).1 = q := by unfold f; split_ifs <;> rfl
        rw [← hp, ← hq, heq]
      have hsub : (Finset.univ.filter (pigeonFixed ρ)).image f ⊆ Finset.univ.filter (fun w => ρ w ≠ none) := by
        intro w hw; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        unfold f; by_cases h0 : ρ (p, 0) ≠ none
        · rw [ite_eq_left h0]; exact h0
        · rw [ite_eq_right h0]; exact (Finset.mem_filter.mp hp).2.resolve_left h0
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injOn hinj] at hc
    omega
  exact b0_eq_six_of_no_sameBitPair hnc hfp hno

theorem req_one_of_fixedBits_le_one {ρ : State} {ow : Finset Collision}
    (h1 : fixedBits ρ ≤ 1) : req 1 ρ ow = 10 := by
  have hb6 := b0_eq_six_of_fixedBits_le_one (ow := ow) h1
  have hnc : ¬ hasCollision ρ := fun hc => by rw [b0_of_hasCollision hc] at hb6; omega
  simp only [req, ite_eq_right hnc, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega), hb6]
  omega

theorem not_hasCollision_of_fixedBits_le_three {ρ : State} (h3 : fixedBits ρ ≤ 3) :
    ¬ hasCollision ρ := by
  rintro ⟨u, v, huv, h, hu, hv⟩
  let S : Finset Variable := {(u, 0), (u, 1), (v, 0), (v, 1)}
  have hsub : S ⊆ Finset.univ.filter (fun w => ρ w ≠ none) := by
    intro w hw; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hw with rfl | rfl | rfl | rfl <;> simp [hu.1, hu.2, hv.1, hv.2]
  have hcard : S.card = 4 := by simp [S, huv.ne]
  have hc := Finset.card_le_card hsub; rw [hcard] at hc
  change 4 ≤ fixedBits ρ at hc; omega

theorem req_nonsingle_step {cs₀ cs₁ : List Collision} {ρ : State} {ow : Finset Collision}
    (nd : ((cs₀ ++ cs₁).map Collision.hole).Nodup)
    (hsub_ow : ∀ c ∈ cs₀ ++ cs₁, c ∈ ow)
    (hs : SignedShared (cs₀ ++ cs₁) ρ) :
    req (cs₀ ++ cs₁).length ρ ow ≤ req cs₀.length ρ ow + req cs₁.length ρ ow := by
  have hlen : (cs₀ ++ cs₁).length = cs₀.length + cs₁.length := List.length_append
  have hle4 : (cs₀ ++ cs₁).length ≤ 4 := by
    have h := Finset.card_le_univ ((cs₀ ++ cs₁).map Collision.hole).toFinset
    rw [List.toFinset_card_of_nodup nd, List.length_map, Fintype.card_fin] at h; exact h
  by_cases hz0 : cs₀.length = 0
  · have e1 : cs₁.length = (cs₀ ++ cs₁).length := by omega
    rw [hz0, e1]; omega
  by_cases hz1 : cs₁.length = 0
  · have e0 : cs₀.length = (cs₀ ++ cs₁).length := by omega
    rw [hz1, e0]; omega
  rcases (show (cs₀ ++ cs₁).length = 2 ∨ (cs₀ ++ cs₁).length = 3 ∨ (cs₀ ++ cs₁).length = 4 by omega) with h2 | h3 | h4
  · rcases hcs0 : cs₀ with _ | ⟨c₁, r0⟩
    · simp [hcs0] at hz0
    rcases hcs1 : cs₁ with _ | ⟨c₂, r1⟩
    · simp [hcs1] at hz1
    have hr0 : r0 = [] := by
      have : r0.length = 0 := by simp [hcs0, hcs1] at h2; omega
      exact List.eq_nil_of_length_eq_zero this
    have hr1 : r1 = [] := by
      have : r1.length = 0 := by simp [hcs0, hcs1] at h2; omega
      exact List.eq_nil_of_length_eq_zero this
    subst hr0; subst hr1
    have hne : c₁.hole ≠ c₂.hole := by
      simp [hcs0, hcs1] at nd; exact nd
    have hb6 := shared_pair_b0_six hs (by simp [hcs0]) (by simp [hcs1]) hne
      (hsub_ow c₁ (by simp [hcs0])) (hsub_ow c₂ (by simp [hcs1]))
    have hfb := (shared_pair_structure hs (by simp [hcs0]) (by simp [hcs1]) hne).1
    have hnc : ¬ hasCollision ρ := fun hc => by rw [b0_of_hasCollision hc] at hb6; omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    simp only [req, ite_eq_right hnc, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega), hb6]
    split_ifs <;> omega
  · have hem := signedShared_three nd (by omega) hs
    subst hem
    have h1 := req_one_of_fixedBits_le_one (ow := ow) (by rw [fixedBits_empty]; omega)
    rw [h3]
    rcases (show (cs₀.length = 2 ∧ cs₁.length = 1) ∨ (cs₀.length = 1 ∧ cs₁.length = 2) by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
      rw [e0, e1, h1] <;> simp [req, fixedBits_empty]
  · have hem := signedShared_three nd (by omega) hs
    subst hem
    have h1 := req_one_of_fixedBits_le_one (ow := ow) (by rw [fixedBits_empty]; omega)
    rw [h4]
    rcases (show (cs₀.length = 3 ∧ cs₁.length = 1) ∨ (cs₀.length = 2 ∧ cs₁.length = 2) ∨
        (cs₀.length = 1 ∧ cs₁.length = 3) by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩
    · rw [e0, e1, h1]; simp [req]
    · rw [e0, e1]; simp [req, fixedBits_empty]
    · rw [e0, e1, h1]; simp [req]

/-- Singleton split closure of `req`: works for ALL k ∈ {0..4}, ALL states, ALL distinct-hole `ow`! -/
theorem req_single_step {cs₀ cs₁ : List Collision} {ρ : State} {ow : Finset Collision}
    (hd : DistinctHoles ow) (nd : ((cs₀ ++ cs₁).map Collision.hole).Nodup)
    (hsub_ow : ∀ c ∈ cs₀ ++ cs₁, c ∈ ow)
    (hs : SignedShared (cs₀ ++ cs₁) ρ) (v : Variable)
    (hs0 : SignedShared cs₀ (State.grant ρ {v} false))
    (hs1 : SignedShared cs₁ (State.grant ρ {v} true)) :
    req (cs₀ ++ cs₁).length ρ ow ≤
      req cs₀.length (State.grant ρ {v} false) ow + req cs₁.length (State.grant ρ {v} true) ow := by
  let ρ0 := State.grant ρ {v} false
  let ρ1 := State.grant ρ {v} true
  change req (cs₀ ++ cs₁).length ρ ow ≤ req cs₀.length ρ0 ow + req cs₁.length ρ1 ow
  have hlen : (cs₀ ++ cs₁).length = cs₀.length + cs₁.length := List.length_append
  have hnd0 : (cs₀.map Collision.hole).Nodup := by
    rw [List.map_append] at nd; exact (List.nodup_append.mp nd).1
  have hnd1 : (cs₁.map Collision.hole).Nodup := by
    rw [List.map_append] at nd; exact (List.nodup_append.mp nd).2.1
  have hle4 : (cs₀ ++ cs₁).length ≤ 4 := by
    have h := Finset.card_le_univ ((cs₀ ++ cs₁).map Collision.hole).toFinset
    rw [List.toFinset_card_of_nodup nd, List.length_map, Fintype.card_fin] at h; exact h
  cases hv : ρ v with
  | some side =>
    cases side
    · have e0 : ρ0 = ρ := grant_eq_self hv
      have h1empty : cs₁ = [] := by
        cases cs₁ with
        | nil => rfl
        | cons c rest =>
          have hf := hs v false hv c (by simp) 0
          have ht := hs1 v true (grant_apply_self ρ v true) c (by simp) 0
          rw [hf] at ht; cases ht
      have e1 : cs₀.length = (cs₀ ++ cs₁).length := by simp [h1empty]
      rw [e0, e1]; omega
    · have e1 : ρ1 = ρ := grant_eq_self hv
      have h0empty : cs₀ = [] := by
        cases cs₀ with
        | nil => rfl
        | cons c rest =>
          have ht := hs v true hv c (by simp) 0
          have hf := hs0 v false (grant_apply_self ρ v false) c (by simp) 0
          rw [ht] at hf; cases hf
      have e0 : cs₁.length = (cs₀ ++ cs₁).length := by simp [h0empty]
      rw [e1, e0]; omega
  | none =>
    have hfb0 : fixedBits ρ0 = fixedBits ρ + 1 := fixedBits_grant_none hv false
    have hfb1 : fixedBits ρ1 = fixedBits ρ + 1 := fixedBits_grant_none hv true
    by_cases hk0 : (cs₀ ++ cs₁).length = 0
    · have e0 : cs₀.length = 0 := by omega
      have e1 : cs₁.length = 0 := by omega
      rw [hk0, e0, e1]; exact b0_split hd v
    by_cases hk3 : 3 ≤ (cs₀ ++ cs₁).length
    · have hem := signedShared_three nd hk3 hs
      have hfb0' : fixedBits ρ0 = 1 := by rw [hfb0, hem, fixedBits_empty]
      have hfb1' : fixedBits ρ1 = 1 := by rw [hfb1, hem, fixedBits_empty]
      have hne0 : ρ0 ≠ State.empty := fun e => by
        have := congrArg (fun f => f v) e; simp [ρ0, grant_apply_self, State.empty] at this
      have hne1 : ρ1 ≠ State.empty := fun e => by
        have := congrArg (fun f => f v) e; simp [ρ1, grant_apply_self, State.empty] at this
      have hle20 : cs₀.length ≤ 2 := by
        by_contra h3; exact hne0 (signedShared_three hnd0 (by omega) hs0)
      have hle21 : cs₁.length ≤ 2 := by
        by_contra h3; exact hne1 (signedShared_three hnd1 (by omega) hs1)
      have hr10 := req_one_of_fixedBits_le_one (ow := ow) (by omega : fixedBits ρ0 ≤ 1)
      have hr11 := req_one_of_fixedBits_le_one (ow := ow) (by omega : fixedBits ρ1 ≤ 1)
      rcases (show (cs₀ ++ cs₁).length = 3 ∨ (cs₀ ++ cs₁).length = 4 by omega) with h3 | h4
      · rw [h3]
        rcases (show (cs₀.length = 2 ∧ cs₁.length = 1) ∨ (cs₀.length = 1 ∧ cs₁.length = 2) by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩
        · rw [e0, e1, hr11]; simp [req, hfb0']
        · rw [e0, e1, hr10]; simp [req, hfb1']
      · rw [h4]
        have e0 : cs₀.length = 2 := by omega
        have e1 : cs₁.length = 2 := by omega
        rw [e0, e1]; simp [req, hfb0', hfb1']
    -- Remaining cases: k = 1 or k = 2!
    rcases (show (cs₀ ++ cs₁).length = 1 ∨ (cs₀ ++ cs₁).length = 2 by omega) with hk1 | hk2
    · -- k = 1! WLOG by symmetry on side!
      have handle_k1 : ∀ (s : Bool) (c : Collision), c ∈ ow →
          SignedShared [c] ρ → SignedShared [c] (State.grant ρ {v} s) →
          req 1 ρ ow ≤ req 1 (State.grant ρ {v} s) ow + b0 (State.grant ρ {v} (!s)) ow := by
        intro s c hcow hsc hscs
        by_cases hcoll : hasCollision ρ
        · simp [req, hcoll]
        have hfbs : fixedBits (State.grant ρ {v} s) = fixedBits ρ + 1 := fixedBits_grant_none hv s
        have hfbo : fixedBits (State.grant ρ {v} (!s)) = fixedBits ρ + 1 := fixedBits_grant_none hv (!s)
        have hfb_le3 : fixedBits ρ ≤ 3 := by
          by_contra h4
          exact hcoll (hasCollision_of_fixedBits_four (c := c) hsc (by simp) (by omega))
        have hv_c := signedShared_const (c := c) hscs (by simp) (grant_apply_self ρ v s)
        have hfp_o : fixedPigeons (State.grant ρ {v} (!s)) ≤ 2 := by
          have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) ⊆ ({c.left, c.right} : Finset (Fin 5)) := by
            intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
            have hpf := (Finset.mem_filter.mp hp).2
            rcases hpf with h0 | h1
            · cases hw : State.grant ρ {v} (!s) (p, 0) with
              | none => exact (h0 hw).elim
              | some val =>
                by_cases he : (p, (0 : Fin 2)) = v
                · rw [← congrArg Prod.fst he] at hv_c; exact hv_c.1
                · rw [grant_apply_ne ρ (Ne.symm he)] at hw; exact (signedShared_const hsc (by simp) hw).1
            · cases hw : State.grant ρ {v} (!s) (p, 1) with
              | none => exact (h1 hw).elim
              | some val =>
                by_cases he : (p, (1 : Fin 2)) = v
                · rw [← congrArg Prod.fst he] at hv_c; exact hv_c.1
                · rw [grant_apply_ne ρ (Ne.symm he)] at hw; exact (signedShared_const hsc (by simp) hw).1
          exact (Finset.card_le_card hsub).trans Finset.card_le_two
        -- Case fixedBits ρ ≤ 1:
        by_cases hle1 : fixedBits ρ ≤ 1
        · have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
          have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} (!s)) ≤ 3)
          have hb_s := shared_single_b0_ge_four hscs (by simp) hcow hnc_s
          have hb_o : 3 ≤ b0 (State.grant ρ {v} (!s)) ow := by
            rw [b0_of_fp_le_two hnc_o hfp_o]; exact leafWeight_ge_three _ ow
          simp only [req, ite_eq_right hcoll, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega),
                     ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega)]
          omega
        -- Case fixedBits ρ = 2:
        by_cases heq2 : fixedBits ρ = 2
        · have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
          have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} (!s)) ≤ 3)
          have hb_s := shared_single_b0_ge_four hscs (by simp) hcow hnc_s
          have hb_ρ := shared_single_b0_ge_four hsc (by simp) hcow hcoll
          simp only [req, ite_eq_right hcoll, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega),
                     ite_eq_right hnc_s, ite_eq_left (show 3 ≤ fixedBits (State.grant ρ {v} s) by omega)]
          by_cases hsp : ∃ b' : Fin 2, ρ (c.left, b') = some (bits c.hole b') ∧ ρ (c.right, b') = some (bits c.hole b')
          · obtain ⟨b', hlb', hrb'⟩ := hsp
            have hne_lr : (c.left, b') ≠ (c.right, b') := fun e => c.ordered.ne (congrArg Prod.fst e)
            have hfilt : Finset.univ.filter (fun w : Variable => ρ w ≠ none) = {(c.left, b'), (c.right, b')} := by
              symm; apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hw with rfl | rfl <;> simp [hlb', hrb']
              · simp [hne_lr]; exact heq2.le
            have hvb_ne : v.2 ≠ b' := by
              intro e
              have hm : v ∈ Finset.univ.filter (fun w : Variable => ρ w ≠ none) := by
                rw [hfilt]; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hv_c.1 with h1 | h1
                · left; exact Prod.ext h1 e
                · right; exact Prod.ext h1 e
              exact (Finset.mem_filter.mp hm).2 hv
            have hsame_only : ∀ (s' : Bool) u w b'' val'', sameBitPair (State.grant ρ {v} s') u w b'' val'' →
                sameBitPair ρ u w b'' val'' := by
              intro s' u w b'' val'' ⟨huw, hu', hw'⟩
              have hb'' : b'' = b' := by
                by_contra hne
                have hu_v : (u, b'') = v := by
                  by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hu'
                  have hm : (u, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
                  rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e <;> exact hne (congrArg Prod.snd e)
                have hw_v : (w, b'') = v := by
                  by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hw'
                  have hm : (w, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
                  rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e <;> exact hne (congrArg Prod.snd e)
                exact huw.ne (congrArg Prod.fst (hu_v.trans hw_v.symm))
              subst b''
              refine ⟨huw, ?_, ?_⟩
              · rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hu'
              · rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hw'
            have hlw_ge : ∀ s', leafWeight ρ ow ≤ leafWeight (State.grant ρ {v} s') ow := by
              intro s'; unfold leafWeight
              by_cases h3' : ∃ u w b'' val'',
                  sameBitPair (State.grant ρ {v} s') u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
              · obtain ⟨u, w, b'', val'', hsp', hdj⟩ := h3'
                rw [ite_eq_left ⟨u, w, b'', val'', hsame_only s' u w b'' val'' hsp', hdj⟩,
                    ite_eq_left ⟨u, w, b'', val'', hsp', hdj⟩]
              · rw [ite_eq_right h3']
                by_cases h4' : ∃ u w b'' val'',
                    sameBitPair (State.grant ρ {v} s') u w b'' val'' ∧ (pairHoles u w b'' val'' ∩ ow).card ≤ 1
                · obtain ⟨u, w, b'', val'', hsp', hcd⟩ := h4'
                  by_cases h3ρ : ∃ u w b'' val'', sameBitPair ρ u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
                  · rw [ite_eq_left h3ρ, ite_eq_left ⟨u, w, b'', val'', hsp', hcd⟩]; omega
                  · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, w, b'', val'', hsame_only s' u w b'' val'' hsp', hcd⟩,
                        ite_eq_left ⟨u, w, b'', val'', hsp', hcd⟩]
                · rw [ite_eq_right h4']; exact leafWeight_le_six ρ ow
            rw [b0_of_fp_le_two hcoll (fixedPigeons_le_two_of_shared (c := c) hsc (by simp)),
                b0_of_fp_le_two hnc_s (fixedPigeons_le_two_of_shared (c := c) hscs (by simp)),
                b0_of_fp_le_two hnc_o hfp_o]
            have := hlw_ge s; have := hlw_ge (!s); omega
          · have hno_o : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} (!s)) u w b' val' := by
              rintro u w b' val' ⟨huw, hu', hw'⟩
              have hpair : u = c.left ∧ w = c.right := by
                have huf : u = c.left ∨ u = c.right := by
                  by_cases e : (u, b') = v
                  · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
                  · rw [grant_apply_ne ρ (Ne.symm e)] at hu'; exact (signedShared_const (c := c) hsc (by simp) hu').1
                have hwf : w = c.left ∨ w = c.right := by
                  by_cases e : (w, b') = v
                  · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
                  · rw [grant_apply_ne ρ (Ne.symm e)] at hw'; exact (signedShared_const (c := c) hsc (by simp) hw').1
                rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
                · exact (huw.ne rfl).elim
                · exact ⟨rfl, rfl⟩
                · exact (not_lt_of_gt c.ordered huw).elim
                · exact (huw.ne rfl).elim
              obtain ⟨rfl, rfl⟩ := hpair
              by_cases e1 : (c.left, b') = v
              · have e2 : (c.right, b') ≠ v := fun e => c.ordered.ne (congrArg Prod.fst (e1.trans e.symm))
                rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
                have hval2 := (signedShared_const (c := c) hsc (by simp) hw').2
                rw [e1, grant_apply_self] at hu'
                have hval1 := Option.some.inj hu'
                have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e1] at hv_c; exact hv_c.2.symm
                rw [← hval1, hvs] at hval2; cases s <;> simp at hval2
              · by_cases e2 : (c.right, b') = v
                · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
                  have hval1 := (signedShared_const (c := c) hsc (by simp) hu').2
                  rw [e2, grant_apply_self] at hw'
                  have hval2 := Option.some.inj hw'
                  have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e2] at hv_c; exact hv_c.2.symm
                  rw [← hval2, hvs] at hval1; cases s <;> simp at hval1
                · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
                  rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
                  have h1 := (signedShared_const (c := c) hsc (by simp) hu').2
                  have h2 := (signedShared_const (c := c) hsc (by simp) hw').2
                  exact hsp ⟨b', h1 ▸ hu', h2 ▸ hw'⟩
            have hbo6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
            omega
        -- Case fixedBits ρ = 3:
        have heq3 : fixedBits ρ = 3 := by omega
        have hnc_o : ¬ hasCollision (State.grant ρ {v} (!s)) := by
          rintro ⟨u, w, huw, h, hu, hw⟩
          have hpair : u = c.left ∧ w = c.right := by
            have huf : u = c.left ∨ u = c.right := by
              by_cases e : (u, (0 : Fin 2)) = v
              · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
              · have := hu.1; rw [grant_apply_ne ρ (Ne.symm e)] at this; exact (signedShared_const (c := c) hsc (by simp) this).1
            have hwf : w = c.left ∨ w = c.right := by
              by_cases e : (w, (0 : Fin 2)) = v
              · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
              · have := hw.1; rw [grant_apply_ne ρ (Ne.symm e)] at this; exact (signedShared_const (c := c) hsc (by simp) this).1
            rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
            · exact (huw.ne rfl).elim
            · exact ⟨rfl, rfl⟩
            · exact (not_lt_of_gt c.ordered huw).elim
            · exact (huw.ne rfl).elim
          obtain ⟨rfl, rfl⟩ := hpair
          rcases hv_c.1 with hvl | hvr
          · have h1 := pigeonHole_bit hu v.2; rw [show (c.left, v.2) = v from Prod.ext hvl.symm rfl, grant_apply_self] at h1
            have h2 := pigeonHole_bit hw v.2
            have hne : (c.right, v.2) ≠ v := fun e => c.ordered.ne' (hvl ▸ congrArg Prod.fst e)
            rw [grant_apply_ne ρ (Ne.symm hne)] at h2
            have e1 := Option.some.inj h1; have e2 := (signedShared_const (c := c) hsc (by simp) h2).2
            rw [← e1, ← hv_c.2] at e2; cases s <;> simp at e2
          · have h1 := pigeonHole_bit hw v.2; rw [show (c.right, v.2) = v from Prod.ext hvr.symm rfl, grant_apply_self] at h1
            have h2 := pigeonHole_bit hu v.2
            have hne : (c.left, v.2) ≠ v := fun e => c.ordered.ne (hvr ▸ congrArg Prod.fst e)
            rw [grant_apply_ne ρ (Ne.symm hne)] at h2
            have e1 := Option.some.inj h1; have e2 := (signedShared_const (c := c) hsc (by simp) h2).2
            rw [← e1, ← hv_c.2] at e2; cases s <;> simp at e2
        have hsame_imp : ∀ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' → sameBitPair ρ u w b' val' := by
          intro u w b' val' ⟨huw, hu', hw'⟩
          have hpair : u = c.left ∧ w = c.right := by
            have huf : u = c.left ∨ u = c.right := by
              by_cases e : (u, b') = v
              · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
              · rw [grant_apply_ne ρ (Ne.symm e)] at hu'; exact (signedShared_const (c := c) hsc (by simp) hu').1
            have hwf : w = c.left ∨ w = c.right := by
              by_cases e : (w, b') = v
              · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
              · rw [grant_apply_ne ρ (Ne.symm e)] at hw'; exact (signedShared_const (c := c) hsc (by simp) hw').1
            rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
            · exact (huw.ne rfl).elim
            · exact ⟨rfl, rfl⟩
            · exact (not_lt_of_gt c.ordered huw).elim
            · exact (huw.ne rfl).elim
          obtain ⟨rfl, rfl⟩ := hpair
          by_cases e1 : (c.left, b') = v
          · have e2 : (c.right, b') ≠ v := fun e => c.ordered.ne (congrArg Prod.fst (e1.trans e.symm))
            rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
            rw [e1, grant_apply_self] at hu'
            have hval1 := Option.some.inj hu'; have hval2 := (signedShared_const (c := c) hsc (by simp) hw').2
            have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e1] at hv_c; exact hv_c.2.symm
            rw [← hval1, hvs] at hval2; cases s <;> simp at hval2
          · by_cases e2 : (c.right, b') = v
            · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
              rw [e2, grant_apply_self] at hw'
              have hval2 := Option.some.inj hw'; have hval1 := (signedShared_const (c := c) hsc (by simp) hu').2
              have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e2] at hv_c; exact hv_c.2.symm
              rw [← hval2, hvs] at hval1; cases s <;> simp at hval1
            · exact ⟨huw, by rwa [grant_apply_ne ρ (Ne.symm e1)] at hu',
                          by rwa [grant_apply_ne ρ (Ne.symm e2)] at hw'⟩
        have hlw_ge : leafWeight ρ ow ≤ leafWeight (State.grant ρ {v} (!s)) ow := by
          unfold leafWeight
          by_cases h3' : ∃ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' ∧ Disjoint (pairHoles u w b' val') ow
          · obtain ⟨u, w, b', val', hsp', hdj⟩ := h3'
            rw [ite_eq_left ⟨u, w, b', val', hsame_imp u w b' val' hsp', hdj⟩,
                ite_eq_left ⟨u, w, b', val', hsp', hdj⟩]
          · rw [ite_eq_right h3']
            by_cases h4' : ∃ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' ∧ (pairHoles u w b' val' ∩ ow).card ≤ 1
            · obtain ⟨u, w, b', val', hsp', hcd⟩ := h4'
              by_cases h3ρ : ∃ u w b' val', sameBitPair ρ u w b' val' ∧ Disjoint (pairHoles u w b' val') ow
              · rw [ite_eq_left h3ρ, ite_eq_left ⟨u, w, b', val', hsp', hcd⟩]; omega
              · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, w, b', val', hsame_imp u w b' val' hsp', hcd⟩,
                    ite_eq_left ⟨u, w, b', val', hsp', hcd⟩]
            · rw [ite_eq_right h4']; exact leafWeight_le_six ρ ow
        simp only [req, ite_eq_right hcoll, ite_eq_left (by omega : 3 ≤ fixedBits ρ)]
        rw [b0_of_fp_le_two hcoll (fixedPigeons_le_two_of_shared (c := c) hsc (by simp)),
            b0_of_fp_le_two hnc_o hfp_o]
        omega
      rcases (show (cs₀.length = 1 ∧ cs₁.length = 0) ∨ (cs₀.length = 0 ∧ cs₁.length = 1) by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩
      · rcases hcs0 : cs₀ with _ | ⟨c, r0⟩; · simp [hcs0] at e0
        have hr0 : r0 = [] := by simpa [hcs0] using e0
        have hr1 : cs₁ = [] := List.eq_nil_of_length_eq_zero e1
        subst hr0; subst hr1
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact handle_k1 false c (hsub_ow c (by simp [hcs0])) (by simpa [hcs0] using hs) (by simpa [hcs0] using hs0)
      · rcases hcs1 : cs₁ with _ | ⟨c, r1⟩; · simp [hcs1] at e1
        have hr1 : r1 = [] := by simpa [hcs1] using e1
        have hr0 : cs₀ = [] := List.eq_nil_of_length_eq_zero e0
        subst hr1; subst hr0
        change req ([c].length) ρ ow ≤ b0 ρ0 ow + req ([c].length) ρ1 ow
        rw [Nat.add_comm]
        exact handle_k1 true c (hsub_ow c (by simp [hcs1])) (by simpa [hcs1] using hs) (by simpa [hcs1] using hs1)
    · -- k = 2!
      have handle_20 : ∀ (s : Bool) (c₁ c₂ : Collision), c₁.hole ≠ c₂.hole →
          SignedShared [c₁, c₂] ρ → SignedShared [c₁, c₂] (State.grant ρ {v} s) →
          req 2 ρ ow ≤ req 2 (State.grant ρ {v} s) ow + b0 (State.grant ρ {v} (!s)) ow := by
        intro s c₁ c₂ hne hs12 hss
        have hfbs : fixedBits (State.grant ρ {v} s) = fixedBits ρ + 1 := fixedBits_grant_none hv s
        have hfbo : fixedBits (State.grant ρ {v} (!s)) = fixedBits ρ + 1 := fixedBits_grant_none hv (!s)
        have hstruc := shared_pair_structure hss (by simp) (by simp) hne
        have hfb_le1 : fixedBits ρ ≤ 1 := by omega
        by_cases h0 : fixedBits ρ = 0
        · have hbo6 := b0_eq_six_of_fixedBits_le_one (ow := ow) (by omega : fixedBits (State.grant ρ {v} (!s)) ≤ 1)
          simp only [req]; split_ifs <;> omega
        · have h1 : fixedBits ρ = 1 := by omega
          obtain ⟨hl_eq, hr_eq, b', hbe, hlb', hrb', hlno, hrno⟩ := hstruc.2 (by omega)
          have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
          have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} s w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
            symm; apply Finset.eq_of_subset_of_card_le
            · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hw with rfl | rfl <;> simp [hlb', hrb']
            · simp [hne_lr]; change fixedBits (State.grant ρ {v} s) ≤ 2; omega
          have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
            rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
          have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} (!s) w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
            ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hwv : w = v
            · subst hwv; simp [grant_apply_self, hvm]
            · have e1 : State.grant ρ {v} (!s) w = ρ w := grant_apply_ne ρ (Ne.symm hwv) (!s)
              have e2 : State.grant ρ {v} s w = ρ w := grant_apply_ne ρ (Ne.symm hwv) s
              have : (State.grant ρ {v} s w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilts]; simp
              rw [e1, ← e2]; exact this
          have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} (!s)) u w b'' val'' := by
            rintro u w b'' val'' ⟨huw, hu', hw'⟩
            have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
            have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
            have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
              rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
              · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
              · exact ⟨e1, e2⟩
              · have e1' : u = c₁.right := congrArg Prod.fst e1
                have e2' : w = c₁.left := congrArg Prod.fst e2
                rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
              · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
            rw [hpair.1] at hu'; rw [hpair.2] at hw'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
            rcases hvm with rfl | rfl
            · rw [grant_apply_self] at hu'
              rw [grant_apply_ne ρ hne_lr] at hw'
              have hr_eq_s : ρ (c₁.right, b') = some (bits c₁.hole b') := by
                rwa [grant_apply_ne ρ hne_lr] at hrb'
              have hl_eq_s : bits c₁.hole b' = s := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') s))
              rw [hr_eq_s, hl_eq_s] at hw'
              have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
              rw [← e1] at e2; cases s <;> cases e2
            · rw [grant_apply_self] at hw'
              rw [grant_apply_ne ρ hne_lr.symm] at hu'
              have hl_eq_s : ρ (c₁.left, b') = some (bits c₁.hole b') := by
                rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
              have hr_eq_s : bits c₁.hole b' = s := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') s))
              rw [hl_eq_s, hr_eq_s] at hu'
              have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
              rw [← e1] at e2; cases s <;> cases e2
          have hfp_o : fixedPigeons (State.grant ρ {v} (!s)) ≤ 2 := by
            have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
              intro p hp
              have hpf := (Finset.mem_filter.mp hp).2
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases hpf with h0' | h1'
              · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                  rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                rcases hm with e | e
                · left; exact congrArg Prod.fst e
                · right; exact congrArg Prod.fst e
              · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                  rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                rcases hm with e | e
                · left; exact congrArg Prod.fst e
                · right; exact congrArg Prod.fst e
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
          have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} (!s)) ≤ 3)
          have hbo6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
          simp only [req]; split_ifs <;> omega
      rcases (show (cs₀.length = 2 ∧ cs₁.length = 0) ∨ (cs₀.length = 0 ∧ cs₁.length = 2) ∨
          (cs₀.length = 1 ∧ cs₁.length = 1) by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩
      · have hr1 : cs₁ = [] := List.eq_nil_of_length_eq_zero e1; subst hr1
        rcases hcs0 : cs₀ with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hcs0] at e0
        subst e0
        have hne : c₁.hole ≠ c₂.hole := by simp [hcs0] at nd; exact nd
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact handle_20 false c₁ c₂ hne (by simpa [hcs0] using hs) (by simpa [hcs0] using hs0)
      · have hr0 : cs₀ = [] := List.eq_nil_of_length_eq_zero e0; subst hr0
        rcases hcs1 : cs₁ with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hcs1] at e1
        subst e1
        have hne : c₁.hole ≠ c₂.hole := by simp [hcs1] at nd; exact nd
        change req ([c₁, c₂].length) ρ ow ≤ b0 ρ0 ow + req ([c₁, c₂].length) ρ1 ow
        rw [Nat.add_comm]
        exact handle_20 true c₁ c₂ hne (by simpa [hcs1] using hs) (by simpa [hcs1] using hs1)
      · -- (1, 1) split of k = 2!
        rcases hcs0 : cs₀ with _ | ⟨c₁, r0⟩; · simp [hcs0] at e0
        rcases hcs1 : cs₁ with _ | ⟨c₂, r1⟩; · simp [hcs1] at e1
        have hr0 : r0 = [] := by simpa [hcs0] using e0
        have hr1 : r1 = [] := by simpa [hcs1] using e1
        subst hr0; subst hr1
        have hne : c₁.hole ≠ c₂.hole := by simp [hcs0, hcs1] at nd; exact nd
        have hstruc := shared_pair_structure hs (by simp [hcs0]) (by simp [hcs1]) hne
        have hfb_le2 : fixedBits ρ ≤ 2 := hstruc.1
        simp only [List.length_append, List.length_cons, List.length_nil]
        by_cases h0 : fixedBits ρ = 0
        · rw [req_one_of_fixedBits_le_one (by omega : fixedBits ρ0 ≤ 1),
              req_one_of_fixedBits_le_one (by omega : fixedBits ρ1 ≤ 1)]
          simp [req, h0]
        by_cases h1 : fixedBits ρ = 1
        · have hno_side : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
              req 1 (State.grant ρ {v} s) ow = 10 := by
            intro s c hsc
            have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hv s, h1]
            have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
            have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
            have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
              intro w hw ew
              cases hww : ρ w with
              | none => exact (hw hww).elim
              | some valw =>
                have e1' := (signedShared_const (c := c₁) hs (by simp [hcs0]) hww).2
                have e2' := (signedShared_const (c := c₂) hs (by simp [hcs1]) hww).2
                have ev1 := (signedShared_const (c := c₁) hs0 (by simp [hcs0]) (grant_apply_self ρ v false)).2
                have ev2 := (signedShared_const (c := c₂) hs1 (by simp [hcs1]) (grant_apply_self ρ v true)).2
                rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
                have := e1'.symm.trans e2'; cases this
            have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
              rintro u w b' val' ⟨huw, hu', hw'⟩
              by_cases e1' : (u, b') = v
              · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
                rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
              · by_cases e2' : (w, b') = v
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                  have hsub : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hx with rfl | rfl <;> simp [hu', hw']
                  have hc := Finset.card_le_card hsub
                  simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                  change 2 ≤ fixedBits ρ at hc; omega
            have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
            simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
          rw [hno_side false c₁ (by simpa [hcs0] using hs0),
              hno_side true c₂ (by simpa [hcs1] using hs1)]
          simp [req, h1]
        · have h2 : fixedBits ρ = 2 := by omega
          obtain ⟨hl_eq, hr_eq, b', hbe, hlb', hrb', hlno, hrno⟩ := hstruc.2 h2
          have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
          have hfilt : Finset.univ.filter (fun w : Variable => ρ w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
            symm; apply Finset.eq_of_subset_of_card_le
            · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hw with rfl | rfl <;> simp [hlb', hrb']
            · simp [hne_lr]; exact h2.le
          have hb6_orig := shared_pair_b0_six hs (by simp [hcs0]) (by simp [hcs1]) hne
            (hsub_ow c₁ (by simp [hcs0])) (hsub_ow c₂ (by simp [hcs1]))
          have hside6 : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
              req 1 (State.grant ρ {v} s) ow = 6 := by
            intro s c hsc
            have hfbs : fixedBits (State.grant ρ {v} s) = 3 := by rw [fixedBits_grant_none hv s, h2]
            have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
            have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
            have hvb_ne : v.2 ≠ b' := by
              intro e
              have hvc := signedShared_const (c := c₁) hs0 (by simp [hcs0]) (grant_apply_self ρ v false)
              have hm : v ∈ Finset.univ.filter (fun w => ρ w ≠ none) := by
                rw [hfilt]; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hvc.1 with h1' | h1'
                · left; exact Prod.ext h1' e
                · right; exact Prod.ext h1' e
              exact (Finset.mem_filter.mp hm).2 hv
            have hsame_imp : ∀ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' → sameBitPair ρ u w b'' val'' := by
              intro u w b'' val'' ⟨huw, hu', hw'⟩
              have hb'' : b'' = b' := by
                by_contra hne'
                have hu_v : (u, b'') = v := by
                  by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hu'
                  have hm : (u, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
                  rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e <;> exact hne' (congrArg Prod.snd e)
                have hw_v : (w, b'') = v := by
                  by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hw'
                  have hm : (w, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
                  rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e <;> exact hne' (congrArg Prod.snd e)
                exact huw.ne (congrArg Prod.fst (hu_v.trans hw_v.symm))
              subst b''
              exact ⟨huw, by rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hu',
                          by rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hw'⟩
            have hlw6 : leafWeight ρ ow = 6 := by
              have hnc_ρ := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits ρ ≤ 3)
              rw [b0_of_fp_le_two hnc_ρ (fixedPigeons_le_two_of_shared (c := c₁) hs (by simp [hcs0]))] at hb6_orig
              exact hb6_orig
            have hlw_s : leafWeight (State.grant ρ {v} s) ow = 6 := by
              unfold leafWeight at hlw6 ⊢
              by_cases h3' : ∃ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
              · obtain ⟨u, w, b'', val'', hsp', hdj⟩ := h3'
                rw [ite_eq_left ⟨u, w, b'', val'', hsame_imp u w b'' val'' hsp', hdj⟩] at hlw6; omega
              · rw [ite_eq_right h3']
                by_cases h4' : ∃ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' ∧ (pairHoles u w b'' val'' ∩ ow).card ≤ 1
                · obtain ⟨u, w, b'', val'', hsp', hcd⟩ := h4'
                  by_cases h3ρ : ∃ u w b'' val'', sameBitPair ρ u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
                  · rw [ite_eq_left h3ρ] at hlw6; omega
                  · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, w, b'', val'', hsame_imp u w b'' val'' hsp', hcd⟩] at hlw6; omega
                · rw [ite_eq_right h4']
            simp only [req, ite_eq_right hnc_s, ite_eq_left (by omega : 3 ≤ fixedBits (State.grant ρ {v} s))]
            rw [b0_of_fp_le_two hnc_s hfp_s, hlw_s]
          rw [hside6 false c₁ (by simpa [hcs0] using hs0),
              hside6 true c₂ (by simpa [hcs1] using hs1)]
          simp [req, h2]

theorem b0_split_six_double_not_lw4 {ρ : State} {ow : Finset Collision} (hd : DistinctHoles ow)
    {v : Variable} (h6 : b0 ρ ow = 6) (s : Bool)
    (h2 : b0 (State.grant ρ {v} s) ow = 2) :
    ¬ leafWeight (State.grant ρ {v} (!s)) ow ≤ 4 := by
  have h7 : b0_all4 ρ ow = 7 := by
    have hlw : leafWeight ρ ow = 3 ∨ leafWeight ρ ow = 4 ∨ leafWeight ρ ow = 6 := by
      unfold leafWeight; split_ifs <;> omega
    unfold b0 at h6; unfold b0_all4; split_ifs at h6 ⊢ <;> omega
  have h2' : b0_all4 (State.grant ρ {v} s) ow = 2 := by
    have hlw := leafWeight_ge_three (State.grant ρ {v} s) ow
    unfold b0 at h2; unfold b0_all4; split_ifs at h2 ⊢ <;> omega
  have hsp := b0_all4_split (ρ := ρ) hd v
  have hge5 : 5 ≤ b0_all4 (State.grant ρ {v} (!s)) ow := by
    cases s <;> simp only [Bool.not_false, Bool.not_true] at * <;> omega
  intro hle4; have := b0_all4_le_four_of_lw4 hle4; omega

theorem grant_nonsingle {ρ : State} {f : Finset Variable} (hns : ∀ v : Variable, f ≠ {v})
    (side : Bool) : State.grant ρ f side = ρ := by
  funext v; unfold State.grant; rw [ite_eq_right (hns v)]

theorem state_le_grant_none {ρ : State} {v : Variable} (hv : ρ v = none) (side : Bool) :
    State.Le ρ (State.grant ρ {v} side) := by
  intro w b hw
  have hne : v ≠ w := fun e => by rw [e, hw] at hv; cases hv
  rw [grant_apply_ne ρ hne, hw]

theorem no_sameBitPair_other_side {c : Collision} {ρ : State} {v : Variable} {s : Bool}
    (_hv : ρ v = none) (_hfb : fixedBits ρ ≤ 2)
    (hno : ∀ u w b val, ¬ sameBitPair ρ u w b val)
    (hsc : SignedShared [c] ρ) (hscs : SignedShared [c] (State.grant ρ {v} s)) :
    ∀ u w b val, ¬ sameBitPair (State.grant ρ {v} (!s)) u w b val := by
  have hv_c := signedShared_const (c := c) hscs (by simp) (grant_apply_self ρ v s)
  rintro u w b' val' ⟨huw, hu', hw'⟩
  have hpair : u = c.left ∧ w = c.right := by
    have huf : u = c.left ∨ u = c.right := by
      by_cases e : (u, b') = v
      · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
      · rw [grant_apply_ne ρ (Ne.symm e)] at hu'; exact (signedShared_const (c := c) hsc (by simp) hu').1
    have hwf : w = c.left ∨ w = c.right := by
      by_cases e : (w, b') = v
      · rw [← congrArg Prod.fst e] at hv_c; exact hv_c.1
      · rw [grant_apply_ne ρ (Ne.symm e)] at hw'; exact (signedShared_const (c := c) hsc (by simp) hw').1
    rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
    · exact (huw.ne rfl).elim
    · exact ⟨rfl, rfl⟩
    · exact (not_lt_of_gt c.ordered huw).elim
    · exact (huw.ne rfl).elim
  obtain ⟨rfl, rfl⟩ := hpair
  by_cases e1 : (c.left, b') = v
  · have e2 : (c.right, b') ≠ v := fun e => c.ordered.ne (congrArg Prod.fst (e1.trans e.symm))
    rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
    have hval2 := (signedShared_const (c := c) hsc (by simp) hw').2
    rw [e1, grant_apply_self] at hu'
    have hval1 := Option.some.inj hu'
    have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e1] at hv_c; exact hv_c.2.symm
    rw [← hval1, hvs] at hval2; cases s <;> simp at hval2
  · by_cases e2 : (c.right, b') = v
    · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
      have hval1 := (signedShared_const (c := c) hsc (by simp) hu').2
      rw [e2, grant_apply_self] at hw'
      have hval2 := Option.some.inj hw'
      have hvs : bits c.hole b' = s := by rw [← congrArg Prod.snd e2] at hv_c; exact hv_c.2.symm
      rw [← hval2, hvs] at hval1; cases s <;> simp at hval1
    · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
      rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
      exact hno c.left c.right b' val' ⟨c.ordered, hu', hw'⟩

theorem b0_other_side_six_of_no_sameBitPair {c : Collision} {ρ : State} {ow : Finset Collision}
    {v : Variable} {s : Bool}
    (hv : ρ v = none) (hfb : fixedBits ρ ≤ 2)
    (hno : ∀ u w b val, ¬ sameBitPair ρ u w b val)
    (hsc : SignedShared [c] ρ) (hscs : SignedShared [c] (State.grant ρ {v} s)) :
    b0 (State.grant ρ {v} (!s)) ow = 6 := by
  have hfbo : fixedBits (State.grant ρ {v} (!s)) = fixedBits ρ + 1 := fixedBits_grant_none hv (!s)
  have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} (!s)) ≤ 3)
  have hv_c := signedShared_const (c := c) hscs (by simp) (grant_apply_self ρ v s)
  have hfp_o : fixedPigeons (State.grant ρ {v} (!s)) ≤ 2 := by
    have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) ⊆ ({c.left, c.right} : Finset (Fin 5)) := by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (Finset.mem_filter.mp hp).2 with h0 | h1
      · cases hw : State.grant ρ {v} (!s) (p, 0) with
        | none => exact (h0 hw).elim
        | some val =>
          by_cases he : (p, (0 : Fin 2)) = v
          · rw [← congrArg Prod.fst he] at hv_c; exact hv_c.1
          · rw [grant_apply_ne ρ (Ne.symm he)] at hw; exact (signedShared_const (c := c) hsc (by simp) hw).1
      · cases hw : State.grant ρ {v} (!s) (p, 1) with
        | none => exact (h1 hw).elim
        | some val =>
          by_cases he : (p, (1 : Fin 2)) = v
          · rw [← congrArg Prod.fst he] at hv_c; exact hv_c.1
          · rw [grant_apply_ne ρ (Ne.symm he)] at hw; exact (signedShared_const (c := c) hsc (by simp) hw).1
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  exact b0_eq_six_of_no_sameBitPair hnc_o hfp_o (no_sameBitPair_other_side hv hfb hno hsc hscs)

-- Measures on `DTree` and abstract `DValid` structural inductions.
section DTreeMeasures

variable {I : Type} [DecidableEq I]

def dExits : Dag.DTree Variable I → ℕ
  | .axUniq _ | .axRep _ => 0
  | .exitDer _ => 1
  | .weak _ t => dExits t
  | .res _ _ l r => dExits l + dExits r

def dAxReps : Dag.DTree Variable I → ℕ
  | .axRep _ => 1
  | .axUniq _ | .exitDer _ => 0
  | .weak _ t => dAxReps t
  | .res _ _ l r => dAxReps l + dAxReps r

def dWeaks : Dag.DTree Variable I → ℕ
  | .axUniq _ | .axRep _ | .exitDer _ => 0
  | .weak _ t => 1 + dWeaks t
  | .res _ _ l r => dWeaks l + dWeaks r

def dMarks (keyAt : I → Collision) : Dag.DTree Variable I → List Collision
  | .axUniq i => [keyAt i]
  | .axRep _ | .exitDer _ => []
  | .weak _ t => dMarks keyAt t
  | .res _ _ l r => dMarks keyAt r ++ dMarks keyAt l

def countExit (target : I) : Dag.DTree Variable I → ℕ
  | .exitDer i => if i = target then 1 else 0
  | .axUniq _ | .axRep _ => 0
  | .weak _ t => countExit target t
  | .res _ _ l r => countExit target l + countExit target r

def countExitsIn (S : Finset I) : Dag.DTree Variable I → ℕ
  | .exitDer i => if i ∈ S then 1 else 0
  | .axUniq _ | .axRep _ => 0
  | .weak _ t => countExitsIn S t
  | .res _ _ l r => countExitsIn S l + countExitsIn S r

def exitWeightSum (wt : I → ℕ) : Dag.DTree Variable I → ℕ
  | .exitDer i => wt i
  | .axUniq _ | .axRep _ => 0
  | .weak _ t => exitWeightSum wt t
  | .res _ _ l r => exitWeightSum wt l + exitWeightSum wt r

def dPhi (wt : I → ℕ) (t : Dag.DTree Variable I) : ℕ :=
  exitWeightSum wt t + dAxReps t + 10 * dWeaks t

theorem countExitsIn_sum (S : Finset I) (t : Dag.DTree Variable I) :
    countExitsIn S t = ∑ j ∈ S, countExit j t := by
  induction t with
  | axUniq _ | axRep _ => simp [countExitsIn, countExit]
  | exitDer i =>
    simp only [countExitsIn, countExit]
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi, Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji.symm]
      · intro hni; exact (hni hi).elim
    · rw [ite_eq_right hi]
      symm; apply Finset.sum_eq_zero; intro j hj
      simp [show i ≠ j from fun e => hi (e ▸ hj)]
  | weak _ t ih => exact ih
  | res _ _ l r ihl ihr =>
    simp only [countExitsIn, countExit, Finset.sum_add_distrib, ihl, ihr]

theorem countExitsIn_mono {S₁ S₂ : Finset I} (hsub : S₁ ⊆ S₂) (t : Dag.DTree Variable I) :
    countExitsIn S₁ t ≤ countExitsIn S₂ t := by
  induction t with
  | axUniq _ | axRep _ => simp [countExitsIn]
  | exitDer i =>
    simp only [countExitsIn]
    by_cases h1 : i ∈ S₁
    · rw [ite_eq_left h1, ite_eq_left (hsub h1)]
    · rw [ite_eq_right h1]; omega
  | weak _ t ih => exact ih
  | res _ _ l r ihl ihr => simp only [countExitsIn]; omega

theorem mul_countExitsIn_le_exitWeightSum {S : Finset I} {wt : I → ℕ} {c : ℕ}
    (hc : ∀ j ∈ S, c ≤ wt j) (t : Dag.DTree Variable I) :
    c * countExitsIn S t ≤ exitWeightSum wt t := by
  induction t with
  | axUniq _ | axRep _ => simp [countExitsIn, exitWeightSum]
  | exitDer i =>
    simp only [countExitsIn, exitWeightSum]
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi, Nat.mul_one]; exact hc i hi
    · rw [ite_eq_right hi]; simp
  | weak _ t ih => exact ih
  | res _ _ l r ihl ihr => simp only [countExitsIn, exitWeightSum, Nat.mul_add]; omega

theorem mul_countExitsIn_le_dPhi {S : Finset I} {wt : I → ℕ} {c : ℕ}
    (hc : ∀ j ∈ S, c ≤ wt j) (t : Dag.DTree Variable I) :
    c * countExitsIn S t ≤ dPhi wt t :=
  (mul_countExitsIn_le_exitWeightSum hc t).trans (by unfold dPhi; omega)

def Disagrees (ρ₁ ρ₂ : State) : Prop :=
  ∃ v : Variable, ∃ b : Bool, ρ₁ v = some b ∧ ρ₂ v = some (!b)

theorem disagrees_of_le {ρ₁ ρ₂ ρ₃ : State} (hd : Disagrees ρ₁ ρ₂) (hle : State.Le ρ₂ ρ₃) :
    Disagrees ρ₁ ρ₃ := by
  obtain ⟨v, b, h1, h2⟩ := hd
  exact ⟨v, b, h1, hle v (!b) h2⟩

theorem not_le_of_disagrees {ρ₁ ρ₂ : State} (hd : Disagrees ρ₁ ρ₂) : ¬ State.Le ρ₁ ρ₂ := by
  intro hle
  obtain ⟨v, b, h1, h2⟩ := hd
  have e := Option.some.inj ((hle v b h1).symm.trans h2)
  cases b <;> cases e

inductive DValid (stAt : I → State) (keyAt : I → Collision)
    (ow : Finset Collision) (wt : I → ℕ) : State → Dag.DTree Variable I → Prop
  | axUniq (i : I) (ρ : State) (hc : hasCollision ρ) (how : keyAt i ∈ ow)
      (hs : SignedShared [keyAt i] ρ) :
      DValid stAt keyAt ow wt ρ (.axUniq i)
  | axRep (i : I) (ρ : State) (hc : hasCollision ρ) :
      DValid stAt keyAt ow wt ρ (.axRep i)
  | exitDer (i : I) (ρ : State) (hle : State.Le (stAt i) ρ)
      (hwt : leafWeight ρ ow ≤ wt i) :
      DValid stAt keyAt ow wt ρ (.exitDer i)
  | weak (i : I) (ρ ρ' : State) (t : Dag.DTree Variable I)
      (hs : SignedShared (dMarks keyAt t) ρ)
      (ht : DValid stAt keyAt ow wt ρ' t) :
      DValid stAt keyAt ow wt ρ (.weak i t)
  | res (i : I) (f : Finset Variable) (ρ : State) (l r : Dag.DTree Variable I)
      (nd : ((dMarks keyAt r ++ dMarks keyAt l).map Collision.hole).Nodup)
      (hs : SignedShared (dMarks keyAt r ++ dMarks keyAt l) ρ)
      (hl : DValid stAt keyAt ow wt (State.grant ρ f true) l)
      (hr : DValid stAt keyAt ow wt (State.grant ρ f false) r) :
      DValid stAt keyAt ow wt ρ (.res i f l r)

omit [DecidableEq I] in
theorem dValid_marks_subset {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hv : DValid stAt keyAt ow wt ρ t) : ∀ c ∈ dMarks keyAt t, c ∈ ow := by
  induction hv with
  | axUniq i ρ _ how _ => intro c hc; simp only [dMarks, List.mem_singleton] at hc; exact hc ▸ how
  | axRep _ _ _ => simp [dMarks]
  | exitDer _ _ _ _ => simp [dMarks]
  | weak _ _ _ _ _ _ ih => exact ih
  | res _ _ _ _ _ _ _ _ _ ihl ihr =>
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ihr c h
    · exact ihl c h

omit [DecidableEq I] in
theorem dValid_nodup {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hv : DValid stAt keyAt ow wt ρ t) : ((dMarks keyAt t).map Collision.hole).Nodup := by
  induction hv with
  | axUniq => simp [dMarks]
  | axRep => simp [dMarks]
  | exitDer => simp [dMarks]
  | weak _ _ _ _ _ _ ih => exact ih
  | res _ _ _ _ _ nd _ _ _ _ _ => exact nd

omit [DecidableEq I] in
theorem dValid_shared {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hv : DValid stAt keyAt ow wt ρ t) : SignedShared (dMarks keyAt t) ρ := by
  cases hv with
  | axUniq _ _ _ _ hs => exact hs
  | axRep => intro _ _ _ _ hc; simp [dMarks] at hc
  | exitDer => intro _ _ _ _ hc; simp [dMarks] at hc
  | weak _ _ _ _ hs _ => exact hs
  | res _ _ _ _ _ _ hs _ _ => exact hs

omit [DecidableEq I] in
theorem dValid_req_bound {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t) :
    req (dMarks keyAt t).length ρ ow ≤ dPhi wt t := by
  induction hv with
  | axUniq i ρ hc _ _ => simp [dMarks, req, hc, dPhi]
  | axRep i ρ hc => simp [dMarks, req, b0_of_hasCollision hc, dPhi, exitWeightSum, dAxReps, dWeaks]
  | exitDer i ρ _ hwt =>
    simp only [dMarks, List.length_nil, req, dPhi, exitWeightSum, dAxReps, dWeaks]
    have := b0_le_leafWeight ρ ow; omega
  | weak i ρ ρ' t _ _ ih =>
    have hw := req_weak_step (dMarks keyAt t).length ρ ρ' ow
    simp only [dMarks, dPhi, exitWeightSum, dAxReps, dWeaks] at ih ⊢; omega
  | res i f ρ l r nd hs hl hr ihl ihr =>
    have hsub : ∀ c ∈ dMarks keyAt r ++ dMarks keyAt l, c ∈ ow := fun c hc =>
      (List.mem_append.mp hc).elim (dValid_marks_subset hr c) (dValid_marks_subset hl c)
    simp only [dMarks, dPhi, exitWeightSum, dAxReps, dWeaks] at ihl ihr ⊢
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      have hstep := req_single_step hd nd hsub hs v (dValid_shared hr) (dValid_shared hl)
      omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at ihl
      rw [grant_nonsingle hns false] at ihr
      have hstep := req_nonsingle_step nd hsub hs
      omega

theorem dValid_b0_all4_bound {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk0 : dMarks keyAt t = [])
    (hall4 : ∀ j, countExit j t ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4) :
    b0_all4 ρ ow ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk0
  | axRep i ρ hc =>
    simp only [dPhi, exitWeightSum, dAxReps, dWeaks, b0_all4, ite_eq_left hc]; omega
  | exitDer i ρ hle _ =>
    have hi := hall4 i (by simp [countExit])
    have h4 := b0_all4_le_four_of_lw4 (hi.2 ρ hle)
    simp only [dPhi, exitWeightSum, dAxReps, dWeaks]; omega
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r _ _ hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.append_eq_nil_iff, dPhi, exitWeightSum, dAxReps] at hpure hk0 ihl ihr ⊢
    have hl4 : ∀ j, countExit j l ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4 :=
      fun j hj => hall4 j (by simp [countExit]; omega)
    have hr4 : ∀ j, countExit j r ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4 :=
      fun j hj => hall4 j (by simp [countExit]; omega)
    have bl := ihl (by omega) hk0.2 hl4
    have br := ihr (by omega) hk0.1 hr4
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      have hsp := b0_all4_split (ρ := ρ) hd v
      omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl
      rw [grant_nonsingle hns false] at br
      omega

theorem dValid_k2_d1_all4_ge_19 {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk2 : (dMarks keyAt t).length = 2) (hfb1 : fixedBits ρ = 1)
    (hall4 : ∀ j, countExit j t ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4) :
    19 ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk2
  | axRep => simp [dMarks] at hk2
  | exitDer => simp [dMarks] at hk2
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.length_append, dPhi, exitWeightSum, dAxReps] at hpure hk2 ihl ihr ⊢
    have hl4 : ∀ j, countExit j l ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4 :=
      fun j hj => hall4 j (by simp [countExit]; omega)
    have hr4 : ∀ j, countExit j r ≥ 1 → 4 ≤ wt j ∧ ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4 :=
      fun j hj => hall4 j (by simp [countExit]; omega)
    have bl := dValid_req_bound hd hl
    have br := dValid_req_bound hd hr
    simp only [dPhi] at bl br
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have hrl2 : (dMarks keyAt r).length = 2 := by simp [hl0] at hk2; exact hk2
          have := ihr (by omega) hrl2 (by rw [e0]; exact hfb1) hr4
          omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have hll2 : (dMarks keyAt l).length = 2 := by simp [hr0] at hk2; exact hk2
          have := ihl (by omega) hll2 (by rw [e1]; exact hfb1) hl4
          omega
      | none =>
        have hfb0 : fixedBits (State.grant ρ {v} false) = 2 := by rw [fixedBits_grant_none hrv false, hfb1]
        have hfb1' : fixedBits (State.grant ρ {v} true) = 2 := by rw [fixedBits_grant_none hrv true, hfb1]
        rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
            ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
            ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
        · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
          have hr12 : req 2 (State.grant ρ {v} false) ow = 12 := by simp [req, hfb0]
          rw [er, hr12] at br
          -- Other side (true) has b0 = 6 and fp ≤ 2, so b0_all4 = 7!
          have hba7 : b0_all4 (State.grant ρ {v} true) ow = 7 := by
            rcases hrm : dMarks keyAt r with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hrm] at er
            subst er
            have hne : c₁.hole ≠ c₂.hole := by simp [hrm, hl0] at nd; exact nd
            have hss : SignedShared [c₁, c₂] (State.grant ρ {v} false) := hrm ▸ dValid_shared hr
            have hstruc := shared_pair_structure hss (by simp) (by simp) hne
            obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 hfb0
            have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
            have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              symm; apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hw with rfl | rfl <;> simp [hlb', hrb']
              · simp [hne_lr]; exact hfb0.le
            have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
            have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hwv : w = v
              · subst hwv; simp [grant_apply_self, hvm]
              · rw [grant_apply_ne ρ (Ne.symm hwv) true, ← grant_apply_ne ρ (Ne.symm hwv) false]
                have : (State.grant ρ {v} false w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                exact this
            have hfp_o : fixedPigeons (State.grant ρ {v} true) ≤ 2 := by
              have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} true)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
              exact (Finset.card_le_card hsub).trans Finset.card_le_two
            have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} true) ≤ 3)
            have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} true) u w b'' val'' := by
              rintro u w b'' val'' ⟨huw, hu', hw'⟩
              have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
              have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
              have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                · exact ⟨e1, e2⟩
                · have e1' : u = c₁.right := congrArg Prod.fst e1
                  have e2' : w = c₁.left := congrArg Prod.fst e2
                  rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
              rw [hpair.1] at hu'; rw [hpair.2] at hw'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
              rcases hvm with rfl | rfl
              · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                have hl_eq : bits c₁.hole b' = false := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') false))
                rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
              · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                have hr_eq : bits c₁.hole b' = false := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') false))
                rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
            have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
            have hlw6 : leafWeight (State.grant ρ {v} true) ow = 6 := by
              rw [b0_of_fp_le_two hnc_o hfp_o] at hb6; exact hb6
            have hnd_o : ¬ hasDoubleOneStep (State.grant ρ {v} true) := by
              intro hdb; unfold b0 at hb6; rw [ite_eq_right hnc_o, ite_eq_left hdb] at hb6; omega
            unfold b0_all4
            rw [ite_eq_right hnc_o, ite_eq_right hnd_o, ite_eq_right (by omega),
                ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          have ba := dValid_b0_all4_bound hd hl (by omega) hl0 hl4
          rw [hba7] at ba; simp only [dPhi] at ba; omega
        · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
          have hl12 : req 2 (State.grant ρ {v} true) ow = 12 := by simp [req, hfb1']
          rw [el, hl12] at bl
          have hba7 : b0_all4 (State.grant ρ {v} false) ow = 7 := by
            rcases hlm : dMarks keyAt l with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hlm] at el
            subst el
            have hne : c₁.hole ≠ c₂.hole := by simp [hlm, hr0] at nd; exact nd
            have hss : SignedShared [c₁, c₂] (State.grant ρ {v} true) := hlm ▸ dValid_shared hl
            have hstruc := shared_pair_structure hss (by simp) (by simp) hne
            obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 hfb1'
            have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
            have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              symm; apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hw with rfl | rfl <;> simp [hlb', hrb']
              · simp [hne_lr]; exact hfb1'.le
            have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
            have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hwv : w = v
              · subst hwv; simp [grant_apply_self, hvm]
              · rw [grant_apply_ne ρ (Ne.symm hwv) false, ← grant_apply_ne ρ (Ne.symm hwv) true]
                have : (State.grant ρ {v} true w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                exact this
            have hfp_o : fixedPigeons (State.grant ρ {v} false) ≤ 2 := by
              have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} false)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
              exact (Finset.card_le_card hsub).trans Finset.card_le_two
            have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} false) ≤ 3)
            have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} false) u w b'' val'' := by
              rintro u w b'' val'' ⟨huw, hu', hw'⟩
              have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
              have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
              have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                · exact ⟨e1, e2⟩
                · have e1' : u = c₁.right := congrArg Prod.fst e1
                  have e2' : w = c₁.left := congrArg Prod.fst e2
                  rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
              rw [hpair.1] at hu'; rw [hpair.2] at hw'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
              rcases hvm with rfl | rfl
              · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                have hl_eq : bits c₁.hole b' = true := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') true))
                rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
              · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                have hr_eq : bits c₁.hole b' = true := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') true))
                rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
            have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
            have hlw6 : leafWeight (State.grant ρ {v} false) ow = 6 := by
              rw [b0_of_fp_le_two hnc_o hfp_o] at hb6; exact hb6
            have hnd_o : ¬ hasDoubleOneStep (State.grant ρ {v} false) := by
              intro hdb; unfold b0 at hb6; rw [ite_eq_right hnc_o, ite_eq_left hdb] at hb6; omega
            unfold b0_all4
            rw [ite_eq_right hnc_o, ite_eq_right hnd_o, ite_eq_right (by omega),
                ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          have ba := dValid_b0_all4_bound hd hr (by omega) hr0 hr4
          rw [hba7] at ba; simp only [dPhi] at ba; omega
        · -- (1, 1) split from fixedBits = 1 gives 10 + 10 = 20!
          rcases hrm : dMarks keyAt r with _ | ⟨c₁, r0⟩; · simp [hrm] at er
          rcases hlm : dMarks keyAt l with _ | ⟨c₂, l0⟩; · simp [hlm] at el
          have hr0 : r0 = [] := by simpa [hrm] using er
          have hl0 : l0 = [] := by simpa [hlm] using el
          subst hr0; subst hl0
          have hno_side : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
              req 1 (State.grant ρ {v} s) ow = 10 := by
            intro s c hsc
            have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hrv s, hfb1]
            have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
            have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
            have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
              intro w hw ew
              cases hww : ρ w with
              | none => exact (hw hww).elim
              | some valw =>
                have e1' := (signedShared_const (c := c₁) hs (by simp [hrm]) hww).2
                have e2' := (signedShared_const (c := c₂) hs (by simp [hlm]) hww).2
                have ev1 := (signedShared_const (c := c₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)).2
                have ev2 := (signedShared_const (c := c₂) (dValid_shared hl) (by simp [hlm]) (grant_apply_self ρ v true)).2
                rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
                have := e1'.symm.trans e2'; cases this
            have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
              rintro u w b' val' ⟨huw, hu', hw'⟩
              by_cases e1' : (u, b') = v
              · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
                rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
              · by_cases e2' : (w, b') = v
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                  have hsub : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hx with rfl | rfl <;> simp [hu', hw']
                  have hc := Finset.card_le_card hsub
                  simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                  change 2 ≤ fixedBits ρ at hc; omega
            have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
            simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
          rw [er, hno_side false c₁ (hrm ▸ dValid_shared hr)] at br
          rw [el, hno_side true c₂ (hlm ▸ dValid_shared hl)] at bl
          omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl ihl
      rw [grant_nonsingle hns false] at br ihr
      rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
          ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
          ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
      · have := ihr (by omega) er hfb1 hr4; omega
      · have := ihl (by omega) el hfb1 hl4; omega
      · have h10 := req_one_of_fixedBits_le_one (ow := ow) (by omega : fixedBits ρ ≤ 1)
        rw [er, h10] at br; rw [el, h10] at bl; omega

theorem dValid_disagree_extra {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t) (hpure : dWeaks t = 0)
    (S : Finset I) (hwtS : ∀ j ∈ S, 4 ≤ wt j) (hdis : ∀ j ∈ S, Disagrees (stAt j) ρ) :
    req (dMarks keyAt t).length ρ ow + 4 * countExitsIn S t ≤ dPhi wt t := by
  induction hv with
  | axUniq i ρ hc _ _ => simp [dMarks, req, hc, countExitsIn, dPhi]
  | axRep i ρ hc => simp [dMarks, req, b0_of_hasCollision hc, countExitsIn, dPhi, exitWeightSum, dAxReps, dWeaks]
  | exitDer i ρ hle hwt =>
    have hni : i ∉ S := fun hi => not_le_of_disagrees (hdis i hi) hle
    simp only [dMarks, List.length_nil, req, countExitsIn, ite_eq_right hni, dPhi, exitWeightSum, dAxReps, dWeaks]
    have := b0_le_leafWeight ρ ow; omega
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    have hsub : ∀ c ∈ dMarks keyAt r ++ dMarks keyAt l, c ∈ ow := fun c hc =>
      (List.mem_append.mp hc).elim (dValid_marks_subset hr c) (dValid_marks_subset hl c)
    simp only [dWeaks, dMarks, List.length_append, countExitsIn, dPhi, exitWeightSum, dAxReps] at hpure ihl ihr ⊢
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have br := ihr (by omega) (by rw [e0]; exact hdis)
          rw [e0] at br
          have bl := mul_countExitsIn_le_dPhi hwtS l
          simp only [dPhi] at bl
          simp only [hl0, List.length_nil, Nat.add_zero]
          omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have bl := ihl (by omega) (by rw [e1]; exact hdis)
          rw [e1] at bl
          have br := mul_countExitsIn_le_dPhi hwtS r
          simp only [dPhi] at br
          simp only [hr0, List.length_nil, Nat.zero_add]
          omega
      | none =>
        have bl := ihl (by omega) (fun j hj => disagrees_of_le (hdis j hj) (state_le_grant_none hrv true))
        have br := ihr (by omega) (fun j hj => disagrees_of_le (hdis j hj) (state_le_grant_none hrv false))
        have hstep := req_single_step hd nd hsub hs v (dValid_shared hr) (dValid_shared hl)
        rw [List.length_append] at hstep
        omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at ihl
      rw [grant_nonsingle hns false] at ihr
      have bl := ihl (by omega) hdis
      have br := ihr (by omega) hdis
      have hstep := req_nonsingle_step nd hsub hs
      rw [List.length_append] at hstep
      omega

theorem dValid_b0M_bound {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk0 : dMarks keyAt t = [])
    (S : Finset I) (hwtS : ∀ j ∈ S, 4 ≤ wt j)
    (hlwS : ∀ j ∈ S, ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4)
    (hm : 1 ≤ countExitsIn S t) :
    (if ∀ j ∈ S, ¬ State.Le (stAt j) ρ then max 4 (b0 ρ ow + 1) else 4) ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk0
  | axRep => simp [countExitsIn] at hm
  | exitDer i ρ hle _ =>
    have hi : i ∈ S := by
      simp only [countExitsIn] at hm; by_contra hni; rw [ite_eq_right hni] at hm; omega
    have hnot : ¬ ∀ j ∈ S, ¬ State.Le (stAt j) ρ := fun h => h i hi hle
    rw [ite_eq_right hnot]
    simp only [dPhi, exitWeightSum, dAxReps, dWeaks]; have := hwtS i hi; omega
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r _ _ hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.append_eq_nil_iff, countExitsIn, dPhi, exitWeightSum, dAxReps] at hpure hk0 hm ihl ihr ⊢
    by_cases hboth : 1 ≤ countExitsIn S l ∧ 1 ≤ countExitsIn S r
    · have bl := mul_countExitsIn_le_dPhi hwtS l
      have br := mul_countExitsIn_le_dPhi hwtS r
      simp only [dPhi] at bl br
      have hb6 := b0_le_six ρ ow
      split_ifs <;> omega
    have b0_l := dValid_req_bound hd hl; rw [hk0.2] at b0_l; simp only [List.length_nil, req, dPhi] at b0_l
    have b0_r := dValid_req_bound hd hr; rw [hk0.1] at b0_r; simp only [List.length_nil, req, dPhi] at b0_r
    have handle_one : ∀ (s : Bool) (ρ_m ρ_o : State) (phi_m phi_o : ℕ),
        (∀ v : Variable, f = {v} → ρ_m = State.grant ρ {v} s ∧ ρ_o = State.grant ρ {v} (!s)) →
        ((∀ v : Variable, f ≠ {v}) → ρ_m = ρ ∧ ρ_o = ρ) →
        (if ∀ j ∈ S, ¬ State.Le (stAt j) ρ_m then max 4 (b0 ρ_m ow + 1) else 4) ≤ phi_m →
        b0 ρ_o ow ≤ phi_o →
        (if ∀ j ∈ S, ¬ State.Le (stAt j) ρ then max 4 (b0 ρ ow + 1) else 4) ≤ phi_m + phi_o := by
      intro s ρ_m ρ_o phi_m phi_o hsing_eq hns_eq hpm hpo
      by_cases hsing : ∃ v : Variable, f = {v}
      · obtain ⟨v, hv_eq⟩ := hsing
        obtain ⟨rfl, rfl⟩ := hsing_eq v hv_eq
        cases hrv : ρ v with
        | some side =>
          by_cases hs : s = side
          · subst s; rw [grant_eq_self hrv] at hpm; omega
          · have hns' : (!s) = side := by cases s <;> cases side <;> simp_all
            rw [hns', grant_eq_self hrv] at hpo
            have : 4 ≤ phi_m := by split_ifs at hpm <;> omega
            split_ifs <;> omega
        | none =>
          have hge1 := b0_ge_one (State.grant ρ {v} (!s)) ow
          have hge4 : 4 ≤ phi_m := by split_ifs at hpm <;> omega
          by_cases hle4 : b0 ρ ow ≤ 4
          · split_ifs <;> omega
          have h6 : b0 ρ ow = 6 := by
            have hlw : leafWeight ρ ow = 3 ∨ leafWeight ρ ow = 4 ∨ leafWeight ρ ow = 6 := by
              unfold leafWeight; split_ifs <;> omega
            unfold b0 at hle4 ⊢; split_ifs at hle4 ⊢ <;> omega
          have hsp := b0_split (ρ := ρ) hd v
          have hsp' : 6 ≤ b0 (State.grant ρ {v} s) ow + b0 (State.grant ρ {v} (!s)) ow := by
            cases s <;> simp only [Bool.not_false, Bool.not_true] at * <;> omega
          by_cases ho3 : 3 ≤ b0 (State.grant ρ {v} (!s)) ow
          · split_ifs <;> omega
          by_cases ho1 : b0 (State.grant ρ {v} (!s)) ow = 1
          · have hm5 : 5 ≤ b0 (State.grant ρ {v} s) ow := by omega
            have hno_m : ∀ j ∈ S, ¬ State.Le (stAt j) (State.grant ρ {v} s) := by
              intro j hj hle
              have hlw4 := hlwS j hj _ hle
              have := b0_le_leafWeight (State.grant ρ {v} s) ow; omega
            rw [ite_eq_left hno_m] at hpm; split_ifs <;> omega
          · have ho2 : b0 (State.grant ρ {v} (!s)) ow = 2 := by omega
            have hnlw4 := b0_split_six_double_not_lw4 hd h6 (!s) ho2
            rw [Bool.not_not] at hnlw4
            have hno_m : ∀ j ∈ S, ¬ State.Le (stAt j) (State.grant ρ {v} s) :=
              fun j hj hle => hnlw4 (hlwS j hj _ hle)
            rw [ite_eq_left hno_m] at hpm; split_ifs <;> omega
      · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
        obtain ⟨rfl, rfl⟩ := hns_eq hns; omega
    by_cases hml : 1 ≤ countExitsIn S l
    · have := handle_one true (State.grant ρ f true) (State.grant ρ f false)
        (exitWeightSum wt l + dAxReps l) (exitWeightSum wt r + dAxReps r)
        (fun v hv => by rw [hv]; exact ⟨rfl, rfl⟩)
        (fun hns => ⟨grant_nonsingle hns true, grant_nonsingle hns false⟩)
        (by have := ihl (by omega) hk0.2 hml; omega) (by omega)
      omega
    · have hmr : 1 ≤ countExitsIn S r := by omega
      have := handle_one false (State.grant ρ f false) (State.grant ρ f true)
        (exitWeightSum wt r + dAxReps r) (exitWeightSum wt l + dAxReps l)
        (fun v hv => by rw [hv]; exact ⟨rfl, rfl⟩)
        (fun hns => ⟨grant_nonsingle hns false, grant_nonsingle hns true⟩)
        (by have := ihr (by omega) hk0.1 hmr; omega) (by omega)
      omega

theorem dValid_b0M_six_ge_seven {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk0 : dMarks keyAt t = [])
    (S : Finset I) (hwtS : ∀ j ∈ S, 4 ≤ wt j)
    (hlwS : ∀ j ∈ S, ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4)
    (hm : 1 ≤ countExitsIn S t) (h6 : b0 ρ ow = 6) : 7 ≤ dPhi wt t := by
  have hno : ∀ j ∈ S, ¬ State.Le (stAt j) ρ := fun j hj hle => by
    have := hlwS j hj ρ hle; have := b0_le_leafWeight ρ ow; omega
  have hb := dValid_b0M_bound hd hv hpure hk0 S hwtS hlwS hm
  rw [ite_eq_left hno, h6] at hb; omega

omit [DecidableEq I] in
theorem dValid_d1_diff_pairs {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hfb1 : fixedBits ρ = 1)
    {c₁ c₂ : Collision} (hm : dMarks keyAt t = [c₁, c₂] ∨ dMarks keyAt t = [c₂, c₁])
    (hdiff : c₁.left ≠ c₂.left ∨ c₁.right ≠ c₂.right) : 20 ≤ dPhi wt t := by
  induction hv with
  | axUniq => rcases hm with h | h <;> simp [dMarks] at h
  | axRep => rcases hm with h | h <;> simp [dMarks] at h
  | exitDer => rcases hm with h | h <;> simp [dMarks] at h
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    have hk2 : (dMarks keyAt r).length + (dMarks keyAt l).length = 2 := by
      rcases hm with h | h <;> simp [dMarks] at h <;> have := congrArg List.length h <;> simp at this <;> omega
    have hne : c₁.hole ≠ c₂.hole := by
      rcases hm with h | h
      · simp only [dMarks] at h; rw [h] at nd; simp at nd; exact nd
      · simp only [dMarks] at h; rw [h] at nd; simp at nd; exact Ne.symm nd
    simp only [dWeaks, dPhi, exitWeightSum, dAxReps] at hpure ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have hrm : dMarks keyAt r = [c₁, c₂] ∨ dMarks keyAt r = [c₂, c₁] := by
            simpa [dMarks, hl0] using hm
          have := ihr (by omega) (by rw [e0]; exact hfb1) hrm; omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have hlm : dMarks keyAt l = [c₁, c₂] ∨ dMarks keyAt l = [c₂, c₁] := by
            simpa [dMarks, hr0] using hm
          have := ihl (by omega) (by rw [e1]; exact hfb1) hlm; omega
      | none =>
        have hfb0 : fixedBits (State.grant ρ {v} false) = 2 := by rw [fixedBits_grant_none hrv false, hfb1]
        have hfb1' : fixedBits (State.grant ρ {v} true) = 2 := by rw [fixedBits_grant_none hrv true, hfb1]
        have hno20 : (dMarks keyAt r).length ≠ 2 := by
          intro e2; have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero (by omega)
          have hrm : dMarks keyAt r = [c₁, c₂] ∨ dMarks keyAt r = [c₂, c₁] := by simpa [dMarks, hl0] using hm
          have hsr := dValid_shared hr
          have hc1 : c₁ ∈ dMarks keyAt r := by rcases hrm with h | h <;> simp [h]
          have hc2 : c₂ ∈ dMarks keyAt r := by rcases hrm with h | h <;> simp [h]
          have hst := (shared_pair_structure hsr hc1 hc2 hne).2 hfb0
          rcases hdiff with h | h; exact h hst.1; exact h hst.2.1
        have hno02 : (dMarks keyAt l).length ≠ 2 := by
          intro e2; have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero (by omega)
          have hlm : dMarks keyAt l = [c₁, c₂] ∨ dMarks keyAt l = [c₂, c₁] := by simpa [dMarks, hr0] using hm
          have hsl := dValid_shared hl
          have hc1 : c₁ ∈ dMarks keyAt l := by rcases hlm with h | h <;> simp [h]
          have hc2 : c₂ ∈ dMarks keyAt l := by rcases hlm with h | h <;> simp [h]
          have hst := (shared_pair_structure hsl hc1 hc2 hne).2 hfb1'
          rcases hdiff with h | h; exact h hst.1; exact h hst.2.1
        have er : (dMarks keyAt r).length = 1 := by omega
        have el : (dMarks keyAt l).length = 1 := by omega
        rcases hrm : dMarks keyAt r with _ | ⟨d₁, r0⟩; · simp [hrm] at er
        rcases hlm : dMarks keyAt l with _ | ⟨d₂, l0⟩; · simp [hlm] at el
        have hr0 : r0 = [] := by simpa [hrm] using er
        have hl0 : l0 = [] := by simpa [hlm] using el
        subst hr0; subst hl0
        have hno_side : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
            req 1 (State.grant ρ {v} s) ow = 10 := by
          intro s c hsc
          have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hrv s, hfb1]
          have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
          have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
          have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
            intro w hw ew
            cases hww : ρ w with
            | none => exact (hw hww).elim
            | some valw =>
              have e1' := (signedShared_const (c := d₁) hs (by simp [hrm]) hww).2
              have e2' := (signedShared_const (c := d₂) hs (by simp [hlm]) hww).2
              have ev1 := (signedShared_const (c := d₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)).2
              have ev2 := (signedShared_const (c := d₂) (dValid_shared hl) (by simp [hlm]) (grant_apply_self ρ v true)).2
              rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
              have := e1'.symm.trans e2'; cases this
          have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
            rintro u w b' val' ⟨huw, hu', hw'⟩
            by_cases e1' : (u, b') = v
            · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
              rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
              exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
            · by_cases e2' : (w, b') = v
              · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
              · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                have hsub : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                  intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  rcases hx with rfl | rfl <;> simp [hu', hw']
                have hc := Finset.card_le_card hsub
                simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                change 2 ≤ fixedBits ρ at hc; omega
          have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
          simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
        rw [er, hno_side false d₁ (hrm ▸ dValid_shared hr)] at br
        rw [el, hno_side true d₂ (hlm ▸ dValid_shared hl)] at bl
        omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl ihl
      rw [grant_nonsingle hns false] at br ihr
      rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
          ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
          ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
      · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
        have := ihr (by omega) hfb1 (by simpa [dMarks, hl0] using hm); omega
      · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
        have := ihl (by omega) hfb1 (by simpa [dMarks, hr0] using hm); omega
      · have h10 := req_one_of_fixedBits_le_one (ow := ow) (by omega : fixedBits ρ ≤ 1)
        rw [er, h10] at br; rw [el, h10] at bl; omega

theorem dValid_d1_same_pair_S {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk2 : (dMarks keyAt t).length = 2) (hfb1 : fixedBits ρ = 1)
    (S_all S_own : Finset I) (hsubS : S_own ⊆ S_all)
    (hwtS : ∀ j ∈ S_all, 4 ≤ wt j)
    (hlwS : ∀ j ∈ S_all, ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4)
    (hdis_H2 : ∀ (ρ2 : State), fixedBits ρ2 = 2 → SignedShared (dMarks keyAt t) ρ2 →
        ∀ j ∈ S_own, Disagrees (stAt j) ρ2) :
    (1 ≤ countExitsIn S_own t → 19 ≤ dPhi wt t) ∧
    (2 ≤ countExitsIn S_own t → 20 ≤ dPhi wt t) := by
  induction hv with
  | axUniq => simp [dMarks] at hk2
  | axRep => simp [dMarks] at hk2
  | exitDer => simp [dMarks] at hk2
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.length_append, countExitsIn, dPhi, exitWeightSum, dAxReps] at hpure hk2 ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    have h18_all : 18 ≤ exitWeightSum wt l + dAxReps l + (exitWeightSum wt r + dAxReps r) := by
      have := dValid_req_bound hd (.res i f ρ l r nd hs hl hr)
      simp only [dMarks, List.length_append, hk2, req, hfb1, dPhi, exitWeightSum, dAxReps, dWeaks, hpure] at this
      split_ifs at this <;> omega
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have hr2 : (dMarks keyAt r).length = 2 := by simp [hl0] at hk2; exact hk2
          have hr18 : 18 ≤ exitWeightSum wt r + dAxReps r := by
            rw [hr2, e0] at br; simp only [req, hfb1] at br; split_ifs at br <;> omega
          have bl_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) l; simp only [dPhi] at bl_own
          have ihr' := ihr (by omega) hr2 (by rw [e0]; exact hfb1)
            (fun ρ2 h2 hss j hj => hdis_H2 ρ2 h2 (by simpa [dMarks, hl0] using hss) j hj)
          constructor <;> intro hm
          · by_cases hml : 1 ≤ countExitsIn S_own l
            · omega
            · have := ihr'.1 (by omega); omega
          · by_cases hml : 1 ≤ countExitsIn S_own l
            · omega
            · have := ihr'.2 (by omega); omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have hl2 : (dMarks keyAt l).length = 2 := by simp [hr0] at hk2; exact hk2
          have hl18 : 18 ≤ exitWeightSum wt l + dAxReps l := by
            rw [hl2, e1] at bl; simp only [req, hfb1] at bl; split_ifs at bl <;> omega
          have br_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) r; simp only [dPhi] at br_own
          have ihl' := ihl (by omega) hl2 (by rw [e1]; exact hfb1)
            (fun ρ2 h2 hss j hj => hdis_H2 ρ2 h2 (by simpa [dMarks, hr0] using hss) j hj)
          constructor <;> intro hm
          · by_cases hmr : 1 ≤ countExitsIn S_own r
            · omega
            · have := ihl'.1 (by omega); omega
          · by_cases hmr : 1 ≤ countExitsIn S_own r
            · omega
            · have := ihl'.2 (by omega); omega
      | none =>
        have hfb0 : fixedBits (State.grant ρ {v} false) = 2 := by rw [fixedBits_grant_none hrv false, hfb1]
        have hfb1' : fixedBits (State.grant ρ {v} true) = 2 := by rw [fixedBits_grant_none hrv true, hfb1]
        rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
            ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
            ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
        · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
          have hdis_r : ∀ j ∈ S_own, Disagrees (stAt j) (State.grant ρ {v} false) :=
            hdis_H2 _ hfb0 (by simpa [dMarks, hl0] using dValid_shared hr)
          have hex_r := dValid_disagree_extra hd hr (by omega) S_own (fun j hj => hwtS j (hsubS hj)) hdis_r
          rw [er] at hex_r; simp only [req, show 2 ≤ fixedBits (State.grant ρ {v} false) by omega, ite_true, dPhi] at hex_r
          have hb6_l : b0 (State.grant ρ {v} true) ow = 6 := by
            rcases hrm : dMarks keyAt r with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hrm] at er
            subst er
            have hne : c₁.hole ≠ c₂.hole := by simp [hrm, hl0] at nd; exact nd
            have hss : SignedShared [c₁, c₂] (State.grant ρ {v} false) := hrm ▸ dValid_shared hr
            have hstruc := shared_pair_structure hss (by simp) (by simp) hne
            obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 hfb0
            have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
            have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              symm; apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hw with rfl | rfl <;> simp [hlb', hrb']
              · simp [hne_lr]; exact hfb0.le
            have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
            have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hwv : w = v
              · subst hwv; simp [grant_apply_self, hvm]
              · rw [grant_apply_ne ρ (Ne.symm hwv) true, ← grant_apply_ne ρ (Ne.symm hwv) false]
                have : (State.grant ρ {v} false w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                exact this
            have hfp_o : fixedPigeons (State.grant ρ {v} true) ≤ 2 := by
              have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} true)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
              exact (Finset.card_le_card hsub).trans Finset.card_le_two
            have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} true) ≤ 3)
            have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} true) u w b'' val'' := by
              rintro u w b'' val'' ⟨huw, hu', hw'⟩
              have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
              have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
              have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                · exact ⟨e1, e2⟩
                · have e1' : u = c₁.right := congrArg Prod.fst e1
                  have e2' : w = c₁.left := congrArg Prod.fst e2
                  rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
              rw [hpair.1] at hu'; rw [hpair.2] at hw'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
              rcases hvm with rfl | rfl
              · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                have hl_eq : bits c₁.hole b' = false := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') false))
                rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
              · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                have hr_eq : bits c₁.hole b' = false := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') false))
                rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
            exact b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
          rw [el] at bl; simp only [req, hb6_l] at bl
          have bl_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) l; simp only [dPhi] at bl_own
          have bl_all := countExitsIn_mono hsubS l
          constructor <;> intro hm
          · by_cases hml : 1 ≤ countExitsIn S_own l
            · have hb7 := dValid_b0M_six_ge_seven hd hl (by omega) hl0 S_all hwtS hlwS (by omega) hb6_l
              simp only [dPhi] at hb7; omega
            · omega
          · by_cases hml2 : 2 ≤ countExitsIn S_own l
            · omega
            · by_cases hml1 : 1 ≤ countExitsIn S_own l
              · have hb7 := dValid_b0M_six_ge_seven hd hl (by omega) hl0 S_all hwtS hlwS (by omega) hb6_l
                simp only [dPhi] at hb7; omega
              · omega
        · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
          have hdis_l : ∀ j ∈ S_own, Disagrees (stAt j) (State.grant ρ {v} true) :=
            hdis_H2 _ hfb1' (by simpa [dMarks, hr0] using dValid_shared hl)
          have hex_l := dValid_disagree_extra hd hl (by omega) S_own (fun j hj => hwtS j (hsubS hj)) hdis_l
          rw [el] at hex_l; simp only [req, show 2 ≤ fixedBits (State.grant ρ {v} true) by omega, ite_true, dPhi] at hex_l
          have hb6_r : b0 (State.grant ρ {v} false) ow = 6 := by
            rcases hlm : dMarks keyAt l with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hlm] at el
            subst el
            have hne : c₁.hole ≠ c₂.hole := by simp [hlm, hr0] at nd; exact nd
            have hss : SignedShared [c₁, c₂] (State.grant ρ {v} true) := hlm ▸ dValid_shared hl
            have hstruc := shared_pair_structure hss (by simp) (by simp) hne
            obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 hfb1'
            have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
            have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              symm; apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hw with rfl | rfl <;> simp [hlb', hrb']
              · simp [hne_lr]; exact hfb1'.le
            have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
              rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
            have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hwv : w = v
              · subst hwv; simp [grant_apply_self, hvm]
              · rw [grant_apply_ne ρ (Ne.symm hwv) false, ← grant_apply_ne ρ (Ne.symm hwv) true]
                have : (State.grant ρ {v} true w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                exact this
            have hfp_o : fixedPigeons (State.grant ρ {v} false) ≤ 2 := by
              have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} false)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
              exact (Finset.card_le_card hsub).trans Finset.card_le_two
            have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} false) ≤ 3)
            have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} false) u w b'' val'' := by
              rintro u w b'' val'' ⟨huw, hu', hw'⟩
              have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
              have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
              have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                · exact ⟨e1, e2⟩
                · have e1' : u = c₁.right := congrArg Prod.fst e1
                  have e2' : w = c₁.left := congrArg Prod.fst e2
                  rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
              rw [hpair.1] at hu'; rw [hpair.2] at hw'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
              rcases hvm with rfl | rfl
              · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                have hl_eq : bits c₁.hole b' = true := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') true))
                rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
              · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                have hr_eq : bits c₁.hole b' = true := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') true))
                rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                rw [← e1] at e2; cases e2
            exact b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
          rw [er] at br; simp only [req, hb6_r] at br
          have br_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) r; simp only [dPhi] at br_own
          have br_all := countExitsIn_mono hsubS r
          constructor <;> intro hm
          · by_cases hmr : 1 ≤ countExitsIn S_own r
            · have hb7 := dValid_b0M_six_ge_seven hd hr (by omega) hr0 S_all hwtS hlwS (by omega) hb6_r
              simp only [dPhi] at hb7; omega
            · omega
          · by_cases hmr2 : 2 ≤ countExitsIn S_own r
            · omega
            · by_cases hmr1 : 1 ≤ countExitsIn S_own r
              · have hb7 := dValid_b0M_six_ge_seven hd hr (by omega) hr0 S_all hwtS hlwS (by omega) hb6_r
                simp only [dPhi] at hb7; omega
              · omega
        · -- (1, 1) split gives 10 + 10 = 20!
          rcases hrm : dMarks keyAt r with _ | ⟨d₁, r0⟩; · simp [hrm] at er
          rcases hlm : dMarks keyAt l with _ | ⟨d₂, l0⟩; · simp [hlm] at el
          have hr0 : r0 = [] := by simpa [hrm] using er
          have hl0 : l0 = [] := by simpa [hlm] using el
          subst hr0; subst hl0
          have hno_side : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
              req 1 (State.grant ρ {v} s) ow = 10 := by
            intro s c hsc
            have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hrv s, hfb1]
            have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
            have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
            have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
              intro w hw ew
              cases hww : ρ w with
              | none => exact (hw hww).elim
              | some valw =>
                have e1' := (signedShared_const (c := d₁) hs (by simp [hrm]) hww).2
                have e2' := (signedShared_const (c := d₂) hs (by simp [hlm]) hww).2
                have ev1 := (signedShared_const (c := d₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)).2
                have ev2 := (signedShared_const (c := d₂) (dValid_shared hl) (by simp [hlm]) (grant_apply_self ρ v true)).2
                rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
                have := e1'.symm.trans e2'; cases this
            have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
              rintro u w b' val' ⟨huw, hu', hw'⟩
              by_cases e1' : (u, b') = v
              · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
                rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
              · by_cases e2' : (w, b') = v
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
                · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                  rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                  have hsub : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hx with rfl | rfl <;> simp [hu', hw']
                  have hc := Finset.card_le_card hsub
                  simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                  change 2 ≤ fixedBits ρ at hc; omega
            have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
            simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
          rw [er, hno_side false d₁ (hrm ▸ dValid_shared hr)] at br
          rw [el, hno_side true d₂ (hlm ▸ dValid_shared hl)] at bl
          constructor <;> intro _ <;> omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl ihl
      rw [grant_nonsingle hns false] at br ihr
      rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
          ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
          ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
      · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
        have hr18 : 18 ≤ exitWeightSum wt r + dAxReps r := by
          rw [er] at br; simp only [req, hfb1] at br; split_ifs at br <;> omega
        have bl_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) l; simp only [dPhi] at bl_own
        have ihr' := ihr (by omega) er hfb1 (fun ρ2 h2 hss j hj => hdis_H2 ρ2 h2 (by simpa [dMarks, hl0] using hss) j hj)
        constructor <;> intro hm
        · by_cases hml : 1 ≤ countExitsIn S_own l
          · omega
          · have := ihr'.1 (by omega); omega
        · by_cases hml : 1 ≤ countExitsIn S_own l
          · omega
          · have := ihr'.2 (by omega); omega
      · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
        have hl18 : 18 ≤ exitWeightSum wt l + dAxReps l := by
          rw [el] at bl; simp only [req, hfb1] at bl; split_ifs at bl <;> omega
        have br_own := mul_countExitsIn_le_dPhi (fun j hj => hwtS j (hsubS hj)) r; simp only [dPhi] at br_own
        have ihl' := ihl (by omega) el hfb1 (fun ρ2 h2 hss j hj => hdis_H2 ρ2 h2 (by simpa [dMarks, hr0] using hss) j hj)
        constructor <;> intro hm
        · by_cases hmr : 1 ≤ countExitsIn S_own r
          · omega
          · have := ihl'.1 (by omega); omega
        · by_cases hmr : 1 ≤ countExitsIn S_own r
          · omega
          · have := ihl'.2 (by omega); omega
      · have h10 := req_one_of_fixedBits_le_one (ow := ow) (by omega : fixedBits ρ ≤ 1)
        rw [er, h10] at br; rw [el, h10] at bl
        constructor <;> intro _ <;> omega

theorem dValid_k1_other_S {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk1 : (dMarks keyAt t).length = 1) (hfb2 : fixedBits ρ ≤ 2)
    (hno : ∀ u w b val, ¬ sameBitPair ρ u w b val)
    (S : Finset I) (hwtS : ∀ j ∈ S, 4 ≤ wt j)
    (hlwS : ∀ j ∈ S, ∀ ρ', State.Le (stAt j) ρ' → leafWeight ρ' ow ≤ 4)
    (hm : 2 ≤ countExitsIn S t) : 11 ≤ dPhi wt t := by
  induction hv with
  | axUniq i ρ hc _ _ => exact (not_hasCollision_of_fixedBits_le_three (by omega) hc).elim
  | axRep => simp [dMarks] at hk1
  | exitDer => simp [dMarks] at hk1
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.length_append, countExitsIn, dPhi, exitWeightSum, dAxReps] at hpure hk1 hm ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    have hnc_ρ := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits ρ ≤ 3)
    have hreq10 : req 1 ρ ow = 10 := by
      rcases (show (dMarks keyAt r).length = 1 ∨ (dMarks keyAt l).length = 1 by omega) with er | el
      · rcases hrm : dMarks keyAt r with _ | ⟨c, r0⟩; · simp [hrm] at er
        have hfp := fixedPigeons_le_two_of_shared (c := c) hs (by simp [hrm])
        have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_ρ hfp hno
        simp only [req, ite_eq_right hnc_ρ, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega), hb6]; omega
      · rcases hlm : dMarks keyAt l with _ | ⟨c, l0⟩; · simp [hlm] at el
        have hfp := fixedPigeons_le_two_of_shared (c := c) hs (by simp [hlm])
        have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_ρ hfp hno
        simp only [req, ite_eq_right hnc_ρ, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega), hb6]; omega
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have er : (dMarks keyAt r).length = 1 := by simp [hl0] at hk1; exact hk1
          rw [er, e0, hreq10] at br
          have bl_S := mul_countExitsIn_le_dPhi hwtS l; simp only [dPhi] at bl_S
          by_cases hml : 1 ≤ countExitsIn S l
          · omega
          · have := ihr (by omega) er (by rw [e0]; exact hfb2) (by rw [e0]; exact hno) (by omega); omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have el : (dMarks keyAt l).length = 1 := by simp [hr0] at hk1; exact hk1
          rw [el, e1, hreq10] at bl
          have br_S := mul_countExitsIn_le_dPhi hwtS r; simp only [dPhi] at br_S
          by_cases hmr : 1 ≤ countExitsIn S r
          · omega
          · have := ihl (by omega) el (by rw [e1]; exact hfb2) (by rw [e1]; exact hno) (by omega); omega
      | none =>
        have hfb0 : fixedBits (State.grant ρ {v} false) = fixedBits ρ + 1 := fixedBits_grant_none hrv false
        have hfb1 : fixedBits (State.grant ρ {v} true) = fixedBits ρ + 1 := fixedBits_grant_none hrv true
        have bl_S := mul_countExitsIn_le_dPhi hwtS l; simp only [dPhi] at bl_S
        have br_S := mul_countExitsIn_le_dPhi hwtS r; simp only [dPhi] at br_S
        rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by omega) with ⟨er, el⟩ | ⟨er, el⟩
        · rcases hrm : dMarks keyAt r with _ | ⟨c, r0⟩; · simp [hrm] at er
          have hr0 : r0 = [] := by simpa [hrm] using er
          subst hr0
          have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
          have hnc_r := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} false) ≤ 3)
          have hcow : c ∈ ow := dValid_marks_subset hr c (by simp [hrm])
          have hb4_r := shared_single_b0_ge_four (hrm ▸ dValid_shared hr) (by simp) hcow hnc_r
          have hr4 : 4 ≤ exitWeightSum wt r + dAxReps r := by
            rw [er] at br; simp only [req, ite_eq_right hnc_r] at br; split_ifs at br <;> omega
          have hb6_l := b0_other_side_six_of_no_sameBitPair (ow := ow) hrv hfb2 hno
            (by simpa [hrm, hl0] using hs) (hrm ▸ dValid_shared hr)
          simp only [Bool.not_false] at hb6_l
          rw [el] at bl; simp only [req, hb6_l] at bl
          by_cases hml0 : countExitsIn S l = 0
          · omega
          · by_cases hml1 : countExitsIn S l = 1
            · have hb7 := dValid_b0M_six_ge_seven hd hl (by omega) hl0 S hwtS hlwS (by omega) hb6_l
              simp only [dPhi] at hb7; omega
            · omega
        · rcases hlm : dMarks keyAt l with _ | ⟨c, l0⟩; · simp [hlm] at el
          have hl0 : l0 = [] := by simpa [hlm] using el
          subst hl0
          have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
          have hnc_l := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} true) ≤ 3)
          have hcow : c ∈ ow := dValid_marks_subset hl c (by simp [hlm])
          have hb4_l := shared_single_b0_ge_four (hlm ▸ dValid_shared hl) (by simp) hcow hnc_l
          have hl4 : 4 ≤ exitWeightSum wt l + dAxReps l := by
            rw [el] at bl; simp only [req, ite_eq_right hnc_l] at bl; split_ifs at bl <;> omega
          have hb6_r := b0_other_side_six_of_no_sameBitPair (ow := ow) hrv hfb2 hno
            (by simpa [hlm, hr0] using hs) (hlm ▸ dValid_shared hl)
          simp only [Bool.not_true] at hb6_r
          rw [er] at br; simp only [req, hb6_r] at br
          by_cases hmr0 : countExitsIn S r = 0
          · omega
          · by_cases hmr1 : countExitsIn S r = 1
            · have hb7 := dValid_b0M_six_ge_seven hd hr (by omega) hr0 S hwtS hlwS (by omega) hb6_r
              simp only [dPhi] at hb7; omega
            · omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl ihl
      rw [grant_nonsingle hns false] at br ihr
      have bl_S := mul_countExitsIn_le_dPhi hwtS l; simp only [dPhi] at bl_S
      have br_S := mul_countExitsIn_le_dPhi hwtS r; simp only [dPhi] at br_S
      rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by omega) with ⟨er, el⟩ | ⟨er, el⟩
      · rw [er, hreq10] at br
        by_cases hml : 1 ≤ countExitsIn S l; · omega
        · have := ihr (by omega) er hfb2 hno (by omega); omega
      · rw [el, hreq10] at bl
        by_cases hmr : 1 ≤ countExitsIn S r; · omega
        · have := ihl (by omega) el hfb2 hno (by omega); omega

/-- For a pure `k = 0` tree extending `ρ1 = {u = h0, v = h1}` with `ow' = {c_r, c_twin}`,
    if every exit leaf extending `ρ1` respects `leafWeight ρ_leaf ow' ≤ wt j`,
    then `b0 ρ ow' ≤ dPhi wt t` (giving `6 ≤ dPhi wt t` at `ρ = ρ1`!). -/
theorem dValid_b0_ext_bound {stAt : I → State} {keyAt : I → Collision}
    {ow ow' : Finset Collision} {wt : I → ℕ} {ρ ρ1 : State} {t : Dag.DTree Variable I}
    (hd' : DistinctHoles ow') (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) (hk0 : dMarks keyAt t = []) (hext : State.Le ρ1 ρ)
    (hwt' : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf → State.Le ρ1 ρ_leaf →
      countExit j t ≥ 1 → leafWeight ρ_leaf ow' ≤ wt j) :
    b0 ρ ow' ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk0
  | axRep i ρ hc =>
    simp only [dPhi, exitWeightSum, dAxReps, dWeaks, b0_of_hasCollision hc]; omega
  | exitDer i ρ hle _ =>
    have hlw := hwt' i ρ hle hext (by simp [countExit])
    simp only [dPhi, exitWeightSum, dAxReps, dWeaks]
    exact (b0_le_leafWeight ρ ow').trans (by omega)
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r _ _ hl hr ihl ihr =>
    simp only [dWeaks, dMarks, List.append_eq_nil_iff, dPhi, exitWeightSum, dAxReps] at hpure hk0 ihl ihr ⊢
    have hwtl : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf → State.Le ρ1 ρ_leaf →
        countExit j l ≥ 1 → leafWeight ρ_leaf ow' ≤ wt j :=
      fun j ρl h1 h2 hc => hwt' j ρl h1 h2 (by simp [countExit]; omega)
    have hwtr : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf → State.Le ρ1 ρ_leaf →
        countExit j r ≥ 1 → leafWeight ρ_leaf ow' ≤ wt j :=
      fun j ρl h1 h2 hc => hwt' j ρl h1 h2 (by simp [countExit]; omega)
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have := ihr (by omega) hk0.1 (by rw [e0]; exact hext) hwtr; rw [e0] at this; omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have := ihl (by omega) hk0.2 (by rw [e1]; exact hext) hwtl; rw [e1] at this; omega
      | none =>
        have bl := ihl (by omega) hk0.2 (hext.trans (state_le_grant_none hrv true)) hwtl
        have br := ihr (by omega) hk0.1 (hext.trans (state_le_grant_none hrv false)) hwtr
        have hsp := b0_split (ρ := ρ) hd' v
        omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      have bl := ihl (by omega) hk0.2 (by rw [grant_nonsingle hns true]; exact hext) hwtl
      rw [grant_nonsingle hns true] at bl; omega

theorem dValid_inTwin_ge_six {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (_hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) {c_r c_twin : Collision}
    (hm : dMarks keyAt t = [c_r])
    (hfb3 : fixedBits ρ = 3) (hnc : ¬ hasCollision ρ)
    (ht_l : c_twin.left = c_r.left) (ht_r : c_twin.right = c_r.right)
    (hb : Fin 2) (ht_hole : c_twin.hole = flipBit c_r.hole (otherBit hb))
    (hsp : sameBitPair ρ c_r.left c_r.right hb (bits c_r.hole hb))
    (hwt_twin : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
      pigeonHole ρ_leaf c_r.left c_r.hole → pigeonHole ρ_leaf c_r.right c_twin.hole →
      countExit j t ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j)
    (hwt_twin' : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
      pigeonHole ρ_leaf c_r.left c_twin.hole → pigeonHole ρ_leaf c_r.right c_r.hole →
      countExit j t ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j) :
    6 ≤ dPhi wt t := by
  have hd_pair : DistinctHoles ({c_r, c_twin} : Finset Collision) := by
    intro x hx y hy heq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hne : c_r.hole ≠ c_twin.hole := by rw [ht_hole]; exact (flipBit_facts c_r.hole (otherBit hb)).1.symm
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact (hne heq).elim
    · exact (hne heq.symm).elim
    · rfl
  induction hv with
  | axUniq i ρ hc _ _ => exact (hnc hc).elim
  | axRep => simp [dMarks] at hm
  | exitDer => simp [dMarks] at hm
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dWeaks, dMarks, dPhi, exitWeightSum, dAxReps] at hpure hm ihl ihr ⊢
    have hwtl : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
        pigeonHole ρ_leaf c_r.left c_r.hole → pigeonHole ρ_leaf c_r.right c_twin.hole →
        countExit j l ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j :=
      fun j ρl h1 h2 h3 hc => hwt_twin j ρl h1 h2 h3 (by simp [countExit]; omega)
    have hwtr : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
        pigeonHole ρ_leaf c_r.left c_r.hole → pigeonHole ρ_leaf c_r.right c_twin.hole →
        countExit j r ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j :=
      fun j ρl h1 h2 h3 hc => hwt_twin j ρl h1 h2 h3 (by simp [countExit]; omega)
    have hwtl' : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
        pigeonHole ρ_leaf c_r.left c_twin.hole → pigeonHole ρ_leaf c_r.right c_r.hole →
        countExit j l ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j :=
      fun j ρl h1 h2 h3 hc => hwt_twin' j ρl h1 h2 h3 (by simp [countExit]; omega)
    have hwtr' : ∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
        pigeonHole ρ_leaf c_r.left c_twin.hole → pigeonHole ρ_leaf c_r.right c_r.hole →
        countExit j r ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j :=
      fun j ρl h1 h2 h3 hc => hwt_twin' j ρl h1 h2 h3 (by simp [countExit]; omega)
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have hrm : dMarks keyAt r = [c_r] := by simpa [hl0] using hm
          have := ihr (by omega) hrm (by rw [e0]; exact hfb3) (by rw [e0]; exact hnc) (by rw [e0]; exact hsp) hwtr hwtr'
          omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have hlm : dMarks keyAt l = [c_r] := by simpa [hr0] using hm
          have := ihl (by omega) hlm (by rw [e1]; exact hfb3) (by rw [e1]; exact hnc) (by rw [e1]; exact hsp) hwtl hwtl'
          omega
      | none =>
        -- Helper: for the 0-side ρ_o = grant ρ {v} (!s), it has {u=h0, v=h1} (or swapped), so b0 ρ_o {c_r, c_twin} = 6!
        have handle_none : ∀ (s : Bool) (t_o : Dag.DTree Variable I),
            SignedShared [c_r] (State.grant ρ {v} s) →
            DValid stAt keyAt ow wt (State.grant ρ {v} (!s)) t_o →
            dWeaks t_o = 0 → dMarks keyAt t_o = [] →
            (∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
              pigeonHole ρ_leaf c_r.left c_r.hole → pigeonHole ρ_leaf c_r.right c_twin.hole →
              countExit j t_o ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j) →
            (∀ j ρ_leaf, State.Le (stAt j) ρ_leaf →
              pigeonHole ρ_leaf c_r.left c_twin.hole → pigeonHole ρ_leaf c_r.right c_r.hole →
              countExit j t_o ≥ 1 → leafWeight ρ_leaf ({c_r, c_twin} : Finset Collision) ≤ wt j) →
            6 ≤ dPhi wt t_o := by
          intro s t_o hss hv_o hp_o hk0_o hw1 hw2
          have hvc := signedShared_const (c := c_r) hss (by simp) (grant_apply_self ρ v s)
          have hfb_s : fixedBits (State.grant ρ {v} s) = 4 := by rw [fixedBits_grant_none hrv s, hfb3]
          -- All 4 bits of {c_r.left, c_r.right} are fixed in grant ρ {v} s!
          have hcoll_s := hasCollision_of_fixedBits_four (c := c_r) hss (by simp) (by omega)
          -- v MUST be (c_r.left, otherBit hb) or (c_r.right, otherBit hb)!
          have hvb : v.2 = otherBit hb := by
            rcases (otherBit_facts hb).2.2 v.2 with eb | eb
            · exfalso
              rcases hvc.1 with hl' | hr'
              · have e : v = (c_r.left, hb) := Prod.ext hl' eb
                rw [e, hsp.2.1] at hrv; cases hrv
              · have e : v = (c_r.right, hb) := Prod.ext hr' eb
                rw [e, hsp.2.2] at hrv; cases hrv
            · exact eb
          have hvs : s = bits c_r.hole (otherBit hb) := by rw [hvc.2, hvb]
          have hns_eq : (!s) = bits c_twin.hole (otherBit hb) := by
            rw [ht_hole, (flipBit_facts c_r.hole (otherBit hb)).2.1, hvs]
          have ht_hb : bits c_twin.hole hb = bits c_r.hole hb := by
            rw [ht_hole]; have := (flipBit_facts c_r.hole (otherBit hb)).2.2.1
            rwa [(otherBit_facts hb).2.1] at this
          -- Helper: ρ_o fixes ONLY {c_r.left, c_r.right} to {c_r.hole, c_twin.hole} (one each)!
          have hother_fixed : ∀ p, (p = c_r.left ∨ p = c_r.right) → (p, otherBit hb) ≠ v →
              ρ (p, otherBit hb) = some (bits c_r.hole (otherBit hb)) := by
            intro p hp hnev
            have hc_s : State.grant ρ {v} s (p, otherBit hb) = some (bits c_r.hole (otherBit hb)) := by
              -- From hfb_s = 4 and SignedShared [c_r] (grant ρ {v} s):
              have hsub : Finset.univ.filter (fun w : Variable => State.grant ρ {v} s w ≠ none) ⊆
                  {(c_r.left, 0), (c_r.left, 1), (c_r.right, 0), (c_r.right, 1)} := by
                intro w hw; cases hww : State.grant ρ {v} s w with
                | none => exact ((Finset.mem_filter.mp hw).2 hww).elim
                | some val =>
                  have h1 := (signedShared_const (c := c_r) hss (by simp) hww).1
                  rcases w with ⟨pw, bw⟩; change pw = c_r.left ∨ pw = c_r.right at h1
                  rcases h1 with rfl | rfl <;> fin_cases bw <;> simp
              have hcard4 : ({(c_r.left, (0 : Fin 2)), (c_r.left, 1), (c_r.right, 0), (c_r.right, 1)} : Finset Variable).card = 4 := by
                simp [c_r.ordered.ne]
              have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard4]; exact hfb_s.symm.le)
              have hm' : (p, otherBit hb) ∈ Finset.univ.filter (fun w : Variable => State.grant ρ {v} s w ≠ none) := by
                rw [heq]; rcases hp with rfl | rfl <;> fin_cases hb <;> simp [otherBit]
              cases hww : State.grant ρ {v} s (p, otherBit hb) with
              | none => exact ((Finset.mem_filter.mp hm').2 hww).elim
              | some val => rw [(signedShared_const (c := c_r) hss (by simp) hww).2]
            rwa [grant_apply_ne ρ hnev.symm] at hc_s
          -- Therefore in ρ_o: one of c_r.left, c_r.right is at c_r.hole and the other is at c_twin.hole!
          have hholes_o : (pigeonHole (State.grant ρ {v} (!s)) c_r.left c_r.hole ∧
              pigeonHole (State.grant ρ {v} (!s)) c_r.right c_twin.hole) ∨
              (pigeonHole (State.grant ρ {v} (!s)) c_r.left c_twin.hole ∧
              pigeonHole (State.grant ρ {v} (!s)) c_r.right c_r.hole) := by
            rcases hvc.1 with hl' | hr'
            · right
              have hv_eq : v = (c_r.left, otherBit hb) := Prod.ext hl' hvb
              have hne_r : (c_r.right, otherBit hb) ≠ v := fun e => c_r.ordered.ne' (hl' ▸ congrArg Prod.fst e)
              have hne_lb : (c_r.left, hb) ≠ v := fun e => (otherBit_facts hb).1 (hvb ▸ congrArg Prod.snd e).symm
              have hne_rb : (c_r.right, hb) ≠ v := fun e => (otherBit_facts hb).1 (hvb ▸ congrArg Prod.snd e).symm
              refine ⟨pigeonHole_of_bits (b := hb) ?_ ?_, pigeonHole_of_bits (b := hb) ?_ ?_⟩
              · rw [grant_apply_ne ρ hne_lb.symm, hsp.2.1, ht_hb]
              · rw [← hv_eq, grant_apply_self, hns_eq]
              · rw [grant_apply_ne ρ hne_rb.symm, hsp.2.2]
              · rw [grant_apply_ne ρ hne_r.symm, hother_fixed c_r.right (Or.inr rfl) hne_r]
            · left
              have hv_eq : v = (c_r.right, otherBit hb) := Prod.ext hr' hvb
              have hne_l : (c_r.left, otherBit hb) ≠ v := fun e => c_r.ordered.ne (hr' ▸ congrArg Prod.fst e)
              have hne_lb : (c_r.left, hb) ≠ v := fun e => (otherBit_facts hb).1 (hvb ▸ congrArg Prod.snd e).symm
              have hne_rb : (c_r.right, hb) ≠ v := fun e => (otherBit_facts hb).1 (hvb ▸ congrArg Prod.snd e).symm
              refine ⟨pigeonHole_of_bits (b := hb) ?_ ?_, pigeonHole_of_bits (b := hb) ?_ ?_⟩
              · rw [grant_apply_ne ρ hne_lb.symm, hsp.2.1]
              · rw [grant_apply_ne ρ hne_l.symm, hother_fixed c_r.left (Or.inl rfl) hne_l]
              · rw [grant_apply_ne ρ hne_rb.symm, hsp.2.2, ht_hb]
              · rw [← hv_eq, grant_apply_self, hns_eq]
          -- Compute b0 (State.grant ρ {v} (!s)) {c_r, c_twin} = 6!
          have hfp_o : fixedPigeons (State.grant ρ {v} (!s)) ≤ 2 := by
            have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) ⊆ ({c_r.left, c_r.right} : Finset (Fin 5)) := by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases (Finset.mem_filter.mp hp).2 with h0 | h1
              · cases hw' : State.grant ρ {v} (!s) (p, 0) with
                | none => exact (h0 hw').elim
                | some val =>
                  by_cases he : (p, (0 : Fin 2)) = v
                  · rw [← congrArg Prod.fst he] at hvc; exact hvc.1
                  · rw [grant_apply_ne ρ (Ne.symm he)] at hw'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').1
              · cases hw' : State.grant ρ {v} (!s) (p, 1) with
                | none => exact (h1 hw').elim
                | some val =>
                  by_cases he : (p, (1 : Fin 2)) = v
                  · rw [← congrArg Prod.fst he] at hvc; exact hvc.1
                  · rw [grant_apply_ne ρ (Ne.symm he)] at hw'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').1
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
          have hne_holes : c_r.hole ≠ c_twin.hole := by rw [ht_hole]; exact (flipBit_facts c_r.hole (otherBit hb)).1.symm
          have hnc_o : ¬ hasCollision (State.grant ρ {v} (!s)) := by
            rintro ⟨u, w, huw, h, hu, hw'⟩
            have hmem : ∀ x, pigeonFixed (State.grant ρ {v} (!s)) x → x = c_r.left ∨ x = c_r.right := by
              intro x hx
              have hsub : ({c_r.left, c_r.right} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) := by
                intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hholes_o with ⟨hlh, hrh⟩ | ⟨hlh, hrh⟩ <;> rcases hy with rfl | rfl
                · exact pigeonFixed_of_hole hlh
                · exact pigeonFixed_of_hole hrh
                · exact pigeonFixed_of_hole hlh
                · exact pigeonFixed_of_hole hrh
              have heq := Finset.eq_of_subset_of_card_le hsub (by simp [c_r.ordered.ne]; exact hfp_o)
              have hm' : x ∈ ({c_r.left, c_r.right} : Finset (Fin 5)) := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
              simpa using hm'
            have hpair : u = c_r.left ∧ w = c_r.right := by
              rcases hmem u (pigeonFixed_of_hole hu) with rfl | rfl <;>
                rcases hmem w (pigeonFixed_of_hole hw') with rfl | rfl
              · exact (huw.ne rfl).elim
              · exact ⟨rfl, rfl⟩
              · exact (not_lt_of_gt c_r.ordered huw).elim
              · exact (huw.ne rfl).elim
            obtain ⟨rfl, rfl⟩ := hpair
            rcases hholes_o with ⟨hlh, hrh⟩ | ⟨hlh, hrh⟩
            · exact hne_holes ((pigeonHole_unique hlh hu).trans (pigeonHole_unique hw' hrh))
            · exact hne_holes.symm ((pigeonHole_unique hlh hu).trans (pigeonHole_unique hw' hrh))
          have hb6_o : b0 (State.grant ρ {v} (!s)) ({c_r, c_twin} : Finset Collision) = 6 := by
            rw [b0_of_fp_le_two hnc_o hfp_o]
            have hcard2 : ∀ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' →
                2 ≤ (pairHoles u w b' val' ∩ ({c_r, c_twin} : Finset Collision)).card := by
              intro u w b' val' ⟨huw, hu', hw'⟩
              have hsub : ({c_r.left, c_r.right} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) := by
                intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rcases hholes_o with ⟨hlh, hrh⟩ | ⟨hlh, hrh⟩ <;> rcases hy with rfl | rfl
                · exact pigeonFixed_of_hole hlh
                · exact pigeonFixed_of_hole hrh
                · exact pigeonFixed_of_hole hlh
                · exact pigeonFixed_of_hole hrh
              have heq := Finset.eq_of_subset_of_card_le hsub (by simp [c_r.ordered.ne]; exact hfp_o)
              have hmem : ∀ x, pigeonFixed (State.grant ρ {v} (!s)) x → x = c_r.left ∨ x = c_r.right := fun x hx => by
                simpa using (heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩ : x ∈ ({c_r.left, c_r.right} : Finset (Fin 5)))
              have hpair : u = c_r.left ∧ w = c_r.right := by
                rcases hmem u (pigeonFixed_of_some hu') with rfl | rfl <;>
                  rcases hmem w (pigeonFixed_of_some hw') with rfl | rfl
                · exact (huw.ne rfl).elim
                · exact ⟨rfl, rfl⟩
                · exact (not_lt_of_gt c_r.ordered huw).elim
                · exact (huw.ne rfl).elim
              obtain ⟨rfl, rfl⟩ := hpair
              have hbits_eq : bits c_r.hole b' = val' ∧ bits c_twin.hole b' = val' := by
                rcases hholes_o with ⟨hlh, hrh⟩ | ⟨hlh, hrh⟩
                · exact ⟨Option.some.inj ((pigeonHole_bit hlh b').symm.trans hu'),
                         Option.some.inj ((pigeonHole_bit hrh b').symm.trans hw')⟩
                · exact ⟨Option.some.inj ((pigeonHole_bit hrh b').symm.trans hw'),
                         Option.some.inj ((pigeonHole_bit hlh b').symm.trans hu')⟩
              have hcne : c_r ≠ c_twin := fun e => hne_holes (congrArg Collision.hole e)
              have hsub2 : ({c_r, c_twin} : Finset Collision) ⊆ pairHoles c_r.left c_r.right b' val' ∩ {c_r, c_twin} := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simpa using hx⟩
                rcases hx with rfl | rfl
                · exact ⟨rfl, rfl, hbits_eq.1⟩
                · exact ⟨ht_l, ht_r, hbits_eq.2⟩
              have := Finset.card_le_card hsub2; simp [hcne] at this; exact this
            unfold leafWeight
            by_cases h3' : ∃ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' ∧ Disjoint (pairHoles u w b' val') {c_r, c_twin}
            · obtain ⟨u, w, b', val', hsp', hdj⟩ := h3'
              have := hcard2 u w b' val' hsp'; rw [Finset.disjoint_iff_inter_eq_empty.mp hdj] at this; simp at this
            · rw [ite_eq_right h3']
              by_cases h4' : ∃ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' ∧ (pairHoles u w b' val' ∩ {c_r, c_twin}).card ≤ 1
              · obtain ⟨u, w, b', val', hsp', hcd⟩ := h4'
                have := hcard2 u w b' val' hsp'; omega
              · rw [ite_eq_right h4']
          have hbound := dValid_b0_ext_bound (ρ1 := State.grant ρ {v} (!s)) hd_pair hv_o hp_o hk0_o (State.Le.refl _)
            (fun j ρ_leaf h1 h2 hc => by
              rcases hholes_o with ⟨hlh, hrh⟩ | ⟨hlh, hrh⟩
              · exact hw1 j ρ_leaf h1 ⟨h2 _ _ hlh.1, h2 _ _ hlh.2⟩ ⟨h2 _ _ hrh.1, h2 _ _ hrh.2⟩ hc
              · exact hw2 j ρ_leaf h1 ⟨h2 _ _ hlh.1, h2 _ _ hlh.2⟩ ⟨h2 _ _ hrh.1, h2 _ _ hrh.2⟩ hc)
          omega
        rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by
              have := congrArg List.length hm; simp at this; omega) with ⟨er, el⟩ | ⟨er, el⟩
        · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
          have hrm : dMarks keyAt r = [c_r] := by simpa [hl0] using hm
          have := handle_none false l (hrm ▸ dValid_shared hr) hl (by omega) hl0 hwtl hwtl'
          simp only [dPhi] at this; omega
        · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
          have hlm : dMarks keyAt l = [c_r] := by simpa [hr0] using hm
          have := handle_none true r (hlm ▸ dValid_shared hl) hr (by omega) hr0 hwtr hwtr'
          simp only [dPhi] at this; omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by
            have := congrArg List.length hm; simp at this; omega) with ⟨er, el⟩ | ⟨er, el⟩
      · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
        have hrm : dMarks keyAt r = [c_r] := by simpa [hl0] using hm
        have := ihr (by omega) hrm (by rw [grant_nonsingle hns false]; exact hfb3)
          (by rw [grant_nonsingle hns false]; exact hnc) (by rw [grant_nonsingle hns false]; exact hsp) hwtr hwtr'
        omega
      · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
        have hlm : dMarks keyAt l = [c_r] := by simpa [hr0] using hm
        have := ihl (by omega) hlm (by rw [grant_nonsingle hns true]; exact hfb3)
          (by rw [grant_nonsingle hns true]; exact hnc) (by rw [grant_nonsingle hns true]; exact hsp) hwtl hwtl'
        omega

omit [DecidableEq I] in
theorem dValid_k2_weak_ge_16 {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hk2 : (dMarks keyAt t).length = 2) (hw : 1 ≤ dWeaks t) : 16 ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk2
  | axRep => simp [dMarks] at hk2
  | exitDer => simp [dMarks] at hk2
  | weak i ρ ρ' t _ ht _ =>
    have hb := dValid_req_bound hd ht
    simp only [dMarks, dPhi, exitWeightSum, dAxReps, dWeaks] at hk2 hb ⊢
    rw [hk2] at hb; simp only [req] at hb; split_ifs at hb <;> omega
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dMarks, List.length_append, dWeaks, dPhi, exitWeightSum, dAxReps] at hk2 hw ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
        ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
        ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
        ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
    · by_cases hwr : 1 ≤ dWeaks r
      · have := ihr er hwr; omega
      · rw [er] at br; simp only [req] at br; split_ifs at br <;> omega
    · by_cases hwl : 1 ≤ dWeaks l
      · have := ihl el hwl; omega
      · rw [el] at bl; simp only [req] at bl; split_ifs at bl <;> omega
    · -- (1, 1) split: one side has dWeaks ≥ 1 (so dPhi ≥ 10), and the OTHER side has req 1 ≥ 6!
      rcases hrm : dMarks keyAt r with _ | ⟨c₁, r0⟩; · simp [hrm] at er
      rcases hlm : dMarks keyAt l with _ | ⟨c₂, l0⟩; · simp [hlm] at el
      have hr0 : r0 = [] := by simpa [hrm] using er
      have hl0 : l0 = [] := by simpa [hlm] using el
      subst hr0; subst hl0
      have hne : c₁.hole ≠ c₂.hole := by simp [hrm, hlm] at nd; exact nd
      have hsub : ∀ c ∈ dMarks keyAt r ++ dMarks keyAt l, c ∈ ow := fun c hc =>
        (List.mem_append.mp hc).elim (dValid_marks_subset hr c) (dValid_marks_subset hl c)
      have hb6_ρ := shared_pair_b0_six hs (by simp [hrm]) (by simp [hlm]) hne
        (hsub c₁ (by simp [hrm])) (hsub c₂ (by simp [hlm]))
      have hstruc := shared_pair_structure hs (by simp [hrm]) (by simp [hlm]) hne
      have hfb_le2 : fixedBits ρ ≤ 2 := hstruc.1
      have hside_ge6 : 6 ≤ req 1 (State.grant ρ f false) ow ∧ 6 ≤ req 1 (State.grant ρ f true) ow := by
        by_cases hsing : ∃ v : Variable, f = {v}
        · obtain ⟨v, rfl⟩ := hsing
          cases hrv : ρ v with
          | some side =>
            cases side
            · exfalso
              have hf := hs v false hrv c₂ (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c₂ (by simp [hlm]) 0
              rw [hf] at ht; cases ht
            · exfalso
              have ht := hs v true hrv c₁ (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c₁ (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          | none =>
            have hfb0 : fixedBits (State.grant ρ {v} false) = fixedBits ρ + 1 := fixedBits_grant_none hrv false
            have hfb1 : fixedBits (State.grant ρ {v} true) = fixedBits ρ + 1 := fixedBits_grant_none hrv true
            by_cases h0 : fixedBits ρ = 0
            · rw [req_one_of_fixedBits_le_one (by omega : fixedBits (State.grant ρ {v} false) ≤ 1),
                  req_one_of_fixedBits_le_one (by omega : fixedBits (State.grant ρ {v} true) ≤ 1)]; omega
            by_cases h1 : fixedBits ρ = 1
            · have h10 : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
                  req 1 (State.grant ρ {v} s) ow = 10 := by
                intro s c hsc
                have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hrv s, h1]
                have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
                have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
                have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
                  intro w hw' ew
                  cases hww : ρ w with
                  | none => exact (hw' hww).elim
                  | some valw =>
                    have e1' := (signedShared_const (c := c₁) hs (by simp [hrm]) hww).2
                    have e2' := (signedShared_const (c := c₂) hs (by simp [hlm]) hww).2
                    have ev1 := (signedShared_const (c := c₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)).2
                    have ev2 := (signedShared_const (c := c₂) (dValid_shared hl) (by simp [hlm]) (grant_apply_self ρ v true)).2
                    rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
                    have := e1'.symm.trans e2'; cases this
                have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
                  rintro u w b' val' ⟨huw, hu', hw'⟩
                  by_cases e1' : (u, b') = v
                  · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
                    rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                    exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
                  · by_cases e2' : (w, b') = v
                    · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                      exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
                    · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'; rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                      have hsub' : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                        rcases hx with rfl | rfl <;> simp [hu', hw']
                      have hc := Finset.card_le_card hsub'
                      simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                      change 2 ≤ fixedBits ρ at hc; omega
                have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
                simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
              rw [h10 false c₁ (hrm ▸ dValid_shared hr), h10 true c₂ (hlm ▸ dValid_shared hl)]; omega
            · have h2 : fixedBits ρ = 2 := by omega
              obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 h2
              have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
              have hfilt : Finset.univ.filter (fun w : Variable => ρ w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
                symm; apply Finset.eq_of_subset_of_card_le
                · intro w hw'; simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  rcases hw' with rfl | rfl <;> simp [hlb', hrb']
                · simp [hne_lr]; exact h2.le
              have h6 : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
                  req 1 (State.grant ρ {v} s) ow = 6 := by
                intro s c hsc
                have hfbs : fixedBits (State.grant ρ {v} s) = 3 := by rw [fixedBits_grant_none hrv s, h2]
                have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
                have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
                have hvb_ne : v.2 ≠ b' := by
                  intro e
                  have hvc := signedShared_const (c := c₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)
                  have hm : v ∈ Finset.univ.filter (fun w => ρ w ≠ none) := by
                    rw [hfilt]; simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases hvc.1 with h1' | h1'; left; exact Prod.ext h1' e; right; exact Prod.ext h1' e
                  exact (Finset.mem_filter.mp hm).2 hrv
                have hsame_imp : ∀ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' → sameBitPair ρ u w b'' val'' := by
                  intro u w b'' val'' ⟨huw, hu', hw'⟩
                  have hb'' : b'' = b' := by
                    by_contra hne'
                    have hu_v : (u, b'') = v := by
                      by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hu'
                      have hm : (u, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
                      rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e <;> exact hne' (congrArg Prod.snd e)
                    have hw_v : (w, b'') = v := by
                      by_contra hnv; rw [grant_apply_ne ρ (Ne.symm hnv)] at hw'
                      have hm : (w, b'') ∈ Finset.univ.filter (fun x => ρ x ≠ none) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
                      rw [hfilt] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e <;> exact hne' (congrArg Prod.snd e)
                    exact huw.ne (congrArg Prod.fst (hu_v.trans hw_v.symm))
                  subst b''
                  exact ⟨huw, by rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hu',
                              by rwa [grant_apply_ne ρ (fun e => hvb_ne (congrArg Prod.snd e))] at hw'⟩
                have hlw6 : leafWeight ρ ow = 6 := by
                  have hnc_ρ := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits ρ ≤ 3)
                  rw [b0_of_fp_le_two hnc_ρ (fixedPigeons_le_two_of_shared (c := c₁) hs (by simp [hrm]))] at hb6_ρ
                  exact hb6_ρ
                have hlw_s : leafWeight (State.grant ρ {v} s) ow = 6 := by
                  unfold leafWeight at hlw6 ⊢
                  by_cases h3' : ∃ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
                  · obtain ⟨u, w, b'', val'', hsp', hdj⟩ := h3'
                    rw [ite_eq_left ⟨u, w, b'', val'', hsame_imp u w b'' val'' hsp', hdj⟩] at hlw6; omega
                  · rw [ite_eq_right h3']
                    by_cases h4' : ∃ u w b'' val'', sameBitPair (State.grant ρ {v} s) u w b'' val'' ∧ (pairHoles u w b'' val'' ∩ ow).card ≤ 1
                    · obtain ⟨u, w, b'', val'', hsp', hcd⟩ := h4'
                      by_cases h3ρ : ∃ u w b'' val'', sameBitPair ρ u w b'' val'' ∧ Disjoint (pairHoles u w b'' val'') ow
                      · rw [ite_eq_left h3ρ] at hlw6; omega
                      · rw [ite_eq_right h3ρ, ite_eq_left ⟨u, w, b'', val'', hsame_imp u w b'' val'' hsp', hcd⟩] at hlw6; omega
                    · rw [ite_eq_right h4']
                simp only [req, ite_eq_right hnc_s, ite_eq_left (by omega : 3 ≤ fixedBits (State.grant ρ {v} s))]
                rw [b0_of_fp_le_two hnc_s hfp_s, hlw_s]
              rw [h6 false c₁ (hrm ▸ dValid_shared hr), h6 true c₂ (hlm ▸ dValid_shared hl)]; omega
        · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
          rw [grant_nonsingle hns false, grant_nonsingle hns true]
          have hnc_ρ := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits ρ ≤ 3)
          simp only [req, ite_eq_right hnc_ρ, ite_eq_right (show ¬ 3 ≤ fixedBits ρ by omega), hb6_ρ]; omega
      rw [er] at br; rw [el] at bl; omega

omit [DecidableEq I] in
theorem dValid_k2_d1_weak_ge_20 {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hk2 : (dMarks keyAt t).length = 2) (hfb1 : fixedBits ρ ≤ 1) (hw : 1 ≤ dWeaks t) :
    20 ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk2
  | axRep => simp [dMarks] at hk2
  | exitDer => simp [dMarks] at hk2
  | weak i ρ ρ' t _ ht _ =>
    have hb := dValid_req_bound hd ht
    simp only [dMarks, dPhi, exitWeightSum, dAxReps, dWeaks] at hk2 hb ⊢
    rw [hk2] at hb; simp only [req] at hb; split_ifs at hb <;> omega
  | res i f ρ l r nd hs hl hr ihl ihr =>
    simp only [dMarks, List.length_append, dWeaks, dPhi, exitWeightSum, dAxReps] at hk2 hw ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have er : (dMarks keyAt r).length = 2 := by simp [hl0] at hk2; exact hk2
          by_cases hwr : 1 ≤ dWeaks r
          · have := ihr er (by rw [e0]; exact hfb1) hwr; omega
          · rw [er, e0] at br; simp only [req] at br; split_ifs at br <;> omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have el : (dMarks keyAt l).length = 2 := by simp [hr0] at hk2; exact hk2
          by_cases hwl : 1 ≤ dWeaks l
          · have := ihl el (by rw [e1]; exact hfb1) hwl; omega
          · rw [el, e1] at bl; simp only [req] at bl; split_ifs at bl <;> omega
      | none =>
        have hfb0 : fixedBits (State.grant ρ {v} false) = fixedBits ρ + 1 := fixedBits_grant_none hrv false
        have hfb1' : fixedBits (State.grant ρ {v} true) = fixedBits ρ + 1 := fixedBits_grant_none hrv true
        rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
            ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
            ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
        · by_cases hwr : 1 ≤ dWeaks r
          · have hr16 := dValid_k2_weak_ge_16 hd hr er hwr; simp only [dPhi] at hr16
            have hb6_l : b0 (State.grant ρ {v} true) ow = 6 := by
              by_cases h0 : fixedBits ρ = 0
              · exact b0_eq_six_of_fixedBits_le_one (by omega)
              · have h1 : fixedBits ρ = 1 := by omega
                rcases hrm : dMarks keyAt r with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hrm] at er
                subst er
                have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
                have hne : c₁.hole ≠ c₂.hole := by simp [hrm, hl0] at nd; exact nd
                have hss : SignedShared [c₁, c₂] (State.grant ρ {v} false) := hrm ▸ dValid_shared hr
                have hstruc := shared_pair_structure hss (by simp) (by simp) hne
                obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 (by omega)
                have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
                have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
                  symm; apply Finset.eq_of_subset_of_card_le
                  · intro w hw'; simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hw' with rfl | rfl <;> simp [hlb', hrb']
                  · simp [hne_lr]; change fixedBits (State.grant ρ {v} false) ≤ 2; omega
                have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                  rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
                have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
                  ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  by_cases hwv : w = v
                  · subst hwv; simp [grant_apply_self, hvm]
                  · rw [grant_apply_ne ρ (Ne.symm hwv) true, ← grant_apply_ne ρ (Ne.symm hwv) false]
                    have : (State.grant ρ {v} false w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                    exact this
                have hfp_o : fixedPigeons (State.grant ρ {v} true) ≤ 2 := by
                  have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} true)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                    · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                        rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                    · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                        rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                  exact (Finset.card_le_card hsub).trans Finset.card_le_two
                have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} true) ≤ 3)
                have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} true) u w b'' val'' := by
                  rintro u w b'' val'' ⟨huw, hu', hw'⟩
                  have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
                  have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
                  have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                    rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                    · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                    · exact ⟨e1, e2⟩
                    · have e1' : u = c₁.right := congrArg Prod.fst e1
                      have e2' : w = c₁.left := congrArg Prod.fst e2
                      rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                    · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                  rw [hpair.1] at hu'; rw [hpair.2] at hw'
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
                  rcases hvm with rfl | rfl
                  · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                    have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                    have hl_eq : bits c₁.hole b' = false := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') false))
                    rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                    rw [← e1] at e2; cases e2
                  · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                    have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                    have hr_eq : bits c₁.hole b' = false := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') false))
                    rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                    rw [← e1] at e2; cases e2
                exact b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
            rw [el] at bl; simp only [req, hb6_l] at bl; omega
          · rw [er] at br; simp only [req] at br; split_ifs at br <;> omega
        · by_cases hwl : 1 ≤ dWeaks l
          · have hl16 := dValid_k2_weak_ge_16 hd hl el hwl; simp only [dPhi] at hl16
            have hb6_r : b0 (State.grant ρ {v} false) ow = 6 := by
              by_cases h0 : fixedBits ρ = 0
              · exact b0_eq_six_of_fixedBits_le_one (by omega)
              · have h1 : fixedBits ρ = 1 := by omega
                rcases hlm : dMarks keyAt l with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [hlm] at el
                subst el
                have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
                have hne : c₁.hole ≠ c₂.hole := by simp [hlm, hr0] at nd; exact nd
                have hss : SignedShared [c₁, c₂] (State.grant ρ {v} true) := hlm ▸ dValid_shared hl
                have hstruc := shared_pair_structure hss (by simp) (by simp) hne
                obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 (by omega)
                have hne_lr : (c₁.left, b') ≠ (c₁.right, b') := fun e => c₁.ordered.ne (congrArg Prod.fst e)
                have hfilts : Finset.univ.filter (fun w : Variable => State.grant ρ {v} true w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
                  symm; apply Finset.eq_of_subset_of_card_le
                  · intro w hw'; simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hw' with rfl | rfl <;> simp [hlb', hrb']
                  · simp [hne_lr]; change fixedBits (State.grant ρ {v} true) ≤ 2; omega
                have hvm : v ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                  rw [← hfilts]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [grant_apply_self]⟩
                have hfilto : Finset.univ.filter (fun w : Variable => State.grant ρ {v} false w ≠ none) = {(c₁.left, b'), (c₁.right, b')} := by
                  ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  by_cases hwv : w = v
                  · subst hwv; simp [grant_apply_self, hvm]
                  · rw [grant_apply_ne ρ (Ne.symm hwv) false, ← grant_apply_ne ρ (Ne.symm hwv) true]
                    have : (State.grant ρ {v} true w ≠ none) ↔ w ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by rw [← hfilts]; simp
                    exact this
                have hfp_o : fixedPigeons (State.grant ρ {v} false) ≤ 2 := by
                  have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} false)) ⊆ ({c₁.left, c₁.right} : Finset (Fin 5)) := by
                    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases (Finset.mem_filter.mp hp).2 with h0' | h1'
                    · have hm : (p, (0 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                        rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                    · have hm : (p, (1 : Fin 2)) ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                        rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                      rcases hm with e | e; left; exact congrArg Prod.fst e; right; exact congrArg Prod.fst e
                  exact (Finset.card_le_card hsub).trans Finset.card_le_two
                have hnc_o := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} false) ≤ 3)
                have hno_o : ∀ u w b'' val'', ¬ sameBitPair (State.grant ρ {v} false) u w b'' val'' := by
                  rintro u w b'' val'' ⟨huw, hu', hw'⟩
                  have hum : (u, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu']⟩
                  have hwm : (w, b'') ∈ ({(c₁.left, b'), (c₁.right, b')} : Finset Variable) := by
                    rw [← hfilto]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hw']⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hum hwm
                  have hpair : (u, b'') = (c₁.left, b') ∧ (w, b'') = (c₁.right, b') := by
                    rcases hum with e1 | e1 <;> rcases hwm with e2 | e2
                    · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                    · exact ⟨e1, e2⟩
                    · have e1' : u = c₁.right := congrArg Prod.fst e1
                      have e2' : w = c₁.left := congrArg Prod.fst e2
                      rw [e1', e2'] at huw; exact (not_lt_of_gt c₁.ordered huw).elim
                    · exact (huw.ne (congrArg Prod.fst (e1.trans e2.symm))).elim
                  rw [hpair.1] at hu'; rw [hpair.2] at hw'
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hvm
                  rcases hvm with rfl | rfl
                  · rw [grant_apply_self] at hu'; rw [grant_apply_ne ρ hne_lr] at hw'
                    have hr_eq : ρ (c₁.right, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr] at hrb'
                    have hl_eq : bits c₁.hole b' = true := Option.some.inj (hlb'.symm.trans (grant_apply_self ρ (c₁.left, b') true))
                    rw [hr_eq, hl_eq] at hw'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                    rw [← e1] at e2; cases e2
                  · rw [grant_apply_self] at hw'; rw [grant_apply_ne ρ hne_lr.symm] at hu'
                    have hl_eq : ρ (c₁.left, b') = some (bits c₁.hole b') := by rwa [grant_apply_ne ρ hne_lr.symm] at hlb'
                    have hr_eq : bits c₁.hole b' = true := Option.some.inj (hrb'.symm.trans (grant_apply_self ρ (c₁.right, b') true))
                    rw [hl_eq, hr_eq] at hu'; have e1 := Option.some.inj hu'; have e2 := Option.some.inj hw'
                    rw [← e1] at e2; cases e2
                exact b0_eq_six_of_no_sameBitPair (ow := ow) hnc_o hfp_o hno_o
            rw [er] at br; simp only [req, hb6_r] at br; omega
          · rw [el] at bl; simp only [req] at bl; split_ifs at bl <;> omega
        · -- (1, 1) from fixedBits ≤ 1 gives 10 + 10 = 20!
          by_cases h0 : fixedBits ρ = 0
          · rw [er, req_one_of_fixedBits_le_one (by omega : fixedBits (State.grant ρ {v} false) ≤ 1)] at br
            rw [el, req_one_of_fixedBits_le_one (by omega : fixedBits (State.grant ρ {v} true) ≤ 1)] at bl
            omega
          · have h1 : fixedBits ρ = 1 := by omega
            rcases hrm : dMarks keyAt r with _ | ⟨c₁, r0⟩; · simp [hrm] at er
            rcases hlm : dMarks keyAt l with _ | ⟨c₂, l0⟩; · simp [hlm] at el
            have hr0 : r0 = [] := by simpa [hrm] using er
            have hl0 : l0 = [] := by simpa [hlm] using el
            subst hr0; subst hl0
            have h10 : ∀ (s : Bool) (c : Collision), SignedShared [c] (State.grant ρ {v} s) →
                req 1 (State.grant ρ {v} s) ow = 10 := by
              intro s c hsc
              have hfbs : fixedBits (State.grant ρ {v} s) = 2 := by rw [fixedBits_grant_none hrv s, h1]
              have hnc_s := not_hasCollision_of_fixedBits_le_three (by omega : fixedBits (State.grant ρ {v} s) ≤ 3)
              have hfp_s := fixedPigeons_le_two_of_shared (c := c) hsc (by simp)
              have hvb_ne : ∀ w, ρ w ≠ none → w.2 ≠ v.2 := by
                intro w hw' ew
                cases hww : ρ w with
                | none => exact (hw' hww).elim
                | some valw =>
                  have e1' := (signedShared_const (c := c₁) hs (by simp [hrm]) hww).2
                  have e2' := (signedShared_const (c := c₂) hs (by simp [hlm]) hww).2
                  have ev1 := (signedShared_const (c := c₁) (dValid_shared hr) (by simp [hrm]) (grant_apply_self ρ v false)).2
                  have ev2 := (signedShared_const (c := c₂) (dValid_shared hl) (by simp [hlm]) (grant_apply_self ρ v true)).2
                  rw [ew, ← ev1] at e1'; rw [ew, ← ev2] at e2'
                  have := e1'.symm.trans e2'; cases this
              have hno_sp : ∀ u w b' val', ¬ sameBitPair (State.grant ρ {v} s) u w b' val' := by
                rintro u w b' val' ⟨huw, hu', hw'⟩
                by_cases e1' : (u, b') = v
                · have e2' : (w, b') ≠ v := fun e => huw.ne (congrArg Prod.fst (e1'.trans e.symm))
                  rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                  exact hvb_ne (w, b') (by simp [hw']) (congrArg Prod.snd e1' : b' = v.2)
                · by_cases e2' : (w, b') = v
                  · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'
                    exact hvb_ne (u, b') (by simp [hu']) (congrArg Prod.snd e2' : b' = v.2)
                  · rw [grant_apply_ne ρ (Ne.symm e1')] at hu'; rw [grant_apply_ne ρ (Ne.symm e2')] at hw'
                    have hsub' : ({(u, b'), (w, b')} : Finset Variable) ⊆ Finset.univ.filter (fun x => ρ x ≠ none) := by
                      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                      rcases hx with rfl | rfl <;> simp [hu', hw']
                    have hc := Finset.card_le_card hsub'
                    simp [show (u, b') ≠ (w, b') from fun e => huw.ne (congrArg Prod.fst e)] at hc
                    change 2 ≤ fixedBits ρ at hc; omega
              have hb6 := b0_eq_six_of_no_sameBitPair (ow := ow) hnc_s hfp_s hno_sp
              simp only [req, ite_eq_right hnc_s, ite_eq_right (show ¬ 3 ≤ fixedBits (State.grant ρ {v} s) by omega), hb6]; omega
            rw [er, h10 false c₁ (hrm ▸ dValid_shared hr)] at br
            rw [el, h10 true c₂ (hlm ▸ dValid_shared hl)] at bl
            omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl ihl; rw [grant_nonsingle hns false] at br ihr
      rcases (show ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 2) ∨
          ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 1) by omega) with
          ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
      · by_cases hwr : 1 ≤ dWeaks r
        · have := ihr er hfb1 hwr; omega
        · rw [er] at br; simp only [req] at br; split_ifs at br <;> omega
      · by_cases hwl : 1 ≤ dWeaks l
        · have := ihl el hfb1 hwl; omega
        · rw [el] at bl; simp only [req] at bl; split_ifs at bl <;> omega
      · rw [er, req_one_of_fixedBits_le_one hfb1] at br
        rw [el, req_one_of_fixedBits_le_one hfb1] at bl; omega

omit [DecidableEq I] in
theorem dValid_k4_weak_ge_38 {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hk4 : (dMarks keyAt t).length = 4) (hw : 1 ≤ dWeaks t) : 38 ≤ dPhi wt t := by
  induction hv with
  | axUniq => simp [dMarks] at hk4
  | axRep => simp [dMarks] at hk4
  | exitDer => simp [dMarks] at hk4
  | weak i ρ ρ' t _ ht _ =>
    have hb := dValid_req_bound hd ht
    simp only [dMarks, dPhi, exitWeightSum, dAxReps, dWeaks] at hk4 hb ⊢
    rw [hk4] at hb; simp only [req] at hb; omega
  | res i f ρ l r nd hs hl hr ihl ihr =>
    have hem := signedShared_three nd (by simp only [dMarks] at hk4; omega) hs
    subst ρ
    simp only [dMarks, List.length_append, dWeaks, dPhi, exitWeightSum, dAxReps] at hk4 hw ihl ihr ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      have hfb0 : fixedBits (State.grant State.empty {v} false) = 1 := by
        rw [fixedBits_grant_none rfl false, fixedBits_empty]
      have hfb1 : fixedBits (State.grant State.empty {v} true) = 1 := by
        rw [fixedBits_grant_none rfl true, fixedBits_empty]
      have hne0 : State.grant State.empty {v} false ≠ State.empty := fun e => by
        have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
      have hne1 : State.grant State.empty {v} true ≠ State.empty := fun e => by
        have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
      have hnd0 : ((dMarks keyAt r).map Collision.hole).Nodup := dValid_nodup hr
      have hnd1 : ((dMarks keyAt l).map Collision.hole).Nodup := dValid_nodup hl
      have hle20 : (dMarks keyAt r).length ≤ 2 := by
        by_contra h3; exact hne0 (signedShared_three hnd0 (by omega) (dValid_shared hr))
      have hle21 : (dMarks keyAt l).length ≤ 2 := by
        by_contra h3; exact hne1 (signedShared_three hnd1 (by omega) (dValid_shared hl))
      have er : (dMarks keyAt r).length = 2 := by omega
      have el : (dMarks keyAt l).length = 2 := by omega
      by_cases hwr : 1 ≤ dWeaks r
      · have hr20 := dValid_k2_d1_weak_ge_20 hd hr er (by omega) hwr
        rw [el] at bl; simp only [req, hfb1] at bl; split_ifs at bl <;> simp only [dPhi] at hr20 <;> omega
      · have hl20 := dValid_k2_d1_weak_ge_20 hd hl el (by omega) (by omega)
        rw [er] at br; simp only [req, hfb0] at br; split_ifs at br <;> simp only [dPhi] at hl20 <;> omega
    · have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl; rw [grant_nonsingle hns false] at br
      rcases (show ((dMarks keyAt r).length = 4 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 3 ∧ (dMarks keyAt l).length = 1) ∨
          ((dMarks keyAt r).length = 2 ∧ (dMarks keyAt l).length = 2) ∨
          ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 3) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 4) by omega) with
          ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
      · by_cases hwr : 1 ≤ dWeaks r
        · have := ihr er hwr; omega
        · rw [er] at br; simp only [req] at br; omega
      · rw [er] at br; rw [el, req_one_of_fixedBits_le_one (by rw [fixedBits_empty]; omega)] at bl
        simp only [req] at br; omega
      · rw [er] at br; rw [el] at bl; simp [req, fixedBits_empty] at br bl; omega
      · rw [el] at bl; rw [er, req_one_of_fixedBits_le_one (by rw [fixedBits_empty]; omega)] at br
        simp only [req] at bl; omega
      · by_cases hwl : 1 ≤ dWeaks l
        · have := ihl el hwl; omega
        · rw [el] at bl; simp only [req] at bl; omega

/-- If an `H1_d3` pure tree has `dPhi ≤ 4`, it must have `e = 1, a = 0` and its single exit has `wt = 4`. -/
theorem dValid_h1_d3_phi_four {stAt : I → State} {keyAt : I → Collision}
    {ow : Finset Collision} {wt : I → ℕ} {ρ : State} {t : Dag.DTree Variable I}
    (hd : DistinctHoles ow) (hv : DValid stAt keyAt ow wt ρ t)
    (hpure : dWeaks t = 0) {c_r : Collision} (hm : dMarks keyAt t = [c_r])
    (hfb3 : fixedBits ρ = 3) (hnc : ¬ hasCollision ρ)
    (hwt3 : ∀ j, countExit j t ≥ 1 → 3 ≤ wt j) (hphi4 : dPhi wt t ≤ 4) :
    dExits t = 1 ∧ dAxReps t = 0 ∧ ∃ q : I, countExit q t = 1 ∧ wt q = 4 := by
  have hcow : c_r ∈ ow := dValid_marks_subset hv c_r (by simp [hm])
  have hzero_empty : ∀ (t0 : Dag.DTree Variable I), dWeaks t0 = 0 →
      (∀ j, countExit j t0 ≥ 1 → 3 ≤ wt j) → dPhi wt t0 = 0 → dExits t0 = 0 ∧ dAxReps t0 = 0 ∧ ∀ q, countExit q t0 = 0 := by
    intro t0 hp0 hw3 h0
    induction t0 with
    | axUniq => simp [dExits, dAxReps, countExit]
    | axRep => simp [dPhi, dAxReps] at h0
    | exitDer j =>
      have := hw3 j (by simp [countExit]); simp [dPhi, exitWeightSum] at h0; omega
    | weak => simp [dWeaks] at hp0
    | res _ _ l r ihl ihr =>
      simp only [dWeaks, dPhi, exitWeightSum, dAxReps, dExits, countExit] at hp0 h0 ⊢
      have hl := ihl (by omega) (fun j hj => hw3 j (by simp [countExit]; omega)) (by simp only [dPhi]; omega)
      have hr := ihr (by omega) (fun j hj => hw3 j (by simp [countExit]; omega)) (by simp only [dPhi]; omega)
      exact ⟨by omega, by omega, fun q => by have := hl.2.2 q; have := hr.2.2 q; omega⟩
  cases hv with
  | axUniq i ρ hc _ _ => exact (hnc hc).elim
  | axRep => simp [dMarks] at hm
  | exitDer => simp [dMarks] at hm
  | weak => simp [dWeaks] at hpure
  | res i f ρ l r nd hs hl hr =>
    simp only [dWeaks, dMarks, dPhi, exitWeightSum, dAxReps, dExits, countExit] at hpure hm hphi4 ⊢
    have bl := dValid_req_bound hd hl; have br := dValid_req_bound hd hr; simp only [dPhi] at bl br
    have hb4_ρ := shared_single_b0_ge_four (by simpa [hm] using hs) (by simp) hcow hnc
    have hreq4 : req 1 ρ ow ≥ 4 := by simp only [req, ite_eq_right hnc, ite_eq_left (by omega : 3 ≤ fixedBits ρ)]; exact hb4_ρ
    by_cases hsing : ∃ v : Variable, f = {v}
    · obtain ⟨v, rfl⟩ := hsing
      cases hrv : ρ v with
      | some side =>
        -- Override: matching side has req 1 ≥ 4, other side has b0 ≥ 1 -> sum ≥ 5, contradicting hphi4!
        exfalso
        cases side
        · have e0 : State.grant ρ {v} false = ρ := grant_eq_self hrv
          have hl0 : dMarks keyAt l = [] := by
            cases hlm : dMarks keyAt l with
            | nil => rfl
            | cons c rest =>
              have hf := hs v false hrv c (by simp [hlm]) 0
              have ht := (dValid_shared hl) v true (grant_apply_self ρ v true) c (by simp [hlm]) 0
              rw [hf] at ht; cases ht
          have hrm : dMarks keyAt r = [c_r] := by simpa [hl0] using hm
          rw [hrm, e0] at br; rw [hl0] at bl
          simp only [List.length_singleton, List.length_nil] at br bl; simp only [req] at bl
          have := b0_ge_one (State.grant ρ {v} true) ow; omega
        · have e1 : State.grant ρ {v} true = ρ := grant_eq_self hrv
          have hr0 : dMarks keyAt r = [] := by
            cases hrm : dMarks keyAt r with
            | nil => rfl
            | cons c rest =>
              have ht := hs v true hrv c (by simp [hrm]) 0
              have hf := (dValid_shared hr) v false (grant_apply_self ρ v false) c (by simp [hrm]) 0
              rw [ht] at hf; cases hf
          have hlm : dMarks keyAt l = [c_r] := by simpa [hr0] using hm
          rw [hlm, e1] at bl; rw [hr0] at br
          simp only [List.length_singleton, List.length_nil] at br bl; simp only [req] at br
          have := b0_ge_one (State.grant ρ {v} false) ow; omega
      | none =>
        -- Helper: for the 0-side t_o at ρ_o (with fixedPigeons ≤ 2, 2 distinct holes occupied, b0 ≥ 4),
        -- if dPhi t_o ≤ 4 then t_o MUST be `.exitDer q` with wt q = 4!
        have handle_o : ∀ (s : Bool) (t_s t_o : Dag.DTree Variable I),
            SignedShared [c_r] (State.grant ρ {v} s) →
            DValid stAt keyAt ow wt (State.grant ρ {v} (!s)) t_o →
            dWeaks t_s = 0 → dWeaks t_o = 0 → dMarks keyAt t_o = [] →
            (∀ j, countExit j t_s ≥ 1 → 3 ≤ wt j) →
            dPhi wt t_s + dPhi wt t_o ≤ 4 →
            dExits t_s + dExits t_o = 1 ∧ dAxReps t_s + dAxReps t_o = 0 ∧
            ∃ q : I, countExit q t_s + countExit q t_o = 1 ∧ wt q = 4 := by
          intro s t_s t_o hss hv_o hp_s hp_o hk0_o hw3s hsum
          have hvc := signedShared_const (c := c_r) hss (by simp) (grant_apply_self ρ v s)
          have hfb_s : fixedBits (State.grant ρ {v} s) = 4 := by rw [fixedBits_grant_none hrv s, hfb3]
          -- Show ¬ hasCollision (grant ρ {v} !s) and fixedPigeons ≤ 2 and 4 ≤ b0 (grant ρ {v} !s) ow!
          have hfp_o : fixedPigeons (State.grant ρ {v} (!s)) ≤ 2 := by
            have hsub : Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) ⊆ ({c_r.left, c_r.right} : Finset (Fin 5)) := by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases (Finset.mem_filter.mp hp).2 with h0 | h1
              · cases hw' : State.grant ρ {v} (!s) (p, 0) with
                | none => exact (h0 hw').elim
                | some val =>
                  by_cases he : (p, (0 : Fin 2)) = v
                  · rw [← congrArg Prod.fst he] at hvc; exact hvc.1
                  · rw [grant_apply_ne ρ (Ne.symm he)] at hw'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').1
              · cases hw' : State.grant ρ {v} (!s) (p, 1) with
                | none => exact (h1 hw').elim
                | some val =>
                  by_cases he : (p, (1 : Fin 2)) = v
                  · rw [← congrArg Prod.fst he] at hvc; exact hvc.1
                  · rw [grant_apply_ne ρ (Ne.symm he)] at hw'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').1
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
          have hnc_o : ¬ hasCollision (State.grant ρ {v} (!s)) := by
            rintro ⟨u, w, huw, h, hu, hw'⟩
            have huf : u = c_r.left ∨ u = c_r.right := by
              by_cases e : (u, (0 : Fin 2)) = v
              · rw [← congrArg Prod.fst e] at hvc; exact hvc.1
              · have := hu.1; rw [grant_apply_ne ρ (Ne.symm e)] at this
                exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) this).1
            have hwf : w = c_r.left ∨ w = c_r.right := by
              by_cases e : (w, (0 : Fin 2)) = v
              · rw [← congrArg Prod.fst e] at hvc; exact hvc.1
              · have := hw'.1; rw [grant_apply_ne ρ (Ne.symm e)] at this
                exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) this).1
            have hpair : u = c_r.left ∧ w = c_r.right := by
              rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
              · exact (huw.ne rfl).elim
              · exact ⟨rfl, rfl⟩
              · exact (not_lt_of_gt c_r.ordered huw).elim
              · exact (huw.ne rfl).elim
            obtain ⟨rfl, rfl⟩ := hpair
            rcases hvc.1 with hvl | hvr
            · have h1 := pigeonHole_bit hu v.2; rw [show (c_r.left, v.2) = v from Prod.ext hvl.symm rfl, grant_apply_self] at h1
              have h2 := pigeonHole_bit hw' v.2
              have hne : (c_r.right, v.2) ≠ v := fun e => c_r.ordered.ne' (hvl ▸ congrArg Prod.fst e)
              rw [grant_apply_ne ρ (Ne.symm hne)] at h2
              have e1 := Option.some.inj h1; have e2 := (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) h2).2
              rw [← e1, ← hvc.2] at e2; cases s <;> simp at e2
            · have h1 := pigeonHole_bit hw' v.2; rw [show (c_r.right, v.2) = v from Prod.ext hvr.symm rfl, grant_apply_self] at h1
              have h2 := pigeonHole_bit hu v.2
              have hne : (c_r.left, v.2) ≠ v := fun e => c_r.ordered.ne (hvr ▸ congrArg Prod.fst e)
              rw [grant_apply_ne ρ (Ne.symm hne)] at h2
              have e1 := Option.some.inj h1; have e2 := (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) h2).2
              rw [← e1, ← hvc.2] at e2; cases s <;> simp at e2
          have hbo4 : 4 ≤ b0 (State.grant ρ {v} (!s)) ow := by
            rw [b0_of_fp_le_two hnc_o hfp_o]
            unfold leafWeight
            by_cases h3' : ∃ u w b' val', sameBitPair (State.grant ρ {v} (!s)) u w b' val' ∧ Disjoint (pairHoles u w b' val') ow
            · exfalso; obtain ⟨u, w, b', val', ⟨huw, hu', hw'⟩, hdj⟩ := h3'
              have huf : u = c_r.left ∨ u = c_r.right := by
                by_cases e : (u, b') = v
                · rw [← congrArg Prod.fst e] at hvc; exact hvc.1
                · rw [grant_apply_ne ρ (Ne.symm e)] at hu'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hu').1
              have hwf : w = c_r.left ∨ w = c_r.right := by
                by_cases e : (w, b') = v
                · rw [← congrArg Prod.fst e] at hvc; exact hvc.1
                · rw [grant_apply_ne ρ (Ne.symm e)] at hw'; exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').1
              have hpair : u = c_r.left ∧ w = c_r.right := by
                rcases huf with rfl | rfl <;> rcases hwf with rfl | rfl
                · exact (huw.ne rfl).elim
                · exact ⟨rfl, rfl⟩
                · exact (not_lt_of_gt c_r.ordered huw).elim
                · exact (huw.ne rfl).elim
              obtain ⟨rfl, rfl⟩ := hpair
              have hval_c : bits c_r.hole b' = val' := by
                by_cases e1 : (c_r.left, b') = v
                · have e2 : (c_r.right, b') ≠ v := fun e => c_r.ordered.ne (congrArg Prod.fst (e1.trans e.symm))
                  rw [grant_apply_ne ρ (Ne.symm e2)] at hw'
                  exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hw').2.symm
                · rw [grant_apply_ne ρ (Ne.symm e1)] at hu'
                  exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hu').2.symm
              exact Finset.disjoint_left.mp hdj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl, hval_c⟩) hcow
            · rw [ite_eq_right h3']; split_ifs <;> omega
          have hbo_o := dValid_req_bound hd hv_o; rw [hk0_o] at hbo_o; simp only [List.length_nil, req] at hbo_o
          have hts0 : dPhi wt t_s = 0 := by omega
          have hto4 : dPhi wt t_o = 4 := by omega
          have hz := hzero_empty t_s hp_s hw3s hts0
          -- Now inspect t_o: cannot be axUniq, axRep, weak, or res (res gives ≥ 5!)!
          cases hv_o with
          | axUniq => simp [dMarks] at hk0_o
          | axRep _ _ hc => exact (hnc_o hc).elim
          | weak => simp [dWeaks] at hp_o
          | exitDer q _ _ _ =>
            simp only [dExits, dAxReps, countExit, dPhi, exitWeightSum, dWeaks] at hto4 ⊢
            exact ⟨by omega, by omega, q, by simp [hz.2.2 q], by omega⟩
          | res i' f' _ l' r' _ _ hl' hr' =>
            exfalso
            simp only [dMarks, List.append_eq_nil_iff, dWeaks, dPhi, exitWeightSum, dAxReps] at hk0_o hp_o hto4
            have bl' := dValid_req_bound hd hl'; rw [hk0_o.2] at bl'; simp only [List.length_nil, req, dPhi] at bl'
            have br' := dValid_req_bound hd hr'; rw [hk0_o.1] at br'; simp only [List.length_nil, req, dPhi] at br'
            by_cases hsing' : ∃ v' : Variable, f' = {v'}
            · obtain ⟨v', rfl⟩ := hsing'
              cases hv' : State.grant ρ {v} (!s) v' with
              | some sd' =>
                cases sd'
                · rw [grant_eq_self hv'] at br'; have := b0_ge_one (State.grant (State.grant ρ {v} (!s)) {v'} true) ow; omega
                · rw [grant_eq_self hv'] at bl'; have := b0_ge_one (State.grant (State.grant ρ {v} (!s)) {v'} false) ow; omega
              | none =>
                -- v' is on a 3rd pigeon p' ∉ {c_r.left, c_r.right} (since all 4 bits of {c_r.left, c_r.right} are fixed in ρ_o)!
                -- So BOTH children of ρ_o have ¬ hasCollision (since p' only has 1 bit fixed!),
                -- AND they CANNOT BOTH have hasDoubleOneStep (only 2 holes occupied in ρ_o!),
                -- so sum ≥ 2 + 3 = 5, contradicting hto4!
                have hfb_o : fixedBits (State.grant ρ {v} (!s)) = 4 := by rw [fixedBits_grant_none hrv (!s), hfb3]
                have hp_both_none : State.grant ρ {v} (!s) (v'.1, otherBit v'.2) = none := by
                  have hsub4 : Finset.univ.filter (fun w : Variable => State.grant ρ {v} (!s) w ≠ none) ⊆
                      {(c_r.left, 0), (c_r.left, 1), (c_r.right, 0), (c_r.right, 1)} := by
                    intro w hw''; cases hww : State.grant ρ {v} (!s) w with
                    | none => exact ((Finset.mem_filter.mp hw'').2 hww).elim
                    | some val =>
                      have hp' : w.1 = c_r.left ∨ w.1 = c_r.right := by
                        by_cases e : w = v
                        · rw [e]; exact hvc.1
                        · rw [grant_apply_ne ρ (Ne.symm e)] at hww
                          exact (signedShared_const (c := c_r) (by simpa [hm] using hs) (by simp) hww).1
                      rcases w with ⟨pw, bw⟩; change pw = c_r.left ∨ pw = c_r.right at hp'
                      rcases hp' with rfl | rfl <;> fin_cases bw <;> simp
                  have hcard4 : ({(c_r.left, (0 : Fin 2)), (c_r.left, 1), (c_r.right, 0), (c_r.right, 1)} : Finset Variable).card = 4 := by
                    simp [c_r.ordered.ne]
                  have heq := Finset.eq_of_subset_of_card_le hsub4 (by rw [hcard4]; exact hfb_o.symm.le)
                  have hv'_not : v'.1 ≠ c_r.left ∧ v'.1 ≠ c_r.right := by
                    constructor <;> intro e
                    · have hm' : v' ∈ Finset.univ.filter (fun w => State.grant ρ {v} (!s) w ≠ none) := by
                        rw [heq]; rcases v' with ⟨p', b'⟩; change p' = c_r.left at e; subst e; fin_cases b' <;> simp
                      exact (Finset.mem_filter.mp hm').2 hv'
                    · have hm' : v' ∈ Finset.univ.filter (fun w => State.grant ρ {v} (!s) w ≠ none) := by
                        rw [heq]; rcases v' with ⟨p', b'⟩; change p' = c_r.right at e; subst e; fin_cases b' <;> simp
                      exact (Finset.mem_filter.mp hm').2 hv'
                  by_contra hne
                  have hm' : (v'.1, otherBit v'.2) ∈ Finset.univ.filter (fun w => State.grant ρ {v} (!s) w ≠ none) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
                  rw [heq] at hm'; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
                  rcases hm' with e | e | e | e
                  · exact hv'_not.1 (congrArg Prod.fst e)
                  · exact hv'_not.1 (congrArg Prod.fst e)
                  · exact hv'_not.2 (congrArg Prod.fst e)
                  · exact hv'_not.2 (congrArg Prod.fst e)
                have hnc_c : ∀ s', ¬ hasCollision (State.grant (State.grant ρ {v} (!s)) {v'} s') := by
                  intro s' hc'
                  obtain ⟨_, _, _, _, ho', _⟩ := hasCollision_grant_elim hnc_o hc'
                  rw [hp_both_none] at ho'; cases ho'
                have hnb_double : ¬ (hasDoubleOneStep (State.grant (State.grant ρ {v} (!s)) {v'} false) ∧
                    hasDoubleOneStep (State.grant (State.grant ρ {v} (!s)) {v'} true)) := by
                  rintro ⟨hd0, hd1⟩
                  -- Each hasDoubleOneStep requires 2 full pigeons in ρ_o with bit v'.2 = false resp. true -> 4 full pigeons in ρ_o, contradicting hfp_o ≤ 2!
                  have hnd_o : ¬ hasDoubleOneStep (State.grant ρ {v} (!s)) := by
                    intro hdb; have := b0_of_fp_le_two (ow := ow) hnc_o hfp_o
                    -- Actually hfp_o ≤ 2 already rules out hasDoubleOneStep!
                    obtain ⟨x, bx, valx, hxb, hxo, hallx⟩ := hdb
                    obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits bx valx false
                    obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits bx valx true
                    obtain ⟨q0, hq0⟩ := hallx h0 hb0; obtain ⟨q1, hq1⟩ := hallx h1 hb1
                    have hq01 : q0 ≠ q1 := fun e => by have eh := pigeonHole_unique (e ▸ hq0) hq1; rw [eh, ho1] at ho0; cases ho0
                    have hxq0 : x ≠ q0 := fun e => by have := pigeonHole_bit (e ▸ hq0) (otherBit bx); rw [hxo] at this; cases this
                    have hxq1 : x ≠ q1 := fun e => by have := pigeonHole_bit (e ▸ hq1) (otherBit bx); rw [hxo] at this; cases this
                    have hsub3 : ({x, q0, q1} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) := by
                      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                      rcases hy with rfl | rfl | rfl; exact pigeonFixed_of_some hxb; exact pigeonFixed_of_hole hq0; exact pigeonFixed_of_hole hq1
                    have hc3 := Finset.card_le_card hsub3; simp [hxq0, hxq1, hq01] at hc3
                    change 3 ≤ fixedPigeons (State.grant ρ {v} (!s)) at hc3; omega
                  have extr : ∀ s', hasDoubleOneStep (State.grant (State.grant ρ {v} (!s)) {v'} s') →
                      ∀ h : Fin 4, bits h v'.2 = s' → ∃ q : Fin 5, pigeonHole (State.grant ρ {v} (!s)) q h := by
                    intro s' ⟨x, bx, valx, hxb, hxo, hallx⟩
                    have hxp : x = v'.1 := by
                      by_contra hne; apply hnd_o
                      refine ⟨x, bx, valx, ?_, ?_, fun h hh => ?_⟩
                      · rwa [grant_apply_ne _ (fun e => hne (congrArg Prod.fst e).symm)] at hxb
                      · rwa [grant_apply_ne _ (fun e => hne (congrArg Prod.fst e).symm)] at hxo
                      · obtain ⟨q, hq⟩ := hallx h hh
                        have hqp : q ≠ v'.1 := fun e => by
                          subst q; have := pigeonHole_bit hq (otherBit v'.2)
                          rw [grant_apply_ne _ (fun e => (otherBit_facts v'.2).1 (congrArg Prod.snd e).symm), hp_both_none] at this; cases this
                        exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
                    subst x
                    have hbx : bx = v'.2 := by
                      by_contra hne
                      have : bx = otherBit v'.2 := (otherBit_facts v'.2).2.2 bx |>.resolve_left hne
                      rw [this, grant_apply_ne _ (fun e => (otherBit_facts v'.2).1 (congrArg Prod.snd e).symm), hp_both_none] at hxb; cases hxb
                    subst bx
                    have hvx : valx = s' := Option.some.inj (hxb.symm.trans (grant_apply_self _ v' s'))
                    subst valx
                    intro h hh; obtain ⟨q, hq⟩ := hallx h hh
                    have hqp : q ≠ v'.1 := fun e => by
                      subst q; have := pigeonHole_bit hq (otherBit v'.2)
                      rw [grant_apply_ne _ (fun e => (otherBit_facts v'.2).1 (congrArg Prod.snd e).symm), hp_both_none] at this; cases this
                    exact ⟨q, (pigeonHole_grant_ne hqp).mp hq⟩
                  obtain ⟨h0, hb0, ho0⟩ := exists_hole_of_bits v'.2 false false
                  obtain ⟨h1, hb1, ho1⟩ := exists_hole_of_bits v'.2 false true
                  obtain ⟨h2, hb2, _⟩ := exists_hole_of_bits v'.2 true false
                  obtain ⟨q0, hq0⟩ := extr false hd0 h0 hb0
                  obtain ⟨q1, hq1⟩ := extr false hd0 h1 hb1
                  obtain ⟨q2, hq2⟩ := extr true hd1 h2 hb2
                  have hq01 : q0 ≠ q1 := fun e => by have eh := pigeonHole_unique (e ▸ hq0) hq1; rw [eh, ho1] at ho0; cases ho0
                  have hq02 : q0 ≠ q2 := fun e => by have eh := pigeonHole_unique (e ▸ hq0) hq2; rw [eh, hb2] at hb0; cases hb0
                  have hq12 : q1 ≠ q2 := fun e => by have eh := pigeonHole_unique (e ▸ hq1) hq2; rw [eh, hb2] at hb1; cases hb1
                  have hsub3 : ({q0, q1, q2} : Finset (Fin 5)) ⊆ Finset.univ.filter (pigeonFixed (State.grant ρ {v} (!s))) := by
                    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    rcases hy with rfl | rfl | rfl; exact pigeonFixed_of_hole hq0; exact pigeonFixed_of_hole hq1; exact pigeonFixed_of_hole hq2
                  have hc3 := Finset.card_le_card hsub3; simp [hq01, hq02, hq12] at hc3
                  change 3 ≤ fixedPigeons (State.grant ρ {v} (!s)) at hc3; omega
                have hb2_0 : 2 ≤ b0 (State.grant (State.grant ρ {v} (!s)) {v'} false) ow := by
                  unfold b0; rw [ite_eq_right (hnc_c false)]; have := leafWeight_ge_three (State.grant (State.grant ρ {v} (!s)) {v'} false) ow; split_ifs <;> omega
                have hb2_1 : 2 ≤ b0 (State.grant (State.grant ρ {v} (!s)) {v'} true) ow := by
                  unfold b0; rw [ite_eq_right (hnc_c true)]; have := leafWeight_ge_three (State.grant (State.grant ρ {v} (!s)) {v'} true) ow; split_ifs <;> omega
                by_cases hd0 : hasDoubleOneStep (State.grant (State.grant ρ {v} (!s)) {v'} false)
                · have hnd1 : ¬ hasDoubleOneStep (State.grant (State.grant ρ {v} (!s)) {v'} true) := fun hd1 => hnb_double ⟨hd0, hd1⟩
                  have hb3_1 : 3 ≤ b0 (State.grant (State.grant ρ {v} (!s)) {v'} true) ow := by
                    unfold b0; rw [ite_eq_right (hnc_c true), ite_eq_right hnd1]
                    have := leafWeight_ge_three (State.grant (State.grant ρ {v} (!s)) {v'} true) ow; split_ifs <;> omega
                  omega
                · have hb3_0 : 3 ≤ b0 (State.grant (State.grant ρ {v} (!s)) {v'} false) ow := by
                    unfold b0; rw [ite_eq_right (hnc_c false), ite_eq_right hd0]
                    have := leafWeight_ge_three (State.grant (State.grant ρ {v} (!s)) {v'} false) ow; split_ifs <;> omega
                  omega
            · have hns' : ∀ v' : Variable, f' ≠ {v'} := fun v' hv' => hsing' ⟨v', hv'⟩
              rw [grant_nonsingle hns' true] at bl'; rw [grant_nonsingle hns' false] at br'; omega
        rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
            ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by
              have := congrArg List.length hm; simp at this; omega) with ⟨er, el⟩ | ⟨er, el⟩
        · have hl0 : dMarks keyAt l = [] := List.eq_nil_of_length_eq_zero el
          have hrm : dMarks keyAt r = [c_r] := by simpa [hl0] using hm
          have h := handle_o false r l (hrm ▸ dValid_shared hr) hl (by omega) (by omega) hl0
            (fun j hj => hwt3 j (by simp [countExit]; omega)) (by simp [dPhi]; omega)
          obtain ⟨h1, h2, q, h3, h4⟩ := h
          exact ⟨by omega, by omega, q, by omega, h4⟩
        · have hr0 : dMarks keyAt r = [] := List.eq_nil_of_length_eq_zero er
          have hlm : dMarks keyAt l = [c_r] := by simpa [hr0] using hm
          have h := handle_o true l r (hlm ▸ dValid_shared hl) hr (by omega) (by omega) hr0
            (fun j hj => hwt3 j (by simp [countExit]; omega)) (by simp [dPhi]; omega)
          obtain ⟨h1, h2, q, h3, h4⟩ := h
          exact ⟨by omega, by omega, q, by omega, h4⟩
    · -- Non-singleton split: req 1 ρ + b0 ρ ≥ 4 + 4 = 8 > 4!
      exfalso
      have hns : ∀ v : Variable, f ≠ {v} := fun v hv => hsing ⟨v, hv⟩
      rw [grant_nonsingle hns true] at bl; rw [grant_nonsingle hns false] at br
      rcases (show ((dMarks keyAt r).length = 1 ∧ (dMarks keyAt l).length = 0) ∨
          ((dMarks keyAt r).length = 0 ∧ (dMarks keyAt l).length = 1) by
            have := congrArg List.length hm; simp at this; omega) with ⟨er, el⟩ | ⟨er, el⟩
      · rw [er] at br; rw [el] at bl; simp only [req] at bl; omega
      · rw [el] at bl; rw [er] at br; simp only [req] at br; omega

end DTreeMeasures

end Potential

/-! ## Section 4: Derived-Cut Components & Exact Conservation Laws -/

namespace DComponents

open PEqualNP.ProofComplexity Dag BPHP Potential
open scoped BigOperators

variable (d : ShortestDag Formula)

noncomputable def keyAt (i : Fin d.pi.length) : Collision :=
  if h : d.children i = [] then
    Classical.choose (clause_key (d.axiom_of_no_children i h))
  else ⟨0, 1, 0, by decide⟩

theorem keyAt_clause {i : Fin d.pi.length} (h : d.children i = []) :
    (keyAt d i).clause = d.pi.get i := by
  unfold keyAt; rw [dite_eq_left h]
  exact (Classical.choose_spec (clause_key (d.axiom_of_no_children i h))).symm

theorem root_not_ax : d.children d.root ≠ [] := by
  intro hax
  have heq := keyAt_clause d hax
  rw [d.rootEmpty] at heq
  have hm := (Collision.mem_clause_bit (keyAt d d.root) 0).1
  rw [heq] at hm; simp at hm

theorem axiom_count :
    (Finset.univ.filter (fun i : Fin d.pi.length => d.children i = [])).card = 40 := by
  classical
  let axSet := Finset.univ.filter (fun i : Fin d.pi.length => d.children i = [])
  let f : Collision → Fin d.pi.length := fun c => Classical.choose (d.active_initial_clause (sample c 0))
  have hf_spec (c : Collision) : d.children (f c) = [] ∧ d.pi.get (f c) = c.clause := by
    have hs := Classical.choose_spec (d.active_initial_clause (sample c 0))
    exact ⟨hs.2.1, sample_only_axiom c 0 (d.axiom_of_no_children _ hs.2.1) hs.2.2⟩
  have hinj : Function.Injective f := by
    intro c₁ c₂ heq
    exact clause_injective ((hf_spec c₁).2.symm.trans (congrArg d.pi.get heq |>.trans (hf_spec c₂).2))
  have himg : Finset.univ.image f = axSet := by
    ext i; simp only [Finset.mem_image, Finset.mem_univ, true_and, axSet, Finset.mem_filter]
    constructor
    · rintro ⟨c, rfl⟩; exact (hf_spec c).1
    · intro hax
      refine ⟨keyAt d i, d.nodup.injective_get ((hf_spec (keyAt d i)).2.trans (keyAt_clause d hax))⟩
  change axSet.card = 40
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, collision_count]

def dRoots : Finset (Fin d.pi.length) :=
  Finset.univ.filter (fun i => d.children i ≠ [] ∧ d.incoming i ≠ 1)

def keptDerChildren (u : Fin d.pi.length) : List (Fin d.pi.length) :=
  (d.children u).filter (fun v => decide (d.children v ≠ [] ∧ d.incoming v = 1))

def s_der : ℕ := ∑ v : Fin d.pi.length, if d.children v ≠ [] then d.incoming v - 1 else 0
def s_ax : ℕ := ∑ v : Fin d.pi.length, if d.children v = [] then d.incoming v - 1 else 0
def A_rep : ℕ := (Finset.univ.filter (fun v : Fin d.pi.length => d.children v = [] ∧ 2 ≤ d.incoming v)).card
def W_tot : ℕ := (Finset.univ.filter (fun v : Fin d.pi.length => (d.children v).length = 1)).card

theorem sum_incoming_eq_sum_len :
    (∑ v : Fin d.pi.length, d.incoming v) = ∑ u : Fin d.pi.length, (d.children u).length := by
  classical
  simp only [ShortestDag.incoming]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  have hcount : ∀ l : List (Fin d.pi.length), (∑ v : Fin d.pi.length, l.count v) = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [List.count_cons, Finset.sum_add_distrib, ih, Nat.add_comm]
  exact hcount (d.children u)

theorem degree_mass :
    (∑ v : Fin d.pi.length, d.incoming v) + 1 = d.pi.length + (s_der d + s_ax d) := by
  have hsplit : s_der d + s_ax d = ∑ v : Fin d.pi.length, (d.incoming v - 1) := by
    unfold s_der s_ax; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _; by_cases h : d.children v = [] <;> simp [h]
  rw [hsplit]
  have point (v : Fin d.pi.length) :
      d.incoming v + (if v = d.root then 1 else 0) = 1 + (d.incoming v - 1) := by
    by_cases e : v = d.root
    · subst v; simp [d.incoming_at_first]
    · have hpos := d.incoming_pos v (fun h => e (Fin.ext (h.trans d.root_val_zero.symm)))
      simp [e]; omega
  have ans := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => point v)
  simpa [Finset.sum_add_distrib] using ans

theorem node_budget (hsmall : d.pi.length ≤ 111) :
    s_der d + s_ax d + W_tot d ≤ 32 := by
  have point (v : Fin d.pi.length) :
      (d.children v).length + (if (d.children v).length = 1 then 1 else 0) +
      2 * (if d.children v = [] then 1 else 0) = 2 := by
    have h := d.children_length v
    rcases (show (d.children v).length = 0 ∨ (d.children v).length = 1 ∨ (d.children v).length = 2 by omega) with e | e | e
    · have he : d.children v = [] := List.eq_nil_of_length_eq_zero e
      simp [he]
    · have hne : d.children v ≠ [] := fun h' => by rw [h'] at e; simp at e
      simp [e, hne]
    · have hne : d.children v ≠ [] := fun h' => by rw [h'] at e; simp at e
      simp [e, hne]
  have sums := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => point v)
  have hax := axiom_count d
  have hdeg := degree_mass d
  rw [sum_incoming_eq_sum_len] at hdeg
  have hshape : (∑ v : Fin d.pi.length, (d.children v).length) + W_tot d + 2 * 40 = d.pi.length * 2 := by
    rw [← hax]; unfold W_tot
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum]
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using sums
  omega

theorem dRoots_card_le : (dRoots d).card ≤ s_der d + 1 := by
  have point (v : Fin d.pi.length) :
      (if d.children v ≠ [] ∧ d.incoming v ≠ 1 then 1 else 0) ≤
      (if d.children v ≠ [] then d.incoming v - 1 else 0) + (if v = d.root then 1 else 0) := by
    by_cases e : v = d.root
    · subst v; simp [d.incoming_at_first, root_not_ax]
    · have hpos := d.incoming_pos v (fun h => e (Fin.ext (h.trans d.root_val_zero.symm)))
      by_cases hax : d.children v = [] <;> by_cases h1 : d.incoming v = 1 <;> simp [e, hax, h1]; omega
  have ans := Finset.sum_le_sum (s := Finset.univ) (fun v _ => point v)
  rw [dRoots, Finset.card_filter, s_der]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using ans

theorem A_rep_le_s_ax : A_rep d ≤ s_ax d := by
  unfold A_rep s_ax; rw [Finset.card_filter]
  apply Finset.sum_le_sum; intro v _
  by_cases hax : d.children v = [] <;> by_cases h2 : 2 ≤ d.incoming v <;> simp [hax, h2]; omega

theorem weighted_count {α : Type} [Fintype α] [DecidableEq α] (l : List α) (m : α → ℕ) :
    (l.map m).sum = ∑ v, l.count v * m v := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, Nat.add_mul, Finset.sum_add_distrib, ih, ite_mul, Nat.add_comm]

theorem filtered_count {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) : (l.filter fun a => decide (P a)).length = ∑ v, if P v then l.count v else 0 := by
  have hcount : ∀ l' : List α, (∑ v : α, l'.count v) = l'.length := by
    intro l'; induction l' with
    | nil => simp
    | cons a l' ih => simp [List.count_cons, Finset.sum_add_distrib, ih]
  rw [← hcount (l.filter fun a => decide (P a))]
  apply Finset.sum_congr rfl; intro v _
  by_cases h : P v
  · simp [h]
  · rw [ite_eq_right h]; apply List.count_eq_zero_of_not_mem; simp [h]

theorem dComponent_mass (m weight : Fin d.pi.length → ℕ)
    (hrec : ∀ u, d.children u ≠ [] → m u = weight u + ((keptDerChildren d u).map m).sum) :
    (∑ r ∈ dRoots d, m r) = ∑ u ∈ Finset.univ.filter (fun u : Fin d.pi.length => d.children u ≠ []), weight u := by
  classical
  let D := Finset.univ.filter (fun u : Fin d.pi.length => d.children u ≠ [])
  have hkept : (∑ u ∈ D, ((keptDerChildren d u).map m).sum) =
      ∑ v ∈ D, if d.incoming v = 1 then m v else 0 := by
    have hsum_all : (∑ u ∈ D, ((keptDerChildren d u).map m).sum) =
        ∑ u : Fin d.pi.length, ((keptDerChildren d u).map m).sum := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro u _
      by_cases h : d.children u ≠ []
      · simp [h]
      · simp only [not_not] at h; simp [keptDerChildren, h]
    rw [hsum_all]
    simp_rw [weighted_count]
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro v _
    by_cases hD : d.children v ≠ []
    · by_cases h1 : d.incoming v = 1
      · have hcnt (u : Fin d.pi.length) : (keptDerChildren d u).count v = (d.children u).count v :=
          List.count_filter (by simp [hD, h1])
        simp_rw [hcnt]; rw [← Finset.sum_mul]; change d.incoming v * m v = _; simp [hD, h1]
      · have hcnt (u : Fin d.pi.length) : (keptDerChildren d u).count v = 0 := by
          apply List.count_eq_zero_of_not_mem; simp [keptDerChildren, h1]
        simp [hcnt, hD, h1]
    · have hcnt (u : Fin d.pi.length) : (keptDerChildren d u).count v = 0 := by
        apply List.count_eq_zero_of_not_mem; simp [keptDerChildren, hD]
      simp [hcnt, hD]
  have gathered : (∑ u ∈ D, m u) = (∑ u ∈ D, weight u) + ∑ u ∈ D, ((keptDerChildren d u).map m).sum := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u hu => hrec u (Finset.mem_filter.mp hu).2)
  rw [hkept] at gathered
  have parts : (∑ r ∈ dRoots d, m r) + (∑ v ∈ D, if d.incoming v = 1 then m v else 0) = ∑ v ∈ D, m v := by
    have hsub : dRoots d = D.filter (fun v => d.incoming v ≠ 1) := by
      ext v; simp [dRoots, D]
    rw [hsub, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    by_cases h : d.incoming v = 1 <;> simp [h]
  exact Nat.add_right_cancel (parts.trans gathered)

theorem sum_nonAx_filter_count (P : Fin d.pi.length → Prop) [DecidablePred P] :
    (∑ u ∈ Finset.univ.filter (fun u : Fin d.pi.length => d.children u ≠ []),
      ((d.children u).filter (fun v => decide (P v))).length) =
    ∑ v : Fin d.pi.length, if P v then d.incoming v else 0 := by
  have hall : (∑ u ∈ Finset.univ.filter (fun u : Fin d.pi.length => d.children u ≠ []),
      ((d.children u).filter (fun v => decide (P v))).length) =
      ∑ u : Fin d.pi.length, ((d.children u).filter (fun v => decide (P v))).length := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro u _
    by_cases h : d.children u ≠ []
    · simp [h]
    · simp only [not_not] at h; simp [h]
  rw [hall]; simp_rw [filtered_count]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  by_cases h : P v <;> simp [h, ShortestDag.incoming]

theorem dMarks_recurrence (u : Fin d.pi.length) (hD : d.children u ≠ []) :
    (dMarks (keyAt d) (d.dUnroll u)).length =
      ((d.children u).filter (fun v => decide (d.children v = [] ∧ d.incoming v = 1))).length +
      ((keptDerChildren d u).map (fun v => (dMarks (keyAt d) (d.dUnroll v)).length)).sum := by
  have hcut (j : Fin d.pi.length) :
      (dMarks (keyAt d) (d.dCutChild j)).length =
      (if d.children j = [] ∧ d.incoming j = 1 then 1 else 0) +
      (if d.children j ≠ [] ∧ d.incoming j = 1 then (dMarks (keyAt d) (d.dUnroll j)).length else 0) := by
    unfold ShortestDag.dCutChild
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hax, h1, dMarks]
  cases hr : d.rules u with
  | ax _ => simp [ShortestDag.children, hr, Rule.parents] at hD
  | weak j _ _ =>
    have hcu : d.children u = [j] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_weak hr, keptDerChildren, hcu]; simp only [dMarks, hcut j]
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hax, h1]
  | res j k _ _ _ =>
    have hcu : d.children u = [j, k] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_res hr, keptDerChildren, hcu]; simp only [dMarks, List.length_append, hcut j, hcut k]
    by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;>
      by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;> simp [h1, h2, h3, h4] <;> omega

theorem sum_dMarks :
    (∑ r ∈ dRoots d, (dMarks (keyAt d) (d.dUnroll r)).length) + A_rep d = 40 := by
  classical
  rw [dComponent_mass d _ _ (dMarks_recurrence d), sum_nonAx_filter_count]
  have h40 := axiom_count d
  rw [← h40, Finset.card_filter]; unfold A_rep; rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro v _
  by_cases hax : d.children v = []
  · have hne : v ≠ d.root := fun e => root_not_ax d (e ▸ hax)
    have hpos := d.incoming_pos v (fun h => hne (Fin.ext (h.trans d.root_val_zero.symm)))
    by_cases h1 : d.incoming v = 1 <;> simp [hax, h1]; omega
  · simp [hax]

theorem dAxReps_recurrence (u : Fin d.pi.length) (hD : d.children u ≠ []) :
    dAxReps (d.dUnroll u) =
      ((d.children u).filter (fun v => decide (d.children v = [] ∧ 2 ≤ d.incoming v))).length +
      ((keptDerChildren d u).map (fun v => dAxReps (d.dUnroll v))).sum := by
  have hcut (j : Fin d.pi.length) (hj : j ∈ d.children u) :
      dAxReps (d.dCutChild j) =
      (if d.children j = [] ∧ 2 ≤ d.incoming j then 1 else 0) +
      (if d.children j ≠ [] ∧ d.incoming j = 1 then dAxReps (d.dUnroll j) else 0) := by
    have hpos : 0 < d.incoming j := by
      have hne : j ≠ d.root := fun e => by
        have hlt : u.val < j.val := d.children_lt u j hj; rw [e, d.root_val_zero] at hlt; omega
      exact d.incoming_pos j (fun h => hne (Fin.ext (h.trans d.root_val_zero.symm)))
    unfold ShortestDag.dCutChild
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;>
      simp [hax, h1, dAxReps, show (2 ≤ d.incoming j) ↔ d.incoming j ≠ 1 by omega]
  cases hr : d.rules u with
  | ax _ => simp [ShortestDag.children, hr, Rule.parents] at hD
  | weak j _ _ =>
    have hcu : d.children u = [j] := by simp [ShortestDag.children, hr, Rule.parents]
    have hj : j ∈ d.children u := by simp [hcu]
    rw [d.dUnroll_weak hr, keptDerChildren, hcu]; simp only [dAxReps, hcut j hj]
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> by_cases h2 : 2 ≤ d.incoming j <;> simp [hax, h1, h2]
  | res j k _ _ _ =>
    have hcu : d.children u = [j, k] := by simp [ShortestDag.children, hr, Rule.parents]
    have hj : j ∈ d.children u := by simp [hcu]
    have hk : k ∈ d.children u := by simp [hcu]
    rw [d.dUnroll_res hr, keptDerChildren, hcu]; simp only [dAxReps, hcut j hj, hcut k hk]
    by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;>
      by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;>
      by_cases h5 : 2 ≤ d.incoming j <;> by_cases h6 : 2 ≤ d.incoming k <;> simp [h1, h2, h3, h4, h5, h6] <;> omega

theorem sum_dAxReps :
    (∑ r ∈ dRoots d, dAxReps (d.dUnroll r)) = A_rep d + s_ax d := by
  classical
  rw [dComponent_mass d _ _ (dAxReps_recurrence d), sum_nonAx_filter_count]
  unfold A_rep s_ax; rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro v _
  by_cases hax : d.children v = [] <;> by_cases h2 : 2 ≤ d.incoming v <;> simp [hax, h2] <;> omega

theorem dWeaks_recurrence (u : Fin d.pi.length) (hD : d.children u ≠ []) :
    dWeaks (d.dUnroll u) =
      (if (d.children u).length = 1 then 1 else 0) +
      ((keptDerChildren d u).map (fun v => dWeaks (d.dUnroll v))).sum := by
  have hcut (j : Fin d.pi.length) :
      dWeaks (d.dCutChild j) =
      if d.children j ≠ [] ∧ d.incoming j = 1 then dWeaks (d.dUnroll j) else 0 := by
    unfold ShortestDag.dCutChild
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hax, h1, dWeaks]
  cases hr : d.rules u with
  | ax _ => simp [ShortestDag.children, hr, Rule.parents] at hD
  | weak j _ _ =>
    have hcu : d.children u = [j] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_weak hr, keptDerChildren, hcu]; simp only [dWeaks, hcut j]
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hax, h1]
  | res j k _ _ _ =>
    have hcu : d.children u = [j, k] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_res hr, keptDerChildren, hcu]; simp only [dWeaks, hcut j, hcut k]
    by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;>
      by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;> simp [h1, h2, h3, h4]

theorem sum_dWeaks : (∑ r ∈ dRoots d, dWeaks (d.dUnroll r)) = W_tot d := by
  classical
  rw [dComponent_mass d _ _ (dWeaks_recurrence d), Finset.sum_filter]
  unfold W_tot; rw [Finset.card_filter]
  apply Finset.sum_congr rfl; intro u _
  by_cases h1 : (d.children u).length = 1
  · have hne : d.children u ≠ [] := fun h => by rw [h] at h1; simp at h1
    simp [h1, hne]
  · simp [h1]

theorem dExits_recurrence (u : Fin d.pi.length) (hD : d.children u ≠ []) :
    dExits (d.dUnroll u) =
      ((d.children u).filter (fun v => decide (d.children v ≠ [] ∧ 2 ≤ d.incoming v))).length +
      ((keptDerChildren d u).map (fun v => dExits (d.dUnroll v))).sum := by
  have hcut (j : Fin d.pi.length) (hj : j ∈ d.children u) :
      dExits (d.dCutChild j) =
      (if d.children j ≠ [] ∧ 2 ≤ d.incoming j then 1 else 0) +
      (if d.children j ≠ [] ∧ d.incoming j = 1 then dExits (d.dUnroll j) else 0) := by
    have hpos : 0 < d.incoming j := by
      have hne : j ≠ d.root := fun e => by
        have hlt : u.val < j.val := d.children_lt u j hj; rw [e, d.root_val_zero] at hlt; omega
      exact d.incoming_pos j (fun h => hne (Fin.ext (h.trans d.root_val_zero.symm)))
    unfold ShortestDag.dCutChild
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;>
      simp [hax, h1, dExits, show (2 ≤ d.incoming j) ↔ d.incoming j ≠ 1 by omega]
  cases hr : d.rules u with
  | ax _ => simp [ShortestDag.children, hr, Rule.parents] at hD
  | weak j _ _ =>
    have hcu : d.children u = [j] := by simp [ShortestDag.children, hr, Rule.parents]
    have hj : j ∈ d.children u := by simp [hcu]
    rw [d.dUnroll_weak hr, keptDerChildren, hcu]; simp only [dExits, hcut j hj]
    by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> by_cases h2 : 2 ≤ d.incoming j <;> simp [hax, h1, h2]
  | res j k _ _ _ =>
    have hcu : d.children u = [j, k] := by simp [ShortestDag.children, hr, Rule.parents]
    have hj : j ∈ d.children u := by simp [hcu]
    have hk : k ∈ d.children u := by simp [hcu]
    rw [d.dUnroll_res hr, keptDerChildren, hcu]; simp only [dExits, hcut j hj, hcut k hk]
    by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;>
      by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;>
      by_cases h5 : 2 ≤ d.incoming j <;> by_cases h6 : 2 ≤ d.incoming k <;> simp [h1, h2, h3, h4, h5, h6] <;> omega

theorem sum_dExits :
    (∑ r ∈ dRoots d, dExits (d.dUnroll r)) + 1 = (dRoots d).card + s_der d := by
  classical
  rw [dComponent_mass d _ _ (dExits_recurrence d), sum_nonAx_filter_count]
  have point (v : Fin d.pi.length) :
      (if d.children v ≠ [] ∧ 2 ≤ d.incoming v then d.incoming v else 0) + (if v = d.root then 1 else 0) =
      (if d.children v ≠ [] ∧ d.incoming v ≠ 1 then 1 else 0) +
      (if d.children v ≠ [] then d.incoming v - 1 else 0) := by
    by_cases e : v = d.root
    · subst v; simp [d.incoming_at_first, root_not_ax]
    · have hpos := d.incoming_pos v (fun h => e (Fin.ext (h.trans d.root_val_zero.symm)))
      by_cases hax : d.children v = [] <;> by_cases h1 : d.incoming v = 1 <;>
        by_cases h2 : 2 ≤ d.incoming v <;> simp [e, hax, h1, h2] <;> omega
  have ans := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => point v)
  rw [dRoots, Finset.card_filter, s_der]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using ans

theorem countExit_recurrence (t : Fin d.pi.length) (ht : t ∈ dRoots d)
    (u : Fin d.pi.length) (hD : d.children u ≠ []) :
    countExit t (d.dUnroll u) =
      (d.children u).count t + ((keptDerChildren d u).map (fun v => countExit t (d.dUnroll v))).sum := by
  have ht_prop := (Finset.mem_filter.mp ht).2
  have hcut (j : Fin d.pi.length) :
      countExit t (d.dCutChild j) =
      (if j = t then 1 else 0) +
      (if d.children j ≠ [] ∧ d.incoming j = 1 then countExit t (d.dUnroll j) else 0) := by
    unfold ShortestDag.dCutChild
    by_cases hjt : j = t
    · subst hjt; simp [ht_prop.1, ht_prop.2, countExit]
    · by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hjt, hax, h1, countExit]
  cases hr : d.rules u with
  | ax _ => simp [ShortestDag.children, hr, Rule.parents] at hD
  | weak j _ _ =>
    have hcu : d.children u = [j] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_weak hr, keptDerChildren, hcu]; simp only [countExit, hcut j, List.count_singleton]
    rcases eq_or_ne j t with rfl | hjt
    · simp [ht_prop.1, ht_prop.2]
    · by_cases hax : d.children j = [] <;> by_cases h1 : d.incoming j = 1 <;> simp [hjt, hax, h1]
  | res j k _ _ _ =>
    have hcu : d.children u = [j, k] := by simp [ShortestDag.children, hr, Rule.parents]
    rw [d.dUnroll_res hr, keptDerChildren, hcu]; simp only [countExit, hcut j, hcut k, List.count_cons, List.count_nil]
    by_cases hj : j = t <;> by_cases hk : k = t
    · subst hj; subst hk; simp [ht_prop.1, ht_prop.2]
    · subst hj; by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;> simp [ht_prop.1, ht_prop.2, hk, h3, h4]
    · subst hk; by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;> simp [ht_prop.1, ht_prop.2, hj, h1, h2]; omega
    · by_cases h1 : d.children j = [] <;> by_cases h2 : d.incoming j = 1 <;>
        by_cases h3 : d.children k = [] <;> by_cases h4 : d.incoming k = 1 <;>
        simp [hj, hk, h1, h2, h3, h4]

theorem sum_countExit (t : Fin d.pi.length) (ht : t ∈ dRoots d) :
    (∑ r ∈ dRoots d, countExit t (d.dUnroll r)) = d.incoming t := by
  classical
  rw [dComponent_mass d _ _ (countExit_recurrence d t ht)]
  unfold ShortestDag.incoming; rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro u _
  by_cases h : d.children u ≠ []
  · simp [h]
  · simp only [not_not] at h; simp [h]

theorem dMark_route {t : DTree Variable (Fin d.pi.length)} {c : Collision}
    (hc : c ∈ dMarks (keyAt d) t) :
    ∃ j qs, DTree.Route t j qs ∧ c = keyAt d j := by
  induction t with
  | axUniq j => exact ⟨j, [], .axUniq j, by simpa [dMarks] using hc⟩
  | axRep _ | exitDer _ => simp [dMarks] at hc
  | weak i t ih =>
    obtain ⟨j, qs, path, eq⟩ := ih hc; exact ⟨j, none :: qs, .weak path, eq⟩
  | res i f l r ihl ihr =>
    rcases List.mem_append.mp hc with h | h
    · obtain ⟨j, qs, path, eq⟩ := ihr h; exact ⟨j, some (f, false) :: qs, .right path, eq⟩
    · obtain ⟨j, qs, path, eq⟩ := ihl h; exact ⟨j, some (f, true) :: qs, .left path, eq⟩

theorem testParity_eq_parity (a : Assignment) (f : Finset Variable) :
    Dag.testParity a f = parity f a := rfl

theorem dMarks_false (i : Fin d.pi.length) :
    ∀ c ∈ dMarks (keyAt d) (d.dUnroll i), ∀ phase : Fin 3,
      ¬ LinClauseSat (sample c phase) (d.pi.get i) := by
  intro c hc phase
  obtain ⟨j, qs, path, rfl⟩ := dMark_route d hc
  have hax := (d.route_of_dUnroll path).2.1
  exact (d.dUnroll_route_active (sample (keyAt d j) phase) path (fun C hC hf => by
    rw [← keyAt_clause d hax]; exact sample_only_axiom (keyAt d j) phase hC hf)).1

theorem dMarks_nodup (i : Fin d.pi.length) :
    ((dMarks (keyAt d) (d.dUnroll i)).map Collision.hole).Nodup := by
  have aux : ∀ (t : DTree Variable (Fin d.pi.length)),
      (∀ j qs, DTree.Route t j qs → ∀ q ∈ qs, ∀ phase : Fin 3,
        ShortestDag.Accepts (sample (keyAt d j) phase) q) →
      ((dMarks (keyAt d) t).map Collision.hole).Nodup := by
    intro t; induction t with
    | axUniq _ | axRep _ | exitDer _ => intro _; simp [dMarks]
    | weak _ t ih => intro hv; exact ih (fun j qs p q hq ph => hv j _ (.weak p) q (List.mem_cons_of_mem _ hq) ph)
    | res _ f l r ihl ihr =>
      intro hv
      simp only [dMarks, List.map_append, List.nodup_append']
      refine ⟨ihr (fun j qs p q hq ph => hv j _ (.right p) q (List.mem_cons_of_mem _ hq) ph),
              ihl (fun j qs p q hq ph => hv j _ (.left p) q (List.mem_cons_of_mem _ hq) ph), ?_⟩
      intro h hm hn
      obtain ⟨e, he, eqe⟩ := List.mem_map.mp hm
      obtain ⟨g, hg, eqg⟩ := List.mem_map.mp hn
      obtain ⟨j, ps, rpath, rfl⟩ := dMark_route d he
      obtain ⟨k, qs, lpath, rfl⟩ := dMark_route d hg
      have heven := allIn_follows (keyAt d j) f false (fun ph => hv j _ (.right rpath) (some (f, false)) List.mem_cons_self ph)
      have hodd := allIn_follows (keyAt d k) f true (fun ph => hv k _ (.left lpath) (some (f, true)) List.mem_cons_self ph)
      rw [eqe, ← eqg, hodd] at heven; cases heven
  exact aux (d.dUnroll i) (fun j qs path q hq phase =>
    (d.dUnroll_route_active (sample (keyAt d j) phase) path (fun C hC hf => by
      rw [← keyAt_clause d (d.route_of_dUnroll path).2.1]
      exact sample_only_axiom (keyAt d j) phase hC hf)).2 q hq)

theorem dMarks_distinctHoles (i : Fin d.pi.length) :
    DistinctHoles (dMarks (keyAt d) (d.dUnroll i)).toFinset := by
  intro c₁ hc₁ c₂ hc₂ heq
  have h1 := List.mem_toFinset.mp hc₁; have h2 := List.mem_toFinset.mp hc₂
  have hnd := dMarks_nodup d i
  -- In a list whose map Collision.hole is Nodup, two elements with equal hole must be equal!
  have huniq : ∀ (l : List Collision), (l.map Collision.hole).Nodup →
      ∀ x ∈ l, ∀ y ∈ l, x.hole = y.hole → x = y := by
    intro l; induction l with
    | nil => simp
    | cons a l ih =>
      intro nd x hx y hy eq
      obtain ⟨hnot, hndl⟩ := List.nodup_cons.mp nd
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact (hnot (List.mem_map.mpr ⟨y, hy', eq.symm⟩)).elim
      · exact (hnot (List.mem_map.mpr ⟨x, hx', eq⟩)).elim
      · exact ih hndl x hx' y hy' eq
  exact huniq _ hnd c₁ h1 c₂ h2 heq

noncomputable def dParent (v : Fin d.pi.length) (h : d.incoming v = 1) : Fin d.pi.length :=
  Classical.choose (d.exists_parent v (fun hz => by
    have : v = d.root := Fin.ext (hz.trans d.root_val_zero.symm)
    rw [this, d.incoming_at_first] at h; omega))

theorem dParent_mem (v : Fin d.pi.length) (h : d.incoming v = 1) :
    v ∈ d.children (dParent d v h) :=
  Classical.choose_spec (d.exists_parent v (fun hz => by
    have : v = d.root := Fin.ext (hz.trans d.root_val_zero.symm)
    rw [this, d.incoming_at_first] at h; omega))

noncomputable def dOwner (v : Fin d.pi.length) : Fin d.pi.length :=
  if h : d.incoming v = 1 then dOwner (dParent d v h) else v
termination_by v.val
decreasing_by exact d.children_lt _ _ (dParent_mem d v h)

theorem dOwner_root (v : Fin d.pi.length) (hv : d.incoming v ≠ 1) : dOwner d v = v := by
  rw [dOwner, dite_eq_right hv]

theorem dOwner_child {u v : Fin d.pi.length} (h : v ∈ d.children u) (hv : d.incoming v = 1) :
    dOwner d v = dOwner d u := by
  rw [dOwner, dite_eq_left hv, d.parent_unique hv (dParent_mem d v hv) h]

theorem dOwner_of_localPath {i j : Fin d.pi.length} {qs} (hp : d.LocalPath i j qs) :
    dOwner d j = dOwner d i := by
  induction hp with
  | nil _ => rfl
  | @cons i j k q qs hl hu _ ih =>
    rw [ih, dOwner_child d (d.label_child hl) hu]

theorem dMarks_disjoint {r₁ r₂ : Fin d.pi.length} (hr₁ : r₁ ∈ dRoots d) (hr₂ : r₂ ∈ dRoots d)
    {c : Collision} (hc₁ : c ∈ dMarks (keyAt d) (d.dUnroll r₁))
    (hc₂ : c ∈ dMarks (keyAt d) (d.dUnroll r₂)) : r₁ = r₂ := by
  obtain ⟨j₁, qs₁, p₁, rfl⟩ := dMark_route d hc₁
  obtain ⟨j₂, qs₂, p₂, heq⟩ := dMark_route d hc₂
  have h1 := d.route_of_dUnroll p₁; have h2 := d.route_of_dUnroll p₂
  have hj : j₁ = j₂ := d.nodup.injective_get (by rw [← keyAt_clause d h1.2.1, ← keyAt_clause d h2.2.1, heq])
  subst hj
  have o1 := dOwner_of_localPath d h1.1; have o2 := dOwner_of_localPath d h2.1
  rw [dOwner_root d r₁ (Finset.mem_filter.mp hr₁).2.2] at o1
  rw [dOwner_root d r₂ (Finset.mem_filter.mp hr₂).2.2] at o2
  exact o1.symm.trans o2

theorem dUnroll_exit_props (i j : Fin d.pi.length) (hc : 1 ≤ countExit j (d.dUnroll i)) :
    i < j ∧ j ∈ dRoots d ∧ j ≠ d.root := by
  have aux (n : ℕ) : ∀ (i : Fin d.pi.length), d.pi.length - i.val = n →
      1 ≤ countExit j (d.dUnroll i) → i < j ∧ j ∈ dRoots d ∧ j ≠ d.root := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hn hc
      have sub (k : Fin d.pi.length) (lt : i < k) (hck : 1 ≤ countExit j (d.dCutChild k)) :
          i < j ∧ j ∈ dRoots d ∧ j ≠ d.root := by
        unfold ShortestDag.dCutChild at hck
        by_cases hax : d.children k = []
        · rw [ite_eq_left hax] at hck; by_cases h1 : d.incoming k = 1 <;> simp [h1, countExit] at hck
        · rw [ite_eq_right hax] at hck
          by_cases h1 : d.incoming k = 1
          · rw [ite_eq_left h1] at hck
            have hb := k.isLt; have hlt : i.val < k.val := lt
            obtain ⟨h1', h2', h3'⟩ := ih _ (by omega) k rfl hck
            exact ⟨lt.trans h1', h2', h3'⟩
          · rw [ite_eq_right h1] at hck
            simp only [countExit] at hck
            have heq : k = j := by by_contra hne; rw [ite_eq_right hne] at hck; omega
            subst heq
            have hne_r : k ≠ d.root := fun e => by
              have hlt : i.val < k.val := lt; rw [e, d.root_val_zero] at hlt; omega
            exact ⟨lt, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax, h1⟩, hne_r⟩
      cases hr : d.rules i with
      | ax _ => rw [d.dUnroll_ax hr] at hc; by_cases h1 : d.incoming i = 1 <;> simp [h1, countExit] at hc
      | weak k hk _ => rw [d.dUnroll_weak hr] at hc; exact sub k hk hc
      | res k l hk hl _ =>
        rw [d.dUnroll_res hr] at hc; simp only [countExit] at hc
        by_cases h1 : 1 ≤ countExit j (d.dCutChild k)
        · exact sub k hk h1
        · exact sub l hl (by omega)
  exact aux _ i rfl hc

theorem exitWeightSum_eq_sum_dRoots (f : Fin d.pi.length → ℕ) (i : Fin d.pi.length) :
    exitWeightSum f (d.dUnroll i) = ∑ j ∈ dRoots d, countExit j (d.dUnroll i) * f j := by
  have aux : ∀ (t : DTree Variable (Fin d.pi.length)),
      (∀ j, 1 ≤ countExit j t → j ∈ dRoots d) →
      exitWeightSum f t = ∑ j ∈ dRoots d, countExit j t * f j := by
    intro t; induction t with
    | axUniq _ | axRep _ => intro _; simp [exitWeightSum, countExit]
    | exitDer k =>
      intro hmem
      have hk : k ∈ dRoots d := hmem k (by simp [countExit])
      simp only [exitWeightSum, countExit]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [hjk.symm]
      · intro hnk; exact (hnk hk).elim
    | weak _ t ih => exact ih
    | res _ _ l r ihl ihr =>
      intro hmem
      simp only [exitWeightSum, countExit, Nat.add_mul, Finset.sum_add_distrib]
      rw [ihl (fun j hj => hmem j (by simp [countExit]; omega)),
          ihr (fun j hj => hmem j (by simp [countExit]; omega))]
  exact aux (d.dUnroll i) (fun j hj => (dUnroll_exit_props d i j hj).2.1)

theorem hasCollision_clauseState_ax {i : Fin d.pi.length} (hax : d.children i = []) :
    hasCollision (clauseState (d.pi.get i)) := by
  let c := keyAt d i
  have heq : c.clause = d.pi.get i := keyAt_clause d hax
  have hU := d.nonTaut i
  have get_l (b : Fin 2) : clauseState (d.pi.get i) (c.left, b) = some (bits c.hole b) :=
    (clauseState_some_iff hU (c.left, b) (bits c.hole b)).mpr (heq ▸ (Collision.mem_clause_bit c b).1)
  have get_r (b : Fin 2) : clauseState (d.pi.get i) (c.right, b) = some (bits c.hole b) :=
    (clauseState_some_iff hU (c.right, b) (bits c.hole b)).mpr (heq ▸ (Collision.mem_clause_bit c b).2)
  exact ⟨c.left, c.right, c.ordered, c.hole, ⟨get_l 0, get_l 1⟩, ⟨get_r 0, get_r 1⟩⟩

theorem hasCollision_of_le {ρ₁ ρ₂ : State} (hc : hasCollision ρ₁) (hle : State.Le ρ₁ ρ₂) :
    hasCollision ρ₂ := by
  obtain ⟨u, v, huv, h, ⟨hu0, hu1⟩, ⟨hv0, hv1⟩⟩ := hc
  exact ⟨u, v, huv, h, ⟨hle _ _ hu0, hle _ _ hu1⟩, ⟨hle _ _ hv0, hle _ _ hv1⟩⟩

theorem dUnroll_dValid (ow : Finset Collision) (wt : Fin d.pi.length → ℕ)
    (i : Fin d.pi.length) (ρ : State)
    (hle : State.Le (clauseState (d.pi.get i)) ρ)
    (hsh : SignedShared (dMarks (keyAt d) (d.dUnroll i)) ρ)
    (hsub : ∀ c ∈ dMarks (keyAt d) (d.dUnroll i), c ∈ ow)
    (hwt : ∀ j ρ_leaf, 1 ≤ countExit j (d.dUnroll i) →
      State.Le (clauseState (d.pi.get j)) ρ_leaf → leafWeight ρ_leaf ow ≤ wt j) :
    DValid (fun u => clauseState (d.pi.get u)) (keyAt d) ow wt ρ (d.dUnroll i) := by
  have aux (n : ℕ) : ∀ (i : Fin d.pi.length) (ρ : State), d.pi.length - i.val = n →
      State.Le (clauseState (d.pi.get i)) ρ →
      SignedShared (dMarks (keyAt d) (d.dUnroll i)) ρ →
      (∀ c ∈ dMarks (keyAt d) (d.dUnroll i), c ∈ ow) →
      (∀ j ρ_leaf, 1 ≤ countExit j (d.dUnroll i) →
        State.Le (clauseState (d.pi.get j)) ρ_leaf → leafWeight ρ_leaf ow ≤ wt j) →
      DValid (fun u => clauseState (d.pi.get u)) (keyAt d) ow wt ρ (d.dUnroll i) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i ρ hn hle hsh hsub hwt
      have sub (k : Fin d.pi.length) (lt : i < k) (ρk : State)
          (hlek : State.Le (clauseState (d.pi.get k)) ρk)
          (hshk : SignedShared (dMarks (keyAt d) (d.dCutChild k)) ρk)
          (hsubk : ∀ c ∈ dMarks (keyAt d) (d.dCutChild k), c ∈ ow)
          (hwtk : ∀ j ρ_leaf, 1 ≤ countExit j (d.dCutChild k) →
            State.Le (clauseState (d.pi.get j)) ρ_leaf → leafWeight ρ_leaf ow ≤ wt j) :
          DValid (fun u => clauseState (d.pi.get u)) (keyAt d) ow wt ρk (d.dCutChild k) := by
        unfold ShortestDag.dCutChild at hshk hsubk hwtk ⊢
        by_cases hax : d.children k = []
        · rw [ite_eq_left hax] at hshk hsubk hwtk ⊢
          have hc := hasCollision_of_le (hasCollision_clauseState_ax d hax) hlek
          by_cases h1 : d.incoming k = 1
          · rw [ite_eq_left h1] at hshk hsubk ⊢
            exact .axUniq k ρk hc (hsubk _ (by simp [dMarks])) hshk
          · rw [ite_eq_right h1]; exact .axRep k ρk hc
        · rw [ite_eq_right hax] at hshk hsubk hwtk ⊢
          by_cases h1 : d.incoming k = 1
          · rw [ite_eq_left h1] at hshk hsubk hwtk ⊢
            have hb := k.isLt; have hlt : i.val < k.val := lt
            exact ih _ (by omega) k ρk rfl hlek hshk hsubk hwtk
          · rw [ite_eq_right h1] at hwtk ⊢
            exact .exitDer k ρk hlek (hwtk k ρk (by simp [countExit]) hlek)
      cases hr : d.rules i with
      | ax _ =>
        have hax : d.children i = [] := by simp [ShortestDag.children, hr, Rule.parents]
        have hc := hasCollision_of_le (hasCollision_clauseState_ax d hax) hle
        rw [d.dUnroll_ax hr] at hsh hsub ⊢
        by_cases h1 : d.incoming i = 1
        · rw [ite_eq_left h1] at hsh hsub ⊢
          exact .axUniq i ρ hc (hsub _ (by simp [dMarks])) hsh
        · rw [ite_eq_right h1]; exact .axRep i ρ hc
      | weak k hk _ =>
        rw [d.dUnroll_weak hr] at hsh hsub hwt ⊢
        have hshk : SignedShared (dMarks (keyAt d) (d.dCutChild k)) (clauseState (d.pi.get k)) := by
          unfold ShortestDag.dCutChild
          by_cases hax : d.children k = []
          · rw [ite_eq_left hax]; by_cases h1 : d.incoming k = 1
            · rw [ite_eq_left h1]
              exact signedShared_of_clause (d.nonTaut k) _ (fun c hc ph => by
                simp only [dMarks, List.mem_singleton] at hc; rw [hc, ← keyAt_clause d hax]; exact sample_falsifies _ ph)
            · rw [ite_eq_right h1]; intro _ _ _ _ hc; simp [dMarks] at hc
          · rw [ite_eq_right hax]; by_cases h1 : d.incoming k = 1
            · rw [ite_eq_left h1]; exact signedShared_of_clause (d.nonTaut k) _ (dMarks_false d k)
            · rw [ite_eq_right h1]; intro _ _ _ _ hc; simp [dMarks] at hc
        exact .weak i ρ (clauseState (d.pi.get k)) (d.dCutChild k) hsh
          (sub k hk (clauseState (d.pi.get k)) (State.Le.refl _) hshk hsub hwt)
      | res j k hj hk hres =>
        let f := Classical.choose hres
        have hspec := Classical.choose_spec hres
        have hcarry := carry_state (d.nonTaut j) (d.nonTaut k) (d.nonTaut i) hspec hle
        have hnd := dMarks_nodup d i
        rw [d.dUnroll_res hr] at hnd hsh hsub hwt ⊢
        have hsh_l : SignedShared (dMarks (keyAt d) (d.dCutChild j)) (State.grant ρ f true) := by
          apply signedShared_grant (signedShared_mono hsh (fun c hc => List.mem_append_right _ hc))
          intro c hc phase
          obtain ⟨a_idx, qs, path, rfl⟩ := dMark_route d hc
          have hpath : DTree.Route (d.dUnroll i) a_idx (some (f, true) :: qs) := by
            rw [d.dUnroll_res hr]; exact .left path
          have hact := d.dUnroll_route_active (sample (keyAt d a_idx) phase) hpath (fun C hC hf => by
            rw [← keyAt_clause d (d.route_of_dUnroll hpath).2.1]
            exact sample_only_axiom (keyAt d a_idx) phase hC hf)
          exact hact.2 (some (f, true)) List.mem_cons_self
        have hsh_r : SignedShared (dMarks (keyAt d) (d.dCutChild k)) (State.grant ρ f false) := by
          apply signedShared_grant (signedShared_mono hsh (fun c hc => List.mem_append_left _ hc))
          intro c hc phase
          obtain ⟨a_idx, qs, path, rfl⟩ := dMark_route d hc
          have hpath : DTree.Route (d.dUnroll i) a_idx (some (f, false) :: qs) := by
            rw [d.dUnroll_res hr]; exact .right path
          have hact := d.dUnroll_route_active (sample (keyAt d a_idx) phase) hpath (fun C hC hf => by
            rw [← keyAt_clause d (d.route_of_dUnroll hpath).2.1]
            exact sample_only_axiom (keyAt d a_idx) phase hC hf)
          exact hact.2 (some (f, false)) List.mem_cons_self
        exact .res i f ρ (d.dCutChild j) (d.dCutChild k) hnd hsh
          (sub j hj (State.grant ρ f true) hcarry.1 hsh_l
            (fun c hc => hsub c (List.mem_append_right _ hc))
            (fun q ρl hcq => hwt q ρl (by simp [countExit]; omega)))
          (sub k hk (State.grant ρ f false) hcarry.2 hsh_r
            (fun c hc => hsub c (List.mem_append_left _ hc))
            (fun q ρl hcq => hwt q ρl (by simp [countExit]; omega)))
  exact aux _ i ρ rfl hle hsh hsub hwt

/-- A pure derived root with k = 1 cannot already contain a collision in its clause. -/
theorem nonAx_not_hasCollision_of_pure {r : Fin d.pi.length} (hr : r ∈ dRoots d)
    (hpure : dWeaks (d.dUnroll r) = 0) {c : Collision}
    (hm : dMarks (keyAt d) (d.dUnroll r) = [c]) :
    ¬ hasCollision (clauseState (d.pi.get r)) := by
  intro hc
  have hsh : SignedShared [c] (clauseState (d.pi.get r)) := by
    have := signedShared_of_clause (d.nonTaut r) _ (dMarks_false d r)
    rwa [hm] at this
  obtain ⟨u, v, huv, h, hu, hv⟩ := hc
  have huf := (signedShared_const (c := c) hsh (by simp) hu.1).1
  have hvf := (signedShared_const (c := c) hsh (by simp) hv.1).1
  have hpair : u = c.left ∧ v = c.right := by
    rcases huf with rfl | rfl <;> rcases hvf with rfl | rfl
    · exact (huv.ne rfl).elim
    · exact ⟨rfl, rfl⟩
    · exact (not_lt_of_gt c.ordered huv).elim
    · exact (huv.ne rfl).elim
  obtain ⟨rfl, rfl⟩ := hpair
  have hh : h = c.hole := bits_injective (funext fun b => by
    have := (signedShared_const (c := c) hsh (by simp) (pigeonHole_bit hu b)).2; exact this)
  subst hh
  -- Therefore c.clause ⊆ d.pi.get r!
  have hsubC : c.clause ⊆ d.pi.get r := by
    intro lit hlit
    obtain ⟨⟨⟨p, b⟩, pol⟩, hmem, rfl⟩ := Finset.mem_image.mp hlit
    simp only [pairClause, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨b', eb⟩ | ⟨b', eb⟩
    · cases eb
      exact (clauseState_some_iff (d.nonTaut r) (c.left, b) (bits c.hole b)).mp (pigeonHole_bit hu b)
    · cases eb
      exact (clauseState_some_iff (d.nonTaut r) (c.right, b) (bits c.hole b)).mp (pigeonHole_bit hv b)
  have hsubSat : ∀ a, LinClauseSat a c.clause → LinClauseSat a (d.pi.get r) :=
    fun a ⟨q, hq, hs⟩ => ⟨q, hsubC hq, hs⟩
  obtain ⟨j_c, qs, path, heq_c⟩ := dMark_route d (by rw [hm]; simp : c ∈ dMarks (keyAt d) (d.dUnroll r))
  have hrp := d.route_of_dUnroll path
  have hjc_clause : d.pi.get j_c = c.clause := by rw [heq_c, keyAt_clause d hrp.2.1]
  have hD : d.children r ≠ [] := (Finset.mem_filter.mp hr).2.1
  cases hru : d.rules r with
  | ax _ => simp [ShortestDag.children, hru, Rule.parents] at hD
  | weak _ _ _ => rw [d.dUnroll_weak hru] at hpure; simp [dWeaks] at hpure
  | res a b ha hb hres =>
    -- Case 1: j_c = a or j_c = b -> contradicts nonTaut of the other child!
    let f := Classical.choose hres
    obtain ⟨hfa, hfb, hreq⟩ := Classical.choose_spec hres
    by_cases hja : j_c = a
    · subst hja
      have hfm : (f, false) ∈ d.pi.get r := hsubC (hjc_clause ▸ hfa)
      rw [hreq, Finset.mem_union] at hfm
      rcases hfm with h1 | h2
      · exact (Finset.mem_erase.mp h1).1 rfl
      · have hfb' : (f, false) ∈ d.pi.get b := Finset.mem_of_mem_erase h2
        obtain ⟨asg, hasg⟩ := d.nonTaut b
        cases hp : testParity asg f
        · exact hasg ⟨(f, false), hfb', by simp [LinEqSat, testParity] at hp ⊢; exact hp⟩
        · exact hasg ⟨(f, true), hfb, by simp [LinEqSat, testParity] at hp ⊢; exact hp⟩
    · by_cases hjb : j_c = b
      · subst hjb
        have hfm : (f, true) ∈ d.pi.get r := hsubC (hjc_clause ▸ hfb)
        rw [hreq, Finset.mem_union] at hfm
        rcases hfm with h1 | h2
        · have hfa' : (f, true) ∈ d.pi.get a := Finset.mem_of_mem_erase h1
          obtain ⟨asg, hasg⟩ := d.nonTaut a
          cases hp : testParity asg f
          · exact hasg ⟨(f, false), hfa, by simp [LinEqSat, testParity] at hp ⊢; exact hp⟩
          · exact hasg ⟨(f, true), hfa', by simp [LinEqSat, testParity] at hp ⊢; exact hp⟩
        · exact (Finset.mem_erase.mp h2).1 rfl
      · -- Case 2: first step of LocalPath r j_c goes to some ch ∈ d.children r with incoming ch = 1 and ch ≠ j_c!
        cases hlp : hrp.1 with
        | nil => exact hD hrp.2.1
        | @cons _ ch _ q' qs' hlbl hinc rest =>
          have hch_mem : ch ∈ d.children r := d.label_child hlbl
          have hch_ne : ch ≠ j_c := by
            simp [ShortestDag.children, hru, Rule.parents] at hch_mem
            rcases hch_mem with rfl | rfl
            · exact Ne.symm hja
            · exact Ne.symm hjb
          have hlt : r < j_c := by
            have aux_lt : ∀ {x y : Fin d.pi.length} {rs}, d.LocalPath x y rs → x ≤ y := by
              intro x y rs p; induction p with
              | nil _ => exact le_rfl
              | @cons x y z _ _ hl _ _ ih => exact (d.children_lt x y (d.label_child hl)).le.trans ih
            exact (d.children_lt r ch hch_mem).trans_le (aux_lt rest)
          exact d.nonAx_not_subsumed_by_child_ax ⟨a, b, ha, hb, hres, hru⟩
            (by rw [hjc_clause]; exact hsubSat) hlt ⟨ch, hch_mem, hinc, hch_ne⟩

end DComponents

/-! ## Section 5: Global Charge Accounting & Local Bound -/

namespace GlobalCharge

open PEqualNP.ProofComplexity Dag BPHP Potential DComponents
open scoped BigOperators Classical

variable (d : ShortestDag Formula)

noncomputable abbrev st (r : Fin d.pi.length) : State := clauseState (d.pi.get r)
noncomputable abbrev M_list (r : Fin d.pi.length) : List Collision := dMarks (keyAt d) (d.dUnroll r)
noncomputable abbrev M (r : Fin d.pi.length) : Finset Collision := (M_list d r).toFinset
noncomputable abbrev k (r : Fin d.pi.length) : ℕ := (M_list d r).length
noncomputable abbrev e (r : Fin d.pi.length) : ℕ := dExits (d.dUnroll r)
noncomputable abbrev a (r : Fin d.pi.length) : ℕ := dAxReps (d.dUnroll r)
noncomputable abbrev w (r : Fin d.pi.length) : ℕ := dWeaks (d.dUnroll r)

theorem k_le_four (r : Fin d.pi.length) : k d r ≤ 4 := by
  have h := Finset.card_le_univ ((M_list d r).map Collision.hole).toFinset
  rw [List.toFinset_card_of_nodup (dMarks_nodup d r), List.length_map, Fintype.card_fin] at h
  exact h

theorem st_shared (r : Fin d.pi.length) : SignedShared (M_list d r) (st d r) :=
  signedShared_of_clause (d.nonTaut r) _ (dMarks_false d r)

def isH2 (r : Fin d.pi.length) : Prop :=
  r ∈ dRoots d ∧ r ≠ d.root ∧ k d r = 2 ∧ ∃ u v b val, sameBitPair (st d r) u v b val

def isH1_d3 (r : Fin d.pi.length) : Prop :=
  r ∈ dRoots d ∧ r ≠ d.root ∧ k d r = 1 ∧ ¬ hasCollision (st d r) ∧ 3 ≤ fixedBits (st d r)

def isH1_d2 (r : Fin d.pi.length) : Prop :=
  r ∈ dRoots d ∧ r ≠ d.root ∧ k d r = 1 ∧ ¬ hasCollision (st d r) ∧
    fixedBits (st d r) = 2 ∧ ∃ u v b val, sameBitPair (st d r) u v b val

noncomputable def cOf (r : Fin d.pi.length) : Collision :=
  (M_list d r).headD ⟨0, 1, 0, by decide⟩

theorem M_list_eq_cOf {r : Fin d.pi.length} (hk1 : k d r = 1) :
    M_list d r = [cOf d r] := by
  unfold cOf
  rcases h : M_list d r with _ | ⟨c, rest⟩
  · simp [k, h] at hk1
  · have hr : rest = [] := by simpa [k, h] using hk1
    subst hr; rfl

theorem cOf_mem_M {r : Fin d.pi.length} (hk1 : k d r = 1) : cOf d r ∈ M d r := by
  rw [M, M_list_eq_cOf d hk1]; simp

theorem sameBitPair_of_k1_fb3 {c : Collision} {ρ : State}
    (hs : SignedShared [c] ρ) (hnc : ¬ hasCollision ρ) (h3 : 3 ≤ fixedBits ρ) :
    fixedBits ρ = 3 ∧ ∃ b : Fin 2, sameBitPair ρ c.left c.right b (bits c.hole b) := by
  have hle4 := fixedBits_le_four_of_shared (c := c) hs (by simp)
  have hfb3 : fixedBits ρ = 3 := by
    by_contra hne; exact hnc (hasCollision_of_fixedBits_four (c := c) hs (by simp) (by omega))
  refine ⟨hfb3, ?_⟩
  -- Among the 4 variables {(c.left,0),(c.left,1),(c.right,0),(c.right,1)}, 3 are fixed -> one bit has both fixed!
  have hsub : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆
      ({(c.left, 0), (c.left, 1), (c.right, 0), (c.right, 1)} : Finset Variable) := by
    intro v hv; cases h : ρ v with
    | none => exact ((Finset.mem_filter.mp hv).2 h).elim
    | some val =>
      have h1 := (signedShared_const (c := c) hs (by simp) h).1
      rcases v with ⟨p, b⟩; change p = c.left ∨ p = c.right at h1
      rcases h1 with rfl | rfl <;> fin_cases b <;> simp
  have hget : ∀ p b, (p = c.left ∨ p = c.right) → ρ (p, b) ≠ none → ρ (p, b) = some (bits c.hole b) := by
    intro p b _ hne; cases h : ρ (p, b) with
    | none => exact (hne h).elim
    | some val => rw [(signedShared_const (c := c) hs (by simp) h).2]
  by_cases h0 : ρ (c.left, 0) ≠ none ∧ ρ (c.right, 0) ≠ none
  · exact ⟨0, c.ordered, hget _ 0 (Or.inl rfl) h0.1, hget _ 0 (Or.inr rfl) h0.2⟩
  · by_cases h1 : ρ (c.left, 1) ≠ none ∧ ρ (c.right, 1) ≠ none
    · exact ⟨1, c.ordered, hget _ 1 (Or.inl rfl) h1.1, hget _ 1 (Or.inr rfl) h1.2⟩
    · exfalso
      -- At least one of bit 0 is none AND at least one of bit 1 is none -> ≤ 2 fixed bits!
      have hle2 : (Finset.univ.filter (fun v : Variable => ρ v ≠ none)).card ≤ 2 := by
        have hnot0 : ρ (c.left, 0) = none ∨ ρ (c.right, 0) = none := by
          by_contra h'; push Not at h'; exact h0 h'
        have hnot1 : ρ (c.left, 1) = none ∨ ρ (c.right, 1) = none := by
          by_contra h'; push Not at h'; exact h1 h'
        rcases hnot0 with e0 | e0 <;> rcases hnot1 with e1 | e1
        · have hs' : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ {(c.right, 0), (c.right, 1)} := by
            intro v hv; have hm := hsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact ((Finset.mem_filter.mp hv).2 e0).elim
            · exact ((Finset.mem_filter.mp hv).2 e1).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
          exact (Finset.card_le_card hs').trans Finset.card_le_two
        · have hs' : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ {(c.right, 0), (c.left, 1)} := by
            intro v hv; have hm := hsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact ((Finset.mem_filter.mp hv).2 e0).elim
            · exact Or.inr rfl
            · exact Or.inl rfl
            · exact ((Finset.mem_filter.mp hv).2 e1).elim
          exact (Finset.card_le_card hs').trans Finset.card_le_two
        · have hs' : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ {(c.left, 0), (c.right, 1)} := by
            intro v hv; have hm := hsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact ((Finset.mem_filter.mp hv).2 e1).elim
            · exact ((Finset.mem_filter.mp hv).2 e0).elim
            · exact Or.inr rfl
          exact (Finset.card_le_card hs').trans Finset.card_le_two
        · have hs' : Finset.univ.filter (fun v : Variable => ρ v ≠ none) ⊆ {(c.left, 0), (c.left, 1)} := by
            intro v hv; have hm := hsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact ((Finset.mem_filter.mp hv).2 e0).elim
            · exact ((Finset.mem_filter.mp hv).2 e1).elim
          exact (Finset.card_le_card hs').trans Finset.card_le_two
      change fixedBits ρ ≤ 2 at hle2; omega

noncomputable def bOf (r : Fin d.pi.length) : Fin 2 :=
  if sameBitPair (st d r) (cOf d r).left (cOf d r).right 0 (bits (cOf d r).hole 0) then 0 else 1

noncomputable def twinOf (r : Fin d.pi.length) : Collision :=
  ⟨(cOf d r).left, (cOf d r).right, flipBit (cOf d r).hole (otherBit (bOf d r)), (cOf d r).ordered⟩

theorem sameBitPair_bOf {r : Fin d.pi.length} (h : isH1_d3 d r ∨ isH1_d2 d r) :
    sameBitPair (st d r) (cOf d r).left (cOf d r).right (bOf d r) (bits (cOf d r).hole (bOf d r)) := by
  have hk1 : k d r = 1 := by rcases h with h | h <;> exact h.2.2.1
  have hsh : SignedShared [cOf d r] (st d r) := M_list_eq_cOf d hk1 ▸ st_shared d r
  have hex : ∃ b : Fin 2, sameBitPair (st d r) (cOf d r).left (cOf d r).right b (bits (cOf d r).hole b) := by
    rcases h with h3 | h2
    · exact (sameBitPair_of_k1_fb3 hsh h3.2.2.2.1 h3.2.2.2.2).2
    · obtain ⟨u, v, b, val, huv, hu, hv⟩ := h2.2.2.2.2.2
      have hcu := signedShared_const (c := cOf d r) hsh (by simp) hu
      have hcv := signedShared_const (c := cOf d r) hsh (by simp) hv
      have hpair : u = (cOf d r).left ∧ v = (cOf d r).right := by
        rcases hcu.1 with e1 | e1 <;> rcases hcv.1 with e2 | e2
        · exact (huv.ne (e1.trans e2.symm)).elim
        · exact ⟨e1, e2⟩
        · exact (not_lt_of_gt (cOf d r).ordered (e1 ▸ e2 ▸ huv)).elim
        · exact (huv.ne (e1.trans e2.symm)).elim
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨b, (cOf d r).ordered, hcu.2 ▸ hu, hcv.2 ▸ hv⟩
  obtain ⟨b, hb⟩ := hex
  unfold bOf
  by_cases h0 : sameBitPair (st d r) (cOf d r).left (cOf d r).right 0 (bits (cOf d r).hole 0)
  · rw [ite_eq_left h0]; exact h0
  · rw [ite_eq_right h0]
    fin_cases b
    · exact (h0 hb).elim
    · exact hb

theorem pairHoles_eq_cOf_twinOf {r : Fin d.pi.length} :
    pairHoles (cOf d r).left (cOf d r).right (bOf d r) (bits (cOf d r).hole (bOf d r)) =
      {cOf d r, twinOf d r} := by
  ext c; simp only [pairHoles, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hr, hb⟩
    by_cases ho : bits c.hole (otherBit (bOf d r)) = bits (cOf d r).hole (otherBit (bOf d r))
    · left
      have eh : c.hole = (cOf d r).hole := hole_eq_of_bits c.hole (cOf d r).hole (bOf d r) hb ho
      cases c; simp_all
    · right
      have eh : c.hole = flipBit (cOf d r).hole (otherBit (bOf d r)) := by
        apply hole_eq_of_bits c.hole _ (bOf d r)
        · have := (flipBit_facts (cOf d r).hole (otherBit (bOf d r))).2.2.1
          rw [(otherBit_facts (bOf d r)).2.1] at this; exact hb.trans this.symm
        · rw [(flipBit_facts (cOf d r).hole (otherBit (bOf d r))).2.1]
          cases h1 : bits c.hole (otherBit (bOf d r)) <;> cases h2 : bits (cOf d r).hole (otherBit (bOf d r)) <;> simp_all
      unfold twinOf; cases c; simp_all
  · rintro (rfl | rfl)
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, ?_⟩
      unfold twinOf
      have := (flipBit_facts (cOf d r).hole (otherBit (bOf d r))).2.2.1
      rwa [(otherBit_facts (bOf d r)).2.1] at this

theorem H2_pairHoles_eq_M {r : Fin d.pi.length} (h2 : isH2 d r) :
    ∃ u v b val, sameBitPair (st d r) u v b val ∧ pairHoles u v b val = M d r := by
  obtain ⟨_, _, hk2, u, v, b, val, huv, hu, hv⟩ := h2
  rcases hm : M_list d r with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [k, hm] at hk2
  subst hk2
  have hnd : ((M_list d r).map Collision.hole).Nodup := dMarks_nodup d r; rw [hm] at hnd
  have hne : c₁.hole ≠ c₂.hole := by simp at hnd; exact hnd
  have hsh : SignedShared [c₁, c₂] (st d r) := hm ▸ st_shared d r
  have h1u := signedShared_const (c := c₁) hsh (by simp) hu
  have h1v := signedShared_const (c := c₁) hsh (by simp) hv
  have h2u := signedShared_const (c := c₂) hsh (by simp) hu
  have h2v := signedShared_const (c := c₂) hsh (by simp) hv
  have hp1 : u = c₁.left ∧ v = c₁.right := by
    rcases h1u.1 with e1 | e1 <;> rcases h1v.1 with e2 | e2
    · exact (huv.ne (e1.trans e2.symm)).elim
    · exact ⟨e1, e2⟩
    · exact (not_lt_of_gt c₁.ordered (e1 ▸ e2 ▸ huv)).elim
    · exact (huv.ne (e1.trans e2.symm)).elim
  have hp2 : u = c₂.left ∧ v = c₂.right := by
    rcases h2u.1 with e1 | e1 <;> rcases h2v.1 with e2 | e2
    · exact (huv.ne (e1.trans e2.symm)).elim
    · exact ⟨e1, e2⟩
    · exact (not_lt_of_gt c₂.ordered (e1 ▸ e2 ▸ huv)).elim
    · exact (huv.ne (e1.trans e2.symm)).elim
  refine ⟨u, v, b, val, ⟨huv, hu, hv⟩, ?_⟩
  have hM : M d r = {c₁, c₂} := by simp [M, hm]
  rw [hM]; ext c
  simp only [pairHoles, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hr, hb⟩
    have ho_ne : bits c₁.hole (otherBit b) ≠ bits c₂.hole (otherBit b) := fun eo =>
      hne (hole_eq_of_bits c₁.hole c₂.hole b (h1u.2.symm.trans h2u.2) eo)
    by_cases h1 : bits c.hole (otherBit b) = bits c₁.hole (otherBit b)
    · left; have eh := hole_eq_of_bits c.hole c₁.hole b (hb.trans h1u.2) h1
      cases c; simp_all
    · right
      have h2' : bits c.hole (otherBit b) = bits c₂.hole (otherBit b) := by
        cases a1 : bits c.hole (otherBit b) <;> cases a2 : bits c₁.hole (otherBit b) <;>
          cases a3 : bits c₂.hole (otherBit b) <;> simp_all
      have eh := hole_eq_of_bits c.hole c₂.hole b (hb.trans h2u.2) h2'
      cases c; cases c₂; simp_all
  · rintro (rfl | rfl)
    · exact ⟨hp1.1.symm, hp1.2.symm, h1u.2.symm⟩
    · exact ⟨hp2.1.symm, hp2.2.symm, h2u.2.symm⟩

noncomputable def edgeCh (r j : Fin d.pi.length) : ℕ :=
  if isH2 d j then 3
  else if isH1_d3 d j ∨ isH1_d2 d j then (if twinOf d j ∈ M d r then 2 else 3)
  else 0

noncomputable def wt (r j : Fin d.pi.length) : ℕ := 6 - edgeCh d r j

theorem edgeCh_add_wt (r j : Fin d.pi.length) : edgeCh d r j + wt d r j = 6 := by
  unfold wt edgeCh; split_ifs <;> omega

theorem wt_ge_three (r j : Fin d.pi.length) : 3 ≤ wt d r j := by
  unfold wt edgeCh; split_ifs <;> omega

theorem leafWeight_le_wt {r j : Fin d.pi.length} (hr : r ∈ dRoots d) (hj : j ∈ dRoots d)
    (hne : j ≠ r) {ρ_leaf : State} (hle : State.Le (st d j) ρ_leaf) :
    leafWeight ρ_leaf (M d r) ≤ wt d r j := by
  unfold wt edgeCh
  by_cases h2 : isH2 d j
  · rw [ite_eq_left h2]
    obtain ⟨u, v, b, val, ⟨huv, hu, hv⟩, hph⟩ := H2_pairHoles_eq_M d h2
    have hsp : sameBitPair ρ_leaf u v b val := ⟨huv, hle _ _ hu, hle _ _ hv⟩
    have hdj : Disjoint (pairHoles u v b val) (M d r) := by
      rw [hph]; refine Finset.disjoint_left.mpr (fun c hcj hcr => hne ?_)
      exact dMarks_disjoint d hj hr (List.mem_toFinset.mp hcj) (List.mem_toFinset.mp hcr)
    rw [leafWeight_eq_three_of_disjoint hsp hdj]
  · rw [ite_eq_right h2]
    by_cases h1 : isH1_d3 d j ∨ isH1_d2 d j
    · rw [ite_eq_left h1]
      have hspj := sameBitPair_bOf d h1
      have hsp : sameBitPair ρ_leaf (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j)) :=
        ⟨hspj.1, hle _ _ hspj.2.1, hle _ _ hspj.2.2⟩
      have hph := pairHoles_eq_cOf_twinOf d (r := j)
      have hcj_not : cOf d j ∉ M d r := fun hm => hne (dMarks_disjoint d hj hr
        (List.mem_toFinset.mp (cOf_mem_M d (by rcases h1 with h | h <;> exact h.2.2.1)))
        (List.mem_toFinset.mp hm))
      by_cases htw : twinOf d j ∈ M d r
      · rw [ite_eq_left htw]
        have hcard : (pairHoles (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j)) ∩ M d r).card ≤ 1 := by
          rw [hph]
          have hsub : ({cOf d j, twinOf d j} ∩ M d r : Finset Collision) ⊆ {twinOf d j} := by
            intro x hx; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            rcases hx.1 with rfl | rfl
            · exact (hcj_not hx.2).elim
            · rfl
          exact (Finset.card_le_card hsub).trans (by simp)
        exact leafWeight_le_four_of_card_le_one hsp hcard
      · rw [ite_eq_right htw]
        have hdj : Disjoint (pairHoles (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j))) (M d r) := by
          rw [hph]; refine Finset.disjoint_left.mpr (fun x hx hxr => ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl; exact hcj_not hxr; exact htw hxr
        rw [leafWeight_eq_three_of_disjoint hsp hdj]
    · rw [ite_eq_right h1]; exact leafWeight_le_six ρ_leaf (M d r)

theorem dValid_at_root {r : Fin d.pi.length} (hr : r ∈ dRoots d) :
    DValid (st d) (keyAt d) (M d r) (wt d r) (st d r) (d.dUnroll r) :=
  dUnroll_dValid d (M d r) (wt d r) r (st d r) (State.Le.refl _) (st_shared d r)
    (fun c hc => List.mem_toFinset.mpr hc)
    (fun j ρl hcj hle => by
      have hp := dUnroll_exit_props d r j hcj
      exact leafWeight_le_wt d hr hp.2.1 hp.1.ne' hle)

noncomputable def S_set (r : Fin d.pi.length) : Finset (Fin d.pi.length) :=
  (dRoots d).filter (fun j => isH1_d3 d j ∧ d.incoming j = 2 ∧
    countExit j (d.dUnroll r) = 2 ∧ twinOf d j ∈ M d r)

theorem S_set_wt_four {r j : Fin d.pi.length} (hj : j ∈ S_set d r) : wt d r j = 4 := by
  have hp := (Finset.mem_filter.mp hj).2
  have hnot2 : ¬ isH2 d j := fun h2 => by have := h2.2.2.1; have := hp.1.2.2.1; omega
  unfold wt edgeCh
  rw [ite_eq_right hnot2, ite_eq_left (Or.inl hp.1), ite_eq_left hp.2.2.2]

theorem S_set_lw_le_four {r j : Fin d.pi.length} (hr : r ∈ dRoots d) (hj : j ∈ S_set d r)
    {ρ' : State} (hle : State.Le (st d j) ρ') : leafWeight ρ' (M d r) ≤ 4 := by
  have hp := (Finset.mem_filter.mp hj).2
  have hex := dUnroll_exit_props d r j (by omega : 1 ≤ countExit j (d.dUnroll r))
  have h := leafWeight_le_wt d hr hex.2.1 hex.1.ne' hle
  rwa [S_set_wt_four d hj] at h

theorem S_set_count_eq (r : Fin d.pi.length) :
    countExitsIn (S_set d r) (d.dUnroll r) = 2 * (S_set d r).card := by
  rw [countExitsIn_sum]
  have h := Finset.sum_congr (s₁ := S_set d r) rfl (fun j hj => (Finset.mem_filter.mp hj).2.2.2.1)
  rw [h, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem sum_inCharge_le :
    (∑ j ∈ dRoots d, ((if isH2 d j then 6 else 0) + (if isH1_d3 d j then 5 else 0) + (if isH1_d2 d j then 4 else 0))) ≤
    (∑ r ∈ dRoots d, exitWeightSum (edgeCh d r) (d.dUnroll r)) + ∑ r ∈ dRoots d, (S_set d r).card := by
  classical
  simp_rw [exitWeightSum_eq_sum_dRoots]
  rw [Finset.sum_comm]
  have hS_comm : (∑ r ∈ dRoots d, (S_set d r).card) =
      ∑ j ∈ dRoots d, ((dRoots d).filter (fun r => j ∈ S_set d r)).card := by
    trans (∑ r ∈ dRoots d, ∑ j ∈ dRoots d, if j ∈ S_set d r then 1 else 0)
    · apply Finset.sum_congr rfl; intro r _
      rw [← Finset.card_filter]
      congr 1; ext j
      exact ⟨fun h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, h⟩, fun h => (Finset.mem_filter.mp h).2⟩
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.card_filter]
  rw [hS_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j hj
  have hnot_both : ¬ (isH1_d3 d j ∧ isH1_d2 d j) := fun ⟨h3, h2⟩ => by
    have := h3.2.2.2.2; have := h2.2.2.2.2.1; omega
  by_cases h2 : isH2 d j
  · have hn3 : ¬ isH1_d3 d j := fun h => by have := h2.2.2.1; have := h.2.2.1; omega
    have hn2 : ¬ isH1_d2 d j := fun h => by have := h2.2.2.1; have := h.2.2.1; omega
    simp only [ite_eq_left h2, ite_eq_right hn3, ite_eq_right hn2, Nat.add_zero]
    have hch : ∀ r, edgeCh d r j = 3 := fun r => by unfold edgeCh; rw [ite_eq_left h2]
    simp_rw [hch, ← Finset.sum_mul, sum_countExit d j hj]
    have hpos := d.incoming_pos j (fun h => h2.2.1 (Fin.ext (h.trans d.root_val_zero.symm)))
    have hne1 := (Finset.mem_filter.mp hj).2.2
    omega
  · rw [ite_eq_right h2, Nat.zero_add]
    by_cases h13 : isH1_d3 d j
    · have hn12 : ¬ isH1_d2 d j := fun h => hnot_both ⟨h13, h⟩
      rw [ite_eq_left h13, ite_eq_right hn12, Nat.add_zero]
      have hpos := d.incoming_pos j (fun h => h13.2.1 (Fin.ext (h.trans d.root_val_zero.symm)))
      have hne1 := (Finset.mem_filter.mp hj).2.2
      have hge2 : 2 ≤ d.incoming j := by omega
      have hch_ge2 : ∀ r, 2 ≤ edgeCh d r j := fun r => by
        unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inl h13)]; split_ifs <;> omega
      by_cases hge3 : 3 ≤ d.incoming j
      · have hlb : 2 * d.incoming j ≤ ∑ r ∈ dRoots d, countExit j (d.dUnroll r) * edgeCh d r j := by
          rw [← sum_countExit d j hj, Finset.mul_sum]
          apply Finset.sum_le_sum; intro r _; have := hch_ge2 r; rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this
        omega
      · have heq2 : d.incoming j = 2 := by omega
        have hsum2 : (∑ r ∈ dRoots d, countExit j (d.dUnroll r)) = 2 := by rw [sum_countExit d j hj, heq2]
        by_cases hex2 : ∃ r ∈ dRoots d, countExit j (d.dUnroll r) = 2
        · obtain ⟨r0, hr0, hcnt2⟩ := hex2
          have hterm := Finset.single_le_sum (f := fun r => countExit j (d.dUnroll r) * edgeCh d r j) (fun _ _ => Nat.zero_le _) hr0
          by_cases htw : twinOf d j ∈ M d r0
          · have hch2 : edgeCh d r0 j = 2 := by unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inl h13), ite_eq_left htw]
            have hmemS : r0 ∈ (dRoots d).filter (fun r => j ∈ S_set d r) := by
              refine Finset.mem_filter.mpr ⟨hr0, Finset.mem_filter.mpr ⟨hj, h13, heq2, hcnt2, htw⟩⟩
            have hcard1 : 1 ≤ ((dRoots d).filter (fun r => j ∈ S_set d r)).card := Finset.card_pos.mpr ⟨r0, hmemS⟩
            rw [hcnt2, hch2] at hterm; omega
          · have hch3 : edgeCh d r0 j = 3 := by unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inl h13), ite_eq_right htw]
            rw [hcnt2, hch3] at hterm; omega
        · -- No single r has count = 2 -> two distinct r₁ ≠ r₂ each have count = 1!
          have hall_le1 : ∀ r ∈ dRoots d, countExit j (d.dUnroll r) ≤ 1 := by
            intro r hr
            have hle2 := Finset.single_le_sum (f := fun x => countExit j (d.dUnroll x)) (fun _ _ => Nat.zero_le _) hr
            rw [hsum2] at hle2
            have hne2 : countExit j (d.dUnroll r) ≠ 2 := fun e => hex2 ⟨r, hr, e⟩
            omega
          have hex1 : ∃ r₁ ∈ dRoots d, countExit j (d.dUnroll r₁) = 1 := by
            by_contra hno; push Not at hno
            have hz : (∑ r ∈ dRoots d, countExit j (d.dUnroll r)) = 0 := Finset.sum_eq_zero (fun r hr => by
              have := hall_le1 r hr; have := hno r hr; omega)
            omega
          obtain ⟨r₁, hr1, hc1⟩ := hex1
          have hex1' : ∃ r₂ ∈ (dRoots d).erase r₁, countExit j (d.dUnroll r₂) = 1 := by
            by_contra hno; push Not at hno
            have her := Finset.add_sum_erase (dRoots d) (fun r => countExit j (d.dUnroll r)) hr1
            have hz : (∑ r ∈ (dRoots d).erase r₁, countExit j (d.dUnroll r)) = 0 := Finset.sum_eq_zero (fun r hr => by
              have := hall_le1 r (Finset.mem_of_mem_erase hr); have := hno r hr; omega)
            omega
          obtain ⟨r₂, hr2e, hc2⟩ := hex1'
          have hne12 : r₂ ≠ r₁ := Finset.ne_of_mem_erase hr2e
          have hr2 : r₂ ∈ dRoots d := Finset.mem_of_mem_erase hr2e
          have hnot_both_tw : ¬ (twinOf d j ∈ M d r₁ ∧ twinOf d j ∈ M d r₂) := fun ⟨m1, m2⟩ =>
            hne12 (dMarks_disjoint d hr2 hr1 (List.mem_toFinset.mp m2) (List.mem_toFinset.mp m1))
          have hsub : ({r₁, r₂} : Finset (Fin d.pi.length)) ⊆ dRoots d := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
          have hsum_pair := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => countExit j (d.dUnroll r) * edgeCh d r j) hsub (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hne12.symm, hc1, hc2, Nat.one_mul, Nat.one_mul] at hsum_pair
          have h5 : 5 ≤ edgeCh d r₁ j + edgeCh d r₂ j := by
            have h1' : edgeCh d r₁ j = if twinOf d j ∈ M d r₁ then 2 else 3 := by
              unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inl h13)]
            have h2' : edgeCh d r₂ j = if twinOf d j ∈ M d r₂ then 2 else 3 := by
              unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inl h13)]
            rw [h1', h2']; split_ifs with m1 m2
            · exact (hnot_both_tw ⟨m1, m2⟩).elim
            · omega
            · omega
            · omega
          omega
    · rw [ite_eq_right h13, Nat.zero_add]
      by_cases h12 : isH1_d2 d j
      · rw [ite_eq_left h12]
        have hpos := d.incoming_pos j (fun h => h12.2.1 (Fin.ext (h.trans d.root_val_zero.symm)))
        have hne1 := (Finset.mem_filter.mp hj).2.2
        have hch_ge2 : ∀ r, 2 ≤ edgeCh d r j := fun r => by
          unfold edgeCh; rw [ite_eq_right h2, ite_eq_left (Or.inr h12)]; split_ifs <;> omega
        have hlb : 2 * d.incoming j ≤ ∑ r ∈ dRoots d, countExit j (d.dUnroll r) * edgeCh d r j := by
          rw [← sum_countExit d j hj, Finset.mul_sum]
          apply Finset.sum_le_sum; intro r _; have := hch_ge2 r; rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this
        omega
      · rw [ite_eq_right h12]; omega

def TwinEdge (p r : Fin d.pi.length) : Prop :=
  p ∈ dRoots d ∧ r ∈ dRoots d ∧ isH1_d3 d p ∧ (isH1_d3 d r ∨ isH1_d2 d r) ∧
    twinOf d r ∈ M d p ∧ 1 ≤ countExit r (d.dUnroll p) ∧ e d p = 1 ∧ w d p = 0 ∧ a d p = 0

noncomputable def outTwin (p : Fin d.pi.length) : ℕ :=
  if ∃ r, TwinEdge d p r then 1 else 0

noncomputable def inTwin (r : Fin d.pi.length) : ℕ :=
  if ∃ p, TwinEdge d p r then 1 else 0

theorem TwinEdge_unique_right {p r₁ r₂ : Fin d.pi.length}
    (h1 : TwinEdge d p r₁) (h2 : TwinEdge d p r₂) : r₁ = r₂ := by
  by_contra hne
  have hsum : (∑ j ∈ dRoots d, countExit j (d.dUnroll p)) = e d p := by
    have := exitWeightSum_eq_sum_dRoots d (fun _ => 1) p
    have heq : exitWeightSum (fun _ => 1) (d.dUnroll p) = e d p := by
      unfold e; generalize d.dUnroll p = t
      induction t <;> simp_all [exitWeightSum, dExits]
    simpa [heq] using this.symm
  have hsub : ({r₁, r₂} : Finset (Fin d.pi.length)) ⊆ dRoots d := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl; exact h1.2.1; exact h2.2.1
  have hlb := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => countExit j (d.dUnroll p)) hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hne, hsum, h1.2.2.2.2.2.2.1] at hlb
  have := h1.2.2.2.2.2.1; have := h2.2.2.2.2.2.1; omega

theorem TwinEdge_unique_left {p₁ p₂ r : Fin d.pi.length}
    (h1 : TwinEdge d p₁ r) (h2 : TwinEdge d p₂ r) : p₁ = p₂ :=
  dMarks_disjoint d h1.1 h2.1 (List.mem_toFinset.mp h1.2.2.2.2.1) (List.mem_toFinset.mp h2.2.2.2.2.1)

theorem sum_outTwin_eq_sum_inTwin :
    (∑ p ∈ dRoots d, outTwin d p) = ∑ r ∈ dRoots d, inTwin d r := by
  classical
  have hL : (∑ p ∈ dRoots d, outTwin d p) = ∑ p ∈ dRoots d, ∑ r ∈ dRoots d, if TwinEdge d p r then 1 else 0 := by
    apply Finset.sum_congr rfl; intro p _
    unfold outTwin
    by_cases h : ∃ r, TwinEdge d p r
    · obtain ⟨r0, hr0⟩ := h
      rw [ite_eq_left (⟨r0, hr0⟩ : ∃ r, TwinEdge d p r), Finset.sum_eq_single r0]
      · simp [hr0]
      · intro r _ hne; rw [ite_eq_right (fun hr => hne (TwinEdge_unique_right d hr hr0))]
      · intro hnr; exact (hnr hr0.2.1).elim
    · rw [ite_eq_right h]; symm; apply Finset.sum_eq_zero; intro r _
      rw [ite_eq_right (fun hr => h ⟨r, hr⟩)]
  have hR : (∑ r ∈ dRoots d, inTwin d r) = ∑ r ∈ dRoots d, ∑ p ∈ dRoots d, if TwinEdge d p r then 1 else 0 := by
    apply Finset.sum_congr rfl; intro r _
    unfold inTwin
    by_cases h : ∃ p, TwinEdge d p r
    · obtain ⟨p0, hp0⟩ := h
      rw [ite_eq_left (⟨p0, hp0⟩ : ∃ p, TwinEdge d p r), Finset.sum_eq_single p0]
      · simp [hp0]
      · intro p _ hne; rw [ite_eq_right (fun hp => hne (TwinEdge_unique_left d hp hp0))]
      · intro hnp; exact (hnp hp0.1).elim
    · rw [ite_eq_right h]; symm; apply Finset.sum_eq_zero; intro p _
      rw [ite_eq_right (fun hp => h ⟨p, hp⟩)]
  rw [hL, hR, Finset.sum_comm]

theorem inTwin_h1_d3_phi_ge_six {r : Fin d.pi.length} (hr : r ∈ dRoots d)
    (h13 : isH1_d3 d r) (hw0 : w d r = 0) (hin : inTwin d r = 1) :
    6 ≤ dPhi (wt d r) (d.dUnroll r) := by
  have hexp : ∃ p, TwinEdge d p r := by
    unfold inTwin at hin; by_contra h; rw [ite_eq_right h] at hin; omega
  obtain ⟨p, hp_te⟩ := hexp
  have hm := M_list_eq_cOf d h13.2.2.1
  have hsh : SignedShared [cOf d r] (st d r) := hm ▸ st_shared d r
  have hfb3 := (sameBitPair_of_k1_fb3 hsh h13.2.2.2.1 h13.2.2.2.2).1
  have hsp := sameBitPair_bOf d (Or.inl h13)
  have hcheck : ∀ j ρ_leaf, State.Le (st d j) ρ_leaf →
      ((pigeonHole ρ_leaf (cOf d r).left (cOf d r).hole ∧ pigeonHole ρ_leaf (cOf d r).right (twinOf d r).hole) ∨
       (pigeonHole ρ_leaf (cOf d r).left (twinOf d r).hole ∧ pigeonHole ρ_leaf (cOf d r).right (cOf d r).hole)) →
      countExit j (d.dUnroll r) ≥ 1 →
      leafWeight ρ_leaf {cOf d r, twinOf d r} ≤ wt d r j := by
    intro j ρ_leaf hle hholes hcj
    have hj_props := dUnroll_exit_props d r j hcj
    have hp_lt_r := (dUnroll_exit_props d p r hp_te.2.2.2.2.2.1).1
    have hj_ne_r : j ≠ r := hj_props.1.ne'
    have hj_ne_p : j ≠ p := (hp_lt_r.trans hj_props.1).ne'
    unfold wt edgeCh
    by_cases h2 : isH2 d j
    · rw [ite_eq_left h2]
      obtain ⟨u, v, b', val', hspj, hph⟩ := H2_pairHoles_eq_M d h2
      have hsp' : sameBitPair ρ_leaf u v b' val' := ⟨hspj.1, hle _ _ hspj.2.1, hle _ _ hspj.2.2⟩
      have hdj : Disjoint (pairHoles u v b' val') {cOf d r, twinOf d r} := by
        rw [hph]; refine Finset.disjoint_left.mpr (fun c hcm hcp => ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcp
        rcases hcp with rfl | rfl
        · exact hj_ne_r (dMarks_disjoint d hj_props.2.1 hr (List.mem_toFinset.mp hcm) (List.mem_toFinset.mp (cOf_mem_M d h13.2.2.1)))
        · exact hj_ne_p (dMarks_disjoint d hj_props.2.1 hp_te.1 (List.mem_toFinset.mp hcm) (List.mem_toFinset.mp hp_te.2.2.2.2.1))
      rw [leafWeight_eq_three_of_disjoint hsp' hdj]
    · rw [ite_eq_right h2]
      by_cases h1 : isH1_d3 d j ∨ isH1_d2 d j
      · rw [ite_eq_left h1]
        have hspj := sameBitPair_bOf d h1
        have hsp' : sameBitPair ρ_leaf (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j)) :=
          ⟨hspj.1, hle _ _ hspj.2.1, hle _ _ hspj.2.2⟩
        have hph := pairHoles_eq_cOf_twinOf d (r := j)
        have hcj_ne_r : cOf d j ≠ cOf d r := fun e => hj_ne_r (dMarks_disjoint d hj_props.2.1 hr
          (List.mem_toFinset.mp (cOf_mem_M d (by rcases h1 with h | h <;> exact h.2.2.1)))
          (List.mem_toFinset.mp (e ▸ cOf_mem_M d h13.2.2.1)))
        have hcj_ne_tw : cOf d j ≠ twinOf d r := fun e => hj_ne_p (dMarks_disjoint d hj_props.2.1 hp_te.1
          (List.mem_toFinset.mp (cOf_mem_M d (by rcases h1 with h | h <;> exact h.2.2.1)))
          (List.mem_toFinset.mp (e ▸ hp_te.2.2.2.2.1)))
        by_cases htw : twinOf d j ∈ M d r
        · rw [ite_eq_left htw]
          have hcard : (pairHoles (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j)) ∩ {cOf d r, twinOf d r}).card ≤ 1 := by
            rw [hph]
            have hsub : ({cOf d j, twinOf d j} ∩ {cOf d r, twinOf d r} : Finset Collision) ⊆ {twinOf d j} := by
              intro x hx; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx.1 with rfl | rfl
              · rcases hx.2 with e | e; exact (hcj_ne_r e).elim; exact (hcj_ne_tw e).elim
              · rfl
            exact (Finset.card_le_card hsub).trans (by simp)
          exact leafWeight_le_four_of_card_le_one hsp' hcard
        · rw [ite_eq_right htw]
          have htw_ne_r : twinOf d j ≠ cOf d r := fun e => htw (e ▸ cOf_mem_M d h13.2.2.1)
          have htw_ne_tw : twinOf d j ≠ twinOf d r := by
            intro e
            have hl_eq : (cOf d j).left = (cOf d r).left := (congrArg Collision.left e : (twinOf d j).left = (twinOf d r).left)
            have hr_eq : (cOf d j).right = (cOf d r).right := (congrArg Collision.right e : (twinOf d j).right = (twinOf d r).right)
            have hh_eq : flipBit (cOf d j).hole (otherBit (bOf d j)) = flipBit (cOf d r).hole (otherBit (bOf d r)) :=
              congrArg Collision.hole e
            rcases (otherBit_facts (bOf d r)).2.2 (bOf d j) with hb_eq | hb_eq
            · rw [hb_eq] at hh_eq
              have eh : (cOf d j).hole = (cOf d r).hole := by
                have := congrArg (fun x => flipBit x (otherBit (bOf d r))) hh_eq
                rwa [(flipBit_facts _ _).2.2.2, (flipBit_facts _ _).2.2.2] at this
              exact hcj_ne_r (by cases hcj' : cOf d j; cases hcr' : cOf d r; simp_all)
            · -- bOf d j = otherBit (bOf d r): then ρ_leaf has SAME bit on c_r.left and c_r.right at otherBit (bOf d r),
              -- contradicting hholes!
              rw [hl_eq, hr_eq, hb_eq] at hsp'
              rcases hholes with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · have e1 := Option.some.inj ((pigeonHole_bit h1' (otherBit (bOf d r))).symm.trans hsp'.2.1)
                have e2 := Option.some.inj ((pigeonHole_bit h2' (otherBit (bOf d r))).symm.trans hsp'.2.2)
                have e3 : bits (twinOf d r).hole (otherBit (bOf d r)) = !bits (cOf d r).hole (otherBit (bOf d r)) :=
                  (flipBit_facts (cOf d r).hole (otherBit (bOf d r))).2.1
                rw [e3] at e2; rw [e1] at e2; cases bits (cOf d r).hole (otherBit (bOf d r)) <;> simp at e2
              · have e1 := Option.some.inj ((pigeonHole_bit h1' (otherBit (bOf d r))).symm.trans hsp'.2.1)
                have e2 := Option.some.inj ((pigeonHole_bit h2' (otherBit (bOf d r))).symm.trans hsp'.2.2)
                have e3 : bits (twinOf d r).hole (otherBit (bOf d r)) = !bits (cOf d r).hole (otherBit (bOf d r)) :=
                  (flipBit_facts (cOf d r).hole (otherBit (bOf d r))).2.1
                rw [e3] at e1; rw [e2] at e1; cases bits (cOf d r).hole (otherBit (bOf d r)) <;> simp at e1
          have hdj : Disjoint (pairHoles (cOf d j).left (cOf d j).right (bOf d j) (bits (cOf d j).hole (bOf d j))) {cOf d r, twinOf d r} := by
            rw [hph]; refine Finset.disjoint_left.mpr (fun x hx hxp => ?_)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hxp
            rcases hx with rfl | rfl <;> rcases hxp with e | e
            · exact hcj_ne_r e
            · exact hcj_ne_tw e
            · exact htw_ne_r e
            · exact htw_ne_tw e
          rw [leafWeight_eq_three_of_disjoint hsp' hdj]
      · rw [ite_eq_right h1]; exact leafWeight_le_six ρ_leaf _
  exact dValid_inTwin_ge_six (c_r := cOf d r) (c_twin := twinOf d r)
    (dMarks_distinctHoles d r) (dValid_at_root d hr) hw0 hm hfb3
    h13.2.2.2.1 rfl rfl (bOf d r) rfl hsp
    (fun j ρl hle h1 h2 hc => hcheck j ρl hle (Or.inl ⟨h1, h2⟩) hc)
    (fun j ρl hle h1 h2 hc => hcheck j ρl hle (Or.inr ⟨h1, h2⟩) hc)

theorem local_bound {r : Fin d.pi.length} (hr : r ∈ dRoots d) :
    8 * k d r + 2 + (S_set d r).card + inTwin d r ≤
    dPhi (wt d r) (d.dUnroll r) + (if isH2 d r then 6 else 0) +
      (if isH1_d3 d r then 5 else 0) + (if isH1_d2 d r then 4 else 0) + outTwin d r := by
  have hd : DistinctHoles (M d r) := dMarks_distinctHoles d r
  have hv := dValid_at_root d hr
  have hreq : req (k d r) (st d r) (M d r) ≤ dPhi (wt d r) (d.dUnroll r) := dValid_req_bound hd hv
  have hk4 := k_le_four d r
  have hS_phi : 8 * (S_set d r).card + 10 * w d r ≤ dPhi (wt d r) (d.dUnroll r) := by
    have hmul := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
      (fun j hj => by rw [S_set_wt_four d hj]) (d.dUnroll r)
    rw [S_set_count_eq] at hmul; unfold dPhi w; omega
  have hin_le1 : inTwin d r ≤ 1 := by unfold inTwin; split_ifs <;> omega
  have hin_zero : ¬ isH1_d3 d r → ¬ isH1_d2 d r → inTwin d r = 0 := by
    intro hn3 hn2; unfold inTwin; rw [ite_eq_right]; rintro ⟨p, hp⟩
    rcases hp.2.2.2.1 with h | h; exact hn3 h; exact hn2 h
  have hS_empty_k0 : k d r = 0 → (S_set d r).card = 0 := by
    intro hk0; apply Finset.card_eq_zero.mpr; ext j; simp only [S_set, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨_, _, _, _, htw⟩
    have hm : M_list d r = [] := List.eq_nil_of_length_eq_zero hk0
    simp [M, hm] at htw
  -- Helper: any j ∈ H1_d3 with twinOf j ∈ M(r) and k(r) = 2 at ρ2 (fixedBits = 2, SignedShared) DISAGREES with ρ2!
  have hdis_H2 : ∀ (c₁ c₂ : Collision) (ρ2 : State),
      M_list d r = [c₁, c₂] ∨ M_list d r = [c₂, c₁] →
      fixedBits ρ2 = 2 → SignedShared [c₁, c₂] ρ2 →
      ∀ j ∈ S_set d r, twinOf d j ∈ ({c₁, c₂} : Finset Collision) → Disagrees (st d j) ρ2 := by
    intro c₁ c₂ ρ2 hm h2 hss j hj htw_mem
    have hjp := (Finset.mem_filter.mp hj).2
    have hnd : ((M_list d r).map Collision.hole).Nodup := dMarks_nodup d r
    have hne : c₁.hole ≠ c₂.hole := by
      rcases hm with h | h <;> rw [h] at hnd <;> simp at hnd
      · exact hnd
      · exact Ne.symm hnd
    obtain ⟨hl_eq, hr_eq, b', hbe, hlb', hrb', _, _⟩ := (shared_pair_structure hss (by simp) (by simp) hne).2 h2
    have hcj_not : cOf d j ∉ ({c₁, c₂} : Finset Collision) := by
      intro hmem
      have hmr : cOf d j ∈ M d r := by
        rcases hm with h | h <;> simp [M, h] at hmem ⊢
        · exact hmem
        · exact hmem.symm
      have hex := dUnroll_exit_props d r j (by omega : 1 ≤ countExit j (d.dUnroll r))
      exact hex.1.ne' (dMarks_disjoint d hex.2.1 hr (List.mem_toFinset.mp (cOf_mem_M d hjp.1.2.2.1)) (List.mem_toFinset.mp hmr))
    -- twinOf j ∈ {c₁, c₂}, so (cOf j).left = c₁.left, (cOf j).right = c₁.right, and bits (twinOf j).hole b' = bits c₁.hole b'!
    have htw_eq : (twinOf d j).left = c₁.left ∧ (twinOf d j).right = c₁.right ∧
        bits (twinOf d j).hole b' = bits c₁.hole b' := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at htw_mem
      rcases htw_mem with e | e
      · rw [e]; exact ⟨rfl, rfl, rfl⟩
      · rw [e]; exact ⟨hl_eq.symm, hr_eq.symm, hbe.symm⟩
    -- Can bOf d j = b'? If so, cOf d j has same bit b' as twinOf d j, so cOf d j ∈ {c₁, c₂}, contradicting hcj_not!
    have hbj_ne : bOf d j ≠ b' := by
      intro eb
      have hcb : bits (cOf d j).hole b' = bits c₁.hole b' := by
        have h1 := (flipBit_facts (cOf d j).hole (otherBit (bOf d j))).2.2.1
        rw [(otherBit_facts (bOf d j)).2.1] at h1
        have h2 : bits (twinOf d j).hole b' = bits c₁.hole b' := htw_eq.2.2
        dsimp only [twinOf] at h2
        rw [eb] at h1 h2
        exact h1.symm.trans h2
      have h1_or_2 : (cOf d j).hole = c₁.hole ∨ (cOf d j).hole = c₂.hole := by
        have ho_ne : bits c₁.hole (otherBit b') ≠ bits c₂.hole (otherBit b') := fun eo =>
          hne (hole_eq_of_bits c₁.hole c₂.hole b' hbe eo)
        by_cases e1 : bits (cOf d j).hole (otherBit b') = bits c₁.hole (otherBit b')
        · exact Or.inl (hole_eq_of_bits _ _ b' hcb e1)
        · right; apply hole_eq_of_bits _ _ b' (hcb.trans hbe)
          cases a1 : bits (cOf d j).hole (otherBit b') <;> cases a2 : bits c₁.hole (otherBit b') <;>
            cases a3 : bits c₂.hole (otherBit b') <;> simp_all
      apply hcj_not; simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h1_or_2 with eh | eh
      · left; cases hcj' : cOf d j; cases hc1' : c₁; simp_all [twinOf]
      · right; cases hcj' : cOf d j; cases hc2' : c₂; simp_all [twinOf]
    -- So bOf d j = otherBit b', hence otherBit (bOf d j) = b', and bits (cOf d j).hole b' = !bits c₁.hole b'!
    have hbj_eq : bOf d j = otherBit b' := (otherBit_facts b').2.2 (bOf d j) |>.resolve_left hbj_ne
    have hcb_neg : bits (cOf d j).hole b' = !bits c₁.hole b' := by
      have := htw_eq.2.2; unfold twinOf at this
      rw [hbj_eq, (otherBit_facts b').2.1, (flipBit_facts (cOf d j).hole b').2.1] at this
      cases h1 : bits (cOf d j).hole b' <;> cases h2' : bits c₁.hole b' <;> simp_all
    -- Since j ∈ H1_d3, fixedBits (st d j) = 3, so at least one of (c₁.left, b') or (c₁.right, b') is fixed in st d j to bits (cOf j).hole b' = !bits c₁.hole b'!
    have hshj : SignedShared [cOf d j] (st d j) := M_list_eq_cOf d hjp.1.2.2.1 ▸ st_shared d j
    have hfbj := (sameBitPair_of_k1_fb3 hshj hjp.1.2.2.2.1 hjp.1.2.2.2.2).1
    by_cases hlj : st d j (c₁.left, b') ≠ none
    · cases hv' : st d j (c₁.left, b') with
      | none => exact (hlj hv').elim
      | some valj =>
        have hv_eq : valj = bits (cOf d j).hole b' := (signedShared_const (c := cOf d j) hshj (by simp) hv').2
        exact ⟨(c₁.left, b'), !bits c₁.hole b', by rw [hv', hv_eq, hcb_neg], by rw [Bool.not_not]; exact hlb'⟩
    · by_cases hrj : st d j (c₁.right, b') ≠ none
      · cases hv' : st d j (c₁.right, b') with
        | none => exact (hrj hv').elim
        | some valj =>
          have hv_eq : valj = bits (cOf d j).hole b' := (signedShared_const (c := cOf d j) hshj (by simp) hv').2
          exact ⟨(c₁.right, b'), !bits c₁.hole b', by rw [hv', hv_eq, hcb_neg], by rw [Bool.not_not]; exact hrb'⟩
      · exfalso; simp only [not_not] at hlj hrj
        have hsub2 : Finset.univ.filter (fun v : Variable => st d j v ≠ none) ⊆ {(c₁.left, otherBit b'), (c₁.right, otherBit b')} := by
          intro v hv'; cases hvv : st d j v with
          | none => exact ((Finset.mem_filter.mp hv').2 hvv).elim
          | some val =>
            have h1 := (signedShared_const (c := cOf d j) hshj (by simp) hvv).1
            have hl' : (cOf d j).left = c₁.left := htw_eq.1
            have hr' : (cOf d j).right = c₁.right := htw_eq.2.1
            rw [hl', hr'] at h1
            rcases v with ⟨pv, bv⟩; change pv = c₁.left ∨ pv = c₁.right at h1
            rcases (otherBit_facts b').2.2 bv with rfl | rfl
            · rcases h1 with rfl | rfl
              · rw [hlj] at hvv; cases hvv
              · rw [hrj] at hvv; cases hvv
            · rcases h1 with rfl | rfl <;> simp
        have hc2 := (Finset.card_le_card hsub2).trans Finset.card_le_two
        change fixedBits (st d j) ≤ 2 at hc2; omega
  -- Now split on k d r ∈ {0, 1, 2, 3, 4}!
  rcases (show k d r = 0 ∨ k d r = 1 ∨ k d r = 2 ∨ k d r = 3 ∨ k d r = 4 by omega) with hk0 | hk1 | hk2 | hk3 | hk4
  · -- k = 0
    have hS0 := hS_empty_k0 hk0
    have hn2 : ¬ isH2 d r := fun h => by have := h.2.2.1; omega
    have hn13 : ¬ isH1_d3 d r := fun h => by have := h.2.2.1; omega
    have hn12 : ¬ isH1_d2 d r := fun h => by have := h.2.2.1; omega
    rw [hk0, hS0, hin_zero hn13 hn12, ite_eq_right hn2, ite_eq_right hn13, ite_eq_right hn12]
    by_cases hw0 : w d r = 0
    · -- Pure derived node is `.res`, so both children have b0 ≥ 1 -> dPhi ≥ 2!
      have hD := (Finset.mem_filter.mp hr).2.1
      cases hru : d.rules r with
      | ax _ => simp [ShortestDag.children, hru, Rule.parents] at hD
      | weak _ _ _ => unfold w at hw0; rw [d.dUnroll_weak hru] at hw0; simp [dWeaks] at hw0
      | res j' k' _ _ hv_res =>
        have hv' := hv; rw [d.dUnroll_res hru] at hv'
        cases hv' with
        | res _ _ _ _ _ _ _ hl' hr' =>
          have bl := dValid_req_bound hd hl'; have br := dValid_req_bound hd hr'
          have hm0 : M_list d r = [] := List.eq_nil_of_length_eq_zero hk0
          rw [M_list, d.dUnroll_res hru, dMarks, List.append_eq_nil_iff] at hm0
          rw [hm0.2] at bl; rw [hm0.1] at br; simp only [List.length_nil, req] at bl br
          have := b0_ge_one (State.grant (st d r) (Classical.choose hv_res) true) (M d r)
          have := b0_ge_one (State.grant (st d r) (Classical.choose hv_res) false) (M d r)
          rw [d.dUnroll_res hru]; simp only [dPhi, exitWeightSum, dAxReps, dWeaks] at bl br ⊢; omega
    · omega
  · -- k = 1
    have hn2 : ¬ isH2 d r := fun h => by have := h.2.2.1; omega
    rw [hk1, ite_eq_right hn2]
    by_cases hw0 : w d r = 0
    · have hm := M_list_eq_cOf d hk1
      have hnc : ¬ hasCollision (st d r) := nonAx_not_hasCollision_of_pure d hr hw0 hm
      by_cases h13 : isH1_d3 d r
      · have hn12 : ¬ isH1_d2 d r := fun h => by have := h13.2.2.2.2; have := h.2.2.2.2.1; omega
        rw [ite_eq_left h13, ite_eq_right hn12]
        by_cases hS1 : 1 ≤ (S_set d r).card
        · omega
        · have hS0 : (S_set d r).card = 0 := by omega
          by_cases hin1 : inTwin d r = 1
          · have h6 := inTwin_h1_d3_phi_ge_six d hr h13 hw0 hin1; omega
          · have hin0 : inTwin d r = 0 := by omega
            have hsh : SignedShared [cOf d r] (st d r) := hm ▸ st_shared d r
            have hfb3 := (sameBitPair_of_k1_fb3 hsh h13.2.2.2.1 h13.2.2.2.2).1
            have hb4 := shared_single_b0_ge_four hsh (by simp) (cOf_mem_M d hk1) hnc
            have h4 : 4 ≤ dPhi (wt d r) (d.dUnroll r) := by
              rw [hk1] at hreq; simp only [req, ite_eq_right hnc, ite_eq_left h13.2.2.2.2] at hreq; omega
            by_cases h5 : 5 ≤ dPhi (wt d r) (d.dUnroll r)
            · omega
            · have hle4 : dPhi (wt d r) (d.dUnroll r) ≤ 4 := by omega
              obtain ⟨he1, ha0, q, hcq1, hwtq4⟩ := dValid_h1_d3_phi_four hd hv hw0 hm hfb3 hnc
                (fun j _ => wt_ge_three d r j) hle4
              have hq_props := dUnroll_exit_props d r q (by omega)
              -- wt d r q = 4 -> edgeCh d r q = 2 -> (isH1_d3 q ∨ isH1_d2 q) ∧ twinOf q ∈ M r!
              have hq_te : TwinEdge d r q := by
                have hch2 : edgeCh d r q = 2 := by have := edgeCh_add_wt d r q; omega
                unfold edgeCh at hch2
                by_cases hq2 : isH2 d q
                · rw [ite_eq_left hq2] at hch2; omega
                · rw [ite_eq_right hq2] at hch2
                  by_cases hq1 : isH1_d3 d q ∨ isH1_d2 d q
                  · rw [ite_eq_left hq1] at hch2
                    by_cases htw : twinOf d q ∈ M d r
                    · exact ⟨hr, hq_props.2.1, h13, hq1, htw, by omega, he1, hw0, ha0⟩
                    · rw [ite_eq_right htw] at hch2; omega
                  · rw [ite_eq_right hq1] at hch2; omega
              have hout1 : outTwin d r = 1 := by unfold outTwin; rw [ite_eq_left (⟨q, hq_te⟩ : ∃ q', TwinEdge d r q')]
              omega
      · rw [ite_eq_right h13]
        by_cases h12 : isH1_d2 d r
        · rw [ite_eq_left h12]
          by_cases hS2 : 2 ≤ (S_set d r).card
          · omega
          · have hsh : SignedShared [cOf d r] (st d r) := hm ▸ st_shared d r
            have hb4 := shared_single_b0_ge_four hsh (by simp) (cOf_mem_M d hk1) hnc
            rw [hk1] at hreq
            simp only [req, ite_eq_right hnc, ite_eq_right (show ¬ 3 ≤ fixedBits (st d r) by have := h12.2.2.2.2.1; omega)] at hreq
            omega
        · rw [ite_eq_right h12, hin_zero h13 h12]
          by_cases hS2 : 2 ≤ (S_set d r).card
          · omega
          · -- ¬ isH1_d3 ∧ ¬ isH1_d2 ∧ ¬ hasCollision -> fixedBits ≤ 2 and NO sameBitPair -> req = 10!
            have hfb2 : fixedBits (st d r) ≤ 2 := by
              by_contra h3
              have hne_r : r ≠ d.root := fun e => by
                rw [e, st, d.rootEmpty, clauseState_empty, fixedBits_empty] at h3; omega
              exact h13 ⟨hr, hne_r, hk1, hnc, by omega⟩
            have hno_sp : ∀ u v b val, ¬ sameBitPair (st d r) u v b val := by
              rintro u v b val hsp
              have hge2 : 2 ≤ fixedBits (st d r) := by
                have hsub : ({(u, b), (v, b)} : Finset Variable) ⊆ Finset.univ.filter (fun x => st d r x ≠ none) := by
                  intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  rcases hx with rfl | rfl <;> simp [hsp.2.1, hsp.2.2]
                have hc := Finset.card_le_card hsub; simp [show (u, b) ≠ (v, b) from fun e => hsp.1.ne (congrArg Prod.fst e)] at hc; exact hc
              have hne_r : r ≠ d.root := fun e => by
                rw [e, st, d.rootEmpty, clauseState_empty, fixedBits_empty] at hge2; omega
              exact h12 ⟨hr, hne_r, hk1, hnc, by omega, u, v, b, val, hsp⟩
            by_cases hS0 : (S_set d r).card = 0
            · have hsh : SignedShared [cOf d r] (st d r) := hm ▸ st_shared d r
              have hb6 : b0 (st d r) (M d r) = 6 := b0_eq_six_of_no_sameBitPair (ow := M d r) hnc (fixedPigeons_le_two_of_shared (c := cOf d r) hsh (by simp)) hno_sp
              rw [hk1] at hreq; simp only [req, ite_eq_right hnc, ite_eq_right (show ¬ 3 ≤ fixedBits (st d r) by omega), hb6] at hreq
              omega
            · have h11 := dValid_k1_other_S hd hv hw0 hk1 hfb2 hno_sp (S_set d r)
                (fun j hj => by rw [S_set_wt_four d hj])
                (fun j hj ρ' hle => S_set_lw_le_four d hr hj hle)
                (by rw [S_set_count_eq]; omega)
              omega
    · -- k = 1, w ≥ 1
      by_cases h13 : isH1_d3 d r
      · have hn12 : ¬ isH1_d2 d r := fun h => by have := h13.2.2.2.2; have := h.2.2.2.2.1; omega
        rw [ite_eq_left h13, ite_eq_right hn12]; omega
      · rw [ite_eq_right h13]
        by_cases h12 : isH1_d2 d r
        · rw [ite_eq_left h12]; omega
        · rw [ite_eq_right h12, hin_zero h13 h12]; omega
  · -- k = 2
    have hn13 : ¬ isH1_d3 d r := fun h => by have := h.2.2.1; omega
    have hn12 : ¬ isH1_d2 d r := fun h => by have := h.2.2.1; omega
    rw [hk2, ite_eq_right hn13, ite_eq_right hn12, hin_zero hn13 hn12]
    rcases hm : M_list d r with _ | ⟨c₁, _ | ⟨c₂, rest⟩⟩ <;> simp [k, hm] at hk2
    subst hk2
    have hnd : ((M_list d r).map Collision.hole).Nodup := dMarks_nodup d r; rw [hm] at hnd
    have hne : c₁.hole ≠ c₂.hole := by simp at hnd; exact hnd
    have hsh : SignedShared [c₁, c₂] (st d r) := hm ▸ st_shared d r
    have hstruc := shared_pair_structure hsh (by simp) (by simp) hne
    by_cases h2 : isH2 d r
    · rw [ite_eq_left h2]
      by_cases hw0 : w d r = 0
      · have hfb2 : fixedBits (st d r) = 2 := by
          obtain ⟨_, _, _, u, v, b, val, huv, hu, hv'⟩ := h2
          have hsub : ({(u, b), (v, b)} : Finset Variable) ⊆ Finset.univ.filter (fun x => st d r x ≠ none) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rcases hx with rfl | rfl <;> simp [hu, hv']
          have hc := Finset.card_le_card hsub; simp [show (u, b) ≠ (v, b) from fun e => huv.ne (congrArg Prod.fst e)] at hc
          change 2 ≤ fixedBits (st d r) at hc; have := hstruc.1; omega
        have hex := dValid_disagree_extra hd hv hw0 (S_set d r)
          (fun j hj => by rw [S_set_wt_four d hj])
          (fun j hj => hdis_H2 c₁ c₂ (st d r) (Or.inl hm) hfb2 hsh j hj (by
            have := (Finset.mem_filter.mp hj).2.2.2.2; simpa [M, hm] using this))
        rw [show (dMarks (keyAt d) (d.dUnroll r)).length = 2 by simp [M_list] at hm; simp [hm],
            S_set_count_eq] at hex
        simp only [req, show 2 ≤ fixedBits (st d r) by omega, ite_true] at hex
        omega
      · -- k = 2, H2, w ≥ 1: dPhi ≥ 16 (by dValid_k2_weak_ge_16) and ≥ 10 + 8*|S_r| -> +6 covers all |S_r|!
        have h16 := dValid_k2_weak_ge_16 hd hv (by simp [M_list] at hm; simp [hm]) (by change 1 ≤ w d r; omega)
        omega
    · rw [ite_eq_right h2]
      have hfb1 : fixedBits (st d r) ≤ 1 := by
        by_contra hge2
        have hfb2 : fixedBits (st d r) = 2 := by have := hstruc.1; omega
        obtain ⟨_, _, b', _, hlb', hrb', _, _⟩ := hstruc.2 hfb2
        have hne_r : r ≠ d.root := fun e => by
          rw [e, st, d.rootEmpty, clauseState_empty, fixedBits_empty] at hfb2; omega
        exact h2 ⟨hr, hne_r, by simp [k, hm], c₁.left, c₁.right, b', bits c₁.hole b', c₁.ordered, hlb', hrb'⟩
      by_cases hw0 : w d r = 0
      · by_cases hS3 : 3 ≤ (S_set d r).card
        · omega
        · by_cases h0 : fixedBits (st d r) = 0
          · rw [show k d r = 2 by simp [k, hm]] at hreq
            simp [req, h0] at hreq; omega
          · have heq1 : fixedBits (st d r) = 1 := by omega
            by_cases hS0 : (S_set d r).card = 0
            · rw [show k d r = 2 by simp [k, hm]] at hreq
              simp [req, heq1] at hreq; omega
            · by_cases hdiff : c₁.left ≠ c₂.left ∨ c₁.right ≠ c₂.right
              · have h20 := dValid_d1_diff_pairs hd hv hw0 heq1 (Or.inl hm) hdiff; omega
              · have h20 := (dValid_d1_same_pair_S hd hv hw0 (by simp [M_list] at hm; simp [hm]) heq1
                  (S_set d r) (S_set d r) (Finset.Subset.refl _)
                  (fun j hj => by rw [S_set_wt_four d hj])
                  (fun j hj ρ' hle => S_set_lw_le_four d hr hj hle)
                  (fun ρ2 h2' hss' j hj => hdis_H2 c₁ c₂ ρ2 (Or.inl hm) h2' (by simpa [M_list, hm] using hss') j hj (by
                    have := (Finset.mem_filter.mp hj).2.2.2.2; simpa [M, hm] using this))).2
                  (by rw [S_set_count_eq]; omega)
                omega
      · -- k = 2, ¬H2 (so fixedBits ≤ 1), w ≥ 1: dPhi ≥ 20 and ≥ 10 + 8*|S_r|!
        have h20 := dValid_k2_d1_weak_ge_20 hd hv (by simp [M_list] at hm; simp [hm]) hfb1 (by change 1 ≤ w d r; omega)
        omega
  · -- k = 3
    have hn2 : ¬ isH2 d r := fun h => by have := h.2.2.1; omega
    have hn13 : ¬ isH1_d3 d r := fun h => by have := h.2.2.1; omega
    have hn12 : ¬ isH1_d2 d r := fun h => by have := h.2.2.1; omega
    rw [hk3, ite_eq_right hn2, ite_eq_right hn13, ite_eq_right hn12, hin_zero hn13 hn12]
    rw [hk3] at hreq; simp only [req] at hreq
    by_cases hS2 : (S_set d r).card ≤ 2
    · omega
    · by_cases hS4 : 4 ≤ (S_set d r).card
      · omega
      · have hS3 : (S_set d r).card = 3 := by omega
        by_cases hw0 : w d r = 0
        · -- Pure k = 3, |S_r| = 3 (6 leaves in S_r): need dPhi ≥ 29!
          have aux3 : ∀ (t : DTree Variable (Fin d.pi.length)) (ρ : State),
              DValid (st d) (keyAt d) (M d r) (wt d r) ρ t →
              dWeaks t = 0 → (dMarks (keyAt d) t).length = 3 →
              6 ≤ countExitsIn (S_set d r) t → 29 ≤ dPhi (wt d r) t := by
            intro t ρ hv'; induction hv' with
            | axUniq => intro _ h3 _; simp [dMarks] at h3
            | axRep => intro _ h3 _; simp [dMarks] at h3
            | exitDer => intro _ h3 _; simp [dMarks] at h3
            | weak => intro hp _ _; simp [dWeaks] at hp
            | res i f ρ l' r' nd hs hl' hr' ihl ihr =>
              intro hp h3 hm6
              have hem := signedShared_three nd (by simp only [dMarks] at h3; omega) hs
              subst ρ
              simp only [dWeaks, dMarks, List.length_append, countExitsIn, dPhi, exitWeightSum, dAxReps] at hp h3 hm6 ihl ihr ⊢
              have bl := dValid_req_bound hd hl'; have br := dValid_req_bound hd hr'; simp only [dPhi] at bl br
              have blS := mul_countExitsIn_le_dPhi (S := S_set d r) (wt := wt d r) (c := 4) (fun j hj => by rw [S_set_wt_four d hj]) l'
              have brS := mul_countExitsIn_le_dPhi (S := S_set d r) (wt := wt d r) (c := 4) (fun j hj => by rw [S_set_wt_four d hj]) r'
              simp only [dPhi] at blS brS
              by_cases hsing : ∃ v : Variable, f = {v}
              · obtain ⟨v, rfl⟩ := hsing
                have hfb0 : fixedBits (State.grant State.empty {v} false) = 1 := by rw [fixedBits_grant_none rfl false, fixedBits_empty]
                have hfb1 : fixedBits (State.grant State.empty {v} true) = 1 := by rw [fixedBits_grant_none rfl true, fixedBits_empty]
                have hne0 : State.grant State.empty {v} false ≠ State.empty := fun e => by
                  have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
                have hne1 : State.grant State.empty {v} true ≠ State.empty := fun e => by
                  have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
                have hle20 : (dMarks (keyAt d) r').length ≤ 2 := by
                  by_contra h; exact hne0 (signedShared_three (dValid_nodup hr') (by omega) (dValid_shared hr'))
                have hle21 : (dMarks (keyAt d) l').length ≤ 2 := by
                  by_contra h; exact hne1 (signedShared_three (dValid_nodup hl') (by omega) (dValid_shared hl'))
                have hr10 := req_one_of_fixedBits_le_one (ow := M d r) (by omega : fixedBits (State.grant State.empty {v} false) ≤ 1)
                have hl10 := req_one_of_fixedBits_le_one (ow := M d r) (by omega : fixedBits (State.grant State.empty {v} true) ≤ 1)
                rcases (show ((dMarks (keyAt d) r').length = 2 ∧ (dMarks (keyAt d) l').length = 1) ∨
                    ((dMarks (keyAt d) r').length = 1 ∧ (dMarks (keyAt d) l').length = 2) by omega) with ⟨er, el⟩ | ⟨er, el⟩
                · rw [er] at br; rw [el, hl10] at bl; simp [req, hfb0] at br
                  by_cases hm_l3 : 3 ≤ countExitsIn (S_set d r) l'
                  · omega
                  · by_cases hm_r5 : 5 ≤ countExitsIn (S_set d r) r'
                    · omega
                    · have hm_r4 : countExitsIn (S_set d r) r' = 4 := by omega
                      by_cases hall : ∀ j, countExit j r' ≥ 1 → j ∈ S_set d r
                      · have h19 := dValid_k2_d1_all4_ge_19 hd hr' (by omega) er hfb0
                          (fun j hj => ⟨by rw [S_set_wt_four d (hall j hj)], fun ρ' hle => S_set_lw_le_four d hr (hall j hj) hle⟩)
                        simp only [dPhi] at h19; omega
                      · push Not at hall; obtain ⟨j0, hcj0, hnj0⟩ := hall
                        have hsum_ex : 4 * countExitsIn (S_set d r) r' + 3 ≤ exitWeightSum (wt d r) r' := by
                          have aux_ex : ∀ (t0 : DTree Variable (Fin d.pi.length)),
                              (∀ j, 1 ≤ countExit j t0 → 3 ≤ wt d r j) →
                              1 ≤ countExit j0 t0 → j0 ∉ S_set d r →
                              4 * countExitsIn (S_set d r) t0 + 3 ≤ exitWeightSum (wt d r) t0 := by
                            intro t0; induction t0 with
                            | axUniq _ | axRep _ => intro _ h1 _; simp [countExit] at h1
                            | exitDer q =>
                              intro hw3 h1 hnj
                              have hq : q = j0 := by simp only [countExit] at h1; by_contra hne; rw [ite_eq_right hne] at h1; omega
                              subst hq; simp [countExitsIn, exitWeightSum, hnj]; exact hw3 q (by simp [countExit])
                            | weak _ t0 ih => exact ih
                            | res _ _ la ra ihla ihra =>
                              intro hw3 h1 hnj
                              simp only [countExit, countExitsIn, exitWeightSum] at h1 ⊢
                              have hmla := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                                (fun j hj => by rw [S_set_wt_four d hj]) la
                              have hmra := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                                (fun j hj => by rw [S_set_wt_four d hj]) ra
                              by_cases h1l : 1 ≤ countExit j0 la
                              · have := ihla (fun j hj => hw3 j (by simp [countExit]; omega)) h1l hnj; omega
                              · have := ihra (fun j hj => hw3 j (by simp [countExit]; omega)) (by omega) hnj; omega
                          exact aux_ex r' (fun j _ => wt_ge_three d r j) hcj0 hnj0
                        omega
                · rw [el] at bl; rw [er, hr10] at br; simp [req, hfb1] at bl
                  by_cases hm_r3 : 3 ≤ countExitsIn (S_set d r) r'
                  · omega
                  · by_cases hm_l5 : 5 ≤ countExitsIn (S_set d r) l'
                    · omega
                    · have hm_l4 : countExitsIn (S_set d r) l' = 4 := by omega
                      by_cases hall : ∀ j, countExit j l' ≥ 1 → j ∈ S_set d r
                      · have h19 := dValid_k2_d1_all4_ge_19 hd hl' (by omega) el hfb1
                          (fun j hj => ⟨by rw [S_set_wt_four d (hall j hj)], fun ρ' hle => S_set_lw_le_four d hr (hall j hj) hle⟩)
                        simp only [dPhi] at h19; omega
                      · push Not at hall; obtain ⟨j0, hcj0, hnj0⟩ := hall
                        have hsum_ex : 4 * countExitsIn (S_set d r) l' + 3 ≤ exitWeightSum (wt d r) l' := by
                          have aux_ex : ∀ (t0 : DTree Variable (Fin d.pi.length)),
                              (∀ j, 1 ≤ countExit j t0 → 3 ≤ wt d r j) →
                              1 ≤ countExit j0 t0 → j0 ∉ S_set d r →
                              4 * countExitsIn (S_set d r) t0 + 3 ≤ exitWeightSum (wt d r) t0 := by
                            intro t0; induction t0 with
                            | axUniq _ | axRep _ => intro _ h1 _; simp [countExit] at h1
                            | exitDer q =>
                              intro hw3 h1 hnj
                              have hq : q = j0 := by simp only [countExit] at h1; by_contra hne; rw [ite_eq_right hne] at h1; omega
                              subst hq; simp [countExitsIn, exitWeightSum, hnj]; exact hw3 q (by simp [countExit])
                            | weak _ t0 ih => exact ih
                            | res _ _ la ra ihla ihra =>
                              intro hw3 h1 hnj
                              simp only [countExit, countExitsIn, exitWeightSum] at h1 ⊢
                              have hmla := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                                (fun j hj => by rw [S_set_wt_four d hj]) la
                              have hmra := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                                (fun j hj => by rw [S_set_wt_four d hj]) ra
                              by_cases h1l : 1 ≤ countExit j0 la
                              · have := ihla (fun j hj => hw3 j (by simp [countExit]; omega)) h1l hnj; omega
                              · have := ihra (fun j hj => hw3 j (by simp [countExit]; omega)) (by omega) hnj; omega
                          exact aux_ex l' (fun j _ => wt_ge_three d r j) hcj0 hnj0
                        omega
              · have hns : ∀ v : Variable, f ≠ {v} := fun v hv' => hsing ⟨v, hv'⟩
                rw [grant_nonsingle hns true] at bl; rw [grant_nonsingle hns false] at br
                have h10 := req_one_of_fixedBits_le_one (ow := M d r) (by rw [fixedBits_empty]; omega)
                rcases (show ((dMarks (keyAt d) r').length = 3 ∧ (dMarks (keyAt d) l').length = 0) ∨
                    ((dMarks (keyAt d) r').length = 2 ∧ (dMarks (keyAt d) l').length = 1) ∨
                    ((dMarks (keyAt d) r').length = 1 ∧ (dMarks (keyAt d) l').length = 2) ∨
                    ((dMarks (keyAt d) r').length = 0 ∧ (dMarks (keyAt d) l').length = 3) by omega) with
                    ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
                · rw [er] at br; simp only [req] at br
                  by_cases hml1 : 1 ≤ countExitsIn (S_set d r) l'
                  · omega
                  · have := ihr (by omega) er (by omega); omega
                · rw [er] at br; rw [el, h10] at bl; simp [req, fixedBits_empty] at br; omega
                · rw [el] at bl; rw [er, h10] at br; simp [req, fixedBits_empty] at bl; omega
                · rw [el] at bl; simp only [req] at bl
                  by_cases hmr1 : 1 ≤ countExitsIn (S_set d r) r'
                  · omega
                  · have := ihl (by omega) el (by omega); omega
          have h29 := aux3 (d.dUnroll r) (st d r) hv hw0 hk3 (by rw [S_set_count_eq]; omega)
          omega
        · omega
  · -- k = 4
    have hn2 : ¬ isH2 d r := fun h => by have := h.2.2.1; omega
    have hn13 : ¬ isH1_d3 d r := fun h => by have := h.2.2.1; omega
    have hn12 : ¬ isH1_d2 d r := fun h => by have := h.2.2.1; omega
    rw [hk4, ite_eq_right hn2, ite_eq_right hn13, ite_eq_right hn12, hin_zero hn13 hn12]
    rw [hk4] at hreq; simp only [req] at hreq
    by_cases hS2 : (S_set d r).card ≤ 2
    · omega
    · by_cases hS5 : 5 ≤ (S_set d r).card
      · omega
      · by_cases hw0 : w d r = 0
        · -- Pure k = 4, |S_r| ∈ {3, 4}: prove 34 + |S_r| ≤ dPhi!
          have aux4_side : ∀ (t0 : DTree Variable (Fin d.pi.length)) (ρ0 : State),
              DValid (st d) (keyAt d) (M d r) (wt d r) ρ0 t0 →
              dWeaks t0 = 0 → (dMarks (keyAt d) t0).length = 2 → fixedBits ρ0 = 1 →
              4 ≤ countExitsIn (S_set d r) t0 → 19 ≤ dPhi (wt d r) t0 := by
            intro t0 ρ0 hv0 hp0 hk20 hfb0 hm4
            by_cases hm5 : 5 ≤ countExitsIn (S_set d r) t0
            · have := mul_countExitsIn_le_dPhi (S := S_set d r) (wt := wt d r) (c := 4)
                (fun j hj => by rw [S_set_wt_four d hj]) t0; omega
            · by_cases hall : ∀ j, countExit j t0 ≥ 1 → j ∈ S_set d r
              · exact dValid_k2_d1_all4_ge_19 hd hv0 hp0 hk20 hfb0
                  (fun j hj => ⟨by rw [S_set_wt_four d (hall j hj)], fun ρ' hle => S_set_lw_le_four d hr (hall j hj) hle⟩)
              · push Not at hall; obtain ⟨j0, hcj0, hnj0⟩ := hall
                have aux_ex : ∀ (tx : DTree Variable (Fin d.pi.length)),
                    (∀ j, 1 ≤ countExit j tx → 3 ≤ wt d r j) →
                    1 ≤ countExit j0 tx → j0 ∉ S_set d r →
                    4 * countExitsIn (S_set d r) tx + 3 ≤ exitWeightSum (wt d r) tx := by
                  intro tx; induction tx with
                  | axUniq _ | axRep _ => intro _ h1 _; simp [countExit] at h1
                  | exitDer q =>
                    intro hw3 h1 hnj
                    have hq : q = j0 := by simp only [countExit] at h1; by_contra hne; rw [ite_eq_right hne] at h1; omega
                    subst hq; simp [countExitsIn, exitWeightSum, hnj]; exact hw3 q (by simp [countExit])
                  | weak _ tx ih => exact ih
                  | res _ _ la ra ihla ihra =>
                    intro hw3 h1 hnj
                    simp only [countExit, countExitsIn, exitWeightSum] at h1 ⊢
                    have hmla := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                      (fun j hj => by rw [S_set_wt_four d hj]) la
                    have hmra := mul_countExitsIn_le_exitWeightSum (S := S_set d r) (wt := wt d r) (c := 4)
                      (fun j hj => by rw [S_set_wt_four d hj]) ra
                    by_cases h1l : 1 ≤ countExit j0 la
                    · have := ihla (fun j hj => hw3 j (by simp [countExit]; omega)) h1l hnj; omega
                    · have := ihra (fun j hj => hw3 j (by simp [countExit]; omega)) (by omega) hnj; omega
                have h19 := aux_ex t0 (fun j _ => wt_ge_three d r j) hcj0 hnj0
                unfold dPhi; omega
          have aux4 : ∀ (t : DTree Variable (Fin d.pi.length)) (ρ : State),
              DValid (st d) (keyAt d) (M d r) (wt d r) ρ t →
              dWeaks t = 0 → (dMarks (keyAt d) t).length = 4 →
              (∀ j ∈ S_set d r, twinOf d j ∈ (dMarks (keyAt d) t).toFinset) →
              (∀ j ∈ S_set d r, countExit j t ≤ 2) →
              (countExitsIn (S_set d r) t = 2 * (S_set d r).card) →
              34 + (S_set d r).card ≤ dPhi (wt d r) t := by
            intro t ρ hv'; induction hv' with
            | axUniq => intro _ h4 _ _ _; simp [dMarks] at h4
            | axRep => intro _ h4 _ _ _; simp [dMarks] at h4
            | exitDer => intro _ h4 _ _ _; simp [dMarks] at h4
            | weak => intro hp _ _ _ _; simp [dWeaks] at hp
            | res i f ρ l' r' nd hs hl' hr' ihl ihr =>
              intro hp h4 htw_sub hcnt_le2 hm_eq
              have hem := signedShared_three nd (by simp only [dMarks] at h4; omega) hs
              subst ρ
              simp only [dWeaks, dMarks, List.length_append, countExitsIn, dPhi, exitWeightSum, dAxReps] at hp h4 hm_eq ihl ihr ⊢
              have bl := dValid_req_bound hd hl'; have br := dValid_req_bound hd hr'; simp only [dPhi] at bl br
              have blS := mul_countExitsIn_le_dPhi (S := S_set d r) (wt := wt d r) (c := 4) (fun j hj => by rw [S_set_wt_four d hj]) l'
              have brS := mul_countExitsIn_le_dPhi (S := S_set d r) (wt := wt d r) (c := 4) (fun j hj => by rw [S_set_wt_four d hj]) r'
              simp only [dPhi] at blS brS
              by_cases hsing : ∃ v : Variable, f = {v}
              · obtain ⟨v, rfl⟩ := hsing
                have hfb0 : fixedBits (State.grant State.empty {v} false) = 1 := by rw [fixedBits_grant_none rfl false, fixedBits_empty]
                have hfb1 : fixedBits (State.grant State.empty {v} true) = 1 := by rw [fixedBits_grant_none rfl true, fixedBits_empty]
                have hne0 : State.grant State.empty {v} false ≠ State.empty := fun e => by
                  have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
                have hne1 : State.grant State.empty {v} true ≠ State.empty := fun e => by
                  have := congrArg (fun g => g v) e; simp [grant_apply_self, State.empty] at this
                have hle20 : (dMarks (keyAt d) r').length ≤ 2 := by
                  by_contra h; exact hne0 (signedShared_three (dValid_nodup hr') (by omega) (dValid_shared hr'))
                have hle21 : (dMarks (keyAt d) l').length ≤ 2 := by
                  by_contra h; exact hne1 (signedShared_three (dValid_nodup hl') (by omega) (dValid_shared hl'))
                have er : (dMarks (keyAt d) r').length = 2 := by omega
                have el : (dMarks (keyAt d) l').length = 2 := by omega
                rw [er] at br; rw [el] at bl; simp [req, hfb0] at br; simp [req, hfb1] at bl
                rcases (show (S_set d r).card = 3 ∨ (S_set d r).card = 4 by omega) with hS3 | hS4
                · -- |S_r| = 3 (6 leaves): if either side has ≥ 4 -> aux4_side gives 19+18=37!
                  -- If 3 and 3: pigeonhole on the 3 twins into M(r') ∪ M(l') -> one side owns ≥ 2 twins!
                  -- Since each j ∈ S_r has countExit j ≤ 2, that side MUST have ≥ 1 leaf to its own twins -> dValid_d1_same_pair_S gives 19+18=37!
                  by_cases hr4 : 4 ≤ countExitsIn (S_set d r) r'
                  · have h19 := aux4_side r' _ hr' (by omega) er hfb0 hr4; simp only [dPhi] at h19; omega
                  · by_cases hl4 : 4 ≤ countExitsIn (S_set d r) l'
                    · have h19 := aux4_side l' _ hl' (by omega) el hfb1 hl4; simp only [dPhi] at h19; omega
                    · have hr3 : countExitsIn (S_set d r) r' = 3 := by omega
                      have hl3 : countExitsIn (S_set d r) l' = 3 := by omega
                      let Sr := (S_set d r).filter (fun j => twinOf d j ∈ (dMarks (keyAt d) r').toFinset)
                      let Sl := (S_set d r).filter (fun j => twinOf d j ∈ (dMarks (keyAt d) l').toFinset)
                      have hcov : S_set d r ⊆ Sr ∪ Sl := by
                        intro j hj; simp only [Sr, Sl, Finset.mem_union, Finset.mem_filter]
                        have hm' := htw_sub j hj; simp only [dMarks, List.toFinset_append, Finset.mem_union] at hm'
                        rcases hm' with h | h; exact Or.inl ⟨hj, h⟩; exact Or.inr ⟨hj, h⟩
                      have hsum_card : 3 ≤ Sr.card + Sl.card := by
                        have := (Finset.card_le_card hcov).trans (Finset.card_union_le Sr Sl); omega
                      -- Helper for a side owning ≥ 2 twins from S_r and receiving 3 exits from S_r -> dPhi ≥ 19!
                      have hside19 : ∀ (tx : DTree Variable (Fin d.pi.length)) (ρx : State) (Sx : Finset (Fin d.pi.length)),
                          DValid (st d) (keyAt d) (M d r) (wt d r) ρx tx →
                          dWeaks tx = 0 → (dMarks (keyAt d) tx).length = 2 → fixedBits ρx = 1 →
                          Sx = (S_set d r).filter (fun j => twinOf d j ∈ (dMarks (keyAt d) tx).toFinset) →
                          (∀ j ∈ S_set d r, countExit j tx ≤ 2) →
                          2 ≤ Sx.card → countExitsIn (S_set d r) tx = 3 → 19 ≤ dPhi (wt d r) tx := by
                        intro tx ρx Sx hvx hpx hk2x hfbx hSx_def hcnt_x hSx2 hcnt3
                        have hown1 : 1 ≤ countExitsIn Sx tx := by
                          have hsub_x : Sx ⊆ S_set d r := by rw [hSx_def]; exact Finset.filter_subset _ _
                          have hdiff_card : (S_set d r \ Sx).card ≤ 1 := by
                            have hcu : (Sx ∪ (S_set d r \ Sx)).card = Sx.card + (S_set d r \ Sx).card :=
                              Finset.card_union_of_disjoint Finset.disjoint_sdiff
                            rw [Finset.union_sdiff_of_subset hsub_x] at hcu
                            omega
                          have hsplit_ex : countExitsIn (S_set d r) tx = countExitsIn Sx tx + countExitsIn (S_set d r \ Sx) tx := by
                            rw [countExitsIn_sum, countExitsIn_sum, countExitsIn_sum]
                            rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub_x]
                          have hdiff_le2 : countExitsIn (S_set d r \ Sx) tx ≤ 2 := by
                            rw [countExitsIn_sum]
                            have hle : (∑ j ∈ S_set d r \ Sx, countExit j tx) ≤ ∑ _ ∈ S_set d r \ Sx, 2 :=
                              Finset.sum_le_sum (fun j hj => hcnt_x j (Finset.mem_sdiff.mp hj).1)
                            rw [Finset.sum_const, smul_eq_mul] at hle; omega
                          omega
                        exact (dValid_d1_same_pair_S hd hvx hpx hk2x hfbx (S_set d r) Sx
                          (by rw [hSx_def]; exact Finset.filter_subset _ _)
                          (fun j hj => by rw [S_set_wt_four d hj])
                          (fun j hj ρ' hle => S_set_lw_le_four d hr hj hle)
                          (fun ρ2 h2' hss' j hj => by
                            rcases htxm : dMarks (keyAt d) tx with _ | ⟨a1, _ | ⟨a2, rt⟩⟩ <;> simp [htxm] at hk2x
                            subst hk2x
                            have hjp_s : j ∈ S_set d r := by rw [hSx_def] at hj; exact (Finset.mem_filter.mp hj).1
                            have htw_m : twinOf d j ∈ ({a1, a2} : Finset Collision) := by
                              rw [hSx_def] at hj; have := (Finset.mem_filter.mp hj).2; simpa [htxm] using this
                            -- Note: hdis_H2 only needed a1, a2 ∈ M_list d r (with distinct holes) and j ∈ S_set d r!
                            -- Let's invoke a clean local proof of Disagrees (st d j) ρ2!
                            have hnd_x := dValid_nodup hvx; rw [htxm] at hnd_x
                            have hne_a : a1.hole ≠ a2.hole := by simp at hnd_x; exact hnd_x
                            have hss_a : SignedShared [a1, a2] ρ2 := htxm ▸ hss'
                            obtain ⟨hl_eq, hr_eq, b', hbe, hlb', hrb', _, _⟩ := (shared_pair_structure hss_a (by simp) (by simp) hne_a).2 h2'
                            have hjp := (Finset.mem_filter.mp hjp_s).2
                            have hcj_not : cOf d j ∉ ({a1, a2} : Finset Collision) := by
                              intro hmem
                              have hmr : cOf d j ∈ M d r := by
                                simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                                rcases hmem with e | e
                                · exact dValid_marks_subset hvx _ (by rw [htxm, e]; simp)
                                · exact dValid_marks_subset hvx _ (by rw [htxm, e]; simp)
                              have hex := dUnroll_exit_props d r j (by omega : 1 ≤ countExit j (d.dUnroll r))
                              exact hex.1.ne' (dMarks_disjoint d hex.2.1 hr (List.mem_toFinset.mp (cOf_mem_M d hjp.1.2.2.1)) (List.mem_toFinset.mp hmr))
                            have htw_eq : (twinOf d j).left = a1.left ∧ (twinOf d j).right = a1.right ∧
                                bits (twinOf d j).hole b' = bits a1.hole b' := by
                              simp only [Finset.mem_insert, Finset.mem_singleton] at htw_m
                              rcases htw_m with e | e
                              · rw [e]; exact ⟨rfl, rfl, rfl⟩
                              · rw [e]; exact ⟨hl_eq.symm, hr_eq.symm, hbe.symm⟩
                            have hbj_ne : bOf d j ≠ b' := by
                              intro eb
                              have hcb : bits (cOf d j).hole b' = bits a1.hole b' := by
                                have h1 := (flipBit_facts (cOf d j).hole (otherBit (bOf d j))).2.2.1
                                rw [(otherBit_facts (bOf d j)).2.1] at h1
                                have h2 : bits (twinOf d j).hole b' = bits a1.hole b' := htw_eq.2.2
                                dsimp only [twinOf] at h2
                                rw [eb] at h1 h2
                                exact h1.symm.trans h2
                              have h12 : (cOf d j).hole = a1.hole ∨ (cOf d j).hole = a2.hole := by
                                have ho_ne : bits a1.hole (otherBit b') ≠ bits a2.hole (otherBit b') := fun eo =>
                                  hne_a (hole_eq_of_bits a1.hole a2.hole b' hbe eo)
                                by_cases e1 : bits (cOf d j).hole (otherBit b') = bits a1.hole (otherBit b')
                                · exact Or.inl (hole_eq_of_bits _ _ b' hcb e1)
                                · right; apply hole_eq_of_bits _ _ b' (hcb.trans hbe)
                                  cases x1 : bits (cOf d j).hole (otherBit b') <;> cases x2 : bits a1.hole (otherBit b') <;>
                                    cases x3 : bits a2.hole (otherBit b') <;> simp_all
                              apply hcj_not; simp only [Finset.mem_insert, Finset.mem_singleton]
                              rcases h12 with eh | eh
                              · left; cases hcj' : cOf d j; cases ha1' : a1; simp_all [twinOf]
                              · right; cases hcj' : cOf d j; cases ha2' : a2; simp_all [twinOf]
                            have hbj_eq : bOf d j = otherBit b' := (otherBit_facts b').2.2 (bOf d j) |>.resolve_left hbj_ne
                            have hcb_neg : bits (cOf d j).hole b' = !bits a1.hole b' := by
                              have := htw_eq.2.2; unfold twinOf at this
                              rw [hbj_eq, (otherBit_facts b').2.1, (flipBit_facts (cOf d j).hole b').2.1] at this
                              cases x1 : bits (cOf d j).hole b' <;> cases x2 : bits a1.hole b' <;> simp_all
                            have hshj : SignedShared [cOf d j] (st d j) := M_list_eq_cOf d hjp.1.2.2.1 ▸ st_shared d j
                            have hfbj := (sameBitPair_of_k1_fb3 hshj hjp.1.2.2.2.1 hjp.1.2.2.2.2).1
                            by_cases hlj : st d j (a1.left, b') ≠ none
                            · cases hv'' : st d j (a1.left, b') with
                              | none => exact (hlj hv'').elim
                              | some valj =>
                                have hv_eq : valj = bits (cOf d j).hole b' := (signedShared_const (c := cOf d j) hshj (by simp) hv'').2
                                exact ⟨(a1.left, b'), !bits a1.hole b', by rw [hv'', hv_eq, hcb_neg], by rw [Bool.not_not]; exact hlb'⟩
                            · by_cases hrj : st d j (a1.right, b') ≠ none
                              · cases hv'' : st d j (a1.right, b') with
                                | none => exact (hrj hv'').elim
                                | some valj =>
                                  have hv_eq : valj = bits (cOf d j).hole b' := (signedShared_const (c := cOf d j) hshj (by simp) hv'').2
                                  exact ⟨(a1.right, b'), !bits a1.hole b', by rw [hv'', hv_eq, hcb_neg], by rw [Bool.not_not]; exact hrb'⟩
                              · exfalso; simp only [not_not] at hlj hrj
                                have hsub2 : Finset.univ.filter (fun w' : Variable => st d j w' ≠ none) ⊆ {(a1.left, otherBit b'), (a1.right, otherBit b')} := by
                                  intro w' hw''; cases hww : st d j w' with
                                  | none => exact ((Finset.mem_filter.mp hw'').2 hww).elim
                                  | some val =>
                                    have h1 := (signedShared_const (c := cOf d j) hshj (by simp) hww).1
                                    have hl' : (cOf d j).left = a1.left := htw_eq.1
                                    have hr' : (cOf d j).right = a1.right := htw_eq.2.1
                                    rw [hl', hr'] at h1
                                    rcases w' with ⟨pw, bw⟩; change pw = a1.left ∨ pw = a1.right at h1
                                    rcases (otherBit_facts b').2.2 bw with rfl | rfl
                                    · rcases h1 with rfl | rfl
                                      · rw [hlj] at hww; cases hww
                                      · rw [hrj] at hww; cases hww
                                    · rcases h1 with rfl | rfl <;> simp
                                have hc2 := (Finset.card_le_card hsub2).trans Finset.card_le_two
                                change fixedBits (st d j) ≤ 2 at hc2; omega)).1 hown1
                      by_cases hSr2 : 2 ≤ Sr.card
                      · have h19 := hside19 r' _ Sr hr' (by omega) er hfb0 rfl
                          (fun j hj => by have := hcnt_le2 j hj; simp only [countExit] at this; omega) hSr2 hr3
                        simp only [dPhi] at h19; omega
                      · have h19 := hside19 l' _ Sl hl' (by omega) el hfb1 rfl
                          (fun j hj => by have := hcnt_le2 j hj; simp only [countExit] at this; omega) (by omega) hl3
                        simp only [dPhi] at h19; omega
                · -- |S_r| = 4 (8 leaves): either ≥ 5 on one side (20+18=38) or (4, 4) -> 19+19=38!
                  by_cases hr5 : 5 ≤ countExitsIn (S_set d r) r'
                  · omega
                  · by_cases hl5 : 5 ≤ countExitsIn (S_set d r) l'
                    · omega
                    · have h19r := aux4_side r' _ hr' (by omega) er hfb0 (by omega)
                      have h19l := aux4_side l' _ hl' (by omega) el hfb1 (by omega)
                      simp only [dPhi] at h19r h19l; omega
              · have hns : ∀ v : Variable, f ≠ {v} := fun v hv' => hsing ⟨v, hv'⟩
                rw [grant_nonsingle hns true] at bl; rw [grant_nonsingle hns false] at br
                have h10 := req_one_of_fixedBits_le_one (ow := M d r) (by rw [fixedBits_empty]; omega)
                rcases (show ((dMarks (keyAt d) r').length = 4 ∧ (dMarks (keyAt d) l').length = 0) ∨
                    ((dMarks (keyAt d) r').length = 3 ∧ (dMarks (keyAt d) l').length = 1) ∨
                    ((dMarks (keyAt d) r').length = 2 ∧ (dMarks (keyAt d) l').length = 2) ∨
                    ((dMarks (keyAt d) r').length = 1 ∧ (dMarks (keyAt d) l').length = 3) ∨
                    ((dMarks (keyAt d) r').length = 0 ∧ (dMarks (keyAt d) l').length = 4) by omega) with
                    ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩ | ⟨er, el⟩
                · have hl0 : dMarks (keyAt d) l' = [] := List.eq_nil_of_length_eq_zero el
                  rw [er] at br; simp only [req] at br
                  by_cases hml1 : 1 ≤ countExitsIn (S_set d r) l'
                  · omega
                  · have := ihr (by omega) er (by intro j hj; have := htw_sub j hj; simpa [dMarks, hl0] using this)
                      (fun j hj => by have := hcnt_le2 j hj; simp only [countExit] at this; omega) (by omega)
                    omega
                · rw [er] at br; rw [el, h10] at bl; simp only [req] at br; omega
                · rw [er] at br; rw [el] at bl; simp [req, fixedBits_empty] at br bl; omega
                · rw [el] at bl; rw [er, h10] at br; simp only [req] at bl; omega
                · have hr0 : dMarks (keyAt d) r' = [] := List.eq_nil_of_length_eq_zero er
                  rw [el] at bl; simp only [req] at bl
                  by_cases hmr1 : 1 ≤ countExitsIn (S_set d r) r'
                  · omega
                  · have := ihl (by omega) el (by intro j hj; have := htw_sub j hj; simpa [dMarks, hr0] using this)
                      (fun j hj => by have := hcnt_le2 j hj; simp only [countExit] at this; omega) (by omega)
                    omega
          have h34 := aux4 (d.dUnroll r) (st d r) hv hw0 hk4
            (fun j hj => (Finset.mem_filter.mp hj).2.2.2.2)
            (fun j hj => by have := (Finset.mem_filter.mp hj).2.2.2.1; omega)
            (S_set_count_eq d r)
          omega
        · -- k = 4, w ≥ 1: dPhi ≥ 38 (and ≥ 10 + 8*|S_r|) covers |S_r| = 3 and |S_r| = 4!
          have h38 := dValid_k4_weak_ge_38 hd hv hk4 (by change 1 ≤ w d r; omega)
          omega

theorem global_contradiction (hsmall : d.pi.length ≤ 111) : False := by
  classical
  have hsum_local := Finset.sum_le_sum (s := dRoots d) (fun r hr => local_bound d hr)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum_local
  have hch := sum_inCharge_le d
  have htw := sum_outTwin_eq_sum_inTwin d
  have hphi_ch : (∑ r ∈ dRoots d, dPhi (wt d r) (d.dUnroll r)) +
      (∑ r ∈ dRoots d, exitWeightSum (edgeCh d r) (d.dUnroll r)) =
      6 * (∑ r ∈ dRoots d, e d r) + (∑ r ∈ dRoots d, a d r) + 10 * (∑ r ∈ dRoots d, w d r) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    unfold dPhi e a w
    have h6e : exitWeightSum (wt d r) (d.dUnroll r) + exitWeightSum (edgeCh d r) (d.dUnroll r) = 6 * dExits (d.dUnroll r) := by
      generalize d.dUnroll r = t
      induction t with
      | axUniq _ | axRep _ => simp [exitWeightSum, dExits]
      | exitDer j => simp [exitWeightSum, dExits]; have := edgeCh_add_wt d r j; omega
      | weak _ t ih => exact ih
      | res _ _ l' r' ihl ihr => simp only [exitWeightSum, dExits]; omega
    omega
  have hk_sum := sum_dMarks d
  have ha_sum := sum_dAxReps d
  have hw_sum := sum_dWeaks d
  have he_sum := sum_dExits d
  have hroots := dRoots_card_le d
  have harep := A_rep_le_s_ax d
  have hbud := node_budget d hsmall
  -- Combine all global conservation laws: 322 ≤ 10 * (s_der + s_ax + W_tot) ≤ 320!
  have hbonus_eq : (∑ r ∈ dRoots d, ((if isH2 d r then 6 else 0) + (if isH1_d3 d r then 5 else 0) + (if isH1_d2 d r then 4 else 0))) =
      (∑ r ∈ dRoots d, if isH2 d r then 6 else 0) + (∑ r ∈ dRoots d, if isH1_d3 d r then 5 else 0) +
      (∑ r ∈ dRoots d, if isH1_d2 d r then 4 else 0) := by
    simp only [Finset.sum_add_distrib]
  rw [hbonus_eq] at hch
  dsimp only [k, e, a, w, M_list] at hsum_local hphi_ch
  omega

end GlobalCharge

/-! ## Section 6: Main Theorem -/

open PEqualNP.ProofComplexity Dag BPHP GlobalCharge

theorem proved : ¬ (∃ π : List (LinClause (Fin 5 × Fin 2)),
    IsLinRefutation (BPHP 5 2) π ∧ π.length ≤ 111) := by
  rintro ⟨pi, ⟨deriv, empty⟩, size⟩
  obtain ⟨d, smaller⟩ := shortest_dag deriv empty
  exact global_contradiction d (smaller.trans size)

end PEqualNP.Outside.L_pcx_132_aux

theorem PEqualNP.Outside.L_pcx_132 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 111) := PEqualNP.Outside.L_pcx_132_aux.proved
