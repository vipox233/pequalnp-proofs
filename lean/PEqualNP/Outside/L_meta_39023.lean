import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39023

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276813000 * 2 ^ 32 + 4241029256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x00319e44391098a8#64 ++ 0xa00633c887221315#64 ++ 0xa873fe44791199ff#64 ++ 0xd50e7fc88f22333f#64 : BitVec 256),
   (0x08844019c0676152#64 ++ 0x41108803380cec2a#64 ++ 0xd98c407fe1ffe1ff#64 ++ 0xbb31880ffc3ffc3f#64 : BitVec 256),
   (0x020b82868a1a2a60#64 ++ 0x80417050d143454c#64 ++ 0xfe0f87879e1e7e67#64 ++ 0x7fc1f0f0f3c3cfcc#64 : BitVec 256),
   (0x0570056815a05583#64 ++ 0x00ae00ad02b40ab0#64 ++ 0xfff007f81fe07f86#64 ++ 0xfffe00ff03fc0ff0#64 : BitVec 256),
   (0x17dee8001fdd8004#64 ++ 0x02fbdd0003fbb000#64 ++ 0x97fff8001fff8005#64 ++ 0xf2ffff0003fff000#64 : BitVec 256),
   (0x27ef77f760000000#64 ++ 0x04fdeefeec000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 9]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa873fe44791199ff 0xd50e7fc88f22333f

def z1 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0f87879e1e7e67 0x7fc1f0f0f3c3cfcc

def z2 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff007f81fe07f86 0xfffe00ff03fc0ff0

def z3 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd98c407fe1ffe1ff 0xbb31880ffc3ffc3f

def z4 : W := mkw 0x15f5fe443dd598ac 0xa2bebfc887bab315 0xa9f3fe4479f199ff 0xd53e7fc88f3e333f

def z5 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97fff8001fff8005 0xf2ffff0003fff000

def z6 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x2de47579e0676152 0x45bc8eaf3c0cec2a 0xd9fc787fe1ffe1ff 0xbb3f8f0ffc3ffc3f

def z8 : W := mkw 0x0df4457955e55593 0x41be88af2abcaab2 0x01f0407861e18198 0x803e080f0c3c3033

def z9 : W := mkw 0x0df44579d5e775d3 0x41be88af3abceeba 0xfffc47ffffffffff 0xffff88ffffffffff

def z10 : W := mkw 0x0020056800205583 0x000400ad00040ab0 0xf98007f801e07f86 0xbf3000ff003c0ff0

def z11 : W := mkw 0x08844019c0226152 0x4110880338044c2a 0xc98c407fe00061fb 0xb931880ffc000c3f

def z12 : W := mkw 0x17fffec6bfdfbaec 0xa2ffffd8d7fbf75d 0xffffffc7ffffffff 0xfffffff8ffffffff

def z13 : W := mkw 0x0030044011001080 0x0006008802200210 0xa870064019001986 0xd50e00c803200330

def z14 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0x578001b806e06600 0x2af0003700dc0cc0

def z15 : W := mkw 0x200001b340000000 0x0400003668000000 0x400001bb80000000 0x0800003770000000

def z16 : W := mkw 0x00211644200018a8 0xa00422c884000315 0x28000644600019fa 0x050000c88c00033f

def z17 : W := mkw 0x37fffff77fdd8004 0x06fffffeeffbb000 0xf7ffffffffff8007 0xfefffffffffff000

def z18 : W := mkw 0x021b8a869b1abae8 0xa0437150d363575d 0xfe0f87879f1fffff 0x7fc1f0f0f3e3ffff

def z19 : W := mkw 0x282117ffe0226152 0x450422fffc044c2a 0x680007ffe00061fa 0x0d0000fffc000c3f

def z20 : W := mkw 0x2fef77ffe0676152 0x45fdeefffc0cec2a 0xffffffffe1ffe1ff 0xfffffffffc3ffc3f

def z21 : W := mkw 0x0030056815a05583 0x000600ad02b40ab0 0x780007f81fe07f86 0x0f0000ff03fc0ff0

def z22 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x000f8007801e0061 0x0001f000f003c00c

def z23 : W := mkw 0x0001820488122860 0x800030409102450c 0xf80f8607981e7867 0x7f01f0c0f303cf0c

def z24 : W := mkw 0x2fef77ffe0676152 0x45fdeefffc0cec2a 0xf7ffffffe0ee6003 0xfefffffffc1dcc00

def z25 : W := mkw 0x175aa8001f988004 0x02eb550003f31000 0x0673b8001e000000 0x40ce770003c00000

def z26 : W := mkw 0x17fffe443fdd98ac 0xa2ffffc887fbb315 0xbffffe447fff99ff 0xf7ffffc88ffff33f

def z27 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x180f80079e1e7e65 0x0301f000f3c3cfcc

def z28 : W := mkw 0x17cee8000a5d8004 0x02f9dd00014bb000 0x87fff800001f8001 0xf0ffff000003f000

def z29 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0xb60f87801e1e1e05 0x76c1f0f003c3c3c0

def z30 : W := mkw 0x0df44579d5e775d3 0x41be88af3abceeba 0xd9fc407fe1ffe1ff 0xbb3f880ffc3ffc3f

def z31 : W := mkw 0x076b87e68a1a2a60 0x80ed70fcd143454c 0xffff87ff9e1e7e67 0xfffff0fff3c3cfcc

def z32 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x01fff80001ff8001 0x803fff00003ff000

def z33 : W := mkw 0x00118a0419108820 0x8002314083221104 0xa873fe0419119867 0xd50e7fc08322330c

def z34 : W := mkw 0x0000000800204102 0x0000000100040820 0xd980007801e06186 0xbb30000f003c0c30

def z35 : W := mkw 0x0084400800654102 0x00108801000ca820 0xd98c407801ffe187 0xbb31880f003ffc30

def z36 : W := mkw 0x0560056000000000 0x00ac00ac00000000 0xe7f007f800000002 0xfcfe00ff00000000

def z37 : W := mkw 0x228f729760000000 0x0451ee52ec000000 0x000ff807e0000001 0x0001ff00fc000000

def z38 : W := mkw 0x0084400000450000 0x001088000008a000 0x918c400001ff8005 0xb2318800003ff000

def z39 : W := mkw 0x1fdee819dfffe156 0x43fbdd033bfffc2a 0xdffff87fffffe1ff 0xfbffff0ffffffc3f

def z40 : W := mkw 0x175aa8001fdd8004 0x02eb550003fbb000 0x1673b8001fff8004 0x42ce770003fff000

def z41 : W := mkw 0x25e5777560000000 0x04bcaeeeac000000 0xa1f3fe7c60000003 0xd43e7fcf8c000000

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe0007801e007e06 0x7fc000f003c00fc0

def z43 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x01f0007801e00180 0x803e000f003c0030

def z44 : W := mkw 0x0550000015800000 0x00aa000002b00000 0x01f0000001e00000 0x803e0000003c0000

def z45 : W := mkw 0x17de680015c58004 0x02fbcd0002b8b000 0x87fff80001e18001 0xf0ffff00003c3000

def z46 : W := mkw 0x08000019c0676152 0x41000003380cec2a 0x5800007fe1ffe1fe 0x0b00000ffc3ffc3f

def z47 : W := mkw 0x0885c21dc8776972 0xc110b843b90eed2e 0xf98fc67ff9fff9ff 0xff31f8cfff3fff3f

def z48 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0x260387801e001e00 0x44c070f003c003c0

def z49 : W := mkw 0x0a8fc297ca5f2a70 0xc151f852f94be54e 0x000fc007e01f8079 0x0001f800fc03f00f

def z50 : W := mkw 0x0a8fc29fca7f6b72 0xc151f853f94fed6e 0xff8fc7ffffffffff 0xfff1f8ffffffffff

def z51 : W := mkw 0x000080008a1a2a60 0x800010001143454c 0x180000001e1e7e64 0x0300000003c3cfcc

def z52 : W := mkw 0x27ee65f340000000 0x04fdccbe68000000 0xe7fc07fb80000002 0xfcff80ff70000000

def z53 : W := mkw 0x021b8a869b1aaa60 0x80437150d363554c 0xfe7fff879f1ffe67 0xffcffff0f3e3ffcc

def z54 : W := mkw 0x17dfea869fdfaa64 0x82fbfd50d3fbf54c 0x97fff8079fff8065 0xf2ffff00f3fff00c

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x88004044611181ff 0x910008088c22303f

def z56 : W := mkw 0x08b5de5df977f9fa 0xe116bbcbbf2eff3f 0xf9fffe7ff9fff9ff 0xff3fffcfff3fff3f

def z57 : W := mkw 0x202117f7600018a8 0xa40422feec000315 0x680007ffe00019fa 0x0d0000fffc00033f

def z58 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0x267007801e001e00 0x44ce00f003c003c0

def z59 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x6e0387879e007e62 0x4dc070f0f3c00fcc

def z60 : W := mkw 0x0094c80019558000 0x00129900032ab000 0x91fff80019ff8005 0xf23fff00033ff000

def z61 : W := mkw 0x27ffffff7db0ddab 0xa4ffffffefb61bb5 0xfffffffffff1ffff 0xfffffffffffe3fff

def z62 : W := mkw 0x0000000080022040 0x0000000010004408 0xd80c4047e11fe1ff 0xbb018808fc23fc3f

def z63 : W := mkw 0x00301c4031009088 0x2006038806201211 0x0070784061018198 0x800e0f080c203033

def z64 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0xff8007b81ee07e06 0x7ff000f703dc0fc0

def z65 : W := mkw 0x081088089977f9fa 0xe1021101132eff3f 0x1800000019fff9fc 0x03000000033fff3f

def z66 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xfe73ffc47f11ffff 0xffce7ff88fe23fff

def z67 : W := mkw 0x25e4757160000000 0x04bc8eae2c000000 0xe7f07ff860000002 0xfcfe0fff0c000000

def z68 : W := mkw 0x0084400000450000 0x001088000008a000 0x0180400001e18000 0x80300800003c3000

def z69 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd98c003f80fe6067 0x3b318007f01fcc0c

def z70 : W := mkw 0x0000000804a04503 0x00000001009408a0 0x1000000006e06600 0x0200000000dc0cc0

def z71 : W := mkw 0x276b37e620000000 0x04ed66fcc4000000 0xe67fbf8780000003 0x7ccff7f0f0000000

def z72 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0fc7c7ff1fffff 0xffc1f8f8ffe3ffff

def z73 : W := mkw 0x27ce61b340000000 0x04f9cc3668000000 0xc7fff9bb80000001 0xf8ffff3770000000

def z74 : W := mkw 0x080080088a7f6b72 0xc1001001114fed6e 0x180000001ffffffc 0x0300000003ffffff

def z75 : W := mkw 0x0084400000450000 0x001088000008a000 0x000c4000001f8001 0x000188000003f000

def z76 : W := mkw 0x00019a0428108828 0xa000334085021105 0x0003f80460118079 0x00007f008c02300f

def z77 : W := mkw 0x276b37e620000000 0x04ed66fcc4000000 0xe7f3bff800000002 0xfcfe77ff00000000

def z78 : W := mkw 0x05719f64391098a8 0xa0ae33ec87221315 0xeff3fffc791199ff 0xfdfe7fff8f22333f

def z79 : W := mkw 0x07ce600000000000 0x00f9cc0000000000 0x87fff80000000001 0xf0ffff0000000000

def z80 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x267fff87e0000001 0x44cffff0fc000000

def z81 : W := mkw 0x17feed681ffdd587 0x02ffddad03ffbab0 0xfffffff81fffff87 0xffffffff03fffff0

def z82 : W := mkw 0x00000000820a2240 0x0000000010414448 0x10000000060e6600 0x0200000000c1ccc0

def z83 : W := mkw 0x0084400000450000 0x001088000008a000 0x998c404461ff81ff 0xb33188088c3ff03f

def z84 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x27f3fff860000000 0xc4fe7fff0c000000

def z85 : W := mkw 0x17dfea869fdfaa64 0x82fbfd50d3fbf54c 0xffffff879ffffe67 0xfffffff0f3ffffcc

def z86 : W := mkw 0x020b028680022a60 0x80416050d000454c 0xee0f878780007e63 0x7dc1f0f0f0000fcc

def z87 : W := mkw 0x0010880019108000 0x0002110003221000 0x8073f80019118005 0xd00e7f0003223000

def z88 : W := mkw 0x020a80000a180000 0x0041500001430000 0x960f80001e1e0005 0x72c1f00003c3c000

def z89 : W := mkw 0x028fc2868a5f2a60 0x8051f850d14be54c 0xff8fc7879ffffe67 0xfff1f8f0f3ffffcc

def z90 : W := mkw 0x202117e620000000 0x040422fcc4000000 0x2000078000000000 0x040000f000000000

def z91 : W := mkw 0x202117f760000000 0x040422feec000000 0x600007ffe0000002 0x0c0000fffc000000

def z92 : W := mkw 0x0884401940654112 0x41108803280ca822 0x0180407861e18198 0x8030080f0c3c3033

def z93 : W := mkw 0x20319ff7791098a8 0xa40633feef221315 0xe873fffff91199ff 0xdd0e7fffff22333f

def z94 : W := mkw 0x0021164420000000 0x000422c884000000 0xa073fe4460000003 0xd40e7fc88c000000

def z95 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xd9f0007801e06186 0xbb3e000f003c0c30

def z96 : W := mkw 0x202117ff60205583 0x040422ffec040ab0 0x680007ffe0007f82 0x0d0000fffc000ff0

def z97 : W := mkw 0x07ce600000450000 0x00f9cc000008a000 0x97fff80001ff8005 0xf2ffff00003ff000

def z98 : W := mkw 0x27ff7ff771009088 0x24ffeffeee201211 0xe7ffffffe101819b 0xfcfffffffc203033

def z99 : W := mkw 0x020a0082820a2240 0x0041401050414448 0xfe0c07839e0e7e06 0x7fc180f073c1cfc0

def z100 : W := mkw 0x202117f760000000 0x040422feec000000 0xe073ffffe0000003 0xdc0e7ffffc000000

def z101 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xffffff801ffffe07 0xfffffff003ffffc0

def z102 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xfffffffffe007e07 0xffffffffffc00fc0

def z103 : W := mkw 0x08844011c0472050 0x411088023808e40a 0x000c4007e01f8079 0x00018800fc03f00f

def z104 : W := mkw 0x0800000880676152 0x41000001100cec2a 0x1800000001ffe1fc 0x03000000003ffc3f

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000404061018198 0x800008080c203033

def z106 : W := mkw 0x101088001fdd8004 0x0202110003fbb000 0x9073f8001fff8005 0xd20e7f0003fff000

def z107 : W := mkw 0x0801029fc0226b72 0xc1002053f8044d6e 0x680007ffe0007ffa 0x0d0000fffc000fff

def z108 : W := mkw 0x020a80000a180000 0x0041500001430000 0x060380001e000000 0x40c0700003c00000

def z109 : W := mkw 0x27eff7f76a180a20 0x84fdfefeed430144 0xe7fffffffe001e03 0xfcffffffffc003c0

def z110 : W := mkw 0x128fea868a5faa64 0x8251fd50d14bf54c 0xfe0fff879e1ffe67 0x7fc1fff0f3c3ffcc

def z111 : W := mkw 0x0010000815a05583 0x0002000102b40ab0 0x180000001fe07f84 0x0300000003fc0ff0

def z112 : W := mkw 0x27ff77ff75a05583 0x04ffeeffeeb40ab0 0xffffffffffe07f87 0xfffffffffffc0ff0

def z113 : W := mkw 0x0000000080022040 0x0000000010004408 0x500c0003800e6000 0x2a0180007001cc00

def z114 : W := mkw 0x0571876c1db05da3 0x80ae30ed83b60bb4 0xfff387fc1ff07fe7 0xfffe70ff83fe0ffc

def z115 : W := mkw 0x0020044000000000 0x0004008800000000 0xa070064000000002 0xd40e00c800000000

def z116 : W := mkw 0x00108800191098a8 0xa002110003221315 0x08000000191199fc 0x010000000322333f

def z117 : W := mkw 0x27ce61b340000000 0x04f9cc3668000000 0x478c01bb80000000 0x28f1803770000000

def z118 : W := mkw 0x05c4600000000000 0x00b88c0000000000 0x01f0780000000000 0x803e0f0000000000

def z119 : W := mkw 0x077b07ee15a05583 0x00ef60fdc2b40ab0 0xffff87ff9fe07f87 0xfffff0fff3fc0ff0

def z120 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa073fe0019119805 0xd40e7fc003223300

def z121 : W := mkw 0x020b82860a180000 0x00417050c1430000 0xf60f87879e1e0007 0x7ec1f0f0f3c3c000

def z122 : W := mkw 0x0010080011008000 0x0002010002201000 0x0070780001018000 0x800e0f0000203000

def z123 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd18c407fe0ee6003 0xba31880ffc1dcc00

def z124 : W := mkw 0x000080008a1a2a60 0x800010001143454c 0x00000000001e0060 0x000000000003c00c

def z125 : W := mkw 0x37dffa977fdd8004 0x06fbff52effbb000 0x97fff807ffff8005 0xf2ffff00fffff000

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000400100067 0x110000008002000c

def z127 : W := mkw 0x023b9ec6bb1abae8 0xa04773d8d763575d 0xfe7fffc7ff1fffff 0xffcffff8ffe3ffff

def z128 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x77f007b81ee07e00 0x6efe00f703dc0fc0

def z129 : W := mkw 0x0000000800204102 0x0000000100040820 0x0180007801e00180 0x8030000f003c0030

def z130 : W := mkw 0x08b5de55f957b8f8 0xe116bbcabf2af71f 0xa87ffe47f91f99ff 0xd50fffc8ff23f33f

def z131 : W := mkw 0x0084401140000000 0x0010880228000000 0xc18c407fe0000003 0xb831880ffc000000

def z132 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x0073f844611181f9 0x800e7f088c22303f

def z133 : W := mkw 0x228ff297ea1a2a60 0x8451fe52fd43454c 0x000ff807e01e0061 0x0001ff00fc03c00c

def z134 : W := mkw 0x08000019c0226152 0x4100000338044c2a 0x4800007fe00061fa 0x0900000ffc000c3f

def z135 : W := mkw 0x0884c019ca7f6b72 0xc1109803394fed6e 0xd98c407fffffffff 0xbb31880fffffffff

def z136 : W := mkw 0x1fce6019c6ef6156 0x43f9cc0338ddec2a 0x578c003b86ee6000 0x2af1800770ddcc00

def z137 : W := mkw 0x05719f6c3db0ddab 0xa0ae33ed87b61bb5 0xfff3fffc7ff1ffff 0xfffe7fff8ffe3fff

def z138 : W := mkw 0x0000000800204102 0x0000000100040820 0xff8007f81fe07f86 0xfff000ff03fc0ff0

def z139 : W := mkw 0x023b9ec63b189aa8 0xa04773d8c7631355 0xae73ffc47f119fff 0xd5ce7ff88fe233ff

def z140 : W := mkw 0x276b37e620000000 0x04ed66fcc4000000 0x2673bf8000000000 0x44ce77f000000000

def z141 : W := mkw 0x17dee9281ffdc507 0x02fbdd2503ffb8a0 0xd7fff9b81fffe605 0xfaffff3703fffcc0

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0xe600078000000002 0x7cc000f000000000

def z143 : W := mkw 0x277b37ee35a05583 0x04ef66fdc6b40ab0 0xfff3bff81fe07f86 0xfffe77ff03fc0ff0

def z144 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x018c407fe1ff81f9 0x8031880ffc3ff03f

def z145 : W := mkw 0x020a000000000000 0x0041400000000000 0x860f800000000001 0x70c1f00000000000

def z146 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0xb7f007801fe01e04 0xf6fe00f003fc03c0

def z147 : W := mkw 0x228e609340000000 0x0451cc1268000000 0x000c000380000000 0x0001800070000000

def z148 : W := mkw 0x17ce600006cd0004 0x02f9cc0000d9a000 0x178c000006ee0000 0x22f1800000ddc000

def z149 : W := mkw 0x00319f6c3930ddab 0xa00633ed87261bb5 0xe873fffc7911ffff 0xdd0e7fff8f223fff

def z150 : W := mkw 0x020b9a86aa1aaa68 0xa0417350d543554d 0xfe0fff87fe1ffe7f 0x7fc1fff0ffc3ffcf

def z151 : W := mkw 0x27fffff779108000 0x04fffffeef221000 0xe7fffffff9118007 0xfcffffffff223000

def z152 : W := mkw 0x07ef764420000000 0x00fdeec884000000 0xa7fffe4460000003 0xf4ffffc88c000000

def z153 : W := mkw 0x0df4457955e55593 0x41be88af2abcaab2 0xfff047f87fe1ff9e 0xfffe08ff0ffc3ff3

def z154 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xe7f007f801e00182 0xfcfe00ff003c0030

def z155 : W := mkw 0x0fffc7ffdfff7ff3 0xc1fff8fffbffeffe 0xffffc7ffffffffff 0xfffff8ffffffffff

def z156 : W := mkw 0x0000000080022040 0x0000000010004408 0x4800000780006062 0x09000000f0000c0c

def z157 : W := mkw 0x128ee8000a5d8004 0x0251dd00014bb000 0x000ff800001f8001 0x0001ff000003f000

def z158 : W := mkw 0x00311644310018a8 0xa00622c886200315 0xa8700644790019fe 0xd50e00c88f20033f

def z159 : W := mkw 0x0030044011001080 0x0006008802200210 0x0070004001000180 0x800e000800200030

def z160 : W := mkw 0x276bb7e62a180a20 0x84ed76fcc5430144 0x2673bf801e001e00 0x44ce77f003c003c0

def z161 : W := mkw 0x27ef77ff60205583 0x04fdeeffec040ab0 0xefffffffe0007f83 0xfdfffffffc000ff0

def z162 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x57f001f807e06780 0xaafe003f00fc0cf0

def z163 : W := mkw 0x2084701160000000 0x04108e022c000000 0x0000780060000000 0x00000f000c000000

def z164 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x3e7007801fe07f84 0x47ce00f003fc0ff0

def z165 : W := mkw 0x17ffff6c3ffdddaf 0xa2ffffed87ffbbb5 0xfffffffc7fffffff 0xffffffff8fffffff

def z166 : W := mkw 0x128ffa042a5d882c 0xa251ff40854bb105 0x000ff804601f8079 0x0001ff008c03f00f

def z167 : W := mkw 0x000080008a1a2a60 0x800010001143454c 0xfe0007801e1e7e66 0x7fc000f003c3cfcc

def z168 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x01fff87fe0000001 0x803fff0ffc000000

def z169 : W := mkw 0x175baa869f9aaa64 0x82eb7550d3f3554c 0xfe7fbf879e1e7e67 0x7fcff7f0f3c3cfcc

def z170 : W := mkw 0x17cee0000edd0004 0x02f9dc0001dba000 0x978f80001efe0005 0x72f1f00003dfc000

def z171 : W := mkw 0x1fdee819dfffe156 0x43fbdd033bfffc2a 0xd7fff83b9fffe005 0xfaffff0773fffc00

def z172 : W := mkw 0x175aa8001f988004 0x02eb550003f31000 0x8673f8001f118005 0xd0ce7f0003e23000

def z173 : W := mkw 0x202117f7e0022a60 0x840422fefc00454c 0x680007ffe0007e62 0x0d0000fffc000fcc

def z174 : W := mkw 0x220b328620000000 0x04416650c4000000 0x0003b80000000000 0x0000770000000000

def z175 : W := mkw 0x00319e4439108000 0x000633c887221000 0xa073fe4479118007 0xd40e7fc88f223000

def z176 : W := mkw 0x25c4613140000000 0x04b88c2628000000 0x0180003800000000 0x0030000700000000

def z177 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x678c07ffe0000002 0x2cf180fffc000000

def z178 : W := mkw 0x128ee8000a5d8004 0x0251dd00014bb000 0x918ff80001ff8005 0xb231ff00003ff000

def z179 : W := mkw 0x17dee8001fdd98ac 0xa2fbdd0003fbb315 0x9ffff8001fff99fd 0xf3ffff0003fff33f

def z180 : W := mkw 0x0001028600000000 0x00002050c0000000 0x6000078780000002 0x0c0000f0f0000000

def z181 : W := mkw 0x0030044011001080 0x0006008802200210 0xa8704644791199ff 0xd50e08c88f22333f

def z182 : W := mkw 0x05708d681db0d583 0x00ae11ad03b61ab0 0xfff3fff81ff1ff87 0xfffe7fff03fe3ff0

def z183 : W := mkw 0x37ef77f766cd0004 0x06fdeefeecd9a000 0xf7ffffffe6ee0003 0xfefffffffcddc000

def z184 : W := mkw 0x075b82869f9a2a60 0x80eb7050d3f3454c 0xffff87879ffe7e67 0xfffff0f0f3ffcfcc

def z185 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2073be0018001800 0x440e77c003000300

def z186 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x518c003b80ee6000 0x2a318007701dcc00

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000001e007e04 0x0300000003c00fc0

def z188 : W := mkw 0x228f729760000000 0x0451ee52ec000000 0xc18ff87fe0000003 0xb831ff0ffc000000

def z189 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x680f8787801e7e63 0x0d01f0f0f003cfcc

def z190 : W := mkw 0x0001820408100820 0x8000304081020104 0xa803860418101867 0x550070c08302030c

def z191 : W := mkw 0x17ce608286cf2244 0x02f9cc1050d9e448 0x578c018386ee6600 0x2af1803070ddccc0

def z192 : W := mkw 0x1fdee8089fffe156 0x43fbdd0113fffc2a 0x9ffff8001fffe1fd 0xf3ffff0003fffc3f

def z193 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x518c403fe0ffe079 0x2a318807fc1ffc0f

def z194 : W := mkw 0x0800000880676152 0x41000001100cec2a 0x9800404461ffe1ff 0x930008088c3ffc3f

def z195 : W := mkw 0x05719f6c3db0ddab 0xa0ae33ed87b61bb5 0xa9f3fe7c79f199ff 0xd53e7fcf8f3e333f

def z196 : W := mkw 0x27ff77ff75a05583 0x04ffeeffeeb40ab0 0xe7ffffffe1e00183 0xfcfffffffc3c0030

def z197 : W := mkw 0x0d700579d5a275d3 0x41ae00af3ab44eba 0xfff007ffffe07ffe 0xfffe00fffffc0fff

def z198 : W := mkw 0x0800001940204112 0x4100000328040822 0x0000007860000198 0x0000000f0c000033

def z199 : W := mkw 0x1ffffe5dfffff9fe 0xe3ffffcbbfffff3f 0xfffffe7ffffff9ff 0xffffffcfffffff3f

def z200 : W := mkw 0x0df44579d5e775d3 0x41be88af3abceeba 0xfffc07fb9fee7f86 0xffff80ff73fdcff0

def z201 : W := mkw 0x0010000815a05583 0x0002000102b40ab0 0xd98000781fe07f86 0xbb30000f03fc0ff0

def z202 : W := mkw 0x0030044011001080 0x0006008802200210 0xfe7007c01f007f86 0xffce00f803e00ff0

def z203 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xefffffffe11181ff 0xfdfffffffc22303f

def z204 : W := mkw 0x020a0082820a2240 0x0041401050414448 0x560c0183860e6600 0x2ac1803070c1ccc0

def z205 : W := mkw 0x0885da1de877e97a 0xe110bb43bd0efd2f 0xd98ff87fe1ffe1ff 0xbb31ff0ffc3ffc3f

def z206 : W := mkw 0x17de600017cd0004 0x02fbcc0002f9a000 0x97fc00001fee0004 0xf2ff800003fdc000

def z207 : W := mkw 0x000182868a1a2a60 0x80003050d143454c 0x780007879e1e7e66 0x0f0000f0f3c3cfcc

def z208 : W := mkw 0x020a80828a1a2a60 0x804150105143454c 0x5e0c01839e1e7e64 0x2bc1803073c3cfcc

def z209 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x3e0387801e1e7e64 0x47c070f003c3cfcc

def z210 : W := mkw 0x37dee9b35fdd8004 0x06fbdd366bfbb000 0xd7fff9bb9fff8005 0xfaffff3773fff000

def z211 : W := mkw 0x0000000080022040 0x0000000010004408 0xd80c0007801e6067 0x3b018000f003cc0c

def z212 : W := mkw 0x021b828e9fba7fe3 0x80437051d3f74ffc 0xfe0f87879ffe7fe7 0x7fc1f0f0f3ffcffc

def z213 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x9ffff8447fff81ff 0xf3ffff088ffff03f

def z214 : W := mkw 0x0550000015800000 0x00aa000002b00000 0x97f000001fe00004 0xf2fe000003fc0000

def z215 : W := mkw 0x0020056800205583 0x000400ad00040ab0 0x680007f800007f82 0x0d0000ff00000ff0

def z216 : W := mkw 0x22bffed7791098a8 0xa457ffdaef221315 0xa87ffe47f91199ff 0xd50fffc8ff22333f

def z217 : W := mkw 0x0000800008100820 0x8000100001020104 0x0800000018101864 0x010000000302030c

def z218 : W := mkw 0x0000880008108828 0xa000110001021105 0x0000000000118078 0x000000000002300f

def z219 : W := mkw 0x0000000080022a60 0x800000001000454c 0x0800000000007e60 0x0100000000000fcc

def z220 : W := mkw 0x074a200000000000 0x00e9440000000000 0x0673b80000000000 0x40ce770000000000

def z221 : W := mkw 0x0030044011001080 0x0006008802200210 0x2070060018001800 0x440e00c003000300

def z222 : W := mkw 0x101088001fdd8004 0x0202110003fbb000 0x100000001fff8004 0x0200000003fff000

def z223 : W := mkw 0x276b37e620000000 0x04ed66fcc4000000 0xa673ffc460000003 0xd4ce7ff88c000000

def z224 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x97f000781fe00184 0xf2fe000f03fc0030

def z225 : W := mkw 0x020b0286820a2a60 0x80416050d041454c 0x7e0c0787860e7e62 0x2fc180f0f0c1cfcc

def z226 : W := mkw 0x05e4457140000000 0x00bc88ae28000000 0xe7fc47ffe0000003 0xfcff88fffc000000

def z227 : W := mkw 0x0001820408100820 0x8000304081020104 0xfe0387841e107e67 0x7fc070f083c20fcc

def z228 : W := mkw 0x0540012000000000 0x00a8002400000000 0x478001b800000000 0x28f0003700000000

def z229 : W := mkw 0x05701d6835a0d58b 0x20ae03ad06b41ab1 0xfff07ff87fe1ff9e 0xfffe0fff0ffc3ff3

def z230 : W := mkw 0x020a80000a180000 0x0041500001430000 0x000f8000001e0001 0x0001f0000003c000

def z231 : W := mkw 0x17dfea861fdd8004 0x02fbfd50c3fbb000 0xf7ffff879fff8007 0xfefffff0f3fff000

def z232 : W := mkw 0x25e4757160000000 0x04bc8eae2c000000 0x01f0787860000000 0x803e0f0f0c000000

def z233 : W := mkw 0x0010000015801481 0x0002000002b00290 0x000000001e001e00 0x0000000003c003c0

def z234 : W := mkw 0x0800000880226152 0x4100000110044c2a 0x08000000000061f8 0x0100000000000c3f

def z235 : W := mkw 0x020b028600000000 0x00416050c0000000 0xe60f878780000003 0x7cc1f0f0f0000000

def z236 : W := mkw 0x17ce612806ed4507 0x02f9cc2500dda8a0 0x578c01b806ee6600 0x2af1803700ddccc0

def z237 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873be00191199fc 0x450e77c00322333f

def z238 : W := mkw 0x0001028680022a60 0x80002050d000454c 0x6800078780007e62 0x0d0000f0f0000fcc

def z239 : W := mkw 0x15d4680015c58004 0x02ba8d0002b8b000 0x01f0780001e18000 0x803e0f00003c3000

def z240 : W := mkw 0x25f5ff75791098a8 0xa4bebfeeaf221315 0xa9f3fe7c791199ff 0xd53e7fcf8f22333f

def z241 : W := mkw 0x0000000800204102 0x0000000100040820 0xd980407c61f1e1ff 0xbb30080f8c3e3c3f

def z242 : W := mkw 0x1fdfea9fdfffeb76 0xc3fbfd53fbfffd6e 0xffffffffffffffff 0xffffffffffffffff

def z243 : W := mkw 0x0885429fc0676b72 0xc110a853f80ced6e 0xf98c47ffe1ffffff 0xbf3188fffc3fffff

def z244 : W := mkw 0x08a5565de0676152 0x4114aacbbc0cec2a 0xf9fffe7fe1ffe1ff 0xff3fffcffc3ffc3f

def z245 : W := mkw 0x023b9ec6bb1abae8 0xa04773d8d763575d 0xa87ffe47f91f99ff 0xd50fffc8ff23f33f

def z246 : W := mkw 0x27eff7f7ea1a2a60 0x84fdfefefd43454c 0xfffffffffe1e7e67 0xffffffffffc3cfcc

def z247 : W := mkw 0x0550000015800000 0x00aa000002b00000 0x067000001e000000 0x40ce000003c00000

def z248 : W := mkw 0x0570044015801080 0x00ae008802b00210 0xbff006401fe01986 0xf7fe00c803fc0330

def z249 : W := mkw 0x0001120420000828 0xa000224084000105 0x0000000460000078 0x000000008c00000f

def z250 : W := mkw 0x07dee80019108000 0x00fbdd0003221000 0x87fff80019118005 0xf0ffff0003223000

def z251 : W := mkw 0x27ef77f7e0022040 0x04fdeefefc004408 0xffffffffe01e6067 0xfffffffffc03cc0c

def z252 : W := mkw 0x020a0082820a2240 0x0041401050414448 0xde0c0187861e6667 0x3bc18030f0c3cccc

def z253 : W := mkw 0x0560056804a05583 0x00ac00ad00940ab0 0x7f8007f806e07f82 0x2ff000ff00dc0ff0

def z254 : W := mkw 0x075a80001f980000 0x00eb500003f30000 0x97ff80001ffe0005 0xf2fff00003ffc000

def z255 : W := mkw 0x0084400000000000 0x0010880000000000 0x818c400000000001 0xb031880000000000

def z256 : W := mkw 0x27ef77f760450000 0x04fdeefeec08a000 0xf7ffffffe1ff8007 0xfefffffffc3ff000

def z257 : W := mkw 0x27ff77f771001080 0x04ffeefeee200210 0xeffffffff9001987 0xfdffffffff200330

def z258 : W := mkw 0x27ce61b3c20a2240 0x04f9cc3678414448 0x578c01bb860e6600 0x2af1803770c1ccc0

def z259 : W := mkw 0x27ff77f775801481 0x04ffeefeeeb00290 0xe7fffffffe001e03 0xfcffffffffc003c0

def z260 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17ffb8001eee0000 0x62fff70003ddc000

def z261 : W := mkw 0x17feed681ffdd587 0x02ffddad03ffbab0 0x97fff8781fff8185 0xf2ffff0f03fff030

def z262 : W := mkw 0x077b87ee1fb85fa3 0x80ef70fdc3f70bf4 0xfff387f81fe07f86 0xfffe70ff03fc0ff0

def z263 : W := mkw 0x222b17f760000000 0x044562feec000000 0xe60f87ffe0000003 0x7cc1f0fffc000000

def z264 : W := mkw 0x020a000002080000 0x0041400000410000 0x160c0000060e0000 0x22c1800000c1c000

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x8073f80000000001 0xd00e7f0000000000

def z266 : W := mkw 0x07ce600000000000 0x00f9cc0000000000 0x078c000000000000 0x20f1800000000000

def z267 : W := mkw 0x00211644200018a8 0xa00422c884000315 0xa873fe44600019fb 0xd50e7fc88c00033f

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400460118079 0x000008008c02300f

def z269 : W := mkw 0x27fffff7791098a8 0xa4fffffeef221315 0xeffffffff91199ff 0xfdffffffff22333f

def z270 : W := mkw 0x08000019c0226152 0x4100000338044c2a 0xd80c007fe01e61ff 0x3b01800ffc03cc3f

def z271 : W := mkw 0x17cfe2868edf2a64 0x82f9fc50d1dbe54c 0xff8f87879efe7e67 0x7ff1f0f0f3dfcfcc

def z272 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa873be4019001986 0xd50e77c803200330

def z273 : W := mkw 0x0800000880676152 0x41000001100cec2a 0xd980007801ffe1fe 0xbb30000f003ffc3f

def z274 : W := mkw 0x0000000800204102 0x0000000100040820 0x5180003800e06000 0x2a300007001c0c00

def z275 : W := mkw 0x0010880019108000 0x0002110003221000 0x0000000019118004 0x0000000003223000

def z276 : W := mkw 0x17dee8009fdfaa64 0x82fbdd0013fbf54c 0x9ffff8001ffffe65 0xf3ffff0003ffffcc

def z277 : W := mkw 0x0550012815a04503 0x00aa002502b408a0 0xd7f001b81fe06604 0xfafe003703fc0cc0

def z278 : W := mkw 0x0020056000001481 0x000400ac00000290 0x2000078000001e00 0x040000f0000003c0

def z279 : W := mkw 0x08844011c0472050 0x411088023808e40a 0x918c4007e1ff807d 0xb2318800fc3ff00f

def z280 : W := mkw 0x17feed601fdd8004 0x02ffddac03fbb000 0xf7fffff81fff8007 0xfeffffff03fff000

def z281 : W := mkw 0x3fffffffffffe156 0x47fffffffffffc2a 0xffffffffffffe1ff 0xfffffffffffffc3f

def z282 : W := mkw 0x2fce61bbc0676152 0x45f9cc37780cec2a 0x578c01bb80ee6000 0x2af18037701dcc00

def z283 : W := mkw 0x0020056800205583 0x000400ad00040ab0 0x0000007800000180 0x0000000f00000030

def z284 : W := mkw 0x077a85681fb85583 0x00ef50ad03f70ab0 0xffff87f81ffe7f87 0xfffff0ff03ffcff0

def z285 : W := mkw 0x27fffff7fb1abae8 0xa4fffffeff63575d 0xffffffffff1fffff 0xffffffffffe3ffff

def z286 : W := mkw 0x27ef77f7600018a8 0xa4fdeefeec000315 0xefffffffe00019fb 0xfdfffffffc00033f

def z287 : W := mkw 0x08000019c0226152 0x4100000338044c2a 0xc800407fe111e1ff 0x9900080ffc223c3f

def z288 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xd80f8007801e6067 0x3b01f000f003cc0c

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x5600018006006600 0x2ac0003000c00cc0

def z290 : W := mkw 0x2560356020000000 0x04ac06ac04000000 0x0070380000000000 0x000e070000000000

def z291 : W := mkw 0x0000000800204102 0x0000000100040820 0x1800000001e06184 0x03000000003c0c30

def z292 : W := mkw 0x1a8ee819ca7fe156 0x4351dd03394ffc2a 0xd98ff87fe1ffe1ff 0xbb31ff0ffc3ffc3f

def z293 : W := mkw 0x0561176420000000 0x00ac22ec84000000 0xe7f3fffc60000003 0xfcfe7fff8c000000

def z294 : W := mkw 0x0000000880226142 0x0000000110044c28 0xd98c007f81fe61e7 0xbb31800ff03fcc3c

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c0000001e0005 0x320180000003c000

def z296 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x260f87879e1e1e61 0x44c1f0f0f3c3c3cc

def z297 : W := mkw 0x00308c4019109080 0x0006118803221210 0xa873fe4019119987 0xd50e7fc803223330

def z298 : W := mkw 0x17fe656817ed5587 0x02ffccad02fdaab0 0xfffc07f81fee7f86 0xffff80ff03fdcff0

def z299 : W := mkw 0x077b87ee9fba7fe3 0x80ef70fdd3f74ffc 0xffff87ff9ffe7fe7 0xfffff0fff3ffcffc

def z300 : W := mkw 0x08944019d5e775d3 0x411288033abceeba 0xd98c407fffffffff 0xbb31880fffffffff

def z301 : W := mkw 0x028e600000000000 0x0051cc0000000000 0x000ff80000000001 0x0001ff0000000000

def z302 : W := mkw 0x020b028680022040 0x00416050d0004408 0xfe0f8787801e6067 0x7fc1f0f0f003cc0c

def z303 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd18c403b81ffe005 0xba318807703ffc00

def z304 : W := mkw 0x0000000080022040 0x0000000010004408 0xfe0c07879e1e7e67 0x7fc180f0f3c3cfcc

def z305 : W := mkw 0x100088000a5d8004 0x02001100014bb000 0x00000000001f8000 0x000000000003f000

def z306 : W := mkw 0x0800000880676152 0x41000001100cec2a 0x1000000000ee6000 0x02000000001dcc00

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x9180000001e00004 0xb2300000003c0000

def z308 : W := mkw 0x00108800191098a8 0xa002110003221315 0x88004044791199ff 0x910008088f22333f

def z309 : W := mkw 0x0560056800205583 0x00ac00ad00040ab0 0xeff007f800007f82 0xfdfe00ff00000ff0

def z310 : W := mkw 0x1010080015c58004 0x0202010002b8b000 0x0000000001e18000 0x00000000003c3000

def z311 : W := mkw 0x1fdee811dfdfa054 0x43fbdd023bfbf40a 0x97fff807ffff807d 0xf2ffff00fffff00f

def z312 : W := mkw 0x0010000015800000 0x0002000002b00000 0x100000001fe00004 0x0200000003fc0000

def z313 : W := mkw 0x08000019c0226152 0x4100000338044c2a 0xd980007fe1e061fe 0xbb30000ffc3c0c3f

def z314 : W := mkw 0x20a557f760000000 0x0414aafeec000000 0xe18c47ffe0000003 0xbc3188fffc000000

def z315 : W := mkw 0x17dee8115fdd8004 0x02fbdd022bfbb000 0xd7fff87fffff8007 0xfaffff0ffffff000

def z316 : W := mkw 0x022b96c6aa1a3ae8 0xa04572d8d543475d 0xfe0f87c7fe1e7fff 0x7fc1f0f8ffc3cfff

def z317 : W := mkw 0x0020056800205583 0x000400ad00040ab0 0xfe0007f81e007f86 0x7fc000ff03c00ff0

def z318 : W := mkw 0x021a88001b188000 0x0043510003631000 0x967ff8001f1f8005 0xf2cfff0003e3f000

def z319 : W := mkw 0x077b87e61f981ea1 0x80ef70fcc3f303d4 0x267387801e001e00 0x44ce70f003c003c0

def z320 : W := mkw 0x00311e44310098a8 0xa00623c886201315 0x28707e44610199fa 0x850e0fc88c20333f

def z321 : W := mkw 0x00844011c0022040 0x0010880238004408 0xd98c407fe01e6067 0xbb31880ffc03cc0c

def z322 : W := mkw 0x00019a0428108828 0xa000334085021105 0x8803f844611181ff 0x91007f088c22303f

def z323 : W := mkw 0x181088089fffe156 0x4302110113fffc2a 0x180000001fffe1fc 0x0300000003fffc3f

def z324 : W := mkw 0x274a21a200000000 0x04e9443440000000 0x0600018000000000 0x00c0003000000000

def z325 : W := mkw 0x15708d681ffdd587 0x02ae11ad03ffbab0 0xfff007f81fffff86 0xfffe00ff03fffff0

def z326 : W := mkw 0x057107ee95a27fe3 0x80ae20fdd2b44ffc 0xfff007ff9fe07fe6 0xfffe00fff3fc0ffc

def z327 : W := mkw 0x020a80000a180000 0x0041500001430000 0xfe0f87801e1e7e07 0x7fc1f0f003c3cfc0

def z328 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0xe7f007f81e001e02 0xfcfe00ff03c003c0

def z329 : W := mkw 0x00a5565560000000 0x0014aacaac000000 0xe1fffe7fe0000003 0xfc3fffcffc000000

def z330 : W := mkw 0x0a8f429fc0676152 0x4151e853f80cec2a 0xff8fc7ffe1ffe1ff 0xfff1f8fffc3ffc3f

def z331 : W := mkw 0x022b96c6aa1a2a60 0x804572d8d543454c 0xfe7fffc7fe1e7e67 0xffcffff8ffc3cfcc

def z332 : W := mkw 0x22af77f760000000 0x0455eefeec000000 0x600fffffe0000003 0x0c01fffffc000000

def z333 : W := mkw 0x15f46d6815e5d587 0x02be8dad02bcbab0 0x01f0787801e18180 0x803e0f0f003c3030

def z334 : W := mkw 0x08a44579c06775d3 0x411488af380ceeba 0xf98c47ffe1ffffff 0xbf3188fffc3fffff

def z335 : W := mkw 0x256117f760000000 0x04ac22feec000000 0xe7f007ffe0000002 0xfcfe00fffc000000

def z336 : W := mkw 0x05719f6c3db0ddab 0xa0ae33ed87b61bb5 0xfff3bff81fe07f86 0xfffe77ff03fc0ff0

def z337 : W := mkw 0x27ce61b340000000 0x04f9cc3668000000 0xc78c41ffe0000003 0xb8f1883ffc000000

def z338 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0x0070000000000000 0x000e000000000000

def z339 : W := mkw 0x0084401940204102 0x0010880328040820 0xd98c407fe1e06187 0xbb31880ffc3c0c30

def z340 : W := mkw 0x27ef77ff64a04503 0x04fdeeffec9408a0 0xf7ffffffe6e06603 0xfefffffffcdc0cc0

def z341 : W := mkw 0x27ef77ff60204102 0x04fdeeffec040820 0xffffffffe1e06187 0xfffffffffc3c0c30

def z342 : W := mkw 0x37effff76a5d8004 0x06fdfffeed4bb000 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z343 : W := mkw 0x276b37f760000000 0x04ed66feec000000 0x6673bfffe0000002 0x4cce77fffc000000

def z344 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x760f87839e0e7e00 0x6ec1f0f073c1cfc0

def z345 : W := mkw 0x00108800191098a8 0xa002110003221315 0x0000000018001800 0x0000000003000300

def z346 : W := mkw 0x020b82040a180820 0x8041704081430104 0xbe0f86041e1e1867 0x77c1f0c083c3c30c

def z347 : W := mkw 0x0884401940654112 0x41108803280ca822 0xd980407861e1e19e 0xbb30080f0c3c3c33

def z348 : W := mkw 0x15d4680015c58004 0x02ba8d0002b8b000 0x97f078001fe18004 0xf2fe0f0003fc3000

def z349 : W := mkw 0x15d4680015c58004 0x02ba8d0002b8b000 0x91fc780001ff8005 0xb23f8f00003ff000

def z350 : W := mkw 0x08844011c0472050 0x411088023808e40a 0xc18c407fe01f807b 0xb831880ffc03f00f

def z351 : W := mkw 0x0885da15e857a878 0xe110bb42bd0af50f 0x000ff807e01f8079 0x0001ff00fc03f00f

def z352 : W := mkw 0x020b828e8a3a6b62 0x80417051d1474d6c 0xff8f87ff9ffe7fe7 0xfff1f0fff3ffcffc

def z353 : W := mkw 0x0010880019108000 0x0002110003221000 0x8873f844791181ff 0xd10e7f088f22303f

def z354 : W := mkw 0x276bb7e6aa1a2a60 0x84ed76fcd543454c 0xfe7fbf879e1e7e67 0x7fcff7f0f3c3cfcc

def z355 : W := mkw 0x0fce6019c0676152 0x41f9cc03380cec2a 0xdffff87fe1ffe1ff 0xfbffff0ffc3ffc3f

def z356 : W := mkw 0x27fff7ffffba7fe3 0x84fffefffff74ffc 0xfffffffffffe7fe7 0xffffffffffffcffc

def z357 : W := mkw 0x028ec0000a5d0000 0x0051d800014ba000 0x978fc0001fff8005 0xf2f1f80003fff000

def z358 : W := mkw 0x2fef77f7e0472050 0x45fdeefefc08e40a 0xe7ffffffe01f807b 0xfcfffffffc03f00f

def z359 : W := mkw 0x00019a0428108828 0xa000334085021105 0x0003b80000000000 0x0000770000000000

def z360 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x07f3f8001fe18000 0xc0fe7f0003fc3000

def z361 : W := mkw 0x37fffff77fdd98ac 0xa6fffffeeffbb315 0xffffffffffff99ff 0xfffffffffffff33f

def z362 : W := mkw 0x05708d681db0ddab 0xa0ae11ad03b61bb5 0xfff007f81ff1fffe 0xfffe00ff03fe3fff

def z363 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x69f007f801e07f82 0x8d3e00ff003c0ff0

def z364 : W := mkw 0x0560056000000000 0x00ac00ac00000000 0xfff007f81e007e06 0xfffe00ff03c00fc0

def z365 : W := mkw 0x120aa8000a188004 0x0241550001431000 0x0003b80000000000 0x0000770000000000

def z366 : W := mkw 0x0084401140000000 0x0010880228000000 0x000c4007e0000001 0x00018800fc000000

def z367 : W := mkw 0x1dd4681955e5c116 0x43ba8d032abcb822 0x01f0787861e18198 0x803e0f0f0c3c3033

def z368 : W := mkw 0x0571176c35a05583 0x00ae22ed86b40ab0 0xfff3fffc7fe07f87 0xfffe7fff8ffc0ff0

def z369 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x178c00001fff8004 0x22f1800003fff000

def z370 : W := mkw 0x17dee8001f988004 0x02fbdd0003f31000 0x87fff8001e000001 0xf0ffff0003c00000

def z371 : W := mkw 0x000080000a180a20 0x8000100001430144 0x000000001e001e00 0x0000000003c003c0

def z372 : W := mkw 0x27eff7f76a180000 0x04fdfefeed430000 0xf7fffffffe1e0007 0xfeffffffffc3c000

def z373 : W := mkw 0x074b83ae8eba6f63 0x80e97075d1d74dec 0xff8f87bf9efe7e67 0x7ff1f0f7f3dfcfcc

def z374 : W := mkw 0x020a80828a1a2240 0x0041501051434448 0xd60f81839e1e6605 0x7ac1f03073c3ccc0

def z375 : W := mkw 0x08000011c0022050 0x410000023800440a 0x00000007e0000078 0x00000000fc00000f

def z376 : W := mkw 0x0020056000000000 0x000400ac00000000 0x600007f800000002 0x0c0000ff00000000

def z377 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x598c007fe0ee61fa 0x2b31800ffc1dcc3f

def z378 : W := mkw 0x002107ee80227fe3 0x800420fdd0044ffc 0x680007ff80007fe2 0x0d0000fff0000ffc

def z379 : W := mkw 0x37fffff7ffdfaa64 0x86fffffefffbf54c 0xfffffffffffffe67 0xffffffffffffffcc

def z380 : W := mkw 0x27ef77e620000000 0x04fdeefcc4000000 0xa7ffff8000000001 0xf4fffff000000000

def z381 : W := mkw 0x277bbfe6391098a8 0xa4ef77fcc7221315 0xae73ffc4791199ff 0xd5ce7ff88f22333f

def z382 : W := mkw 0x257117ff75a05583 0x04ae22ffeeb40ab0 0xfff007ffffe07f86 0xfffe00fffffc0ff0

def z383 : W := mkw 0x0540012004800401 0x00a8002400900080 0x0600018006000600 0x00c0003000c000c0

def z384 : W := mkw 0x0894c819d977e152 0x411299033b2efc2a 0xd9fff87ff9ffe1ff 0xfb3fff0fff3ffc3f

def z385 : W := mkw 0x17ce600006cd0004 0x02f9cc0000d9a000 0x978c400007ff8005 0xb2f1880000fff000

def z386 : W := mkw 0x0021164420000000 0x000422c884000000 0xa873fe44611181ff 0xd50e7fc88c22303f

def z387 : W := mkw 0x05701d6835a0d58b 0x20ae03ad06b41ab1 0x01f0787861e18198 0x803e0f0f0c3c3033

def z388 : W := mkw 0x0dc44139c4e76553 0x41b88827389cecaa 0xdf8c41ffe7ffe7ff 0xbbf1883ffcfffcff

def z389 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff047fc7ff1ffff 0xfffe08ff8ffe3fff

def z390 : W := mkw 0x020b0286820a2240 0x00416050d0414448 0xf60f8787860e6603 0x7ec1f0f0f0c1ccc0

def z391 : W := mkw 0x37fefd717fdd8004 0x06ffdfae2ffbb000 0x97fff8787fff8005 0xf2ffff0f0ffff000

def z392 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x960f80079e1e0065 0x72c1f000f3c3c00c

def z393 : W := mkw 0x0001028680022a60 0x80002050d000454c 0xf80c0787801e7e67 0x3f0180f0f003cfcc

def z394 : W := mkw 0x328ffa976a5d8004 0x0651ff52ed4bb000 0x000ff807e01f8001 0x0001ff00fc03f000

def z395 : W := mkw 0x077b9feebfbaffeb 0xa0ef73fdd7f75ffd 0xffffffffffffffff 0xffffffffffffffff

def z396 : W := mkw 0x08b45c597165d19a 0x61168b8b2e2cba33 0x01f0787861e18198 0x803e0f0f0c3c3033

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x260007801e001e00 0x44c000f003c003c0

def z398 : W := mkw 0x07ce601140000000 0x00f9cc0228000000 0xc7fff87fe0000003 0xf8ffff0ffc000000

def z399 : W := mkw 0x0000000800205583 0x0000000100040ab0 0x0800000000007f80 0x0100000000000ff0

def z400 : W := mkw 0x08000019c0226152 0x4100000338044c2a 0x4000003b80006000 0x0800000770000c00

def z401 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x067ff8001e1f8001 0x40cfff0003c3f000

def z402 : W := mkw 0x08200579c02275d3 0x410400af38044eba 0x680007ffe0007ffa 0x0d0000fffc000fff

def z403 : W := mkw 0x17ce600006cd0004 0x02f9cc0000d9a000 0x97fff80006ee0001 0xf2ffff0000ddc000

def z404 : W := mkw 0x0884401140450010 0x411088022808a002 0x0000400060018018 0x000008000c003003

def z405 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2073fe4079019998 0xc40e7fc80f203333

def z406 : W := mkw 0x37ff7ff775c58004 0x06ffeffeeeb8b000 0xe7ffffffe1e18003 0xfcfffffffc3c3000

def z407 : W := mkw 0x0000800008100000 0x0000100001020000 0x8003800018100005 0x5000700003020000

def z408 : W := mkw 0x055088001d908000 0x00aa110003b21000 0x97f3f8001ff18005 0xf2fe7f0003fe3000

def z409 : W := mkw 0x00219644281018a8 0xa00432c885020315 0xa8038644781019ff 0x550070c88f02033f

def z410 : W := mkw 0x17dee8081ffdd587 0x02fbdd0103ffbab0 0x9ffff8001fffff85 0xf3ffff0003fffff0

def z411 : W := mkw 0x0d70056895e775d3 0x41ae00ad12bceeba 0xfff007f81ffffffe 0xfffe00ff03ffffff

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000044600001fa 0x010000088c00003f

def z413 : W := mkw 0x17fffe443fdd98ac 0xa2ffffc887fbb315 0xb7fffe001fff9805 0xf6ffffc003fff300

def z414 : W := mkw 0x0560056000000000 0x00ac00ac00000000 0x2670078000000000 0x44ce00f000000000

def z415 : W := mkw 0x2001129760000000 0x04002252ec000000 0x00000007e0000000 0x00000000fc000000

def z416 : W := mkw 0x00119a04391098a8 0xa002334087221315 0x0803f804791199fd 0x01007f008f22333f

def z417 : W := mkw 0x0dc44139c4e76553 0x41b88827389cecaa 0x578c01bb86ee6600 0x2af1803770ddccc0

def z418 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xa9f0067819e01986 0xd53e00cf033c0330

def z419 : W := mkw 0x101088001fdd98ac 0xa202110003fbb315 0x180000001fff99fc 0x0300000003fff33f

def z420 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa873be0418101867 0x550e77c08302030c

def z421 : W := mkw 0x05f4457955a05583 0x00be88af2ab40ab0 0xfffc47ffffe07f87 0xffff88fffffc0ff0

def z422 : W := mkw 0x1094c8001fdd8004 0x0212990003fbb000 0x918c40001fff8005 0xb231880003fff000

def z423 : W := mkw 0x0021164420000000 0x000422c884000000 0x2073be0000000000 0x440e77c000000000

def z424 : W := mkw 0x0001028600000a20 0x80002050c0000144 0x2000078000001e00 0x040000f0000003c0

def z425 : W := mkw 0x0a8ec019ca7f6152 0x4151d803394fec2a 0xdf8fc07fffffe1ff 0xfbf1f80ffffffc3f

def z426 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x19f000781fe07f84 0x833e000f03fc0ff0

def z427 : W := mkw 0x27cf73b760000000 0x04f9ee76ec000000 0x478ff9bfe0000001 0x28f1ff37fc000000

def z428 : W := mkw 0x27effff768108828 0xa4fdfffeed021105 0xe7ffffffe011807b 0xfcfffffffc02300f

def z429 : W := mkw 0x00b5de55791098a8 0xa016bbcaaf221315 0xe9fffe7ff91199ff 0xfd3fffcfff22333f

def z430 : W := mkw 0x27ff77f775800000 0x04ffeefeeeb00000 0xf7ffffffffe00007 0xfefffffffffc0000

def z431 : W := mkw 0x00319e4c3db0ddab 0xa00633c987b61bb5 0xb873fe447ff1ffff 0xd70e7fc88ffe3fff

def z432 : W := mkw 0x2a8f729fe0676152 0x4551ee53fc0cec2a 0xd98ff87fe1ffe1ff 0xbb31ff0ffc3ffc3f

def z433 : W := mkw 0x001088081db0ddab 0xa002110103b61bb5 0x180000001ff1fffc 0x0300000003fe3fff

def z434 : W := mkw 0x08844011c0472050 0x411088023808e40a 0x880c4047e11f81ff 0x91018808fc23f03f

def z435 : W := mkw 0x25f47d7171009088 0x24be8fae2e201211 0x01f0787861018198 0x803e0f0f0c203033

def z436 : W := mkw 0x2fef77ffe0226152 0x45fdeefffc044c2a 0xefffffffe00061fb 0xfdfffffffc000c3f

def z437 : W := mkw 0x2fef77ff60654112 0x45fdeeffec0ca822 0xe7ffffffe1e1819b 0xfcfffffffc3c3033

def z438 : W := mkw 0x0030056811205583 0x000600ad02240ab0 0xe87007f819007f86 0xdd0e00ff03200ff0

def z439 : W := mkw 0x020a008202080200 0x0041401040410040 0x0600018006000600 0x00c0003000c000c0

def z440 : W := mkw 0x17dfea861fdd8a24 0x82fbfd50c3fbb144 0xb7ffff801fff9e05 0xf6fffff003fff3c0

def z441 : W := mkw 0x17dee8081ffdc106 0x02fbdd0103ffb820 0xdffff8781fffe187 0xfbffff0f03fffc30

def z442 : W := mkw 0x020b028600000000 0x00416050c0000000 0xfe0f87879e007e07 0x7fc1f0f0f3c00fc0

def z443 : W := mkw 0x17dffa043fdd882c 0xa2fbff4087fbb105 0x97fff8047fff807d 0xf2ffff008ffff00f

def z444 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x27f007f81fe01f80 0xc4fe00ff03fc03f0

def z445 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x28000644791199fe 0x050000c88f22333f

def z446 : W := mkw 0x17dfea041fdd8824 0x82fbfd4083fbb104 0xbffffe041fff9867 0xf7ffffc083fff30c

def z447 : W := mkw 0x0020144020001088 0x2004028804000211 0x0000004060000198 0x000000080c000033

def z448 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x67ffbfbb80000000 0x6cfff7f770000000

def z449 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x180c4007e1ffe1fd 0x03018800fc3ffc3f

def z450 : W := mkw 0x05719f643d909ca9 0xa0ae33ec87b21395 0xae73ffc47f119fff 0xd5ce7ff88fe233ff

def z451 : W := mkw 0x08b5de5d7975d9ba 0xe116bbcbaf2ebb37 0xa9f3fe7c79f199ff 0xd53e7fcf8f3e333f

def z452 : W := mkw 0x077a05ea97aa77c3 0x00ef40bd52f54ef8 0xfffc07fb9fee7f86 0xffff80ff73fdcff0

def z453 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0x0003800000000000 0x0000700000000000

def z454 : W := mkw 0x023b9e443b1898a8 0xa04773c887631315 0xbe7ffe447f1f99ff 0xf7cfffc88fe3f33f

def z455 : W := mkw 0x27ce61bb44a04503 0x04f9cc37689408a0 0x578c01bb86e06600 0x2af1803770dc0cc0

def z456 : W := mkw 0x35f47d7175c58004 0x06be8fae2eb8b000 0x01f0787861e18000 0x803e0f0f0c3c3000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000011181fc 0x010000000022303f

def z458 : W := mkw 0x128fea868a5faa64 0x8251fd50d14bf54c 0x000ff807801f8061 0x0001ff00f003f00c

def z459 : W := mkw 0x022b16c620000000 0x004562d8c4000000 0xe67fffc7e0000003 0xfccffff8fc000000

def z460 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd98c007b81ee6186 0xbb31800f703dcc30

def z461 : W := mkw 0x277bbfe6391098a8 0xa4ef77fcc7221315 0x2673bf8018001800 0x44ce77f003000300

def z462 : W := mkw 0x25e4757160000000 0x04bc8eae2c000000 0xc1fc787fe0000003 0xb83f8f0ffc000000

def z463 : W := mkw 0x023b9ec6391098a8 0xa04773d8c7221315 0xee7fffc7f91199ff 0xfdcffff8ff22333f

def z464 : W := mkw 0x12bffe443b5d98ac 0xa257ffc8876bb315 0xa87ffe44791f99ff 0xd50fffc88f23f33f

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800078000007e02 0x0d0000f000000fc0

def z466 : W := mkw 0x0550000015800000 0x00aa000002b00000 0xfff007801fe07e06 0xfffe00f003fc0fc0

def z467 : W := mkw 0x00119a0439108828 0xa002334087221105 0x8073f8047911807d 0xd00e7f008f22300f

def z468 : W := mkw 0x020a008200000000 0x0041401040000000 0x460c018380000000 0x28c1803070000000

def z469 : W := mkw 0x0084401140000000 0x0010880228000000 0x418c003b80000000 0x2831800770000000

def z470 : W := mkw 0x020b028600000000 0x00416050c0000000 0x2603878000000000 0x44c070f000000000

def z471 : W := mkw 0x0000000800204102 0x0000000100040820 0x4800007800006182 0x0900000f00000c30

def z472 : W := mkw 0x028fc297ca1a2a60 0x8051f852f943454c 0xff8fc7fffe1e7e67 0xfff1f8ffffc3cfcc

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000404460000003 0x900008088c000000

def z474 : W := mkw 0x0894c819d977f9fa 0xe11299033b2eff3f 0xd98c407ff9fff9ff 0xbb31880fff3fff3f

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c000780000003 0x38018000f0000000

def z476 : W := mkw 0x0a8fc297ca5f2a70 0xc151f852f94be54e 0xfe0fc787fe1ffe7f 0x7fc1f8f0ffc3ffcf

def z477 : W := mkw 0x0a0b829fca3a6b72 0xc1417053f9474d6e 0xfe0f87fffe1e7fff 0x7fc1f0ffffc3cfff

def z478 : W := mkw 0x0550000815a05583 0x00aa000102b40ab0 0x9ff000001fe07f84 0xf3fe000003fc0ff0

def z479 : W := mkw 0x0001828688122a60 0x80003050d102454c 0xe803878798107e67 0x5d0070f0f3020fcc

def z480 : W := mkw 0x0570056011001080 0x00ae00ac02200210 0xeff007f819001986 0xfdfe00ff03200330

def z481 : W := mkw 0x228f729760000000 0x0451ee52ec000000 0xe60fff87e0000003 0x7cc1fff0fc000000

def z482 : W := mkw 0x17ffefee9fffffe7 0x82fffdfdd3fffffc 0xffffffff9fffffe7 0xfffffffff3fffffc

def z483 : W := mkw 0x0000000080022040 0x0000000010004408 0x000c0007801e0061 0x00018000f003c00c

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xc180007800000002 0xb830000f00000000

def z485 : W := mkw 0x129ee8001fdd8004 0x0253dd0003fbb000 0x100ff8001fff8005 0x0201ff0003fff000

def z486 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xe60f8787801e0063 0x7cc1f0f0f003c00c

def z487 : W := mkw 0x00311e4431009088 0x200623c886201211 0xa073fe446101819b 0xd40e7fc88c203033

def z488 : W := mkw 0x0884401940654112 0x41108803280ca822 0xc18c407fe1e1819b 0xb831880ffc3c3033

def z489 : W := mkw 0x0031164431001080 0x000622c886200210 0xa873fe4479001987 0xd50e7fc88f200330

def z490 : W := mkw 0x0084401140000000 0x0010880228000000 0x0180407860000000 0x8030080f0c000000

def z491 : W := mkw 0x00319e44bb1abae8 0xa00633c89763575d 0xb873fe447f1fffff 0xd70e7fc88fe3ffff

def z492 : W := mkw 0x37fffff77f988004 0x06fffffeeff31000 0xe7fffffffe000003 0xfcffffffffc00000

def z493 : W := mkw 0x27fe65fb55a05583 0x04ffccbf6ab40ab0 0xfffc07fb9fe07f86 0xffff80ff73fc0ff0

def z494 : W := mkw 0x0010000815a05583 0x0002000102b40ab0 0x0000000001e00180 0x00000000003c0030

def z495 : W := mkw 0x00309c40391098a8 0xa006138807221315 0x08707840791199fc 0x810e0f080f22333f

def z496 : W := mkw 0x0800000080472050 0x410000001008e40a 0x00000000001f8078 0x000000000003f00f

def z497 : W := mkw 0x07ee656000000000 0x00fdccac00000000 0xe7fffff800000003 0xfcffffff00000000

def z498 : W := mkw 0x27ee75f360000000 0x04fdcebe6c000000 0x47fc79fbe0000000 0xa8ff8f3f7c000000

def z499 : W := mkw 0x000080008a1a2a60 0x800010001143454c 0xd80c00079e1e7e67 0x3b018000f3c3cfcc

def z500 : W := mkw 0x37ffffe63fdd8004 0x06fffffcc7fbb000 0xb7ffff801fff8005 0xf6fffff003fff000

def z501 : W := mkw 0x222b97f7ea1a2a60 0x844572fefd43454c 0xfe0f87fffe1e7e67 0x7fc1f0ffffc3cfcc

def z502 : W := mkw 0x128e6000024d0004 0x0251cc000049a000 0x000c0000000e0000 0x000180000001c000

def z503 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0xae0387841e101e67 0x55c070f083c203cc

def z504 : W := mkw 0x05719e443d9098a8 0xa0ae33c887b21315 0xbff3fe447ff199ff 0xf7fe7fc88ffe333f

def z505 : W := mkw 0x17fefc403fdd908c 0x22ffdf8807fbb211 0x97fff8407fff819d 0xf2ffff080ffff033

def z506 : W := mkw 0x1550280015808004 0x02aa050002b01000 0x0070380000000000 0x000e070000000000

def z507 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x6e7007f81e007f82 0x4dce00ff03c00ff0

def z508 : W := mkw 0x0570056895a275c3 0x00ae00ad12b44eb8 0xfffc07ff9ffe7fe7 0xffff80fff3ffcffc

def z509 : W := mkw 0x07cf628600000000 0x00f9ec50c0000000 0xe7ffff8780000003 0xfcfffff0f0000000

def z510 : W := mkw 0x101088009fdfaa64 0x8202110013fbf54c 0x180000001ffffe64 0x0300000003ffffcc

def z511 : W := mkw 0x27ef77f7e20a2240 0x04fdeefefc414448 0xf7ffffffe60e6603 0xfefffffffcc1ccc0

def z512 : W := mkw 0x08b44459d16771d2 0x4116888b3a2cee3a 0xf9fc467ff9fff9ff 0xff3f88cfff3fff3f

def z513 : W := mkw 0x17feec401fdd9084 0x02ffdd8803fbb210 0xbffffe401fff9987 0xf7ffffc803fff330

def z514 : W := mkw 0x2ffffffff977f9fa 0xe5ffffffff2eff3f 0xfffffffff9fff9ff 0xffffffffff3fff3f

def z515 : W := mkw 0x0030044815a05583 0x0006008902b40ab0 0xb87006401fe07f86 0xd70e00c803fc0ff0

def z516 : W := mkw 0x00301c4031009088 0x2006038806201211 0xa8707e407901999e 0xd50e0fc80f203333

def z517 : W := mkw 0x05d4400015c50000 0x00ba880002b8a000 0x97fc40001fff8005 0xf2ff880003fff000

def z518 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x480c407fe01fe1fb 0x0901880ffc03fc3f

def z519 : W := mkw 0x0571176c35a05dab 0xa0ae22ed86b40bb5 0xfff007fc7fe07ffe 0xfffe00ff8ffc0fff

def z520 : W := mkw 0x001080089fba7fe3 0x8002100113f74ffc 0x180000001ffe7fe4 0x0300000003ffcffc

def z521 : W := mkw 0x020b028600000000 0x00416050c0000000 0x000f800780000001 0x0001f000f0000000

def z522 : W := mkw 0x08a5565de06779fa 0xe114aacbbc0cef3f 0xf98c467fe1fff9ff 0xbf3188cffc3fff3f

def z523 : W := mkw 0x08844011c0472050 0x411088023808e40a 0x000c0003800e0000 0x000180007001c000

def z524 : W := mkw 0x0001020400000820 0x8000204080000104 0x2800060400001862 0x050000c08000030c

def z525 : W := mkw 0x023b9ec6bb1abae8 0xa04773d8d763575d 0xfe7fbf879e1e7e67 0x7fcff7f0f3c3cfcc

def z526 : W := mkw 0x2fce61bbc0676152 0x45f9cc37780cec2a 0xdf8c41ffe1ffe1ff 0xbbf1883ffc3ffc3f

def z527 : W := mkw 0x1dd46819d5e7e156 0x43ba8d033abcfc2a 0xd9fc787fe1ffe1ff 0xbb3f8f0ffc3ffc3f

def z528 : W := mkw 0x00118a04191098a8 0xa002314083221315 0xa8038604191199ff 0x550070c08322333f

def z529 : W := mkw 0x0000000000450000 0x000000000008a000 0x1000000001ff8004 0x02000000003ff000

def z530 : W := mkw 0x00000000000018a8 0xa000000000000315 0x08000000000019f8 0x010000000000033f

def z531 : W := mkw 0x0010000815a05583 0x0002000102b40ab0 0xfe0007801fe07f86 0x7fc000f003fc0ff0

def z532 : W := mkw 0x377bbfe63f988004 0x06ef77fcc7f31000 0x2673bf801e000000 0x44ce77f003c00000

def z533 : W := mkw 0x0550000815a04102 0x00aa000102b40820 0xdff000781fe06186 0xfbfe000f03fc0c30

def z534 : W := mkw 0x27eff7f768100820 0x84fdfefeed020104 0xeffffffff8101867 0xfdffffffff02030c

def z535 : W := mkw 0x0df5df7dfdf7fdfb 0xe1bebbefbfbeffbf 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0x00319e44b912b8e8 0xa00633c89722571d 0xf87ffe47f91ff9ff 0xff0fffc8ff23ff3f

def z537 : W := mkw 0x023b9ec63b189aa8 0xa04773d8c7631355 0x2673bf801e001e00 0x44ce77f003c003c0

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x960000001e000004 0x72c0000003c00000

def z539 : W := mkw 0x00019a0428108828 0xa000334085021105 0xa803fe047811987f 0x55007fc08f02330f

def z540 : W := mkw 0x05f4456815e55583 0x00be88ad02bcaab0 0xfffc47f81fffff87 0xffff88ff03fffff0

def z541 : W := mkw 0x020a0082820a2240 0x0041401050414448 0x000c0003800e0000 0x000180007001c000

def z542 : W := mkw 0x0000880008108000 0x0000110001021000 0x0003f80000118001 0x00007f0000023000

def z543 : W := mkw 0x00219e44281098a8 0xa00433c885021315 0x2803fe44601199fb 0x05007fc88c02333f

def z544 : W := mkw 0x174a200006880004 0x02e9440000d10000 0x0600000006000000 0x00c0000000c00000

def z545 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xff8c47ffffffffff 0xfff188ffffffffff

def z546 : W := mkw 0x074a01aa86aa6743 0x00e9403550d54ce8 0x578c01bb86ee6600 0x2af1803770ddccc0

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000400001118005 0x9000080000223000

def z548 : W := mkw 0x020b828608100820 0x80417050c1020104 0xee0f878798101867 0x7dc1f0f0f302030c

def z549 : W := mkw 0x00211644200018a8 0xa00422c884000315 0xa8004644611199ff 0x950008c88c22333f

def z550 : W := mkw 0x177aad681fb8d587 0x02ef55ad03f71ab0 0xfff3bff81fe07f86 0xfffe77ff03fc0ff0

def z551 : W := mkw 0x28a557ffe0676152 0x4514aafffc0cec2a 0xf98c47ffe1ffe1ff 0xbf3188fffc3ffc3f

def z552 : W := mkw 0x121a88001fdd8004 0x0243510003fbb000 0x960f80001fff8005 0x72c1f00003fff000

def z553 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0xfe0387801e007e06 0x7fc070f003c00fc0

def z554 : W := mkw 0x0a8e409bc26f6352 0x4151c813784dec6a 0xdf8c41ffe7ffe7ff 0xbbf1883ffcfffcff

def z555 : W := mkw 0x05719f643d909ca9 0xa0ae33ec87b21395 0x2673bf801e001e00 0x44ce77f003c003c0

def z556 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x4980407fe1e1e1fa 0x8930080ffc3c3c3f

def z557 : W := mkw 0x077b87e69f9a3ee1 0x80ef70fcd3f347dc 0xfe7f87879e1e7e67 0x7fcff0f0f3c3cfcc

def z558 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x518c407be1efe198 0xaa31880f7c3dfc33

def z559 : W := mkw 0x020a80008a1a2a60 0x804150001143454c 0x9e0f80001e1e7e65 0x73c1f00003c3cfcc

def z560 : W := mkw 0x25e577f760000000 0x04bcaefeec000000 0x61f07fffe0000002 0x8c3e0ffffc000000

def z561 : W := mkw 0x0dd44019d5e76152 0x41ba88033abcec2a 0xdffc407fffffe1ff 0xfbff880ffffffc3f

def z562 : W := mkw 0x0001820408100820 0x8000304081020104 0xa803c644791199ff 0xd50078c88f22333f

def z563 : W := mkw 0x2a8f7297e0472050 0x4551ee52fc08e40a 0x000ff807e01f8079 0x0001ff00fc03f00f

def z564 : W := mkw 0x0001120420000000 0x0000224084000000 0x0003f80460000001 0x00007f008c000000

def z565 : W := mkw 0x101088001f988004 0x0202110003f31000 0x000000001e000000 0x0000000003c00000

def z566 : W := mkw 0x00b5de44395598a8 0xa016bbc8872ab315 0xb9fffe4479ff99ff 0xf73fffc88f3ff33f

def z567 : W := mkw 0x0a8e409bc26f6352 0x4151c813784dec6a 0x578c01bb86ee6600 0x2af1803770ddccc0

def z568 : W := mkw 0x2feff7ffea7f6b72 0xc5fdfefffd4fed6e 0xffffffffffffffff 0xffffffffffffffff

def z569 : W := mkw 0x00108800191098a8 0xa002110003221315 0x8873f800191199fd 0xd10e7f000322333f

def z570 : W := mkw 0x00211644200018a8 0xa00422c884000315 0x2000060000001800 0x040000c000000300

def z571 : W := mkw 0x175aa8001f988004 0x02eb550003f31000 0x967fb8001e1e0005 0x72cff70003c3c000

def z572 : W := mkw 0x0010080011009088 0x2002010002201211 0x0000000001018198 0x0000000000203033

def z573 : W := mkw 0x0010000011001080 0x0002000002200210 0x0800000019001984 0x0100000003200330

def z574 : W := mkw 0x022b87ee8a3a7fe3 0x804570fdd1474ffc 0xfe0f87ff9e1e7fe7 0x7fc1f0fff3c3cffc

def z575 : W := mkw 0x0084400080472040 0x001088001008e408 0xd98c400781ffe067 0xbb318800f03ffc0c

def z576 : W := mkw 0x07fffe44391098a8 0xa0ffffc887221315 0xaffffe44791199ff 0xf5ffffc88f22333f

def z577 : W := mkw 0x175baa861f988a24 0x82eb7550c3f31144 0x2673bf801e001e00 0x44ce77f003c003c0

def z578 : W := mkw 0x0000180020008008 0x2000030004001001 0x0000780060018018 0x00000f000c003003

def z579 : W := mkw 0x17fffe443fdd8004 0x02ffffc887fbb000 0xb7fffe447fff8007 0xf6ffffc88ffff000

def z580 : W := mkw 0x0001028680022a60 0x80002050d000454c 0x0000000780000060 0x00000000f000000c

def z581 : W := mkw 0x15c4600004c50004 0x02b88c000098a000 0x0180000000e00000 0x00300000001c0000

def z582 : W := mkw 0x0884401940654112 0x41108803280ca822 0x8980407c61f181ff 0x9130080f8c3e303f

def z583 : W := mkw 0x00301c4031009088 0x2006038806201211 0x88707844611181ff 0x910e0f088c22303f

def z584 : W := mkw 0x0de44579c0676152 0x41bc88af380cec2a 0xfffc47ffe1ffe1ff 0xffff88fffc3ffc3f

def z585 : W := mkw 0x277b37e635801481 0x04ef66fcc6b00290 0x2673bf801e001e00 0x44ce77f003c003c0

def z586 : W := mkw 0x0001820408100820 0x8000304081020104 0x2003860018001800 0x440070c003000300

def z587 : W := mkw 0x17cee8000edd8004 0x02f9dd0001dbb000 0x178ff80006ff8001 0x22f1ff0000dff000

def z588 : W := mkw 0x0884401940654112 0x41108803280ca822 0x918c407861ff819d 0xb231880f0c3ff033

def z589 : W := mkw 0x15d4e8001fdd8004 0x02ba9d0003fbb000 0x11f078001fff8004 0x823e0f0003fff000

def z590 : W := mkw 0x001088009b1abae8 0xa00211001363575d 0x180000001f1ffffc 0x0300000003e3ffff

def z591 : W := mkw 0x00318644191018a0 0x800630c883220314 0xa8738644191019e7 0xd50e70c88322033c

def z592 : W := mkw 0x000080000a180000 0x0000100001430000 0x100000001e1e0004 0x0200000003c3c000

def z593 : W := mkw 0x37ce61b346cd0004 0x06f9cc3668d9a000 0x578c01bb86ee0000 0x2af1803770ddc000

def z594 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xa80f8607981e1867 0x5501f0c0f303c30c

def z595 : W := mkw 0x2020157160000000 0x040402ae2c000000 0x0000007860000000 0x0000000f0c000000

def z596 : W := mkw 0x028f429740000000 0x0051e852e8000000 0xe78fc7ffe0000003 0xfcf1f8fffc000000

def z597 : W := mkw 0x0021964428100820 0x800432c885020104 0xa873fe4478101867 0xd50e7fc88f02030c

def z598 : W := mkw 0x00219e4428108828 0xa00433c885021105 0xa073fe446011807b 0xd40e7fc88c02300f

def z599 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x560f8187861e6661 0x2ac1f030f0c3cccc

def z600 : W := mkw 0x0084401140000000 0x0010880228000000 0xc98c407fe11181ff 0xb931880ffc22303f

def z601 : W := mkw 0x020a80008a1a2040 0x0041500011434408 0xde0f80079e1e6067 0x7bc1f000f3c3cc0c

def z602 : W := mkw 0x0021164420000000 0x000422c884000000 0x2000064460000002 0x040000c88c000000

def z603 : W := mkw 0x1894c819dfffe156 0x431299033bfffc2a 0xd98c407fffffe1ff 0xbb31880ffffffc3f

def z604 : W := mkw 0x076b07e600000000 0x00ed60fcc0000000 0xe7ff87ff80000003 0xfcfff0fff0000000

def z605 : W := mkw 0x17de680017cd8004 0x02fbcd0002f9b000 0x17fc780007ef8000 0xa2ff8f0000fdf000

def z606 : W := mkw 0x00308c40191098a8 0xa006118803221315 0xa8700640191199fe 0xd50e00c80322333f

def z607 : W := mkw 0x08319e4cb977f9fa 0xe10633c9972eff3f 0xb873fe4479fff9ff 0xd70e7fc88f3fff3f

def z608 : W := mkw 0x08b45c59f167f1da 0x61168b8b3e2cfe3b 0xd9fc787fe1ffe1ff 0xbb3f8f0ffc3ffc3f

def z609 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0xae7007c01f001f86 0xd5ce00f803e003f0

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0xd800000000006006 0x3b00000000000c00

def z611 : W := mkw 0x0001028680022a60 0x80002050d000454c 0xfe0007879e007e66 0x7fc000f0f3c00fcc

def z612 : W := mkw 0x020b82860a180a20 0x80417050c1430144 0xe60f87879e001e03 0x7cc1f0f0f3c003c0

def z613 : W := mkw 0x00301c4031009088 0x2006038806201211 0x0070380000000000 0x000e070000000000

def z614 : W := mkw 0x129ee8001b5d8004 0x0253dd00036bb000 0x807ff800191f8005 0xd00fff000323f000

def z615 : W := mkw 0x08844011c0472050 0x411088023808e40a 0xd80c4007e01fe07f 0x3b018800fc03fc0f

def z616 : W := mkw 0x0560056000000000 0x00ac00ac00000000 0x01f0007800000000 0x803e000f00000000

def z617 : W := mkw 0x057085689fba7fe3 0x80ae10ad13f74ffc 0xfff007f81ffe7fe6 0xfffe00ff03ffcffc

def z618 : W := mkw 0x07cfe2868a1a2a60 0x80f9fc50d143454c 0xffffff879e1e7e67 0xfffffff0f3c3cfcc

def z619 : W := mkw 0x0884400880676152 0x41108801100cec2a 0x998c400001ffe1fd 0xb3318800003ffc3f

def z620 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0x0180003800e00000 0x00300007001c0000

def z621 : W := mkw 0x0821165de02279fa 0xe10422cbbc044f3f 0x6800067fe00079fa 0x0d0000cffc000f3f

def z622 : W := mkw 0x10319e443fdd98ac 0xa20633c887fbb315 0xb873fe447fff99ff 0xd70e7fc88ffff33f

def z623 : W := mkw 0x0084400000450000 0x001088000008a000 0x118c000000ee0000 0x22318000001dc000

def z624 : W := mkw 0x1084680000458004 0x02108d000008b000 0x0000780000018000 0x00000f0000003000

def z625 : W := mkw 0x25f4757975a05583 0x04be8eaf2eb40ab0 0xfff07ff87fe07f86 0xfffe0fff0ffc0ff0

def z626 : W := mkw 0x0000000080022040 0x0000000010004408 0x18000000001e6064 0x030000000003cc0c

def z627 : W := mkw 0x121b8a869fdfaa64 0x82437150d3fbf54c 0xfe0f87879ffffe67 0x7fc1f0f0f3ffffcc

def z628 : W := mkw 0x27cf729760000000 0x04f9ee52ec000000 0x87fff807e0000001 0xf0ffff00fc000000

def z629 : W := mkw 0x020b9a86aa1aaa68 0xa0417350d543554d 0x000ff807e01f8079 0x0001ff00fc03f00f

def z630 : W := mkw 0x0800000800654112 0x41000001000ca822 0x0000000001e18198 0x00000000003c3033

def z631 : W := mkw 0x0540000004800000 0x00a8000000900000 0x1780000006e00000 0x22f0000000dc0000

def z632 : W := mkw 0x0010880019108000 0x0002110003221000 0x0073b80018000000 0x400e770003000000

def z633 : W := mkw 0x0a8fc29fca7f6b72 0xc151f853f94fed6e 0xff8f87bf9efe7e67 0x7ff1f0f7f3dfcfcc

def z634 : W := mkw 0x07de600015800000 0x00fbcc0002b00000 0x97fff8001fe00005 0xf2ffff0003fc0000

def z635 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873be44780019fa 0x450e77c88f00033f

def z636 : W := mkw 0x0010000011000000 0x0002000002200000 0x8070000019000004 0xd00e000003200000

def z637 : W := mkw 0x27eff7f7ea1a2a60 0x84fdfefefd43454c 0xe7ffffffe01e0063 0xfcfffffffc03c00c

def z638 : W := mkw 0x15f46d6815e5d587 0x02be8dad02bcbab0 0xfff07ff81fe1ff86 0xfffe0fff03fc3ff0

def z639 : W := mkw 0x15f47c4035c5908c 0x22be8f8806b8b211 0x01f0784061e18198 0x803e0f080c3c3033

def z640 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0xdf8001f807e06786 0xbbf0003f00fc0cf0

def z641 : W := mkw 0x155088001fdd8004 0x02aa110003fbb000 0x97f000001fff8004 0xf2fe000003fff000

def z642 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x1980407861ffe1fc 0x8330080f0c3ffc3f

def z643 : W := mkw 0x27cf63b740000000 0x04f9ec76e8000000 0xe78f87bf80000003 0x7cf1f0f7f0000000

def z644 : W := mkw 0x0550012815a05583 0x00aa002502b40ab0 0x5f8001b81fe07f84 0x2bf0003703fc0ff0

def z645 : W := mkw 0x1000000006cd0004 0x0200000000d9a000 0x1000000006ee0000 0x0200000000ddc000

def z646 : W := mkw 0x1fdee8195ffdc116 0x43fbdd032bffb822 0x97fff8787fff819d 0xf2ffff0f0ffff033

def z647 : W := mkw 0x101088081ffdd587 0x0202110103ffbab0 0x180000001fffff84 0x0300000003fffff0

def z648 : W := mkw 0x0020144020000000 0x0004028804000000 0x0070784060000000 0x800e0f080c000000

def z649 : W := mkw 0x00309c4039109088 0x2006138807221211 0x8073f8407911819d 0xd00e7f080f223033

def z650 : W := mkw 0x00319e4c3930d9aa 0xa00633c987261b35 0xf9f3fe7c79f1f9ff 0xff3e7fcf8f3e3f3f

def z651 : W := mkw 0x2de4757960654112 0x45bc8eaf2c0ca822 0x01f0787861e18198 0x803e0f0f0c3c3033

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800004001000186 0x9100000800200030

def z653 : W := mkw 0x0a8fc29fca7f6b72 0xc151f853f94fed6e 0xd98fc07fe1ffe1ff 0xbb31f80ffc3ffc3f

def z654 : W := mkw 0x0810000895e775d3 0x4102000112bceeba 0x180000001ffffffc 0x0300000003ffffff

def z655 : W := mkw 0x07fe656815a05583 0x00ffccad02b40ab0 0xfffffff81fe07f87 0xffffffff03fc0ff0

def z656 : W := mkw 0x0030044811205182 0x0006008902240a30 0xf9f0067819e07986 0xff3e00cf033c0f30

def z657 : W := mkw 0x177aad601f989485 0x02ef55ac03f31290 0x2673bf801e001e00 0x44ce77f003c003c0

def z658 : W := mkw 0x177bbe443f9898ac 0xa2ef77c887f31315 0xae73fe447f1199ff 0xd5ce7fc88fe2333f

def z659 : W := mkw 0x0001820408100820 0x8000304081020104 0x0003800400100061 0x000070008002000c

def z660 : W := mkw 0x0021176c20205dab 0xa00422ed84040bb5 0x680007fc60007ffa 0x0d0000ff8c000fff

def z661 : W := mkw 0x0000012800204503 0x00000025000408a0 0x400001b800006600 0x0800003700000cc0

def z662 : W := mkw 0x37ffffff7ffdd587 0x06ffffffefffbab0 0xffffffffffffff87 0xfffffffffffffff0

def z663 : W := mkw 0x27ee757160000000 0x04fdceae2c000000 0x87fff87860000001 0xf0ffff0f0c000000

def z664 : W := mkw 0x0560056800204102 0x00ac00ad00040820 0xfff007f801e06186 0xfffe00ff003c0c30

def z665 : W := mkw 0x27ef77f7e0022a60 0x84fdeefefc00454c 0xefffffffe0007e63 0xfdfffffffc000fcc

def z666 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x598c003b81ffe1fc 0x2b318007703ffc3f

def z667 : W := mkw 0x0560056804a04503 0x00ac00ad009408a0 0xf7f007f806e06602 0xfefe00ff00dc0cc0

def z668 : W := mkw 0x07cee0000a180000 0x00f9dc0001430000 0x97fff8001e1e0005 0xf2ffff0003c3c000

def z669 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2073fe0478119879 0x440e7fc08f02330f

def z670 : W := mkw 0x023b86c69b1a3ae0 0x804770d8d363475c 0xfe7f87c79f1e7fe7 0xffcff0f8f3e3cffc

def z671 : W := mkw 0x2fff77fff5e775d3 0x45ffeefffebceeba 0xffffffffffffffff 0xffffffffffffffff

def z672 : W := mkw 0x0084401140450000 0x001088022808a000 0xd18c407fe1ff8007 0xba31880ffc3ff000

def z673 : W := mkw 0x0001020400000000 0x0000204080000000 0xa003860400000003 0x540070c080000000

def z674 : W := mkw 0x0884401940654112 0x41108803280ca822 0x0180003800e00000 0x00300007001c0000

def z675 : W := mkw 0x177bbe443f9898ac 0xa2ef77c887f31315 0x2673be001e001800 0x44ce77c003c00300

def z676 : W := mkw 0x1ffeed79dffff5d7 0x43ffddaf3bfffeba 0xffffffffffffffff 0xffffffffffffffff

def z677 : W := mkw 0x0540000000000000 0x00a8000000000000 0x87f0000000000000 0xf0fe000000000000

def z678 : W := mkw 0x0000001140000000 0x0000000228000000 0x4000007fe0000002 0x0800000ffc000000

def z679 : W := mkw 0x00319ec6b912bae8 0xa00633d8d722575d 0xe873ffc7f911ffff 0xdd0e7ff8ff223fff

def z680 : W := mkw 0x0570056015800000 0x00ae00ac02b00000 0xf7f007f81fe00006 0xfefe00ff03fc0000

def z681 : W := mkw 0x128ee8000a5d8004 0x0251dd00014bb000 0x960ff8001e1f8005 0x72c1ff0003c3f000

def z682 : W := mkw 0x228ffa9768108828 0xa451ff52ed021105 0x000ff807e0118079 0x0001ff00fc02300f

def z683 : W := mkw 0x0570056015801481 0x00ae00ac02b00290 0xfe7007801e007e06 0x7fce00f003c00fc0

def z684 : W := mkw 0x08319e5df932f9fa 0xe10633cbbf265f3f 0xe873fe7ff911f9ff 0xdd0e7fcfff223f3f

def z685 : W := mkw 0x0abfdedffb7ffbfa 0xe157fbdbff6fff7f 0xffffffffffffffff 0xffffffffffffffff

def z686 : W := mkw 0x002116c6a0023ae8 0xa00422d8d400475d 0x680007c7e0007ffa 0x0d0000f8fc000fff

def z687 : W := mkw 0x0000008280022240 0x0000001050004448 0x4000018380006600 0x0800003070000cc0

def z688 : W := mkw 0x1fce6019c6ef6156 0x43f9cc0338ddec2a 0xdf8c407fe7ffe1ff 0xbbf1880ffcfffc3f

def z689 : W := mkw 0x17dee8829fdfa244 0x02fbdd1053fbf448 0xd7fff9839fffe605 0xfaffff3073fffcc0

def z690 : W := mkw 0x0800000880676152 0x41000001100cec2a 0xd80c000781ffe1ff 0x3b018000f03ffc3f

def z691 : W := mkw 0x175aa8001f988004 0x02eb550003f31000 0x97f3b8001fe00004 0xf2fe770003fc0000

def z692 : W := mkw 0x000182048a1a2a60 0x800030409143454c 0xb80386041e1e7e67 0x570070c083c3cfcc

def z693 : W := mkw 0x17feed601fdd9485 0x02ffddac03fbb290 0xb7ffff801fff9e05 0xf6fffff003fff3c0

def z694 : W := mkw 0x228ff297ea1a2a60 0x8451fe52fd43454c 0xfe0fff87fe1e7e67 0x7fc1fff0ffc3cfcc

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800060018001806 0x550000c003000300

def z696 : W := mkw 0x15d4e8001dd58004 0x02ba9d0003bab000 0x81f3f80019f18005 0xd03e7f00033e3000

def z697 : W := mkw 0x25f4757975a05583 0x04be8eaf2eb40ab0 0x01f0787861e00180 0x803e0f0f0c3c0030

def z698 : W := mkw 0x0020044000001080 0x0004008800000210 0x2800064000001982 0x050000c800000330

def z699 : W := mkw 0x1a8ee811ca5fa054 0x4351dd02394bf40a 0x000ff807e01f8079 0x0001ff00fc03f00f

def z700 : W := mkw 0x22af76d760000000 0x0455eedaec000000 0xa07ffe47e0000003 0xd40fffc8fc000000

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z702 : W := mkw 0x27fffff7791098a8 0xa4fffffeef221315 0xe7fffffff8001803 0xfcffffffff000300

def z703 : W := mkw 0x27cfe3b7ca1a2a60 0x84f9fc76f943454c 0xff8f87bf9e1e7e67 0x7ff1f0f7f3c3cfcc

def z704 : W := mkw 0x17dee8009fdfa044 0x02fbdd0013fbf408 0xdffff8079fffe067 0xfbffff00f3fffc0c

def z705 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa073fe4478001803 0xd40e7fc88f000300

def z706 : W := mkw 0x0a0b828e8a7f6b72 0xc1417051d14fed6e 0xfe0f87879fffffff 0x7fc1f0f0f3ffffff

def z707 : W := mkw 0x25e577f760000000 0x04bcaefeec000000 0xe1f3ffffe0000003 0xdc3e7ffffc000000

def z708 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffbffb80000002 0xfcfff7ff70000000

def z709 : W := mkw 0x17dee8001fdd98ac 0xa2fbdd0003fbb315 0x97fff8001fff9805 0xf2ffff0003fff300

def z710 : W := mkw 0x27ce61b340000000 0x04f9cc3668000000 0x47ffb9bb80000000 0x68fff73770000000

def z711 : W := mkw 0x075a88001f988000 0x00eb510003f31000 0x97fff8001fff8005 0xf2ffff0003fff000

def z712 : W := mkw 0x05419b2c2cb0cd2b 0xa0a83365859619a5 0x5783f9bc66f1e679 0x2af07f378cde3ccf

def z713 : W := mkw 0x220bb286aa1a2a60 0x84417650d543454c 0xfe0fbf879e1e7e67 0x7fc1f7f0f3c3cfcc

def z714 : W := mkw 0x020a0082820a2240 0x0041401050414448 0x760c07839e0e7e00 0x6ec180f073c1cfc0

def z715 : W := mkw 0x082116dfe0227bfa 0xe10422dbfc044f7f 0x680007ffe0007ffa 0x0d0000fffc000fff

def z716 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xf7fffffffe000007 0xfeffffffffc00000

def z717 : W := mkw 0x081088089932f9fa 0xe102110113265f3f 0x080000001911f9fc 0x0100000003223f3f

def z718 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x898c407fe1ff81ff 0x9131880ffc3ff03f

def z719 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x47fff9ffe0000001 0xa8ffff3ffc000000

def z720 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17ffb8001fff8004 0x62fff70003fff000

def z721 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x760f87879e1e7e61 0x6ec1f0f0f3c3cfcc

def z722 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff047fc7fe07f87 0xfffe08ff8ffc0ff0

def z723 : W := mkw 0x37dee9b35fdd8004 0x06fbdd366bfbb000 0xd7fff9ffffff8007 0xfaffff3ffffff000

def z724 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xefffffffe0007e03 0xfdfffffffc000fc0

def z725 : W := mkw 0x00308c4019109080 0x0006118803221210 0xa873fe44791199ff 0xd50e7fc88f22333f

def z726 : W := mkw 0x0a8fc29f4a7d4b32 0xc151f853e94fa966 0x2783c7f87fe19f98 0xc4f078ff0ffc33f3

def z727 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2073fe44791199f9 0xc40e7fc88f22333f

def z728 : W := mkw 0x0df44571d5c734d1 0x41be88ae3ab8e69a 0x267c4787fe1f9e79 0x44cf88f0ffc3f3cf

def z729 : W := mkw 0x12aeed680a7dd587 0x0255ddad014fbab0 0x680ffff8001fff83 0x0d01ffff0003fff0

def z730 : W := mkw 0x25e4f571ea1a2a60 0x84bc9eae3d43454c 0x19f078787e1e7e64 0x833e0f0f0fc3cfcc

def z731 : W := mkw 0x17dee8001fdd908c 0x22fbdd0003fbb211 0x97fff8001fff819d 0xf2ffff0003fff033

def z732 : W := mkw 0x256117f760000000 0x04ac22feec000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z733 : W := mkw 0x37ef77f766880004 0x06fdeefeecd10000 0xe7ffffffe6000003 0xfcfffffffcc00000

def z734 : W := mkw 0x17dee8001fdd8a24 0x82fbdd0003fbb144 0x97fff8001fff9e05 0xf2ffff0003fff3c0

def z735 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xe873ffc47911ffff 0xdd0e7ff88f223fff

def z736 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x167ff8001fff8005 0x42cfff0003fff000

def z737 : W := mkw 0x0094c811591098a8 0xa01299022b221315 0xc98c407ff91199ff 0xb931880fff22333f

def z738 : W := mkw 0x20319fe6391098a8 0xa40633fcc7221315 0xa873ffc4791199ff 0xd50e7ff88f22333f

def z739 : W := mkw 0x00108800191098a8 0xa002110003221315 0x8873f844791199ff 0xd10e7f088f22333f

def z740 : W := mkw 0x1f5aa819dfbae156 0x43eb55033bf75c2a 0x4e73b87ffe0061fa 0x49ce770fffc00c3f

def z741 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xf7ffff801fff8007 0xfefffff003fff000

def z742 : W := mkw 0x00319e443b189aa8 0xa00633c887631355 0xa873fe447f119fff 0xd50e7fc88fe233ff

def z743 : W := mkw 0x15d56a8695c7aa64 0x82baad50d2b8f54c 0x69f07f8781e1fe62 0x8d3e0ff0f03c3fcc

def z744 : W := mkw 0x020b9286aa1a2a60 0x80417250d543454c 0xfe0fff87fe1e7e67 0x7fc1fff0ffc3cfcc

def z745 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff007f81ff1fffe 0xfffe00ff03fe3fff

def z746 : W := mkw 0x08108819d932e152 0x410211033b265c2a 0xc873f87ff911e1ff 0xd90e7f0fff223c3f

def z747 : W := mkw 0x27dee9b3591098a8 0xa4fbdd366b221315 0x4f8c01bb991199fc 0x29f180377322333f

def z748 : W := mkw 0x00319e443d9098a8 0xa00633c887b21315 0xb873fe447ff199ff 0xd70e7fc88ffe333f

def z749 : W := mkw 0x00219e44281098a8 0xa00433c885021315 0xa873fe44601199fb 0xd50e7fc88c02333f

def z750 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0fc7c7fe1e7e67 0xffc1f8f8ffc3cfcc

def z751 : W := mkw 0x1a8fea97ca5faa74 0xc351fd52f94bf54e 0x000ff807e01f8079 0x0001ff00fc03f00f

def z752 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xa1fffe7fe0000003 0xd43fffcffc000000

def z753 : W := mkw 0x17ce600006cd0004 0x02f9cc0000d9a000 0x97fff80007ff8005 0xf2ffff0000fff000

def z754 : W := mkw 0x020a80008a1a2040 0x0041500011434408 0xfe0f87879e1e7e67 0x7fc1f0f0f3c3cfcc

def z755 : W := mkw 0x27ef77f760000828 0xa4fdeefeec000105 0xe7ffffffe000007b 0xfcfffffffc00000f

def z756 : W := mkw 0x276b37f760000000 0x04ed66feec000000 0xe67fbfffe0000003 0x7ccff7fffc000000

def z757 : W := mkw 0x17ef764426cd18ac 0xa2fdeec884d9a315 0x3f8c064466ee19fa 0x27f180c88cddc33f

def z758 : W := mkw 0x27cf73b760000000 0x04f9ee76ec000000 0xc7fff9bfe0000001 0xf8ffff37fc000000

def z759 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x498c407fe1ffe1fb 0x8931880ffc3ffc3f

def z760 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0f87879f1fffff 0x7fc1f0f0f3e3ffff

def z761 : W := mkw 0x0021964428100820 0x800432c885020104 0xa873fe44791199ff 0xd50e7fc88f22333f

def z762 : W := mkw 0x2f6b37eea0676152 0x45ed66fdd40cec2a 0x3e73bf8001ffe1fc 0x47ce77f0003ffc3f

def z763 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff3fff81fe07f87 0xfffe7fff03fc0ff0

def z764 : W := mkw 0x0821164ca0676152 0x410422c9940cec2a 0xb873fe4461ffe1ff 0xd70e7fc88c3ffc3f

def z765 : W := mkw 0x07cf629740000000 0x00f9ec52e8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z766 : W := mkw 0x276b37f760000000 0x04ed66feec000000 0x6673bfbb80000000 0x4cce77f770000000

def z767 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xbe73fe447f1199ff 0xf7ce7fc88fe2333f

def z768 : W := mkw 0x00319e443b1898a8 0xa00633c887631315 0xb873fe447f1f99ff 0xd70e7fc88fe3f33f

def z769 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x518c407fe1ffe1f9 0xaa31880ffc3ffc3f

def z770 : W := mkw 0x077b87ee9fba7fe3 0x80ef70fdd3f74ffc 0x01ff807f81fe01e1 0x803ff00ff03fc03c

def z771 : W := mkw 0x0fce6019c0676152 0x41f9cc03380cec2a 0x578c003b80ee6000 0x2af18007701dcc00

def z772 : W := mkw 0x0821177de0227dfb 0xe10422efbc044fbf 0x680007ffe0007ffa 0x0d0000fffc000fff

def z773 : W := mkw 0x30319ff77fdd8004 0x060633feeffbb000 0x700007ffffff8006 0x0e0000fffffff000

def z774 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xdf8c407fffffe1ff 0xfbf1880ffffffc3f

def z775 : W := mkw 0x0031164431001080 0x000622c886200210 0xa873fe44791199ff 0xd50e7fc88f22333f

def z776 : W := mkw 0x175aa8001fdd8004 0x02eb550003fbb000 0x97f3b8001fff8004 0xf2fe770003fff000

def z777 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0xff8007f81fe07f86 0xfff000ff03fc0ff0

def z778 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x198c407fe1ffe1fd 0x8331880ffc3ffc3f

def z779 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x87fff80001ff8001 0xf0ffff00003ff000

def z780 : W := mkw 0x1fce609bc6ef6356 0x43f9cc1378ddec6a 0x578c01bb86ee6600 0x2af1803770ddccc0

def z781 : W := mkw 0x0010000815a05583 0x0002000102b40ab0 0xff8007f81fe07f86 0xfff000ff03fc0ff0

def z782 : W := mkw 0x0fce6019c0226152 0x41f9cc0338044c2a 0xcffff87fe00061fb 0xf9ffff0ffc000c3f

def z783 : W := mkw 0x101088001fdd8004 0x0202110003fbb000 0x1073b8001fff8004 0x420e770003fff000

def z784 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x598c007fe1ffe1fe 0x2b31800ffc3ffc3f

def z785 : W := mkw 0x0021165560000000 0x000422caac000000 0xe073fe7fe0000003 0xdc0e7fcffc000000

def z786 : W := mkw 0x22af77f760000000 0x0455eefeec000000 0xe07fffffe0000003 0xdc0ffffffc000000

def z787 : W := mkw 0x020b028680022040 0x00416050d0004408 0xfe0f87879e1e7e67 0x7fc1f0f0f3c3cfcc

def z788 : W := mkw 0x0560056804a05583 0x00ac00ad00940ab0 0xff8007f81ee07f86 0x7ff000ff03dc0ff0

def z789 : W := mkw 0x020b9286aa1a2a68 0xa0417250d543454d 0xfe0f8787fe1e7e7f 0x7fc1f0f0ffc3cfcf

def z790 : W := mkw 0x0fce600880676152 0x41f9cc01100cec2a 0x9ffff80001ffe1fd 0xf3ffff00003ffc3f

def z791 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97ffb8001efe0005 0x72fff70003dfc000

def z792 : W := mkw 0x0550000815a04102 0x00aa000102b40820 0xfff007f81fe07f86 0xfffe00ff03fc0ff0

def z793 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0f87c7fe1e7fff 0x7fc1f0f8ffc3cfff

def z794 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x7e0f87839e1e7e64 0x6fc1f0f073c3cfcc

def z795 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x27ffffffe0000001 0xc4fffffffc000000

def z796 : W := mkw 0x1094c8001fdd8004 0x0212990003fbb000 0x91fff8001fff8005 0xf23fff0003fff000

def z797 : W := mkw 0x2fce61bbc26f6352 0x45f9cc37784dec6a 0x578c01bb86ee6600 0x2af1803770ddccc0

def z798 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97ffb8001fee0004 0xf2fff70003fdc000

def z799 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd9fff87fe1ffe1ff 0xfb3fff0ffc3ffc3f

def z800 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xf7ffffffe1e00007 0xfefffffffc3c0000

def z801 : W := mkw 0x27ef77f760000820 0x84fdeefeec000104 0xefffffffe0001863 0xfdfffffffc00030c

def z802 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x9ffff8001ffffe05 0xf3ffff0003ffffc0

def z803 : W := mkw 0x07cee0000a5d0000 0x00f9dc00014ba000 0x97fff8001fff8005 0xf2ffff0003fff000

def z804 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x3e0f87879e1e7e65 0x47c1f0f0f3c3cfcc

def z805 : W := mkw 0x27ef77f760001088 0x24fdeefeec000211 0xe7ffffffe000019b 0xfcfffffffc000033

def z806 : W := mkw 0x282117ffe0226152 0x450422fffc044c2a 0x600007ffe0006002 0x0c0000fffc000c00

def z807 : W := mkw 0x27ef77f760000a20 0x84fdeefeec000144 0xe7ffffffe0001e03 0xfcfffffffc0003c0

def z808 : W := mkw 0x181088089ffff5d7 0x4302110113fffeba 0x180000001ffffffc 0x0300000003ffffff

def z809 : W := mkw 0x27ef77f760450000 0x04fdeefeec08a000 0xe7ffffffe1e18003 0xfcfffffffc3c3000

def z810 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x67fffffbe0000000 0xecffffff7c000000

def z811 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0fc787fe1ffe7f 0x7fc1f8f0ffc3ffcf

def z812 : W := mkw 0x00319e443d909ca9 0xa00633c887b21395 0xa873fe447f119fff 0xd50e7fc88fe233ff

def z813 : W := mkw 0x229f729f75a05583 0x0453ee53eeb40ab0 0x180ff807ffe07f85 0x0301ff00fffc0ff0

def z814 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x3ff007f81fe07f84 0xc7fe00ff03fc0ff0

def z815 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff007fc1ff07fe7 0xfffe00ff83fe0ffc

def z816 : W := mkw 0x17cee8000a5d8004 0x02f9dd00014bb000 0x97fff80001ff8005 0xf2ffff00003ff000

def z817 : W := mkw 0x27ef77f760450000 0x04fdeefeec08a000 0xf7ffffffe0ee0003 0xfefffffffc1dc000

def z818 : W := mkw 0x17dee8001fdd98ac 0xa2fbdd0003fbb315 0x9ffff8447fff99ff 0xf3ffff088ffff33f

def z819 : W := mkw 0x17dee8001fdd882c 0xa2fbdd0003fbb105 0x97fff8001fff807d 0xf2ffff0003fff00f

def z820 : W := mkw 0x00211644200018a8 0xa00422c884000315 0xa873fe44611199ff 0xd50e7fc88c22333f

def z821 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xf98c467ff9fff9ff 0xff3188cfff3fff3f

def z822 : W := mkw 0x020a80828a1a2240 0x0041501051434448 0xfe0f87839e1e7e07 0x7fc1f0f073c3cfc0

def z823 : W := mkw 0x27ce61b340000000 0x04f9cc3668000000 0xc7fff9ffe0000003 0xf8ffff3ffc000000

def z824 : W := mkw 0x282117ffe0226b72 0xc50422fffc044d6e 0x680007ffe0007ffa 0x0d0000fffc000fff

def z825 : W := mkw 0x27ee757160000000 0x04fdceae2c000000 0xc7fff87fe0000003 0xf8ffff0ffc000000

def z826 : W := mkw 0x076b17e620000000 0x00ed62fcc4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z827 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x8873f844611181ff 0x910e7f088c22303f

def z828 : W := mkw 0x023a1cc2b30ab2c8 0x2047439856615659 0x567c79c3e70fe798 0xaacf8f387ce1fcf3

def z829 : W := mkw 0x37ef77f766cd0004 0x06fdeefeecd9a000 0x778c07ffe6ee0002 0x2ef180fffcddc000

def z830 : W := mkw 0x2570356835a05583 0x04ae06ad06b40ab0 0xfff03ff81fe07f86 0xfffe07ff03fc0ff0

def z831 : W := mkw 0x000080008a1a2a60 0x800010001143454c 0xfe0c07879e1e7e67 0x7fc180f0f3c3cfcc

def z832 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x9ffff8401fff8187 0xf3ffff0803fff030

def z833 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0x918c407fe1ff81fd 0xb231880ffc3ff03f

def z834 : W := mkw 0x27ee75f360000000 0x04fdcebe6c000000 0xc7fff9fbe0000001 0xf8ffff3f7c000000

def z835 : W := mkw 0x0030044811205182 0x0006008902240a30 0xfff007f81fe07f86 0xfffe00ff03fc0ff0

def z836 : W := mkw 0x20a557f760000000 0x0414aafeec000000 0xe1ffffffe0000003 0xfc3ffffffc000000

def z837 : W := mkw 0x08b5de5df977f9fa 0xe116bbcbbf2eff3f 0x71ffbe3b98ee7800 0x6e3ff7c7731dcf00

def z838 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7fffffffe001e03 0xfcffffffffc003c0

def z839 : W := mkw 0x17dee8821fdd8004 0x02fbdd1043fbb000 0xd7fff9839fff8005 0xfaffff3073fff000

def z840 : W := mkw 0x10319e443f9898ac 0xa20633c887f31315 0xa873fe447f1199ff 0xd50e7fc88fe2333f

def z841 : W := mkw 0x0084401140450000 0x001088022808a000 0xd98c407fe1ff81ff 0xbb31880ffc3ff03f

def z842 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xee73ffc4791199ff 0xfdce7ff88f22333f

def z843 : W := mkw 0x17dee9201fdd8004 0x02fbdd2403fbb000 0xd7fff9b81fff8005 0xfaffff3703fff000

def z844 : W := mkw 0x0000000800204102 0x0000000100040820 0xff8007b81ee07e06 0x7ff000f703dc0fc0

def z845 : W := mkw 0x0df45d7975e5d59b 0x61be8baf2ebcbab3 0x01f0787861e18198 0x803e0f0f0c3c3033

def z846 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xff8f87879ffe7e67 0xfff1f0f0f3ffcfcc

def z847 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xd98c407fffffffff 0xbb31880fffffffff

def z848 : W := mkw 0x05d4c8001dd58000 0x00ba990003bab000 0x97fff8001fff8005 0xf2ffff0003fff000

def z849 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x87fff87fe0000001 0xf0ffff0ffc000000

def z850 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xefffffffe0100067 0xfdfffffffc02000c

def z851 : W := mkw 0x27ef77f760001080 0x04fdeefeec000210 0xefffffffe0001983 0xfdfffffffc000330

def z852 : W := mkw 0x27ef77f760450000 0x04fdeefeec08a000 0xffffffffe1ff81ff 0xfffffffffc3ff03f

def z853 : W := mkw 0x1094c8115fdd8004 0x021299022bfbb000 0xd18c407fffff8007 0xba31880ffffff000

def z854 : W := mkw 0x37ef77f764c50004 0x06fdeefeec98a000 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z855 : W := mkw 0x07dee80019558000 0x00fbdd00032ab000 0x97fff80019ff8005 0xf2ffff00033ff000

def z856 : W := mkw 0x17dee8001fdd9485 0x02fbdd0003fbb290 0x97fff8001fff9e05 0xf2ffff0003fff3c0

def z857 : W := mkw 0x020b9a86aa1aaa68 0xa0417350d543554d 0xfe0fffc7ff1fffff 0xffc1fff8ffe3ffff

def z858 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x6e0f87879e1e7e63 0x4dc1f0f0f3c3cfcc

def z859 : W := mkw 0x02af56d760000000 0x0055eadaec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z860 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17f3f8001fff8004 0xc2fe7f0003fff000

def z861 : W := mkw 0x077b9fe63f989ea9 0xa0ef73fcc7f313d5 0x2673bf801e001e00 0x44ce77f003c003c0

def z862 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xe87ffe47f91199ff 0xfd0fffc8ff22333f

def z863 : W := mkw 0x129ee8001b5d8004 0x0253dd00036bb000 0x91fff80019ff8005 0xf23fff00033ff000

def z864 : W := mkw 0x1fce6139c6ef6557 0x43f9cc2738ddecaa 0x578c01bb86ee6600 0x2af1803770ddccc0

def z865 : W := mkw 0x2df4757975e55593 0x45be8eaf2ebcaab2 0x01f0787861e18198 0x803e0f0f0c3c3033

def z866 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xdffff8001fffe007 0xfbffff0003fffc00

def z867 : W := mkw 0x07ce601140000000 0x00f9cc0228000000 0xc7fff83b80000001 0xf8ffff0770000000

def z868 : W := mkw 0x020b9a86aa1aaa68 0xa0417350d543554d 0xfe0fbf879e1e7e67 0x7fc1f7f0f3c3cfcc

def z869 : W := mkw 0x0a8fc297ca5f2a70 0xc151f852f94be54e 0x000f8007801e0061 0x0001f000f003c00c

def z870 : W := mkw 0x00309c40391098a8 0xa006138807221315 0x8873f840791199fd 0xd10e7f080f22333f

def z871 : W := mkw 0x0550012815a04503 0x00aa002502b408a0 0xfff007b81fe07e06 0xfffe00f703fc0fc0

def z872 : W := mkw 0x0000000080022040 0x0000000010004408 0xfe0c07839e0e7e06 0x7fc180f073c1cfc0

def z873 : W := mkw 0x0084401140000000 0x0010880228000000 0xc1fff87fe0000003 0xf83fff0ffc000000

def z874 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff007b81ee07e06 0x7ffe00f703dc0fc0

def z875 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x07fff8001fff8001 0xc0ffff0003fff000

def z876 : W := mkw 0x282117ffe02279fa 0xe50422fffc044f3f 0x680007ffe00079fa 0x0d0000fffc000f3f

def z877 : W := mkw 0x00311e44310098a8 0xa00623c886201315 0xa873fe44610199fb 0xd50e7fc88c20333f

def z878 : W := mkw 0x00319ec6391098a8 0xa00633d8c7221315 0xe873ffc7f91199ff 0xdd0e7ff8ff22333f

def z879 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17fff8001eff8001 0x62ffff0003dff000

def z880 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffbfbf80000003 0x7cfff7f7f0000000

def z881 : W := mkw 0x07ef765560000000 0x00fdeecaac000000 0xe7fffe7fe0000003 0xfcffffcffc000000

def z882 : W := mkw 0x05700d6815a0d58b 0x20ae01ad02b41ab1 0xfff007f81fe1ff9e 0xfffe00ff03fc3ff3

def z883 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xd7fff9801fffe605 0xfaffff3003fffcc0

def z884 : W := mkw 0x175aa8001fdd8004 0x02eb550003fbb000 0x9673f8001fff8005 0xd2ce7f0003fff000

def z885 : W := mkw 0x2a8ff297ea5f2a70 0xc551fe52fd4be54e 0x000ff807e01f8079 0x0001ff00fc03f00f

def z886 : W := mkw 0x081088089b7ffbfa 0xe1021101136fff7f 0x180000001ffffffc 0x0300000003ffffff

def z887 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xf873fe447911f9ff 0xff0e7fc88f223f3f

def z888 : W := mkw 0x020a0082820a2240 0x0041401050414448 0xfe0c07879e1e7e67 0x7fc180f0f3c3cfcc

def z889 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17fff8001fef8000 0xe2ffff0003fdf000

def z890 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xf7ffffffe6006603 0xfefffffffcc00cc0

def z891 : W := mkw 0x07ce600000450000 0x00f9cc000008a000 0x97fff80000ee0001 0xf2ffff00001dc000

def z892 : W := mkw 0x202117ffe0227fe3 0x840422fffc044ffc 0x680007ffe0007fe2 0x0d0000fffc000ffc

def z893 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xf7f007b81fe07e04 0xfefe00f703fc0fc0

def z894 : W := mkw 0x020b8a868a1aaa60 0x80417150d143554c 0xfe0fff879e1ffe67 0x7fc1fff0f3c3ffcc

def z895 : W := mkw 0x17dee8115fdd8004 0x02fbdd022bfbb000 0x97fff8787fff8005 0xf2ffff0f0ffff000

def z896 : W := mkw 0x00319e4439108000 0x000633c887221000 0xa873fe44791181ff 0xd50e7fc88f22303f

def z897 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x8073f844791181fd 0xd00e7f088f22303f

def z898 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z899 : W := mkw 0x181088089fffeb76 0xc302110113fffd6e 0x180000001ffffffc 0x0300000003ffffff

def z900 : W := mkw 0x17ce600006cd0004 0x02f9cc0000d9a000 0x17ffb80006ee0000 0x62fff70000ddc000

def z901 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff047f81ff1ff87 0xfffe08ff03fe3ff0

def z902 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x7ff007f81ee07f82 0x6ffe00ff03dc0ff0

def z903 : W := mkw 0x121a88001fdd8004 0x0243510003fbb000 0x967ff8001fff8005 0xf2cfff0003fff000

def z904 : W := mkw 0x35f47d7975e5d587 0x06be8faf2ebcbab0 0x01f0787861e18180 0x803e0f0f0c3c3030

def z905 : W := mkw 0x3fce61bbc6ef6156 0x47f9cc3778ddec2a 0x578c01bb86ee6000 0x2af1803770ddcc00

def z906 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x7ff007b81fe07f84 0x6ffe00f703fc0ff0

def z907 : W := mkw 0x00a55644204518a8 0xa014aac88408a315 0xb98c464461ff99ff 0xb73188c88c3ff33f

def z908 : W := mkw 0x05700d6815a0d583 0x00ae01ad02b41ab0 0xfff07ff81fe1ff86 0xfffe0fff03fc3ff0

def z909 : W := mkw 0x020b0286820a2240 0x00416050d0414448 0xfe0f87879e0e7e07 0x7fc1f0f0f3c1cfc0

def z910 : W := mkw 0x00119a0439108828 0xa002334087221105 0x8873f844791181ff 0xd10e7f088f22303f

def z911 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x81fff80019ff8005 0xd03fff00033ff000

def z912 : W := mkw 0x1df46d7955e5d597 0x43be8daf2abcbab2 0x01f0787861e18198 0x803e0f0f0c3c3033

def z913 : W := mkw 0x17dee8115fdd8004 0x02fbdd022bfbb000 0x97fff807ffff8005 0xf2ffff00fffff000

def z914 : W := mkw 0x37dee9b35fdd8004 0x06fbdd366bfbb000 0x578c01bb9fff8004 0x2af1803773fff000

def z915 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xeffffffff8001807 0xfdffffffff000300

def z916 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffffffe1118007 0xfcfffffffc223000

def z917 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873fe44611199fb 0x850e7fc88c22333f

def z918 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97fff8447fff8007 0xf2ffff088ffff000

def z919 : W := mkw 0x081088089977e152 0x41021101132efc2a 0x1800000019ffe1fc 0x03000000033ffc3f

def z920 : W := mkw 0x37dee8935fdd8004 0x06fbdd126bfbb000 0x97fff8039fff8005 0xf2ffff0073fff000

def z921 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x0873f844791199fd 0x810e7f088f22333f

def z922 : W := mkw 0x328ffa97ea5faa64 0x8651ff52fd4bf54c 0x000ff807e01f8061 0x0001ff00fc03f00c

def z923 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff047f87fe1ff9e 0xfffe08ff0ffc3ff3

def z924 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xff8c47ffe1ffe1ff 0xfff188fffc3ffc3f

def z925 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xf7ffffffe01e0007 0xfefffffffc03c000

def z926 : W := mkw 0x0000000000000000 0x0000000000000000 0x8873f844611181ff 0xd10e7f088c22303f

def z927 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873fe40791199fc 0xc50e7fc80f22333f

def z928 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xf60f87879e0e7e03 0x7ec1f0f0f3c1cfc0

def z929 : W := mkw 0x17de680015c58004 0x02fbcd0002b8b000 0x97fff80001ff8005 0xf2ffff00003ff000

def z930 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfff007fc7fe07ffe 0xfffe00ff8ffc0fff

def z931 : W := mkw 0x27ef77f764800000 0x04fdeefeec900000 0xf7ffffffe6e00003 0xfefffffffcdc0000

def z932 : W := mkw 0x175aa8001f988004 0x02eb550003f31000 0x97ffb8001ffe0005 0xf2fff70003ffc000

def z933 : W := mkw 0x020b8a868a1aaa68 0xa0417150d143554d 0xfe0f87879e1ffe7f 0x7fc1f0f0f3c3ffcf

def z934 : W := mkw 0x020b82860a180000 0x00417050c1430000 0xfe0f87879e1e7e07 0x7fc1f0f0f3c3cfc0

def z935 : W := mkw 0x00219e4428108828 0xa00433c885021105 0xa873fe44611181ff 0xd50e7fc88c22303f

def z936 : W := mkw 0x27ef77f760450000 0x04fdeefeec08a000 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z937 : W := mkw 0x15d4e8001dd58004 0x02ba9d0003bab000 0x91fff80019ff8005 0xf23fff00033ff000

def z938 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873fe04791199fd 0x450e7fc08f22333f

def z939 : W := mkw 0x0001820488122860 0x800030409102450c 0xfe0f87879e1e7e67 0x7fc1f0f0f3c3cfcc

def z940 : W := mkw 0x20319ff7791098a8 0xa40633feef221315 0x680007fff91199fe 0x0d0000ffff22333f

def z941 : W := mkw 0x00118a0419108820 0x8002314083221104 0xa873fe44791199ff 0xd50e7fc88f22333f

def z942 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x17fff80007ff8001 0xa2ffff0000fff000

def z943 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffffffe011807b 0xfcfffffffc02300f

def z944 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xb87ffe44791f99ff 0xf70fffc88f23f33f

def z945 : W := mkw 0x0560056804a04503 0x00ac00ad009408a0 0xfff007f81ee07e06 0xfffe00ff03dc0fc0

def z946 : W := mkw 0x175aa8001fdd8004 0x02eb550003fbb000 0x1673b8001eee0000 0x42ce770003ddc000

def z947 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xb7ffff801fff9e05 0xf6fffff003fff3c0

def z948 : W := mkw 0x37ef77f766cd0004 0x06fdeefeecd9a000 0xf7ffffffe7ff8007 0xfefffffffcfff000

def z949 : W := mkw 0x029ec8001b5d8000 0x0053d900036bb000 0x97fff8001fff8005 0xf2ffff0003fff000

def z950 : W := mkw 0x07de600015c50000 0x00fbcc0002b8a000 0x97fff8001fff8005 0xf2ffff0003fff000

def z951 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xdf8c41ffe7ffe7ff 0xbbf1883ffcfffcff

def z952 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xe9f3fe7c791199ff 0xfd3e7fcf8f22333f

def z953 : W := mkw 0x05e5577560000000 0x00bcaaeeac000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z954 : W := mkw 0x00311e4431009088 0x200623c886201211 0xa873fe44611181ff 0xd50e7fc88c22303f

def z955 : W := mkw 0x17dee8821fdd8204 0x02fbdd1043fbb040 0x97fff9801fff8605 0xf2ffff3003fff0c0

def z956 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97fff8001eee0001 0xf2ffff0003ddc000

def z957 : W := mkw 0x05701d6835a0d58b 0x20ae03ad06b41ab1 0xfff07ffc7ff1ffff 0xfffe0fff8ffe3fff

def z958 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x7e0c07879e1e7e66 0x2fc180f0f3c3cfcc

def z959 : W := mkw 0x276b37f760000000 0x04ed66feec000000 0xe673ffffe0000003 0xdcce7ffffc000000

def z960 : W := mkw 0x0560056800204102 0x00ac00ad00040820 0xfff007f81fe07f86 0xfffe00ff03fc0ff0

def z961 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xb9f3fe4479f199ff 0xf73e7fc88f3e333f

def z962 : W := mkw 0x07ef67e600000000 0x00fdecfcc0000000 0xe7ffffff80000003 0xfcfffffff0000000

def z963 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x9ffff8041fff8067 0xf3ffff0083fff00c

def z964 : W := mkw 0x001088089fbaffeb 0xa002110113f75ffd 0x180000001ffffffc 0x0300000003ffffff

def z965 : W := mkw 0x27ef77f7600018a8 0xa4fdeefeec000315 0xe7ffffffe0001803 0xfcfffffffc000300

def z966 : W := mkw 0x17dee8115fdd8004 0x02fbdd022bfbb000 0xd7fff83b9fff8005 0xfaffff0773fff000

def z967 : W := mkw 0x0084400000450000 0x001088000008a000 0x91fff80001ff8005 0xf23fff00003ff000

def z968 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0f87c79f1e7fe7 0xffc1f0f8f3e3cffc

def z969 : W := mkw 0x17dee8001fdd9084 0x02fbdd0003fbb210 0x9ffff8001fff9985 0xf3ffff0003fff330

def z970 : W := mkw 0x20a557f760450000 0x0414aafeec08a000 0xf18c47ffe1ff8007 0xbe3188fffc3ff000

def z971 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xff8f87ff9e1e7e67 0xfff1f0fff3c3cfcc

def z972 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xd7fff8781fff8007 0xfaffff0f03fff000

def z973 : W := mkw 0x00319f64391098a8 0xa00633ec87221315 0xe873fffc791199ff 0xdd0e7fff8f22333f

def z974 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x9ffff8001fff81fd 0xf3ffff0003fff03f

def z975 : W := mkw 0x020a80828a1a2a60 0x804150105143454c 0xfe0c07839e1e7e66 0x7fc180f073c3cfcc

def z976 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfffc07f81ffe7f87 0xffff80ff03ffcff0

def z977 : W := mkw 0x101088089fffffe7 0x8202110113fffffc 0x180000001fffffe4 0x0300000003fffffc

def z978 : W := mkw 0x0821164ca02279fa 0xe10422c994044f3f 0x28000644600079fa 0x050000c88c000f3f

def z979 : W := mkw 0x07ee657140000000 0x00fdccae28000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z980 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x67ffffbfe0000001 0x6cfffff7fc000000

def z981 : W := mkw 0x37dee9a21fdd8004 0x06fbdd3443fbb000 0x97fff9801fff8005 0xf2ffff3003fff000

def z982 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xffffffffe0006007 0xfffffffffc000c00

def z983 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xae73ffc47f119fff 0xd5ce7ff88fe233ff

def z984 : W := mkw 0x27cf729760000000 0x04f9ee52ec000000 0xc7fff87fe0000003 0xf8ffff0ffc000000

def z985 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xefffffffe1000187 0xfdfffffffc200030

def z986 : W := mkw 0x37ef77f7624d0004 0x06fdeefeec49a000 0xe7ffffffe00e0003 0xfcfffffffc01c000

def z987 : W := mkw 0x27ef77f764800401 0x04fdeefeec900080 0xe7ffffffe6000603 0xfcfffffffcc000c0

def z988 : W := mkw 0x181088089fffe156 0x4302110113fffc2a 0x100000001fffe004 0x0200000003fffc00

def z989 : W := mkw 0x0821165de0226152 0x410422cbbc044c2a 0x6800067fe00061fa 0x0d0000cffc000c3f

def z990 : W := mkw 0x37dee9315fdd8004 0x06fbdd262bfbb000 0x97fff8381fff8005 0xf2ffff0703fff000

def z991 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xf7f007f81ee07e02 0xfefe00ff03dc0fc0

def z992 : W := mkw 0x27cf63b740000000 0x04f9ec76e8000000 0xe7ffffbf80000003 0xfcfffff7f0000000

def z993 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0fc7879f1ffe67 0xffc1f8f0f3e3ffcc

def z994 : W := mkw 0x27ef77f762080200 0x04fdeefeec410040 0xe7ffffffe6000603 0xfcfffffffcc000c0

def z995 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xa073fe44611181fb 0xd40e7fc88c22303f

def z996 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x667fffffe0000003 0x4ccffffffc000000

def z997 : W := mkw 0x120baa868a1aaa64 0x82417550d143554c 0xfe0fbf879e1e7e67 0x7fc1f7f0f3c3cfcc

def z998 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xd7fff8079fff8007 0xfaffff00f3fff000

def z999 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xf98c47ffe1ffffff 0xbf3188fffc3fffff

def z1000 : W := mkw 0x282117ffe02275d3 0x450422fffc044eba 0x680007ffe0007ffa 0x0d0000fffc000fff

def z1001 : W := mkw 0x17cee0000edd0004 0x02f9dc0001dba000 0x97fff8001efe0005 0xf2ffff0003dfc000

def z1002 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x61ffffffe0000003 0x8c3ffffffc000000

def z1003 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe0f87839e0e7e06 0x7fc1f0f073c1cfc0

def z1004 : W := mkw 0x22af76d760000000 0x0455eedaec000000 0xe1fffe7fe0000003 0xfc3fffcffc000000

def z1005 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0x7e0f87879e0e7e62 0x6fc1f0f0f3c1cfcc

def z1006 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xf60f87839e1e7e05 0x7ec1f0f073c3cfc0

def z1007 : W := mkw 0x1fdee8115fdd8014 0x43fbdd022bfbb002 0x97fff8007fff801d 0xf2ffff000ffff003

def z1008 : W := mkw 0x27ef77f7600018a8 0xa4fdeefeec000315 0xefffffffe11199ff 0xfdfffffffc22333f

def z1009 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffffbb80000001 0xfcfffff770000000

def z1010 : W := mkw 0x020b82868a1a2a60 0x80417050d143454c 0xfe7fff879e1e7e67 0xffcffff0f3c3cfcc

def z1011 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x7f8007f81fe07f86 0x2ff000ff03fc0ff0

def z1012 : W := mkw 0x081088089df7fdfb 0xe102110113beffbf 0x180000001ffffffc 0x0300000003ffffff

def z1013 : W := mkw 0x0000000880226142 0x0000000110044c28 0xd98c407fe1ffe1ff 0xbb31880ffc3ffc3f

def z1014 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xefffffffe00001fb 0xfdfffffffc00003f

def z1015 : W := mkw 0x155088001fdd8004 0x02aa110003fbb000 0x97f3f8001fff8005 0xf2fe7f0003fff000

def z1016 : W := mkw 0x05701d6835a0d58b 0x20ae03ad06b41ab1 0xfff03ff81fe07f86 0xfffe07ff03fc0ff0

def z1017 : W := mkw 0x0df4457955e55593 0x41be88af2abcaab2 0x01f0007801e00180 0x803e000f003c0030

def z1018 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0xfffc07ff9fe07f87 0xffff80fff3fc0ff0

def z1019 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x77f007f81fe07f80 0xeefe00ff03fc0ff0

def z1020 : W := mkw 0x07dee0001f980000 0x00fbdc0003f30000 0x97fff8001ffe0005 0xf2ffff0003ffc000

def z1021 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0xbffffe001fff9807 0xf7ffffc003fff300

def z1022 : W := mkw 0x0010880019558000 0x00021100032ab000 0x9073f80019ff8005 0xd20e7f00033ff000

def z1023 : W := mkw 0x002117eea0227feb 0xa00422fdd4044ffd 0x680007ffe0007ffa 0x0d0000fffc000fff

def z1024 : W := mkw 0x175aa8001fdd8004 0x02eb550003fbb000 0x967fb8001fff8005 0x72cff70003fff000

def z1025 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97fff8407fff819d 0xf2ffff080ffff033

def z1026 : W := mkw 0x17de600017cd0004 0x02fbcc0002f9a000 0x97fff8001fee0005 0xf2ffff0003fdc000

def z1027 : W := mkw 0x0570156835a0558b 0x20ae02ad06b40ab1 0xfff007f87fe07f9e 0xfffe00ff0ffc0ff3

def z1028 : W := mkw 0x276b37e620000000 0x04ed66fcc4000000 0xe7ffbfff80000003 0xfcfff7fff0000000

def z1029 : W := mkw 0x2fef77f760450010 0x45fdeefeec08a002 0xe7ffffffe001801b 0xfcfffffffc003003

def z1030 : W := mkw 0x276b37f760000000 0x04ed66feec000000 0xe7f3bfffe0000002 0xfcfe77fffc000000

def z1031 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0xb873fe447f11ffff 0xd70e7fc88fe23fff

def z1032 : W := mkw 0x00319ec639109aa8 0xa00633d8c7221355 0xa873ffc479119fff 0xd50e7ff88f2233ff

def z1033 : W := mkw 0x17dee9201fdd8405 0x02fbdd2403fbb080 0x97fff9801fff8605 0xf2ffff3003fff0c0

def z1034 : W := mkw 0x129ee8001fdd8004 0x0253dd0003fbb000 0x907ff8001fff8005 0xd20fff0003fff000

def z1035 : W := mkw 0x17cee8000edd8004 0x02f9dd0001dbb000 0x97fff80006ff8001 0xf2ffff0000dff000

def z1036 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873fe44790199fa 0xc50e7fc88f20333f

def z1037 : W := mkw 0x00319f6439109ca9 0xa00633ec87221395 0xa873ffc479119fff 0xd50e7ff88f2233ff

def z1038 : W := mkw 0x15d4e8001fdd8004 0x02ba9d0003fbb000 0x91f3f8001fff8005 0xd23e7f0003fff000

def z1039 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xc1fff87fe0000003 0xb83fff0ffc000000

def z1040 : W := mkw 0x17dee8001fdd8824 0x82fbdd0003fbb104 0x9ffff8001fff9865 0xf3ffff0003fff30c

def z1041 : W := mkw 0x0001028680022a60 0x80002050d000454c 0xfe0c07879e1e7e67 0x7fc180f0f3c3cfcc

def z1042 : W := mkw 0x0570156835a05583 0x00ae02ad06b40ab0 0xfff07ff87fe07f86 0xfffe0fff0ffc0ff0

def z1043 : W := mkw 0x10319e443fdd98ac 0xa20633c887fbb315 0x380006447fff99fe 0x070000c88ffff33f

def z1044 : W := mkw 0x0540012804a04503 0x00a80025009408a0 0x778007b81ee07e00 0x6ef000f703dc0fc0

def z1045 : W := mkw 0x377bbfe63f9898ac 0xa6ef77fcc7f31315 0x2673bf801e001800 0x44ce77f003c00300

def z1046 : W := mkw 0x2fce61bbc4e76553 0x45f9cc37789cecaa 0x578c01bb86ee6600 0x2af1803770ddccc0

def z1047 : W := mkw 0x202117f760000000 0x040422feec000000 0x6073bfffe0000002 0x4c0e77fffc000000

def z1048 : W := mkw 0x00119a04391098a8 0xa002334087221315 0x8873f804791199fd 0xd10e7f008f22333f

def z1049 : W := mkw 0x27ee65f340000000 0x04fdccbe68000000 0xe7fffffb80000003 0xfcffffff70000000

def z1050 : W := mkw 0x181088089ffff9fe 0xe302110113ffff3f 0x180000001ffff9fc 0x0300000003ffff3f

def z1051 : W := mkw 0x15702d6815a0d587 0x02ae05ad02b41ab0 0xfff03ff81fe07f86 0xfffe07ff03fc0ff0

def z1052 : W := mkw 0x00309c4039109088 0x2006138807221211 0x8873f844791181ff 0xd10e7f088f22303f

def z1053 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0x67ffbfffe0000002 0x6cfff7fffc000000

def z1054 : W := mkw 0x17dee8115fdd8004 0x02fbdd022bfbb000 0xdffff87fffff81ff 0xfbffff0ffffff03f

def z1055 : W := mkw 0x0570056015800000 0x00ae00ac02b00000 0xfff007f81fe07e06 0xfffe00ff03fc0fc0

def z1056 : W := mkw 0x0a8fda97ea5faa78 0xe151fb52fd4bf54f 0x000ff807e01f8079 0x0001ff00fc03f00f

def z1057 : W := mkw 0x00319e44391098a8 0xa00633c887221315 0x2873fe44781199fb 0x450e7fc88f02333f

def z1058 : W := mkw 0x27ef77f762080000 0x04fdeefeec410000 0xf7ffffffe60e0003 0xfefffffffcc1c000

def z1059 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x97fff8047fff807d 0xf2ffff008ffff00f

def z1060 : W := mkw 0x020b0286820a2a60 0x80416050d041454c 0xfe0c07879e0e7e66 0x7fc180f0f3c1cfcc

def z1061 : W := mkw 0x222b17f760000000 0x044562feec000000 0xe67fffffe0000003 0xfccffffffc000000

def z1062 : W := mkw 0x17de680017cd8004 0x02fbcd0002f9b000 0x97fff80007ef8001 0xf2ffff0000fdf000

def z1063 : W := mkw 0x25e5777560000000 0x04bcaeeeac000000 0xe1fffe7fe0000003 0xfc3fffcffc000000

def z1064 : W := mkw 0x08844019c0676152 0x41108803380cec2a 0xc18c407fe1ff81fb 0xb831880ffc3ff03f

def z1065 : W := mkw 0x27ef77f760001481 0x04fdeefeec000290 0xe7ffffffe0001e03 0xfcfffffffc0003c0

def z1066 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x91fff80001ff8005 0xb23fff00003ff000

def z1067 : W := mkw 0x0020056800205583 0x000400ad00040ab0 0xff8007f81fe07f86 0xfff000ff03fc0ff0

def z1068 : W := mkw 0x17dee8001fdd8004 0x02fbdd0003fbb000 0x11fff8001fff8005 0x823fff0003fff000

def z1069 : W := mkw 0x0570056815a05583 0x00ae00ad02b40ab0 0x6ff007f81fe07f82 0xcdfe00ff03fc0ff0

def z1070 : W := mkw 0x27ef77f760000000 0x04fdeefeec000000 0xe7ffffffe101819b 0xfcfffffffc203033

def z1071 : W := mkw 0x0550012815a05583 0x00aa002502b40ab0 0xff8007b81fe07f86 0x7ff000f703fc0ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z7]),(0,[z0,z2,z3,z8,z9,z5,z6]),(0,[z10,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z12,z6]),(0,[z13,z0,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z15,z6]),(0,[z16,z0,z1,z2,z3,z6,z17])],[(0,[z0,z1,z18,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z19,z20]),(0,[z21,z0,z1,z2,z3,z5,z6])],[(0,[z0,z22,z1,z14,z3,z5,z6]),(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z25,z26,z6]),(0,[z0,z27,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z28,z5,z6]),(0,[z0,z29,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z30,z5,z6]),(0,[z0,z1,z2,z31,z3,z5,z6])],[(1,[z0,z1,z2,z3,z32,z6]),(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z34,z0,z1,z3,z9,z5,z6]),(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z0,z1,z36,z2,z3,z5,z37]),(0,[z0,z38,z1,z2,z5,z39,z6]),(0,[z0,z1,z2,z3,z40,z5,z6])],[(0,[z0,z1,z2,z3,z5,z41,z6]),(0,[z42,z0,z1,z43,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z45,z5,z6]),(0,[z0,z1,z2,z46,z3,z5,z6])],[(0,[z0,z1,z2,z3,z47,z5,z6]),(0,[z0,z48,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z49,z50,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z52,z6]),(0,[z0,z1,z14,z3,z9,z5,z6]),(0,[z0,z1,z53,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z54,z6]),(0,[z0,z38,z1,z2,z3,z5,z6])],[(0,[z55,z1,z2,z3,z56,z5,z6]),(0,[z0,z1,z2,z3,z5,z57,z6]),(0,[z0,z1,z43,z2,z3,z5,z6]),(0,[z34,z0,z1,z58,z3,z5,z6]),(0,[z0,z59,z1,z2,z3,z5,z6])],[(1,[z0,z60,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z6,z61])],[(0,[z62,z0,z1,z2,z3,z5,z6]),(0,[z63,z0,z1,z64,z3,z5,z6]),(0,[z0,z1,z2,z65,z3,z56,z5]),(1,[z66,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z6]),(0,[z0,z68,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z69,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z71,z6])],[(1,[z0,z72,z2,z3,z5,z6]),(1,[z0,z1,z2,z65,z3,z5]),(0,[z16,z0,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z74,z3,z5,z6]),(0,[z0,z75,z1,z2,z3,z5,z6])],[(1,[z76,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z77,z6]),(0,[z0,z1,z2,z78,z3,z5,z6]),(0,[z0,z38,z1,z2,z79,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z80,z6]),(0,[z0,z1,z2,z3,z5,z81,z6])],[(0,[z82,z0,z1,z2,z3,z5,z6])],[(0,[z0,z83,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z84,z6])],[(0,[z0,z1,z2,z3,z5,z85,z6]),(0,[z0,z86,z1,z2,z3,z5,z6])],[(0,[z87,z0,z1,z2,z3,z6,z17]),(0,[z0,z88,z1,z2,z3,z5,z6]),(0,[z0,z1,z89,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z90,z6]),(1,[z0,z1,z2,z3,z40,z6])],[(0,[z0,z1,z2,z3,z26,z91,z6]),(0,[z0,z1,z2,z92,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z93,z6])],[(0,[z55,z94,z1,z2,z3,z5,z6]),(0,[z0,z1,z95,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z96,z6]),(0,[z0,z1,z2,z97,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z98]),(1,[z0,z99,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z100]),(0,[z42,z0,z1,z2,z3,z101,z6]),(0,[z42,z0,z1,z2,z3,z5,z102]),(0,[z0,z1,z58,z103,z3,z5,z6]),(0,[z0,z1,z2,z104,z3,z5,z20])]],
   [[(0,[z105,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z106,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z6]),(0,[z0,z108,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z109]),(0,[z0,z1,z2,z3,z110,z5,z6]),(0,[z111,z0,z1,z2,z3,z5,z112]),(0,[z0,z1,z2,z3,z91,z6,z17])],[(0,[z113,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z114,z3,z5,z6]),(0,[z115,z0,z1,z2,z3,z5,z6]),(1,[z116,z1,z2,z3,z5,z117]),(0,[z0,z1,z2,z118,z3,z5,z6]),(0,[z0,z1,z2,z119,z3,z5,z6]),(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z0,z121,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z123,z3,z5,z6]),(0,[z124,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z36,z3,z5,z112]),(0,[z0,z1,z2,z3,z5,z6,z125]),(0,[z0,z1,z2,z3,z5,z6,z20])],[(0,[z126,z0,z1,z2,z3,z5,z6]),(0,[z0,z127,z2,z3,z50,z5,z6]),(1,[z0,z1,z128,z3,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z130,z5,z6]),(0,[z0,z131,z1,z2,z5,z6,z20])],[(0,[z42,z132,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z49,z5,z6]),(0,[z0,z1,z2,z3,z5,z133,z6]),(0,[z0,z1,z2,z134,z25,z5,z6])],[(0,[z0,z1,z2,z3,z135,z5,z6]),(0,[z0,z1,z2,z3,z5,z136,z6])],[(0,[z0,z1,z137,z3,z9,z5,z6]),(0,[z138,z0,z1,z3,z50,z5,z6]),(0,[z0,z1,z139,z2,z3,z5,z6]),(1,[z111,z0,z1,z3,z5,z37]),(0,[z0,z1,z2,z3,z5,z91,z140])]],
   [[(0,[z0,z1,z2,z3,z5,z141,z6]),(0,[z142,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z143,z6])],[(0,[z0,z1,z2,z144,z3,z5,z6])],[(0,[z0,z145,z1,z2,z3,z5,z6]),(0,[z0,z88,z2,z3,z5,z85,z6]),(0,[z0,z1,z146,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z104,z5,z6])],[(0,[z0,z1,z2,z3,z5,z147,z6]),(0,[z0,z1,z2,z3,z148,z91,z6]),(0,[z0,z149,z1,z2,z3,z5,z6])],[(0,[z76,z0,z150,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z151]),(1,[z87,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z152,z3,z5,z6]),(0,[z0,z1,z2,z3,z153,z5,z6]),(0,[z0,z1,z154,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z155,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z157,z5,z81,z6]),(0,[z158,z0,z1,z2,z3,z5,z6])],[(0,[z159,z0,z1,z2,z3,z5,z6]),(1,[z16,z1,z2,z3,z148,z6]),(1,[z0,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z5,z160,z6]),(0,[z0,z1,z2,z3,z5,z6,z161])],[(0,[z0,z1,z162,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z163,z6]),(0,[z0,z1,z2,z103,z92,z5,z6]),(0,[z0,z1,z164,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z165,z6]),(0,[z0,z1,z2,z3,z166,z5,z6]),(0,[z0,z48,z1,z2,z50,z5,z6]),(0,[z34,z0,z1,z2,z103,z5,z6]),(0,[z167,z0,z1,z2,z3,z5,z6])],[(0,[z42,z0,z1,z2,z3,z5,z168]),(0,[z138,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z169,z5,z6]),(0,[z0,z1,z2,z79,z104,z3,z5])],[(0,[z0,z1,z2,z3,z170,z5,z6]),(0,[z0,z1,z2,z3,z5,z171,z6]),(0,[z0,z1,z2,z3,z172,z5,z6]),(1,[z0,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z5,z173,z6]),(0,[z0,z1,z2,z3,z5,z174,z6]),(0,[z0,z1,z3,z5,z37,z6,z112]),(0,[z175,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z176,z6]),(0,[z0,z1,z2,z3,z5,z177,z6]),(0,[z0,z1,z2,z3,z178,z5,z6])],[(0,[z0,z1,z2,z3,z5,z179,z6]),(1,[z132,z1,z2,z3,z5,z6]),(0,[z180,z0,z1,z2,z3,z5,z6]),(0,[z181,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z182,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z183]),(0,[z0,z1,z2,z184,z3,z5,z6])],[(1,[z185,z1,z2,z186,z5,z6]),(0,[z187,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z188,z6]),(0,[z0,z189,z1,z2,z3,z5,z6])],[(1,[z190,z127,z2,z3,z5,z6]),(0,[z55,z0,z1,z2,z56,z5,z6]),(0,[z0,z1,z2,z3,z191,z5,z6]),(0,[z0,z1,z2,z3,z5,z192,z6])]],
   [[(0,[z0,z1,z2,z193,z3,z5,z6]),(0,[z1,z14,z2,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z39,z6]),(0,[z0,z1,z2,z194,z3,z5,z6]),(0,[z0,z1,z2,z195,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z196]),(0,[z34,z0,z1,z2,z9,z5,z6]),(0,[z0,z1,z2,z3,z197,z5,z6])],[(0,[z0,z1,z2,z198,z3,z5,z6])],[(0,[z55,z1,z2,z3,z5,z117,z6]),(0,[z0,z1,z2,z3,z5,z199,z6]),(0,[z0,z1,z2,z3,z200,z5,z6]),(0,[z0,z1,z2,z3,z85,z81,z6]),(0,[z201,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z140,z17])],[(0,[z202,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z203])],[(0,[z0,z204,z2,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z205,z5,z6]),(0,[z0,z1,z2,z3,z206,z5,z6]),(0,[z0,z38,z1,z2,z3,z25,z6]),(0,[z207,z0,z1,z2,z3,z5,z6])],[(0,[z0,z208,z1,z2,z3,z5,z6]),(0,[z0,z209,z1,z2,z3,z5,z6])],[(0,[z55,z87,z1,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z117,z6,z210]),(0,[z0,z1,z2,z3,z106,z117,z6]),(0,[z42,z0,z1,z2,z144,z5,z6]),(0,[z211,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z212,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z17])],[(0,[z55,z0,z1,z2,z3,z213,z6]),(0,[z0,z1,z214,z2,z3,z5,z6]),(0,[z215,z0,z1,z3,z157,z5,z6]),(0,[z0,z1,z2,z3,z5,z216,z6])]],
   [[(0,[z217,z0,z1,z2,z3,z5,z6]),(0,[z218,z0,z1,z2,z3,z5,z6]),(0,[z219,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z36,z2,z3,z5,z112]),(0,[z0,z1,z2,z220,z3,z5,z6])],[(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z87,z0,z1,z2,z134,z3,z6]),(0,[z87,z0,z1,z2,z3,z222,z6]),(0,[z42,z0,z1,z2,z3,z32,z6]),(0,[z42,z0,z1,z103,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z223,z6]),(0,[z0,z1,z224,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z222,z25,z6])],[(0,[z0,z225,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z6])],[(0,[z0,z1,z2,z137,z3,z5,z6]),(0,[z227,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z228,z2,z3,z5,z6])],[(1,[z0,z1,z229,z3,z5,z6]),(0,[z55,z0,z1,z2,z186,z5,z6]),(0,[z0,z230,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z231,z6]),(0,[z51,z0,z2,z3,z5,z232,z6]),(0,[z233,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z234,z3,z5,z6])],[(0,[z0,z1,z2,z3,z148,z39,z6]),(1,[z0,z22,z43,z3,z5,z6]),(0,[z51,z0,z235,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z236,z5,z6]),(0,[z237,z0,z1,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z3,z5,z140])],[(0,[z76,z13,z1,z2,z3,z5,z6]),(1,[z238,z0,z2,z3,z239,z6]),(0,[z0,z1,z2,z3,z5,z240,z6])]],
   [[(0,[z241,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z117,z20]),(0,[z42,z66,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z242,z6]),(0,[z0,z1,z2,z3,z243,z5,z6])],[(0,[z0,z1,z2,z3,z244,z5,z6]),(0,[z0,z1,z245,z2,z3,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z246])],[(1,[z13,z1,z137,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z100]),(0,[z0,z1,z247,z2,z3,z5,z6])],[(0,[z0,z1,z248,z2,z3,z5,z6])],[(0,[z249,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z106,z6])],[(0,[z0,z1,z2,z250,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z210]),(1,[z0,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z251]),(0,[z0,z1,z2,z79,z134,z3,z6]),(0,[z0,z1,z2,z79,z3,z222,z6])],[(0,[z0,z252,z1,z2,z3,z5,z6]),(0,[z0,z1,z253,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z6]),(0,[z0,z1,z2,z254,z3,z5,z6]),(0,[z0,z255,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z256])],[(0,[z0,z1,z2,z3,z5,z6,z257]),(0,[z0,z1,z2,z3,z5,z258,z6]),(0,[z0,z1,z2,z3,z5,z6,z259])]],
   [[(0,[z0,z1,z2,z3,z260,z5,z6]),(0,[z0,z1,z2,z3,z5,z261,z6])],[(0,[z87,z0,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z262,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z263,z6]),(1,[z0,z235,z2,z3,z5,z246]),(0,[z0,z38,z1,z2,z134,z5,z6]),(0,[z0,z1,z2,z134,z3,z39,z6])],[(0,[z0,z264,z1,z2,z3,z5,z6]),(0,[z265,z0,z1,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z266,z3,z5,z6]),(0,[z267,z0,z1,z2,z3,z5,z6])],[(0,[z63,z0,z127,z2,z3,z5,z6]),(0,[z268,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z5,z269]),(0,[z0,z1,z2,z270,z3,z5,z6]),(0,[z111,z0,z1,z36,z3,z5,z6])],[(0,[z0,z1,z2,z3,z271,z5,z6]),(0,[z272,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z273,z3,z5,z6])],[(0,[z204,z1,z127,z2,z3,z5,z6]),(0,[z274,z0,z1,z2,z3,z5,z6]),(0,[z55,z0,z1,z2,z3,z5,z203]),(0,[z275,z0,z1,z2,z3,z5,z6]),(0,[z16,z0,z38,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z276,z6])],[(0,[z0,z1,z277,z2,z3,z5,z6]),(0,[z278,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z279,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z280,z6]),(0,[z0,z1,z36,z3,z5,z6,z112]),(0,[z0,z1,z2,z3,z5,z6,z281]),(1,[z1,z2,z3,z5,z6,z282])],[(0,[z0,z1,z14,z58,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z6]),(0,[z283,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z284,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z50,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z285]),(1,[z0,z1,z2,z3,z5,z286]),(0,[z0,z1,z2,z287,z3,z5,z6]),(0,[z0,z288,z1,z2,z3,z5,z6])],[(0,[z289,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z50,z9,z5,z6]),(0,[z0,z1,z2,z3,z5,z290,z6]),(0,[z291,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z292,z6])],[(0,[z0,z1,z293,z2,z3,z5,z6]),(0,[z294,z0,z1,z2,z3,z5,z6]),(0,[z295,z0,z1,z2,z3,z5,z6]),(0,[z0,z235,z2,z3,z5,z6,z246]),(0,[z0,z296,z1,z2,z3,z5,z6]),(0,[z297,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z298,z6]),(0,[z0,z1,z2,z3,z5,z269,z20]),(0,[z0,z1,z2,z3,z5,z246,z112]),(0,[z0,z1,z2,z3,z5,z91,z6])],[(0,[z87,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z299,z3,z5,z6]),(0,[z0,z1,z2,z3,z300,z5,z6])],[(0,[z0,z1,z2,z3,z5,z140,z269]),(0,[z0,z1,z301,z2,z3,z5,z6]),(0,[z0,z302,z1,z2,z3,z5,z6])],[(0,[z87,z1,z2,z186,z3,z5,z6]),(0,[z0,z1,z2,z303,z3,z5,z6]),(0,[z211,z0,z1,z2,z50,z5,z6]),(0,[z304,z0,z2,z3,z9,z5,z6]),(0,[z0,z1,z2,z3,z305,z5,z6])]],
   [[(0,[z0,z1,z2,z306,z3,z5,z6]),(0,[z307,z0,z1,z2,z3,z5,z6]),(0,[z308,z0,z1,z2,z3,z5,z6])],[(0,[z76,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z309,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z269]),(0,[z0,z48,z2,z92,z3,z5,z6]),(0,[z0,z1,z2,z3,z310,z5,z6]),(0,[z0,z1,z2,z3,z5,z311,z6]),(0,[z312,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z239,z5,z6]),(0,[z0,z1,z2,z313,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z314,z6]),(1,[z0,z1,z2,z3,z315,z6])],[(0,[z0,z1,z316,z2,z3,z5,z6]),(0,[z317,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z1,z2,z3,z260,z6]),(0,[z0,z60,z1,z2,z3,z56,z6])],[(0,[z0,z1,z318,z2,z3,z5,z6]),(0,[z0,z1,z2,z319,z3,z5,z6]),(0,[z320,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z239,z5,z85,z6]),(0,[z0,z321,z1,z2,z3,z5,z6]),(0,[z322,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z323])],[(0,[z0,z1,z2,z3,z5,z324,z6]),(0,[z94,z0,z1,z2,z3,z5,z17]),(0,[z42,z0,z2,z92,z3,z5,z6]),(0,[z42,z34,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z325,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z213,z6]),(0,[z0,z1,z2,z3,z5,z73,z6]),(0,[z0,z1,z2,z326,z3,z5,z6]),(0,[z0,z327,z1,z2,z3,z5,z6]),(0,[z0,z1,z328,z2,z3,z5,z6])],[(1,[z0,z329,z1,z2,z3,z5]),(0,[z94,z0,z1,z2,z104,z3,z5]),(1,[z42,z0,z299,z3,z5,z6]),(0,[z0,z1,z2,z3,z330,z5,z6]),(0,[z0,z1,z58,z2,z103,z5,z6])],[(0,[z0,z1,z331,z2,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z5,z269]),(0,[z0,z235,z1,z2,z3,z5,z246]),(0,[z0,z1,z2,z3,z5,z332,z6]),(0,[z0,z1,z2,z3,z333,z5,z6]),(0,[z0,z1,z2,z3,z334,z5,z6]),(0,[z0,z1,z2,z3,z5,z335,z6])],[(0,[z0,z1,z2,z336,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z337,z6]),(0,[z0,z1,z338,z2,z3,z5,z6]),(0,[z0,z339,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z6,z17])],[(0,[z0,z1,z2,z3,z5,z6,z340]),(0,[z0,z1,z2,z3,z5,z6,z341]),(0,[z0,z1,z2,z3,z5,z6,z342]),(0,[z0,z38,z1,z2,z3,z5,z343])],[(0,[z0,z344,z1,z2,z3,z5,z6]),(0,[z345,z0,z1,z2,z3,z5,z6]),(0,[z238,z0,z1,z2,z3,z5,z6])],[(0,[z0,z346,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z347,z3,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z232])],[(0,[z0,z1,z2,z3,z348,z5,z6]),(0,[z0,z1,z2,z3,z349,z5,z6]),(0,[z0,z1,z2,z350,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z351,z5,z6]),(0,[z0,z1,z352,z2,z3,z5,z6])],[(0,[z0,z1,z58,z2,z9,z5,z6]),(1,[z353,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z354,z6]),(0,[z0,z1,z2,z3,z355,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z356]),(0,[z0,z1,z357,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z358]),(0,[z0,z1,z2,z79,z3,z5,z17])],[(0,[z359,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z360,z5,z6]),(0,[z0,z235,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z361]),(0,[z0,z1,z2,z362,z3,z5,z6]),(0,[z0,z1,z363,z2,z3,z5,z6]),(0,[z0,z1,z364,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z365,z5,z6]),(0,[z0,z366,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z367,z6]),(0,[z0,z131,z1,z2,z3,z40,z6])],[(0,[z0,z1,z64,z2,z3,z5,z6]),(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z0,z1,z2,z3,z369,z5,z6]),(0,[z0,z88,z1,z2,z3,z85,z6]),(0,[z0,z1,z2,z3,z370,z5,z6])],[(0,[z371,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z372])],[(0,[z190,z0,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z39,z6]),(1,[z0,z1,z2,z97,z3,z6])]],
   [[(0,[z0,z1,z2,z373,z3,z5,z6]),(0,[z42,z0,z1,z14,z3,z5,z6]),(0,[z0,z374,z1,z2,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z375,z3,z5,z6]),(0,[z0,z131,z1,z2,z3,z315,z6])],[(0,[z376,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z91,z6])],[(0,[z0,z1,z150,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z377,z3,z5,z6]),(0,[z0,z1,z2,z3,z222,z5,z269]),(0,[z378,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z379])],[(0,[z0,z1,z2,z3,z5,z380,z6]),(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z381,z6]),(0,[z0,z1,z2,z3,z5,z382,z6])],[(0,[z0,z1,z383,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z384,z5,z6])],[(0,[z0,z1,z2,z3,z385,z5,z6]),(0,[z42,z211,z0,z2,z3,z5,z6]),(0,[z386,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z387,z3,z5,z6]),(0,[z0,z1,z2,z3,z388,z5,z6]),(0,[z0,z1,z2,z389,z3,z5,z6]),(0,[z0,z390,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z391]),(0,[z0,z392,z1,z2,z3,z5,z6]),(0,[z393,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z394])],[(0,[z0,z1,z2,z395,z3,z5,z6]),(0,[z63,z0,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z396,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z3,z5,z140,z117]),(0,[z397,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z343]),(1,[z0,z1,z2,z398,z3,z5]),(0,[z0,z1,z2,z3,z25,z6,z17])]],
   [[(0,[z16,z0,z1,z2,z3,z5,z286]),(0,[z399,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z64,z3,z5,z6]),(0,[z0,z1,z2,z400,z3,z5,z6]),(0,[z0,z1,z2,z3,z401,z5,z6]),(0,[z0,z1,z2,z402,z3,z5,z6])],[(0,[z55,z0,z344,z2,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z403,z6]),(0,[z0,z1,z2,z104,z3,z5,z140])],[(0,[z0,z1,z2,z3,z5,z6,z102]),(0,[z0,z43,z2,z299,z3,z5,z6]),(0,[z0,z1,z2,z404,z3,z5,z6]),(0,[z405,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z406])],[(0,[z407,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z408,z2,z3,z5,z6]),(0,[z409,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z410,z6]),(0,[z0,z1,z2,z3,z39,z6,z17]),(0,[z0,z1,z2,z3,z411,z5,z6])],[(0,[z412,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z413,z6]),(0,[z211,z0,z43,z2,z3,z5,z6]),(0,[z0,z1,z414,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z415,z6]),(0,[z416,z0,z1,z2,z3,z5,z6])],[(0,[z0,z43,z2,z92,z3,z5,z6]),(0,[z211,z0,z48,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z417,z5,z6])],[(0,[z0,z1,z418,z2,z3,z5,z6]),(0,[z87,z1,z2,z3,z5,z26,z6]),(0,[z0,z1,z2,z3,z419,z5,z6]),(0,[z420,z0,z1,z2,z3,z5,z6]),(1,[z51,z0,z2,z3,z5,z232])]],
   [[(0,[z0,z1,z2,z3,z5,z232,z112]),(0,[z0,z1,z2,z421,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z19]),(0,[z0,z1,z2,z3,z422,z5,z6])],[(0,[z0,z22,z1,z137,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z5,z17])],[(0,[z423,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z101,z6]),(0,[z424,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z425,z5,z6]),(0,[z0,z1,z426,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z427,z6]),(0,[z0,z1,z2,z3,z5,z6,z428]),(0,[z94,z0,z1,z2,z3,z5,z269]),(0,[z116,z0,z1,z2,z104,z3,z5]),(0,[z215,z0,z1,z2,z3,z81,z6]),(0,[z0,z429,z1,z2,z3,z5,z6])],[],[(1,[z63,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z430]),(0,[z0,z431,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z432])],[(0,[z190,z0,z127,z2,z3,z5,z6]),(0,[z433,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z434,z3,z5,z6]),(1,[z0,z1,z2,z3,z260,z6]),(0,[z0,z1,z2,z3,z157,z85,z6])],[(0,[z0,z1,z2,z3,z5,z435,z6]),(0,[z0,z235,z1,z2,z3,z5,z232]),(0,[z0,z1,z2,z103,z3,z5,z6])]],
   [[(1,[z0,z150,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z117,z6,z269]),(0,[z0,z1,z2,z3,z5,z6,z436]),(1,[z0,z1,z2,z134,z25,z6])],[(0,[z0,z66,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z437])],[(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z3,z222,z5])],[(0,[z0,z439,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z440,z6])],[(0,[z0,z1,z2,z3,z5,z441,z6]),(0,[z0,z442,z1,z2,z3,z5,z6])],[(0,[z215,z0,z1,z2,z3,z157,z6])],[],[(0,[z0,z1,z2,z3,z5,z443,z6])]],
   [[(0,[z0,z1,z444,z2,z3,z5,z6]),(0,[z111,z0,z1,z2,z3,z5,z6]),(0,[z445,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z446,z6]),(0,[z94,z0,z1,z2,z3,z5,z91]),(0,[z0,z1,z2,z3,z222,z5,z17])],[(0,[z0,z127,z43,z2,z3,z5,z6]),(0,[z447,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z448]),(0,[z0,z1,z2,z449,z3,z5,z6])],[(0,[z0,z1,z2,z3,z403,z5,z6]),(0,[z0,z1,z2,z450,z3,z5,z6])],[(0,[z0,z2,z92,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z451,z5,z6]),(0,[z0,z1,z2,z92,z9,z5,z6]),(0,[z0,z1,z2,z134,z3,z5,z6])],[(0,[z63,z1,z2,z137,z3,z5,z6]),(0,[z0,z1,z2,z452,z3,z5,z6]),(1,[z0,z1,z2,z104,z5,z140])],[(0,[z0,z453,z1,z2,z3,z5,z6]),(0,[z0,z1,z454,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z455,z6])],[(1,[z0,z1,z2,z3,z403,z6]),(0,[z0,z1,z2,z3,z5,z6,z456])]],
   [[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z457,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z148,z6]),(0,[z0,z1,z2,z3,z458,z5,z6])],[(0,[z0,z1,z459,z2,z3,z5,z6]),(0,[z76,z0,z1,z137,z3,z5,z6]),(0,[z0,z1,z2,z460,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z461,z6]),(0,[z0,z22,z1,z43,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z462,z6]),(0,[z0,z88,z1,z2,z3,z239,z6]),(0,[z0,z1,z463,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z464,z5,z6])],[(0,[z0,z1,z2,z186,z3,z5,z6]),(0,[z465,z0,z1,z2,z3,z5,z6]),(0,[z0,z22,z1,z299,z3,z5,z6]),(0,[z0,z1,z466,z2,z3,z5,z6]),(0,[z467,z0,z1,z2,z3,z5,z6])],[(0,[z76,z63,z1,z2,z3,z5,z6]),(0,[z0,z468,z1,z2,z3,z5,z6]),(0,[z0,z469,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z183]),(0,[z132,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z49,z5,z6]),(0,[z0,z470,z1,z2,z3,z5,z6]),(0,[z471,z0,z1,z2,z3,z5,z6]),(0,[z0,z38,z1,z2,z3,z5,z256]),(0,[z0,z1,z472,z2,z3,z5,z6])],[(0,[z473,z0,z1,z2,z3,z5,z6]),(1,[z138,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z5,z91])],[(0,[z1,z127,z2,z137,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z474,z5,z6]),(0,[z475,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z476,z5,z6]),(0,[z0,z1,z2,z3,z477,z5,z6]),(0,[z0,z1,z478,z2,z3,z5,z6])],[(0,[z94,z1,z2,z3,z5,z6,z269])],[(0,[z479,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z480,z2,z3,z5,z6]),(0,[z42,z0,z2,z299,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z481,z6]),(1,[z386,z1,z2,z3,z5,z6])]],
   [[(0,[z87,z0,z1,z2,z3,z26,z6])],[(0,[z0,z1,z2,z3,z5,z482,z6]),(0,[z483,z0,z1,z2,z3,z5,z6]),(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z485,z5,z6]),(0,[z0,z486,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z136,z6])],[(0,[z0,z1,z127,z2,z3,z5,z6]),(0,[z487,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z488,z3,z5,z6]),(0,[z489,z0,z1,z2,z3,z5,z6]),(0,[z0,z38,z1,z2,z3,z91,z6])],[(1,[z0,z344,z2,z3,z5,z6]),(0,[z87,z0,z38,z1,z2,z3,z6]),(0,[z0,z490,z1,z2,z3,z5,z6]),(0,[z0,z491,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z492])],[(0,[z0,z48,z127,z2,z3,z5,z6]),(0,[z94,z0,z1,z2,z3,z5,z117]),(0,[z0,z1,z2,z3,z5,z6,z493]),(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z495,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z496,z3,z5,z6]),(0,[z0,z1,z2,z497,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z498,z6]),(0,[z185,z0,z1,z2,z3,z5,z6]),(1,[z211,z0,z2,z50,z5,z6]),(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z500]),(0,[z0,z1,z2,z3,z5,z501,z6])],[(0,[z0,z204,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z210])],[(0,[z0,z1,z2,z3,z502,z5,z6]),(0,[z0,z329,z1,z2,z3,z5,z6]),(0,[z185,z1,z2,z186,z3,z5,z6]),(0,[z0,z503,z1,z2,z3,z5,z6]),(0,[z0,z48,z1,z2,z92,z5,z6]),(1,[z0,z1,z58,z103,z5,z6]),(0,[z0,z1,z2,z504,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z505,z6]),(1,[z55,z1,z2,z56,z5,z6]),(0,[z0,z1,z2,z103,z50,z5,z6]),(0,[z0,z1,z2,z3,z506,z5,z6]),(0,[z0,z1,z507,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z222,z91,z6])],[(0,[z0,z1,z2,z508,z3,z5,z6]),(0,[z0,z1,z2,z509,z3,z5,z6]),(0,[z0,z1,z2,z3,z510,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z511]),(0,[z0,z1,z2,z3,z512,z5,z6]),(0,[z0,z1,z2,z3,z5,z513,z6]),(0,[z0,z1,z2,z3,z5,z6,z514]),(0,[z0,z1,z2,z3,z5,z6,z246]),(1,[z34,z0,z1,z9,z5,z6]),(0,[z0,z1,z214,z3,z5,z81,z6]),(0,[z353,z1,z2,z3,z5,z39,z6])],[(0,[z515,z0,z1,z2,z3,z5,z6]),(0,[z516,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z517,z3,z5,z6]),(0,[z0,z1,z2,z518,z3,z5,z6]),(1,[z0,z1,z214,z3,z81,z6])],[(0,[z55,z0,z1,z2,z3,z5,z448]),(0,[z0,z1,z2,z79,z3,z26,z6]),(0,[z0,z1,z2,z519,z3,z5,z6]),(0,[z0,z1,z2,z3,z25,z148,z6]),(0,[z520,z0,z1,z2,z3,z5,z6]),(0,[z0,z521,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z343,z6])],[(0,[z185,z0,z1,z2,z186,z5,z6]),(0,[z0,z1,z2,z3,z522,z5,z6])],[(0,[z63,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z523,z3,z5,z6]),(0,[z0,z1,z2,z3,z32,z5,z6]),(0,[z0,z2,z3,z5,z232,z6,z246]),(0,[z304,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z5,z6]),(1,[z0,z1,z2,z3,z5,z256])],[(0,[z524,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z56,z5,z6]),(0,[z0,z1,z525,z2,z3,z5,z6]),(0,[z1,z2,z186,z3,z148,z5,z6]),(0,[z87,z16,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z526]),(0,[z0,z1,z2,z79,z3,z5,z117]),(0,[z0,z1,z2,z3,z5,z527,z6]),(0,[z528,z0,z1,z2,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z104,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z140,z6])]],
   [[(0,[z0,z1,z128,z2,z3,z5,z6]),(0,[z530,z0,z1,z2,z3,z5,z6])],[(0,[z531,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z532])],[(0,[z0,z1,z2,z3,z157,z239,z6]),(0,[z0,z1,z533,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z534]),(0,[z0,z1,z2,z3,z535,z5,z6]),(0,[z76,z0,z99,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z116,z0,z1,z2,z3,z5,z91]),(0,[z0,z536,z1,z2,z3,z5,z6])],[(0,[z0,z1,z537,z2,z3,z5,z6]),(0,[z538,z0,z1,z2,z3,z5,z6]),(0,[z539,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z540,z3,z5,z6]),(1,[z0,z1,z2,z3,z222,z91])],[(0,[z0,z541,z1,z2,z3,z5,z6]),(0,[z542,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z543,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z136,z39,z6])],[(0,[z0,z1,z2,z3,z544,z5,z6]),(0,[z42,z0,z1,z2,z545,z5,z6]),(0,[z0,z1,z2,z546,z3,z5,z6])],[(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z547,z0,z1,z2,z3,z5,z6]),(0,[z0,z329,z1,z2,z3,z56,z5]),(0,[z0,z548,z1,z2,z3,z5,z6]),(1,[z215,z0,z1,z3,z157,z6]),(0,[z549,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z550,z5,z6]),(0,[z0,z1,z2,z3,z5,z315,z6]),(0,[z0,z1,z2,z3,z5,z6,z551])]],
   [[(0,[z0,z1,z2,z3,z25,z5,z6])],[(0,[z0,z1,z2,z3,z552,z5,z6]),(0,[z0,z553,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z97,z3,z6,z20])],[(0,[z0,z1,z2,z3,z554,z5,z6]),(0,[z0,z1,z2,z555,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z5,z6]),(0,[z42,z0,z22,z2,z3,z5,z6]),(0,[z238,z0,z88,z2,z3,z5,z6]),(0,[z0,z1,z2,z556,z3,z5,z6]),(0,[z238,z0,z2,z3,z239,z5,z6]),(0,[z0,z1,z2,z557,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z20,z17])],[(0,[z0,z1,z2,z558,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z213,z6]),(0,[z0,z1,z2,z3,z5,z91,z20]),(0,[z0,z559,z1,z2,z3,z5,z6])],[(0,[z0,z38,z1,z2,z3,z39,z6])],[(0,[z0,z1,z2,z3,z5,z560,z6]),(0,[z238,z0,z1,z2,z3,z85,z6]),(0,[z0,z1,z2,z3,z561,z5,z6]),(1,[z0,z38,z1,z2,z39,z6]),(1,[z0,z131,z1,z2,z5,z20])],[(0,[z0,z1,z2,z229,z3,z5,z6]),(0,[z562,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z563])]],
   [[(1,[z0,z48,z2,z92,z5,z6]),(0,[z0,z1,z2,z134,z3,z25,z6])],[(0,[z76,z1,z127,z2,z3,z5,z6]),(0,[z564,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z148,z5,z26,z6]),(0,[z111,z0,z1,z3,z5,z37,z6]),(0,[z0,z1,z2,z3,z565,z5,z6]),(0,[z0,z1,z2,z5,z140,z6,z20])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z26,z6]),(0,[z0,z566,z1,z2,z3,z5,z6])],[(0,[z0,z60,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z567,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z568]),(0,[z0,z1,z2,z3,z222,z39,z6]),(0,[z0,z1,z2,z3,z222,z5,z91]),(0,[z569,z0,z1,z2,z3,z5,z6])],[(0,[z570,z0,z1,z2,z3,z5,z6]),(0,[z42,z0,z1,z299,z3,z5,z6]),(0,[z211,z0,z2,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z571,z5,z6])],[(0,[z572,z0,z1,z2,z3,z5,z6]),(0,[z573,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z183]),(1,[z0,z1,z2,z545,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z246]),(0,[z0,z1,z574,z2,z3,z5,z6])],[(0,[z116,z0,z1,z2,z3,z5,z117]),(0,[z0,z1,z2,z104,z3,z222,z5])],[(0,[z13,z1,z2,z137,z3,z5,z6]),(0,[z0,z575,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z576,z3,z5,z6])],[(0,[z0,z1,z2,z3,z577,z5,z6])],[(0,[z578,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z579,z6]),(0,[z580,z0,z1,z2,z3,z5,z6]),(1,[z0,z88,z2,z3,z85,z6])],[(0,[z0,z1,z2,z3,z581,z5,z6]),(0,[z0,z1,z2,z582,z3,z5,z6]),(0,[z55,z0,z1,z389,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z203]),(0,[z34,z0,z22,z1,z3,z5,z6]),(0,[z583,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z584,z5,z6]),(0,[z0,z1,z2,z3,z5,z585,z6]),(0,[z0,z1,z2,z3,z5,z6,z282]),(0,[z0,z1,z2,z3,z222,z5,z6])],[(0,[z586,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z587,z5,z6]),(0,[z0,z1,z58,z137,z3,z5,z6]),(0,[z116,z0,z131,z1,z2,z3,z5]),(0,[z0,z22,z1,z103,z3,z5,z6]),(0,[z0,z1,z2,z588,z3,z5,z6]),(0,[z0,z1,z2,z3,z589,z5,z6])],[(0,[z190,z63,z1,z2,z3,z5,z6]),(0,[z590,z0,z1,z2,z3,z5,z6]),(0,[z591,z0,z1,z2,z3,z5,z6])],[(0,[z592,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z6])],[]],
   [[(0,[z63,z0,z1,z229,z3,z5,z6]),(1,[z0,z1,z2,z3,z179,z6]),(0,[z0,z1,z214,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z5,z323,z6]),(0,[z0,z1,z2,z3,z5,z6,z593])],[(0,[z0,z594,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z595,z6])],[(0,[z0,z1,z596,z2,z3,z5,z6]),(0,[z597,z0,z1,z2,z3,z5,z6]),(0,[z598,z0,z1,z2,z3,z5,z6])],[(0,[z0,z599,z1,z2,z3,z5,z6]),(0,[z0,z600,z1,z2,z3,z5,z6]),(0,[z353,z0,z1,z2,z3,z5,z6]),(0,[z0,z601,z1,z2,z3,z5,z6])],[(0,[z602,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z603,z6])],[(0,[z42,z0,z204,z2,z3,z5,z6]),(0,[z1,z2,z186,z3,z56,z5,z6]),(0,[z0,z1,z2,z604,z3,z5,z6])],[(0,[z0,z1,z2,z3,z605,z5,z6]),(0,[z0,z1,z2,z3,z222,z5,z117]),(0,[z211,z0,z1,z2,z92,z5,z6]),(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z607,z3,z5,z6])],[(0,[z0,z1,z2,z3,z608,z5,z6]),(0,[z0,z1,z609,z2,z3,z5,z6]),(0,[z610,z0,z1,z2,z3,z5,z6]),(0,[z611,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z398,z3,z5,z39]),(0,[z0,z612,z1,z2,z3,z5,z6])]],
   [[(0,[z613,z0,z1,z2,z3,z5,z6]),(0,[z0,z99,z1,z2,z3,z5,z6]),(0,[z76,z0,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z2,z3,z5,z117,z6]),(0,[z0,z1,z2,z615,z3,z5,z6]),(0,[z0,z1,z616,z2,z3,z5,z6]),(0,[z0,z1,z2,z617,z3,z5,z6]),(0,[z0,z1,z2,z618,z3,z5,z6]),(0,[z0,z1,z2,z619,z3,z5,z6])],[(0,[z0,z1,z620,z2,z3,z5,z6]),(0,[z0,z1,z2,z621,z3,z56,z6]),(0,[z0,z1,z2,z3,z545,z5,z6]),(0,[z0,z1,z2,z3,z622,z5,z6])],[(0,[z0,z623,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z624,z5,z6]),(0,[z0,z1,z2,z3,z5,z625,z6]),(0,[z0,z1,z214,z2,z3,z157,z6])],[(0,[z626,z0,z1,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z627,z5,z6])],[(0,[z0,z1,z2,z3,z5,z100,z6]),(0,[z94,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z628,z6])],[],[(0,[z0,z1,z629,z2,z3,z5,z6]),(0,[z94,z1,z2,z186,z3,z5,z6])],[(0,[z116,z94,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z630,z3,z5,z6])]],
   [[(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z631,z2,z3,z5,z6]),(0,[z632,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z633,z5,z6]),(0,[z0,z1,z2,z634,z3,z5,z6]),(0,[z635,z0,z1,z2,z3,z5,z6])],[(0,[z215,z0,z1,z214,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z19])],[(0,[z636,z0,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z56,z5,z6]),(0,[z0,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z168,z6]),(0,[z0,z1,z2,z3,z5,z6,z637]),(0,[z0,z1,z2,z3,z638,z5,z6])],[(0,[z55,z1,z2,z3,z148,z5,z6]),(0,[z0,z1,z2,z3,z639,z5,z6]),(0,[z16,z0,z1,z2,z134,z3,z6]),(0,[z16,z0,z1,z2,z3,z222,z6]),(1,[z0,z1,z2,z3,z5,z102])],[(0,[z0,z1,z640,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z641,z5,z6])],[(0,[z55,z0,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z448,z6]),(0,[z0,z1,z2,z642,z3,z5,z6]),(0,[z111,z0,z1,z2,z3,z5,z37])],[(0,[z0,z1,z2,z3,z5,z643,z6]),(0,[z0,z1,z644,z2,z3,z5,z6]),(1,[z94,z1,z2,z3,z5,z269]),(0,[z0,z22,z43,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z645,z5,z6]),(0,[z0,z1,z2,z3,z5,z646,z6]),(0,[z0,z1,z2,z3,z647,z5,z6])]],
   [[(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z649,z0,z1,z2,z3,z5,z6]),(0,[z0,z650,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z651]),(1,[z0,z1,z2,z79,z3,z17])],[(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z652,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z286]),(0,[z0,z1,z2,z3,z653,z5,z6]),(0,[z0,z1,z2,z654,z3,z5,z6]),(0,[z0,z1,z2,z655,z3,z5,z6])],[(0,[z238,z0,z1,z2,z3,z239,z6]),(0,[z0,z1,z2,z3,z5,z37,z232]),(0,[z0,z1,z58,z2,z3,z5,z6]),(0,[z215,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z157,z5,z6])],[(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z657,z5,z6]),(0,[z0,z1,z2,z3,z658,z5,z6])],[(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z42,z0,z127,z2,z3,z5,z6]),(0,[z660,z0,z1,z2,z3,z5,z6]),(0,[z661,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z662]),(0,[z0,z1,z2,z104,z5,z140,z6])],[(0,[z0,z204,z43,z2,z3,z5,z6]),(0,[z94,z0,z131,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z663,z6]),(0,[z0,z1,z664,z2,z3,z5,z6])],[(0,[z0,z204,z48,z2,z3,z5,z6]),(0,[z42,z0,z1,z137,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z665]),(0,[z0,z1,z2,z3,z5,z323,z39])]],
   [[(0,[z16,z1,z2,z3,z148,z5,z6]),(0,[z0,z131,z1,z2,z79,z3,z5])],[(0,[z0,z1,z2,z666,z3,z5,z6]),(0,[z0,z1,z667,z2,z3,z5,z6]),(0,[z0,z1,z2,z668,z3,z5,z6]),(0,[z669,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z103,z3,z9,z5,z6])],[(0,[z0,z1,z670,z2,z3,z5,z6]),(0,[z55,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z671]),(0,[z0,z672,z1,z2,z3,z5,z6])],[(0,[z673,z0,z1,z2,z3,z5,z6]),(0,[z190,z1,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z674,z3,z5,z6]),(0,[z55,z0,z1,z128,z3,z5,z6]),(0,[z0,z1,z2,z3,z675,z5,z6]),(0,[z0,z1,z2,z3,z5,z676,z6]),(0,[z0,z1,z677,z2,z3,z5,z6]),(0,[z0,z1,z36,z2,z3,z5,z6]),(0,[z678,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z389,z3,z5,z6]),(0,[z0,z679,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z239,z81,z6]),(0,[z34,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z680,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z168]),(1,[z304,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z681,z5,z6])],[(0,[z0,z1,z14,z2,z3,z5,z6]),(1,[z0,z1,z2,z621,z3,z6]),(0,[z0,z1,z2,z3,z5,z682,z6]),(0,[z0,z1,z683,z2,z3,z5,z6]),(0,[z0,z1,z2,z684,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z685,z5,z6]),(0,[z686,z0,z1,z2,z3,z5,z6]),(0,[z687,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z688,z6]),(0,[z0,z1,z2,z3,z5,z232,z6]),(0,[z0,z1,z2,z3,z5,z6,z112]),(0,[z386,z1,z2,z3,z5,z6,z20])],[(0,[z0,z1,z2,z3,z5,z689,z6]),(0,[z0,z1,z2,z690,z3,z5,z6]),(0,[z0,z1,z2,z3,z691,z5,z6])],[(0,[z0,z1,z2,z25,z5,z39,z6])],[(0,[z116,z1,z2,z3,z5,z117,z6]),(0,[z692,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z693,z6]),(0,[z0,z1,z2,z3,z5,z694,z6]),(0,[z0,z1,z2,z398,z3,z5,z6])],[(0,[z695,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z696,z5,z6]),(0,[z0,z1,z2,z621,z3,z5,z6]),(0,[z0,z1,z2,z65,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z697,z6])],[(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z55,z185,z1,z2,z3,z5,z6]),(1,[z0,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z5,z699,z6])],[(0,[z0,z1,z2,z3,z5,z700,z6]),(0,[z1,z2,z186,z3,z5,z117,z6]),(0,[z1,z2,z3,z5,z6,z282,z20])],[(0,[z701,z0,z1,z2,z3,z5,z6]),(0,[z63,z204,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z702]),(0,[z0,z1,z2,z3,z5,z703,z6]),(0,[z0,z1,z2,z3,z5,z704,z6]),(0,[z705,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z5,z707]),(0,[z0,z1,z128,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z708]),(0,[z0,z1,z2,z3,z709,z6])],[(0,[z0,z1,z2,z3,z25,z256]),(0,[z0,z1,z2,z3,z5,z710])],[(0,[z0,z1,z2,z711,z3,z6]),(0,[z0,z1,z712,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z73]),(0,[z0,z2,z3,z5,z713,z6]),(0,[z0,z714,z2,z3,z5,z6])],[(0,[z0,z1,z2,z715,z3,z6]),(0,[z0,z1,z2,z144,z5,z168]),(0,[z0,z1,z2,z3,z5,z716]),(0,[z0,z1,z2,z717,z3,z5])],[(0,[z0,z1,z2,z718,z5,z6]),(0,[z0,z1,z2,z194,z5,z140])],[(0,[z0,z1,z2,z3,z5,z719]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z531,z0,z1,z3,z5,z37])],[(0,[z0,z721,z2,z3,z5,z6]),(0,[z0,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z723]),(0,[z0,z1,z2,z3,z5,z724]),(0,[z0,z1,z2,z3,z32,z168]),(0,[z304,z0,z103,z3,z5,z6]),(0,[z725,z1,z2,z3,z5,z6])],[(0,[z0,z1,z58,z434,z5,z6])]],
   [[(0,[z0,z48,z2,z726,z5,z6]),(0,[z1,z2,z398,z3,z5,z136]),(0,[z0,z1,z2,z3,z6,z19])],[(0,[z138,z0,z204,z3,z5,z6]),(0,[z0,z1,z2,z3,z39,z183])],[(0,[z63,z204,z64,z3,z5,z6]),(0,[z0,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z5,z102]),(0,[z727,z1,z2,z3,z5,z6]),(0,[z0,z1,z58,z728,z5,z6]),(0,[z0,z1,z3,z729,z5,z6]),(0,[z0,z1,z2,z3,z315,z140])],[(1,[z0,z2,z3,z5,z730]),(0,[z34,z0,z8,z9,z5,z6])],[(0,[z132,z99,z2,z3,z5,z6]),(0,[z353,z1,z2,z3,z6,z17])],[(0,[z66,z1,z2,z3,z5,z168])],[(0,[z0,z1,z2,z3,z731,z6]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z0,z1,z2,z3,z5,z733]),(0,[z0,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z0,z1,z3,z157,z729,z6])],[(0,[z0,z1,z2,z3,z20,z210]),(0,[z735,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z736,z6]),(0,[z0,z1,z2,z79,z3,z17])]],
   [[(0,[z132,z1,z2,z3,z5,z6]),(0,[z0,z737,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z738,z6]),(0,[z739,z1,z2,z3,z5,z6])],[(0,[z0,z38,z1,z2,z740,z6])],[(0,[z1,z712,z2,z3,z5,z6]),(0,[z185,z1,z2,z186,z5,z6]),(0,[z55,z329,z1,z2,z56,z5]),(0,[z0,z83,z1,z2,z39,z6]),(0,[z16,z0,z1,z2,z3,z183]),(0,[z42,z132,z299,z3,z5,z6]),(0,[z211,z0,z2,z545,z5,z6]),(0,[z0,z1,z2,z3,z741,z6]),(0,[z742,z1,z2,z3,z5,z6])],[(0,[z190,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z144,z32,z6]),(0,[z0,z2,z92,z726,z5,z6]),(0,[z0,z2,z3,z743,z85,z6]),(0,[z0,z1,z728,z9,z5,z6])],[(0,[z0,z744,z2,z3,z5,z6]),(0,[z55,z1,z2,z56,z213,z6]),(0,[z0,z1,z745,z3,z5,z6]),(0,[z0,z1,z2,z746,z3,z6]),(1,[z1,z2,z3,z5,z747]),(0,[z748,z1,z2,z3,z5,z6]),(0,[z749,z1,z2,z3,z5,z6]),(0,[z1,z2,z97,z3,z6,z282])],[(0,[z0,z750,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z751,z6])],[(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z0,z1,z2,z3,z26,z73]),(1,[z0,z1,z728,z5,z6])],[]],
   [[(0,[z60,z1,z2,z186,z3,z6])],[(0,[z16,z1,z2,z3,z148,z73]),(0,[z1,z2,z3,z6,z19,z282]),(0,[z0,z1,z2,z97,z3,z17])],[(0,[z66,z1,z2,z144,z5,z6]),(0,[z386,z1,z2,z97,z3,z6])],[(0,[z132,z1,z2,z3,z101,z6]),(0,[z132,z1,z2,z3,z5,z102]),(0,[z0,z754,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z755]),(0,[z569,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z5,z168]),(0,[z0,z1,z2,z3,z5,z756])],[(0,[z0,z1,z389,z3,z213,z6]),(0,[z1,z2,z3,z5,z757,z6]),(0,[z66,z1,z2,z3,z32,z6])],[(0,[z0,z1,z2,z3,z5,z758]),(0,[z0,z1,z2,z621,z3,z6]),(0,[z0,z1,z2,z759,z5,z6])],[(0,[z241,z0,z1,z9,z5,z6]),(0,[z0,z760,z2,z3,z5,z6]),(0,[z265,z0,z1,z2,z3,z17]),(0,[z1,z2,z3,z5,z747,z269]),(0,[z42,z0,z299,z3,z5,z168]),(0,[z211,z0,z49,z50,z5,z6]),(0,[z761,z1,z2,z3,z5,z6]),(0,[z304,z34,z0,z9,z5,z6]),(1,[z0,z1,z2,z5,z762])]],
   [[(0,[z0,z1,z763,z3,z5,z6]),(0,[z0,z1,z2,z3,z743,z6])],[(0,[z62,z0,z2,z50,z5,z6]),(0,[z0,z1,z2,z764,z3,z5]),(0,[z0,z1,z2,z765,z3,z5]),(0,[z0,z1,z2,z11,z25,z6]),(0,[z131,z1,z2,z5,z282,z20])],[(0,[z63,z99,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z167,z0,z2,z3,z5,z232]),(0,[z0,z38,z1,z2,z323,z39])],[(0,[z767,z1,z2,z3,z5,z6]),(0,[z238,z0,z2,z3,z239,z6]),(0,[z768,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z740,z6])],[(0,[z0,z1,z2,z769,z5,z6]),(1,[z0,z770,z3,z5,z6]),(0,[z0,z1,z2,z104,z5,z762])],[(0,[z1,z2,z3,z771,z5,z6])],[(0,[z0,z204,z64,z3,z5,z6]),(0,[z13,z1,z137,z3,z5,z6]),(0,[z0,z1,z2,z104,z5,z603])],[(0,[z0,z2,z92,z30,z5,z6])]],
   [[(0,[z0,z1,z2,z772,z3,z6])],[(0,[z116,z1,z2,z3,z117,z210]),(0,[z0,z1,z2,z144,z5,z6]),(0,[z211,z0,z2,z726,z5,z6]),(0,[z0,z1,z2,z97,z3,z256]),(0,[z0,z1,z2,z5,z762,z20]),(0,[z0,z1,z2,z3,z773,z17])],[(0,[z0,z1,z2,z774,z5,z6]),(0,[z775,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z776,z6])],[(0,[z0,z48,z2,z582,z5,z6]),(0,[z0,z1,z2,z3,z32,z6])],[(0,[z0,z1,z777,z3,z5,z6]),(0,[z0,z1,z2,z778,z5,z6]),(0,[z0,z1,z2,z3,z779,z6]),(0,[z0,z2,z3,z726,z5,z6]),(0,[z1,z2,z3,z5,z780,z6]),(0,[z781,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z782,z6])],[(0,[z0,z1,z2,z3,z783,z6]),(0,[z0,z1,z2,z784,z5,z6]),(0,[z785,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z222,z192]),(0,[z0,z1,z2,z619,z5,z140])],[(0,[z0,z1,z2,z3,z5,z786]),(0,[z329,z1,z2,z186,z3,z5]),(0,[z317,z0,z1,z3,z157,z6]),(0,[z0,z787,z2,z3,z5,z6]),(0,[z0,z1,z2,z398,z3,z315])]],
   [[(0,[z76,z1,z64,z3,z5,z6]),(0,[z0,z1,z788,z3,z5,z6]),(0,[z0,z789,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z790,z5])],[(0,[z0,z1,z2,z3,z791,z6]),(0,[z0,z60,z1,z2,z3,z6]),(0,[z0,z1,z792,z3,z5,z6]),(0,[z353,z1,z2,z134,z3,z6]),(0,[z353,z1,z2,z3,z222,z6])],[(0,[z76,z99,z14,z3,z5,z6])],[(0,[z66,z1,z2,z3,z5,z6]),(0,[z0,z1,z389,z3,z5,z203]),(0,[z0,z793,z2,z3,z5,z6]),(0,[z0,z794,z2,z3,z5,z6]),(0,[z0,z88,z2,z3,z743,z6])],[(0,[z0,z60,z329,z1,z2,z3]),(0,[z0,z1,z2,z3,z5,z795]),(0,[z0,z1,z2,z144,z101,z6]),(0,[z215,z0,z1,z3,z729,z6])],[(0,[z1,z2,z3,z148,z213,z6]),(0,[z0,z1,z2,z3,z796,z6]),(0,[z0,z1,z2,z3,z5,z286]),(0,[z1,z2,z3,z5,z6,z797]),(0,[z0,z38,z1,z2,z39,z256])],[(0,[z76,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z798,z6]),(0,[z0,z1,z364,z3,z5,z112])],[(0,[z0,z72,z2,z3,z213,z6]),(0,[z0,z131,z1,z2,z19,z20])]],
   [[(0,[z0,z1,z2,z799,z5,z6]),(0,[z549,z1,z2,z3,z148,z6])],[(0,[z0,z1,z2,z3,z5,z800])],[(0,[z0,z1,z2,z3,z5,z801]),(0,[z55,z1,z2,z56,z260,z6]),(0,[z87,z0,z1,z2,z3,z256]),(0,[z132,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z3,z802,z6]),(0,[z0,z1,z2,z803,z3,z6])],[(0,[z94,z1,z2,z306,z3,z5]),(0,[z0,z804,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z6])],[(0,[z0,z1,z2,z3,z222,z314])],[(0,[z0,z1,z2,z3,z5,z805]),(0,[z304,z0,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z806]),(0,[z0,z1,z2,z97,z3,z269]),(0,[z132,z1,z2,z3,z32,z6])],[(0,[z0,z99,z2,z3,z5,z6]),(0,[z1,z2,z186,z5,z6,z526]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z3,z5,z807]),(0,[z0,z1,z2,z3,z5,z808])],[(0,[z87,z1,z2,z3,z757,z6]),(0,[z0,z38,z1,z2,z398,z39]),(0,[z0,z1,z2,z3,z315,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z809])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z0,z811,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z117]),(0,[z0,z1,z2,z3,z403,z17]),(0,[z812,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z813,z6])],[(0,[z42,z294,z0,z3,z5,z6]),(0,[z0,z1,z814,z3,z5,z6]),(0,[z0,z1,z36,z3,z5,z112]),(0,[z0,z1,z2,z3,z5,z323])],[(0,[z0,z1,z815,z3,z5,z6]),(0,[z0,z1,z389,z3,z260,z6]),(0,[z0,z1,z2,z3,z816,z6])],[(0,[z0,z1,z2,z3,z213,z6])],[(0,[z0,z1,z128,z3,z213,z6]),(0,[z0,z329,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z817]),(0,[z0,z1,z2,z79,z3,z361]),(0,[z42,z0,z299,z3,z5,z6]),(0,[z0,z1,z2,z3,z818,z6])],[(0,[z0,z127,z2,z545,z5,z6]),(0,[z0,z1,z2,z3,z819,z6]),(0,[z55,z1,z2,z56,z5,z448]),(0,[z0,z329,z1,z2,z621,z3]),(0,[z111,z0,z1,z3,z5,z37]),(0,[z820,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z821,z5,z6]),(0,[z227,z127,z2,z3,z5,z6]),(0,[z0,z822,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z823]),(0,[z0,z1,z2,z3,z6,z824]),(0,[z0,z1,z2,z3,z5,z825])]],
   [[(0,[z0,z1,z2,z826,z3,z5]),(0,[z827,z1,z2,z3,z5,z6])],[(0,[z63,z828,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z829]),(0,[z16,z1,z2,z3,z148,z100]),(0,[z0,z2,z770,z3,z5,z6]),(0,[z0,z1,z3,z5,z830,z6]),(0,[z386,z1,z2,z3,z5,z17])],[],[(0,[z87,z1,z2,z3,z26,z6]),(0,[z386,z1,z2,z104,z3,z5])],[(0,[z583,z204,z2,z3,z5,z6]),(0,[z831,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z832,z6]),(0,[z0,z72,z2,z3,z5,z203]),(0,[z16,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z419,z91]),(0,[z0,z1,z2,z833,z5,z6])],[],[(0,[z0,z1,z2,z3,z5,z834]),(0,[z835,z0,z1,z3,z5,z6]),(0,[z0,z1,z389,z3,z5,z448]),(0,[z0,z1,z2,z3,z5,z836]),(0,[z185,z1,z2,z837,z5,z6])]],
   [[(0,[z16,z0,z1,z2,z3,z256]),(0,[z0,z1,z2,z3,z5,z838]),(0,[z42,z0,z299,z3,z101,z6]),(0,[z42,z0,z299,z3,z5,z102]),(0,[z0,z1,z2,z79,z3,z315])],[(0,[z0,z1,z2,z3,z839,z6]),(0,[z1,z2,z3,z840,z5,z6])],[(0,[z0,z841,z1,z2,z5,z6]),(0,[z842,z1,z2,z3,z5,z6])],[(0,[z116,z1,z2,z3,z5,z593]),(0,[z0,z1,z2,z398,z3,z222])],[(0,[z0,z1,z2,z3,z843,z6]),(0,[z844,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z183]),(0,[z0,z327,z2,z3,z85,z6]),(0,[z0,z1,z36,z3,z5,z813])],[(0,[z16,z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z3,z5,z730])],[(0,[z0,z2,z3,z845,z5,z6]),(0,[z0,z1,z2,z104,z3,z403]),(0,[z0,z846,z2,z3,z5,z6])],[(0,[z55,z344,z2,z56,z5,z6]),(0,[z0,z1,z2,z847,z5,z6]),(0,[z0,z1,z2,z3,z91,z773])]],
   [[(0,[z0,z1,z2,z848,z3,z6]),(0,[z445,z1,z2,z3,z148,z6])],[(0,[z0,z1,z2,z3,z5,z849])],[(0,[z0,z1,z2,z3,z5,z850]),(0,[z202,z1,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z203]),(0,[z42,z0,z103,z92,z5,z6]),(0,[z0,z2,z726,z50,z5,z6]),(0,[z0,z1,z2,z220,z3,z17])],[(0,[z0,z1,z2,z3,z5,z851]),(0,[z0,z1,z128,z3,z5,z203])],[(0,[z0,z60,z1,z2,z65,z3]),(0,[z0,z38,z1,z2,z3,z73]),(0,[z94,z0,z1,z2,z3,z210])],[(0,[z0,z1,z64,z3,z5,z6]),(0,[z0,z72,z2,z3,z260,z6]),(0,[z0,z1,z2,z3,z5,z852]),(0,[z0,z1,z2,z3,z853,z5])],[(0,[z0,z1,z2,z3,z5,z854]),(0,[z87,z1,z2,z400,z3,z6]),(0,[z0,z1,z2,z97,z3,z117]),(0,[z0,z1,z2,z3,z222,z773])],[(0,[z0,z99,z14,z3,z5,z6]),(0,[z0,z1,z2,z855,z3,z6]),(0,[z16,z1,z2,z3,z148,z183]),(0,[z0,z1,z2,z3,z856,z6])]],
   [[(0,[z0,z344,z389,z3,z5,z6]),(0,[z1,z2,z3,z148,z171,z6]),(0,[z0,z131,z1,z2,z244,z5]),(0,[z0,z857,z2,z3,z5,z6])],[(0,[z1,z2,z3,z837,z5,z6]),(0,[z0,z858,z2,z3,z5,z6])],[(0,[z0,z1,z859,z2,z3,z5]),(0,[z0,z1,z2,z3,z860,z6])],[(0,[z51,z0,z2,z3,z5,z232])],[(0,[z0,z1,z229,z3,z5,z6]),(0,[z0,z1,z2,z134,z740,z6])],[(0,[z0,z828,z2,z3,z5,z6]),(0,[z0,z1,z2,z861,z5,z6]),(1,[z1,z712,z3,z5,z6]),(0,[z0,z1,z2,z3,z403,z269]),(0,[z0,z22,z43,z3,z5,z6]),(0,[z862,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z863,z6]),(0,[z16,z1,z2,z684,z3,z6]),(0,[z0,z1,z2,z79,z3,z593])],[(0,[z1,z2,z3,z5,z864,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z865]),(0,[z0,z131,z1,z2,z355,z5])],[(0,[z0,z72,z2,z3,z5,z448]),(0,[z94,z429,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z866,z6]),(0,[z386,z131,z1,z2,z5,z20])],[(0,[z0,z1,z2,z3,z260,z6]),(0,[z0,z1,z2,z867,z3,z5]),(0,[z87,z566,z1,z2,z3,z6]),(0,[z116,z1,z2,z3,z106,z117])],[(0,[z0,z1,z128,z3,z260,z6]),(0,[z0,z1,z2,z3,z106,z6]),(0,[z0,z1,z2,z3,z73,z17]),(0,[z0,z1,z2,z5,z740,z6])],[],[(0,[z0,z868,z2,z3,z5,z6]),(0,[z1,z2,z186,z3,z106,z6]),(0,[z0,z1,z3,z869,z5,z6]),(0,[z386,z1,z2,z3,z5,z269]),(0,[z138,z0,z1,z545,z5,z6])],[(0,[z132,z1,z64,z3,z5,z6]),(0,[z0,z600,z1,z2,z5,z20]),(0,[z0,z1,z770,z3,z5,z6]),(0,[z870,z1,z2,z3,z5,z6])],[(0,[z0,z1,z871,z3,z5,z6]),(0,[z16,z1,z2,z3,z6,z593]),(0,[z0,z1,z2,z3,z369,z91]),(0,[z116,z0,z1,z2,z3,z210]),(0,[z445,z1,z2,z3,z5,z117]),(0,[z42,z0,z299,z144,z5,z6]),(0,[z0,z1,z2,z3,z91,z256])]],
   [[(0,[z0,z235,z2,z3,z5,z246]),(0,[z0,z672,z1,z2,z5,z20])],[(0,[z872,z0,z2,z3,z5,z6]),(0,[z0,z873,z1,z2,z3,z5]),(0,[z0,z1,z2,z545,z5,z102])],[(0,[z0,z1,z874,z3,z5,z6]),(0,[z0,z204,z2,z545,z5,z6]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z42,z0,z299,z3,z32,z6])],[(0,[z0,z1,z2,z3,z6,z876]),(0,[z0,z1,z2,z3,z403,z91])],[(0,[z132,z1,z14,z3,z5,z6]),(0,[z87,z1,z2,z3,z622,z6]),(0,[z877,z1,z2,z3,z5,z6]),(0,[z878,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z282]),(0,[z0,z1,z2,z3,z222,z210]),(0,[z0,z1,z214,z3,z729,z6]),(0,[z0,z1,z2,z3,z5,z762])],[(0,[z828,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z879,z6]),(1,[z0,z2,z726,z5,z6]),(0,[z0,z2,z3,z239,z743,z6])],[(0,[z0,z1,z2,z3,z5,z880]),(0,[z0,z1,z128,z3,z5,z448]),(0,[z0,z1,z2,z881,z3,z5])]],
   [[(0,[z0,z1,z882,z3,z5,z6]),(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z1,z2,z3,z884,z6]),(0,[z1,z2,z3,z5,z747,z6]),(0,[z0,z1,z3,z5,z6,z885])],[(0,[z0,z1,z2,z886,z3,z5]),(0,[z887,z1,z2,z3,z5,z6])],[(0,[z0,z888,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z73,z210]),(0,[z0,z1,z2,z3,z5,z773])],[(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z0,z1,z2,z891,z3,z6]),(0,[z386,z1,z2,z3,z5,z91])],[(0,[z55,z1,z2,z65,z56,z5]),(0,[z0,z1,z2,z3,z892,z6]),(0,[z238,z0,z2,z3,z743,z6])],[(0,[z0,z1,z893,z3,z5,z6]),(0,[z0,z1,z2,z3,z355,z17])],[(0,[z0,z894,z2,z3,z5,z6]),(0,[z94,z1,z2,z3,z5,z203]),(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z1,z2,z3,z729,z6])],[(0,[z0,z1,z3,z49,z5,z6]),(0,[z896,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z25,z183]),(0,[z897,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z6,z551])],[(0,[z55,z60,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z2,z3,z5,z899]),(0,[z0,z1,z2,z3,z900,z6])],[(0,[z0,z1,z901,z3,z5,z6]),(0,[z0,z1,z902,z3,z5,z6]),(0,[z0,z1,z2,z3,z260,z203]),(0,[z0,z131,z1,z2,z97,z3])],[(0,[z0,z1,z2,z3,z903,z6]),(0,[z16,z1,z2,z3,z148,z286]),(0,[z116,z1,z2,z607,z3,z5]),(0,[z304,z0,z2,z545,z5,z6]),(0,[z0,z1,z2,z545,z5,z168]),(0,[z0,z2,z3,z5,z6,z904]),(0,[z0,z1,z2,z740,z39,z6]),(0,[z0,z672,z1,z2,z79,z3])],[(0,[z353,z1,z2,z3,z148,z6]),(0,[z1,z2,z3,z5,z6,z905]),(1,[z0,z1,z2,z3,z773])],[(0,[z0,z1,z906,z3,z5,z6]),(0,[z0,z907,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z403,z117]),(0,[z0,z1,z3,z5,z813,z112])],[(0,[z0,z344,z2,z3,z5,z6]),(0,[z138,z0,z127,z3,z5,z6]),(0,[z0,z22,z387,z3,z5,z6]),(0,[z0,z1,z2,z837,z5,z6]),(0,[z0,z1,z3,z728,z5,z6])]],
   [[(0,[z0,z1,z908,z3,z5,z6]),(0,[z0,z344,z128,z3,z5,z6]),(0,[z87,z1,z2,z3,z213,z6])],[(0,[z0,z909,z2,z3,z5,z6]),(0,[z1,z2,z186,z837,z5,z6]),(0,[z211,z0,z2,z50,z5,z6]),(0,[z910,z1,z2,z3,z5,z6])],[(0,[z13,z1,z712,z3,z5,z6]),(0,[z0,z1,z2,z3,z39,z256])],[(0,[z0,z1,z137,z545,z5,z6]),(0,[z0,z2,z3,z5,z232,z730]),(0,[z0,z1,z58,z103,z5,z6]),(0,[z111,z0,z1,z3,z5,z813])],[(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z235,z2,z3,z5,z730]),(0,[z0,z2,z3,z5,z912,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z386,z1,z2,z3,z6,z19])],[(0,[z0,z1,z2,z3,z5,z914])],[(0,[z0,z1,z2,z3,z5,z915]),(0,[z55,z1,z2,z3,z5,z100]),(0,[z386,z1,z2,z3,z5,z117]),(0,[z34,z0,z1,z9,z5,z6]),(0,[z0,z1,z2,z97,z3,z91])],[(0,[z0,z1,z2,z3,z5,z916]),(0,[z1,z2,z3,z5,z117,z24]),(0,[z917,z1,z2,z3,z5,z6]),(0,[z0,z1,z214,z3,z81,z6])]],
   [[(0,[z353,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z1,z2,z919,z3,z5])],[(0,[z0,z2,z3,z5,z730,z6])],[(0,[z353,z1,z2,z3,z213,z6]),(0,[z0,z1,z2,z3,z5,z256])],[(0,[z0,z1,z2,z3,z6,z920]),(0,[z0,z1,z2,z545,z32,z6]),(0,[z921,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z922])],[(0,[z0,z1,z923,z3,z5,z6]),(0,[z55,z1,z2,z384,z5,z6]),(0,[z0,z1,z2,z924,z5,z6]),(0,[z0,z1,z2,z3,z5,z925]),(0,[z926,z1,z2,z3,z5,z6])],[(0,[z927,z1,z2,z3,z5,z6])],[(0,[z0,z928,z2,z3,z5,z6]),(0,[z0,z1,z2,z97,z3,z6])],[(0,[z0,z1,z2,z3,z929,z6])]],
   [[(0,[z0,z1,z930,z3,z5,z6]),(0,[z353,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z222,z91])],[(0,[z0,z1,z2,z3,z5,z931]),(0,[z0,z1,z2,z3,z932,z6]),(0,[z0,z1,z2,z3,z5,z813]),(0,[z0,z1,z2,z398,z134,z3])],[(0,[z0,z933,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z117,z203]),(0,[z66,z1,z2,z545,z5,z6]),(0,[z0,z934,z2,z3,z5,z6])],[(0,[z267,z1,z2,z3,z5,z269]),(0,[z935,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z215,z0,z1,z3,z157,z6]),(0,[z353,z38,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z937,z6]),(0,[z0,z1,z103,z728,z5,z6])],[(0,[z51,z0,z2,z3,z5,z730]),(0,[z938,z1,z2,z3,z5,z6])],[(0,[z939,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z183]),(0,[z0,z1,z2,z3,z5,z940]),(0,[z941,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z343]),(0,[z0,z1,z2,z398,z3,z5])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z1,z2,z3,z5,z943]),(0,[z0,z1,z2,z3,z213,z203]),(0,[z0,z131,z1,z2,z3,z403]),(0,[z944,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z422,z91])]],
   [[(0,[z0,z1,z945,z3,z5,z6]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z304,z34,z0,z3,z5,z6])],[(0,[z539,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z948]),(1,[z1,z2,z3,z757,z6])],[(0,[z0,z1,z949,z2,z3,z6]),(0,[z0,z1,z2,z950,z3,z6]),(0,[z0,z38,z1,z2,z39,z6])],[(0,[z76,z150,z14,z3,z5,z6]),(0,[z42,z0,z373,z3,z5,z6]),(0,[z0,z1,z103,z653,z5,z6]),(0,[z0,z1,z3,z729,z81,z6])],[(0,[z0,z1,z2,z951,z5,z6]),(0,[z1,z14,z712,z3,z5,z6]),(0,[z55,z1,z2,z244,z5,z6]),(0,[z952,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z953,z3,z5]),(0,[z0,z38,z1,z2,z355,z6])],[(0,[z0,z1,z2,z134,z522,z6]),(0,[z42,z66,z299,z3,z5,z6]),(0,[z954,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z1,z2,z3,z222,z315])]],
   [[(0,[z55,z1,z389,z56,z5,z6]),(0,[z55,z1,z2,z621,z56,z6]),(0,[z0,z1,z957,z3,z5,z6]),(0,[z0,z38,z1,z2,z398,z3])],[(0,[z0,z958,z2,z3,z5,z6]),(0,[z0,z1,z2,z545,z5,z6])],[(0,[z42,z0,z395,z3,z5,z6])],[(0,[z562,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z959]),(0,[z0,z1,z960,z3,z5,z6]),(0,[z961,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z398,z3,z17])],[(0,[z63,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z962,z3,z5]),(0,[z0,z1,z2,z25,z740,z6])],[(0,[z0,z1,z2,z3,z963,z6]),(0,[z132,z127,z2,z3,z5,z6]),(0,[z964,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z965])],[(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z967,z1,z2,z3,z6]),(0,[z42,z0,z404,z3,z5,z6]),(0,[z0,z22,z3,z476,z5,z6]),(0,[z0,z88,z2,z3,z85,z6])],[(0,[z0,z150,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z73]),(0,[z0,z1,z2,z3,z222,z73]),(0,[z0,z1,z2,z134,z25,z6])]],
   [[(0,[z0,z968,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z969,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z131,z1,z2,z5,z762])],[(0,[z0,z1,z2,z3,z5,z747]),(0,[z0,z1,z2,z104,z474,z5]),(0,[z0,z971,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z972,z6]),(0,[z0,z1,z2,z728,z5,z6]),(0,[z973,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z140,z762])],[(0,[z0,z1,z2,z3,z974,z6]),(0,[z0,z1,z466,z3,z81,z6])],[(0,[z516,z1,z137,z3,z5,z6]),(0,[z0,z975,z2,z3,z5,z6]),(0,[z0,z1,z2,z545,z101,z6])],[(0,[z0,z43,z770,z3,z5,z6]),(0,[z0,z1,z976,z3,z5,z6])],[(0,[z1,z64,z137,z3,z5,z6]),(0,[z204,z828,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z977,z5]),(0,[z211,z138,z0,z3,z5,z6]),(0,[z0,z1,z2,z978,z3,z6]),(0,[z0,z1,z2,z3,z6,z773])],[(0,[z181,z1,z137,z3,z5,z6]),(0,[z611,z0,z2,z3,z239,z6]),(0,[z0,z1,z2,z979,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z980]),(0,[z0,z1,z2,z3,z6,z981]),(0,[z38,z1,z2,z136,z39,z6])],[(0,[z42,z127,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z448]),(0,[z1,z2,z3,z757,z26,z6]),(0,[z0,z1,z2,z3,z5,z982]),(0,[z983,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z984])],[(0,[z0,z1,z2,z3,z5,z985]),(0,[z0,z1,z2,z3,z5,z986]),(0,[z0,z1,z2,z3,z5,z987]),(0,[z0,z1,z2,z3,z5,z988]),(0,[z132,z1,z2,z545,z5,z6]),(0,[z0,z2,z3,z743,z5,z6])],[(0,[z304,z0,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z213,z448]),(0,[z55,z60,z1,z2,z56,z6]),(0,[z55,z1,z2,z3,z106,z6])],[(0,[z0,z1,z2,z989,z3,z6]),(0,[z304,z0,z2,z92,z5,z6]),(0,[z0,z1,z2,z104,z5,z140])],[(0,[z0,z1,z2,z3,z6,z990]),(0,[z0,z1,z991,z3,z5,z6]),(0,[z94,z600,z1,z2,z3,z5]),(0,[z116,z1,z2,z3,z403,z117]),(0,[z0,z672,z1,z2,z39,z6]),(0,[z0,z1,z2,z79,z234,z3])],[(0,[z0,z1,z2,z3,z5,z992]),(0,[z0,z993,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z403,z6]),(0,[z87,z83,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z994]),(0,[z995,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z996]),(0,[z0,z2,z3,z997,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z998,z6]),(0,[z0,z1,z2,z726,z5,z6])],[(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z2,z3,z6,z1000])],[(0,[z0,z1,z2,z3,z1001,z6]),(0,[z55,z72,z2,z56,z5,z6]),(0,[z0,z1,z2,z3,z5,z1002]),(0,[z34,z0,z1,z728,z5,z6])],[(0,[z0,z1003,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1004]),(0,[z0,z1005,z2,z3,z5,z6]),(0,[z0,z1006,z2,z3,z5,z6]),(0,[z138,z0,z1,z3,z5,z6])],[(0,[z0,z38,z1,z2,z384,z6]),(0,[z0,z1,z2,z3,z1007,z6]),(0,[z0,z1,z2,z79,z3,z773])],[(0,[z0,z1,z2,z398,z3,z26]),(0,[z0,z1,z2,z3,z5,z1008])],[(0,[z0,z1,z2,z3,z5,z1009]),(0,[z386,z1,z2,z3,z5,z6]),(0,[z0,z1010,z2,z3,z5,z6]),(0,[z0,z1,z1011,z3,z5,z6]),(0,[z94,z1,z2,z3,z5,z93])],[(0,[z0,z1,z2,z1012,z3,z5])]],
   [[(1,[z828,z2,z3,z5,z6]),(0,[z42,z0,z452,z3,z5,z6]),(0,[z1,z2,z3,z5,z136,z6])],[(0,[z0,z1,z2,z3,z140,z210])],[(0,[z1013,z0,z1,z2,z5,z6]),(0,[z0,z1,z14,z545,z5,z6]),(0,[z0,z1,z2,z3,z5,z1014]),(0,[z1,z2,z186,z5,z688,z6]),(0,[z94,z1,z2,z3,z5,z269]),(0,[z0,z1,z3,z5,z37,z813])],[(0,[z0,z1,z2,z3,z1015,z6]),(0,[z0,z72,z389,z3,z5,z6]),(0,[z0,z2,z3,z5,z730,z246])],[(0,[z0,z344,z2,z3,z213,z6])],[(0,[z0,z1,z2,z3,z6,z210]),(0,[z0,z43,z3,z153,z5,z6]),(1,[z0,z1,z2,z740,z6])],[(0,[z63,z204,z229,z3,z5,z6]),(0,[z0,z1,z2,z3,z222,z57])],[(0,[z0,z1,z1016,z3,z5,z6]),(0,[z55,z1,z2,z56,z5,z6]),(0,[z0,z2,z3,z1017,z5,z6]),(0,[z0,z1,z1018,z3,z5,z6])]],
   [[(0,[z0,z1,z1019,z3,z5,z6]),(0,[z55,z1,z128,z56,z5,z6]),(0,[z0,z1,z2,z3,z403,z183]),(0,[z138,z0,z92,z3,z5,z6])],[(0,[z94,z0,z1,z2,z3,z315]),(0,[z445,z0,z1,z2,z3,z17])],[(0,[z1,z828,z2,z3,z5,z6]),(0,[z0,z629,z43,z3,z5,z6]),(0,[z0,z1,z2,z3,z101,z102])],[(0,[z0,z1,z2,z1020,z3,z6]),(0,[z353,z1,z2,z3,z5,z323])],[(0,[z0,z1,z2,z3,z1021,z6]),(0,[z1022,z0,z1,z2,z3,z6])],[(0,[z76,z1,z712,z3,z5,z6]),(0,[z94,z1,z2,z3,z5,z747]),(0,[z42,z0,z352,z3,z5,z6])],[(0,[z308,z1,z2,z3,z5,z117]),(0,[z0,z1,z103,z545,z5,z6]),(1,[z0,z2,z3,z743,z6])],[(0,[z1023,z0,z1,z2,z3,z6]),(0,[z55,z1,z2,z837,z5,z6]),(0,[z211,z138,z0,z50,z5,z6]),(0,[z386,z131,z1,z2,z3,z5]),(0,[z0,z1,z2,z97,z104,z3])]],
   [[(0,[z0,z1,z389,z3,z5,z6]),(0,[z55,z329,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1024,z6])],[(0,[z0,z1,z2,z3,z1025,z6]),(0,[z132,z204,z2,z3,z5,z6]),(0,[z304,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1026,z6]),(0,[z0,z22,z770,z3,z5,z6])],[(0,[z0,z1,z1027,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z210])],[(0,[z190,z828,z2,z3,z5,z6]),(0,[z99,z127,z2,z3,z5,z6]),(0,[z42,z0,z508,z3,z5,z6]),(0,[z0,z1,z683,z103,z5,z6]),(0,[z0,z1,z2,z79,z3,z256])],[(0,[z0,z99,z137,z3,z5,z6]),(0,[z322,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1028]),(0,[z1,z2,z3,z5,z323,z136])],[(0,[z386,z1,z2,z3,z5,z203]),(0,[z0,z1,z2,z287,z25,z6]),(0,[z0,z1,z2,z3,z5,z1029]),(0,[z0,z1,z2,z3,z5,z1030]),(0,[z0,z131,z1,z2,z40,z20])],[(0,[z0,z1,z2,z3,z222,z177])]],
   [[(0,[z1031,z1,z2,z3,z5,z6]),(0,[z1032,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1033,z6]),(0,[z0,z1,z2,z3,z260,z448]),(0,[z0,z2,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z344,z2,z3,z5,z203]),(1,[z0,z1,z3,z729,z6]),(0,[z0,z131,z1,z2,z315,z20])],[(0,[z0,z1,z2,z3,z1035,z6])],[(0,[z1,z2,z837,z56,z5,z6]),(0,[z116,z0,z1,z2,z3,z315]),(0,[z0,z1,z2,z3,z101,z168])],[(0,[z0,z131,z1,z2,z5,z20])],[(0,[z0,z1,z2,z398,z3,z148]),(0,[z1036,z1,z2,z3,z5,z6]),(0,[z1037,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1038,z6]),(0,[z55,z1,z2,z56,z5,z203]),(0,[z0,z1,z2,z3,z5,z1039]),(0,[z0,z48,z2,z92,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1040,z6]),(0,[z116,z1,z2,z3,z5,z747]),(0,[z1041,z0,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z97,z20])],[(0,[z42,z0,z546,z3,z5,z6]),(0,[z0,z442,z2,z3,z5,z246])],[(1,[z1,z2,z837,z5,z6]),(0,[z132,z1,z2,z3,z5,z168]),(0,[z0,z1,z2,z3,z315,z20])],[(0,[z0,z1,z1042,z3,z5,z6]),(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z770,z299,z3,z5,z6]),(0,[z0,z1,z1044,z3,z5,z6])],[(0,[z0,z1,z2,z5,z6,z1045]),(0,[z1,z2,z3,z148,z757,z6]),(0,[z353,z1,z2,z398,z3,z5])],[(0,[z1,z2,z3,z5,z6,z1046])],[(0,[z0,z1,z2,z3,z5,z1047]),(0,[z0,z1,z2,z3,z91,z183]),(0,[z1048,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1049]),(0,[z42,z0,z299,z545,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z353,z38,z1,z2,z39,z6])],[(0,[z1,z2,z3,z5,z117,z747]),(0,[z0,z1,z2,z144,z5,z102]),(0,[z0,z1,z3,z1051,z5,z6]),(0,[z1052,z1,z2,z3,z5,z6])],[(0,[z0,z72,z2,z3,z5,z6]),(0,[z132,z1,z137,z3,z5,z6]),(0,[z0,z344,z2,z3,z260,z6]),(0,[z0,z1,z2,z3,z5,z1053]),(0,[z0,z1,z2,z65,z3,z5])],[(0,[z0,z72,z128,z3,z5,z6]),(0,[z0,z1,z2,z65,z621,z3]),(0,[z0,z1,z2,z3,z1054,z6]),(0,[z0,z1,z1055,z3,z5,z6])],[(0,[z0,z1,z3,z1056,z5,z6]),(0,[z1,z712,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z32,z102]),(0,[z0,z553,z2,z92,z5,z6]),(0,[z1057,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z91,z436])],[(0,[z0,z1,z2,z3,z5,z1058])],[(0,[z0,z1,z2,z3,z1059,z6]),(0,[z0,z1060,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z179,z117])],[(0,[z0,z1,z2,z3,z179,z6]),(0,[z138,z0,z1,z103,z5,z6])]],
   [[],[(0,[z0,z1,z2,z5,z6,z762])],[(0,[z0,z127,z64,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1061]),(0,[z304,z0,z2,z50,z5,z6])],[(0,[z0,z1,z2,z3,z1062,z6]),(0,[z0,z1,z2,z3,z5,z1063]),(0,[z0,z1,z2,z3,z5,z100]),(0,[z66,z1,z2,z3,z101,z6]),(0,[z66,z1,z2,z3,z5,z102]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z0,z1,z2,z3,z5,z1065])],[(0,[z87,z0,z1,z2,z3,z183]),(0,[z0,z2,z92,z545,z5,z6]),(0,[z34,z0,z1,z545,z5,z6]),(0,[z0,z1,z2,z3,z1066,z6]),(0,[z42,z0,z770,z3,z5,z6])],[(0,[z1,z2,z186,z3,z5,z100]),(0,[z1067,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z5,z813])],[(0,[z0,z344,z2,z3,z5,z448]),(0,[z0,z1,z2,z3,z1068,z6]),(0,[z0,z1,z1069,z3,z5,z6]),(0,[z0,z38,z1,z2,z39,z343])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1070]),(0,[z0,z1,z1071,z3,z5,z6]),(0,[z138,z0,z1,z9,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 549) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 549).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1050)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [549, 501] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 158).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [158, 98] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_39023

theorem PEqualNP.Outside.L_meta_39023 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4241029256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4241029256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39023.solve