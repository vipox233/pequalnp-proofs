import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38023

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277061768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa0008084c088c2a0#64 ++ 0x2500040426044615#64 ++ 0xd829818fc199c7fb#64 ++ 0xbec14c0c7e0cce3f#64 : BitVec 256),
   (0x4002063202221d41#64 ++ 0x12001031901110ea#64 ++ 0xbc560e7206667fff#64 ++ 0xfde2b073903333ff#64 : BitVec 256),
   (0x8298b05c58786980#64 ++ 0x2414c582e2c3c34c#64 ++ 0x7398f07c78787997#64 ++ 0x6b9cc783e3c3c3cc#64 : BitVec 256),
   (0x0560db806f80760a#64 ++ 0x382b06dc037c03b0#64 ++ 0xf7e0ff807f807e0e#64 ++ 0xe7bf07fc03fc03f0#64 : BitVec 256),
   (0x01fd00003555000c#64 ++ 0x400fe80001aaa800#64 ++ 0xfbff00007fff801e#64 ++ 0x1fdff80003fffc00#64 : BitVec 256),
   (0x01ff6d6b0000000f#64 ++ 0x800ffb6b58000000#64 ++ 0xf5ffffff80000001#64 ++ 0xffaffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00007fff801e 0x1fdff80003fffc00

def z1 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff80000001 0xffaffffffc000000

def z2 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff807f807e0e 0xe7bf07fc03fc03f0

def z3 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc560e7206667fff 0xfde2b073903333ff

def z4 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c78787997 0x6b9cc783e3c3c3cc

def z5 : W := mkw 0x83fdb05c7d7d698c 0x641fed82e3ebeb4c 0x73b9f07c79f9f997 0x6b9dcf83e3cfcfcc

def z6 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd829818fc199c7fb 0xbec14c0c7e0cce3f

def z7 : W := mkw 0x0098000010500000 0x0004c00000828000 0x7398000078780016 0x0b9cc00003c3c000

def z8 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390707038603804 0x411c838381c301c0

def z9 : W := mkw 0x4000021002221d40 0x12000010801110ea 0x0800000006667ffe 0x00400000003333ff

def z10 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfbb9f1fff9f9ffff 0xffddcf8fffcfcfff

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0xd029818f80000001 0xbe814c0c7c000000

def z12 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27c07e003e003804 0x413e03f001f001c0

def z13 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x0200000079998000 0x0010000003cccc00

def z14 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x04000e7200007fe1 0xe0200073900003ff

def z15 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x2c560e7006667ffe 0x4162b073803333ff

def z16 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x24560e7006663804 0x4122b073803331c0

def z17 : W := mkw 0xe0008294c2aadfe0 0x37000414a61556ff 0x0800000047fffffe 0x00400000023fffff

def z18 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x25d67e7000000000 0x412eb3f380000000

def z19 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x080000004199c7fa 0x00400000020cce3f

def z20 : W := mkw 0x05604b002700140a 0x182b0258013800a0 0x04400e0006000000 0x0022007000300000

def z21 : W := mkw 0x2000008080808220 0x0100000404040411 0x8821018381818668 0x9441080c1c0c0c33

def z22 : W := mkw 0x05fddb807fd5760e 0x782feedc03feabb0 0xffffff807ffffe1e 0xfffffffc03fffff0

def z23 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xd429ffff80000001 0xfea14ffffc000000

def z24 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0xfbfff18dffff801e 0x1fdfff8c6ffffc00

def z25 : W := mkw 0x41fd021037771d4c 0x520fe81081bbb8ea 0xfbff00007ffffffe 0x1fdff80003ffffff

def z26 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e9ff8fff807e0f 0xffbf4ffc7ffc03f0

def z27 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x0400ffff80000001 0xe02007fffc000000

def z28 : W := mkw 0x40026f7b02221d43 0x9200137bd81110ea 0xbc56ffff86667fff 0xfde2b7fffc3333ff

def z29 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0800818fc199c7fb 0xa040040c7e0cce3f

def z30 : W := mkw 0x0000808040804200 0x2000040402040210 0xd02081804180460a 0xa681040c020c0230

def z31 : W := mkw 0x009d000010550004 0x4004e8000082a800 0x081f0000007f8010 0x1840f8000003fc00

def z32 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x7380f07c78007987 0x639c0783e3c003cc

def z33 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0000818f800047e1 0xa000040c7c00023f

def z34 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe9ff8fff99ffff 0xffff4ffc7ffccfff

def z35 : W := mkw 0xa09d8084d0ddc2a4 0x6504ec042686ee15 0xd83f818fc1ffc7fb 0xbec1fc0c7e0ffe3f

def z36 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0x8467ffff80000001 0xf4233ffffc000000

def z37 : W := mkw 0x0002043200200901 0x0000102190010048 0xb4560e7200607997 0xfda2b073900303cc

def z38 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x7388f00c78187806 0x639c478063c0c3c0

def z39 : W := mkw 0xa200b0dcc8a8eba0 0x25100586e645475d 0x0000f1ff80007fe1 0xe000078ffc0003ff

def z40 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc7f8fff86667fff 0xffe3fc7ffc3333ff

def z41 : W := mkw 0x05fddb807fd5760e 0x782feedc03feabb0 0xf7f6ff807fe67e0e 0xe7bfb7fc03ff33f0

def z42 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0x7598ffff80000001 0xebacc7fffc000000

def z43 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390707078787996 0x411c838383c3c3cc

def z44 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398f07c38603805 0x6b9cc783e1c301c0

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0x98000002000047fb 0xbcc000001000023f

def z46 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x6398f07c78783804 0x431cc783e3c3c1c0

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xd82900004199801a 0x1ec14800020ccc00

def z48 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0x41a9f18d80000000 0x020d4f8c6c000000

def z49 : W := mkw 0xa0000004800880a0 0x0500000024004405 0x0009000d80198000 0x000048006c00cc00

def z50 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x4388f00c78180000 0x021c478063c0c000

def z51 : W := mkw 0x8200901458786980 0x24100480a2c3c34c 0x0200000078787996 0x0010000003c3c3cc

def z52 : W := mkw 0x05654b802785160e 0x582b2a5c013c28b0 0x8c670f8007878608 0x9463387c003c3c30

def z53 : W := mkw 0x01ff246b0000000d 0x800ff92358000000 0xf1ff007f80000001 0x1f8ff803fc000000

def z54 : W := mkw 0x8000900448086080 0x2400048022404304 0x7388f00c78187997 0x6b9c478063c0c3cc

def z55 : W := mkw 0x0000001000200900 0x0000000080010048 0x2010007000603804 0x41008003800301c0

def z56 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffffff801f 0xfffffffffffffc00

def z57 : W := mkw 0x87fdfbdc7ffd7f8e 0x7c3fefdee3ffebfc 0xfffffffc7fffff9f 0xffffffffe3fffffc

def z58 : W := mkw 0x05ffffeb6f80760f 0xb82fffff5b7c03b0 0xf7ffffffff807e0f 0xffbffffffffc03f0

def z59 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x8c460e0206667ffe 0x94623070103333ff

def z60 : W := mkw 0x8298205c10780980 0x0414c102e083c04c 0x0018007c00780191 0x0800c003e003c00c

def z61 : W := mkw 0x41ff063237771d4d 0x520ff83191bbb8ea 0xffff0e727fffffff 0xfffff87393ffffff

def z62 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe0ff807f99fffe 0xe7ff07fc03fccfff

def z63 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e0ff803e003804 0xe7bf07fc01f001c0

def z64 : W := mkw 0xa298205c907889a0 0x0514c102e483c44d 0x0819007f807981f1 0x1840c803fc03cc0f

def z65 : W := mkw 0xa1608084e588c2a8 0x250b0404272c4615 0xfbe9818fff99c7ff 0xbfdf4c0c7ffcce3f

def z66 : W := mkw 0x0000008000800200 0x0000000400040010 0x8020018001800608 0x8401000c000c0030

def z67 : W := mkw 0x8298a05c50784980 0x2414c502e283c24c 0x5018807c40784193 0x2a80c403e203c20c

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x0809000000198010 0x184048000000cc00

def z69 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x23d600003e660004 0x011eb00001f33000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z71 : W := mkw 0x00024d2300000003 0x8000126918000000 0x04000f8380000000 0x8020007c1c000000

def z72 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfb98f07e78787fff 0xffdcc783f3c3c3ff

def z73 : W := mkw 0xa0000004800880a0 0x0500000024004405 0x9809000f8019c7fb 0xbcc048007c00ce3f

def z74 : W := mkw 0x83fffd7f5878698f 0xa41fffebfac3c34c 0xf7fffffff8787997 0xffbfffffffc3c3cc

def z75 : W := mkw 0xe562dfb6efaaffeb 0x3f2b16fdb77d57ff 0xffffffffffffffff 0xffffffffffffffff

def z76 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xa5f77ff380000000 0xd52fbbff9c000000

def z77 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0xf1ff000000000000 0x1f8ff80000000000

def z78 : W := mkw 0x0160000025000008 0x000b000001280000 0xf3e000007f80000e 0x079f000003fc0000

def z79 : W := mkw 0x01ff04223555000d 0x400ff82111aaa800 0xffff0e727fff801f 0xfffff87393fffc00

def z80 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0x04008fff80007fe1 0xe020047ffc0003ff

def z81 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x5808800c4199c7fb 0x2ac04400620cce3f

def z82 : W := mkw 0x0000900048006000 0x2000048002400300 0x7380f00078007806 0x639c078003c003c0

def z83 : W := mkw 0x87f8fbdc7ff87f8a 0x3c3fc7dee3ffc3fc 0xf7f8fffc7ff87f9f 0xefbfc7ffe3ffc3fc

def z84 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xb5d67e7200000001 0xfdaeb3f390000000

def z85 : W := mkw 0xa3fffdffd8f8ebaf 0xa51fffeffec7c75d 0xfffffffff9f9ffff 0xffffffffffcfcfff

def z86 : W := mkw 0xa1fde9cdc088c2ae 0xa50fef4e6e044615 0xd9a9f18fc199c7fb 0xbecd4f8c7e0cce3f

def z87 : W := mkw 0x01624d220000000b 0x000b126910000000 0xf5f6fff200000001 0xffafb7ff90000000

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x0009000f80000001 0x180048007c000000

def z89 : W := mkw 0xa4009284ef88f6a0 0x3d200494277c47b5 0x0a0000007f99fffe 0x0050000003fccfff

def z90 : W := mkw 0x0098205800200900 0x0004c102c0010048 0x7198f07c00607997 0x6b8cc783e00303cc

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0xb85600000666001e 0x1dc2b00000333000

def z92 : W := mkw 0x4002043200220941 0x020010219001104a 0x08160072006601f1 0x1840b0039003300f

def z93 : W := mkw 0x4562dfb26fa27f4b 0x3a2b16fd937d13fa 0xfff6fff27fe67fff 0xffffb7ff93ff33ff

def z94 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x73b9f1fdf9f9f997 0x6b9dcf8fefcfcfcc

def z95 : W := mkw 0x0000490000000002 0x0000024800000000 0x0400ff8000000000 0xe02007fc00000000

def z96 : W := mkw 0x01674d230000000f 0x800b3a6918000000 0xb4770ff380000001 0xfda3b87f9c000000

def z97 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xb7c07e003e007e0e 0xe5be03f001f003f0

def z98 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4029818dc1998000 0x02014c0c6e0ccc00

def z99 : W := mkw 0x016500000000000c 0x000b280000000000 0x8067000000000000 0x1403380000000000

def z100 : W := mkw 0x0160000025000008 0x000b000001280000 0xfbf600007fe6001e 0x1fdfb00003ff3000

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0xd020818000000000 0xa681040c00000000

def z102 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x65fffffd80000000 0x432fffffec000000

def z103 : W := mkw 0x829afd7f58786983 0xa414d7ebfac3c34c 0x7798fffff8787997 0xebbcc7ffffc3c3cc

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x3010007000000001 0x6980800380000000

def z105 : W := mkw 0x016500002505000c 0x400b280001282800 0x8867000007878008 0x14433800003c3c00

def z106 : W := mkw 0x8000800440084080 0x2400040022004204 0x5008800c40184193 0x2a8044006200c20c

def z107 : W := mkw 0x0000001000200900 0x0000000080010048 0x0000007000007981 0x60000003800003cc

def z108 : W := mkw 0x009f246b00000005 0x8004f92358000000 0x001f007f80000001 0x1800f803fc000000

def z109 : W := mkw 0x0098204800000000 0x0004c10240000000 0x7198f07c00000001 0x6b8cc783e0000000

def z110 : W := mkw 0x016500003555000c 0x400b280001aaa800 0x8a6700007fff801e 0x1453380003fffc00

def z111 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x2398707c38783995 0x491cc383e1c3c1cc

def z112 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c0ff803e007e04 0xe13e07fc01f003f0

def z113 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4829818dc199c7fa 0x02414c0c6e0cce3f

def z114 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0x7b99f07ff879f9f7 0x7bdccf83ffc3cfcf

def z115 : W := mkw 0x0560db906fa07f0a 0x382b06dc837d03f8 0xf7f0fff07fe07f9f 0xefbf87ff83ff03fc

def z116 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd82900004199c7fa 0x1ec14800020cce3f

def z117 : W := mkw 0x8200001410780980 0x04100000a083c04c 0x0000000000780190 0x000000000003c00c

def z118 : W := mkw 0xa1fd8084c088c2ac 0x250fec0426044615 0xf9ff818fc199c7fb 0xbfcffc0c7e0cce3f

def z119 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xfff6ff807fe67e1e 0xffffb7fc03ff33f0

def z120 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xb456ffff80000001 0xfda2b7fffc000000

def z121 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x43a9000079998000 0x021d480003cccc00

def z122 : W := mkw 0xa0000004800880a0 0x0500000024004405 0x0809000f801981f1 0x184048007c00cc0f

def z123 : W := mkw 0x0200101018702900 0x0010008080c38148 0x0200000038603804 0x0010000001c301c0

def z124 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0xfbff818fffffc7ff 0xbfdffc0c7ffffe3f

def z125 : W := mkw 0x4002062202021441 0x12001031101010a2 0xbc560e7206060669 0xfde2b07390303033

def z126 : W := mkw 0x05604b802780160a 0x182b025c013c00b0 0xf5e0ff8007800608 0xe7af07fc003c0030

def z127 : W := mkw 0xa1ffedefc088c2af 0xa50fff6f7e044615 0xf5ffffff800047e1 0xffaffffffc00023f

def z128 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0xa7e07f803f803e0c 0xc53f03fc01fc01f0

def z129 : W := mkw 0x0000694900000002 0x8000034a48000000 0x0000f18d80000000 0x0000078c6c000000

def z130 : W := mkw 0x4000021002221d40 0x12000010801110ea 0xb856000006667ffe 0x1dc2b000003333ff

def z131 : W := mkw 0x416706222707144d 0x520b3831113838a2 0x8c670e0207878668 0x94633870103c3c33

def z132 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0xfc7f8fffc7ffffff 0xffe3fc7ffe3fffff

def z133 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd82081804199c7fa 0xa6c1040c020cce3f

def z134 : W := mkw 0x01674d230000000f 0x800b3a6918000000 0x84670f8380000000 0x9423387c1c000000

def z135 : W := mkw 0xa1ffedefc088c2af 0xa50fff6f7e044615 0xfdffffffc199c7fb 0xffeffffffe0cce3f

def z136 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0xfbff00007fffc7fe 0x1fdff80003fffe3f

def z137 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3b9f1fff8787997 0xff9dcf8fffc3c3cc

def z138 : W := mkw 0x0000000035550000 0x4000000001aaa800 0xda2900007fff801e 0x1ed1480003fffc00

def z139 : W := mkw 0x8298205c10780980 0x0414c102e083c04c 0x3018007c00787997 0x6980c003e003c3cc

def z140 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0x0400ff8000007e00 0xe02007fc000003f0

def z141 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0xdba9818ff999c7fb 0xbedd4c0c7fccce3f

def z142 : W := mkw 0x83fdb05c7d7d698c 0x641fed82e3ebeb4c 0xfbfff07c7ffff99f 0x7fdfff83e3ffffcc

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0xd02000004180000a 0x06810000020c0000

def z144 : W := mkw 0x0565db806f85760e 0x782b2edc037c2bb0 0xffe7ff807f87fe0e 0xf7ff3ffc03fc3ff0

def z145 : W := mkw 0x0000020002001400 0x10000010001000a0 0x84400e0006000608 0x8422007000300030

def z146 : W := mkw 0x0400d98048806202 0x282006cc02440310 0x0000f18000000000 0x0000078c00000000

def z147 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xffe1ff83ff81fe6e 0xf7ff0ffc1ffc0ff3

def z148 : W := mkw 0x21650080a585822c 0x410b2804052c2c11 0x8867018387878668 0x9443380c1c3c3c33

def z149 : W := mkw 0xa0009084c888e2a0 0x2500048426444715 0xfba9f18ff999ffff 0xffdd4f8c7fcccfff

def z150 : W := mkw 0xa09d0004905d80a4 0x4504e8002482ec05 0x081f000f807f81f1 0x1840f8007c03fc0f

def z151 : W := mkw 0x0000020002001400 0x10000010001000a0 0xb4400e0006007e0e 0xe5a20070003003f0

def z152 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x45a9ffff80000001 0xe22d4ffffc000000

def z153 : W := mkw 0xa098a0ccc088c2a0 0x2504c50666044615 0xf9b9f1ffc199c7fb 0xffcdcf8ffe0cce3f

def z154 : W := mkw 0x8200901458786980 0x24100480a2c3c34c 0x7380f00078787996 0x639c078003c3c3cc

def z155 : W := mkw 0x4000020002021440 0x12000010001010a2 0x0800000006060668 0x0040000000303033

def z156 : W := mkw 0x41ff6f7b02221d4f 0x920ffb7bd81110ea 0xf5ffffff86663805 0xffaffffffc3331c0

def z157 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ff7e7000000000 0x5faffbf380000000

def z158 : W := mkw 0x0098900058506000 0x2004c48002c28300 0x7398f00078787816 0x6b9cc78003c3c3c0

def z159 : W := mkw 0x8698fbdc5af87f82 0x3c34c7dee2d7c3fc 0x7798fffc78787f97 0xebbcc7ffe3c3c3fc

def z160 : W := mkw 0x05fdd9807dd5620e 0x682feecc03eeab10 0x43a9f18079998000 0x021d4f8c03cccc00

def z161 : W := mkw 0x016090006d006008 0x200b048003680300 0xf3e0f0007f80780e 0x679f078003fc03c0

def z162 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x04007e7000000000 0x402003f380000000

def z163 : W := mkw 0x41ff6f7b02221d4f 0x920ffb7bd81110ea 0xfdffffff86667fff 0xffeffffffc3333ff

def z164 : W := mkw 0x4402dfb24aa27f43 0x3a2016fd925513fa 0x0400fff200007fe1 0xe02007ff900003ff

def z165 : W := mkw 0x45624fa22782164b 0x1a2b127d113c10b2 0x8c660f8207860668 0x9463307c103c3033

def z166 : W := mkw 0xa0000084808882a0 0x0500000424044415 0x8829018f819987f9 0x9c41480c7c0ccc3f

def z167 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0xf5e0ffff80000001 0xe7af07fffc000000

def z168 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0x77c0fe007e007806 0x63be07f003f003c0

def z169 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xfdffffff87878009 0xffeffffffc3c3c00

def z170 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbb9f07c79f9f99f 0x7fddcf83e3cfcfcc

def z171 : W := mkw 0xc29ab67e5a7a7dc1 0x3614d5b3f2d3d3ee 0xffdefe7e7e7e7fff 0xfffef7f3f3f3f3ff

def z172 : W := mkw 0xa09fa4efc088c2a5 0xa504fd277e044615 0xd83f81ffc199c7fb 0xbec1fc0ffe0cce3f

def z173 : W := mkw 0xc29a247e107a09c1 0x0614d123f083d04e 0x081e007e007e01f1 0x1840f003f003f00f

def z174 : W := mkw 0x04004b8002801602 0x1820025c001400b0 0x04000f8000000600 0x8020007c00000030

def z175 : W := mkw 0x8600fbdc4aa87f82 0x3c3007dee25543fc 0x0400fffc00007f81 0xe02007ffe00003fc

def z176 : W := mkw 0x05604b802780160a 0x182b025c013c00b0 0x84600f8007800608 0x8423007c003c0030

def z177 : W := mkw 0x009d000000000004 0x0004e80000000000 0x001f000000000000 0x1800f80000000000

def z178 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c07e007f807e0e 0x413e03f003fc03f0

def z179 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x0a0000007fff801e 0x0050000003fffc00

def z180 : W := mkw 0xa002edefc088c2a3 0xa500176f7e044615 0xdc29ffffc199c7fb 0xfee14ffffe0cce3f

def z181 : W := mkw 0xa5fddb84ffddf6ae 0x7d2feedc27feefb5 0xffffff8fffffffff 0xfffffffc7fffffff

def z182 : W := mkw 0x000092004a007400 0x30000490025003a0 0xf7c0fe007e007e0e 0xe7be07f003f003f0

def z183 : W := mkw 0x81ffed6f4008408f 0xa40fff6b7a004204 0xf5ffffffc0184193 0xffaffffffe00c20c

def z184 : W := mkw 0x0098000010500000 0x0004c00000828000 0xfbb9000079f9801e 0x1fddc80003cfcc00

def z185 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7ffffffbe660005 0xffbffffffdf33000

def z186 : W := mkw 0x0098204800000000 0x0004c10240000000 0xf1b9f1ff80000001 0xff8dcf8ffc000000

def z187 : W := mkw 0x41ff6f7b37771d4f 0xd20ffb7bd9bbb8ea 0xffffffffffffffff 0xffffffffffffffff

def z188 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xf7fffffff8780017 0xffbfffffffc3c000

def z189 : W := mkw 0x016049000000000a 0x000b024800000000 0x84600f8000000000 0x8423007c00000000

def z190 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x3390707038607997 0x699c838381c303cc

def z191 : W := mkw 0x4002062202021441 0x12001031101010a2 0x04460e0006060000 0x0022307000303000

def z192 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0xbc568fff86667fff 0xfde2b47ffc3333ff

def z193 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0x27d67e703e660004 0x413eb3f381f33000

def z194 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff800047fb 0xffeffffffc00023f

def z195 : W := mkw 0x0160000035550008 0x400b000001aaa800 0xfbe000007fff801e 0x07df000003fffc00

def z196 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0x71b9f1fd80000001 0x6b8dcf8fec000000

def z197 : W := mkw 0x016049000000000a 0x000b024800000000 0xf5e0ff8000000000 0xe7af07fc00000000

def z198 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xf7e8ff8c7f987f9f 0xefbf47fc63fcc3fc

def z199 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xac560e7206663e6c 0xd562b073903331f3

def z200 : W := mkw 0x01674d230000000f 0x800b3a6918000000 0xd46f8f8f80000001 0xbea37c7c7c000000

def z201 : W := mkw 0x83fffd7f7d7d698f 0xe41fffebfbebeb4c 0xfffffffffffff99f 0xffffffffffffffcc

def z202 : W := mkw 0x83fdf95d5878698e 0xa41fefcaeac3c34c 0x73b9f1fdf8787997 0x6b9dcf8fefc3c3cc

def z203 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5f6fff000000000 0xe7afb7ff80000000

def z204 : W := mkw 0x8000801440284980 0x24000400a201424c 0x7018807c40787997 0x6b80c403e203c3cc

def z205 : W := mkw 0x4562dfb26fa27f4b 0x3a2b16fd937d13fa 0xf7f6fff07fe67e0e 0xe7bfb7ff83ff33f0

def z206 : W := mkw 0x05fddb806f80760e 0x382feedc037c03b0 0xf7ffff807f807e0e 0xffbffffc03fc03f0

def z207 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff818fffff801f 0xbfdffc0c7ffffc00

def z208 : W := mkw 0x0000001000200900 0x0000000080010048 0x3010007000607997 0x69808003800303cc

def z209 : W := mkw 0x05fddb807fd5760e 0x782feedc03feabb0 0xf7e9ff807f99fe0e 0xe7bf4ffc03fccff0

def z210 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x24560e7206667fe5 0xe122b073903333ff

def z211 : W := mkw 0x040092806f807600 0x38200494037c03b0 0x020000007f807e0e 0x0010000003fc03f0

def z212 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0x43a0f18079800000 0x021d078c03cc0000

def z213 : W := mkw 0x2000008080808220 0x0100000404040411 0x0000018380000660 0x8000000c1c000033

def z214 : W := mkw 0x0160808065804208 0x200b0404032c0210 0xf3e081807f80460e 0xa79f040c03fc0230

def z215 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x847f0fff80000001 0x9c23f87ffc000000

def z216 : W := mkw 0xa0000004800880a0 0x0500000024004405 0xd829000fc19981fb 0x1ec148007e0ccc0f

def z217 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x7390f07078607806 0x639c878383c303c0

def z218 : W := mkw 0x009f246b00000005 0x8004f92358000000 0x719ff07f80000001 0x7b8cff83fc000000

def z219 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x25d6ffff80000001 0xe12eb7fffc000000

def z220 : W := mkw 0x0002062202001401 0x10001031101000a0 0xb4560e7206007e0f 0xfda2b073903003f0

def z221 : W := mkw 0x41ff063237771d4d 0x520ff83191bbb8ea 0xffff0e707fffb81e 0x5ffff87383fffdc0

def z222 : W := mkw 0x05674fa32780160f 0x982b3a7d193c00b0 0x84670f8387800608 0x9423387c1c3c0030

def z223 : W := mkw 0xa560d984ed88e2aa 0x2d2b06cc276c4715 0xdba9f18ff999c7fb 0xbedd4f8c7fccce3f

def z224 : W := mkw 0xa200b0dcc8a8eba0 0x25100586e645475d 0xd829f1ffc199fffb 0xfec14f8ffe0ccfff

def z225 : W := mkw 0x8298205c10780980 0x0414c102e083c04c 0x7198f07c00780191 0x6b8cc783e003c00c

def z226 : W := mkw 0x0000000035550000 0x4000000001aaa800 0xba5600007fff801e 0x1dd2b00003fffc00

def z227 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x41bff1ff80000001 0x1a0dff8ffc000000

def z228 : W := mkw 0x05fdd9807dd5620e 0x682feecc03eeab10 0xfbfff1807fff801e 0x1fdfff8c03fffc00

def z229 : W := mkw 0xe00286a6c28ad6e1 0x37001435361456b7 0xdc6f8f8fc79fc7fb 0xbee37c7c7e3cfe3f

def z230 : W := mkw 0x41ff063202221d4d 0x120ff831901110ea 0xfdff0e7206667fff 0xffeff873903333ff

def z231 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe9ff807f99fe1e 0xffff4ffc03fccff0

def z232 : W := mkw 0x829f247f10780985 0x8414f923f883c04c 0x001f007f80780191 0x1800f803fc03c00c

def z233 : W := mkw 0x87f8f9cc7dd8628a 0x2c3fc7ce63eec314 0x43a8f18c79980000 0x021d478c63ccc000

def z234 : W := mkw 0x0562ffeb6f80760b 0xb82b17ff5b7c03b0 0xf7e0ffffff807e0f 0xe7bf07fffffc03f0

def z235 : W := mkw 0xa2009094d8f8eba0 0x25100484a6c7c75d 0x0a00000079f9fffe 0x0050000003cfcfff

def z236 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff8666001f 0xffeffffffc333000

def z237 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0000818d80000000 0x0000040c6c000000

def z238 : W := mkw 0x040012002f003400 0x18200090017801a0 0x020000003e003804 0x0010000001f001c0

def z239 : W := mkw 0x45625f322f223d4b 0x1a2b12f9917911ea 0xbfd67e723e667fff 0xfdfeb3f391f333ff

def z240 : W := mkw 0x4167063227271d4d 0x520b3831913938ea 0xbc770e7207e7ffff 0xfde3b873903f3fff

def z241 : W := mkw 0x8000800440084080 0x2400040022004204 0x0000000040184192 0x000000000200c20c

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0xb4400e0000000000 0xe5a2007000000000

def z243 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4029818fc199c7e1 0xa2014c0c7e0cce3f

def z244 : W := mkw 0x4000021002221d40 0x12000010801110ea 0x3810007006667fff 0x69c08003803333ff

def z245 : W := mkw 0x01ff4d233555000f 0xc00ffa6919aaa800 0xffff0f83ffff801e 0x9ffff87c1ffffc00

def z246 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x63ff00007fff8004 0x031ff80003fffc00

def z247 : W := mkw 0x0002042200000001 0x0000102110000000 0x0016007200000001 0x1800b00390000000

def z248 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x47a0ff8079807e00 0xe23d07fc03cc03f0

def z249 : W := mkw 0x8298b25c5a787d80 0x3414c592e2d3c3ec 0xf7d8fe7c7e787f9f 0xefbec7f3e3f3c3fc

def z250 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x9800818f800047fb 0xbcc0040c7c00023f

def z251 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0xdc298fffc199fffb 0xfee14c7ffe0ccfff

def z252 : W := mkw 0x01ff246b3555000d 0xc00ff92359aaa800 0xfbff007fffff801f 0x1fdff803fffffc00

def z253 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0x41a9000000000000 0x020d480000000000

def z254 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7398f1fff8787ff7 0xeb9cc78fffc3c3ff

def z255 : W := mkw 0x4002042200020041 0x0200102110001002 0x0806000200060060 0x1040300010003003

def z256 : W := mkw 0x0000001000200900 0x0000000080010048 0xb810007200607fff 0xfdc08003900303ff

def z257 : W := mkw 0x056092806f807608 0x382b0494037c03b0 0xf3e000007f807e0e 0x079f000003fc03f0

def z258 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbdef07c7e7e799f 0x7fdef783e3f3f3cc

def z259 : W := mkw 0x41ff6d7b0022094f 0x820ffb6bd801104a 0xfdffffff806601f1 0xffeffffffc03300f

def z260 : W := mkw 0x009d000010550004 0x4004e8000082a800 0x0009000000198000 0x000048000000cc00

def z261 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd029818fc1998001 0xbe814c0c7e0ccc00

def z262 : W := mkw 0x0098000035550000 0x4004c00001aaa800 0x7b9800007fff801e 0x0bdcc00003fffc00

def z263 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x00000000000047e0 0x000000000000023f

def z264 : W := mkw 0x0002042200000001 0x0000102110000000 0xb4560e7200000001 0xfda2b07390000000

def z265 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x0000f07c00007981 0x60000783e00003cc

def z266 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e0ff8fff807fef 0xe7bf07fc7ffc03ff

def z267 : W := mkw 0x8760fbdc6fa87f8a 0x3c3b07dee37d43fc 0xf7e0fffc7f807f8f 0xe7bf07ffe3fc03fc

def z268 : W := mkw 0x040092804a807600 0x38200494025403b0 0x0000000000007e00 0x00000000000003f0

def z269 : W := mkw 0xa1ffedefc088c2af 0xa50fff6f7e044615 0xf5ffffffc1998001 0xffaffffffe0ccc00

def z270 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x0018f07c00787991 0x6800c783e003c3cc

def z271 : W := mkw 0x41ff04323577094d 0x420ff82191abb84a 0xfbff00727fff81ff 0x1fdff80393fffc0f

def z272 : W := mkw 0x01fd49000000000e 0x000fea4800000000 0xf5ffff8000000000 0xffaffffc00000000

def z273 : W := mkw 0x04005b000a003402 0x182002d8005001a0 0x04007e0000003800 0x402003f0000001c0

def z274 : W := mkw 0x83f8f95c5878698a 0x241fc7cae2c3c34c 0xf7f8fffc78787997 0xefbfc7ffe3c3c3cc

def z275 : W := mkw 0x0000001000200900 0x0000000080010048 0xb85600700666799f 0x7dc2b003803333cc

def z276 : W := mkw 0x01fd20480000000c 0x000fe90240000000 0xf1fff07c00000001 0x7f8fff83e0000000

def z277 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0x041fffff80000001 0xf820fffffc000000

def z278 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3f600007fe6000e 0x079fb00003ff3000

def z279 : W := mkw 0x83fd90147d7d698c 0x641fec80a3ebeb4c 0xfbff00007ffff99e 0x1fdff80003ffffcc

def z280 : W := mkw 0x0098b04848006000 0x2004c58242400300 0x7398f07c78007807 0x6b9cc783e3c003c0

def z281 : W := mkw 0x0298205810700900 0x0014c102c0838048 0x0010007000600000 0x0000800380030000

def z282 : W := mkw 0x0000828042805600 0x30000414021402b0 0xf4608f8047807e0e 0xe7a3047c023c03f0

def z283 : W := mkw 0x8200901448286980 0x24100480a241434c 0x0000000000007980 0x00000000000003cc

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000000047fa 0x004000000000023f

def z285 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x8460ff8007807e08 0xe42307fc003c03f0

def z286 : W := mkw 0x016500002505000c 0x400b280001282800 0xd86f0000479f801a 0x1ec37800023cfc00

def z287 : W := mkw 0xc3ffff7f5a7a7dcf 0xb61ffffbfad3d3ee 0xfffffffffe7e7fff 0xfffffffffff3f3ff

def z288 : W := mkw 0x429a367a1a723d41 0x1214d1b3d0d391ea 0x27d67e703e663804 0x413eb3f381f331c0

def z289 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x67e0ff807f803804 0x433f07fc03fc01c0

def z290 : W := mkw 0xe0008294c2aadfe0 0x37000414a61556ff 0xd829818fc7ffffff 0xbec14c0c7e3fffff

def z291 : W := mkw 0xc7fafffe7ffa7fcb 0x3e3fd7fff3ffd3fe 0xfffefffe7ffe7fff 0xfffff7fff3fff3ff

def z292 : W := mkw 0x8200b05c58786980 0x24100582e2c3c34c 0x0200f07c78787997 0x60100783e3c3c3cc

def z293 : W := mkw 0xa1658084e58dc2ac 0x650b2c04272c6e15 0xd86f818fc79fc7fb 0xbec37c0c7e3cfe3f

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0xd829818f800047fb 0xbec14c0c7c00023f

def z295 : W := mkw 0x4002062202021441 0x12001031101010a2 0xbc460e0206067e6e 0xf5e23070103033f3

def z296 : W := mkw 0x009f246b10550005 0xc004f9235882a800 0x081f007f807f8011 0x1840f803fc03fc00

def z297 : W := mkw 0x0200305808202900 0x00100182c0410148 0x0000707000003800 0x40000383800001c0

def z298 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0xf9ff00000666001e 0x1fcff80000333000

def z299 : W := mkw 0xa0000004800880a0 0x0500000024004405 0x0000000f800001e1 0x000000007c00000f

def z300 : W := mkw 0x400296324a227d41 0x320014b1925113ea 0xffd6fe727e667fff 0xfffeb7f393f333ff

def z301 : W := mkw 0x87f8fb5c7f787d8a 0x3c3fc7dae3fbc3ec 0x77d8fe7c7e787997 0x6bbec7f3e3f3c3cc

def z302 : W := mkw 0xa0000004800880a0 0x0500000024004405 0xd829818f801981f1 0xbec14c0c7c00cc0f

def z303 : W := mkw 0x0000808040804200 0x2000040402040210 0x4020818041800000 0x0201040c020c0000

def z304 : W := mkw 0x2000008080808220 0x0100000404040411 0x0021018181818000 0x0001080c0c0c0c00

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000200000668 0x9440000010000033

def z306 : W := mkw 0x8298901458786980 0x2414c480a2c3c34c 0x7398000078787996 0x0b9cc00003c3c3cc

def z307 : W := mkw 0x2000008080808220 0x0100000404040411 0xd8290183c199867a 0x9ec1480c1e0ccc33

def z308 : W := mkw 0x05ff7f6b2f00340f 0x982ffbfb597801a0 0x27d67e703e003804 0x413eb3f381f001c0

def z309 : W := mkw 0x040092806f807600 0x38200494037c03b0 0xb6400e007f807e0e 0xe5b2007003fc03f0

def z310 : W := mkw 0x45ffdfb27ff77f4f 0x7a2ffefd93ffbbfa 0xfffffff27fffffff 0xffffffff93ffffff

def z311 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0x7780ff8078007e06 0xe3bc07fc03c003f0

def z312 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x2bdf00003e7f8014 0x195ef80001f3fc00

def z313 : W := mkw 0x4000021002221d40 0x12000010801110ea 0x0000000006663804 0x00000000003331c0

def z314 : W := mkw 0x440296b26fa27f41 0x3a2014b5937d13fa 0xbe560e727fe67fff 0xfdf2b07393ff33ff

def z315 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0x21d6000000000000 0x010eb00000000000

def z316 : W := mkw 0x8098a04c40084080 0x2404c50262004204 0x7198f07c40184193 0x6b8cc783e200c20c

def z317 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd029818dc199c60a 0xa6814c0c6e0cce30

def z318 : W := mkw 0x4002043200220941 0x020010219001104a 0x98160072006647fb 0xbcc0b0039003323f

def z319 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0x73a0f18079807806 0x639d078c03cc03c0

def z320 : W := mkw 0x01ffedeb4080420f 0xa00fff6f5a040210 0xf5ffffffc180460b 0xffaffffffe0c0230

def z321 : W := mkw 0x0160000025000008 0x000b000001280000 0x23c000003e000004 0x011e000001f00000

def z322 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0xf1ff818f80000001 0xbf8ffc0c7c000000

def z323 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x0218007c78787997 0x0810c003e3c3c3cc

def z324 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7fffffff9998001 0xffbfffffffcccc00

def z325 : W := mkw 0x4562dfb26fa27f4b 0x3a2b16fd937d13fa 0xf7e0fff27f807fef 0xe7bf07ff93fc03ff

def z326 : W := mkw 0x429a367a1a723d41 0x1214d1b3d0d391ea 0xbfd67e723e667fff 0xfdfeb3f391f333ff

def z327 : W := mkw 0x0000808040804200 0x2000040402040210 0xd8208182418047fb 0xbec1040c120c023f

def z328 : W := mkw 0x0560db804a80760a 0x382b06dc025403b0 0xf5e0ff8000007e00 0xe7af07fc000003f0

def z329 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xfdffffff807f8011 0xffeffffffc03fc00

def z330 : W := mkw 0xa09f246f800880a5 0x8504f9237c004405 0x081f007f801981f1 0x1840f803fc00cc0f

def z331 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390f07c38607985 0x611c8783e1c303cc

def z332 : W := mkw 0x409f247b00220945 0x8204f923d801104a 0x081f007f806601f1 0x1840f803fc03300f

def z333 : W := mkw 0xa400db84ca88f6a2 0x3d2006dc265447b5 0x0400ff8f80007fe1 0xe02007fc7c0003ff

def z334 : W := mkw 0x0098000010500000 0x0004c00000828000 0x2390000038600004 0x011c800001c30000

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x4029818d80000000 0x02014c0c6c000000

def z336 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc7f0e7247ffffff 0xffe3f873923fffff

def z337 : W := mkw 0x01fd00000000000c 0x000fe80000000000 0xf9ff00004199801a 0x1fcff800020ccc00

def z338 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e9ff8dff99fe0e 0xe7bf4ffc6ffccff0

def z339 : W := mkw 0x0002042200000001 0x0000102110000000 0x84460e0200000000 0x9422307010000000

def z340 : W := mkw 0x0005000000050004 0x4000280000002800 0x0807000000078000 0x1040380000003c00

def z341 : W := mkw 0x2000008080808220 0x0100000404040411 0x982101838181c7fb 0xbcc1080c1c0c0e3f

def z342 : W := mkw 0x05ffffeb6f80760f 0xb82fffff5b7c03b0 0xf7f6fff07f807e0e 0xe7bfb7ff83fc03f0

def z343 : W := mkw 0x4002062202021441 0x12001031101010a2 0x04000e0200000660 0x8020007010000033

def z344 : W := mkw 0x4000021037771d40 0x5200001081bbb8ea 0x0a0000007ffffffe 0x0050000003ffffff

def z345 : W := mkw 0xa0008284c288d6a0 0x35000414261446b5 0xfc698f8fc799ffff 0xffe34c7c7e3ccfff

def z346 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0xf3b8f1fc79f87f9f 0xef9dc78fe3cfc3fc

def z347 : W := mkw 0xa5ffffefef88f6af 0xbd2fffff7f7c47b5 0xffffffffff99ffff 0xfffffffffffccfff

def z348 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf87f818fc7ffc7ff 0xbfc3fc0c7e3ffe3f

def z349 : W := mkw 0x41ff063237771d4d 0x520ff83191bbb8ea 0x27d60e703e663804 0x413eb07381f331c0

def z350 : W := mkw 0x05fd4b8037d5160e 0x582fea5c01bea8b0 0xffff0f807fff861e 0x9ffff87c03fffc30

def z351 : W := mkw 0xc20092145a7a7dc0 0x36100490a2d3d3ee 0x0a0000007e7e7ffe 0x0050000003f3f3ff

def z352 : W := mkw 0x016500002505000c 0x400b280001282800 0x0021000001818000 0x00010800000c0c00

def z353 : W := mkw 0x0000100008002000 0x0000008000400100 0x2380700038003804 0x411c038001c001c0

def z354 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x04000e7000003800 0x40200073800001c0

def z355 : W := mkw 0x409f063212771d45 0x5204f8319093b8ea 0xbc5f0e72067fffff 0xfde2f8739033ffff

def z356 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0xf7e0ff8079800000 0xe7bf07fc03cc0000

def z357 : W := mkw 0x829db05c587d6984 0x6414ed82e2c3eb4c 0x7b9ff07c787ff997 0x7bdcff83e3c3ffcc

def z358 : W := mkw 0xc29ab67e5a7a7dc1 0x3614d5b3f2d3d3ee 0x7798fe7e78787ff7 0xebbcc7f3f3c3c3ff

def z359 : W := mkw 0x0098204800000000 0x0004c10240000000 0x4188f00c00000000 0x020c478060000000

def z360 : W := mkw 0xa560cb84e788d6aa 0x3d2b065c273c46b5 0xdc698f8fc799c7fb 0xbee34c7c7e3cce3f

def z361 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0xd1a9f18f80000001 0xbe8d4f8c7c000000

def z362 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x0c160e7200667ff1 0xf860b073900333ff

def z363 : W := mkw 0x8000808440884280 0x2400040422044214 0xd028818c4198479b 0xae81440c620cc23c

def z364 : W := mkw 0x05ff7f6b2f00340f 0x982ffbfb597801a0 0xf7ffffffbe003805 0xffbffffffdf001c0

def z365 : W := mkw 0x83fffd7f5878698f 0xa41fffebfac3c34c 0x77defe7c78787997 0x6bbef7f3e3c3c3cc

def z366 : W := mkw 0x8298205c10780980 0x0414c102e083c04c 0x7398007c78780197 0x0b9cc003e3c3c00c

def z367 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4560e7206663805 0xfda2b073903331c0

def z368 : W := mkw 0x0000020002001400 0x10000010001000a0 0x04000e0000007e00 0xe0200070000003f0

def z369 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0xf3e0f1807f80000e 0x079f078c03fc0000

def z370 : W := mkw 0x009d204900000004 0x8004e90248000000 0x0009000d80000000 0x000048006c000000

def z371 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4388f07c78187981 0x621c4783e3c0c3cc

def z372 : W := mkw 0x056049802580020a 0x082b024c012c0010 0x0020018001800000 0x0001000c000c0000

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000000000001a 0x1cc0000000000000

def z374 : W := mkw 0x03fd30583d75290c 0x401fe982c1eba948 0x23d670703e663804 0x411eb38381f331c0

def z375 : W := mkw 0x0000020002001400 0x10000010001000a0 0x24400e0006003804 0x41220070003001c0

def z376 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00027fffc7ff 0xbfdff80013fffe3f

def z377 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd029818f800047e1 0xbe814c0c7c00023f

def z378 : W := mkw 0x4002062202021441 0x12001031101010a2 0x8c460e0206060668 0x9462307010303033

def z379 : W := mkw 0x009d000010550004 0x4004e8000082a800 0xb85f0000067f801e 0x1dc2f8000033fc00

def z380 : W := mkw 0x0160000025000008 0x000b000001280000 0xfbe900007f99801e 0x1fdf480003fccc00

def z381 : W := mkw 0xa1ffedeff5ddc2af 0xe50fff6f7faeee15 0xffffffffffffc7ff 0xfffffffffffffe3f

def z382 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0xf1fff18d80000000 0x1f8fff8c6c000000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x900000000000460a 0xa480000000000230

def z384 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x887f000007ff8018 0x1c43f800003ffc00

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000818f80000001 0xa000040c7c000000

def z386 : W := mkw 0x016049002500000a 0x000b024801280000 0xf7e0ff807f80000e 0xe7bf07fc03fc0000

def z387 : W := mkw 0x400286b242a25f41 0x32001435921512fa 0xfc768ff247e67fff 0xffe3b47f923f33ff

def z388 : W := mkw 0xa298b0ccd8d8e2a0 0x2514c58666c6c715 0x43a9f18df9998000 0x021d4f8c6fcccc00

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x8821000001818008 0x14410800000c0c00

def z390 : W := mkw 0xc29ab47e587a69c1 0x2614d5a3f2c3d34e 0x7b9ef07e787e79f7 0x7bdcf783f3c3f3cf

def z391 : W := mkw 0x0298304818502000 0x0014c18240c28100 0x0380700038000000 0x001c038001c00000

def z392 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0xb440ff8006007e0e 0xe5a207fc003003f0

def z393 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4398f07c78780191 0x0a1cc783e3c3c00c

def z394 : W := mkw 0x4002062202021441 0x12001031101010a2 0xbc560e020666067e 0x9de2b07010333033

def z395 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398707078783816 0x4b9cc38383c3c1c0

def z396 : W := mkw 0x05604b802780160a 0x182b025c013c00b0 0xf7e00f807f80060e 0x87bf007c03fc0030

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0xd829818fc199801b 0xbec14c0c7e0ccc00

def z398 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x5008f07c40187993 0x6a804783e200c3cc

def z399 : W := mkw 0x41ff063237771d4d 0x520ff83191bbb8ea 0xbfd60e723e667fff 0xfdfeb07391f333ff

def z400 : W := mkw 0x01fd49003555000e 0x400fea4801aaa800 0xffffff807fff801e 0xfffffffc03fffc00

def z401 : W := mkw 0x01fd00001050000c 0x000fe80000828000 0xf3ff000078780016 0x1f9ff80003c3c000

def z402 : W := mkw 0x4002043200220941 0x020010219001104a 0x38160072006679f7 0x79c0b003900333cf

def z403 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7b98f07c79f9ffff 0x6bdcc783e3cfcfff

def z404 : W := mkw 0x0098001010700900 0x0004c00080838048 0x7398007078787997 0x6b9cc00383c3c3cc

def z405 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x2c560e72066639f5 0x5962b073903331cf

def z406 : W := mkw 0x03fd30583d75290c 0x401fe982c1eba948 0xfbff70707fffb81e 0x5fdffb8383fffdc0

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x8021018380000000 0x9401080c1c000000

def z408 : W := mkw 0x0000901048206900 0x2000048082410348 0x7390f07078607997 0x6b9c878383c303cc

def z409 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0xd3a0f1807980460a 0xa69d078c03cc0230

def z410 : W := mkw 0x21fd0080b5d5822c 0x410fe80405aeac11 0xfbff0183ffff867e 0x9fdff80c1ffffc33

def z411 : W := mkw 0x4162063227221d49 0x120b1031913910ea 0xfff60e727fe67fff 0xffffb07393ff33ff

def z412 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc560e700666381e 0x5de2b073803331c0

def z413 : W := mkw 0x83fdb04c7d5d608c 0x641fed8263eaeb04 0x43a9f00c79998000 0x021d4f8063cccc00

def z414 : W := mkw 0x01674d230000000f 0x800b3a6918000000 0x04460e0000000000 0x0022307000000000

def z415 : W := mkw 0x8000800440084080 0x2400040022004204 0xd829800c4199c19b 0x3ec14c00620cce0c

def z416 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff827f807fff 0xffff07fc13fc03ff

def z417 : W := mkw 0x05fd5b003f55340e 0x582fead801faa9a0 0xffff7e007fffb81e 0x5ffffbf003fffdc0

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x8846000006060008 0x1442300000303000

def z419 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x2bd600007fff801e 0x015eb00003fffc00

def z420 : W := mkw 0x009d000035550004 0x4004e80001aaa800 0x0a1f00007fff801e 0x1850f80003fffc00

def z421 : W := mkw 0x0000908048806200 0x2000048402440310 0xf3a0f18079807e0e 0xe79d078c03cc03f0

def z422 : W := mkw 0x0160c9804080420a 0x200b064c02040210 0xf5e0ff804180460a 0xe7af07fc020c0230

def z423 : W := mkw 0x01fd02003755140c 0x500fe81001baa8a0 0xffff0e007ffffe1e 0xfffff87003fffff0

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0xb04000000600000e 0x0582000000300000

def z425 : W := mkw 0x0002246b00000001 0x8000112358000000 0x0000007f80000001 0x00000003fc000000

def z426 : W := mkw 0x0098000010500000 0x0004c00000828000 0x0018000000780010 0x0800c0000003c000

def z427 : W := mkw 0x05ffffeb7fd5760f 0xf82fffff5bfeabb0 0xfffffffffffffe1f 0xfffffffffffffff0

def z428 : W := mkw 0x41ff6f7b02221d4f 0x920ffb7bd81110ea 0x25d67e7006663804 0x412eb3f3803331c0

def z429 : W := mkw 0x0098204800000000 0x0004c10240000000 0x2190707000000000 0x410c838380000000

def z430 : W := mkw 0xc3ffb67e7f7f7dcd 0x761ffdb3f3fbfbee 0xfffffe7e7fffffff 0xfffffff3f3ffffff

def z431 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffffc199801b 0xffeffffffe0ccc00

def z432 : W := mkw 0x8200205c00280980 0x04100102e001404c 0x0000007c00000181 0x00000003e000000c

def z433 : W := mkw 0x0160d9004800600a 0x200b06c802400300 0xf7e0ff8078007806 0xe7bf07fc03c003c0

def z434 : W := mkw 0x0560cb806780560a 0x382b065c033c02b0 0xd4608f804780460a 0xa6a3047c023c0230

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000666001e 0x0040000000333000

def z436 : W := mkw 0x01fd00001055000c 0x400fe8000082a800 0xf9ff0000007f8010 0x1fcff8000003fc00

def z437 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x0380000038000000 0x001c000001c00000

def z438 : W := mkw 0x01f869480000000a 0x000fc34a40000000 0xf5f8fffc00000001 0xefafc7ffe0000000

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0xd029000000000000 0x1e81480000000000

def z440 : W := mkw 0x8298b05c48286980 0x2414c582e241434c 0x7198f07c00007981 0x6b8cc783e00003cc

def z441 : W := mkw 0x05fdf9c96d80620e 0xa82fefce4b6c0310 0x43a9f18df9800000 0x021d4f8c6fcc0000

def z442 : W := mkw 0x4000021002221d40 0x12000010801110ea 0x9800000206667fff 0xbcc00000103333ff

def z443 : W := mkw 0x0000204800000000 0x0000010240000000 0x0000f07c00000001 0x60000783e0000000

def z444 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0xbc560e7247ffffff 0xfde2b073923fffff

def z445 : W := mkw 0x01fd00002500000c 0x000fe80001280000 0xf3ff00007f80000e 0x1f9ff80003fc0000

def z446 : W := mkw 0x05ff6feb2780160f 0x982ffb7f593c00b0 0xf5ffffff87800609 0xffaffffffc3c0030

def z447 : W := mkw 0x01604b000200140a 0x100b0258001000a0 0xf5e0ff8006007e0e 0xe7af07fc003003f0

def z448 : W := mkw 0x040092806f807600 0x38200494037c03b0 0x7380f0007f807e0e 0x639c078003fc03f0

def z449 : W := mkw 0x0000020002001400 0x10000010001000a0 0xbc400e0206007fff 0xfde20070103003ff

def z450 : W := mkw 0xa400db84ca88f6a2 0x3d2006dc265447b5 0xdc29ff8fc199fffb 0xfee14ffc7e0ccfff

def z451 : W := mkw 0xa0008084f5ddc2a0 0x6500040427aeee15 0x0a0000007fffc7fe 0x0050000003fffe3f

def z452 : W := mkw 0x009f246b00000005 0x8004f92358000000 0xd03f81ff80000001 0xbe81fc0ffc000000

def z453 : W := mkw 0xc29ab67e5a7a7dc1 0x3614d5b3f2d3d3ee 0x77defe7c7e7e7997 0x6bbef7f3e3f3f3cc

def z454 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e07e007f80380e 0x47bf03f003fc01c0

def z455 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4560e7200007fe1 0xfda2b073900003ff

def z456 : W := mkw 0xe29ab6fedafaffe1 0x3714d5b7f6d7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z457 : W := mkw 0x8202fd7f48286983 0xa41017ebfa41434c 0x0400ffff80007981 0xe02007fffc0003cc

def z458 : W := mkw 0x0000000010500000 0x0000000000828000 0x0200000078780016 0x0010000003c3c000

def z459 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xdba900007999801a 0x1edd480003cccc00

def z460 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x0c000e7206667fff 0xe0600073903333ff

def z461 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xf7ffffffff80000f 0xffbffffffffc0000

def z462 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0809000fc199c7fb 0x184048007e0cce3f

def z463 : W := mkw 0x0002042200000001 0x0000102110000000 0xf47f8fff80000001 0xffa3fc7ffc000000

def z464 : W := mkw 0x016500002505000c 0x400b280001282800 0x0046000006060000 0x0002300000303000

def z465 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xc829818fc1998668 0x96414c0c7e0ccc33

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000002000001f1 0x184000001000000f

def z467 : W := mkw 0x829d205c107d0984 0x4414e902e083e84c 0x081f007c007f8191 0x1840f803e003fc0c

def z468 : W := mkw 0x41ff6f7b02221d4f 0x920ffb7bd81110ea 0xbdd67e7206667fff 0xfdeeb3f3903333ff

def z469 : W := mkw 0x8200b04c48086080 0x2410058262404304 0x0000f00c00000000 0x0000078060000000

def z470 : W := mkw 0x8098800450584080 0x2404c4002282c204 0x7398800c78784197 0x2b9cc40063c3c20c

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000002000047e1 0xa00000001000023f

def z472 : W := mkw 0x21674da38080822f 0x810b3a6d1c040411 0x8c670f8381818668 0x9463387c1c0c0c33

def z473 : W := mkw 0x8200900458586080 0x2410048022c2c304 0x0200000078180000 0x0010000003c0c000

def z474 : W := mkw 0x4000021002221d40 0x12000010801110ea 0x0000000000007fe0 0x00000000000003ff

def z475 : W := mkw 0x016500002505000c 0x400b280001282800 0xb877000007e7801e 0x1dc3b800003f3c00

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000004199801a 0x00400000020ccc00

def z477 : W := mkw 0x4002043200220941 0x020010219001104a 0x0016007000660000 0x0000b00380033000

def z478 : W := mkw 0x009f246b00000005 0x8004f92358000000 0x0016007000000000 0x0000b00380000000

def z479 : W := mkw 0x4002043200220941 0x020010219001104a 0xbc560e72006601f1 0xfde2b0739003300f

def z480 : W := mkw 0x45625f322f223d4b 0x1a2b12f9917911ea 0x27d67e703e663804 0x413eb3f381f331c0

def z481 : W := mkw 0x01fd20483555000c 0x400fe90241aaa800 0xfbfff07c7fff801f 0x7fdfff83e3fffc00

def z482 : W := mkw 0x0567dfa36f80760f 0xb82b3efd1b7c03b0 0xf7e7ff83ff807e0e 0xf7bf3ffc1ffc03f0

def z483 : W := mkw 0x21ff6deb8080822f 0x810ffb6f5c040411 0xfdffffff81818669 0xffeffffffc0c0c33

def z484 : W := mkw 0xe0020636822a9de1 0x17001031b41154ef 0xbc5f0e7f867fffff 0xfde2f873fc33ffff

def z485 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x9c000e7200007ffb 0xfce00073900003ff

def z486 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x34100e7200607ff7 0xe9a08073900303ff

def z487 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x5008818fc01847f3 0xaa80440c7e00c23f

def z488 : W := mkw 0x0002042200000001 0x0000102110000000 0xbc560e72000047fb 0xfde2b0739000023f

def z489 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xabf700003fe7800c 0x155fb80001ff3c00

def z490 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x7398f00c78780016 0x0b9cc78063c3c000

def z491 : W := mkw 0x2000008080808220 0x0100000404040411 0x0800000001818668 0x00400000000c0c33

def z492 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x88210183c199c7fa 0x9441080c1e0cce3f

def z493 : W := mkw 0x860092947ff87f80 0x3c300494a3ffc3fc 0x020000007ff87f9e 0x0010000003ffc3fc

def z494 : W := mkw 0x07f87b583f703d0a 0x183fc3dac1fb81e8 0x27d07e703e603804 0x413e83f381f301c0

def z495 : W := mkw 0x0000020002001400 0x10000010001000a0 0xbc560e0006667e1e 0xfde2b070003333f0

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0xd82900024199c7fb 0xbec14800120cce3f

def z497 : W := mkw 0x83fffd7f4828698f 0xa41fffebfa41434c 0xf5ffffff80007981 0xffaffffffc0003cc

def z498 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x25df7e7f80000001 0x592efbf3fc000000

def z499 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x75defe7c00000001 0x6baef7f3e0000000

def z500 : W := mkw 0x05fffdeb6d80620f 0xa82fffef5b6c0310 0xf7fffffff9800001 0xffbfffffffcc0000

def z501 : W := mkw 0xa1ff6d6f800880af 0x850ffb6b7c004405 0xfdffffff801981f1 0xffeffffffc00cc0f

def z502 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xcbef00007f9f8008 0x165f780003fcfc00

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x5008800c00000001 0x2a80440060000000

def z504 : W := mkw 0x01674d230000000f 0x800b3a6918000000 0xf5e7ff8380000000 0xf7af3ffc1c000000

def z505 : W := mkw 0x0400028027801600 0x18200014013c00b0 0x0000000007800608 0x00000000003c0030

def z506 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0x43a9818df9998000 0x021d4c0c6fcccc00

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0xb056000000000000 0x1d82b00000000000

def z508 : W := mkw 0x829fb47f58786985 0xa414fda3fac3c34c 0x739ff07ff8787997 0x7b9cff83ffc3c3cc

def z509 : W := mkw 0x03ff7d7b1870290f 0x801ffbebd8c38148 0x27d67e7038603804 0x413eb3f381c301c0

def z510 : W := mkw 0x4000001000220940 0x020000008001104a 0x08000000006601f0 0x004000000003300f

def z511 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x8c460e7206067fe9 0xf4623073903033ff

def z512 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3e900007f99800e 0x079f480003fccc00

def z513 : W := mkw 0xa3fdb0dcfdfdebac 0x651fed86e7efef5d 0xfbfff1ffffffffff 0xffdfff8fffffffff

def z514 : W := mkw 0x0160000025000008 0x000b000001280000 0x8060000007800008 0x04030000003c0000

def z515 : W := mkw 0x01ff6f6b0200140f 0x900ffb7b581000a0 0xf5ffffff86007e0f 0xffaffffffc3003f0

def z516 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4560e7006667e0e 0xe5a2b073803333f0

def z517 : W := mkw 0x4002043200220941 0x020010219001104a 0x00000072000001e1 0x000000039000000f

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x0816000000660010 0x1840b00000033000

def z519 : W := mkw 0xa298a0dcd0f8cba0 0x2514c506e687c65d 0xd83981ffc1f9c7fb 0xbec1cc0ffe0fce3f

def z520 : W := mkw 0x0560db807fd5760a 0x782b06dc03feabb0 0xffe0ff807ffffe1e 0xe7ff07fc03fffff0

def z521 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x86600f807f807e0e 0x8433007c03fc03f0

def z522 : W := mkw 0x83fdf94d5858608e 0xa41fefca6ac2c304 0x43a9f18df8180000 0x021d4f8c6fc0c000

def z523 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x4ba900007fff801e 0x025d480003fffc00

def z524 : W := mkw 0x2000000080008020 0x0100000004000401 0x0801000380018060 0x104008001c000c03

def z525 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffff7e707fff801e 0x5ffffbf383fffc00

def z526 : W := mkw 0xa160c984c088c2aa 0x250b064c26044615 0xfde9ff8fc199c7fb 0xffef4ffc7e0cce3f

def z527 : W := mkw 0x016049000000000a 0x000b024800000000 0x25c07e0000000000 0x412e03f000000000

def z528 : W := mkw 0x0002042200000001 0x0000102110000000 0x04000e7200000001 0xe020007390000000

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x3010000000600016 0x0980800000030000

def z530 : W := mkw 0xa002edefc088c2a3 0xa500176f7e044615 0x0400ffff800047e1 0xe02007fffc00023f

def z531 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x0816007206667fff 0x1840b003903333ff

def z532 : W := mkw 0x0000001000200900 0x0000000080010048 0x0000000000607996 0x00000000000303cc

def z533 : W := mkw 0x409a063212721d41 0x1204d031909390ea 0xffde0e727e7e7fff 0xfffef07393f3f3ff

def z534 : W := mkw 0x8000800440084080 0x2400040022004204 0xd029818fc0184193 0xbe814c0c7e00c20c

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x5008000040180012 0x0a8040000200c000

def z536 : W := mkw 0x07f8fbd87ff07f0a 0x383fc7dec3ff83f8 0xf7f0fff07fe07e0e 0xe7bf87ff83ff03f0

def z537 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0x43a9f18df9998000 0x021d4f8c6fcccc00

def z538 : W := mkw 0xa167cda7c088c2af 0xa50b3e6d3e044615 0xdc6f8f8fc199c7fb 0xbee37c7c7e0cce3f

def z539 : W := mkw 0x8000800440084080 0x2400040022004204 0x0000800c00004181 0x200004006000020c

def z540 : W := mkw 0x4002063237771d41 0x5200103191bbb8ea 0xbe560e727fffffff 0xfdf2b07393ffffff

def z541 : W := mkw 0x0002042200000001 0x0000102110000000 0x24560e7000000000 0x4122b07380000000

def z542 : W := mkw 0x4000021002221d40 0x12000010801110ea 0xbc400e0006667ffe 0xe5e20070003333ff

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x4029000041998000 0x02014800020ccc00

def z544 : W := mkw 0x83fd205c357d098c 0x441fe902e1abe84c 0xfbff007c7fff819f 0x1fdff803e3fffc0c

def z545 : W := mkw 0x83fffd6f5858608f 0xa41fffeb7ac2c304 0xf7fffffff8180001 0xffbfffffffc0c000

def z546 : W := mkw 0x01ff04220000000d 0x000ff82110000000 0xf5ff0e7200000001 0xffaff87390000000

def z547 : W := mkw 0xa2009094d8f8eba0 0x25100484a6c7c75d 0xda29818ff9f9ffff 0xbed14c0c7fcfcfff

def z548 : W := mkw 0x016049000000000a 0x000b024800000000 0x41a0f18000000000 0x020d078c00000000

def z549 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0000000041998000 0x00000000020ccc00

def z550 : W := mkw 0x0098204800000000 0x0004c10240000000 0x0018007c00000001 0x0800c003e0000000

def z551 : W := mkw 0x83fdb05c7d7d698c 0x641fed82e3ebeb4c 0x73def07c7e7e7997 0x6b9ef783e3f3f3cc

def z552 : W := mkw 0x8200901458786980 0x24100480a2c3c34c 0x5208800c78787997 0x2a90440063c3c3cc

def z553 : W := mkw 0x25604b80a780962a 0x192b025c053c04b1 0x8c610f8387818668 0x9463087c1c3c0c33

def z554 : W := mkw 0xa1fde9cdc088c2ae 0xa50fef4e6e044615 0x41a9f18dc1998000 0x020d4f8c6e0ccc00

def z555 : W := mkw 0x0000900048006000 0x2000048002400300 0x0000f00000007800 0x60000780000003c0

def z556 : W := mkw 0x8200901458786980 0x24100480a2c3c34c 0x3210007078787997 0x6990800383c3c3cc

def z557 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x7398f07c78180001 0x6b9cc783e3c0c000

def z558 : W := mkw 0x87f8f9dc7df86b8a 0x2c3fc7cee3efc35c 0x73b8f1fc79f87997 0x6b9dc78fe3cfc3cc

def z559 : W := mkw 0x0002042200000001 0x0000102110000000 0xbc560e720666001f 0xfde2b07390333000

def z560 : W := mkw 0x05fdfbc96f80760e 0xb82fefde4b7c03b0 0xf7e9ff8dff807e0e 0xe7bf4ffc6ffc03f0

def z561 : W := mkw 0x016549010000000e 0x800b2a4808000000 0x0021018180000000 0x0001080c0c000000

def z562 : W := mkw 0x2000008080808220 0x0100000404040411 0xd829818f81818669 0xbec14c0c7c0c0c33

def z563 : W := mkw 0x20008080c080c220 0x2100040406040611 0xd8218183c181c66a 0xb6c10c0c1e0c0e33

def z564 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x980000024199c7fb 0xbcc00000120cce3f

def z565 : W := mkw 0x829ab47e58786981 0x2414d5a3f2c3c34c 0xf7defe7e78787997 0xffbef7f3f3c3c3cc

def z566 : W := mkw 0x83ff6d7f1078098f 0x841ffb6bf883c04c 0xf5ffffff80780191 0xffaffffffc03c00c

def z567 : W := mkw 0x05ffffeb4a80760f 0xb82fffff5a5403b0 0xf5ffffff80007e01 0xffaffffffc0003f0

def z568 : W := mkw 0x05f8db807fd0760a 0x382fc6dc03fe83b0 0xf7f8ff807ff87e1e 0xefbfc7fc03ffc3f0

def z569 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xbbd600003e66001e 0x1ddeb00001f33000

def z570 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x5029818dc199c193 0x2a814c0c6e0cce0c

def z571 : W := mkw 0x040092806f807600 0x38200494037c03b0 0xd22081807f807e0e 0xa691040c03fc03f0

def z572 : W := mkw 0x4562dfa26f82764b 0x3a2b16fd137c13b2 0xffe6ff827f867e6e 0xf7ff37fc13fc33f3

def z573 : W := mkw 0x0160000000000008 0x000b000000000000 0xf1e0000000000000 0x078f000000000000

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x2056000006660004 0x0102b00000333000

def z575 : W := mkw 0x41ff6f7b02221d4f 0x920ffb7bd81110ea 0xf5ffffff80007fe1 0xffaffffffc0003ff

def z576 : W := mkw 0x4560db906fa27f4a 0x3a2b06dc837d13fa 0xffe0ff807fe67ffe 0xe7ff07fc03ff33ff

def z577 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0x0180700000000000 0x000c038000000000

def z578 : W := mkw 0x01fd00002505000c 0x400fe80001282800 0xf9ff000007878008 0x1fcff800003c3c00

def z579 : W := mkw 0x0000900048006000 0x2000048002400300 0x4380f00078000000 0x021c078003c00000

def z580 : W := mkw 0x0000021002201d00 0x10000010801100e8 0xb4500e7006607f9f 0xeda28073803303fc

def z581 : W := mkw 0x016049000000000a 0x000b024800000000 0xf5e9ff8f80000001 0xffaf4ffc7c000000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000000200000001 0xbc80000010000000

def z583 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4388f00c78787996 0x021c478063c3c3cc

def z584 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd020818fc18047eb 0xa681040c7e0c023f

def z585 : W := mkw 0xa0988084d0d8c2a0 0x2504c4042686c615 0xfbb9818ff9f9c7ff 0xbfddcc0c7fcfce3f

def z586 : W := mkw 0xa0008004c008c0a0 0x2500040026004605 0x5809800fc019c1f3 0x3ac04c007e00ce0f

def z587 : W := mkw 0x009a246a00000001 0x0004d12350000000 0xf5defe7e00000001 0xffaef7f3f0000000

def z588 : W := mkw 0x01fd00103575090c 0x400fe80081aba848 0xfbff00707ffff99f 0x7fdff80383ffffcc

def z589 : W := mkw 0xc202b67e4a2a7dc1 0x361015b3f25153ee 0x0400fe7e00007fe1 0xe02007f3f00003ff

def z590 : W := mkw 0x0000000010550000 0x400000000082a800 0x08000000007f8010 0x004000000003fc00

def z591 : W := mkw 0x4002062202021441 0x12001031101010a2 0x9c460e02060647fb 0xbce230701030323f

def z592 : W := mkw 0x009f246b00000005 0x8004f92358000000 0xb45f0e7f80000001 0xfda2f873fc000000

def z593 : W := mkw 0x4402dfb24aa27f43 0x3a2016fd925513fa 0xbc56fff206667fff 0xfde2b7ff903333ff

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xf87f000047ff801e 0x1fc3f800023ffc00

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x7180f00000000000 0x638c078000000000

def z596 : W := mkw 0x0000000025000000 0x0000000001280000 0x020000007f80000e 0x0010000003fc0000

def z597 : W := mkw 0xa0000004800880a0 0x0500000024004405 0x08000000001981f0 0x004000000000cc0f

def z598 : W := mkw 0xa7f8fbdcfff8ffaa 0x3d3fc7dee7ffc7fd 0xfff9fffffff9ffff 0xffffcfffffffcfff

def z599 : W := mkw 0x0000808040804200 0x2000040402040210 0x0000818000004600 0xa000040c00000230

def z600 : W := mkw 0x05f8fbc86f80760a 0x382fc7de437c03b0 0xf7f8fffc7f807e0f 0xefbfc7ffe3fc03f0

def z601 : W := mkw 0x600206a282829661 0x13001035141414b3 0x8c670f8387878668 0x9463387c1c3c3c33

def z602 : W := mkw 0x05604b802780160a 0x182b025c013c00b0 0xb4600f8007807e0e 0xe5a3007c003c03f0

def z603 : W := mkw 0x009d000010550004 0x4004e8000082a800 0x7b9f0000787f8016 0x1bdcf80003c3fc00

def z604 : W := mkw 0x016500002505000c 0x400b280001282800 0xfbe700007f87800e 0x17df380003fc3c00

def z605 : W := mkw 0x41624f3202221d4b 0x120b1279901110ea 0xfdf6fff206667fff 0xffefb7ff903333ff

def z606 : W := mkw 0x8298b05c7d7d6980 0x6414c582e3ebeb4c 0x7b98f07c7ffff99f 0x6bdcc783e3ffffcc

def z607 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x4bbf000079ff8010 0x1a5df80003cffc00

def z608 : W := mkw 0xe00284b6c0aacbe1 0x27001425b605565f 0xd83f81ffc1ffc7fb 0xbec1fc0ffe0ffe3f

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8560002066647ff 0xbdc2b0001033323f

def z610 : W := mkw 0x45fffffb6fa27f4f 0xba2fffffdb7d13fa 0xffffffffffe67fff 0xffffffffffff33ff

def z611 : W := mkw 0x0562dfa26f80760b 0x382b16fd137c03b0 0xf7f6fff27f807e0f 0xffbfb7ff93fc03f0

def z612 : W := mkw 0x8760db947ff87f8a 0x3c3b06dca3ffc3fc 0xf7e0ff807ff87f9e 0xe7bf07fc03ffc3fc

def z613 : W := mkw 0x03ff7d7b1870290f 0x801ffbebd8c38148 0xf7ffffffb8603805 0xffbffffffdc301c0

def z614 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x73b9000079f98016 0x0b9dc80003cfcc00

def z615 : W := mkw 0x0000808040804200 0x2000040402040210 0xd82981804199c61a 0xbec14c0c020cce30

def z616 : W := mkw 0x409a267a02221d41 0x1204d133d01110ea 0xfddefe7e06667fff 0xffeef7f3f03333ff

def z617 : W := mkw 0xe1ff86b6f7ffdfed 0x770ffc35b7bffeff 0xffff8fffffffffff 0xfffffc7fffffffff

def z618 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x8c560e72066607f9 0x9c62b0739033303f

def z619 : W := mkw 0x0098000000000000 0x0004c00000000000 0x7198000000000000 0x0b8cc00000000000

def z620 : W := mkw 0x01674d232505000f 0xc00b3a6919282800 0x8c670f8387878008 0x9463387c1c3c3c00

def z621 : W := mkw 0x8698b2dc7ff87f80 0x3c34c596e3ffc3fc 0x7398f07c7ff87f9f 0x6b9cc783e3ffc3fc

def z622 : W := mkw 0x0000808040804200 0x2000040402040210 0x000000004180460a 0x00000000020c0230

def z623 : W := mkw 0x45624fb227a21f4b 0x1a2b127d913d10fa 0xbc760ff207e67fff 0xfde3b07f903f33ff

def z624 : W := mkw 0x83f8b05c7d786988 0x241fc582e3ebc34c 0xf3f8f07c7ff8799f 0x6f9fc783e3ffc3cc

def z625 : W := mkw 0x05fd5b003f55340e 0x582fead801faa9a0 0x27d67e003e663804 0x413eb3f001f331c0

def z626 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x0809818f8019c7f1 0xb8404c0c7c00ce3f

def z627 : W := mkw 0x0000808040804200 0x2000040402040210 0xd029818fc180460b 0xbe814c0c7e0c0230

def z628 : W := mkw 0x056059002d00200a 0x082b02c801680100 0x0380700038000000 0x001c038001c00000

def z629 : W := mkw 0x820090147d7d6980 0x64100480a3ebeb4c 0x0a0000007ffff99e 0x0050000003ffffcc

def z630 : W := mkw 0xa560d984ed88e2aa 0x2d2b06cc276c4715 0x43a9f18df9998000 0x021d4f8c6fcccc00

def z631 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x8821818f8181c7e9 0xb4410c0c7c0c0e3f

def z632 : W := mkw 0x0160020027001408 0x100b0010013800a0 0xf7e00e007f807e0e 0xe7bf007003fc03f0

def z633 : W := mkw 0xc298b25c5a7a7dc0 0x3614c592e2d3d3ee 0x7b98f07c7e7e7fff 0x6bdcc783e3f3f3ff

def z634 : W := mkw 0x009d000010550004 0x4004e8000082a800 0xd83f000041ff801a 0x1ec1f800020ffc00

def z635 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3ff00003e660004 0x1f9ff80001f33000

def z636 : W := mkw 0x83fdb05c5878698c 0x241fed82e2c3c34c 0xf3fff07c78787997 0x7f9fff83e3c3c3cc

def z637 : W := mkw 0xa0008084f5ddc2a0 0x6500040427aeee15 0xda29818fffffc7ff 0xbed14c0c7ffffe3f

def z638 : W := mkw 0x0098000010500000 0x0004c00000828000 0x4388000078180000 0x021c400003c0c000

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000007806 0x61800000000003c0

def z640 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0xf5e9ff8d80000000 0xe7af4ffc6c000000

def z641 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4400e7206007fef 0xe5a20073903003ff

def z642 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4829818fc19981f1 0x1a414c0c7e0ccc0f

def z643 : W := mkw 0xa0008094c0a8cba0 0x25000404a605465d 0xf83981ffc1f9ffff 0xffc1cc0ffe0fcfff

def z644 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x3010f07c00607997 0x69808783e00303cc

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000004193 0x288000000000020c

def z646 : W := mkw 0x87f8fbcc7fd8768a 0x3c3fc7de63fec3b4 0xf7e8ff8c7f987e0e 0xe7bf47fc63fcc3f0

def z647 : W := mkw 0x0000800040004000 0x2000040002000200 0x5000800040004002 0x2280040002000200

def z648 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x73de00007e7e0016 0x0b9ef00003f3f000

def z649 : W := mkw 0x0000020002001400 0x10000010001000a0 0x0000000006007e0e 0x00000000003003f0

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x7380000078000006 0x039c000003c00000

def z651 : W := mkw 0xc29a267e127a1dc1 0x1614d133f093d0ee 0xbc5e0e7e067e7fff 0xfde2f073f033f3ff

def z652 : W := mkw 0x4002043200220941 0x020010219001104a 0xb8560072066601ff 0x1dc2b0039033300f

def z653 : W := mkw 0x41674f230202144f 0x920b3a79181010a2 0x8c670f8386060668 0x9463387c1c303033

def z654 : W := mkw 0x87ffffff7ff87f8f 0xbc3ffffffbffc3fc 0xf7fffffffff87f9f 0xffbfffffffffc3fc

def z655 : W := mkw 0x440092906fa27f40 0x3a200494837d13fa 0x0a0000007fe67ffe 0x0050000003ff33ff

def z656 : W := mkw 0x009d000010550004 0x4004e8000082a800 0x0016000000660000 0x0000b00000033000

def z657 : W := mkw 0xc202b67e4a2a7dc1 0x361015b3f25153ee 0xbc56fe7e06667fff 0xfde2b7f3f03333ff

def z658 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xc5efff8f80000000 0x962f7ffc7c000000

def z659 : W := mkw 0x409f267b02221d45 0x9204f933d81110ea 0xbc5f0e7f86667fff 0xfde2f873fc3333ff

def z660 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x5388f00c78184193 0x2a9c478063c0c20c

def z661 : W := mkw 0x01ff4d230000000f 0x800ffa6918000000 0xf5ff0f8380000000 0x9faff87c1c000000

def z662 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0xfbff818dffff801e 0x1fdffc0c6ffffc00

def z663 : W := mkw 0xa00284a6c088c2a1 0x2500142536044615 0xfc7f8fffc199c7fb 0xffe3fc7ffe0cce3f

def z664 : W := mkw 0xe0020436802a89e1 0x07001021b401544f 0x081f007f807f81f1 0x1840f803fc03fc0f

def z665 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x43a0f1807f807e0e 0x021d078c03fc03f0

def z666 : W := mkw 0xe1ffefffc2aadfef 0xb70fff7ffe1556ff 0xfdffffffc7ffffff 0xffeffffffe3fffff

def z667 : W := mkw 0x01ff6d7b0020090f 0x800ffb6bd8010048 0xf5ffffff80607997 0xffaffffffc0303cc

def z668 : W := mkw 0x81fd8004755d408c 0x640fec0023aaea04 0xfbff800c7fffc19f 0x3fdffc0063fffe0c

def z669 : W := mkw 0x040092807fd57600 0x7820049403feabb0 0x0a0000007ffffe1e 0x0050000003fffff0

def z670 : W := mkw 0x409f043210770945 0x4204f8219083b84a 0x081f0072007f81f1 0x1840f8039003fc0f

def z671 : W := mkw 0xa1fd0004b55d80ac 0x450fe80025aaec05 0xfbff000fffff81ff 0x1fdff8007ffffc0f

def z672 : W := mkw 0x0000001000200900 0x0000000080010048 0x0010007000600191 0x080080038003000c

def z673 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3ff000079998000 0x1f9ff80003cccc00

def z674 : W := mkw 0x0098000010500000 0x0004c00000828000 0xfbde00007e7e001e 0x1fdef00003f3f000

def z675 : W := mkw 0x600206b282a29f61 0x13001035941514fb 0xbc770ff387e7ffff 0xfde3b87f9c3f3fff

def z676 : W := mkw 0x05fd92807fd5760c 0x782fec9403feabb0 0xfbff00007ffffe1e 0x1fdff80003fffff0

def z677 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0xd420ff8041807e0a 0xe6a107fc020c03f0

def z678 : W := mkw 0xa4009284ef88f6a0 0x3d200494277c47b5 0xda29818fff99ffff 0xbed14c0c7ffccfff

def z679 : W := mkw 0x8000800440084080 0x2400040022004204 0x4008800c40180000 0x020044006200c000

def z680 : W := mkw 0x01f8000035500008 0x000fc00001aa8000 0xf3f800007ff8001e 0x0f9fc00003ffc000

def z681 : W := mkw 0x0098204810500000 0x0004c10240828000 0x7398f07c78780017 0x6b9cc783e3c3c000

def z682 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x020000003e660004 0x0010000001f33000

def z683 : W := mkw 0xc20296365a7a7dc1 0x361014b1b2d3d3ee 0xbe560e727e7e7fff 0xfdf2b07393f3f3ff

def z684 : W := mkw 0x0000900048006000 0x2000048002400300 0x0200000078007806 0x0010000003c003c0

def z685 : W := mkw 0x83fdb04c7d5d608c 0x641fed8263eaeb04 0xfbfff00c7fff801e 0x1fdfff8063fffc00

def z686 : W := mkw 0x0007042300000005 0x8000382118000000 0x0007000380000000 0x100038001c000000

def z687 : W := mkw 0x40026f7b02221d43 0x9200137bd81110ea 0x0400ffff80007fe1 0xe02007fffc0003ff

def z688 : W := mkw 0xc0028636422a5dc1 0x36001431b21152ee 0xfc5e8e7e467e7fff 0xffe2f473f233f3ff

def z689 : W := mkw 0x01fd808075d5420c 0x600fec0403aeaa10 0xfbff81807fffc61e 0xbfdffc0c03fffe30

def z690 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xc7e0ff807f800608 0x863f07fc03fc0030

def z691 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd829818dc199801a 0x1ec14c0c6e0ccc00

def z692 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x34560e7006667997 0x69a2b073803333cc

def z693 : W := mkw 0x0000000025050000 0x4000000001282800 0x0800000007878008 0x00400000003c3c00

def z694 : W := mkw 0x040090806d806200 0x28200484036c0310 0x0200000079800000 0x0010000003cc0000

def z695 : W := mkw 0x0400db806f807602 0x382006dc037c03b0 0x0600ff807f807e0e 0xe03007fc03fc03f0

def z696 : W := mkw 0x8298204c10580080 0x0414c1026082c004 0x0008000c00180000 0x000040006000c000

def z697 : W := mkw 0xa298b0ccd8d8e2a0 0x2514c58666c6c715 0xdba9f18ff999c7fb 0xbedd4f8c7fccce3f

def z698 : W := mkw 0x01fd90007d55600c 0x600fec8003eaab00 0xfbfff0007ffff81e 0x7fdfff8003ffffc0

def z699 : W := mkw 0x8000000400080080 0x0400000020004004 0x0008000c00180191 0x080040006000c00c

def z700 : W := mkw 0x01fffd6b4800600f 0xa00fffeb5a400300 0xf7fffffff8007807 0xffbfffffffc003c0

def z701 : W := mkw 0x41674f3302221d4f 0x920b3a79981110ea 0xbc770ff386667fff 0xfde3b87f9c3333ff

def z702 : W := mkw 0x41ff6f6b0202144f 0x920ffb7b581010a2 0xfdffffff86060669 0xffeffffffc303033

def z703 : W := mkw 0x0402ffeb4a807603 0xb82017ff5a5403b0 0x0400ffff80007e01 0xe02007fffc0003f0

def z704 : W := mkw 0x8000800440084080 0x2400040022004204 0xd808800e401847fb 0xbec044007200c23f

def z705 : W := mkw 0x41ff06223757144d 0x520ff83111bab8a2 0xffff0e027fff867e 0x9ffff87013fffc33

def z706 : W := mkw 0x0160000025000008 0x000b000001280000 0x43a0000079800000 0x021d000003cc0000

def z707 : W := mkw 0xa5605b04af08b4aa 0x1d2b02d8257845a5 0x2fc97e0fbe19b9f5 0x597e4bf07df0cdcf

def z708 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xfdffffffc1ff801b 0xffeffffffe0ffc00

def z709 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0xd43fffff80000001 0xfea1fffffc000000

def z710 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xfffffffff9f9801f 0xffffffffffcfcc00

def z711 : W := mkw 0x0565db806f85760e 0x782b2edc037c2bb0 0xffefff807f9ffe1e 0xffff7ffc03fcfff0

def z712 : W := mkw 0xa1ffedefc088c2af 0xa50fff6f7e044615 0x2dd67e704199c7fa 0x416eb3f3820cce3f

def z713 : W := mkw 0x05624fa32780160b 0x982b127d193c00b0 0x84600f8387800608 0x8423007c1c3c0030

def z714 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xabf700007fff801e 0x155fb80003fffc00

def z715 : W := mkw 0xa0009084c888e2a0 0x2500048426444715 0xd829f18fc199fffb 0xfec14f8c7e0ccfff

def z716 : W := mkw 0x41fd6b5902221d4e 0x920feb5ac81110ea 0x49a9f18d86667ffe 0x024d4f8c6c3333ff

def z717 : W := mkw 0x800092044a087480 0x34000490225043a4 0xffc8fe0e7e187fff 0xfffe47f073f0c3ff

def z718 : W := mkw 0xa098b0ccc888e2a0 0x2504c58666444715 0xfbb9f1fff999ffff 0xffddcf8fffcccfff

def z719 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x73b9f1fff9f9fff7 0xeb9dcf8fffcfcfff

def z720 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c38607985 0x6b9cc783e1c303cc

def z721 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x7390f07c78607997 0x6b9c8783e3c303cc

def z722 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd86f818fc79fc7fb 0xbec37c0c7e3cfe3f

def z723 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xf7e9ff8fff987f9f 0xffbf4ffc7ffcc3fc

def z724 : W := mkw 0x01fd49003555000e 0x400fea4801aaa800 0xffffff8fffff801f 0xfffffffc7ffffc00

def z725 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x63b9f1fdf9f9b804 0x431dcf8fefcfcdc0

def z726 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe0ff8fff99ffff 0xe7ff07fc7ffccfff

def z727 : W := mkw 0x829db05c587d6984 0x6414ed82e2c3eb4c 0xfbdff07c7e7ff99f 0x7fdeff83e3f3ffcc

def z728 : W := mkw 0x41ff063237771d4d 0x520ff83191bbb8ea 0x47a90e727999ffe1 0xe23d487393cccfff

def z729 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5fffffd80000000 0xe7afffffec000000

def z730 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xdba9f1fff999fffb 0xfedd4f8fffcccfff

def z731 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x75fffffd80000001 0x6bafffffec000000

def z732 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc760e7247e67fff 0xffe3b073923f33ff

def z733 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffffc7ff801f 0xffeffffffe3ffc00

def z734 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe9ff8fff99fe1f 0xffff4ffc7ffccff0

def z735 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7398f1fdf8787997 0x6b9cc78fefc3c3cc

def z736 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x5029818fc199c7f3 0xaa814c0c7e0cce3f

def z737 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x65ffffff80000001 0x5b2ffffffc000000

def z738 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3b9f07c78787997 0x7f9dcf83e3c3c3cc

def z739 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0x7b98f07c7879f9f7 0x6bdcc783e3c3cfcf

def z740 : W := mkw 0x009d000035550004 0x4004e80001aaa800 0xda3f00007fff801e 0x1ed1f80003fffc00

def z741 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x3390f07c38607997 0x699c8783e1c303cc

def z742 : W := mkw 0x0098000010500000 0x0004c00000828000 0xfbff00007fff801e 0x1fdff80003fffc00

def z743 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe8ff8c7f99ffff 0xefff47fc63fccfff

def z744 : W := mkw 0x05674f232700140f 0x982b3a79193800a0 0x84670f8386000000 0x9423387c1c300000

def z745 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7390f07c78607987 0x639c8783e3c303cc

def z746 : W := mkw 0x016500003555000c 0x400b280001aaa800 0xfbe700007fff801e 0x17df380003fffc00

def z747 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0xfbb8f1fe79f87fff 0xffddc78ff3cfc3ff

def z748 : W := mkw 0x0000101008202900 0x0000008080410148 0x3390707038607997 0x699c838381c303cc

def z749 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3b8f07c79f8799f 0x6f9dc783e3cfc3cc

def z750 : W := mkw 0x0098b04858506000 0x2004c58242c28300 0x7398f07c78787817 0x6b9cc783e3c3c3c0

def z751 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff8fff807e0f 0xe7bf07fc7ffc03f0

def z752 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7ffffffb8000001 0xffbffffffdc00000

def z753 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe0ff8fff807fff 0xffff07fc7ffc03ff

def z754 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x2b90707079f9fffe 0x415c838383cfcfff

def z755 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x43a9f1fff999ffe1 0xe21d4f8fffcccfff

def z756 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xbfc07e023e007fff 0xfdfe03f011f003ff

def z757 : W := mkw 0x8200b05c58786980 0x24100582e2c3c34c 0x7380f07c78787997 0x639c0783e3c3c3cc

def z758 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xc7e0ff807f807e0e 0x863f07fc03fc03f0

def z759 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x5388f07c78187993 0x6a9c4783e3c0c3cc

def z760 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfbb9f07c79f9ffff 0x7fddcf83e3cfcfff

def z761 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x73def07c7e7e7997 0x6b9ef783e3f3f3cc

def z762 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x25dfffff80000001 0xf92efffffc000000

def z763 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff800c7fff801f 0x3fdffc0063fffc00

def z764 : W := mkw 0xa565db84ef8df6ae 0x7d2b2edc277c6fb5 0xffefff8fff9fffff 0xffff7ffc7ffcffff

def z765 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x6390f07078603804 0x431c878383c301c0

def z766 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0xf7a0ff8079807e0e 0xe7bd07fc03cc03f0

def z767 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390707078783816 0x411c838383c3c1c0

def z768 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0x759fffff80000001 0xfbacfffffc000000

def z769 : W := mkw 0x0000901048206900 0x2000048082410348 0x7380f07078007987 0x639c078383c003cc

def z770 : W := mkw 0x41674f232707144f 0xd20b3a79193838a2 0x8c670f8387878668 0x9463387c1c3c3c33

def z771 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3d8f07c7e78799f 0x6f9ec783e3f3c3cc

def z772 : W := mkw 0x0200b05848206900 0x20100582c2410348 0x7380f07078007806 0x639c078383c003c0

def z773 : W := mkw 0x8560db046f08748a 0x3c2b06d8237843a4 0x77c8fe0c7e187997 0x6bbe47f063f0c3cc

def z774 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x7388f07c78187997 0x6b9c4783e3c0c3cc

def z775 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0xf7e0fe007f80780e 0x67bf07f003fc03c0

def z776 : W := mkw 0xc29ab66e5a5a74c1 0x3614d5b372d2d3a6 0xcfcefe0e7e1e0668 0x967e77f073f0f033

def z777 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe6ff807f867e0e 0xf7ff37fc03fc33f0

def z778 : W := mkw 0x01fd69490000000e 0x800feb4a48000000 0xf5f9fffd80000001 0xefafcfffec000000

def z779 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0x2590ffff80000001 0xe12c87fffc000000

def z780 : W := mkw 0x0160d9006d00600a 0x200b06c803680300 0xf7e0ff807f80780e 0xe7bf07fc03fc03c0

def z781 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b99f07c7879f997 0x7bdccf83e3c3cfcc

def z782 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x77e0ff807f807806 0x63bf07fc03fc03c0

def z783 : W := mkw 0xa0000084808882a0 0x0500000424044415 0xd829018fc19987fb 0x9ec1480c7e0ccc3f

def z784 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xc829818fc199c7e9 0xb6414c0c7e0cce3f

def z785 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390707038607984 0x411c838381c303cc

def z786 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xfdffffff867f801f 0xffeffffffc33fc00

def z787 : W := mkw 0x4562ddb26da26b4b 0x2a2b16ed936d135a 0x4bb6f1f279e601f1 0x1a5db78f93cf300f

def z788 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b98f07c79f9f99f 0x6bdcc783e3cfcfcc

def z789 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc568fff86667fff 0xfde2b47ffc3333ff

def z790 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x6398707078783804 0x431cc38383c3c1c0

def z791 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0xf5b9ffff80000001 0xffadcffffc000000

def z792 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x6398f07c38603804 0x431cc783e1c301c0

def z793 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00707fff801f 0x7fdff80383fffc00

def z794 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbfff07c7ffff99f 0x7fdfff83e3ffffcc

def z795 : W := mkw 0x000012000a003400 0x10000090005001a0 0x27c07e003e003804 0x413e03f001f001c0

def z796 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffffff8fffffffff 0xfffffffc7fffffff

def z797 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xffe97e007f99b81e 0x5fff4bf003fccdc0

def z798 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x8c560e7206667fff 0x9c62b073903333ff

def z799 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x2456ffff80000001 0xe122b7fffc000000

def z800 : W := mkw 0xe202b6fecaaaffe1 0x371015b7f65557ff 0x0400ffff80007fe1 0xe02007fffc0003ff

def z801 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x47a0ff8079803800 0x423d07fc03cc01c0

def z802 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfbb8f1fc79f9ffff 0xefddc78fe3cfcfff

def z803 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbdef07e7e7e7fff 0xffdef783f3f3f3ff

def z804 : W := mkw 0x01ff6d6b3550000f 0x800ffb6b59aa8000 0xf7fffffffff8001f 0xffbfffffffffc000

def z805 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7b99f07ff9f9ffff 0x7bdccf83ffcfcfff

def z806 : W := mkw 0x829a247e10780981 0x0414d123f083c04c 0x001e007e00780191 0x1800f003f003c00c

def z807 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5f6ffff80000001 0xe7afb7fffc000000

def z808 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b98f07e787879f7 0x7bdcc783f3c3c3cf

def z809 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff0183ffff801e 0x9fdff80c1ffffc00

def z810 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0x47a9fffff9998001 0xe23d4fffffcccc00

def z811 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3ff00007fff800e 0x079ff80003fffc00

def z812 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7ffffffffe6000f 0xffbfffffffff3000

def z813 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x2390f1ffb8607fe5 0xe11c878ffdc303ff

def z814 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4398f07c78787991 0x6a1cc783e3c3c3cc

def z815 : W := mkw 0xc29f247e107f09c5 0x4614f923f083f84e 0x081f007e007f81f1 0x1840f803f003fc0f

def z816 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xf7e1ff81ff81fe0e 0xe7bf0ffc0ffc0ff0

def z817 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xe5ffffff80000000 0xd72ffffffc000000

def z818 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0xfb99f07ff879ffff 0xffdccf83ffc3cfff

def z819 : W := mkw 0x0098000035550000 0x4004c00001aaa800 0xfbde00007fff801e 0x1fdef00003fffc00

def z820 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe0ff827f99ffff 0xffff07fc13fccfff

def z821 : W := mkw 0xa1fd8084f5ddc2ac 0x650fec0427aeee15 0x23d6818fbe6647e5 0xa11eb40c7df3323f

def z822 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x4429ffff80000001 0xe2214ffffc000000

def z823 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390707038607985 0x611c838381c303cc

def z824 : W := mkw 0x016500003555000c 0x400b280001aaa800 0x0a4600007fff801e 0x0052300003fffc00

def z825 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0x4780ff8078007e00 0xe23c07fc03c003f0

def z826 : W := mkw 0x0565db806f85760e 0x782b2edc037c2bb0 0xf7e6ff807f867e0e 0xe7bf37fc03fc33f0

def z827 : W := mkw 0x009a246a00000001 0x0004d12350000000 0xf5ffffff80000001 0xffaffffffc000000

def z828 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xffe1ff83ff81ffff 0xffff0ffc1ffc0fff

def z829 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0xd46fffff80000001 0xfea37ffffc000000

def z830 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2398707c78787997 0x491cc383e3c3c3cc

def z831 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0x25c0ffff80000001 0xe12e07fffc000000

def z832 : W := mkw 0x87f86bdc37f81f8a 0x1c3fc35ee1bfc0fc 0x84780ffc07f80799 0x8c23c07fe03fc03c

def z833 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xdc29ffffc199801b 0xfee14ffffe0ccc00

def z834 : W := mkw 0x0560db806f85760a 0x782b06dc037c2bb0 0xffe0ff807f87fe0e 0xe7ff07fc03fc3ff0

def z835 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x8829818f8199c7f9 0xbc414c0c7c0cce3f

def z836 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff807f807f9f 0xefbf07fc03fc03fc

def z837 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xa7e07f807f807e0e 0xc53f03fc03fc03f0

def z838 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xfffffffdffff801e 0x5fffffffeffffc00

def z839 : W := mkw 0xe402dfb6caaaffe3 0x3f2016fdb65557ff 0x0400ffff80007fe1 0xe02007fffc0003ff

def z840 : W := mkw 0x0565db806f80760e 0x382b2edc037c03b0 0xf7e7ff807f807e0e 0xf7bf3ffc03fc03f0

def z841 : W := mkw 0x829f247f107d0985 0xc414f923f883e84c 0x081f007f807f8191 0x1840f803fc03fc0c

def z842 : W := mkw 0xa29db05cd87de9a4 0x6514ed82e6c3ef4d 0x7b9ff07ff87ff9f7 0x7bdcff83ffc3ffcf

def z843 : W := mkw 0x000092804a807600 0x30000494025403b0 0xf7e0ff807f807e0e 0xe7bf07fc03fc03f0

def z844 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x6bff00007fff8014 0x1b5ff80003fffc00

def z845 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x4380f07c78007981 0x621c0783e3c003cc

def z846 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x45a9fffd80000000 0x422d4fffec000000

def z847 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf398f07e78787997 0xff9cc783f3c3c3cc

def z848 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0xfbff70007fff801e 0x1fdffb8003fffc00

def z849 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xfffffffffe7e001f 0xfffffffffff3f000

def z850 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0xf7e0ff803f803e0c 0xe7bf07fc01fc01f0

def z851 : W := mkw 0xe00286b6c2aadfe1 0x37001435b61556ff 0x647f8ffdc7ffb804 0x4323fc7fee3ffdc0

def z852 : W := mkw 0x409f247b10770945 0xc204f923d883b84a 0x081f007f807f81f1 0x1840f803fc03fc0f

def z853 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5fffffd80000000 0x5fafffffec000000

def z854 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x6398f07c78783995 0x4b1cc783e3c3c1cc

def z855 : W := mkw 0x8298b05c48286980 0x2414c582e241434c 0x7398f07c78007987 0x6b9cc783e3c003cc

def z856 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xf3b9f1fff9f9f997 0xff9dcf8fffcfcfcc

def z857 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7fffffffe7e0017 0xffbffffffff3f000

def z858 : W := mkw 0x01624d220000000b 0x000b126910000000 0xf5ffffff80000001 0xffaffffffc000000

def z859 : W := mkw 0xc29aa47e507a49c1 0x2614d523f283d24e 0xd81e807e407e47fb 0xbec0f403f203f23f

def z860 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2398f07c38787995 0x691cc783e1c3c3cc

def z861 : W := mkw 0x45674fa32782164f 0x9a2b3a7d193c10b2 0x8c670f8387860668 0x9463387c1c3c3033

def z862 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc770ff386667fff 0xfde3b87f9c3333ff

def z863 : W := mkw 0x8367dd375878698f 0xa41b3ee9bac3c34c 0x86670f83f8787996 0x9433387c1fc3c3cc

def z864 : W := mkw 0x01f869480000000a 0x000fc34a40000000 0xf5f9ffff80000001 0xffafcffffc000000

def z865 : W := mkw 0x0000901048206900 0x2000048082410348 0x7390f07078607806 0x639c878383c303c0

def z866 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x24560e7006667fe4 0x4122b073803333ff

def z867 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe9ff8dff99fffe 0xe7ff4ffc6ffccfff

def z868 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e9ff807f807e0e 0xffbf4ffc03fc03f0

def z869 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x37c07e003e007806 0x61be03f001f003c0

def z870 : W := mkw 0x41ff6f7b37771d4f 0xd20ffb7bd9bbb8ea 0x27d67e703e663804 0x413eb3f381f331c0

def z871 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0x0418ffff80000001 0xe820c7fffc000000

def z872 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x0380f07c38007981 0x601c0783e1c003cc

def z873 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xcbff00007fff8018 0x1e5ff80003fffc00

def z874 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0x0446ffff80000001 0xe02237fffc000000

def z875 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xd5a9ffff80000001 0xfead4ffffc000000

def z876 : W := mkw 0x049fb6eb6f807605 0xb824fdb75b7c03b0 0x021f007fff807e0f 0x1810f803fffc03f0

def z877 : W := mkw 0x049ddb805ad57606 0x7824eedc02d6abb0 0x0c1fff80007ffe10 0xf860fffc0003fff0

def z878 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xbbd600007fff801e 0x1ddeb00003fffc00

def z879 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0x0421ffff80000001 0xe0210ffffc000000

def z880 : W := mkw 0x0565db806f85760e 0x782b2edc037c2bb0 0xfff7ff807fe7fe1e 0xffffbffc03ff3ff0

def z881 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff80660011 0xffeffffffc033000

def z882 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x07807e0038003800 0x403c03f001c001c0

def z883 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff8000001b 0xffeffffffc000000

def z884 : W := mkw 0x65624fa2a782966b 0x1b2b127d153c14b3 0x8c670f8387878668 0x9463387c1c3c3c33

def z885 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7388f07c78187987 0x639c4783e3c0c3cc

def z886 : W := mkw 0x01fd20483555000c 0x400fe90241aaa800 0xfbff70707fff801e 0x5fdffb8383fffc00

def z887 : W := mkw 0x429a247a10720941 0x0214d123d083904a 0x08160072006601f1 0x1840b0039003300f

def z888 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x0416ffff80000001 0xf820b7fffc000000

def z889 : W := mkw 0x829db05c587d6984 0x6414ed82e2c3eb4c 0x7399f07c7879f997 0x6b9ccf83e3c3cfcc

def z890 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xffd60e727e667fff 0xfffeb07393f333ff

def z891 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf7fffffff8000007 0xffbfffffffc00000

def z892 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc560e7006667ffe 0x5de2b073803333ff

def z893 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xf7ffffffb8600005 0xffbffffffdc30000

def z894 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3b8f1fc78787997 0xef9dc78fe3c3c3cc

def z895 : W := mkw 0x829a247f10780981 0x8414d123f883c04c 0x0018007f80780191 0x0800c003fc03c00c

def z896 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2398707038783814 0x491cc38381c3c1c0

def z897 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff866647ff 0xffeffffffc33323f

def z898 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e9ff8fff99ffef 0xe7bf4ffc7ffccfff

def z899 : W := mkw 0x00026d6b35550003 0xc000136b59aaa800 0x0e00ffffffff801f 0xe07007fffffffc00

def z900 : W := mkw 0xa29db0dcd8fdeba4 0x6514ed86e6c7ef5d 0xfbbff1fff9ffffff 0xffddff8fffcfffff

def z901 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0x27c07e003f803e0c 0x413e03f001fc01f0

def z902 : W := mkw 0x0298b0d858f06b00 0x2014c586c2c78358 0xf3b0f1f079e07e0e 0xe79d878f83cf03f0

def z903 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x5408ffff80000001 0xeaa047fffc000000

def z904 : W := mkw 0x0000d90048006002 0x200006c802400300 0x7780ff8078007806 0xe3bc07fc03c003c0

def z905 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf83981ffc199c7fb 0xffc1cc0ffe0cce3f

def z906 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc560e7247ffffff 0xfde2b073923fffff

def z907 : W := mkw 0x229830d898f0ab20 0x0114c186c4c78559 0xabb171f3b9e1be6c 0xd55d8b8f9dcf0df3

def z908 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xa7e0ff803f807e0c 0xe53f07fc01fc03f0

def z909 : W := mkw 0x0098304808002000 0x0004c18240400100 0x7398f07c38003805 0x6b9cc783e1c001c0

def z910 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc5e0e72467e7fff 0xffe2f0739233f3ff

def z911 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x7398f07c78607807 0x6b9cc783e3c303c0

def z912 : W := mkw 0x01fd49013555000e 0xc00fea4809aaa800 0xfbff0181ffff801e 0x1fdff80c0ffffc00

def z913 : W := mkw 0x0565db806f85760e 0x782b2edc037c2bb0 0xf7e1ff807f81fe0e 0xe7bf0ffc03fc0ff0

def z914 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0x4588ffff80000001 0xe22c47fffc000000

def z915 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffffc1998001 0xffaffffffe0ccc00

def z916 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4560e7206667fe5 0xfda2b073903333ff

def z917 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x6bff00007fff801e 0x035ff80003fffc00

def z918 : W := mkw 0xa0009284ca88f6a0 0x35000494265447b5 0xffe9ff8fff99ffff 0xffff4ffc7ffccfff

def z919 : W := mkw 0xa200b0dcc8a8eba0 0x25100586e645475d 0xf3a0f1fff9807fef 0xe79d078fffcc03ff

def z920 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff807f803804 0xe7bf07fc03fc01c0

def z921 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x0780ff8038007e00 0xe03c07fc01c003f0

def z922 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xf5ffffff87800009 0xffaffffffc3c0000

def z923 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27d67e003e663804 0x413eb3f001f331c0

def z924 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff818dffff801e 0x1fdffc0c6ffffc00

def z925 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x47a0ff807f807e0e 0xe23d07fc03fc03f0

def z926 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfbfff1ffffffffff 0xffdfff8fffffffff

def z927 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7bb9f1fff9f9f9f7 0x7bddcf8fffcfcfcf

def z928 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xc829818fc199c7fa 0x96414c0c7e0cce3f

def z929 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0x0416ffff80000001 0xe020b7fffc000000

def z930 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xbc56ffff8666001f 0xfde2b7fffc333000

def z931 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x25d6fffd80000000 0x412eb7ffec000000

def z932 : W := mkw 0x009d000035550004 0x4004e80001aaa800 0x7b9f00007fff801e 0x1bdcf80003fffc00

def z933 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xd7a0ff8079807e0a 0xe6bd07fc03cc03f0

def z934 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0xfbfff18fffff801f 0xbfdfff8c7ffffc00

def z935 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xac560e7206667ffe 0xd562b073903333ff

def z936 : W := mkw 0x8200b05c48286980 0x24100582e241434c 0x2380f07c38007985 0x611c0783e1c003cc

def z937 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7b98f1fff9f9ffff 0xebdcc78fffcfcfff

def z938 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xbfd67e003e66381e 0x5dfeb3f001f331c0

def z939 : W := mkw 0x0160db004a00740a 0x300b06d8025003a0 0xf7e0ff807e007e0e 0xe7bf07fc03f003f0

def z940 : W := mkw 0x25605b80af80b62a 0x192b02dc057c05b1 0xafe17f83bf81be6c 0xd57f0bfc1dfc0df3

def z941 : W := mkw 0xa0000084808882a0 0x0500000424044415 0x9829018f8199c7fb 0xbcc1480c7c0cce3f

def z942 : W := mkw 0x029f247b10700905 0x8014f923d8838048 0x0016007000600000 0x0000b00380030000

def z943 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0x7398f07ff87879f7 0x6b9cc783ffc3c3cf

def z944 : W := mkw 0x01fa6d6b0000000b 0x800fd36b58000000 0xf5f8ffff80000001 0xefafc7fffc000000

def z945 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e0ff807f80380e 0xe7bf07fc03fc01c0

def z946 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0xb45fffff80000001 0xfda2fffffc000000

def z947 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27c0ff803e003804 0xe13e07fc01f001c0

def z948 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x67e0ff803e003804 0x433f07fc01f001c0

def z949 : W := mkw 0x01fd20483555000c 0x400fe90241aaa800 0xfbfff00c7fff801e 0x1fdfff8063fffc00

def z950 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e8ff8fff987fff 0xefbf47fc7ffcc3ff

def z951 : W := mkw 0x4562cfa26782564b 0x3a2b167d133c12b2 0xdc668f82478647fb 0xbee3347c123c323f

def z952 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4829818fc199c7fb 0xa2414c0c7e0cce3f

def z953 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x0580ffff80000001 0xe02c07fffc000000

def z954 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x7398707c78783997 0x4b9cc383e3c3c1cc

def z955 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x6398f07c78787985 0x631cc783e3c3c3cc

def z956 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390f07c38603805 0x611c8783e1c301c0

def z957 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xb5d6ffff80000001 0xfdaeb7fffc000000

def z958 : W := mkw 0x8000901448286980 0x24000480a241434c 0x7398f07c78787997 0x6b9cc783e3c3c3cc

def z959 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x2a5600007fff801e 0x0152b00003fffc00

def z960 : W := mkw 0x01626d6b2500000b 0x800b136b59280000 0xf7e0ffffff80000f 0xe7bf07fffffc0000

def z961 : W := mkw 0x0000000000000000 0x0000000000000000 0xd829818fc199c7fb 0xbec14c0c7e0cce3f

def z962 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7390707078603806 0x439c838383c301c0

def z963 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0xf5f6ffff80000001 0xffafb7fffc000000

def z964 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c0ff803e003804 0x413e07fc01f001c0

def z965 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x23d600007fff8004 0x011eb00003fffc00

def z966 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xfdffffffc79f801b 0xffeffffffe3cfc00

def z967 : W := mkw 0x0200305808202900 0x00100182c0410148 0x2380707038003804 0x411c038381c001c0

def z968 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0xf3b9f1fff9f87f9f 0xff9dcf8fffcfc3fc

def z969 : W := mkw 0xe562cfa6e78ad6eb 0x3f2b167d373c56b7 0xdc6f8f8fc79fc7fb 0xbee37c7c7e3cfe3f

def z970 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf839818fc1f9c7ff 0xbfc1cc0c7e0fce3f

def z971 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff86060009 0xffeffffffc303000

def z972 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7f6ff807fe67e0e 0xe7bfb7fc03ff33f0

def z973 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07e78787ff7 0xeb9cc783f3c3c3ff

def z974 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xa7e07e003f80380c 0x453f03f001fc01c0

def z975 : W := mkw 0x016059000800200a 0x000b02c800400100 0x27c07e0038003804 0x413e03f001c001c0

def z976 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xfffffffff999801b 0xffffffffffcccc00

def z977 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xf5ffffff80198001 0xffaffffffc00cc00

def z978 : W := mkw 0x01fd20483555000c 0x400fe90241aaa800 0xfbfff1ffffff801f 0xffdfff8ffffffc00

def z979 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x0400fffd80000000 0x402007ffec000000

def z980 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff807f80380e 0x47bf07fc03fc01c0

def z981 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x2c560e7206667fff 0x5962b073903333ff

def z982 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xf5ffffff86060001 0xffaffffffc303000

def z983 : W := mkw 0x829f247f10780985 0x8414f923f883c04c 0x001e007c00780191 0x0800f003e003c00c

def z984 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xfff6ff827fe67fff 0xffffb7fc13ff33ff

def z985 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0x27e07f803f803804 0x413f03fc01fc01c0

def z986 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e1ff83ff807e0e 0xf7bf0ffc1ffc03f0

def z987 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390f07c78787997 0x611c8783e3c3c3cc

def z988 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x7398f07c38783995 0x6b9cc783e1c3c1cc

def z989 : W := mkw 0x009a6d6b10500003 0x8004d36b58828000 0x7798fffff8780017 0xebbcc7ffffc3c000

def z990 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x73b9f1fdf8787997 0x6b9dcf8fefc3c3cc

def z991 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xffffffffff99801f 0xfffffffffffccc00

def z992 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7f6ff807f807e0e 0xffbfb7fc03fc03f0

def z993 : W := mkw 0x829fa47f50784985 0xa414fd23fa83c24c 0xd03f81ffc0784193 0xbe81fc0ffe03c20c

def z994 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x34560e7206667ff7 0xe9a2b073903333ff

def z995 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x2398707c38783804 0x411cc383e1c3c1c0

def z996 : W := mkw 0x016500003555000c 0x400b280001aaa800 0xda6f00007fff801e 0x1ed3780003fffc00

def z997 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c78783805 0x6b9cc783e3c3c1c0

def z998 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbb9f07e79f9ffff 0xffddcf83f3cfcfff

def z999 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xf3b8f1fff9f87fff 0xef9dc78fffcfc3ff

def z1000 : W := mkw 0xa0000084808882a0 0x0500000424044415 0xd829818f819987f9 0xbec14c0c7c0ccc3f

def z1001 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xffffffffff87800f 0xfffffffffffc3c00

def z1002 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffbfe7800d 0xfffffffffdff3c00

def z1003 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x75b9ffff80000001 0xebadcffffc000000

def z1004 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff827f807fef 0xe7bf07fc13fc03ff

def z1005 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc5e8e7e06667fff 0xffe2f473f03333ff

def z1006 : W := mkw 0x4560db806f82764a 0x3a2b06dc037c13b2 0xffe0ff807f867e6e 0xe7ff07fc03fc33f3

def z1007 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e07e003e003804 0x47bf03f001f001c0

def z1008 : W := mkw 0x016092006f007408 0x300b0490037803a0 0xf7e0fe007f807e0e 0xe7bf07f003fc03f0

def z1009 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xb7c07e003e003804 0xe5be03f001f001c0

def z1010 : W := mkw 0x829db05c58786984 0x2414ed82e2c3c34c 0x739ff07c78787997 0x7b9cff83e3c3c3cc

def z1011 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x4bbf00007fff801e 0x1a5df80003fffc00

def z1012 : W := mkw 0xc29a247e107a09c1 0x0614d123f083d04e 0x0018007e007801f1 0x0800c003f003c00f

def z1013 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe1ff8fff81ffef 0xf7ff0ffc7ffc0fff

def z1014 : W := mkw 0x0400db004a007402 0x382006d8025003a0 0x7780fe0078007806 0x63bc07f003c003c0

def z1015 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7398f07c78787ff7 0x6b9cc783e3c3c3ff

def z1016 : W := mkw 0x8365b05c6d2d698c 0x641b2d82e3696b4c 0x8867f07c0787f989 0x74433f83e03c3fcc

def z1017 : W := mkw 0x000092004a007400 0x30000490025003a0 0x77c0fe007e007806 0x63be07f003f003c0

def z1018 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff827f807e0f 0xffbf07fc13fc03f0

def z1019 : W := mkw 0x0160d9804880620a 0x200b06cc02440310 0xf7e0ff8079807e0e 0xe7bf07fc03cc03f0

def z1020 : W := mkw 0xa298305c9878a9a0 0x0514c182e4c3c54d 0x2b99707fb879b9f5 0x595ccb83fdc3cdcf

def z1021 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xa5f7ffff80000001 0xf52fbffffc000000

def z1022 : W := mkw 0x0567cfa36780560f 0xb82b3e7d1b3c02b0 0xd46f8f8fc780460b 0xbea37c7c7e3c0230

def z1023 : W := mkw 0xa400db84ca88f6a2 0x3d2006dc265447b5 0xffa9ff8ff999ffff 0xfffd4ffc7fcccfff

def z1024 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7399f07ff8787997 0x7b9ccf83ffc3c3cc

def z1025 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0x7399f07df879f997 0x6b9ccf83efc3cfcc

def z1026 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbb9f1fff8787fff 0xffddcf8fffc3c3ff

def z1027 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x3390707078787997 0x699c838383c3c3cc

def z1028 : W := mkw 0x0560db804a80760a 0x382b06dc025403b0 0xf7e0ff8078007e06 0xe7bf07fc03c003f0

def z1029 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7390f07038603804 0x639c878381c301c0

def z1030 : W := mkw 0x0098205810700900 0x0004c102c0838048 0x7398f07c78787997 0x6b9cc783e3c3c3cc

def z1031 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5e9ffff80000001 0xe7af4ffffc000000

def z1032 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xf7fffffff8180001 0xffbfffffffc0c000

def z1033 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e9ff8dff99ff9f 0xefbf4ffc6ffccffc

def z1034 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xffff0e007fff801e 0xfffff87003fffc00

def z1035 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0xfbb9f1fff879f9f7 0xffddcf8fffc3cfcf

def z1036 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0x67c0fe007e003804 0x433e07f003f001c0

def z1037 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff80600017 0xffaffffffc030000

def z1038 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe1ff83ff99fffe 0xf7ff0ffc1ffccfff

def z1039 : W := mkw 0x8098b04c48086080 0x2404c58262404304 0x7398f07c78187997 0x6b9cc783e3c0c3cc

def z1040 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffbe7f8015 0xfffffffffdf3fc00

def z1041 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x2390707038783994 0x411c838381c3c1cc

def z1042 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff803e007e04 0xe7bf07fc01f003f0

def z1043 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c0ff807f807e0e 0xe13e07fc03fc03f0

def z1044 : W := mkw 0x8298b05c587d6980 0x6414c582e2c3eb4c 0x7b98f07c787ff997 0x6bdcc783e3c3ffcc

def z1045 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf869818fc799c7ff 0xbfc34c0c7e3cce3f

def z1046 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398707078787997 0x6b9cc38383c3c3cc

def z1047 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd829818fc7ffc7ff 0xbec14c0c7e3ffe3f

def z1048 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffffc180000b 0xffaffffffe0c0000

def z1049 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x73b9f07c79f9f997 0x6b9dcf83e3cfcfcc

def z1050 : W := mkw 0x000092004a007400 0x30000490025003a0 0x7780fe0078007e06 0xe3bc07f003c003f0

def z1051 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfb98f07e79f9ffff 0xffdcc783f3cfcfff

def z1052 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x0a1600007fff801e 0x1850b00003fffc00

def z1053 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffffff807ffffe1e 0xfffffffc03fffff0

def z1054 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x67e07e007f803804 0x433f03f003fc01c0

def z1055 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe9ff8dff99fe1e 0xffff4ffc6ffccff0

def z1056 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x3398707c38787997 0x699cc383e1c3c3cc

def z1057 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe1ff807f81fe0e 0xf7ff0ffc03fc0ff0

def z1058 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xb7c07e003e00380e 0x45be03f001f001c0

def z1059 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xfffffffff9ff8011 0xffffffffffcffc00

def z1060 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390707078783804 0x411c838383c3c1c0

def z1061 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe9ff807f99fffe 0xffff4ffc03fccfff

def z1062 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd029818fc199c7eb 0xa6814c0c7e0cce3f

def z1063 : W := mkw 0x0000909048a06b00 0x2000048482450358 0xfbb0f1f279e07fff 0xffdd878f93cf03ff

def z1064 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xf7e8ff8c7f987e0e 0xe7bf47fc63fcc3f0

def z1065 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff81807fff801e 0xbfdffc0c03fffc00

def z1066 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c07e007f803804 0x413e03f003fc01c0

def z1067 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0xfbfff1fdffff801f 0x7fdfff8feffffc00

def z1068 : W := mkw 0x0098b05848206900 0x2004c582c2410348 0x7398f07c78607997 0x6b9cc783e3c303cc

def z1069 : W := mkw 0x0000900048006000 0x2000048002400300 0x7390f07078007807 0x6b9c878383c003c0

def z1070 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00007fffc7fe 0x1fdff80003fffe3f

def z1071 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xd420ffff80000001 0xe6a107fffc000000

def z1072 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffffffc7ff 0xfffffffffffffe3f

def z1073 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e0ff803e007e0e 0xe7bf07fc01f003f0

def z1074 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e9ff807f99fe0e 0xe7bf4ffc03fccff0

def z1075 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00007ffff81e 0x7fdff80003ffffc0

def z1076 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffffc0180013 0xffaffffffe00c000

def z1077 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x7bde00007fff801e 0x0bdef00003fffc00

def z1078 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x3410ffff80000001 0xe9a087fffc000000

def z1079 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff800047e1 0xffaffffffc00023f

def z1080 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xf3b9f1fdf9f9ff9f 0xef9dcf8fefcfcffc

def z1081 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x67e0ff807f807e04 0xe33f07fc03fc03f0

def z1082 : W := mkw 0x009d000035550004 0x4004e80001aaa800 0x0a1600007fff801e 0x0050b00003fffc00

def z1083 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xc5efffff80000001 0xf62f7ffffc000000

def z1084 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff807f807ffe 0xe7ff07fc03fc03ff

def z1085 : W := mkw 0x029d305818752904 0x4014e982c0c3a948 0x2b9f7070387fb814 0x595cfb8381c3fdc0

def z1086 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe9ff827f99ffff 0xffff4ffc13fccfff

def z1087 : W := mkw 0xc298b05c587a69c0 0x2614c582e2c3d34e 0x7b98f07c787e79f7 0x6bdcc783e3c3f3cf

def z1088 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e0ff8079807e00 0xe7bf07fc03cc03f0

def z1089 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xb7c0ff803e007e0e 0xe5be07fc01f003f0

def z1090 : W := mkw 0xa567cfa7e788d6af 0xbd2b3e7d3f3c46b5 0xdc6f8f8fc799c7fb 0xbee37c7c7e3cce3f

def z1091 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0xf7c0ff807e007e0e 0xe7be07fc03f003f0

def z1092 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xfc698f8fc199c7fb 0xffe34c7c7e0cce3f

def z1093 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x2c560e7206667ff5 0xf962b073903333ff

def z1094 : W := mkw 0x029d305818752904 0x4014e982c0c3a948 0x2396707038663804 0x411cb38381c331c0

def z1095 : W := mkw 0xc29f247f107a09c5 0x8614f923f883d04e 0x081f007f807e01f1 0x1840f803fc03f00f

def z1096 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27c07e007f80380e 0x413e03f003fc01c0

def z1097 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff807f807e1e 0xffff07fc03fc03f0

def z1098 : W := mkw 0x8160d9044808608a 0x240b06c822404304 0xf7e9ff8ff8187997 0xffbf4ffc7fc0c3cc

def z1099 : W := mkw 0x829db05d58786984 0xa414ed82eac3c34c 0x7399f07df8787997 0x6b9ccf83efc3c3cc

def z1100 : W := mkw 0x009d000035550004 0x4004e80001aaa800 0xba5f00007fff801e 0x1dd2f80003fffc00

def z1101 : W := mkw 0x45624f222702144b 0x1a2b1279113810a2 0x8c460e0206060668 0x9462307010303033

def z1102 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0xb7e07f803f807e0e 0xe5bf03fc01fc03f0

def z1103 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2398707c38603805 0x491cc383e1c301c0

def z1104 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xf7e0ff807f987f9e 0xe7bf07fc03fcc3fc

def z1105 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x7390f07078607997 0x6b9c878383c303cc

def z1106 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x8446ffff80000001 0xf42237fffc000000

def z1107 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc770e7207e7ffff 0xfde3b873903f3fff

def z1108 : W := mkw 0x01fd49003555000e 0x400fea4801aaa800 0xffff0f807fff801e 0x9ffff87c03fffc00

def z1109 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x2390707078607806 0x411c838383c303c0

def z1110 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc7f0e7206667fff 0xffe3f873903333ff

def z1111 : W := mkw 0x0400db804a807602 0x382006dc025403b0 0x2780ff8038007e04 0xe13c07fc01c003f0

def z1112 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x9c00ffff800047fb 0xfce007fffc00023f

def z1113 : W := mkw 0x01fd20483555000c 0x400fe90241aaa800 0xfbff007c7fff801f 0x1fdff803e3fffc00

def z1114 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x73ff00007fff8016 0x0b9ff80003fffc00

def z1115 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff8600000f 0xffaffffffc300000

def z1116 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff86660005 0xffaffffffc333000

def z1117 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xffe9ff83ff99fe7e 0xffff4ffc1ffccff3

def z1118 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc768ff206667fff 0xffe3b47f903333ff

def z1119 : W := mkw 0x0160000035550008 0x400b000001aaa800 0xfbf600007fff801e 0x1fdfb00003fffc00

def z1120 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x7580ffff80000001 0xe3ac07fffc000000

def z1121 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xf7e0ff83ff807e6e 0xe7bf07fc1ffc03f3

def z1122 : W := mkw 0x25674fa3a780962f 0x992b3a7d1d3c04b1 0x8c670f8387818668 0x9463387c1c3c0c33

def z1123 : W := mkw 0xa160d984c888e2aa 0x250b06cc26444715 0xffe9ff8ff999ffff 0xffff4ffc7fcccfff

def z1124 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x6398f07c78787996 0x431cc783e3c3c3cc

def z1125 : W := mkw 0xe29a247e907a89e1 0x0714d123f483d44f 0x081f007f807f81f1 0x1840f803fc03fc0f

def z1126 : W := mkw 0x829db05c587d6984 0x6414ed82e2c3eb4c 0x739ef07c787e7997 0x6b9cf783e3c3f3cc

def z1127 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c78187981 0x6b9cc783e3c0c3cc

def z1128 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x67e0ff807f807e0e 0x433f07fc03fc03f0

def z1129 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398f07c38607997 0x6b9cc783e1c303cc

def z1130 : W := mkw 0x45624fa22782164b 0x1a2b127d113c10b2 0x84660f8007860608 0x8423307c003c3030

def z1131 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffff9f8009 0xfffffffffffcfc00

def z1132 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x77c07e007e003806 0x43be03f003f001c0

def z1133 : W := mkw 0x05674f232700140f 0x982b3a79193800a0 0x04460e0006000000 0x0022307000300000

def z1134 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xffe9ff8fff99fe6e 0xf7ff4ffc7ffccff3

def z1135 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x0380707038003800 0x401c038381c001c0

def z1136 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xfdffffff87e7801f 0xffeffffffc3f3c00

def z1137 : W := mkw 0x0098901058706900 0x2004c48082c38348 0x7398f07078787997 0x6b9cc78383c3c3cc

def z1138 : W := mkw 0xa0009084c888e2a0 0x2500048426444715 0xda29818ff999ffff 0xbed14c0c7fcccfff

def z1139 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfdd6fe7206667fff 0xffeeb7f3903333ff

def z1140 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xebff00007fff800c 0x175ff80003fffc00

def z1141 : W := mkw 0x01676d6b2505000f 0xc00b3b6b59282800 0x8c67ffff87878009 0xf4633ffffc3c3c00

def z1142 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4829818fc199c7f1 0xba414c0c7e0cce3f

def z1143 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff818fffffc7ff 0xbfdffc0c7ffffe3f

def z1144 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x45bfffff80000001 0xfa2dfffffc000000

def z1145 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x0409ffff80000001 0xf8204ffffc000000

def z1146 : W := mkw 0xe29aa4fed0facbe1 0x2714d527f687d65f 0xd83f81ffc1ffc7fb 0xbec1fc0ffe0ffe3f

def z1147 : W := mkw 0x05655b002f05340e 0x582b2ad8017829a0 0xafe77e003f87b80c 0x557f3bf001fc3dc0

def z1148 : W := mkw 0xa6009294fff8ffa0 0x3d300494a7ffc7fd 0x0a0000007ff9fffe 0x0050000003ffcfff

def z1149 : W := mkw 0x029f247b10700905 0x8014f923d8838048 0x001f007f80600001 0x1800f803fc030000

def z1150 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398f07c78783817 0x6b9cc783e3c3c1c0

def z1151 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xb4560e7206667fef 0xe5a2b073903333ff

def z1152 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbf600007fff801e 0x07dfb00003fffc00

def z1153 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00027fff867e 0x9fdff80013fffc33

def z1154 : W := mkw 0x8298305c18782980 0x0414c182e0c3c14c 0x2390707c38603985 0x411c8383e1c301cc

def z1155 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x3390707038603816 0x499c838381c301c0

def z1156 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfbb9f1fdf9f9f99f 0x7fddcf8fefcfcfcc

def z1157 : W := mkw 0x0565db816f80760e 0xb82b2edc0b7c03b0 0xf7e1ff81ff807e0e 0xe7bf0ffc0ffc03f0

def z1158 : W := mkw 0x41ff6d6b0002004f 0x820ffb6b58001002 0xfdffffff80060061 0xffeffffffc003003

def z1159 : W := mkw 0xe2009294dafaffe0 0x37100494a6d7d7ff 0x0a0000007ffffffe 0x0050000003ffffff

def z1160 : W := mkw 0x000012000a003400 0x10000090005001a0 0xb7c07e003e007e0e 0xe5be03f001f003f0

def z1161 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b9ef07c787e7997 0x7bdcf783e3c3f3cc

def z1162 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf7d8fe7c78787997 0xefbec7f3e3c3c3cc

def z1163 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x4829818fc199c7fb 0x1a414c0c7e0cce3f

def z1164 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff807fe67e1e 0xe7ff07fc03ff33f0

def z1165 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x8c560e7206667ff9 0xfc62b073903333ff

def z1166 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7b99f1fff879fff7 0xfbdccf8fffc3cfff

def z1167 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xffe9ff8c7f99ff9f 0xffff4ffc63fccffc

def z1168 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0xf7c0fe007e007e0e 0xe7be07f003f003f0

def z1169 : W := mkw 0x0098304808002000 0x0004c18240400100 0x2390707038003804 0x411c838381c001c0

def z1170 : W := mkw 0x01ff6d6b1050000f 0x800ffb6b58828000 0xf5ffffff80780011 0xffaffffffc03c000

def z1171 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfb98f07c7878799f 0x7fdcc783e3c3c3cc

def z1172 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c78783816 0x4b9cc783e3c3c1c0

def z1173 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27c07e003e007e04 0xe13e03f001f003f0

def z1174 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc560e7006667ffe 0xe5e2b073803333ff

def z1175 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x27c07e003e007e04 0x413e03f001f003f0

def z1176 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x77c0ff807e007e06 0xe3be07fc03f003f0

def z1177 : W := mkw 0x05674fa32785160f 0xd82b3a7d193c28b0 0x8c670f8387878608 0x9463387c1c3c3c30

def z1178 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xfc7f8fffc7ffffff 0xffe3fc7ffe3fffff

def z1179 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x2390f07038607804 0x611c878381c303c0

def z1180 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x7398707038603804 0x4b9cc38381c301c0

def z1181 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x23d670703e663804 0x411eb38381f331c0

def z1182 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e07e007f807e0e 0xe7bf03f003fc03f0

def z1183 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f1fff8787997 0xeb9cc78fffc3c3cc

def z1184 : W := mkw 0xc29a247e107a09c1 0x0614d123f083d04e 0x001e007c007e0191 0x0800f003e003f00c

def z1185 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xf47fffff80000001 0xffa3fffffc000000

def z1186 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00027fff81ff 0x1fdff80013fffc0f

def z1187 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x8a7f00007fff801e 0x1c53f80003fffc00

def z1188 : W := mkw 0x0160d9004800600a 0x200b06c802400300 0x77c0fe0078007806 0x63be07f003c003c0

def z1189 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xf5ffffff80660001 0xffaffffffc033000

def z1190 : W := mkw 0x009f6d6b00000007 0x8004fb6b58000000 0x0409ffff80000001 0xe0204ffffc000000

def z1191 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0xf3b9f1ffb8603805 0xff9dcf8ffdc301c0

def z1192 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e07e007f807e0e 0x47bf03f003fc03f0

def z1193 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0xbbd670703e66381e 0x5ddeb38381f331c0

def z1194 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xb7c07e007f807e0e 0xe5be03f003fc03f0

def z1195 : W := mkw 0x45624f222702144b 0x1a2b1279113810a2 0x04460e0006060000 0x0022307000303000

def z1196 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xffe8ff8e7f987fff 0xffff47fc73fcc3ff

def z1197 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0x27d6ffffbe660005 0xe13eb7fffdf33000

def z1198 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7f0fff07f807e0f 0xefbf87ff83fc03f0

def z1199 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff000fffff801f 0x1fdff8007ffffc00

def z1200 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xffe0ff807f81fe6e 0xe7ff07fc03fc0ff3

def z1201 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xfbb9f1fff9f9f99f 0xffddcf8fffcfcfcc

def z1202 : W := mkw 0x0000900048006000 0x2000048002400300 0xf7c0fe0078007806 0xe7be07f003c003c0

def z1203 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0x45a0ffff80000001 0xe22d07fffc000000

def z1204 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xffffffffffe6001f 0xffffffffffff3000

def z1205 : W := mkw 0xa0009094c8a8eba0 0x25000484a645475d 0xfbb9f1fff9f9ffff 0xffddcf8fffcfcfff

def z1206 : W := mkw 0x00076d6b00000007 0x80003b6b58000000 0x0407ffff80000001 0xf0203ffffc000000

def z1207 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff80007807 0xffaffffffc0003c0

def z1208 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7fffffff9f98017 0xffbfffffffcfcc00

def z1209 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x847fffff80000001 0xfc23fffffc000000

def z1210 : W := mkw 0x04005b000a003402 0x182002d8005001a0 0x27807e0038003804 0x413c03f001c001c0

def z1211 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe9ff8fff807fff 0xffff4ffc7ffc03ff

def z1212 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e0ff807f807fee 0xe7bf07fc03fc03ff

def z1213 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xfba9818ff999c7ff 0xbfdd4c0c7fccce3f

def z1214 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x3c560e7006667fff 0x69e2b073803333ff

def z1215 : W := mkw 0xe4009294efaaffe0 0x3f200494a77d57ff 0x0a0000007ffffffe 0x0050000003ffffff

def z1216 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e8ff807f987e1e 0xefbf47fc03fcc3f0

def z1217 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0xfbb9707079f9b81e 0x5fddcb8383cfcdc0

def z1218 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x9400ffff80000001 0xfca007fffc000000

def z1219 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e0ff8dff807e0e 0xe7bf07fc6ffc03f0

def z1220 : W := mkw 0xa0009084c888e2a0 0x2500048426444715 0xdba9f18ff999c7fb 0xbedd4f8c7fccce3f

def z1221 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x27c07e003e007e0e 0x413e03f001f003f0

def z1222 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbfff0007fff801e 0x7fdfff8003fffc00

def z1223 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0xf5e9ffff80000001 0xffaf4ffffc000000

def z1224 : W := mkw 0x8560db846f88768a 0x3c2b06dc237c43b4 0xf7e0ff8c7f807f8f 0xe7bf07fc63fc03fc

def z1225 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0x7398f07c79f87f9f 0x6b9cc783e3cfc3fc

def z1226 : W := mkw 0x01fd49003555000e 0x400fea4801aaa800 0xffff7e007fff801e 0x5ffffbf003fffc00

def z1227 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xcbef00007fff801e 0x165f780003fffc00

def z1228 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff800001f1 0xffeffffffc00000f

def z1229 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x8421ffff80000001 0xf4210ffffc000000

def z1230 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0xb477ffff80000001 0xfda3bffffc000000

def z1231 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e9ff8fff807fef 0xffbf4ffc7ffc03ff

def z1232 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0xf7e0ff807e007806 0xe7bf07fc03f003c0

def z1233 : W := mkw 0x01604b002700140a 0x100b0258013800a0 0xf7e0ff807f807e0e 0xe7bf07fc03fc03f0

def z1234 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf87f818fc199c7fb 0xbfc3fc0c7e0cce3f

def z1235 : W := mkw 0x0000b04848006000 0x2000058242400300 0x7380f07c78007807 0x639c0783e3c003c0

def z1236 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x75deffff80000001 0xebaef7fffc000000

def z1237 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7bb9f1fdf9f9ffff 0x6bddcf8fefcfcfff

def z1238 : W := mkw 0x4002063202221d41 0x12001031901110ea 0x2c560e7206667fff 0xe162b073903333ff

def z1239 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0x7398f07c79f9f997 0x6b9cc783e3cfcfcc

def z1240 : W := mkw 0x01ff6d6b1055000f 0xc00ffb6b5882a800 0xfffffffff87f8017 0xffffffffffc3fc00

def z1241 : W := mkw 0x01fd20493555000c 0xc00fe90249aaa800 0xfbff000dffff801e 0x1fdff8006ffffc00

def z1242 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd029818fc199c7e1 0xbe814c0c7e0cce3f

def z1243 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00007fffc19f 0x3fdff80003fffe0c

def z1244 : W := mkw 0xa29f247f907889a5 0x8514f923fc83c44d 0x081f007f807981f1 0x1840f803fc03cc0f

def z1245 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xac560e7206667fed 0xf562b073903333ff

def z1246 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xffffffffbe66001f 0xfffffffffdf33000

def z1247 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0x67fffffdffff8004 0x433fffffeffffc00

def z1248 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0xbb90707238607fff 0xfddc838391c303ff

def z1249 : W := mkw 0x0098b0c848806200 0x2004c58642440310 0xf3b9f1fff9807e0f 0xff9dcf8fffcc03f0

def z1250 : W := mkw 0x01fd69483555000e 0x400feb4a41aaa800 0xfffffffc7fff801f 0xffffffffe3fffc00

def z1251 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff827f807e6e 0xf7ff07fc13fc03f3

def z1252 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4388f07c78787997 0x621c4783e3c3c3cc

def z1253 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398707078787996 0x4b9cc38383c3c3cc

def z1254 : W := mkw 0x0000000035550000 0x4000000001aaa800 0x8a4600007fff801e 0x1452300003fffc00

def z1255 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0x67e9ff8dff99b804 0x433f4ffc6ffccdc0

def z1256 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xa7c07e003e003e0c 0xc53e03f001f001f0

def z1257 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7398f07c78787806 0x639cc783e3c3c3c0

def z1258 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xe7e0ff807f803e0c 0xc73f07fc03fc01f0

def z1259 : W := mkw 0x05655b002f05340e 0x582b2ad8017829a0 0x27c67e003e063804 0x413e33f001f031c0

def z1260 : W := mkw 0x01676d6b0000000f 0x800b3b6b58000000 0xf5e7ffff80000001 0xf7af3ffffc000000

def z1261 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xc7e0ff807f807e08 0xe63f07fc03fc03f0

def z1262 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xfdffffff87ff8019 0xffeffffffc3ffc00

def z1263 : W := mkw 0xa29fa4ffd0f8cba5 0xa514fd27fe87c65d 0xd83f81ffc1f9c7fb 0xbec1fc0ffe0fce3f

def z1264 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4398f07c78787997 0x0a1cc783e3c3c3cc

def z1265 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff80000669 0xffeffffffc000033

def z1266 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0x7398f1fc78787f97 0xeb9cc78fe3c3c3fc

def z1267 : W := mkw 0x016059000800200a 0x000b02c800400100 0xf7e0ff8038003804 0xe7bf07fc01c001c0

def z1268 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0x0400ffff800047e1 0xe02007fffc00023f

def z1269 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b98f07c78787fff 0x6bdcc783e3c3c3ff

def z1270 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7ffffffff99800f 0xffbffffffffccc00

def z1271 : W := mkw 0x01ff6d6b3555000f 0xc00ffb6b59aaa800 0xf7ffffffffff8005 0xffbffffffffffc00

def z1272 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e9ff8dff807e0e 0xe7bf4ffc6ffc03f0

def z1273 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0x27c07e007e007806 0x413e03f003f003c0

def z1274 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xdfa9ff8ff999fffb 0xfefd4ffc7fcccfff

def z1275 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7f0ff807fe07e1e 0xefbf87fc03ff03f0

def z1276 : W := mkw 0x8200901458786980 0x24100480a2c3c34c 0x7390f07078787997 0x6b9c878383c3c3cc

def z1277 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e0ff807f99fe0e 0xe7bf07fc03fccff0

def z1278 : W := mkw 0x429a247a10720941 0x0214d123d083904a 0x0016007000660000 0x0000b00380033000

def z1279 : W := mkw 0x01fd49003555000e 0x400fea4801aaa800 0xfbfff1807fff801e 0x1fdfff8c03fffc00

def z1280 : W := mkw 0x05674fa32780160f 0x982b3a7d193c00b0 0x84660f8007800608 0x8423307c003c0030

def z1281 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0x77c0fe003e003804 0x63be07f001f001c0

def z1282 : W := mkw 0x00026d6b00000003 0x8000136b58000000 0xb440ffff80000001 0xe5a207fffc000000

def z1283 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xc5ffffff80000001 0x9e2ffffffc000000

def z1284 : W := mkw 0x0560d9806d80620a 0x282b06cc036c0310 0xf7e0ff8079807806 0xe7bf07fc03cc03c0

def z1285 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390707038603995 0x491c838381c301cc

def z1286 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0x65ffffff80000001 0xe32ffffffc000000

def z1287 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0xf7e9ff8fff99fe0f 0xffbf4ffc7ffccff0

def z1288 : W := mkw 0x0400db806f807602 0x382006dc037c03b0 0x7780ff807f807e0e 0xe3bc07fc03fc03f0

def z1289 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf829818fc199ffff 0xffc14c0c7e0ccfff

def z1290 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xffe0ff807f99fe1e 0xe7ff07fc03fccff0

def z1291 : W := mkw 0x0160000025000008 0x000b000001280000 0xfbff00007fff801e 0x1fdff80003fffc00

def z1292 : W := mkw 0x01fd69493555000e 0xc00feb4a49aaa800 0xffffff8dffff801e 0xfffffffc6ffffc00

def z1293 : W := mkw 0x2565db80ef85f62e 0x792b2edc077c2fb1 0xffe7ff83ff87fe6e 0xf7ff3ffc1ffc3ff3

def z1294 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0x47a9ff8ff999ffe1 0xe23d4ffc7fcccfff

def z1295 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0xfbb9f1fc79f9ff9f 0xffddcf8fe3cfcffc

def z1296 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xfb98f1fff8787fff 0xffdcc78fffc3c3ff

def z1297 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00007fffc61e 0xbfdff80003fffe30

def z1298 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff81818009 0xffeffffffc0c0c00

def z1299 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7390f07078787996 0x639c878383c3c3cc

def z1300 : W := mkw 0xa298b0dcd8f8eba0 0x2514c586e6c7c75d 0xf3b9f1fff8787ff7 0xff9dcf8fffc3c3ff

def z1301 : W := mkw 0x01ff6d6b2505000f 0xc00ffb6b59282800 0xf5ffffff81818001 0xffaffffffc0c0c00

def z1302 : W := mkw 0x05624fa22780160b 0x182b127d113c00b0 0x84660f8207800608 0x9423307c103c0030

def z1303 : W := mkw 0x2560db80ef80f62a 0x392b06dc077c07b1 0xffe9ff8fff81fe6f 0xffff4ffc7ffc0ff3

def z1304 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf398f07c78787f9f 0xef9cc783e3c3c3fc

def z1305 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xf7ffffffbe000005 0xffbffffffdf00000

def z1306 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0x2bdf00007fff801e 0x195ef80003fffc00

def z1307 : W := mkw 0x8298b04c58586080 0x2414c58262c2c304 0x7398f07c78187807 0x6b9cc783e3c0c3c0

def z1308 : W := mkw 0x0000101008202900 0x0000008080410148 0x2390707038603804 0x411c838381c301c0

def z1309 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x2390707038607996 0x411c838381c303cc

def z1310 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0xf7e8ff8c7f807e0f 0xefbf47fc63fc03f0

def z1311 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xd83f818fc1ffc7fb 0xbec1fc0c7e0ffe3f

def z1312 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x77a0ff8079807e06 0xe3bd07fc03cc03f0

def z1313 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x7b98f07c7e7e799f 0x6bdcc783e3f3f3cc

def z1314 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff8000460b 0xffaffffffc000230

def z1315 : W := mkw 0x45674fa22787164f 0x5a2b3a7d113c38b2 0x8c670f8207878668 0x9463387c103c3c33

def z1316 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xfbff00027fff801f 0xbfdff80013fffc00

def z1317 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xa7e07f803e003804 0xc53f03fc01f001c0

def z1318 : W := mkw 0x0000000035550000 0x4000000001aaa800 0xfa7f00007fff801e 0x1fd3f80003fffc00

def z1319 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x3390707038603805 0x699c838381c301c0

def z1320 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc5f0e7f86667fff 0xfde2f873fc3333ff

def z1321 : W := mkw 0x01fd00003555000c 0x400fe80001aaa800 0xf3ff00007fff8004 0x1f9ff80003fffc00

def z1322 : W := mkw 0xa200b0dcc8a8eba0 0x25100586e645475d 0xfba9f1fff999ffff 0xffdd4f8fffcccfff

def z1323 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffff80198011 0xffeffffffc00cc00

def z1324 : W := mkw 0x829db05c587d6984 0x6414ed82e2c3eb4c 0xfbbff07c79fff99f 0x7fddff83e3cfffcc

def z1325 : W := mkw 0x009a6d6b00000003 0x8004d36b58000000 0xf5deffff80000001 0xffaef7fffc000000

def z1326 : W := mkw 0x0560db006f00740a 0x382b06d8037803a0 0x27c0fe003e007804 0x613e07f001f003c0

def z1327 : W := mkw 0xa298b05cd878e9a0 0x2514c582e6c3c74d 0xfbb9f07ff9f9f9ff 0x7fddcf83ffcfcfcf

def z1328 : W := mkw 0x0005000035550004 0x4000280001aaa800 0x0a0700007fff801e 0x1050380003fffc00

def z1329 : W := mkw 0x01ff6d6b0005000f 0xc00ffb6b58002800 0xfdffffff80078001 0xffeffffffc003c00

def z1330 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xc829818fc19987f9 0x9e414c0c7e0ccc3f

def z1331 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0x27c07f803e003e04 0xc13e03fc01f001f0

def z1332 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0x27c0ff8fbe007fe5 0xe13e07fc7df003ff

def z1333 : W := mkw 0x05605b002f00340a 0x182b02d8017801a0 0xf7e9ff8fbe003805 0xffbf4ffc7df001c0

def z1334 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0xf3def07c78787997 0x7f9ef783e3c3c3cc

def z1335 : W := mkw 0x0298305818702900 0x0014c182c0c38148 0x3390707038607806 0x619c838381c303c0

def z1336 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x2390f07c38603804 0x411c8783e1c301c0

def z1337 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xf5ffffff80004193 0xffaffffffc00020c

def z1338 : W := mkw 0x4002063202221d41 0x12001031901110ea 0xbc5f0e72067fffff 0xfde2f8739033ffff

def z1339 : W := mkw 0xa400db84ca88f6a2 0x3d2006dc265447b5 0x7788ff8ff8187ff7 0xebbc47fc7fc0c3ff

def z1340 : W := mkw 0x05605b802f80360a 0x182b02dc017c01b0 0xf7e07f807f803e0e 0xc7bf03fc03fc01f0

def z1341 : W := mkw 0x45624fa22782164b 0x1a2b127d113c10b2 0x84600f8207800668 0x8423007c103c0033

def z1342 : W := mkw 0x01626d6b0000000b 0x800b136b58000000 0x8460ffff80000001 0xe42307fffc000000

def z1343 : W := mkw 0x009f6d6b10550007 0xc004fb6b5882a800 0x0c1fffff807f8011 0xf860fffffc03fc00

def z1344 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0xf9a9f18fc199c7fb 0xffcd4f8c7e0cce3f

def z1345 : W := mkw 0x01ff6d6b0000000f 0x800ffb6b58000000 0xfdffffffc199c7fb 0xffeffffffe0cce3f

def z1346 : W := mkw 0x8298b05c58786980 0x2414c582e2c3c34c 0x4388f07c78183800 0x421c4783e3c0c1c0

def z1347 : W := mkw 0x01ff6d6b2500000f 0x800ffb6b59280000 0xf7fffffff9800001 0xffbfffffffcc0000

def z1348 : W := mkw 0x0098b04848006000 0x2004c58242400300 0x7390f07078007806 0x639c878383c003c0

def z1349 : W := mkw 0x0298b05858706900 0x2014c582c2c38348 0x7398f07078787816 0x6b9cc78383c3c3c0

def z1350 : W := mkw 0xa560db84ef88f6aa 0x3d2b06dc277c47b5 0x2fc07e007f99fffe 0x417e03f003fccfff

def z1351 : W := mkw 0x8298b0dc58f86b80 0x2414c586e2c7c35c 0x73b8f1fc79f87997 0x6b9dc78fe3cfc3cc

def z1352 : W := mkw 0x016500003555000c 0x400b280001aaa800 0xba7700007fff801e 0x1dd3b80003fffc00

def z1353 : W := mkw 0x040092806f807600 0x38200494037c03b0 0xf7c0fe007f807e0e 0xe7be07f003fc03f0

def z1354 : W := mkw 0x0560db806f80760a 0x382b06dc037c03b0 0x77c0fe007f807e0e 0x63be07f003fc03f0

def z1355 : W := mkw 0xa0008084c088c2a0 0x2500040426044615 0x8829018fc199c7fb 0x9c41480c7e0cce3f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z9,z3,z6,z10]),(0,[z11,z0,z1,z12,z3,z4,z6])],[(0,[z13,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z14,z3,z4,z6]),(0,[z11,z0,z1,z2,z15,z4,z6])],[(0,[z0,z1,z12,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z17])],[(1,[z0,z18,z2,z3,z4,z19]),(0,[z0,z1,z20,z12,z3,z4,z6]),(0,[z0,z1,z8,z2,z21,z3,z4])],[(0,[z0,z1,z2,z22,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z6]),(1,[z24,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z4,z6]),(0,[z0,z1,z2,z26,z3,z4,z6])],[(0,[z27,z0,z2,z3,z28,z4,z6]),(0,[z0,z1,z2,z21,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z29,z6]),(0,[z30,z27,z0,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z32,z6]),(0,[z0,z1,z3,z4,z33,z6,z34])],[(0,[z0,z1,z2,z3,z4,z6,z35]),(1,[z36,z0,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z38,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z39])],[(1,[z0,z1,z2,z40,z4,z6])],[(0,[z0,z1,z2,z41,z3,z4,z6])],[(1,[z42,z0,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z44,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z46,z6])],[(0,[z47,z0,z1,z12,z3,z4,z6]),(0,[z0,z48,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z4,z49,z6])],[(0,[z27,z0,z2,z3,z50,z4,z6]),(0,[z27,z0,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z52,z3,z4,z6]),(0,[z0,z53,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z55,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z10,z10])],[(1,[z56,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z57,z6]),(0,[z0,z1,z58,z3,z4,z6,z34]),(0,[z0,z1,z2,z59,z3,z4,z6])],[(0,[z0,z56,z2,z3,z60,z4,z6]),(0,[z0,z1,z2,z16,z61,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z62]),(0,[z0,z1,z63,z3,z4,z19,z6]),(0,[z0,z1,z2,z3,z6,z64,z10])],[(0,[z0,z1,z56,z12,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z65]),(0,[z66,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z67,z4,z6]),(0,[z0,z1,z2,z3,z50,z6,z10])],[(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z34])],[(0,[z69,z0,z1,z2,z3,z4,z33])],[(0,[z70,z0,z56,z2,z3,z4,z6]),(0,[z71,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z10,z34]),(0,[z45,z0,z1,z2,z16,z4,z6]),(0,[z45,z0,z1,z2,z3,z72,z6])],[(0,[z0,z1,z2,z3,z4,z73,z6])],[(0,[z0,z1,z2,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z4,z6,z75]),(1,[z0,z1,z21,z3,z4,z34]),(0,[z0,z76,z1,z2,z3,z4,z6])],[],[(0,[z77,z0,z1,z3,z4,z6,z34]),(1,[z78,z1,z22,z3,z4,z6]),(0,[z0,z79,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z80])],[(0,[z0,z1,z2,z3,z4,z81,z6]),(0,[z82,z0,z1,z3,z4,z83,z6]),(0,[z0,z84,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z10,z85])],[(0,[z0,z1,z2,z3,z4,z6,z86]),(0,[z0,z1,z2,z3,z19,z6,z10]),(0,[z87,z0,z1,z2,z3,z4,z6])],[(0,[z88,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z89,z34])],[(0,[z70,z0,z1,z2,z3,z4,z6])],[(0,[z90,z0,z1,z2,z3,z4,z6])],[(0,[z91,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z92,z3,z93,z4,z6]),(1,[z0,z1,z2,z3,z6,z94])],[(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z3,z4,z6,z34])],[(0,[z69,z1,z56,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z97,z3,z4,z98,z6])]],
   [[(0,[z99,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z50,z6])],[(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z45,z0,z102,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z4,z103,z6]),(0,[z31,z0,z1,z3,z4,z6,z34]),(0,[z104,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z56,z2,z3,z4,z6]),(0,[z105,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z20,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z106,z6])],[(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z82,z108,z0,z1,z3,z4,z6]),(0,[z109,z110,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z111,z6])],[(0,[z47,z0,z1,z112,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z6]),(1,[z0,z1,z3,z4,z10,z34]),(0,[z0,z1,z2,z3,z4,z6,z114]),(0,[z0,z1,z2,z115,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z116,z6]),(0,[z0,z1,z2,z3,z117,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z118]),(0,[z91,z0,z1,z119,z3,z4,z6]),(0,[z120,z121,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z122,z6,z10]),(1,[z0,z1,z2,z16,z4,z98]),(0,[z0,z1,z123,z8,z2,z3,z6])],[(0,[z47,z1,z2,z3,z4,z6,z124]),(0,[z0,z1,z2,z125,z3,z4,z6])],[(1,[z27,z0,z2,z3,z6,z10]),(0,[z0,z1,z126,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z34])],[(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z127]),(0,[z0,z1,z128,z2,z3,z4,z6])],[(0,[z129,z27,z0,z2,z3,z4,z6])],[(0,[z27,z0,z2,z130,z3,z4,z6])],[(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z0,z1,z8,z2,z3,z6,z132])],[(0,[z0,z1,z56,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z133,z6]),(0,[z0,z48,z1,z2,z3,z6,z10]),(0,[z134,z0,z1,z2,z3,z74,z6]),(0,[z11,z0,z2,z3,z4,z6,z135]),(0,[z0,z1,z2,z3,z4,z6,z136])],[(1,[z0,z1,z2,z3,z137,z6]),(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z139,z4,z6]),(0,[z0,z1,z3,z106,z4,z6,z34])],[(0,[z27,z77,z0,z2,z3,z4,z6]),(0,[z27,z109,z0,z2,z3,z4,z6]),(0,[z31,z1,z140,z2,z3,z4,z6]),(0,[z91,z1,z2,z3,z61,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z141]),(0,[z0,z1,z12,z58,z3,z4,z6])],[(0,[z0,z56,z2,z3,z4,z142,z6])],[(0,[z91,z0,z56,z2,z3,z4,z6]),(0,[z31,z78,z1,z2,z3,z4,z6]),(0,[z143,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z144,z3,z4,z6]),(0,[z0,z18,z1,z8,z2,z3,z6]),(0,[z145,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z60,z4,z6]),(0,[z0,z1,z146,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z21,z147,z3,z4,z6])],[(1,[z7,z1,z2,z3,z142,z6]),(0,[z0,z1,z2,z148,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z149]),(0,[z0,z1,z2,z21,z3,z4,z122])],[(0,[z0,z1,z8,z2,z14,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z150]),(0,[z0,z1,z8,z2,z58,z3,z6]),(0,[z151,z0,z1,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z60,z6,z10])],[(0,[z91,z0,z152,z2,z3,z4,z6]),(0,[z0,z1,z12,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z153])],[(0,[z77,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z154,z4,z6]),(0,[z0,z1,z8,z8,z2,z3,z6])],[(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z155,z3,z4,z6])],[(0,[z0,z56,z2,z3,z4,z33,z6]),(0,[z0,z1,z2,z3,z156,z4,z6])],[(1,[z77,z56,z2,z3,z4,z6]),(0,[z121,z0,z1,z12,z3,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z6,z10])]],
   [[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z159,z6]),(0,[z0,z1,z3,z4,z74,z6,z34])],[(0,[z0,z1,z2,z160,z3,z4,z6]),(0,[z161,z0,z1,z2,z3,z4,z6])],[(0,[z162,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z14,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z163,z4,z6]),(0,[z0,z1,z2,z3,z164,z4,z6]),(1,[z0,z1,z2,z3,z165,z6]),(0,[z0,z1,z2,z3,z4,z166,z6])],[(0,[z31,z167,z0,z2,z3,z4,z6]),(0,[z0,z1,z140,z3,z93,z4,z6]),(1,[z0,z1,z168,z3,z4,z6])],[(0,[z78,z0,z1,z8,z2,z3,z6]),(0,[z105,z0,z169,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z3,z170,z6]),(0,[z0,z1,z2,z3,z6,z10,z171])],[(1,[z0,z56,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z172]),(0,[z0,z1,z2,z3,z4,z19,z6]),(0,[z0,z1,z2,z3,z4,z6,z173]),(0,[z0,z1,z2,z16,z3,z4,z98])],[(0,[z0,z1,z174,z2,z3,z4,z6]),(0,[z134,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z4,z175,z6]),(0,[z0,z1,z176,z3,z4,z6,z34])],[(0,[z177,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z6,z10]),(1,[z69,z1,z2,z3,z4,z33])],[(0,[z11,z0,z1,z178,z3,z4,z6])],[(0,[z179,z77,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z61,z4,z6,z124]),(0,[z0,z1,z16,z3,z4,z6,z34]),(0,[z70,z0,z1,z3,z4,z6,z34])],[(0,[z1,z56,z2,z3,z4,z142,z6]),(0,[z27,z0,z2,z3,z4,z6,z180]),(0,[z0,z1,z3,z4,z6,z34,z181]),(0,[z0,z1,z3,z4,z6,z34,z171])],[(0,[z0,z1,z12,z3,z51,z4,z6]),(0,[z0,z1,z12,z3,z50,z4,z6]),(0,[z182,z0,z1,z3,z4,z6,z171])],[(0,[z0,z1,z2,z3,z183,z4,z6]),(0,[z184,z0,z1,z2,z3,z6,z10])],[(1,[z0,z185,z2,z3,z4,z6]),(1,[z0,z1,z8,z2,z3,z6])],[(0,[z11,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z12,z92,z3,z4,z6]),(0,[z186,z0,z1,z2,z3,z6,z10])],[(0,[z179,z0,z1,z8,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z187,z4,z6]),(0,[z31,z0,z1,z22,z3,z4,z6]),(0,[z7,z0,z188,z2,z3,z4,z6]),(0,[z189,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z10])],[(0,[z69,z0,z1,z12,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z149]),(0,[z0,z1,z190,z2,z3,z98,z6]),(0,[z0,z1,z2,z191,z3,z6,z10])],[(0,[z0,z1,z2,z3,z4,z6,z192])],[(0,[z0,z193,z56,z2,z3,z4,z6]),(0,[z1,z2,z14,z3,z61,z4,z6]),(1,[z0,z194,z2,z3,z4,z6]),(0,[z0,z1,z168,z21,z3,z4,z6])],[(0,[z0,z18,z1,z2,z3,z4,z135])],[(0,[z27,z7,z0,z2,z3,z4,z6]),(0,[z195,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z149]),(0,[z0,z196,z1,z2,z3,z4,z6])],[(0,[z197,z0,z1,z2,z3,z6,z10]),(1,[z0,z1,z3,z4,z198,z6]),(0,[z0,z1,z2,z199,z3,z4,z6])],[(0,[z121,z0,z56,z2,z3,z4,z6])],[(0,[z91,z121,z1,z2,z3,z4,z6]),(0,[z200,z0,z1,z8,z2,z3,z6])],[(0,[z0,z56,z2,z3,z4,z201,z6]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z12,z12,z3,z4,z6]),(0,[z0,z203,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z204,z4,z6]),(0,[z0,z1,z2,z3,z205,z4,z6])],[(0,[z0,z1,z2,z206,z3,z4,z6]),(0,[z11,z207,z1,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z3,z50,z6])],[(0,[z27,z0,z2,z3,z4,z142,z6])],[(0,[z0,z1,z2,z209,z3,z4,z6]),(0,[z121,z1,z2,z3,z4,z6,z124]),(0,[z47,z0,z1,z2,z210,z4,z6]),(0,[z0,z211,z2,z58,z3,z4,z6]),(0,[z0,z1,z12,z212,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z10,z34])],[(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z213,z3,z4,z6]),(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z0,z215,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z0,z1,z8,z2,z3,z61,z6]),(0,[z0,z1,z12,z3,z4,z98,z6]),(0,[z0,z1,z217,z2,z3,z4,z6])],[],[(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z4,z6])],[(1,[z91,z1,z2,z61,z4,z6]),(0,[z47,z0,z219,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z33,z6,z124])],[(0,[z220,z0,z1,z2,z3,z4,z6]),(0,[z45,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z221,z4,z6])],[(0,[z27,z0,z1,z8,z2,z3,z6]),(0,[z197,z0,z2,z58,z3,z4,z6]),(0,[z0,z1,z2,z222,z58,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z223])],[(0,[z27,z0,z2,z3,z4,z33,z6]),(0,[z69,z1,z2,z3,z61,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z224]),(0,[z0,z1,z2,z3,z225,z4,z6]),(0,[z226,z0,z1,z2,z3,z4,z6]),(0,[z0,z227,z1,z2,z3,z4,z6])],[(0,[z27,z0,z176,z2,z3,z4,z6]),(0,[z0,z1,z2,z228,z3,z4,z6]),(0,[z82,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z229])],[(0,[z0,z1,z2,z3,z230,z4,z6]),(0,[z151,z27,z0,z2,z3,z4,z6])],[(0,[z69,z0,z56,z2,z3,z4,z6]),(0,[z47,z0,z1,z231,z3,z4,z6]),(1,[z0,z1,z3,z4,z232,z6]),(0,[z0,z1,z12,z3,z4,z6,z6])],[(0,[z27,z0,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z4,z6])],[(0,[z167,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z19,z6,z34]),(0,[z0,z1,z2,z3,z4,z233,z6]),(0,[z0,z1,z176,z2,z3,z6,z10])],[(0,[z0,z1,z2,z234,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z235,z10])],[(1,[z0,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z237,z6]),(0,[z0,z1,z238,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z239,z4,z6])],[(0,[z78,z1,z2,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z240,z4,z6]),(0,[z0,z1,z2,z3,z241,z4,z6])],[(0,[z242,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z2,z3,z4,z122,z6]),(0,[z0,z1,z3,z50,z4,z6,z34])]],
   [[(0,[z71,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z243,z6]),(0,[z0,z1,z2,z244,z3,z4,z6]),(0,[z208,z0,z1,z176,z2,z3,z6])],[(0,[z69,z0,z1,z2,z3,z4,z6]),(0,[z0,z245,z1,z2,z3,z4,z6]),(0,[z45,z246,z1,z2,z3,z4,z6])],[(0,[z208,z0,z1,z2,z3,z6,z171])],[(1,[z0,z1,z2,z222,z3,z6])],[(0,[z247,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z248,z3,z4,z6]),(1,[z109,z0,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z4,z249,z6]),(0,[z0,z1,z12,z3,z60,z4,z6]),(0,[z0,z1,z8,z2,z3,z98,z6])],[(0,[z0,z1,z2,z3,z61,z4,z6]),(0,[z0,z1,z2,z3,z4,z250,z6]),(0,[z0,z1,z2,z3,z4,z6,z251]),(0,[z0,z1,z2,z3,z4,z98,z124]),(0,[z0,z252,z1,z2,z3,z4,z6])],[(0,[z0,z2,z3,z51,z4,z74,z6])],[(0,[z70,z27,z0,z2,z3,z4,z6]),(0,[z109,z0,z2,z3,z4,z74,z6])],[(0,[z253,z0,z1,z2,z3,z4,z6]),(0,[z0,z0,z56,z2,z3,z4,z6]),(0,[z179,z1,z2,z22,z3,z4,z6]),(0,[z0,z1,z8,z2,z92,z3,z6]),(0,[z0,z1,z12,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z254]),(0,[z109,z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z2,z255,z3,z4,z6]),(0,[z0,z1,z3,z4,z122,z6,z34]),(0,[z256,z0,z1,z2,z3,z6,z10])],[(0,[z95,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z257,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z2,z3,z259,z4,z6]),(0,[z0,z1,z97,z2,z3,z4,z6])],[(0,[z260,z0,z1,z2,z3,z4,z6]),(0,[z120,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z261,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z26,z3,z4,z6])],[(0,[z0,z56,z2,z3,z4,z263,z6]),(0,[z264,z0,z56,z2,z3,z4,z6]),(0,[z11,z27,z0,z2,z3,z4,z6])],[(1,[z110,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z10,z132])],[(0,[z0,z56,z2,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z4,z6,z124])]],
   [[(0,[z27,z0,z2,z3,z265,z4,z6]),(0,[z0,z1,z3,z4,z33,z6,z266]),(0,[z0,z1,z2,z4,z98,z6,z132])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z267,z6])],[(0,[z0,z56,z268,z2,z3,z4,z6]),(0,[z0,z56,z176,z2,z3,z4,z6]),(0,[z105,z0,z1,z144,z3,z4,z6])],[(0,[z0,z56,z2,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z4,z6,z269])],[(0,[z0,z1,z2,z3,z270,z4,z6]),(0,[z0,z1,z2,z3,z265,z6,z10]),(0,[z0,z1,z2,z3,z271,z4,z6]),(0,[z0,z1,z3,z4,z6,z34,z132])],[(0,[z0,z272,z1,z2,z3,z4,z6]),(0,[z0,z1,z273,z12,z3,z4,z6])],[(0,[z0,z48,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z21,z3,z4,z34])],[(0,[z7,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z274,z6]),(0,[z0,z1,z212,z92,z3,z4,z6])],[(0,[z47,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z181]),(0,[z0,z1,z212,z2,z93,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z171])],[(0,[z275,z0,z1,z2,z3,z4,z6])],[(0,[z0,z276,z1,z2,z3,z4,z6]),(0,[z0,z48,z2,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z135]),(0,[z0,z1,z176,z2,z3,z83,z6])],[(1,[z277,z0,z2,z3,z4,z6]),(0,[z105,z0,z1,z2,z3,z6,z10]),(0,[z278,z0,z1,z2,z3,z4,z6])],[(0,[z69,z121,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z279,z6])],[(1,[z280,z0,z1,z2,z3,z6]),(0,[z0,z1,z238,z2,z3,z4,z6]),(0,[z0,z18,z1,z2,z3,z4,z19]),(0,[z0,z1,z281,z2,z3,z4,z6]),(0,[z282,z0,z1,z2,z3,z4,z6])],[(0,[z108,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z8,z2,z9,z3,z6])],[]],
   [[(0,[z0,z1,z2,z3,z283,z4,z6]),(0,[z264,z0,z2,z3,z163,z4,z6]),(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z82,z134,z0,z1,z2,z3,z6])],[(0,[z27,z69,z0,z2,z3,z4,z6]),(0,[z91,z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z285,z2,z3,z4,z6])],[(0,[z109,z0,z56,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z286,z0,z1,z8,z2,z3,z6])],[(0,[z45,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z266]),(1,[z0,z1,z2,z3,z6,z254]),(0,[z0,z1,z2,z3,z4,z6,z287]),(0,[z0,z1,z2,z3,z288,z4,z6]),(1,[z0,z1,z289,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z290]),(0,[z0,z1,z2,z3,z4,z6,z291])],[(0,[z0,z1,z2,z3,z292,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z293]),(0,[z294,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z19,z6]),(0,[z0,z1,z92,z3,z60,z4,z6])],[(0,[z27,z0,z2,z22,z3,z4,z6]),(0,[z0,z1,z2,z295,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z111,z6]),(0,[z0,z1,z2,z3,z4,z10,z34])],[(0,[z296,z0,z56,z2,z3,z4,z6]),(0,[z27,z0,z2,z21,z3,z4,z6])],[],[],[(0,[z0,z1,z2,z22,z3,z6,z10]),(0,[z0,z1,z297,z2,z3,z4,z6]),(0,[z0,z1,z3,z51,z4,z6,z34])],[(0,[z0,z56,z2,z3,z265,z4,z6]),(0,[z0,z1,z12,z3,z4,z142,z6]),(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z3,z6,z10])],[(0,[z0,z1,z2,z3,z4,z299,z6]),(0,[z0,z1,z2,z14,z4,z6,z132]),(0,[z47,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z300,z4,z6]),(0,[z0,z1,z2,z3,z4,z301,z6]),(1,[z208,z0,z1,z2,z6,z171])],[(1,[z0,z188,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z302,z6]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z304,z3,z4,z6])],[(1,[z69,z56,z2,z3,z4,z6]),(0,[z305,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z16,z3,z4,z132])],[(0,[z7,z0,z56,z2,z3,z4,z6]),(0,[z296,z0,z1,z2,z3,z4,z6]),(0,[z162,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z306,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z85])]],
   [[(0,[z0,z1,z56,z3,z4,z6,z34]),(1,[z0,z1,z176,z3,z60,z6])],[(0,[z151,z0,z1,z2,z3,z6,z10])],[],[(0,[z0,z1,z2,z307,z3,z4,z6]),(0,[z280,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z308,z3,z4,z6]),(0,[z0,z1,z309,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z19,z6,z62])],[(0,[z0,z1,z211,z12,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z33,z6])],[],[(1,[z56,z2,z3,z4,z142,z6]),(0,[z27,z0,z2,z3,z4,z74,z6])],[(0,[z179,z69,z1,z2,z3,z4,z6]),(0,[z264,z0,z1,z12,z3,z4,z6]),(0,[z0,z48,z1,z2,z9,z4,z6])],[],[(1,[z27,z0,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z310,z4,z6]),(0,[z105,z0,z1,z311,z3,z4,z6]),(0,[z312,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z6,z34]),(0,[z0,z1,z2,z313,z3,z4,z6]),(0,[z0,z1,z21,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z314,z4,z6]),(1,[z0,z1,z63,z3,z4,z6])],[],[(0,[z315,z0,z1,z2,z3,z4,z6]),(0,[z91,z0,z1,z3,z4,z6,z34]),(0,[z134,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z316,z4,z6]),(0,[z0,z1,z2,z3,z4,z317,z6])],[(0,[z78,z0,z1,z140,z3,z4,z6]),(0,[z0,z1,z12,z318,z3,z4,z6])]],
   [[(0,[z0,z1,z319,z2,z3,z4,z6])],[(0,[z0,z56,z2,z22,z3,z4,z6]),(0,[z0,z1,z320,z2,z3,z4,z6]),(0,[z321,z0,z1,z12,z3,z4,z6]),(0,[z70,z0,z1,z2,z3,z6,z10])],[(0,[z0,z56,z2,z21,z3,z4,z6]),(0,[z108,z0,z1,z211,z3,z4,z6])],[(0,[z322,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z103,z6]),(1,[z23,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z323,z4,z6])],[(0,[z0,z1,z324,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z325,z4,z6]),(0,[z11,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z326,z4,z6])],[(0,[z7,z0,z1,z2,z3,z142,z6]),(0,[z0,z1,z2,z3,z6,z135,z10])],[(0,[z327,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z60,z6])],[(0,[z0,z1,z328,z2,z3,z4,z6]),(0,[z0,z1,z20,z2,z3,z6,z10])],[(0,[z27,z1,z56,z2,z3,z4,z6]),(0,[z31,z0,z329,z2,z3,z4,z6]),(1,[z264,z0,z2,z163,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z330]),(0,[z208,z0,z1,z8,z2,z3,z6])],[(0,[z0,z1,z140,z3,z60,z4,z6]),(0,[z0,z1,z2,z3,z331,z4,z6]),(0,[z0,z1,z2,z3,z332,z4,z6])],[(0,[z0,z1,z2,z3,z265,z6,z171]),(0,[z0,z207,z1,z2,z3,z4,z6]),(0,[z0,z18,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z60,z4,z6,z34]),(0,[z0,z1,z2,z3,z4,z6,z333]),(0,[z334,z0,z1,z8,z2,z3,z6])],[(0,[z335,z0,z1,z2,z3,z4,z6]),(0,[z109,z0,z1,z12,z3,z4,z6]),(0,[z0,z2,z3,z4,z19,z6,z135])],[(1,[z0,z1,z2,z336,z4,z6]),(0,[z337,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z338])],[(0,[z30,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z190,z2,z3,z4,z6])]],
   [[],[(0,[z47,z0,z1,z2,z3,z6,z10]),(0,[z339,z0,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z2,z92,z4,z6]),(0,[z0,z1,z8,z2,z3,z6,z6])],[(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z341,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z132])],[(0,[z47,z0,z1,z2,z3,z331,z6]),(0,[z0,z1,z8,z2,z3,z51,z6]),(0,[z0,z1,z2,z342,z3,z4,z6])],[(0,[z0,z1,z211,z2,z3,z4,z6])],[(0,[z0,z1,z56,z2,z3,z6,z10]),(0,[z27,z31,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z343,z3,z4,z6])],[(0,[z0,z1,z2,z344,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z345])],[(0,[z1,z56,z2,z22,z3,z4,z6]),(1,[z0,z1,z2,z3,z346,z6]),(0,[z0,z1,z2,z3,z4,z198,z6])],[(0,[z264,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z169,z2,z3,z4,z6])],[],[(0,[z78,z0,z1,z12,z3,z4,z6]),(0,[z121,z1,z2,z14,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z34,z347])],[(1,[z0,z56,z12,z3,z4,z6]),(0,[z91,z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z2,z3,z349,z4,z6]),(0,[z0,z1,z2,z350,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z351]),(0,[z45,z0,z1,z2,z3,z6,z10])],[(0,[z352,z0,z1,z2,z3,z4,z6])],[(0,[z353,z0,z1,z8,z2,z3,z6])],[(0,[z0,z1,z123,z2,z3,z4,z6])]],
   [[(0,[z121,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z163,z4,z6,z132])],[(0,[z321,z0,z1,z2,z3,z4,z6])],[(1,[z31,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z354,z3,z4,z6])],[],[(0,[z0,z18,z56,z2,z3,z4,z6]),(0,[z27,z0,z2,z3,z163,z4,z6]),(0,[z0,z1,z2,z3,z355,z4,z6]),(0,[z0,z1,z356,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z83,z6,z10]),(1,[z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z4,z98,z6,z338])],[(1,[z0,z1,z2,z3,z357,z6]),(0,[z134,z0,z2,z3,z51,z4,z6])],[(0,[z179,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z358]),(0,[z0,z1,z112,z2,z3,z4,z6]),(0,[z197,z0,z1,z8,z2,z3,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z9,z4,z6,z132]),(0,[z0,z1,z2,z3,z4,z6,z360]),(0,[z208,z0,z1,z2,z4,z6,z171]),(0,[z0,z361,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z19,z6]),(0,[z0,z1,z2,z362,z3,z4,z6]),(0,[z0,z1,z2,z3,z363,z4,z6]),(0,[z0,z1,z2,z364,z3,z4,z6])],[(0,[z0,z1,z2,z3,z163,z6,z10]),(0,[z0,z1,z2,z3,z4,z365,z6]),(0,[z0,z1,z2,z3,z4,z6,z235])],[(0,[z0,z56,z2,z3,z4,z83,z6])],[(0,[z0,z1,z2,z3,z366,z4,z6]),(0,[z0,z1,z2,z3,z4,z232,z6]),(0,[z0,z1,z2,z367,z3,z4,z6])],[(0,[z368,z0,z1,z2,z3,z4,z6])],[(0,[z0,z56,z56,z2,z3,z4,z6]),(0,[z179,z31,z1,z2,z3,z4,z6]),(0,[z0,z1,z369,z2,z3,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6])],[(0,[z91,z27,z0,z2,z3,z4,z6]),(0,[z91,z0,z1,z2,z3,z371,z6]),(0,[z0,z1,z2,z3,z336,z4,z6]),(0,[z109,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z372,z2,z3,z4,z6])],[(1,[z0,z1,z119,z3,z4,z6]),(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z121,z0,z324,z2,z3,z4,z6]),(1,[z120,z0,z2,z3,z4,z6]),(0,[z0,z1,z374,z2,z3,z4,z6]),(1,[z0,z1,z3,z6,z10,z34])],[(0,[z27,z0,z0,z2,z3,z4,z6]),(0,[z375,z0,z1,z12,z3,z4,z6]),(0,[z45,z376,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z377,z6]),(0,[z0,z1,z2,z378,z3,z4,z6])],[(0,[z379,z0,z1,z2,z3,z4,z6]),(0,[z380,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z67,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z381]),(0,[z0,z1,z140,z12,z3,z4,z6]),(0,[z69,z0,z1,z3,z4,z6,z34])],[(0,[z78,z0,z56,z2,z3,z4,z6]),(0,[z82,z0,z1,z92,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z60,z6]),(0,[z0,z1,z2,z3,z4,z6,z94])],[(0,[z0,z382,z1,z2,z3,z4,z6]),(0,[z134,z0,z1,z176,z2,z3,z6]),(0,[z383,z0,z1,z2,z3,z4,z6]),(0,[z384,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z16,z4,z98,z6])],[(0,[z385,z0,z1,z2,z3,z4,z6])],[(0,[z386,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z140,z212,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z387,z4,z6]),(0,[z0,z1,z2,z3,z6,z388,z10])],[(0,[z389,z0,z1,z2,z3,z4,z6]),(0,[z0,z18,z2,z3,z163,z4,z6]),(1,[z0,z1,z2,z3,z122,z10])],[(0,[z0,z1,z273,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z265,z50,z6]),(0,[z0,z1,z2,z3,z4,z33,z98]),(0,[z0,z1,z2,z3,z4,z6,z390]),(0,[z0,z1,z391,z2,z3,z4,z6])],[(0,[z0,z1,z392,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z93,z4,z6])],[(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z18,z2,z3,z4,z19,z6]),(0,[z0,z1,z2,z3,z393,z4,z6]),(0,[z0,z1,z12,z3,z4,z6,z34])],[(0,[z78,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z394,z3,z4,z6]),(1,[z0,z1,z395,z2,z3,z6]),(0,[z0,z1,z3,z54,z4,z6,z34])],[(1,[z0,z56,z2,z3,z4,z6]),(0,[z27,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z142,z6,z10]),(0,[z0,z1,z396,z2,z3,z4,z6])],[(0,[z397,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z398,z4,z6])],[(0,[z179,z0,z56,z2,z3,z4,z6]),(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z193,z2,z3,z4,z6]),(1,[z0,z1,z112,z3,z4,z6]),(0,[z0,z1,z12,z2,z3,z4,z122]),(0,[z0,z1,z2,z16,z3,z4,z6])],[(0,[z0,z56,z2,z3,z163,z4,z6]),(0,[z0,z1,z2,z3,z399,z4,z6]),(0,[z0,z400,z1,z2,z3,z4,z6]),(0,[z108,z0,z1,z58,z3,z4,z6]),(0,[z401,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z7,z0,z1,z2,z3,z265,z6]),(0,[z0,z1,z2,z402,z3,z4,z6]),(1,[z0,z1,z147,z3,z4,z6])],[(0,[z11,z0,z1,z2,z40,z4,z6]),(1,[z0,z1,z2,z3,z6,z403])],[(0,[z0,z56,z2,z3,z4,z19,z6]),(1,[z0,z152,z2,z3,z4,z6])],[(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z142,z6]),(0,[z0,z48,z1,z8,z2,z3,z6]),(0,[z0,z1,z178,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z179,z1,z2,z3,z4,z6,z124]),(0,[z27,z0,z2,z3,z106,z4,z6])],[(0,[z121,z0,z1,z2,z3,z6,z10]),(0,[z109,z0,z1,z2,z3,z74,z6]),(0,[z0,z1,z212,z2,z3,z4,z6]),(0,[z0,z1,z2,z405,z3,z4,z6]),(0,[z0,z1,z8,z406,z2,z3,z6])],[(0,[z179,z0,z1,z2,z3,z4,z6]),(0,[z264,z0,z1,z3,z4,z6,z34]),(0,[z407,z0,z1,z2,z3,z4,z6]),(0,[z408,z0,z1,z2,z3,z93,z6])],[(0,[z0,z1,z2,z3,z4,z137,z6]),(0,[z0,z1,z409,z2,z3,z4,z6]),(0,[z0,z1,z2,z410,z3,z4,z6])],[(0,[z0,z1,z2,z3,z411,z4,z6]),(0,[z0,z1,z2,z412,z3,z4,z6]),(0,[z0,z48,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z6,z10])],[],[(0,[z27,z121,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z413,z6]),(0,[z48,z24,z1,z2,z3,z4,z6]),(0,[z414,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z415,z4,z6]),(0,[z110,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z416,z3,z4,z6])],[],[(0,[z0,z56,z2,z3,z187,z4,z6]),(0,[z0,z56,z2,z3,z4,z6,z10]),(0,[z0,z1,z8,z2,z3,z33,z6]),(1,[z182,z0,z1,z3,z4,z6])],[(0,[z0,z1,z281,z3,z4,z6,z34]),(0,[z0,z1,z12,z417,z3,z4,z6])],[(0,[z77,z0,z1,z8,z2,z3,z6]),(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z200,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z418,z0,z1,z2,z3,z4,z6]),(0,[z11,z419,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z83,z6])],[(0,[z0,z1,z140,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z265,z4,z6]),(1,[z420,z1,z2,z3,z4,z6])],[(0,[z421,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z56,z2,z3,z4,z6]),(0,[z408,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z378,z50,z4,z6])],[(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z0,z423,z1,z2,z3,z4,z6])],[(0,[z82,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z8,z12,z3,z4,z6]),(1,[z0,z1,z12,z3,z4,z122])],[(0,[z69,z0,z1,z2,z3,z6,z10])],[(0,[z424,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z124,z132])],[(0,[z425,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z347]),(0,[z0,z1,z3,z4,z6,z135,z34]),(0,[z0,z1,z2,z3,z6,z6,z10])],[(0,[z426,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z92,z3,z4,z6,z34])],[(0,[z0,z1,z2,z427,z3,z4,z6]),(0,[z105,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z109,z0,z1,z3,z4,z6,z34]),(1,[z0,z1,z2,z3,z46,z6])],[(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z61,z6,z10]),(0,[z429,z0,z1,z8,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z430]),(0,[z0,z1,z2,z14,z16,z4,z6]),(0,[z47,z0,z431,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z432,z4,z6])],[(0,[z0,z56,z2,z3,z106,z4,z6]),(0,[z0,z1,z2,z222,z3,z4,z6]),(1,[z433,z0,z1,z3,z4,z6]),(0,[z0,z1,z434,z2,z3,z4,z6])]],
   [[(0,[z435,z0,z1,z2,z3,z4,z6]),(0,[z436,z0,z1,z2,z3,z4,z6])],[(0,[z91,z179,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6])],[(0,[z437,z0,z1,z2,z3,z4,z6]),(1,[z226,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z165,z93,z6]),(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z60,z4,z83,z6])],[(0,[z439,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z440,z4,z6]),(0,[z0,z1,z2,z441,z3,z4,z6]),(0,[z0,z1,z2,z442,z3,z4,z6])],[(0,[z443,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z72,z6])],[(1,[z179,z27,z2,z3,z4,z6]),(0,[z82,z0,z1,z140,z3,z4,z6]),(0,[z108,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z444]),(0,[z0,z1,z217,z2,z3,z122,z6])],[(0,[z91,z0,z1,z2,z3,z6,z10]),(0,[z82,z109,z0,z1,z2,z3,z6])],[(0,[z121,z0,z1,z2,z14,z4,z6]),(0,[z0,z219,z1,z2,z3,z4,z6]),(0,[z445,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z446,z3,z4,z6])],[(0,[z0,z1,z12,z22,z3,z4,z6]),(0,[z7,z0,z1,z3,z4,z6,z34]),(1,[z0,z1,z2,z15,z4,z6]),(0,[z0,z1,z8,z2,z3,z93,z6])],[(0,[z0,z1,z431,z2,z3,z4,z6]),(1,[z47,z1,z2,z3,z4,z124]),(0,[z447,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z448,z2,z3,z4,z6]),(0,[z0,z1,z12,z21,z3,z4,z6])],[(0,[z11,z0,z1,z2,z3,z137,z6]),(0,[z449,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z450]),(0,[z0,z1,z2,z3,z4,z6,z451]),(0,[z452,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z453])],[(0,[z0,z56,z2,z3,z4,z122,z6]),(0,[z27,z0,z2,z3,z4,z6,z135]),(0,[z264,z0,z48,z2,z3,z4,z6])],[(1,[z0,z1,z454,z3,z4,z6])],[(0,[z0,z1,z2,z455,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z142,z6]),(0,[z0,z1,z2,z3,z6,z10,z456])],[(0,[z105,z1,z2,z3,z265,z4,z6]),(0,[z0,z1,z2,z3,z457,z4,z6]),(0,[z0,z18,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z165,z4,z6])],[(0,[z458,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z43,z6]),(0,[z151,z0,z1,z8,z2,z3,z6]),(0,[z208,z0,z1,z2,z378,z4,z6])],[(0,[z420,z0,z1,z2,z3,z4,z6]),(1,[z0,z102,z2,z3,z4,z6]),(0,[z459,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z106,z4,z198,z6]),(0,[z55,z0,z1,z8,z2,z3,z6])],[(0,[z0,z56,z2,z3,z61,z4,z6])],[(1,[z56,z2,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z32,z4,z6]),(0,[z0,z1,z2,z3,z142,z6,z171])],[(0,[z0,z1,z2,z460,z3,z4,z6]),(0,[z27,z0,z2,z3,z4,z6,z10]),(0,[z264,z27,z0,z2,z3,z4,z6])],[(0,[z0,z56,z12,z2,z3,z4,z6]),(0,[z0,z1,z461,z2,z3,z4,z6]),(1,[z0,z1,z2,z210,z4,z6]),(0,[z0,z1,z3,z4,z83,z6,z34]),(0,[z0,z1,z8,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z462,z6]),(0,[z463,z0,z1,z2,z3,z4,z6])],[(0,[z82,z0,z1,z176,z3,z4,z6]),(0,[z0,z1,z128,z3,z106,z4,z6])],[(0,[z464,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z465,z6]),(0,[z0,z1,z2,z3,z98,z6,z10])],[(0,[z466,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z395,z2,z3,z33,z6])],[(0,[z0,z56,z2,z3,z4,z6,z124]),(0,[z0,z1,z8,z2,z3,z265,z6])],[(0,[z108,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z467,z6])],[(0,[z134,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z468,z4,z6])],[(0,[z0,z1,z2,z3,z469,z4,z6]),(0,[z0,z1,z2,z3,z470,z4,z6]),(1,[z207,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z46,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z338]),(1,[z0,z1,z2,z3,z106,z10])]],
   [[(0,[z0,z1,z2,z3,z28,z4,z6]),(0,[z0,z1,z140,z3,z4,z6,z34]),(0,[z0,z152,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z6]),(0,[z471,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z472,z3,z4,z6])],[(0,[z27,z0,z2,z3,z306,z4,z6]),(1,[z27,z0,z12,z3,z4,z6]),(0,[z0,z1,z22,z3,z93,z4,z6]),(0,[z108,z0,z1,z3,z60,z4,z6]),(0,[z0,z1,z2,z3,z473,z4,z6]),(1,[z134,z0,z2,z3,z51,z6]),(0,[z82,z0,z1,z12,z3,z4,z6]),(2,[z0,z1,z3,z10,z34])],[(0,[z0,z1,z2,z474,z3,z4,z6]),(1,[z0,z1,z231,z3,z4,z6]),(0,[z475,z0,z1,z2,z3,z4,z6])],[(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z477,z3,z4,z6])],[(0,[z0,z1,z2,z61,z4,z6,z132])],[(0,[z0,z56,z2,z3,z4,z6,z171]),(0,[z108,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z211,z3,z4,z6,z34]),(1,[z0,z1,z97,z3,z4,z6])],[(0,[z478,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z479,z3,z4,z6]),(0,[z11,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z480,z4,z6])],[(0,[z0,z56,z2,z3,z4,z6,z135]),(0,[z197,z0,z1,z58,z3,z4,z6]),(0,[z0,z481,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z3,z50,z4,z6])],[(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z277,z0,z1,z2,z3,z4,z6]),(0,[z91,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z482,z3,z4,z6]),(0,[z0,z1,z2,z483,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z484]),(0,[z286,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z485,z3,z4,z6]),(0,[z109,z134,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z92,z3,z4,z6]),(0,[z0,z1,z2,z50,z4,z6,z171])],[(1,[z91,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z486,z3,z4,z6]),(1,[z408,z0,z1,z2,z3,z6]),(0,[z452,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z487,z6]),(0,[z226,z48,z1,z2,z3,z4,z6]),(1,[z82,z0,z1,z3,z83,z6])],[(0,[z0,z56,z2,z3,z283,z4,z6]),(0,[z197,z0,z1,z211,z3,z4,z6]),(0,[z488,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z19,z6,z403]),(0,[z0,z1,z12,z2,z3,z4,z34]),(0,[z489,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z490,z4,z6]),(0,[z0,z1,z3,z4,z142,z6,z34]),(0,[z0,z1,z8,z2,z3,z74,z6]),(0,[z0,z1,z2,z491,z3,z4,z6]),(0,[z0,z102,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z492,z6]),(0,[z0,z1,z2,z3,z4,z493,z6]),(0,[z0,z1,z2,z494,z3,z4,z6])]],
   [[(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z329,z2,z3,z4,z6]),(0,[z496,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z497,z6]),(0,[z0,z1,z12,z3,z4,z83,z6]),(0,[z0,z498,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z378,z3,z6])],[(0,[z27,z0,z2,z234,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z258,z6]),(0,[z0,z1,z2,z3,z4,z33,z132]),(0,[z208,z0,z1,z12,z3,z4,z6]),(0,[z0,z499,z1,z2,z3,z4,z6])],[(0,[z1,z56,z2,z3,z4,z6,z124]),(0,[z0,z1,z2,z500,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z89]),(0,[z0,z1,z8,z2,z3,z6,z34])],[(0,[z0,z1,z2,z3,z4,z6,z501])],[(0,[z27,z0,z2,z3,z4,z122,z6]),(0,[z502,z0,z1,z2,z3,z4,z6])],[(0,[z503,z0,z1,z2,z3,z4,z6]),(0,[z504,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z406,z2,z3,z4,z6])],[(0,[z0,z1,z505,z2,z3,z4,z6])],[(0,[z78,z0,z1,z22,z3,z4,z6]),(0,[z1,z2,z3,z265,z4,z142,z6]),(0,[z0,z1,z2,z3,z50,z142,z6]),(0,[z0,z1,z2,z3,z4,z6,z506]),(0,[z0,z1,z2,z9,z16,z4,z6])],[(0,[z507,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z2,z3,z4,z508,z6]),(0,[z0,z1,z509,z2,z3,z4,z6]),(0,[z449,z0,z1,z3,z4,z6,z34]),(1,[z0,z1,z8,z2,z3,z10])],[(1,[z0,z1,z2,z3,z32,z6])],[(0,[z0,z1,z2,z510,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z98])],[(0,[z27,z0,z2,z3,z61,z4,z6]),(0,[z0,z1,z2,z511,z3,z4,z6]),(1,[z197,z0,z58,z3,z4,z6])],[(0,[z0,z1,z2,z210,z3,z4,z6]),(0,[z151,z0,z1,z3,z93,z4,z6]),(0,[z512,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z98,z6]),(0,[z45,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z10,z513]),(0,[z0,z1,z2,z3,z4,z6,z388])],[(0,[z0,z18,z1,z3,z4,z6,z34]),(1,[z0,z1,z190,z2,z3,z6])],[(0,[z27,z0,z12,z2,z3,z4,z6]),(0,[z514,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z515,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z111,z4,z6])],[(0,[z0,z1,z2,z119,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z124,z10]),(0,[z0,z1,z2,z516,z3,z4,z6])]],
   [[(0,[z27,z0,z257,z2,z3,z4,z6]),(0,[z0,z1,z2,z517,z3,z4,z6]),(0,[z518,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z170,z6]),(0,[z109,z481,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z519])],[(0,[z0,z1,z2,z520,z3,z4,z6]),(0,[z0,z1,z212,z22,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z6]),(1,[z45,z0,z1,z2,z4,z132])],[(0,[z380,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z12,z2,z3,z6,z10]),(0,[z45,z0,z194,z2,z3,z4,z6])],[(0,[z179,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z521,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z522,z6])],[(0,[z77,z1,z56,z2,z3,z4,z6]),(0,[z27,z0,z2,z3,z4,z6,z124]),(0,[z0,z1,z395,z2,z3,z4,z6]),(0,[z523,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z524,z3,z4,z6]),(0,[z0,z1,z8,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z11,z0,z1,z2,z3,z4,z135]),(0,[z0,z1,z525,z2,z3,z4,z6]),(0,[z353,z0,z1,z12,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z12,z3,z163,z4,z6])],[(0,[z82,z0,z1,z2,z3,z265,z6]),(0,[z0,z1,z2,z3,z4,z6,z526]),(0,[z527,z0,z1,z12,z3,z4,z6])],[(0,[z528,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z130,z3,z4,z6]),(0,[z529,z0,z1,z2,z3,z4,z6])],[(0,[z208,z0,z56,z2,z3,z4,z6]),(0,[z42,z105,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z254]),(0,[z0,z1,z2,z3,z4,z6,z530]),(0,[z0,z1,z12,z3,z4,z19,z6]),(0,[z0,z1,z2,z3,z239,z4,z6])],[(0,[z0,z1,z2,z531,z3,z4,z6]),(0,[z0,z1,z211,z2,z3,z6,z10]),(0,[z532,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z62])],[(0,[z1,z140,z2,z22,z3,z4,z6]),(0,[z151,z82,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z6,z34])],[(0,[z78,z0,z1,z3,z4,z6,z34])],[(1,[z0,z56,z3,z4,z6,z34]),(0,[z27,z0,z2,z3,z4,z6,z171]),(0,[z197,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z8,z2,z16,z3,z6]),(0,[z0,z1,z2,z3,z106,z4,z10])],[(0,[z30,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z533,z4,z6]),(0,[z264,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z534,z4,z6])],[(0,[z31,z1,z56,z2,z3,z4,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z178,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z114]),(0,[z0,z1,z2,z536,z3,z4,z6])]],
   [[(0,[z27,z0,z48,z2,z3,z4,z6])],[(0,[z0,z537,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z538]),(0,[z0,z1,z2,z3,z60,z4,z6]),(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z434,z2,z3,z6]),(0,[z0,z1,z2,z147,z3,z4,z6])],[(0,[z179,z1,z2,z14,z3,z4,z6]),(1,[z400,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z58,z3,z4,z6])],[(0,[z27,z78,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z539,z4,z6]),(0,[z108,z0,z1,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z540,z4,z6]),(0,[z478,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z12,z3,z4,z6,z10])],[(0,[z541,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z34])],[(0,[z425,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z542,z3,z4,z6]),(0,[z0,z1,z212,z3,z4,z6,z34]),(0,[z0,z1,z8,z2,z3,z326,z6])],[(0,[z179,z0,z1,z3,z4,z6,z34])],[(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z544,z6])],[(0,[z0,z537,z1,z2,z3,z4,z6]),(0,[z27,z27,z0,z2,z3,z4,z6]),(0,[z27,z134,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z545,z6])],[(0,[z0,z546,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z547]),(1,[z0,z1,z12,z3,z6,z10])],[(0,[z0,z1,z3,z4,z232,z74,z6]),(0,[z82,z0,z1,z2,z378,z3,z6]),(0,[z182,z0,z1,z2,z3,z4,z6])],[(0,[z0,z56,z140,z2,z3,z4,z6]),(0,[z548,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z549,z6]),(1,[z0,z1,z8,z12,z3,z6]),(0,[z0,z1,z2,z416,z3,z4,z6])],[(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z0,z376,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z551,z6]),(0,[z0,z1,z2,z3,z552,z4,z6])],[(0,[z0,z56,z2,z3,z4,z6,z132]),(1,[z0,z219,z2,z3,z4,z6]),(0,[z0,z1,z553,z3,z4,z6,z34])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z554])],[(0,[z0,z56,z211,z2,z3,z4,z6]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z556,z4,z6]),(0,[z0,z1,z2,z3,z557,z4,z6]),(0,[z0,z1,z63,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z558,z6])],[(0,[z559,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z560,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z2,z562,z3,z4,z6]),(1,[z246,z1,z2,z3,z4,z6])],[(1,[z0,z324,z2,z3,z4,z6]),(0,[z109,z0,z1,z2,z3,z6,z10])],[(0,[z0,z1,z2,z563,z3,z4,z6]),(1,[z0,z1,z8,z3,z6,z34]),(0,[z70,z0,z1,z8,z2,z3,z6])],[(0,[z0,z56,z2,z427,z3,z4,z6]),(0,[z197,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z564,z6]),(0,[z353,z0,z1,z2,z3,z4,z6])],[(1,[z27,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z565,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z12,z3,z106,z4,z6])],[(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z0,z1,z2,z568,z3,z4,z6]),(0,[z0,z1,z454,z3,z4,z33,z6]),(0,[z569,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z173,z171]),(0,[z0,z1,z2,z191,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z570,z6])],[(0,[z197,z0,z1,z3,z60,z4,z6]),(0,[z0,z1,z571,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z572,z4,z6]),(0,[z0,z1,z2,z3,z98,z6,z94])],[(0,[z573,z0,z1,z2,z3,z4,z6]),(0,[z574,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z575,z4,z6]),(0,[z0,z48,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z576,z4,z6])],[(0,[z0,z577,z1,z2,z3,z4,z6]),(0,[z578,z0,z1,z2,z3,z4,z6]),(0,[z579,z0,z1,z2,z3,z4,z6]),(0,[z580,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z98,z6,z34]),(0,[z0,z1,z2,z553,z3,z4,z6])],[(0,[z30,z0,z1,z2,z3,z346,z6]),(0,[z581,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z1,z3,z4,z6,z34]),(0,[z197,z0,z1,z2,z3,z4,z6]),(1,[z151,z0,z1,z93,z4,z6])],[(0,[z0,z1,z248,z2,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z18,z2,z3,z4,z6])],[(0,[z121,z0,z1,z2,z61,z4,z6]),(0,[z0,z1,z2,z3,z93,z6,z10]),(0,[z82,z0,z1,z3,z4,z6,z34])]],
   [[(0,[z179,z27,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z583,z4,z6])],[(0,[z78,z0,z1,z2,z3,z6,z10]),(0,[z69,z1,z2,z3,z4,z33,z6])],[(1,[z0,z56,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z4,z584,z6]),(0,[z0,z1,z2,z3,z4,z6,z585]),(0,[z0,z1,z2,z3,z4,z586,z6]),(0,[z0,z1,z2,z3,z4,z6,z64])],[(1,[z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z12,z3,z4,z122,z6]),(0,[z587,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z1,z8,z2,z3,z6]),(0,[z0,z588,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z589]),(0,[z0,z1,z2,z16,z3,z6,z10])],[(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z385,z27,z0,z2,z3,z4,z6]),(1,[z0,z1,z128,z3,z4,z6])],[(0,[z77,z0,z1,z12,z3,z4,z6]),(1,[z167,z0,z2,z3,z4,z6]),(1,[z0,z169,z2,z3,z4,z6]),(0,[z433,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z536,z3,z6])],[(0,[z27,z0,z212,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z142,z6]),(0,[z69,z0,z185,z2,z3,z4,z6])],[(0,[z0,z1,z56,z8,z2,z3,z6]),(0,[z0,z1,z8,z2,z591,z3,z6])],[(0,[z23,z69,z0,z2,z3,z4,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z592,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z12,z3,z4,z6])],[(0,[z0,z1,z2,z3,z593,z4,z6]),(0,[z0,z1,z12,z3,z61,z4,z6]),(0,[z0,z1,z3,z4,z6,z333,z34]),(0,[z594,z0,z1,z2,z3,z4,z6])],[(0,[z595,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z212,z2,z3,z6,z10])],[(0,[z596,z0,z1,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z3,z6,z10]),(1,[z0,z1,z2,z3,z331,z6])],[(0,[z0,z56,z2,z378,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z0,z1,z2,z3,z4,z346,z6]),(0,[z0,z1,z2,z3,z6,z10,z598])],[(0,[z0,z1,z454,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z19])],[(0,[z0,z56,z2,z3,z4,z6,z381]),(0,[z277,z78,z0,z2,z3,z4,z6]),(0,[z599,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z600,z3,z4,z6]),(0,[z0,z1,z2,z3,z601,z4,z6])]],
   [[(0,[z0,z56,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z513]),(0,[z0,z1,z185,z2,z3,z4,z6]),(0,[z0,z1,z602,z2,z3,z4,z6])],[(0,[z31,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6]),(0,[z0,z24,z1,z2,z3,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6])],[(0,[z0,z48,z56,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z357,z6]),(0,[z604,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z10,z34]),(0,[z0,z1,z8,z2,z21,z3,z6])],[(0,[z0,z1,z12,z3,z4,z6,z124]),(0,[z0,z1,z2,z3,z605,z4,z6]),(0,[z264,z0,z1,z2,z9,z4,z6]),(1,[z0,z1,z26,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z34,z598])],[(1,[z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z606,z6]),(0,[z27,z0,z140,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z116,z6]),(1,[z0,z1,z2,z3,z371,z6]),(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z608]),(1,[z0,z1,z2,z3,z4,z166])],[(0,[z609,z0,z1,z2,z3,z4,z6])],[(0,[z0,z56,z2,z3,z93,z4,z6]),(0,[z91,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z194,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z4,z6,z132]),(0,[z0,z1,z2,z3,z4,z72,z6])],[(0,[z0,z1,z140,z2,z3,z6,z10]),(0,[z47,z0,z1,z2,z3,z4,z124]),(0,[z82,z197,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z610,z4,z6]),(0,[z0,z1,z8,z211,z2,z3,z6]),(0,[z0,z1,z2,z611,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z612,z6]),(0,[z0,z1,z8,z2,z3,z83,z6]),(0,[z0,z1,z477,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z6,z34,z34]),(1,[z0,z1,z12,z3,z4,z34])],[(0,[z27,z0,z211,z2,z3,z4,z6]),(0,[z421,z0,z1,z2,z3,z6,z10])],[(0,[z0,z56,z2,z14,z3,z4,z6]),(1,[z108,z0,z211,z3,z4,z6]),(0,[z0,z48,z1,z2,z3,z4,z6])],[(0,[z0,z56,z2,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(0,[z7,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z318,z3,z4,z6]),(0,[z0,z1,z8,z613,z2,z3,z6])],[(0,[z0,z1,z12,z3,z4,z6,z171]),(0,[z614,z0,z1,z2,z3,z4,z6])],[],[(0,[z77,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z6,z135]),(0,[z151,z0,z1,z2,z93,z4,z6])],[(1,[z56,z2,z3,z4,z6,z124]),(0,[z615,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z616,z4,z6])]],
   [[(0,[z91,z0,z1,z2,z61,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z617]),(0,[z0,z1,z2,z618,z3,z4,z6])],[(0,[z619,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z124,z34])],[(0,[z620,z0,z56,z2,z3,z4,z6]),(0,[z0,z56,z212,z2,z3,z4,z6]),(0,[z27,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z176,z2,z3,z142,z6]),(0,[z0,z1,z2,z3,z4,z621,z6]),(0,[z45,z0,z1,z2,z4,z6,z132])],[(0,[z105,z1,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z231,z3,z4,z6]),(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z623,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z132])],[(0,[z0,z56,z2,z92,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z456])],[(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z624,z6]),(0,[z0,z1,z2,z625,z3,z4,z6]),(0,[z334,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z289,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z626,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z628,z12,z3,z4,z6])],[(0,[z31,z0,z56,z2,z3,z4,z6]),(0,[z27,z197,z0,z2,z3,z4,z6]),(0,[z0,z1,z22,z3,z60,z4,z6]),(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z109,z0,z1,z176,z2,z3,z6]),(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z630,z34])],[(0,[z105,z0,z56,z2,z3,z4,z6]),(0,[z620,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z631,z6]),(0,[z0,z48,z2,z3,z4,z6,z135]),(1,[z481,z1,z2,z3,z4,z6]),(0,[z0,z1,z176,z2,z3,z60,z6])],[(0,[z632,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z633]),(0,[z634,z0,z1,z12,z3,z4,z6])],[(0,[z635,z0,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z212,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z636,z6]),(0,[z0,z1,z2,z3,z4,z6,z637]),(0,[z82,z0,z1,z22,z3,z4,z6]),(0,[z638,z0,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z142,z6]),(0,[z0,z1,z2,z15,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z122,z10])],[(0,[z82,z27,z0,z2,z3,z4,z6]),(0,[z639,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z93,z4,z6,z34]),(0,[z0,z640,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z166]),(1,[z0,z1,z2,z378,z50,z6])],[(0,[z0,z1,z2,z641,z3,z4,z6])]],
   [[(0,[z1,z56,z2,z14,z3,z4,z6]),(0,[z0,z1,z236,z2,z3,z4,z6]),(0,[z433,z0,z1,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z4,z642,z6]),(0,[z0,z1,z12,z3,z4,z301,z6]),(0,[z0,z1,z2,z3,z4,z6,z643]),(0,[z0,z1,z297,z8,z2,z3,z6])],[(0,[z31,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z19,z6])],[(0,[z0,z1,z2,z3,z644,z4,z6])],[(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z646,z6])],[(0,[z443,z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z10]),(0,[z264,z0,z1,z2,z163,z4,z6]),(0,[z647,z0,z1,z2,z3,z4,z6])],[(0,[z528,z27,z0,z2,z3,z4,z6]),(0,[z27,z0,z2,z378,z3,z4,z6]),(0,[z134,z0,z1,z12,z3,z4,z6]),(0,[z0,z18,z1,z2,z3,z6,z10]),(0,[z0,z1,z176,z12,z3,z4,z6]),(0,[z648,z0,z1,z2,z3,z4,z6])],[(0,[z91,z0,z236,z2,z3,z4,z6]),(0,[z280,z0,z1,z2,z58,z3,z6]),(0,[z0,z1,z2,z21,z3,z106,z4]),(0,[z0,z1,z2,z3,z6,z39,z10]),(0,[z184,z0,z1,z2,z3,z4,z6])],[(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z403])],[(0,[z27,z0,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z180]),(0,[z650,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z140,z3,z4,z6]),(0,[z121,z0,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z651]),(0,[z186,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z652,z3,z4,z6]),(0,[z0,z1,z2,z3,z653,z4,z6]),(0,[z0,z1,z2,z378,z3,z6,z10])],[(0,[z7,z36,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z654,z6]),(1,[z0,z1,z44,z2,z3,z6]),(0,[z0,z1,z2,z3,z655,z4,z6])],[(0,[z656,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z630]),(1,[z0,z1,z217,z2,z3,z6]),(0,[z0,z1,z8,z2,z3,z6,z10])],[(0,[z559,z0,z1,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z93,z4,z6]),(0,[z208,z27,z0,z2,z3,z4,z6]),(0,[z91,z0,z1,z248,z3,z4,z6]),(0,[z246,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z657]),(0,[z0,z658,z1,z2,z3,z4,z6]),(0,[z464,z0,z1,z2,z3,z6,z10])]],
   [[(0,[z151,z0,z56,z2,z3,z4,z6])],[(1,[z11,z0,z2,z3,z4,z135])],[(0,[z27,z0,z2,z14,z3,z4,z6]),(1,[z27,z0,z3,z4,z6,z34]),(0,[z105,z0,z1,z2,z3,z142,z6]),(0,[z0,z1,z2,z3,z659,z4,z6]),(0,[z108,z0,z211,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z660,z4,z6])],[(0,[z27,z0,z2,z16,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z83,z6])],[(0,[z91,z0,z1,z2,z3,z258,z6]),(1,[z0,z1,z144,z3,z4,z6]),(0,[z0,z661,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z3,z60,z4,z6])],[(1,[z30,z0,z1,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z6,z662])],[(0,[z0,z1,z2,z14,z3,z6,z10]),(0,[z0,z1,z2,z3,z4,z6,z663]),(0,[z0,z1,z2,z3,z43,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z664])],[(1,[z121,z1,z2,z14,z4,z6])],[(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z628,z2,z3,z4,z6])],[(0,[z0,z1,z665,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z666]),(0,[z0,z1,z667,z2,z3,z4,z6])],[(0,[z69,z0,z1,z8,z2,z3,z6])],[(0,[z108,z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z3,z163,z4,z6,z34]),(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z668,z4,z6])],[(0,[z0,z56,z2,z58,z3,z4,z6]),(0,[z27,z0,z2,z92,z3,z4,z6]),(0,[z0,z1,z8,z2,z22,z3,z6]),(0,[z47,z0,z1,z2,z3,z4,z33])],[(0,[z134,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z669,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z670,z4,z6]),(0,[z0,z1,z2,z3,z51,z6,z10]),(0,[z0,z1,z2,z3,z4,z6,z671]),(1,[z0,z1,z2,z3,z6,z10])],[(0,[z672,z0,z1,z2,z3,z4,z6])],[(0,[z129,z0,z1,z2,z3,z4,z6]),(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z675,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z263,z6]),(0,[z0,z1,z2,z92,z3,z6,z10])],[(1,[z0,z1,z212,z92,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z598]),(0,[z0,z1,z176,z3,z60,z4,z6])],[(0,[z108,z197,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z208,z0,z1,z3,z4,z6,z34])],[(0,[z27,z105,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z170,z6]),(0,[z45,z0,z1,z12,z3,z4,z6]),(0,[z414,z0,z1,z2,z3,z6,z10])],[(0,[z0,z56,z2,z9,z3,z4,z6]),(0,[z0,z1,z677,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z678]),(1,[z419,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z173])],[(0,[z11,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z268,z2,z3,z4,z6]),(0,[z105,z0,z1,z12,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z176,z2,z3,z4,z6]),(0,[z45,z0,z1,z289,z3,z4,z6])],[(0,[z0,z1,z311,z2,z3,z4,z6]),(1,[z0,z431,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z34]),(0,[z0,z1,z12,z3,z4,z6,z132])],[(0,[z30,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z6,z34,z75]),(0,[z0,z1,z2,z3,z679,z4,z6])],[(0,[z0,z2,z9,z3,z163,z4,z6])],[],[(0,[z78,z0,z461,z2,z3,z4,z6]),(0,[z0,z2,z3,z163,z4,z6,z135]),(0,[z0,z1,z2,z16,z163,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z378,z3,z50,z6])],[(0,[z681,z0,z56,z2,z3,z4,z6]),(0,[z0,z1,z176,z2,z3,z265,z6]),(0,[z30,z0,z1,z2,z3,z4,z122]),(0,[z0,z1,z8,z2,z3,z122,z6])],[],[(0,[z47,z69,z1,z2,z3,z4,z6])],[(0,[z682,z0,z1,z2,z3,z4,z6]),(0,[z27,z0,z2,z3,z4,z98,z6]),(0,[z69,z0,z1,z2,z3,z4,z124]),(0,[z264,z0,z1,z8,z2,z3,z6])],[(0,[z0,z56,z2,z474,z3,z4,z6]),(0,[z0,z1,z8,z140,z2,z3,z6]),(1,[z0,z1,z3,z4,z6,z266]),(0,[z0,z1,z2,z3,z4,z6,z683])]],
   [[(1,[z105,z56,z2,z3,z4,z6]),(0,[z0,z1,z188,z2,z3,z4,z6]),(1,[z376,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z591,z3,z4,z6])],[(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z685,z6])],[(0,[z0,z1,z3,z265,z4,z6,z34])],[(0,[z681,z0,z1,z2,z3,z4,z6]),(1,[z0,z461,z2,z3,z4,z6]),(0,[z686,z0,z1,z2,z3,z4,z6])],[(0,[z0,z56,z2,z3,z50,z4,z6]),(0,[z0,z56,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z348]),(0,[z256,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z8,z2,z3,z163,z6])],[(0,[z0,z1,z378,z3,z4,z6,z34]),(0,[z0,z1,z281,z8,z2,z3,z6])],[(0,[z82,z0,z1,z2,z3,z6,z10])],[(0,[z0,z1,z2,z3,z687,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z688])],[(0,[z208,z82,z0,z1,z2,z3,z6]),(0,[z656,z0,z1,z3,z4,z6,z34])],[(0,[z179,z105,z1,z2,z3,z4,z6]),(0,[z0,z689,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z417,z3,z4,z6]),(0,[z0,z1,z613,z2,z3,z4,z6])],[(0,[z45,z0,z56,z2,z3,z4,z6]),(0,[z91,z1,z56,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z6,z124]),(0,[z197,z400,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z364,z3,z4,z6])],[(0,[z0,z1,z3,z61,z4,z6,z34]),(1,[z0,z1,z311,z3,z4,z6]),(0,[z420,z197,z1,z2,z3,z4,z6])],[(0,[z581,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z690,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z691,z6]),(0,[z0,z1,z2,z3,z265,z4,z6]),(1,[z105,z1,z2,z3,z265,z6]),(0,[z197,z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z74,z6,z10]),(0,[z0,z1,z212,z2,z92,z4,z6]),(0,[z0,z1,z2,z692,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z201,z6]),(0,[z0,z1,z176,z2,z378,z3,z6])]],
   [[(0,[z693,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z694,z2,z3,z4,z6])],[(0,[z0,z1,z695,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z696,z4,z6]),(0,[z0,z1,z2,z378,z3,z6,z171])],[(0,[z27,z108,z0,z2,z3,z4,z6]),(0,[z0,z1,z8,z176,z2,z3,z6])],[(0,[z109,z0,z1,z8,z2,z3,z6])],[(0,[z27,z0,z2,z58,z3,z4,z6]),(0,[z0,z1,z12,z378,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z6,z171])],[(0,[z105,z0,z1,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z336,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z697])],[(0,[z0,z1,z2,z3,z371,z4,z6]),(0,[z0,z1,z8,z2,z3,z6,z135]),(0,[z0,z698,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z699,z4,z6]),(0,[z0,z1,z168,z2,z3,z4,z6])],[(0,[z208,z0,z1,z2,z3,z6,z10])],[(0,[z0,z1,z2,z58,z3,z6,z10]),(0,[z0,z1,z700,z2,z3,z4,z6])],[(0,[z0,z56,z2,z3,z4,z98,z6]),(0,[z0,z1,z2,z3,z701,z4,z6]),(0,[z0,z1,z2,z3,z702,z4,z6])],[(0,[z0,z1,z703,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z704,z4,z6]),(0,[z0,z1,z2,z3,z705,z4,z6]),(0,[z45,z0,z1,z416,z3,z4,z6])],[(0,[z105,z0,z1,z2,z3,z265,z6]),(0,[z70,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z8,z12,z2,z3,z6])],[(0,[z179,z1,z2,z3,z4,z142,z6]),(0,[z27,z0,z2,z9,z3,z4,z6])],[(1,[z0,z329,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z93,z4,z6]),(0,[z0,z1,z2,z3,z122,z6,z114])],[(0,[z706,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z391,z8,z2,z3,z6])],[(0,[z0,z1,z8,z212,z2,z3,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z463,z0,z2,z163,z4,z6]),(1,[z0,z1,z3,z4,z707]),(0,[z0,z1,z168,z3,z6,z10])],[(0,[z298,z56,z2,z3,z4,z6]),(0,[z0,z1,z454,z3,z4,z6]),(0,[z82,z0,z1,z3,z57,z6]),(0,[z0,z1,z8,z2,z15,z6]),(0,[z0,z1,z3,z4,z34,z608]),(0,[z0,z1,z3,z46,z6,z34]),(0,[z0,z708,z2,z3,z4,z6]),(1,[z376,z1,z2,z4,z132])],[(0,[z0,z56,z2,z210,z4,z6]),(0,[z709,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z35,z34]),(0,[z0,z710,z2,z3,z6,z10]),(0,[z0,z1,z711,z3,z4,z6])],[(0,[z0,z1,z8,z2,z3,z348]),(1,[z0,z2,z3,z4,z712]),(0,[z0,z1,z8,z416,z3,z6])],[(0,[z0,z1,z2,z713,z3,z6]),(0,[z0,z1,z112,z210,z4,z6]),(0,[z714,z1,z2,z3,z4,z6])],[(0,[z277,z0,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z2,z716,z163,z4,z6]),(0,[z66,z0,z1,z3,z4,z34]),(0,[z0,z1,z20,z3,z4,z34]),(0,[z0,z1,z3,z717,z4,z6]),(0,[z0,z1,z3,z6,z10,z34])],[(0,[z167,z0,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z718]),(0,[z0,z102,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z243,z719])],[(0,[z56,z2,z22,z3,z4,z6]),(0,[z56,z2,z3,z25,z4,z6]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z0,z1,z3,z61,z10,z34]),(0,[z0,z1,z3,z4,z723,z6]),(0,[z0,z1,z44,z3,z6,z34]),(0,[z724,z1,z3,z4,z6,z34]),(0,[z414,z0,z1,z3,z10,z34]),(0,[z0,z1,z2,z3,z6,z725])],[(0,[z91,z56,z119,z3,z4,z6]),(0,[z69,z324,z2,z3,z4,z6]),(0,[z23,z0,z3,z4,z6,z34])],[(0,[z77,z0,z1,z3,z10,z34]),(0,[z7,z36,z2,z3,z142,z6]),(0,[z109,z0,z1,z3,z10,z34]),(0,[z0,z1,z217,z3,z6,z34])],[(0,[z0,z1,z3,z4,z6,z726]),(0,[z31,z56,z2,z3,z32,z6]),(0,[z56,z2,z3,z4,z6,z35]),(0,[z207,z56,z2,z3,z4,z6])],[(0,[z45,z0,z56,z2,z4,z132]),(0,[z0,z1,z12,z3,z4,z243]),(0,[z0,z1,z8,z2,z3,z631]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z1,z2,z3,z149,z10]),(0,[z421,z0,z1,z3,z10,z34])],[(0,[z56,z2,z41,z3,z4,z6]),(0,[z0,z1,z12,z3,z32,z6]),(0,[z0,z1,z212,z652,z4,z6]),(0,[z0,z102,z416,z3,z4,z6])],[(0,[z0,z56,z231,z3,z4,z6]),(0,[z121,z1,z2,z728,z4,z6]),(0,[z0,z729,z2,z3,z4,z6]),(0,[z82,z0,z1,z536,z3,z6]),(0,[z0,z1,z3,z363,z4,z34]),(0,[z0,z1,z2,z3,z122,z10])],[(0,[z0,z1,z2,z3,z6,z730]),(0,[z0,z1,z2,z3,z243,z10]),(0,[z0,z731,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z732,z4,z6]),(0,[z275,z0,z1,z2,z6,z171]),(0,[z0,z194,z2,z3,z6,z10]),(0,[z0,z733,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z57,z6]),(0,[z0,z56,z734,z3,z4,z6]),(0,[z419,z1,z8,z2,z3,z6]),(0,[z151,z0,z1,z3,z4,z149])],[(1,[z56,z144,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z735]),(0,[z0,z1,z395,z2,z3,z6])],[(0,[z0,z56,z2,z3,z4,z6]),(0,[z408,z0,z1,z22,z3,z6]),(0,[z0,z1,z2,z3,z4,z736]),(0,[z594,z1,z2,z61,z4,z6]),(0,[z0,z431,z8,z2,z3,z6]),(0,[z23,z419,z2,z3,z4,z6]),(0,[z0,z737,z2,z3,z4,z6]),(0,[z0,z1,z92,z4,z6,z630]),(0,[z82,z0,z1,z115,z3,z6])],[(0,[z0,z1,z12,z3,z170,z6]),(0,[z0,z1,z8,z2,z3,z697])],[(0,[z0,z1,z2,z3,z738,z6]),(0,[z0,z1,z112,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z739]),(0,[z0,z1,z2,z716,z4,z6]),(0,[z134,z0,z2,z3,z51,z6])],[(0,[z0,z1,z231,z3,z4,z6]),(0,[z47,z1,z2,z3,z170,z124]),(0,[z740,z1,z12,z3,z4,z6])],[(0,[z27,z0,z2,z3,z6,z254]),(0,[z27,z0,z289,z3,z4,z6]),(0,[z0,z1,z147,z3,z4,z6])],[(0,[z69,z56,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z6,z403])],[(0,[z0,z152,z2,z3,z4,z6]),(0,[z56,z2,z676,z3,z4,z6]),(0,[z0,z1,z734,z3,z4,z6]),(0,[z91,z1,z2,z61,z4,z348]),(0,[z1,z2,z728,z61,z4,z6]),(0,[z0,z1,z8,z231,z3,z6]),(0,[z226,z1,z12,z3,z4,z6]),(0,[z151,z0,z1,z8,z93,z6]),(0,[z45,z0,z1,z4,z34,z132])],[(0,[z0,z1,z2,z3,z741,z6]),(0,[z294,z0,z2,z3,z4,z135]),(0,[z742,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z56,z2,z3,z4,z6,z80]),(0,[z425,z0,z257,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z743]),(0,[z0,z1,z16,z4,z98,z34]),(0,[z0,z1,z12,z744,z3,z6]),(0,[z376,z1,z2,z3,z4,z98])],[(0,[z0,z1,z2,z3,z745,z6]),(0,[z746,z1,z2,z3,z4,z6]),(0,[z0,z18,z2,z3,z4,z712]),(0,[z0,z1,z2,z3,z747,z6]),(0,[z748,z0,z1,z2,z3,z6])],[(0,[z105,z56,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z749,z6]),(0,[z0,z219,z2,z336,z4,z6]),(0,[z376,z1,z8,z2,z3,z6])],[(0,[z750,z0,z56,z2,z3,z6]),(0,[z0,z1,z751,z3,z4,z6]),(0,[z0,z752,z2,z3,z4,z6])],[(0,[z91,z56,z2,z3,z4,z6]),(0,[z27,z0,z119,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z753]),(0,[z0,z1,z2,z3,z6,z754])]],
   [[(0,[z91,z1,z2,z61,z6,z10]),(0,[z0,z1,z2,z3,z6,z755]),(0,[z82,z0,z1,z3,z83,z6]),(0,[z0,z1,z2,z3,z346,z122]),(0,[z0,z1,z756,z3,z4,z6])],[(0,[z0,z1,z2,z3,z757,z6]),(0,[z0,z1,z758,z3,z4,z6])],[(0,[z56,z22,z3,z4,z6,z34]),(0,[z27,z79,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z0,z1,z416,z3,z4,z6])],[(0,[z0,z236,z2,z3,z4,z348]),(0,[z376,z194,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z198,z10])],[(0,[z0,z56,z2,z3,z4,z243]),(0,[z27,z0,z176,z3,z60,z6]),(0,[z0,z1,z2,z3,z6,z760]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z321,z1,z417,z3,z4,z6])],[(0,[z656,z56,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z32,z6]),(0,[z0,z56,z12,z3,z4,z122])],[(0,[z56,z2,z3,z4,z103,z6]),(0,[z0,z762,z2,z3,z4,z6]),(0,[z528,z24,z2,z3,z4,z6]),(0,[z763,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z3,z6,z10])],[(0,[z31,z56,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z6,z764]),(0,[z0,z1,z765,z2,z3,z6])],[(0,[z56,z2,z3,z4,z685,z6]),(0,[z0,z1,z3,z6,z94,z34]),(0,[z0,z1,z766,z3,z6,z10])],[(0,[z0,z56,z190,z2,z3,z6]),(0,[z0,z1,z767,z2,z3,z6]),(0,[z768,z0,z2,z3,z4,z6]),(0,[z481,z2,z3,z4,z74,z6]),(0,[z0,z1,z2,z40,z137,z6]),(0,[z0,z1,z2,z15,z43,z6]),(0,[z0,z1,z2,z3,z363,z10]),(1,[z0,z1,z3,z10,z34]),(0,[z0,z1,z20,z3,z67,z6])],[(0,[z71,z56,z2,z3,z4,z6]),(0,[z0,z236,z2,z3,z6,z10]),(0,[z0,z152,z2,z3,z4,z243]),(0,[z91,z1,z2,z61,z371,z6]),(0,[z769,z0,z1,z2,z3,z6]),(0,[z246,z1,z2,z3,z46,z6])],[(0,[z56,z2,z3,z4,z6,z118]),(0,[z0,z56,z2,z3,z770,z6]),(0,[z0,z1,z2,z3,z771,z6]),(0,[z0,z1,z248,z3,z4,z348]),(0,[z0,z1,z772,z2,z3,z6]),(0,[z109,z0,z700,z2,z3,z6]),(0,[z0,z1,z44,z63,z3,z6]),(0,[z0,z1,z3,z4,z773,z34])],[(0,[z0,z56,z2,z3,z170,z6]),(0,[z620,z0,z2,z3,z51,z6]),(0,[z0,z1,z2,z3,z774,z6]),(0,[z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z775,z3,z4,z6]),(0,[z208,z0,z1,z2,z6,z776])],[(0,[z0,z1,z777,z3,z4,z6]),(0,[z7,z0,z1,z3,z10,z34]),(0,[z0,z1,z12,z210,z4,z6]),(0,[z0,z1,z12,z3,z4,z122]),(0,[z0,z1,z3,z774,z6,z34])],[(0,[z0,z1,z112,z3,z170,z6]),(0,[z108,z400,z2,z3,z4,z6]),(0,[z0,z778,z2,z3,z4,z6])],[(0,[z425,z56,z2,z3,z4,z6]),(0,[z56,z2,z3,z687,z4,z6]),(0,[z47,z1,z2,z210,z4,z124]),(0,[z197,z0,z8,z58,z3,z6]),(0,[z0,z1,z12,z3,z4,z73])]],
   [[(0,[z397,z56,z2,z3,z4,z124]),(0,[z464,z56,z2,z3,z6,z10]),(0,[z779,z0,z8,z2,z3,z6])],[(0,[z226,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z258,z348]),(0,[z0,z1,z190,z2,z3,z6])],[(0,[z780,z0,z56,z3,z4,z6]),(0,[z0,z1,z2,z3,z781,z6]),(0,[z0,z1,z248,z3,z6,z10]),(0,[z0,z1,z3,z6,z114,z34])],[(0,[z382,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z609,z1,z2,z61,z4,z6]),(0,[z120,z0,z3,z4,z6,z34]),(0,[z0,z219,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z704,z10]),(0,[z0,z1,z782,z3,z4,z6]),(0,[z246,z1,z2,z3,z72,z6])],[(0,[z56,z2,z3,z4,z6,z136]),(0,[z0,z1,z140,z3,z32,z6]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z82,z0,z1,z3,z159,z6]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z2,z3,z170,z6]),(0,[z0,z1,z217,z12,z3,z122])],[(0,[z0,z1,z2,z3,z785,z6]),(0,[z47,z219,z2,z3,z4,z124])],[(0,[z0,z1,z8,z311,z3,z6]),(0,[z433,z0,z1,z3,z4,z6]),(0,[z740,z1,z2,z3,z4,z6]),(0,[z207,z1,z12,z3,z4,z6]),(0,[z246,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z106,z10])],[(0,[z408,z27,z0,z2,z3,z6]),(0,[z226,z152,z2,z3,z4,z6]),(0,[z200,z0,z2,z3,z51,z6]),(0,[z207,z1,z2,z15,z4,z6]),(0,[z0,z786,z2,z3,z4,z6])],[(0,[z151,z0,z56,z93,z4,z6]),(0,[z502,z56,z2,z3,z4,z6]),(0,[z397,z1,z2,z3,z4,z124]),(0,[z543,z1,z2,z3,z4,z124]),(0,[z0,z1,z2,z336,z6,z10]),(0,[z82,z0,z1,z3,z274,z6]),(0,[z109,z0,z3,z232,z74,z6])],[(0,[z226,z1,z2,z3,z4,z6]),(0,[z56,z2,z144,z3,z4,z6]),(0,[z11,z0,z1,z3,z10,z34]),(0,[z0,z1,z92,z787,z4,z6])],[(0,[z105,z1,z2,z3,z440,z6]),(0,[z0,z1,z2,z3,z788,z6]),(0,[z27,z0,z2,z789,z4,z6]),(0,[z615,z0,z1,z3,z4,z34]),(0,[z0,z329,z8,z2,z3,z6]),(0,[z0,z1,z790,z2,z3,z6]),(0,[z791,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z336,z331,z6]),(0,[z0,z1,z792,z2,z3,z6]),(0,[z82,z0,z1,z3,z175,z6]),(0,[z581,z0,z3,z4,z6,z347])],[(0,[z0,z56,z178,z3,z4,z6]),(0,[z47,z1,z231,z3,z4,z124]),(0,[z793,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z744,z3,z6])],[(0,[z334,z1,z406,z2,z3,z6])],[(0,[z56,z2,z3,z4,z6,z150]),(0,[z30,z0,z56,z3,z4,z34]),(0,[z0,z1,z2,z3,z794,z6])],[(0,[z400,z56,z2,z3,z4,z6]),(0,[z121,z1,z14,z4,z6,z34]),(0,[z464,z0,z1,z3,z10,z34]),(0,[z795,z0,z1,z3,z4,z6])],[(0,[z278,z56,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z796]),(0,[z0,z1,z210,z4,z6,z34]),(0,[z0,z1,z797,z3,z4,z6]),(0,[z0,z1,z2,z798,z4,z6]),(0,[z799,z0,z2,z3,z4,z6]),(0,[z1,z2,z3,z6,z10,z800])]],
   [[(0,[z0,z193,z2,z3,z4,z19]),(0,[z0,z1,z801,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z802]),(0,[z207,z1,z2,z3,z43,z6]),(0,[z0,z18,z8,z2,z3,z19]),(0,[z0,z1,z281,z553,z3,z6])],[(0,[z0,z56,z3,z4,z6,z34]),(0,[z379,z56,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z348,z796]),(0,[z24,z1,z8,z2,z3,z6]),(0,[z246,z102,z2,z3,z4,z6])],[(0,[z82,z56,z22,z3,z4,z6]),(0,[z27,z0,z3,z4,z6,z338]),(0,[z91,z1,z2,z728,z4,z6]),(0,[z0,z1,z8,z2,z3,z224]),(0,[z400,z1,z3,z60,z4,z6]),(0,[z0,z18,z1,z3,z10,z34])],[(0,[z386,z0,z427,z3,z4,z6]),(0,[z0,z1,z178,z3,z4,z6])],[(0,[z36,z0,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z803,z6])],[(0,[z0,z804,z2,z3,z4,z6])],[(0,[z315,z56,z2,z3,z4,z6]),(0,[z56,z14,z3,z4,z6,z34]),(0,[z56,z2,z3,z164,z4,z6]),(0,[z0,z1,z2,z3,z6,z805]),(0,[z24,z18,z2,z3,z4,z6])],[(0,[z0,z152,z3,z4,z6,z34]),(0,[z42,z0,z8,z2,z3,z6]),(0,[z0,z1,z3,z4,z806,z6])],[(0,[z56,z12,z14,z3,z4,z6]),(0,[z0,z56,z8,z12,z3,z6]),(0,[z0,z807,z2,z3,z4,z6]),(0,[z0,z1,z231,z210,z4,z6]),(0,[z109,z110,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z43,z6])],[(0,[z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z212,z318,z4,z6]),(0,[z0,z1,z2,z3,z808,z6])],[(0,[z296,z56,z22,z3,z4,z6]),(0,[z0,z169,z12,z3,z4,z6])],[(0,[z27,z0,z2,z3,z346,z6]),(0,[z809,z1,z2,z3,z4,z6])],[(0,[z31,z56,z2,z3,z6,z10]),(0,[z27,z0,z2,z3,z46,z6]),(0,[z45,z0,z1,z2,z46,z132])],[(0,[z45,z27,z0,z2,z4,z132]),(0,[z0,z1,z2,z210,z4,z6]),(0,[z0,z219,z112,z3,z4,z6]),(0,[z82,z0,z1,z3,z301,z6])],[(0,[z810,z56,z2,z3,z4,z6]),(0,[z56,z3,z4,z6,z34,z181]),(0,[z246,z56,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z106,z10])],[(0,[z811,z1,z2,z3,z4,z6]),(0,[z0,z1,z477,z4,z6,z630])]],
   [[(0,[z0,z1,z12,z3,z331,z6]),(0,[z0,z1,z8,z12,z3,z6]),(0,[z0,z1,z289,z3,z6,z10])],[(0,[z0,z1,z119,z3,z4,z348]),(0,[z0,z812,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z6,z813]),(0,[z0,z1,z92,z4,z6,z651])],[(0,[z0,z219,z2,z3,z4,z6]),(0,[z56,z2,z52,z3,z4,z6]),(0,[z656,z56,z3,z4,z6,z34]),(0,[z634,z56,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z814,z6]),(0,[z1,z2,z336,z4,z6,z124]),(0,[z0,z1,z8,z2,z336,z6])],[(0,[z423,z56,z2,z3,z4,z6]),(0,[z0,z56,z97,z3,z4,z6]),(0,[z27,z7,z2,z3,z142,z6]),(0,[z0,z1,z52,z3,z60,z6]),(0,[z0,z1,z3,z4,z6,z815]),(0,[z0,z1,z816,z3,z4,z6])],[(0,[z31,z56,z22,z3,z4,z6]),(0,[z27,z0,z2,z3,z72,z6]),(0,[z100,z1,z22,z3,z4,z6]),(0,[z0,z1,z3,z43,z6,z34]),(0,[z0,z817,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z72,z132])],[(0,[z1,z56,z144,z3,z4,z6]),(0,[z207,z1,z2,z3,z4,z6]),(0,[z246,z1,z2,z3,z4,z6]),(0,[z324,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z394,z50,z6]),(0,[z11,z0,z2,z3,z4,z712]),(0,[z0,z1,z2,z3,z6,z818]),(0,[z0,z1,z2,z3,z106,z10])],[(0,[z386,z0,z58,z3,z4,z6]),(0,[z420,z1,z3,z4,z6,z34]),(0,[z819,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z820]),(0,[z151,z0,z1,z300,z4,z6])],[(0,[z27,z0,z12,z3,z4,z6]),(0,[z1,z56,z2,z3,z4,z348]),(0,[z0,z1,z119,z3,z6,z10]),(0,[z0,z1,z12,z3,z371,z6]),(0,[z120,z0,z2,z3,z6,z10]),(1,[z1,z2,z3,z4,z821]),(0,[z0,z1,z26,z15,z4,z6]),(0,[z0,z1,z12,z3,z4,z166]),(0,[z822,z0,z2,z3,z4,z6])],[(0,[z27,z0,z2,z3,z357,z6]),(0,[z27,z0,z2,z15,z4,z6]),(0,[z0,z1,z823,z2,z3,z6]),(0,[z824,z1,z2,z3,z4,z6])],[(0,[z0,z188,z2,z3,z6,z10]),(0,[z0,z1,z8,z2,z3,z153]),(0,[z134,z0,z1,z2,z3,z149]),(0,[z0,z1,z825,z3,z4,z6]),(0,[z0,z1,z826,z3,z6,z10]),(0,[z827,z0,z2,z3,z6,z10])],[(0,[z7,z1,z3,z142,z6,z34]),(0,[z0,z1,z828,z3,z4,z6]),(0,[z829,z0,z8,z2,z3,z6])],[(0,[z1,z2,z3,z61,z4,z348]),(0,[z0,z1,z2,z3,z830,z6]),(0,[z0,z1,z97,z3,z4,z6]),(0,[z30,z0,z1,z8,z3,z34])],[(0,[z831,z0,z2,z3,z4,z6]),(0,[z246,z1,z416,z3,z4,z6]),(0,[z414,z0,z2,z3,z6,z235])],[(0,[z27,z0,z454,z3,z4,z6]),(0,[z0,z1,z3,z60,z832,z6])],[(0,[z56,z2,z206,z3,z4,z6]),(0,[z833,z69,z2,z3,z4,z6]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z27,z481,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z8,z248,z3,z6]),(0,[z1,z2,z14,z728,z4,z6]),(0,[z134,z481,z2,z3,z4,z6]),(0,[z0,z1,z836,z3,z4,z6])]],
   [[(0,[z91,z1,z8,z2,z61,z6]),(0,[z594,z1,z2,z3,z4,z124]),(0,[z0,z1,z837,z3,z4,z6]),(0,[z0,z1,z3,z4,z465,z34]),(0,[z0,z1,z20,z3,z10,z34]),(0,[z0,z838,z2,z3,z4,z6])],[(0,[z27,z0,z2,z713,z3,z6]),(0,[z0,z1,z281,z176,z3,z6]),(0,[z1,z3,z4,z6,z34,z839])],[(0,[z162,z56,z2,z3,z4,z6]),(0,[z27,z0,z3,z6,z10,z34]),(0,[z0,z1,z119,z3,z371,z6]),(0,[z408,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z832,z6])],[(0,[z0,z461,z8,z2,z3,z6]),(0,[z376,z1,z289,z3,z4,z6])],[(0,[z0,z1,z840,z3,z4,z6]),(0,[z0,z56,z3,z4,z841,z6]),(0,[z0,z1,z2,z3,z6,z842]),(0,[z843,z0,z1,z3,z4,z6])],[(0,[z121,z1,z8,z2,z14,z6]),(0,[z0,z1,z2,z3,z293,z10]),(0,[z844,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z845,z6])],[(0,[z0,z1,z2,z210,z170,z6]),(0,[z0,z846,z2,z3,z4,z6]),(0,[z0,z1,z3,z6,z254,z266]),(0,[z280,z197,z0,z58,z3,z6]),(0,[z0,z1,z2,z3,z847,z6]),(0,[z848,z1,z2,z3,z4,z6]),(0,[z134,z0,z3,z51,z6,z34]),(0,[z0,z1,z562,z3,z4,z34]),(0,[z207,z2,z3,z4,z6,z135]),(0,[z0,z18,z2,z3,z19,z403]),(0,[z0,z1,z3,z10,z34,z456]),(0,[z0,z1,z12,z3,z6,z114]),(0,[z0,z849,z2,z3,z4,z6])],[(0,[z0,z56,z8,z2,z3,z10]),(0,[z226,z1,z3,z4,z6,z34]),(0,[z0,z1,z850,z3,z4,z6]),(0,[z0,z1,z178,z15,z4,z6]),(0,[z0,z1,z2,z4,z851,z132])],[(0,[z0,z56,z2,z3,z331,z6]),(0,[z0,z56,z3,z852,z4,z6]),(0,[z0,z853,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z854,z6])],[(0,[z69,z0,z1,z3,z10,z34]),(0,[z400,z1,z12,z3,z4,z6]),(0,[z82,z0,z1,z3,z249,z6]),(1,[z0,z1,z2,z4,z851])],[(0,[z0,z169,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z179,z27,z3,z4,z6,z34]),(0,[z0,z1,z112,z3,z331,z6]),(0,[z0,z1,z2,z3,z6,z856])],[(0,[z56,z2,z228,z3,z4,z6]),(0,[z27,z0,z2,z3,z122,z10]),(0,[z0,z857,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z841,z6]),(0,[z69,z431,z2,z3,z4,z6]),(0,[z0,z219,z2,z3,z170,z6])],[(0,[z559,z56,z2,z14,z4,z6]),(0,[z0,z1,z3,z33,z10,z34]),(0,[z0,z1,z3,z480,z4,z34]),(0,[z858,z0,z2,z3,z4,z6])],[(0,[z397,z0,z2,z3,z4,z381]),(0,[z481,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z859])],[(0,[z0,z56,z26,z3,z4,z6]),(0,[z27,z0,z395,z2,z3,z6]),(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z2,z3,z415,z10]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z1,z2,z3,z346,z34]),(0,[z0,z1,z8,z2,z3,z10])]],
   [[(0,[z0,z56,z2,z3,z371,z6]),(0,[z0,z56,z2,z3,z4,z166]),(0,[z0,z1,z3,z852,z4,z6]),(0,[z0,z1,z2,z3,z32,z6]),(0,[z459,z1,z2,z14,z4,z6]),(0,[z264,z0,z8,z2,z163,z6]),(0,[z0,z1,z2,z862,z4,z6]),(0,[z134,z0,z2,z3,z863,z6]),(0,[z0,z1,z178,z3,z43,z6]),(0,[z864,z0,z2,z3,z4,z6]),(0,[z865,z0,z1,z2,z3,z6])],[(0,[z0,z56,z2,z866,z4,z6]),(0,[z23,z0,z2,z3,z6,z10])],[(0,[z27,z0,z112,z3,z4,z6]),(0,[z0,z1,z231,z3,z170,z6]),(0,[z197,z0,z58,z3,z4,z6]),(0,[z0,z1,z378,z3,z10,z34]),(0,[z0,z1,z3,z4,z697,z34]),(0,[z0,z1,z12,z378,z50,z6])],[(0,[z91,z56,z2,z3,z4,z243]),(0,[z634,z56,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z867]),(0,[z376,z1,z2,z4,z6,z132])],[(0,[z0,z1,z868,z3,z4,z6]),(0,[z0,z56,z12,z3,z4,z34]),(0,[z27,z0,z147,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z149]),(0,[z0,z1,z3,z4,z832,z6]),(0,[z0,z1,z869,z3,z4,z6]),(0,[z0,z1,z3,z6,z10,z173]),(0,[z376,z1,z2,z3,z4,z132])],[(0,[z27,z0,z2,z3,z6,z403]),(0,[z105,z188,z2,z3,z4,z6]),(0,[z82,z0,z1,z3,z267,z6])],[(0,[z0,z56,z2,z3,z870,z4]),(0,[z179,z1,z2,z3,z258,z6]),(0,[z27,z523,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z584,z34]),(0,[z0,z152,z2,z3,z371,z6]),(0,[z0,z1,z3,z4,z492,z34]),(0,[z0,z1,z494,z3,z4,z34])],[(0,[z27,z433,z0,z3,z4,z6]),(0,[z0,z1,z26,z3,z4,z6]),(0,[z264,z0,z2,z163,z6,z10]),(0,[z871,z0,z2,z3,z4,z6]),(0,[z0,z102,z3,z4,z6,z34]),(0,[z182,z0,z1,z3,z6,z10]),(0,[z0,z1,z2,z3,z872,z6])],[(0,[z27,z0,z2,z3,z4,z6]),(0,[z0,z1,z56,z3,z10,z34]),(0,[z91,z1,z2,z540,z4,z6]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z166]),(0,[z45,z0,z1,z2,z4,z132]),(0,[z0,z1,z3,z4,z198,z10]),(0,[z874,z0,z2,z3,z6,z10])],[(0,[z0,z56,z3,z4,z6,z62]),(0,[z0,z1,z2,z866,z4,z6]),(0,[z151,z27,z0,z93,z4,z6])],[(0,[z56,z2,z3,z4,z6,z251]),(0,[z0,z324,z12,z3,z4,z6]),(0,[z69,z1,z3,z4,z33,z34]),(0,[z0,z1,z12,z3,z4,z678]),(0,[z134,z0,z2,z446,z3,z6])],[(0,[z27,z0,z751,z3,z4,z6]),(0,[z0,z875,z2,z3,z4,z6]),(0,[z108,z0,z876,z3,z4,z6]),(0,[z0,z1,z3,z93,z10,z34]),(0,[z0,z1,z3,z10,z85,z34])],[(0,[z559,z0,z2,z163,z4,z6]),(0,[z420,z1,z2,z3,z6,z10]),(0,[z0,z1,z176,z3,z832,z6]),(0,[z0,z1,z12,z3,z4,z34]),(0,[z30,z0,z1,z3,z346,z34])],[(0,[z27,z56,z12,z3,z4,z6]),(0,[z42,z105,z2,z3,z265,z6])],[(0,[z56,z2,z148,z3,z4,z6]),(0,[z0,z56,z2,z3,z6,z114]),(0,[z0,z1,z2,z3,z870,z4]),(0,[z30,z27,z0,z3,z4,z34]),(0,[z0,z1,z877,z3,z4,z6]),(0,[z878,z1,z2,z3,z4,z6]),(0,[z207,z1,z178,z3,z4,z6])],[(0,[z56,z8,z2,z14,z3,z6]),(0,[z152,z56,z2,z3,z4,z6]),(0,[z27,z0,z416,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z450]),(0,[z0,z1,z14,z3,z10,z34]),(0,[z0,z1,z3,z6,z10,z266]),(0,[z879,z0,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z16,z98])]],
   [[(0,[z0,z1,z16,z3,z10,z34]),(0,[z0,z1,z880,z3,z4,z6])],[(0,[z620,z56,z2,z3,z142,z6]),(0,[z27,z0,z2,z3,z6,z760]),(0,[z0,z881,z2,z3,z4,z6]),(0,[z0,z1,z882,z3,z4,z6]),(0,[z0,z883,z2,z3,z4,z6]),(0,[z0,z1,z8,z112,z3,z6]),(1,[z1,z2,z336,z4,z124]),(0,[z0,z1,z3,z4,z6,z62]),(0,[z151,z408,z0,z1,z93,z6]),(0,[z0,z1,z3,z4,z346,z34])],[(0,[z121,z1,z2,z3,z4,z348]),(0,[z208,z0,z1,z6,z34,z171]),(0,[z0,z1,z3,z884,z6,z34]),(0,[z0,z1,z8,z12,z3,z122])],[(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z1,z336,z4,z6,z34]),(0,[z886,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z887,z4,z6])],[(0,[z0,z431,z2,z336,z4,z6]),(0,[z69,z185,z2,z3,z4,z33]),(0,[z69,z1,z8,z2,z3,z33]),(0,[z207,z1,z3,z4,z6,z34]),(0,[z888,z0,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z149])],[(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z3,z371,z6,z34]),(0,[z0,z219,z2,z210,z4,z6]),(0,[z11,z0,z12,z3,z4,z135]),(0,[z0,z1,z2,z16,z98,z10])],[(0,[z481,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z114])],[(0,[z418,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z890,z4,z6])],[(0,[z184,z1,z2,z3,z142,z6])],[(0,[z0,z56,z12,z3,z6,z10]),(0,[z400,z1,z2,z3,z4,z6]),(0,[z27,z0,z2,z3,z4,z243]),(0,[z0,z891,z2,z3,z4,z6]),(0,[z0,z1,z92,z3,z10,z34]),(0,[z0,z1,z3,z10,z333,z34])],[(0,[z0,z56,z2,z378,z50,z6]),(0,[z750,z0,z1,z2,z3,z6]),(0,[z27,z0,z12,z3,z4,z122]),(0,[z0,z1,z2,z892,z4,z6]),(0,[z0,z1,z12,z3,z4,z348]),(0,[z0,z893,z2,z3,z4,z6]),(0,[z0,z185,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z894,z6]),(0,[z82,z481,z1,z2,z3,z6]),(0,[z82,z0,z1,z3,z10,z34]),(0,[z0,z1,z628,z318,z4,z6])],[(0,[z0,z1,z3,z4,z895,z6]),(0,[z0,z1,z896,z2,z3,z6]),(0,[z0,z1,z212,z787,z4,z6])],[(0,[z56,z2,z3,z4,z6,z181]),(0,[z580,z82,z0,z1,z3,z6])],[(0,[z167,z0,z12,z3,z4,z6]),(0,[z0,z897,z2,z3,z4,z6]),(0,[z0,z18,z2,z40,z4,z6])],[(0,[z481,z1,z2,z3,z4,z6]),(0,[z27,z0,z190,z2,z3,z6]),(0,[z167,z0,z2,z3,z357,z6]),(0,[z0,z1,z3,z4,z348,z34]),(0,[z0,z1,z3,z4,z243,z898])],[(1,[z899,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z900]),(0,[z0,z1,z8,z144,z3,z6]),(0,[z0,z1,z8,z2,z210,z6]),(0,[z0,z1,z901,z3,z4,z6]),(0,[z0,z1,z3,z64,z10,z34]),(0,[z0,z1,z902,z2,z3,z10]),(0,[z0,z376,z1,z2,z4,z132]),(0,[z903,z0,z2,z3,z4,z6])]],
   [[(0,[z91,z56,z3,z4,z6,z34]),(0,[z56,z2,z3,z4,z279,z6]),(0,[z904,z27,z0,z3,z4,z6]),(0,[z280,z0,z1,z12,z3,z6]),(0,[z0,z1,z8,z3,z6,z62]),(0,[z0,z194,z8,z2,z3,z6])],[(0,[z105,z56,z2,z3,z142,z6]),(0,[z27,z0,z2,z3,z170,z6]),(0,[z0,z219,z231,z3,z4,z6]),(0,[z0,z1,z12,z3,z6,z10]),(0,[z184,z1,z2,z3,z6,z513])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z186,z0,z2,z3,z74,z6]),(0,[z0,z1,z2,z15,z6,z10]),(0,[z208,z0,z1,z2,z3,z149]),(0,[z0,z1,z3,z10,z34,z598]),(0,[z0,z1,z2,z378,z50,z6])],[(0,[z0,z56,z8,z3,z6,z34]),(0,[z0,z1,z2,z906,z4,z6]),(0,[z581,z0,z58,z3,z4,z6]),(0,[z0,z1,z2,z907,z3,z4])],[(0,[z337,z56,z2,z3,z4,z6]),(0,[z91,z27,z2,z61,z4,z6]),(0,[z0,z1,z908,z3,z4,z6]),(0,[z909,z0,z1,z12,z3,z6])],[(0,[z0,z1,z2,z910,z4,z6]),(0,[z47,z1,z2,z3,z331,z124]),(0,[z0,z1,z911,z2,z3,z6]),(0,[z912,z1,z2,z3,z4,z6])],[(0,[z0,z56,z44,z2,z3,z6]),(0,[z179,z1,z119,z3,z4,z6]),(0,[z0,z1,z913,z3,z4,z6]),(0,[z914,z0,z2,z3,z4,z6])],[(0,[z0,z915,z2,z3,z4,z6]),(0,[z0,z1,z454,z3,z6,z10]),(1,[z0,z876,z3,z4,z6]),(0,[z294,z0,z1,z2,z4,z132]),(0,[z0,z18,z3,z4,z19,z34]),(0,[z0,z1,z2,z3,z345,z10]),(0,[z0,z1,z3,z10,z34,z34])],[(0,[z0,z810,z2,z3,z4,z6]),(0,[z0,z56,z217,z2,z3,z6]),(0,[z0,z1,z2,z916,z4,z6]),(0,[z0,z1,z2,z3,z487,z10]),(0,[z69,z1,z2,z3,z4,z821]),(0,[z82,z400,z1,z3,z4,z6]),(0,[z917,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z787,z4,z6]),(0,[z0,z1,z3,z4,z6,z918]),(0,[z376,z1,z2,z3,z46,z6])],[(0,[z56,z2,z3,z4,z6,z293]),(0,[z0,z876,z58,z3,z4,z6])],[(0,[z0,z324,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z919]),(0,[z0,z431,z12,z3,z4,z6]),(0,[z108,z0,z8,z211,z3,z6])],[(0,[z1,z2,z3,z4,z821,z124]),(0,[z0,z1,z920,z3,z4,z6]),(0,[z0,z1,z8,z3,z6,z34]),(0,[z0,z1,z921,z3,z4,z6])],[(0,[z0,z922,z2,z3,z4,z6]),(0,[z0,z102,z2,z3,z6,z10])],[(0,[z27,z56,z2,z3,z4,z6]),(0,[z574,z56,z2,z3,z4,z6]),(0,[z31,z0,z1,z3,z10,z34]),(0,[z0,z1,z923,z3,z4,z6]),(0,[z0,z1,z311,z3,z142,z6]),(0,[z924,z1,z2,z3,z4,z6])],[(0,[z0,z1,z925,z3,z4,z6]),(0,[z56,z2,z22,z3,z6,z10]),(0,[z780,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z926]),(0,[z0,z1,z44,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z927]),(0,[z864,z0,z3,z4,z6,z34])],[(0,[z56,z12,z3,z4,z142,z6]),(0,[z475,z56,z2,z3,z4,z6]),(0,[z69,z1,z2,z3,z33,z10]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z18,z63,z3,z4,z19]),(0,[z1,z2,z3,z4,z6,z839]),(0,[z929,z0,z2,z3,z4,z6])]],
   [[(0,[z930,z0,z2,z3,z4,z6]),(0,[z56,z2,z14,z4,z6,z132]),(0,[z0,z56,z144,z3,z4,z6]),(0,[z0,z1,z2,z3,z348,z926]),(0,[z0,z931,z2,z3,z4,z6]),(0,[z932,z1,z2,z3,z4,z6]),(0,[z0,z1,z15,z4,z6,z34])],[(0,[z1,z877,z2,z3,z4,z6]),(0,[z0,z1,z933,z3,z4,z6]),(0,[z0,z1,z374,z2,z3,z10]),(0,[z934,z1,z2,z3,z4,z6]),(0,[z0,z1,z190,z97,z3,z6])],[(0,[z0,z56,z2,z3,z4,z348]),(0,[z0,z1,z2,z210,z331,z6])],[(0,[z495,z56,z2,z3,z4,z6]),(0,[z121,z56,z2,z14,z4,z6]),(0,[z0,z1,z2,z935,z4,z6])],[(0,[z91,z810,z2,z3,z4,z6]),(0,[z105,z56,z12,z3,z4,z6]),(0,[z0,z56,z128,z3,z4,z6]),(0,[z0,z1,z26,z3,z43,z6]),(0,[z151,z0,z1,z93,z4,z6]),(0,[z0,z1,z12,z3,z936,z6]),(0,[z376,z1,z12,z3,z4,z6])],[(0,[z0,z1,z2,z3,z6,z937]),(0,[z27,z0,z2,z3,z43,z6]),(0,[z541,z0,z2,z163,z4,z6]),(0,[z11,z0,z2,z3,z4,z135])],[(0,[z648,z56,z2,z3,z4,z6]),(0,[z496,z1,z2,z3,z4,z124])],[(0,[z0,z1,z938,z3,z4,z6]),(0,[z0,z1,z3,z74,z10,z34]),(0,[z0,z1,z2,z787,z4,z6])],[(0,[z0,z1,z144,z3,z4,z6]),(0,[z0,z152,z2,z3,z4,z348]),(0,[z939,z0,z1,z3,z4,z6]),(0,[z0,z1,z940,z3,z4,z6])],[(0,[z0,z56,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z6,z719]),(0,[z30,z0,z1,z3,z4,z34])],[(0,[z27,z0,z2,z210,z4,z6]),(0,[z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z2,z3,z4,z941])],[(0,[z0,z1,z112,z3,z6,z10]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z1,z563,z3,z4,z34])],[(0,[z0,z1,z2,z3,z6,z943]),(0,[z944,z0,z2,z3,z4,z6]),(0,[z264,z0,z2,z716,z4,z6]),(0,[z0,z1,z128,z3,z4,z6])],[(0,[z167,z0,z2,z3,z4,z6]),(0,[z99,z56,z2,z3,z4,z6]),(0,[z0,z56,z945,z3,z4,z6]),(0,[z0,z56,z212,z92,z4,z6]),(0,[z27,z0,z8,z12,z3,z6]),(0,[z31,z461,z2,z3,z4,z6]),(0,[z946,z0,z2,z3,z4,z6]),(0,[z475,z1,z2,z3,z265,z6]),(0,[z197,z0,z700,z3,z4,z6]),(0,[z0,z1,z92,z3,z4,z149]),(0,[z527,z0,z364,z3,z4,z6]),(0,[z0,z1,z147,z3,z6,z10])],[(0,[z91,z56,z2,z3,z4,z348]),(0,[z0,z1,z231,z3,z331,z6]),(0,[z0,z1,z12,z3,z4,z707])],[(0,[z0,z1,z947,z3,z4,z6]),(0,[z0,z152,z2,z3,z6,z10]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z376,z102,z2,z3,z4,z6])]],
   [[(0,[z0,z56,z3,z4,z6,z173]),(0,[z419,z56,z2,z3,z4,z6]),(0,[z27,z419,z2,z3,z4,z6]),(0,[z742,z1,z2,z3,z6,z10])],[(0,[z0,z1,z2,z3,z6,z10]),(0,[z0,z1,z58,z3,z10,z34]),(0,[z949,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z950]),(0,[z105,z1,z12,z3,z265,z6]),(0,[z207,z1,z26,z3,z4,z6]),(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z1,z21,z3,z4,z773])],[(0,[z0,z1,z2,z3,z4,z952]),(0,[z56,z2,z234,z3,z4,z6]),(0,[z385,z0,z2,z3,z4,z180]),(0,[z27,z0,z2,z3,z106,z10]),(0,[z471,z0,z1,z2,z4,z132]),(0,[z0,z1,z2,z3,z331,z6]),(0,[z0,z953,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z954,z6]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z431,z112,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z302])],[(0,[z0,z1,z945,z3,z4,z6]),(0,[z0,z1,z956,z2,z3,z6]),(0,[z0,z957,z2,z3,z4,z6])],[(0,[z27,z245,z2,z3,z4,z6]),(0,[z27,z0,z231,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z65]),(0,[z0,z2,z40,z4,z6,z135]),(0,[z0,z1,z2,z3,z958,z6]),(0,[z959,z1,z2,z3,z4,z6])],[(0,[z960,z56,z2,z3,z4,z6]),(0,[z400,z1,z3,z4,z6,z34]),(0,[z0,z1,z211,z3,z10,z34])],[(0,[z961,z0,z56,z2,z3,z4]),(0,[z0,z1,z962,z2,z3,z6]),(0,[z0,z1,z3,z4,z6,z173]),(0,[z0,z1,z416,z3,z6,z10])],[(0,[z27,z0,z97,z3,z4,z6]),(0,[z963,z0,z2,z3,z4,z6]),(0,[z0,z1,z964,z3,z4,z6]),(0,[z965,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z10,z34])],[(0,[z0,z431,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z224,z34]),(0,[z0,z966,z8,z2,z3,z6])],[(0,[z904,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z371,z6]),(0,[z110,z1,z8,z2,z3,z6])],[(0,[z376,z56,z2,z3,z4,z6]),(0,[z0,z1,z967,z2,z3,z6]),(0,[z121,z1,z2,z485,z4,z6]),(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z1,z3,z4,z547,z34]),(0,[z0,z1,z2,z3,z6,z969])],[(0,[z56,z2,z3,z4,z98,z124]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z0,z971,z2,z3,z4,z6]),(0,[z0,z1,z972,z3,z4,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z0,z1,z974,z3,z4,z6]),(0,[z975,z0,z1,z3,z4,z6]),(0,[z478,z0,z3,z4,z6,z89]),(0,[z0,z976,z2,z3,z4,z6])],[(0,[z0,z977,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z712]),(0,[z0,z1,z8,z63,z3,z6]),(0,[z0,z1,z3,z4,z6,z707]),(0,[z978,z1,z2,z3,z4,z6])],[(0,[z77,z56,z8,z2,z3,z6]),(0,[z91,z56,z2,z3,z371,z6]),(0,[z979,z0,z2,z3,z4,z6]),(0,[z78,z1,z877,z3,z4,z6]),(0,[z0,z1,z980,z3,z4,z6]),(1,[z0,z1,z3,z83,z149])]],
   [[(0,[z0,z1,z2,z981,z4,z6]),(0,[z408,z0,z1,z92,z3,z6]),(0,[z82,z0,z1,z3,z83,z166])],[(0,[z27,z420,z2,z3,z4,z6]),(0,[z108,z0,z211,z3,z4,z6])],[(0,[z0,z329,z2,z3,z357,z6]),(0,[z0,z982,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z983,z6])],[],[(0,[z105,z56,z2,z3,z4,z6]),(0,[z376,z1,z2,z3,z4,z6]),(0,[z7,z188,z2,z3,z142,z6]),(0,[z0,z219,z3,z4,z6,z34]),(0,[z0,z1,z984,z3,z4,z6]),(0,[z0,z1,z2,z3,z936,z6]),(0,[z0,z1,z985,z3,z4,z6])],[(0,[z0,z1,z986,z3,z4,z6]),(0,[z0,z1,z477,z3,z10,z34]),(0,[z0,z1,z8,z128,z3,z6])],[(0,[z0,z1,z2,z3,z987,z6]),(0,[z56,z2,z3,z4,z6,z124]),(0,[z833,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z462,z10]),(0,[z1,z2,z3,z4,z6,z800]),(0,[z0,z1,z8,z711,z3,z6])],[(0,[z71,z0,z2,z3,z306,z6]),(0,[z0,z1,z2,z3,z988,z6]),(0,[z0,z18,z12,z3,z4,z19]),(0,[z246,z1,z3,z4,z6,z34])],[(0,[z0,z56,z311,z3,z4,z6]),(0,[z277,z0,z8,z2,z3,z6]),(0,[z1,z2,z3,z728,z4,z6]),(0,[z0,z324,z3,z4,z6,z34]),(0,[z24,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z6,z403,z34])],[(1,[z56,z2,z3,z258,z6]),(0,[z56,z2,z343,z3,z4,z6]),(0,[z0,z1,z3,z51,z10,z34]),(0,[z0,z1,z8,z2,z562,z3]),(0,[z11,z0,z2,z15,z4,z135]),(0,[z0,z2,z3,z4,z712,z135]),(0,[z656,z0,z1,z3,z10,z34]),(0,[z0,z1,z3,z50,z10,z34])],[(0,[z989,z105,z2,z3,z4,z6]),(0,[z105,z56,z2,z3,z265,z6]),(0,[z627,z0,z1,z3,z4,z34]),(0,[z0,z1,z2,z3,z990,z6])],[(0,[z27,z56,z3,z4,z6,z34]),(0,[z36,z0,z12,z3,z4,z6]),(0,[z0,z1,z3,z958,z6,z34]),(0,[z376,z1,z416,z3,z4,z6])],[(0,[z27,z0,z8,z2,z3,z10]),(0,[z0,z1,z22,z3,z32,z6]),(0,[z0,z1,z2,z3,z371,z243]),(0,[z433,z0,z1,z3,z6,z10]),(0,[z0,z1,z12,z40,z4,z6]),(0,[z0,z2,z3,z4,z19,z712]),(0,[z380,z0,z1,z3,z10,z34]),(0,[z0,z991,z2,z3,z4,z6])],[(0,[z559,z0,z2,z187,z4,z6]),(0,[z27,z0,z2,z3,z32,z6]),(0,[z151,z0,z1,z165,z93,z6])],[(0,[z121,z1,z12,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z707])],[(0,[z0,z1,z992,z3,z4,z6]),(0,[z27,z78,z22,z3,z4,z6]),(0,[z264,z0,z2,z28,z4,z6]),(0,[z380,z1,z22,z3,z4,z6]),(0,[z226,z1,z2,z3,z6,z10]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z18,z3,z4,z19,z62]),(0,[z45,z0,z102,z2,z4,z132])]],
   [[(0,[z56,z2,z350,z3,z4,z6]),(0,[z179,z1,z2,z3,z357,z6]),(0,[z0,z1,z311,z3,z4,z6]),(0,[z0,z2,z3,z51,z863,z6]),(0,[z791,z0,z2,z3,z6,z10])],[(0,[z1,z2,z61,z4,z124,z132]),(0,[z0,z2,z3,z863,z74,z6])],[(0,[z167,z56,z2,z3,z4,z6]),(0,[z179,z27,z2,z3,z6,z10]),(0,[z121,z0,z1,z3,z10,z34]),(0,[z0,z1,z2,z994,z4,z6]),(0,[z23,z69,z2,z3,z4,z33]),(0,[z11,z0,z2,z3,z43,z135]),(0,[z0,z1,z2,z3,z995,z6]),(0,[z996,z1,z8,z2,z3,z6])],[(0,[z588,z56,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z10,z132])],[(0,[z27,z0,z26,z3,z4,z6]),(0,[z0,z1,z2,z3,z997,z6]),(0,[z0,z1,z40,z4,z6,z34]),(0,[z0,z1,z2,z3,z570,z10])],[(0,[z960,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z124,z10,z34]),(0,[z0,z1,z2,z4,z98,z851])],[(0,[z56,z2,z354,z3,z4,z6]),(0,[z27,z262,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z998,z6]),(0,[z0,z1,z311,z3,z265,z6]),(0,[z0,z1,z3,z10,z34,z75])],[(0,[z0,z1,z2,z3,z6,z999]),(0,[z0,z1,z2,z3,z4,z1000]),(0,[z0,z1,z12,z3,z10,z34])],[(0,[z0,z1,z2,z494,z3,z10]),(0,[z0,z1001,z2,z3,z4,z6])],[(0,[z27,z0,z12,z3,z4,z34]),(0,[z0,z1,z3,z4,z153,z34]),(0,[z0,z1,z3,z54,z6,z598]),(0,[z0,z1002,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z6,z358]),(0,[z0,z1003,z2,z3,z4,z6]),(0,[z0,z1,z1004,z3,z4,z6]),(0,[z0,z188,z8,z2,z3,z6]),(0,[z0,z1,z2,z1005,z4,z6]),(0,[z0,z1,z176,z3,z67,z6]),(0,[z0,z1,z2,z907,z3,z10])],[(0,[z69,z56,z8,z2,z3,z6]),(0,[z0,z1,z3,z4,z585,z34]),(0,[z0,z169,z3,z4,z6,z34]),(0,[z609,z0,z1,z2,z4,z132]),(0,[z280,z0,z1,z3,z6,z34]),(0,[z0,z1,z3,z1006,z4,z6]),(0,[z419,z1,z12,z3,z4,z6]),(0,[z0,z1,z212,z3,z10,z34]),(0,[z30,z0,z1,z3,z4,z707])],[(0,[z0,z1,z1007,z3,z4,z6]),(0,[z1008,z0,z1,z3,z4,z6]),(0,[z0,z1,z1009,z3,z4,z6]),(0,[z419,z1,z2,z15,z4,z6]),(1,[z0,z1,z2,z6,z776])],[(0,[z0,z1,z2,z3,z1010,z6]),(0,[z0,z1,z625,z3,z4,z34]),(0,[z1011,z1,z2,z3,z4,z6]),(0,[z0,z1,z21,z3,z4,z198]),(0,[z0,z1,z3,z106,z198,z10])],[(0,[z27,z0,z3,z4,z6,z62]),(0,[z108,z0,z3,z4,z6,z89]),(0,[z0,z1,z2,z3,z586,z10]),(0,[z858,z0,z3,z4,z6,z34]),(0,[z70,z0,z1,z3,z10,z34]),(0,[z0,z1,z2,z4,z6,z851])],[(0,[z0,z1,z12,z3,z4,z626]),(0,[z0,z1,z3,z4,z6,z1012]),(0,[z47,z431,z2,z3,z4,z124]),(0,[z0,z876,z2,z3,z4,z6]),(0,[z280,z108,z0,z1,z3,z6]),(0,[z0,z1,z8,z2,z341,z3]),(0,[z0,z1,z2,z3,z4,z851])]],
   [[(0,[z24,z56,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1013])],[(0,[z340,z56,z2,z3,z4,z6]),(0,[z78,z1,z417,z3,z4,z6]),(0,[z0,z1,z3,z4,z631,z34]),(0,[z0,z1,z1014,z3,z4,z6]),(0,[z449,z0,z1,z4,z6,z75])],[(0,[z56,z374,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z6,z1015]),(0,[z105,z1,z2,z3,z1016,z6]),(0,[z0,z1,z3,z170,z6,z34]),(0,[z0,z1,z8,z212,z92,z6]),(0,[z208,z0,z1,z12,z6,z171]),(0,[z1017,z0,z1,z3,z4,z6])],[(0,[z27,z0,z2,z3,z6,z114]),(0,[z27,z0,z178,z3,z4,z6]),(0,[z0,z1,z2,z210,z6,z10]),(0,[z0,z1,z1018,z3,z4,z6]),(0,[z1019,z0,z1,z3,z4,z6]),(0,[z0,z1,z217,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1020])],[(0,[z0,z56,z2,z40,z4,z6]),(0,[z0,z1021,z2,z3,z4,z6]),(0,[z0,z1,z281,z3,z10,z34]),(0,[z376,z1,z2,z16,z4,z6]),(0,[z376,z1,z2,z3,z72,z6])],[(0,[z635,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z1022,z3,z6]),(0,[z419,z1,z2,z3,z43,z6])],[(0,[z0,z1,z2,z3,z4,z821]),(0,[z0,z194,z2,z4,z6,z132])],[(0,[z27,z0,z2,z892,z4,z6]),(0,[z0,z18,z2,z3,z4,z116]),(0,[z0,z1,z3,z4,z6,z1023]),(0,[z0,z18,z2,z3,z4,z19]),(0,[z0,z1,z128,z3,z106,z10])],[(0,[z24,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z142,z149]),(0,[z82,z686,z0,z1,z3,z6]),(0,[z0,z1,z12,z3,z111,z6])],[(0,[z27,z0,z3,z4,z6,z34]),(0,[z91,z324,z2,z3,z4,z6]),(0,[z0,z219,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z1024,z6]),(0,[z151,z408,z0,z1,z3,z6]),(0,[z0,z1,z2,z3,z6,z1025])],[(0,[z0,z1,z2,z3,z6,z1015]),(0,[z0,z461,z12,z3,z4,z6]),(0,[z420,z167,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1026,z6]),(0,[z0,z1,z2,z3,z1027,z6])],[(0,[z36,z0,z2,z3,z4,z6]),(0,[z833,z56,z2,z3,z4,z6]),(0,[z594,z56,z2,z3,z4,z6]),(0,[z0,z219,z2,z3,z331,z6]),(0,[z0,z1,z3,z10,z630,z34])],[(0,[z0,z1,z1028,z3,z4,z6]),(0,[z0,z431,z2,z210,z4,z6]),(0,[z0,z1,z1029,z2,z3,z6]),(0,[z207,z1,z2,z3,z6,z10]),(0,[z246,z1,z2,z3,z6,z10])],[(0,[z1030,z0,z56,z2,z3,z6]),(0,[z179,z152,z2,z3,z4,z6]),(0,[z0,z1031,z2,z3,z4,z6]),(0,[z0,z236,z8,z2,z3,z6]),(0,[z0,z1032,z2,z3,z4,z6])],[(0,[z27,z0,z12,z3,z6,z10]),(0,[z121,z1,z2,z14,z4,z6]),(0,[z0,z1,z395,z12,z3,z6])],[(0,[z69,z56,z2,z3,z4,z124]),(0,[z0,z56,z2,z3,z10,z34]),(0,[z489,z56,z2,z3,z4,z6]),(0,[z27,z0,z2,z378,z50,z6]),(0,[z0,z1,z231,z3,z6,z10]),(0,[z0,z1,z3,z4,z6,z1033]),(0,[z824,z1,z2,z3,z6,z10])]],
   [[(0,[z56,z2,z3,z142,z6,z10]),(0,[z443,z0,z2,z3,z103,z6]),(0,[z569,z1,z2,z3,z4,z33]),(0,[z0,z1,z2,z3,z60,z149])],[(0,[z0,z56,z21,z3,z4,z34]),(0,[z23,z0,z8,z2,z3,z6]),(0,[z1034,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1035]),(0,[z0,z2,z3,z716,z4,z6]),(0,[z0,z1,z1036,z3,z4,z6])],[(0,[z0,z1037,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1038]),(0,[z0,z1,z97,z3,z6,z10])],[(0,[z78,z56,z22,z3,z4,z6]),(0,[z27,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1039,z6]),(0,[z0,z1,z3,z135,z10,z34]),(0,[z0,z1,z3,z60,z10,z34]),(0,[z0,z1040,z2,z3,z4,z6])],[(0,[z69,z1,z3,z4,z33,z266]),(0,[z0,z1,z2,z3,z1041,z6]),(0,[z45,z0,z194,z2,z4,z132]),(0,[z0,z1,z190,z3,z6,z338])],[(0,[z0,z1,z2,z3,z10,z678]),(0,[z0,z1,z12,z3,z137,z6])],[(0,[z0,z1,z1042,z3,z4,z6]),(0,[z0,z1,z2,z3,z348,z10]),(0,[z0,z1,z8,z3,z887,z6])],[(0,[z0,z1,z1043,z3,z4,z6]),(0,[z56,z8,z2,z3,z142,z6]),(0,[z0,z1,z2,z3,z1044,z6]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z0,z1,z1046,z2,z3,z6]),(0,[z0,z169,z144,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z34])],[(0,[z91,z56,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z27,z0,z8,z3,z6,z34]),(0,[z0,z1048,z2,z3,z4,z6]),(0,[z0,z431,z231,z3,z4,z6]),(0,[z0,z1,z212,z92,z4,z6]),(0,[z0,z1,z3,z39,z10,z34]),(0,[z748,z0,z1,z12,z3,z6])],[(0,[z0,z56,z2,z3,z6,z94]),(0,[z56,z8,z406,z2,z3,z6]),(0,[z0,z1,z2,z3,z1049,z6]),(0,[z1050,z0,z1,z3,z4,z6]),(0,[z0,z1,z21,z3,z4,z34])],[(0,[z0,z991,z3,z4,z6,z34]),(0,[z843,z0,z1,z3,z6,z10])],[(0,[z419,z1,z2,z3,z4,z6]),(0,[z604,z56,z2,z3,z4,z6]),(0,[z78,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1051]),(0,[z1052,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z149]),(0,[z0,z1,z1053,z3,z4,z6])],[(0,[z0,z1,z1054,z3,z4,z6])],[(0,[z56,z2,z3,z325,z4,z6]),(0,[z1,z877,z22,z3,z4,z6])],[(0,[z0,z56,z3,z4,z6,z266]),(0,[z0,z1,z140,z3,z10,z34]),(0,[z0,z1,z3,z4,z6,z1055]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z449,z0,z1,z3,z10,z34]),(0,[z256,z0,z1,z2,z6,z456])],[(0,[z120,z121,z2,z14,z4,z6]),(0,[z0,z1,z1057,z3,z4,z6]),(0,[z481,z1,z3,z4,z6,z34]),(0,[z0,z18,z2,z3,z19,z10]),(0,[z0,z1,z2,z16,z4,z851]),(0,[z0,z1,z8,z168,z3,z6])]],
   [[(0,[z0,z56,z2,z3,z111,z6]),(0,[z0,z1,z1058,z3,z4,z6]),(0,[z0,z169,z2,z3,z6,z10]),(0,[z0,z1,z3,z6,z403,z62]),(0,[z0,z1059,z2,z3,z4,z6])],[(0,[z0,z56,z3,z4,z10,z34]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z11,z0,z26,z3,z4,z135]),(0,[z0,z1,z3,z346,z6,z34])],[(0,[z56,z12,z417,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1061]),(0,[z167,z0,z2,z3,z32,z6]),(0,[z0,z1,z2,z3,z4,z1062]),(0,[z829,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z626,z10]),(0,[z91,z236,z2,z61,z4,z6]),(0,[z1063,z0,z1,z2,z3,z6])],[(0,[z0,z329,z12,z3,z4,z6]),(0,[z30,z0,z1,z3,z10,z34]),(0,[z0,z1,z3,z4,z1064,z6])],[(0,[z27,z0,z144,z3,z4,z6]),(0,[z1065,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z266]),(0,[z0,z1,z12,z3,z4,z216]),(0,[z91,z0,z1,z3,z10,z34]),(0,[z0,z1,z1066,z3,z4,z6]),(0,[z0,z1,z8,z178,z3,z6]),(0,[z864,z0,z2,z3,z6,z10])],[(0,[z27,z0,z2,z3,z4,z348]),(0,[z47,z27,z2,z3,z4,z124]),(0,[z0,z1,z2,z3,z371,z348])],[(0,[z197,z0,z58,z3,z6,z10]),(0,[z0,z1,z2,z3,z111,z6]),(0,[z1067,z1,z2,z3,z4,z6])],[(0,[z27,z0,z128,z3,z4,z6]),(0,[z0,z1,z20,z3,z6,z64])],[(0,[z0,z461,z2,z3,z4,z6]),(0,[z91,z1,z61,z4,z6,z34]),(0,[z0,z1,z191,z3,z10,z34]),(0,[z0,z1,z8,z3,z6,z173])],[(0,[z609,z56,z2,z3,z4,z6]),(0,[z91,z1,z248,z61,z4,z6]),(0,[z69,z1,z12,z3,z4,z33]),(0,[z1068,z0,z1,z2,z3,z6]),(0,[z1069,z0,z1,z2,z3,z6]),(0,[z1070,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z223]),(0,[z1071,z0,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z124,z132]),(0,[z0,z1072,z2,z3,z4,z6]),(0,[z27,z0,z947,z3,z4,z6])],[(0,[z0,z56,z2,z3,z137,z6]),(0,[z109,z0,z3,z74,z6,z34]),(0,[z0,z1,z26,z3,z6,z10]),(0,[z0,z1,z3,z832,z83,z6]),(0,[z0,z1,z553,z3,z10,z34])],[(0,[z27,z0,z2,z3,z6,z10]),(0,[z208,z182,z0,z1,z3,z6])],[(0,[z31,z56,z8,z2,z3,z6]),(0,[z0,z1,z2,z336,z4,z124])]],
   [[(0,[z27,z0,z2,z3,z331,z6]),(0,[z0,z1,z882,z3,z4,z348]),(0,[z0,z1,z1073,z3,z4,z6]),(0,[z11,z0,z178,z3,z4,z135]),(0,[z929,z0,z3,z4,z6,z34]),(0,[z380,z1,z3,z4,z6,z181]),(0,[z0,z1,z281,z434,z3,z6]),(0,[z0,z1,z8,z147,z3,z6])],[(0,[z56,z2,z14,z16,z4,z6]),(0,[z91,z1,z2,z61,z258,z6]),(0,[z0,z1,z1058,z3,z4,z243]),(0,[z0,z1,z1074,z3,z4,z6]),(0,[z42,z0,z12,z3,z4,z6]),(0,[z0,z185,z12,z3,z4,z6]),(0,[z1075,z1,z2,z3,z4,z6]),(0,[z0,z1,z176,z3,z10,z34]),(0,[z0,z1,z3,z10,z513,z34])],[(0,[z108,z0,z257,z3,z4,z6]),(0,[z0,z1076,z2,z3,z4,z6]),(0,[z108,z0,z3,z4,z566,z6]),(0,[z1077,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z378,z6,z776])],[(0,[z7,z56,z2,z3,z142,z6]),(0,[z0,z56,z2,z3,z4,z149]),(0,[z488,z0,z2,z163,z4,z6]),(0,[z1078,z0,z2,z3,z4,z6])],[(0,[z0,z1079,z2,z3,z4,z6]),(0,[z151,z0,z1,z239,z4,z6]),(0,[z0,z1,z2,z3,z6,z1080]),(0,[z0,z1,z8,z12,z3,z34])],[(0,[z0,z236,z248,z3,z4,z6]),(0,[z105,z1,z2,z3,z265,z6]),(0,[z0,z1,z8,z3,z6,z266]),(1,[z0,z2,z3,z863,z6]),(0,[z0,z1,z3,z19,z10,z34])],[(0,[z0,z1,z1081,z3,z4,z6]),(0,[z0,z431,z2,z3,z170,z6]),(0,[z0,z1,z20,z3,z60,z6]),(0,[z1082,z1,z2,z3,z4,z6])],[(0,[z193,z56,z2,z3,z4,z124]),(0,[z0,z1083,z2,z3,z4,z6]),(0,[z0,z1,z1084,z3,z4,z6])],[(0,[z27,z0,z2,z3,z371,z6]),(0,[z27,z0,z2,z3,z4,z166]),(0,[z0,z1,z1085,z2,z3,z6]),(0,[z0,z1,z1086,z3,z4,z6]),(0,[z1,z2,z3,z265,z1016,z6]),(0,[z0,z1,z2,z3,z6,z1087]),(0,[z0,z1,z2,z16,z98,z94])],[(0,[z0,z1,z1088,z3,z4,z6]),(0,[z105,z1,z2,z3,z6,z39]),(0,[z0,z1,z3,z4,z113,z34]),(0,[z0,z1,z2,z40,z43,z6]),(0,[z0,z1,z3,z10,z89,z34]),(0,[z0,z194,z289,z3,z4,z6])],[(0,[z91,z56,z2,z14,z4,z6]),(0,[z0,z1,z1089,z3,z4,z6]),(0,[z69,z1,z2,z3,z4,z250]),(0,[z0,z1,z2,z3,z6,z1090]),(0,[z779,z0,z2,z3,z4,z6])],[(0,[z0,z236,z2,z3,z258,z6]),(0,[z120,z0,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z149])],[(0,[z56,z12,z22,z3,z4,z6]),(0,[z0,z1,z1091,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1092]),(0,[z0,z1,z178,z3,z6,z10])],[(0,[z0,z1,z2,z1093,z4,z6]),(0,[z0,z1,z1094,z2,z3,z6]),(0,[z0,z1,z2,z412,z4,z98]),(0,[z0,z1,z2,z591,z50,z6])],[(0,[z167,z0,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z6,z1095]),(0,[z82,z438,z0,z1,z3,z6])],[(0,[z0,z169,z311,z3,z4,z6]),(0,[z400,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z526,z10])]],
   [[(0,[z0,z1,z1096,z3,z4,z6]),(0,[z0,z1,z1097,z3,z4,z6]),(0,[z0,z1,z3,z1098,z4,z6]),(0,[z11,z419,z2,z3,z4,z135]),(0,[z82,z0,z1,z3,z83,z149])],[(0,[z0,z1,z2,z3,z265,z149]),(0,[z0,z1,z2,z3,z1099,z6])],[(0,[z275,z56,z2,z3,z4,z6]),(0,[z0,z1,z140,z3,z4,z149]),(0,[z69,z1,z395,z2,z3,z33])],[(1,[z56,z2,z3,z357,z6]),(0,[z69,z56,z2,z3,z4,z33]),(0,[z56,z2,z3,z457,z4,z6]),(0,[z0,z1,z248,z3,z258,z6]),(0,[z109,z0,z1,z2,z3,z149]),(0,[z419,z1,z178,z3,z4,z6])],[(0,[z0,z329,z2,z3,z4,z6]),(0,[z961,z0,z1,z2,z3,z4]),(0,[z27,z376,z2,z3,z4,z6]),(0,[z1100,z1,z2,z3,z4,z6]),(0,[z481,z1,z2,z3,z6,z10]),(0,[z0,z1,z3,z122,z10,z34]),(0,[z0,z1,z12,z3,z6,z94]),(0,[z45,z376,z1,z2,z4,z132]),(0,[z0,z1,z391,z2,z591,z6])],[(0,[z899,z0,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z1101,z6]),(0,[z0,z1,z1102,z3,z4,z6])],[(0,[z0,z1,z1103,z2,z3,z6]),(0,[z0,z1,z3,z4,z1104,z6])],[(0,[z1,z2,z3,z4,z1016,z6]),(0,[z207,z1,z2,z40,z4,z6]),(0,[z0,z1,z1105,z2,z3,z6]),(0,[z1106,z0,z2,z3,z4,z6]),(0,[z45,z0,z1,z289,z4,z132]),(0,[z286,z1,z297,z2,z3,z6])],[(0,[z56,z2,z3,z142,z6,z171]),(0,[z0,z1,z2,z1107,z4,z6]),(0,[z1108,z1,z2,z3,z4,z6]),(0,[z0,z1,z1109,z2,z3,z6]),(0,[z55,z0,z1,z2,z326,z6])],[(0,[z0,z56,z8,z2,z3,z6]),(0,[z419,z1,z3,z4,z6,z34])],[(0,[z0,z1,z2,z1110,z4,z6]),(0,[z0,z1,z2,z378,z6,z388])],[(0,[z27,z0,z3,z4,z895,z6]),(0,[z0,z431,z3,z4,z6,z34]),(0,[z0,z1,z8,z1111,z3,z6])],[(1,[z56,z119,z3,z4,z6])],[(0,[z899,z77,z2,z3,z4,z6]),(0,[z27,z0,z311,z3,z4,z6]),(0,[z1112,z0,z2,z3,z4,z6]),(0,[z1113,z1,z2,z3,z4,z6]),(0,[z264,z24,z2,z3,z4,z6]),(0,[z82,z0,z1,z494,z3,z6]),(0,[z1114,z1,z2,z3,z4,z6])],[(0,[z0,z1115,z2,z3,z4,z6]),(0,[z0,z1116,z2,z3,z4,z6]),(0,[z0,z1,z1117,z3,z4,z6]),(0,[z0,z1,z2,z1118,z4,z6])],[(0,[z0,z1,z2,z40,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z898]),(0,[z0,z324,z2,z3,z6,z10]),(0,[z1119,z1,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z300,z6])],[(0,[z177,z56,z2,z3,z4,z6]),(0,[z42,z0,z2,z3,z4,z6]),(0,[z0,z185,z2,z3,z4,z6]),(0,[z91,z1,z119,z61,z4,z6]),(0,[z264,z0,z163,z4,z6,z34])],[(0,[z0,z56,z3,z4,z198,z6]),(0,[z1120,z0,z2,z3,z4,z6])],[(0,[z27,z56,z2,z3,z6,z10]),(0,[z0,z1,z1121,z3,z4,z6]),(0,[z0,z1,z3,z60,z6,z360]),(0,[z0,z1,z1122,z3,z6,z34])],[(0,[z56,z2,z14,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1123]),(0,[z0,z1,z3,z54,z83,z6])],[(0,[z56,z22,z3,z93,z4,z6]),(0,[z105,z56,z3,z4,z6,z34]),(0,[z673,z56,z2,z3,z4,z6]),(0,[z0,z1,z176,z3,z4,z149]),(0,[z0,z1,z2,z378,z3,z149]),(0,[z376,z1,z3,z4,z6,z34]),(0,[z208,z0,z1,z2,z326,z6])],[(0,[z0,z329,z2,z3,z32,z6]),(0,[z0,z1,z2,z3,z1124,z6]),(0,[z0,z1,z434,z3,z60,z6]),(0,[z0,z1,z3,z6,z10,z1125])],[(0,[z425,z400,z2,z3,z4,z6])],[(0,[z0,z461,z3,z4,z6,z34]),(0,[z0,z48,z1,z3,z10,z34])],[(0,[z0,z1,z395,z3,z6,z34]),(0,[z109,z0,z2,z3,z863,z6]),(0,[z109,z0,z12,z3,z74,z6]),(0,[z0,z1,z2,z15,z137,z6]),(0,[z0,z1,z3,z1126,z6,z34])],[(0,[z0,z1,z2,z3,z1127,z6]),(0,[z0,z1,z1128,z3,z4,z6]),(0,[z0,z1,z1129,z2,z3,z6]),(0,[z151,z0,z1,z93,z6,z10]),(0,[z0,z1,z3,z4,z198,z6])],[(0,[z78,z0,z1,z3,z10,z34]),(0,[z0,z236,z119,z3,z4,z6]),(0,[z24,z2,z3,z4,z6,z135]),(0,[z0,z1,z2,z3,z1130,z6])],[(1,[z1,z2,z61,z4,z348]),(0,[z0,z1131,z2,z3,z4,z6])],[],[(0,[z56,z2,z485,z3,z4,z6]),(0,[z56,z2,z410,z3,z4,z6]),(0,[z27,z0,z44,z2,z3,z6]),(0,[z0,z1,z2,z3,z65,z10]),(0,[z0,z1,z2,z16,z4,z691]),(0,[z7,z1,z12,z3,z142,z6]),(0,[z0,z1,z144,z3,z6,z10]),(0,[z408,z0,z1,z12,z3,z6]),(0,[z0,z194,z416,z3,z4,z6])],[(0,[z56,z2,z486,z3,z4,z6]),(0,[z0,z1,z1132,z3,z4,z6]),(0,[z420,z1,z8,z2,z3,z6]),(0,[z0,z1,z2,z1133,z3,z6]),(0,[z0,z1,z3,z4,z6,z1134])]],
   [[(0,[z27,z0,z217,z2,z3,z6]),(0,[z0,z1,z217,z2,z3,z166])],[(0,[z286,z56,z8,z2,z3,z6]),(0,[z27,z0,z1,z3,z10,z34]),(0,[z0,z1,z1135,z2,z3,z6]),(0,[z134,z0,z1,z3,z10,z34]),(0,[z0,z1136,z2,z3,z4,z6])],[(0,[z56,z3,z4,z142,z6,z34]),(0,[z1137,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z110,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z388,z10,z34]),(0,[z0,z1,z128,z3,z6,z10])],[(0,[z226,z27,z2,z3,z4,z6]),(0,[z167,z0,z2,z3,z6,z10]),(0,[z0,z1,z2,z336,z4,z33]),(0,[z0,z1,z8,z454,z3,z6]),(0,[z0,z1,z2,z3,z699,z10]),(0,[z186,z0,z1,z3,z10,z34])],[(0,[z496,z0,z1,z2,z4,z132]),(0,[z0,z1,z2,z1139,z4,z6]),(0,[z1140,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z94])],[(0,[z56,z2,z3,z4,z258,z6]),(0,[z1141,z0,z2,z3,z4,z6]),(0,[z607,z56,z2,z3,z4,z6]),(0,[z698,z56,z2,z3,z4,z6]),(0,[z0,z56,z3,z4,z232,z6]),(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z3,z137,z6,z34]),(0,[z0,z1,z3,z60,z6,z390]),(0,[z0,z1,z2,z3,z1101,z6])],[(0,[z77,z56,z12,z3,z4,z6]),(0,[z296,z0,z211,z3,z4,z6]),(0,[z1143,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z547])],[(0,[z569,z56,z2,z3,z4,z6]),(0,[z0,z1144,z2,z3,z4,z6]),(0,[z431,z2,z3,z4,z6,z124]),(0,[z47,z1,z3,z4,z124,z34]),(0,[z421,z0,z1,z3,z6,z598])],[(0,[z280,z0,z56,z2,z3,z6]),(0,[z1145,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1146])],[(0,[z56,z406,z2,z3,z4,z6]),(0,[z0,z1,z119,z3,z258,z6]),(0,[z280,z197,z0,z1,z3,z6]),(0,[z0,z1,z12,z3,z165,z6]),(0,[z0,z1,z3,z10,z34,z181]),(0,[z0,z1,z3,z10,z34,z171]),(0,[z0,z1,z1111,z3,z4,z6])],[(0,[z899,z56,z2,z3,z4,z6]),(0,[z0,z1,z1147,z3,z4,z6]),(0,[z0,z1,z3,z331,z6,z34]),(0,[z45,z0,z1,z416,z4,z132]),(0,[z0,z2,z3,z6,z10,z1148]),(0,[z0,z1,z1149,z3,z4,z6])],[(0,[z56,z2,z3,z50,z142,z6]),(0,[z0,z56,z1150,z2,z3,z6]),(0,[z445,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z1151,z4,z6]),(0,[z1152,z1,z2,z3,z4,z6]),(0,[z1153,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1154,z6]),(0,[z0,z1,z1155,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1156]),(0,[z11,z0,z3,z4,z135,z34]),(0,[z0,z1,z3,z83,z6,z149]),(0,[z45,z0,z1,z3,z10,z34]),(0,[z0,z1,z3,z4,z10,z34])],[(0,[z179,z42,z2,z3,z4,z6]),(0,[z0,z1,z1157,z3,z4,z6]),(0,[z0,z1,z3,z232,z6,z10]),(0,[z0,z2,z3,z1158,z4,z6]),(0,[z0,z2,z3,z6,z10,z1159])],[(0,[z0,z194,z2,z3,z46,z6]),(0,[z1160,z0,z1,z8,z3,z6])],[(0,[z277,z0,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z1161,z6]),(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z1,z2,z3,z4,z1163]),(0,[z0,z1,z2,z3,z642,z10]),(0,[z0,z1,z2,z16,z4,z98])]],
   [[(0,[z56,z2,z3,z6,z10,z513]),(0,[z1,z56,z2,z3,z258,z6]),(0,[z207,z1,z2,z3,z137,z6]),(0,[z0,z1,z190,z12,z3,z6])],[(0,[z0,z1,z1164,z3,z4,z6]),(0,[z0,z1,z2,z1165,z4,z6]),(0,[z0,z1,z2,z3,z6,z1166]),(0,[z0,z1,z3,z4,z1167,z6]),(1,[z0,z1,z3,z832,z6]),(0,[z0,z1,z2,z6,z776,z171])],[(0,[z899,z1,z2,z3,z4,z6]),(0,[z179,z27,z8,z2,z3,z6]),(0,[z27,z207,z2,z3,z4,z6]),(0,[z0,z329,z3,z4,z6,z34]),(0,[z0,z431,z2,z3,z331,z6]),(0,[z0,z1,z876,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z776]),(0,[z0,z1,z1168,z3,z4,z6])],[(0,[z56,z2,z119,z3,z4,z6]),(0,[z56,z2,z3,z6,z124,z10]),(0,[z1169,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z4,z863,z6])],[(0,[z69,z1,z2,z336,z4,z6]),(0,[z69,z1,z454,z3,z4,z33]),(0,[z0,z1,z8,z2,z40,z6]),(0,[z978,z1,z2,z3,z6,z10])],[(0,[z27,z0,z956,z2,z3,z6]),(0,[z27,z0,z212,z92,z4,z6]),(1,[z0,z1,z3,z198,z10]),(0,[z0,z1,z2,z907,z3,z106])],[(0,[z312,z56,z2,z3,z4,z6]),(0,[z42,z56,z2,z3,z4,z6]),(0,[z0,z1170,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1171,z6]),(0,[z0,z1,z2,z3,z1172,z6]),(0,[z47,z1,z8,z2,z3,z124])],[(0,[z0,z56,z2,z3,z258,z6]),(0,[z208,z0,z56,z2,z6,z171]),(0,[z0,z1,z1173,z3,z4,z6]),(0,[z0,z1,z12,z3,z6,z254]),(0,[z0,z1,z2,z1174,z4,z6]),(0,[z108,z0,z211,z3,z6,z10]),(0,[z419,z1,z26,z3,z4,z6]),(0,[z0,z1,z178,z40,z4,z6]),(0,[z184,z0,z1,z3,z10,z34]),(0,[z0,z194,z2,z16,z4,z6]),(0,[z0,z194,z2,z3,z72,z6])],[(0,[z27,z0,z3,z4,z6,z173]),(0,[z109,z433,z0,z3,z74,z6]),(0,[z0,z1,z2,z3,z137,z6]),(0,[z0,z1,z190,z3,z6,z34]),(0,[z0,z982,z2,z3,z6,z10]),(0,[z200,z0,z123,z2,z3,z6])],[(0,[z0,z56,z1175,z3,z4,z6]),(0,[z1030,z0,z1,z2,z3,z6]),(0,[z0,z1,z1176,z3,z4,z6]),(0,[z24,z1,z3,z4,z6,z34])],[(0,[z0,z56,z2,z1177,z3,z6]),(0,[z110,z56,z2,z3,z4,z6]),(0,[z162,z207,z2,z3,z4,z6]),(0,[z0,z194,z12,z3,z4,z6]),(0,[z376,z1,z2,z3,z6,z10])],[(0,[z296,z0,z268,z3,z4,z6]),(0,[z0,z1,z8,z3,z10,z34])],[(0,[z56,z2,z130,z3,z4,z6]),(0,[z0,z56,z2,z1178,z4,z6]),(0,[z138,z27,z2,z3,z4,z6]),(0,[z0,z1,z1179,z2,z3,z6]),(0,[z36,z0,z3,z4,z6,z34]),(0,[z197,z400,z58,z3,z4,z6])],[(0,[z0,z1,z1180,z2,z3,z6]),(0,[z56,z2,z3,z4,z6,z530]),(0,[z0,z1,z1181,z2,z3,z6]),(0,[z0,z1,z1155,z2,z3,z243]),(0,[z0,z1,z1182,z3,z4,z6]),(0,[z0,z1,z3,z10,z10,z34])],[(0,[z0,z1,z2,z3,z1183,z6]),(0,[z7,z1,z2,z3,z142,z6]),(0,[z0,z1,z8,z2,z3,z585]),(1,[z0,z1,z3,z346,z34]),(0,[z0,z1,z3,z4,z6,z1184]),(0,[z0,z1,z3,z6,z10,z338])],[(0,[z27,z0,z3,z4,z6,z1061]),(0,[z1185,z0,z2,z3,z4,z6]),(0,[z42,z0,z3,z4,z6,z34]),(0,[z0,z102,z8,z2,z3,z6]),(0,[z186,z0,z2,z3,z6,z85])]],
   [[(1,[z1,z2,z3,z1016,z6]),(0,[z7,z1,z406,z2,z3,z6]),(0,[z1186,z1,z2,z3,z4,z6])],[(0,[z386,z56,z22,z3,z4,z6]),(0,[z0,z56,z2,z3,z165,z6]),(0,[z0,z1,z1175,z3,z4,z6]),(0,[z0,z188,z12,z3,z4,z6]),(0,[z1187,z1,z2,z3,z4,z6]),(0,[z1188,z0,z1,z3,z4,z6]),(0,[z0,z966,z2,z3,z4,z6])],[(0,[z110,z1,z2,z3,z4,z6]),(0,[z69,z56,z12,z3,z4,z6]),(0,[z0,z56,z168,z3,z4,z6]),(0,[z0,z1,z2,z1177,z3,z6]),(0,[z27,z400,z2,z3,z4,z6]),(0,[z0,z1189,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z348]),(0,[z0,z1,z3,z60,z508,z6])],[(0,[z27,z0,z3,z4,z6,z266]),(0,[z1190,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1178,z4,z6]),(0,[z7,z1,z2,z3,z1016,z6]),(0,[z105,z169,z2,z3,z265,z6])],[(0,[z27,z0,z2,z3,z111,z6]),(1,[z1,z2,z728,z4,z6]),(0,[z0,z1,z1191,z2,z3,z6])],[(0,[z77,z56,z2,z3,z4,z6]),(0,[z0,z1,z311,z3,z6,z10]),(0,[z0,z1,z3,z4,z643,z34])],[(0,[z1,z56,z2,z3,z357,z6]),(0,[z0,z1,z1192,z3,z4,z6]),(0,[z27,z110,z2,z3,z4,z6]),(0,[z0,z1,z1193,z2,z3,z6]),(0,[z0,z1,z3,z4,z133,z34]),(0,[z0,z1,z1194,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1195,z6]),(0,[z0,z1,z3,z4,z1196,z6])],[(0,[z0,z1197,z2,z3,z4,z6]),(0,[z386,z1,z22,z3,z4,z6]),(0,[z420,z197,z58,z3,z4,z6]),(0,[z0,z1,z2,z3,z165,z6])],[(0,[z91,z1,z12,z61,z4,z6]),(0,[z0,z1,z1198,z3,z4,z6]),(0,[z0,z1,z168,z3,z4,z6]),(0,[z353,z0,z1,z536,z3,z6])],[],[(0,[z56,z2,z460,z3,z4,z6]),(0,[z47,z1,z2,z3,z124,z10]),(0,[z1199,z1,z2,z3,z4,z6]),(0,[z207,z1,z8,z2,z3,z6]),(0,[z0,z1,z12,z3,z4,z345]),(0,[z0,z1,z8,z21,z3,z34]),(0,[z0,z710,z2,z3,z4,z6])],[(0,[z121,z324,z2,z14,z4,z6]),(0,[z0,z1,z1200,z3,z4,z6])],[(0,[z69,z1,z2,z3,z4,z377]),(0,[z69,z1,z2,z3,z4,z33])],[(0,[z277,z0,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z6,z254]),(0,[z0,z56,z2,z3,z1201,z6]),(0,[z47,z0,z1,z3,z10,z34]),(0,[z1202,z0,z1,z3,z4,z6]),(0,[z1203,z0,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z519])]],
   [[(0,[z1,z56,z119,z3,z4,z6]),(0,[z0,z1204,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1205]),(0,[z0,z1,z2,z3,z73,z10]),(0,[z1206,z0,z2,z3,z4,z6]),(0,[z452,z0,z238,z3,z4,z6])],[(0,[z105,z1,z3,z265,z6,z34]),(0,[z400,z2,z58,z3,z4,z6]),(0,[z0,z1207,z2,z3,z4,z6]),(0,[z0,z1208,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z551,z6]),(0,[z0,z1209,z2,z3,z4,z6]),(0,[z0,z152,z8,z2,z3,z6]),(0,[z0,z1,z1210,z3,z4,z6]),(0,[z0,z1,z3,z4,z663,z34])],[(0,[z0,z1,z1211,z3,z4,z6])],[(0,[z0,z1,z8,z2,z3,z6]),(0,[z56,z2,z3,z4,z467,z6]),(0,[z0,z56,z3,z4,z6,z1212]),(0,[z0,z1,z2,z3,z4,z1213]),(0,[z0,z236,z12,z3,z4,z6]),(0,[z188,z2,z3,z4,z142,z6]),(0,[z0,z1,z12,z3,z4,z462]),(0,[z0,z1,z2,z1214,z4,z6]),(0,[z0,z1,z787,z93,z4,z6]),(0,[z0,z3,z4,z6,z34,z1215]),(0,[z0,z1,z16,z4,z98,z338])],[(0,[z182,z0,z56,z3,z4,z6]),(0,[z0,z1,z1216,z3,z4,z6]),(0,[z0,z1,z1217,z2,z3,z6]),(0,[z197,z0,z222,z58,z3,z6]),(0,[z0,z2,z163,z4,z6,z663])],[(0,[z0,z1,z2,z50,z6,z776]),(0,[z1218,z246,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1201,z6])],[(0,[z91,z56,z8,z2,z3,z6]),(0,[z27,z0,z2,z3,z4,z149]),(0,[z0,z1,z3,z4,z6,z1219]),(0,[z23,z0,z12,z3,z4,z6])],[(0,[z105,z56,z311,z3,z4,z6]),(0,[z996,z1,z2,z3,z4,z6]),(0,[z109,z433,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z166,z34]),(0,[z208,z0,z1,z3,z10,z34])],[(0,[z0,z1,z12,z222,z3,z6]),(0,[z0,z194,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1220]),(0,[z0,z1,z3,z4,z6,z1125])],[(0,[z0,z1,z1221,z3,z4,z6])],[(0,[z689,z56,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1212]),(0,[z179,z1,z144,z3,z4,z6]),(0,[z27,z195,z2,z3,z4,z6]),(0,[z1222,z1,z2,z3,z4,z6]),(0,[z353,z0,z1,z3,z83,z6]),(0,[z0,z1,z12,z3,z4,z360])],[(0,[z578,z56,z2,z3,z4,z6]),(0,[z134,z0,z2,z3,z306,z6]),(0,[z1223,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z1039,z6,z34])],[(0,[z179,z1,z2,z3,z4,z348]),(0,[z0,z1,z3,z4,z1224,z6]),(0,[z264,z0,z12,z163,z4,z6]),(0,[z24,z1,z2,z3,z6,z10]),(0,[z45,z0,z1,z8,z2,z132])],[(0,[z0,z1,z2,z3,z1225,z6]),(0,[z11,z207,z2,z3,z4,z135]),(0,[z1226,z1,z12,z3,z4,z6]),(0,[z0,z1,z190,z2,z16,z98])]],
   [[(0,[z0,z1,z3,z265,z10,z34]),(0,[z1227,z1,z2,z3,z4,z6]),(0,[z0,z1,z178,z3,z137,z6]),(0,[z0,z1228,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z122,z114])],[(0,[z197,z0,z1,z3,z10,z34]),(0,[z0,z1,z2,z3,z113,z10]),(0,[z0,z1,z3,z6,z94,z338]),(0,[z1229,z0,z2,z3,z4,z6])],[(0,[z69,z56,z2,z3,z4,z6]),(0,[z91,z56,z2,z61,z4,z6]),(0,[z0,z1,z12,z3,z258,z6]),(0,[z0,z1,z12,z336,z4,z6]),(0,[z208,z182,z0,z1,z6,z171])],[(0,[z461,z2,z22,z3,z4,z6]),(0,[z109,z481,z2,z3,z74,z6])],[(0,[z507,z56,z2,z3,z4,z6]),(0,[z989,z0,z2,z3,z4,z6]),(0,[z121,z1,z2,z14,z6,z10]),(0,[z47,z1,z2,z336,z4,z124])],[(0,[z528,z0,z2,z28,z4,z6]),(0,[z0,z1,z8,z2,z3,z243]),(0,[z0,z1,z97,z3,z6,z94])],[(0,[z1230,z0,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1231]),(0,[z0,z1,z1232,z3,z4,z6]),(0,[z1082,z1,z3,z4,z6,z34])],[(0,[z56,z2,z3,z4,z6,z589]),(0,[z0,z56,z63,z3,z4,z6]),(0,[z91,z152,z2,z61,z4,z6]),(0,[z0,z1,z176,z3,z6,z519]),(0,[z0,z1,z2,z3,z10,z229])],[(0,[z1233,z0,z56,z3,z4,z6]),(0,[z0,z1,z3,z4,z172,z34]),(0,[z408,z0,z1,z3,z6,z34])],[(0,[z0,z1,z2,z3,z4,z1234]),(0,[z95,z0,z234,z3,z4,z6]),(0,[z1235,z27,z0,z2,z3,z6]),(0,[z91,z1,z2,z61,z4,z6]),(0,[z0,z1236,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z142,z6]),(0,[z179,z0,z1,z3,z10,z34]),(0,[z0,z1,z2,z3,z6,z1237]),(0,[z0,z1,z26,z40,z4,z6])],[(0,[z27,z0,z2,z40,z4,z6]),(0,[z0,z1,z8,z3,z198,z6])],[(0,[z0,z1,z2,z1238,z4,z6]),(0,[z0,z1,z63,z3,z6,z403]),(0,[z0,z1,z3,z83,z10,z34]),(0,[z0,z1,z12,z3,z4,z586])],[(0,[z0,z1,z2,z3,z6,z1239]),(0,[z0,z1,z212,z92,z6,z10]),(0,[z0,z1,z8,z12,z3,z10]),(0,[z0,z1,z289,z3,z46,z6])],[]],
   [[(0,[z0,z1,z63,z3,z4,z6]),(0,[z0,z1,z3,z4,z232,z6]),(0,[z0,z1189,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z301,z34]),(0,[z0,z1,z2,z3,z288,z10]),(0,[z0,z1,z97,z16,z4,z98])],[(0,[z78,z1,z22,z3,z6,z10]),(0,[z419,z1,z2,z3,z6,z10]),(0,[z82,z0,z1,z255,z3,z6])],[(0,[z0,z56,z2,z222,z3,z6]),(0,[z0,z1,z766,z3,z4,z6]),(0,[z226,z1,z8,z2,z3,z6]),(0,[z0,z1240,z2,z3,z4,z6]),(0,[z0,z1,z2,z191,z6,z388])],[(0,[z674,z56,z2,z3,z4,z6]),(0,[z0,z431,z2,z3,z6,z10]),(0,[z0,z1,z2,z1122,z3,z6]),(0,[z1241,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z534,z10]),(0,[z0,z1,z378,z50,z6,z34]),(0,[z0,z3,z4,z6,z34,z1148])],[(0,[z77,z56,z3,z4,z6,z34]),(0,[z518,z56,z2,z3,z4,z6]),(0,[z0,z56,z248,z3,z4,z6]),(0,[z56,z2,z3,z4,z6,z513]),(0,[z105,z56,z144,z3,z4,z6]),(0,[z0,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1242]),(0,[z0,z1,z902,z2,z3,z6]),(0,[z1243,z1,z2,z3,z4,z6]),(0,[z182,z0,z1,z8,z3,z6]),(0,[z0,z1,z3,z6,z10,z1244])],[],[(0,[z31,z56,z12,z3,z4,z6]),(0,[z0,z1,z1150,z2,z3,z6]),(0,[z0,z1,z22,z3,z10,z34]),(0,[z0,z1,z2,z1245,z4,z6]),(0,[z134,z0,z2,z3,z6,z235]),(0,[z30,z0,z1,z3,z111,z34])],[(0,[z56,z2,z517,z3,z4,z6]),(0,[z31,z56,z2,z3,z357,z6]),(0,[z56,z12,z3,z4,z6,z124]),(0,[z27,z0,z2,z3,z10,z34]),(0,[z27,z0,z3,z4,z198,z6]),(0,[z256,z0,z1,z3,z10,z34]),(0,[z0,z1,z21,z3,z10,z34]),(0,[z45,z0,z1,z12,z4,z132]),(0,[z0,z1,z289,z3,z72,z6]),(0,[z0,z1246,z2,z3,z4,z6])],[(0,[z23,z0,z2,z3,z4,z6]),(0,[z56,z212,z22,z3,z4,z6]),(0,[z0,z1247,z2,z3,z4,z6]),(0,[z208,z27,z0,z2,z6,z171])],[(0,[z27,z0,z21,z3,z4,z34]),(0,[z0,z1,z12,z3,z357,z6]),(0,[z0,z1,z1248,z2,z3,z6]),(0,[z0,z1,z3,z198,z6,z10])],[(0,[z464,z56,z2,z3,z4,z6]),(0,[z0,z56,z2,z336,z4,z6]),(0,[z620,z0,z2,z3,z283,z6]),(0,[z0,z56,z3,z4,z6,z338]),(0,[z0,z152,z248,z3,z4,z6]),(0,[z0,z1,z2,z222,z3,z6]),(0,[z1249,z0,z1,z2,z3,z6]),(0,[z0,z1,z509,z2,z3,z10])],[(0,[z91,z1,z2,z61,z4,z243]),(0,[z1250,z1,z2,z3,z4,z6]),(0,[z0,z1,z1251,z3,z4,z6]),(0,[z1160,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1252,z6]),(0,[z0,z1,z248,z3,z4,z6]),(0,[z0,z1,z112,z336,z4,z6]),(0,[z109,z0,z2,z3,z74,z6]),(0,[z0,z1,z168,z3,z4,z122])],[(0,[z105,z56,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z1253,z6]),(0,[z481,z1,z176,z2,z3,z6]),(0,[z151,z0,z1,z787,z4,z6])],[(0,[z47,z1,z2,z3,z4,z821]),(0,[z0,z1,z2,z3,z166,z10]),(0,[z0,z1,z3,z54,z10,z34]),(0,[z1254,z1,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z357,z6]),(0,[z400,z1,z8,z2,z3,z6]),(0,[z1226,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z3,z232,z6]),(0,[z709,z0,z12,z3,z4,z6])]],
   [[(0,[z91,z56,z248,z3,z4,z6]),(0,[z0,z461,z2,z3,z6,z10]),(0,[z0,z152,z2,z3,z258,z6]),(0,[z0,z1,z454,z3,z6,z254]),(0,[z0,z1,z3,z4,z6,z1255]),(0,[z0,z1,z1256,z3,z4,z6])],[(0,[z322,z56,z2,z3,z4,z6]),(0,[z27,z0,z2,z3,z6,z94]),(0,[z1,z2,z3,z336,z4,z124]),(0,[z0,z1,z8,z97,z3,z6])],[(0,[z604,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z2,z336,z4,z6]),(0,[z120,z0,z12,z3,z4,z6]),(0,[z105,z1,z144,z3,z265,z6]),(0,[z0,z185,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z1257,z6]),(0,[z421,z0,z1,z3,z83,z6]),(0,[z581,z0,z1,z3,z10,z34]),(0,[z0,z1,z1258,z3,z4,z6])],[(0,[z0,z56,z2,z3,z346,z6])],[(0,[z0,z1,z1259,z3,z4,z6]),(0,[z0,z1,z3,z4,z149,z34])],[(0,[z56,z3,z4,z6,z124,z34]),(0,[z1260,z0,z2,z3,z4,z6]),(0,[z0,z236,z2,z3,z4,z243]),(0,[z0,z1,z1261,z3,z4,z6]),(0,[z197,z0,z1,z3,z4,z149]),(0,[z0,z1262,z2,z3,z4,z6]),(0,[z0,z102,z289,z3,z4,z6])],[(0,[z91,z56,z2,z3,z258,z6]),(0,[z56,z176,z2,z3,z142,z6]),(0,[z433,z0,z1,z8,z3,z6]),(0,[z0,z1,z3,z4,z6,z1263])],[(0,[z27,z899,z2,z3,z4,z6]),(0,[z0,z1,z3,z357,z6,z34]),(0,[z0,z1,z8,z119,z3,z6]),(0,[z0,z1,z3,z4,z243,z34]),(0,[z0,z1,z2,z3,z1264,z6]),(0,[z0,z1265,z2,z3,z4,z6])],[(0,[z0,z1,z176,z3,z467,z6]),(0,[z69,z1,z2,z3,z33,z254]),(0,[z0,z194,z3,z4,z6,z34])],[(0,[z989,z56,z2,z3,z4,z6]),(0,[z27,z0,z3,z4,z10,z34]),(0,[z109,z0,z2,z3,z103,z6]),(0,[z78,z1,z8,z22,z3,z6]),(0,[z0,z1,z2,z3,z1266,z6]),(0,[z478,z0,z1,z3,z10,z34]),(0,[z353,z0,z1,z3,z301,z6])],[(0,[z0,z1,z3,z4,z773,z6]),(0,[z1267,z0,z1,z8,z3,z6])],[(0,[z408,z0,z1,z140,z3,z6]),(0,[z674,z1,z2,z3,z142,z6]),(0,[z105,z0,z1,z3,z10,z34]),(0,[z1223,z0,z3,z4,z6,z34]),(0,[z1268,z0,z2,z3,z4,z6])],[(0,[z0,z219,z8,z2,z3,z6])],[(0,[z56,z22,z3,z60,z4,z6]),(0,[z0,z1,z248,z3,z4,z243]),(0,[z1,z2,z61,z4,z6,z348]),(0,[z0,z1,z2,z3,z1269,z6]),(0,[z0,z18,z44,z2,z3,z19]),(0,[z0,z1270,z2,z3,z4,z6]),(0,[z0,z1271,z2,z3,z4,z6])],[(0,[z1,z2,z3,z1016,z142,z6]),(0,[z182,z0,z1,z3,z142,z6]),(0,[z0,z1,z176,z3,z572,z6]),(0,[z979,z376,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z544,z6]),(0,[z0,z1,z1272,z3,z4,z6]),(0,[z0,z1,z1273,z3,z4,z6]),(0,[z0,z1,z3,z149,z10,z34]),(0,[z246,z1,z8,z2,z3,z6])]],
   [[(0,[z179,z167,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1274]),(0,[z0,z1,z1275,z3,z4,z6]),(0,[z0,z324,z8,z2,z3,z6]),(0,[z0,z1,z2,z3,z1276,z6]),(0,[z0,z1,z3,z4,z6,z1277]),(0,[z208,z0,z1,z6,z173,z171])],[(0,[z56,z2,z3,z4,z636,z6]),(0,[z31,z960,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z357,z6]),(0,[z0,z1,z3,z1278,z4,z6]),(0,[z421,z0,z1,z3,z4,z34]),(0,[z0,z1,z2,z3,z54,z10])],[(0,[z0,z56,z289,z3,z4,z6]),(0,[z27,z69,z2,z3,z4,z33]),(0,[z0,z2,z3,z4,z6,z1215])],[(0,[z56,z2,z641,z3,z4,z6]),(0,[z537,z56,z2,z14,z4,z6]),(0,[z82,z56,z2,z3,z142,z6]),(0,[z27,z252,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z258,z243]),(0,[z0,z1,z395,z3,z6,z266]),(0,[z1279,z1,z2,z3,z4,z6])],[(0,[z82,z0,z56,z3,z83,z6]),(0,[z280,z0,z1,z2,z3,z6]),(0,[z207,z18,z2,z3,z4,z6]),(0,[z0,z1,z26,z3,z137,z6]),(0,[z11,z0,z2,z3,z135,z10]),(0,[z0,z1,z2,z1280,z3,z6])],[(0,[z27,z121,z2,z14,z4,z6]),(0,[z1235,z0,z1,z2,z3,z6]),(0,[z27,z0,z2,z3,z137,z6]),(0,[z0,z1,z12,z3,z6,z403]),(0,[z449,z0,z1,z93,z4,z6]),(0,[z0,z1,z281,z2,z3,z10]),(0,[z376,z1072,z2,z3,z4,z6]),(0,[z246,z194,z2,z3,z4,z6])],[(0,[z31,z56,z2,z3,z4,z6]),(0,[z182,z27,z0,z3,z4,z6]),(0,[z0,z1,z1281,z3,z4,z6]),(0,[z1282,z0,z2,z3,z4,z6]),(0,[z0,z1283,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z642]),(0,[z0,z1,z2,z4,z6,z776])],[(0,[z0,z1,z1284,z3,z4,z6]),(0,[z0,z1,z2,z3,z81,z10]),(0,[z375,z0,z1,z239,z4,z6])],[(0,[z0,z1,z1285,z2,z3,z6]),(0,[z909,z0,z1,z2,z3,z6])],[(0,[z0,z1286,z2,z3,z4,z6]),(0,[z11,z0,z2,z40,z4,z135]),(0,[z0,z1,z2,z536,z3,z10])],[(0,[z0,z56,z119,z3,z4,z6]),(0,[z0,z1,z22,z3,z4,z149]),(0,[z0,z329,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z6,z254]),(0,[z1,z2,z3,z4,z6,z821]),(0,[z0,z1,z289,z3,z4,z6]),(0,[z327,z0,z1,z3,z4,z34]),(0,[z0,z1,z281,z2,z3,z149]),(0,[z0,z1,z176,z3,z6,z64])],[(0,[z537,z1,z2,z14,z4,z6]),(0,[z27,z0,z2,z3,z1183,z6]),(0,[z0,z1,z2,z336,z170,z6]),(0,[z0,z1,z3,z4,z6,z1287])],[(0,[z0,z1,z1288,z3,z4,z6]),(0,[z56,z2,z3,z4,z6,z180]),(0,[z0,z1,z2,z3,z216,z10]),(0,[z0,z1,z2,z3,z4,z1289]),(0,[z1019,z0,z1,z3,z6,z10])],[(0,[z31,z56,z140,z3,z4,z6]),(1,[z0,z56,z3,z10,z34]),(0,[z23,z56,z2,z3,z4,z6]),(0,[z0,z1,z1290,z3,z4,z6]),(0,[z0,z1,z44,z12,z3,z6])],[(0,[z42,z0,z144,z3,z4,z6]),(0,[z264,z0,z1,z3,z10,z34]),(0,[z1291,z1,z2,z3,z4,z6]),(0,[z1292,z1,z2,z3,z4,z6])],[(0,[z0,z56,z176,z3,z60,z6]),(0,[z197,z0,z234,z3,z4,z6]),(0,[z0,z1,z217,z12,z3,z6])]],
   [[(0,[z0,z152,z119,z3,z4,z6]),(0,[z0,z1,z1293,z3,z4,z6])],[(0,[z179,z23,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z450]),(0,[z0,z1,z3,z4,z6,z1294])],[(0,[z120,z0,z2,z3,z4,z6]),(0,[z0,z1,z119,z3,z4,z6]),(0,[z0,z1,z2,z3,z1295,z6]),(0,[z0,z236,z3,z4,z6,z34]),(0,[z0,z1,z2,z3,z6,z1296]),(0,[z603,z1,z2,z3,z142,z6]),(0,[z1297,z1,z2,z3,z4,z6])],[(0,[z0,z56,z2,z3,z122,z10]),(0,[z27,z525,z2,z3,z4,z6]),(0,[z27,z280,z0,z2,z3,z6]),(0,[z0,z169,z8,z2,z3,z6]),(0,[z0,z1298,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z884,z6]),(0,[z0,z1,z553,z3,z60,z6]),(0,[z208,z0,z1,z2,z6,z171])],[(0,[z0,z188,z2,z3,z4,z6]),(0,[z27,z0,z1192,z3,z4,z6]),(0,[z27,z105,z2,z3,z265,z6]),(0,[z36,z0,z2,z3,z6,z10]),(0,[z0,z1,z826,z3,z4,z6]),(0,[z0,z1,z2,z3,z1299,z6]),(0,[z827,z0,z2,z3,z4,z6]),(0,[z0,z1,z8,z1149,z3,z6])],[(0,[z574,z1,z2,z61,z4,z6]),(0,[z0,z1,z2,z40,z6,z10]),(0,[z82,z0,z1,z3,z6,z598])],[(0,[z0,z1,z2,z3,z6,z1300]),(0,[z27,z0,z2,z3,z165,z6]),(0,[z277,z78,z22,z3,z4,z6]),(0,[z420,z1,z12,z3,z4,z6]),(0,[z0,z1,z3,z10,z34,z132]),(0,[z0,z1,z902,z2,z3,z122])],[(0,[z0,z56,z395,z2,z3,z6]),(0,[z27,z0,z168,z3,z4,z6]),(0,[z42,z0,z2,z3,z6,z10]),(0,[z0,z185,z2,z3,z6,z10]),(0,[z0,z1,z176,z3,z60,z6]),(0,[z0,z1,z168,z3,z4,z166])],[(0,[z0,z1301,z2,z3,z4,z6]),(0,[z0,z1,z2,z1302,z3,z6])],[(0,[z681,z56,z2,z3,z142,z6]),(0,[z681,z0,z2,z3,z201,z6]),(0,[z56,z2,z3,z4,z6,z662]),(0,[z0,z1,z1303,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z223])],[(0,[z56,z2,z14,z3,z6,z10]),(0,[z0,z56,z112,z3,z4,z6]),(0,[z433,z0,z56,z3,z4,z6]),(0,[z0,z1,z2,z61,z4,z348]),(0,[z105,z1,z311,z3,z265,z6]),(0,[z108,z0,z1,z3,z10,z34]),(0,[z0,z1,z176,z482,z3,z6]),(0,[z0,z1,z2,z3,z1304,z6]),(0,[z0,z1,z3,z10,z34,z347]),(0,[z0,z1305,z12,z3,z4,z6])],[(0,[z1306,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1307,z6])],[(0,[z0,z56,z147,z3,z4,z6]),(0,[z0,z18,z2,z3,z4,z564]),(0,[z419,z1,z2,z40,z4,z6]),(0,[z1308,z0,z1,z2,z3,z6])],[(0,[z0,z56,z2,z3,z6,z403]),(0,[z0,z1,z3,z258,z6,z34]),(0,[z0,z1,z1309,z2,z3,z6]),(0,[z0,z1,z1310,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1311]),(0,[z0,z1,z12,z3,z346,z6])],[(0,[z56,z2,z3,z668,z4,z6]),(0,[z0,z1,z1312,z3,z4,z6]),(0,[z0,z1,z2,z3,z538,z10]),(0,[z0,z1,z12,z3,z46,z6]),(0,[z0,z1,z8,z2,z3,z643]),(0,[z45,z0,z1,z2,z4,z851])]],
   [[(0,[z528,z56,z2,z3,z4,z6]),(0,[z56,z8,z2,z22,z3,z6]),(0,[z0,z1,z2,z3,z1313,z6]),(0,[z0,z1,z1135,z2,z3,z348]),(0,[z0,z1,z2,z3,z863,z6]),(0,[z0,z1,z2,z3,z83,z149])],[(0,[z27,z0,z8,z2,z3,z6]),(1,[z56,z2,z3,z4,z348]),(0,[z56,z2,z3,z4,z6,z671]),(0,[z681,z1,z2,z3,z142,z6]),(0,[z0,z1,z8,z2,z3,z166]),(0,[z0,z2,z3,z4,z6,z1148])],[(0,[z0,z1314,z2,z3,z4,z6])],[(0,[z397,z0,z2,z3,z4,z135]),(0,[z11,z0,z2,z3,z4,z180]),(0,[z0,z1,z2,z3,z1315,z6]),(0,[z0,z1,z119,z3,z4,z243]),(0,[z110,z1,z3,z4,z6,z34])],[(0,[z272,z56,z2,z3,z4,z6]),(0,[z1316,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z163,z10,z34]),(0,[z0,z2,z3,z4,z6,z1159])],[(0,[z0,z1,z1317,z3,z4,z6])],[(0,[z1318,z1,z2,z3,z4,z6])],[(0,[z0,z56,z416,z3,z4,z6]),(0,[z429,z0,z613,z2,z3,z6])],[(0,[z0,z1,z1319,z2,z3,z6]),(0,[z24,z2,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1244]),(0,[z0,z1,z12,z3,z72,z6]),(0,[z0,z1,z3,z4,z122,z707])],[(0,[z276,z56,z2,z3,z4,z6]),(0,[z179,z27,z12,z3,z4,z6]),(0,[z0,z1,z2,z1320,z4,z6]),(0,[z1321,z1,z2,z3,z4,z6]),(1,[z0,z1,z787,z4,z6])],[(0,[z0,z1,z307,z3,z4,z34]),(0,[z0,z1,z308,z3,z4,z34]),(0,[z0,z1,z2,z3,z663,z10]),(0,[z724,z1,z2,z3,z4,z6]),(0,[z0,z102,z2,z3,z46,z6])],[],[(0,[z384,z56,z2,z3,z4,z6]),(0,[z0,z1,z12,z15,z4,z6]),(0,[z0,z2,z3,z4,z6,z712]),(0,[z886,z1,z8,z2,z3,z6])],[(0,[z0,z1,z2,z789,z4,z6]),(0,[z0,z1,z2,z3,z6,z1322]),(0,[z0,z1323,z2,z3,z4,z6]),(0,[z42,z110,z2,z3,z4,z6]),(0,[z47,z1,z12,z3,z4,z124]),(0,[z0,z1,z3,z111,z6,z34])],[(0,[z420,z56,z2,z3,z4,z6]),(0,[z82,z0,z1,z600,z3,z6]),(0,[z0,z1,z3,z235,z10,z34]),(0,[z0,z1,z12,z3,z1324,z6]),(0,[z0,z1,z217,z2,z3,z10])],[(0,[z0,z211,z876,z3,z4,z6]),(0,[z0,z1,z2,z907,z3,z6])]],
   [[(0,[z277,z0,z3,z4,z6,z34]),(0,[z1325,z0,z2,z3,z4,z6]),(0,[z0,z1,z231,z336,z4,z6]),(0,[z0,z1,z8,z289,z3,z6])],[(0,[z0,z193,z2,z3,z4,z263]),(0,[z0,z1,z395,z454,z3,z6]),(0,[z0,z1,z222,z3,z6,z34]),(0,[z264,z0,z2,z163,z4,z6]),(0,[z182,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z72,z6,z34]),(0,[z0,z708,z12,z3,z4,z6]),(0,[z256,z0,z1,z2,z6,z171])],[(0,[z11,z0,z2,z3,z137,z135]),(0,[z0,z1,z3,z4,z83,z149]),(0,[z0,z1,z3,z98,z10,z34]),(0,[z874,z0,z2,z3,z4,z6])],[(0,[z0,z1,z1326,z3,z4,z6]),(0,[z0,z1,z3,z4,z707,z34]),(0,[z0,z102,z2,z3,z72,z6]),(0,[z0,z893,z8,z2,z3,z6])],[],[(0,[z0,z1,z2,z3,z1126,z6]),(0,[z0,z1,z12,z3,z43,z6]),(0,[z0,z1,z3,z4,z6,z338]),(0,[z0,z1,z3,z4,z317,z34])],[(0,[z420,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1327]),(0,[z42,z0,z311,z3,z4,z6]),(0,[z0,z102,z12,z3,z4,z6])],[(0,[z0,z56,z2,z3,z46,z6]),(0,[z182,z0,z1,z3,z265,z6]),(0,[z197,z0,z364,z3,z4,z6]),(0,[z481,z1,z8,z2,z3,z6]),(0,[z1328,z1,z2,z3,z4,z6])],[(0,[z56,z2,z3,z4,z6,z348]),(0,[z286,z56,z2,z3,z4,z6]),(0,[z324,z2,z3,z4,z6,z124]),(0,[z0,z1,z3,z142,z10,z34]),(0,[z246,z1271,z2,z3,z4,z6])],[(0,[z0,z1329,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1330])],[(0,[z0,z56,z2,z3,z785,z6]),(0,[z78,z461,z22,z3,z4,z6]),(0,[z0,z1305,z2,z3,z4,z6]),(0,[z0,z1,z1331,z3,z4,z6]),(0,[z384,z1,z2,z3,z265,z6]),(0,[z0,z1,z3,z4,z6,z1332])],[(0,[z436,z56,z2,z3,z4,z6]),(0,[z0,z1,z168,z3,z4,z34])],[(0,[z0,z1,z3,z6,z254,z34]),(0,[z71,z481,z2,z3,z4,z6]),(0,[z0,z1,z1333,z3,z4,z6]),(0,[z0,z1,z2,z378,z623,z6]),(0,[z1291,z1,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z1334,z6]),(0,[z56,z2,z625,z3,z4,z6]),(0,[z603,z56,z2,z3,z4,z6]),(0,[z27,z0,z3,z4,z232,z6]),(0,[z27,z0,z63,z3,z4,z6]),(0,[z0,z1,z1335,z2,z3,z6]),(0,[z151,z0,z1,z3,z10,z34])],[(0,[z56,z2,z417,z3,z4,z6]),(0,[z162,z0,z2,z3,z4,z116]),(0,[z0,z1,z2,z3,z1336,z6]),(0,[z0,z1,z2,z3,z1016,z6]),(0,[z108,z0,z1,z3,z4,z149]),(0,[z0,z1,z2,z3,z346,z6]),(0,[z0,z1,z12,z3,z122,z10]),(0,[z0,z1337,z2,z3,z4,z6])],[(0,[z56,z8,z2,z3,z6,z124]),(0,[z681,z0,z2,z3,z74,z6]),(0,[z197,z0,z876,z3,z4,z6]),(0,[z0,z1,z2,z3,z46,z6]),(0,[z464,z1,z2,z3,z6,z39])]],
   [[(0,[z0,z56,z2,z3,z72,z6]),(0,[z0,z1,z2,z1338,z4,z6]),(0,[z0,z1,z3,z4,z6,z1339]),(0,[z0,z1,z1340,z3,z4,z6])],[(0,[z100,z56,z2,z3,z4,z6]),(0,[z179,z899,z2,z3,z4,z6]),(0,[z0,z236,z2,z3,z371,z6]),(0,[z0,z1,z2,z16,z4,z261]),(0,[z0,z1,z3,z4,z519,z34])],[(0,[z0,z1,z2,z3,z1341,z6]),(0,[z0,z188,z3,z4,z6,z34]),(0,[z0,z1,z3,z165,z6,z34])],[(0,[z0,z56,z12,z3,z4,z6]),(0,[z69,z56,z3,z4,z6,z34]),(0,[z27,z246,z2,z3,z4,z6]),(0,[z0,z1,z2,z728,z4,z6]),(0,[z1342,z0,z2,z3,z4,z6]),(0,[z45,z246,z1,z2,z4,z132])],[(0,[z1343,z0,z2,z3,z4,z6]),(0,[z0,z56,z2,z15,z4,z6]),(0,[z0,z1,z2,z3,z4,z1344]),(0,[z0,z1,z3,z106,z10,z34]),(0,[z0,z1,z8,z3,z6,z338])],[(0,[z47,z56,z2,z3,z4,z124]),(0,[z1233,z0,z1,z3,z4,z6]),(0,[z82,z27,z0,z3,z83,z6]),(0,[z134,z0,z12,z3,z51,z6]),(0,[z419,z1,z2,z3,z137,z6]),(0,[z82,z0,z1,z3,z832,z6]),(0,[z246,z1,z289,z3,z4,z6])],[(0,[z27,z56,z8,z2,z3,z6]),(0,[z408,z0,z56,z2,z3,z6]),(0,[z0,z1,z3,z32,z6,z34]),(0,[z0,z1345,z2,z3,z4,z6]),(0,[z286,z1,z2,z3,z265,z6]),(0,[z0,z1,z2,z3,z1346,z6]),(0,[z1,z2,z3,z4,z33,z821]),(0,[z0,z1,z8,z26,z3,z6]),(0,[z0,z1,z416,z3,z46,z6])],[(0,[z27,z0,z2,z222,z3,z6]),(0,[z0,z1347,z2,z3,z4,z6]),(0,[z47,z1,z112,z3,z4,z124]),(0,[z1348,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z10,z360]),(0,[z1267,z0,z1,z3,z4,z6])],[(0,[z110,z1,z2,z3,z6,z10]),(0,[z0,z1,z2,z3,z72,z6])],[(0,[z179,z27,z2,z3,z4,z6]),(0,[z0,z56,z454,z3,z4,z6]),(0,[z27,z0,z248,z3,z4,z6]),(0,[z0,z152,z12,z3,z4,z6]),(0,[z0,z1,z248,z3,z371,z6]),(0,[z0,z1,z2,z3,z302,z10]),(0,[z109,z0,z613,z2,z3,z6]),(0,[z0,z1,z341,z3,z4,z34])],[(0,[z27,z0,z2,z3,z1253,z6]),(0,[z0,z1,z1349,z2,z3,z6]),(0,[z0,z1,z3,z4,z6,z1350]),(0,[z0,z1,z3,z6,z10,z62]),(0,[z831,z0,z12,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z6]),(0,[z452,z0,z211,z3,z4,z6]),(0,[z182,z0,z1,z378,z3,z6]),(0,[z1218,z0,z2,z3,z4,z6])],[(0,[z77,z56,z2,z3,z6,z10]),(0,[z401,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z357,z6]),(0,[z0,z1,z2,z15,z4,z6]),(0,[z0,z1,z2,z3,z1351,z6])],[(0,[z0,z56,z3,z6,z10,z34]),(0,[z0,z56,z2,z3,z43,z6]),(0,[z47,z1,z2,z3,z4,z124]),(0,[z0,z1,z12,z3,z4,z526]),(0,[z1352,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z3,z6,z62])],[(0,[z56,z703,z2,z3,z4,z6]),(1,[z27,z0,z3,z10,z34]),(0,[z495,z0,z1,z93,z4,z6]),(0,[z0,z1,z1353,z3,z4,z6]),(0,[z0,z1,z1354,z3,z4,z6]),(0,[z11,z0,z8,z2,z3,z135]),(0,[z0,z1,z2,z3,z1324,z6])],[(0,[z91,z56,z12,z3,z4,z6]),(0,[z27,z0,z2,z3,z258,z6]),(0,[z27,z0,z2,z336,z4,z6]),(0,[z0,z1,z2,z3,z4,z1355]),(0,[z433,z134,z0,z1,z3,z6]),(0,[z0,z1,z416,z3,z72,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 470) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 470).take 473) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 943).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1428).take 154) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1582)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [470, 473, 485, 154] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 83).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 156).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 231).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 315).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 401).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 477).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [83, 73, 75, 84, 86, 76, 35] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38023

theorem PEqualNP.Outside.L_meta_38023 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277061768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277061768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38023.solve