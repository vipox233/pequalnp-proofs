import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39363

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276152832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0021021510e1c2a8#64 ++ 0x20010810a8870e15#64 ++ 0x81630e3f11e3c7ef#64 ++ 0xdc0b1871f88f1e3f#64 : BitVec 256),
   (0x422c8acc166c5993#64 ++ 0x4211645660b362cc#64 ++ 0xc6bc8bcc1e7c799b#64 ++ 0xb635e45e60f3e3cc#64 : BitVec 256),
   (0x28c033706036ee01#64 ++ 0x8146019b8301b770#64 ++ 0x38c0f3f0e07ffe1f#64 ++ 0x79c6079f8703fff0#64 : BitVec 256),
   (0x1700dc00ab003542#64 ++ 0x00b806e0055801aa#64 ++ 0xbf00fc00ff807ffe#64 ++ 0xfdf807e007fc03ff#64 : BitVec 256),
   (0x9df70000dddb001c#64 ++ 0x04efb80006eed800#64 ++ 0xdfff0000ffff8019#64 ++ 0xfefff80007fffc00#64 : BitVec 256),
   (0x1fdaedaa00000000#64 ++ 0x00fed76d50000000#64 ++ 0x7fffffff00000007#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f11e3c7ef 0xdc0b1871f88f1e3f

def z1 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fc00ff807ffe 0xfdf807e007fc03ff

def z2 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff00000007 0xf3fffffff8000000

def z3 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07ffe1f 0x79c6079f8703fff0

def z4 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1e7c799b 0xb635e45e60f3e3cc

def z5 : W := mkw 0x5fdeedea060c1913 0x42fef76f503060c8 0x7fffffff0e1c3817 0xf3fffffff870e1c0

def z6 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0000ffff8019 0xfefff80007fffc00

def z7 : W := mkw 0x420888c802041903 0x42104446401020c8 0x000081c000003800 0x0000040e000001c0

def z8 : W := mkw 0x0208888800000000 0x0010444440000000 0x46bc8bcc00000003 0xb235e45e60000000

def z9 : W := mkw 0x5ffeefee166c5993 0x42fff77f70b362cc 0xffffffff1e7c799f 0xf7fffffff8f3e3cc

def z10 : W := mkw 0x0200dc00ab003542 0x001006e0055801aa 0xa000fc00ff807ffe 0x0d0007e007fc03ff

def z11 : W := mkw 0x0208edaa00000000 0x0010476d50000000 0x2000ffff00000006 0x010007fff8000000

def z12 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0x80000000ffff8018 0x0c00000007fffc00

def z13 : W := mkw 0xbdd33130e993a60c 0x85ee9989874c9d30 0x39437030e1838604 0x49ca1b81870c1c30

def z14 : W := mkw 0xbdf73370fdffee1d 0x85efb99b87efff70 0xfffff3f0fffffe1f 0xffffff9f87fffff0

def z15 : W := mkw 0x00001000ab003542 0x00000080055801aa 0x00000000ee003810 0x00000000077001c0

def z16 : W := mkw 0x0001001100818228 0x2000080088040c11 0x0143043301838664 0x480a1821980c1c33

def z17 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x81230c0f118001e0 0x84091860788c000f

def z18 : W := mkw 0x1fc0dc00eb123542 0x00fe06e0075891aa 0xbfc0fc00ffffffff 0xfdfe07e007ffffff

def z19 : W := mkw 0xdfff8accdfff599f 0x46fffc5666fffacc 0xdfff8bccfffff99b 0xfefffc5e67ffffcc

def z20 : W := mkw 0x000002100020c200 0x0000001080010610 0x0040023000638001 0x0002001180031c00

def z21 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8000000011e3c7e8 0x0c000000008f1e3f

def z22 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7ff8fff1fffffff 0xfe3ffc7ff8ffffff

def z23 : W := mkw 0x402d02dd14edcab9 0x62016816e8a76e55 0x40ff03ff007f8001 0x0207f81ff803fc00

def z24 : W := mkw 0xffffbbfcffffff9f 0xc7fffddfe7fffffc 0xfffffbfcffffff9f 0xffffffdfe7fffffc

def z25 : W := mkw 0x1fdafdaaab003542 0x00fed7ed555801aa 0xff9cfdc0ff807ffe 0xfffce7ee07fc03ff

def z26 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0x469c83c00e7c781b 0x3234e41e0073e3c0

def z27 : W := mkw 0x28da33fa6036ee01 0x8146d19fd301b770 0x78fff3ffe07ffe1f 0x7bc7ff9fff03fff0

def z28 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf007c00ff8007e4 0xcdf803e007fc003f

def z29 : W := mkw 0x0025021514e9c2b8 0x20012810a8a74e15 0xc7ff0e3f1fffc7ff 0xfe3ff871f8fffe3f

def z30 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0x060000000e000000 0x0030000000700000

def z31 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5edc0000ee7f8019 0x7af6e0000773fc00

def z32 : W := mkw 0x572ccc8c9f4811d2 0x42b9666464fa408e 0xc73c0c0c1f8001e0 0x8639e06060fc000f

def z33 : W := mkw 0x171adc8aab003542 0x00b8d6e4555801aa 0xff3ffc0fff807ffe 0xfff9ffe07ffc03ff

def z34 : W := mkw 0x1721de15bbe1f7ea 0x20b90ef0addf0fbf 0xbf63fe3fffe3ffff 0xfdfb1ff1ffff1fff

def z35 : W := mkw 0x28e1337570f7eea9 0xa147099bab87bf75 0x38e3f3ffe07ffe1f 0x79c71f9fff03fff0

def z36 : W := mkw 0x88f7000054db001c 0x0447b80002a6d800 0x40ff0000007f8001 0x0207f8000003fc00

def z37 : W := mkw 0x572cdeccbf6c7dd3 0x42b966f665fb63ee 0xffbcffccfffc7fff 0xfffde7fe67ffe3ff

def z38 : W := mkw 0x572c8acc9f6c5993 0x42b9645664fb62cc 0xdfbc8bccfffc799b 0xfefde45e67ffe3cc

def z39 : W := mkw 0x1dd2652200000000 0x00ee932910000000 0x3943743300000004 0x41ca1ba198000000

def z40 : W := mkw 0x02009800ab003542 0x001004c0055801aa 0x86008800ff807ffa 0xbc30044007fc03ff

def z41 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8063023f11e3c7e9 0x0c031811f88f1e3f

def z42 : W := mkw 0x1dd2000000000000 0x00ee900000000000 0x5fff000000000001 0xf2fff80000000000

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0x81000c00118001e0 0x84080060008c000f

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x01630e3f00000007 0xd00b1871f8000000

def z45 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xde9c0000ffff8018 0x2ef4e00007fffc00

def z46 : W := mkw 0x28e033747076ee81 0x8147019ba383b774 0xb8e0fbfcf07fff9f 0xfdc707dfe783fffc

def z47 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c81c00e1c3810 0x2234e40e0070e1c0

def z48 : W := mkw 0x570cdcc8af0c3d53 0x42b866e6457861ea 0xff9cfdc0ff9c7ffe 0xfffce7ee07fce3ff

def z49 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x00000e3f000047e6 0x00000071f800023f

def z50 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc6bc8fff1e7c7fff 0xb635e47ff8f3e3ff

def z51 : W := mkw 0x28c023704036ca01 0x8146011b8201b650 0x00c083f0007ff81b 0x3006041f8003ffc0

def z52 : W := mkw 0x400802cc00244881 0x4200401660012244 0x000003cc00000000 0x0000001e60000000

def z53 : W := mkw 0x28c033702024ee01 0x8146019b81012770 0x38c0f3f000007e07 0x71c6079f800003f0

def z54 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x3880f1c0e01c3810 0x21c4078e0700e1c0

def z55 : W := mkw 0x9df70215ddfbc2bc 0x24efb810aeefde15 0xdfff0e3fffffc7ff 0xfefff871fffffe3f

def z56 : W := mkw 0x1500000089000000 0x00a8000004480000 0x9f000000ff800018 0xfcf8000007fc0000

def z57 : W := mkw 0x9ff7dc00ffdb355e 0x04ffbee007fed9aa 0xfffffc00ffffffff 0xffffffe007ffffff

def z58 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7e9cf1c000000000 0x23f4e78e00000000

def z59 : W := mkw 0x1fdafdaaab003542 0x00fed7ed555801aa 0xffffffffff807fff 0xfffffffffffc03ff

def z60 : W := mkw 0x3fdafffa6036ee01 0x81fed7ffd301b770 0x7fffffffe07ffe1f 0xfbffffffff03fff0

def z61 : W := mkw 0x6accbbf8663eff13 0xc35665dfc331f7f8 0x7edcf3f0ee7ffe1f 0x7bf6e79f8773fff0

def z62 : W := mkw 0x1721ce1510e1c2a8 0x20b90e70a8870e15 0xbf63fe3f11e3c7ef 0xfdfb1ff1f88f1e3f

def z63 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x81630c0f11e381e9 0xdc0b1860788f1c0f

def z64 : W := mkw 0x15005400a9002440 0x00a802a005480122 0x38007000e0000000 0x01c0038007000000

def z65 : W := mkw 0x171acc8a00000000 0x00b8d66450000000 0x473f0c0f00000000 0x8239f86078000000

def z66 : W := mkw 0x000002100020c200 0x0000001080010610 0x000000000063c608 0x0800000000031e30

def z67 : W := mkw 0xbdf73375fdffeebd 0xa5efb99bafefff75 0xffffffffffffffff 0xffffffffffffffff

def z68 : W := mkw 0x6aecabfc567edb93 0xc357655fe2b3f6dc 0xc6fc8bfc1e7ff99b 0xb637e45fe0f3ffcc

def z69 : W := mkw 0x572ddeddbfedfffb 0x62b96ef6edff6fff 0xffffffffffffffff 0xffffffffffffffff

def z70 : W := mkw 0x200033702024ee01 0x8100019b81012770 0x2040f3f00063fe0f 0x5902079f80031ff0

def z71 : W := mkw 0x6aecbbec767e7d93 0xc35765df63b3f3ec 0xfebcfbccfe7c799b 0xb7f5e7de67f3e3cc

def z72 : W := mkw 0x0020020410604080 0x0001001020830204 0x80200a0c1060418b 0x940100506083020c

def z73 : W := mkw 0xdffe8accdf7e5997 0x46fff45666fbf2cc 0xdebc8bccfe7c799b 0xb6f5e45e67f3e3cc

def z74 : W := mkw 0x1708dc88ab003542 0x00b846e4455801aa 0xffbcffccff807fff 0xfffde7fe67fc03ff

def z75 : W := mkw 0x973fcc8a9dc9001c 0x04b9fe6454ee4800 0xc73f0c0f1f800000 0x8639f86078fc0000

def z76 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0c00ffffc7ff 0xfefff86007fffe3f

def z77 : W := mkw 0x0000020000204000 0x0000001000010200 0x000002000060400b 0x1000001000030200

def z78 : W := mkw 0x40040040060c1913 0x42002002003060c8 0x000000000e1c3810 0x000000000070e1c0

def z79 : W := mkw 0xdfff88c8dfdf191f 0x46fffc4646fef8c8 0xdfff81c0ffffb819 0xfefffc0e07fffdc0

def z80 : W := mkw 0x1700cc0000000000 0x00b8066000000000 0x3f00fc0000000006 0xf1f807e000000000

def z81 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c073f0e07f8605 0x49c6039f8703fc30

def z82 : W := mkw 0x152400009d480010 0x00a9200004ea4000 0xdfbc0000fffc0019 0xfefde00007ffe000

def z83 : W := mkw 0x4aec8acc567e5993 0x4257645662b3f2cc 0xdefc8bccfe7ff99b 0xfef7e45e67f3ffcc

def z84 : W := mkw 0x9ff7dc00ffdb355e 0x04ffbee007fed9aa 0xfffff000ffffb819 0xffffff8007fffdc0

def z85 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5fff0000ee1c0011 0xf2fff8000770e000

def z86 : W := mkw 0x00001000ab003542 0x00000080055801aa 0x80000000ff807ff8 0x0c00000007fc03ff

def z87 : W := mkw 0x1721ce159be1d3ea 0x20b90e70acdf0e9f 0x87630e3f1fe3c7ef 0xdc3b1871f8ff1e3f

def z88 : W := mkw 0x0024000014480010 0x0001200000a24000 0xc6bc00001e7c0019 0xb635e00000f3e000

def z89 : W := mkw 0x28c031306012a600 0x8146018983009530 0x38407030e0038604 0x49c2038187001c30

def z90 : W := mkw 0xddff02ccddff489d 0x46eff81666effa44 0xdfff03ccffff8019 0xfefff81e67fffc00

def z91 : W := mkw 0x1fdafdaa22003542 0x00fed7ed511001aa 0x7fffffff00007fe7 0xf3fffffff80003ff

def z92 : W := mkw 0x0021000010c10008 0x0001080000860800 0x0063000000638001 0x0003180000031c00

def z93 : W := mkw 0x0200880002001102 0x0010044000100088 0x860008001e000180 0x8430004000f0000c

def z94 : W := mkw 0x1500440089000040 0x00a8022004480002 0x0100040001800060 0x00080020000c0003

def z95 : W := mkw 0x3dd277726036ee01 0x81ee93bb9301b770 0x39c3f7f3e07ffe1f 0x79ce1fbf9f03fff0

def z96 : W := mkw 0x42088acc02245983 0x42104456601122cc 0x00008bcc00007982 0x0000045e600003cc

def z97 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7bc8fcc1ffc7fff 0xfe3de47e60ffe3ff

def z98 : W := mkw 0x9fffedaadddb001c 0x04ffff6d56eed800 0xffffffffffff801f 0xfffffffffffffc00

def z99 : W := mkw 0x000821aa00000000 0x0000410d50000000 0x000003ff00000000 0x0000001ff8000000

def z100 : W := mkw 0x0200880002001102 0x0010044000100088 0x860088001e00799a 0xb430044000f003cc

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z102 : W := mkw 0x1fdaefba0020c200 0x00fed77dd0010610 0x7fffffff0063c60f 0xfbfffffff8031e30

def z103 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x38c0f1c0e07fb819 0x79c6078e0703fdc0

def z104 : W := mkw 0x200033702024ee01 0x8100019b81012770 0x2000f3f000007e06 0x0100079f800003f0

def z105 : W := mkw 0x953700009dc9001c 0x04a9b80004ee4800 0xc73f00001f800000 0x8639f80000fc0000

def z106 : W := mkw 0x08fb23bf10e1c2a8 0x2047d91df8870e15 0x40ff03ff00638001 0x0207f81ff8031c00

def z107 : W := mkw 0x3fc0ff70eb36ff43 0x81fe07fb8759b7fa 0xbfc0fff0ffffffff 0xfdfe07ff87ffffff

def z108 : W := mkw 0x1dd2000000000000 0x00ee900000000000 0x5e9c000000000000 0x22f4e00000000000

def z109 : W := mkw 0x1dda21aa00000000 0x00eed10d50000000 0x5fff03ff00000001 0xf2fff81ff8000000

def z110 : W := mkw 0xa8e53370fdffee1d 0x8547299b87efff70 0xb8c0f3f0fffffe1f 0x7dc6079f87fffff0

def z111 : W := mkw 0x9df30215d9f3c2ac 0x24ef9810aecf9e15 0x99630e3ff1e3c7ef 0xdccb1871ff8f1e3f

def z112 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x78fff3ff00000007 0x73c7ff9ff8000000

def z113 : W := mkw 0x9dd35400e993244c 0x04ee9aa0074c9922 0x39437400e1838664 0x49ca1ba0070c1c33

def z114 : W := mkw 0x9dd30000c993000c 0x04ee9800064c9800 0x19430000e1838000 0x48ca1800070c1c00

def z115 : W := mkw 0x5fffefff16eddbbb 0x62ffff7ff8b76edd 0xffffffff1fffffff 0xfffffffff8ffffff

def z116 : W := mkw 0x3dc07770e936ee41 0x81ee03bb8749b772 0x39c0f7f0e1fffe7f 0x79ce07bf870ffff3

def z117 : W := mkw 0x0200dc0022003542 0x001006e0011001aa 0x2000fc0000007fe6 0x010007e0000003ff

def z118 : W := mkw 0x0020020410604080 0x0001001020830204 0x81630e3f1060418f 0xd40b1871f883020c

def z119 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc69c81c01e7c7998 0x2634e40e00f3e3cc

def z120 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc6fc8bfc1e7fff9f 0xfe37e45fe0f3fffc

def z121 : W := mkw 0x00001000a9002440 0x0000008005480122 0x00000000e1800660 0x08000000070c0033

def z122 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x81000e3f118047ee 0xdc080071f88c023f

def z123 : W := mkw 0x9fffcc8adddb001c 0x04fffe6456eed800 0xdfff0c0fffff8019 0xfefff8607ffffc00

def z124 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xa700fc001f807fe6 0x853807e000fc03ff

def z125 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x0063023f00638001 0x00031811f8031c00

def z126 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x40ff03ff00000001 0x0207f81ff8000000

def z127 : W := mkw 0x200012506036ee01 0x810000928301b770 0x00000000e07ffe18 0x080000000703fff0

def z128 : W := mkw 0x28c0213040128200 0x8146010982009410 0x0040003000038000 0x0002000180001c00

def z129 : W := mkw 0x02088ac800244801 0x0010445640012240 0x46bc8bcc007c781b 0xb235e45e6003e3c0

def z130 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x46bc8bcc0e1c3813 0xb235e45e6070e1c0

def z131 : W := mkw 0x42088add0224dba3 0x62104456e81126dd 0x00008fff00007fe6 0x0000047ff80003ff

def z132 : W := mkw 0x9df76522dddb001c 0x04efbb2916eed800 0xffff7433ffff801d 0xfffffba19ffffc00

def z133 : W := mkw 0x8037000014c9001c 0x0401b80000a64800 0x403f000000000000 0x0201f80000000000

def z134 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x20c0f3f0007ffe07 0x0106079f8003fff0

def z135 : W := mkw 0x0200dc0022003542 0x001006e0011001aa 0x3800fc00e0007ffe 0x79c007e0070003ff

def z136 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3e00f000ee003810 0x21f00780077001c0

def z137 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f1c0e07ffe18 0x29c4078e0703fff0

def z138 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0xbf00fc001f8001e6 0xf5f807e000fc000f

def z139 : W := mkw 0x9df700009dc9001c 0x04efb80004ee4800 0xdfff00001f800001 0xf6fff80000fc0000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c00000047e6 0x000000600000023f

def z141 : W := mkw 0x1ffbefbf10e1c2a8 0x20ffdf7df8870e15 0xffffffff11e3c7ef 0xfffffffff88f1e3f

def z142 : W := mkw 0x28e1337570f7eea9 0xa147099bab87bf75 0xb8c0f3f0f1ffffff 0x7dc6079f878fffff

def z143 : W := mkw 0x28c131316093a628 0xa14609898b049d31 0x39437433e1838664 0x49ca1ba19f0c1c33

def z144 : W := mkw 0x0000024000244801 0x0000001200012240 0x008083c0007c781b 0x3004041e0003e3c0

def z145 : W := mkw 0x3fdaeffa4036ca01 0x81fed77fd201b650 0x7fffffff007f8007 0xf3fffffff803fc00

def z146 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x81630e3f118001e7 0xd40b1871f88c000f

def z147 : W := mkw 0x0021001510c182a8 0x20010800a8860c15 0x81630c3f118387e4 0xcc0b1861f88c1c3f

def z148 : W := mkw 0x422d8a9d16e9d3ba 0x62116c54e8b74e9d 0xc77f0e3f1fe3c7ef 0xde3bf871f8ff1e3f

def z149 : W := mkw 0x0000100020002400 0x0000008001000120 0x3800f000e0003810 0x21c00780070001c0

def z150 : W := mkw 0x88f7021554fbc2bc 0x2447b810aaa7de15 0x40ff023f007f8001 0x0207f811f803fc00

def z151 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x01630e3f00638007 0xd00b1871f8031c00

def z152 : W := mkw 0x9737dc00bfc9355e 0x04b9bee005fe49aa 0xff3ffc00ff807ffe 0xfff9ffe007fc03ff

def z153 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7efff3ff00000001 0x23f7ff9ff8000000

def z154 : W := mkw 0x1ffaefae10604080 0x00ffd77d70830204 0xffffffff1060418f 0xf7fffffff883020c

def z155 : W := mkw 0x08c0000000000000 0x0046000000000000 0x18c0000000000001 0x70c6000000000000

def z156 : W := mkw 0x1dd2000000000000 0x00ee900000000000 0x1943000000000000 0x40ca180000000000

def z157 : W := mkw 0x42088acc02245983 0x42104456601122cc 0x00808bcc007c799b 0x3004045e6003e3cc

def z158 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x0023000f00000000 0x0001180078000000

def z159 : W := mkw 0x572cdeccbf6c7dd3 0x42b966f665fb63ee 0xfebcfbccfe7c799b 0xb7f5e7de67f3e3cc

def z160 : W := mkw 0x1df3000010c10008 0x00ef980000860800 0xdfff000011e38009 0xfefff800008f1c00

def z161 : W := mkw 0x08c0000040120000 0x0046000002009000 0x18c00000e07f8019 0x78c600000703fc00

def z162 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f00000000000000 0xf0f8000000000000

def z163 : W := mkw 0x2021125570f7eea9 0xa1010892ab87bf75 0x81630e3ff1ffffff 0xdc0b1871ff8fffff

def z164 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81230e3f118047e6 0x84091871f88c023f

def z165 : W := mkw 0x0020000010400000 0x0001000000820000 0x8020000010600009 0x9401000000830000

def z166 : W := mkw 0x402c02cc146c4891 0x4201601660a36244 0x40bc03cc007c0001 0x0205e01e6003e000

def z167 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc7ff8bcc1ffff99b 0xfe3ffc5e60ffffcc

def z168 : W := mkw 0x000002100020c200 0x0000001080010610 0x004002300063c60f 0x5802001180031e30

def z169 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5e9c0000ee1c0010 0x22f4e0000770e000

def z170 : W := mkw 0x28c031306012a600 0x8146018983009530 0x38c0f3f0e0038607 0x79c6079f87001c30

def z171 : W := mkw 0x9df70005dddb00bc 0x24efb8002eeed805 0xdfff0c0fffff81f9 0xfefff8607ffffc0f

def z172 : W := mkw 0x15005400a9002440 0x00a802a005480122 0x39007400e1800664 0x49c803a0070c0033

def z173 : W := mkw 0x1512440200000000 0x00a8922010000000 0x0103040300000000 0x0008182018000000

def z174 : W := mkw 0x00240240146c4811 0x0001201200a36240 0xc6bc83c01e7c781b 0xb635e41e00f3e3c0

def z175 : W := mkw 0x0200880002001102 0x0010044000100088 0x87008c001f807ffe 0xfc38046000fc03ff

def z176 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc63c8bcc1e007982 0x8631e45e60f003cc

def z177 : W := mkw 0x0208efbf0020c2a0 0x2010477df8010615 0x2000ffff000047e6 0x010007fff800023f

def z178 : W := mkw 0x5fdaefee02245983 0x42fed77f701122cc 0x7fffffff00007987 0xf3fffffff80003cc

def z179 : W := mkw 0x9dd70000cd9b001c 0x04eeb800066cd800 0x5fdf0000ef9f8010 0x6afef800077cfc00

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x81000c00118047ee 0xdc080060008c023f

def z181 : W := mkw 0x28c031706016ae01 0x8146018b8300b570 0x38c0f1f0e01fbe14 0x69c6078f8700fdf0

def z182 : W := mkw 0x9dd20000c9120004 0x04ee900006489000 0x18000000e0000000 0x00c0000007000000

def z183 : W := mkw 0x02218a1512e1d3aa 0x20110c50a8970e9d 0x87638e3f1fe3ffff 0xfc3b1c71f8ff1fff

def z184 : W := mkw 0x6208bbfc2224ff83 0xc31045dfe11127fc 0x2000fbfc00007f86 0x010007dfe00003fc

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100040001800664 0x48080020000c0033

def z186 : W := mkw 0x200012506036ee01 0x810000928301b770 0x00400230e07ffe1f 0x580200118703fff0

def z187 : W := mkw 0x1fd2ed2200000000 0x00fe976910000000 0x3f43fc3300000006 0xf1fa1fe198000000

def z188 : W := mkw 0x402c02cc146c4891 0x4201601660a36244 0xc6bc03cc1e7c0019 0xb635e01e60f3e000

def z189 : W := mkw 0x15005400a9002440 0x00a802a005480122 0xb9007c00f18047ee 0xddc803e0078c023f

def z190 : W := mkw 0x3fdafdea60162c01 0x81fed7ef5300b160 0x7e9cf1c0e01c3810 0x23f4e78e0700e1c0

def z191 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0x87000c001f8001e0 0x8438006000fc000f

def z192 : W := mkw 0x953700009dc9001c 0x04a9b80004ee4800 0xdf3f0000ff800018 0xfef9f80007fc0000

def z193 : W := mkw 0x08c0212000000000 0x0046010900000000 0x38c0f3f000000007 0x71c6079f80000000

def z194 : W := mkw 0x1ffbffbfbbe1f7ea 0x20ffdffdfddf0fbf 0xffffffffffe3ffff 0xffffffffffff1fff

def z195 : W := mkw 0x28c023704036ca01 0x8146011b8201b650 0x00c003f0007fc60f 0x5806001f8003fe30

def z196 : W := mkw 0x0000024000244801 0x0000001200012240 0x000083c000007802 0x0000041e000003c0

def z197 : W := mkw 0x28e1337570f7eea9 0xa147099bab87bf75 0xb9e3fffff1ffffff 0xfdcf1fffff8fffff

def z198 : W := mkw 0x0021000010c10008 0x0001080000860800 0x8163000011e38009 0xdc0b1800008f1c00

def z199 : W := mkw 0x0021121530e1e6a8 0x20010890a9870f35 0xb963fe3ff1e3ffff 0xfdcb1ff1ff8f1fff

def z200 : W := mkw 0x6aecbbfc767eff93 0xc35765dfe3b3f7fc 0xfefcfbfcfe7fff9f 0xfff7e7dfe7f3fffc

def z201 : W := mkw 0x422c888c16481192 0x4211644460b2408c 0xc63c080c1e000180 0x8631e04060f0000c

def z202 : W := mkw 0x1dd3653300818228 0x20ee9b2998040c11 0x3943743301838664 0x49ca1ba1980c1c33

def z203 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0x469c8bcc0e1c7992 0x2234e45e6070e3cc

def z204 : W := mkw 0xdfffdeccffff7ddf 0x46fffef667fffbee 0xffffffccffffffff 0xfffffffe67ffffff

def z205 : W := mkw 0x0208cc8a00000000 0x0010466450000000 0x00000c0f00000000 0x0000006078000000

def z206 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf63fe3fff807fff 0xfdfb1ff1fffc03ff

def z207 : W := mkw 0x0000100020002400 0x0000008001000120 0x3800f000e0007e1e 0x79c00780070003f0

def z208 : W := mkw 0x0001000100810028 0x2000080008040801 0x0103040301800060 0x00081820180c0003

def z209 : W := mkw 0x171acc8a00000000 0x00b8d66450000000 0x477f0e3f00000007 0xd23bf871f8000000

def z210 : W := mkw 0x1fdbedbb00818228 0x20fedf6dd8040c11 0x7fffffff01838667 0xfbfffffff80c1c33

def z211 : W := mkw 0x1708cc8800000000 0x00b8466440000000 0x7fbcffcc00000007 0xf3fde7fe60000000

def z212 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbe00f000ff807ff8 0x2df0078007fc03ff

def z213 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6bc8bcc1ffffffb 0xbe35e45e60ffffff

def z214 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8040023011e3c7ef 0x5c020011808f1e3f

def z215 : W := mkw 0x622c9adc767eff93 0xc31164d6e3b3f7fc 0xc6bc8bccfe7fff9b 0xbe35e45e67f3fffc

def z216 : W := mkw 0x0ac8a9a800000000 0x0056454d40000000 0x7efcfbfc00000007 0xf3f7e7dfe0000000

def z217 : W := mkw 0x0001021100a1c228 0x2000081088050e11 0x0143063301e3c66f 0x580a1831980f1e33

def z218 : W := mkw 0x0001000000810008 0x0000080000040800 0x0143000001838000 0x480a1800000c1c00

def z219 : W := mkw 0x422cdecc366c7dd3 0x421166f661b363ee 0xe6bcffcc1e7c7fff 0xb735e7fe60f3e3ff

def z220 : W := mkw 0x08fb23bf10e1c2a8 0x2047d91df8870e15 0xc1ff0fff11e3c7ef 0xde0ff87ff88f1e3f

def z221 : W := mkw 0x1700dc0022003542 0x00b806e0011001aa 0x3f00fc0000007fe6 0xf1f807e0000003ff

def z222 : W := mkw 0x40240244146c4891 0x4201201220a36244 0x00000000007c0000 0x000000000003e000

def z223 : W := mkw 0x0adaedaa00000000 0x0056d76d50000000 0x60ffffff00000007 0x0307fffff8000000

def z224 : W := mkw 0x1724dc00bf483552 0x00b926e005fa41aa 0xffbcfc00fffc7fff 0xfffde7e007ffe3ff

def z225 : W := mkw 0x3fdafffa6036ee01 0x81fed7ffd301b770 0x7edcf3f0e07ffe1f 0x7bf6e79f8703fff0

def z226 : W := mkw 0x0000004000040801 0x0000000200002040 0x008081c0001c3810 0x2004040e0000e1c0

def z227 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x39e3ffffe07ffe1f 0xf9cf1fffff03fff0

def z228 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc0bcc1e7c0181 0x8635e05e60f3e00c

def z229 : W := mkw 0x1dda65aa00000000 0x00eed32d50000000 0x79ff77ff00000005 0x43cffbbff8000000

def z230 : W := mkw 0x6aedbbfd76ffffbb 0xe3576ddfebb7fffd 0xffffffffffffffff 0xffffffffffffffff

def z231 : W := mkw 0x4aecabec166c5993 0x4257655f60b362cc 0xfefcfbfc1e7c799f 0xf7f7e7dfe0f3e3cc

def z232 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0xc6bc0000ffff8019 0xbe35e00007fffc00

def z233 : W := mkw 0x1700dc00a9002440 0x00b806e005480122 0x3f00fc00e1800666 0xf9f807e0070c0033

def z234 : W := mkw 0x28c0312060122400 0x8146018903009120 0x38007000e0000000 0x01c0038007000000

def z235 : W := mkw 0x0004000004080010 0x0000200000204000 0x469c00000e1c0010 0x2234e0000070e000

def z236 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x80000e3f11e3c7ee 0x0c000071f88f1e3f

def z237 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x01630e3f000047e7 0xd00b1871f800023f

def z238 : W := mkw 0x9df70215ddfbc2bc 0x24efb810aeefde15 0xdfff023fffff8019 0xfefff811fffffc00

def z239 : W := mkw 0x2000104060162c01 0x810000820300b160 0x00000000e01c3810 0x000000000700e1c0

def z240 : W := mkw 0x1701dc11ab81b76a 0x20b80ee08d5c0dbb 0xbf43fc33ff83fffe 0xfdfa1fe19ffc1fff

def z241 : W := mkw 0x28c033306032e600 0x8146019983019730 0x38407230e063c60f 0x59c2039187031e30

def z242 : W := mkw 0xa8f7237054ffca1d 0x8547b91b82a7fe50 0x40ff03f0007f8001 0x0207f81f8003fc00

def z243 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x59ff0000e1ff8001 0x4acff800070ffc00

def z244 : W := mkw 0x0000100020002400 0x0000008001000120 0x38007000e0000604 0x49c0038007000030

def z245 : W := mkw 0x951300008981000c 0x04a89800044c0800 0x0103000001800000 0x00081800000c0000

def z246 : W := mkw 0x1fda888800000000 0x00fed44440000000 0x5fff8bcc00000003 0xf2fffc5e60000000

def z247 : W := mkw 0x28c0216040160801 0x8146010b0200b040 0x008001c0001c0000 0x0004000e0000e000

def z248 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc69c89c01e1c799a 0xb634e44e00f0e3cc

def z249 : W := mkw 0x3ffbffff70f7eea9 0xa1ffdffffb87bf75 0xfffffffff1ffffff 0xffffffffff8fffff

def z250 : W := mkw 0x1ffbedaf10c100a8 0x20ffdf6d78860805 0xffffffff118001e7 0xf7fffffff88c000f

def z251 : W := mkw 0x28c023704036ca01 0x8146011b8201b650 0x00c003f0007f8001 0x0006001f8003fc00

def z252 : W := mkw 0x1df3673710e1c2a8 0x20ef9b39b8870e15 0xb9637e3f11e3c7ef 0xddcb1bf1f88f1e3f

def z253 : W := mkw 0x400c00c8040c0811 0x4200600640206040 0x409c01c0001c0000 0x0204e00e0000e000

def z254 : W := mkw 0x3dd275326012a600 0x81ee93a993009530 0x39437433e0038604 0x49ca1ba19f001c30

def z255 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x99430000ffff8018 0x4cca180007fffc00

def z256 : W := mkw 0x0200cc0000000000 0x0010066000000000 0x2000fc0000000006 0x010007e000000000

def z257 : W := mkw 0x00001000ab003542 0x00000080055801aa 0xb800f000ff807ffe 0x7dc0078007fc03ff

def z258 : W := mkw 0x1700cc0002001102 0x00b8066000100088 0xbf00fc001e00799e 0xf5f807e000f003cc

def z259 : W := mkw 0x200012506036ee01 0x810000928301b770 0x008083c0e07ffe1b 0x3804041e0703fff0

def z260 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7f7f7c3f00000004 0xc3fbfbe1f8000000

def z261 : W := mkw 0x68ec33fc747eee91 0xc347619fe3a3f774 0x78fcf3fce07ffe1f 0x7bc7e79fe703fff0

def z262 : W := mkw 0x00211215bbe1f7ea 0x20010890addf0fbf 0x81630e3fffe3ffff 0xdc0b1871ffff1fff

def z263 : W := mkw 0x0001021500a1c2a8 0x20000810a8050e15 0x01430e3f0183c7e6 0x480a1871f80c1e3f

def z264 : W := mkw 0x0208fdaa22003542 0x001047ed511001aa 0x2000ffff00007fe6 0x010007fff80003ff

def z265 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f11e381e1 0x840b1871f88f1c0f

def z266 : W := mkw 0x1fdaedaa8b001142 0x00fed76d5458008a 0xffffffff1f8001e7 0xf7fffffff8fc000f

def z267 : W := mkw 0x1700cc0089000000 0x00b8066004480000 0xbf00fc00ff80001e 0xfdf807e007fc0000

def z268 : W := mkw 0x1dd2652200000000 0x00ee932910000000 0x3800700000000000 0x01c0038000000000

def z269 : W := mkw 0x88d300004093000c 0x0446980002049800 0x0043000000038000 0x0002180000001c00

def z270 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7ff8fff1e7c799f 0xf63ffc7ff8f3e3cc

def z271 : W := mkw 0x0200880000000000 0x0010044000000000 0x0600880000000002 0xb030044000000000

def z272 : W := mkw 0x1fdafdaaab003542 0x00fed7ed555801aa 0x7e9cf1c0ee003810 0x23f4e78e077001c0

def z273 : W := mkw 0x3dc07530e912a640 0x81ee03a987489532 0x39407430e1838664 0x49ca03a1870c1c33

def z274 : W := mkw 0x0000024000244801 0x0000001200012240 0x00000000007c7818 0x000000000003e3c0

def z275 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8163000011e3c7e9 0xdc0b1800008f1e3f

def z276 : W := mkw 0x0020020410604080 0x0001001020830204 0x81200e0c11e047ef 0xdc090070608f023f

def z277 : W := mkw 0x0021001110c18228 0x2001080088860c11 0x8163043311e3866d 0xdc0b1821988f1c33

def z278 : W := mkw 0x1720de04bb6075c2 0x00b906f025db03ae 0xbf20fe0cffe07fff 0xfdf907f067ff03ff

def z279 : W := mkw 0x1fdaedaa02001102 0x00fed76d50100088 0xffffffff1e00799f 0xf7fffffff8f003cc

def z280 : W := mkw 0x4000024402245983 0x42000012201122cc 0x0000000000007980 0x00000000000003cc

def z281 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x5eff0000ee7f8011 0x22f7f8000773fc00

def z282 : W := mkw 0x80040000cd1a0014 0x040020000668d000 0x00000000ee1c0010 0x000000000770e000

def z283 : W := mkw 0x1dd2000089000000 0x00ee900004480000 0xdfff0000ff800019 0xfefff80007fc0000

def z284 : W := mkw 0x9fdeedaacd1a0014 0x04fef76d5668d000 0x7e9cf1c0ee1c0010 0x23f4e78e0770e000

def z285 : W := mkw 0x000002500024ca01 0x0000001280012650 0x00c083f0007ffe1f 0x7806041f8003fff0

def z286 : W := mkw 0x200031302000a600 0x8100018981000530 0x2000703000000604 0x0100038180000030

def z287 : W := mkw 0x80251000ffdb355e 0x0401288007fed9aa 0x80000000fffffff8 0x0c00000007ffffff

def z288 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81230c0f11e3c7e8 0x8c091860788f1e3f

def z289 : W := mkw 0x9df72120dddb001c 0x04efb90906eed800 0xfffff3f0ffff801f 0xffffff9f87fffc00

def z290 : W := mkw 0x40240244166c5993 0x4201201220b362cc 0x808083c01e7c799b 0x3404041e00f3e3cc

def z291 : W := mkw 0xdfde88c8cf1e1917 0x46fef4464678f0c8 0x5e9c81c0ee1c3810 0x22f4e40e0770e1c0

def z292 : W := mkw 0x1721cc059bc111ea 0x20b90e602cde088f 0x87230c0f1f8001e0 0x8439186078fc000f

def z293 : W := mkw 0x0208edaa00000000 0x0010476d50000000 0x2000f1c000000000 0x0100078e00000000

def z294 : W := mkw 0x28c0336060366c01 0x8146019b0301b360 0x3880f3c0e07c781b 0x31c4079e0703e3c0

def z295 : W := mkw 0x4208888c02001182 0x421044446010008c 0x0000080c00000180 0x000000406000000c

def z296 : W := mkw 0x1df3021510e1c2a8 0x20ef9810a8870e15 0xdfff0e3f11e3c7ef 0xfefff871f88f1e3f

def z297 : W := mkw 0xc22d8accdfff599f 0x46116c5666fffacc 0xc6bc8bccfffff99b 0xbe35e45e67ffffcc

def z298 : W := mkw 0x0021020510e140a8 0x2001081028870a05 0x81230e0f11e041eb 0x94091870788f020f

def z299 : W := mkw 0x5724de44bf6c7dd3 0x42b926f225fb63ee 0xbf00fc00fffc7ffe 0xfdf807e007ffe3ff

def z300 : W := mkw 0x1df6000014480010 0x00efb00000a24000 0xdfff00001e7c0019 0xf6fff80000f3e000

def z301 : W := mkw 0x9dd30000c993000c 0x04ee9800064c9800 0x5fff0000e1838001 0xfafff800070c1c00

def z302 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x00400e3f0063c7ef 0x58020071f8031e3f

def z303 : W := mkw 0x0021020410e14088 0x0001081020870a04 0x81630a0c11e3c18b 0xdc0b1850608f1e0c

def z304 : W := mkw 0x0025000014c90018 0x0001280000a64800 0xc7ff00001fff8019 0xfe3ff80000fffc00

def z305 : W := mkw 0x40240244166c5993 0x4201201220b362cc 0x800000001e7c7998 0x0400000000f3e3cc

def z306 : W := mkw 0x0021000010c10008 0x0001080000860800 0x81630e3f11e3800f 0xdc0b1871f88f1c00

def z307 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x0000023f00000000 0x00000011f8000000

def z308 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc7bf8fcf1ffc79fb 0xb63dfc7e78ffe3cf

def z309 : W := mkw 0x0000100020002400 0x0000008001000120 0x2000f00000007e06 0x01000780000003f0

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x008083c000000003 0x3004041e00000000

def z311 : W := mkw 0x1500000089000000 0x00a8000004480000 0x9f000c00ff8047fe 0xfcf8006007fc023f

def z312 : W := mkw 0x422c9accbf6c7dd3 0x421164d665fb63ee 0xc6bc8bccfffc7ffb 0xbe35e45e67ffe3ff

def z313 : W := mkw 0x42298add12e5dbab 0x62114c56e8972edd 0x81638fff11e3ffef 0xdc0b1c7ff88f1fff

def z314 : W := mkw 0x28c031306012a600 0x8146018983009530 0x38c07030e07f861d 0x79c603818703fc30

def z315 : W := mkw 0x9dd30000c993000c 0x04ee9800064c9800 0x9f430000ff838018 0xfcfa180007fc1c00

def z316 : W := mkw 0x402c02cc146c4891 0x4201601660a36244 0xc0bc0bcc107c418b 0x9605e05e6083e20c

def z317 : W := mkw 0x802500009dc9001c 0x0401280004ee4800 0x800000001f800000 0x0400000000fc0000

def z318 : W := mkw 0x022c888814480010 0x0011644440a24000 0xc6bc8bcc1e7c001b 0xb635e45e60f3e000

def z319 : W := mkw 0x0200880002001102 0x0010044000100088 0x060080000e003810 0x20300400007001c0

def z320 : W := mkw 0x1500000089000000 0x00a8000004480000 0x19000000e1800000 0x48c80000070c0000

def z321 : W := mkw 0x1fdaedaa40120000 0x00fed76d52009000 0x7fffffffe07f801f 0xfbffffffff03fc00

def z322 : W := mkw 0x0208edaa00000000 0x0010476d50000000 0x66bcffff00000007 0xb335e7fff8000000

def z323 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6ff8bff1e7ff99b 0xb637fc5ff8f3ffcc

def z324 : W := mkw 0x9ff7de15fffbf7fe 0x24ffbef0afffdfbf 0xfffffe3fffffffff 0xfffffff1ffffffff

def z325 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x00630e3f0063c7e7 0x00031871f8031e3f

def z326 : W := mkw 0x0200de152220f7e2 0x201006f0a91107bf 0x2000fe3f00007fe6 0x010007f1f80003ff

def z327 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0xc6bc81c01e7c3819 0xb635e40e00f3e1c0

def z328 : W := mkw 0x08c0312020002400 0x0046018901000120 0x38c0f3f0e0007e1f 0x79c6079f870003f0

def z329 : W := mkw 0x28c023704036ca01 0x8146011b8201b650 0x38c0f3f0007f8007 0x71c6079f8003fc00

def z330 : W := mkw 0x0000024000244801 0x0000001200012240 0x008003c0007c0001 0x0004001e0003e000

def z331 : W := mkw 0xcaff8acc56ff599f 0x4657fc5662b7facc 0xc6ff8bcc1e7ff99b 0xb637fc5e60f3ffcc

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800f00000000006 0x71c0078000000000

def z333 : W := mkw 0x08c0212000000000 0x0046010900000000 0x00c003f000000001 0x0006001f80000000

def z334 : W := mkw 0x20001250eb36ff43 0x810000928759b7fa 0x80000000fffffff8 0x0c00000007ffffff

def z335 : W := mkw 0x171acc8a00000000 0x00b8d66450000000 0x7f3ffc0f00000006 0xf3f9ffe078000000

def z336 : W := mkw 0x08c0024040364801 0x004600120201b240 0x18c083c0e07ff81b 0x78c6041e0703ffc0

def z337 : W := mkw 0x001a008a00000000 0x0000d00450000000 0x403f000f00000000 0x0201f80078000000

def z338 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x47ff0fff00000001 0x823ff87ff8000000

def z339 : W := mkw 0x0200cc0002001142 0x001006600010008a 0x00000c00000001e0 0x000000600000000f

def z340 : W := mkw 0x0000540020002440 0x000002a001000122 0x2000740000000664 0x010003a000000033

def z341 : W := mkw 0x88f7021554fbc2bc 0x2447b810aaa7de15 0xc1ff0e3f11ffc7ef 0xde0ff871f88ffe3f

def z342 : W := mkw 0x402c02cc166c5993 0x4201601660b362cc 0xc0bc03cc1e7c7999 0x0605e01e60f3e3cc

def z343 : W := mkw 0x422c888c16481192 0x4211644460b2408c 0xc63c880c1e00799a 0xb631e44060f003cc

def z344 : W := mkw 0x0001001100818228 0x2000080088040c11 0x81430c331183c7ee 0xdc0a1861988c1e3f

def z345 : W := mkw 0x1ffeedaa14480010 0x00fff76d50a24000 0xffffffff1e7c001f 0xf7fffffff8f3e000

def z346 : W := mkw 0x15005400a9002440 0x00a802a005480122 0xbf007400ff80067c 0xfdf803a007fc0033

def z347 : W := mkw 0x1dd2652200000000 0x00ee932910000000 0x7fff743300000005 0xf3fffba198000000

def z348 : W := mkw 0x0000100020002400 0x0000008001000120 0x00000000e0007e18 0x08000000070003f0

def z349 : W := mkw 0x08c0212000000000 0x0046010900000000 0x3840703000000004 0x41c2038180000000

def z350 : W := mkw 0x80250215ddfbc2bc 0x24012810aeefde15 0x80000000ffffc7f8 0x0c00000007fffe3f

def z351 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0x9f000c00ff8001f8 0xfcf8006007fc000f

def z352 : W := mkw 0x08c023300020c200 0x0046011980010610 0x38c0f3f00063c60f 0x79c6079f80031e30

def z353 : W := mkw 0x000000008b001142 0x000000000458008a 0x800000001f8001e0 0x0400000000fc000f

def z354 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0xc6bc89cc1e1c3990 0xa635e44e60f0e1cc

def z355 : W := mkw 0x200012506036ee01 0x810000928301b770 0x3800f000e07ffe1e 0x79c007800703fff0

def z356 : W := mkw 0x08c0100060122400 0x0046008003009120 0x38c0f000e07ffe1f 0x79c607800703fff0

def z357 : W := mkw 0x3700de50eb36ff43 0x81b806f28759b7fa 0xbf00fc00fffffffe 0xfdf807e007ffffff

def z358 : W := mkw 0xa8f7337074ffee1d 0x8547b99b83a7ff70 0x78fff3f0e07ffe1f 0x7bc7ff9f8703fff0

def z359 : W := mkw 0x0208888800000000 0x0010444440000000 0x47ff8fff00000007 0xf23ffc7ff8000000

def z360 : W := mkw 0x9df7000054db001c 0x04efb80002a6d800 0x5fff0000007f8001 0xf2fff8000003fc00

def z361 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x0163063f01e38665 0x480b1831f80f1c33

def z362 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x46bc83cc0e7c3811 0x2235e41e6073e1c0

def z363 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x41ff0fff00000007 0xd20ff87ff8000000

def z364 : W := mkw 0x08c002104032c200 0x0046001082019610 0x18c00230e07fc61f 0x78c600118703fe30

def z365 : W := mkw 0x08d2212200000000 0x0046910910000000 0x0043003300000000 0x0002180198000000

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000e0000018 0x78c0000007000000

def z367 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xb9c0fff0f1ffffff 0xfdce07ff878fffff

def z368 : W := mkw 0x9dff21aadddb001c 0x04eff90d56eed800 0xdfff03ffffff8019 0xfefff81ffffffc00

def z369 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0e3fffff801f 0xfefff871fffffc00

def z370 : W := mkw 0x0208888800000000 0x0010444440000000 0x469c81c000000000 0x2234e40e00000000

def z371 : W := mkw 0x9df30000d9d3000c 0x04ef980006ce9800 0x99630000f1e38009 0xdccb1800078f1c00

def z372 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07fb811 0x21c6079f8703fdc0

def z373 : W := mkw 0x02288a8c10604080 0x0011445460830204 0xc6bc8bcc1060418b 0xb635e45e6083020c

def z374 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xc7ff00001fff8001 0x863ff80000fffc00

def z375 : W := mkw 0x3dc03370e936ee01 0x81ee019b8749b770 0xbfc0f3f0fffffe1f 0xfdfe079f87fffff0

def z376 : W := mkw 0xbffffffafdffee1d 0x85ffffffd7efff70 0xfffffffffffffe1f 0xfffffffffffffff0

def z377 : W := mkw 0x5fdeedea060c1913 0x42fef76f503060c8 0x7e9cf1c00e1c3810 0x23f4e78e0070e1c0

def z378 : W := mkw 0xa0251250fdffee1d 0x8501289287efff70 0x80000000fffffe18 0x0c00000007fffff0

def z379 : W := mkw 0x9fdeedaacd1a0014 0x04fef76d5668d000 0x7fffffffee1c0017 0xf3ffffffff70e000

def z380 : W := mkw 0x1dd27522a9002440 0x00ee93a915480122 0x39437433e1800664 0x49ca1ba19f0c0033

def z381 : W := mkw 0x9ff78800dfdb111e 0x04ffbc4006fed888 0xdfff8800fffff99b 0xfefffc4007ffffcc

def z382 : W := mkw 0x48fe23ee146c4891 0x4247f11f70a36244 0x40ff03ff007c0001 0x0207f81ff803e000

def z383 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3900fc00e1807fe6 0x49c807e0070c03ff

def z384 : W := mkw 0x08c0212000000000 0x0046010900000000 0x3880f1c000000000 0x21c4078e00000000

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x81630e3f118047ef 0xdc0b1871f88c023f

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x00800000007c0019 0x300400000003e000

def z387 : W := mkw 0x572cdc8cbf4835d2 0x42b966e465fa41ae 0xff3cfc0cff807ffe 0xfff9e7e067fc03ff

def z388 : W := mkw 0x953702159de9c2bc 0x24a9b810acef4e15 0xc77f0e3f1fe3c7ef 0xde3bf871f8ff1e3f

def z389 : W := mkw 0xdfff8adddfffdbbf 0x66fffc56eefffedd 0xdfff8fffffffffff 0xfefffc7fffffffff

def z390 : W := mkw 0x000002100020c200 0x0000001080010610 0x01630e3f0063c60f 0xd80b1871f8031e30

def z391 : W := mkw 0xbdf71250fdffee1d 0x85efb89287efff70 0xdfff0000fffffe19 0xfefff80007fffff0

def z392 : W := mkw 0x1fd2dc00ab003542 0x00fe96e0055801aa 0xfffffc00ff807fff 0xffffffe007fc03ff

def z393 : W := mkw 0x88d60000441a0014 0x0446b0000220d000 0x409c0000001c0000 0x0204e0000000e000

def z394 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbe00f800fe00799a 0xb5f007c007f003cc

def z395 : W := mkw 0x95250000dddb001c 0x04a9280006eed800 0x9f000000ffff8018 0xfcf8000007fffc00

def z396 : W := mkw 0x0224880016481112 0x0011244000b24088 0xc6bc88001e7c799b 0xb635e44000f3e3cc

def z397 : W := mkw 0x08c0000040120000 0x0046000002009000 0x18800000e01c0010 0x20c400000700e000

def z398 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x00c003f0e07ffe19 0x0806001f8703fff0

def z399 : W := mkw 0x15005400ab003542 0x00a802a0055801aa 0xb9007400ff807ffc 0x4dc803a007fc03ff

def z400 : W := mkw 0x422c888c16481192 0x4211644460b2408c 0xc6bc080c1e7c0199 0xb635e04060f3e00c

def z401 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x80000000118001e0 0x04000000008c000f

def z402 : W := mkw 0x420c888806081112 0x4210644440304088 0x461c00000e000000 0x0230e00000700000

def z403 : W := mkw 0x0208888802001102 0x0010444440100088 0xc6bc8bcc1e00799b 0xb635e45e60f003cc

def z404 : W := mkw 0x0001001100818228 0x2000080088040c11 0x01630e3f01838667 0xd80b1871f80c1c33

def z405 : W := mkw 0x1500000089000000 0x00a8000004480000 0x1e000000ee000010 0x20f0000007700000

def z406 : W := mkw 0x4208decc22247dc3 0x421046f6611123ee 0x2000ffcc00007fe6 0x010007fe600003ff

def z407 : W := mkw 0x1dd2652200000000 0x00ee932910000000 0x39637e3f00000007 0xd1cb1bf1f8000000

def z408 : W := mkw 0x1fdafdaaa9002440 0x00fed7ed55480122 0x7fffffffe1800667 0xfbffffffff0c0033

def z409 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0x87008c001f8079fa 0xb438046000fc03cf

def z410 : W := mkw 0x9dd30011c993822c 0x24ee98008e4c9c11 0x19430433e1838664 0x48ca18219f0c1c33

def z411 : W := mkw 0x200012502024ee01 0x8100009281012770 0x0000000000007e00 0x00000000000003f0

def z412 : W := mkw 0x4025025516eddbbb 0x62012812a8b76edd 0x81630e3f1fffffff 0xdc0b1871f8ffffff

def z413 : W := mkw 0x28e1237550f7caa9 0xa147091baa87be55 0x81e30fff11ffc7ef 0xdc0f187ff88ffe3f

def z414 : W := mkw 0x28da23fa4036ca01 0x8146d11fd201b650 0x40ff03ff007f8001 0x0207f81ff803fc00

def z415 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81000c0011e3c7ee 0xdc080060008f1e3f

def z416 : W := mkw 0x88f7000054db001c 0x0447b80002a6d800 0x58ff0000e07f8019 0x7ac7f8000703fc00

def z417 : W := mkw 0x0200880002001102 0x0010044000100088 0x0000880000007982 0x00000440000003cc

def z418 : W := mkw 0x171acc8a00000000 0x00b8d66450000000 0x47bf8fcf00000003 0xb23dfc7e78000000

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x800008001000418a 0x940000400080020c

def z420 : W := mkw 0x28e1237550f7caa9 0xa147091baa87be55 0x00e303ff007f8001 0x0007181ff803fc00

def z421 : W := mkw 0x1fdafdaa20002400 0x00fed7ed51000120 0x7fffffffe0007e1f 0xfbffffffff0003f0

def z422 : W := mkw 0x95370000dddb001c 0x04a9b80006eed800 0xc73f0000ffff8018 0x8e39f80007fffc00

def z423 : W := mkw 0x15015411a981a668 0x20a80aa08d4c0d33 0x39437433e1838664 0x49ca1ba19f0c1c33

def z424 : W := mkw 0xbdd63370ed3eee15 0x85eeb19b8769f770 0x7edcf3f0ee7ffe1f 0x7bf6e79f8773fff0

def z425 : W := mkw 0x4024000416481192 0x4201200020b2408c 0x800000001e000180 0x0400000000f0000c

def z426 : W := mkw 0x1dd2000040120000 0x00ee900002009000 0x5fff0000e07f8019 0xfafff8000703fc00

def z427 : W := mkw 0xbdf73130fddba61c 0x85efb98987eedd30 0xffff7030ffff861d 0xfffffb8187fffc30

def z428 : W := mkw 0x2ac0bb706236ff03 0x815605db8311b7f8 0xbec0fbf0fe7fff9f 0xfdf607df87f3fffc

def z429 : W := mkw 0x15215615b9e1e6e8 0x20a90ab0adcf0f37 0xb9637e3ff1e3c7ef 0xddcb1bf1ff8f1e3f

def z430 : W := mkw 0x0adaa9aa00000000 0x0056d54d50000000 0x46ff8bff00000003 0xb237fc5ff8000000

def z431 : W := mkw 0x4025025516eddbbb 0x62012812a8b76edd 0x800000001ffffff8 0x0c00000000ffffff

def z432 : W := mkw 0xbdd63160ed1e2c15 0x85eeb18b0768f160 0x7e9cf1c0ee1c3810 0x23f4e78e0770e1c0

def z433 : W := mkw 0x2021125570f7eea9 0xa1010892ab87bf75 0x80000000f1fffff8 0x0c000000078fffff

def z434 : W := mkw 0x5ffeedae16481192 0x42fff76d70b2408c 0xffffffff1e000187 0xf7fffffff8f0000c

def z435 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0xffffffff118047ef 0xfffffffff88c023f

def z436 : W := mkw 0x951600008d080014 0x04a8b00004684000 0x461c00000e000000 0x0230e00000700000

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x000080000000781a 0x30000400000003c0

def z438 : W := mkw 0x0229efbf10e1c2a8 0x20114f7df8870e15 0xa163ffff11e3c7ef 0xdd0b1ffff88f1e3f

def z439 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0xdf9c0000ff9c0018 0xfefce00007fce000

def z440 : W := mkw 0x28c012506036ee01 0x814600928301b770 0x18c00000e07ffe19 0x78c600000703fff0

def z441 : W := mkw 0x0020020410604080 0x0001001020830204 0x0020020c00600001 0x0001001060030000

def z442 : W := mkw 0xc8ff02cc54ff489d 0x4647f81662a7fa44 0x40ff03cc007f8001 0x0207f81e6003fc00

def z443 : W := mkw 0x0200dc0022003542 0x001006e0011001aa 0x2000f00000003800 0x01000780000001c0

def z444 : W := mkw 0x9fffedaadddb001c 0x04ffff6d56eed800 0xfffff1c0ffff8019 0xffffff8e07fffc00

def z445 : W := mkw 0x0024000014480010 0x0001200000a24000 0x800000001e7c0018 0x0400000000f3e000

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100000011800008 0xdc080000008c0000

def z447 : W := mkw 0x402c02cc146c4891 0x4201601660a36244 0x40bc83cc007c781b 0x3205e41e6003e3c0

def z448 : W := mkw 0x1fd2cc0000000000 0x00fe966000000000 0x7ffffc0000000007 0xf3ffffe000000000

def z449 : W := mkw 0x9df71000fddb241c 0x04efb88007eed920 0xfffff000fffffe1f 0xffffff8007fffff0

def z450 : W := mkw 0x1512000000000000 0x00a8900000000000 0x473f000000000000 0x8239f80000000000

def z451 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fbffdcf00000000 0xa3fdffee78000000

def z452 : W := mkw 0x2200ff702224ff43 0x811007fb811127fa 0x2000fff000007fe6 0x010007ff800003ff

def z453 : W := mkw 0x1700de10ab20f742 0x00b806f0855907ba 0xbf40fe30ffe3ffff 0xfdfa07f187ff1fff

def z454 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3e00fc00ee007ff6 0x21f007e0077003ff

def z455 : W := mkw 0x9ff7cc00dddb001c 0x04ffbe6006eed800 0xfffffc00ffff801f 0xffffffe007fffc00

def z456 : W := mkw 0x9ffffdaaffdb355e 0x04ffffed57fed9aa 0xffffffffffffffff 0xffffffffffffffff

def z457 : W := mkw 0x9fffedaa54db001c 0x04ffff6d52a6d800 0x7fffffff007f8007 0xf3fffffff803fc00

def z458 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0x81630000ffff8019 0xdc0b180007fffc00

def z459 : W := mkw 0x573ecece166c5993 0x42b9f67670b362cc 0xc7bf8fcf1e7c799b 0xb63dfc7e78f3e3cc

def z460 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x80008bcc1e7c799a 0x0400045e60f3e3cc

def z461 : W := mkw 0x08e40000545a0010 0x0047200002a2d000 0xdefc0000fe7f8019 0xfef7e00007f3fc00

def z462 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x3943ffff00000006 0x41ca1ffff8000000

def z463 : W := mkw 0x9df60000dd5a0014 0x04efb00006ead000 0xdebc0000fe7c0019 0xb6f5e00007f3e000

def z464 : W := mkw 0x80010000c993000c 0x04000800064c9800 0x00000000e1838000 0x08000000070c1c00

def z465 : W := mkw 0x9ff7cc00dfdb115e 0x04ffbe6006fed88a 0xdfff0c00ffff81f9 0xfefff86007fffc0f

def z466 : W := mkw 0x9fffefbfddfbc2bc 0x24ffff7dfeefde15 0xffffffffffffc7ff 0xfffffffffffffe3f

def z467 : W := mkw 0x0021000010c10008 0x0001080000860800 0x8123000011800000 0x84091800008c0000

def z468 : W := mkw 0x0000001100008220 0x2000000088000411 0x0000043300000664 0x0000002198000033

def z469 : W := mkw 0x7ffefffe767eff93 0xc3fff7fff3b3f7fc 0xfffffffffe7fff9f 0xfffffffffff3fffc

def z470 : W := mkw 0xbdd33370e9b7ee0d 0x85ee999b874dbf70 0x39c3f3f0e1fffe1f 0x79ce1f9f870ffff0

def z471 : W := mkw 0x9df70210ddfbc21c 0x04efb81086efde10 0xdfff0230ffffc61f 0xfefff81187fffe30

def z472 : W := mkw 0x02008a4002245903 0x00100452001122c8 0x86808bc01e7c799b 0xb434045e00f3e3cc

def z473 : W := mkw 0x68ec23fc547eca91 0xc347611fe2a3f654 0x40fc03fc007f8001 0x0207e01fe003fc00

def z474 : W := mkw 0x0021021010e1c208 0x0001081080870e10 0x8163023011e3c60f 0xdc0b1811808f1e30

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200a0c00000003 0x9001005060000000

def z476 : W := mkw 0x0000001000008200 0x0000000080000410 0x0040003000038604 0x4802000180001c30

def z477 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8143043311e3c7ec 0x4c0a1821988f1e3f

def z478 : W := mkw 0x171aedaa00000000 0x00b8d76d50000000 0x673fffff00000006 0x8339fffff8000000

def z479 : W := mkw 0x00000005000000a0 0x2000000028000005 0x00000c0f000001e0 0x000000607800000f

def z480 : W := mkw 0x1dc00000c9120000 0x00ee000006489000 0x9fc00000ffff8019 0xfcfe000007fffc00

def z481 : W := mkw 0x200010106012a600 0x8100008083009530 0x00000000e0038600 0x0800000007001c30

def z482 : W := mkw 0x1700cc0000000000 0x00b8066000000000 0x3f63fe3f00000007 0xf1fb1ff1f8000000

def z483 : W := mkw 0x9df70011dddb823c 0x24efb8008eeedc11 0xdfff0433ffff867d 0xfefff8219ffffc33

def z484 : W := mkw 0x1fdaefbf0020c2a0 0x20fed77df8010615 0x7fffffff000047e7 0xf3fffffff800023f

def z485 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x40bc8bcc007c7983 0x0205e45e6003e3cc

def z486 : W := mkw 0x1700de15ab20f7e2 0x20b806f0ad5907bf 0xbf00fe3fff807ffe 0xfdf807f1fffc03ff

def z487 : W := mkw 0x200033706036ee01 0x8100019b8301b770 0x2000f3f0e07ffe1e 0x0900079f8703fff0

def z488 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fc00ff8039f0 0xa5f807e007fc01cf

def z489 : W := mkw 0x28e1333570f3e6a8 0xa1470999ab879f35 0xb9637e3ff1e3c7ef 0xddcb1bf1ff8f1e3f

def z490 : W := mkw 0x6ac8bbfc6236ff83 0xc35645dfe311b7fc 0x38c0fbfce07fff9f 0x79c607dfe703fffc

def z491 : W := mkw 0x0001001100818228 0x2000080088040c11 0x0043003300038000 0x0002180198001c00

def z492 : W := mkw 0xdfffefeedfff599f 0x46ffff7f76fffacc 0xfffffffffffff99f 0xffffffffffffffcc

def z493 : W := mkw 0xc0250244dfff599f 0x4601281226fffacc 0x80000000fffff998 0x0c00000007ffffcc

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000e3f00000006 0x00000071f8000000

def z495 : W := mkw 0x173bcc8f10c100a8 0x20b9de6478860805 0xc73f0c0f118001e0 0x8639f860788c000f

def z496 : W := mkw 0x02298a9d10e1c2a8 0x20114c54e8870e15 0xc7ff8fff11e3c7ef 0xfe3ffc7ff88f1e3f

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000460e 0x5800000000000230

def z498 : W := mkw 0x1ffbefbf10e1c2a8 0x20ffdf7df8870e15 0x7fffffff00638007 0xf3fffffff8031c00

def z499 : W := mkw 0x173bce9f10e1c2a8 0x20b9de74f8870e15 0xc77f0e3f11e3c7ef 0xde3bf871f88f1e3f

def z500 : W := mkw 0xddf70244dfff599f 0x46efb81226fffacc 0xdfff0000fffff999 0xfefff80007ffffcc

def z501 : W := mkw 0x9fffedaa9dc9001c 0x04ffff6d54ee4800 0xffffffff1f800007 0xf7fffffff8fc0000

def z502 : W := mkw 0x1700dc0020002400 0x00b806e001000120 0x3f00fc00e0007e1e 0xf9f807e0070003f0

def z503 : W := mkw 0x08c0236000244801 0x0046011b00012240 0x38c0f3f0007c781f 0x71c6079f8003e3c0

def z504 : W := mkw 0x0021025510e5caa9 0x20010812a8872e55 0x81e38fff11ffffff 0xfc0f1c7ff88fffff

def z505 : W := mkw 0x0024000014480010 0x0001200000a24000 0xc63c00001e000000 0x8631e00000f00000

def z506 : W := mkw 0x28c033756036eea1 0xa146019bab01b775 0x38c0ffffe07fffff 0x79c607ffff03ffff

def z507 : W := mkw 0x4afeabee166c5993 0x4257f55f70b362cc 0xc6ff8bff1e7c799b 0xb637fc5ff8f3e3cc

def z508 : W := mkw 0x08e1233510e1c2a8 0x20470919a8870e15 0xb9e3ffff11e3c7ef 0xfdcf1ffff88f1e3f

def z509 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x87000c00ff807ff8 0x8c38006007fc03ff

def z510 : W := mkw 0x622cbbfc366cff93 0xc31165dfe1b367fc 0xe6bcfbfc1e7c7f9f 0xb735e7dfe0f3e3fc

def z511 : W := mkw 0x8025000054db001c 0x0401280002a6d800 0x00000000007f8000 0x000000000003fc00

def z512 : W := mkw 0x422c8acc146c4891 0x4211645660a36244 0x46bc8bcc007c0003 0xb235e45e6003e000

def z513 : W := mkw 0x422c9acc366c7d93 0x421164d661b363ec 0xfebcfbccfe7c7f9f 0xfff5e7de67f3e3fc

def z514 : W := mkw 0x0208888800000000 0x0010444440000000 0x00008bcc00000002 0x0000045e60000000

def z515 : W := mkw 0x08e1021550f3c2a8 0x20470810aa879e15 0x99e30e3ff1ffc7ff 0xfccf1871ff8ffe3f

def z516 : W := mkw 0x171acc8a00000000 0x00b8d66450000000 0x461c000000000000 0x0230e00000000000

def z517 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7ebcfbcc00000003 0xb3f5e7de60000000

def z518 : W := mkw 0x0200dc0022003542 0x001006e0011001aa 0xa100fc0011807fee 0xdd0807e0008c03ff

def z519 : W := mkw 0x1721dc00bbc1354a 0x00b90ee005de09aa 0xbf63fc00ffe3ffff 0xfdfb1fe007ff1fff

def z520 : W := mkw 0x08c0212040120000 0x0046010902009000 0x38c0f3f0e07f801f 0x79c6079f8703fc00

def z521 : W := mkw 0x9725dc00ffdb355e 0x04b92ee007fed9aa 0xbf00fc00fffffffe 0xfdf807e007ffffff

def z522 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3840f3f0e003fe06 0x49c2079f87001ff0

def z523 : W := mkw 0x422c888c16481192 0x4211644460b2408c 0xc6bc8bcc1e000183 0xb635e45e60f0000c

def z524 : W := mkw 0x28c1337160b7ee29 0xa146099b8b05bf71 0x39c3f7f3e1fffe7f 0x79ce1fbf9f0ffff3

def z525 : W := mkw 0x08c0000040120000 0x0046000002009000 0x00c00000007f8001 0x000600000003fc00

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x0163000000000001 0xd00b180000000000

def z527 : W := mkw 0x0021000010c10008 0x0001080000860800 0x8000000011e38008 0x0c000000008f1c00

def z528 : W := mkw 0x1521021599e1c2a8 0x20a90810accf0e15 0x9f630e3fffe3c7ff 0xfcfb1871ffff1e3f

def z529 : W := mkw 0x9dd36522c993000c 0x04ee9b29164c9800 0x39437433e1838004 0x49ca1ba19f0c1c00

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x0063023f00000001 0x00031811f8000000

def z531 : W := mkw 0xdfff888cdfdb119e 0x46fffc4466fed88c 0xdfff080cffff8199 0xfefff84067fffc0c

def z532 : W := mkw 0x88f7000054db001c 0x0447b80002a6d800 0xc6ff00001e7f8019 0xb637f80000f3fc00

def z533 : W := mkw 0x1fdaedaa89000000 0x00fed76d54480000 0xffffffffff80001f 0xfffffffffffc0000

def z534 : W := mkw 0x42088acc02245983 0x42104456601122cc 0x86008bcc1e00799a 0xb430045e60f003cc

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x46bc000000000001 0xb235e00000000000

def z536 : W := mkw 0x1dd2652200000000 0x00ee932910000000 0x39c3f7f300000007 0x71ce1fbf98000000

def z537 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3f00fc00ee003816 0xf1f807e0077001c0

def z538 : W := mkw 0x0020024410644881 0x0001001220832244 0x80a08bcc107c799b 0xb405045e6083e3cc

def z539 : W := mkw 0x0000000002001102 0x0000000000100088 0x800000001e007998 0x0400000000f003cc

def z540 : W := mkw 0x3fdafdba6012a600 0x81fed7edd3009530 0x7fffffffe0038607 0xfbffffffff001c30

def z541 : W := mkw 0x40240244166c5993 0x4201201220b362cc 0xc6bc00001e7c7999 0xb635e00000f3e3cc

def z542 : W := mkw 0x9df70204ddfb409c 0x04efb81026efda04 0xdfff0a0cffffc19b 0xfefff85067fffe0c

def z543 : W := mkw 0x0020020410604080 0x0001001020830204 0x8000000010604188 0x040000000083020c

def z544 : W := mkw 0x3fdafffa2024ee01 0x81fed7ffd1012770 0x7fffffff00007e07 0xf3fffffff80003f0

def z545 : W := mkw 0x002002151060c2a0 0x20010010a8830615 0x80200e3f106047ef 0x94010071f883023f

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0x01230c0f00000000 0x8009186078000000

def z547 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdf7f0000ff838000 0xcefbf80007fc1c00

def z548 : W := mkw 0x9fd3dc00eb93354e 0x04fe9ee0075c99aa 0xbf43fc00ff83fffe 0xfdfa1fe007fc1fff

def z549 : W := mkw 0x9737cc009fc9115e 0x04b9be6004fe488a 0xc73f0c001f8001e0 0x8639f86000fc000f

def z550 : W := mkw 0x002002141060c280 0x00010010a0830614 0x80600a3c1063c78f 0xdc030051e0831e3c

def z551 : W := mkw 0x6accb9e8661e3d13 0xc35665cf4330f1e8 0x7e9cf1c0ee1c3810 0x23f4e78e0770e1c0

def z552 : W := mkw 0x1721dc05bbc135ea 0x20b90ee02dde09af 0xbf23fc0fff807ffe 0xfdf91fe07ffc03ff

def z553 : W := mkw 0x5ffeffeebf6c7dd3 0x42fff7ff75fb63ee 0xfffffffffffc7fff 0xffffffffffffe3ff

def z554 : W := mkw 0x88f7000054db001c 0x0447b80002a6d800 0xc1ff000011ff8009 0xde0ff800008ffc00

def z555 : W := mkw 0x42088acc02245983 0x42104456601122cc 0x46bc8bcc00007983 0xb235e45e600003cc

def z556 : W := mkw 0x1fdaefea00244801 0x00fed77f50012240 0x7fffffff007c781f 0xf3fffffff803e3c0

def z557 : W := mkw 0x3700ff70ab24ff43 0x81b807fb855927fa 0xbf00fff0ff807ffe 0xfdf807ff87fc03ff

def z558 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x0000000000638000 0x0000000000031c00

def z559 : W := mkw 0x3fdafdea60162c01 0x81fed7ef5300b160 0x7fffffffe01c3817 0xf3ffffffff00e1c0

def z560 : W := mkw 0x402c008c14480090 0x4201600460a24004 0x403c000c00000000 0x0201e00060000000

def z561 : W := mkw 0x0221de1532e1f7ea 0x20110ef0a9970fbf 0xa163fe3f11e3ffef 0xdd0b1ff1f88f1fff

def z562 : W := mkw 0x1ffbedaa10c10008 0x00ffdf6d50860800 0xffffffff11e3800f 0xfffffffff88f1c00

def z563 : W := mkw 0x2ac8bbf86036ee01 0x815645dfc301b770 0x7efcfbfce07ffe1f 0xfbf7e7dfe703fff0

def z564 : W := mkw 0x1708fdaaab003542 0x00b847ed555801aa 0xbf00ffffff807ffe 0xfdf807fffffc03ff

def z565 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7ffff1c000000001 0xf3ffff8e00000000

def z566 : W := mkw 0x573ecc8e16481192 0x42b9f66470b2408c 0xc73f0c0f1e000180 0x8639f86078f0000c

def z567 : W := mkw 0x5ffe8acc166c5993 0x42fff45660b362cc 0xdfff8bcc1e7c799b 0xf6fffc5e60f3e3cc

def z568 : W := mkw 0xbdf73160fddf2c1d 0x85efb98b07eef960 0xfffff1c0ffffb819 0xffffff8e07fffdc0

def z569 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x80630a3f1063c18b 0x94031851f8831e0c

def z570 : W := mkw 0x42288acc12645983 0x42114456609322cc 0x80208bcc1060798b 0x9401045e608303cc

def z571 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x409c01c000000000 0x0204e00e00000000

def z572 : W := mkw 0x1721de15bbe1f7ea 0x20b90ef0addf0fbf 0xbf00fc00ffe3fffe 0xfdf807e007ff1fff

def z573 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3e00f000ee007e1e 0x79f00780077003f0

def z574 : W := mkw 0x15001000a9002400 0x00a8008005480120 0xbf00f000ff807e1e 0xfdf8078007fc03f0

def z575 : W := mkw 0x2021337530e5eea9 0xa101099ba9872f75 0xa163ffff11e3ffef 0xdd0b1ffff88f1fff

def z576 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7f9cfdc000000006 0xf3fce7ee00000000

def z577 : W := mkw 0x1500000089000000 0x00a8000004480000 0x870000001f800000 0x8438000000fc0000

def z578 : W := mkw 0x2208fffa2024ee01 0x811047ffd1012770 0x2000ffff00007e06 0x010007fff80003f0

def z579 : W := mkw 0x00001000ab003542 0x00000080055801aa 0x81000c00ff807ffe 0xdc08006007fc03ff

def z580 : W := mkw 0x170088008b001102 0x00b8044004580088 0x9f008800ff80799a 0xfcf8044007fc03cc

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000638009 0x5802000000031c00

def z582 : W := mkw 0x88f70000dddb001c 0x0447b80006eed800 0xc0ff0000ffff8019 0x0e07f80007fffc00

def z583 : W := mkw 0x000002100020c200 0x0000001080010610 0x81400e3011e3c7ef 0xdc0a0071808f1e3f

def z584 : W := mkw 0x88ff21aa54db001c 0x0447f90d52a6d800 0x40ff03ff007f8001 0x0207f81ff803fc00

def z585 : W := mkw 0x5ffeefee166c5993 0x42fff77f70b362cc 0xfebcfbcc1e7c799b 0xb7f5e7de60f3e3cc

def z586 : W := mkw 0xbdf72370ddffca1d 0x85efb91b86effe50 0xdfff03f0ffff8019 0xfefff81f87fffc00

def z587 : W := mkw 0x40241244bf6c7dd3 0x4201209225fb63ee 0x80000000fffc7ff8 0x0c00000007ffe3ff

def z588 : W := mkw 0x0200dc0022003542 0x001006e0011001aa 0xa600fc001e007ffe 0xb53007e000f003ff

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000118047e8 0x0c000000008c023f

def z590 : W := mkw 0x953700009dc9001c 0x04a9b80004ee4800 0xc77f00001fe38009 0xde3bf80000ff1c00

def z591 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7e9cffff00000006 0x23f4e7fff8000000

def z592 : W := mkw 0x0024000014480010 0x0001200000a24000 0x40bc0000007c0001 0x0205e0000003e000

def z593 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x38c0f3f0e01c3817 0x71c6079f8700e1c0

def z594 : W := mkw 0x200033702024ee01 0x8100019b81012770 0x3800f3f0e0007e1e 0x79c0079f870003f0

def z595 : W := mkw 0x3fc0ff706036ee01 0x81fe07fb8301b770 0x3fc0fff0e07ffe1f 0xf9fe07ff8703fff0

def z596 : W := mkw 0x5ffeefee146c4891 0x42fff77f70a36244 0x7fffffff007c0007 0xf3fffffff803e000

def z597 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x8163023f11e38009 0xdc0b1811f88f1c00

def z598 : W := mkw 0x570cdcc8af0c3d53 0x42b866e6457861ea 0x7e9cf1c0ee1c3810 0x23f4e78e0770e1c0

def z599 : W := mkw 0x422cefee166c5993 0x4211677f70b362cc 0xe6bcffff1e7c799f 0xb735e7fff8f3e3cc

def z600 : W := mkw 0x422d888d16c911ba 0x62116c4468b6488d 0xc73f0c0f1f8001e0 0x8639f86078fc000f

def z601 : W := mkw 0x1700cc0000000000 0x00b8066000000000 0xbf00fc00118047ee 0xfdf807e0008c023f

def z602 : W := mkw 0x08d2000000000000 0x0046900000000000 0x40ff000000000001 0x0207f80000000000

def z603 : W := mkw 0x0200980022003502 0x001004c0011001a8 0xbe00f800fe007f9e 0xfdf007c007f003fc

def z604 : W := mkw 0x15005400a9002440 0x00a802a005480122 0x3900f400e1807e7e 0x79c807a0070c03f3

def z605 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00f000ff803818 0xfdf8078007fc01c0

def z606 : W := mkw 0x0000212000000000 0x0000010900000000 0x2000f3f000000006 0x0100079f80000000

def z607 : W := mkw 0x0ac8edaa00000000 0x0056476d50000000 0x38c0ffff00000007 0x71c607fff8000000

def z608 : W := mkw 0x0001001100818228 0x2000080088040c11 0x0000000001838660 0x08000000000c1c33

def z609 : W := mkw 0x28c03370eb36ff43 0x8146019b8759b7fa 0xb8c0f3f0ffffffff 0x7dc6079f87ffffff

def z610 : W := mkw 0x1fd2fd22ab003542 0x00fe97e9155801aa 0xbf43fc33ff807ffe 0xfdfa1fe19ffc03ff

def z611 : W := mkw 0x1dd2212000000000 0x00ee910900000000 0x7ffff3f000000007 0xf3ffff9f80000000

def z612 : W := mkw 0x08e1000050d30008 0x0047080002869800 0x99e30000f1ff8019 0xfccf1800078ffc00

def z613 : W := mkw 0x0000000089000000 0x0000000004480000 0x80000000ff800018 0x0c00000007fc0000

def z614 : W := mkw 0xd73f888c9fc9119e 0x46b9fc4464fe488c 0xc73f080c1f800180 0x8639f84060fc000c

def z615 : W := mkw 0x1fdacc8a00000000 0x00fed66450000000 0x5fff0c0f00000001 0xf2fff86078000000

def z616 : W := mkw 0x200002504036ca01 0x810000128201b650 0x00000000007f8000 0x000000000003fc00

def z617 : W := mkw 0x0000000040120000 0x0000000002009000 0x00000000e07f8018 0x080000000703fc00

def z618 : W := mkw 0x9df70240ddff481d 0x04efb81206effa40 0xdfff83c0fffff81b 0xfefffc1e07ffffc0

def z619 : W := mkw 0x9df71000ffdb355e 0x04efb88007fed9aa 0xdfff0000fffffff9 0xfefff80007ffffff

def z620 : W := mkw 0x9fd6dc00ef1a3556 0x04feb6e00778d1aa 0x7e9cf000ee1c3810 0x23f4e7800770e1c0

def z621 : W := mkw 0x1708edaa00000000 0x00b8476d50000000 0x3f00ffff00000006 0xf1f807fff8000000

def z622 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfbf0000ff9c0010 0xa6fdf80007fce000

def z623 : W := mkw 0x0021000010c10008 0x0001080000860800 0x81630c0011e3c7ef 0xdc0b1860008f1e3f

def z624 : W := mkw 0x1521000099c10008 0x00a9080004ce0800 0x9f630000ffe38019 0xfcfb180007ff1c00

def z625 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x3880f1c0e01c7e1e 0x79c4078e0700e3f0

def z626 : W := mkw 0x000002150020c2a0 0x20000010a8010615 0x00000000000047e0 0x000000000000023f

def z627 : W := mkw 0x60241254767eff93 0xc3012092a3b3f7fc 0x80000000fe7fff98 0x0c00000007f3fffc

def z628 : W := mkw 0x08c0212000000000 0x0046010900000000 0x39e3ffff00000007 0xf1cf1ffff8000000

def z629 : W := mkw 0x572ccecc9f6c59d3 0x42b9667664fb62ce 0xc7bc8fcc1ffc79fb 0xb63de47e60ffe3cf

def z630 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f3f0e01c7e16 0x21c4079f8700e3f0

def z631 : W := mkw 0x9df70215ddfbc2bc 0x24efb810aeefde15 0xdfff0000ffffc7f9 0xfefff80007fffe3f

def z632 : W := mkw 0x953700059dc900bc 0x24a9b8002cee4805 0xc73f0c0f1f8001e0 0x8639f86078fc000f

def z633 : W := mkw 0x1500440000000000 0x00a8022000000000 0x3900740000000004 0x41c803a000000000

def z634 : W := mkw 0x2ac8fffa6036ee01 0x815647ffd301b770 0x38c0ffffe07ffe1f 0x79c607ffff03fff0

def z635 : W := mkw 0x0208888800000000 0x0010444440000000 0x463c080c00000000 0x8231e04060000000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040023000000007 0x5002001180000000

def z637 : W := mkw 0x2000316020042c01 0x8100018b01002160 0x2000f1c000003800 0x0100078e000001c0

def z638 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fdff5f300000004 0x63feffaf98000000

def z639 : W := mkw 0x7fecfffcff7effd3 0xc3ff67ffe7fbf7fe 0xfffcfffcffffffff 0xffffe7ffe7ffffff

def z640 : W := mkw 0x3fc0fd60eb163d43 0x81fe07eb0758b1ea 0xbf80fdc0ff9c7ffe 0xfdfc07ee07fce3ff

def z641 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38407030e07ffe1c 0x49c203818703fff0

def z642 : W := mkw 0x08c0000040120000 0x0046000002009000 0x18400000e0038000 0x48c2000007001c00

def z643 : W := mkw 0x00211215bbe1f7ea 0x20010890addf0fbf 0x80000000ffe3fff8 0x0c00000007ff1fff

def z644 : W := mkw 0x28e1337070f7ee09 0x8147099b8387bf70 0xb9e3f3f0f1fffe1f 0xfdcf1f9f878ffff0

def z645 : W := mkw 0x000012102020e600 0x0000009081010730 0x3840f230e063fe1f 0x79c2079187031ff0

def z646 : W := mkw 0x000002100020c200 0x0000001080010610 0x0000023000004606 0x0000001180000230

def z647 : W := mkw 0x42248a44166c5993 0x4211245220b362cc 0x860088001e7c799a 0xb430044000f3e3cc

def z648 : W := mkw 0x3fc0fd60eb163d43 0x81fe07eb0758b1ea 0x3e80f1c0ee1c3810 0x21f4078e0770e1c0

def z649 : W := mkw 0x9fff8888dddb001c 0x04fffc4446eed800 0xdfff8bccffff801b 0xfefffc5e67fffc00

def z650 : W := mkw 0x68e43374767eff93 0xc347219ba3b3f7fc 0xb8c0f3f0fe7fff9f 0x7dc6079f87f3fffc

def z651 : W := mkw 0x15001000ab003542 0x00a80080055801aa 0x9f000000ff807ff8 0xfcf8000007fc03ff

def z652 : W := mkw 0x1700de40ab247d43 0x00b806f2055923ea 0xbf80ffc0fffc7fff 0xfdfc07fe07ffe3ff

def z653 : W := mkw 0x5708deccab247dc3 0x42b846f6655923ee 0xbf00ffccff807ffe 0xfdf807fe67fc03ff

def z654 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x0063023f0063c60f 0x58031811f8031e30

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000c0000000006 0xd008006000000000

def z656 : W := mkw 0x0000020400204080 0x0000001020010204 0x00000a0c00004182 0x000000506000020c

def z657 : W := mkw 0x171acc8a8b001142 0x00b8d6645458008a 0xc73f0c0f1f8001e0 0x8639f86078fc000f

def z658 : W := mkw 0x1700cc008b001142 0x00b806600458008a 0x87000c001f8047ee 0xdc38006000fc023f

def z659 : W := mkw 0x9dd30000c993000c 0x04ee9800064c9800 0x19c30000e1ff8019 0x78ce1800070ffc00

def z660 : W := mkw 0x40240244166c5993 0x4201201220b362cc 0x80200a0c1e7c799b 0x9401005060f3e3cc

def z661 : W := mkw 0x0000100020002400 0x0000008001000120 0xb900fc00f1807ffe 0xfdc807e0078c03ff

def z662 : W := mkw 0x572ccecc166c5993 0x42b9667660b362cc 0xffbcffcc1e7c799f 0xf7fde7fe60f3e3cc

def z663 : W := mkw 0x1dd2000000000000 0x00ee900000000000 0x5fff0e3f00000007 0xf2fff871f8000000

def z664 : W := mkw 0x0021000510c100a8 0x2001080028860805 0x81230c0f118047ee 0xdc091860788c023f

def z665 : W := mkw 0x1700cc0000000000 0x00b8066000000000 0x07000c0000000000 0x8038006000000000

def z666 : W := mkw 0x1fc0fd20ab003542 0x00fe07e9055801aa 0xbfc0fff0ff807fff 0xfdfe07ff87fc03ff

def z667 : W := mkw 0xbff7ff70ffffff5f 0x85ffbffb87fffffa 0xfffffff0ffffffff 0xffffffff87ffffff

def z668 : W := mkw 0x2ac0ff706236ff43 0x815607fb8311b7fa 0x38c0fff0e07fffff 0x79c607ff8703ffff

def z669 : W := mkw 0x1fdafdaaab003542 0x00fed7ed555801aa 0x7fffffffee003817 0xf3ffffffff7001c0

def z670 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0x3f00f400ef803e74 0x69f807a0077c01f3

def z671 : W := mkw 0x953700009dc9001c 0x04a9b80004ee4800 0xc7bf00001ffc0019 0xb63df80000ffe000

def z672 : W := mkw 0x28e43370747eee11 0x8147219b83a3f770 0xfefcf3f0fe7ffe1f 0xfff7e79f87f3fff0

def z673 : W := mkw 0x3fc0ff70eb36ff43 0x81fe07fb8759b7fa 0x3ec0f3f0ee7ffe1f 0x79f6079f8773fff0

def z674 : W := mkw 0x0008008800000000 0x0000400440000000 0x40bc03cc00000001 0x0205e01e60000000

def z675 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x80200a0c11e3c7eb 0x9c010050608f1e3f

def z676 : W := mkw 0x1700cc0000000000 0x00b8066000000000 0x3e00f00000000000 0x21f0078000000000

def z677 : W := mkw 0x9fd6dc00ef1a3556 0x04feb6e00778d1aa 0xff9cfc00ff9c7ffe 0xfffce7e007fce3ff

def z678 : W := mkw 0x3fc0fd30eb12b742 0x81fe07e9875895ba 0xbf40fc30ff83fffe 0xfdfa07e187fc1fff

def z679 : W := mkw 0x200033752024eea1 0xa100019ba9012775 0x2000ffff00007fe6 0x010007fff80003ff

def z680 : W := mkw 0x200023700024ca01 0x8100011b80012650 0x000003f000000000 0x0000001f80000000

def z681 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc63c080c1e7c7998 0x8631e04060f3e3cc

def z682 : W := mkw 0x3fdafffaeb36ff43 0x81fed7ffd759b7fa 0xffffffffffffffff 0xffffffffffffffff

def z683 : W := mkw 0x9df75400fddb245c 0x04efbaa007eed922 0xffff7400ffff867d 0xfffffba007fffc33

def z684 : W := mkw 0x402d02dd14edcab9 0x62016816e8a76e55 0xc1ff0fff11ffc7ef 0xde0ff87ff88ffe3f

def z685 : W := mkw 0x28c031306012a600 0x8146018983009530 0x3840f030e003fe1e 0x79c2078187001ff0

def z686 : W := mkw 0x4208efee02245983 0x4210477f701122cc 0x2000ffff00007986 0x010007fff80003cc

def z687 : W := mkw 0x3fe1ff75fbf7ffeb 0xa1ff0ffbafdfbfff 0xbfe3ffffffffffff 0xfdff1fffffffffff

def z688 : W := mkw 0x422c8a8c16685192 0x4211645460b3428c 0xc63c0a0c1e60418b 0x9631e05060f3020c

def z689 : W := mkw 0x3dd233706036ee01 0x81ee919b8301b770 0x7ffff3f0e07ffe1f 0xfbffff9f8703fff0

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x860000001e000018 0xb430000000f00000

def z691 : W := mkw 0x80250215ddfbc2bc 0x24012810aeefde15 0x81630e3fffffc7ff 0xdc0b1871fffffe3f

def z692 : W := mkw 0x0020000410400080 0x0001000020820004 0x8020080c10000180 0x840100406080000c

def z693 : W := mkw 0x02208a0412605182 0x001104502093028c 0x86208a0c1e60799b 0xb431045060f303cc

def z694 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7edcf3f000000007 0x73f6e79f80000000

def z695 : W := mkw 0x0000124020246c01 0x0000009201012360 0x3880f3c0e07c7e1f 0x79c4079e0703e3f0

def z696 : W := mkw 0x0000652200000000 0x0000032910000000 0x2000743300000004 0x010003a198000000

def z697 : W := mkw 0x0000100022003542 0x00000080011001aa 0x0000000000007fe0 0x00000000000003ff

def z698 : W := mkw 0x200033702024ee01 0x8100019b81012770 0x2080f3f0007c7e1f 0x3104079f8003e3f0

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x0143043300000004 0x400a182198000000

def z700 : W := mkw 0x28c023704036ca01 0x8146011b8201b650 0x18c003f0e07f8019 0x78c6001f8703fc00

def z701 : W := mkw 0x0024020414684090 0x0001201020a34204 0xc6bc0a0c1e7c419b 0xb635e05060f3e20c

def z702 : W := mkw 0x0208edaa00000000 0x0010476d50000000 0x2163ffff00000007 0xd10b1ffff8000000

def z703 : W := mkw 0xd73f8acc9fed599f 0x46b9fc5664ff6acc 0xc7bf8bcc1ffc799b 0xb63dfc5e60ffe3cc

def z704 : W := mkw 0x9fdbedaac993000c 0x04fedf6d564c9800 0x7fffffffe1838007 0xfbffffffff0c1c00

def z705 : W := mkw 0x88e50000dddb001c 0x0447280006eed800 0x98c00000ffff8019 0x7cc6000007fffc00

def z706 : W := mkw 0x1fc0ed2000000000 0x00fe076900000000 0x3fc0fff000000007 0xf1fe07ff80000000

def z707 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfdf0000ffff8018 0x6efef80007fffc00

def z708 : W := mkw 0x1fdaedaa8b001142 0x00fed76d5458008a 0xffffffff1f8079ff 0xf7fffffff8fc03cf

def z709 : W := mkw 0x552c56ccbd6c6cd1 0x42a962b665eb6366 0x79bc77cce1fc0665 0x4bcde3be670fe033

def z710 : W := mkw 0x5df66766166c5993 0x42efb33b30b362cc 0xb94374331e7c799c 0x45ca1ba198f3e3cc

def z711 : W := mkw 0x422d88c816cd191b 0x42116c4640b668c8 0xc7ff81c01fffb819 0xfe3ffc0e00fffdc0

def z712 : W := mkw 0xb5373370bdedee1d 0x85a9b99b85ef6f70 0xe73ff3f01f807e06 0x8739ff9f80fc03f0

def z713 : W := mkw 0x000012502024ee01 0x0000009281012770 0x38c0f3f0e07ffe1f 0x79c6079f8703fff0

def z714 : W := mkw 0x28c0336060366c01 0x8146019b0301b360 0x38c0f3c0e07ff81b 0x79c6079e0703ffc0

def z715 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc69c83c01e7c799b 0x3634e41e00f3e3cc

def z716 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdf7f0000ffff8018 0xcefbf80007fffc00

def z717 : W := mkw 0x0025021514e9c2b8 0x20012810a8a74e15 0x81630e3f1fffc7ff 0xdc0b1871f8fffe3f

def z718 : W := mkw 0x9df76522dddb001c 0x04efbb2916eed800 0xffff7000ffff8019 0xfffffb8007fffc00

def z719 : W := mkw 0x88f7000054db001c 0x0447b80002a6d800 0xdeff0000fe7f8019 0xfef7f80007f3fc00

def z720 : W := mkw 0xbdd37532e993a60c 0x85ee9ba9974c9d30 0x39437433e1838604 0x49ca1ba19f0c1c30

def z721 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x46bc83cc0e7c781b 0x3235e41e6073e3c0

def z722 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xb9c0f3f0f1fffe1f 0xfdce079f878ffff0

def z723 : W := mkw 0x0021001510c182a8 0x20010800a8860c15 0x81630e3f118387e7 0xdc0b1871f88c1c3f

def z724 : W := mkw 0x9df72122dddb001c 0x04efb90916eed800 0xdfff0033ffff8019 0xfefff8019ffffc00

def z725 : W := mkw 0x95250000dddb001c 0x04a9280006eed800 0xdfbc0000ffff8019 0xfefde00007fffc00

def z726 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0xffffffff1180000f 0xfffffffff88c0000

def z727 : W := mkw 0x28c031706016ae01 0x8146018b8300b570 0x38c0f1f0e07fbe1d 0x79c6078f8703fdf0

def z728 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7bf8fff1ffc7fff 0xb63dfc7ff8ffe3ff

def z729 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c81c00e7c3819 0x3234e40e0073e1c0

def z730 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc6bf8bcf1e7c799b 0xb635fc5e78f3e3cc

def z731 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x47ff8fff0e1c3817 0xf23ffc7ff870e1c0

def z732 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdedc0000ffff8019 0x7ef6e00007fffc00

def z733 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0x469c8bcc0e7c799b 0x3234e45e6073e3cc

def z734 : W := mkw 0x420d88d9068d9b3b 0x62106c46c8346cd9 0x47df85f30f9fbe74 0x6a3efc2f987cfdf3

def z735 : W := mkw 0x9df76522dddb001c 0x04efbb2916eed800 0xffff7e3fffff801f 0xfffffbf1fffffc00

def z736 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07ff81b 0x31c6079f8703ffc0

def z737 : W := mkw 0x28c033716036ee21 0xa146019b8b01b771 0x38c0f7f3e07ffe7f 0x79c607bf9f03fff3

def z738 : W := mkw 0x15005400ab003542 0x00a802a0055801aa 0xb9007c00ff807ffe 0xddc803e007fc03ff

def z739 : W := mkw 0x9dd60215cd3ac2b4 0x24eeb010ae69d615 0x5e9c0e3fee1c47f6 0x22f4e071ff70e23f

def z740 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f1c0e07fb810 0x21c4078e0703fdc0

def z741 : W := mkw 0x1de40000dd5a0010 0x00ef200006ead000 0xdffc0000ffff8019 0xfeffe00007fffc00

def z742 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81e38fff11e3c7ef 0xfc0f1c7ff88f1e3f

def z743 : W := mkw 0x6208fffe2224ff83 0xc31047fff11127fc 0x2000ffff00007f86 0x010007fff80003fc

def z744 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff0063800f 0xfbfffffff8031c00

def z745 : W := mkw 0xbdd33120e993240c 0x85ee9989074c9920 0x39437000e1838000 0x49ca1b80070c1c00

def z746 : W := mkw 0x000002100020c200 0x0000001080010610 0x81630e3f11e3c7ef 0xdc0b1871f88f1e3f

def z747 : W := mkw 0x1fdaedaac9120000 0x00fed76d56489000 0xffffffffffff801f 0xfffffffffffffc00

def z748 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0xffffffff118001e7 0xf7fffffff88c000f

def z749 : W := mkw 0x1ffbefbf10e1c2a8 0x20ffdf7df8870e15 0xfe9cf1c011e3c7e8 0x2ff4e78e008f1e3f

def z750 : W := mkw 0x420c8ad8062cdb13 0x42106456c03166d8 0x46dc83f00e7ffe1f 0x7a36e41f8073fff0

def z751 : W := mkw 0x0200dc00ab003542 0x001006e0055801aa 0xb800fc00ff807ffe 0x7dc007e007fc03ff

def z752 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0000ffffc61f 0xfefff80007fffe30

def z753 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fbfffff00000006 0xa3fdfffff8000000

def z754 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0433ffff801d 0xfefff8219ffffc00

def z755 : W := mkw 0x422d88cd16cd19bb 0x62116c4668b668cd 0xc7bf8dcf1f9c39f0 0xa63dfc6e78fce1cf

def z756 : W := mkw 0x1721de15bbe1f7ea 0x20b90ef0addf0fbf 0x3e63f23fee63b811 0x21f31f91ff731dc0

def z757 : W := mkw 0x08c40000441a0010 0x004620000220d000 0x5edc0000ee7f8019 0x7af6e0000773fc00

def z758 : W := mkw 0x15005400ab003542 0x00a802a0055801aa 0xb900f400ff807ffe 0x7dc807a007fc03ff

def z759 : W := mkw 0x08e5000054db0018 0x0047280002a6d800 0xdfff0000ffff8019 0xfefff80007fffc00

def z760 : W := mkw 0x1fdaedaa02001102 0x00fed76d50100088 0xffffffff1f807fff 0xfffffffff8fc03ff

def z761 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc7ff8fff1ffc79ff 0xf63ffc7ff8ffe3cf

def z762 : W := mkw 0x9df70005dddb00bc 0x24efb8002eeed805 0xdfff0e3fffff81ff 0xfefff871fffffc0f

def z763 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fc00ff807ff6 0xa5f807e007fc03ff

def z764 : W := mkw 0x0ac8a9a800000000 0x0056454d40000000 0x7fffffff00000007 0xf3fffffff8000000

def z765 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x38c0f1c0e07fb811 0x21c6078e0703fdc0

def z766 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf80fc00fffc7fff 0xfdfc07e007ffe3ff

def z767 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0xc6bc89c01e7c799b 0xb635e44e00f3e3cc

def z768 : W := mkw 0xbdd23120e9122404 0x85ee918907489120 0x38007000e0000000 0x01c0038007000000

def z769 : W := mkw 0xdfdb8acccbb7598f 0x46fedc56665dbacc 0x19438bcce183f982 0x48ca1c5e670c1fcc

def z770 : W := mkw 0x0001021500a1c2a8 0x20000810a8050e15 0x01630e3f0183c7e7 0xd80b1871f80c1e3f

def z771 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x5eff0000ee7f8019 0x7af7f8000773fc00

def z772 : W := mkw 0x08da65aa00000000 0x0046d32d50000000 0x60ff77ff00000005 0x0307fbbff8000000

def z773 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc89cc1e7c7998 0xa635e44e60f3e3cc

def z774 : W := mkw 0x15005400ab003542 0x00a802a0055801aa 0xb8007000ff807ff8 0x0dc0038007fc03ff

def z775 : W := mkw 0x022c8ac8146c4811 0x0011645640a36240 0xc6bc8bcc1e7c781b 0xb635e45e60f3e3c0

def z776 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f11e3c7e9 0x8c0b1871f88f1e3f

def z777 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7ffff3ff00000001 0xf3ffff9ff8000000

def z778 : W := mkw 0x420c8add062cdbb3 0x62106456e83166dd 0x469c8fff0e1c7ff6 0x2234e47ff870e3ff

def z779 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fff7fff00000005 0xc3fffbfff8000000

def z780 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1ffc7ffb 0xbe35e45e60ffe3ff

def z781 : W := mkw 0x9df70005dddb00bc 0x24efb8002eeed805 0xdfff0000ffff81f9 0xfefff80007fffc0f

def z782 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x469c81c00e7c3810 0x2234e40e0073e1c0

def z783 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7ffff7ff00000005 0x63ffffbff8000000

def z784 : W := mkw 0x95370000dddb001c 0x04a9b80006eed800 0xdf3f0000ffff8018 0xfef9f80007fffc00

def z785 : W := mkw 0xbdd23130e912a604 0x85ee918987489530 0x38407030e0038604 0x49c2038187001c30

def z786 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x79ffffff00000007 0xf3cffffff8000000

def z787 : W := mkw 0xbdd33131e993a62c 0xa5ee99898f4c9d31 0x39437433e1838664 0x49ca1ba19f0c1c33

def z788 : W := mkw 0x00240040144c0811 0x0001200200a26040 0xc6bc81c01e7c3819 0xb635e40e00f3e1c0

def z789 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xb9e3fffff1ffffff 0xfdcf1fffff8fffff

def z790 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc7ff8fff1e7c7fff 0xf63ffc7ff8f3e3ff

def z791 : W := mkw 0x28c033756036eea1 0xa146019bab01b775 0x38c0f3f0e07fffff 0x79c6079f8703ffff

def z792 : W := mkw 0x0021000010c10008 0x0001080000860800 0x81630e3f11e3c7ef 0xdc0b1871f88f1e3f

def z793 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5edc0000ee7f8011 0x22f6e0000773fc00

def z794 : W := mkw 0x371adeda6036ee01 0x81b8d6f6d301b770 0x473f0c0fe07ffe18 0x8a39f8607f03fff0

def z795 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81430e3f11e3c7ee 0x4c0a1871f88f1e3f

def z796 : W := mkw 0x00001000ab003542 0x00000080055801aa 0xb900fc00ff807ffe 0xfdc807e007fc03ff

def z797 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6fc8bcc1e7ff99b 0xfe37e45e60f3ffcc

def z798 : W := mkw 0x88f70000dddb001c 0x0447b80006eed800 0xc6ff0000ffff8019 0xbe37f80007fffc00

def z799 : W := mkw 0x1708dc88ab003542 0x00b846e4455801aa 0xffffffffff807fff 0xfffffffffffc03ff

def z800 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc7bf8fcf1ffc7fff 0xfe3dfc7e78ffe3ff

def z801 : W := mkw 0x6aecb9bc765ab792 0xc35765cde3b2d5bc 0xfe7c783cfe038784 0xcff3e3c1e7f01c3c

def z802 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630c3f11e3c7ec 0xcc0b1861f88f1e3f

def z803 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc81c01e7c7999 0xb635e40e00f3e3cc

def z804 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf40fe30ff807fff 0xfdfa07f187fc03ff

def z805 : W := mkw 0x9df76522dddb001c 0x04efbb2916eed800 0xfffff7f3ffff801f 0xffffffbf9ffffc00

def z806 : W := mkw 0x1dda65aa00000000 0x00eed32d50000000 0x78ff73ff00000001 0x03c7fb9ff8000000

def z807 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x99630e3ff1e3c7ff 0xfccb1871ff8f1e3f

def z808 : W := mkw 0x422ccecc166c59d3 0x4211667660b362ce 0xc6bc8fcc1e7c79fb 0xb635e47e60f3e3cf

def z809 : W := mkw 0x021aedaa00000000 0x0010d76d50000000 0x603fffff00000006 0x0301fffff8000000

def z810 : W := mkw 0x0025025514edcab9 0x20012812a8a76e55 0xc7ff8fff1fffffff 0xfe3ffc7ff8ffffff

def z811 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x60fff3ff00000007 0x0307ff9ff8000000

def z812 : W := mkw 0x0adaedaa00000000 0x0056d76d50000000 0x61ffffff00000007 0xd30ffffff8000000

def z813 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6ff8bff1e7fff9f 0xfe37fc5ff8f3fffc

def z814 : W := mkw 0x1dd20000c9120000 0x00ee900006489000 0xdfff0000ffff8019 0xfefff80007fffc00

def z815 : W := mkw 0x822dedaadddb001c 0x04116f6d56eed800 0xa000ffffffff801e 0x0d0007fffffffc00

def z816 : W := mkw 0x3fc0ef70cb36db43 0x81fe077b8659b6da 0x87c00ff01fff81e1 0x843e007f80fffc0f

def z817 : W := mkw 0x572dcc8d9fc911fa 0x62b96e646cfe488f 0xc73f0c0f1f8001e0 0x8639f86078fc000f

def z818 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00f000ff807ff8 0xfdf8078007fc03ff

def z819 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0xc6bc89cc1e7c3999 0xb635e44e60f3e1cc

def z820 : W := mkw 0x08c0312060122400 0x0046018903009120 0x38c0f3f0e07ffe1f 0x79c6079f8703fff0

def z821 : W := mkw 0x0208edaa00000000 0x0010476d50000000 0x67ffffff00000007 0xf33ffffff8000000

def z822 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xb8c0fbf0f07fff9f 0xfdc607df8783fffc

def z823 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0000ffff8011 0xa6fff80007fffc00

def z824 : W := mkw 0x171adc8aab003542 0x00b8d6e4555801aa 0xff7ffe3fff807fff 0xfffbfff1fffc03ff

def z825 : W := mkw 0x08da31aaab003542 0x0046d18d555801aa 0xc0ff03ffff807ff9 0x0e07f81ffffc03ff

def z826 : W := mkw 0x1dda21aa00000000 0x00eed10d50000000 0x7ffff3ff00000007 0xf3ffff9ff8000000

def z827 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00f400ff807ffc 0x6df807a007fc03ff

def z828 : W := mkw 0x152500009dc90018 0x00a9280004ee4800 0xdfff0000ffff8019 0xfefff80007fffc00

def z829 : W := mkw 0x1708dc88ab003542 0x00b846e4455801aa 0xff9cfdc0ff807ffe 0xfffce7ee07fc03ff

def z830 : W := mkw 0x1fdaedaa89000000 0x00fed76d54480000 0xffffffff1f800007 0xf7fffffff8fc0000

def z831 : W := mkw 0x8af7dc0076db355e 0x0457bee003b6d9aa 0x60fffc00007fffe7 0x0307ffe00003ffff

def z832 : W := mkw 0x0021001510c182a8 0x20010800a8860c15 0x81630c3f11e387ed 0xdc0b1861f88f1c3f

def z833 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7f7fffff00000006 0xc3fbfffff8000000

def z834 : W := mkw 0x1708cc8800000000 0x00b8466440000000 0x7fffffff00000007 0xf3fffffff8000000

def z835 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xbec0f3f0fe7ffe1f 0xfdf6079f87f3fff0

def z836 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0x46bc81c00e7c3811 0x2235e40e0073e1c0

def z837 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7bc8fcc1ffc79fb 0xb63de47e60ffe3cf

def z838 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x46bc8bcc0e7c7993 0x2235e45e6073e3cc

def z839 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f3c0e07ffe1b 0x39c4079e0703fff0

def z840 : W := mkw 0x1fdaedaa40120000 0x00fed76d52009000 0x7fffffffe0038007 0xfbffffffff001c00

def z841 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0000ffff8001 0xcefff80007fffc00

def z842 : W := mkw 0xa0251255fdffeebd 0xa5012892afefff75 0x80000000fffffff8 0x0c00000007ffffff

def z843 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff8000fffff81b 0xfefffc0007ffffc0

def z844 : W := mkw 0x1fdaedaa40120000 0x00fed76d52009000 0x7fffffff007f8007 0xf3fffffff803fc00

def z845 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc69c81c01e1c3818 0xb634e40e00f0e1c0

def z846 : W := mkw 0x40251255bfedfffb 0x62012892adff6fff 0x80000000fffffff8 0x0c00000007ffffff

def z847 : W := mkw 0x9df70005dddb00bc 0x24efb8002eeed805 0xdfff0c0fffffc7ff 0xfefff8607ffffe3f

def z848 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0xffffffff1e00001f 0xf7fffffff8f00000

def z849 : W := mkw 0x28c033756036eea1 0xa146019bab01b775 0xb9c0fffff1ffffff 0xfdce07ffff8fffff

def z850 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7ff8bcc1ffffffb 0xfe3ffc5e60ffffff

def z851 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc6fc8bfc1e7ff99b 0xb637e45fe0f3ffcc

def z852 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0xc69c8bcc1e1c799a 0xb634e45e60f0e3cc

def z853 : W := mkw 0x00040240042c4811 0x0000201200216240 0x469c83c00e7c781b 0x3234e41e0073e3c0

def z854 : W := mkw 0x0adaedaa00000000 0x0056d76d50000000 0x78ffffff00000007 0x73c7fffff8000000

def z855 : W := mkw 0x1fdaedaa89000000 0x00fed76d54480000 0xffffffffff8047ff 0xfffffffffffc023f

def z856 : W := mkw 0x1708dc88ab003542 0x00b846e4455801aa 0xbf00ffccff807ffe 0xfdf807fe67fc03ff

def z857 : W := mkw 0x0200980022003502 0x001004c0011001a8 0xbf00fc00ff807ffe 0xfdf807e007fc03ff

def z858 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0xc69c0000ffff8018 0x2e34e00007fffc00

def z859 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38e3f3ffe07ffe1f 0x79c71f9fff03fff0

def z860 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc6bc8bcc1ffff99b 0xbe35e45e60ffffcc

def z861 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f11e3c7e7 0x840b1871f88f1e3f

def z862 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1e7c7983 0x8635e45e60f3e3cc

def z863 : W := mkw 0x0001021500a1c2a8 0x20000810a8050e15 0x01430e3f01e3c7ef 0x580a1871f80f1e3f

def z864 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x39c0fff0e07ffe1f 0xf9ce07ff8703fff0

def z865 : W := mkw 0x200033706036ee01 0x8100019b8301b770 0x3800f3f0e07ffe1e 0x79c0079f8703fff0

def z866 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff83c0ffff801b 0xfefffc1e07fffc00

def z867 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf80ffc0ff807fff 0xfdfc07fe07fc03ff

def z868 : W := mkw 0x0025021514e9c2b8 0x20012810a8a74e15 0xc77f0e3f1fe3c7ef 0xde3bf871f8ff1e3f

def z869 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0x469c83c00e1c7812 0x2234e41e0070e3c0

def z870 : W := mkw 0x1dda65aa00000000 0x00eed32d50000000 0x7fff77ff00000005 0xf3fffbbff8000000

def z871 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0xc63c0000ffff8018 0x8e31e00007fffc00

def z872 : W := mkw 0x1dda65aa00000000 0x00eed32d50000000 0x79ff7fff00000007 0xd3cffbfff8000000

def z873 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xfffff000ffff801f 0xffffff8007fffc00

def z874 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5e9c0000ee7f8018 0x2af4e0000773fc00

def z875 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7ff8fff1e7ff99f 0xf63ffc7ff8f3ffcc

def z876 : W := mkw 0x80250000dddb001c 0x0401280006eed800 0xc7ff0000ffff8019 0xfe3ff80007fffc00

def z877 : W := mkw 0x00010015008182a8 0x20000800a8040c15 0x01430c3f018387e4 0x480a1861f80c1c3f

def z878 : W := mkw 0x28d233706036ee01 0x8146919b8301b770 0x78fff3f0e07ffe1f 0x7bc7ff9f8703fff0

def z879 : W := mkw 0x1fdaedaa02001102 0x00fed76d50100088 0xffffffff1e000187 0xf7fffffff8f0000c

def z880 : W := mkw 0x6025125576ffffbb 0xe3012892abb7fffd 0x80000000fffffff8 0x0c00000007ffffff

def z881 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc6bc8bcc1e7c7ffb 0xb635e45e60f3e3ff

def z882 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x87630e3f1fe3c7ff 0xfc3b1871f8ff1e3f

def z883 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c8bcc0e1c3812 0x2234e45e6070e1c0

def z884 : W := mkw 0x9df72120dddb001c 0x04efb90906eed800 0xffffffffffff801f 0xfffffffffffffc00

def z885 : W := mkw 0x171adc8aab003542 0x00b8d6e4555801aa 0xffbfffcfff807fff 0xfffdfffe7ffc03ff

def z886 : W := mkw 0x6208bbf82224ff03 0xc31045dfc11127f8 0x2000f3f000007e06 0x0100079f800003f0

def z887 : W := mkw 0x0adaedaa00000000 0x0056d76d50000000 0x66ffffff00000007 0xb337fffff8000000

def z888 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbe00f800ff807ffa 0xbdf007c007fc03ff

def z889 : W := mkw 0x1fdaedaa89000000 0x00fed76d54480000 0x7fffffffee000017 0xf3ffffffff700000

def z890 : W := mkw 0x68ed23fd54ffcab9 0xe347691feaa7fe55 0x40ff03ff007f8001 0x0207f81ff803fc00

def z891 : W := mkw 0x3dd27532e912a640 0x81ee93a997489532 0x39437433e1838664 0x49ca1ba19f0c1c33

def z892 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xdebc8bccfe7c799b 0xfef5e45e67f3e3cc

def z893 : W := mkw 0x1fdaedaa89000000 0x00fed76d54480000 0x7fffffffe1800007 0xfbffffffff0c0000

def z894 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0c00ffff81f9 0xfefff86007fffc0f

def z895 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc6bc8bcc1e7fff9b 0xbe35e45e60f3fffc

def z896 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbe00fc00ff807ffe 0x2df007e007fc03ff

def z897 : W := mkw 0xd73fcc8c9fc911de 0x46b9fe6464fe488e 0xc73f0c0c1f8001e0 0x8639f86060fc000f

def z898 : W := mkw 0x171aedaa00000000 0x00b8d76d50000000 0x67bfffff00000007 0xb33dfffff8000000

def z899 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0x46ff83ff0e7fb811 0x2237fc1ff873fdc0

def z900 : W := mkw 0x9df72120dddb001c 0x04efb90906eed800 0xfffff1c0ffff8019 0xffffff8e07fffc00

def z901 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0xb8c0f3f0f1ffffff 0x7dc6079f878fffff

def z902 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc6bc8bcc1e1c799b 0xb635e45e60f0e3cc

def z903 : W := mkw 0x1fdaedaa02001102 0x00fed76d50100088 0x7fffffff0e003817 0xf3fffffff87001c0

def z904 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc7ff8fcc1fffffff 0xfe3ffc7e60ffffff

def z905 : W := mkw 0x9df70004dddb009c 0x04efb80026eed804 0xdfff080cffff8199 0xfefff84067fffc0c

def z906 : W := mkw 0x0025025014edca19 0x0001281280a76e50 0xc7ff83f01ffffe1f 0xfe3ffc1f80fffff0

def z907 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffffe000001f 0xfbffffffff000000

def z908 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf20fe0cff807fff 0xfdf907f067fc03ff

def z909 : W := mkw 0xbdf33330f9f3e60c 0x85ef999987cf9f30 0xb9637230f1e3c60f 0xddcb1b91878f1e30

def z910 : W := mkw 0x1708dc88ab003542 0x00b846e4455801aa 0xff3cfc0cff807ffe 0xfff9e7e067fc03ff

def z911 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x7efcf3f0e07ffe1f 0xfbf7e79f8703fff0

def z912 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff007c001f 0xf3fffffff803e000

def z913 : W := mkw 0x9dd37522e993244c 0x04ee9ba9174c9922 0x39437433e1838664 0x49ca1ba19f0c1c33

def z914 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c83c00e1c3813 0x3234e41e0070e1c0

def z915 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc7fc8ffc1fffffff 0xfe3fe47fe0ffffff

def z916 : W := mkw 0x62089adc2224ff83 0xc31044d6e11127fc 0x00008bcc00007f82 0x0000045e600003fc

def z917 : W := mkw 0x28c033756036eea1 0xa146019bab01b775 0x38c0f3ffe07ffe1f 0x79c6079fff03fff0

def z918 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdebc0000ffff8019 0xbef5e00007fffc00

def z919 : W := mkw 0x9fdaedaac9120004 0x04fed76d56489000 0x7fffffffe0000007 0xf3ffffffff000000

def z920 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0x469c83cc0e1c3810 0x2234e41e6070e1c0

def z921 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xffbcfc00ff807fff 0xfffde7e007fc03ff

def z922 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0xdfdc0000ffff8019 0xfefee00007fffc00

def z923 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6fc8bfc1fffffff 0xfe37e45fe0ffffff

def z924 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f1c0e07ffe1e 0x79c4078e0703fff0

def z925 : W := mkw 0x4025025514edcab9 0x62012812a8a76e55 0x81630e3f11ffc7ef 0xdc0b1871f88ffe3f

def z926 : W := mkw 0x2208fffa2224ff43 0x811047ffd11127fa 0x2000ffff00007fe6 0x010007fff80003ff

def z927 : W := mkw 0x0001021500a1c2a8 0x20000810a8050e15 0x81430e3f1183c7ee 0xdc0a1871f88c1e3f

def z928 : W := mkw 0x00001000ab003542 0x00000080055801aa 0xb8007000ff807ffc 0x4dc0038007fc03ff

def z929 : W := mkw 0x9df74400dddb001c 0x04efba2006eed800 0xffff7400ffff801d 0xfffffba007fffc00

def z930 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xc7ff0000ffff8019 0x8e3ff80007fffc00

def z931 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8fcc1e7c7fff 0xb635e47e60f3e3ff

def z932 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x79ffffff00000007 0x43cffffff8000000

def z933 : W := mkw 0x1fdaedaa8b001102 0x00fed76d54580088 0xffffffffff80799f 0xfffffffffffc03cc

def z934 : W := mkw 0x15001000ab003542 0x00a80080055801aa 0xbf00f000ff807ffe 0xfdf8078007fc03ff

def z935 : W := mkw 0x1dd2212000000000 0x00ee910900000000 0x7fffffff00000007 0xf3fffffff8000000

def z936 : W := mkw 0x1712dc02ab003542 0x00b896e0155801aa 0xbf03fc03ff807ffe 0xfdf81fe01ffc03ff

def z937 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff0000460f 0xfbfffffff8000230

def z938 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x38c0f1c0e07ffe1f 0x79c6078e0703fff0

def z939 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x39c0f7f0e1fffe7f 0x79ce07bf870ffff3

def z940 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7ff8bcc1e7c799b 0xf63ffc5e60f3e3cc

def z941 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0xc6bc81c01e1c3810 0xa635e40e00f0e1c0

def z942 : W := mkw 0x4208dedd2224ffe3 0x621046f6e91127ff 0x2000ffff00007fe6 0x010007fff80003ff

def z943 : W := mkw 0x6208bbfd2224ffa3 0xe31045dfe91127fd 0x2000ffff00007fe6 0x010007fff80003ff

def z944 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fe3fff807ffe 0xfdf807f1fffc03ff

def z945 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f1c0e07ffe19 0x79c6078e0703fff0

def z946 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1e1c7992 0xa635e45e60f0e3cc

def z947 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3840f3f0e07ffe1e 0x49c2079f8703fff0

def z948 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7efff3ff00000007 0x73f7ff9ff8000000

def z949 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc6ff8bcc1e7ff99b 0xb637fc5e60f3ffcc

def z950 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0e3fffffc7ff 0xfefff871fffffe3f

def z951 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc69c89c01e1c3990 0xa634e44e00f0e1cc

def z952 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff000047e7 0xf3fffffff800023f

def z953 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x38c0f3f0e07fb81f 0x79c6079f8703fdc0

def z954 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6bc8bcc1e7ff99b 0xb635e45e60f3ffcc

def z955 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x46bc89cc0e1c3810 0xa235e44e6070e1c0

def z956 : W := mkw 0xd73fcc8e9fc9119e 0x46b9fe6474fe488c 0xc73f0c0f1f800180 0x8639f86078fc000c

def z957 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdeff0000ffff8019 0x2ef7f80007fffc00

def z958 : W := mkw 0x3fdafdeaeb163d43 0x81fed7ef5758b1ea 0x7e9cf1c0ee1c3810 0x23f4e78e0770e1c0

def z959 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7bf8fcf1ffffffb 0xbe3dfc7e78ffffff

def z960 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07fb819 0x79c6079f8703fdc0

def z961 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc6bc8bcc1ffc79fb 0xb635e45e60ffe3cf

def z962 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7bc8bcc1ffc799b 0xfe3de45e60ffe3cc

def z963 : W := mkw 0x28e1316570d72ca9 0xa147098b2b86b965 0xb9a3fdcff19c39f0 0xa5cd1fee7f8ce1cf

def z964 : W := mkw 0x402c02cc166c5993 0x4201601660b362cc 0xc6bc03cc1e7c7999 0xb635e01e60f3e3cc

def z965 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf007c00ff807ffc 0xcdf803e007fc03ff

def z966 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6ff8bff1ffffffb 0xbe37fc5ff8ffffff

def z967 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff00000001 0xa3fffffff8000000

def z968 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x46bc83cc0e1c3811 0x2235e41e6070e1c0

def z969 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0000ffffc7f9 0xfefff80007fffe3f

def z970 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0x469c83c00e7c3811 0x2234e41e0073e1c0

def z971 : W := mkw 0x422d8acd16ed59bb 0x62116c5668b76acd 0xc7ff8fcf1ffff9fb 0xfe3ffc7e78ffffcf

def z972 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0800ffffc19b 0xfefff84007fffe0c

def z973 : W := mkw 0x171aedaa00000000 0x00b8d76d50000000 0x677fffff00000007 0xd33bfffff8000000

def z974 : W := mkw 0x9fdefdaaef1a3556 0x04fef7ed5778d1aa 0x7e9cf1c0ee1c3810 0x23f4e78e0770e1c0

def z975 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0xc69c81c01e1c3990 0x2634e40e00f0e1cc

def z976 : W := mkw 0x00001000ab003542 0x00000080055801aa 0xb800f000ff807ff8 0x2dc0078007fc03ff

def z977 : W := mkw 0x95370000dddb001c 0x04a9b80006eed800 0xc7bf0000ffff8019 0xbe3df80007fffc00

def z978 : W := mkw 0x88e50000dddb001c 0x0447280006eed800 0xdefc0000ffff8019 0xfef7e00007fffc00

def z979 : W := mkw 0x402c02cc146c4891 0x4201601660a36244 0xc6bc83cc1e7c781b 0xb635e41e60f3e3c0

def z980 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x46bc81c00e1c3811 0xb235e40e0070e1c0

def z981 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0xc6bc8bcc1e1c3993 0xb635e45e60f0e1cc

def z982 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0x46bc8bcc0e1c7993 0xb235e45e6070e3cc

def z983 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x5e9c0000ee7f8010 0x22f4e0000773fc00

def z984 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07ffe19 0x29c6079f8703fff0

def z985 : W := mkw 0x0025021514e9c2b8 0x20012810a8a74e15 0xc1ff0e3f11ffc7ef 0xde0ff871f88ffe3f

def z986 : W := mkw 0x02088ac802245903 0x00104456401122c8 0xc6bc8bcc1e7c799b 0xb635e45e60f3e3cc

def z987 : W := mkw 0xbdf33335f9f3e6ac 0xa5ef9999afcf9f35 0xb9637e3ff1e3c7ef 0xddcb1bf1ff8f1e3f

def z988 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc7bf8bcc1ffc799b 0xb63dfc5e60ffe3cc

def z989 : W := mkw 0x1fdaedaa40120000 0x00fed76d52009000 0x7fffffffe01c0017 0xf3ffffffff00e000

def z990 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf63fc00ff807fff 0xfdfb1fe007fc03ff

def z991 : W := mkw 0x973fcc8a9fc9115e 0x04b9fe6454fe488a 0xc73f0c0f1f8001e0 0x8639f86078fc000f

def z992 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc69c81c01e1c7998 0x2634e40e00f0e3cc

def z993 : W := mkw 0x6208fffc2224ffc3 0xc31047ffe11127fe 0x2000fffc00007fe6 0x010007ffe00003ff

def z994 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07ffe07 0x49c6079f8703fff0

def z995 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c89c00e1c3812 0xb234e44e0070e1c0

def z996 : W := mkw 0x422c8acd166c59b3 0x6211645668b362cd 0xc6bc8fcf1e7c79fb 0xb635e47e78f3e3cf

def z997 : W := mkw 0x15005400ab003542 0x00a802a0055801aa 0xbf007400ff807ffc 0xfdf803a007fc03ff

def z998 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfbf0000ffff8018 0xaefdf80007fffc00

def z999 : W := mkw 0x422c8ac8166c5913 0x4211645640b362c8 0xc6bc83c01e7c781b 0xb635e41e00f3e3c0

def z1000 : W := mkw 0x0021001510c182a8 0x20010800a8860c15 0x81630c3f1183c7ee 0xdc0b1861f88c1e3f

def z1001 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x5fff0000efff8011 0x6afff800077ffc00

def z1002 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6fc8bfc1e7c799f 0xf637e45fe0f3e3cc

def z1003 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7ff8fff1ffc7fff 0xfe3ffc7ff8ffe3ff

def z1004 : W := mkw 0x9df74400dddb005c 0x04efba2006eed802 0xdfff0400ffff8079 0xfefff82007fffc03

def z1005 : W := mkw 0x0021025510e5caa9 0x20010812a8872e55 0x81630e3f11ffffff 0xdc0b1871f88fffff

def z1006 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0xc69c8bc01e7c799b 0xb634e45e00f3e3cc

def z1007 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7bc8fcc1fffffff 0xfe3de47e60ffffff

def z1008 : W := mkw 0x9df60000dd5a0014 0x04efb00006ead000 0xdefc0000fe7f8019 0xfef7e00007f3fc00

def z1009 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0xc6bc8bcc1e7c381b 0xb635e45e60f3e1c0

def z1010 : W := mkw 0x9df70001dddb003c 0x24efb8000eeed801 0xdfff0403ffff8079 0xfefff8201ffffc03

def z1011 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x67ffffff00000007 0x833ffffff8000000

def z1012 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07fbe15 0x69c6079f8703fdf0

def z1013 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7ff8fff1ffff9fb 0xb63ffc7ff8ffffcf

def z1014 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc0bcc1e7c7999 0x8635e05e60f3e3cc

def z1015 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6bc8fff1fffffff 0xbe35e47ff8ffffff

def z1016 : W := mkw 0x02248a40166c5913 0x0011245200b362c8 0xc6bc8bc01e7c799b 0xb635e45e00f3e3cc

def z1017 : W := mkw 0x1708dc8aab003542 0x00b846e4555801aa 0xbf00fc0fff807ffe 0xfdf807e07ffc03ff

def z1018 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0fff0e07fffff 0x79c607ff8703ffff

def z1019 : W := mkw 0xa8f7237554ffcabd 0xa547b91baaa7fe55 0x40ff03ff007f8001 0x0207f81ff803fc00

def z1020 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fc00ff807ff8 0xadf807e007fc03ff

def z1021 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x39c3f7f3e07ffe1f 0x79ce1fbf9f03fff0

def z1022 : W := mkw 0x28c0316060162c01 0x8146018b0300b160 0x3880f1c0e07fb818 0x29c4078e0703fdc0

def z1023 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff01800667 0xfbfffffff80c0033

def z1024 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0xc79c8dc01f9c7ffe 0xfe3ce46e00fce3ff

def z1025 : W := mkw 0x9df70005dddb00bc 0x24efb8002eeed805 0xdfff000fffff8019 0xfefff8007ffffc00

def z1026 : W := mkw 0x00240244146c4891 0x0001201220a36244 0xc6bc8bcc1e7c799b 0xb635e45e60f3e3cc

def z1027 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf00fc00ff807fe6 0xcdf807e007fc03ff

def z1028 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x78ff73ff00000005 0x43c7fb9ff8000000

def z1029 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0xb963fe3f11e3c7ef 0xfdcb1ff1f88f1e3f

def z1030 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc7ff8bff1ffff99b 0xfe3ffc5ff8ffffcc

def z1031 : W := mkw 0x02009800ab003542 0x001004c0055801aa 0xbe00f800ff807ffe 0xfdf007c007fc03ff

def z1032 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf43fc33ff807ffe 0xfdfa1fe19ffc03ff

def z1033 : W := mkw 0x28d233726036ee01 0x8146919b9301b770 0x38c3f3f3e07ffe1f 0x79c61f9f9f03fff0

def z1034 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7bf8fcf1e7c799b 0xb63dfc7e78f3e3cc

def z1035 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c89c00e1c7992 0x2234e44e0070e3cc

def z1036 : W := mkw 0x1fdaedaa8b001142 0x00fed76d5458008a 0xffffffffff8001ff 0xfffffffffffc000f

def z1037 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1e7c3991 0xa635e45e60f3e1cc

def z1038 : W := mkw 0x95370000dddb001c 0x04a9b80006eed800 0xc61c0000ffff8018 0x0e30e00007fffc00

def z1039 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0a0cffff801b 0xfefff85067fffc00

def z1040 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8bcc1e7c7f9f 0xfe35e45e60f3e3fc

def z1041 : W := mkw 0x1df60000545a0010 0x00efb00002a2d000 0xdfff0000fe7f8019 0xfefff80007f3fc00

def z1042 : W := mkw 0x420c88c8060c1913 0x42106446403060c8 0x469c81c00e1c781a 0x3234e40e0070e3c0

def z1043 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81638e3f11e3ffff 0xfc0b1c71f88f1fff

def z1044 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc83cc1e7c3819 0xb635e41e60f3e1c0

def z1045 : W := mkw 0x9dd60000cd1a0014 0x04eeb0000668d000 0x5fff0000ee7f8019 0xfafff8000773fc00

def z1046 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6ff8bff1e7c799b 0xb637fc5ff8f3e3cc

def z1047 : W := mkw 0x422ccece166c5993 0x4211667670b362cc 0xc6bc8fcf1e7c799b 0xb635e47e78f3e3cc

def z1048 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc6bc8bff1e7c799b 0xb635e45ff8f3e3cc

def z1049 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0x5fff0000ee7f8011 0xf2fff8000773fc00

def z1050 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x01630e3f01e3c7e7 0x480b1871f80f1e3f

def z1051 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f1f0e07ffe1c 0x69c6078f8703fff0

def z1052 : W := mkw 0x200012506036ee01 0x810000928301b770 0x3880f3c0e07ffe1f 0x79c4079e0703fff0

def z1053 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f11e387e5 0xcc0b1871f88f1c3f

def z1054 : W := mkw 0x0021025510e5caa9 0x20010812a8872e55 0x81638fff11e3ffef 0xdc0b1c7ff88f1fff

def z1055 : W := mkw 0x9df74402dddb001c 0x04efba2016eed800 0xdfff0403ffff8019 0xfefff8201ffffc00

def z1056 : W := mkw 0x422d8adc16eddb9b 0x42116c56e0b76edc 0xc7ff8bfc1fffff9f 0xfe3ffc5fe0fffffc

def z1057 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x3880f3f0e07ffe1e 0x29c4079f8703fff0

def z1058 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc69c81c01ffffff8 0x2e34e40e00ffffff

def z1059 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc6fc8fff1e7fffff 0xfe37e47ff8f3ffff

def z1060 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0xffffffff1000418f 0xf7fffffff880020c

def z1061 : W := mkw 0x28c033746036ee81 0x8146019ba301b774 0x38c0fbfce07fff9f 0x79c607dfe703fffc

def z1062 : W := mkw 0x1fdaedaa8b001142 0x00fed76d5458008a 0xffffffff1f8047ef 0xfffffffff8fc023f

def z1063 : W := mkw 0x0001001100818228 0x2000080088040c11 0x81630e3f1183c7ef 0xdc0b1871f88c1e3f

def z1064 : W := mkw 0x022c888816481112 0x0011644440b24088 0xc6bc8bcc1e7c799b 0xb635e45e60f3e3cc

def z1065 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07fb817 0x71c6079f8703fdc0

def z1066 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0400ffff867d 0xfefff82007fffc33

def z1067 : W := mkw 0x40240244166c5993 0x4201201220b362cc 0xc6bc83c01e7c799b 0xb635e41e00f3e3cc

def z1068 : W := mkw 0x422d8acc16ed599b 0x42116c5660b76acc 0xc7ff8fff1ffff99f 0xfe3ffc7ff8ffffcc

def z1069 : W := mkw 0x420c8acc062c5993 0x42106456603162cc 0x469c81c00e1c7990 0x2234e40e0070e3cc

def z1070 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0230ffff801f 0xfefff81187fffc00

def z1071 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf40fc00ffe3ffff 0xfdfa07e007ff1fff

def z1072 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0x46bc81cc0e1c3810 0x2235e40e6070e1c0

def z1073 : W := mkw 0x00040040040c0811 0x0000200200206040 0x469c81c00e1c3810 0x2234e40e0070e1c0

def z1074 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xfebcfbcc1e7c799f 0xf7f5e7de60f3e3cc

def z1075 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0c00ffff801f 0xfefff86007fffc00

def z1076 : W := mkw 0x9dd70000cd9b001c 0x04eeb800066cd800 0x5fdf0000efff8019 0x7afef800077ffc00

def z1077 : W := mkw 0x08da21aa00000000 0x0046d10d50000000 0x78fff3ff00000001 0x23c7ff9ff8000000

def z1078 : W := mkw 0xbdd37530e993a64c 0x85ee9ba9874c9d32 0x39437430e1838664 0x49ca1ba1870c1c33

def z1079 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc6bc8bfc1e7c7f9f 0xb635e45fe0f3e3fc

def z1080 : W := mkw 0x420c88cc060c1993 0x42106446603060cc 0x469c89cc0e1c3990 0x2234e44e6070e1cc

def z1081 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc83cc1e7c7999 0x2635e41e60f3e3cc

def z1082 : W := mkw 0x1fdaedaa89000040 0x00fed76d54480002 0x7fffffff01800067 0xf3fffffff80c0003

def z1083 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0x46bc8bcc0e7c3813 0xb235e45e6073e1c0

def z1084 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbe00f000ff807ffe 0x7df0078007fc03ff

def z1085 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc7bc8fcc1e7c799f 0xf63de47e60f3e3cc

def z1086 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdf9c0000ffff8018 0xfefce00007fffc00

def z1087 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x39e3f3f0e07ffe1f 0xf9cf1f9f8703fff0

def z1088 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7fffffff0000781f 0xf3fffffff80003c0

def z1089 : W := mkw 0x28c033756036eea1 0xa146019bab01b775 0x39e3ffffe07fffff 0xf9cf1fffff03ffff

def z1090 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81e30e3f11ffc7ff 0xfc0f1871f88ffe3f

def z1091 : W := mkw 0x1fdaedaa8b001142 0x00fed76d5458008a 0x7fffffff0e000007 0xf3fffffff8700000

def z1092 : W := mkw 0x422d8add16eddbbb 0x62116c56e8b76edd 0xc6ff8fff1e7fffff 0xb637fc7ff8f3ffff

def z1093 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38e0fbfce07ffe1f 0xf9c707dfe703fff0

def z1094 : W := mkw 0x422ccecc166c5993 0x4211667660b362cc 0xe6bcffcc1e7c799f 0xb735e7fe60f3e3cc

def z1095 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc6bc8fff1e7c799f 0xb635e47ff8f3e3cc

def z1096 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0x469c81c00e7c7818 0x2234e40e0073e3c0

def z1097 : W := mkw 0x08c0236040364801 0x0046011b0201b240 0x38c0f3f0e07ff81f 0x79c6079f8703ffc0

def z1098 : W := mkw 0x422c88c8164c1913 0x4211644640b260c8 0xc69c81c01e7c3818 0x2634e40e00f3e1c0

def z1099 : W := mkw 0x422c8adc166cdb93 0x42116456e0b366dc 0xc7ff8fff1e7fff9f 0xfe3ffc7ff8f3fffc

def z1100 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdeff0000fe7f8019 0xb6f7f80007f3fc00

def z1101 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc69c8bcc1e7c799a 0x2634e45e60f3e3cc

def z1102 : W := mkw 0x0adaedaa00000000 0x0056d76d50000000 0x60fff3ff00000001 0x0307ff9ff8000000

def z1103 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0f3f0e07ffe17 0x21c6079f8703fff0

def z1104 : W := mkw 0x9df72120dddb001c 0x04efb90906eed800 0xdfff03f0ffff8019 0xfefff81f87fffc00

def z1105 : W := mkw 0x15001000a9002400 0x00a8008005480120 0xbf00fc00ff807ffe 0xfdf807e007fc03ff

def z1106 : W := mkw 0x0021025510e5caa9 0x20010812a8872e55 0x81e30fff11ffc7ef 0xdc0f187ff88ffe3f

def z1107 : W := mkw 0x1dda65aa00000000 0x00eed32d50000000 0x79fff7ff00000007 0x73cfffbff8000000

def z1108 : W := mkw 0x422c8add166cdbb3 0x62116456e8b366dd 0xc7bc8fff1ffc7fff 0xfe3de47ff8ffe3ff

def z1109 : W := mkw 0x420c8ac8062c5913 0x42106456403162c8 0x46bc8bcc0e7c781b 0xb235e45e6073e3c0

def z1110 : W := mkw 0x9df72120dddb001c 0x04efb90906eed800 0xffff7030ffff801d 0xfffffb8187fffc00

def z1111 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7efffbff00000003 0xb3f7ffdff8000000

def z1112 : W := mkw 0x95370000dddb001c 0x04a9b80006eed800 0xc77f0000ffff8019 0xde3bf80007fffc00

def z1113 : W := mkw 0x1712dc00ab003542 0x00b896e0055801aa 0xff3ffc00ff807ffe 0xfff9ffe007fc03ff

def z1114 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0x81630e3f1183c7e6 0xcc0b1871f88c1e3f

def z1115 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff023fffff8019 0xfefff811fffffc00

def z1116 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xbf23fc0fff807ffe 0xfdf91fe07ffc03ff

def z1117 : W := mkw 0x171adc8aab003542 0x00b8d6e4555801aa 0xff1cfc00ff807ffe 0xfff8e7e007fc03ff

def z1118 : W := mkw 0x0021021510e1c2a8 0x20010810a8870e15 0xc7ff0e3f11e3c7ef 0xfe3ff871f88f1e3f

def z1119 : W := mkw 0x1fdaedaa00000000 0x00fed76d50000000 0x7effffff00000007 0x23f7fffff8000000

def z1120 : W := mkw 0x422c88cc164c1993 0x4211644660b260cc 0xc6bc89cc1e1c799a 0xb635e44e60f0e3cc

def z1121 : W := mkw 0x171aedaa00000000 0x00b8d76d50000000 0x7f3fffff00000006 0xf3f9fffff8000000

def z1122 : W := mkw 0x1fdaedaa02001102 0x00fed76d50100088 0x7fffffff00007987 0xf3fffffff80003cc

def z1123 : W := mkw 0x422c8acc166c5993 0x4211645660b362cc 0xc69c89c01e7c799a 0xb634e44e00f3e3cc

def z1124 : W := mkw 0x9df70000dddb001c 0x04efb80006eed800 0xdfff0c0fffff8019 0xfefff8607ffffc00

def z1125 : W := mkw 0x0adaa9aa00000000 0x0056d54d50000000 0x7efffbff00000007 0xf3f7ffdff8000000

def z1126 : W := mkw 0x08c0124060366c01 0x004600920301b360 0x38c0f3c0e07ffe1f 0x79c6079e0703fff0

def z1127 : W := mkw 0x1700dc00ab003542 0x00b806e0055801aa 0xb900fc00ff807ffe 0x4dc807e007fc03ff

def z1128 : W := mkw 0x1fdaedaa02001142 0x00fed76d5010008a 0x7fffffff000001e7 0xf3fffffff800000f

def z1129 : W := mkw 0x00240000545a0010 0x0001200002a2d000 0xc6bc0000fe7f8019 0xbe35e00007f3fc00

def z1130 : W := mkw 0x28c033706036ee01 0x8146019b8301b770 0x38c0ffffe07ffe1f 0x79c607ffff03fff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z4,z6]),(0,[z0,z8,z1,z3,z4,z9,z6]),(0,[z0,z10,z1,z2,z3,z4,z6])],[(0,[z0,z11,z1,z3,z4,z12,z6]),(0,[z0,z1,z2,z3,z6,z13,z14])],[(0,[z15,z0,z1,z2,z3,z4,z6]),(0,[z16,z17,z1,z2,z3,z4,z6]),(0,[z0,z1,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z19])],[(0,[z20,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z23,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z24])],[(0,[z0,z1,z2,z25,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z6]),(0,[z0,z28,z1,z2,z3,z4,z6]),(1,[z29,z1,z2,z3,z4,z6])],[(0,[z0,z30,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z31]),(0,[z0,z1,z2,z3,z4,z32,z6]),(0,[z0,z1,z33,z2,z3,z4,z6])],[(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z35,z4,z6]),(0,[z0,z1,z2,z3,z22,z36,z6]),(0,[z0,z1,z2,z3,z4,z37,z6]),(0,[z0,z1,z2,z3,z4,z38,z6]),(0,[z0,z1,z39,z2,z3,z9,z6]),(0,[z0,z40,z1,z2,z3,z4,z6])],[(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z42,z3,z4,z6])]],
   [[(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z46,z4,z6]),(0,[z0,z8,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z47,z48,z6]),(0,[z49,z0,z1,z2,z3,z50,z6]),(0,[z0,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z4,z6]),(0,[z0,z1,z2,z53,z3,z4,z6])],[(0,[z17,z0,z1,z2,z54,z4,z6]),(0,[z49,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z12,z55]),(0,[z0,z56,z1,z2,z3,z4,z57])],[(0,[z0,z1,z58,z59,z3,z4,z6]),(0,[z0,z1,z2,z54,z60,z4,z6]),(0,[z0,z1,z2,z3,z4,z61,z6]),(0,[z0,z1,z62,z2,z3,z4,z6]),(0,[z63,z0,z1,z2,z3,z4,z6])],[(0,[z0,z64,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z22,z6]),(0,[z0,z1,z65,z2,z3,z22,z6])],[(0,[z66,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z67]),(0,[z0,z1,z2,z3,z4,z68,z6])],[(0,[z0,z1,z2,z3,z22,z69,z6]),(0,[z0,z1,z2,z70,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z71,z6]),(1,[z72,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z73]),(1,[z0,z74,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z6])],[(0,[z0,z1,z2,z3,z4,z6,z76]),(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z78,z47,z6]),(0,[z0,z1,z2,z3,z47,z6,z79]),(0,[z0,z80,z1,z59,z3,z4,z6]),(0,[z0,z1,z2,z81,z3,z4,z6]),(0,[z0,z82,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z83,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z84]),(0,[z44,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z85,z6]),(0,[z86,z0,z80,z2,z3,z4,z6]),(0,[z0,z1,z87,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z14]),(0,[z0,z88,z1,z2,z89,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z90]),(0,[z0,z1,z2,z91,z3,z4,z6])],[(0,[z92,z0,z1,z2,z3,z4,z6]),(0,[z0,z93,z1,z2,z3,z4,z6]),(0,[z0,z94,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z95,z4,z6])],[(0,[z0,z1,z2,z3,z96,z4,z6])],[(1,[z0,z1,z2,z3,z97,z6]),(0,[z44,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z6,z98]),(0,[z99,z0,z1,z2,z3,z4,z6]),(0,[z0,z100,z2,z3,z4,z37,z6])],[(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z102,z3,z4,z6]),(0,[z49,z1,z2,z3,z4,z22,z6]),(1,[z0,z1,z2,z103,z4,z6]),(0,[z0,z1,z2,z104,z4,z105,z6])],[(0,[z0,z106,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z107,z22,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z3,z4,z6]),(0,[z0,z1,z109,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z110]),(0,[z0,z1,z2,z3,z4,z111,z6])]],
   [[(1,[z0,z112,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z6]),(0,[z0,z1,z2,z3,z4,z114,z6])],[(0,[z0,z1,z2,z3,z4,z115,z6]),(0,[z0,z1,z2,z3,z116,z4,z6]),(0,[z0,z117,z1,z2,z3,z4,z57]),(0,[z118,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z119,z4,z6]),(1,[z0,z1,z2,z3,z120,z6]),(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z122,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z123]),(0,[z0,z124,z1,z2,z3,z4,z6])],[(0,[z125,z0,z34,z2,z3,z4,z6]),(0,[z0,z8,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z104,z3,z4,z55]),(0,[z0,z126,z1,z127,z3,z4,z6]),(0,[z0,z1,z2,z128,z3,z4,z6]),(0,[z0,z129,z1,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z3,z130,z6]),(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z0,z1,z74,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z132])],[(0,[z0,z1,z2,z3,z4,z133,z6]),(0,[z0,z100,z1,z2,z3,z37,z6]),(0,[z0,z1,z2,z134,z3,z4,z6]),(0,[z0,z135,z1,z2,z3,z4,z6])],[(0,[z0,z136,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z137,z4,z6]),(0,[z0,z1,z2,z3,z47,z47,z6]),(0,[z0,z138,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z139,z6]),(0,[z0,z1,z2,z3,z4,z105,z6])],[(0,[z140,z0,z1,z2,z3,z4,z6]),(0,[z0,z126,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z142,z4,z6]),(0,[z0,z1,z2,z3,z143,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z22,z22,z6]),(0,[z144,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z145,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z144,z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z148,z6])],[(0,[z149,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z150,z6]),(0,[z0,z1,z59,z3,z4,z6,z98]),(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z152,z6])],[(1,[z0,z1,z153,z3,z4,z6]),(0,[z125,z0,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z154,z3,z4,z6]),(0,[z0,z155,z1,z2,z3,z4,z6]),(0,[z0,z1,z156,z2,z3,z4,z6]),(0,[z0,z1,z2,z104,z3,z4,z14]),(1,[z0,z1,z2,z3,z6,z13]),(1,[z0,z1,z2,z104,z4,z105]),(0,[z0,z1,z2,z3,z157,z4,z6])],[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z159,z6]),(0,[z44,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z160,z2,z3,z4,z6]),(0,[z0,z161,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z47,z6,z57]),(0,[z0,z162,z1,z2,z3,z4,z6]),(0,[z0,z126,z1,z3,z4,z9,z6]),(0,[z0,z1,z2,z163,z3,z4,z6]),(0,[z164,z0,z1,z2,z3,z4,z6])],[(0,[z165,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z166,z22,z6]),(0,[z0,z1,z2,z3,z4,z167,z6])],[(0,[z0,z1,z58,z2,z3,z47,z6]),(0,[z168,z0,z1,z2,z3,z22,z6]),(0,[z49,z0,z1,z2,z3,z4,z169]),(0,[z0,z1,z2,z170,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z171]),(0,[z0,z172,z2,z3,z166,z4,z6]),(0,[z0,z65,z33,z2,z3,z4,z6]),(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z0,z174,z1,z2,z3,z4,z6])],[(0,[z0,z175,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z176,z4,z6])]],
   [[(0,[z0,z177,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z31,z6]),(0,[z0,z172,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z178,z6])],[(0,[z17,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z4,z179,z6]),(0,[z0,z1,z2,z3,z107,z47,z6])],[(0,[z180,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z181,z3,z4,z6]),(0,[z0,z1,z2,z59,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z182,z6]),(0,[z0,z80,z1,z2,z3,z47,z6]),(0,[z0,z183,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z184])],[(0,[z185,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z186,z3,z4,z6]),(0,[z0,z1,z187,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z188,z4,z6])],[(0,[z0,z189,z1,z2,z3,z4,z6]),(0,[z0,z172,z2,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z190,z4,z6]),(0,[z0,z1,z2,z89,z3,z4,z6])],[(0,[z0,z1,z65,z3,z4,z6,z98]),(0,[z0,z29,z1,z2,z3,z4,z6])],[(0,[z0,z191,z1,z2,z107,z4,z6]),(0,[z0,z1,z2,z3,z4,z192,z6]),(0,[z0,z193,z1,z3,z60,z4,z6])],[(0,[z0,z1,z2,z194,z3,z4,z6]),(0,[z0,z1,z2,z195,z3,z4,z6]),(0,[z196,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z197,z22,z6]),(0,[z198,z0,z1,z2,z3,z47,z6]),(0,[z0,z199,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z3,z200,z6]),(0,[z0,z1,z2,z201,z4,z200,z6])],[(1,[z0,z193,z1,z60,z4,z6])],[(0,[z0,z1,z202,z2,z3,z4,z6]),(0,[z198,z0,z1,z2,z3,z203,z6]),(0,[z0,z1,z2,z3,z4,z36,z169]),(0,[z0,z1,z2,z3,z4,z6,z204]),(0,[z0,z205,z1,z2,z3,z4,z6]),(0,[z144,z0,z1,z2,z4,z200,z6])],[(1,[z0,z206,z2,z3,z4,z6]),(0,[z207,z0,z2,z3,z107,z4,z6]),(0,[z0,z193,z1,z2,z127,z4,z6])],[(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z209,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z210,z3,z4,z6]),(0,[z0,z1,z211,z2,z3,z4,z6])],[(0,[z44,z0,z212,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z213,z6]),(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z215,z6]),(0,[z0,z216,z1,z2,z3,z4,z6]),(0,[z217,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z59,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z219,z6])],[(0,[z0,z1,z2,z3,z166,z47,z6]),(0,[z0,z220,z1,z2,z3,z4,z6]),(0,[z0,z221,z1,z2,z3,z4,z6])]],
   [[(0,[z168,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z22,z6,z57]),(0,[z0,z1,z2,z3,z4,z169,z98]),(0,[z0,z1,z2,z3,z222,z4,z6]),(0,[z86,z0,z126,z1,z3,z4,z6]),(0,[z0,z223,z1,z2,z3,z4,z6]),(0,[z0,z1,z224,z2,z3,z4,z6])],[(0,[z0,z126,z1,z58,z3,z4,z6]),(0,[z0,z1,z2,z3,z225,z4,z6]),(0,[z226,z0,z1,z2,z3,z47,z6]),(0,[z0,z8,z1,z39,z3,z4,z6])],[(0,[z44,z0,z1,z2,z227,z4,z6]),(0,[z1,z58,z2,z141,z3,z4,z6]),(0,[z0,z1,z2,z54,z3,z22,z6]),(0,[z0,z1,z59,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z228,z4,z6]),(0,[z0,z100,z1,z229,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z200,z6])],[(0,[z0,z1,z2,z3,z22,z230,z6]),(0,[z0,z172,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z169,z6]),(0,[z0,z1,z2,z3,z4,z231,z6]),(0,[z0,z1,z39,z2,z3,z4,z232]),(0,[z0,z233,z1,z2,z3,z4,z6])],[(1,[z1,z2,z3,z22,z6,z55]),(0,[z0,z1,z2,z234,z3,z22,z6]),(0,[z0,z1,z39,z2,z3,z22,z6]),(0,[z235,z0,z1,z2,z3,z47,z6]),(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z237,z0,z1,z2,z3,z4,z6])],[(0,[z180,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z6,z238]),(0,[z0,z1,z2,z239,z3,z4,z6]),(0,[z0,z1,z240,z2,z3,z4,z6]),(0,[z0,z1,z2,z59,z3,z47,z6]),(0,[z0,z1,z2,z241,z3,z47,z6]),(1,[z0,z8,z1,z3,z9,z6]),(0,[z0,z1,z2,z3,z4,z6,z242])],[(0,[z0,z1,z2,z3,z47,z12,z6]),(0,[z198,z1,z2,z3,z4,z6,z55]),(0,[z0,z1,z2,z3,z4,z243,z6]),(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z3,z60,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z47,z6]),(0,[z244,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z245,z6])]],
   [[(0,[z0,z1,z2,z3,z47,z5,z6]),(1,[z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z246,z2,z3,z4,z6])],[(0,[z0,z1,z2,z247,z3,z4,z6]),(0,[z0,z1,z2,z3,z248,z4,z6]),(0,[z0,z1,z2,z3,z249,z4,z6]),(0,[z0,z1,z2,z250,z3,z4,z6]),(0,[z0,z1,z2,z251,z3,z4,z6]),(0,[z0,z1,z252,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z253,z47,z6]),(0,[z0,z1,z42,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z47,z6,z19]),(0,[z0,z1,z2,z3,z254,z4,z6]),(0,[z0,z1,z2,z3,z4,z255,z6])],[(0,[z207,z0,z1,z2,z3,z22,z6]),(0,[z0,z256,z1,z2,z3,z4,z6]),(0,[z257,z0,z1,z2,z3,z4,z6]),(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z259,z3,z4,z6]),(0,[z0,z1,z260,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z261,z6])],[(0,[z0,z262,z1,z2,z3,z4,z6]),(0,[z263,z88,z1,z2,z3,z4,z6])],[(0,[z0,z264,z1,z2,z3,z4,z6])],[(0,[z207,z0,z2,z59,z3,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z266,z3,z4,z6]),(0,[z0,z267,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z268,z2,z3,z4,z6]),(0,[z207,z0,z191,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z0,z1,z2,z3,z114,z6,z19])],[(0,[z44,z0,z1,z2,z3,z270,z6]),(0,[z0,z1,z2,z251,z197,z4,z6]),(0,[z0,z1,z2,z3,z4,z55,z57]),(0,[z0,z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z272,z3,z4,z6]),(0,[z0,z1,z2,z3,z273,z4,z6]),(0,[z0,z56,z2,z3,z4,z6,z57]),(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z275,z0,z1,z2,z3,z4,z6])],[(1,[z1,z2,z3,z197,z22,z6]),(0,[z86,z0,z1,z2,z3,z22,z6]),(0,[z16,z0,z1,z2,z3,z22,z6]),(0,[z276,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z36,z6,z57]),(0,[z0,z1,z2,z127,z3,z4,z6]),(0,[z277,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z278,z2,z3,z4,z6]),(1,[z0,z1,z279,z3,z4,z6]),(0,[z0,z1,z2,z3,z280,z4,z6]),(0,[z0,z11,z1,z2,z3,z4,z98]),(0,[z0,z11,z1,z2,z3,z4,z12]),(1,[z0,z1,z2,z89,z201,z6])],[(0,[z180,z0,z1,z2,z3,z4,z281]),(0,[z0,z1,z2,z3,z4,z282,z6]),(0,[z198,z0,z1,z2,z3,z4,z169]),(0,[z0,z1,z283,z2,z3,z4,z6])],[(0,[z0,z1,z2,z54,z3,z47,z6]),(0,[z0,z126,z1,z3,z4,z6,z98]),(0,[z0,z100,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z284])],[(0,[z0,z1,z2,z141,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z4,z6])],[(0,[z285,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z39,z2,z3,z47,z6]),(0,[z0,z1,z2,z286,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z47,z6,z55]),(0,[z0,z1,z2,z3,z4,z287,z6]),(0,[z288,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z289]),(0,[z0,z1,z2,z3,z290,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z291])],[(0,[z0,z1,z292,z2,z3,z4,z6]),(0,[z0,z293,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z294,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z4,z98]),(0,[z0,z88,z1,z2,z3,z4,z12]),(1,[z263,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z127,z197,z4,z6]),(0,[z0,z161,z1,z2,z3,z4,z169]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z295,z4,z6])],[(0,[z0,z1,z2,z3,z22,z12,z6]),(0,[z0,z1,z296,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z297]),(0,[z0,z1,z2,z3,z4,z184,z200]),(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z96,z4,z19])],[(0,[z125,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z299,z6]),(0,[z0,z1,z42,z2,z3,z4,z12]),(0,[z0,z1,z42,z2,z3,z4,z98])],[(0,[z86,z0,z172,z2,z3,z4,z6]),(0,[z0,z1,z300,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z301,z6]),(0,[z302,z0,z1,z2,z3,z4,z6]),(0,[z303,z0,z1,z2,z3,z4,z6])],[(0,[z0,z304,z1,z2,z3,z4,z6]),(0,[z207,z0,z1,z2,z3,z47,z6]),(1,[z49,z1,z2,z3,z4,z169]),(1,[z0,z1,z39,z3,z305,z6]),(0,[z306,z0,z1,z2,z3,z4,z6])],[(0,[z307,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z308,z6]),(0,[z0,z1,z2,z3,z22,z6,z19]),(0,[z0,z1,z2,z3,z47,z6,z14]),(0,[z309,z0,z1,z2,z3,z4,z6]),(0,[z310,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z65,z127,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z47,z114,z6]),(0,[z0,z311,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z312,z6]),(0,[z0,z8,z1,z2,z3,z305,z6]),(0,[z0,z1,z2,z3,z313,z4,z6]),(0,[z0,z1,z2,z314,z3,z4,z6])],[(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z169,z6,z55]),(0,[z0,z1,z2,z3,z4,z315,z6]),(0,[z0,z1,z2,z89,z3,z201,z6])],[(0,[z0,z1,z2,z3,z316,z4,z6]),(1,[z0,z172,z2,z3,z166,z6]),(0,[z0,z1,z2,z3,z4,z317,z6])],[(0,[z125,z136,z1,z2,z3,z4,z6]),(0,[z0,z318,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z97,z6]),(0,[z0,z319,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z169,z57]),(0,[z0,z320,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z321,z3,z4,z6]),(0,[z0,z322,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z323,z6]),(0,[z0,z1,z2,z3,z305,z22,z6]),(0,[z86,z0,z1,z2,z3,z47,z6]),(0,[z0,z193,z1,z2,z3,z4,z289])],[(0,[z136,z1,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z0,z1,z2,z3,z47,z105,z6]),(0,[z325,z0,z1,z2,z3,z4,z6]),(0,[z0,z56,z1,z2,z3,z4,z36])],[(0,[z0,z326,z1,z2,z3,z4,z6]),(0,[z49,z0,z1,z2,z3,z327,z6]),(0,[z0,z328,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z329,z3,z4,z6]),(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z0,z172,z1,z2,z3,z166,z6]),(0,[z0,z1,z2,z3,z4,z6,z331])]],
   [[(0,[z49,z16,z1,z2,z3,z4,z6]),(0,[z332,z0,z1,z2,z3,z4,z6]),(0,[z0,z333,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z334,z3,z4,z6]),(0,[z0,z1,z335,z2,z3,z4,z6]),(0,[z0,z193,z1,z2,z60,z4,z6]),(0,[z0,z336,z1,z2,z3,z4,z6])],[(0,[z17,z0,z1,z2,z197,z4,z6]),(0,[z0,z1,z65,z2,z3,z47,z6]),(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z59,z251,z3,z4,z6]),(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z338,z2,z3,z4,z6]),(0,[z0,z1,z2,z266,z3,z4,z6]),(0,[z0,z339,z1,z2,z3,z4,z6]),(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6]),(1,[z0,z1,z42,z3,z4,z98])],[(0,[z0,z1,z2,z3,z4,z120,z6]),(0,[z0,z1,z2,z104,z3,z22,z6]),(0,[z0,z1,z2,z3,z342,z4,z6]),(0,[z0,z1,z2,z3,z343,z4,z6]),(0,[z344,z0,z1,z2,z3,z4,z6]),(1,[z0,z223,z1,z3,z4,z6]),(0,[z0,z1,z2,z345,z3,z4,z6]),(0,[z0,z346,z1,z2,z3,z4,z6]),(0,[z0,z1,z347,z2,z3,z4,z6])],[(0,[z348,z0,z1,z2,z3,z4,z6]),(0,[z0,z349,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z6,z19])],[],[(0,[z0,z1,z2,z3,z22,z6,z55]),(0,[z0,z1,z2,z3,z96,z22,z6]),(1,[z198,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z350,z6]),(0,[z0,z1,z2,z279,z3,z4,z6]),(0,[z0,z351,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z327,z4,z6]),(0,[z0,z1,z2,z3,z201,z4,z6])],[(0,[z0,z352,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z78,z4,z6]),(0,[z101,z0,z1,z2,z3,z22,z6]),(0,[z353,z0,z1,z2,z3,z4,z6]),(0,[z0,z100,z1,z279,z3,z4,z6])]],
   [[(0,[z180,z0,z1,z2,z3,z4,z76]),(1,[z44,z1,z141,z3,z4,z6]),(0,[z168,z0,z1,z2,z3,z354,z6]),(0,[z0,z1,z2,z355,z3,z4,z6]),(0,[z0,z356,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z357,z4,z6])],[(0,[z0,z0,z1,z2,z3,z22,z6]),(0,[z0,z2,z59,z3,z4,z37,z6]),(0,[z0,z1,z2,z3,z4,z6,z358]),(1,[z257,z0,z2,z3,z4,z6])],[(0,[z0,z359,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z360,z6]),(0,[z361,z0,z1,z2,z3,z4,z6]),(0,[z0,z117,z2,z3,z4,z36,z6]),(0,[z0,z1,z2,z3,z4,z6,z13])],[(0,[z0,z1,z2,z3,z362,z4,z6]),(0,[z0,z363,z1,z2,z3,z4,z6]),(0,[z0,z364,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z22,z6,z14]),(0,[z0,z365,z1,z2,z3,z4,z6]),(0,[z366,z0,z1,z2,z3,z4,z6])],[(0,[z180,z0,z1,z2,z367,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z368]),(0,[z144,z0,z1,z2,z3,z114,z6])],[(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z369]),(0,[z0,z370,z1,z2,z3,z4,z6]),(0,[z0,z126,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z371,z6]),(0,[z0,z1,z2,z3,z4,z36,z6]),(0,[z0,z117,z1,z2,z3,z4,z36])],[(0,[z180,z0,z1,z2,z372,z4,z6]),(0,[z0,z373,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z374,z6]),(0,[z0,z1,z2,z3,z375,z4,z6]),(0,[z0,z193,z1,z65,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z376]),(0,[z0,z1,z2,z3,z4,z377,z6]),(0,[z0,z1,z2,z3,z4,z6,z378])]],
   [[(0,[z0,z1,z2,z3,z305,z47,z6]),(0,[z0,z1,z2,z3,z4,z6,z379]),(0,[z0,z1,z380,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z381]),(0,[z0,z1,z2,z3,z4,z382,z6]),(0,[z0,z383,z1,z2,z3,z4,z6])],[(0,[z0,z384,z1,z2,z3,z4,z6]),(0,[z385,z0,z1,z2,z3,z4,z6]),(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6]),(0,[z0,z1,z2,z3,z4,z388,z6]),(1,[z0,z1,z2,z3,z96,z114])],[(0,[z0,z1,z2,z3,z4,z6,z369]),(0,[z0,z1,z2,z3,z22,z6,z389]),(0,[z0,z126,z2,z59,z3,z4,z6]),(0,[z390,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z391])],[(0,[z0,z1,z392,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z393,z6]),(0,[z0,z394,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z395,z6]),(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z0,z396,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z69,z6]),(0,[z0,z397,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z104,z3,z47,z6]),(0,[z0,z1,z2,z398,z3,z4,z6]),(0,[z0,z8,z399,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z400,z4,z6])],[(0,[z144,z0,z1,z2,z3,z47,z6]),(0,[z198,z0,z1,z2,z3,z167,z6])],[(0,[z401,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z402,z4,z6]),(0,[z0,z1,z39,z59,z3,z4,z6]),(0,[z0,z403,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z281,z6]),(0,[z0,z161,z1,z2,z3,z96,z4])],[(1,[z0,z1,z2,z3,z270,z6]),(0,[z0,z1,z2,z197,z107,z4,z6]),(0,[z404,z0,z1,z2,z3,z4,z6])],[(0,[z0,z405,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z406,z4,z6])],[(0,[z44,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z45]),(0,[z0,z1,z407,z2,z3,z47,z6]),(1,[z0,z100,z2,z3,z37,z6]),(0,[z0,z1,z2,z408,z3,z4,z6]),(0,[z0,z409,z1,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z410,z6]),(0,[z0,z1,z2,z411,z3,z4,z6]),(0,[z0,z1,z2,z3,z412,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z98])],[(0,[z0,z1,z58,z2,z3,z4,z6]),(0,[z0,z56,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z1,z2,z3,z414,z4,z6])],[(1,[z0,z1,z2,z3,z4,z76]),(0,[z0,z1,z2,z89,z3,z22,z6]),(0,[z415,z0,z1,z2,z3,z4,z6]),(0,[z0,z193,z126,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z416,z6]),(0,[z0,z417,z1,z2,z3,z4,z6]),(0,[z0,z1,z418,z2,z3,z4,z6])],[(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z420,z4,z6]),(0,[z17,z0,z1,z2,z3,z308,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z4,z12,z169]),(0,[z0,z1,z2,z421,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z422,z6])]],
   [[(0,[z0,z423,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z424]),(0,[z0,z1,z2,z3,z425,z4,z6]),(0,[z0,z1,z426,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z427])],[(0,[z0,z161,z1,z2,z54,z4,z6]),(0,[z1,z2,z3,z4,z22,z6,z55]),(0,[z0,z126,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z0,z429,z1,z2,z3,z4,z6]),(0,[z0,z430,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z4,z114])],[(0,[z0,z1,z2,z3,z431,z22,z6]),(0,[z0,z80,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z232]),(0,[z0,z1,z2,z3,z4,z6,z432])],[(0,[z168,z0,z1,z2,z54,z4,z6]),(0,[z0,z1,z2,z433,z3,z4,z6]),(1,[z0,z1,z2,z3,z22,z6]),(0,[z0,z191,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z434,z6])],[(0,[z180,z0,z1,z435,z3,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z436,z6]),(0,[z437,z0,z1,z2,z3,z4,z6]),(0,[z0,z438,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z372,z4,z6]),(0,[z0,z1,z2,z3,z4,z439,z6]),(0,[z86,z0,z1,z59,z3,z4,z6]),(0,[z0,z191,z2,z251,z3,z4,z6]),(0,[z0,z1,z2,z440,z3,z4,z6])],[(0,[z0,z1,z2,z3,z197,z47,z6]),(0,[z72,z0,z1,z2,z3,z22,z6]),(0,[z0,z223,z56,z1,z3,z4,z6])],[(0,[z441,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z39,z2,z3,z4,z132]),(0,[z0,z1,z2,z3,z4,z6,z442])]],
   [[(0,[z0,z443,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z22,z6]),(0,[z198,z0,z1,z2,z3,z4,z6]),(0,[z49,z0,z1,z2,z103,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z444]),(0,[z0,z1,z2,z3,z47,z37,z6]),(0,[z0,z1,z2,z3,z203,z4,z6]),(0,[z0,z445,z1,z2,z3,z4,z6])],[(0,[z49,z198,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z98,z14])],[(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z447,z4,z6]),(0,[z0,z1,z448,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z132])],[(0,[z0,z1,z2,z3,z4,z6,z79]),(0,[z0,z1,z2,z3,z4,z6,z449]),(0,[z0,z450,z1,z2,z3,z4,z6]),(0,[z0,z1,z39,z2,z3,z305,z6]),(0,[z0,z161,z1,z2,z4,z6,z14])],[(0,[z0,z1,z451,z2,z3,z4,z6]),(1,[z17,z1,z2,z3,z22,z6]),(0,[z0,z117,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z60,z22,z6]),(0,[z0,z1,z2,z3,z47,z61,z6]),(0,[z0,z1,z2,z452,z3,z4,z6])],[(0,[z0,z1,z453,z2,z3,z4,z6]),(0,[z0,z454,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z455]),(0,[z0,z1,z2,z3,z4,z6,z456]),(0,[z207,z86,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z457]),(0,[z0,z161,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z166,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z458,z6]),(0,[z0,z193,z1,z2,z3,z22,z6]),(0,[z0,z56,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z459,z6]),(0,[z0,z1,z2,z3,z460,z4,z6]),(0,[z0,z461,z1,z2,z3,z4,z6]),(0,[z0,z1,z462,z2,z3,z4,z6])],[(0,[z17,z0,z1,z2,z3,z4,z171]),(0,[z226,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z463,z6]),(0,[z0,z189,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z89,z3,z47,z6]),(0,[z0,z1,z2,z104,z3,z4,z169]),(0,[z0,z1,z2,z3,z4,z464,z6])],[],[(0,[z0,z1,z2,z54,z107,z4,z6]),(0,[z0,z1,z2,z251,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z465]),(0,[z0,z8,z74,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z466]),(0,[z467,z0,z1,z2,z3,z4,z6]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z235,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z469,z6]),(1,[z0,z88,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z6,z470])],[(0,[z0,z1,z2,z3,z227,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z471]),(1,[z16,z1,z2,z3,z47,z6]),(1,[z0,z1,z2,z3,z50,z6]),(0,[z0,z1,z2,z59,z3,z4,z6]),(0,[z0,z472,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z473,z6]),(0,[z474,z0,z1,z2,z3,z4,z6])],[(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z2,z197,z4,z6]),(1,[z0,z1,z2,z3,z47,z6]),(0,[z477,z0,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z478,z3,z4,z6])],[(0,[z479,z0,z1,z2,z3,z4,z6]),(0,[z0,z399,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z203,z6]),(0,[z0,z1,z480,z2,z3,z4,z6])],[(0,[z72,z0,z1,z2,z3,z47,z6]),(0,[z0,z191,z1,z266,z3,z4,z6]),(0,[z0,z1,z2,z481,z3,z4,z6])],[(1,[z0,z1,z435,z3,z4,z6]),(0,[z0,z482,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z253,z4,z6]),(0,[z168,z1,z2,z3,z197,z4,z6]),(1,[z0,z1,z2,z3,z4,z31]),(0,[z0,z1,z2,z3,z4,z6,z483]),(0,[z16,z1,z2,z3,z47,z4,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(0,[z0,z1,z2,z3,z485,z4,z6]),(0,[z0,z1,z42,z2,z3,z4,z6])],[(0,[z0,z1,z34,z2,z3,z22,z6]),(0,[z1,z2,z54,z3,z197,z4,z6]),(0,[z0,z1,z486,z2,z3,z4,z6]),(0,[z0,z1,z2,z487,z3,z4,z6])],[(1,[z0,z1,z2,z3,z130,z6]),(0,[z0,z488,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z127,z3,z22,z6]),(0,[z207,z0,z1,z2,z107,z4,z6]),(0,[z0,z1,z2,z3,z489,z4,z6])],[],[(0,[z0,z1,z2,z3,z22,z37,z6]),(0,[z0,z1,z3,z305,z4,z9,z6]),(0,[z0,z1,z2,z3,z4,z490,z6])],[(0,[z180,z0,z34,z2,z3,z4,z6]),(0,[z491,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z308,z6]),(0,[z0,z100,z1,z2,z3,z22,z6]),(0,[z0,z126,z1,z39,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z492]),(0,[z0,z161,z1,z2,z104,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z493])]],
   [[(0,[z494,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z3,z22,z6]),(0,[z0,z1,z495,z2,z3,z4,z6]),(0,[z0,z64,z1,z2,z3,z22,z6]),(0,[z0,z11,z1,z2,z3,z22,z6]),(0,[z16,z0,z1,z2,z3,z47,z6]),(0,[z0,z117,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z60,z47,z6]),(0,[z0,z1,z2,z3,z4,z6,z57])],[(0,[z0,z496,z1,z2,z3,z4,z6])],[(0,[z497,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z498,z3,z4,z6]),(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z500]),(1,[z0,z174,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z501])],[(1,[z180,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z230,z6]),(0,[z0,z193,z1,z2,z3,z47,z6]),(0,[z0,z502,z1,z2,z3,z4,z6]),(0,[z0,z503,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z12,z6,z98]),(0,[z144,z504,z1,z2,z3,z4,z6]),(0,[z0,z505,z1,z2,z3,z4,z6])],[(0,[z49,z0,z1,z2,z506,z4,z6]),(0,[z0,z1,z2,z3,z4,z507,z6]),(0,[z0,z508,z1,z2,z3,z4,z6]),(0,[z0,z509,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z60,z4,z6,z98]),(0,[z0,z1,z2,z3,z4,z510,z6])],[(1,[z0,z1,z2,z3,z4,z281]),(0,[z0,z1,z2,z3,z4,z323,z6]),(0,[z72,z1,z2,z3,z4,z22,z6])],[(0,[z180,z0,z136,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z511,z6]),(0,[z0,z1,z2,z3,z512,z4,z6]),(0,[z0,z172,z1,z2,z3,z37,z6])],[(0,[z0,z1,z2,z234,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z513,z6])]],
   [[(1,[z0,z212,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z0,z304,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z7,z47,z6]),(1,[z0,z1,z2,z3,z4,z422]),(0,[z0,z514,z1,z2,z3,z4,z6]),(0,[z0,z515,z1,z2,z3,z4,z6])],[(0,[z0,z1,z516,z2,z3,z4,z6]),(0,[z0,z1,z517,z2,z3,z4,z6]),(0,[z0,z518,z1,z2,z3,z4,z6]),(0,[z0,z126,z80,z1,z3,z4,z6])],[(0,[z0,z1,z519,z2,z3,z4,z6]),(0,[z0,z1,z39,z3,z305,z4,z6]),(0,[z0,z520,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z521,z6]),(0,[z0,z1,z2,z522,z3,z4,z6])],[(0,[z44,z0,z1,z2,z137,z4,z6]),(0,[z17,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z523,z4,z6])],[(0,[z0,z1,z2,z3,z524,z4,z6]),(0,[z0,z525,z1,z2,z3,z4,z6])],[(0,[z0,z212,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z227,z4,z6]),(0,[z526,z0,z1,z2,z3,z4,z6]),(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z528,z1,z2,z3,z4,z6]),(1,[z0,z399,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z529,z6])],[(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z34,z2,z3,z47,z6]),(0,[z530,z0,z1,z2,z3,z4,z6]),(0,[z16,z1,z2,z3,z4,z6,z55]),(0,[z0,z1,z2,z3,z47,z371,z6]),(0,[z207,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z65,z2,z127,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z531])],[(0,[z0,z1,z2,z127,z3,z47,z6]),(0,[z49,z0,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z532,z6]),(0,[z0,z56,z1,z533,z3,z4,z6]),(0,[z0,z1,z2,z3,z534,z4,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z536,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z248,z6]),(0,[z0,z537,z1,z2,z3,z4,z6]),(0,[z538,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z114,z6]),(0,[z539,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z540,z4,z6])],[(0,[z0,z1,z2,z3,z22,z115,z6]),(0,[z0,z1,z2,z3,z131,z22,z6]),(0,[z0,z1,z2,z3,z23,z4,z6]),(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z0,z161,z1,z2,z3,z4,z105])],[(0,[z0,z1,z2,z137,z3,z4,z6]),(0,[z44,z1,z2,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z542]),(0,[z0,z100,z1,z2,z3,z47,z6])],[(0,[z0,z136,z1,z2,z3,z22,z6]),(0,[z543,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z478,z3,z4,z6]),(0,[z0,z1,z2,z3,z544,z4,z6]),(0,[z545,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z435,z3,z4,z6]),(0,[z546,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z547,z6]),(0,[z0,z1,z2,z3,z4,z6,z548])],[(1,[z0,z1,z2,z3,z213,z6]),(0,[z86,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z533,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z549,z6]),(0,[z0,z193,z1,z2,z3,z4,z422]),(0,[z550,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z22,z105,z6]),(0,[z0,z8,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z551,z6])],[(0,[z180,z125,z1,z2,z3,z4,z6]),(0,[z0,z136,z2,z59,z3,z4,z6]),(0,[z0,z1,z552,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z171]),(0,[z0,z1,z2,z3,z4,z553,z6]),(0,[z86,z0,z2,z251,z3,z4,z6]),(0,[z0,z1,z2,z104,z3,z96,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z554,z6]),(0,[z44,z0,z1,z2,z3,z119,z6])],[(0,[z125,z0,z1,z2,z3,z47,z6]),(1,[z168,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z3,z47,z4,z6]),(0,[z0,z191,z1,z2,z251,z4,z6]),(0,[z0,z1,z65,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z555,z4,z6]),(0,[z0,z1,z2,z556,z3,z4,z6]),(0,[z0,z1,z2,z3,z557,z4,z6])],[],[(0,[z180,z0,z1,z2,z3,z97,z6]),(0,[z558,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z559,z4,z6]),(0,[z0,z1,z2,z3,z96,z47,z6]),(1,[z207,z0,z2,z107,z4,z6]),(0,[z0,z1,z2,z3,z560,z4,z6]),(0,[z0,z561,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z6])],[(0,[z168,z0,z1,z2,z3,z120,z6]),(0,[z0,z1,z2,z3,z47,z6,z98]),(0,[z0,z1,z2,z562,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z36,z55]),(0,[z0,z1,z2,z3,z563,z4,z6]),(0,[z0,z1,z564,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z201,z4,z6]),(1,[z0,z1,z321,z3,z4,z6])],[(0,[z0,z1,z2,z3,z47,z200,z6]),(0,[z0,z1,z565,z2,z3,z4,z6]),(0,[z257,z0,z65,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z2,z3,z4,z567,z6])],[(0,[z180,z0,z1,z2,z3,z362,z6]),(1,[z0,z1,z2,z3,z26,z6]),(0,[z17,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z6,z568]),(0,[z0,z1,z2,z3,z47,z169,z6]),(0,[z569,z0,z1,z2,z3,z4,z6]),(1,[z0,z461,z1,z2,z3,z4])],[(0,[z86,z0,z34,z2,z3,z4,z6]),(0,[z16,z1,z2,z3,z197,z4,z6]),(0,[z86,z0,z2,z3,z4,z37,z6]),(0,[z0,z2,z251,z3,z107,z4,z6])]],
   [[(0,[z44,z0,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z570,z4,z6])],[(0,[z0,z571,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z270,z6]),(0,[z44,z0,z1,z141,z3,z4,z6]),(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z573,z1,z2,z3,z4,z6])],[(0,[z0,z1,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z182,z6]),(0,[z0,z11,z1,z65,z3,z4,z6]),(0,[z0,z574,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z575,z3,z4,z6])],[(0,[z0,z1,z576,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z3,z323,z6]),(0,[z86,z0,z126,z2,z3,z4,z6]),(0,[z0,z577,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z578,z3,z4,z6]),(1,[z504,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z107,z4,z6]),(0,[z0,z174,z1,z2,z3,z6,z14])],[(0,[z579,z0,z1,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6]),(0,[z0,z580,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z367,z4,z6]),(0,[z0,z136,z1,z2,z3,z47,z6]),(0,[z86,z0,z136,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z354,z6]),(0,[z581,z0,z1,z2,z3,z4,z6]),(0,[z16,z72,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z582,z6]),(0,[z583,z0,z1,z2,z3,z4,z6]),(0,[z0,z112,z191,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z584,z6])],[(0,[z180,z1,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z585,z6]),(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z0,z1,z229,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z587,z4,z6]),(0,[z0,z588,z1,z2,z3,z4,z6])]],
   [[(0,[z589,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z590,z6]),(0,[z0,z1,z2,z3,z4,z48,z6]),(0,[z0,z1,z591,z2,z3,z4,z6]),(0,[z49,z1,z2,z3,z4,z169,z6]),(0,[z0,z592,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z305,z4,z6])],[(0,[z180,z0,z1,z153,z3,z4,z6]),(0,[z0,z1,z2,z593,z3,z4,z6]),(0,[z0,z1,z2,z594,z3,z4,z6])],[(0,[z17,z1,z2,z3,z4,z22,z6]),(0,[z0,z1,z2,z3,z595,z4,z6]),(0,[z0,z1,z2,z3,z4,z596,z6]),(0,[z597,z0,z1,z2,z3,z4,z6])],[(0,[z0,z193,z1,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z598,z6]),(0,[z0,z1,z42,z3,z4,z6,z98]),(0,[z0,z1,z2,z3,z4,z599,z6]),(0,[z0,z1,z2,z89,z3,z114,z6])],[(0,[z0,z1,z2,z3,z4,z600,z6])],[(0,[z0,z1,z2,z3,z4,z6,z55]),(0,[z0,z1,z2,z3,z96,z4,z98]),(0,[z0,z1,z2,z3,z96,z4,z12]),(0,[z0,z1,z2,z104,z3,z4,z6])],[(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z58,z3,z4,z6]),(0,[z0,z602,z1,z2,z3,z4,z6]),(0,[z144,z0,z1,z2,z3,z4,z6]),(0,[z0,z603,z1,z2,z3,z4,z6]),(0,[z0,z604,z1,z2,z3,z4,z6])],[(0,[z0,z1,z58,z2,z3,z22,z6]),(0,[z0,z605,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z533,z3,z4,z6]),(0,[z606,z0,z1,z2,z3,z4,z6]),(0,[z0,z607,z1,z2,z3,z4,z6])]],
   [[(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z609,z4,z6]),(0,[z0,z1,z610,z2,z3,z4,z6]),(0,[z0,z1,z611,z2,z3,z4,z6])],[(0,[z0,z612,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z600,z22,z6]),(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z126,z1,z3,z4,z6]),(0,[z0,z117,z56,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z614])],[(0,[z0,z1,z2,z3,z22,z200,z6]),(0,[z0,z1,z127,z3,z60,z4,z6]),(0,[z0,z8,z1,z2,z3,z9,z6]),(0,[z144,z0,z1,z2,z3,z200,z6]),(0,[z0,z1,z615,z2,z3,z4,z6])],[(0,[z125,z0,z1,z2,z3,z248,z6]),(0,[z168,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z197,z4,z105,z6]),(0,[z0,z1,z2,z3,z22,z169,z6]),(0,[z0,z370,z1,z2,z3,z47,z6]),(0,[z0,z1,z407,z2,z3,z4,z6]),(0,[z0,z1,z2,z616,z3,z4,z6]),(0,[z617,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z618])],[(1,[z0,z1,z2,z3,z362,z6]),(0,[z21,z1,z58,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z619]),(0,[z0,z1,z2,z3,z4,z6,z620]),(0,[z0,z1,z621,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z14])],[(0,[z0,z1,z2,z3,z130,z4,z6]),(0,[z0,z1,z2,z3,z4,z622,z6]),(0,[z0,z191,z1,z2,z3,z22,z6]),(0,[z0,z175,z1,z2,z3,z4,z6]),(0,[z0,z359,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z9,z6]),(0,[z623,z0,z1,z2,z3,z4,z6])],[(0,[z0,z624,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z625,z3,z4,z6]),(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z198,z0,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z506,z4,z6]),(1,[z0,z80,z59,z3,z4,z6]),(0,[z0,z172,z1,z2,z3,z4,z6]),(0,[z0,z100,z1,z2,z3,z166,z6]),(0,[z0,z1,z2,z321,z3,z4,z6])],[(0,[z1,z2,z3,z47,z4,z22,z6]),(0,[z0,z1,z2,z3,z4,z627,z6]),(0,[z0,z88,z161,z1,z2,z3,z4]),(0,[z0,z88,z1,z2,z3,z4,z19])]],
   [[(0,[z180,z0,z1,z2,z3,z4,z6]),(0,[z0,z628,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z241,z3,z4,z6]),(0,[z0,z80,z2,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z629,z6]),(0,[z0,z1,z2,z3,z4,z105,z98])],[(0,[z0,z1,z2,z630,z3,z4,z6]),(0,[z0,z126,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z631]),(0,[z198,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z389]),(0,[z0,z1,z2,z3,z4,z632,z6]),(0,[z0,z633,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z166,z4,z37,z6]),(0,[z0,z1,z2,z3,z634,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z6])],[(0,[z44,z0,z1,z58,z3,z4,z6]),(0,[z168,z0,z1,z2,z197,z4,z6]),(0,[z0,z11,z1,z59,z3,z4,z6]),(1,[z0,z1,z229,z3,z4,z6]),(0,[z0,z1,z65,z2,z60,z4,z6]),(0,[z0,z635,z1,z2,z3,z4,z6])],[(0,[z636,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z637,z3,z4,z6]),(0,[z0,z1,z638,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z402,z47,z6]),(1,[z0,z1,z2,z3,z167,z6]),(0,[z0,z161,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z639,z6])],[(0,[z168,z17,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z640,z4,z6]),(0,[z0,z1,z268,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z50,z6]),(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z0,z642,z1,z2,z3,z4,z6])],[(0,[z0,z643,z1,z2,z3,z4,z6]),(1,[z125,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z197,z4,z6]),(0,[z0,z1,z2,z3,z644,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z105])],[(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z649])]],
   [[(0,[z0,z1,z2,z3,z4,z650,z6]),(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z0,z1,z652,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z653,z6])],[(1,[z0,z1,z2,z3,z4,z369]),(0,[z654,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z289])],[(0,[z655,z0,z1,z2,z3,z4,z6]),(0,[z656,z0,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z47,z22,z6]),(0,[z0,z1,z2,z3,z4,z55,z98]),(0,[z0,z1,z657,z2,z3,z4,z6]),(1,[z144,z0,z1,z2,z200,z6])],[(0,[z0,z658,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z659,z6]),(0,[z0,z161,z1,z2,z3,z4,z14])],[(0,[z0,z1,z2,z3,z660,z4,z6]),(0,[z661,z0,z1,z2,z3,z4,z6]),(1,[z49,z1,z2,z3,z22,z6]),(0,[z285,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z662,z6]),(0,[z207,z0,z1,z2,z251,z4,z6])],[(0,[z0,z1,z663,z2,z3,z4,z6]),(0,[z0,z1,z2,z103,z3,z4,z6])],[(0,[z0,z1,z2,z3,z47,z201,z6]),(0,[z664,z0,z1,z2,z3,z4,z6])],[(1,[z21,z1,z58,z3,z4,z6]),(0,[z17,z1,z2,z54,z3,z4,z6]),(0,[z0,z665,z1,z2,z3,z4,z6]),(0,[z0,z1,z666,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z372,z3,z4,z6]),(1,[z0,z1,z2,z3,z119,z6]),(0,[z0,z1,z2,z54,z3,z4,z6]),(0,[z0,z191,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z6,z667]),(0,[z0,z56,z1,z2,z3,z4,z6]),(1,[z0,z56,z2,z3,z4,z57]),(0,[z0,z1,z2,z3,z668,z4,z6]),(1,[z0,z117,z2,z3,z4,z36])],[(0,[z0,z1,z2,z669,z3,z4,z6]),(0,[z0,z670,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z251,z3,z47,z6]),(0,[z0,z461,z1,z2,z3,z4,z200]),(0,[z0,z1,z2,z3,z4,z671,z6]),(1,[z0,z161,z1,z2,z4,z14])],[(0,[z0,z34,z2,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z9,z6]),(0,[z0,z1,z39,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z672,z4,z6])],[(1,[z17,z1,z2,z54,z4,z6])],[(0,[z0,z1,z2,z3,z673,z4,z6]),(0,[z0,z1,z42,z2,z3,z22,z6]),(1,[z0,z1,z2,z3,z327,z6]),(0,[z0,z504,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z45,z6]),(0,[z0,z1,z2,z54,z4,z105,z6]),(0,[z0,z1,z2,z3,z431,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z0,z100,z172,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z96,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z506,z4,z6]),(0,[z0,z1,z2,z4,z105,z6,z14])],[(0,[z0,z1,z59,z127,z3,z4,z6]),(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z478,z2,z3,z4,z6])]],
   [[(0,[z0,z676,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z197,z60,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z677]),(0,[z0,z1,z2,z3,z678,z4,z6]),(0,[z0,z1,z2,z104,z3,z4,z105])],[(0,[z0,z1,z2,z679,z3,z4,z6]),(0,[z0,z1,z2,z251,z54,z4,z6]),(0,[z0,z1,z2,z3,z47,z36,z6]),(0,[z0,z1,z2,z680,z3,z4,z6]),(0,[z0,z1,z2,z3,z681,z4,z6]),(0,[z144,z0,z88,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z682,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z683]),(0,[z0,z1,z2,z3,z684,z4,z6])],[(0,[z0,z1,z2,z685,z3,z4,z6]),(0,[z0,z1,z2,z3,z686,z4,z6])],[(0,[z0,z1,z2,z3,z687,z4,z6]),(0,[z0,z1,z2,z3,z688,z4,z6]),(0,[z0,z1,z2,z3,z689,z4,z6])],[(0,[z0,z1,z2,z3,z96,z114,z6])],[(0,[z0,z1,z2,z141,z3,z47,z6]),(0,[z49,z0,z1,z2,z3,z22,z6]),(0,[z0,z11,z1,z2,z3,z47,z6]),(0,[z690,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z691,z6])],[(0,[z0,z319,z1,z2,z3,z4,z6]),(0,[z692,z0,z1,z2,z3,z4,z6]),(1,[z0,z33,z2,z3,z4,z6])]],
   [[(0,[z0,z693,z1,z2,z3,z4,z6]),(0,[z0,z1,z694,z2,z3,z4,z6]),(0,[z16,z0,z1,z2,z3,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6]),(0,[z0,z117,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z60,z4,z6]),(0,[z696,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z232,z6])],[(0,[z697,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z698,z3,z4,z6])],[(0,[z699,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z127,z54,z4,z6]),(0,[z0,z1,z2,z700,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z184,z6])],[(0,[z0,z1,z2,z3,z201,z22,z6]),(0,[z0,z701,z1,z2,z3,z4,z6]),(0,[z0,z702,z1,z2,z3,z4,z6]),(0,[z0,z1,z65,z127,z3,z4,z6]),(0,[z144,z0,z1,z2,z3,z201,z6]),(0,[z0,z1,z2,z3,z4,z6,z703])],[(0,[z1,z2,z3,z197,z4,z22,z6]),(0,[z88,z29,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z213,z6]),(0,[z0,z1,z2,z3,z96,z4,z114]),(0,[z0,z1,z2,z3,z4,z6,z704])],[(0,[z0,z1,z2,z3,z4,z705,z6]),(0,[z144,z0,z1,z2,z89,z4,z6])],[(0,[z0,z1,z706,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z104,z3,z4])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z193,z1,z60,z47,z6]),(0,[z0,z1,z2,z241,z201,z6]),(0,[z0,z1,z708,z3,z4,z6])],[(0,[z0,z1,z39,z3,z431,z6]),(0,[z0,z2,z3,z166,z709,z6]),(0,[z0,z1,z3,z4,z710,z6])],[(0,[z0,z1,z2,z3,z119,z369]),(0,[z1,z2,z3,z711,z22,z6]),(0,[z0,z1,z229,z3,z4,z6]),(1,[z0,z1,z2,z4,z712])],[(0,[z0,z1,z2,z3,z167,z6]),(0,[z0,z189,z2,z3,z253,z6])],[(0,[z713,z0,z1,z2,z22,z6]),(0,[z0,z1,z2,z3,z22,z132]),(0,[z0,z1,z2,z714,z4,z6]),(0,[z496,z1,z2,z3,z47,z6]),(0,[z0,z1,z59,z3,z4,z289])],[(0,[z125,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z0,z1,z2,z3,z4,z716]),(0,[z717,z1,z2,z3,z4,z6])],[(0,[z0,z1,z153,z3,z4,z6]),(0,[z44,z212,z141,z3,z4,z6]),(0,[z0,z1,z2,z679,z4,z105]),(0,[z0,z1,z2,z3,z22,z718]),(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z1,z2,z3,z6,z720]),(0,[z0,z1,z2,z104,z4,z105])],[(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z2,z722,z4,z6]),(0,[z285,z1,z2,z197,z22,z6]),(0,[z17,z1,z2,z54,z4,z171]),(0,[z265,z1,z2,z3,z22,z6]),(0,[z723,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z369]),(0,[z1,z2,z3,z197,z120,z6]),(0,[z0,z1,z2,z3,z131,z182])],[(0,[z16,z1,z2,z3,z4,z171]),(0,[z1,z2,z3,z47,z22,z6]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z4,z725])],[(0,[z0,z1,z726,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z76]),(0,[z0,z1,z2,z3,z4,z171]),(0,[z538,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z727,z4,z6]),(0,[z207,z0,z266,z3,z4,z6]),(0,[z0,z1,z2,z3,z728,z6]),(0,[z0,z1,z2,z3,z729,z6])],[(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z1,z2,z3,z731,z6]),(0,[z49,z1,z2,z3,z22,z6]),(0,[z49,z1,z2,z506,z22,z6]),(0,[z0,z1,z663,z3,z4,z98])],[(0,[z0,z1,z2,z3,z4,z732]),(0,[z0,z1,z2,z3,z733,z6]),(0,[z1,z2,z3,z734,z4,z6]),(0,[z0,z1,z2,z3,z47,z735]),(0,[z0,z1,z283,z3,z4,z98]),(0,[z0,z88,z1,z2,z3,z297])],[(0,[z0,z1,z2,z736,z4,z6]),(0,[z0,z1,z2,z737,z4,z6]),(0,[z0,z738,z2,z3,z47,z6]),(0,[z198,z1,z2,z3,z4,z739]),(0,[z0,z1,z2,z740,z4,z6]),(0,[z0,z1,z741,z2,z3,z4]),(0,[z742,z1,z2,z3,z4,z6]),(0,[z504,z88,z1,z2,z3,z6])],[(0,[z16,z1,z2,z3,z734,z6]),(0,[z0,z1,z2,z3,z47,z232]),(0,[z0,z223,z56,z3,z4,z57]),(0,[z0,z1,z2,z3,z4,z743]),(0,[z0,z8,z399,z3,z9,z6]),(0,[z0,z1,z2,z3,z4,z184])],[(0,[z0,z1,z2,z3,z119,z6]),(0,[z0,z1,z744,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z745]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z147,z1,z2,z3,z47,z6]),(0,[z746,z1,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z413,z22,z6]),(0,[z0,z1,z747,z3,z4,z6]),(0,[z0,z161,z1,z2,z4,z14])],[(0,[z0,z1,z748,z3,z4,z6]),(0,[z0,z1,z2,z372,z47,z6]),(0,[z21,z1,z749,z3,z4,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z751,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z1,z753,z3,z4,z6]),(0,[z1,z2,z575,z3,z22,z6]),(0,[z0,z193,z1,z60,z4,z422])],[(0,[z0,z1,z435,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z754]),(0,[z0,z1,z2,z3,z755,z6]),(0,[z0,z1,z2,z3,z22,z31]),(0,[z0,z1,z2,z506,z327,z6])],[(0,[z664,z1,z2,z3,z22,z6]),(0,[z16,z1,z2,z506,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z1,z756,z2,z3,z4,z6]),(0,[z0,z1,z2,z506,z4,z6]),(0,[z0,z757,z1,z2,z3,z4])],[(0,[z1,z2,z3,z750,z22,z6]),(0,[z0,z758,z2,z3,z4,z6])],[(0,[z180,z34,z2,z3,z4,z76]),(0,[z0,z759,z1,z2,z3,z4]),(0,[z0,z1,z760,z3,z4,z6]),(0,[z1,z2,z3,z167,z6,z55]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z0,z1,z2,z3,z4,z762])]],
   [[(0,[z0,z763,z2,z3,z4,z6]),(0,[z0,z764,z1,z3,z4,z6])],[(0,[z0,z206,z2,z227,z4,z6]),(0,[z0,z1,z2,z234,z600,z6]),(0,[z0,z1,z2,z765,z4,z6])],[(0,[z44,z1,z141,z3,z270,z6]),(0,[z0,z766,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z767,z6]),(0,[z583,z1,z2,z197,z4,z6]),(0,[z17,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z6,z768]),(0,[z0,z1,z2,z3,z769,z19])],[(0,[z180,z34,z2,z3,z22,z6]),(0,[z44,z1,z141,z3,z4,z45])],[(0,[z661,z0,z2,z107,z4,z6]),(0,[z0,z1,z2,z3,z26,z171]),(0,[z17,z1,z2,z3,z22,z31]),(0,[z332,z0,z59,z3,z4,z6]),(0,[z0,z33,z127,z3,z4,z6]),(0,[z770,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z2,z13,z14])],[(0,[z0,z1,z2,z3,z4,z771]),(0,[z180,z34,z2,z372,z4,z6]),(0,[z0,z1,z2,z3,z22,z281]),(0,[z1,z2,z3,z22,z598,z6]),(0,[z0,z319,z2,z3,z48,z6]),(0,[z0,z772,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z773,z6]),(0,[z0,z774,z2,z3,z4,z6]),(0,[z298,z1,z2,z3,z22,z6]),(0,[z0,z775,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z372,z4,z281])],[(0,[z0,z212,z2,z3,z22,z6]),(0,[z1,z58,z749,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z422]),(0,[z0,z100,z2,z3,z48,z6]),(0,[z776,z1,z2,z3,z4,z6]),(0,[z0,z8,z1,z3,z9,z6]),(0,[z0,z1,z2,z3,z114,z769])],[(0,[z0,z1,z777,z3,z4,z6]),(0,[z1,z2,z3,z22,z6,z79]),(0,[z1,z2,z3,z412,z47,z6])],[(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z1,z779,z3,z4,z6])],[(0,[z0,z1,z2,z3,z780,z6]),(0,[z0,z1,z2,z3,z4,z781]),(0,[z302,z1,z2,z3,z22,z6]),(0,[z361,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z782,z6])],[(0,[z0,z1,z783,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z784])],[(0,[z0,z1,z2,z227,z22,z6]),(0,[z0,z759,z1,z2,z3,z22]),(0,[z0,z399,z2,z3,z22,z6])],[(0,[z0,z461,z1,z2,z3,z47]),(0,[z217,z1,z2,z3,z47,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z785])],[(0,[z0,z786,z1,z3,z4,z6]),(0,[z161,z1,z2,z197,z22,z6])],[(0,[z0,z1,z2,z3,z6,z787]),(0,[z0,z788,z1,z2,z3,z6]),(0,[z385,z1,z2,z3,z22,z6]),(0,[z0,z518,z2,z3,z4,z36]),(0,[z0,z1,z2,z789,z4,z6]),(0,[z0,z1,z2,z3,z790,z6])],[(0,[z0,z1,z2,z791,z4,z6]),(0,[z29,z1,z2,z3,z4,z6]),(0,[z226,z0,z1,z2,z61,z6]),(0,[z0,z1,z266,z3,z4,z6]),(0,[z792,z1,z2,z3,z4,z6]),(0,[z0,z100,z2,z3,z709,z6])],[(0,[z0,z1,z153,z3,z97,z6]),(0,[z0,z1,z478,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z794,z4,z6])],[(0,[z0,z1,z2,z3,z270,z45]),(0,[z795,z1,z2,z3,z4,z6])],[(0,[z796,z0,z2,z3,z4,z6]),(0,[z1,z2,z3,z197,z22,z6]),(0,[z479,z1,z2,z3,z22,z6]),(0,[z0,z1,z533,z3,z22,z6])],[(0,[z0,z1,z153,z3,z362,z6]),(0,[z180,z34,z2,z3,z47,z6]),(0,[z1,z749,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z797,z6]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z0,z1,z279,z3,z4,z6])]],
   [[(0,[z0,z1,z42,z3,z47,z98]),(0,[z0,z1,z407,z3,z305,z6]),(0,[z1,z2,z3,z4,z739,z55])],[(0,[z0,z1,z2,z3,z47,z281]),(0,[z0,z799,z2,z3,z22,z6]),(0,[z0,z223,z1,z3,z47,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z0,z1,z2,z801,z200,z6])],[(0,[z168,z1,z2,z197,z22,z6]),(0,[z477,z1,z2,z3,z47,z6]),(0,[z802,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z803,z6]),(0,[z263,z1,z2,z3,z327,z6]),(0,[z0,z59,z398,z3,z4,z6])],[(0,[z0,z212,z2,z3,z47,z6]),(0,[z0,z804,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z422]),(0,[z0,z1,z2,z3,z4,z289]),(0,[z0,z1,z2,z3,z4,z805])],[(0,[z0,z1,z435,z3,z4,z281]),(0,[z72,z1,z2,z3,z22,z6]),(0,[z263,z1,z2,z3,z4,z6]),(0,[z0,z1,z806,z3,z22,z6]),(0,[z0,z1,z321,z3,z22,z6]),(0,[z0,z126,z1,z3,z4,z132]),(0,[z807,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z808,z6])],[(0,[z0,z809,z1,z3,z4,z6]),(1,[z810,z1,z2,z3,z6]),(0,[z0,z811,z1,z3,z4,z6])],[(0,[z0,z812,z1,z3,z4,z6]),(0,[z147,z1,z2,z3,z26,z6]),(0,[z198,z1,z2,z3,z167,z55]),(0,[z0,z1,z2,z3,z813,z6])]],
   [[(0,[z0,z1,z2,z137,z4,z369]),(0,[z17,z1,z2,z54,z308,z6]),(0,[z49,z1,z2,z3,z327,z169]),(0,[z0,z1,z814,z2,z3,z4]),(0,[z0,z1,z3,z4,z815,z98])],[(0,[z0,z399,z2,z3,z47,z6]),(0,[z0,z1,z2,z816,z4,z6])],[(0,[z0,z1,z2,z367,z4,z76]),(0,[z0,z1,z2,z4,z817,z6]),(0,[z0,z818,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z819,z6]),(0,[z49,z1,z2,z3,z4,z169]),(0,[z0,z820,z1,z2,z4,z6]),(0,[z0,z1,z39,z3,z305,z6])],[(0,[z0,z1,z2,z3,z308,z6]),(0,[z515,z1,z2,z3,z22,z6]),(0,[z0,z821,z1,z3,z4,z6]),(0,[z0,z1,z65,z127,z4,z6])],[(0,[z0,z1,z2,z372,z4,z76]),(0,[z0,z1,z2,z822,z4,z6]),(0,[z504,z1,z2,z3,z22,z6]),(0,[z0,z74,z3,z4,z9,z6])],[(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z824,z2,z3,z4,z6]),(0,[z0,z825,z1,z3,z4,z6])],[(0,[z180,z34,z2,z3,z4,z281]),(0,[z146,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z104,z4,z632]),(0,[z0,z1,z826,z3,z4,z6]),(0,[z0,z172,z2,z3,z166,z6]),(0,[z0,z520,z1,z60,z4,z6]),(0,[z144,z0,z461,z1,z2,z200])],[(0,[z0,z1,z2,z367,z22,z6]),(0,[z0,z1,z2,z137,z119,z6]),(0,[z0,z1,z478,z3,z47,z6]),(0,[z0,z1,z59,z3,z4,z132]),(0,[z0,z1,z2,z104,z4,z490]),(0,[z0,z1,z2,z3,z4,z769])]],
   [[(0,[z1,z2,z197,z60,z22,z6]),(0,[z0,z403,z1,z3,z9,z6]),(1,[z0,z1,z2,z3,z769])],[(0,[z0,z1,z2,z3,z323,z6]),(0,[z0,z827,z2,z3,z4,z6]),(0,[z1,z2,z679,z3,z22,z6]),(0,[z0,z1,z533,z3,z47,z6])],[(0,[z0,z828,z1,z2,z3,z22]),(0,[z0,z829,z2,z3,z47,z6]),(0,[z0,z1,z830,z3,z4,z6]),(0,[z0,z56,z2,z3,z4,z831]),(0,[z0,z1,z42,z3,z4,z815]),(0,[z832,z1,z2,z3,z4,z6])],[(0,[z0,z1,z833,z3,z4,z6])],[(0,[z0,z1,z834,z3,z22,z6]),(0,[z0,z74,z2,z3,z22,z6]),(0,[z0,z1,z2,z835,z4,z6]),(0,[z0,z1,z2,z3,z836,z6])],[(0,[z0,z1,z2,z3,z837,z6]),(0,[z0,z1,z2,z137,z4,z6]),(0,[z168,z1,z2,z197,z47,z6]),(0,[z0,z88,z1,z2,z3,z79])],[(0,[z0,z1,z2,z3,z838,z6]),(0,[z0,z1,z2,z839,z4,z6]),(0,[z306,z1,z2,z3,z4,z55]),(0,[z0,z2,z3,z709,z37,z6]),(0,[z0,z520,z1,z2,z4,z14]),(0,[z0,z1,z2,z3,z801,z6]),(0,[z0,z1,z840,z3,z4,z6])],[(0,[z207,z0,z2,z107,z47,z6]),(0,[z0,z1,z2,z103,z4,z55]),(0,[z0,z1,z2,z3,z4,z841])]],
   [[(0,[z0,z161,z1,z2,z4,z67]),(0,[z0,z1,z3,z4,z6,z842]),(0,[z1,z2,z3,z22,z6,z542]),(0,[z675,z1,z2,z3,z22,z6]),(0,[z0,z1,z321,z3,z47,z6])],[(0,[z198,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z1,z844,z3,z4,z6]),(0,[z0,z1,z2,z3,z845,z6]),(0,[z0,z1,z2,z3,z6,z13])],[(0,[z0,z1,z2,z3,z47,z45]),(0,[z0,z1,z3,z846,z22,z6]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z848,z3,z4,z6]),(0,[z0,z1,z2,z849,z4,z6]),(0,[z0,z1,z2,z3,z850,z6]),(0,[z0,z1,z2,z3,z4,z712])],[(0,[z0,z1,z2,z3,z851,z6]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z17,z1,z2,z3,z120,z6]),(0,[z701,z1,z2,z3,z22,z6]),(0,[z1,z2,z3,z4,z169,z739]),(0,[z853,z0,z1,z2,z3,z6])],[(0,[z1,z2,z3,z22,z551,z6])],[(0,[z0,z206,z2,z3,z4,z369]),(0,[z1,z2,z3,z22,z6,z171]),(0,[z257,z0,z2,z3,z4,z6]),(0,[z0,z193,z1,z794,z4,z6]),(0,[z0,z1,z347,z3,z4,z98])],[(0,[z44,z1,z141,z227,z4,z6]),(0,[z164,z1,z2,z3,z22,z6])],[(0,[z0,z80,z59,z3,z22,z6]),(0,[z504,z1,z2,z3,z47,z6]),(0,[z0,z854,z1,z3,z4,z6]),(0,[z0,z33,z3,z4,z6,z98])]],
   [[(0,[z0,z1,z855,z3,z4,z6]),(0,[z0,z856,z2,z3,z4,z6])],[(0,[z0,z1,z435,z3,z4,z76]),(0,[z0,z857,z2,z3,z22,z6]),(0,[z285,z0,z1,z2,z200,z6]),(0,[z0,z1,z2,z3,z4,z858]),(0,[z0,z172,z2,z3,z709,z6])],[(0,[z0,z1,z2,z367,z47,z6]),(0,[z0,z1,z2,z859,z4,z6]),(0,[z0,z1,z2,z3,z860,z6]),(0,[z1,z2,z3,z22,z36,z55]),(0,[z0,z174,z1,z2,z104,z3])],[(0,[z861,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z862,z6]),(0,[z863,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z864,z4,z6]),(0,[z151,z136,z2,z3,z4,z6]),(0,[z0,z206,z2,z3,z119,z6]),(0,[z0,z1,z229,z3,z22,z6]),(0,[z118,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z865,z4,z6]),(0,[z0,z1,z2,z3,z4,z866])],[(0,[z1,z2,z3,z684,z47,z6]),(0,[z0,z825,z59,z3,z4,z6]),(0,[z0,z867,z2,z3,z4,z6]),(0,[z868,z1,z2,z3,z4,z6]),(0,[z0,z161,z1,z321,z4,z14]),(0,[z0,z1,z2,z3,z869,z6]),(0,[z0,z1,z2,z3,z96,z114])],[(0,[z0,z1,z870,z3,z4,z6]),(0,[z0,z1,z426,z3,z4,z98]),(0,[z0,z1,z2,z3,z4,z871])],[(0,[z125,z136,z2,z3,z22,z6]),(0,[z0,z1,z268,z3,z431,z6]),(0,[z0,z1,z872,z3,z47,z6]),(0,[z0,z757,z1,z2,z3,z47]),(0,[z0,z1,z2,z3,z4,z873]),(0,[z0,z1,z2,z3,z4,z874])]],
   [[(0,[z0,z1,z435,z372,z4,z6]),(0,[z1,z2,z3,z46,z22,z6]),(0,[z0,z1,z2,z104,z22,z105]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z0,z193,z1,z60,z4,z6])],[(0,[z49,z1,z2,z3,z22,z55]),(0,[z0,z1,z2,z3,z22,z876]),(0,[z277,z1,z2,z3,z47,z6]),(0,[z877,z174,z1,z2,z3,z6])],[(0,[z0,z206,z2,z3,z4,z6]),(0,[z0,z212,z2,z3,z270,z6]),(0,[z0,z1,z2,z3,z22,z369]),(0,[z0,z1,z2,z3,z47,z132]),(0,[z0,z1,z2,z878,z4,z6]),(0,[z0,z1,z879,z3,z4,z6])],[(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z2,z104,z4,z712])],[(0,[z0,z212,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z882,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z883,z6])],[(0,[z0,z206,z141,z3,z4,z6]),(0,[z415,z1,z58,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z17,z1,z2,z294,z4,z6])],[(0,[z1,z2,z3,z47,z148,z6]),(0,[z0,z885,z2,z3,z4,z6])],[(0,[z180,z34,z2,z367,z4,z6]),(0,[z0,z1,z2,z227,z270,z6]),(0,[z0,z1,z209,z127,z4,z6]),(0,[z0,z1,z2,z3,z47,z886]),(0,[z0,z887,z1,z3,z4,z6])]],
   [[(0,[z0,z888,z2,z3,z4,z6]),(0,[z21,z1,z58,z3,z22,z6])],[(0,[z0,z1,z2,z367,z4,z281]),(0,[z0,z1,z889,z3,z4,z6]),(0,[z0,z1,z2,z227,z4,z45]),(0,[z0,z2,z3,z4,z890,z6]),(0,[z0,z56,z2,z3,z22,z57]),(0,[z0,z117,z2,z3,z22,z36]),(0,[z49,z1,z2,z103,z4,z169]),(0,[z0,z1,z2,z3,z891,z6]),(0,[z0,z810,z1,z2,z3,z6])],[(0,[z49,z1,z2,z3,z711,z6]),(0,[z0,z161,z1,z2,z22,z14]),(0,[z0,z80,z59,z3,z47,z6]),(0,[z0,z88,z1,z2,z3,z769])],[(0,[z0,z601,z59,z3,z4,z6]),(0,[z1,z2,z3,z22,z6,z55]),(0,[z0,z1,z2,z3,z892,z6])],[(0,[z17,z1,z2,z54,z22,z6]),(0,[z49,z1,z2,z3,z167,z6]),(0,[z0,z1,z321,z3,z4,z169]),(0,[z0,z193,z1,z27,z4,z6]),(0,[z0,z1,z893,z3,z4,z6]),(0,[z0,z174,z161,z1,z2,z3])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z738,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z232]),(0,[z0,z161,z1,z478,z4,z14])],[(0,[z0,z1,z2,z3,z22,z6]),(0,[z0,z896,z2,z3,z4,z6]),(0,[z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z506,z22,z6]),(0,[z0,z1,z229,z3,z47,z6]),(0,[z0,z1,z2,z4,z6,z897]),(0,[z0,z1,z3,z60,z4,z289])]],
   [[(0,[z0,z628,z1,z60,z4,z6])],[(0,[z0,z1,z435,z3,z47,z6]),(0,[z1,z2,z197,z22,z105,z6]),(0,[z0,z1,z2,z3,z47,z31]),(0,[z1,z2,z3,z506,z22,z6]),(0,[z0,z1,z760,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z831]),(0,[z0,z1,z898,z3,z4,z6])],[(0,[z0,z1,z2,z3,z899,z6]),(0,[z0,z1,z2,z3,z4,z900]),(0,[z1,z2,z3,z22,z111,z6])],[(0,[z0,z1,z2,z901,z4,z6]),(0,[z0,z1,z2,z3,z902,z6]),(0,[z0,z1,z903,z3,z4,z6]),(0,[z1,z2,z104,z3,z22,z55]),(0,[z0,z1,z2,z3,z904,z6]),(0,[z29,z161,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z906,z1,z2,z3,z6]),(0,[z0,z267,z59,z3,z4,z6]),(0,[z0,z1,z907,z3,z4,z6])],[(0,[z0,z908,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z909]),(0,[z0,z62,z59,z3,z4,z6])],[(0,[z0,z1,z127,z794,z4,z6])],[(0,[z0,z1,z2,z3,z362,z281]),(0,[z161,z1,z2,z3,z22,z55]),(0,[z0,z910,z2,z3,z4,z6]),(0,[z0,z1,z2,z911,z4,z6]),(0,[z0,z1,z912,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z22,z632,z6]),(0,[z0,z33,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z0,z2,z816,z107,z4,z6]),(0,[z0,z1,z2,z3,z914,z6])],[(0,[z17,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z54,z4,z31]),(0,[z0,z774,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z2,z3,z4,z916])],[(0,[z0,z1,z2,z917,z4,z6]),(0,[z285,z1,z2,z197,z4,z6]),(0,[z664,z1,z2,z54,z4,z6]),(0,[z0,z1,z2,z89,z201,z6]),(0,[z88,z29,z1,z2,z3,z19])],[(0,[z21,z1,z58,z3,z47,z6]),(0,[z0,z1,z2,z3,z308,z171]),(0,[z1,z2,z163,z3,z22,z6]),(1,[z0,z1,z3,z710,z6])],[(0,[z125,z136,z2,z3,z323,z6]),(0,[z0,z676,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z918]),(1,[z1,z2,z3,z22,z171]),(0,[z0,z1,z3,z4,z6,z919]),(0,[z0,z56,z2,z3,z47,z57]),(0,[z0,z117,z2,z3,z47,z36]),(0,[z0,z1,z2,z3,z920,z6]),(0,[z0,z921,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z922]),(0,[z168,z1,z2,z197,z354,z6]),(0,[z0,z161,z1,z2,z47,z14]),(0,[z0,z1,z2,z3,z923,z6])],[(0,[z180,z34,z435,z3,z4,z6]),(0,[z0,z828,z1,z2,z3,z4]),(0,[z0,z1,z2,z924,z4,z6]),(0,[z0,z1,z2,z89,z801,z6])],[(0,[z17,z1,z2,z54,z47,z6]),(0,[z285,z0,z1,z2,z230,z6]),(0,[z1,z2,z3,z925,z4,z6])]],
   [[(0,[z1,z2,z3,z22,z55,z98]),(0,[z0,z1,z2,z926,z3,z4]),(0,[z0,z1,z794,z60,z4,z6]),(0,[z144,z147,z1,z2,z200,z6]),(0,[z0,z88,z1,z2,z3,z19])],[(0,[z21,z1,z58,z3,z130,z6]),(0,[z17,z1,z2,z197,z22,z6]),(0,[z16,z1,z2,z3,z47,z6]),(0,[z122,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z50,z6]),(0,[z0,z1,z2,z506,z50,z6]),(0,[z0,z633,z59,z3,z4,z6])],[(0,[z0,z1,z2,z3,z47,z6]),(0,[z390,z1,z2,z197,z4,z6]),(0,[z927,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z831,z6]),(0,[z928,z0,z2,z3,z4,z6])],[(0,[z756,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z929])],[(0,[z0,z1,z2,z227,z47,z6]),(0,[z0,z1,z2,z3,z4,z930])],[(0,[z0,z1,z2,z3,z931,z6]),(0,[z29,z1,z2,z3,z22,z6]),(0,[z550,z1,z2,z3,z22,z6]),(0,[z49,z1,z2,z506,z4,z169]),(0,[z164,z1,z2,z3,z4,z169])],[(0,[z0,z1,z932,z3,z4,z6]),(0,[z0,z1,z3,z4,z815,z6]),(0,[z0,z1,z933,z3,z4,z6])],[(1,[z1,z2,z506,z22,z6]),(0,[z0,z403,z2,z3,z37,z6]),(0,[z0,z934,z2,z3,z4,z6]),(0,[z29,z1,z2,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z130,z6])],[(0,[z0,z1,z935,z3,z4,z6]),(0,[z0,z936,z2,z3,z4,z6]),(0,[z29,z1,z2,z3,z96,z6])],[(0,[z0,z1,z937,z3,z4,z6]),(0,[z0,z1,z2,z938,z4,z6]),(0,[z44,z1,z141,z3,z4,z369])],[(0,[z0,z1,z2,z939,z4,z6]),(0,[z0,z1,z2,z3,z940,z6]),(0,[z0,z33,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z941,z6])],[(0,[z125,z136,z2,z3,z248,z6]),(0,[z1,z2,z197,z600,z22,z6]),(0,[z0,z1,z2,z3,z942,z22]),(0,[z0,z1,z2,z3,z22,z943]),(0,[z0,z189,z2,z3,z166,z6])],[(0,[z0,z944,z2,z3,z4,z6]),(0,[z0,z1,z2,z945,z4,z6]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z810,z1,z2,z3,z6,z14])],[(0,[z63,z1,z2,z3,z4,z55]),(0,[z0,z450,z1,z3,z4,z98]),(0,[z0,z1,z2,z947,z4,z6])],[(0,[z180,z34,z2,z3,z4,z6]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z692,z1,z2,z3,z22,z6])]],
   [[(0,[z0,z34,z435,z3,z4,z6]),(0,[z0,z1,z2,z3,z97,z76]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z49,z1,z2,z3,z4,z739]),(0,[z0,z1,z2,z3,z4,z950]),(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z1,z42,z3,z4,z98]),(0,[z0,z1,z2,z3,z6,z769])],[(0,[z0,z1,z2,z3,z4,z281]),(0,[z0,z1,z952,z3,z4,z6]),(0,[z44,z1,z141,z3,z119,z6]),(0,[z0,z1,z2,z953,z4,z6]),(0,[z0,z223,z1,z3,z4,z6]),(0,[z504,z1,z2,z3,z114,z6])],[(0,[z0,z1,z2,z3,z954,z6]),(0,[z0,z206,z2,z137,z4,z6]),(0,[z0,z359,z1,z3,z115,z6]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z1,z2,z4,z6,z956]),(0,[z0,z1,z321,z3,z96,z4])],[(0,[z0,z1,z2,z3,z4,z957]),(0,[z0,z1,z2,z3,z362,z76]),(0,[z1,z2,z3,z958,z4,z6]),(0,[z0,z1,z2,z3,z959,z6]),(0,[z0,z8,z74,z3,z9,z6])],[(0,[z0,z212,z2,z3,z4,z6]),(0,[z0,z1,z2,z960,z4,z6]),(0,[z0,z1,z2,z3,z961,z6]),(0,[z1,z2,z3,z22,z691,z6]),(0,[z0,z88,z1,z2,z3,z618])],[(0,[z183,z1,z2,z3,z47,z6])],[(0,[z0,z212,z2,z227,z4,z6]),(0,[z0,z1,z2,z103,z22,z6]),(0,[z0,z175,z2,z3,z37,z6])],[(0,[z0,z136,z435,z3,z4,z6]),(0,[z0,z1,z2,z372,z97,z6]),(0,[z44,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z22,z817,z6]),(0,[z0,z100,z229,z3,z37,z6])]],
   [[(0,[z0,z1,z2,z3,z962,z6]),(1,[z1,z749,z3,z4,z6]),(0,[z168,z1,z2,z963,z4,z6]),(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z965,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z83])],[(0,[z0,z1,z2,z3,z26,z31]),(0,[z0,z112,z1,z3,z22,z6])],[(0,[z0,z1,z2,z372,z362,z6]),(0,[z21,z1,z58,z3,z213,z6]),(0,[z0,z1,z2,z4,z105,z712])],[(0,[z0,z1,z2,z3,z270,z369]),(0,[z0,z1,z321,z54,z4,z6]),(0,[z1,z2,z3,z7,z22,z6]),(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z56,z533,z3,z4,z57]),(0,[z0,z1,z3,z305,z710,z6]),(0,[z29,z1,z2,z104,z3,z4])],[(0,[z0,z1,z2,z3,z248,z6]),(0,[z0,z1,z967,z3,z4,z6]),(0,[z0,z1,z657,z127,z4,z6]),(0,[z0,z1,z2,z3,z968,z6]),(1,[z0,z2,z3,z4,z831]),(0,[z0,z88,z336,z1,z2,z3])],[(0,[z0,z1,z2,z3,z4,z969])],[(0,[z0,z1,z153,z3,z4,z76]),(0,[z0,z1,z2,z3,z970,z6])],[(0,[z0,z1,z2,z137,z22,z6]),(0,[z1,z2,z3,z26,z22,z6])]],
   [[(0,[z180,z756,z2,z3,z4,z6]),(0,[z656,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z89,z600,z6]),(0,[z0,z1,z2,z3,z971,z6])],[(0,[z0,z1,z435,z367,z4,z6]),(0,[z1,z2,z251,z197,z22,z6]),(0,[z0,z1,z533,z3,z4,z6]),(0,[z0,z1,z39,z3,z710,z6])],[(0,[z0,z1,z2,z3,z4,z972]),(0,[z0,z829,z2,z3,z4,z6]),(0,[z0,z1,z973,z3,z4,z6]),(0,[z288,z1,z2,z3,z22,z6]),(0,[z0,z74,z2,z3,z47,z6]),(0,[z1,z2,z3,z4,z6,z974]),(0,[z0,z1,z2,z3,z975,z6])],[(0,[z0,z1,z153,z3,z22,z6]),(0,[z0,z1,z407,z3,z78,z6]),(0,[z0,z1,z2,z3,z7,z371]),(0,[z0,z2,z3,z4,z831,z57])],[(0,[z0,z1,z2,z3,z119,z45]),(0,[z976,z0,z2,z3,z4,z6]),(0,[z146,z1,z2,z54,z4,z6]),(0,[z1,z2,z3,z22,z55,z57]),(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z3,z4,z978])],[(0,[z0,z1,z153,z372,z4,z6]),(0,[z168,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z3,z96,z371])],[(0,[z1,z2,z54,z963,z4,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z2,z3,z980,z6])],[(0,[z385,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z171]),(0,[z1,z2,z3,z22,z12,z55]),(0,[z207,z0,z2,z107,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z270,z6]),(0,[z0,z1,z2,z3,z981,z6]),(0,[z0,z1,z2,z3,z982,z6]),(0,[z1,z2,z3,z22,z61,z6]),(0,[z0,z311,z2,z3,z4,z57]),(0,[z0,z1,z2,z103,z50,z6]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z1,z321,z3,z4,z6]),(0,[z0,z1,z65,z794,z4,z6])],[(0,[z0,z1,z2,z984,z4,z6]),(0,[z1,z2,z3,z734,z22,z6]),(0,[z0,z1,z2,z103,z47,z6]),(0,[z985,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z45]),(1,[z1,z2,z963,z4,z6]),(0,[z1,z2,z127,z197,z22,z6]),(0,[z1,z2,z3,z22,z6,z67]),(0,[z304,z1,z2,z3,z4,z55]),(0,[z0,z59,z3,z4,z662,z6]),(0,[z0,z100,z2,z3,z37,z6])],[(0,[z1,z2,z963,z197,z4,z6]),(0,[z1,z296,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z22,z184]),(0,[z0,z370,z1,z3,z5,z6]),(0,[z0,z986,z1,z2,z3,z6]),(0,[z0,z1,z2,z89,z6,z470])],[(0,[z0,z1,z435,z3,z97,z6]),(0,[z0,z112,z1,z3,z47,z6]),(0,[z29,z1,z2,z89,z3,z6])],[(0,[z0,z1,z2,z3,z4,z76]),(0,[z877,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z987])],[(0,[z0,z1,z2,z3,z988,z6]),(0,[z0,z1,z989,z3,z4,z6]),(0,[z0,z1,z2,z4,z801,z6])],[(0,[z0,z1,z435,z3,z362,z6]),(0,[z0,z990,z2,z3,z4,z6]),(0,[z504,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z735])]],
   [[(0,[z0,z1,z321,z197,z4,z6]),(0,[z545,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z4,z991,z6]),(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z1,z2,z3,z4,z993]),(0,[z0,z1,z2,z994,z4,z6]),(0,[z0,z2,z3,z4,z709,z6]),(0,[z0,z1,z65,z3,z4,z289])],[(0,[z17,z1,z2,z3,z22,z171]),(0,[z0,z1,z2,z3,z995,z6])],[(0,[z0,z1,z2,z367,z4,z6]),(0,[z0,z1,z2,z137,z47,z6]),(0,[z0,z1,z2,z3,z354,z6]),(0,[z0,z1,z2,z3,z996,z6]),(0,[z0,z193,z1,z60,z22,z6]),(0,[z1,z2,z506,z4,z22,z6]),(0,[z0,z997,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z998]),(0,[z0,z1,z2,z3,z999,z6]),(0,[z207,z0,z2,z609,z4,z6]),(0,[z1000,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z372,z4,z6]),(0,[z0,z206,z2,z3,z22,z6]),(0,[z1,z2,z749,z3,z4,z6]),(0,[z164,z1,z2,z54,z4,z6]),(0,[z144,z504,z1,z2,z200,z6])],[(0,[z0,z1,z2,z3,z4,z1001]),(0,[z180,z34,z2,z3,z97,z6]),(0,[z0,z764,z1,z3,z22,z6]),(0,[z0,z172,z2,z3,z23,z6])],[(0,[z0,z1,z153,z3,z47,z6]),(0,[z0,z1,z2,z3,z1002,z6]),(0,[z0,z1,z2,z104,z47,z105])],[(0,[z0,z1,z2,z3,z97,z281]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z0,z1,z872,z3,z4,z6]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z0,z1,z2,z3,z4,z1004]),(0,[z1005,z1,z2,z3,z4,z6])]],
   [[(0,[z180,z34,z2,z3,z362,z6]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z0,z1,z2,z3,z47,z369]),(0,[z0,z825,z80,z3,z4,z6]),(0,[z0,z1,z2,z3,z1007,z6]),(0,[z0,z1,z2,z53,z4,z105])],[(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z461,z1,z2,z3,z22]),(0,[z1,z2,z3,z47,z734,z6]),(0,[z0,z1,z2,z3,z709,z6])],[(0,[z713,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1009,z6]),(0,[z0,z1,z2,z3,z47,z171]),(0,[z0,z1,z2,z3,z4,z132])],[(0,[z0,z1,z2,z3,z4,z1010]),(0,[z0,z1,z1011,z3,z4,z6]),(0,[z174,z810,z1,z2,z3,z6])],[(0,[z0,z1,z2,z1012,z4,z6]),(0,[z0,z1,z2,z3,z4,z718]),(0,[z1,z2,z3,z22,z341,z6]),(0,[z0,z1,z2,z3,z1013,z6]),(0,[z29,z1,z2,z3,z6,z19])],[(0,[z1,z2,z3,z47,z313,z6]),(0,[z0,z1,z2,z3,z114,z427])],[(0,[z1,z2,z3,z327,z22,z6]),(0,[z0,z1,z2,z3,z47,z184]),(0,[z0,z1,z2,z3,z1014,z6]),(0,[z257,z0,z65,z127,z4,z6]),(0,[z0,z1,z2,z3,z1015,z6])],[(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z126,z1,z3,z4,z289]),(0,[z0,z1016,z1,z2,z3,z6]),(0,[z0,z1017,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z1018,z4,z6]),(0,[z0,z1,z2,z3,z942,z4]),(0,[z0,z2,z3,z4,z6,z1019]),(0,[z237,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z22,z232]),(0,[z0,z74,z39,z3,z4,z6])],[(0,[z0,z1020,z2,z3,z4,z6]),(0,[z0,z1,z2,z1021,z4,z6]),(0,[z147,z1,z2,z3,z22,z6]),(0,[z623,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z1022,z4,z6]),(0,[z0,z88,z1,z2,z286,z3])],[(0,[z0,z1,z1023,z3,z4,z6]),(0,[z0,z1,z2,z3,z1024,z6]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z206,z58,z3,z4,z6]),(0,[z0,z1026,z1,z2,z3,z6]),(0,[z1,z2,z3,z131,z22,z55]),(0,[z0,z175,z2,z3,z69,z6]),(0,[z236,z1,z2,z3,z22,z6]),(0,[z0,z80,z59,z3,z4,z6]),(0,[z0,z193,z1,z60,z4,z289]),(0,[z0,z1027,z2,z3,z4,z6]),(0,[z0,z1028,z1,z3,z4,z6])],[(0,[z180,z34,z153,z3,z4,z6]),(0,[z0,z1,z749,z3,z4,z6]),(0,[z0,z1,z3,z689,z4,z98]),(1,[z0,z1,z2,z801,z6])],[(0,[z0,z212,z2,z137,z4,z6]),(0,[z0,z857,z2,z3,z4,z6]),(0,[z0,z161,z1,z2,z4,z424]),(0,[z1029,z1,z2,z3,z4,z6]),(0,[z0,z100,z279,z3,z37,z6]),(0,[z0,z1,z2,z3,z1030,z6])],[(0,[z0,z1,z153,z3,z4,z281]),(0,[z276,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z506,z47,z6]),(0,[z0,z1,z2,z103,z4,z169]),(0,[z0,z1031,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z96,z510])],[(0,[z1,z2,z3,z4,z22,z171]),(0,[z17,z1,z2,z54,z4,z31]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z161,z1,z2,z4,z432])],[(0,[z0,z206,z2,z3,z47,z6]),(0,[z44,z1,z141,z137,z4,z6]),(0,[z0,z1032,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z203,z6]),(0,[z144,z29,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z266,z3,z22,z6])],[(0,[z0,z1,z435,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z31]),(0,[z0,z64,z2,z3,z23,z6]),(0,[z404,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z1033,z4,z6])],[(1,[z756,z2,z3,z4,z6]),(0,[z0,z212,z2,z3,z4,z369]),(0,[z1,z2,z3,z22,z377,z6]),(0,[z0,z304,z1,z2,z3,z19])],[(0,[z199,z1,z2,z3,z22,z6]),(0,[z0,z359,z1,z3,z9,z6]),(0,[z0,z335,z59,z3,z4,z6]),(0,[z0,z8,z1,z3,z710,z6]),(0,[z0,z1,z321,z3,z4,z105])],[(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z3,z4,z876]),(0,[z1,z2,z3,z22,z388,z6]),(0,[z0,z1,z279,z3,z22,z6])],[(0,[z49,z1,z2,z3,z4,z463]),(0,[z0,z1,z2,z3,z1035,z6]),(0,[z0,z1,z1036,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z174,z1,z2,z3,z98]),(0,[z0,z174,z1,z2,z3,z12]),(0,[z144,z0,z1,z2,z200,z6])],[(0,[z0,z1,z2,z227,z4,z369]),(0,[z0,z1,z2,z3,z4,z1039]),(0,[z1,z2,z3,z402,z22,z6])]],
   [[(0,[z0,z1,z2,z3,z1040,z6]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z0,z1,z1041,z2,z3,z4])],[(0,[z0,z212,z2,z3,z119,z6]),(0,[z168,z1,z2,z197,z120,z6]),(0,[z0,z1,z2,z197,z4,z31]),(0,[z1,z2,z197,z107,z22,z6]),(0,[z0,z1,z2,z3,z22,z289]),(0,[z0,z1,z3,z22,z6,z919]),(0,[z0,z1,z2,z3,z1042,z6]),(0,[z1043,z1,z2,z3,z4,z6]),(0,[z0,z174,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1044,z6]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z263,z1,z2,z3,z22,z6])],[(0,[z21,z1,z58,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1046,z6]),(0,[z125,z756,z2,z3,z4,z6]),(0,[z0,z56,z2,z3,z4,z57]),(0,[z0,z117,z2,z3,z4,z36]),(1,[z0,z1,z794,z4,z6]),(0,[z0,z1,z2,z3,z4,z815])],[(0,[z0,z1,z2,z963,z4,z6]),(0,[z63,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z1047,z6])],[(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z2,z227,z119,z6]),(0,[z0,z1,z39,z3,z305,z232]),(0,[z0,z88,z1,z321,z3,z4])],[(0,[z17,z1,z2,z54,z4,z6]),(0,[z1,z2,z3,z963,z4,z6]),(0,[z49,z1,z2,z3,z22,z169]),(0,[z16,z1,z2,z3,z327,z6]),(0,[z344,z1,z2,z3,z47,z6]),(0,[z0,z8,z1,z3,z5,z6]),(0,[z0,z172,z279,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z422]),(0,[z144,z0,z461,z1,z2,z3]),(0,[z0,z174,z161,z1,z2,z14])]],
   [[(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z1,z2,z367,z97,z6]),(0,[z0,z1,z2,z137,z270,z6]),(0,[z0,z1,z2,z3,z327,z6]),(0,[z0,z1,z65,z127,z22,z6]),(0,[z0,z821,z1,z3,z22,z6]),(0,[z0,z1,z903,z3,z47,z6]),(0,[z0,z1,z2,z241,z402,z6]),(0,[z0,z2,z3,z816,z4,z6]),(0,[z1050,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1051,z4,z6]),(0,[z429,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z1052,z4,z6]),(0,[z1053,z1,z2,z3,z4,z6]),(0,[z1054,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z137,z4,z45]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z1,z2,z3,z1056,z6])],[(0,[z0,z1,z2,z367,z362,z6]),(0,[z0,z1,z266,z3,z47,z6]),(0,[z29,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z710,z6])],[(0,[z0,z1,z2,z227,z4,z6]),(0,[z44,z206,z141,z3,z4,z6]),(0,[z1,z252,z2,z3,z22,z6]),(0,[z0,z399,z2,z3,z4,z6]),(0,[z504,z1,z2,z3,z201,z6])],[(0,[z0,z1,z2,z1057,z4,z6]),(0,[z207,z0,z2,z816,z4,z6])],[(0,[z0,z1,z2,z3,z1058,z6]),(0,[z0,z1,z2,z201,z801,z6]),(0,[z0,z1,z2,z3,z1059,z6])],[(0,[z17,z1,z2,z963,z4,z6]),(0,[z0,z1,z279,z3,z47,z6]),(0,[z0,z1,z39,z3,z305,z132])]],
   [[(0,[z0,z1,z2,z3,z96,z769])],[(0,[z0,z1,z1060,z3,z4,z6]),(0,[z144,z0,z1,z2,z61,z6]),(0,[z0,z258,z59,z3,z4,z6]),(0,[z0,z1,z611,z3,z4,z98])],[(0,[z302,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z1061,z4,z6]),(0,[z0,z1,z42,z3,z22,z98]),(0,[z0,z211,z59,z3,z4,z6]),(0,[z0,z1,z478,z3,z4,z6])],[(0,[z385,z1,z141,z3,z4,z6]),(0,[z0,z1,z1062,z3,z4,z6]),(0,[z0,z223,z1,z3,z22,z6]),(0,[z0,z33,z2,z3,z4,z6]),(0,[z1063,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z36,z831]),(0,[z263,z88,z1,z2,z3,z19])],[(0,[z0,z1,z2,z3,z213,z6]),(0,[z1,z2,z272,z3,z22,z6]),(0,[z0,z1,z2,z3,z47,z289]),(0,[z0,z1064,z1,z2,z3,z6]),(1,[z0,z2,z3,z709,z6])],[(0,[z0,z1,z2,z1065,z4,z6]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z72,z1,z2,z3,z734,z6]),(0,[z0,z304,z1,z2,z3,z389]),(0,[z263,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z1067,z6]),(0,[z0,z1,z2,z3,z1068,z6]),(0,[z0,z1,z2,z3,z1069,z6])],[(0,[z0,z1,z153,z367,z4,z6]),(0,[z198,z1,z2,z3,z22,z55])],[(0,[z0,z1,z2,z3,z4,z1070]),(0,[z0,z1071,z2,z3,z4,z6]),(0,[z569,z1,z2,z3,z22,z6]),(0,[z0,z799,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1072,z6]),(0,[z144,z0,z1,z2,z184,z200])]],
   [[(0,[z1073,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1074,z6]),(0,[z0,z193,z33,z3,z4,z6])],[(0,[z44,z1,z141,z3,z22,z6]),(0,[z49,z1,z2,z3,z50,z169])],[(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z1,z2,z3,z4,z1076]),(0,[z17,z1,z2,z54,z26,z6]),(0,[z257,z0,z2,z3,z22,z6]),(0,[z49,z1,z2,z3,z47,z169]),(0,[z1,z2,z3,z4,z739,z6])],[(0,[z0,z1077,z1,z3,z4,z6]),(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z1,z65,z127,z47,z6]),(0,[z0,z138,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1078])],[(0,[z0,z1,z2,z3,z1079,z6]),(0,[z16,z1,z2,z3,z26,z6]),(1,[z1,z2,z3,z734,z6]),(0,[z0,z1,z2,z3,z4,z739]),(0,[z0,z1,z2,z3,z1080,z6])],[(0,[z0,z206,z2,z3,z270,z6]),(0,[z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z65,z440,z4,z6]),(0,[z29,z1,z2,z3,z4,z98]),(0,[z29,z1,z2,z3,z4,z12]),(0,[z0,z461,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z712,z14])],[(0,[z0,z1,z2,z3,z1081,z6]),(0,[z1,z2,z3,z22,z6,z291]),(0,[z0,z1,z39,z3,z647,z6]),(0,[z0,z1,z1082,z3,z4,z6]),(0,[z0,z65,z33,z127,z4,z6])],[(0,[z0,z1,z2,z3,z1083,z6]),(0,[z0,z206,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z308,z31]),(0,[z237,z1,z2,z3,z4,z169]),(0,[z504,z1,z2,z3,z402,z6]),(0,[z810,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1084,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1085,z6]),(0,[z0,z1,z2,z3,z4,z1086])],[(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z172,z2,z3,z512,z6]),(0,[z0,z1,z1088,z3,z4,z6]),(0,[z0,z1,z2,z1089,z4,z6]),(0,[z144,z0,z1,z2,z672,z6])],[(0,[z122,z1,z2,z3,z4,z169]),(0,[z1090,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1091,z3,z4,z6]),(0,[z1,z2,z3,z489,z22,z6]),(0,[z0,z1,z2,z3,z1092,z6])],[(0,[z0,z756,z2,z3,z4,z6]),(0,[z0,z1,z2,z1093,z4,z6]),(0,[z0,z117,z2,z3,z4,z831])],[(0,[z235,z0,z1,z2,z3,z79]),(0,[z0,z1,z321,z3,z4,z55]),(0,[z0,z1,z2,z3,z1094,z6]),(0,[z504,z1,z2,z3,z200,z6]),(0,[z0,z461,z1,z2,z89,z3])],[(0,[z0,z1,z2,z3,z1095,z6]),(0,[z44,z1,z749,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z943]),(0,[z49,z1,z2,z103,z22,z6]),(0,[z0,z1,z2,z3,z1096,z6]),(0,[z0,z1097,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1098,z6])]],
   [[(0,[z0,z1,z2,z3,z1099,z6]),(0,[z0,z161,z1,z2,z4,z712])],[(0,[z0,z1,z2,z3,z4,z1100]),(0,[z0,z1,z2,z3,z1101,z6]),(0,[z207,z0,z2,z107,z22,z6]),(0,[z198,z1,z2,z3,z47,z55]),(0,[z0,z1102,z1,z3,z4,z6]),(0,[z0,z161,z1,z2,z672,z4])],[(0,[z0,z1,z2,z1103,z4,z6]),(0,[z0,z74,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z0,z1,z2,z3,z96,z529])],[(0,[z0,z1105,z2,z3,z4,z6]),(0,[z0,z1,z3,z22,z880,z6]),(0,[z198,z1,z2,z3,z203,z55]),(0,[z1106,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z710,z9,z6]),(0,[z144,z0,z1,z2,z801,z6]),(0,[z0,z1,z2,z4,z6,z712])],[(0,[z136,z756,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z45]),(0,[z44,z1,z141,z3,z47,z6]),(0,[z304,z1,z2,z3,z22,z55]),(0,[z508,z1,z2,z3,z22,z6]),(0,[z303,z1,z2,z3,z22,z6]),(0,[z0,z1,z1107,z3,z4,z6]),(0,[z0,z1,z2,z3,z1108,z6])],[(0,[z0,z1,z2,z3,z1109,z6]),(0,[z257,z0,z2,z3,z47,z6]),(0,[z0,z1,z2,z3,z4,z1110]),(0,[z0,z1,z321,z3,z4,z14])],[(0,[z0,z1,z1111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1112]),(0,[z0,z1113,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z22,z76]),(0,[z0,z1,z2,z103,z327,z6]),(0,[z1114,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z97,z6]),(0,[z0,z1,z3,z846,z4,z6]),(0,[z0,z1,z2,z3,z4,z1115]),(0,[z0,z1116,z2,z3,z4,z6]),(0,[z0,z1117,z2,z3,z4,z6]),(0,[z1118,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1119,z3,z4,z6]),(0,[z0,z1,z2,z3,z1120,z6]),(0,[z0,z1,z2,z103,z4,z6]),(0,[z325,z1,z2,z3,z22,z6]),(0,[z0,z2,z3,z22,z890,z6]),(0,[z0,z1,z2,z3,z47,z858]),(0,[z0,z1,z1121,z3,z4,z6])],[(0,[z0,z161,z1,z2,z4,z568]),(0,[z0,z1,z1122,z3,z4,z6]),(0,[z0,z1,z3,z794,z4,z6])],[(0,[z0,z1,z2,z3,z362,z6]),(0,[z0,z1,z2,z3,z1123,z6]),(0,[z0,z1,z2,z3,z4,z1124]),(0,[z0,z1125,z1,z3,z4,z6]),(0,[z0,z279,z3,z4,z37,z6]),(0,[z0,z1126,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z131,z114]),(1,[z1,z2,z3,z4,z739]),(0,[z0,z112,z1,z3,z4,z6]),(0,[z0,z1127,z2,z3,z4,z6])],[(0,[z528,z1,z2,z3,z22,z6]),(0,[z0,z266,z251,z3,z4,z6])],[(0,[z0,z1,z2,z372,z22,z6]),(0,[z0,z1,z2,z3,z120,z6]),(0,[z0,z1,z1128,z3,z4,z6]),(0,[z0,z1129,z1,z2,z3,z4])],[(0,[z0,z482,z59,z3,z4,z6]),(0,[z0,z1,z2,z1130,z4,z6]),(0,[z0,z11,z33,z3,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 529).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1062).take 143) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1205)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [529, 533, 143] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 231).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 114, 25] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_39363

theorem PEqualNP.Outside.L_meta_39363 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276152832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276152832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39363.solve