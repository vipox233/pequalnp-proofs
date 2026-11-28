import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40417

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4209683104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1000080858005154#64 ++ 0x0400020216001455#64 ++ 0xee027918f831ffff#64 ++ 0xfb809e463e0c7fff#64 : BitVec 256),
   (0x210ca2632e26cb31#64 ++ 0x08432898cb89b2cc#64 ++ 0xdf1da6e73e2ecb31#64 ++ 0xf7c769b9cf8bb2cc#64 : BitVec 256),
   (0x4061470582cb0c28#64 ++ 0x501851c160b2c30a#64 ++ 0xbee1c707c7cf0c3f#64 ++ 0x6fb871c1f1f3c30f#64 : BitVec 256),
   (0x80b607b007700e82#64 ++ 0x602d81ec01dc03a0#64 ++ 0x79fe07f807f00fc3#64 ++ 0xde7f81fe01fc03f0#64 : BitVec 256),
   (0x00dff00005bda003#64 ++ 0x8037fc00016f6800#64 ++ 0xfcfff80007fff003#64 ++ 0x3f3ffe0001fffc00#64 : BitVec 256),
   (0x02fbfddef0000000#64 ++ 0x00beff77bc000000#64 ++ 0xfbfffffff8000000#64 ++ 0xfefffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00b2059000000000 0x002c816400000000 0x79fe07f800000000 0xde7f81fe00000000

def z1 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff80007fff003 0x3f3ffe0001fffc00

def z2 : W := mkw 0x02200ddef0000000 0x00880377bc000000 0x030007fff8000000 0xc0c001fffe000000

def z3 : W := mkw 0x1000080858005154 0x0400020216001455 0xee027918f831ffff 0xfb809e463e0c7fff

def z4 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e2ecb31 0xf7c769b9cf8bb2cc

def z5 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c707c7cf0c3f 0x6fb871c1f1f3c30f

def z6 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe07f807f00fc3 0xde7f81fe01fc03f0

def z7 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8000000 0xfefffffffe000000

def z8 : W := mkw 0x02fff5d6a5bda003 0x80bffd75a96f6800 0xfdfffee707fff003 0x3f7fffb9c1fffc00

def z9 : W := mkw 0x310caa6b7e26db75 0x0c432a9adf89b6dd 0xdf1dfee7fe2ffb3d 0xf7c77fb9ff8bfecf

def z10 : W := mkw 0xe1ffe7f7afffcfbb 0x787ff9fdebfff3ee 0xffffe7ffffffcfff 0xfffff9fffffff3ff

def z11 : W := mkw 0x21dff0622dbde313 0x8877fc188b6f78c4 0xfdfff8e03ffff303 0xbf7ffe380ffffcc0

def z12 : W := mkw 0x50614d0cd8c9555c 0x5418534336325557 0xeee27918f9f1ffff 0xfbb89e463e7c7fff

def z13 : W := mkw 0x8004022007700e82 0x6001008801dc03a0 0x0000000007f00fc3 0x0000000001fc03f0

def z14 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3ff07c7fffc3f 0x7fb8ffc1f1ffff0f

def z15 : W := mkw 0x0008a04220000000 0x0002281088000000 0xdb1da6e738000000 0xf6c769b9ce000000

def z16 : W := mkw 0x0096000005300002 0x00258000014c0000 0x78fe000007f00003 0x1e3f800001fc0000

def z17 : W := mkw 0x1000000008005154 0x0400000002001455 0x040000000031ffff 0x01000000000c7fff

def z18 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0xdb1da6e73e0e0000 0xf6c769b9cf838000

def z19 : W := mkw 0x239ebafb7e26cb31 0x08e7aebedf89b2cc 0xdf1fbeff3e2ecb31 0xf7c7efbfcf8bb2cc

def z20 : W := mkw 0x40f3479582cb0c28 0x503cd1e560b2c30a 0xffffc7ffc7cf0c3f 0xfffff1fff1f3c30f

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00000000000831 0x638000000000020c

def z22 : W := mkw 0x00baa5d220000000 0x002ea97488000000 0xfbffa7ff38000000 0xfeffe9ffce000000

def z23 : W := mkw 0x02f35ddef0000000 0x00bcd777bc000000 0x23e25ffff8000000 0xc8f897fffe000000

def z24 : W := mkw 0x00dbf04220000000 0x0036fc1088000000 0xfbfffee738000000 0xfeffffb9ce000000

def z25 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xffffffffffcf0003 0xfffffffffff3c000

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x6802011800000000 0xda00804600000000

def z27 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0x11fd86e700000000 0x047f61b9c0000000

def z28 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x04000000062ecb31 0x01000000018bb2cc

def z29 : W := mkw 0x00dbf00001992002 0x8036fc0000664800 0xf8fff80001d13002 0x3e3ffe0000744c00

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0xae004100c0010c3f 0x6b8010403000430f

def z31 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x51ffbeff38000000 0x947fefbfce000000

def z32 : W := mkw 0x000ca0000c24c111 0x0003280003093044 0xde1da0003e2ecb31 0xf78768000f8bb2cc

def z33 : W := mkw 0xa1bea7f32f76cfb3 0x686fa9fccbddb3ec 0xffffa7ff3ffecff3 0xffffe9ffcfffb3fc

def z34 : W := mkw 0x00dff04225bda003 0x8037fc10896f6800 0xfffffee73ffff003 0xffffffb9cffffc00

def z35 : W := mkw 0x5041480dd88b517c 0x141052037622d45f 0xee03f91ff83fffff 0xfb80fe47fe0fffff

def z36 : W := mkw 0x210402632e224b30 0x08410098cb8892cc 0x5b1c06e73e200b31 0xd6c701b9cf8802cc

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x86004000c001003c 0x218010003000400f

def z38 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x411e00f8003003c0 0x9047803e000c00f0

def z39 : W := mkw 0x90b60fb85f705fd6 0x642d83ee17dc17f5 0xfffe7ff8fff1ffff 0xffff9ffe3ffc7fff

def z40 : W := mkw 0x90ffffb85ffdffd7 0xe43fffee17ff7ff5 0xfffffff8ffffffff 0xfffffffe3fffffff

def z41 : W := mkw 0x00d7500005bda003 0x8035d400016f6800 0x24e2580007fff003 0x0938960001fffc00

def z42 : W := mkw 0x02f35d9cd0000000 0x00bcd76734000000 0x20e25918c0000000 0x0838964630000000

def z43 : W := mkw 0x0008a24322020820 0x00022890c8808208 0xdf1da6e73e0e0831 0xf7c769b9cf83820c

def z44 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x011c00e000000000 0x0047003800000000

def z45 : W := mkw 0x2108a0432806c131 0x08422810ca01b04c 0x8601a007380ec030 0x21806801ce03b00c

def z46 : W := mkw 0x80b2059001500482 0x602c816400540120 0x20e2011801d004c2 0x0838804600740130

def z47 : W := mkw 0x1049f808588df155 0x84127e0216237c55 0x8601f800f80ff03c 0x21807e003e03fc0f

def z48 : W := mkw 0x40f3570583db2c2a 0xd03cd5c160f6cb0a 0xbee3df07c7df3c3f 0x6fb8f7c1f1f7cf0f

def z49 : W := mkw 0x1049f808588df155 0x84127e0216237c55 0xee03f918f83fffff 0xfb80fe463e0fffff

def z50 : W := mkw 0x50200f0dda425d7c 0x540803c37690975f 0x0200071ff8000ffc 0xc08001c7fe0003ff

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x6802011800300fc3 0xda008046000c03f0

def z52 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff91807ffffc3 0xff3ffe4601fffff0

def z53 : W := mkw 0x80b605b005700682 0x602d816c015c01a0 0x61fe01f801f007c2 0x987f807e007c01f0

def z54 : W := mkw 0x4020070582cb0c28 0x500801c160b2c30a 0x06000707c7cf0c3f 0x418001c1f1f3c30f

def z55 : W := mkw 0x00b2079002400c00 0x402c81e400900300 0x79fe07f807c00c03 0xde7f81fe01f00300

def z56 : W := mkw 0x4041420102cb0c28 0x5010508040b2c30a 0xbce1c00007cf0c3f 0x2f38700001f3c30f

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0278000031f003 0x3b009e00000c7c00

def z58 : W := mkw 0x10dff8085dbdf157 0x8437fe02176f7c55 0xfefff918ffffffff 0xffbffe463fffffff

def z59 : W := mkw 0x900402200f705fd6 0x6401008803dc17f5 0x0400000007f1ffff 0x0100000001fc7fff

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x2002580000113002 0x0800960000044c00

def z61 : W := mkw 0x210ca0622c24c311 0x084328188b0930c4 0x411c20e03820c300 0x904708380e0830c0

def z62 : W := mkw 0x4061450480c90408 0x5018514120324102 0x20e04100c1c1040e 0x0838104030704103

def z63 : W := mkw 0x21dff0432dbfe133 0x8877fc10cb6ff84c 0xfefff8073ffff033 0x3fbffe01cffffc0c

def z64 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x131d86e73e0e0b30 0xc4c761b9cf8382cc

def z65 : W := mkw 0x8020059000400480 0x6008016400100120 0x00000118000004c0 0x0000004600000130

def z66 : W := mkw 0x00fbf50480000000 0x003efd4120000000 0xfaffff07c0000000 0x7ebfffc1f0000000

def z67 : W := mkw 0x210ca06224248201 0x0843281889092080 0x011c00e000000000 0x0047003800000000

def z68 : W := mkw 0x1000080858005154 0x0400020216001455 0xc6027818f831f3fc 0xb1809e063e0c7cff

def z69 : W := mkw 0x42fbfddff08b0028 0x10beff77fc22c00a 0xfffffffff80f003c 0xfffffffffe03c00f

def z70 : W := mkw 0x40f3550481d9240a 0xd03cd54120764902 0x20e25900c1d1340e 0x0838964030744d03

def z71 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xdbfda6e738000000 0xf6ff69b9ce000000

def z72 : W := mkw 0x1000080850001044 0x0400020214000411 0x20025918c01134ce 0x0800964630044d33

def z73 : W := mkw 0x1000080858005154 0x0400020216001455 0x400238183830f3c0 0x90008e060e0c3cf0

def z74 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0x411e38f838000000 0x90478e3e0e000000

def z75 : W := mkw 0x0000080850000000 0x0000020214000000 0xea027918f8000000 0xfa809e463e000000

def z76 : W := mkw 0x310caa6b7e26db75 0x0c432a9adf89b6dd 0xff1ffffffe3fffff 0xffc7ffffff8fffff

def z77 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1de7e7fe2fcf3f 0xffc779f9ff8bf3cf

def z78 : W := mkw 0x1000080858005154 0x0400020216001455 0xa6027918f811f4fe 0x29809e463e047d3f

def z79 : W := mkw 0x00dbf00000000000 0x0036fc0000000000 0xf8fff80000000000 0x3e3ffe0000000000

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000000031f003 0x01000000000c7c00

def z81 : W := mkw 0x4020070582420c28 0x500801c16090830a 0xae004707c0010c3f 0x6b8011c1f000430f

def z82 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbce1c60707cf0003 0x2f387181c1f3c000

def z83 : W := mkw 0x210402210fbfeb33 0x8841008843effacc 0x0400000007fffb33 0x0100000001fffecc

def z84 : W := mkw 0x0228addef0000000 0x008a2b77bc000000 0xdb1da7fff8000000 0xf6c769fffe000000

def z85 : W := mkw 0x0249f84ef0000000 0x00927e13bc000000 0x8201f807f8000000 0x20807e01fe000000

def z86 : W := mkw 0xc004022107fb0eaa 0x7001008841fec3aa 0x0400000007ff0fff 0x0100000001ffc3ff

def z87 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xf9fffee700000000 0x3e7fffb9c0000000

def z88 : W := mkw 0x02fbfddef08da001 0x80beff77bc236800 0xfffffffff80ff000 0xfffffffffe03fc00

def z89 : W := mkw 0x506147058acb5d7c 0x541851c162b2d75f 0xbee1c707c7ffffff 0x6fb871c1f1ffffff

def z90 : W := mkw 0x0000000008004110 0x0000000002001044 0xce0020003820cb31 0xf38008000e0832cc

def z91 : W := mkw 0x80b2079003500c82 0x602c81e400d40320 0x38e2071807d00cc3 0x4e3881c601f40330

def z92 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x10fd800007ce0000 0x043f600001f38000

def z93 : W := mkw 0x1000080858005154 0x0400020216001455 0x02000118f8000ffc 0xc08000463e0003ff

def z94 : W := mkw 0x1000000008005154 0x0400000002001455 0x040000000001f03c 0x0100000000007c0f

def z95 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x111d86e7060e0000 0x044761b9c1838000

def z96 : W := mkw 0x616de767aeefcf39 0x585b79d9ebbbf3ce 0xfffde7e7ffefcf3f 0xffff79f9fffbf3cf

def z97 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1ffee73e3ffb33 0xffc7ffb9cf8ffecc

def z98 : W := mkw 0x0049f000008da001 0x80127c0000236800 0x8401f800000ff000 0x21007e000003fc00

def z99 : W := mkw 0x802007b002400e80 0x600801ec009003a0 0x010007f800000fc0 0xc04001fe000003f0

def z100 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xbbfdc7e7c0000000 0x6eff71f9f0000000

def z101 : W := mkw 0x0000020102020820 0x0000008040808208 0x9e018607060e0831 0x67806181c183820c

def z102 : W := mkw 0x0061450480000000 0x0018514120000000 0xbae1c707c0000000 0x6eb871c1f0000000

def z103 : W := mkw 0x82fffffef7700e82 0x60bfffffbddc03a0 0xfbfffffffff00fc3 0xfefffffffffc03f0

def z104 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x50ffb80007fef000 0x143fee0001ffbc00

def z105 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xdf1da6e73e3fffff 0xf7c769b9cf8fffff

def z106 : W := mkw 0x0004022006200a00 0x0001008801880280 0x591c06e006200b01 0xd64701b8018802c0

def z107 : W := mkw 0x4061450480c90408 0x5018514120324102 0xbae1c707c1c1040e 0x6eb871c1f0704103

def z108 : W := mkw 0x80b607b107720ea2 0x602d81ec41dc83a8 0xffff87ff07fe0ff3 0xffffe1ffc1ff83fc

def z109 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x12e18707c7ce0c3c 0x44b861c1f1f3830f

def z110 : W := mkw 0x10200f085a405d54 0x440803c216901755 0xfee27f18fff1ffff 0xffb89fc63ffc7fff

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a01860700000000 0x66806181c0000000

def z112 : W := mkw 0x406de70586ef8c29 0x501b79c161bbe30a 0xfefde707c7efcc3f 0x7fbf79c1f1fbf30f

def z113 : W := mkw 0x000ca00004248001 0x0003280001092000 0xdc1da000062ec001 0x37076800018bb000

def z114 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x411e07f800300fc0 0xd04781fe000c03f0

def z115 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x511da6e73e2ec300 0x944769b9cf8bb0c0

def z116 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x10e1860707ce0000 0x04386181c1f38000

def z117 : W := mkw 0x50614f0ddacb5d7c 0x541853c376b2d75f 0xfee3ff1fffffffff 0xffb8ffc7ffffffff

def z118 : W := mkw 0x0020050000400400 0x4008014000100100 0x20e0010001c00402 0x0838004000700100

def z119 : W := mkw 0x802407b007700e82 0x600901ec01dc03a0 0x010007f807f00fc3 0xc04001fe01fc03f0

def z120 : W := mkw 0x4020070582420c28 0x500801c16090830a 0x0000060700000000 0x00000181c0000000

def z121 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfbfffffff81134ce 0xfefffffffe044d33

def z122 : W := mkw 0x23fbfddff806c131 0x08feff77fe01b04c 0xfffffffff80ec030 0xfffffffffe03b00c

def z123 : W := mkw 0x000ca04224248001 0x0003281089092000 0xdf1da6e73e2ec001 0xf7c769b9cf8bb000

def z124 : W := mkw 0x31dffa6b7fbffb77 0x8c77fe9adfeffedd 0xffffffffffffffff 0xffffffffffffffff

def z125 : W := mkw 0x42fbf7d7a2cb0c28 0x50befdf5e8b2c30a 0xbffdc7e7c7cf0c3f 0x6fff71f9f1f3c30f

def z126 : W := mkw 0x40000001008b0028 0x100000004022c00a 0x04000000000f003c 0x010000000003c00f

def z127 : W := mkw 0x21dff2632fbfeb33 0x8877fc98cbeffacc 0xfffffee73ffffb33 0xffffffb9cffffecc

def z128 : W := mkw 0x0096000005300002 0x00258000014c0000 0x401e000000300000 0x10078000000c0000

def z129 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0x401e38000030f000 0x10078e00000c3c00

def z130 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x20e2011807f00fc3 0x0838804601fc03f0

def z131 : W := mkw 0x0008a84a70000000 0x00022a129c000000 0xfb1ffffff8000000 0xfec7fffffe000000

def z132 : W := mkw 0x23fffdfefc24c311 0x08ffff7fbf0930c4 0xfbfffffff820c300 0xfefffffffe0830c0

def z133 : W := mkw 0x210402632e26cb31 0x08410098cb89b2cc 0x070006e73e2ecb31 0xc1c001b9cf8bb2cc

def z134 : W := mkw 0x12fbfddef8005154 0x04beff77be001455 0xfffffffff831ffff 0xfffffffffe0c7fff

def z135 : W := mkw 0x00d3500001992002 0x8034d40000664800 0x20e2580001d13002 0x0838960000744c00

def z136 : W := mkw 0x802407b006600e80 0x600901ec019803a0 0x591c07f806200fc1 0xd64701fe018803f0

def z137 : W := mkw 0x00dff00004248001 0x0037fc0001092000 0xfcfff800062ec001 0x3f3ffe00018bb000

def z138 : W := mkw 0x42200fdff2420c28 0x508803f7fc90830a 0x030007fff8000c3c 0xc0c001fffe00030f

def z139 : W := mkw 0x0000020002000800 0x0000008000800200 0x1800060006000801 0x4600018001800200

def z140 : W := mkw 0x42fbfddef0c90408 0x50beff77bc324102 0xfbfffffff9c1040e 0xfefffffffe704103

def z141 : W := mkw 0x4061470582420c28 0x501851c16090830a 0xbae1c707c0000c3c 0x6eb871c1f000030f

def z142 : W := mkw 0x40fff70587ffac2b 0xd03ffdc161ffeb0a 0xbefdc707c7cf0c3f 0x6fbf71c1f1f3c30f

def z143 : W := mkw 0x2100006228004310 0x084000188a0010c4 0x010000e038000300 0x804000380e0000c0

def z144 : W := mkw 0x0041400000890000 0x0010500000224000 0xbce1c00007cf0003 0x2f38700001f3c000

def z145 : W := mkw 0x00fff59005bda003 0x803ffd64016f6800 0xfdfffff807fff003 0xff7ffffe01fffc00

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0xee027900c031fc3f 0x7b809e40300c7f0f

def z147 : W := mkw 0x0008a00000000000 0x0002280000000000 0xd81da00000000000 0x3607680000000000

def z148 : W := mkw 0x004de00004ad8001 0x00137800012b6000 0xfcfde00007efc003 0x3f3f780001fbf000

def z149 : W := mkw 0x0004022106220a20 0x0001008841888288 0xdf1d86e7062e0b31 0xf7c761b9c18b82cc

def z150 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x11fc07f807c00fc0 0xc47f01fe01f003f0

def z151 : W := mkw 0x4249f84ff08b0028 0x10927e13fc22c00a 0x8601f807f80f003c 0x21807e01fe03c00f

def z152 : W := mkw 0x0004000005300002 0x00010000014c0000 0x0000000007f00003 0x0000000001fc0000

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x840078000001f000 0x21001e0000007c00

def z154 : W := mkw 0x210002632a024b30 0x08400098ca8092cc 0x030006e738000b30 0xc0c001b9ce0002cc

def z155 : W := mkw 0x612ca767ae66cf39 0x584b29d9eb99b3ce 0xdf1da7e7fe2ecf3d 0xf7c769f9ff8bb3cf

def z156 : W := mkw 0x82f35d9cd1500482 0x60bcd76734540120 0x20e25918c1d004c2 0x0838964630740130

def z157 : W := mkw 0x909608b85d3053d6 0x2425822e174c14f5 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z158 : W := mkw 0x40414005808b0028 0x101050016022c00a 0xae01c107c00f0c3f 0x6b807041f003c30f

def z159 : W := mkw 0x1000000008005154 0x0400000002001455 0xce0020003831ffff 0xf38008000e0c7fff

def z160 : W := mkw 0x210400200c24c311 0x08410008030930c4 0x000000000020c300 0x00000000000830c0

def z161 : W := mkw 0x02fffddef5bda003 0x80bfff77bd6f6800 0xfffffffffffff003 0xfffffffffffffc00

def z162 : W := mkw 0x2104022106268a21 0x084100884189a288 0x00000000060e0000 0x0000000001838000

def z163 : W := mkw 0x0004022006200a00 0x0001008801880280 0x0000000006200b01 0x00000000018802c0

def z164 : W := mkw 0x616de767aeefcf39 0x585b79d9ebbbf3ce 0xdffda6e73feecb31 0xf7ff69b9cffbb2cc

def z165 : W := mkw 0xc0f747b587fb0eaa 0x703dd1ed61fec3aa 0xbffdc7e7c7cf0c3f 0x6fff71f9f1f3c30f

def z166 : W := mkw 0x0000000008004110 0x0000000002001044 0xee0278003831fb33 0xfb809e000e0c7ecc

def z167 : W := mkw 0x61614767aacb4f38 0x585851d9eab2d3ce 0xbfe1c7e7ffcf0f3f 0xeff871f9fff3c3cf

def z168 : W := mkw 0x02dbf84ef0000000 0x00b6fe13bc000000 0xfafff807f8000000 0x3ebffe01fe000000

def z169 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff8010c3f 0xfffffffffe00430f

def z170 : W := mkw 0x809602b007300a82 0x202580ac01cc02a0 0x591e06f806300bc1 0xd64781be018c02f0

def z171 : W := mkw 0x40414005808b0028 0x101050016022c00a 0x8601c007c00f003c 0x21807001f003c00f

def z172 : W := mkw 0x000ca00004248001 0x0003280001092000 0xfc1ff800063ff003 0x3f07fe00018ffc00

def z173 : W := mkw 0x1000080858005154 0x0400020216001455 0x02000000f800003c 0x008000003e00000f

def z174 : W := mkw 0x61fff767afffef3b 0xd87ffdd9ebfffbce 0xffffffe7ffffff3f 0xfffffff9ffffffcf

def z175 : W := mkw 0x4020070102cb0c28 0x500801c040b2c30a 0x3ce0070007cf0c3f 0x4f3801c001f3c30f

def z176 : W := mkw 0x02f35d9cd0000000 0x00bcd76734000000 0x79fe5ff8c0000000 0xde7f97fe30000000

def z177 : W := mkw 0x80dff0b005bda283 0xa037fc2c016f68a0 0xfdfff8f807fff3c3 0xbf7ffe3e01fffcf0

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000100c0000c3c 0x408000403000030f

def z179 : W := mkw 0x00414201028b0820 0x0010508040a2c208 0xbee1c60707cf0833 0x6fb87181c1f3c20c

def z180 : W := mkw 0x1000000008005154 0x0400000002001455 0xae004100c031ffff 0x6b801040300c7fff

def z181 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x93fdfee7f8000000 0x24ff7fb9fe000000

def z182 : W := mkw 0x0096000005300002 0x00258000014c0000 0xfcfe780007f1f003 0x3f3f9e0001fc7c00

def z183 : W := mkw 0x23ffffffffbfeb33 0x88ffffffffeffacc 0xfffffffffffffb33 0xfffffffffffffecc

def z184 : W := mkw 0xc06147b582cb0ea8 0x701851ed60b2c3aa 0xbfe1c7ffc7cf0fff 0xeff871fff1f3c3ff

def z185 : W := mkw 0x0061450480000000 0x0018514120000000 0xbee1c707c0010c3f 0x6fb871c1f000430f

def z186 : W := mkw 0x0061450480000000 0x0018514120000000 0x10e1860700000000 0x04386181c0000000

def z187 : W := mkw 0xa10ca2632f76cfb3 0x68432898cbddb3ec 0xdf1da6e73ffecff3 0xf7c769b9cfffb3fc

def z188 : W := mkw 0x4020070582420c28 0x500801c16090830a 0x02000707c0000c3c 0x408001c1f000030f

def z189 : W := mkw 0xc0b607b587720eaa 0x702d81ed61dc83aa 0x7bfe07ffc7f00fff 0xdeff81fff1fc03ff

def z190 : W := mkw 0x10dff0000dbdf157 0x8437fc00036f7c55 0xfcfff80007ffffff 0x3f3ffe0001ffffff

def z191 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbae1c707c7ce0000 0x6eb871c1f1f38000

def z192 : W := mkw 0x40414005808b0028 0x101050016022c00a 0x00018007000e0000 0x00006001c0038000

def z193 : W := mkw 0x02fffffef6200a00 0x00bfffffbd880280 0xfbfffffffe200b01 0xfeffffffff8802c0

def z194 : W := mkw 0x004df00004ada001 0x80137c00012b6800 0xdc1df800062ff001 0x37077e00018bfc00

def z195 : W := mkw 0x4065470587ffac2b 0xd01951c161ffeb0a 0xbee1c707c7fffc3f 0x6fb871c1f1ffff0f

def z196 : W := mkw 0x802007b002400e80 0x600801ec009003a0 0x690207f800300fc3 0xda4081fe000c03f0

def z197 : W := mkw 0x80beb7b00774ae83 0xe02fadec01dd2ba0 0x79fe3ff807f0ffc3 0xde7f8ffe01fc3ff0

def z198 : W := mkw 0x0000000008004110 0x0000000002001044 0x0200000038000b30 0xc08000000e0002cc

def z199 : W := mkw 0x1000080858005154 0x0400020216001455 0x24025918c031ffff 0x09009646300c7fff

def z200 : W := mkw 0x12f35d9cd8005154 0x04bcd76736001455 0xeee27918f831ffff 0xfbb89e463e0c7fff

def z201 : W := mkw 0xc0f747b587fb0eaa 0x703dd1ed61fec3aa 0xffffc7ffc7ff0fff 0xfffff1fff1ffc3ff

def z202 : W := mkw 0xa10402210f76cfb3 0x6841008843ddb3ec 0x0400000007fecff3 0x0100000001ffb3fc

def z203 : W := mkw 0x000ca00004248001 0x0003280001092000 0x101d8000060e0000 0x0407600001838000

def z204 : W := mkw 0x4000000580020028 0x100000016000800a 0x02000007c000003c 0x00800001f000000f

def z205 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x79fe00f807f003c3 0x9e7f803e01fc00f0

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa004100c0000000 0x6a80104030000000

def z207 : W := mkw 0x10614d0cd8005154 0x0418534336001455 0xfee3ff1ff831ffff 0xffb8ffc7fe0c7fff

def z208 : W := mkw 0x02f35d9cd1992002 0x80bcd76734664800 0x20e25918c1d13002 0x0838964630744c00

def z209 : W := mkw 0x80b207b003500e82 0x602c81ec00d403a0 0x21e207f801d00fc2 0xc87881fe007403f0

def z210 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfffe47f8c7f10fff 0xffff91fe31fc43ff

def z211 : W := mkw 0x0096000005300002 0x00258000014c0000 0x10fc000007c00000 0x043f000001f00000

def z212 : W := mkw 0x40f7470587fb0c2a 0x503dd1c161fec30a 0xfeffc707c7ff0c3f 0x7fbff1c1f1ffc30f

def z213 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x31ffdfffc0000000 0x0c7ff7fff0000000

def z214 : W := mkw 0x80f747b007f90e82 0x603dd1ec01fe43a0 0xfdffc7f807ff0fc3 0xff7ff1fe01ffc3f0

def z215 : W := mkw 0x1000080858005154 0x0400020216001455 0x86007800f831ffff 0x21801e003e0c7fff

def z216 : W := mkw 0x6149e047a88fc139 0x18527811ea23f04e 0x8601e007f80fc03c 0x21807801fe03f00f

def z217 : W := mkw 0x80fff7b007fdae83 0xe03ffdec01ff6ba0 0xfdfffff807ffffc3 0xff7ffffe01fffff0

def z218 : W := mkw 0x00dff80855bda003 0x8037fe02156f6800 0xfefff918fffff003 0xffbffe463ffffc00

def z219 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x24e04100c7cf0c3f 0x0938104031f3c30f

def z220 : W := mkw 0x80b207b002400e80 0x602c81ec009003a0 0x79fe07f800000fc0 0xde7f81fe000003f0

def z221 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0x431e3ffff8000000 0xd0c78ffffe000000

def z222 : W := mkw 0x80fff7b007fdae83 0xe03ffdec01ff6ba0 0x11fd86e007ce0000 0x047f61b801f38000

def z223 : W := mkw 0x1000080858005154 0x0400020216001455 0x6a020118f8300fff 0xda8080463e0c03ff

def z224 : W := mkw 0x4000020102cb0c28 0x5000008040b2c30a 0x9e01860707cf0c3f 0x67806181c1f3c30f

def z225 : W := mkw 0x42fbffdff2cb0c28 0x50befff7fcb2c30a 0xffffffffffcf0c3f 0xfffffffffff3c30f

def z226 : W := mkw 0x50614f0ddacb5d7c 0x541853c376b2d75f 0xbee1ff07ffcffc3f 0x6fb87fc1fff3ff0f

def z227 : W := mkw 0x802007b002400e80 0x600801ec009003a0 0x39e007f807c00fc3 0xce7801fe01f003f0

def z228 : W := mkw 0x02fffddef5300002 0x00bfff77bd4c0000 0xfbfffffffff00003 0xfefffffffffc0000

def z229 : W := mkw 0x0004000004248001 0x0001000001092000 0x04000000062ec001 0x01000000018bb000

def z230 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8300fc3 0xfefffffffe0c03f0

def z231 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x96e1c607c7cf003c 0x25b87181f1f3c00f

def z232 : W := mkw 0x2108a2432a06c931 0x08422890ca81b24c 0x9e01a6073e0ec831 0x67806981cf83b20c

def z233 : W := mkw 0x2108a0432806c131 0x08422810ca01b04c 0xdf1da6e7380ec030 0xf7c769b9ce03b00c

def z234 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x451c20e03e2ecb31 0x914708380f8bb2cc

def z235 : W := mkw 0x02dff8da75bda003 0x80b7fe369d6f6800 0xfdfff8f83ffff003 0xbf7ffe3e0ffffc00

def z236 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x38e1870707ce0c03 0x4e3861c1c1f38300

def z237 : W := mkw 0x00dff20107bfa823 0x8037fc8041efea08 0xfefffe0707fff833 0x7fbfff81c1fffe0c

def z238 : W := mkw 0x23fffffffe26cb31 0x08ffffffff89b2cc 0xfffffffffe2ecb31 0xffffffffff8bb2cc

def z239 : W := mkw 0x000002010a024930 0x000000804280924c 0xde01a6073e2ecb31 0xf7806981cf8bb2cc

def z240 : W := mkw 0x1000080858005154 0x0400020216001455 0x00000018380003c0 0x800000060e0000f0

def z241 : W := mkw 0xd0f74fbddffb5ffe 0x743dd3ef77fed7ff 0xffffffffffffffff 0xffffffffffffffff

def z242 : W := mkw 0x40fff70587ffac2b 0xd03ffdc161ffeb0a 0xfeffff07c7fffc3f 0x7fbfffc1f1ffff0f

def z243 : W := mkw 0x210caa6b7e26cb31 0x08432a9adf89b2cc 0xff1ffffffe2ecb31 0xffc7ffffff8bb2cc

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z245 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x11fc06e007c00000 0x047f01b801f00000

def z246 : W := mkw 0x50614f0dd2cb1c6c 0x541853c374b2c71b 0xbee3df1fc7df3cff 0x6fb8f7c7f1f7cf3f

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x40020018003003c0 0x90008006000c00f0

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0xee024118c0310fff 0xfb809046300c43ff

def z249 : W := mkw 0x1000000008005154 0x0400000002001455 0xec0278000031ffff 0x3b009e00000c7fff

def z250 : W := mkw 0x0061470002c90c00 0x401851c000b24300 0xbce1c70007cf0c03 0x6f3871c001f3c300

def z251 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x151d86e7062ecb31 0x054761b9c18bb2cc

def z252 : W := mkw 0x310402210e26db75 0x0c4100884389b6dd 0x04000000063fffff 0x01000000018fffff

def z253 : W := mkw 0x92fffffeff705fd6 0x64bfffffbfdc17f5 0xfffffffffff1ffff 0xfffffffffffc7fff

def z254 : W := mkw 0x80bea7f227700e82 0x602fa9fc89dc03a0 0xfbffa7ff3ff00fc3 0xfeffe9ffcffc03f0

def z255 : W := mkw 0x610402210eefcf39 0x5841008843bbf3ce 0x0400000007efcf3f 0x0100000001fbf3cf

def z256 : W := mkw 0x0000080850000000 0x0000020214000000 0xee027918f831f003 0xfb809e463e0c7c00

def z257 : W := mkw 0x4041400480890008 0x1010500120224002 0x00004000c001000c 0x0000100030004003

def z258 : W := mkw 0x210ca0632c26c331 0x08432818cb09b0cc 0xc71da0e7382ec330 0xb1c76839ce0bb0cc

def z259 : W := mkw 0xa19ea2f32f36cbb3 0x2867a8bccbcdb2ec 0xdf1fa6ff3e3ecbf1 0xf7c7e9bfcf8fb2fc

def z260 : W := mkw 0x02fbfd9cd0000000 0x00beff6734000000 0xf8fff918c0000000 0x3e3ffe4630000000

def z261 : W := mkw 0xa1b607f32f724fb2 0x686d81fccbdc93ec 0x7bfe07ff3ff00ff3 0xdeff81ffcffc03fc

def z262 : W := mkw 0x4069e747a2cb0c28 0x501a79d1e8b2c30a 0xfffde7e7ffcf0c3f 0xffff79f9fff3c30f

def z263 : W := mkw 0x21bea7f32e26cb31 0x086fa9fccb89b2cc 0xffffa7ff3e2ecb31 0xffffe9ffcf8bb2cc

def z264 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0xec1e78000031f003 0x3b079e00000c7c00

def z265 : W := mkw 0x1000080850001044 0x0400020214000411 0xae025918c0113cff 0x6b80964630044f3f

def z266 : W := mkw 0x0049f000008da001 0x80127c0000236800 0xbce1f80007cff003 0x2f387e0001f3fc00

def z267 : W := mkw 0x0041400000890000 0x0010500000224000 0xfce3f80007fff003 0x3f38fe0001fffc00

def z268 : W := mkw 0x31000a6b7a025b74 0x0c40029ade8096dd 0x030007fff8000ffc 0xc0c001fffe0003ff

def z269 : W := mkw 0x21dff2632fbfeb33 0x8877fc98cbeffacc 0xdffda6e73feecb31 0xf7ff69b9cffbb2cc

def z270 : W := mkw 0x614de267aeafcb39 0x18537899ebabf2ce 0xdf1de6e7fe2fcb3d 0xf7c779b9ff8bf2cf

def z271 : W := mkw 0x90b607b00f705fd6 0x642d81ec03dc17f5 0x7dfe07f807f1ffff 0xdf7f81fe01fc7fff

def z272 : W := mkw 0x029eb8da7534a003 0x80a7ae369d4d2800 0x411e38f83830f000 0x90478e3e0e0c3c00

def z273 : W := mkw 0x4000020102cb0c28 0x5000008040b2c30a 0x0400000007cf0c3f 0x0100000001f3c30f

def z274 : W := mkw 0x42fbffdff2cb0c28 0x50befff7fcb2c30a 0xfbffffffffce0000 0xfefffffffff38000

def z275 : W := mkw 0x2108a0422804c111 0x084228108a013044 0x000020003800c000 0x000008000e003000

def z276 : W := mkw 0x42fbffdff2420c28 0x50befff7fc90830a 0xfbfffffff8000c3c 0xfefffffffe00030f

def z277 : W := mkw 0x0000000100020020 0x0000000040008008 0x86018007000e0030 0x21806001c003800c

def z278 : W := mkw 0x00d3500000000000 0x0034d40000000000 0x20e2580000000000 0x0838960000000000

def z279 : W := mkw 0x0000080850000000 0x0000020214000000 0x02000118f8000000 0xc08000463e000000

def z280 : W := mkw 0x310ca86a7c24d355 0x0c432a1a9f0934d5 0xef1e79f8f831ffff 0xfbc79e7e3e0c7fff

def z281 : W := mkw 0x8000022002400e80 0x60000088009003a0 0x0000000000000fc0 0x00000000000003f0

def z282 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff831f003 0xfffffffffe0c7c00

def z283 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0x001c000000000000 0x0007000000000000

def z284 : W := mkw 0xb1beaffb7f76dff7 0x6c6fabfedfddb7fd 0xffffffffffffffff 0xffffffffffffffff

def z285 : W := mkw 0x1000080858005154 0x0400020216001455 0x86007800f801f03c 0x21801e003e007c0f

def z286 : W := mkw 0x0041400000890000 0x0010500000224000 0x20e0400001c10002 0x0838100000704000

def z287 : W := mkw 0x31000a6b7a025b74 0x0c40029ade8096dd 0xef027ffff831ffff 0xfbc09ffffe0c7fff

def z288 : W := mkw 0x0004000005bda003 0x80010000016f6800 0x0400000007fff003 0x0100000001fffc00

def z289 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfdfe7ff807f1ffc3 0xff7f9ffe01fc7ff0

def z290 : W := mkw 0x0241580cd0000000 0x0090560334000000 0x00005800c0000000 0x0000160030000000

def z291 : W := mkw 0x2149f043288fe131 0x88527c10ca23f84c 0x8601f807380ff030 0x21807e01ce03fc0c

def z292 : W := mkw 0x210ca0622c24c311 0x084328188b0930c4 0xcf1c20e03820cb31 0xf3c708380e0832cc

def z293 : W := mkw 0x4061470482c90c08 0x501851c120b24302 0x38e04700c7c10c0f 0x4e3811c031f04303

def z294 : W := mkw 0x232caffffe26cb31 0x08cb2bffff89b2cc 0xdf1da7fffe2ecb31 0xf7c769ffff8bb2cc

def z295 : W := mkw 0x000ca20106268821 0x000328804189a208 0xde1da607062ec831 0x77876981c18bb20c

def z296 : W := mkw 0x0008b0000004a001 0x80022c0000012800 0x000038000000f000 0x00000e0000003c00

def z297 : W := mkw 0x90200fb85a405fd4 0x640803ee169017f5 0xef027ff8f831ffff 0xfbc09ffe3e0c7fff

def z298 : W := mkw 0x0000020102020820 0x0000008040808208 0x04000000060e0831 0x010000000183820c

def z299 : W := mkw 0x50000a095acb5d7c 0x5400028256b2d75f 0xee027918ffffffff 0xfb809e463fffffff

def z300 : W := mkw 0x82200ffef2400e80 0x608803ffbc9003a0 0x030007fff8000fc0 0xc0c001fffe0003f0

def z301 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x30e1c707c7cf040e 0x0c3871c1f1f3c103

def z302 : W := mkw 0x80b2059001500482 0x602c816400540120 0x68e2011801f00fc3 0xda388046007c03f0

def z303 : W := mkw 0x90b60fb85f705fd6 0x642d83ee17dc17f5 0x79fe3ff83ff0ffc3 0xde7f8ffe0ffc3ff0

def z304 : W := mkw 0x020008da70000000 0x008002369c000000 0x010000f838000000 0x8040003e0e000000

def z305 : W := mkw 0x02f35d9cd0000000 0x00bcd76734000000 0xbae3df1fc0000000 0x6eb8f7c7f0000000

def z306 : W := mkw 0x50200f0dda425d7c 0x540803c37690975f 0xee027f1ff831ffff 0xfb809fc7fe0c7fff

def z307 : W := mkw 0x210ca0622c24c311 0x084328188b0930c4 0xdd1da0e03e2ec301 0xb74768380f8bb0c0

def z308 : W := mkw 0x80f747b487700e82 0x603dd1ed21dc03a0 0xfbffc7ffc7f00fc3 0xfefff1fff1fc03f0

def z309 : W := mkw 0x90b60fb857701ec6 0x642d83ee15dc07b1 0x79fe5ff8c7f13fcf 0xde7f97fe31fc4ff3

def z310 : W := mkw 0x02fffddef5bda003 0x80bfff77bd6f6800 0xfbffffffffce0000 0xfefffffffff38000

def z311 : W := mkw 0x1000000008005154 0x0400000002001455 0x0000000000000ffc 0x00000000000003ff

def z312 : W := mkw 0x23200ffffa024b30 0x08c803fffe8092cc 0x030007fff8000b30 0xc0c001fffe0002cc

def z313 : W := mkw 0x2349f84ff806c131 0x08d27e13fe01b04c 0x8601f807f80ec030 0x21807e01fe03b00c

def z314 : W := mkw 0x310ca86a7c24d355 0x0c432a1a9f0934d5 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z315 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fa7ff3e3ecff3 0xffc7e9ffcf8fb3fc

def z316 : W := mkw 0x02fbfddef1992002 0x80beff77bc664800 0xfbfffffff9d13002 0xfefffffffe744c00

def z317 : W := mkw 0x40414005808b0028 0x101050016022c00a 0xbee1c007c7cf003f 0x2fb87001f1f3c00f

def z318 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0x78fe380007f0f003 0x1e3f8e0001fc3c00

def z319 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x22e04707c1c10c3e 0x48b811c1f070430f

def z320 : W := mkw 0x00dff0000dbde113 0x8037fc00036f7844 0xfefff8003ffffb33 0xffbffe000ffffecc

def z321 : W := mkw 0x4065472586eb0e28 0x501951c961bac38a 0xfffdc7e7c7ef0f3f 0xffff71f9f1fbc3cf

def z322 : W := mkw 0x90b60fb85f705fd6 0x642d83ee17dc17f5 0x7bfe07f8fff00fff 0xdeff81fe3ffc03ff

def z323 : W := mkw 0x0041500000892000 0x8010540000224800 0x0000580000013000 0x0000160000004c00

def z324 : W := mkw 0x0020059000000000 0x0008016400000000 0x010007f800000000 0xc04001fe00000000

def z325 : W := mkw 0x129ab8da78005154 0x04a6ae369e001455 0xef1e79f8f831ffff 0xfbc79e7e3e0c7fff

def z326 : W := mkw 0x0020070002400c00 0x400801c000900300 0x38e0070007c00c03 0x4e3801c001f00300

def z327 : W := mkw 0x1008a84a78005154 0x04022a129e001455 0xff1ffffff831ffff 0xffc7fffffe0c7fff

def z328 : W := mkw 0x02f35d9cd0000000 0x00bcd76734000000 0xeae27918f8000000 0xfab89e463e000000

def z329 : W := mkw 0x100400000dbdf157 0x84010000036f7c55 0x0400000007ffffff 0x0100000001ffffff

def z330 : W := mkw 0x0000004220000000 0x0000001088000000 0x030006e738000000 0xc0c001b9ce000000

def z331 : W := mkw 0x82bebffa77700e82 0x60afaffe9ddc03a0 0x79fe3ff83ff00fc3 0xde7f8ffe0ffc03f0

def z332 : W := mkw 0x00614d0cd0000000 0x0018534334000000 0xfae3ff1ff8000000 0xfeb8ffc7fe000000

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0279180031ffc3 0xfb009e46000c7ff0

def z334 : W := mkw 0x1000080858005154 0x0400020216001455 0xee027800f831f03f 0x3b809e003e0c7c0f

def z335 : W := mkw 0x2108a04320068021 0x08422810c801a008 0x00018007000e0000 0x00006001c0038000

def z336 : W := mkw 0x8092009001100082 0x2024802400440020 0x00020018001000c0 0x0000800600040030

def z337 : W := mkw 0x210000010806c131 0x084000004201b04c 0x04000000000ec030 0x010000000003b00c

def z338 : W := mkw 0x0000000008004110 0x0000000002001044 0x400020003820c300 0x900008000e0830c0

def z339 : W := mkw 0x0000000008004110 0x0000000002001044 0xee006100f821cf3f 0xfb8018403e0873cf

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x6802000000300003 0x1a008000000c0000

def z341 : W := mkw 0x82fbfffef2400e80 0x60beffffbc9003a0 0xfbfffffff8000fc0 0xfefffffffe0003f0

def z342 : W := mkw 0x00dbf00000000000 0x0036fc0000000000 0xfcfff8000031f003 0x3f3ffe00000c7c00

def z343 : W := mkw 0x00d7500005b92002 0x8035d400016e4800 0x78fe580007f13003 0x1e3f960001fc4c00

def z344 : W := mkw 0x00b6059005300002 0x002d8164014c0000 0x79fe07f807f00003 0xde7f81fe01fc0000

def z345 : W := mkw 0x1000080850001044 0x0400020214000411 0x00000118c00004cc 0x0000004630000133

def z346 : W := mkw 0x214de2632eafcb31 0x08537898cbabf2cc 0xfffde6e73fefcb33 0xffff79b9cffbf2cc

def z347 : W := mkw 0x33fffffffe26db75 0x0cffffffff89b6dd 0xfffffffffe3fffff 0xffffffffff8fffff

def z348 : W := mkw 0x716def6ffeefdf7d 0x5c5b7bdbffbbf7df 0xffffffffffffffff 0xffffffffffffffff

def z349 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x51fe06f807f003c0 0x947f81be01fc00f0

def z350 : W := mkw 0x61200767aa424f38 0x584801d9ea9093ce 0x030007e7f8000f3c 0xc0c001f9fe0003cf

def z351 : W := mkw 0x000ca22006248a01 0x0003288801892280 0xdd1da6e0062ecb01 0xf74769b8018bb2c0

def z352 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x11fc06e007f00fc3 0x047f01b801fc03f0

def z353 : W := mkw 0x809602b007700e82 0x602580ac01dc03a0 0x411e00f807f00fc3 0x9047803e01fc03f0

def z354 : W := mkw 0xc0fff7b587ffaeab 0xf03ffded61ffebaa 0xffffffffc7ffffff 0xfffffffff1ffffff

def z355 : W := mkw 0x4020050480400408 0x5008014120100102 0x00000100c000040c 0x0000004030000103

def z356 : W := mkw 0x42f35d9cd0c90408 0x50bcd76734324102 0x20e25918c1c1040e 0x0838964630704103

def z357 : W := mkw 0x12fbfddef8005154 0x04beff77be001455 0xfbfffffff830f3c0 0xfefffffffe0c3cf0

def z358 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xa2e3f91ff8000000 0x28b8fe47fe000000

def z359 : W := mkw 0x0000000000890000 0x0000000000224000 0x0400000007cf0003 0x0100000001f3c000

def z360 : W := mkw 0x12200ddef8005154 0x04880377be001455 0xef027ffff831ffff 0xfbc09ffffe0c7fff

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000011800000fc0 0xc0000046000003f0

def z362 : W := mkw 0x129ab8da78005154 0x04a6ae369e001455 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z363 : W := mkw 0x210002210a024b30 0x08400088428092cc 0x0000000000000b30 0x00000000000002cc

def z364 : W := mkw 0x3108a84b7806d175 0x0c422a12de01b45d 0xee03f91ff83fffff 0xfb80fe47fe0fffff

def z365 : W := mkw 0x0249f84ef0000000 0x00927e13bc000000 0xdb1dfee7f8000000 0xf6c77fb9fe000000

def z366 : W := mkw 0x00dbf00000000000 0x0036fc0000000000 0x10fd800000000000 0x043f600000000000

def z367 : W := mkw 0x0000020102020820 0x0000008040808208 0xbe01c707c60f0c3f 0x6f8071c1f183c30f

def z368 : W := mkw 0x0000020102020820 0x0000008040808208 0x10018607060e0000 0x04006181c1838000

def z369 : W := mkw 0x1041480858895154 0x0410520216225455 0xfee3f918ffffffff 0xffb8fe463fffffff

def z370 : W := mkw 0x8004022007700e82 0x6001008801dc03a0 0x6802011807f00fc3 0xda00804601fc03f0

def z371 : W := mkw 0x1000080858005154 0x0400020216001455 0x60027918f831f7ce 0x98009e463e0c7df3

def z372 : W := mkw 0x00f3459480000000 0x003cd16520000000 0xfbffc7ffc0000000 0xfefff1fff0000000

def z373 : W := mkw 0x0049f00000000000 0x00127c0000000000 0x8001f80000000000 0x20007e0000000000

def z374 : W := mkw 0x00dbf00000890000 0x0036fc0000224000 0xfcfff80007cf0003 0x3f3ffe0001f3c000

def z375 : W := mkw 0x616de767a6ef8e29 0x585b79d9e9bbe38a 0x11fd86e707ce0000 0x047f61b9c1f38000

def z376 : W := mkw 0x0096000005300002 0x00258000014c0000 0x78fe011807f00fc3 0xde3f804601fc03f0

def z377 : W := mkw 0x82f75fbcd7700e82 0x60bdd7ef35dc03a0 0x79fe5ff8c7f00fc3 0xde7f97fe31fc03f0

def z378 : W := mkw 0x0020050000000000 0x0008014000000000 0x38e0070000000000 0x4e3801c000000000

def z379 : W := mkw 0x0092000000000000 0x0024800000000000 0x78fe000000000000 0x1e3f800000000000

def z380 : W := mkw 0x82fffffef7fdae83 0xe0bfffffbdff6ba0 0xffffffffffffffc3 0xfffffffffffffff0

def z381 : W := mkw 0x80b6059005700482 0x602d8164015c0120 0x78fe011807f004c3 0x1e3f804601fc0130

def z382 : W := mkw 0x1000080858005154 0x0400020216001455 0xec0278183831f3c3 0xbb009e060e0c7cf0

def z383 : W := mkw 0x02f3559480000000 0x00bcd56520000000 0x00e0000000000000 0x0038000000000000

def z384 : W := mkw 0x82fffffef7700e82 0x60bfffffbddc03a0 0xfbffffffffc00000 0xfefffffffff00000

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0xe802780000000000 0x3a009e0000000000

def z386 : W := mkw 0x1000080858005154 0x0400020216001455 0x42023918f830fffc 0xd0808e463e0c3fff

def z387 : W := mkw 0x1000080858005154 0x0400020216001455 0x86007918f801fffc 0xe1801e463e007fff

def z388 : W := mkw 0x00dff00005300002 0x0037fc00014c0000 0xf8fff80007f00003 0x3e3ffe0001fc0000

def z389 : W := mkw 0x40614505808b0028 0x101851416022c00a 0xbee1c707c00f003c 0x6fb871c1f003c00f

def z390 : W := mkw 0x0008a04220000000 0x0002281088000000 0x411c20e038000000 0x904708380e000000

def z391 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0xeb1e79f8f8000000 0xfac79e7e3e000000

def z392 : W := mkw 0xa1bea7f32f76cfb3 0x686fa9fccbddb3ec 0xdffda6e73feecb31 0xf7ff69b9cffbb2cc

def z393 : W := mkw 0x00dff22007bdaa03 0x8037fc8801ef6a80 0xfdfffee007fffb03 0xff7fffb801fffec0

def z394 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xc41ff800003ff000 0x3107fe00000ffc00

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x38e0000007c00003 0x0e38000001f00000

def z396 : W := mkw 0x82fbfddef1500482 0x60beff77bc540120 0xfbfffffff9d004c2 0xfefffffffe740130

def z397 : W := mkw 0x80b607b007fdae83 0xe02d81ec01ff6ba0 0x7dfe07f807ffffc3 0xdf7f81fe01fffff0

def z398 : W := mkw 0x00d3500001992002 0x8034d40000664800 0xbce3d80007df3003 0x2f38f60001f7cc00

def z399 : W := mkw 0x2100026322020a20 0x08400098c8808288 0x010006e700000000 0x004001b9c0000000

def z400 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x14fd800007fff003 0x053f600001fffc00

def z401 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0xce0020003e2ecb31 0xf38008000f8bb2cc

def z402 : W := mkw 0x2108a2632a024b30 0x08422898ca8092cc 0xdb1da6e738000b30 0xf6c769b9ce0002cc

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0020000020c001 0x3300080000083000

def z404 : W := mkw 0x829eb8fa75300282 0x20a7ae3e9d4c00a0 0x411e38f8383003c0 0x90478e3e0e0c00f0

def z405 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3c71fc7ff0fff 0xffb8f1c7f1ffc3ff

def z406 : W := mkw 0x21dff2632e26cb31 0x0877fc98cb89b2cc 0xfffffee73e2ecb31 0xffffffb9cf8bb2cc

def z407 : W := mkw 0x1000000008005154 0x0400000002001455 0x000000000030f3c0 0x00000000000c3cf0

def z408 : W := mkw 0x1000080858005154 0x0400020216001455 0xce0238183830fbf1 0xf3808e060e0c3efc

def z409 : W := mkw 0x80f3559001d92482 0xe03cd56400764920 0x20e2591801d134c2 0x0838964600744d30

def z410 : W := mkw 0xa1b607b10f76cfb3 0x686d81ec43ddb3ec 0x7dfe07f807fecff3 0xdf7f81fe01ffb3fc

def z411 : W := mkw 0x004df00005bda003 0x80137c00016f6800 0x8401f80007fff003 0x21007e0001fffc00

def z412 : W := mkw 0x0000020102020820 0x0000008040808208 0x0200060700000830 0x40800181c000020c

def z413 : W := mkw 0x1000080850001044 0x0400020214000411 0xea027918f81134ce 0xfa809e463e044d33

def z414 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x9e018607062ecb31 0x67806181c18bb2cc

def z415 : W := mkw 0x000400000534a003 0x80010000014d2800 0x000000000030f000 0x00000000000c3c00

def z416 : W := mkw 0x0096000005bda003 0x80258000016f6800 0x7cfe000007fff003 0x1f3f800001fffc00

def z417 : W := mkw 0x02200ddef0000000 0x00880377bc000000 0xeb027ffff8000000 0xfac09ffffe000000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0xca00200038000000 0xf28008000e000000

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x591c06e000000000 0xd64701b800000000

def z420 : W := mkw 0x02dbf8def0000000 0x00b6fe37bc000000 0xc31ff8fff8000000 0xb0c7fe3ffe000000

def z421 : W := mkw 0x0004000005bda003 0x80010000016f6800 0xec02780007fff003 0x3b009e0001fffc00

def z422 : W := mkw 0x5041480dd88b517c 0x141052037622d45f 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z423 : W := mkw 0x80fff7b007fdae83 0xe03ffdec01ff6ba0 0x79ff87f807fe0fc3 0xde7fe1fe01ff83f0

def z424 : W := mkw 0x800000b000000280 0x2000002c000000a0 0x010000f8000003c0 0x8040003e000000f0

def z425 : W := mkw 0x02fffd9cd5bda003 0x80bfff67356f6800 0xfcfff918c7fff003 0x3f3ffe4631fffc00

def z426 : W := mkw 0x10000a095a025974 0x040002825680965d 0xfe03ff1ffe3fffff 0xff80ffc7ff8fffff

def z427 : W := mkw 0x212ca7632e66cf31 0x484b29d8cb99b3cc 0xfffda7e73feecf33 0xffff69f9cffbb3cc

def z428 : W := mkw 0x809eb0b00534a283 0xa027ac2c014d28a0 0x411e38f80030f3c0 0x90478e3e000c3cf0

def z429 : W := mkw 0x02b20ddef0000000 0x00ac8377bc000000 0x7bfe07fff8000000 0xdeff81fffe000000

def z430 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0xdb1fbeff38000000 0xf6c7efbfce000000

def z431 : W := mkw 0x234dfa6ffe26cb31 0x08d37e9bff89b2cc 0xdf1dfee7fe2ecb31 0xf7c77fb9ff8bb2cc

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800010000000c03 0x4a00004000000300

def z433 : W := mkw 0x0020050480000000 0x0008014120000000 0x02000707c0000000 0x408001c1f0000000

def z434 : W := mkw 0x0008a04228004110 0x000228108a001044 0xdf1da6e73820cb31 0xf7c769b9ce0832cc

def z435 : W := mkw 0x029ab0d220000000 0x00a6ac3488000000 0x011c00e000000000 0x0047003800000000

def z436 : W := mkw 0x0000000008004110 0x0000000002001044 0x040000000020cb31 0x01000000000832cc

def z437 : W := mkw 0x0004000005bda003 0x80010000016f6800 0x0000000007ce0000 0x0000000001f38000

def z438 : W := mkw 0x310caa6b7e26db75 0x0c432a9adf89b6dd 0xdf1da7fffe2ecffd 0xf7c769ffff8bb3ff

def z439 : W := mkw 0x0008a00000048001 0x0002280000012000 0x8401a000000ec000 0x210068000003b000

def z440 : W := mkw 0xa12ca7f32e66cfb1 0x684b29fccb99b3ec 0xdf1da7ff3e2ecff1 0xf7c769ffcf8bb3fc

def z441 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x94fdf80007cff000 0x253f7e0001f3fc00

def z442 : W := mkw 0xc0f3459481d9048a 0x703cd16520764122 0x20e24118c1d104ce 0x0838904630744133

def z443 : W := mkw 0x23fff7f7ae26cb31 0x08fffdfdeb89b2cc 0xdffda6e73e2ecb31 0xf7ff69b9cf8bb2cc

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x20004100c001040e 0x0800104030004103

def z445 : W := mkw 0x10dff8085dbdf157 0x8437fe02176f7c55 0xfefff800fffff03f 0x3fbffe003ffffc0f

def z446 : W := mkw 0x0000022002000a00 0x0000008800800280 0x010006e000000b00 0xc04001b8000002c0

def z447 : W := mkw 0x000ca26226200a00 0x0003289889880280 0xdb1da6e73e200b01 0xf6c769b9cf8802c0

def z448 : W := mkw 0x0004002004200200 0x0001000801080080 0x411c00e000200300 0x90470038000800c0

def z449 : W := mkw 0xc02007b582420ea8 0x700801ed609083aa 0x030007ffc0000ffc 0xc0c001fff00003ff

def z450 : W := mkw 0x50614d0cd0c9144c 0x5418534334324513 0x20e25918c1d134ce 0x0838964630744d33

def z451 : W := mkw 0x310caa6b7e26db75 0x0c432a9adf89b6dd 0xdf1fbeff3e3efbf1 0xf7c7efbfcf8fbefc

def z452 : W := mkw 0x1000080850001044 0x0400020214000411 0x00005800c001300c 0x0000160030004c03

def z453 : W := mkw 0x1000080858005154 0x0400020216001455 0xce002118f820cffd 0xf38008463e0833ff

def z454 : W := mkw 0x009ea00005348003 0x0027a800014d2000 0xfcffa00007fec003 0x3f3fe80001ffb000

def z455 : W := mkw 0x0020070002400c00 0x400801c000900300 0x0000070000000c00 0x400001c000000300

def z456 : W := mkw 0x2108a2632a06cb31 0x08422898ca81b2cc 0x8701a6e7380ecb30 0xe1c069b9ce03b2cc

def z457 : W := mkw 0xc2fffffff7fb0eaa 0x70bffffffdfec3aa 0xffffffffffff0fff 0xffffffffffffc3ff

def z458 : W := mkw 0x0041400000890000 0x0010500000224000 0x8401c000000f0000 0x210070000003c000

def z459 : W := mkw 0x80b2059001500482 0x602c816400540120 0x79fe07f801d004c2 0xde7f81fe00740130

def z460 : W := mkw 0x1000080850001044 0x0400020214000411 0x00021818001030c0 0x0000860600040c30

def z461 : W := mkw 0x0096022007300a02 0x0025808801cc0280 0x79fe06e007f00b03 0xde7f81b801fc02c0

def z462 : W := mkw 0x4049f005808fa029 0x90127c016023e80a 0x8601f807c00ff03c 0x21807e01f003fc0f

def z463 : W := mkw 0x1000080850001044 0x0400020214000411 0xec027918c031f4cf 0x3b009e46300c7d33

def z464 : W := mkw 0x0269fd4ef0000000 0x009a7f53bc000000 0xbae1ff07f8000000 0x6eb87fc1fe000000

def z465 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x59fc06e007e00b01 0xd67f01b801f802c0

def z466 : W := mkw 0x00b6070007700c02 0x402d81c001dc0300 0x78fe070007f00c03 0x5e3f81c001fc0300

def z467 : W := mkw 0xc0b607b107fb0eaa 0x702d81ec41fec3aa 0x7dfe07f807ff0fff 0xdf7f81fe01ffc3ff

def z468 : W := mkw 0x210ca2210e26cb31 0x084328884389b2cc 0xdc1da000062ecb31 0x37076800018bb2cc

def z469 : W := mkw 0x00dbf80850000000 0x0036fe0214000000 0xfafff918f8000000 0xfebffe463e000000

def z470 : W := mkw 0x52fbffdffacb5d7c 0x54befff7feb2d75f 0xffffffffffffffff 0xffffffffffffffff

def z471 : W := mkw 0x00d7400005b90002 0x0035d000016e4000 0xfcffc00007ff0003 0x3f3ff00001ffc000

def z472 : W := mkw 0x1000080858005154 0x0400020216001455 0xee027918f801f03c 0xfb809e463e007c0f

def z473 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x31fe07f807d004c2 0x0c7f81fe01f40130

def z474 : W := mkw 0x12fbfddef8005154 0x04beff77be001455 0xfbfffffff8000ffc 0xfefffffffe0003ff

def z475 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff900c7fffc3f 0x7fbffe4031ffff0f

def z476 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0xdc1fb800063ef001 0x3707ee00018fbc00

def z477 : W := mkw 0x1000080850001044 0x0400020214000411 0x68025918c0313fcf 0xda009646300c4ff3

def z478 : W := mkw 0x02babdda70000000 0x00aeaf769c000000 0x79fe3ff838000000 0xde7f8ffe0e000000

def z479 : W := mkw 0x02fffddef534a003 0x80bfff77bd4d2800 0xfbfffffff830f000 0xfefffffffe0c3c00

def z480 : W := mkw 0x40dff00585bfa02b 0x9037fc01616fe80a 0xfefff807c7fff03f 0x3fbffe01f1fffc0f

def z481 : W := mkw 0x4020070582420c28 0x500801c16090830a 0x9e018707c60e0c3d 0x678061c1f183830f

def z482 : W := mkw 0x210ca0622c24c311 0x084328188b0930c4 0xdb1da6e73820c300 0xf6c769b9ce0830c0

def z483 : W := mkw 0x80b605b005300282 0x202d816c014c00a0 0x79fe07f8003003c0 0xde7f81fe000c00f0

def z484 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x691e01f800300fc3 0xda47807e000c03f0

def z485 : W := mkw 0x80fff7b007fdae83 0xe03ffdec01ff6ba0 0xfdfffee007fff003 0x3f7fffb801fffc00

def z486 : W := mkw 0x0069e546a0000000 0x001a7951a8000000 0xfbfde7e7f8000000 0xfeff79f9fe000000

def z487 : W := mkw 0x4061450480c90408 0x5018514120324102 0xbce1c100c7cf040f 0x2f38704031f3c103

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000010c3f 0x010000000000430f

def z489 : W := mkw 0x0092009000000000 0x0024802400000000 0x411e00f800000000 0x9047803e00000000

def z490 : W := mkw 0x0269fddef0000000 0x009a7f77bc000000 0x8301fffff8000000 0xe0c07ffffe000000

def z491 : W := mkw 0x0041400000890000 0x0010500000224000 0xbee1c100c7cf0c3f 0x6fb8704031f3c30f

def z492 : W := mkw 0x0041400000890000 0x0010500000224000 0x10e1800007ce0000 0x0438600001f38000

def z493 : W := mkw 0x406147058acb4d38 0x501851c162b2d34e 0xfee1e707ffefcf3f 0xffb879c1fffbf3cf

def z494 : W := mkw 0x0004022006200a00 0x0001008801880280 0x111c06e006000000 0x044701b801800000

def z495 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x971da6e73e0ec030 0x25c769b9cf83b00c

def z496 : W := mkw 0x0200084ef0000000 0x00800213bc000000 0x02000007f8000000 0x00800001fe000000

def z497 : W := mkw 0x109eb8085d34f157 0x8427ae02174d3c55 0xee1e7918f831ffff 0xfb879e463e0c7fff

def z498 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x13fd87fff8000000 0xc4ff61fffe000000

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0xac00400000010003 0x2b00100000004000

def z500 : W := mkw 0x802007b002400e80 0x600801ec009003a0 0x010006e000000000 0x004001b800000000

def z501 : W := mkw 0x42f35f9dd2cb0c28 0x50bcd7e774b2c30a 0xbee3df1fc7cf0c3f 0x6fb8f7c7f1f3c30f

def z502 : W := mkw 0x02fbfddef8004110 0x00beff77be001044 0xfffffffff820cb31 0xfffffffffe0832cc

def z503 : W := mkw 0x4061450480c90408 0x5018514120324102 0xaee04100c1c10c3f 0x6bb810403070430f

def z504 : W := mkw 0x500002010acb5d7c 0x5400008042b2d75f 0x0400000007ffffff 0x0100000001ffffff

def z505 : W := mkw 0x02fbffdff2020820 0x00befff7fc808208 0xfffffffffe0e0831 0xffffffffff83820c

def z506 : W := mkw 0x8004022007700e82 0x6001008801dc03a0 0x591c06e007f00fc3 0xd64701b801fc03f0

def z507 : W := mkw 0x10dff8085dbdf157 0x8437fe02176f7c55 0xfcfff8183ffff3c3 0xbf3ffe060ffffcf0

def z508 : W := mkw 0x8096022007700e82 0x6025808801dc03a0 0x78fe000007f00fc3 0x1e3f800001fc03f0

def z509 : W := mkw 0xa3ffffffff76cfb3 0x68ffffffffddb3ec 0xfffffffffffecff3 0xffffffffffffb3fc

def z510 : W := mkw 0x616de767a6ef8e29 0x585b79d9e9bbe38a 0xbffdc7e7c7cf0c3f 0x6fff71f9f1f3c30f

def z511 : W := mkw 0x8024072007700e82 0x600901c801dc03a0 0x38e0070007f00fc3 0x4e3801c001fc03f0

def z512 : W := mkw 0x0061470482400c00 0x401851c120900300 0xbae1c707c7c00c03 0x6eb871c1f1f00300

def z513 : W := mkw 0x80bea7b007748e83 0x602fa9ec01dd23a0 0xfdffa7f807fecfc3 0xff7fe9fe01ffb3f0

def z514 : W := mkw 0x8004002005300282 0x20010008014c00a0 0x00000000003003c0 0x00000000000c00f0

def z515 : W := mkw 0xa19ea0f22d34c393 0x2867a83c8b4d30e4 0x411e20f83830c3c0 0x9047883e0e0c30f0

def z516 : W := mkw 0x109eb8085d34f157 0x8427ae02174d3c55 0x401e38183830f3c0 0x90078e060e0c3cf0

def z517 : W := mkw 0x0008a04220000000 0x0002281088000000 0x111d86e700000000 0x044761b9c0000000

def z518 : W := mkw 0x0008a04220000000 0x0002281088000000 0x8201a00738000000 0x20806801ce000000

def z519 : W := mkw 0x4061450480c90408 0x5018514120324102 0x00e0000001c00000 0x0038000000700000

def z520 : W := mkw 0xc0f747b587fb0eaa 0x703dd1ed61fec3aa 0x11fd86e707ce0000 0x047f61b9c1f38000

def z521 : W := mkw 0x0049f000008da001 0x80127c0000236800 0xec03f800003ff003 0x3b00fe00000ffc00

def z522 : W := mkw 0x0249f84ef08da001 0x80927e13bc236800 0x8601f807f80ff000 0x21807e01fe03fc00

def z523 : W := mkw 0x10d3580851993046 0x8434d60214664c11 0x20e25918c1d134ce 0x0838964630744d33

def z524 : W := mkw 0x8004022007fdae83 0xe001008801ff6ba0 0x0400000007ffffc3 0x0100000001fffff0

def z525 : W := mkw 0x00d3500001992002 0x8034d40000664800 0xece2780001f1f003 0x3b389e00007c7c00

def z526 : W := mkw 0xc0f747b587fb0eaa 0x703dd1ed61fec3aa 0x79ff87ff07fe0fc3 0xde7fe1ffc1ff83f0

def z527 : W := mkw 0x0000080858004110 0x0000020216001044 0xee027918f820cb31 0xfb809e463e0832cc

def z528 : W := mkw 0x82fff7f6a7700e82 0x60bffdfda9dc03a0 0x11fd86e707c00000 0x047f61b9c1f00000

def z529 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x30ffd80007df3002 0x0c3ff60001f7cc00

def z530 : W := mkw 0x0020070002400c00 0x400801c000900300 0x78e2071807f00fc3 0xde3881c601fc03f0

def z531 : W := mkw 0x0000080850000000 0x0000020214000000 0x82007800f8000000 0x20801e003e000000

def z532 : W := mkw 0x000ca00004248001 0x0003280001092000 0x401c20000020c000 0x1007080000083000

def z533 : W := mkw 0x0092000001100002 0x0024800000440000 0x20e2000001d00002 0x0838800000740000

def z534 : W := mkw 0x21dff2210fbfeb33 0x8877fc8843effacc 0xfcfff80007fffb33 0x3f3ffe0001fffecc

def z535 : W := mkw 0x82fff7f6a7700e82 0x60bffdfda9dc03a0 0x79ff87ff07f00fc3 0xde7fe1ffc1fc03f0

def z536 : W := mkw 0x1249f84ef8005154 0x04927e13be001455 0x8601f807f801f03c 0x21807e01fe007c0f

def z537 : W := mkw 0x1249f84ef8005154 0x04927e13be001455 0xee03f91ff831ffff 0xfb80fe47fe0c7fff

def z538 : W := mkw 0xc065472587fb0eaa 0x701951c961fec3aa 0xbee1c707c7ff0fff 0x6fb871c1f1ffc3ff

def z539 : W := mkw 0x0049f000008da001 0x80127c0000236800 0x00018000000e0000 0x0000600000038000

def z540 : W := mkw 0x1000080858005154 0x0400020216001455 0xce007800f821fb3d 0xf3801e003e087ecf

def z541 : W := mkw 0x00000000008da001 0x8000000000236800 0x04000000000ff000 0x010000000003fc00

def z542 : W := mkw 0x00fff50485bda003 0x803ffd41216f6800 0xfeffff07c7fff003 0x7fbfffc1f1fffc00

def z543 : W := mkw 0x82b60ffef7700e82 0x60ad83ffbddc03a0 0x7bfe07fffff00fc3 0xdeff81fffffc03f0

def z544 : W := mkw 0x1000080858005154 0x0400020216001455 0xae007900f801fc3f 0x6b801e403e007f0f

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000300fc3 0x00000000000c03f0

def z546 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0x79ff87ff00000000 0xde7fe1ffc0000000

def z547 : W := mkw 0x80f757b007f92e82 0xe03dd5ec01fe4ba0 0x79fe5ff807f13fc3 0xde7f97fe01fc4ff0

def z548 : W := mkw 0x000402200e204b10 0x00010088038812c4 0xdf1c26e03e20cb31 0xf7c709b80f8832cc

def z549 : W := mkw 0xa1bea7f327768ea3 0x686fa9fcc9dda3a8 0x11fd86e707ce0000 0x047f61b9c1f38000

def z550 : W := mkw 0x40414205828b0828 0x1010508160a2c20a 0x9e01c607c60f083d 0x67807181f183c20f

def z551 : W := mkw 0x0292189850000000 0x00a4862614000000 0x0002181800000000 0x0000860600000000

def z552 : W := mkw 0x00dbf000008da001 0x8036fc0000236800 0xfcfff800000ff000 0x3f3ffe000003fc00

def z553 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x78ff800007fe0003 0x1e3fe00001ff8000

def z554 : W := mkw 0x00b2059000000000 0x002c816400000000 0x11fc06e000000000 0x047f01b800000000

def z555 : W := mkw 0x0092100001102002 0x8024840000440800 0x0002180000103000 0x0000860000040c00

def z556 : W := mkw 0xa1bea7f327768ea3 0x686fa9fcc9dda3a8 0x79ff87ff07fe0fc3 0xde7fe1ffc1ff83f0

def z557 : W := mkw 0x4004020107ffac2b 0xd001008041ffeb0a 0x0400000007fffc3f 0x0100000001ffff0f

def z558 : W := mkw 0x216de767ae26cb31 0x085b79d9eb89b2cc 0xfffde7e7fe2ecb31 0xffff79f9ff8bb2cc

def z559 : W := mkw 0x23fffffff6268a21 0x08fffffffd89a288 0xfbfffffffe0e0000 0xfeffffffff838000

def z560 : W := mkw 0x0020070002400c00 0x400801c000900300 0x10e0060007c00000 0x0438018001f00000

def z561 : W := mkw 0x0020070002400c00 0x400801c000900300 0xbee04700c7c10c3f 0x6fb811c031f0430f

def z562 : W := mkw 0x0000000001992002 0x8000000000664800 0x0000000001d13002 0x0000000000744c00

def z563 : W := mkw 0x214df2632eafeb31 0x88537c98cbabfacc 0xdf1dfee73e2ffb31 0xf7c77fb9cf8bfecc

def z564 : W := mkw 0x00b607b006200a00 0x002d81ec01880280 0x79fe07f806200b01 0xde7f81fe018802c0

def z565 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x9f1d86e7060e0831 0x67c761b9c183820c

def z566 : W := mkw 0x00fbf59000000000 0x003efd6400000000 0xf9fffff800000000 0xfe7ffffe00000000

def z567 : W := mkw 0x12200ddef8005154 0x04880377be001455 0x030007fff8000ffc 0xc0c001fffe0003ff

def z568 : W := mkw 0x00dff0000534a003 0x8037fc00014d2800 0xf8fff8000030f000 0x3e3ffe00000c3c00

def z569 : W := mkw 0x80dff22007fdae83 0xe037fc8801ff6ba0 0xfcfff80007ffffc3 0x3f3ffe0001fffff0

def z570 : W := mkw 0x2100004328024130 0x08400010ca00904c 0x0200000738000030 0x00800001ce00000c

def z571 : W := mkw 0x63fffffffeefcf39 0x58ffffffffbbf3ce 0xffffffffffefcf3f 0xfffffffffffbf3cf

def z572 : W := mkw 0x31040a295e26db75 0x0c41028a5789b6dd 0xee027918fe3fffff 0xfb809e463f8fffff

def z573 : W := mkw 0x80b2059001500482 0x602c816400540120 0x00e0000001c00000 0x0038000000700000

def z574 : W := mkw 0x90b20d98595055d6 0x642c836616541575 0xeee27918f9f1ffff 0xfbb89e463e7c7fff

def z575 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x431c26e73820cb30 0xd0c709b9ce0832cc

def z576 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe07f807c00000 0xde7f81fe01f00000

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800000000200b01 0xd2000000000802c0

def z578 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x39fc07e007c00c03 0x4e7f01f801f00300

def z579 : W := mkw 0x40614f0dd2cb0c28 0x501853c374b2c30a 0xfee3ff1fffcf0c3f 0xffb8ffc7fff3c30f

def z580 : W := mkw 0x0249f84ef0000000 0x00927e13bc000000 0xea03f91ff8000000 0xfa80fe47fe000000

def z581 : W := mkw 0xc0f747b487f90e8a 0x703dd1ed21fe43a2 0x79fe47f8c7f10fcf 0xde7f91fe31fc43f3

def z582 : W := mkw 0x0000080850000000 0x0000020214000000 0x4002381838000000 0x90008e060e000000

def z583 : W := mkw 0x0000080850000000 0x0000020214000000 0xee027918f8010c3f 0xfb809e463e00430f

def z584 : W := mkw 0x90b20d98515014c6 0x642c836614540531 0x20e25918c1d134ce 0x0838964630744d33

def z585 : W := mkw 0x1000080858005154 0x0400020216001455 0x680239183830ffc3 0xda008e460e0c3ff0

def z586 : W := mkw 0x219eb0622d34e313 0x8867ac188b4d38c4 0x411e38e03830f300 0x90478e380e0c3cc0

def z587 : W := mkw 0x90040a285f705fd6 0x6401028a17dc17f5 0xee027918fff1ffff 0xfb809e463ffc7fff

def z588 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xf8fff80007ce0000 0x3e3ffe0001f38000

def z589 : W := mkw 0x616547258eefcf39 0x585951c963bbf3ce 0xbee1c707c7efcf3f 0x6fb871c1f1fbf3cf

def z590 : W := mkw 0x610ca2632eefcf39 0x58432898cbbbf3ce 0xdf1da6e73fefcf3f 0xf7c769b9cffbf3cf

def z591 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x8601a0073e2ecb31 0x21806801cf8bb2cc

def z592 : W := mkw 0x02dff84ef5bda003 0x80b7fe13bd6f6800 0xfefff807fffff003 0x3fbffe01fffffc00

def z593 : W := mkw 0x1000080858005154 0x0400020216001455 0xea027918f8000ffc 0xfa809e463e0003ff

def z594 : W := mkw 0x82fffdfef5300282 0x20bfff7fbd4c00a0 0xfbfffffff83003c0 0xfefffffffe0c00f0

def z595 : W := mkw 0x022005d6a0000000 0x00880175a8000000 0x010006e700000000 0x004001b9c0000000

def z596 : W := mkw 0x210002632a024b30 0x08400098ca8092cc 0x9f0186e73e0e0b31 0xe7c061b9cf8382cc

def z597 : W := mkw 0x239eb8fa7c24c311 0x08e7ae3e9f0930c4 0x411e38f83820c300 0x90478e3e0e0830c0

def z598 : W := mkw 0x0000000008004110 0x0000000002001044 0xee0221183830cff3 0xfb8088460e0c33fc

def z599 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xdcfda00007eec001 0x373f680001fbb000

def z600 : W := mkw 0x210ca2622e24cb11 0x084328988b8932c4 0x591c26e03e20cb01 0xd64709b80f8832c0

def z601 : W := mkw 0x4000020102420c28 0x500000804090830a 0x0000000000000c3c 0x000000000000030f

def z602 : W := mkw 0xa1bea7f22f74cf93 0x686fa9fc8bdd33e4 0x79fe27f83ff0cfc3 0xde7f89fe0ffc33f0

def z603 : W := mkw 0x00fff70007fdac03 0xc03ffdc001ff6b00 0xfcffff0007fffc03 0x7f3fffc001ffff00

def z604 : W := mkw 0x1000080858005154 0x0400020216001455 0x06000118f831ffff 0xc18000463e0c7fff

def z605 : W := mkw 0x02fff5d6a5bda003 0x80bffd75a96f6800 0x11fd86e707ce0000 0x047f61b9c1f38000

def z606 : W := mkw 0x0000020002400c00 0x4000008000900300 0x0000000007c00c03 0x0000000001f00300

def z607 : W := mkw 0x0004022006200a00 0x0001008801880280 0x791e07f806300fc3 0xde4781fe018c03f0

def z608 : W := mkw 0x10b20d9858005154 0x042c836616001455 0xfffe7ff8f831ffff 0xffff9ffe3e0c7fff

def z609 : W := mkw 0x50614f0ddacb5d7c 0x541853c376b2d75f 0xbee1c71fffcf0fff 0xefb871c7fff3c3ff

def z610 : W := mkw 0x4000020102cb0c28 0x5000008040b2c30a 0xae004100c7cf0c3f 0x6b80104031f3c30f

def z611 : W := mkw 0x8000000001500482 0x6000000000540120 0x0000000001d004c2 0x0000000000740130

def z612 : W := mkw 0x3108a84b7806d175 0x0c422a12de01b45d 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z613 : W := mkw 0x12fffddefdbdf157 0x84bfff77bf6f7c55 0xffffffffffffffff 0xffffffffffffffff

def z614 : W := mkw 0x1000080858005154 0x0400020216001455 0x22025918f8113ffe 0xc88096463e044fff

def z615 : W := mkw 0x02dbf8da70000000 0x00b6fe369c000000 0xf9fff8f838000000 0xbe7ffe3e0e000000

def z616 : W := mkw 0xc0f3479583db0caa 0x703cd1e560f6c32a 0xbee3c71fc7df0cff 0x6fb8f1c7f1f7c33f

def z617 : W := mkw 0x50ffff0ddffffd7f 0xd43fffc377ffff5f 0xfeffff1fffffffff 0xffbfffc7ffffffff

def z618 : W := mkw 0x100ca8085c24d155 0x04032a0217093455 0xfe1ff918fe3fffff 0xff87fe463f8fffff

def z619 : W := mkw 0x0000080850000000 0x0000020214000000 0x20025918c0000000 0x0800964630000000

def z620 : W := mkw 0x8004022007700e82 0x6001008801dc03a0 0x0000000007c00000 0x0000000001f00000

def z621 : W := mkw 0x000ca00005bda003 0x80032800016f6800 0xdc1da00007fff003 0x3707680001fffc00

def z622 : W := mkw 0x40fff50485fda40b 0xd03ffd41217f6902 0xfcfff900c7fff40f 0x3f3ffe4031fffd03

def z623 : W := mkw 0xa12007f32a424fb0 0x684801fcca9093ec 0x030007ff38000ff0 0xc0c001ffce0003fc

def z624 : W := mkw 0x0249f046a0000000 0x00927c11a8000000 0x0001800700000000 0x00006001c0000000

def z625 : W := mkw 0x12fbfddef8005154 0x04beff77be001455 0xfffffffff801f03c 0xfffffffffe007c0f

def z626 : W := mkw 0x2108a0432806c131 0x08422810ca01b04c 0xce01a007382ecb31 0xf3806801ce0bb2cc

def z627 : W := mkw 0x10dff80855bdb047 0x8437fe02156f6c11 0xfcfff918c7fff4cf 0x3f3ffe4631fffd33

def z628 : W := mkw 0x0041400000000000 0x0010500000000000 0xb8e1c00000000000 0x2e38700000000000

def z629 : W := mkw 0x80fff59005fda483 0xe03ffd64017f6920 0xfcfff91807fff4c3 0x3f3ffe4601fffd30

def z630 : W := mkw 0x0004000004200000 0x0001000001080000 0x581c000006200001 0x1607000001880000

def z631 : W := mkw 0x42fbf7d7a2cb0c28 0x50befdf5e8b2c30a 0x11fd86e707ce0000 0x047f61b9c1f38000

def z632 : W := mkw 0x0000000008004110 0x0000000002001044 0x860020003800c030 0x218008000e00300c

def z633 : W := mkw 0x100408085dbdf157 0x84010202176f7c55 0xee027918ffffffff 0xfb809e463fffffff

def z634 : W := mkw 0x4000020102cb0c28 0x5000008040b2c30a 0x0000000007ce0000 0x0000000001f38000

def z635 : W := mkw 0x0061470582020820 0x001851c160808208 0xbee1c707c60e0831 0x6fb871c1f183820c

def z636 : W := mkw 0x1000000008005154 0x0400000002001455 0x6c0201180031ffff 0xdb008046000c7fff

def z637 : W := mkw 0x4269ff4ff2cb0c28 0x509a7fd3fcb2c30a 0xbee1ff07ffcf0c3f 0x6fb87fc1fff3c30f

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x400238000030f000 0x10008e00000c3c00

def z639 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x9ee1860707ce0831 0x67b86181c1f3820c

def z640 : W := mkw 0x219ea2632f36cb33 0x0867a898cbcdb2cc 0xffffa6e73ffecb33 0xffffe9b9cfffb2cc

def z641 : W := mkw 0x40fff70587ffac2b 0xd03ffdc161ffeb0a 0x10fd860707ce0000 0x043f6181c1f38000

def z642 : W := mkw 0x10dbf80858005154 0x0436fe0216001455 0xfefff918f831ffff 0xffbffe463e0c7fff

def z643 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0xdd1da6e7062ec001 0x374769b9c18bb000

def z644 : W := mkw 0x00b2059000000000 0x002c816400000000 0x20e2011800000000 0x0838804600000000

def z645 : W := mkw 0x40dff20107ffac2b 0xd037fc8041ffeb0a 0xfcfff80007fffc3f 0x3f3ffe0001ffff0f

def z646 : W := mkw 0x02614ddef0000000 0x00985377bc000000 0xbbe1c7fff8000000 0xeef871fffe000000

def z647 : W := mkw 0x40fff70587ffac2b 0xd03ffdc161ffeb0a 0xfcfffe0707fff003 0x3f3fff81c1fffc00

def z648 : W := mkw 0x909608b85d3053d6 0x2425822e174c14f5 0xef1e79f8f831ffff 0xfbc79e7e3e0c7fff

def z649 : W := mkw 0x0000080850000000 0x0000020214000000 0xea027918f8300fc3 0xfa809e463e0c03f0

def z650 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x591d86e7062e0b01 0xd64761b9c18b82c0

def z651 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x5d1c06e0062ecb31 0xd74701b8018bb2cc

def z652 : W := mkw 0x4061450580cb0428 0x501851416032c10a 0xa6e1c107c1cf043e 0x29b87041f073c10f

def z653 : W := mkw 0x210ca2632fbfeb33 0x88432898cbeffacc 0xdf1da6e73ffffb33 0xf7c769b9cffffecc

def z654 : W := mkw 0x1000080858005154 0x0400020216001455 0x440238183831ffff 0x91008e060e0c7fff

def z655 : W := mkw 0x00b20d9850000000 0x002c836614000000 0xfbfe7ff8f8000000 0xfeff9ffe3e000000

def z656 : W := mkw 0x10d3580859997156 0x8434d60216665c55 0xeee27918f9f1ffff 0xfbb89e463e7c7fff

def z657 : W := mkw 0x0045400005bda003 0x80115000016f6800 0xbce1c00007fff003 0x2f38700001fffc00

def z658 : W := mkw 0x42614fdff2cb0c28 0x509853f7fcb2c30a 0xbfe1c7ffffcf0c3f 0xeff871fffff3c30f

def z659 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x60fe780001f1f002 0x183f9e00007c7c00

def z660 : W := mkw 0x80b607b00f704f92 0x602d81ec03dc13e4 0xfffe27f83ff0cff3 0xffff89fe0ffc33fc

def z661 : W := mkw 0x90200fb85a405fd4 0x640803ee169017f5 0x030007f8f8000ffc 0xc0c001fe3e0003ff

def z662 : W := mkw 0x42ffffdff7ffac2b 0xd0bffff7fdffeb0a 0xfffffffffffffc3f 0xffffffffffffff0f

def z663 : W := mkw 0x23fff7f7a6268a21 0x08fffdfde989a288 0x11fd86e7060e0000 0x047f61b9c1838000

def z664 : W := mkw 0x210ca0432c26c131 0x08432810cb09b04c 0xde1da0073e2ec031 0x37876801cf8bb00c

def z665 : W := mkw 0x4041420582cb0c28 0x5010508160b2c30a 0x8601c007c7cf0c3f 0x21807001f1f3c30f

def z666 : W := mkw 0x6169e747aacfcd39 0x585a79d1eab3f34e 0xbee1e707ffcfcc3f 0x6fb879c1fff3f30f

def z667 : W := mkw 0x00b2059000000000 0x002c816400000000 0x79fe07f800300fc3 0xde7f81fe000c03f0

def z668 : W := mkw 0x10040a285e205b54 0x0401028a178816d5 0xff1e7ff8fe31ffff 0xffc79ffe3f8c7fff

def z669 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x8601c707c00f0c3c 0x618071c1f003c30f

def z670 : W := mkw 0x1000080858005154 0x0400020216001455 0xea027918f830f3c0 0xfa809e463e0c3cf0

def z671 : W := mkw 0x80fff7b007700e82 0x603ffdec01dc03a0 0xf9fffff807f00fc3 0xfe7ffffe01fc03f0

def z672 : W := mkw 0x210002632a024b30 0x08400098ca8092cc 0xcf0026e73820cb31 0xf3c009b9ce0832cc

def z673 : W := mkw 0x21dff26327bfaa23 0x8877fc98c9efea88 0x11fd86e707ce0000 0x047f61b9c1f38000

def z674 : W := mkw 0x0061450480890000 0x0018514120224000 0xbee1c707c7cf0003 0x6fb871c1f1f3c000

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c018000060e0001 0x2700600001838000

def z676 : W := mkw 0x1000080858005154 0x0400020216001455 0xae004118f8010fff 0xeb8010463e0043ff

def z677 : W := mkw 0x12f35d9cd0001044 0x04bcd76734000411 0x20e25918c01134ce 0x0838964630044d33

def z678 : W := mkw 0x02fbffdef2400c00 0x40befff7bc900300 0xfbffffffffc00c03 0xfefffffffff00300

def z679 : W := mkw 0x4069f70582cfac29 0xd01a7dc160b3eb0a 0xbee1ff07c7cffc3f 0x6fb87fc1f1f3ff0f

def z680 : W := mkw 0x0041400480000000 0x0010500120000000 0x8201c007c0000000 0x20807001f0000000

def z681 : W := mkw 0x009ab00000000000 0x0026ac0000000000 0x401e380000000000 0x10078e0000000000

def z682 : W := mkw 0xa1fff7f32fffefb3 0xe87ffdfccbfffbec 0xffffffff3ffffff3 0xffffffffcffffffc

def z683 : W := mkw 0x80b60fb857700e82 0x602d83ee15dc03a0 0xfbfe7ff8fff00fc3 0xfeff9ffe3ffc03f0

def z684 : W := mkw 0x0024072006600e00 0x400901c801980380 0x79fc07e007e00f03 0xde7f01f801f803c0

def z685 : W := mkw 0x40fbf70582cb0c28 0x503efdc160b2c30a 0xfeffff07c7cf0c3f 0x7fbfffc1f1f3c30f

def z686 : W := mkw 0x02fffddef4248001 0x00bfff77bd092000 0xfffffffffe2ec001 0xffffffffff8bb000

def z687 : W := mkw 0x00d3500001992002 0x8034d40000664800 0x00e0000001c00000 0x0038000000700000

def z688 : W := mkw 0x0208b84a70000000 0x00822e129c000000 0x0000380038000000 0x00000e000e000000

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x20020118001004c2 0x0800804600040130

def z690 : W := mkw 0x21dff26327bfaa23 0x8877fc98c9efea88 0xfdfffee707fff003 0x3f7fffb9c1fffc00

def z691 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x61fe79f8f8000000 0x987f9e7e3e000000

def z692 : W := mkw 0x109608085d305156 0x04258202174c1455 0xfefe7918fff1ffff 0xffbf9e463ffc7fff

def z693 : W := mkw 0x4020070582420c28 0x500801c16090830a 0x3ae00707c7c00c3f 0x4eb801c1f1f0030f

def z694 : W := mkw 0x1000000000001044 0x0400000000000411 0x00000000001134ce 0x0000000000044d33

def z695 : W := mkw 0x0020070102420c20 0x400801c040908308 0xbee1870707ce0c33 0x6fb861c1c1f3830c

def z696 : W := mkw 0x02200d9cd0000000 0x0088036734000000 0x00000118c0000000 0x0000004630000000

def z697 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe06e007f00003 0x1e7f81b801fc0000

def z698 : W := mkw 0x23fbfffffa024b30 0x08fefffffe8092cc 0xfbfffffff8000b30 0xfefffffffe0002cc

def z699 : W := mkw 0x219eb2632f36eb33 0x8867ac98cbcdbacc 0xdf1fbee73e3efb31 0xf7c7efb9cf8fbecc

def z700 : W := mkw 0x0061450480000000 0x0018514120000000 0x20e04100c0000000 0x0838104030000000

def z701 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xbcfdc00007cf0003 0x2f3f700001f3c000

def z702 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x14e1860707cf0c3f 0x05386181c1f3c30f

def z703 : W := mkw 0x1000080858005154 0x0400020216001455 0x000038003800f000 0x00000e000e003c00

def z704 : W := mkw 0x4000000000c90408 0x5000000000324102 0x0000000001c1040e 0x0000000000704103

def z705 : W := mkw 0x00dbf000019da003 0x8036fc0000676800 0xa4e3f80001dff002 0x2938fe000077fc00

def z706 : W := mkw 0x009eb00005bda003 0x8027ac00016f6800 0x441e380007fff003 0x11078e0001fffc00

def z707 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0x13fd86e738000000 0xc4ff61b9ce000000

def z708 : W := mkw 0x210402210eafeb31 0x8841008843abfacc 0x04000000062ffb31 0x01000000018bfecc

def z709 : W := mkw 0xa1b607b10f76cfb3 0x686d81ec43ddb3ec 0x24e2011807fecff3 0x0938804601ffb3fc

def z710 : W := mkw 0x00baa5d220000000 0x002ea97488000000 0xdbfda6e738000000 0xf6ff69b9ce000000

def z711 : W := mkw 0x80b2059001500482 0x602c816400540120 0x79fe07f801f00fc3 0xde7f81fe007c03f0

def z712 : W := mkw 0x02240ddef5bda003 0x80890377bd6f6800 0x070007fffffff003 0xc1c001fffffffc00

def z713 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fa7ff3e2ecb31 0xffc7e9ffcf8bb2cc

def z714 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfffdc7e7c7cf0c3f 0xffff71f9f1f3c30f

def z715 : W := mkw 0x429abadb72cb0c28 0x50a6aeb6dcb2c30a 0x451e38f83fcf0c3f 0x91478e3e0ff3c30f

def z716 : W := mkw 0x710402210eefdf7d 0x5c41008843bbf7df 0x0400000007ffffff 0x0100000001ffffff

def z717 : W := mkw 0xb10ca2632f76dff7 0x6c432898cbddb7fd 0xdf1da6e73fffffff 0xf7c769b9cfffffff

def z718 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x93fdfffff8000000 0xe4ff7ffffe000000

def z719 : W := mkw 0x02fbfddef1100002 0x00beff77bc440000 0xfbfffffff9d00002 0xfefffffffe740000

def z720 : W := mkw 0x210402632e224b30 0x08410098cb8892cc 0xdf1d86e73e2e0b31 0xf7c761b9cf8b82cc

def z721 : W := mkw 0x31040a295e26db75 0x0c41028a5789b6dd 0x24025918c63fffff 0x09009646318fffff

def z722 : W := mkw 0x4061570582cb2c28 0xd01855c160b2cb0a 0xbee1df07c7cf3c3f 0x6fb877c1f1f3cf0f

def z723 : W := mkw 0x0049e04220000000 0x0012781088000000 0xfbfde6e738000000 0xfeff79b9ce000000

def z724 : W := mkw 0x214df2210eafeb31 0x88537c8843abfacc 0x8401f800062ffb31 0x21007e00018bfecc

def z725 : W := mkw 0x4069e546a0c90408 0x501a7951a8324102 0xfbfde7e7f9c1040e 0xfeff79f9fe704103

def z726 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee1e707c7efcc3f 0x7fb879c1f1fbf30f

def z727 : W := mkw 0xc0b607b587720eaa 0x702d81ed61dc83aa 0x79fe07ff07f00fc3 0xde7f81ffc1fc03f0

def z728 : W := mkw 0x210ca0432c26c131 0x08432810cb09b04c 0xdf1da6e73e2ec031 0xf7c769b9cf8bb00c

def z729 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1ff07c7cffc3f 0x6fb87fc1f1f3ff0f

def z730 : W := mkw 0x00fbe5d6a0000000 0x003ef975a8000000 0xfbffe7fff8000000 0xfefff9fffe000000

def z731 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee1e707ffcf0c3f 0xffb879c1fff3c30f

def z732 : W := mkw 0x1000080858005154 0x0400020216001455 0xfe03ff1ff831ffff 0xff80ffc7fe0c7fff

def z733 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x9f1d86e73e0e0b31 0xe7c761b9cf8382cc

def z734 : W := mkw 0x8069f7b002cdae81 0xe01a7dec00b36ba0 0x8501fff8000fffc0 0xe1407ffe0003fff0

def z735 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x59fc07f807e00fc1 0xd67f01fe01f803f0

def z736 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe06f807f003c3 0x9e7f81be01fc00f0

def z737 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x31fe07f807f00fc3 0x0c7f81fe01fc03f0

def z738 : W := mkw 0x0008a04220000000 0x0002281088000000 0x931da6e738000000 0x24c769b9ce000000

def z739 : W := mkw 0xc0b607b107720eaa 0x702d81ec41dc83aa 0x79fe07f807f00fff 0xde7f81fe01fc03ff

def z740 : W := mkw 0x00414201028b0820 0x0010508040a2c208 0xbee1c707c7cf0c3f 0x6fb871c1f1f3c30f

def z741 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfdff87f807fe0fc3 0xff7fe1fe01ff83f0

def z742 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xf9fffeff38000000 0xbe7fffbfce000000

def z743 : W := mkw 0x00d3500001992002 0x8034d40000664800 0xfce3f80007fff003 0x3f38fe0001fffc00

def z744 : W := mkw 0xa1baa5d32956c5b3 0x686ea974ca55b16c 0xa6e3a11f39dec4f2 0x29b8e847ce77b13c

def z745 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0xec027800063ffb33 0x3b009e00018ffecc

def z746 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0xdb1da6e73e2e0b01 0xf6c769b9cf8b82c0

def z747 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfffe07f807f00ff3 0xffff81fe01fc03fc

def z748 : W := mkw 0x40614505808b0028 0x101851416022c00a 0xbee1c707c7cf003f 0x6fb871c1f1f3c00f

def z749 : W := mkw 0x10dff8085dbdf157 0x8437fe02176f7c55 0x12fd8118ffce0ffc 0xc4bf60463ff383ff

def z750 : W := mkw 0x02fbfddef0892000 0x80beff77bc224800 0xfbfffffff8013000 0xfefffffffe004c00

def z751 : W := mkw 0x40beb7058776ac2b 0xd02fadc161ddab0a 0x421e3f07c030fc3c 0x50878fc1f00c3f0f

def z752 : W := mkw 0x12fbf5d6a8005154 0x04befd75aa001455 0x15fd86e70031ffff 0x057f61b9c00c7fff

def z753 : W := mkw 0x00dff00485bda003 0x8037fc01216f6800 0xfefff807c7fff003 0x3fbffe01f1fffc00

def z754 : W := mkw 0x80b607b107720ea2 0x602d81ec41dc83a8 0x79ff87ff07fe0fc3 0xde7fe1ffc1ff83f0

def z755 : W := mkw 0x4041420582cb0c28 0x5010508160b2c30a 0xbee1c007c7cf0c3f 0x2fb87001f1f3c30f

def z756 : W := mkw 0x210ca2632e66cf31 0x48432898cb99b3cc 0xdf1da6e73feecf33 0xf7c769b9cffbb3cc

def z757 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff80007fff833 0x7fbffe0001fffe0c

def z758 : W := mkw 0xa10402210f76cfb3 0x6841008843ddb3ec 0x0400000007eecb31 0x0100000001fbb2cc

def z759 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0x431e3eff38000000 0xd0c78fbfce000000

def z760 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xfffffffff80f0000 0xfffffffffe03c000

def z761 : W := mkw 0x0228a5d6a0000000 0x008a2975a8000000 0xdb1da6e738000000 0xf6c769b9ce000000

def z762 : W := mkw 0x00b205d220000000 0x002c817488000000 0x7bfe07ff38000000 0xdeff81ffce000000

def z763 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xfbfde7e7f8000000 0xfeff79f9fe000000

def z764 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfbfffffff81030c0 0xfefffffffe040c30

def z765 : W := mkw 0x610402210eefcf39 0x5841008843bbf3ce 0x0400000007eecb31 0x0100000001fbb2cc

def z766 : W := mkw 0x616de566acedc719 0x585b7959ab3b71c6 0x61fc61e0f9e1c70e 0x987f18783e7871c3

def z767 : W := mkw 0x3149f84b788ff175 0x8c527e12de23fc5d 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z768 : W := mkw 0x52fbfddef0c9144c 0x54beff77bc324513 0xfbfffffff9d134ce 0xfefffffffe744d33

def z769 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xfbfffffff9c10002 0xfefffffffe704000

def z770 : W := mkw 0x1000080858005154 0x0400020216001455 0xc6027918f831fffc 0xf1809e463e0c7fff

def z771 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1de6e7fe2fcb3d 0xf7c779b9ff8bf2cf

def z772 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff83003c0 0xfefffffffe0c00f0

def z773 : W := mkw 0x40dff00485bda00b 0x9037fc01216f6802 0xfcfff800c7fff00f 0x3f3ffe0031fffc03

def z774 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdd1da6e73e2ec301 0xb74769b9cf8bb0c0

def z775 : W := mkw 0x0008a04220000000 0x0002281088000000 0xdf1da6e73e0e0001 0xf7c769b9cf838000

def z776 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff8003ffff003 0xffbffe000ffffc00

def z777 : W := mkw 0xd00402210ffb5ffe 0x7401008843fed7ff 0x0400000007ffffff 0x0100000001ffffff

def z778 : W := mkw 0x02fbfddef08da001 0x80beff77bc236800 0xffffffffffcff003 0xfffffffffff3fc00

def z779 : W := mkw 0x21d352632b9b6b32 0x8874d498cae6dacc 0x23e25ee739d13b32 0xc8f897b9ce744ecc

def z780 : W := mkw 0x0208a84ef0000000 0x00822a13bc000000 0xdb1da6e7f8000000 0xf6c769b9fe000000

def z781 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x71fffffff8000000 0x9c7ffffffe000000

def z782 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x3ae18707c7ce0c3f 0x4eb861c1f1f3830f

def z783 : W := mkw 0x42fbfddef0c90408 0x50beff77bc324102 0xffffffffffcf040f 0xfffffffffff3c103

def z784 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x11fc06f807c003c0 0x847f01be01f000f0

def z785 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x971da6e73e2ecb31 0x25c769b9cf8bb2cc

def z786 : W := mkw 0xa10ca2632f76cfb3 0x68432898cbddb3ec 0xdf1da6e73feecb31 0xf7c769b9cffbb2cc

def z787 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff800c7fff03f 0x3fbffe0031fffc0f

def z788 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x11fd86ff38000000 0x847f61bfce000000

def z789 : W := mkw 0x824dfa6ef7700e82 0x60937e9bbddc03a0 0x8201f807fff00fc3 0x20807e01fffc03f0

def z790 : W := mkw 0x310caa6b76269a65 0x0c432a9add89a699 0x311fdfffc61f34ce 0x0c47f7fff187cd33

def z791 : W := mkw 0x00b6059005300002 0x002d8164014c0000 0x79fe07f807f00fc3 0xde7f81fe01fc03f0

def z792 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x591da6e73e2ecb01 0xd64769b9cf8bb2c0

def z793 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x000000000020cb30 0x00000000000832cc

def z794 : W := mkw 0xa10ca2632f76cfb3 0x68432898cbddb3ec 0xff1fa7ff3ffecff3 0xffc7e9ffcfffb3fc

def z795 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x39fc07f807c00fc3 0xce7f01fe01f003f0

def z796 : W := mkw 0x00dff04225bda003 0x8037fc10896f6800 0xfdfff8e03ffff003 0xbf7ffe380ffffc00

def z797 : W := mkw 0x0049e04220890000 0x0012781088224000 0xfffde6e73fcf0003 0xffff79b9cff3c000

def z798 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x04000000060ec030 0x010000000183b00c

def z799 : W := mkw 0xe10402210fffcfbb 0x7841008843fff3ee 0x0400000007ffcfff 0x0100000001fff3ff

def z800 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1de7e7fe2ecb31 0xffc779f9ff8bb2cc

def z801 : W := mkw 0x0008a84a70000000 0x00022a129c000000 0xdb1dfee7f8000000 0xf6c77fb9fe000000

def z802 : W := mkw 0x210cb2632e26eb31 0x88432c98cb89bacc 0xdf1dbee73e2efb31 0xf7c76fb9cf8bbecc

def z803 : W := mkw 0x0000004220000000 0x0000001088000000 0x5b1c06e738000000 0xd6c701b9ce000000

def z804 : W := mkw 0x0008a04220000000 0x0002281088000000 0x511da6e738000000 0x944769b9ce000000

def z805 : W := mkw 0x80b605b005700682 0x602d816c015c01a0 0x79fe07f801f007c2 0xde7f81fe007c01f0

def z806 : W := mkw 0x009eb0000534a003 0x8027ac00014d2800 0xfcffb80007fef003 0x3f3fee0001ffbc00

def z807 : W := mkw 0x809602b007700e82 0x602580ac01dc03a0 0x79fe00f807f00fc3 0x9e7f803e01fc03f0

def z808 : W := mkw 0x42fbfddef0c90408 0x50beff77bc324102 0xfbfffffff9c00000 0xfefffffffe700000

def z809 : W := mkw 0x0008a04220048001 0x0002281088012000 0xdf1da6e7380ec000 0xf7c769b9ce03b000

def z810 : W := mkw 0x02fbfddef1992002 0x80beff77bc664800 0xfffffffff9f1f003 0xfffffffffe7c7c00

def z811 : W := mkw 0x82fbfddef1100082 0x20beff77bc440020 0xfbfffffff81000c0 0xfefffffffe040030

def z812 : W := mkw 0x210ca2210e26cb31 0x084328884389b2cc 0x8401a000062ecb31 0x21006800018bb2cc

def z813 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe47f8c7f10fcf 0xde7f91fe31fc43f3

def z814 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xd3fffefff8000000 0xb4ffffbffe000000

def z815 : W := mkw 0x90b60fb85f705fd6 0x642d83ee17dc17f5 0x97fc7ee0ffc1f03c 0x25ff1fb83ff07c0f

def z816 : W := mkw 0x2108a04320068021 0x08422810c801a008 0xdb1da6e7380e0000 0xf6c769b9ce038000

def z817 : W := mkw 0x610ca2632e66cf39 0x58432898cb99b3ce 0xdf1da6e73e2ecf3d 0xf7c769b9cf8bb3cf

def z818 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e0ec030 0xf7c769b9cf83b00c

def z819 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xd4fff80007fff000 0x353ffe0001fffc00

def z820 : W := mkw 0x02b20ddef0000000 0x00ac8377bc000000 0x431e07fff8000000 0xd0c781fffe000000

def z821 : W := mkw 0x00dbf84a70000000 0x0036fe129c000000 0xfbfffffff8000000 0xfefffffffe000000

def z822 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x34e1c707c7cf0c3f 0x0d3871c1f1f3c30f

def z823 : W := mkw 0x1008a84a70001044 0x04022a129c000411 0xfb1ffffff81134ce 0xfec7fffffe044d33

def z824 : W := mkw 0x50200f0dda425d7c 0x540803c37690975f 0x02000707f8000c3c 0x408001c1fe00030f

def z825 : W := mkw 0x0069ed4ef0000000 0x001a7b53bc000000 0xfbfffffff8000000 0xfefffffffe000000

def z826 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xbcfdf80007cff003 0x2f3f7e0001f3fc00

def z827 : W := mkw 0x00d7500005bda003 0x8035d400016f6800 0xece2780007fff003 0x3b389e0001fffc00

def z828 : W := mkw 0x310402210e26db75 0x0c4100884389b6dd 0x04000000063efbf1 0x01000000018fbefc

def z829 : W := mkw 0x129eb8da7d34f157 0x84a7ae369f4d3c55 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z830 : W := mkw 0x02fbfddef1992002 0x80beff77bc664800 0xfbfffffff9c00000 0xfefffffffe700000

def z831 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c607c7cf003f 0x2fb87181f1f3c00f

def z832 : W := mkw 0xc0d740b585bb02aa 0x3035d02d616ec0aa 0xc71fc0ffc03f03fc 0xb1c7f03ff00fc0ff

def z833 : W := mkw 0x80dff09005bda083 0xa037fc24016f6820 0xfcfff81807fff0c3 0x3f3ffe0601fffc30

def z834 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x64fe780007fff003 0x193f9e0001fffc00

def z835 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfdfffee007fff003 0xff7fffb801fffc00

def z836 : W := mkw 0x210402210f36cb33 0x0841008843cdb2cc 0x0400000007fecb33 0x0100000001ffb2cc

def z837 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xdf1da6e73e2ecffd 0xf7c769b9cf8bb3ff

def z838 : W := mkw 0x0049f042208da001 0x80127c1088236800 0xdf1dfee7380ff000 0xf7c77fb9ce03fc00

def z839 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x551da6e73e2ecb31 0x954769b9cf8bb2cc

def z840 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0xfb1ffffff8000000 0xfec7fffffe000000

def z841 : W := mkw 0x2108a0432806c131 0x08422810ca01b04c 0x971da6e7380ec030 0x25c769b9ce03b00c

def z842 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0x51fda6e738000000 0x947f69b9ce000000

def z843 : W := mkw 0x00dbf00000890000 0x0036fc0000224000 0xfcfff80007fff003 0x3f3ffe0001fffc00

def z844 : W := mkw 0x004df00004ada001 0x80137c00012b6800 0xfcfdf80007eff003 0x3f3f7e0001fbfc00

def z845 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fa6e73e3ecb33 0xffc7e9b9cf8fb2cc

def z846 : W := mkw 0x0049f000008da001 0x80127c0000236800 0xfce3f80007fff003 0x3f38fe0001fffc00

def z847 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xfbfffee738000000 0xfeffffb9ce000000

def z848 : W := mkw 0x80b607b107720ea2 0x602d81ec41dc83a8 0x7dfe07f807fe0ff3 0xdf7f81fe01ff83fc

def z849 : W := mkw 0x610402210eafcb39 0x1841008843abf2ce 0x04000000062fcb3d 0x01000000018bf2cf

def z850 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x131d86e73e0e0000 0xc4c761b9cf838000

def z851 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfbfffffff80004cc 0xfefffffffe000133

def z852 : W := mkw 0x80b605b005700682 0x602d816c015c01a0 0x41fe00f801f003c0 0x907f803e007c00f0

def z853 : W := mkw 0x0269eddef0000000 0x009a7b77bc000000 0xfbfde7fff8000000 0xfeff79fffe000000

def z854 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1fbee73e3efb31 0xf7c7efb9cf8fbecc

def z855 : W := mkw 0x02dbf84ef0000000 0x00b6fe13bc000000 0xfbfffee7f8000000 0xfeffffb9fe000000

def z856 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x7dfe07f807f10fff 0xdf7f81fe01fc43ff

def z857 : W := mkw 0x80baa5d221500482 0x602ea97488540120 0xfbffa7ff39d004c2 0xfeffe9ffce740130

def z858 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x34ffd80007fff003 0x0d3ff60001fffc00

def z859 : W := mkw 0x21d752210fbfeb33 0x8875d48843effacc 0x24e2580007fffb33 0x0938960001fffecc

def z860 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xdbfdfee7f8000000 0xf6ff7fb9fe000000

def z861 : W := mkw 0x82fbfddef0400480 0x60beff77bc100120 0xfbfffffff80004c0 0xfefffffffe000130

def z862 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x70fff80007fff002 0x1c3ffe0001fffc00

def z863 : W := mkw 0x80b605b005700682 0x602d816c015c01a0 0x69fe01f801f00fc3 0xda7f807e007c03f0

def z864 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x12e18607c7ce003c 0x04b86181f1f3800f

def z865 : W := mkw 0x02f35d9cd0890000 0x00bcd76734224000 0x20e25918c1c10002 0x0838964630704000

def z866 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbae1c707c7ce0c3c 0x6eb871c1f1f3830f

def z867 : W := mkw 0x02dff0d225bda003 0x80b7fc34896f6800 0xfdfff8e007fff003 0x3f7ffe3801fffc00

def z868 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xa6e1c107c7cf0c3f 0x29b87041f1f3c30f

def z869 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x04000000063ecff3 0x01000000018fb3fc

def z870 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xff1ffee73e3fffff 0xffc7ffb9cf8fffff

def z871 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x61fe01f807f00fc3 0x987f807e01fc03f0

def z872 : W := mkw 0x310402210e26db75 0x0c4100884389b6dd 0x04000000062ffb3d 0x01000000018bfecf

def z873 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x5b1d86e73e2e0b31 0xd6c761b9cf8b82cc

def z874 : W := mkw 0x000ca26326220a20 0x00032898c9888288 0xdf1da6e73e2e0b31 0xf7c769b9cf8b82cc

def z875 : W := mkw 0x0049e046a0000000 0x00127811a8000000 0xdb1de6e7f8000000 0xf6c779b9fe000000

def z876 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee3df07c7df3c3f 0x6fb8f7c1f1f7cf0f

def z877 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x54ffb80007fff003 0x153fee0001fffc00

def z878 : W := mkw 0x5249f84ff88b517c 0x14927e13fe22d45f 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z879 : W := mkw 0x42fbfddef0890008 0x10beff77bc224002 0xfbfffffff801000c 0xfefffffffe004003

def z880 : W := mkw 0x23f75fbdde26cb31 0x08fdd7ef7789b2cc 0x24e25918c62ecb31 0x09389646318bb2cc

def z881 : W := mkw 0x210ca0632c26c331 0x08432818cb09b0cc 0xdf1da6e7382ec330 0xf7c769b9ce0bb0cc

def z882 : W := mkw 0x00d7500005bda003 0x8035d400016f6800 0xbce3d80007fff003 0x2f38f60001fffc00

def z883 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fffe7fe3fff3f 0xffc7fff9ff8fffcf

def z884 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff918c7ffffff 0xffbffe4631ffffff

def z885 : W := mkw 0x50614f0ddacb5d7c 0x541853c376b2d75f 0x50e3be1f3ffef3c0 0x9438ef87cfffbcf0

def z886 : W := mkw 0x029ab0d220000000 0x00a6ac3488000000 0xdb1da6e738000000 0xf6c769b9ce000000

def z887 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x16e18707c7cf0c3f 0x45b861c1f1f3c30f

def z888 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x131d86e73e0e0030 0x04c761b9cf83800c

def z889 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c707c7ff0fff 0x6fb871c1f1ffc3ff

def z890 : W := mkw 0x2108a2432a06c931 0x08422890ca81b24c 0xdf1da6e73e0ec831 0xf7c769b9cf83b20c

def z891 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdb1da6e73e0e0b30 0xf6c769b9cf8382cc

def z892 : W := mkw 0x0008a04220000000 0x0002281088000000 0xfb1ffee738000000 0xfec7ffb9ce000000

def z893 : W := mkw 0x029ab8da70000000 0x00a6ae369c000000 0x511fbeff38000000 0x9447efbfce000000

def z894 : W := mkw 0x210ca2632f36cb33 0x08432898cbcdb2cc 0xdf1da6e73ffecb33 0xf7c769b9cfffb2cc

def z895 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e3ecff3 0xf7c769b9cf8fb3fc

def z896 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0xae004100c62fcf3f 0x6b801040318bf3cf

def z897 : W := mkw 0x80b607b107720ea2 0x602d81ec41dc83a8 0x7bfe07ff07f00ff3 0xdeff81ffc1fc03fc

def z898 : W := mkw 0x610402210fffef3b 0xd841008843fffbce 0x0400000007ffff3f 0x0100000001ffffcf

def z899 : W := mkw 0x214542210eafcb31 0x0851508843abf2cc 0xbce1c00007efcb33 0x2f38700001fbf2cc

def z900 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x51fe06f807f00fc3 0x947f81be01fc03f0

def z901 : W := mkw 0x80b207b003500e82 0x602c81ec00d403a0 0x79fe07f801d00fc2 0xde7f81fe007403f0

def z902 : W := mkw 0x4020070582420c28 0x500801c16090830a 0xbee18707c7ce0c3f 0x6fb861c1f1f3830f

def z903 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff80007fffc3f 0x3f3ffe0001ffff0f

def z904 : W := mkw 0x00dbf04221992002 0x8036fc1088664800 0xfbfffee739d13002 0xfeffffb9ce744c00

def z905 : W := mkw 0x02fbfddef19da003 0x80beff77bc676800 0xfffffffff9dff002 0xfffffffffe77fc00

def z906 : W := mkw 0x0061450480890000 0x0018514120224000 0xbee1c707c7cf0c3f 0x6fb871c1f1f3c30f

def z907 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff801f000 0xfffffffffe007c00

def z908 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x9c018000062ecb31 0x27006000018bb2cc

def z909 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfffe7ff8c7f1ffff 0xffff9ffe31fc7fff

def z910 : W := mkw 0x02dbf8def0000000 0x00b6fe37bc000000 0xdb1ffefff8000000 0xf6c7ffbffe000000

def z911 : W := mkw 0x00dbf04220000000 0x0036fc1088000000 0xdbfda6e738000000 0xf6ff69b9ce000000

def z912 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xff1fa7ff3e3fffff 0xffc7e9ffcf8fffff

def z913 : W := mkw 0x0269fd4ef0000000 0x009a7f53bc000000 0xfbfdffe7f8000000 0xfeff7ff9fe000000

def z914 : W := mkw 0x02babdda70000000 0x00aeaf769c000000 0xfbffbfff38000000 0xfeffefffce000000

def z915 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x6c020118063ecff3 0xdb008046018fb3fc

def z916 : W := mkw 0x0069e546a0000000 0x001a7951a8000000 0xdbfda6e738000000 0xf6ff69b9ce000000

def z917 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x10fdb80007cef000 0x043f6e0001f3bc00

def z918 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8300003 0xfefffffffe0c0000

def z919 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x00000000062ec300 0x00000000018bb0c0

def z920 : W := mkw 0x0008a04220000000 0x0002281088000000 0xfb1fa7ff38000000 0xfec7e9ffce000000

def z921 : W := mkw 0x80b207b002400e80 0x602c81ec009003a0 0x79fe07f807c00fc3 0xde7f81fe01f003f0

def z922 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff80007fffb03 0xff3ffe0001fffec0

def z923 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe5ff807f13fc3 0xde7f97fe01fc4ff0

def z924 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffffe0e0001 0xffffffffff838000

def z925 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x61fe07f801f00fc2 0xd87f81fe007c03f0

def z926 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xffffffffffcf0c3f 0xfffffffffff3c30f

def z927 : W := mkw 0x82fbfddef1d92482 0xe0beff77bc764920 0xfbfffffff9d134c2 0xfefffffffe744d30

def z928 : W := mkw 0x2108a2632a024b30 0x08422898ca8092cc 0xdf1da6e73e0e0b31 0xf7c769b9cf8382cc

def z929 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefffe0707fff003 0x7fbfff81c1fffc00

def z930 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8200b01 0xfefffffffe0802c0

def z931 : W := mkw 0x02f35d9cd0892000 0x80bcd76734224800 0x20e25918c0013000 0x0838964630004c00

def z932 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0xdb1fbffff8000000 0xf6c7effffe000000

def z933 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfffffffff831f4cf 0xfffffffffe0c7d33

def z934 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbffffffffc00003 0xfefffffffff00000

def z935 : W := mkw 0x00dbf000008da001 0x8036fc0000236800 0xfcfff80007cff003 0x3f3ffe0001f3fc00

def z936 : W := mkw 0x12f35d9cd1993046 0x84bcd76734664c11 0x20e25918c1d134ce 0x0838964630744d33

def z937 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe07f807f003c0 0xde7f81fe01fc00f0

def z938 : W := mkw 0xc2f35d9cd1d9048a 0x70bcd76734764122 0x20e25918c1d104ce 0x0838964630744133

def z939 : W := mkw 0x92fbfddef15014c6 0x64beff77bc540531 0xfbfffffff9d134ce 0xfefffffffe744d33

def z940 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x111d86e73e0e0300 0x844761b9cf8380c0

def z941 : W := mkw 0x42fbfddef1d9240a 0xd0beff77bc764902 0xfbfffffff9d1340e 0xfefffffffe744d03

def z942 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xf8fff80007fef000 0x3e3ffe0001ffbc00

def z943 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x7dfe07f807f1ffc3 0xdf7f81fe01fc7ff0

def z944 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0xeb1e7ffff8000000 0xfac79ffffe000000

def z945 : W := mkw 0x00dff04225bda003 0x8037fc10896f6800 0xfdfffee707fff003 0x3f7fffb9c1fffc00

def z946 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8000c3c 0xfefffffffe00030f

def z947 : W := mkw 0x80b605b005700682 0x602d816c015c01a0 0x79fe01f807f007c3 0x9e7f807e01fc01f0

def z948 : W := mkw 0x210402210e66cf31 0x484100884399b3cc 0x0400000007eecf33 0x0100000001fbb3cc

def z949 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xc31ffffff8000000 0xf0c7fffffe000000

def z950 : W := mkw 0x52f35d9cd0c9144c 0x54bcd76734324513 0x20e25918c1d134ce 0x0838964630744d33

def z951 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xdf1da6e73e3efbf1 0xf7c769b9cf8fbefc

def z952 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x00000000060e0b30 0x00000000018382cc

def z953 : W := mkw 0x0041400000890000 0x0010500000224000 0xbce1f80007cff003 0x2f387e0001f3fc00

def z954 : W := mkw 0x0008a24322020820 0x00022890c8808208 0xdb1da6e73e0e0000 0xf6c769b9cf838000

def z955 : W := mkw 0x00fbf546a0000000 0x003efd51a8000000 0xfbffffe7f8000000 0xfefffff9fe000000

def z956 : W := mkw 0x2108a0432806c131 0x08422810ca01b04c 0xdf1da6e7382ecb31 0xf7c769b9ce0bb2cc

def z957 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee3c71fc7df0cff 0x6fb8f1c7f1f7c33f

def z958 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xdcffb80007fef001 0x373fee0001ffbc00

def z959 : W := mkw 0x210402210e224b30 0x08410088438892cc 0x0000000006200b31 0x00000000018802cc

def z960 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfffffffff8113cff 0xfffffffffe044f3f

def z961 : W := mkw 0xc061479582cb0ca8 0x701851e560b2c32a 0xbee1c71fc7cf0cff 0x6fb871c7f1f3c33f

def z962 : W := mkw 0x0208a8da70000000 0x00822a369c000000 0xdb1da6ff38000000 0xf6c769bfce000000

def z963 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfbfffffff8313fcf 0xfefffffffe0c4ff3

def z964 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0x031c07fff8000000 0xc0c701fffe000000

def z965 : W := mkw 0x000ca24326268821 0x00032890c989a208 0xdf1da6e73e2ec831 0xf7c769b9cf8bb20c

def z966 : W := mkw 0x000ca26226248a01 0x0003289889892280 0xdf1da6e73e2ecb01 0xf7c769b9cf8bb2c0

def z967 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff81807fff3c3 0xbf3ffe0601fffcf0

def z968 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x96e1c707c7cf0c3c 0x65b871c1f1f3c30f

def z969 : W := mkw 0x02fbfddef08da001 0x80beff77bc236800 0xfbfffffff80e0000 0xfefffffffe038000

def z970 : W := mkw 0x40414205828b0828 0x1010508160a2c20a 0xbee1c607c7cf083f 0x6fb87181f1f3c20f

def z971 : W := mkw 0xa10402210f36cbb3 0x2841008843cdb2ec 0x04000000063ecbf1 0x01000000018fb2fc

def z972 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3ff1fc7ffffff 0xffb8ffc7f1ffffff

def z973 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff80007cff000 0x3f3ffe0001f3fc00

def z974 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff8000831 0xfffffffffe00020c

def z975 : W := mkw 0x0249f84ef0000000 0x00927e13bc000000 0xfb1ffffff8000000 0xfec7fffffe000000

def z976 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xff1de7e7fe3fffff 0xffc779f9ff8fffff

def z977 : W := mkw 0x210ca2632f36eb33 0x88432898cbcdbacc 0xdf1da6e73e3efb31 0xf7c769b9cf8fbecc

def z978 : W := mkw 0x0269fddef0000000 0x009a7f77bc000000 0xdb1dfffff8000000 0xf6c77ffffe000000

def z979 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff90007fffc03 0x7f3ffe4001ffff00

def z980 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x4c000000062ecb31 0xd3000000018bb2cc

def z981 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x171d86e73e2ecb31 0xc5c761b9cf8bb2cc

def z982 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfbfe27f83ff00fc3 0xfeff89fe0ffc03f0

def z983 : W := mkw 0x0008a2432a024930 0x00022890ca80924c 0xdf1da6e73e2ecb31 0xf7c769b9cf8bb2cc

def z984 : W := mkw 0x02200ddef0000000 0x00880377bc000000 0x5b1c07fff8000000 0xd6c701fffe000000

def z985 : W := mkw 0x210402210eafcb31 0x0841008843abf2cc 0x0400000007efcb33 0x0100000001fbf2cc

def z986 : W := mkw 0x210ca0622c24c311 0x084328188b0930c4 0xdf1da6e73e2ec301 0xf7c769b9cf8bb0c0

def z987 : W := mkw 0xc0b607b587720eaa 0x702d81ed61dc83aa 0xffff87ffc7fe0fff 0xffffe1fff1ff83ff

def z988 : W := mkw 0x82fbfddef1500482 0x60beff77bc540120 0xfbfffffff9f00fc3 0xfefffffffe7c03f0

def z989 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xf9fe7ff807f00fc3 0xfe7f9ffe01fc03f0

def z990 : W := mkw 0x02dff046a5bda003 0x80b7fc11a96f6800 0xfcfff80707fff003 0x3f3ffe01c1fffc00

def z991 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xfffffffffffff003 0xfffffffffffffc00

def z992 : W := mkw 0x1000080858005154 0x0400020216001455 0x64027918f831ffff 0x99009e463e0c7fff

def z993 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x9ee1c607c7cf083d 0x67b87181f1f3c20f

def z994 : W := mkw 0x80b607b007748e83 0x602d81ec01dd23a0 0x7dfe07f807fecfc3 0xdf7f81fe01ffb3f0

def z995 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff900c7fff40f 0x3f3ffe4031fffd03

def z996 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x7bff87fff8000000 0xdeffe1fffe000000

def z997 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x971da6e73e0ecb30 0xe5c769b9cf83b2cc

def z998 : W := mkw 0x00fbf5d220000000 0x003efd7488000000 0xfbffffff38000000 0xfeffffffce000000

def z999 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0x411e3eff38000000 0x90478fbfce000000

def z1000 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfbff87ff07f00fc3 0xfeffe1ffc1fc03f0

def z1001 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3c707c7ff0c3f 0x7fb8f1c1f1ffc30f

def z1002 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0xcc002000062ecb31 0x33000800018bb2cc

def z1003 : W := mkw 0x02fbfddef0890000 0x00beff77bc224000 0xfbffffffffce0000 0xfefffffffff38000

def z1004 : W := mkw 0x80dff0b005bda283 0xa037fc2c016f68a0 0xfdfff8e007fff003 0x3f7ffe3801fffc00

def z1005 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfdfe27f807f0cfc3 0xff7f89fe01fc33f0

def z1006 : W := mkw 0x0008a04320020020 0x00022810c8008008 0xdf1da6e7380e0030 0xf7c769b9ce03800c

def z1007 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfdfe47f807f10fc3 0xff7f91fe01fc43f0

def z1008 : W := mkw 0x802407b006600e80 0x600901ec019803a0 0x79fc07f807e00fc3 0xde7f01fe01f803f0

def z1009 : W := mkw 0x12fbfddef0001044 0x04beff77bc000411 0xfbfffffff801300c 0xfefffffffe004c03

def z1010 : W := mkw 0x809602b007300a82 0x202580ac01cc02a0 0x79fe06f807f00bc3 0xde7f81be01fc02f0

def z1011 : W := mkw 0x00dff02005bda203 0x8037fc08016f6880 0xfdfff8e007fff303 0xbf7ffe3801fffcc0

def z1012 : W := mkw 0x2108a2632a06cb31 0x08422898ca81b2cc 0xdf1da6e7380ecb30 0xf7c769b9ce03b2cc

def z1013 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x53ffbffff8000000 0xd4ffeffffe000000

def z1014 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff831ffc3 0xfffffffffe0c7ff0

def z1015 : W := mkw 0xa10402210e66cfb1 0x684100884399b3ec 0x04000000062ecff1 0x01000000018bb3fc

def z1016 : W := mkw 0x80b617b007702e82 0xe02d85ec01dc0ba0 0x79fe1ff807f03fc3 0xde7f87fe01fc0ff0

def z1017 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xb4fff80007dff002 0x2d3ffe0001f7fc00

def z1018 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff81004c2 0xfefffffffe040130

def z1019 : W := mkw 0x0008a04220000000 0x0002281088000000 0xfb1de7e7f8000000 0xfec779f9fe000000

def z1020 : W := mkw 0x1000080858005154 0x0400020216001455 0xfee27918fff1ffff 0xffb89e463ffc7fff

def z1021 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff91807fff4c3 0x3f3ffe4601fffd30

def z1022 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3ff07c7cf0c3f 0x7fb8ffc1f1f3c30f

def z1023 : W := mkw 0x00dff04225bda003 0x8037fc10896f6800 0xfefff8073ffff003 0x3fbffe01cffffc00

def z1024 : W := mkw 0x1000080858005154 0x0400020216001455 0xff1e7ff8f831ffff 0xffc79ffe3e0c7fff

def z1025 : W := mkw 0x009eb00005bda003 0x8027ac00016f6800 0x7cfe380007fff003 0x1f3f8e0001fffc00

def z1026 : W := mkw 0x02dbf8da70000000 0x00b6fe369c000000 0xfbfffeff38000000 0xfeffffbfce000000

def z1027 : W := mkw 0x0208b84a70000000 0x00822e129c000000 0xdb1dbee738000000 0xf6c76fb9ce000000

def z1028 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8000fc0 0xfefffffffe0003f0

def z1029 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x61fe00f801f003c2 0x987f803e007c00f0

def z1030 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x04000000063ffb33 0x01000000018ffecc

def z1031 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1fa6ff3e3ecbf1 0xf7c7e9bfcf8fb2fc

def z1032 : W := mkw 0x80dff02005bda283 0xa037fc08016f68a0 0xfcfff80007fff3c3 0x3f3ffe0001fffcf0

def z1033 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x8e000000062ecb31 0x63800000018bb2cc

def z1034 : W := mkw 0xc061472582cb0ea8 0x701851c960b2c3aa 0xbee1c707c7cf0fff 0x6fb871c1f1f3c3ff

def z1035 : W := mkw 0x7149e84ff88fd17d 0x1c527a13fe23f45f 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z1036 : W := mkw 0xa1b607b107768ea3 0x686d81ec41dda3a8 0x79fe07f807fe0fc3 0xde7f81fe01ff83f0

def z1037 : W := mkw 0x610402210e66cf39 0x584100884399b3ce 0x04000000062ecf3d 0x01000000018bb3cf

def z1038 : W := mkw 0x42f35d9cd0890008 0x10bcd76734224002 0x20e25918c001000c 0x0838964630004003

def z1039 : W := mkw 0xc0b607b487700e8a 0x702d81ed21dc03a2 0x79fe07f8c7f00fcf 0xde7f81fe31fc03f3

def z1040 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0xfbffa7ff38000000 0xfeffe9ffce000000

def z1041 : W := mkw 0x4061479582cb0c28 0x501851e560b2c30a 0xbfe1c7ffc7cf0c3f 0xeff871fff1f3c30f

def z1042 : W := mkw 0x0008a04220000000 0x0002281088000000 0x131d86e738000000 0xc4c761b9ce000000

def z1043 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1dfee73e2ffb31 0xf7c77fb9cf8bfecc

def z1044 : W := mkw 0x1000080858005154 0x0400020216001455 0xa6027918f831ffff 0x29809e463e0c7fff

def z1045 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe3ff807f0ffc3 0xde7f8ffe01fc3ff0

def z1046 : W := mkw 0x02f35ddef0000000 0x00bcd777bc000000 0x7bfe5ffff8000000 0xdeff97fffe000000

def z1047 : W := mkw 0x319eb86a7d34f357 0x8c67ae1a9f4d3cd5 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z1048 : W := mkw 0x71200f6ffa425f7c 0x5c4803dbfe9097df 0x030007fff8000ffc 0xc0c001fffe0003ff

def z1049 : W := mkw 0x4020070582420c28 0x500801c16090830a 0xee027f07c031fc3f 0x7b809fc1f00c7f0f

def z1050 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff831fc3f 0xfffffffffe0c7f0f

def z1051 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xdbfda7fff8000000 0xf6ff69fffe000000

def z1052 : W := mkw 0x616547258eefcf39 0x585951c963bbf3ce 0x24e04100c7efcf3f 0x0938104031fbf3cf

def z1053 : W := mkw 0x4061450580cb0428 0x501851416032c10a 0xbee1c107c7cf043f 0x2fb87041f1f3c10f

def z1054 : W := mkw 0x0008a04220000000 0x0002281088000000 0xff1ffee73831f003 0xffc7ffb9ce0c7c00

def z1055 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c71fc7cf0fff 0xefb871c7f1f3c3ff

def z1056 : W := mkw 0x0028a5d220000000 0x000a297488000000 0xdb1da7ff38000000 0xf6c769ffce000000

def z1057 : W := mkw 0x000402210e224b30 0x00010088438892cc 0xdf1da6e73e2ecb31 0xf7c769b9cf8bb2cc

def z1058 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdb1da6e73e2ec300 0xf6c769b9cf8bb0c0

def z1059 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xa4e3f80007fff003 0x2938fe0001fffc00

def z1060 : W := mkw 0x0028a54220000000 0x000a295088000000 0xfbfda7e738000000 0xfeff69f9ce000000

def z1061 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fe7fffe3fcfff 0xffc7f9ffff8ff3ff

def z1062 : W := mkw 0x0008a04220000000 0x0002281088000000 0xfb1fa7ff38300fc3 0xfec7e9ffce0c03f0

def z1063 : W := mkw 0x0008a84a70000000 0x00022a129c000000 0xdb1fbeff38000000 0xf6c7efbfce000000

def z1064 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xb3fffffff8000000 0x2cfffffffe000000

def z1065 : W := mkw 0x02f34ddef0000000 0x00bcd377bc000000 0xfbffc7fff8000000 0xfefff1fffe000000

def z1066 : W := mkw 0x0024072006600e00 0x400901c801980380 0x79fe07f807f00fc3 0xde7f81fe01fc03f0

def z1067 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x51fe07f807f00fc0 0xd47f81fe01fc03f0

def z1068 : W := mkw 0x310402210e26db75 0x0c4100884389b6dd 0x04000000062ecffd 0x01000000018bb3ff

def z1069 : W := mkw 0x1000080858005154 0x0400020216001455 0xfe03f918fe3fffff 0xff80fe463f8fffff

def z1070 : W := mkw 0x210402210f36eb33 0x8841008843cdbacc 0x04000000063efb31 0x01000000018fbecc

def z1071 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e2fcf3f 0xf7c769b9cf8bf3cf

def z1072 : W := mkw 0x02f35d9cd1992002 0x80bcd76734664800 0x20e25918c1c00000 0x0838964630700000

def z1073 : W := mkw 0x42fbfddef0400408 0x50beff77bc100102 0xfbfffffff800040c 0xfefffffffe000103

def z1074 : W := mkw 0x02fbfddef1992002 0x80beff77bc664800 0xffffffffffdf3003 0xfffffffffff7cc00

def z1075 : W := mkw 0x1000080858005154 0x0400020216001455 0x62027918f831fffe 0xd8809e463e0c7fff

def z1076 : W := mkw 0xa10402210fffefb3 0xe841008843fffbec 0x0400000007fffff3 0x0100000001fffffc

def z1077 : W := mkw 0x0008a04220000000 0x0002281088000000 0xdf1da6e738000831 0xf7c769b9ce00020c

def z1078 : W := mkw 0x0228addef0000000 0x008a2b77bc000000 0xfb1ffffff8000000 0xfec7fffffe000000

def z1079 : W := mkw 0x4061472582cb0e28 0x501851c960b2c38a 0xbfe1c7e7c7cf0f3f 0xeff871f9f1f3c3cf

def z1080 : W := mkw 0x02fbfddef08da001 0x80beff77bc236800 0xfffffffff83ff003 0xfffffffffe0ffc00

def z1081 : W := mkw 0x0228addef0000000 0x008a2b77bc000000 0x431c27fff8000000 0xd0c709fffe000000

def z1082 : W := mkw 0x009aa0d220000000 0x0026a83488000000 0xdb1fa6ff38000000 0xf6c7e9bfce000000

def z1083 : W := mkw 0x02b20ddef0000000 0x00ac8377bc000000 0xfbfe7ffff8000000 0xfeff9ffffe000000

def z1084 : W := mkw 0x009aa04220000000 0x0026a81088000000 0xfbffa6e738000000 0xfeffe9b9ce000000

def z1085 : W := mkw 0x0096000005bda003 0x80258000016f6800 0xfcfe780007fff003 0x3f3f9e0001fffc00

def z1086 : W := mkw 0xb10402210f76dff7 0x6c41008843ddb7fd 0x0400000007ffffff 0x0100000001ffffff

def z1087 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff801003c 0xfffffffffe00400f

def z1088 : W := mkw 0x0008a04220000000 0x0002281088000000 0xdf1da6e73820c001 0xf7c769b9ce083000

def z1089 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x79ffbfff38000000 0xde7fefffce000000

def z1090 : W := mkw 0xa10402210f724fb2 0x6841008843dc93ec 0x0000000007f00ff3 0x0000000001fc03fc

def z1091 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1da7e73e2ecf33 0xffc769f9cf8bb3cc

def z1092 : W := mkw 0x42f35d9cd1d9240a 0xd0bcd76734764902 0x20e25918c1d1340e 0x0838964630744d03

def z1093 : W := mkw 0x210402210e26cb31 0x084100884389b2cc 0x04000000062fcf3f 0x01000000018bf3cf

def z1094 : W := mkw 0x00dff09005bda003 0x8037fc24016f6800 0xfdfff8f807fff003 0xbf7ffe3e01fffc00

def z1095 : W := mkw 0x82fbfddef1500482 0x60beff77bc540120 0xfbfffffff9c00000 0xfefffffffe700000

def z1096 : W := mkw 0x42f35d9cd0c90408 0x50bcd76734324102 0x20e25918c1c00000 0x0838964630700000

def z1097 : W := mkw 0x000ca04224248001 0x0003281089092000 0xdb1da6e73e0e0000 0xf6c769b9cf838000

def z1098 : W := mkw 0xc0b607b587720eaa 0x702d81ed61dc83aa 0xfffe47ffc7f10fff 0xffff91fff1fc43ff

def z1099 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xd71da6e73e2ec330 0xb5c769b9cf8bb0cc

def z1100 : W := mkw 0x0228addef0000000 0x008a2b77bc000000 0x131d87fff8000000 0xc4c761fffe000000

def z1101 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xdcfdf80007eff001 0x373f7e0001fbfc00

def z1102 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xbbfdffe7f8000000 0x6eff7ff9fe000000

def z1103 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x32e1c707c7cf0c3e 0x4cb871c1f1f3c30f

def z1104 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x31fe07f807d00fc2 0xcc7f81fe01f403f0

def z1105 : W := mkw 0x02fbfddef004a001 0x80beff77bc012800 0xfbfffffff800f000 0xfefffffffe003c00

def z1106 : W := mkw 0x02b20ddef0000000 0x00ac8377bc000000 0x13fc07fff8000000 0xc4ff01fffe000000

def z1107 : W := mkw 0x1249f84ef88df155 0x84927e13be237c55 0x8601f807f80ff03c 0x21807e01fe03fc0f

def z1108 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xfffda6e73feecb33 0xffff69b9cffbb2cc

def z1109 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xc71da6e7382ecb30 0xf1c769b9ce0bb2cc

def z1110 : W := mkw 0xa10ca2632f36cbb3 0x28432898cbcdb2ec 0xdf1da6e73e3ecbf1 0xf7c769b9cf8fb2fc

def z1111 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee1c707c7ef0f3f 0xffb871c1f1fbc3cf

def z1112 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x531da6e73e2ecb30 0xd4c769b9cf8bb2cc

def z1113 : W := mkw 0x1041480858895154 0x0410520216225455 0xbee1c118ffcf0fff 0xefb870463ff3c3ff

def z1114 : W := mkw 0x02fbfddef0048001 0x00beff77bc012000 0xfffffffff80ec000 0xfffffffffe03b000

def z1115 : W := mkw 0x0020070102420c20 0x400801c040908308 0xbee1c707c7cf0c3f 0x6fb871c1f1f3c30f

def z1116 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x9f1da6e73e0ec831 0x67c769b9cf83b20c

def z1117 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff80007ffffc3 0x3f3ffe0001fffff0

def z1118 : W := mkw 0x02fbfddef0400400 0x40beff77bc100100 0xfbfffffff9c00402 0xfefffffffe700100

def z1119 : W := mkw 0x0008a04220000000 0x0002281088000000 0xff1de7e7f8010c3f 0xffc779f9fe00430f

def z1120 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x96e1c607c7cf0c3f 0x25b87181f1f3c30f

def z1121 : W := mkw 0x310ca2632e26db75 0x0c432898cb89b6dd 0xdf1da6e73e2ffb3d 0xf7c769b9cf8bfecf

def z1122 : W := mkw 0x80b607b107720ea2 0x602d81ec41dc83a8 0xffffc7ffc7ff0fff 0xfffff1fff1ffc3ff

def z1123 : W := mkw 0x0049f000008da001 0x80127c0000236800 0x94e1f80007cff000 0x25387e0001f3fc00

def z1124 : W := mkw 0x02fbf5d6a0000000 0x00befd75a8000000 0x93fda6e738000000 0x24ff69b9ce000000

def z1125 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xdbffbeff38000000 0xf6ffefbfce000000

def z1126 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x78ffb80007fef003 0x1e3fee0001ffbc00

def z1127 : W := mkw 0xc06147b582cb0ea8 0x701851ed60b2c3aa 0xffe3c7ffc7ff0fff 0xfff8f1fff1ffc3ff

def z1128 : W := mkw 0x00d7500005bda003 0x8035d400016f6800 0x7cfe580007fff003 0x1f3f960001fffc00

def z1129 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0x9ee18707c7ce0c3d 0x67b861c1f1f3830f

def z1130 : W := mkw 0x52200fdffa425d7c 0x548803f7fe90975f 0x030007fff8000ffc 0xc0c001fffe0003ff

def z1131 : W := mkw 0x00d7400005b90002 0x0035d000016e4000 0xfcfff80007fff003 0x3f3ffe0001fffc00

def z1132 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff830f000 0xfefffffffe0c3c00

def z1133 : W := mkw 0x0045400005bda003 0x80115000016f6800 0xfce3f80007fff003 0x3f38fe0001fffc00

def z1134 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x71fe07f807f007c2 0x9c7f81fe01fc01f0

def z1135 : W := mkw 0x00baadda70000000 0x002eab769c000000 0xfbfffffff8000000 0xfefffffffe000000

def z1136 : W := mkw 0x21dff06225bda203 0x8877fc18896f6880 0xfdfff8e007fff003 0x3f7ffe3801fffc00

def z1137 : W := mkw 0xc06147b582cb0ea8 0x701851ed60b2c3aa 0xbfe1c7e7c7cf0c3f 0x6ff871f9f1f3c30f

def z1138 : W := mkw 0xc2fbfddef1d9048a 0x70beff77bc764122 0xfbfffffff9d104ce 0xfefffffffe744133

def z1139 : W := mkw 0x000ca0422c24c111 0x000328108b093044 0xdf1da6e73e2ecb31 0xf7c769b9cf8bb2cc

def z1140 : W := mkw 0x02babddef0000000 0x00aeaf77bc000000 0x7bfe3ffff8000000 0xdeff8ffffe000000

def z1141 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0xdf1da6e73e0e0831 0xf7c769b9cf83820c

def z1142 : W := mkw 0x42fbfddef0c90408 0x50beff77bc324102 0xfffffffff9c10c3f 0xfffffffffe70430f

def z1143 : W := mkw 0x80b605b005300282 0x202d816c014c00a0 0x79fe07f807f003c3 0xde7f81fe01fc00f0

def z1144 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x931da6e73e0e0000 0x24c769b9cf838000

def z1145 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff820c001 0xfffffffffe083000

def z1146 : W := mkw 0xb1200ffb7a425ff4 0x6c4803fede9097fd 0x030007fff8000ffc 0xc0c001fffe0003ff

def z1147 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x11fc07f807f00fc3 0xc47f01fe01fc03f0

def z1148 : W := mkw 0x40414005808b0028 0x101050016022c00a 0x96e1c007c7cf003c 0x25b87001f1f3c00f

def z1149 : W := mkw 0x00f34d9cd0000000 0x003cd36734000000 0xfbfffffff8000000 0xfefffffffe000000

def z1150 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x63fe7ffff8000000 0xd8ff9ffffe000000

def z1151 : W := mkw 0x00b2079002400c00 0x402c81e400900300 0x79fe07f807f00fc3 0xde7f81fe01fc03f0

def z1152 : W := mkw 0x0008a04220000000 0x0002281088000000 0xdb1da6e738200b01 0xf6c769b9ce0802c0

def z1153 : W := mkw 0x310402210fbffb77 0x8c41008843effedd 0x0400000007ffffff 0x0100000001ffffff

def z1154 : W := mkw 0x0249f046a0000000 0x00927c11a8000000 0xdb1da6e738000000 0xf6c769b9ce000000

def z1155 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0x94fdf80007fff003 0x253f7e0001fffc00

def z1156 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff801040e 0xfefffffffe004103

def z1157 : W := mkw 0xa10ca2632e66cfb1 0x68432898cb99b3ec 0xdf1da6e73e2ecff1 0xf7c769b9cf8bb3fc

def z1158 : W := mkw 0x210402210fbfeb33 0x8841008843effacc 0x0400000007eecb31 0x0100000001fbb2cc

def z1159 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c707c7cf003c 0x6fb871c1f1f3c00f

def z1160 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da7ff3e2ecff1 0xf7c769ffcf8bb3fc

def z1161 : W := mkw 0x02baaddef0000000 0x00aeab77bc000000 0xfbffa7fff8000000 0xfeffe9fffe000000

def z1162 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xb6e1c707c7cf043e 0x2db871c1f1f3c10f

def z1163 : W := mkw 0x80dff0b005bda283 0xa037fc2c016f68a0 0xfdfff9f807ffffc3 0xff7ffe7e01fffff0

def z1164 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1de6e73e2fcb33 0xffc779b9cf8bf2cc

def z1165 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0x111da6e73e0ec000 0x044769b9cf83b000

def z1166 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8000c03 0xfefffffffe000300

def z1167 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x11fdbee738000000 0x047f6fb9ce000000

def z1168 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x33ffdffff8000000 0xccfff7fffe000000

def z1169 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xfee3c71fc7cf0c3f 0xffb8f1c7f1f3c30f

def z1170 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffffff8113002 0xfefffffffe044c00

def z1171 : W := mkw 0xb19ea8fa7d34d3d7 0x2c67aa3e9f4d34f5 0x411e38f83830f3c0 0x90478e3e0e0c3cf0

def z1172 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x51fe00f807f003c0 0x947f803e01fc00f0

def z1173 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfbfffee7f8000000 0x3effffb9fe000000

def z1174 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0xdf1da6e73e2ec001 0xf7c769b9cf8bb000

def z1175 : W := mkw 0x80b607b487700e82 0x602d81ed21dc03a0 0x7bfe07ffc7f00fc3 0xdeff81fff1fc03f0

def z1176 : W := mkw 0x0249f84ef0000000 0x00927e13bc000000 0x931dfee7f8000000 0x24c77fb9fe000000

def z1177 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e3ffb33 0xf7c769b9cf8ffecc

def z1178 : W := mkw 0x00dbf000019da003 0x8036fc0000676800 0xbce3f80007dff003 0x2f38fe0001f7fc00

def z1179 : W := mkw 0x0008a04220000000 0x0002281088000000 0x431c26e738000000 0xd0c709b9ce000000

def z1180 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfcfff91807fff003 0xff3ffe4601fffc00

def z1181 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff8010003 0xfffffffffe004000

def z1182 : W := mkw 0x009ab04220000000 0x0026ac1088000000 0xdb1fbee738000000 0xf6c7efb9ce000000

def z1183 : W := mkw 0x0028a546a0000000 0x000a2951a8000000 0xdb1da7e7f8000000 0xf6c769f9fe000000

def z1184 : W := mkw 0x210ca26326268a21 0x08432898c989a288 0x511da6e73e0e0000 0x944769b9cf838000

def z1185 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1ffee73e2ecb31 0xffc7ffb9cf8bb2cc

def z1186 : W := mkw 0x12fbfddef1993046 0x84beff77bc664c11 0xfbfffffff9d134ce 0xfefffffffe744d33

def z1187 : W := mkw 0x809600b005300282 0x2025802c014c00a0 0x79fe01f807f00fc3 0xde7f807e01fc03f0

def z1188 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x59fe06f807f00bc1 0xd67f81be01fc02f0

def z1189 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xfffffffff8310fff 0xfffffffffe0c43ff

def z1190 : W := mkw 0x80b607b00774ae83 0xe02d81ec01dd2ba0 0x79fe07f807f0ffc3 0xde7f81fe01fc3ff0

def z1191 : W := mkw 0x0008a84a70000000 0x00022a129c000000 0xdb1da7fff8000000 0xf6c769fffe000000

def z1192 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x7bfe07f8c7f00fff 0xdeff81fe31fc03ff

def z1193 : W := mkw 0xd0f34d9cd1d914ce 0x743cd36734764533 0x20e25918c1d134ce 0x0838964630744d33

def z1194 : W := mkw 0x40414005808b0028 0x101050016022c00a 0xbee1c107c7cf0c3f 0x6fb87041f1f3c30f

def z1195 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0x13fd86e7f8000000 0x04ff61b9fe000000

def z1196 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xff1fffff3e3ffff3 0xffc7ffffcf8ffffc

def z1197 : W := mkw 0x009ea00005348003 0x0027a800014d2000 0xfcfff80007fff003 0x3f3ffe0001fffc00

def z1198 : W := mkw 0x0096022007300a02 0x0025808801cc0280 0x79fe07f807f00fc3 0xde7f81fe01fc03f0

def z1199 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da7e7fe2ecf3d 0xf7c769f9ff8bb3cf

def z1200 : W := mkw 0x004de00004ad8001 0x00137800012b6000 0xfcfff80007fff003 0x3f3ffe0001fffc00

def z1201 : W := mkw 0x82f35d9cd1d92482 0xe0bcd76734764920 0x20e25918c1d134c2 0x0838964630744d30

def z1202 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0x79fe07f807c00fc0 0xde7f81fe01f003f0

def z1203 : W := mkw 0x0049f04220000000 0x00127c1088000000 0xdb1dfee738000000 0xf6c77fb9ce000000

def z1204 : W := mkw 0x02fbfddef0000000 0x00beff77bc000000 0xbbfdc7fff8000000 0xeeff71fffe000000

def z1205 : W := mkw 0x00dff00005bda003 0x8037fc00016f6800 0xfefff900c7fff003 0x7fbffe4031fffc00

def z1206 : W := mkw 0xd0200fbdda425ffc 0x740803ef769097ff 0x030007fff8000ffc 0xc0c001fffe0003ff

def z1207 : W := mkw 0x004df00005bda003 0x80137c00016f6800 0xbce1f80007fff003 0x2f387e0001fffc00

def z1208 : W := mkw 0x4061470582cb0c28 0x501851c160b2c30a 0xbee1c707c7fffc3f 0x6fb871c1f1ffff0f

def z1209 : W := mkw 0x80b607b007700e82 0x602d81ec01dc03a0 0xfbfe47f8c7f00fc3 0xfeff91fe31fc03f0

def z1210 : W := mkw 0x210ca2632e26cb31 0x08432898cb89b2cc 0xdf1da6e73e2ec031 0x37c769b9cf8bb00c

def z1211 : W := mkw 0x02fbfddef1102002 0x80beff77bc440800 0xfbfffffff8103000 0xfefffffffe040c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z10]),(0,[z1,z7,z3,z4,z11,z5,z6]),(0,[z1,z7,z3,z4,z5,z12,z6])],[(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z1,z7,z3,z4,z5,z14,z6]),(0,[z15,z16,z1,z3,z4,z5,z6]),(0,[z1,z7,z17,z3,z18,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z19,z5,z6]),(0,[z1,z7,z3,z4,z5,z20,z6]),(0,[z21,z1,z7,z3,z4,z5,z6]),(1,[z22,z1,z3,z4,z5,z6])],[(0,[z1,z23,z7,z3,z4,z5,z6]),(0,[z24,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z25,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z6]),(0,[z1,z27,z3,z28,z4,z5,z6]),(0,[z29,z1,z7,z3,z4,z5,z6]),(0,[z30,z1,z31,z3,z4,z5,z6])],[],[(0,[z32,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z6,z33]),(0,[z1,z34,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z35,z6])],[(0,[z1,z7,z3,z36,z4,z5,z6]),(0,[z37,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z38,z39])],[(0,[z1,z7,z3,z4,z5,z6,z40]),(0,[z15,z41,z1,z3,z4,z5,z6]),(1,[z1,z42,z3,z28,z5,z6]),(1,[z43,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z44,z6]),(1,[z1,z7,z3,z45,z5,z46])],[(0,[z1,z7,z3,z47,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z48,z6]),(0,[z1,z7,z3,z49,z4,z5,z6]),(0,[z43,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z50,z6]),(0,[z51,z52,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z53])]],
   [[(0,[z1,z7,z3,z4,z54,z5,z6]),(0,[z15,z1,z3,z45,z4,z5,z6]),(0,[z55,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z56,z5,z6]),(1,[z57,z7,z58,z4,z5,z6]),(0,[z1,z17,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z59])],[(0,[z60,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z61,z62,z5,z6])],[(0,[z1,z7,z3,z4,z63,z5,z6])],[(1,[z1,z7,z3,z64,z5,z6]),(0,[z57,z1,z7,z58,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z65,z6]),(0,[z1,z66,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z38,z6]),(0,[z1,z7,z3,z67,z4,z5,z6]),(0,[z1,z7,z68,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z69,z6])],[(0,[z1,z7,z3,z4,z5,z70,z6]),(0,[z1,z71,z72,z3,z4,z5,z6]),(0,[z1,z7,z73,z3,z4,z5,z6]),(0,[z1,z7,z3,z61,z4,z5,z6])],[],[(0,[z1,z2,z74,z3,z4,z5,z6]),(0,[z75,z1,z7,z3,z4,z5,z6]),(0,[z1,z42,z7,z3,z76,z5,z6]),(0,[z1,z73,z3,z28,z4,z5,z6]),(1,[z1,z7,z3,z77,z5,z6]),(0,[z1,z7,z3,z4,z77,z5,z6]),(0,[z1,z7,z78,z3,z4,z5,z6])]],
   [[(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z80,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z81,z5,z6]),(0,[z1,z7,z3,z4,z82,z5,z6]),(1,[z1,z3,z83,z4,z5,z6]),(0,[z1,z84,z7,z3,z4,z5,z6]),(0,[z1,z85,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z86])],[(0,[z1,z87,z7,z3,z4,z5,z6]),(1,[z1,z88,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z89,z6]),(0,[z90,z15,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z91,z6])],[(1,[z92,z7,z93,z4,z5,z6]),(0,[z1,z7,z94,z3,z4,z5,z6]),(0,[z1,z7,z3,z95,z5,z96,z6])],[(1,[z1,z7,z3,z97,z5,z6]),(0,[z1,z7,z3,z4,z97,z5,z6]),(0,[z98,z7,z3,z4,z5,z99,z6]),(0,[z15,z1,z3,z95,z4,z5,z6]),(0,[z1,z100,z7,z3,z4,z5,z6]),(0,[z51,z1,z7,z4,z5,z6,z39]),(0,[z101,z1,z7,z3,z5,z96,z6])],[(0,[z102,z1,z3,z28,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z103]),(0,[z30,z104,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z105,z5,z6]),(0,[z106,z15,z1,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z107,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z108])],[(0,[z1,z7,z3,z4,z109,z5,z6]),(0,[z1,z74,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z110,z4,z5,z6])],[(0,[z111,z1,z7,z3,z4,z5,z6]),(0,[z90,z1,z3,z28,z4,z5,z6]),(1,[z90,z1,z7,z76,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z112,z6]),(0,[z113,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z114,z6]),(0,[z1,z3,z28,z4,z5,z96,z6]),(1,[z1,z7,z3,z115,z5,z6]),(0,[z1,z7,z4,z116,z5,z117,z6]),(0,[z118,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z119,z6]),(0,[z1,z7,z3,z4,z120,z5,z6]),(0,[z1,z72,z3,z121,z4,z5,z6]),(1,[z1,z71,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z122,z5,z6])],[(1,[z123,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z124,z5,z6]),(0,[z1,z7,z3,z4,z5,z125,z6]),(0,[z101,z15,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z126,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z6])],[(0,[z113,z7,z3,z4,z127,z5,z6]),(0,[z128,z1,z7,z3,z4,z5,z6]),(0,[z15,z129,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z130,z6]),(0,[z106,z1,z3,z28,z4,z5,z6]),(0,[z131,z1,z3,z4,z76,z5,z6]),(0,[z1,z7,z3,z4,z132,z5,z6])],[(0,[z1,z7,z3,z133,z4,z5,z6]),(0,[z1,z3,z134,z28,z4,z5,z6]),(0,[z1,z7,z3,z45,z5,z46,z6])],[(0,[z135,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z136,z6]),(0,[z137,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z138,z6]),(0,[z139,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z62,z5,z140,z6])],[(0,[z1,z7,z3,z4,z141,z5,z6]),(0,[z1,z7,z3,z4,z5,z142,z6]),(0,[z1,z7,z3,z143,z4,z5,z6]),(0,[z144,z129,z7,z3,z4,z5,z6]),(0,[z1,z145,z7,z3,z4,z5,z6])],[(0,[z146,z1,z7,z3,z4,z5,z6]),(0,[z147,z15,z1,z3,z4,z5,z6]),(0,[z15,z1,z34,z3,z4,z5,z6]),(0,[z148,z1,z7,z3,z4,z5,z6]),(0,[z149,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z150,z6]),(0,[z101,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z151,z6]),(0,[z1,z7,z3,z45,z95,z5,z6])],[(0,[z152,z1,z7,z3,z4,z5,z6]),(0,[z153,z1,z7,z3,z4,z5,z6]),(0,[z135,z1,z7,z3,z154,z5,z6]),(0,[z1,z7,z3,z4,z5,z155,z6]),(0,[z1,z3,z4,z5,z13,z6,z103]),(0,[z1,z7,z3,z4,z5,z6,z156]),(0,[z1,z7,z3,z4,z5,z6,z157]),(0,[z1,z7,z3,z4,z158,z5,z6])],[(0,[z15,z1,z3,z154,z4,z5,z6]),(0,[z15,z1,z27,z3,z4,z5,z6]),(0,[z1,z7,z159,z3,z4,z5,z6]),(0,[z1,z3,z160,z28,z4,z5,z6])],[(0,[z79,z1,z161,z3,z4,z5,z6]),(0,[z1,z3,z162,z28,z4,z5,z6]),(0,[z163,z1,z3,z28,z4,z5,z6]),(0,[z90,z1,z7,z3,z95,z5,z6]),(0,[z1,z7,z3,z4,z5,z164,z6]),(0,[z1,z7,z3,z4,z5,z6,z165])],[(0,[z166,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z167,z6]),(0,[z1,z168,z7,z3,z4,z5,z6]),(1,[z131,z1,z3,z4,z5,z6]),(0,[z1,z7,z169,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z170,z6]),(0,[z1,z7,z3,z4,z171,z5,z6])],[(0,[z98,z16,z7,z3,z4,z5,z6]),(0,[z172,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z173,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z174,z6]),(0,[z1,z7,z3,z4,z175,z5,z6]),(0,[z1,z176,z7,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z6,z177])],[(0,[z178,z1,z7,z3,z4,z5,z6]),(0,[z179,z1,z7,z3,z4,z5,z6]),(0,[z1,z74,z3,z134,z4,z5,z6]),(0,[z1,z7,z180,z3,z4,z5,z6]),(1,[z1,z181,z3,z4,z5,z6]),(0,[z182,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z183,z5,z6]),(1,[z1,z7,z3,z4,z6,z184]),(0,[z185,z1,z7,z3,z4,z5,z6]),(0,[z186,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z187])],[(0,[z15,z1,z93,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z188,z5,z189]),(0,[z1,z7,z3,z190,z4,z5,z6]),(0,[z15,z1,z3,z4,z76,z5,z6])],[(0,[z1,z7,z3,z4,z191,z5,z6]),(0,[z1,z7,z3,z4,z192,z5,z6]),(0,[z1,z7,z193,z3,z4,z5,z6]),(0,[z194,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z195,z6]),(0,[z1,z7,z3,z4,z5,z196,z6]),(0,[z98,z92,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z197]),(1,[z1,z7,z72,z95,z5,z6])],[(0,[z198,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z199,z3,z4,z5,z6]),(0,[z1,z7,z3,z200,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z6,z201]),(0,[z1,z7,z3,z61,z4,z96,z6]),(0,[z1,z7,z3,z4,z5,z6,z202]),(0,[z1,z7,z3,z4,z38,z6,z201])],[(0,[z203,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z204,z5,z6]),(0,[z1,z7,z3,z4,z188,z5,z205]),(0,[z206,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z72,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z46,z6]),(0,[z1,z7,z3,z207,z4,z5,z6])],[(0,[z1,z208,z7,z161,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z209,z6]),(0,[z15,z1,z3,z4,z127,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z210]),(0,[z106,z1,z7,z3,z5,z6,z33])],[(0,[z1,z161,z3,z4,z5,z13,z6]),(0,[z211,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z212,z6]),(0,[z1,z213,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z45,z4,z5,z46])]],
   [[(0,[z1,z7,z3,z4,z5,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z214]),(0,[z15,z98,z1,z3,z4,z5,z6]),(0,[z1,z7,z215,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z216,z6]),(0,[z1,z7,z3,z5,z46,z6,z33])],[(0,[z92,z7,z3,z4,z5,z6,z217]),(1,[z1,z7,z3,z4,z5,z189]),(0,[z1,z7,z3,z4,z5,z217,z39]),(0,[z1,z218,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z219,z5,z6])],[(0,[z1,z7,z3,z4,z5,z220,z6]),(0,[z57,z15,z1,z3,z4,z5,z6]),(0,[z15,z113,z1,z7,z3,z5,z6]),(0,[z1,z221,z7,z3,z4,z5,z6]),(0,[z98,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z222]),(0,[z1,z7,z223,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z224,z5,z6]),(0,[z102,z1,z7,z3,z4,z225,z6]),(0,[z1,z7,z95,z4,z76,z5,z6]),(0,[z1,z7,z3,z95,z5,z6,z33]),(0,[z1,z7,z3,z4,z5,z226,z6])],[(0,[z98,z7,z3,z58,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z227,z6]),(0,[z1,z7,z228,z3,z4,z5,z6]),(0,[z1,z42,z7,z3,z62,z5,z6]),(0,[z229,z1,z3,z28,z4,z5,z6]),(1,[z1,z230,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z231,z5,z6]),(0,[z1,z7,z3,z4,z5,z38,z46])],[(0,[z1,z2,z3,z134,z4,z5,z6]),(0,[z1,z74,z7,z3,z4,z225,z6]),(0,[z1,z7,z3,z232,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z205]),(0,[z1,z7,z3,z233,z5,z13,z6])],[(0,[z113,z135,z7,z3,z4,z5,z6]),(1,[z1,z221,z3,z4,z5,z6]),(0,[z1,z42,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z234,z4,z5,z6]),(0,[z1,z235,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z13]),(0,[z1,z7,z3,z4,z236,z5,z6]),(0,[z1,z237,z7,z3,z4,z5,z6]),(0,[z106,z1,z7,z3,z4,z5,z46])],[(0,[z1,z42,z7,z3,z238,z5,z6]),(0,[z239,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z79,z7,z161,z3,z4,z5,z6]),(0,[z57,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z240,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z117,z6]),(0,[z1,z3,z28,z4,z5,z6,z33]),(0,[z1,z7,z3,z4,z5,z6,z241])],[(0,[z1,z7,z3,z4,z116,z5,z6])],[(0,[z92,z7,z3,z4,z5,z242,z6]),(0,[z1,z7,z3,z154,z95,z5,z6]),(0,[z1,z7,z3,z4,z243,z5,z6]),(0,[z15,z15,z1,z3,z4,z5,z6]),(0,[z244,z15,z1,z3,z4,z5,z6]),(0,[z30,z15,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z245,z6]),(0,[z1,z7,z3,z4,z5,z246,z6]),(0,[z247,z1,z7,z3,z4,z5,z6]),(0,[z248,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z249,z3,z4,z5,z6]),(1,[z135,z7,z3,z154,z5,z6]),(0,[z250,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z251,z4,z5,z6]),(0,[z1,z74,z27,z3,z4,z5,z6]),(0,[z1,z3,z4,z252,z76,z5,z6]),(0,[z1,z7,z3,z76,z5,z96,z6])],[(0,[z1,z7,z3,z4,z5,z6,z253]),(0,[z1,z7,z3,z4,z5,z6,z254]),(0,[z1,z3,z28,z45,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z103]),(1,[z1,z3,z4,z5,z255,z6])],[(0,[z256,z1,z7,z3,z4,z5,z6]),(0,[z113,z1,z42,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z257,z5,z6]),(0,[z1,z7,z3,z258,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z259])],[(0,[z1,z260,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z261]),(0,[z1,z7,z3,z4,z5,z262,z6]),(0,[z1,z7,z3,z4,z263,z5,z6]),(0,[z264,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z265,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z5,z38]),(0,[z266,z7,z3,z4,z5,z38,z6])],[(0,[z267,z7,z3,z4,z5,z117,z6])]],
   [[(0,[z92,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z28,z4,z5,z6]),(0,[z30,z1,z3,z28,z4,z5,z6]),(0,[z244,z1,z3,z28,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z38,z6]),(0,[z1,z7,z3,z4,z268,z5,z6]),(0,[z51,z1,z181,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z269,z5,z6]),(0,[z129,z7,z3,z4,z188,z5,z6]),(0,[z1,z7,z3,z18,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z5,z270,z6])],[(0,[z1,z7,z3,z4,z5,z6,z271])],[(0,[z1,z272,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z242,z117,z6]),(0,[z102,z1,z7,z3,z4,z273,z6]),(0,[z1,z7,z3,z4,z5,z274,z6]),(0,[z1,z7,z3,z275,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z276,z6]),(0,[z277,z1,z7,z3,z4,z5,z6]),(0,[z22,z1,z3,z4,z5,z6,z33])],[(0,[z278,z1,z7,z3,z4,z5,z6]),(0,[z279,z1,z7,z3,z4,z5,z6]),(0,[z144,z7,z3,z4,z5,z6,z217]),(0,[z98,z1,z88,z3,z4,z5,z6]),(0,[z101,z1,z42,z7,z3,z5,z6]),(0,[z1,z74,z7,z3,z4,z273,z6]),(0,[z1,z7,z72,z3,z95,z5,z6]),(0,[z1,z7,z3,z4,z280,z5,z6])],[(0,[z1,z7,z3,z4,z5,z281,z6]),(0,[z1,z7,z282,z3,z4,z5,z6]),(0,[z283,z1,z7,z3,z4,z5,z6]),(0,[z16,z1,z3,z28,z4,z5,z6]),(0,[z1,z42,z7,z3,z28,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z284]),(0,[z1,z7,z285,z3,z4,z5,z39])],[(0,[z286,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z287,z5,z6]),(0,[z1,z7,z17,z3,z4,z5,z6]),(0,[z1,z3,z28,z95,z4,z5,z6])]],
   [[(0,[z288,z15,z1,z3,z4,z5,z6]),(0,[z1,z2,z27,z3,z4,z5,z6]),(0,[z57,z1,z7,z3,z4,z5,z289]),(0,[z1,z290,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z291,z5,z6]),(0,[z1,z7,z3,z292,z4,z5,z6]),(0,[z1,z7,z3,z4,z293,z5,z6])],[(0,[z288,z79,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z294,z5,z6]),(0,[z15,z92,z1,z3,z4,z5,z6]),(0,[z295,z1,z7,z3,z4,z5,z6]),(0,[z296,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z297]),(0,[z298,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z299,z6]),(0,[z1,z7,z3,z4,z5,z6,z300]),(0,[z1,z7,z3,z4,z301,z5,z6]),(0,[z1,z7,z3,z4,z5,z302,z6]),(0,[z1,z7,z3,z4,z5,z6,z303]),(0,[z101,z1,z7,z3,z61,z5,z6])],[(0,[z1,z304,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z50,z117,z6]),(0,[z1,z305,z7,z3,z4,z5,z6])],[(0,[z144,z1,z25,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z306,z6]),(0,[z1,z7,z3,z307,z4,z5,z6]),(0,[z98,z1,z7,z3,z4,z5,z38]),(0,[z15,z1,z7,z3,z95,z5,z6]),(0,[z1,z7,z3,z4,z107,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z308]),(0,[z1,z74,z3,z4,z273,z5,z6]),(0,[z1,z7,z3,z5,z13,z6,z187]),(0,[z1,z7,z3,z45,z76,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z309]),(0,[z51,z1,z230,z3,z4,z5,z6]),(0,[z106,z1,z7,z3,z45,z5,z6])],[(0,[z1,z7,z7,z3,z4,z5,z6]),(0,[z1,z7,z310,z3,z4,z5,z6]),(0,[z15,z1,z285,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z62,z5,z6])],[(0,[z1,z7,z311,z3,z4,z5,z6]),(0,[z288,z1,z3,z28,z4,z5,z6]),(0,[z144,z7,z3,z4,z5,z242,z6]),(0,[z1,z7,z3,z4,z312,z5,z6]),(0,[z1,z7,z3,z4,z313,z5,z6]),(0,[z1,z7,z3,z4,z314,z5,z6]),(1,[z1,z3,z4,z5,z140,z6])],[(0,[z75,z1,z27,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z76,z5,z6]),(1,[z1,z7,z3,z315,z5,z6]),(0,[z1,z7,z3,z4,z315,z5,z6]),(0,[z1,z7,z3,z4,z5,z96,z6])]],
   [[(1,[z1,z316,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z317,z99,z6]),(0,[z15,z1,z3,z4,z4,z5,z6]),(1,[z102,z1,z3,z4,z225,z6]),(0,[z1,z3,z4,z5,z255,z96,z6]),(0,[z318,z1,z7,z3,z4,z5,z6])],[(1,[z79,z161,z3,z4,z5,z6]),(0,[z1,z161,z3,z28,z4,z5,z6]),(0,[z288,z7,z3,z4,z127,z5,z6]),(0,[z1,z7,z3,z4,z319,z5,z6]),(0,[z15,z1,z3,z134,z4,z5,z6]),(0,[z15,z1,z3,z4,z238,z5,z6]),(0,[z1,z320,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z321,z6])],[(0,[z1,z161,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z5,z6,z322]),(0,[z323,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z13,z6])],[(0,[z324,z1,z7,z3,z4,z5,z6]),(1,[z15,z1,z3,z62,z5,z6]),(0,[z41,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z7,z3,z5,z6,z33]),(0,[z1,z7,z3,z325,z4,z5,z6]),(0,[z326,z1,z7,z3,z4,z5,z6]),(1,[z326,z1,z7,z3,z4,z201])],[(0,[z144,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z327,z4,z5,z6]),(0,[z1,z328,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z329,z4,z5,z6]),(0,[z113,z1,z7,z3,z127,z5,z6]),(0,[z330,z15,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z6,z39]),(0,[z1,z7,z3,z4,z5,z6,z331]),(0,[z332,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z5,z201])],[(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z144,z1,z7,z3,z4,z242,z6]),(0,[z333,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z334,z3,z4,z5,z6]),(1,[z15,z1,z3,z4,z5,z6]),(0,[z1,z285,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z335,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z336,z6]),(0,[z1,z7,z3,z61,z4,z62,z6])],[(1,[z15,z1,z3,z238,z5,z6]),(0,[z1,z7,z3,z337,z4,z5,z6]),(0,[z338,z1,z7,z3,z4,z5,z6]),(0,[z339,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z340,z1,z7,z3,z4,z5,z6]),(0,[z15,z135,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z341]),(0,[z342,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z105,z5,z6]),(0,[z343,z1,z7,z3,z4,z5,z6])],[(0,[z344,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z345,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z346,z5,z6]),(0,[z15,z144,z1,z3,z4,z5,z6]),(0,[z16,z1,z7,z3,z4,z5,z217]),(0,[z1,z7,z3,z4,z5,z245,z217]),(0,[z1,z27,z7,z134,z4,z5,z6]),(0,[z1,z7,z3,z4,z347,z5,z6]),(0,[z1,z7,z3,z4,z5,z348,z6]),(0,[z1,z7,z3,z4,z5,z349,z6]),(0,[z1,z7,z3,z4,z5,z350,z6])],[(0,[z351,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z352,z6]),(0,[z1,z7,z3,z4,z5,z353,z6]),(1,[z266,z7,z3,z4,z5,z6])],[],[(1,[z288,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z95,z127,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z354]),(1,[z1,z3,z28,z4,z5,z6])],[(0,[z1,z7,z3,z4,z355,z5,z6]),(1,[z1,z7,z3,z4,z317,z6]),(0,[z1,z3,z28,z4,z76,z5,z6]),(0,[z1,z7,z3,z5,z356,z225,z6]),(0,[z1,z7,z3,z357,z4,z5,z6]),(0,[z1,z358,z7,z3,z4,z5,z6])],[(0,[z359,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z360,z4,z5,z6]),(0,[z361,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z362,z4,z5,z6])],[(0,[z1,z7,z3,z363,z4,z5,z6]),(0,[z1,z7,z3,z83,z4,z5,z6]),(1,[z15,z41,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z364,z5,z6]),(0,[z1,z365,z7,z3,z4,z5,z6])]],
   [[(0,[z366,z1,z7,z3,z4,z5,z6]),(0,[z123,z1,z7,z161,z3,z5,z6]),(0,[z1,z7,z88,z3,z4,z5,z6]),(0,[z367,z1,z7,z3,z4,z5,z6]),(0,[z368,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z177])],[(0,[z1,z7,z3,z369,z4,z5,z6]),(0,[z1,z27,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z370,z6]),(0,[z1,z7,z371,z3,z4,z5,z6])],[(0,[z1,z161,z3,z134,z4,z5,z6]),(0,[z7,z93,z3,z4,z188,z5,z6]),(0,[z1,z3,z28,z4,z127,z5,z6]),(1,[z16,z7,z3,z4,z5,z217]),(0,[z51,z1,z7,z3,z4,z5,z39]),(0,[z101,z1,z7,z3,z4,z5,z108]),(0,[z1,z372,z7,z3,z4,z5,z6])],[(0,[z373,z1,z7,z3,z4,z5,z6]),(0,[z98,z1,z7,z3,z4,z5,z201]),(0,[z374,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z375,z6]),(0,[z1,z7,z3,z4,z5,z6,z201])],[(0,[z376,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z99,z39]),(0,[z1,z7,z3,z4,z5,z46,z6])],[(0,[z1,z7,z3,z4,z5,z6,z377]),(0,[z378,z1,z7,z3,z4,z5,z6])],[(0,[z379,z1,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z154,z76,z5,z6]),(1,[z15,z1,z3,z28,z5,z6]),(1,[z101,z1,z7,z3,z96,z6])],[(0,[z1,z7,z3,z4,z5,z6,z380]),(0,[z1,z2,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z317,z5,z6]),(0,[z75,z15,z1,z3,z4,z5,z6]),(1,[z15,z34,z3,z4,z5,z6])]],
   [[(0,[z7,z161,z3,z4,z127,z5,z6]),(0,[z1,z7,z3,z4,z5,z381,z6]),(0,[z1,z7,z382,z3,z4,z5,z6]),(0,[z1,z383,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z252,z5,z6]),(0,[z51,z1,z7,z3,z315,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z384])],[(0,[z385,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z386,z3,z4,z5,z6]),(0,[z1,z7,z387,z3,z4,z5,z6]),(0,[z388,z1,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z103]),(0,[z1,z7,z3,z4,z389,z5,z6]),(0,[z1,z3,z4,z5,z6,z202,z33])],[(0,[z2,z7,z161,z3,z4,z5,z6]),(0,[z390,z1,z7,z3,z4,z5,z6]),(0,[z1,z391,z7,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z99,z6]),(0,[z1,z52,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z392]),(0,[z1,z393,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z33,z201]),(0,[z394,z1,z7,z3,z4,z5,z6])],[(0,[z288,z135,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z289]),(0,[z395,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z117,z6]),(0,[z1,z7,z3,z4,z116,z6,z201]),(0,[z1,z3,z4,z5,z46,z6,z396])],[(0,[z1,z7,z3,z4,z5,z6,z397]),(0,[z1,z7,z3,z4,z99,z6,z184]),(0,[z75,z1,z3,z28,z4,z5,z6]),(1,[z1,z3,z121,z4,z5,z6]),(0,[z398,z1,z7,z3,z4,z5,z6]),(0,[z326,z1,z7,z3,z4,z5,z38])],[(0,[z135,z7,z161,z3,z4,z5,z6]),(0,[z1,z7,z3,z399,z4,z5,z6]),(0,[z400,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z401,z4,z5,z6])],[(0,[z1,z7,z3,z402,z4,z5,z6]),(0,[z403,z1,z7,z3,z4,z5,z6]),(0,[z51,z15,z1,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z103]),(0,[z1,z7,z3,z4,z5,z6,z404]),(1,[z1,z7,z3,z4,z405,z6]),(0,[z1,z7,z3,z4,z5,z6,z33])]],
   [[(0,[z1,z7,z3,z4,z406,z5,z6]),(0,[z1,z7,z407,z3,z4,z5,z6]),(0,[z1,z7,z408,z3,z4,z5,z6]),(1,[z106,z1,z7,z3,z5,z33])],[(0,[z1,z7,z3,z4,z5,z6,z409]),(0,[z15,z1,z7,z3,z45,z5,z6]),(0,[z1,z3,z28,z4,z5,z6,z410]),(0,[z411,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z72,z3,z76,z5,z6])],[(0,[z92,z1,z7,z58,z4,z5,z6]),(0,[z412,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z413,z3,z4,z5,z6]),(0,[z102,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z414,z4,z5,z6]),(0,[z1,z7,z3,z45,z4,z5,z6])],[(0,[z415,z1,z7,z3,z4,z5,z6]),(1,[z98,z7,z3,z4,z5,z99]),(0,[z1,z3,z28,z28,z4,z5,z6]),(0,[z416,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z210]),(0,[z1,z7,z3,z4,z5,z38,z245])],[(0,[z1,z417,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z6]),(1,[z1,z7,z3,z18,z5,z6]),(0,[z418,z15,z1,z3,z4,z5,z6]),(0,[z419,z15,z1,z3,z4,z5,z6]),(0,[z51,z1,z3,z28,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z225,z6]),(0,[z1,z420,z7,z3,z4,z5,z6])],[(0,[z144,z98,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z273,z5,z6]),(0,[z1,z365,z3,z4,z5,z46,z6])],[(0,[z421,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z61,z95,z5,z6]),(0,[z1,z7,z3,z4,z5,z422,z6]),(0,[z1,z7,z3,z4,z5,z38,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z423]),(0,[z1,z7,z3,z4,z5,z424,z6]),(0,[z15,z1,z7,z3,z76,z5,z6]),(0,[z1,z7,z425,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z4,z5,z6])],[(0,[z1,z7,z3,z426,z4,z5,z6]),(0,[z1,z7,z3,z4,z427,z5,z6])],[(0,[z1,z7,z3,z4,z5,z428,z6]),(1,[z1,z429,z3,z4,z5,z6]),(0,[z1,z429,z7,z3,z4,z5,z6]),(0,[z15,z326,z1,z3,z4,z5,z6]),(0,[z102,z1,z74,z3,z4,z5,z6])],[(0,[z113,z1,z7,z3,z154,z5,z6]),(0,[z15,z1,z3,z4,z5,z6,z217]),(0,[z1,z430,z3,z4,z62,z5,z6])],[(0,[z129,z92,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z431,z5,z6]),(0,[z90,z1,z7,z72,z4,z5,z6]),(0,[z432,z1,z7,z3,z4,z5,z6])],[(0,[z433,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z127,z76,z5,z6]),(0,[z104,z1,z7,z3,z4,z5,z6])],[(0,[z75,z1,z3,z134,z4,z5,z6]),(0,[z434,z1,z7,z3,z4,z5,z6]),(0,[z1,z435,z7,z3,z4,z5,z6]),(0,[z436,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z199,z3,z4,z5,z6]),(0,[z1,z7,z3,z95,z4,z5,z6]),(1,[z51,z1,z7,z4,z5,z39])],[(0,[z437,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z58,z4,z5,z6,z217]),(0,[z1,z7,z3,z4,z438,z5,z6]),(0,[z439,z1,z7,z3,z4,z5,z6]),(0,[z16,z1,z7,z3,z4,z5,z99]),(0,[z1,z7,z3,z4,z5,z6,z440]),(0,[z1,z71,z7,z3,z4,z5,z6]),(0,[z441,z1,z7,z3,z4,z5,z6]),(0,[z101,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z442])]],
   [[(0,[z1,z7,z3,z4,z443,z5,z6]),(0,[z444,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z445,z4,z5,z6]),(0,[z7,z3,z4,z5,z38,z6,z177])],[],[(0,[z446,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z160,z4,z5,z6]),(0,[z163,z1,z7,z3,z4,z5,z6]),(0,[z447,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z73,z4,z116,z5,z6]),(0,[z1,z7,z230,z3,z4,z5,z6]),(0,[z448,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z449])],[(0,[z129,z1,z7,z3,z4,z5,z6]),(0,[z1,z27,z3,z4,z5,z6,z103]),(0,[z1,z7,z3,z4,z5,z450,z6]),(0,[z1,z7,z3,z4,z451,z5,z6])],[(0,[z129,z7,z3,z58,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z242,z6]),(0,[z1,z3,z28,z4,z4,z5,z6]),(0,[z1,z7,z452,z3,z4,z5,z6]),(0,[z326,z1,z7,z3,z4,z5,z201])],[(0,[z1,z7,z453,z3,z4,z5,z6]),(0,[z129,z1,z7,z3,z4,z242,z6]),(0,[z1,z7,z3,z4,z5,z53,z6]),(0,[z454,z1,z7,z3,z4,z5,z6])],[(0,[z7,z3,z4,z188,z5,z6,z217]),(0,[z455,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z456,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z457])],[(0,[z458,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z459,z6]),(0,[z1,z7,z460,z3,z4,z5,z6])]],
   [[(0,[z79,z1,z3,z28,z4,z5,z6]),(0,[z7,z3,z58,z4,z5,z242,z6]),(0,[z461,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z462,z5,z6]),(0,[z51,z1,z7,z3,z4,z405,z6])],[(0,[z1,z7,z161,z3,z4,z5,z6]),(0,[z1,z7,z463,z3,z4,z5,z6]),(0,[z75,z1,z7,z17,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z6,z39]),(0,[z1,z7,z3,z4,z5,z13,z6]),(0,[z90,z1,z7,z4,z76,z5,z6])],[(1,[z1,z7,z3,z4,z109,z6]),(0,[z1,z464,z7,z3,z4,z5,z6])],[(0,[z15,z1,z3,z58,z4,z5,z6]),(0,[z15,z1,z3,z4,z188,z5,z6]),(0,[z15,z1,z3,z4,z116,z5,z6]),(0,[z1,z7,z3,z4,z5,z465,z6]),(1,[z1,z3,z4,z5,z6,z396])],[(0,[z466,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z467])],[(0,[z1,z7,z3,z468,z4,z5,z6]),(0,[z469,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z154,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z470,z6]),(0,[z471,z1,z7,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z6,z254])],[(0,[z7,z3,z4,z188,z5,z242,z6]),(0,[z1,z7,z472,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z473,z6])]],
   [[(0,[z1,z7,z3,z474,z4,z5,z6]),(0,[z98,z1,z3,z28,z4,z5,z6]),(1,[z475,z7,z3,z4,z5,z6]),(0,[z476,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z477,z3,z4,z5,z6]),(0,[z1,z478,z7,z3,z4,z5,z6])],[(0,[z24,z1,z3,z4,z127,z5,z6]),(0,[z1,z7,z479,z3,z4,z5,z6]),(0,[z267,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z480,z6])],[(0,[z1,z7,z3,z4,z481,z5,z6]),(1,[z101,z15,z1,z3,z5,z6]),(1,[z1,z74,z3,z4,z273,z6]),(0,[z1,z7,z3,z482,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z483,z6]),(1,[z1,z169,z3,z4,z5,z6]),(1,[z441,z7,z3,z4,z5,z6])],[(1,[z24,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z99,z6,z217]),(0,[z1,z7,z3,z4,z5,z484,z6]),(0,[z1,z7,z3,z4,z5,z6,z485]),(1,[z486,z1,z3,z4,z5,z6])],[(0,[z1,z7,z93,z3,z4,z5,z6]),(0,[z1,z42,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z76,z5,z6])],[(0,[z1,z7,z72,z95,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z46,z201])],[(0,[z16,z7,z3,z4,z5,z6,z217])],[(0,[z57,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z487,z5,z6]),(0,[z488,z1,z7,z3,z4,z5,z6]),(0,[z15,z41,z7,z3,z4,z5,z6]),(0,[z1,z3,z337,z28,z4,z5,z6]),(0,[z489,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z57,z7,z3,z58,z4,z5,z6]),(0,[z57,z7,z3,z4,z188,z5,z6]),(1,[z1,z84,z3,z4,z5,z6]),(0,[z1,z490,z7,z3,z4,z5,z6]),(0,[z30,z1,z7,z3,z4,z117,z6]),(0,[z1,z7,z3,z4,z117,z6,z201]),(0,[z326,z1,z7,z3,z4,z171,z6])],[(0,[z491,z1,z7,z3,z4,z5,z6]),(0,[z492,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z127,z5,z6]),(0,[z144,z1,z7,z3,z4,z171,z6]),(0,[z1,z7,z3,z4,z5,z493,z6])],[],[(0,[z494,z1,z7,z3,z4,z5,z6]),(0,[z1,z31,z7,z3,z4,z5,z6]),(0,[z30,z1,z7,z3,z4,z5,z210]),(0,[z1,z7,z3,z495,z4,z5,z6])],[(0,[z1,z496,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z497,z4,z5,z6]),(0,[z1,z7,z3,z4,z219,z5,z6])],[(0,[z1,z27,z161,z3,z4,z5,z6]),(0,[z1,z498,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z64,z4,z5,z6]),(0,[z499,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z184]),(0,[z1,z3,z134,z4,z5,z6,z103])],[(0,[z1,z7,z3,z4,z5,z500,z6]),(0,[z92,z1,z7,z93,z4,z5,z6]),(0,[z92,z1,z3,z28,z4,z5,z6]),(0,[z1,z27,z17,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z501,z6]),(0,[z0,z1,z7,z3,z4,z5,z13]),(0,[z1,z7,z502,z3,z4,z5,z6]),(0,[z1,z7,z3,z76,z5,z6,z33]),(0,[z1,z7,z3,z4,z503,z5,z6]),(0,[z1,z7,z3,z4,z5,z504,z6]),(1,[z1,z7,z3,z4,z5,z108]),(0,[z101,z1,z7,z3,z4,z96,z6])],[(0,[z1,z3,z28,z4,z5,z99,z6]),(0,[z1,z7,z505,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z506,z6]),(0,[z1,z42,z7,z3,z95,z5,z6])],[(0,[z1,z7,z17,z3,z105,z5,z6]),(0,[z15,z1,z3,z4,z5,z96,z6]),(0,[z1,z7,z3,z507,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z405,z6])],[(0,[z1,z7,z3,z4,z5,z508,z6]),(0,[z15,z1,z73,z3,z4,z5,z6]),(0,[z15,z1,z3,z61,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z509]),(0,[z30,z1,z7,z3,z4,z116,z6])],[(0,[z1,z208,z7,z3,z4,z5,z6]),(0,[z57,z1,z498,z3,z4,z5,z6]),(0,[z29,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z510,z6]),(0,[z1,z7,z3,z4,z5,z117,z6])],[(1,[z1,z7,z3,z5,z356,z6]),(0,[z1,z7,z3,z4,z5,z356,z6]),(0,[z1,z7,z3,z4,z5,z511,z6]),(0,[z512,z1,z7,z3,z4,z5,z6])],[(0,[z7,z93,z3,z58,z4,z5,z6]),(0,[z16,z1,z7,z3,z4,z5,z6]),(0,[z101,z15,z1,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z513]),(0,[z1,z7,z3,z4,z5,z514,z6]),(0,[z1,z7,z3,z4,z5,z6,z515])],[(0,[z1,z7,z3,z516,z4,z5,z6]),(0,[z15,z113,z1,z3,z4,z5,z6]),(0,[z517,z1,z7,z3,z4,z5,z6]),(0,[z518,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z519,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z520])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z189]),(0,[z298,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z410]),(0,[z521,z1,z7,z3,z4,z5,z6])],[(0,[z1,z522,z7,z3,z4,z5,z6]),(0,[z57,z1,z7,z3,z4,z109,z6]),(0,[z1,z7,z3,z523,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z524,z6])],[(0,[z1,z3,z28,z4,z273,z5,z6]),(0,[z1,z7,z3,z233,z4,z5,z6]),(0,[z525,z1,z7,z3,z4,z5,z6]),(1,[z30,z1,z7,z4,z117,z6]),(0,[z1,z7,z3,z4,z5,z6,z526])],[(0,[z15,z79,z1,z3,z4,z5,z6]),(0,[z57,z1,z7,z3,z4,z14,z6]),(0,[z1,z7,z3,z28,z4,z5,z6]),(0,[z527,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z528]),(0,[z1,z85,z3,z4,z5,z13,z6]),(0,[z529,z1,z7,z3,z4,z5,z6]),(0,[z530,z1,z7,z3,z4,z5,z6]),(0,[z51,z441,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z188,z117,z6]),(0,[z531,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z225,z6])],[(0,[z532,z1,z7,z3,z4,z5,z6]),(0,[z533,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z534,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z535]),(0,[z15,z34,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z38,z6])],[(0,[z1,z3,z28,z4,z5,z6,z217]),(0,[z1,z7,z3,z536,z4,z5,z6]),(0,[z15,z1,z85,z3,z4,z5,z6]),(0,[z1,z7,z3,z537,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z538])]],
   [[(0,[z539,z1,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z130,z6]),(0,[z1,z7,z3,z45,z4,z5,z33]),(0,[z1,z7,z540,z3,z4,z5,z6])],[(0,[z1,z74,z161,z3,z4,z5,z6]),(0,[z541,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z245,z6])],[(0,[z135,z1,z316,z3,z4,z5,z6]),(0,[z111,z15,z1,z3,z4,z5,z6]),(0,[z1,z542,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z543]),(1,[z1,z25,z3,z4,z5,z6]),(1,[z41,z7,z3,z4,z5,z6]),(0,[z1,z7,z544,z3,z4,z5,z6])],[(0,[z1,z3,z83,z4,z127,z5,z6]),(0,[z545,z1,z7,z3,z4,z5,z6]),(0,[z1,z546,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z38,z33])],[(0,[z1,z7,z3,z4,z5,z6,z547]),(0,[z135,z7,z3,z154,z4,z5,z6]),(0,[z548,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z285,z3,z4,z5,z245]),(0,[z1,z7,z3,z4,z5,z6,z549]),(0,[z1,z7,z3,z4,z550,z5,z6])],[(0,[z1,z7,z3,z4,z188,z116,z6]),(0,[z1,z551,z7,z3,z4,z5,z6]),(0,[z552,z1,z7,z3,z4,z5,z6]),(0,[z553,z1,z7,z3,z4,z5,z6])],[(0,[z554,z1,z7,z3,z4,z5,z6]),(0,[z30,z475,z7,z3,z4,z5,z6]),(0,[z106,z1,z7,z3,z4,z5,z33])]],
   [[(0,[z555,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z242,z6]),(0,[z129,z1,z7,z3,z4,z188,z6]),(1,[z1,z27,z17,z4,z5,z6]),(0,[z15,z102,z1,z3,z4,z5,z6]),(0,[z1,z74,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z556]),(0,[z1,z7,z285,z3,z4,z5,z6]),(1,[z1,z7,z285,z4,z5,z245])],[(0,[z1,z7,z3,z4,z557,z5,z6]),(0,[z15,z1,z3,z4,z171,z5,z6]),(0,[z1,z7,z3,z4,z558,z5,z6]),(0,[z90,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z559,z5,z6]),(0,[z30,z1,z169,z3,z4,z5,z6]),(0,[z560,z1,z7,z3,z4,z5,z6]),(0,[z561,z1,z7,z3,z4,z5,z6])],[(0,[z562,z1,z7,z3,z4,z5,z6]),(0,[z113,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z563,z5,z6]),(0,[z564,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z565,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z1,z566,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z567,z4,z5,z6]),(0,[z1,z7,z3,z134,z4,z5,z6]),(0,[z568,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z569])],[(0,[z1,z7,z3,z570,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z571,z6]),(0,[z1,z3,z28,z4,z572,z5,z6]),(0,[z1,z7,z3,z4,z5,z573,z6]),(0,[z106,z1,z7,z3,z4,z5,z6])],[(0,[z135,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z459,z6]),(0,[z1,z7,z3,z4,z5,z6,z574])],[(0,[z1,z7,z3,z575,z4,z5,z6]),(0,[z1,z3,z28,z4,z188,z5,z6]),(0,[z16,z1,z7,z3,z4,z5,z38]),(0,[z1,z3,z28,z4,z116,z5,z6])]],
   [[(0,[z288,z2,z7,z3,z4,z5,z6]),(0,[z1,z27,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z5,z576,z6]),(1,[z15,z1,z3,z95,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z39])],[(0,[z15,z1,z3,z4,z5,z6,z103]),(0,[z577,z1,z7,z3,z4,z5,z6]),(0,[z30,z1,z7,z4,z5,z117,z6]),(0,[z1,z7,z3,z4,z5,z578,z6])],[(1,[z15,z113,z1,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z579,z6]),(0,[z390,z15,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z4,z5,z6]),(1,[z1,z7,z3,z495,z5,z6]),(0,[z1,z580,z7,z3,z4,z5,z6])],[(0,[z1,z7,z73,z3,z4,z117,z6]),(0,[z1,z7,z3,z4,z5,z6,z581])],[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z582,z1,z7,z3,z4,z5,z6]),(0,[z75,z1,z7,z134,z4,z5,z6]),(0,[z1,z3,z28,z4,z62,z5,z6]),(0,[z583,z1,z7,z3,z4,z5,z6])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(1,[z144,z7,z3,z4,z242,z6]),(0,[z1,z42,z7,z3,z45,z5,z6]),(0,[z1,z72,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z584]),(0,[z1,z7,z585,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z586,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z587])],[(0,[z147,z1,z7,z3,z4,z5,z6]),(1,[z1,z498,z3,z4,z5,z6]),(0,[z588,z1,z7,z3,z4,z5,z6]),(1,[z15,z1,z3,z5,z6,z33]),(0,[z1,z3,z28,z4,z5,z589,z6]),(0,[z1,z7,z3,z4,z5,z590,z6]),(0,[z1,z7,z3,z591,z4,z5,z6])]],
   [[(0,[z15,z1,z2,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z150]),(0,[z129,z1,z7,z3,z4,z171,z6]),(0,[z1,z3,z28,z4,z238,z5,z6]),(0,[z101,z1,z7,z3,z4,z62,z6])],[(0,[z98,z1,z7,z3,z4,z5,z99]),(0,[z326,z1,z7,z3,z4,z6,z201])],[(0,[z144,z1,z7,z3,z4,z6,z201]),(1,[z34,z7,z3,z4,z5,z6]),(0,[z1,z592,z7,z3,z4,z5,z6]),(0,[z1,z475,z7,z3,z4,z5,z6])],[(0,[z1,z7,z593,z3,z4,z5,z6]),(0,[z101,z1,z7,z3,z4,z5,z53]),(0,[z1,z7,z3,z4,z5,z6,z594])],[(0,[z1,z595,z7,z3,z4,z5,z6]),(0,[z144,z1,z7,z3,z4,z188,z6]),(0,[z1,z7,z3,z596,z4,z5,z6]),(0,[z1,z7,z3,z4,z597,z5,z6]),(0,[z1,z7,z3,z4,z5,z39,z201]),(0,[z598,z1,z7,z3,z4,z5,z6])],[(0,[z15,z135,z1,z3,z4,z5,z6]),(0,[z1,z3,z363,z28,z4,z5,z6]),(0,[z599,z1,z7,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z50,z6]),(0,[z1,z7,z73,z3,z4,z116,z6]),(0,[z1,z430,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z255,z6]),(0,[z1,z7,z3,z600,z4,z5,z6])],[(0,[z1,z7,z3,z4,z601,z5,z6]),(1,[z1,z7,z3,z4,z14,z6]),(0,[z144,z1,z221,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z602]),(1,[z1,z7,z3,z61,z62,z6]),(0,[z1,z603,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z604,z3,z4,z5,z6]),(0,[z1,z7,z605,z3,z4,z5,z6]),(0,[z606,z1,z7,z3,z4,z5,z6]),(0,[z607,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z608,z4,z5,z6]),(0,[z51,z1,z7,z3,z4,z5,z245])],[(0,[z1,z7,z3,z4,z5,z609,z6]),(0,[z1,z7,z3,z4,z610,z5,z6]),(0,[z1,z7,z3,z4,z5,z611,z6]),(0,[z102,z1,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z612,z5,z6])],[(0,[z1,z7,z3,z613,z4,z5,z6]),(1,[z1,z208,z7,z3,z5,z6]),(0,[z57,z92,z7,z3,z4,z5,z6]),(0,[z57,z1,z282,z3,z4,z5,z6]),(0,[z1,z7,z614,z3,z4,z5,z6]),(0,[z1,z615,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z99,z245]),(0,[z15,z1,z3,z4,z5,z262,z6]),(0,[z1,z7,z3,z4,z5,z6,z616])],[(0,[z1,z7,z3,z4,z5,z617,z6]),(0,[z1,z7,z3,z618,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z205,z6]),(0,[z619,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z620,z6]),(1,[z0,z1,z3,z4,z5,z103]),(0,[z131,z1,z7,z3,z4,z5,z6]),(0,[z51,z1,z7,z3,z4,z5,z6]),(0,[z51,z1,z7,z285,z4,z5,z6])],[(0,[z123,z1,z7,z3,z4,z5,z6]),(0,[z229,z1,z7,z3,z4,z5,z6]),(0,[z621,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z233,z5,z6]),(0,[z1,z7,z3,z4,z5,z622,z6]),(0,[z1,z7,z3,z4,z5,z6,z623])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z99,z6]),(0,[z16,z1,z7,z3,z4,z5,z201]),(0,[z1,z624,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z61,z4,z5,z6]),(1,[z1,z3,z4,z252,z5,z6]),(0,[z1,z7,z3,z625,z4,z5,z6]),(0,[z1,z7,z3,z626,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z245,z201])],[(0,[z1,z17,z3,z134,z4,z5,z6]),(0,[z1,z7,z3,z627,z4,z5,z6]),(1,[z1,z7,z3,z4,z171,z38])]],
   [[(0,[z628,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z58,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z629])],[],[(0,[z630,z1,z7,z3,z4,z5,z6]),(0,[z418,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z134,z4,z5,z225,z6]),(0,[z15,z1,z42,z3,z4,z5,z6]),(0,[z419,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z631,z6]),(0,[z632,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z117,z6]),(0,[z1,z7,z3,z4,z5,z6,z396])],[(0,[z15,z1,z161,z3,z4,z5,z6]),(0,[z1,z7,z3,z633,z4,z5,z6]),(0,[z1,z7,z3,z4,z634,z5,z6]),(0,[z1,z27,z7,z17,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z13,z6]),(0,[z635,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z273,z5,z225,z6]),(0,[z1,z7,z636,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z637,z6]),(0,[z1,z7,z72,z3,z4,z5,z6]),(1,[z1,z31,z3,z4,z5,z6]),(0,[z51,z1,z7,z3,z495,z5,z6])],[(0,[z638,z1,z7,z3,z4,z5,z6]),(1,[z15,z135,z1,z3,z5,z6]),(0,[z15,z1,z17,z3,z4,z5,z6]),(0,[z436,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z639,z5,z6]),(0,[z30,z1,z7,z3,z4,z5,z349]),(0,[z1,z7,z285,z4,z5,z245,z6])],[(0,[z1,z7,z3,z4,z640,z5,z6]),(1,[z1,z3,z4,z5,z6,z202])],[(0,[z1,z3,z154,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z641,z6]),(0,[z1,z85,z3,z134,z4,z5,z6])],[(0,[z1,z7,z3,z642,z4,z5,z6]),(0,[z92,z7,z93,z3,z4,z5,z6]),(0,[z1,z7,z3,z643,z4,z5,z6]),(0,[z15,z1,z7,z3,z62,z5,z6]),(0,[z644,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z645,z6]),(0,[z22,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z646,z7,z3,z4,z5,z6]),(1,[z75,z1,z134,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z647,z6]),(0,[z1,z7,z3,z4,z5,z140,z6]),(0,[z1,z7,z3,z4,z5,z6,z648])],[(0,[z129,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z273,z5,z6]),(0,[z649,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z650,z4,z5,z6])],[(0,[z244,z1,z7,z3,z4,z5,z6]),(0,[z57,z144,z7,z3,z4,z5,z6]),(0,[z1,z7,z316,z3,z4,z5,z6]),(0,[z15,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z651,z4,z5,z6]),(0,[z30,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z231,z6]),(0,[z1,z7,z3,z4,z652,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z289]),(0,[z135,z1,z42,z7,z3,z5,z6]),(0,[z15,z1,z7,z3,z238,z5,z6]),(0,[z1,z413,z3,z28,z4,z5,z6])],[(0,[z1,z7,z3,z4,z653,z5,z6]),(0,[z1,z7,z3,z4,z534,z5,z6]),(0,[z1,z7,z654,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z116,z6]),(0,[z655,z1,z7,z3,z4,z5,z6])],[(1,[z15,z1,z3,z45,z5,z6]),(1,[z1,z7,z3,z5,z6,z187])],[(0,[z1,z7,z3,z656,z4,z5,z6]),(0,[z98,z1,z7,z3,z4,z5,z217]),(0,[z1,z7,z3,z4,z5,z6,z217]),(0,[z657,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z61,z76,z5,z6])],[(0,[z79,z1,z7,z3,z4,z5,z6]),(0,[z57,z1,z7,z3,z4,z5,z150]),(0,[z0,z1,z85,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z658,z6]),(0,[z57,z1,z7,z3,z64,z5,z6]),(0,[z1,z7,z3,z4,z5,z245,z6]),(0,[z659,z1,z7,z3,z4,z5,z6])],[(0,[z288,z1,z161,z3,z4,z5,z6]),(0,[z15,z1,z3,z327,z4,z5,z6]),(0,[z15,z1,z74,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z660]),(0,[z1,z7,z3,z4,z5,z6,z661])],[(0,[z1,z7,z3,z4,z5,z662,z6]),(0,[z1,z7,z3,z4,z663,z5,z6]),(0,[z1,z42,z7,z3,z5,z6,z33])],[(0,[z1,z7,z3,z664,z4,z5,z6]),(0,[z1,z7,z3,z4,z665,z5,z6]),(0,[z1,z7,z3,z4,z5,z666,z6])],[(0,[z667,z1,z7,z3,z4,z5,z6]),(1,[z15,z1,z3,z76,z5,z6]),(0,[z1,z7,z4,z5,z245,z6,z39]),(0,[z1,z7,z3,z668,z4,z5,z6])],[(0,[z1,z7,z3,z4,z669,z5,z6]),(0,[z1,z3,z28,z4,z171,z5,z6]),(0,[z1,z7,z670,z3,z4,z5,z6]),(1,[z104,z7,z3,z4,z5,z6]),(0,[z30,z1,z7,z73,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z671]),(0,[z1,z7,z3,z672,z4,z5,z6]),(0,[z1,z93,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z673,z5,z6]),(0,[z1,z7,z3,z162,z4,z5,z6]),(1,[z52,z7,z3,z4,z5,z6])],[(0,[z674,z1,z7,z3,z4,z5,z6]),(0,[z57,z1,z7,z3,z97,z5,z6]),(0,[z675,z1,z7,z3,z4,z5,z6]),(1,[z113,z7,z3,z127,z5,z6]),(0,[z1,z7,z3,z4,z5,z242,z6]),(0,[z1,z7,z676,z3,z4,z5,z6]),(0,[z1,z7,z3,z677,z4,z5,z6]),(0,[z1,z7,z678,z3,z4,z5,z6])]],
   [[(0,[z288,z1,z7,z3,z4,z5,z6]),(0,[z98,z7,z3,z4,z188,z5,z6]),(0,[z1,z7,z3,z4,z5,z679,z6]),(0,[z680,z1,z7,z3,z4,z5,z6])],[(0,[z681,z1,z7,z3,z4,z5,z6]),(0,[z98,z1,z429,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z682]),(0,[z1,z85,z27,z3,z4,z5,z6]),(0,[z15,z1,z7,z3,z28,z5,z6])],[(0,[z144,z7,z93,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z683]),(0,[z30,z1,z7,z3,z77,z5,z6]),(0,[z684,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z685,z6]),(0,[z1,z7,z686,z3,z4,z5,z6]),(0,[z326,z1,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z572,z5,z6])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(0,[z57,z1,z7,z93,z4,z5,z6]),(0,[z687,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z154,z4,z127,z5,z6]),(0,[z144,z1,z3,z28,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z6,z103]),(0,[z1,z688,z7,z3,z4,z5,z6]),(0,[z689,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z690,z5,z6]),(0,[z1,z691,z7,z3,z4,z5,z6]),(1,[z1,z430,z3,z4,z5,z6]),(1,[z1,z365,z3,z4,z5,z6])],[(0,[z1,z7,z3,z58,z4,z5,z6]),(0,[z1,z7,z3,z4,z188,z5,z6]),(0,[z1,z7,z3,z692,z4,z5,z6]),(0,[z1,z7,z3,z4,z693,z5,z6]),(0,[z1,z7,z694,z3,z4,z5,z6])],[(1,[z1,z282,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z116,z242,z6]),(0,[z15,z1,z3,z4,z5,z6,z201]),(0,[z43,z1,z7,z3,z5,z225,z6]),(1,[z1,z7,z3,z4,z5,z349]),(0,[z695,z1,z7,z3,z4,z5,z6])],[(0,[z1,z696,z7,z3,z4,z5,z6]),(0,[z129,z1,z7,z3,z4,z6,z201]),(0,[z15,z1,z3,z4,z5,z46,z6])],[(0,[z1,z7,z3,z4,z5,z697,z6]),(0,[z135,z1,z84,z3,z4,z5,z6]),(0,[z1,z181,z7,z3,z4,z5,z6])],[(0,[z135,z1,z7,z3,z127,z5,z6]),(0,[z1,z7,z3,z4,z698,z5,z6]),(0,[z1,z7,z3,z4,z699,z5,z6]),(0,[z700,z1,z7,z3,z4,z5,z6]),(0,[z701,z1,z7,z3,z4,z5,z6]),(0,[z51,z1,z7,z3,z4,z231,z6]),(0,[z1,z7,z3,z4,z62,z5,z6]),(0,[z486,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z702,z5,z6]),(0,[z30,z1,z7,z3,z115,z5,z6]),(1,[z267,z7,z3,z4,z5,z6]),(0,[z1,z7,z703,z3,z4,z5,z6])],[(0,[z330,z1,z7,z3,z4,z5,z6]),(1,[z129,z7,z3,z4,z188,z6]),(0,[z1,z7,z3,z4,z704,z5,z6]),(0,[z486,z1,z3,z4,z5,z96,z6]),(0,[z705,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z589,z6]),(0,[z1,z7,z3,z62,z5,z96,z6])],[(0,[z517,z15,z1,z3,z4,z5,z6]),(0,[z518,z15,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z238,z5,z6]),(0,[z706,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z121,z4,z5,z6]),(0,[z266,z1,z7,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z15,z1,z3,z618,z5,z6]),(0,[z1,z707,z3,z4,z5,z6]),(0,[z1,z413,z134,z4,z5,z6])],[(0,[z57,z7,z58,z4,z14,z6]),(0,[z22,z1,z3,z76,z5,z6])],[(0,[z1,z3,z708,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z6]),(0,[z15,z1,z3,z426,z5,z6]),(0,[z1,z3,z5,z6,z709,z33]),(0,[z710,z1,z3,z4,z5,z6])],[(0,[z1,z498,z3,z97,z5,z6]),(0,[z1,z3,z28,z4,z5,z711])],[(0,[z1,z712,z3,z4,z5,z6]),(0,[z1,z7,z3,z64,z14,z6]),(0,[z1,z7,z3,z713,z5,z6]),(0,[z15,z1,z3,z162,z5,z6]),(0,[z1,z7,z3,z4,z714,z6]),(0,[z102,z1,z3,z4,z715,z6]),(0,[z1,z3,z4,z5,z716,z6]),(0,[z1,z7,z3,z4,z171,z484]),(0,[z1,z7,z3,z5,z6,z717])],[(0,[z123,z79,z161,z3,z5,z6]),(0,[z1,z718,z3,z4,z5,z6]),(0,[z1,z719,z3,z4,z5,z6]),(0,[z1,z7,z3,z720,z5,z6]),(0,[z1,z3,z721,z76,z5,z6]),(0,[z15,z1,z3,z626,z5,z6]),(0,[z1,z42,z7,z3,z5,z108])],[(0,[z172,z7,z3,z127,z5,z6]),(0,[z15,z1,z3,z45,z5,z33]),(0,[z447,z1,z3,z28,z5,z6]),(0,[z1,z3,z337,z233,z5,z6])],[(0,[z15,z113,z41,z3,z5,z6]),(0,[z1,z7,z3,z4,z722,z6]),(0,[z723,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z724,z5,z6]),(0,[z75,z1,z134,z4,z5,z6]),(0,[z1,z3,z4,z5,z725,z6]),(0,[z51,z441,z7,z4,z5,z39]),(0,[z101,z1,z3,z255,z96,z6])]],
   [[(0,[z1,z7,z3,z4,z726,z6]),(0,[z1,z7,z3,z4,z5,z727]),(0,[z131,z1,z3,z4,z5,z6]),(0,[z1,z3,z160,z4,z107,z6])],[(0,[z1,z7,z3,z728,z5,z6]),(0,[z1,z7,z3,z97,z109,z6]),(0,[z15,z1,z3,z4,z109,z6]),(0,[z102,z1,z3,z4,z262,z6]),(0,[z1,z3,z28,z5,z590,z6])],[(0,[z1,z7,z3,z4,z729,z6]),(0,[z7,z3,z4,z5,z6,z177]),(0,[z1,z7,z382,z4,z116,z6]),(0,[z7,z3,z4,z317,z6,z217]),(0,[z1,z3,z4,z5,z459,z103]),(0,[z441,z7,z3,z315,z5,z6]),(0,[z1,z730,z3,z4,z5,z6])],[(0,[z1,z7,z3,z97,z14,z6]),(0,[z1,z7,z3,z4,z731,z6]),(0,[z1,z181,z3,z4,z5,z6]),(0,[z1,z3,z134,z18,z5,z6]),(0,[z1,z7,z732,z4,z5,z6])],[(0,[z1,z7,z3,z733,z5,z6]),(0,[z98,z7,z3,z4,z5,z734]),(0,[z15,z1,z3,z45,z5,z6]),(0,[z1,z7,z3,z5,z6,z187])],[(0,[z1,z7,z3,z4,z5,z735]),(0,[z1,z7,z3,z4,z5,z736]),(0,[z7,z3,z369,z4,z242,z6]),(0,[z15,z1,z3,z4,z5,z737]),(0,[z738,z1,z3,z4,z5,z6]),(0,[z34,z3,z4,z5,z225,z6]),(0,[z1,z7,z585,z4,z116,z6]),(0,[z149,z1,z7,z3,z5,z33])],[(0,[z1,z7,z3,z4,z5,z739]),(0,[z7,z3,z4,z188,z5,z289]),(0,[z57,z15,z58,z4,z5,z6]),(0,[z740,z1,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z741]),(0,[z15,z1,z3,z612,z5,z6]),(0,[z104,z7,z3,z4,z5,z349]),(0,[z1,z7,z3,z4,z117,z210])],[(0,[z123,z34,z7,z3,z5,z6]),(0,[z1,z3,z28,z4,z109,z6]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z7,z72,z95,z5,z6]),(0,[z339,z1,z7,z76,z5,z6]),(0,[z743,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z744])]],
   [[(0,[z1,z3,z745,z4,z5,z6]),(0,[z1,z7,z3,z746,z5,z6]),(0,[z1,z7,z3,z4,z5,z747]),(0,[z106,z1,z7,z3,z5,z744])],[(0,[z1,z7,z3,z4,z748,z6]),(0,[z1,z3,z28,z4,z14,z6]),(0,[z7,z93,z749,z4,z5,z6]),(0,[z15,z1,z3,z481,z5,z6]),(0,[z1,z750,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z751,z6]),(0,[z1,z7,z752,z4,z5,z6]),(0,[z753,z7,z3,z4,z5,z6]),(0,[z598,z1,z7,z76,z5,z6]),(0,[z1,z7,z3,z4,z5,z754])],[(0,[z1,z7,z3,z4,z755,z6]),(0,[z129,z7,z3,z4,z81,z6]),(0,[z15,z98,z3,z4,z5,z99]),(0,[z0,z34,z3,z4,z5,z6]),(0,[z1,z7,z3,z756,z5,z6]),(0,[z757,z7,z3,z4,z5,z6]),(0,[z1,z181,z3,z495,z5,z6]),(0,[z1,z3,z4,z5,z6,z758])],[(0,[z411,z2,z3,z4,z5,z6]),(0,[z1,z759,z3,z4,z5,z6]),(0,[z1,z760,z3,z4,z5,z6]),(0,[z15,z1,z3,z76,z5,z6]),(0,[z1,z31,z3,z77,z5,z6]),(0,[z51,z52,z7,z4,z5,z39])],[(0,[z104,z7,z3,z4,z5,z6]),(0,[z1,z761,z3,z4,z5,z6]),(0,[z762,z1,z3,z4,z5,z6]),(0,[z1,z763,z3,z4,z5,z6]),(0,[z738,z1,z3,z495,z5,z6])],[(0,[z712,z7,z3,z4,z5,z6]),(0,[z52,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z189]),(0,[z15,z41,z3,z45,z5,z6]),(0,[z475,z3,z28,z4,z5,z6]),(0,[z1,z72,z121,z95,z5,z6]),(0,[z1,z3,z764,z4,z5,z6]),(0,[z1,z3,z4,z5,z765,z6]),(0,[z1,z7,z3,z61,z766,z6])],[(0,[z1,z7,z3,z4,z767,z5]),(0,[z144,z7,z3,z4,z6,z354]),(0,[z1,z7,z3,z4,z227,z201]),(0,[z1,z3,z4,z5,z768,z6]),(0,[z51,z1,z7,z4,z405,z39]),(0,[z1,z3,z45,z5,z46,z396])],[(0,[z15,z113,z34,z3,z5,z6]),(0,[z1,z769,z3,z4,z5,z6]),(0,[z1,z7,z770,z4,z5,z6]),(0,[z1,z230,z3,z4,z5,z6]),(0,[z41,z34,z3,z4,z5,z6]),(0,[z1,z7,z3,z771,z5,z6]),(0,[z1,z772,z3,z4,z5,z6]),(0,[z1,z7,z3,z495,z405,z6]),(0,[z7,z3,z4,z5,z773,z6])]],
   [[(0,[z1,z7,z3,z774,z5,z6]),(0,[z775,z1,z25,z3,z5,z6]),(0,[z15,z776,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z777]),(0,[z266,z778,z3,z4,z5,z6])],[(0,[z1,z42,z316,z3,z5,z6]),(0,[z7,z3,z154,z779,z5,z6]),(0,[z1,z7,z3,z4,z5,z205]),(0,[z1,z7,z3,z4,z751,z6]),(0,[z15,z1,z3,z640,z5,z6]),(0,[z1,z780,z3,z4,z5,z6]),(0,[z1,z781,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z782,z6]),(0,[z1,z3,z4,z5,z783,z6]),(0,[z1,z7,z3,z4,z5,z784]),(0,[z1,z7,z3,z785,z5,z6]),(0,[z1,z7,z3,z5,z6,z786]),(0,[z787,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z158,z38])],[(0,[z256,z1,z134,z4,z5,z6]),(0,[z1,z788,z3,z4,z5,z6]),(0,[z149,z15,z1,z3,z5,z6]),(0,[z1,z3,z4,z5,z789,z103]),(0,[z367,z1,z7,z3,z96,z6])],[(0,[z15,z41,z3,z76,z5,z6]),(0,[z1,z430,z3,z4,z5,z6]),(0,[z1,z365,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z140,z6]),(0,[z1,z7,z4,z790,z5,z6]),(0,[z1,z31,z3,z115,z5,z6])],[(0,[z791,z1,z7,z3,z4,z5]),(0,[z211,z7,z3,z4,z5,z217]),(0,[z34,z3,z134,z4,z5,z6]),(0,[z15,z34,z3,z45,z5,z6]),(0,[z15,z1,z3,z503,z5,z6]),(0,[z15,z1,z3,z4,z5,z108]),(0,[z1,z7,z3,z792,z5,z6])],[(0,[z492,z7,z3,z4,z242,z6]),(0,[z1,z3,z793,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z794]),(1,[z1,z7,z3,z766,z6])],[(0,[z1,z7,z3,z4,z109,z289]),(0,[z1,z27,z3,z18,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z795]),(0,[z333,z7,z58,z4,z5,z6]),(0,[z16,z7,z3,z4,z5,z734]),(0,[z1,z3,z4,z5,z255,z6])],[(1,[z712,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z14,z289]),(0,[z15,z135,z41,z3,z5,z6]),(0,[z144,z7,z3,z4,z751,z6]),(0,[z15,z796,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z6,z509])],[(0,[z797,z1,z3,z4,z5,z6])],[(0,[z267,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z721,z5,z6]),(0,[z15,z1,z3,z5,z356,z6]),(0,[z1,z3,z28,z4,z5,z108]),(0,[z1,z3,z798,z495,z5,z6]),(0,[z1,z3,z4,z5,z6,z799])],[(0,[z24,z1,z3,z95,z5,z6]),(0,[z1,z7,z3,z800,z5,z6]),(0,[z419,z34,z3,z4,z5,z6]),(0,[z15,z34,z3,z76,z5,z6]),(0,[z15,z1,z199,z95,z5,z6]),(0,[z486,z1,z3,z95,z5,z6])],[(0,[z1,z7,z3,z790,z5,z6]),(0,[z104,z7,z3,z77,z5,z6]),(0,[z267,z7,z3,z4,z171,z6]),(0,[z801,z1,z3,z4,z5,z6])],[(0,[z1,z7,z3,z802,z5,z6]),(0,[z803,z1,z3,z4,z5,z6]),(0,[z1,z7,z334,z4,z5,z245]),(0,[z776,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z519,z5,z6]),(0,[z804,z1,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z805]),(0,[z560,z1,z7,z3,z4,z201]),(0,[z806,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z807]),(0,[z98,z1,z7,z3,z4,z184]),(0,[z15,z1,z3,z5,z6,z410]),(0,[z607,z1,z7,z3,z5,z33]),(0,[z1,z3,z4,z5,z808,z6])]],
   [[(0,[z113,z3,z83,z127,z5,z6]),(0,[z775,z1,z3,z4,z5,z6]),(1,[z809,z1,z3,z5,z6]),(0,[z15,z123,z34,z3,z5,z6]),(0,[z22,z1,z3,z4,z5,z6]),(0,[z1,z810,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z811])],[(0,[z57,z282,z58,z4,z5,z6]),(0,[z1,z3,z28,z5,z356,z6])],[(0,[z1,z3,z812,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z813]),(0,[z475,z7,z3,z4,z117,z6]),(0,[z1,z814,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z815]),(0,[z1,z7,z3,z816,z5,z6]),(0,[z1,z7,z285,z4,z5,z815])],[(0,[z1,z7,z3,z5,z817,z6]),(0,[z1,z7,z3,z818,z5,z6]),(0,[z90,z131,z1,z76,z5,z6]),(0,[z819,z7,z3,z4,z5,z6]),(0,[z1,z820,z3,z4,z5,z6])],[(0,[z1,z282,z3,z64,z5,z6]),(0,[z821,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z822,z6]),(0,[z1,z3,z823,z4,z5,z6]),(0,[z15,z454,z1,z3,z5,z6]),(0,[z7,z3,z4,z5,z824,z6])],[(0,[z43,z1,z161,z3,z5,z6]),(0,[z1,z7,z463,z95,z5,z6]),(0,[z1,z7,z3,z4,z5,z734]),(0,[z15,z1,z3,z251,z5,z6]),(0,[z43,z1,z7,z3,z5,z6]),(0,[z825,z1,z3,z4,z5,z6]),(0,[z826,z7,z3,z4,z5,z6]),(0,[z101,z1,z7,z3,z96,z108]),(0,[z1,z7,z3,z45,z5,z46])],[(0,[z166,z1,z7,z76,z5,z6]),(0,[z827,z7,z3,z4,z5,z6]),(0,[z104,z7,z3,z115,z5,z6]),(0,[z1,z3,z4,z828,z5,z6])],[(0,[z1,z7,z3,z829,z4,z6]),(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z831,z6]),(0,[z1,z7,z477,z95,z5,z6]),(0,[z1,z169,z3,z4,z5,z210]),(0,[z1,z7,z3,z4,z6,z832]),(0,[z1,z7,z3,z4,z171,z832])]],
   [[(0,[z15,z1,z3,z572,z5,z6]),(0,[z1,z7,z3,z77,z5,z349]),(0,[z7,z3,z4,z5,z6,z833])],[(0,[z15,z135,z34,z3,z5,z6]),(0,[z34,z27,z3,z4,z5,z6]),(0,[z15,z834,z3,z4,z5,z6]),(0,[z15,z835,z3,z4,z5,z6]),(0,[z1,z285,z28,z4,z5,z245])],[(0,[z229,z15,z1,z3,z5,z6]),(0,[z7,z3,z4,z5,z205,z217]),(0,[z1,z3,z836,z4,z5,z6]),(0,[z1,z3,z4,z5,z140,z6]),(0,[z1,z413,z162,z4,z5,z6]),(0,[z1,z181,z3,z4,z231,z6])],[(0,[z1,z7,z3,z837,z5,z6]),(0,[z1,z282,z3,z97,z5,z6]),(0,[z838,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z839,z5,z6]),(0,[z15,z1,z3,z5,z38,z33]),(0,[z1,z840,z3,z4,z5,z6]),(0,[z30,z104,z7,z4,z117,z6])],[(0,[z1,z316,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z6,z547]),(0,[z1,z7,z3,z841,z5,z6]),(0,[z15,z1,z3,z5,z6,z549]),(0,[z1,z842,z3,z4,z5,z6])],[(0,[z675,z15,z1,z3,z5,z6]),(0,[z15,z129,z3,z4,z188,z6]),(0,[z843,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z6,z709]),(0,[z1,z74,z3,z4,z715,z6]),(0,[z844,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z845,z5,z6]),(0,[z525,z7,z3,z154,z5,z6]),(1,[z7,z3,z4,z751,z6]),(0,[z390,z34,z3,z4,z5,z6]),(0,[z15,z267,z3,z4,z5,z6]),(0,[z846,z7,z3,z4,z5,z6])],[(0,[z288,z84,z3,z4,z5,z6]),(0,[z1,z847,z3,z4,z5,z6]),(0,[z15,z1,z3,z62,z5,z6]),(0,[z15,z1,z3,z5,z6,z556]),(0,[z15,z1,z285,z4,z5,z245]),(0,[z51,z1,z28,z4,z5,z39])]],
   [[(0,[z41,z3,z28,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z848]),(0,[z1,z3,z4,z5,z849,z6])],[(0,[z92,z7,z93,z4,z5,z6]),(0,[z15,z1,z3,z656,z5,z6]),(0,[z1,z27,z17,z105,z5,z6]),(0,[z1,z3,z4,z721,z5,z6])],[(0,[z15,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z850,z5,z6]),(0,[z1,z3,z851,z4,z5,z6]),(0,[z15,z323,z1,z3,z5,z6]),(0,[z390,z1,z3,z4,z219,z6]),(0,[z1,z3,z28,z4,z5,z349]),(0,[z1,z7,z3,z4,z5,z852]),(0,[z441,z7,z3,z495,z5,z6]),(0,[z7,z3,z4,z5,z177,z39])],[(0,[z1,z853,z3,z4,z5,z6]),(0,[z98,z7,z3,z4,z5,z205]),(0,[z16,z1,z7,z3,z4,z184]),(0,[z330,z41,z3,z4,z5,z6]),(0,[z15,z695,z1,z3,z5,z6]),(0,[z15,z1,z3,z238,z5,z6])],[(0,[z1,z7,z3,z854,z5,z6]),(0,[z1,z855,z3,z4,z5,z6]),(0,[z1,z7,z3,z105,z5,z6]),(0,[z1,z7,z3,z4,z5,z856]),(0,[z1,z3,z4,z5,z6,z857]),(0,[z101,z486,z1,z3,z5,z6])],[(0,[z57,z7,z58,z4,z5,z150]),(0,[z43,z1,z3,z134,z5,z6]),(0,[z1,z3,z162,z18,z5,z6]),(0,[z15,z858,z3,z4,z5,z6])],[(0,[z57,z7,z58,z64,z5,z6]),(0,[z1,z3,z4,z859,z5,z6]),(0,[z75,z1,z752,z4,z5,z6]),(0,[z90,z1,z7,z76,z5,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z52,z181,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z543]),(0,[z57,z58,z28,z4,z5,z6]),(0,[z135,z84,z3,z154,z5,z6])]],
   [[(0,[z1,z3,z28,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z861]),(0,[z15,z827,z3,z4,z5,z6]),(0,[z862,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z863]),(0,[z804,z1,z3,z115,z5,z6])],[(0,[z1,z7,z3,z4,z317,z6]),(0,[z1,z7,z3,z4,z864,z6]),(0,[z15,z1,z3,z495,z5,z6]),(0,[z1,z7,z3,z5,z46,z744])],[(0,[z7,z3,z4,z188,z609,z6]),(0,[z1,z865,z25,z3,z5,z6]),(0,[z7,z3,z4,z751,z242,z6]),(0,[z15,z1,z3,z5,z6,z581])],[(0,[z1,z7,z3,z4,z866,z6]),(0,[z113,z34,z7,z3,z5,z6]),(0,[z7,z3,z4,z171,z38,z177])],[(0,[z24,z161,z3,z4,z5,z6]),(0,[z867,z7,z3,z4,z5,z6]),(0,[z1,z42,z3,z252,z5,z6]),(0,[z1,z3,z4,z273,z589,z6])],[(0,[z57,z7,z58,z97,z5,z6]),(0,[z15,z1,z3,z4,z868,z6]),(0,[z1,z3,z869,z4,z5,z6]),(1,[z1,z7,z3,z4,z832])],[(0,[z288,z123,z1,z3,z5,z6]),(0,[z16,z7,z3,z4,z5,z217])],[(0,[z1,z7,z3,z97,z5,z150]),(0,[z15,z1,z3,z4,z5,z150]),(0,[z439,z15,z1,z3,z5,z6]),(0,[z7,z3,z4,z779,z5,z6]),(0,[z667,z1,z3,z4,z5,z103]),(0,[z367,z15,z1,z3,z5,z6]),(0,[z1,z3,z28,z495,z5,z6]),(0,[z30,z1,z7,z4,z117,z210]),(0,[z1,z7,z3,z62,z766,z6])]],
   [[(0,[z1,z7,z3,z870,z5,z6]),(0,[z15,z34,z3,z62,z5,z6]),(0,[z1,z7,z3,z4,z5,z871]),(0,[z51,z1,z181,z4,z5,z39]),(0,[z1,z3,z4,z872,z5,z6])],[(0,[z92,z7,z3,z4,z5,z289]),(0,[z1,z7,z3,z873,z5,z6]),(0,[z874,z1,z7,z3,z5,z6]),(0,[z875,z1,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z876,z6]),(0,[z144,z3,z28,z4,z242,z6]),(1,[z7,z3,z4,z5,z734]),(0,[z877,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z878]),(0,[z15,z1,z3,z28,z5,z6]),(0,[z52,z230,z3,z4,z5,z6]),(0,[z101,z1,z7,z3,z96,z6]),(0,[z1,z7,z3,z4,z766,z6]),(0,[z1,z3,z4,z5,z879,z6]),(0,[z1,z7,z3,z5,z744,z33])],[(0,[z57,z7,z749,z4,z5,z6]),(0,[z98,z7,z3,z4,z5,z196]),(0,[z144,z7,z3,z4,z480,z6]),(0,[z858,z7,z3,z4,z5,z6]),(0,[z15,z34,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z709]),(0,[z15,z1,z3,z880,z5,z6]),(0,[z1,z42,z3,z5,z6,z202]),(0,[z1,z7,z3,z881,z5,z6]),(0,[z1,z7,z265,z95,z5,z6]),(0,[z475,z169,z3,z4,z5,z6])],[(0,[z92,z93,z28,z4,z5,z6]),(0,[z15,z882,z3,z4,z5,z6]),(0,[z15,z34,z3,z238,z5,z6])],[(0,[z1,z3,z28,z4,z5,z150]),(0,[z1,z7,z3,z883,z5,z6]),(0,[z1,z74,z3,z4,z610,z6]),(0,[z1,z7,z3,z62,z501,z6]),(0,[z884,z7,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z14,z6]),(0,[z1,z17,z752,z4,z5,z6]),(0,[z15,z1,z3,z61,z62,z6]),(0,[z30,z1,z7,z4,z885,z6]),(0,[z1,z886,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z245,z815])],[(0,[z1,z7,z3,z4,z6,z184]),(0,[z34,z3,z28,z4,z5,z6]),(0,[z1,z3,z61,z62,z140,z6])]],
   [[(0,[z1,z7,z3,z4,z887,z6]),(0,[z374,z161,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z289]),(0,[z24,z1,z3,z76,z5,z6]),(0,[z1,z7,z3,z888,z5,z6]),(0,[z1,z7,z3,z4,z889,z6]),(0,[z1,z7,z3,z890,z5,z6]),(0,[z1,z7,z3,z4,z405,z245])],[(0,[z712,z161,z3,z4,z5,z6]),(0,[z123,z1,z3,z134,z5,z6]),(0,[z7,z3,z58,z4,z5,z289]),(0,[z834,z7,z3,z4,z5,z6]),(0,[z1,z3,z28,z880,z5,z6])],[(0,[z1,z7,z3,z891,z5,z6])],[(0,[z892,z1,z3,z4,z5,z6]),(0,[z649,z1,z134,z4,z5,z6]),(0,[z15,z635,z1,z3,z5,z6]),(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z405,z6])],[(0,[z79,z208,z161,z3,z5,z6]),(0,[z1,z7,z3,z894,z5,z6]),(0,[z15,z1,z686,z3,z5,z6]),(0,[z7,z3,z692,z4,z5,z217]),(0,[z1,z7,z3,z895,z5,z6]),(0,[z15,z1,z3,z233,z5,z6]),(0,[z1,z3,z28,z61,z62,z6]),(0,[z106,z1,z7,z3,z5,z33])],[(0,[z1,z27,z249,z4,z5,z6]),(0,[z15,z1,z3,z122,z5,z6]),(0,[z1,z3,z896,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z897]),(0,[z15,z1,z3,z4,z171,z38]),(0,[z267,z7,z3,z4,z6,z201])],[(0,[z1,z3,z4,z5,z898,z6]),(0,[z1,z3,z4,z899,z5,z6]),(0,[z129,z7,z3,z4,z188,z189]),(0,[z1,z7,z3,z4,z5,z900])]],
   [[(0,[z144,z7,z3,z4,z5,z289]),(0,[z57,z7,z369,z4,z5,z6]),(0,[z267,z7,z3,z4,z188,z6]),(0,[z1,z3,z28,z4,z5,z901]),(0,[z1,z7,z3,z4,z885,z6])],[(0,[z43,z1,z2,z3,z5,z6]),(0,[z101,z15,z1,z3,z5,z108]),(0,[z298,z1,z3,z4,z589,z6])],[(0,[z113,z24,z3,z127,z5,z6]),(0,[z1,z7,z3,z4,z902,z6]),(0,[z98,z429,z3,z4,z5,z99]),(0,[z903,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z232,z5,z6]),(0,[z1,z3,z28,z115,z5,z6]),(0,[z1,z3,z28,z233,z5,z6]),(0,[z441,z7,z3,z4,z231,z6]),(0,[z1,z7,z3,z315,z231,z6])],[(0,[z123,z79,z1,z3,z5,z6]),(0,[z657,z2,z3,z4,z5,z6]),(0,[z135,z904,z1,z3,z5,z6]),(0,[z129,z7,z3,z4,z188,z205]),(0,[z15,z34,z3,z28,z5,z6]),(0,[z34,z7,z3,z95,z5,z6]),(0,[z1,z7,z3,z4,z116,z210]),(0,[z101,z486,z1,z3,z96,z6]),(0,[z1,z905,z3,z4,z5,z6])],[(0,[z1,z498,z3,z4,z5,z289]),(0,[z1,z7,z3,z4,z669,z38]),(0,[z434,z1,z3,z28,z5,z6]),(0,[z1,z3,z28,z4,z171,z38])],[(0,[z1,z221,z3,z4,z5,z6]),(0,[z906,z1,z7,z3,z4,z6]),(0,[z1,z907,z3,z4,z5,z6]),(0,[z1,z3,z908,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z909]),(0,[z15,z1,z3,z5,z155,z6]),(0,[z1,z3,z4,z107,z225,z6]),(0,[z1,z910,z3,z4,z5,z6])],[(0,[z79,z712,z3,z4,z5,z6]),(0,[z911,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z912,z5,z6]),(0,[z1,z913,z3,z4,z5,z6]),(0,[z1,z914,z3,z4,z5,z6])],[(0,[z1,z3,z915,z4,z5,z6]),(0,[z1,z3,z798,z4,z5,z6]),(0,[z916,z1,z3,z4,z5,z6]),(0,[z51,z1,z7,z4,z5,z815]),(0,[z917,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z918,z3,z4,z5,z6]),(0,[z15,z113,z3,z127,z5,z6]),(0,[z129,z1,z7,z3,z4,z189]),(0,[z1,z3,z919,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z789]),(0,[z920,z1,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z921]),(0,[z98,z7,z3,z4,z5,z114]),(0,[z298,z15,z1,z3,z5,z6]),(0,[z15,z1,z3,z4,z231,z6]),(0,[z922,z7,z3,z4,z5,z6]),(0,[z1,z7,z790,z76,z5,z6])],[(0,[z1,z7,z3,z4,z5,z923]),(0,[z135,z7,z3,z154,z5,z6]),(0,[z1,z924,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z925]),(0,[z7,z3,z4,z5,z734,z217]),(0,[z1,z7,z3,z4,z5,z711]),(0,[z15,z43,z1,z3,z5,z6]),(0,[z51,z1,z7,z4,z5,z39])],[(0,[z1,z926,z3,z4,z5,z6]),(0,[z15,z144,z3,z4,z242,z6]),(0,[z1,z3,z4,z5,z6,z927]),(0,[z98,z7,z3,z4,z317,z6]),(0,[z30,z1,z28,z4,z117,z6])],[(0,[z123,z1,z3,z5,z225,z6]),(0,[z1,z7,z3,z928,z5,z6]),(0,[z15,z1,z3,z337,z5,z6]),(0,[z15,z929,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z6,z187]),(0,[z1,z930,z3,z4,z5,z6])],[(0,[z1,z931,z88,z3,z5,z6]),(0,[z436,z1,z4,z572,z5,z6]),(0,[z106,z22,z1,z3,z5,z33])],[(0,[z562,z15,z1,z3,z5,z6]),(0,[z1,z932,z3,z4,z5,z6]),(0,[z1,z3,z933,z4,z5,z6]),(0,[z1,z934,z3,z4,z5,z6]),(0,[z935,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z936,z5,z6]),(0,[z144,z221,z3,z4,z242,z6]),(0,[z1,z7,z3,z4,z5,z937]),(0,[z1,z3,z28,z4,z231,z6]),(0,[z1,z7,z3,z5,z6,z938]),(0,[z1,z3,z4,z5,z6,z939]),(0,[z1,z365,z3,z45,z5,z46])]],
   [[(0,[z15,z92,z93,z4,z5,z6]),(0,[z185,z1,z3,z4,z225,z6])],[(0,[z15,z1,z208,z3,z5,z6]),(0,[z1,z3,z28,z653,z5,z6]),(0,[z135,z34,z7,z3,z5,z6]),(0,[z1,z7,z3,z940,z5,z6]),(0,[z1,z3,z4,z5,z941,z6]),(0,[z942,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z663,z5,z6]),(0,[z43,z102,z1,z3,z5,z6]),(0,[z51,z1,z7,z495,z5,z39])],[(0,[z15,z135,z161,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z943]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z945,z7,z3,z4,z5,z6]),(0,[z15,z476,z1,z3,z5,z6]),(0,[z1,z3,z28,z5,z6,z187]),(0,[z1,z7,z3,z45,z5,z744])],[(0,[z92,z7,z749,z4,z5,z6]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z947]),(0,[z1,z3,z948,z4,z5,z6])],[(0,[z1,z949,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z950,z6])],[(0,[z1,z7,z3,z951,z5,z6]),(0,[z15,z945,z3,z4,z5,z6]),(0,[z1,z71,z72,z95,z5,z6])],[(0,[z1,z3,z952,z4,z5,z6]),(0,[z953,z7,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z396]),(0,[z1,z7,z3,z45,z5,z302]),(0,[z954,z1,z7,z3,z5,z6])]],
   [[(0,[z1,z955,z3,z4,z5,z6]),(0,[z1,z7,z3,z956,z5,z6]),(0,[z517,z34,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z957,z6]),(0,[z475,z7,z3,z4,z5,z210])],[(0,[z288,z15,z135,z3,z5,z6]),(0,[z7,z3,z4,z188,z14,z6])],[(0,[z1,z7,z749,z4,z5,z6]),(0,[z15,z326,z1,z3,z4,z201]),(0,[z104,z3,z28,z4,z5,z6])],[(0,[z775,z144,z1,z3,z5,z6]),(0,[z52,z3,z28,z4,z5,z6]),(0,[z958,z7,z3,z4,z5,z6])],[(0,[z123,z0,z1,z3,z5,z6]),(0,[z113,z3,z28,z127,z5,z6]),(0,[z41,z84,z3,z4,z5,z6]),(0,[z809,z1,z3,z4,z5,z6]),(0,[z1,z3,z959,z4,z5,z6]),(0,[z1,z3,z960,z4,z5,z6]),(0,[z1,z7,z3,z4,z38,z832])],[(0,[z1,z7,z3,z4,z6,z961]),(0,[z1,z962,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z39,z184]),(0,[z1,z27,z180,z4,z5,z6]),(0,[z15,z266,z3,z4,z5,z6]),(0,[z1,z3,z963,z4,z5,z6])],[(0,[z441,z7,z3,z4,z5,z6]),(0,[z1,z169,z3,z4,z5,z6]),(0,[z101,z15,z1,z3,z5,z6]),(0,[z1,z74,z3,z4,z273,z6]),(0,[z1,z7,z3,z315,z5,z6]),(0,[z1,z964,z3,z4,z5,z6])],[(0,[z24,z1,z3,z4,z5,z6]),(0,[z15,z1,z327,z95,z5,z6]),(0,[z15,z1,z3,z4,z5,z349]),(0,[z102,z1,z3,z4,z225,z6]),(1,[z1,z3,z4,z715,z6]),(0,[z475,z7,z3,z4,z116,z6])]],
   [[(0,[z79,z161,z3,z4,z5,z6]),(0,[z123,z1,z27,z3,z5,z6]),(0,[z965,z1,z7,z3,z5,z6]),(0,[z966,z1,z7,z3,z5,z6]),(0,[z15,z113,z135,z3,z5,z6]),(0,[z29,z3,z363,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z210]),(0,[z967,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z968,z6]),(0,[z15,z1,z316,z3,z5,z6]),(0,[z1,z778,z3,z4,z5,z6])],[(0,[z1,z969,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z970,z6]),(0,[z15,z1,z3,z699,z5,z6]),(0,[z326,z1,z7,z3,z4,z201]),(0,[z1,z3,z4,z5,z6,z971])],[(0,[z1,z7,z3,z4,z972,z6]),(0,[z1,z7,z3,z232,z5,z46])],[(0,[z288,z712,z3,z4,z5,z6]),(0,[z973,z7,z3,z4,z5,z6]),(0,[z34,z3,z4,z5,z130,z6]),(0,[z101,z1,z7,z3,z262,z6]),(0,[z15,z1,z3,z704,z5,z6]),(0,[z1,z974,z3,z4,z5,z6]),(0,[z1,z7,z3,z766,z96,z6]),(0,[z1,z7,z3,z5,z766,z6])],[(0,[z1,z975,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z245,z177])],[(0,[z1,z7,z3,z976,z5,z6])],[(0,[z1,z208,z3,z28,z5,z6]),(0,[z1,z3,z28,z402,z5,z6]),(0,[z1,z7,z3,z977,z5,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z147,z34,z3,z4,z5,z6]),(0,[z15,z1,z3,z9,z5,z6]),(0,[z15,z1,z3,z5,z12,z6]),(0,[z1,z7,z3,z45,z5,z130]),(1,[z1,z3,z880,z5,z6]),(0,[z1,z3,z4,z273,z715,z6]),(0,[z0,z1,z3,z4,z5,z789]),(0,[z979,z7,z3,z4,z5,z6]),(0,[z1,z3,z980,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z981,z5,z6]),(0,[z15,z1,z3,z19,z5,z6])],[(0,[z15,z687,z1,z3,z5,z6]),(0,[z1,z7,z3,z779,z5,z6]),(1,[z775,z1,z3,z5,z6]),(0,[z266,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z982]),(0,[z983,z1,z7,z3,z5,z6]),(0,[z267,z3,z28,z4,z5,z6]),(0,[z1,z7,z4,z5,z885,z6]),(0,[z1,z984,z3,z4,z5,z6])],[(0,[z129,z3,z28,z4,z188,z6]),(0,[z1,z7,z3,z4,z5,z108])],[(0,[z288,z2,z3,z4,z5,z6]),(0,[z123,z1,z3,z28,z5,z6]),(0,[z1,z3,z985,z4,z5,z6]),(0,[z15,z41,z3,z62,z5,z6]),(0,[z266,z7,z3,z4,z171,z6])],[(0,[z1,z7,z3,z986,z5,z6]),(0,[z1,z7,z3,z4,z5,z987]),(0,[z1,z7,z3,z4,z171,z114]),(0,[z15,z1,z3,z4,z822,z6]),(0,[z229,z3,z4,z534,z5,z6]),(0,[z1,z3,z4,z5,z6,z988])],[(0,[z1,z7,z3,z4,z5,z989]),(0,[z15,z1,z3,z468,z5,z6]),(0,[z990,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z293,z5,z6]),(0,[z15,z1,z3,z45,z5,z46]),(0,[z43,z1,z3,z273,z5,z6]),(0,[z1,z991,z3,z4,z5,z6])],[(0,[z15,z41,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z53]),(0,[z1,z7,z992,z4,z5,z6]),(0,[z1,z7,z3,z4,z993,z6]),(0,[z52,z7,z3,z4,z405,z6])],[(0,[z34,z7,z3,z76,z5,z6]),(0,[z15,z41,z3,z238,z5,z6]),(0,[z1,z3,z28,z4,z5,z994]),(0,[z995,z7,z3,z4,z5,z6]),(0,[z30,z7,z4,z50,z117,z6])]],
   [[(0,[z1,z996,z3,z4,z5,z6]),(0,[z24,z34,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z789]),(0,[z1,z230,z3,z4,z405,z6])],[(0,[z1,z7,z3,z997,z5,z6]),(0,[z1,z998,z3,z4,z5,z6]),(0,[z111,z1,z3,z4,z262,z6]),(0,[z90,z15,z1,z76,z5,z6]),(0,[z51,z1,z7,z4,z231,z39])],[(0,[z1,z999,z3,z4,z5,z6]),(0,[z15,z1,z3,z565,z5,z6]),(0,[z1,z7,z3,z4,z5,z1000]),(0,[z15,z1,z3,z313,z5,z6]),(0,[z30,z267,z7,z4,z117,z6])],[(0,[z15,z1,z3,z64,z5,z6]),(0,[z1,z7,z3,z4,z1001,z6]),(0,[z1,z3,z28,z45,z5,z46]),(0,[z51,z1,z230,z4,z5,z39])],[(0,[z342,z161,z3,z4,z5,z6]),(0,[z1,z282,z3,z4,z5,z289]),(0,[z1,z3,z1002,z4,z5,z6]),(0,[z1,z1003,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z70,z6]),(0,[z1,z3,z28,z4,z5,z53]),(0,[z7,z3,z4,z5,z6,z1004])],[(0,[z1,z7,z3,z4,z5,z1005]),(0,[z809,z1,z88,z3,z5,z6]),(0,[z1006,z1,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1007]),(0,[z15,z1,z3,z77,z5,z6]),(0,[z30,z1,z7,z4,z117,z6])],[(1,[z7,z749,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1008]),(0,[z1,z3,z1009,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1010]),(0,[z1011,z7,z3,z4,z5,z6])],[(0,[z1,z3,z28,z64,z5,z6]),(0,[z394,z1,z7,z3,z4,z201])],[(0,[z674,z1,z3,z4,z225,z6]),(0,[z1,z7,z3,z1012,z5,z6]),(0,[z15,z1,z3,z97,z5,z6]),(0,[z1,z1013,z3,z4,z5,z6]),(0,[z1,z1014,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1015]),(0,[z22,z1,z3,z95,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1016]),(0,[z229,z15,z41,z3,z5,z6]),(0,[z486,z1,z3,z76,z5,z6]),(0,[z101,z1,z7,z3,z766,z6])],[(0,[z1,z931,z7,z3,z5,z6]),(0,[z1,z3,z121,z4,z5,z6]),(0,[z1,z3,z677,z28,z5,z6]),(0,[z1,z27,z752,z4,z5,z6]),(0,[z15,z1,z3,z105,z5,z6]),(0,[z15,z1,z3,z5,z6,z108]),(0,[z1,z3,z28,z77,z5,z6]),(0,[z1,z3,z4,z715,z225,z6]),(0,[z475,z31,z3,z4,z5,z6]),(0,[z326,z1,z7,z3,z4,z832])],[(0,[z15,z1,z3,z347,z5,z6]),(0,[z101,z15,z1,z3,z96,z6]),(0,[z1017,z7,z3,z4,z5,z6]),(0,[z1,z1018,z3,z4,z5,z6]),(0,[z1019,z1,z3,z4,z5,z6])],[(0,[z7,z749,z58,z4,z5,z6]),(0,[z92,z7,z676,z4,z5,z6]),(0,[z15,z1,z3,z643,z5,z6]),(0,[z1,z7,z1020,z4,z5,z6]),(0,[z15,z41,z3,z28,z5,z6]),(0,[z15,z475,z3,z4,z5,z6]),(0,[z1021,z7,z3,z4,z5,z6]),(0,[z101,z1,z7,z3,z96,z53])],[(0,[z1,z7,z3,z4,z1022,z6]),(0,[z41,z7,z3,z4,z5,z6]),(0,[z1,z25,z3,z4,z5,z6]),(0,[z15,z1023,z3,z4,z5,z6]),(0,[z15,z1,z3,z115,z5,z6]),(0,[z1,z7,z1024,z4,z5,z6]),(0,[z1025,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z28,z97,z5,z6]),(0,[z1,z1026,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z744]),(0,[z1,z1027,z3,z4,z5,z6])],[(0,[z1,z1028,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1029]),(0,[z1,z27,z17,z18,z5,z6])],[(0,[z1,z3,z1030,z4,z5,z6]),(0,[z144,z98,z7,z3,z4,z201]),(0,[z15,z1,z3,z456,z5,z6]),(0,[z15,z16,z3,z4,z5,z217]),(0,[z15,z1,z3,z401,z5,z6]),(0,[z1,z3,z28,z105,z5,z6]),(0,[z1,z3,z337,z4,z5,z459]),(0,[z1,z7,z3,z1031,z5,z6])],[(0,[z98,z7,z3,z4,z5,z99]),(0,[z835,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z1032]),(0,[z1,z7,z3,z4,z5,z210])],[(0,[z1,z7,z3,z18,z5,z6]),(0,[z517,z1,z199,z4,z5,z6]),(0,[z1,z3,z1033,z4,z5,z6]),(0,[z1,z7,z285,z4,z5,z245]),(0,[z1,z7,z3,z110,z4,z201])],[(0,[z1,z7,z3,z4,z6,z1034]),(0,[z135,z7,z3,z402,z5,z6]),(1,[z1,z752,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1035]),(0,[z266,z7,z3,z4,z171,z38])],[(0,[z288,z24,z3,z4,z5,z6]),(0,[z57,z7,z58,z4,z5,z289]),(1,[z7,z3,z779,z5,z6]),(0,[z144,z1,z7,z3,z4,z189]),(0,[z1,z3,z28,z4,z5,z1036])],[(0,[z75,z1,z327,z4,z5,z6]),(0,[z34,z3,z4,z5,z262,z6]),(0,[z15,z1,z3,z4,z714,z6]),(0,[z106,z15,z1,z3,z5,z33]),(0,[z1,z3,z28,z482,z5,z6]),(0,[z1,z181,z3,z315,z5,z6])]],
   [[(0,[z113,z24,z1,z3,z5,z6]),(0,[z15,z135,z3,z154,z5,z6]),(0,[z1,z3,z4,z5,z1037,z6]),(0,[z15,z1,z3,z4,z5,z871]),(0,[z1,z7,z3,z5,z1038,z6])],[(0,[z1,z429,z3,z4,z5,z6]),(0,[z1,z7,z3,z64,z5,z289]),(0,[z1,z7,z3,z4,z5,z1039]),(0,[z144,z25,z3,z4,z242,z6]),(0,[z15,z1,z3,z307,z5,z6]),(0,[z1,z1040,z3,z4,z5,z6])],[(0,[z29,z161,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1041,z6]),(0,[z15,z295,z1,z3,z5,z6]),(0,[z1,z27,z199,z4,z5,z6])],[(0,[z123,z135,z7,z3,z5,z6]),(0,[z1042,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z1043,z5,z6]),(0,[z15,z1,z3,z523,z5,z6]),(0,[z1,z7,z1044,z4,z5,z6]),(0,[z52,z7,z3,z4,z5,z39])],[(0,[z1,z7,z3,z4,z5,z1045]),(0,[z1,z1046,z3,z4,z5,z6]),(0,[z368,z15,z1,z3,z5,z6]),(0,[z1,z3,z4,z880,z5,z6]),(0,[z15,z1,z3,z252,z5,z6])],[(0,[z1,z7,z3,z4,z1047,z6]),(0,[z1,z7,z3,z4,z693,z201]),(0,[z7,z3,z4,z5,z1048,z6])],[(0,[z15,z113,z1,z3,z5,z6]),(0,[z15,z1,z3,z4,z731,z6]),(0,[z15,z1,z732,z4,z5,z6]),(0,[z1,z3,z28,z5,z6,z156]),(0,[z1,z7,z3,z495,z5,z6])],[(0,[z7,z3,z4,z1049,z5,z6]),(0,[z1,z1050,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z6,z184]),(0,[z43,z1,z27,z3,z5,z6]),(0,[z15,z1,z3,z5,z33,z201])]],
   [[(0,[z1,z7,z3,z97,z5,z289]),(0,[z1,z1051,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z289]),(0,[z1,z3,z4,z5,z1052,z6]),(0,[z15,z1,z7,z3,z5,z108]),(0,[z90,z1,z7,z790,z5,z6]),(0,[z104,z169,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z1053,z6]),(0,[z929,z7,z3,z4,z5,z6]),(0,[z52,z7,z3,z315,z5,z6])],[(0,[z1,z282,z3,z4,z109,z6]),(0,[z1054,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1055,z6]),(0,[z144,z7,z3,z4,z679,z6]),(0,[z1056,z1,z3,z4,z5,z6]),(0,[z15,z1,z72,z95,z5,z6]),(0,[z1,z71,z3,z95,z5,z6]),(0,[z1057,z1,z7,z3,z5,z6])],[(0,[z1,z498,z3,z4,z5,z6]),(0,[z892,z1,z3,z97,z5,z6]),(0,[z1,z7,z3,z1058,z5,z6]),(0,[z1059,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z5,z6,z202]),(0,[z441,z230,z3,z4,z5,z6]),(0,[z1,z230,z3,z315,z5,z6]),(0,[z1,z365,z3,z45,z5,z6]),(0,[z1,z7,z3,z4,z550,z38]),(0,[z1060,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z1061,z5,z6])],[(0,[z92,z7,z3,z4,z14,z6]),(0,[z7,z3,z4,z5,z205,z177]),(0,[z15,z1,z3,z664,z5,z6]),(0,[z1062,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z77,z5,z210])],[(0,[z1,z3,z28,z4,z6,z184]),(0,[z51,z15,z1,z4,z5,z39]),(0,[z1063,z1,z3,z4,z5,z6])],[(0,[z34,z7,z3,z4,z5,z6]),(0,[z1,z208,z316,z3,z5,z6]),(0,[z1,z3,z28,z4,z5,z289]),(0,[z98,z88,z3,z4,z5,z99]),(0,[z15,z1,z3,z5,z725,z6])],[(0,[z1,z3,z1030,z97,z5,z6]),(0,[z264,z7,z3,z4,z188,z6]),(0,[z1,z3,z880,z238,z5,z6]),(0,[z1,z1064,z3,z4,z5,z6]),(1,[z1,z7,z3,z5,z744])]],
   [[(0,[z1,z1065,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z189]),(0,[z1,z3,z233,z5,z6,z103]),(0,[z1066,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z109,z6]),(0,[z1,z7,z3,z4,z5,z1067]),(0,[z1,z3,z4,z1068,z5,z6]),(0,[z1,z7,z1069,z4,z5,z6]),(0,[z1,z3,z1070,z4,z5,z6]),(0,[z1,z7,z3,z1071,z5,z6]),(0,[z15,z525,z1,z3,z5,z6]),(0,[z1,z3,z28,z4,z405,z6]),(0,[z475,z7,z3,z4,z5,z349])],[(0,[z552,z161,z3,z4,z5,z6]),(0,[z1,z1072,z7,z3,z5,z6]),(0,[z1,z3,z4,z5,z1073,z6]),(0,[z15,z1,z3,z335,z5,z6]),(0,[z277,z15,z1,z3,z5,z6]),(0,[z43,z1,z3,z28,z5,z6])],[(0,[z1,z7,z3,z4,z14,z6]),(0,[z775,z1,z7,z3,z5,z6]),(0,[z298,z43,z1,z3,z5,z6]),(0,[z1,z169,z3,z4,z5,z349])],[(0,[z7,z3,z58,z4,z14,z6]),(0,[z135,z316,z3,z154,z5,z6]),(0,[z15,z1,z3,z4,z5,z205]),(0,[z1,z1074,z3,z4,z5,z6]),(0,[z266,z7,z3,z4,z6,z201])],[(0,[z15,z203,z1,z3,z5,z6]),(0,[z1,z7,z1075,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1076]),(0,[z1,z7,z3,z4,z5,z737]),(0,[z34,z3,z327,z4,z5,z6]),(0,[z15,z1,z3,z427,z5,z6]),(0,[z34,z74,z3,z4,z5,z6]),(0,[z1,z7,z159,z76,z5,z6]),(0,[z1077,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z5,z210])],[(0,[z1,z1078,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1079,z6]),(0,[z1,z3,z28,z4,z5,z189]),(0,[z1,z27,z636,z4,z5,z6]),(0,[z1,z3,z62,z5,z725,z6]),(0,[z1,z1080,z3,z4,z5,z6]),(0,[z1,z1081,z3,z4,z5,z6])],[(0,[z15,z123,z1,z3,z5,z6]),(0,[z475,z7,z3,z4,z5,z6]),(0,[z15,z29,z1,z3,z5,z6]),(0,[z267,z964,z3,z4,z5,z6]),(0,[z486,z1,z3,z62,z5,z6]),(0,[z1082,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z1083,z3,z4,z5,z6]),(0,[z1084,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z243,z5,z6]),(0,[z1085,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1086]),(0,[z1,z1087,z3,z4,z5,z6])],[(0,[z1088,z1,z3,z4,z5,z6]),(0,[z1,z3,z28,z4,z5,z205]),(0,[z1,z3,z4,z252,z5,z6]),(0,[z486,z1,z3,z4,z5,z6]),(0,[z102,z1,z3,z356,z225,z6]),(0,[z1,z1089,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z815,z39])],[(0,[z144,z7,z3,z4,z14,z6]),(0,[z15,z1,z3,z438,z5,z6]),(0,[z7,z3,z779,z127,z5,z6]),(0,[z135,z7,z425,z3,z5,z6]),(0,[z15,z1,z3,z5,z6,z440]),(0,[z15,z1,z3,z5,z6,z442])],[(0,[z79,z34,z3,z4,z5,z6]),(0,[z57,z7,z58,z4,z109,z6]),(0,[z376,z7,z3,z4,z5,z217]),(0,[z15,z1,z3,z257,z5,z6]),(0,[z15,z1,z3,z5,z6,z259]),(0,[z1,z42,z3,z5,z140,z6]),(0,[z131,z1,z3,z5,z6,z33])],[(0,[z1,z498,z3,z4,z109,z6]),(0,[z1,z3,z4,z5,z6,z1090]),(0,[z15,z1,z3,z263,z5,z6]),(0,[z3,z28,z4,z5,z50,z6]),(0,[z1,z3,z919,z115,z5,z6]),(0,[z106,z1,z3,z5,z202,z33])],[(0,[z1,z7,z3,z4,z109,z150]),(0,[z1,z7,z3,z1091,z5,z6])],[(0,[z1,z84,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z1092,z6]),(0,[z1,z498,z3,z4,z14,z6]),(0,[z1,z3,z952,z64,z5,z6]),(0,[z1,z7,z3,z64,z109,z6]),(0,[z15,z1,z3,z5,z450,z6]),(0,[z15,z1,z3,z451,z5,z6]),(0,[z101,z15,z1,z3,z62,z6]),(0,[z1,z3,z1093,z4,z5,z6]),(0,[z1,z181,z3,z4,z405,z6])]],
   [[(0,[z41,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z14,z150]),(0,[z15,z135,z1,z3,z5,z6]),(0,[z16,z7,z3,z4,z5,z177]),(0,[z1094,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1095]),(0,[z1,z7,z3,z5,z1096,z6])],[(0,[z491,z7,z3,z4,z242,z6]),(0,[z1097,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z1098]),(0,[z1,z3,z4,z5,z6,z202]),(0,[z1,z7,z3,z5,z506,z33]),(0,[z1,z7,z3,z1099,z5,z6])],[(0,[z146,z7,z58,z4,z5,z6]),(0,[z1,z7,z3,z4,z245,z184]),(0,[z101,z15,z1,z3,z5,z53]),(0,[z1,z1100,z3,z4,z5,z6])],[(0,[z92,z7,z223,z4,z5,z6]),(0,[z1,z3,z252,z105,z5,z6]),(1,[z1,z7,z790,z5,z6]),(0,[z1101,z7,z3,z4,z5,z6]),(0,[z1,z1102,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z1103,z6]),(0,[z1,z7,z3,z4,z5,z1104]),(0,[z1,z1105,z3,z4,z5,z6]),(0,[z521,z7,z3,z4,z5,z99]),(0,[z15,z1059,z3,z4,z5,z6]),(0,[z1,z1106,z3,z4,z5,z6])],[(0,[z1,z7,z3,z1107,z4,z5]),(0,[z1,z7,z3,z1108,z5,z6]),(0,[z1,z7,z3,z1109,z5,z6]),(0,[z15,z1,z3,z5,z6,z284]),(0,[z1,z7,z3,z5,z6,z1110]),(0,[z1,z7,z3,z4,z1111,z6]),(0,[z530,z1,z7,z3,z4,z201])],[(0,[z1,z7,z3,z1112,z5,z6]),(0,[z7,z3,z1113,z4,z5,z6]),(0,[z7,z93,z4,z5,z306,z6]),(0,[z1,z1114,z3,z4,z5,z6]),(0,[z135,z24,z1,z3,z5,z6]),(0,[z1,z7,z3,z4,z231,z6]),(0,[z267,z991,z3,z4,z5,z6])],[(0,[z146,z1,z7,z4,z117,z6]),(0,[z101,z15,z1,z3,z262,z6]),(0,[z1115,z1,z7,z3,z4,z6]),(0,[z1,z7,z3,z61,z503,z6]),(0,[z1,z7,z3,z1116,z5,z6])]],
   [[(0,[z15,z904,z1,z3,z5,z6]),(0,[z1117,z7,z3,z4,z5,z6]),(0,[z15,z3,z4,z5,z50,z6]),(0,[z0,z1,z3,z4,z5,z254]),(0,[z1,z7,z3,z4,z5,z805]),(0,[z475,z7,z3,z77,z5,z6]),(1,[z1,z7,z4,z5,z815]),(0,[z1,z1118,z3,z4,z5,z6])],[(0,[z15,z1,z3,z294,z5,z6]),(0,[z1,z17,z4,z572,z5,z6]),(0,[z1119,z1,z3,z4,z5,z6]),(0,[z15,z137,z1,z3,z5,z6]),(0,[z1,z85,z3,z233,z5,z6]),(0,[z561,z1,z7,z3,z4,z201])],[(0,[z1,z7,z3,z4,z1120,z6]),(0,[z1,z7,z3,z1121,z5,z6]),(0,[z1,z7,z3,z4,z5,z1122]),(0,[z1,z169,z3,z77,z5,z6]),(0,[z1123,z7,z3,z4,z5,z6]),(0,[z1,z1124,z3,z4,z5,z6]),(0,[z266,z820,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z117,z189]),(0,[z7,z3,z4,z5,z99,z734]),(0,[z1,z3,z752,z4,z5,z6]),(0,[z15,z1,z3,z107,z5,z6]),(0,[z1,z7,z3,z5,z356,z6]),(0,[z1,z1125,z3,z4,z5,z6]),(0,[z1126,z7,z3,z4,z5,z6]),(0,[z30,z1,z7,z4,z117,z349])],[(0,[z1,z7,z199,z95,z5,z6])],[(0,[z15,z1,z95,z76,z5,z6]),(0,[z104,z7,z3,z4,z5,z210]),(0,[z1,z7,z3,z495,z231,z6])],[(0,[z1,z7,z3,z4,z6,z1127]),(0,[z98,z7,z3,z4,z5,z449]),(0,[z101,z15,z1,z3,z219,z6]),(0,[z15,z1,z3,z315,z5,z6]),(0,[z1128,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z715,z6])],[(0,[z1,z7,z3,z4,z1129,z6]),(0,[z7,z3,z4,z5,z1130,z6]),(0,[z101,z1,z3,z28,z96,z6]),(0,[z1131,z7,z3,z4,z5,z6]),(0,[z52,z7,z3,z4,z5,z245])]],
   [[(0,[z1,z1132,z3,z4,z5,z6]),(0,[z15,z1,z3,z319,z5,z6]),(0,[z1133,z7,z3,z4,z5,z6]),(0,[z90,z1,z28,z76,z5,z6]),(0,[z1,z7,z3,z4,z5,z1134]),(0,[z1135,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z1136,z5,z6]),(0,[z1,z3,z1093,z77,z5,z6]),(0,[z1,z365,z3,z5,z6,z33])],[(0,[z1,z7,z3,z4,z6,z1137]),(0,[z418,z1,z327,z4,z5,z6]),(0,[z475,z7,z3,z115,z5,z6]),(0,[z1,z3,z4,z5,z6,z1138])],[(0,[z98,z7,z3,z4,z99,z184])],[(0,[z41,z161,z3,z4,z5,z6]),(0,[z1139,z1,z7,z3,z5,z6]),(0,[z113,z7,z3,z127,z5,z6]),(0,[z1,z1140,z3,z4,z5,z6]),(0,[z1,z7,z3,z1141,z5,z6]),(0,[z15,z1,z3,z45,z5,z254]),(0,[z3,z28,z4,z5,z6,z177]),(0,[z1,z3,z4,z5,z1142,z6]),(0,[z1,z169,z3,z115,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1143]),(0,[z2,z712,z3,z4,z5,z6]),(0,[z239,z15,z1,z3,z5,z6]),(0,[z441,z3,z28,z4,z5,z6]),(0,[z1,z3,z28,z315,z5,z6]),(0,[z1,z7,z3,z1144,z5,z6])],[(0,[z1,z7,z3,z4,z116,z189]),(0,[z15,z1,z3,z651,z5,z6]),(0,[z15,z659,z1,z3,z5,z6])],[(0,[z1,z1145,z3,z4,z5,z6]),(0,[z1,z71,z3,z76,z5,z6]),(0,[z7,z3,z4,z5,z6,z1146])],[(0,[z113,z7,z3,z779,z5,z6]),(0,[z7,z3,z4,z188,z751,z6]),(0,[z101,z15,z41,z3,z5,z6]),(0,[z15,z1,z3,z45,z5,z130])]],
   [[(0,[z1,z7,z3,z4,z5,z1147]),(0,[z1,z7,z3,z4,z1148,z6]),(0,[z1,z1149,z3,z4,z5,z6])],[(0,[z229,z123,z1,z3,z5,z6]),(0,[z1,z74,z3,z4,z56,z6]),(0,[z1,z1150,z3,z4,z5,z6]),(0,[z809,z98,z1,z3,z5,z6]),(0,[z1151,z1,z7,z3,z4,z5]),(0,[z15,z1,z3,z4,z5,z982]),(0,[z30,z15,z1,z4,z117,z6]),(0,[z106,z1,z3,z28,z5,z33]),(0,[z248,z1,z7,z4,z117,z6]),(0,[z52,z7,z3,z495,z5,z6]),(0,[z1152,z1,z3,z4,z5,z6]),(0,[z1,z3,z869,z315,z5,z6])],[(0,[z288,z34,z3,z4,z5,z6]),(0,[z1,z3,z4,z1153,z5,z6]),(0,[z15,z1,z3,z596,z5,z6]),(0,[z419,z1,z3,z4,z5,z254]),(0,[z1,z7,z3,z4,z5,z848]),(0,[z131,z1,z3,z45,z5,z6])],[(0,[z1,z282,z3,z4,z5,z6]),(0,[z1,z230,z3,z495,z5,z6]),(0,[z1,z7,z4,z5,z6,z815]),(0,[z1,z1154,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z317,z6]),(0,[z1155,z7,z3,z4,z5,z6]),(0,[z1,z1156,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z349])],[(0,[z1,z7,z3,z5,z6,z1157]),(0,[z1,z3,z1158,z4,z5,z6]),(0,[z1,z865,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z1159,z6]),(0,[z15,z1,z992,z4,z5,z6]),(0,[z15,z1,z3,z414,z5,z6]),(0,[z15,z1,z3,z364,z5,z6]),(0,[z15,z3,z4,z5,z6,z177])],[(0,[z1,z7,z3,z1160,z5,z6]),(0,[z1,z1161,z3,z4,z5,z6]),(0,[z1,z27,z17,z4,z5,z6]),(0,[z15,z104,z3,z4,z5,z6]),(0,[z15,z441,z3,z4,z5,z6]),(0,[z266,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z1162,z6]),(0,[z1,z7,z95,z790,z5,z6]),(0,[z7,z3,z4,z5,z6,z1163])]],
   [[(0,[z1,z7,z3,z1164,z5,z6]),(0,[z15,z1,z3,z650,z5,z6])],[(0,[z15,z32,z1,z3,z5,z6]),(0,[z129,z7,z3,z4,z188,z6]),(0,[z182,z7,z3,z4,z5,z217]),(0,[z1,z7,z3,z4,z405,z39]),(0,[z1,z7,z3,z1165,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6]),(0,[z123,z7,z3,z127,z5,z6]),(0,[z1,z2,z3,z233,z5,z6]),(0,[z15,z1,z3,z5,z6,z513]),(0,[z267,z7,z3,z4,z242,z6]),(0,[z1,z3,z28,z4,z317,z6]),(0,[z15,z1,z3,z4,z5,z1000]),(0,[z30,z1,z7,z77,z117,z6]),(0,[z1,z1166,z3,z4,z5,z6]),(0,[z441,z181,z3,z4,z5,z6])],[(0,[z395,z1,z7,z3,z4,z201]),(0,[z129,z7,z3,z4,z751,z6]),(0,[z1,z3,z5,z356,z140,z6]),(0,[z1,z1167,z3,z4,z5,z6])],[(0,[z904,z1,z3,z4,z5,z6]),(1,[z15,z1,z3,z5,z108])],[(0,[z1,z1168,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1169,z6]),(0,[z15,z172,z1,z3,z5,z6]),(0,[z882,z7,z3,z4,z5,z6]),(0,[z43,z102,z1,z3,z225,z6])],[(0,[z1,z7,z3,z4,z5,z994]),(0,[z1,z3,z5,z6,z202,z187])],[(0,[z1,z1170,z3,z4,z5,z6]),(0,[z16,z3,z28,z4,z5,z217]),(0,[z101,z15,z34,z3,z5,z6]),(0,[z15,z1,z3,z95,z5,z6]),(0,[z796,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z1171]),(0,[z441,z7,z3,z4,z405,z6]),(0,[z1,z7,z3,z315,z405,z6])]],
   [[(0,[z1,z282,z3,z4,z5,z150]),(0,[z1,z7,z3,z4,z5,z1172]),(0,[z1,z1173,z3,z4,z5,z6]),(0,[z1,z7,z72,z790,z5,z6])],[(0,[z1,z7,z3,z1174,z5,z6]),(0,[z1,z7,z3,z4,z5,z1175]),(0,[z15,z1,z3,z234,z5,z6]),(0,[z1,z1176,z3,z4,z5,z6]),(0,[z1019,z1,z3,z77,z5,z6])],[(0,[z7,z3,z4,z188,z428,z6]),(0,[z15,z1,z3,z5,z6,z392]),(0,[z34,z3,z4,z5,z13,z6]),(0,[z1,z42,z3,z28,z5,z6]),(0,[z30,z475,z7,z4,z117,z6]),(0,[z1,z7,z3,z4,z5,z832])],[(0,[z1,z7,z3,z1177,z5,z6]),(0,[z15,z52,z3,z4,z5,z6]),(0,[z1,z42,z3,z880,z5,z6]),(0,[z1,z7,z3,z4,z715,z6]),(0,[z30,z1,z7,z115,z117,z6]),(0,[z1,z7,z3,z4,z5,z53]),(0,[z1178,z7,z3,z4,z5,z6])],[(0,[z144,z7,z3,z4,z242,z6]),(0,[z1179,z1,z3,z4,z5,z6]),(0,[z1180,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z258,z5,z6])],[(0,[z57,z7,z58,z4,z5,z6]),(0,[z1,z1181,z3,z4,z5,z6]),(0,[z1182,z1,z3,z4,z5,z6]),(0,[z1183,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z868,z6]),(0,[z1,z7,z3,z1184,z5,z6]),(0,[z30,z1,z169,z4,z117,z6]),(0,[z1,z430,z3,z61,z62,z6])],[(0,[z1,z7,z3,z1185,z5,z6]),(0,[z1,z3,z1186,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1187]),(0,[z15,z1,z3,z5,z6,z33]),(0,[z15,z1,z3,z4,z405,z6]),(0,[z15,z1,z505,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z1188]),(0,[z1,z7,z3,z4,z832,z201]),(0,[z1,z1189,z3,z4,z5,z6])],[(0,[z15,z1,z3,z406,z5,z6]),(0,[z1,z7,z3,z4,z5,z1190]),(0,[z1,z7,z3,z4,z5,z150]),(0,[z1,z282,z3,z4,z14,z6]),(0,[z1191,z1,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1192]),(0,[z144,z7,z3,z4,z462,z6]),(0,[z98,z7,z3,z4,z5,z177]),(0,[z15,z1,z1024,z4,z5,z6])]],
   [[(0,[z421,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z64,z5,z6]),(0,[z15,z1,z3,z5,z6,z409]),(0,[z15,z41,z3,z95,z5,z6]),(0,[z695,z1,z7,z3,z4,z201])],[(0,[z288,z3,z4,z534,z5,z6]),(0,[z135,z3,z154,z28,z5,z6]),(0,[z7,z3,z4,z5,z734,z6]),(0,[z104,z31,z3,z4,z5,z6])],[(0,[z15,z1,z3,z591,z5,z6]),(0,[z1,z7,z3,z5,z6,z1193])],[(0,[z15,z1,z3,z4,z5,z210]),(0,[z1,z7,z3,z880,z5,z6]),(0,[z1,z7,z3,z77,z5,z6])],[(0,[z1,z3,z83,z4,z5,z6]),(0,[z1042,z1,z3,z64,z5,z6]),(0,[z267,z7,z3,z4,z14,z6]),(0,[z7,z3,z4,z5,z50,z6]),(0,[z1,z7,z3,z4,z1194,z6]),(0,[z1,z1195,z3,z4,z5,z6]),(0,[z1,z7,z3,z1196,z5,z6]),(0,[z15,z1,z3,z18,z5,z6]),(0,[z1197,z7,z3,z4,z5,z6]),(0,[z920,z1,z3,z315,z5,z6]),(0,[z248,z1,z7,z4,z5,z39])],[(0,[z1,z88,z3,z4,z5,z6]),(0,[z1,z161,z3,z233,z5,z6]),(0,[z1198,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z1199,z5,z6]),(0,[z1023,z7,z3,z4,z5,z6]),(0,[z15,z1,z3,z558,z5,z6]),(0,[z15,z1,z3,z559,z5,z6])],[(0,[z84,z161,z3,z4,z5,z6]),(0,[z1200,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z5,z349]),(0,[z51,z1,z7,z315,z5,z39]),(0,[z1,z7,z3,z61,z62,z6])],[(0,[z1,z7,z3,z97,z5,z6]),(0,[z15,z41,z3,z5,z6,z33])]],
   [[(0,[z583,z1,z134,z4,z5,z6]),(0,[z15,z34,z3,z95,z5,z6]),(0,[z30,z1,z31,z4,z117,z6])],[(0,[z1,z7,z3,z5,z6,z1201]),(0,[z1,z7,z3,z4,z5,z1202]),(0,[z57,z498,z58,z4,z5,z6]),(0,[z1203,z1,z3,z4,z5,z6]),(0,[z98,z3,z28,z4,z5,z99]),(0,[z15,z343,z1,z3,z5,z6]),(0,[z1,z3,z28,z4,z5,z210]),(0,[z90,z1,z252,z76,z5,z6]),(0,[z52,z7,z3,z4,z231,z6])],[(0,[z1,z208,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z901]),(0,[z15,z351,z1,z3,z5,z6]),(0,[z98,z7,z3,z4,z317,z99]),(0,[z1,z3,z28,z18,z5,z6])],[(0,[z1,z498,z3,z4,z5,z150]),(0,[z1,z1204,z3,z4,z5,z6]),(0,[z1,z752,z134,z4,z5,z6]),(0,[z15,z1,z1044,z4,z5,z6]),(0,[z15,z1,z3,z431,z5,z6]),(0,[z0,z1,z3,z4,z5,z103]),(0,[z1,z230,z3,z4,z231,z6])],[(0,[z1,z498,z3,z64,z5,z6]),(0,[z15,z286,z1,z3,z5,z6]),(0,[z1205,z7,z3,z4,z5,z6]),(0,[z15,z1128,z3,z4,z5,z6]),(0,[z1,z7,z3,z233,z5,z6]),(0,[z1,z7,z3,z115,z5,z6]),(0,[z1,z31,z3,z4,z5,z349]),(0,[z7,z3,z4,z5,z6,z1206]),(0,[z1,z7,z544,z4,z5,z245])],[(0,[z1,z7,z3,z64,z5,z150]),(0,[z135,z7,z3,z779,z5,z6]),(0,[z333,z1,z7,z4,z5,z39]),(0,[z1,z71,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1036]),(0,[z1207,z7,z3,z4,z5,z6])],[(0,[z123,z1,z7,z3,z5,z6]),(0,[z123,z1,z3,z5,z13,z6]),(0,[z1,z7,z3,z4,z1208,z6]),(0,[z7,z3,z749,z4,z5,z6]),(0,[z129,z7,z3,z4,z6,z449]),(0,[z1,z7,z3,z4,z5,z1209]),(0,[z1,z74,z3,z4,z219,z6]),(0,[z1,z7,z3,z4,z171,z38])],[(0,[z15,z1,z3,z133,z5,z6]),(0,[z123,z1,z74,z3,z5,z6]),(0,[z1,z7,z3,z1210,z5,z6]),(0,[z1,z1211,z3,z4,z5,z6]),(0,[z809,z1,z7,z3,z5,z6]),(0,[z15,z1,z3,z443,z5,z6]),(0,[z15,z34,z3,z5,z6,z33]),(0,[z326,z1,z3,z28,z4,z201]),(0,[z1,z7,z4,z885,z117,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 516).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1032).take 212) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1244)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [516, 516, 212] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 191).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 100, 65] = true :=
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

end PEqualNP.Outside.L_meta_40417

theorem PEqualNP.Outside.L_meta_40417 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209683104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209683104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40417.solve