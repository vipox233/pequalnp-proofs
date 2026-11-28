import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44666

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
  Nat.testBit (4276812992 * 2 ^ 32 + 4241008768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x18d6c630c44336e1#64 ++ 0x20635b18c3110cdb#64 ++ 0x39fec630c447ffdf#64 ++ 0x20e7fb18c3111fff#64 : BitVec 256),
   (0x423102d7019d8b40#64 ++ 0x1108c40b5c06762d#64 ++ 0xc63107ff07ff8ff7#64 ++ 0x7318c41ffc1ffe3f#64 : BitVec 256),
   (0x05c1582b5868d180#64 ++ 0x84170560ad61a346#64 ++ 0x07c1f83ff878f1fb#64 ++ 0xbc1f07e0ffe1e3c7#64 : BitVec 256),
   (0xb801ad41ae80ec00#64 ++ 0x4ae006b506ba03b0#64 ++ 0xf801ffc1ff80fe3d#64 ++ 0xffe007ff07fe03f8#64 : BitVec 256),
   (0xef6a0000f7760002#64 ++ 0x0fbda80003ddd800#64 ++ 0xfffe0001ffff003f#64 ++ 0xdffff80007fffc00#64 : BitVec 256),
   (0xf7bcf7bc00000004#64 ++ 0x2fdef3def0000000#64 ++ 0xfffffffe0000003e#64 ++ 0xeffffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010021000010240 0x0000400840000409 0x0000063000008fc0 0x20000018c000023f

def z1 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f83ff878f1fb 0xbc1f07e0ffe1e3c7

def z2 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z3 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63107ff07ff8ff7 0x7318c41ffc1ffe3f

def z4 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801ffc1ff80fe3d 0xffe007ff07fe03f8

def z5 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0001ffff003f 0xdffff80007fffc00

def z6 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffe0000003e 0xeffffffff8000000

def z7 : W := mkw 0xfa31afd5ae80ec00 0x4be8c6bf56ba03b0 0xfe31ffffff80fe3f 0xfff8c7fffffe03f8

def z8 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f83e0078f1c2 0x201f07e0f801e3c7

def z9 : W := mkw 0x18428400c44336e1 0x00610a1003110cdb 0x3800c600c447ffdd 0x20e0031803111fff

def z10 : W := mkw 0x4230029400010240 0x0108c00a50000409 0xc63107fe04478ff7 0x6318c41ff8111e3f

def z11 : W := mkw 0x05d6523a506b13e1 0xa4175948e941ac4f 0x07fe003e007f01c2 0x001ff800f801fc07

def z12 : W := mkw 0x0081582b0808d180 0x80020560ac202346 0x0001f83e0000f1c0 0x200007e0f80003c7

def z13 : W := mkw 0xefeb582bff7ed182 0x8fbfad60affdfb46 0xfffff83ffffff1ff 0xffffffe0ffffffc7

def z14 : W := mkw 0xfffff7ffc5dfbfe5 0x3fffffdfff177eff 0xffffffffc7ffffff 0xffffffffff1fffff

def z15 : W := mkw 0xe728000033340002 0x0f9ca00000ccd000 0xc60000013bb80020 0xdf18000004eee000

def z16 : W := mkw 0x0501180b1828c100 0x841404602c60a304 0x0601380f38380020 0x9c1804e03ce0e000

def z17 : W := mkw 0x1dd7de3bdc6bf7e1 0xa4775f78ef71afdf 0x3ffffe3ffc7fffff 0xbcfffff8fff1ffff

def z18 : W := mkw 0x05c0582858605080 0x84170160a1618142 0x01c0f800f8007008 0x8c0703e003e001c0

def z19 : W := mkw 0xbdc1fd6bfee8fd80 0xcef707f5affba3f6 0xffc1fffffff8ffff 0xffff07ffffffe3ff

def z20 : W := mkw 0x4220000001140000 0x0108800000045000 0xc630000107ff0037 0x5318c000041ffc00

def z21 : W := mkw 0xef7b02d7f7ff8b42 0x1fbdec0b5fdffe2d 0xffff07ffffff8fff 0xfffffc1ffffffe3f

def z22 : W := mkw 0xb800a500a6000000 0x0ae0029402980000 0xf801ffc1ff80003d 0xffe007ff07fe0000

def z23 : W := mkw 0xffbcffbcae006404 0x6ffef3fef2b80190 0xfffffffef800703e 0xeffffffffbe001c0

def z24 : W := mkw 0x5231afd7099def40 0x5148c6bf5c2677bd 0xc631ffff07fffff7 0x7318c7fffc1fffff

def z25 : W := mkw 0xb800ad00ae006400 0x4ae002b402b80190 0x3800f800f8007008 0x8ce003e003e001c0

def z26 : W := mkw 0xb800a540a6802c00 0x4ae00295029a00b0 0xf80007c1ff800e3d 0xdfe0001f07fe0038

def z27 : W := mkw 0x0010021000000000 0x0000400840000000 0x0030063000000016 0x2000c018c0000000

def z28 : W := mkw 0x08d64230c44336e1 0x20235908c3110cdb 0x01fe0030c447ffc3 0x0007f800c3111fff

def z29 : W := mkw 0x18c6c420c44234a1 0x20631b10831108d2 0x39cec600c400fe1d 0x20e73b18031003f8

def z30 : W := mkw 0x0800000084002400 0x0020000002100090 0x00000000c400fe01 0x00000000031003f8

def z31 : W := mkw 0x08420000c44336e1 0x0021080003110cdb 0x00000000c447ffc1 0x0000000003111fff

def z32 : W := mkw 0xe728318c00000004 0x0f9ca0c630000000 0xc60139ce00000020 0xcf1804e738000000

def z33 : W := mkw 0x1001ad410880ec00 0x404006b5042203b0 0x0001ffc00000fe00 0x200007ff000003f8

def z34 : W := mkw 0x476a000051760002 0x051da8000145d800 0x07fe0000007f0002 0x001ff8000001fc00

def z35 : W := mkw 0x5ffec630d57736e3 0x257ffb18c355dcdb 0x3ffec630c47fffdf 0x20fffb18c311ffff

def z36 : W := mkw 0x47fd5abf5868d184 0xa51ff56afd61a346 0x07fff83ff878f1fb 0xbc1fffe0ffe1e3c7

def z37 : W := mkw 0x0010021000010240 0x0000400840000409 0x0030063004478fd7 0x2000c018c0111e3f

def z38 : W := mkw 0x0580502800000000 0x04160140a0000000 0x07c1f83e0000003a 0xac1f07e0f8000000

def z39 : W := mkw 0xf7fdffbf5868d184 0xafdff7fefd61a346 0xfffffffff878f1ff 0xffffffffffe1e3c7

def z40 : W := mkw 0x42710ad759fddbc0 0x9109c42b5d67f76f 0xc63107fffffffff7 0x7318c41fffffffff

def z41 : W := mkw 0xf7bcf7bc00010244 0x2fdef3def0000409 0xfffffffe04478fff 0xeffffffff8111e3f

def z42 : W := mkw 0x5af7c6f7c5dfbfe1 0x316bdf1bdf177eff 0xffffc7ffc7ffffff 0x73ffff1fff1fffff

def z43 : W := mkw 0xadc1582bfe68d180 0x8eb70560aff9a346 0xffc1f83ffff8f1ff 0xffff07e0ffffe3c7

def z44 : W := mkw 0xef6b0801ff76c002 0x0fbdac2007fddb00 0xfffff801fffff03f 0xffffffe007ffffc0

def z45 : W := mkw 0x1800840084002400 0x0060021002100090 0x3800c600c400fe1d 0x20e00318031003f8

def z46 : W := mkw 0x058c502800000004 0x24163140a0000000 0x01ce000000000000 0x0007380000000000

def z47 : W := mkw 0x18c6c420c44234a1 0x20631b10831108d2 0x39fec000c447701f 0x00e7fb0003111dc0

def z48 : W := mkw 0xf23ca7d401950a44 0x3bc8f29f50065429 0xf83e07c007870e04 0x43e0f81f001e1c38

def z49 : W := mkw 0x0001000300088100 0x000004000c002204 0x0601003f007881f3 0x30180400fc01e207

def z50 : W := mkw 0x423002d401950a40 0x1108c00b50065429 0xc03007c007870e04 0x4300c01f001e1c38

def z51 : W := mkw 0x05c0502a50681180 0x84170140a941a046 0x07c0003e007801c2 0x001f0000f801e007

def z52 : W := mkw 0xb800a540a6802c00 0x4ae00295029a00b0 0xf80007c007800e04 0x43e0001f001e0038

def z53 : W := mkw 0xb8d6e770e6c33ee1 0x6ae35b9dc39b0cfb 0xf9fec7f0c7c7ffdf 0x63e7fb1fc31f1fff

def z54 : W := mkw 0x001102d700898b40 0x1000440b5c02262d 0x060107ff00788ff3 0x3018041ffc01e23f

def z55 : W := mkw 0x422100c7019d8b40 0x110884031c06762d 0xc60101cf07ff8fe1 0x531804073c1ffe3f

def z56 : W := mkw 0x5af6c630c55736e1 0x216bdb18c3155cdb 0xfffec631c7ffffff 0x73fffb18c71fffff

def z57 : W := mkw 0x00c0402040401080 0x0003010081010042 0x01c0c030c040f1db 0x20070300c30103c7

def z58 : W := mkw 0x0010021000010240 0x0000400840000409 0x0030060004070e04 0x0000c01800101c38

def z59 : W := mkw 0xb800ad40ae806c00 0x4ae002b502ba01b0 0xf800ffc0ff807e0c 0xcfe003ff03fe01f8

def z60 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801f9c1fb807028 0xdfe007e707ee01c0

def z61 : W := mkw 0x0000000033340002 0x0000000000ccd000 0x000000013bb80000 0x1000000004eee000

def z62 : W := mkw 0xb895ef71ae80ec00 0x6ae257bdc6ba03b0 0xf9fffff1ff80fe3f 0xffe7ffffc7fe03f8

def z63 : W := mkw 0x0010029600090340 0x1000400a5800240d 0x0000003e000001c0 0x00000000f8000007

def z64 : W := mkw 0xf7acf5ac00000004 0x2fdeb3d6b0000000 0xffcff9ce00000028 0xcfff3fe738000000

def z65 : W := mkw 0xea2a0000a7160002 0x0ba8a800029c5800 0xfe3e000107ff0037 0x53f8f800041ffc00

def z66 : W := mkw 0x00d64230404312e1 0x20035908c1010c4b 0x01fe0030004701c2 0x0007f800c0011c07

def z67 : W := mkw 0xa00129412a80c800 0x4a8004a504aa0320 0xc00139c13b800020 0xdf0004e704ee0000

def z68 : W := mkw 0xa5c1796b7ae8d980 0xce9705e5adeba366 0xc7c1f9fffbf8f1fb 0xff1f07e7ffefe3c7

def z69 : W := mkw 0xb58cf52800000004 0x2ed633d4a0000000 0x39cef80000000008 0x8ce73be000000000

def z70 : W := mkw 0x423102d500808800 0x0108c40b54020220 0xc63107ff07808e37 0x7318c41ffc1e0238

def z71 : W := mkw 0x0001000100008000 0x0000040004000200 0x0001000100008031 0x3000040004000200

def z72 : W := mkw 0xe728000000000000 0x0f9ca00000000000 0xc600000000000020 0xcf18000000000000

def z73 : W := mkw 0x47f15abf5868d180 0x851fc56afd61a346 0xc7f1fffff878f1ff 0xff1fc7ffffe1e3c7

def z74 : W := mkw 0x08010841ae80ec00 0x4020042106ba03b0 0x00000001ff80fe01 0x1000000007fe03f8

def z75 : W := mkw 0x47bc52bc00000004 0x251ef14af0000000 0x07fe003e00000002 0x001ff800f8000000

def z76 : W := mkw 0xe728000000000000 0x0f9ca00000000000 0xfffe00000000003e 0xcffff80000000000

def z77 : W := mkw 0xfffef7bcf7760006 0x2ffffbdef3ddd800 0xffffffffffff003f 0xfffffffffffffc00

def z78 : W := mkw 0xf7fcf7bc50600004 0x2fdff3def1418000 0xfffffffff878003f 0xffffffffffe1e000

def z79 : W := mkw 0x42300296011d0340 0x1108c00a5804740d 0x0630063e047f8fd7 0x2018c018f811fe3f

def z80 : W := mkw 0x0500000000000000 0x0414000000000000 0x07c000000000003a 0x8c1f000000000000

def z81 : W := mkw 0xf23da7d7019d8b44 0x3bc8f69f5c06762d 0xfe3f07ff07ff8ff7 0x73f8fc1ffc1ffe3f

def z82 : W := mkw 0x52b4f7bc00000004 0x214ad3def0000000 0xc631fffe00000036 0x6318c7fff8000000

def z83 : W := mkw 0xbd8dfd69ae80ec04 0x6ef637f5a6ba03b0 0xf9cfffc1ff80fe3d 0xffe73fff07fe03f8

def z84 : W := mkw 0x08430043c5dfbfe1 0x10210c010f177eff 0x00000001c7ffffc1 0x10000000071fffff

def z85 : W := mkw 0xef6a0000c4420000 0x0fbda80003110800 0xfffe0000c447003f 0xcffff80003111c00

def z86 : W := mkw 0xa8000000a6000000 0x0aa0000002980000 0xf8000001ff80003d 0xdfe0000007fe0000

def z87 : W := mkw 0x054108015860c000 0x0415042005618300 0x07c1f801f878f03b 0xbc1f07e007e1e3c0

def z88 : W := mkw 0x1894c63084002400 0x20625318c2100090 0x39fec630c400fe1f 0x20e7fb18c31003f8

def z89 : W := mkw 0x0080402000000000 0x0002010080000000 0x01c0c0300000001a 0x20070300c0000000

def z90 : W := mkw 0x47f052be517d13c0 0x951fc14af945f44f 0x07f0003e007f01c2 0x001fc000f801fc07

def z91 : W := mkw 0x47f15aff59fddbc0 0x951fc56bfd67f76f 0xc7f1ffffffffffff 0xff1fc7ffffffffff

def z92 : W := mkw 0x05c0582858605080 0x84170160a1618142 0x01c0f830f840f1db 0xac0703e0c3e103c7

def z93 : W := mkw 0x05c0402050601080 0x0417010081418042 0x07c0c031f878f1fb 0xbc1f0300c7e1e3c7

def z94 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0x3801ffc0f800fe08 0xace007ff03e003f8

def z95 : W := mkw 0xf7acf52800000004 0x2fdeb3d4a0000000 0xfffef8000000003e 0xcffffbe000000000

def z96 : W := mkw 0xff6bad41fff6ec02 0x4ffdaeb507ffdbb0 0xffffffc1fffffe3f 0xffffffff07fffff8

def z97 : W := mkw 0x000108412a80c800 0x4000042104aa0320 0x000000013b800000 0x1000000004ee0000

def z98 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0x063107fe007f8fc2 0x2018c41ff801fe3f

def z99 : W := mkw 0x08d64230c44312e1 0x20235908c3110c4b 0x39fe0030c44701df 0x00e7f800c3111c07

def z100 : W := mkw 0x000108010800c000 0x0000042004200300 0x0001f801f800f039 0xbc0007e007e003c0

def z101 : W := mkw 0x054108035868d180 0x841504200d61a346 0x07c00001f878f1fb 0x9c1f000007e1e3c7

def z102 : W := mkw 0xf2bce7b400000004 0x2bcaf39ed0000000 0xf9fec7f00000001e 0x63e7fb1fc0000000

def z103 : W := mkw 0xfffdfffffee8fd84 0xeffff7fffffba3f6 0xfffffffffff8ffff 0xffffffffffffe3ff

def z104 : W := mkw 0x0800000084000000 0x0020000002100000 0x38000000c400001d 0x00e0000003100000

def z105 : W := mkw 0xbddef738c44336e5 0x2ef77bdce3110cdb 0x39fefe30c447ffdf 0xace7fbf8c3111fff

def z106 : W := mkw 0x08000040a6802c00 0x40200001029a00b0 0x0000000007800e00 0x00000000001e0038

def z107 : W := mkw 0xef7a0294f7760002 0x0fbde80a53ddd800 0xffff07ffffff003f 0xfffffc1ffffffc00

def z108 : W := mkw 0xb800a500a6002400 0x4ae0029402980090 0x3800000000000000 0x00e0000000000000

def z109 : W := mkw 0x1094c63000000000 0x20425318c0000000 0x0000c63000000000 0x20000318c0000000

def z110 : W := mkw 0xfffef7bcc44336e5 0x2ffffbdef3110cdb 0xfffffffec447ffff 0xeffffffffb111fff

def z111 : W := mkw 0x00c148235868d180 0x800305208d61a346 0x01c0c031f878f1db 0x30070300c7e1e3c7

def z112 : W := mkw 0x00000002011d0340 0x100000000804740d 0x00000000007f01c0 0x000000000001fc07

def z113 : W := mkw 0x4230029400000000 0x0108c00a50000000 0xc63107fe00000036 0x6318c41ff8000000

def z114 : W := mkw 0x423102d501958a40 0x1108c40b54065629 0xc03107c107878e35 0x7300c41f041e1e38

def z115 : W := mkw 0x1094c630000136e1 0x20425318c00004db 0x0000c6300000ffc0 0x20000318c00003ff

def z116 : W := mkw 0xfffec630f77736e3 0x2ffffb18c3dddcdb 0xfffec631ffffffff 0xfffffb18c7ffffff

def z117 : W := mkw 0x05c1502b50689180 0x84170540ad41a246 0x07c1003f007881f3 0x301f0400fc01e207

def z118 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x01c1f83ef800f1c8 0xac0707e0fbe003c7

def z119 : W := mkw 0x18c6c420c44234a1 0x20631b10831108d2 0x39cec000c0007008 0x00e73b00030001c0

def z120 : W := mkw 0x42310ad7099dcb40 0x1108c42b5c26772d 0xc631ffffffffffff 0xff18c7ffffffffff

def z121 : W := mkw 0x08430841fff6ec02 0x40210c2107ffdbb0 0x00000001fffffe01 0x1000000007fffff8

def z122 : W := mkw 0x0011021300098340 0x000044084c00260d 0x0631063f047f8ff7 0x3018c418fc11fe3f

def z123 : W := mkw 0x423002d6019d0b40 0x1108c00b5806742d 0xc63007fe07ff0fc6 0x4318c01ff81ffc3f

def z124 : W := mkw 0x18568610c44336e1 0x20615a1843110cdb 0x383e0600c447ffc5 0x00e0f81803111fff

def z125 : W := mkw 0xa00029002a004000 0x4a8000a400a80100 0x0000380038000000 0x8c0000e000e00000

def z126 : W := mkw 0xfa31afd7af9def40 0x5be8c6bf5ebe77bd 0xfe31ffffffffffff 0xfff8c7ffffffffff

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000060004008e15 0x2000001800100238

def z128 : W := mkw 0xa508310800000004 0x0e9420c420000000 0x0000380000000000 0x8c0000e000000000

def z129 : W := mkw 0xfffef7bcf77736e7 0x2ffffbdef3dddcdb 0xffffffffffffffff 0xffffffffffffffff

def z130 : W := mkw 0x423102d7019c8900 0x1108c40b5c067224 0xc63107ff03b80036 0x7318c41ffc0ee000

def z131 : W := mkw 0x18d7ce31cc43f6e1 0x20635f38c7310fdb 0x39fffe31fc47ffff 0xbce7fff8c7f11fff

def z132 : W := mkw 0x1095f7ff00898b44 0x304257dffc02262d 0x0001fffe00008fc0 0x200007fff800023f

def z133 : W := mkw 0x08420000c44336e1 0x0021080003110cdb 0x39fe0000c447ffdf 0x00e7f80003111fff

def z134 : W := mkw 0x1014861000012661 0x2040521840000499 0x0000060000000e00 0x0000001800000038

def z135 : W := mkw 0x08420000c4420000 0x0021080003110800 0x00000000c4470001 0x0000000003111c00

def z136 : W := mkw 0xb59cf7bc00000004 0x2ed673def0000000 0x39cffffe00000008 0xace73ffff8000000

def z137 : W := mkw 0xb000a50000000000 0x0ac0029400000000 0xf801ffc00000003c 0xefe007ff00000000

def z138 : W := mkw 0xffbdfffdae80ec04 0x6ffef7fff6ba03b0 0xffffffffff80fe3f 0xfffffffffffe03f8

def z139 : W := mkw 0x4231029700088100 0x0108c40a5c002204 0xc63107ff007881f7 0x7318c41ffc01e207

def z140 : W := mkw 0x1dc1dc2bdc68f580 0x84770770af71a3d6 0x3fc1fe3ffc78ffff 0xbcff07f8fff1e3ff

def z141 : W := mkw 0xfffef7bcc4420004 0x2ffffbdef3110800 0xfffffffec447003f 0xeffffffffb111c00

def z142 : W := mkw 0xb800a50084002400 0x0ae0029402100090 0xf801ffc0c400fe3d 0xefe007ff031003f8

def z143 : W := mkw 0xea3b02d7a79f8b42 0x1ba8ec0b5e9e7e2d 0xfe3f07ff07ff8ff7 0x73f8fc1ffc1ffe3f

def z144 : W := mkw 0x08420000f77736e3 0x0021080003dddcdb 0x00000001ffffffc1 0x1000000007ffffff

def z145 : W := mkw 0x08c24020c4421080 0x0023090083110842 0x39fec030c447f1df 0x20e7fb00c3111fc7

def z146 : W := mkw 0xffeec420f77634a3 0x2fffbb1083ddd8d2 0xfffec001ffff703f 0xdffffb0007fffdc0

def z147 : W := mkw 0x058158290800c000 0x04160560a4200300 0x07c1f83ff800f03b 0xbc1f07e0ffe003c0

def z148 : W := mkw 0xe728318c00000004 0x0f9ca0c630000000 0xffff39ce0000003e 0xcffffce738000000

def z149 : W := mkw 0xe738029400000000 0x0f9ce00a50000000 0xffff07fe0000003e 0xeffffc1ff8000000

def z150 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf80007c1ff80fe05 0x53e0001f07fe03f8

def z151 : W := mkw 0xa000210000000000 0x0a80008400000000 0xc00139c000000020 0xcf0004e700000000

def z152 : W := mkw 0x1594f7bc00000004 0x245653def0000000 0x07c1fffe0000003a 0xac1f07fff8000000

def z153 : W := mkw 0xfa30a7d4a7952e40 0x5be8c29f529e54b9 0xf83007c007870e04 0x43e0c01f001e1c38

def z154 : W := mkw 0x422000c401940800 0x1108800310065020 0xc00001c003800000 0x43000007000e0000

def z155 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xffce0001fbb80028 0xdfff380007eee000

def z156 : W := mkw 0xef6a318cf7760006 0x0fbda8c633ddd800 0xffff39cfffff003f 0xdffffce73ffffc00

def z157 : W := mkw 0x477a0296517f0342 0x151de80a5945fc0d 0x07fe003e007f01c2 0x001ff800f801fc07

def z158 : W := mkw 0x1094f7bc00000004 0x204253def0000000 0x0001fffe00000000 0x200007fff8000000

def z159 : W := mkw 0x18d6f7bcc44336e5 0x20635bdef3110cdb 0x39fffffec447ffdf 0x20e7fffffb111fff

def z160 : W := mkw 0xf7fcf7bc40401084 0x2fdff3def1010042 0xfffffffec040f1ff 0xeffffffffb0103c7

def z161 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec600c4077e0c 0x00e7fb1803101df8

def z162 : W := mkw 0xf23ca79400000004 0x2bc8f29e50000000 0xf83e07c000000004 0x43e0f81f00000000

def z163 : W := mkw 0xb001ad412a80c800 0x4ac006b504aa0320 0xf801ffc13b80003c 0xffe007ff04ee0000

def z164 : W := mkw 0x00010043019d8b40 0x100004010c06762d 0x0000000107ff8fc1 0x10000000041ffe3f

def z165 : W := mkw 0x08420000f7760002 0x0021080003ddd800 0x00000001ffff0001 0x1000000007fffc00

def z166 : W := mkw 0x52b5c6f7019d8b40 0x314ad71bdc06762d 0xffffc7ff07ff8fff 0x73ffff1ffc1ffe3f

def z167 : W := mkw 0x00d64230404312e1 0x20035908c1010c4b 0x01fe063004478fd7 0x2007f818c0111e3f

def z168 : W := mkw 0x001102d700898b40 0x1000440b5c02262d 0xc00107ff07808ff5 0x7300041ffc1e023f

def z169 : W := mkw 0x18d6c630c4420000 0x20635b18c3110800 0x39fec630c447001f 0x20e7fb18c3111c00

def z170 : W := mkw 0xf7bdffbd0800c004 0x2fdef7fef4200300 0xfffffffff800f03f 0xffffffffffe003c0

def z171 : W := mkw 0xbd8cfd28ae006404 0x6ef633f4a2b80190 0x39cef800f8007008 0x8ce73be003e001c0

def z172 : W := mkw 0xffffde3bff7ff7e3 0xafffff78effdffdf 0xfffffe3fffffffff 0xfffffff8ffffffff

def z173 : W := mkw 0x00944230000112e1 0x20025108c000044b 0x00000030000001c0 0x00000000c0000007

def z174 : W := mkw 0x10d6c630404336e1 0x20435b18c1010cdb 0x01fec6300047ffc2 0x2007fb18c0011fff

def z175 : W := mkw 0x0dc3582bff7ed182 0x84370d60affdfb46 0x07c1f83ffffff1fb 0xbc1f07e0ffffffc7

def z176 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0x3ffe0000f87f000a 0x8cfff80003e1fc00

def z177 : W := mkw 0xb58cf52800000004 0x2ed633d4a0000000 0xf9cfffc00000003c 0xefe73fff00000000

def z178 : W := mkw 0x18c6c420c44336e1 0x20631b1083110cdb 0x39cec000c447ffc9 0x00e73b0003111fff

def z179 : W := mkw 0x0000004001950a40 0x1000000100065429 0x0000000007870e00 0x00000000001e1c38

def z180 : W := mkw 0x0040000250681180 0x800100000941a046 0x00000000007801c0 0x000000000001e007

def z181 : W := mkw 0xffbef7bc84032665 0x2ffefbdef2100c99 0xfffffffe04070e3e 0xeffffffff8101c38

def z182 : W := mkw 0xf7bcf7fc01950a44 0x3fdef3dff0065429 0xfffffffe07870e3e 0xeffffffff81e1c38

def z183 : W := mkw 0xe729180b3b3cc102 0x8f9ca4602cecf304 0xc601380f3bb80020 0xdf1804e03ceee000

def z184 : W := mkw 0xfffef7bcc44234a5 0x2ffffbdef31108d2 0xfffffffec000703e 0xeffffffffb0001c0

def z185 : W := mkw 0x0001004100808800 0x0000040104020220 0xc00107c107808e35 0x7300041f041e0238

def z186 : W := mkw 0x0010029400000000 0x0000400a50000000 0x000107fe00000000 0x2000041ff8000000

def z187 : W := mkw 0xfa3ea794a7160006 0x2be8fa9e529c5800 0xf83e07c007870004 0x43e0f81f001e1c00

def z188 : W := mkw 0xf7bdf7bf00088104 0x2fdef7defc002204 0xffffffff007881ff 0xfffffffffc01e207

def z189 : W := mkw 0xea2a0000a7160002 0x0ba8a800029c5800 0xf83e000007870004 0x43e0f800001e1c00

def z190 : W := mkw 0x1084f52800000004 0x204213d4a0000000 0x0000f80000000000 0x000003e000000000

def z191 : W := mkw 0xf7bdf7ff019d8b44 0x3fdef7dffc06762d 0xffffffff07ff8fff 0xfffffffffc1ffe3f

def z192 : W := mkw 0x422100c7019c8900 0x110884031c067224 0xc60101ff03f881f3 0x73180407fc0fe207

def z193 : W := mkw 0x0041084359fddbc0 0x900104210d67f76f 0x00000001ffffffc1 0x1000000007ffffff

def z194 : W := mkw 0x10d4c630404136e1 0x20435318c10104db 0x01c0c630c040ffdb 0x20070318c30103ff

def z195 : W := mkw 0xffbcf7bc84002404 0x2ffef3def2100090 0xfffffffec400fe3f 0xeffffffffb1003f8

def z196 : W := mkw 0x08420000f7760002 0x0021080003ddd800 0x39fe0001ffff001f 0x10e7f80007fffc00

def z197 : W := mkw 0x08010843af9def40 0x502004210ebe77bd 0x00000001ffffffc1 0x1000000007ffffff

def z198 : W := mkw 0xb00ca50000000004 0x2ac0329400000000 0x380e000000000000 0x00e0380000000000

def z199 : W := mkw 0xe768000050600000 0x0f9da00001418000 0xfffe0001f878003f 0xdffff80007e1e000

def z200 : W := mkw 0xef2a0000a7160002 0x0fbca800029c5800 0xfffe00000787003e 0xcffff800001e1c00

def z201 : W := mkw 0x1094c63000000000 0x20425318c0000000 0x39fec6300000001e 0x20e7fb18c0000000

def z202 : W := mkw 0xef6b2941fff6c802 0x4fbdaca507ffdb20 0xffff39c1ffff003f 0xdffffce707fffc00

def z203 : W := mkw 0x05d15a3b5869d3c0 0x84174568ed61a74f 0x07f1fe3ffc7fffff 0xbc1fc7f8fff1ffff

def z204 : W := mkw 0x42f742f741df9be1 0x310bdd0bdd077e6f 0xc7ff07ff07ff8ff7 0x731ffc1ffc1ffe3f

def z205 : W := mkw 0xf7bcf7bc000136e5 0x2fdef3def00004db 0xfffffffe0000fffe 0xeffffffff80003ff

def z206 : W := mkw 0x00010043019d8b40 0x100004010c06762d 0xc00107c107ff8ff5 0x7300041f041ffe3f

def z207 : W := mkw 0x0040000040401080 0x0001000001010042 0x00000000c040f1c1 0x00000000030103c7

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000100780033 0x101800000401e000

def z209 : W := mkw 0xa80a0000a6020002 0x0aa0280002980800 0x380e000000000000 0x00e0380000000000

def z210 : W := mkw 0x0000080008004000 0x0000002000200100 0x0000f800f8007008 0x8c0003e003e001c0

def z211 : W := mkw 0xf23ca79400000004 0x2bc8f29e50000000 0xf83fffc00000003c 0xefe0ffff00000000

def z212 : W := mkw 0xf7bdf7ff019c8904 0x3fdef7dffc067224 0xffffffff03b8003e 0xfffffffffc0ee000

def z213 : W := mkw 0x0dc3582bdc6bf7e1 0x84370d60af71afdf 0x07c1f83ffc7ffffb 0xbc1f07e0fff1ffff

def z214 : W := mkw 0x004108035868d180 0x800104200d61a346 0x00000001f878f1c1 0x1000000007e1e3c7

def z215 : W := mkw 0xb094f7bc00000004 0x2ac253def0000000 0xf801fffe0000003c 0xefe007fff8000000

def z216 : W := mkw 0x001002d400810a40 0x1000400b50020429 0x000007c000000e00 0x0000001f00000038

def z217 : W := mkw 0xb000a50000000000 0x0ac0029400000000 0xf80007c000000004 0x43e0001f00000000

def z218 : W := mkw 0x05c0582a58685180 0x84170160a961a146 0x07c0f83ef87871ca 0x8c1f03e0fbe1e1c7

def z219 : W := mkw 0xad4a0000f7760002 0x0eb5280003ddd800 0x39ce0001ffff0009 0x9ce7380007fffc00

def z220 : W := mkw 0xfffec630c44336e1 0x2ffffb18c3110cdb 0xfffec630c447ffff 0xeffffb18c3111fff

def z221 : W := mkw 0x000108030808c100 0x000004200c202304 0x0601f83ff878f1fb 0xbc1807e0ffe1e3c7

def z222 : W := mkw 0x08430841eec3fee1 0x40210c2107bb0ffb 0x00000001ffc7ffc1 0x1000000007ff1fff

def z223 : W := mkw 0x0541180b5868d180 0x841504602d61a346 0x0601380ff878f1e1 0x9c1804e03fe1e3c7

def z224 : W := mkw 0x001102d700898b40 0x1000440b5c02262d 0x000107fe00008fc0 0x2000041ff800023f

def z225 : W := mkw 0x47f152ff51fd9bc0 0x951fc54bfd47f66f 0xc7f107ff07ff8ff7 0x731fc41ffc1ffe3f

def z226 : W := mkw 0x1095ffbf0808d184 0xa04257fefc202346 0x0001fffe0000f1c0 0x200007fff80003c7

def z227 : W := mkw 0x00010043019d8b40 0x100004010c06762d 0x0601003f07ff8ff3 0x30180400fc1ffe3f

def z228 : W := mkw 0xef6b0043f7ff8b42 0x1fbdac010fdffe2d 0xfffe0001ffff8fff 0xdffff80007fffe3f

def z229 : W := mkw 0xbdd7ff7bfeebffe1 0xeef75ffdeffbafff 0xffffffffffffffff 0xffffffffffffffff

def z230 : W := mkw 0x08420000c4420000 0x0021080003110800 0x39fe0000c447001f 0x00e7f80003111c00

def z231 : W := mkw 0x1095de3b0809f7e1 0xa0425778ec2027df 0x0001fe3e0000ffc0 0x200007f8f80003ff

def z232 : W := mkw 0xeffb5affffffdbc2 0x9fbfed6bffffff6f 0xffffffffffffffff 0xffffffffffffffff

def z233 : W := mkw 0xfa21adc7af9ced00 0x5be886b71ebe73b4 0xfe01ffcfffb8fe3d 0xfff807ff3ffee3f8

def z234 : W := mkw 0xe7e9582b5868d180 0x8f9fa560ad61a346 0xfffff83ff878f1ff 0xffffffe0ffe1e3c7

def z235 : W := mkw 0x00c1582b5868d180 0x80030560ad61a346 0x0001f83ff878f1c1 0x300007e0ffe1e3c7

def z236 : W := mkw 0xad4a0000f6620002 0x0eb5280003d98800 0xf9ce0001ff80003d 0xdfe7380007fe0000

def z237 : W := mkw 0x0000318c00000004 0x000000c630000000 0x000139ce00000000 0x000004e738000000

def z238 : W := mkw 0x18d7c633c44bb7e1 0x20635f18cf112edf 0x3fffc63fc47fffff 0x30ffff18ff11ffff

def z239 : W := mkw 0x42300296011d0340 0x1108c00a5804740d 0x0630003e007f01c2 0x0018c000f801fc07

def z240 : W := mkw 0xe72900c733bc8902 0x1f9ca4031ccef224 0xc60101cf3bb80020 0xdf1804073ceee000

def z241 : W := mkw 0x08430043f7ff8b42 0x10210c010fdffe2d 0x00000001ffff8fc1 0x1000000007fffe3f

def z242 : W := mkw 0x42310297011d8340 0x1108c40a5c04760d 0x0631003f007f81f3 0x3018c400fc01fe07

def z243 : W := mkw 0xb001ad410880ec00 0x4ac006b5042203b0 0xf801ffc00000fe3c 0xefe007ff000003f8

def z244 : W := mkw 0x08010841ae80ec00 0x4020042106ba03b0 0x0001f801ff80fe39 0xbc0007e007fe03f8

def z245 : W := mkw 0x4f6a0000d5760002 0x053da8000355d800 0x3ffe0000c47f001f 0x00fff8000311fc00

def z246 : W := mkw 0xadca5828fe625082 0x8eb72960a3f98942 0x39cef800f8007008 0x8ce73be003e001c0

def z247 : W := mkw 0x15d5de3b5868d180 0xa4575778ed61a346 0x3ffffe3ff878f1ff 0xbcfffff8ffe1e3c7

def z248 : W := mkw 0xad400000f6600000 0x0eb5000003d98000 0xffc00001fff8003f 0xdfff000007ffe000

def z249 : W := mkw 0x18d7ce33dc6bf7e1 0xa0635f38cf71afdf 0x39fec631fc7fffdf 0x30e7fb18c7f1ffff

def z250 : W := mkw 0x1894c630840136e1 0x20625318c21004db 0x3800c630c400ffdd 0x20e00318c31003ff

def z251 : W := mkw 0x47fe52bc51760006 0x251ff94af145d800 0x07fe003e007f0002 0x001ff800f801fc00

def z252 : W := mkw 0x05c0502850601080 0x84170140a1418042 0x01c0000000000000 0x0007000000000000

def z253 : W := mkw 0xef7a02d4f7f70a42 0x1fbde80b53dfdc29 0xfffe07c1ffff0e3f 0xdffff81f07fffc38

def z254 : W := mkw 0x422a000001160002 0x0108a80000045800 0x003e000000070000 0x0000f80000001c00

def z255 : W := mkw 0x4a620000c5560000 0x0129880003155800 0xfffe0001c7ff003f 0x53fff800071ffc00

def z256 : W := mkw 0xfafec630e75736e3 0x2bebfb18c39d5cdb 0xf9fec630c7c7ffdf 0x63e7fb18c31f1fff

def z257 : W := mkw 0x0d420000f7760002 0x0435080003ddd800 0x07c00001ffff003b 0x9c1f000007fffc00

def z258 : W := mkw 0xe768000073740002 0x0f9da00001cdd000 0xc7c00001fbf8003b 0xdf1f000007efe000

def z259 : W := mkw 0xef6b0003f77e8102 0x0fbdac000fddfa04 0xffff003fffff81ff 0xfffffc00fffffe07

def z260 : W := mkw 0xb8d6ef30ee4376e1 0x6ae35bbcc3b90ddb 0x39fefe30fc47ffdf 0xace7fbf8c3f11fff

def z261 : W := mkw 0xad4a0000f6620002 0x0eb5280003d98800 0x39ce0000f8000008 0x8ce7380003e00000

def z262 : W := mkw 0x5af6c6f4c5d73ee1 0x316bdb1bd3175cfb 0xf9fec7f0c7c7ffdf 0x63e7fb1fc31f1fff

def z263 : W := mkw 0xb580f52800000000 0x0ed603d4a0000000 0xffc1fffe0000003e 0xefff07fff8000000

def z264 : W := mkw 0xff7bafd7ffffef42 0x5ffdeebf5fffffbd 0xffffffffffffffff 0xffffffffffffffff

def z265 : W := mkw 0x0802000084020000 0x0020080002100800 0x383e000004070004 0x00e0f80000101c00

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001f8000039 0x9c00000007e00000

def z267 : W := mkw 0x1081fd6b0888fd80 0xc04207f5ac2223f6 0x0001fffe0000ffc0 0x200007fff80003ff

def z268 : W := mkw 0xb800ad00ae006400 0x4ae002b402b80190 0xf800f801ff80703d 0xdfe003e007fe01c0

def z269 : W := mkw 0xb001ad412a80ec00 0x4ac006b504aa03b0 0xc001ffc13b80fe20 0xff0007ff04ee03f8

def z270 : W := mkw 0x0001004100808800 0x0000040104020220 0x0000000107808e01 0x10000000041e0238

def z271 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x0000c630c447ffc1 0x20000318c3111fff

def z272 : W := mkw 0x00110253019d8b40 0x100044094c06762d 0x0030063107ff8fd7 0x3000c018c41ffe3f

def z273 : W := mkw 0x4f6a0000f7760002 0x053da80003ddd800 0x07fe0001ffff0003 0x101ff80007fffc00

def z274 : W := mkw 0xeffe52bcf7760006 0x2fbff94af3ddd800 0xfffe003fffff003f 0xdffff800fffffc00

def z275 : W := mkw 0x0040000040400000 0x0001000001010000 0x01c00000c040001b 0x0007000003010000

def z276 : W := mkw 0x1816861084032661 0x20605a1842100c99 0x383ec600c407fe1d 0x20e0fb1803101ff8

def z277 : W := mkw 0x00420000404312e1 0x0001080001010c4b 0x00000000004701c0 0x0000000000011c07

def z278 : W := mkw 0xf7bcf7bc33340006 0x2fdef3def0ccd000 0xffffffff3bb8003e 0xfffffffffceee000

def z279 : W := mkw 0x0010021000010240 0x0000400840000409 0x00300030004701c2 0x0000c000c0011c07

def z280 : W := mkw 0x000108410880c800 0x0000042104220320 0xc001ffc1ff80fe3d 0xff0007ff07fe03f8

def z281 : W := mkw 0x422100c7019c8900 0x110884031c067224 0xc60101cf03b80020 0x531804073c0ee000

def z282 : W := mkw 0xe728000033340002 0x0f9ca00000ccd000 0xfffe00013bb8003e 0xdffff80004eee000

def z283 : W := mkw 0x05c0582858605080 0x84170160a1618142 0x07c1f83ef800703a 0xac1f07e0fbe001c0

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000107800035 0x53000000041e0000

def z285 : W := mkw 0xa8420000f7760002 0x0aa1080003ddd800 0xf8000001ffff003d 0xdfe0000007fffc00

def z286 : W := mkw 0xfaf7eff7efdfffe1 0x7bebdfbfdfbf7fff 0xffffffffffffffff 0xffffffffffffffff

def z287 : W := mkw 0x4220000001140000 0x0108800000045000 0xc600000103b80020 0x53180000040ee000

def z288 : W := mkw 0x18d7ce71eec3fee1 0x60635f39c7bb0ffb 0x39fec631ffc7ffdf 0x30e7fb18c7ff1fff

def z289 : W := mkw 0xb801ad01ae00e400 0x4ae006b406b80390 0x3801f801f800f039 0xbce007e007e003c0

def z290 : W := mkw 0xfa3dafd5ae80ec04 0x6be8f6bf56ba03b0 0xf83fffc1ff80fe3d 0xffe0ffff07fe03f8

def z291 : W := mkw 0xb800ad00ae006400 0x4ae002b402b80190 0x3800fe00fc00fe1d 0xace003f803f003f8

def z292 : W := mkw 0xb59cf73800000004 0x2ed673dce0000000 0x39fefe300000001e 0xace7fbf8c0000000

def z293 : W := mkw 0xfffec630f7760002 0x2ffffb18c3ddd800 0xfffec631ffff003f 0xfffffb18c7fffc00

def z294 : W := mkw 0xb843ad41eec3fee1 0x4ae10eb507bb0ffb 0xf801ffc1ffc7fffd 0xffe007ff07ff1fff

def z295 : W := mkw 0xff6aa500f7760002 0x0ffdaa9403ddd800 0xffffffc1ffff003f 0xffffffff07fffc00

def z296 : W := mkw 0x1816861084032661 0x20605a1842100c99 0x383e060004070e04 0x00e0f81800101c38

def z297 : W := mkw 0xe7e9582b7b7cd182 0x8f9fa560adedf346 0xc7c1f83ffbf8f1fb 0xff1f07e0ffefe3c7

def z298 : W := mkw 0x0540000050600000 0x0415000001418000 0x07c00001f878003b 0x9c1f000007e1e000

def z299 : W := mkw 0x1094f7bc00000004 0x204253def0000000 0x39fffffe0000001e 0x20e7fffff8000000

def z300 : W := mkw 0x0581582b1828c100 0x84160560ac60a304 0x07c1f83f3838003a 0xbc1f07e0fce0e000

def z301 : W := mkw 0xe7a871ac00000004 0x0f9ea1c6b0000000 0xc7c1f9fe0000003a 0xef1f07e7f8000000

def z302 : W := mkw 0x05c0502a50681180 0x84170140a941a046 0x07c0003ff87801fb 0x9c1f0000ffe1e007

def z303 : W := mkw 0xad4a0000f6620002 0x0eb5280003d98800 0x39fe0000fc47001f 0x8ce7f80003f11c00

def z304 : W := mkw 0x4a7302d7c5dfbfe1 0x1129cc0b5f177eff 0xc63107ffc7fffff7 0x7318c41fff1fffff

def z305 : W := mkw 0xbdc0fd28fe607480 0xcef703f4a3f981d2 0x39c0f800f8007008 0x8ce703e003e001c0

def z306 : W := mkw 0x1014a79400000004 0x2040529e50000000 0x000007c000000000 0x0000001f00000000

def z307 : W := mkw 0x4220008400000000 0x0108800210000000 0xc60101ce00000020 0x4318040738000000

def z308 : W := mkw 0x47bd52ff019d8b44 0x351ef54bfc06762d 0xc7ff07ff07ff8ff7 0x731ffc1ffc1ffe3f

def z309 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fe063004470fc6 0x00e7f818c0111c3f

def z310 : W := mkw 0xe7bc73bc00000004 0x2f9ef1cef0000000 0xc7ff39fe00000022 0xcf1ffce7f8000000

def z311 : W := mkw 0xa8420000e6420000 0x0aa1080003990800 0xf9fe0001ffc7003f 0xdfe7f80007ff1c00

def z312 : W := mkw 0xb094e73000000000 0x2ac2539cc0000000 0xf9fffff00000003e 0xefe7ffffc0000000

def z313 : W := mkw 0x5ffed6bcc44336e5 0x257ffb5af3110cdb 0x3ffec63ec447ffdf 0x20fffb18fb111fff

def z314 : W := mkw 0x5af6c6b6c55f37e1 0x316bdb1adb157cdf 0x3ffec63ec47fffdf 0x20fffb18fb11ffff

def z315 : W := mkw 0x08430803ff7ed182 0x80210c200ffdfb46 0x00000001fffff1c1 0x1000000007ffffc7

def z316 : W := mkw 0xffbef7bca7160006 0x2ffefbdef29c5800 0xfffffffe0787003e 0xeffffffff81e1c00

def z317 : W := mkw 0xef6b0041f7f68802 0x0fbdac0107dfda20 0xffff07c1ffff8e3f 0xfffffc1f07fffe38

def z318 : W := mkw 0x1094c630000136e1 0x20425318c00004db 0x39fec6300000ffde 0x20e7fb18c00003ff

def z319 : W := mkw 0xf7fef7bc404312e5 0x2fdffbdef1010c4b 0xfffffffe004701fe 0xeffffffff8011c07

def z320 : W := mkw 0xf728b58c00000004 0x0fdca2d630000000 0xfe01ffce0000003c 0xeff807ff38000000

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030004081d3 0x20000000c0010207

def z322 : W := mkw 0x477102d751fd8b40 0x151dc40b5d47f62d 0xc7f107ffffff8fff 0xff1fc41ffffffe3f

def z323 : W := mkw 0xbdcef528c44234a5 0x2ef73bd4a31108d2 0x39cef800c0007008 0x8ce73be0030001c0

def z324 : W := mkw 0x47fe52bc404312e5 0x251ff94af1010c4b 0x07fe003e004701c2 0x001ff800f8011c07

def z325 : W := mkw 0x1801ad41ae80ec00 0x406006b506ba03b0 0x0001ffc1ff80fe01 0x300007ff07fe03f8

def z326 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf8013fc13f800e24 0xdfe004ff04fe0038

def z327 : W := mkw 0x000108010800c000 0x0000042004200300 0x0001380138000020 0x9c0004e004e00000

def z328 : W := mkw 0x5a3686d485972e61 0x3168da1b52165cb9 0xf83e07c007870e04 0x43e0f81f001e1c38

def z329 : W := mkw 0x42f642b6415f13e1 0x310bd90ad9057c4f 0x07fe003e007f01c2 0x001ff800f801fc07

def z330 : W := mkw 0x18d7de3bcc4bf7e1 0xa0635f78ef312fdf 0x39fffe3ec447ffdf 0x20e7fff8fb111fff

def z331 : W := mkw 0x5af6c6b4c44336e1 0x216bdb1ad3110cdb 0xffffc7fec447ffff 0x63ffff1ffb111fff

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z333 : W := mkw 0xfa31a7d7a79daf40 0x5be8c69f5e9e76bd 0xfe3107ff07ff8ff7 0x73f8c41ffc1ffe3f

def z334 : W := mkw 0x08010841ae80ec00 0x4020042106ba03b0 0xc00107c1ff80fe35 0x7300041f07fe03f8

def z335 : W := mkw 0x0581582b0808d180 0x84160560ac202346 0x07c1f83e0000f1fa 0xac1f07e0f80003c7

def z336 : W := mkw 0xe73933df019d8b44 0x1f9ce4cf7c06762d 0xc6313fff07ff8ff7 0xff18c4fffc1ffe3f

def z337 : W := mkw 0x47eb582b597ed182 0x851fad60ad65fb46 0x07fff83ff87ff1fb 0xbc1fffe0ffe1ffc7

def z338 : W := mkw 0x47ea502a517e1182 0x851fa940a945f846 0x07fe003e007f01c2 0x001ff800f801fc07

def z339 : W := mkw 0xfffffffdfff6ec06 0x6ffffffff7ffdbb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z340 : W := mkw 0x00c0402040401080 0x0003010081010042 0x01c00030004001c2 0x00070000c0010007

def z341 : W := mkw 0x42b15aff099ddbc0 0x910ac56bfc26776f 0xc631ffff07fffff7 0x7318c7fffc1fffff

def z342 : W := mkw 0xef6b0803ff7ed182 0x8fbdac200ffdfb46 0xfffe0001fffff1ff 0xdffff80007ffffc7

def z343 : W := mkw 0xbdcef528f6620006 0x2ef73bd4a3d98800 0x39cef800f8000008 0x8ce73be003e00000

def z344 : W := mkw 0xe7a8502800000000 0x0f9ea140a0000000 0xfffff83e0000003e 0xefffffe0f8000000

def z345 : W := mkw 0x4a620000f7760002 0x0129880003ddd800 0xc6300001ffff0037 0x5318c00007fffc00

def z346 : W := mkw 0x1000840000002400 0x0040021000000090 0x0000c6000000fe00 0x20000318000003f8

def z347 : W := mkw 0x4728108c00000004 0x051ca04230000000 0x0600000e00000000 0x0018000038000000

def z348 : W := mkw 0x1000a54000802c00 0x40400295000200b0 0x000007c000000e00 0x0000001f00000038

def z349 : W := mkw 0x1095ef710881fee1 0x604257bdc42207fb 0x0001fff00000ffc0 0x200007ffc00003ff

def z350 : W := mkw 0x08430803dc6bf7e1 0x80210c200f71afdf 0x00000001fc7fffc1 0x1000000007f1ffff

def z351 : W := mkw 0x18568610c4432661 0x20615a1843110c99 0x39fe0600c4470e1f 0x00e7f81803111c38

def z352 : W := mkw 0xb8d7ef71eec3fee1 0x6ae35fbdc7bb0ffb 0xf9fffff1ffc7ffff 0xffe7ffffc7ff1fff

def z353 : W := mkw 0x05d75a3b586bd3e1 0xa4175d68ed61af4f 0x07fff83ff87ff1fb 0xbc1fffe0ffe1ffc7

def z354 : W := mkw 0x0016021000030261 0x2000580840000c09 0x003e000000070000 0x0000f80000001c00

def z355 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1383f387801e2 0x9c1f04e0fce1e007

def z356 : W := mkw 0x0011025100818a40 0x0000440944020629 0xc03107f107c78ff7 0x7300c41fc41f1e3f

def z357 : W := mkw 0x1dc6dc28dc6274a1 0xa4771b70a37189d2 0x39cef800f8007008 0x8ce73be003e001c0

def z358 : W := mkw 0xb895ef71ae81fee1 0x6ae257bdc6ba07fb 0xf801fff1ff80fffd 0xffe007ffc7fe03ff

def z359 : W := mkw 0x18c0c420c4403480 0x00630310831100d2 0x39c0c630c440ffdf 0x20e70318c31103ff

def z360 : W := mkw 0xe76a000073760002 0x0f9da80001cdd800 0xc7fe00013bff0022 0xdf1ff80004effc00

def z361 : W := mkw 0xf7bcf7bc01140004 0x2fdef3def0045000 0xffffffff07ff003f 0xfffffffffc1ffc00

def z362 : W := mkw 0xa8010041a6808800 0x0aa00401069a0220 0xf80107c1ff808e3d 0xffe0041f07fe0238

def z363 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc03007c107ff8fc5 0x5300c01f041ffe3f

def z364 : W := mkw 0x0500100800000000 0x0414004020000000 0x0601380e00000020 0x8c1804e038000000

def z365 : W := mkw 0xb8c1ed61eec0fc80 0x4ae307b587bb03f2 0xf9c1fff1ffc0ffff 0xffe707ffc7ff03ff

def z366 : W := mkw 0xefea4020f7761082 0x0fbfa90083ddd842 0xfffec031fffff1ff 0xfffffb00c7ffffc7

def z367 : W := mkw 0x00d04230404112c0 0x00034108c101044b 0x01f0c630c447ffdf 0x2007c318c3111fff

def z368 : W := mkw 0xb001ad010800c000 0x0ac006b404200300 0xf801ffc1f800f03d 0xffe007ff07e003c0

def z369 : W := mkw 0x422100c7019c8900 0x110884031c067224 0xc63101cf07ff0037 0x5318c4073c1ffc00

def z370 : W := mkw 0xb811afd7ae89ef40 0x5ae046bf5eba27bd 0xf801ffffff80fffd 0xffe007fffffe03ff

def z371 : W := mkw 0x0dc1586bfee8fd80 0xc4370561affba3f6 0x07c1f83ffff8fffb 0xbc1f07e0ffffe3ff

def z372 : W := mkw 0x0080502800000000 0x00020140a0000000 0x0001f83e00000000 0x200007e0f8000000

def z373 : W := mkw 0x180184418480ac00 0x00600611061202b0 0xf801c7c1c780fe3d 0x73e0071f071e03f8

def z374 : W := mkw 0x10d6c630404312e1 0x20435b18c1010c4b 0x39fec630004701de 0x20e7fb18c0011c07

def z375 : W := mkw 0xef6b180bff7ec102 0x8fbdac602ffdfb04 0xffff380fffff003f 0xdffffce03ffffc00

def z376 : W := mkw 0x05c1586b58e8d980 0x84170561ad63a366 0xc7c1fffffff8ffff 0xff1f07ffffffe3ff

def z377 : W := mkw 0x001102d7019d8b40 0x1000440b5c06762d 0x000107ff07ff8fc1 0x3000041ffc1ffe3f

def z378 : W := mkw 0x0001000300088100 0x000004000c002204 0x0601000f00380020 0x101804003c00e000

def z379 : W := mkw 0x0001180b0808c100 0x800004602c202304 0x0001380e00000000 0x000004e038000000

def z380 : W := mkw 0x1000840000000000 0x0040021000000000 0x3800c6000000001c 0x20e0031800000000

def z381 : W := mkw 0x4220000001140000 0x0108800000045000 0x06300000007f0002 0x0018c0000001fc00

def z382 : W := mkw 0x52b5f7ff019d8b44 0x314ad7dffc06762d 0xc631ffff07ff8ff7 0x7318c7fffc1ffe3f

def z383 : W := mkw 0x423c029400000004 0x2108f00a50000000 0x003e000000000000 0x0000f80000000000

def z384 : W := mkw 0x0080502a00081180 0x80020140a8002046 0x0000003e000001c0 0x00000000f8000007

def z385 : W := mkw 0x18428400c4422400 0x00610a1003110890 0x39fec600c447fe1f 0x20e7fb1803111ff8

def z386 : W := mkw 0x423002d401950a40 0x1108c00b50065429 0xc03007f007c78fd7 0x6300c01fc01f1e3f

def z387 : W := mkw 0xb800a540a6802c00 0x4ae00295029a00b0 0xf800c7c0c780fe1d 0x63e0031f031e03f8

def z388 : W := mkw 0xa8000000a6000000 0x0aa0000002980000 0xf800000007800004 0x43e00000001e0000

def z389 : W := mkw 0x00000000000136e1 0x00000000000004db 0x000000000000ffc0 0x00000000000003ff

def z390 : W := mkw 0x1896c630840336e1 0x20625b18c2100cdb 0x383ec6300407ffc4 0x20e0fb18c0101fff

def z391 : W := mkw 0x15d5de3b5869f7e1 0xa4575778ed61a7df 0x07c1fe3ff878fffb 0xbc1f07f8ffe1e3ff

def z392 : W := mkw 0xf7bcf7be011d0344 0x3fdef3def804740d 0xfffffffe007f01fe 0xeffffffff801fc07

def z393 : W := mkw 0xb5ccfd2858605084 0xaed733f4a1618142 0x39cef800f8007008 0x8ce73be003e001c0

def z394 : W := mkw 0xf7bcc63000000000 0x2fdef318c0000000 0xfffec6300000003e 0xeffffb18c0000000

def z395 : W := mkw 0x476a000051760002 0x051da8000145d800 0xc7fe000107ff0037 0x531ff800041ffc00

def z396 : W := mkw 0xfa21ad41af94ec00 0x4be886b506be53b0 0xfe31ffc1fffffe3f 0xfff8c7ff07fffff8

def z397 : W := mkw 0xf7bdffbf1828c104 0xafdef7fefc60a304 0xffffffff3838003e 0xfffffffffce0e000

def z398 : W := mkw 0xbdc1fd69fee0fc80 0xcef707f5a7fb83f2 0xf9c1ffc1ff80fe3d 0xffe707ff07fe03f8

def z399 : W := mkw 0xf7bdfffd0880ec04 0x6fdef7fff42203b0 0xfffffffe0000fe3e 0xeffffffff80003f8

def z400 : W := mkw 0xef280000a6000000 0x0fbca00002980000 0xfffe0001ff80003f 0xdffff80007fe0000

def z401 : W := mkw 0xa00129412a80c800 0x4a8004a504aa0320 0xc001f9c1fb80f039 0xff0007e707ee03c0

def z402 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffe07fe00000006 0x43fff81ff8000000

def z403 : W := mkw 0xa000214022800800 0x4a800085008a0020 0xc00001c003800000 0x43000007000e0000

def z404 : W := mkw 0x423002d401950a40 0x1108c00b50065429 0xc63007c107ff0e37 0x5318c01f041ffc38

def z405 : W := mkw 0x001102d700898b40 0x1000440b5c02262d 0x003107fe04478fd7 0x2000c41ff8111e3f

def z406 : W := mkw 0x423102d700898b40 0x1108c40b5c02262d 0xc63107fe00008ff6 0x6318c41ff800023f

def z407 : W := mkw 0xb58cf52800000004 0x2ed633d4a0000000 0x3fcff83e0000003a 0xacff3fe0f8000000

def z408 : W := mkw 0xef280000b7340002 0x0fbca00002dcd000 0xfe000001ffb8003d 0xdff8000007fee000

def z409 : W := mkw 0x00c64020404210a1 0x2003190081010842 0x01ce000000000000 0x0007380000000000

def z410 : W := mkw 0x18018c41ae80ec00 0x4060063106ba03b0 0x3800c601ff80fe1d 0x30e0031807fe03f8

def z411 : W := mkw 0x08520210c4430240 0x0021480843110c09 0x39fe0630c4478fdf 0x20e7f818c3111e3f

def z412 : W := mkw 0x1816861084032661 0x20605a1842100c99 0x383e063004478fd7 0x20e0f818c0111e3f

def z413 : W := mkw 0xefea5028f7760002 0x0fbfa940a3ddd800 0xfffff83fffff003f 0xffffffe0fffffc00

def z414 : W := mkw 0x42300296011d0340 0x1108c00a5804740d 0xc630003f07ff01f7 0x5318c000fc1ffc07

def z415 : W := mkw 0x0042000051760002 0x000108000145d800 0x00000000007f0000 0x000000000001fc00

def z416 : W := mkw 0x4230029401140000 0x0108c00a50045000 0xc63107ff07ff0037 0x7318c41ffc1ffc00

def z417 : W := mkw 0xffffffbfdc6bf7e5 0xaffffffeff71afdf 0xfffffffffc7fffff 0xfffffffffff1ffff

def z418 : W := mkw 0xf7fdffff59fddbc4 0xbfdff7fffd67f76f 0xffffffffffffffff 0xffffffffffffffff

def z419 : W := mkw 0x08520210c44336e1 0x0021480843110cdb 0x00300630c447ffd7 0x2000c018c3111fff

def z420 : W := mkw 0x5a3186d7859daf40 0x1168c61b5e1676bd 0xfe31c7ffc7ffffff 0x73f8c71fff1fffff

def z421 : W := mkw 0x0081582b0808d180 0x80020560ac202346 0x0601f83f0078f1f3 0x301807e0fc01e3c7

def z422 : W := mkw 0xffeef528f7760006 0x2fffbbd4a3ddd800 0xfffef801ffff003f 0xdffffbe007fffc00

def z423 : W := mkw 0x47bc52be011d0344 0x351ef14af804740d 0x07fe003e007f01c2 0x001ff800f801fc07

def z424 : W := mkw 0xffebfd6bfffefd82 0xcfffaff5affffbf6 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63101ff03ff01e2 0x5318c407fc0ffc07

def z426 : W := mkw 0xef6a0000f6620002 0x0fbda80003d98800 0xfffe0000f800003e 0xcffff80003e00000

def z427 : W := mkw 0xfa2bad41af96ec02 0x4be8aeb506be5bb0 0xf83fffc1ff87fe3d 0xffe0ffff07fe1ff8

def z428 : W := mkw 0x08420000f6620002 0x0021080003d98800 0x00000000f8000000 0x0000000003e00000

def z429 : W := mkw 0xb800ad00ae006400 0x4ae002b402b80190 0xf801ffc0f800703c 0xefe007ff03e001c0

def z430 : W := mkw 0x00915aff0889dbc0 0x9002456bfc22276f 0x0001fffe0000ffc0 0x200007fff80003ff

def z431 : W := mkw 0x47bc52bc00000004 0x251ef14af0000000 0x07fff83e0000003a 0xac1fffe0f8000000

def z432 : W := mkw 0x1001ad410880ec00 0x404006b5042203b0 0xc001ffc10780fe35 0x730007ff041e03f8

def z433 : W := mkw 0xffbcf7bca6000004 0x2ffef3def2980000 0xffffffffff80003f 0xfffffffffffe0000

def z434 : W := mkw 0xff7e8610f7772663 0x2ffdfa1843dddc99 0xfffe0601ffff0e3f 0xdffff81807fffc38

def z435 : W := mkw 0x1896c63084032661 0x20625b18c2100c99 0x39fec63004070e1e 0x20e7fb18c0101c38

def z436 : W := mkw 0x18d7ef71ccc3fee1 0x60635fbdc7330ffb 0x39fffff0c447ffdf 0x20e7ffffc3111fff

def z437 : W := mkw 0xb811af51ae81ee40 0x4ae046bd46ba07b9 0xf831fff1ffc7ffff 0xffe0c7ffc7ff1fff

def z438 : W := mkw 0xbddec630f66336e3 0x2ef77b18c3d98cdb 0x39fec630fc47ffdf 0xace7fb18c3f11fff

def z439 : W := mkw 0x004108035868d180 0x800104200d61a346 0x0001f801f878f1f9 0xbc0007e007e1e3c7

def z440 : W := mkw 0x05c0502850600000 0x04170140a1418000 0x07c1f83ff878003b 0xbc1f07e0ffe1e000

def z441 : W := mkw 0xff29bdcdae80ec04 0x4ffca6f736ba03b0 0xfe01ffcfff80fe3d 0xfff807ff3ffe03f8

def z442 : W := mkw 0x1011afd70889ef40 0x504046bf5c2227bd 0x0001fffe0000ffc0 0x200007fff80003ff

def z443 : W := mkw 0x4220000001140000 0x0108800000045000 0xc030000007870004 0x4300c000001e1c00

def z444 : W := mkw 0x0541180b5868c100 0x841504602d61a304 0x07c1380ff878003b 0x9c1f04e03fe1e000

def z445 : W := mkw 0xef7a0210f7770242 0x0fbde80843dddc09 0xfffe0631ffff8fff 0xfffff818c7fffe3f

def z446 : W := mkw 0xffffc6f7f7ffbfe3 0x3fffff1bdfdffeff 0xffffc7ffffffffff 0xffffff1fffffffff

def z447 : W := mkw 0x1000a50000000000 0x0040029400000000 0x0001ffc000000000 0x200007ff00000000

def z448 : W := mkw 0x0500180818204000 0x8414006020608100 0x0000380038000000 0x8c0000e000e00000

def z449 : W := mkw 0x0500000010200000 0x0414000000408000 0x0600000138380020 0x9c18000004e0e000

def z450 : W := mkw 0x47b052bc00000000 0x051ec14af0000000 0xc7f1fffe0000003e 0xef1fc7fff8000000

def z451 : W := mkw 0x0580502800000000 0x04160140a0000000 0x01c0f80000000008 0x8c0703e000000000

def z452 : W := mkw 0x1095c6f70089bfe1 0x3042571bdc0226ff 0x0001c7fe0000ffc0 0x2000071ff80003ff

def z453 : W := mkw 0xa8012941ae80c800 0x4aa004a506ba0320 0xf80139c1ff80003d 0xdfe004e707fe0000

def z454 : W := mkw 0x08420000c4420000 0x0021080003110800 0x39ce0000c0000008 0x00e7380003000000

def z455 : W := mkw 0xb8c6ed20ee4274a1 0x6ae31bb483b909d2 0x39cef800f8007008 0x8ce73be003e001c0

def z456 : W := mkw 0xbd4aad00fe626402 0x4ef52ab403f98990 0x39cef800f8007008 0x8ce73be003e001c0

def z457 : W := mkw 0x42210043019d8b40 0x110884010c06762d 0xc630000107ff8ff7 0x5318c000041ffe3f

def z458 : W := mkw 0x0540000050600000 0x0415000001418000 0x07c0000000780002 0x001f00000001e000

def z459 : W := mkw 0x1001ad410880ec00 0x404006b5042203b0 0x0001ffc1f800fe39 0xbc0007ff07e003f8

def z460 : W := mkw 0x4221004101948800 0x0108840104065220 0xc63107c107ff8e37 0x7318c41f041ffe38

def z461 : W := mkw 0x08c24020c44336e1 0x0023090083110cdb 0x01c0c030c447ffdb 0x20070300c3111fff

def z462 : W := mkw 0x054a000050620002 0x0415280001418800 0x01ce000000000000 0x0007380000000000

def z463 : W := mkw 0x000108031828c100 0x800004200c60a304 0x0000000138380000 0x1000000004e0e000

def z464 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x01c0f801f878f1c9 0x9c0703e007e1e3c7

def z465 : W := mkw 0x08420000c44234a1 0x00210800031108d2 0x00000000c0007000 0x00000000030001c0

def z466 : W := mkw 0xe2312bd72b9dcb40 0x5b88c4af5cae772d 0xc6313fff3fff8ff7 0xff18c4fffcfffe3f

def z467 : W := mkw 0xef6b0841fff6ec02 0x4fbdac2107ffdbb0 0xfffe0001fffffe3f 0xdffff80007fffff8

def z468 : W := mkw 0x1594d63800000000 0x24565358e0000000 0x3ffffe3e0000003e 0xacfffff8f8000000

def z469 : W := mkw 0x1800840084002400 0x0060021002100090 0x3800060004000e04 0x00e0001800100038

def z470 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xf9fe0000ff87000c 0xcfe7f80003fe1c00

def z471 : W := mkw 0x42210003011c8100 0x010884000c047204 0xc631003f07ff81f7 0x7318c400fc1ffe07

def z472 : W := mkw 0xe738339c00000004 0x0f9ce0ce70000000 0xc6313ffe00000036 0xef18c4fff8000000

def z473 : W := mkw 0xf73cb79c00000004 0x2fdcf2de70000000 0xfe3f3fce00000024 0xcff8fcff38000000

def z474 : W := mkw 0x05c0502840401080 0x04170140a1010042 0x07c1f83ec040f1fb 0xac1f07e0fb0103c7

def z475 : W := mkw 0x1dd6c630d46336e1 0x24775b18c3518cdb 0x3ffec631fc7fffff 0xbcfffb18c7f1ffff

def z476 : W := mkw 0xa8000000a6000000 0x0aa0000002980000 0x38000000f8000008 0x8ce0000003e00000

def z477 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xc6000001ffff0021 0xdf18000007fffc00

def z478 : W := mkw 0x0000000001140000 0x0000000000045000 0x0000000107ff0001 0x10000000041ffc00

def z479 : W := mkw 0x000108010800c000 0x0000042004200300 0x00000001f800f001 0x1000000007e003c0

def z480 : W := mkw 0x476a000051760002 0x051da8000145d800 0x07fe0001f87f003b 0x9c1ff80007e1fc00

def z481 : W := mkw 0xefea5828ff765082 0x8fbfa960a3fdd942 0xfffef801ffff703f 0xdffffbe007fffdc0

def z482 : W := mkw 0xbd81fd69ae80ec00 0x4ef607f5a6ba03b0 0xffc1ffffff80fe3f 0xffff07fffffe03f8

def z483 : W := mkw 0x0001000300088100 0x000004000c002204 0x0001003e000081c0 0x20000400f8000207

def z484 : W := mkw 0x00c1402340489180 0x000305008d012246 0x07c1c03fc078f1fb 0x301f0700ff01e3c7

def z485 : W := mkw 0x0501180b1828c100 0x841404602c60a304 0x0601383f387881f3 0xbc1804e0fce1e207

def z486 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0x3ffef83e0000000a 0x8cfffbe0f8000000

def z487 : W := mkw 0x0581502b00088100 0x04160540ac002204 0x07c1f83f007881fb 0xbc1f07e0fc01e207

def z488 : W := mkw 0xb001a54100808800 0x0ac0069504020220 0xf801ffc107808e3d 0xffe007ff041e0238

def z489 : W := mkw 0x18d6c630c44234a1 0x20635b18c31108d2 0x39fec630c000701e 0x20e7fb18c30001c0

def z490 : W := mkw 0x004108035868d180 0x800104200d61a346 0x0601003ff878f1f3 0x30180400ffe1e3c7

def z491 : W := mkw 0x10d4c63040401080 0x20435318c1010042 0x39fec630c040f1df 0x20e7fb18c30103c7

def z492 : W := mkw 0x0000000000010240 0x0000000000000409 0x0000000004478fc1 0x0000000000111e3f

def z493 : W := mkw 0x42200086011c0100 0x1108800218047004 0x0600000e00380000 0x001800003800e000

def z494 : W := mkw 0xea200000a7140000 0x0ba88000029c5000 0xfe300001ffff003f 0xdff8c00007fffc00

def z495 : W := mkw 0x05c1586b59fddbc0 0x94170561ad67f76f 0x07c1f83ffffffffb 0xbc1f07e0ffffffff

def z496 : W := mkw 0xfafee7b4c44336e5 0x2bebfb9ed3110cdb 0xf9fec7f0c447ffdf 0x63e7fb1fc3111fff

def z497 : W := mkw 0x0580502800000000 0x04160140a0000000 0x07c0003e00000002 0x001f0000f8000000

def z498 : W := mkw 0xfffffffdeec3fee5 0x6ffffffff7bb0ffb 0xffffffffffc7ffff 0xffffffffffff1fff

def z499 : W := mkw 0x47f15abf597dd3c0 0x951fc56afd65f74f 0x07f1f83ff87ff1fb 0xbc1fc7e0ffe1ffc7

def z500 : W := mkw 0x08000000a6000000 0x0020000002980000 0x00000001ff800001 0x1000000007fe0000

def z501 : W := mkw 0x18c6c420c44234a1 0x20631b10831108d2 0x39cec030c040f1db 0x20e73b00c30103c7

def z502 : W := mkw 0xef2a0000b7360002 0x0fbca80002dcd800 0xfe3e00013fbf0024 0xdff8f80004fefc00

def z503 : W := mkw 0x0500100a10280100 0x841400402840a004 0x0600000e00380000 0x001800003800e000

def z504 : W := mkw 0x52b4c6b400000000 0x214ad31ad0000000 0xffffc7fe0000003e 0x63ffff1ff8000000

def z505 : W := mkw 0xb5cdfd2b5868d184 0xaed737f4ad61a346 0x3fcff83ff878f1fb 0xbcff3fe0ffe1e3c7

def z506 : W := mkw 0x08410843fee8fd80 0xc02104210ffba3f6 0x00000001fff8ffc1 0x1000000007ffe3ff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030000004470017 0x0000c00000111c00

def z508 : W := mkw 0x00010043019c8900 0x100004010c067224 0x0000000103b80000 0x10000000040ee000

def z509 : W := mkw 0x0dc3582bdc6ad180 0x84370d60af71ab46 0x3ffff83ffc7ff1ff 0xbcffffe0fff1ffc7

def z510 : W := mkw 0x05c158295860d080 0x84170560a5618342 0x01c1f801f800f039 0xbc0707e007e003c0

def z511 : W := mkw 0x18d7c671c4c3bee1 0x20635f19c7130efb 0xf9ffc7f1c7c7ffff 0x73e7ff1fc71f1fff

def z512 : W := mkw 0x47e1582b597cd180 0x851f8560ad65f346 0xc7f1f83ffffff1ff 0xff1fc7e0ffffffc7

def z513 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c0003ff878f1c3 0x101f0000ffe1e3c7

def z514 : W := mkw 0xea2a0000a7160002 0x0ba8a800029c5800 0xf83e0001ff87003d 0xdfe0f80007fe1c00

def z515 : W := mkw 0xadcb582bfe6ad182 0x8eb72d60aff9ab46 0x3fcff83ff878f1fb 0xbcff3fe0ffe1e3c7

def z516 : W := mkw 0xb801ad43af9def40 0x5ae006b50ebe77bd 0xf801ffc1fffffffd 0xffe007ff07ffffff

def z517 : W := mkw 0xb8d6c630e64336e1 0x2ae35b18c3990cdb 0xf9fec631ffc7ffff 0xffe7fb18c7ff1fff

def z518 : W := mkw 0x0540000050600000 0x0415000001418000 0x01c00000f8000008 0x8c07000003e00000

def z519 : W := mkw 0x0001004300898b40 0x100004010c02262d 0x0000000000008fc0 0x000000000000023f

def z520 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xf9feffc00000000c 0xcfe7fbff00000000

def z521 : W := mkw 0xb801ad43ae88ed00 0x4ae006b50eba23b4 0xfe01fffffff8ffff 0xfff807ffffffe3ff

def z522 : W := mkw 0xff29ad41bfb4ec02 0x4ffca6b506fed3b0 0xfe01ffc1ffb8fe3d 0xfff807ff07fee3f8

def z523 : W := mkw 0xe72931cf019c8904 0x1f9ca4c73c067224 0xc60139cf03b80020 0xdf1804e73c0ee000

def z524 : W := mkw 0xb5c1fd2b5868d180 0x8ed707f4ad61a346 0xffc1fffff878f1ff 0xffff07ffffe1e3c7

def z525 : W := mkw 0xfa3ca7d4a6802c04 0x6be8f29f529a00b0 0xf83e07c007800e04 0x43e0f81f001e0038

def z526 : W := mkw 0xbd41ad41fee0ec00 0x4ef506b507fb83b0 0xffc1ffc1fff8fe3f 0xffff07ff07ffe3f8

def z527 : W := mkw 0xe729398f1828c104 0x8f9ca4e63c60a304 0xc60139cf38380020 0xdf1804e73ce0e000

def z528 : W := mkw 0xf23ca79400000004 0x2bc8f29e50000000 0xfe3f07fe00000036 0x63f8fc1ff8000000

def z529 : W := mkw 0xff6aa540f7f62c02 0x4ffdaa9503dfd8b0 0xfffe07c1ffff0e3f 0xdffff81f07fffc38

def z530 : W := mkw 0xe728318c33340006 0x0f9ca0c630ccd000 0xc60139cf3bb80020 0xdf1804e73ceee000

def z531 : W := mkw 0xf7fcffbc58605084 0xafdff3fef1618142 0xfffffffef800703e 0xeffffffffbe001c0

def z532 : W := mkw 0xff29ad41ae80ec00 0x4ffca6b506ba03b0 0xffffffc1ff80fe3f 0xffffffff07fe03f8

def z533 : W := mkw 0xea6a0000f7760002 0x0ba9a80003ddd800 0xf83e0001ffff0005 0x53e0f80007fffc00

def z534 : W := mkw 0x47fc52be50681184 0xa51ff14af941a046 0x07fe003e007801c2 0x001ff800f801e007

def z535 : W := mkw 0xa508000000000000 0x0e94200000000000 0x39ce000000000008 0x8ce7380000000000

def z536 : W := mkw 0x08020000a7160002 0x00200800029c5800 0x0000000007870000 0x00000000001e1c00

def z537 : W := mkw 0x1dc7dc2bdc6af5a1 0xa4771f70af71abd6 0x3fcff83ff878f1fb 0xbcff3fe0ffe1e3c7

def z538 : W := mkw 0x0080582808005080 0x80020160a0200142 0x0000f80000007000 0x000003e0000001c0

def z539 : W := mkw 0xf230a79400000000 0x0bc8c29e50000000 0xfe31fffe0000003e 0xeff8c7fff8000000

def z540 : W := mkw 0xa8010801ae00c000 0x0aa0042006b80300 0xf801f801ff80f03d 0xffe007e007fe03c0

def z541 : W := mkw 0xea3102d7a79d8b40 0x1ba8c40b5e9e762d 0xfe3107ffffff8fff 0xfff8c41ffffffe3f

def z542 : W := mkw 0x15d5ffbf5868d184 0xa45757fefd61a346 0x07c1fffff878f1fb 0xbc1f07ffffe1e3c7

def z543 : W := mkw 0xf7fcf7be50681184 0xafdff3def941a046 0xfffffffe007801fe 0xeffffffff801e007

def z544 : W := mkw 0x47fe4230517712e3 0x251ff908c145dc4b 0x07fe0030007f01c2 0x001ff800c001fc07

def z545 : W := mkw 0x1810861084012640 0x0060421842100499 0x3830c630c447ffdf 0x20e0c318c3111fff

def z546 : W := mkw 0x08000800ae006400 0x4020002002b80190 0x00000000f8007000 0x0000000003e001c0

def z547 : W := mkw 0xbd01bd4bbea8ed00 0xcef406f52efaa3b4 0xfe01ffcfffb8fe3d 0xfff807ff3ffee3f8

def z548 : W := mkw 0xb8c7ed61eec2fca1 0x6ae31fb587bb0bf2 0xf9cfffc1ff80fe3d 0xffe73fff07fe03f8

def z549 : W := mkw 0xbd4bad41fee2ec02 0x4ef52eb507fb8bb0 0xf9cfffc1ff80fe3d 0xffe73fff07fe03f8

def z550 : W := mkw 0x18d7c673c5dfbfe1 0x30635f19cf177eff 0x39fec631c7ffffdf 0x30e7fb18c71fffff

def z551 : W := mkw 0xa8010841ae80ec00 0x4aa0042106ba03b0 0xf8000001ff80fe3d 0xdfe0000007fe03f8

def z552 : W := mkw 0xffffffbfff7ed186 0xaffffffefffdfb46 0xfffffffffffff1ff 0xffffffffffffffc7

def z553 : W := mkw 0xb881fd6bae88fd80 0xcae207f5aeba23f6 0xf801ffffff80fffd 0xffe007fffffe03ff

def z554 : W := mkw 0xb800a540a6802c00 0x4ae00295029a00b0 0xf801ffc007800e3c 0xefe007ff001e0038

def z555 : W := mkw 0xff6a8400f7762402 0x0ffdaa1003ddd890 0xfffec601fffffe3f 0xfffffb1807fffff8

def z556 : W := mkw 0x1801ad418c80ec00 0x406006b5063203b0 0x3801ffc0c400fe1d 0x20e007ff031003f8

def z557 : W := mkw 0x000129410880c800 0x400004a504220320 0x000139c000000000 0x000004e700000000

def z558 : W := mkw 0xa8012941ae80ec00 0x4aa004a506ba03b0 0xc00139c1ff80fe21 0xdf0004e707fe03f8

def z559 : W := mkw 0x000108410880ec00 0x40000421042203b0 0x000000000000fe00 0x00000000000003f8

def z560 : W := mkw 0x4a310ad7af9def40 0x5128c42b5ebe77bd 0xc63107fffffffff7 0x7318c41fffffffff

def z561 : W := mkw 0xe228218400000004 0x0b88a08610000000 0xc00001c000000000 0x4300000700000000

def z562 : W := mkw 0xfffff7fff7ff8b46 0x3fffffdfffdffe2d 0xffffffffffff8fff 0xfffffffffffffe3f

def z563 : W := mkw 0x05d15aff58e9dbc0 0x9417456bfd63a76f 0x07c1fffff878fffb 0xbc1f07ffffe1e3ff

def z564 : W := mkw 0x42300296011d0340 0x1108c00a5804740d 0xc63107fe007f01f6 0x6318c41ff801fc07

def z565 : W := mkw 0x1dd6d638c44336e1 0x24775b58e3110cdb 0x3ffffe3ec447ffff 0xacfffff8fb111fff

def z566 : W := mkw 0x0541000350688100 0x041504000d41a204 0x07c1003ff87881fb 0xbc1f0400ffe1e207

def z567 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0x3800f801ff80fe09 0x9ce003e007fe03f8

def z568 : W := mkw 0x47b152ff019d8b40 0x151ec54bfc06762d 0xc7f1ffff07ff8fff 0xff1fc7fffc1ffe3f

def z569 : W := mkw 0x52b5c6f7019dbfe1 0x314ad71bdc0676ff 0xc631c7ff07fffff7 0x7318c71ffc1fffff

def z570 : W := mkw 0x18d7c6f7c4cbbfe1 0x30635f1bdf132eff 0x39ffc7fec447ffdf 0x20e7ff1ffb111fff

def z571 : W := mkw 0x4230029400000000 0x0108c00a50000000 0xc03007c000000004 0x4300c01f00000000

def z572 : W := mkw 0x4728000011340002 0x051ca0000044d000 0x0600000000380000 0x001800000000e000

def z573 : W := mkw 0x0094423000000000 0x20025108c0000000 0x01fe003000000002 0x0007f800c0000000

def z574 : W := mkw 0xbdc1fd2bfe68f580 0xcef707f4aff9a3d6 0x3fc1f83ff878f1fb 0xbcff07e0ffe1e3c7

def z575 : W := mkw 0xe728000001140000 0x0f9ca00000045000 0xfffe000107ff003f 0xdffff800041ffc00

def z576 : W := mkw 0xf231a7d7019d8b40 0x1bc8c69f5c06762d 0xfe31ffff07ff8fff 0xfff8c7fffc1ffe3f

def z577 : W := mkw 0x0802000084032661 0x0020080002100c99 0x0000000004070e00 0x0000000000101c38

def z578 : W := mkw 0x1dd6de38dc6376e1 0xa4775b78e3718ddb 0x39fefe30fc47ffdf 0xace7fbf8c3f11fff

def z579 : W := mkw 0x422100c7019c8900 0x110884031c067224 0xc60107cf07b88e35 0x7318041f3c1ee238

def z580 : W := mkw 0xffbdffffaf9def44 0x7ffef7fffebe77bd 0xffffffffffffffff 0xffffffffffffffff

def z581 : W := mkw 0xfa3e8610a7172663 0x2be8fa18429c5c99 0xf83e060007870e04 0x43e0f818001e1c38

def z582 : W := mkw 0xff6aad00ff766402 0x4ffdaab403fdd990 0xfffef801ffff703f 0xdffffbe007fffdc0

def z583 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39cec630c000ffc8 0x20e73b18c30003ff

def z584 : W := mkw 0xf728a50000000000 0x0fdca29400000000 0xffffffc00000003e 0xefffffff00000000

def z585 : W := mkw 0x18018c018c00e400 0x0060063006300390 0x3801fe01fc00fe3d 0xbce007f807f003f8

def z586 : W := mkw 0xfff1fffffffdffc0 0xdfffc7fffffff7ff 0xfff1ffffffffffff 0xffffc7ffffffffff

def z587 : W := mkw 0xffffef71fff7fee3 0x6fffffbdc7ffdffb 0xfffffff1ffffffff 0xffffffffc7ffffff

def z588 : W := mkw 0xfa31afd5af95ee40 0x5be8c6bf56be57b9 0xf831ffc1ff87fe3d 0xffe0c7ff07fe1ff8

def z589 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0x0630003f07ff8fc3 0x1018c000fc1ffe3f

def z590 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec030c04771ca 0x00e7fb00c3011dc7

def z591 : W := mkw 0x0d420000d4620000 0x0435080003518800 0x3ffe0001fc7f003f 0x9cfff80007f1fc00

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f80000000038 0xac0007e000000000

def z593 : W := mkw 0xb841ad43fee8fd80 0xcae106b50ffba3f6 0xf801ffc1fff8fffd 0xffe007ff07ffe3ff

def z594 : W := mkw 0x0001004100808800 0x0000040104020220 0xc00101c103800020 0x53000407040e0000

def z595 : W := mkw 0xf7bdf7fd00808804 0x2fdef7dff4020220 0xffffffff07808e3f 0xfffffffffc1e0238

def z596 : W := mkw 0x15c1fd6b58e8fd80 0xc45707f5ad63a3f6 0x07c1fffff878fffb 0xbc1f07ffffe1e3ff

def z597 : W := mkw 0x0000000200080100 0x0000000008002004 0x0600003e007801c2 0x00180000f801e007

def z598 : W := mkw 0x1800840084002400 0x0060021002100090 0x3800c000c0007008 0x00e00300030001c0

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c000c000f019 0x20000300030003c0

def z600 : W := mkw 0x4728000000000000 0x051ca00000000000 0x07fe000000000002 0x001ff80000000000

def z601 : W := mkw 0x4a7302d7f7ff8b42 0x1129cc0b5fdffe2d 0xc63107ffffff8ff7 0x7318c41ffffffe3f

def z602 : W := mkw 0x5a3786d7859faf61 0x3168de1b5e167ebd 0xfe3f07ff07ff8ff7 0x73f8fc1ffc1ffe3f

def z603 : W := mkw 0x00c148214840d080 0x0003052085210342 0x01c1f831f840f1fb 0xbc0707e0c7e103c7

def z604 : W := mkw 0xf7fef7bc51760006 0x2fdffbdef145d800 0xfffffffe007f003e 0xeffffffff801fc00

def z605 : W := mkw 0xe72939cd2a80c804 0x4f9ca4e734aa0320 0xc60139cf3b800020 0xdf1804e73cee0000

def z606 : W := mkw 0xf73ca79400000004 0x2fdcf29e50000000 0xfffe07c00000003e 0xcffff81f00000000

def z607 : W := mkw 0xe728000033340002 0x0f9ca00000ccd000 0xc63000013fff0037 0xdf18c00004fffc00

def z608 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xc601fffe00000020 0xef1807fff8000000

def z609 : W := mkw 0xb816a750a6832e61 0x6ae05a9d429a0cb9 0xf83e07c007870e04 0x43e0f81f001e1c38

def z610 : W := mkw 0x1094c63000010240 0x20425318c0000409 0x39fec63004478fdf 0x20e7fb18c0111e3f

def z611 : W := mkw 0xb8d6e730c44336e1 0x2ae35b9cc3110cdb 0xf9fffff0c447ffff 0xefe7ffffc3111fff

def z612 : W := mkw 0xe228000000000000 0x0b88a00000000000 0xf83e000000000004 0x43e0f80000000000

def z613 : W := mkw 0xa000000000000000 0x0a80000000000000 0xf80000000000003c 0xcfe0000000000000

def z614 : W := mkw 0xe76a000051760002 0x0f9da8000145d800 0xfffe0000007f003e 0xcffff8000001fc00

def z615 : W := mkw 0x1014861000000000 0x2040521840000000 0x383e060000000004 0x00e0f81800000000

def z616 : W := mkw 0x47e158ef59fcd980 0x951f8563bd67f366 0xc7c1f9fffbf8f1fb 0xff1f07e7ffefe3c7

def z617 : W := mkw 0x0501180b1828c100 0x841404602c60a304 0x0601f80ff838f039 0xbc1807e03fe0e3c0

def z618 : W := mkw 0x0001004100808800 0x0000040104020220 0x000107c000008e00 0x2000041f00000238

def z619 : W := mkw 0x00c0402040401080 0x0003010081010042 0x01c0c000c0007008 0x00070300030001c0

def z620 : W := mkw 0x0040080058605080 0x8001002001618142 0x00000000f8007000 0x0000000003e001c0

def z621 : W := mkw 0x05c0582858605080 0x84170160a1618142 0x07c0f801f878703b 0x9c1f03e007e1e1c0

def z622 : W := mkw 0xb801a541a680ac00 0x4ae00695069a02b0 0xf80107c107808e35 0x73e0041f041e0238

def z623 : W := mkw 0xa501394b3aa8c900 0xce9404e52ceaa324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z624 : W := mkw 0xf2bcf7bc00000004 0x2bcaf3def0000000 0xf83ffffe00000004 0x63e0fffff8000000

def z625 : W := mkw 0xf7bdffbf0808d184 0xafdef7fefc202346 0xfffffffe0000f1fe 0xeffffffff80003c7

def z626 : W := mkw 0x1094c630000136e1 0x20425318c00004db 0x0030c6300447ffd7 0x2000c318c0111fff

def z627 : W := mkw 0x1806840084022421 0x20601a1002100890 0x380e000000000000 0x00e0380000000000

def z628 : W := mkw 0x0040000050600000 0x0001000001418000 0x00000001f8780001 0x1000000007e1e000

def z629 : W := mkw 0xb000a50000000000 0x0ac0029400000000 0x3800f80000000008 0x8ce003e000000000

def z630 : W := mkw 0x05c0502a50681180 0x84170140a941a046 0x07c1f83e007801fa 0xac1f07e0f801e007

def z631 : W := mkw 0xb817af51ae83ee61 0x6ae05ebd46ba0fb9 0xf83fffc1ff87fe3d 0xffe0ffff07fe1ff8

def z632 : W := mkw 0x05c0502a50681180 0x84170140a941a046 0x07c0c03ec078f1db 0x201f0300fb01e3c7

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00107c000000034 0x6300041f00000000

def z634 : W := mkw 0xf7bdf7ff00898b44 0x3fdef7dffc02262d 0xfffffffe00008ffe 0xeffffffff800023f

def z635 : W := mkw 0xe73902d7019d8b40 0x1f9ce40b5c06762d 0xffff07ff07ff8fff 0xfffffc1ffc1ffe3f

def z636 : W := mkw 0x00d64230404312e1 0x20035908c1010c4b 0x01fec030c047f1db 0x2007fb00c3011fc7

def z637 : W := mkw 0xa00129412a80c800 0x4a8004a504aa0320 0xc0013fc13f808e35 0xff0004ff04fe0238

def z638 : W := mkw 0xb8008400a6002400 0x0ae0021002980090 0xf800c601ff80fe3d 0xffe0031807fe03f8

def z639 : W := mkw 0x0000004000800800 0x0000000100020020 0xc00007c007800e04 0x4300001f001e0038

def z640 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f80ff8387028 0x9c1f07e03fe0e1c0

def z641 : W := mkw 0xa508000032200002 0x0e94200000c88000 0x0000000038000000 0x8c00000000e00000

def z642 : W := mkw 0xe7bc52bc00000004 0x2f9ef14af0000000 0xfffe003e0000003e 0xcffff800f8000000

def z643 : W := mkw 0x47311adf19bdcb40 0x951cc46b7c66f72d 0xc6313fff3fff8ff7 0xff18c4fffcfffe3f

def z644 : W := mkw 0x009452bc00000004 0x2002514af0000000 0x0000003e00000000 0x00000000f8000000

def z645 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801ffc00780fe04 0x63e007ff001e03f8

def z646 : W := mkw 0xe7e979af5868d184 0x8f9fa5e6bd61a346 0xc7c1f9fff878f1fb 0xff1f07e7ffe1e3c7

def z647 : W := mkw 0x4230029400000000 0x0108c00a50000000 0x0630003e00000002 0x0018c000f8000000

def z648 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc60107ff03b88fe0 0x7318041ffc0ee23f

def z649 : W := mkw 0x42f142f741dd9bc0 0x110bc50bdd07766f 0xc7f1c7ffc7ffffff 0x731fc71fff1fffff

def z650 : W := mkw 0x5ff7deffddffffe1 0xb57fdf7bff77ffff 0xffffffffffffffff 0xffffffffffffffff

def z651 : W := mkw 0xa000000022000000 0x0a80000000880000 0xc00000013b800020 0xdf00000004ee0000

def z652 : W := mkw 0xf7bdfffd2a80c804 0x6fdef7fff4aa0320 0xffffffff3b80003e 0xfffffffffcee0000

def z653 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc03107fe07878fc4 0x6300c41ff81e1e3f

def z654 : W := mkw 0xbdcec420f66234a3 0x2ef73b1083d988d2 0x39cec000f8007008 0x8ce73b0003e001c0

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x0601003e00000032 0x20180400f8000000

def z656 : W := mkw 0x000100c700888900 0x100004031c022224 0x000101ce00000000 0x0000040738000000

def z657 : W := mkw 0xb843ad41eec2ec00 0x4ae10eb507bb0bb0 0xf9ffffc1ffc7fe3f 0xffe7ffff07ff1ff8

def z658 : W := mkw 0x47bc52bc00000004 0x251ef14af0000000 0xc7ff07fe00000036 0x631ffc1ff8000000

def z659 : W := mkw 0xef7a0296f77f0342 0x1fbde80a5bddfc0d 0xfffe003fffff01ff 0xdffff800fffffc07

def z660 : W := mkw 0xe72929413bb4c802 0x4f9ca4a504eed320 0xc60139c13bb80020 0xdf1804e704eee000

def z661 : W := mkw 0x0081582b0808d180 0x80020560ac202346 0x0001f83ff800f1f9 0xbc0007e0ffe003c7

def z662 : W := mkw 0x1084c42000000000 0x2042131080000000 0x39cec00000000008 0x00e73b0000000000

def z663 : W := mkw 0x57bcd6bc00000004 0x255ef35af0000000 0x3ffec63e0000001e 0x20fffb18f8000000

def z664 : W := mkw 0xe73902d733bd8b42 0x1f9ce40b5ccef62d 0xc63107ff3fff8ff7 0xff18c41ffcfffe3f

def z665 : W := mkw 0xea3a02d4a7970a42 0x1ba8e80b529e5c29 0xf83e07c007870e04 0x43e0f81f001e1c38

def z666 : W := mkw 0x477b02d751ff8b42 0x151dec0b5d47fe2d 0xc7ff07ff07ff8ff7 0x731ffc1ffc1ffe3f

def z667 : W := mkw 0xb843ad41fff6ec02 0x4ae10eb507ffdbb0 0xf801ffc1fffffe3d 0xffe007ff07fffff8

def z668 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63107cf07bf0e24 0x5318c41f3c1efc38

def z669 : W := mkw 0x000108010800c000 0x0000042004200300 0x0001f8000000f000 0x200007e0000003c0

def z670 : W := mkw 0x00c1582b4848d180 0x80030560ad212346 0x01c1f83ec040f1db 0x200707e0fb0103c7

def z671 : W := mkw 0x1000ad0008006400 0x404002b400200190 0x0000f80000007000 0x000003e0000001c0

def z672 : W := mkw 0x57bcf7bc00000004 0x255ef3def0000000 0x07fffffe00000002 0x201ffffff8000000

def z673 : W := mkw 0x1095fffd0880ec04 0x604257fff42203b0 0x0001fffe0000fe00 0x200007fff80003f8

def z674 : W := mkw 0x18d6c630f77736e3 0x20635b18c3dddcdb 0x39fec631ffffffdf 0x30e7fb18c7ffffff

def z675 : W := mkw 0xefea502af77e1182 0x8fbfa940abddf846 0xfffe003fffff01ff 0xdffff800fffffc07

def z676 : W := mkw 0xffbcf7fca6802c04 0x6ffef3dff29a00b0 0xfffffffe07800e3e 0xeffffffff81e0038

def z677 : W := mkw 0xff7ea794f7760006 0x2ffdfa9e53ddd800 0xfffe07c1ffff003f 0xdffff81f07fffc00

def z678 : W := mkw 0x0080402000001080 0x0002010080000042 0x0000c0300000f1c0 0x20000300c00003c7

def z679 : W := mkw 0x4230029401150240 0x1108c00a50045409 0x0030000000070000 0x0000c00000001c00

def z680 : W := mkw 0x1084c420000034a1 0x20421310800000d2 0x0000c00000007000 0x00000300000001c0

def z681 : W := mkw 0x000108030808d180 0x800004200c202346 0x000000000000f1c0 0x00000000000003c7

def z682 : W := mkw 0xeffe4230f77712e3 0x2fbff908c3dddc4b 0xfffe0031ffff01ff 0xdffff800c7fffc07

def z683 : W := mkw 0xe22129c72b9cc900 0x5b8884a71cae7324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z684 : W := mkw 0x4220000000000000 0x0108800000000000 0xc630000000000036 0x4318c00000000000

def z685 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe000007ff0006 0x43fff800001ffc00

def z686 : W := mkw 0x4230021001150240 0x0108c00840045409 0xc630063107ff8ff7 0x7318c018c41ffe3f

def z687 : W := mkw 0xfa3ea79484032665 0x2be8fa9e52100c99 0xf83e07c004070e04 0x43e0f81f00101c38

def z688 : W := mkw 0xe228000023140002 0x0b88a000008c5000 0xc000000003800000 0x43000000000e0000

def z689 : W := mkw 0x0001000300088100 0x000004000c002204 0x00000001007881c1 0x100000000401e207

def z690 : W := mkw 0x0001004300888900 0x000004010c022224 0xc60107ff07f88ff7 0x7318041ffc1fe23f

def z691 : W := mkw 0x1dd6d63ad46b37e1 0xa4775b58eb51acdf 0x3ffec63ec47fffdf 0x20fffb18fb11ffff

def z692 : W := mkw 0xef6b00c7f7fe8902 0x1fbdac031fdffa24 0xffff01cfffff003f 0xdffffc073ffffc00

def z693 : W := mkw 0x4a7302d7c5df8b40 0x1129cc0b5f177e2d 0xffff07ffc7ff8fff 0x73fffc1fff1ffe3f

def z694 : W := mkw 0x0042000040420000 0x0001080001010800 0x01fe000000470002 0x0007f80000011c00

def z695 : W := mkw 0x1094f7bc000136e5 0x204253def00004db 0x0001fffe0000ffc0 0x200007fff80003ff

def z696 : W := mkw 0xef6a0000f77736e3 0x0fbda80003dddcdb 0xfffe0001ffffffff 0xdffff80007ffffff

def z697 : W := mkw 0x472118cf19bcc900 0x951c84633c66f324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z698 : W := mkw 0x4760000051740000 0x051d80000145d000 0xc7f00001ffff003f 0xdf1fc00007fffc00

def z699 : W := mkw 0x0581582b1828d180 0x84160560ac60a346 0x0601f83f3838f1e0 0xbc1807e0fce0e3c7

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x39fe00000000001e 0x00e7f80000000000

def z701 : W := mkw 0xfffef7bcf6620006 0x2ffffbdef3d98800 0xfffffffef800003e 0xeffffffffbe00000

def z702 : W := mkw 0xfa2aa540a7962c02 0x4be8aa95029e58b0 0xf83e07c007870e04 0x43e0f81f001e1c38

def z703 : W := mkw 0xb895fffdae80ec04 0x6ae257fff6ba03b0 0xf801ffffff80fe3d 0xffe007fffffe03f8

def z704 : W := mkw 0xea6a0000e7560002 0x0ba9a800039d5800 0xf9fe0000c7c7001f 0x43e7f800031f1c00

def z705 : W := mkw 0xad4a0000f6620002 0x0eb5280003d98800 0x3fce0001f878003b 0x9cff380007e1e000

def z706 : W := mkw 0x423002d401950a40 0x1108c00b50065429 0xc63107fe07870e36 0x6318c41ff81e1c38

def z707 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf831ffc1ffc7fe3f 0xffe0c7ff07ff1ff8

def z708 : W := mkw 0x4f6a0000f7760002 0x053da80003ddd800 0x3ffe0001ffff001f 0x10fff80007fffc00

def z709 : W := mkw 0x18d6c6b4c44336e1 0x20635b1ad3110cdb 0x39ffc7fec447ffdf 0x20e7ff1ffb111fff

def z710 : W := mkw 0xf7bcf7bc000136e5 0x2fdef3def00004db 0xfffffffe0447ffff 0xeffffffff8111fff

def z711 : W := mkw 0xf73cb79c00000004 0x2fdcf2de70000000 0xffff3fce0000003e 0xcffffcff38000000

def z712 : W := mkw 0x1001ad410880ec00 0x404006b5042203b0 0xc001ffc1ff80fe3d 0xff0007ff07fe03f8

def z713 : W := mkw 0x18c2c420c4423480 0x00630b10831108d2 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z714 : W := mkw 0x0581582b1828d180 0x84160560ac60a346 0x0601f83ff838f1f9 0xbc1807e0ffe0e3c7

def z715 : W := mkw 0xbdc0f56af6e83d80 0xcef703d5abdba0f6 0xffc007fe07f80fc6 0x43ff001ff81fe03f

def z716 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffec001fffff03f 0xfffffb0007ffffc0

def z717 : W := mkw 0x18d6c630d46336e1 0x20635b18c3518cdb 0x39fec631fc7fffdf 0x30e7fb18c7f1ffff

def z718 : W := mkw 0xb58cf5ac00000004 0x2ed633d6b0000000 0x39cff9ce00000008 0x8ce73fe738000000

def z719 : W := mkw 0xb800ad40ae806c00 0x4ae002b502ba01b0 0xf800ffc0ff80fe1d 0xefe003ff03fe03f8

def z720 : W := mkw 0x42210043019c8900 0x010884010c067224 0xc63107ff07ff8ff7 0x7318c41ffc1ffe3f

def z721 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc60107ff07ff8fe1 0x7318041ffc1ffe3f

def z722 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f83ef878f1ca 0xac1f07e0fbe1e3c7

def z723 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xffff07c1ffff003f 0xfffffc1f07fffc00

def z724 : W := mkw 0x4fbd5afdae80ec04 0x653ef56bf6ba03b0 0x07fe003fff80fe03 0x101ff800fffe03f8

def z725 : W := mkw 0x18018c418c80ec00 0x00600631063203b0 0xf801ffc1ff80fe3d 0xffe007ff07fe03f8

def z726 : W := mkw 0xe768000051740000 0x0f9da0000145d000 0xfffe0001ffff003f 0xdffff80007fffc00

def z727 : W := mkw 0x5ae7c4e7c5debda1 0x316b9f139f177af6 0xffcfc1cfc3b87028 0x53ff3f073f0ee1c0

def z728 : W := mkw 0xa0d76b716ac3dae1 0x6a835dadc5ab0f6b 0xc1ff39f13bc701e2 0xdf07fce7c4ef1c07

def z729 : W := mkw 0xb001ad412a80ec00 0x4ac006b504aa03b0 0xc001ffc1fb80fe39 0xff0007ff07ee03f8

def z730 : W := mkw 0x47fc52be517d13c4 0xb51ff14af945f44f 0x07fe003e007f01c2 0x001ff800f801fc07

def z731 : W := mkw 0xef280000a7140000 0x0fbca000029c5000 0xfffe0001ffff003f 0xdffff80007fffc00

def z732 : W := mkw 0x08430843ddffffe1 0x90210c210f77ffff 0x00000001ffffffc1 0x1000000007ffffff

def z733 : W := mkw 0x18568610c44336e1 0x20615a1843110cdb 0x39fe0600c447ffdf 0x00e7f81803111fff

def z734 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801ffc0ff80fe0c 0xefe007ff03fe03f8

def z735 : W := mkw 0x18528610c4432640 0x00614a1843110c99 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z736 : W := mkw 0x47f05afc59f55ac0 0x951fc16bf167d56b 0xc1f0ffc0ff877e0c 0xcf07c3ff03fe1df8

def z737 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0x3ffffffe0000000a 0xacfffffff8000000

def z738 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec030c447ffcb 0x00e7fb00c3111fff

def z739 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0031ffff81ff 0xfffff800c7fffe07

def z740 : W := mkw 0x47f652be517f13e1 0xb51fd94af945fc4f 0x07fe003e007f01c2 0x001ff800f801fc07

def z741 : W := mkw 0x576bad4159f6ec02 0x455daeb50567dbb0 0x07ffffc0007ffe02 0x201fffff0001fff8

def z742 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xfe01ffffff80fe3f 0xfff807fffffe03f8

def z743 : W := mkw 0xe729394b3bbcc902 0xcf9ca4e52ceef324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z744 : W := mkw 0x05c0502850601080 0x04170140a1418042 0x07c1f83ff878f1fb 0xbc1f07e0ffe1e3c7

def z745 : W := mkw 0xe72929c73bbcc902 0x5f9ca4a71ceef324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z746 : W := mkw 0x05c1586b58e8d980 0x84170561ad63a366 0xc7c1f9fffbf8f1fb 0xff1f07e7ffefe3c7

def z747 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x3ffff83ff878f1ff 0xbcffffe0ffe1e3c7

def z748 : W := mkw 0xef6a318cc44336e5 0x0fbda8c633110cdb 0xc60139cec447ffe1 0xcf1804e73b111fff

def z749 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec630c407ffcc 0x20e7fb18c3101fff

def z750 : W := mkw 0xf27daf975868d184 0xabc9f6be5d61a346 0xf83e07c1f878f1c5 0x53e0f81f07e1e3c7

def z751 : W := mkw 0x18d6c630e64336e1 0x20635b18c3990cdb 0x39fec631ffc7ffdf 0x30e7fb18c7ff1fff

def z752 : W := mkw 0xbdc6fd28fe6274a1 0xeef71bf4a3f989d2 0x39cef800f8007008 0x8ce73be003e001c0

def z753 : W := mkw 0x18d6c630f66336e3 0x20635b18c3d98cdb 0x39fec630fc47ffdf 0x20e7fb18c3f11fff

def z754 : W := mkw 0x18d6d6bcc44336e5 0x20635b5af3110cdb 0x39fec63ec447ffdf 0x20e7fb18fb111fff

def z755 : W := mkw 0x1594f7bc00000004 0x245653def0000000 0x3ffffffe0000003e 0xacfffffff8000000

def z756 : W := mkw 0xeaab582baf1ed182 0x8baaad60aebc7b46 0xf83ff83e0787f1c4 0x63e0ffe0f81e1fc7

def z757 : W := mkw 0x1d179e1b9c2be761 0xa4745e786e70af9d 0x3e3f3e0f3c3f0e24 0x9cf8fcf83cf0fc38

def z758 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xf9fe0001ffff000d 0xdfe7f80007fffc00

def z759 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffff800003f 0xffffffffffe00000

def z760 : W := mkw 0xef6a0000f77634a3 0x0fbda80003ddd8d2 0xfffe0001ffff703f 0xdffff80007fffdc0

def z761 : W := mkw 0xef6a108cf7760006 0x0fbda84233ddd800 0xfffe000fffff003f 0xdffff8003ffffc00

def z762 : W := mkw 0x18d6f7bcc44336e5 0x20635bdef3110cdb 0x0001fffec447ffc1 0x200007fffb111fff

def z763 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0xf9fec631c7c7ffff 0x73e7fb18c71f1fff

def z764 : W := mkw 0xea6a0000f7760002 0x0ba9a80003ddd800 0xf9fe0001ffff001f 0x53e7f80007fffc00

def z765 : W := mkw 0x08430843efdfffe1 0x50210c210fbf7fff 0x00000001ffffffc1 0x1000000007ffffff

def z766 : W := mkw 0x1094f7bc00000004 0x204253def0000000 0x39cffffe00000008 0x20e73ffff8000000

def z767 : W := mkw 0xf7bcc630333536e3 0x2fdef318c0ccd4db 0xc600c6313bb8ffe0 0xff180318c4eee3ff

def z768 : W := mkw 0x08430843fffefd82 0xc0210c210ffffbf6 0x00000001ffffffc1 0x1000000007ffffff

def z769 : W := mkw 0x00010043019d8b40 0x100004010c06762d 0xc60107ff07ff8ff7 0x7318041ffc1ffe3f

def z770 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0001fbff002a 0xdffff80007effc00

def z771 : W := mkw 0x42310ad50995ca40 0x1108c42b54265729 0xc031ffc1ff87fe3d 0xff00c7ff07fe1ff8

def z772 : W := mkw 0xfa30af96af1d6740 0x5be8c2be5abc759d 0x3e30f83ef87f71ca 0x8cf8c3e0fbe1fdc7

def z773 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe00013fff0026 0xdffff80004fffc00

def z774 : W := mkw 0xf2bcf7bc00000004 0x2bcaf3def0000000 0xf9fffffe0000001e 0x63e7fffff8000000

def z775 : W := mkw 0xb58df56b019d8b44 0x3ed637d5ac06762d 0x39cef80107ff8fc9 0x9ce73be0041ffe3f

def z776 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0601ffff8e3f 0xfffff81807fffe38

def z777 : W := mkw 0xb59cf7bc00000004 0x2ed673def0000000 0x39fffffe0000001e 0xace7fffff8000000

def z778 : W := mkw 0x18d6f7bcf7760006 0x20635bdef3ddd800 0x0001ffffffff0001 0x300007fffffffc00

def z779 : W := mkw 0x05cd582b5868d184 0xa4173560ad61a346 0x07cff83ff878f1fb 0xbc1f3fe0ffe1e3c7

def z780 : W := mkw 0xad420000f6620000 0x0eb5080003d98800 0xfffe0001ffff003f 0xdffff80007fffc00

def z781 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffff9fe0000002a 0xcfffffe7f8000000

def z782 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xffffffce0000002c 0xcfffffff38000000

def z783 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fffe30c447ffff 0xace7fff8c3111fff

def z784 : W := mkw 0x423002d6019d0b40 0x1108c00b5806742d 0xc63107fe07ff0ff6 0x6318c41ff81ffc3f

def z785 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801ffc1fb80fe28 0xffe007ff07ee03f8

def z786 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xfe01ffc1fff8fe3f 0xfff807ff07ffe3f8

def z787 : W := mkw 0x08d24230c44312c0 0x00234908c3110c4b 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z788 : W := mkw 0x18d6d638c44336e1 0x20635b58e3110cdb 0x39fffe3ec447ffdf 0x20e7fff8fb111fff

def z789 : W := mkw 0x08430843ffffdbc2 0x90210c210fffff6f 0x00000001ffffffc1 0x1000000007ffffff

def z790 : W := mkw 0x05c7582b586ad1a1 0xa4171d60ad61ab46 0x07cff83ff878f1fb 0xbc1f3fe0ffe1e3c7

def z791 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xffff07ff07ff8fff 0x73fffc1ffc1ffe3f

def z792 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec630c047ffca 0x20e7fb18c3011fff

def z793 : W := mkw 0xf7bcf7bc00010244 0x2fdef3def0000409 0xfffffffe004701fe 0xeffffffff8011c07

def z794 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801fff1ffc0ffff 0xffe007ffc7ff03ff

def z795 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffe004081ff 0xeffffffff8010207

def z796 : W := mkw 0x10d4c630404112c0 0x20435318c101044b 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z797 : W := mkw 0x57bcf7bc00000004 0x255ef3def0000000 0x3ffffffe0000001e 0x20fffffff8000000

def z798 : W := mkw 0x1094c630000136e1 0x20425318c00004db 0x39fec6300447ffdf 0x20e7fb18c0111fff

def z799 : W := mkw 0x0081582b0808d180 0x80020560ac202346 0x0601f83ff878f1fb 0xbc1807e0ffe1e3c7

def z800 : W := mkw 0xad5b02d7f6eb8b42 0x1eb56c0b5fdbae2d 0x39cf07fef8008fc8 0xace73c1ffbe0023f

def z801 : W := mkw 0x004108035868d180 0x800104200d61a346 0x0601f83ff878f1fb 0xbc1807e0ffe1e3c7

def z802 : W := mkw 0x0011025300898b40 0x000044094c02262d 0xc63107ff07ff8ff7 0x7318c41ffc1ffe3f

def z803 : W := mkw 0xb801a543a688ad00 0x4ae006950e9a22b4 0xfe0107ff07f88ff7 0x73f8041ffc1fe23f

def z804 : W := mkw 0x423d02d7019d8b44 0x3108f40b5c06762d 0xc63f07ff07ff8ff7 0x7318fc1ffc1ffe3f

def z805 : W := mkw 0x054108035868c100 0x041504200d61a304 0x07c1f83ff878f1fb 0xbc1f07e0ffe1e3c7

def z806 : W := mkw 0xf7bcf7bc01140004 0x2fdef3def0045000 0xfffffffe007f003e 0xeffffffff801fc00

def z807 : W := mkw 0x1095deff0889ffe1 0xb042577bfc2227ff 0x0001fffe0000ffc0 0x200007fff80003ff

def z808 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffe00000006 0x63fffffff8000000

def z809 : W := mkw 0x00c148234848d180 0x000305208d212346 0x07c1f83ff878f1fb 0xbc1f07e0ffe1e3c7

def z810 : W := mkw 0xe728318c00000004 0x0f9ca0c630000000 0xffcf39ce00000028 0xcfff3ce738000000

def z811 : W := mkw 0x57b4d6bc00000000 0x255ed35af0000000 0xfffffffe0000003e 0xeffffffff8000000

def z812 : W := mkw 0xf7bcf7bc00010244 0x2fdef3def0000409 0xfffffffe04070e3e 0xeffffffff8101c38

def z813 : W := mkw 0xf738a79400000000 0x0fdce29e50000000 0xfffffffe0000003e 0xeffffffff8000000

def z814 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffe04008e3f 0xeffffffff8100238

def z815 : W := mkw 0xad4a0000f7760002 0x0eb5280003ddd800 0x39fe0001ffff001f 0x9ce7f80007fffc00

def z816 : W := mkw 0x18428400c44336e1 0x00610a1003110cdb 0x39fec600c447ffdf 0x20e7fb1803111fff

def z817 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf800ffc1ff80fe0d 0xdfe003ff07fe03f8

def z818 : W := mkw 0xf7bcf7bc22000004 0x2fdef3def0880000 0xffffffff3b80003e 0xfffffffffcee0000

def z819 : W := mkw 0x05c0582a58685180 0x84170160a961a146 0x07c1f83ef87871fa 0xac1f07e0fbe1e1c7

def z820 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f83ff87871ea 0x9c1f07e0ffe1e1c7

def z821 : W := mkw 0xb094f7bc00000004 0x2ac253def0000000 0xf9fffffe0000003e 0xefe7fffff8000000

def z822 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec6300447ffc6 0x20e7fb18c0111fff

def z823 : W := mkw 0xf728b58c00000004 0x0fdca2d630000000 0xffffffce0000003e 0xefffffff38000000

def z824 : W := mkw 0xb800ad40ae806c00 0x4ae002b502ba01b0 0xf801ffc0ff807e3c 0xefe007ff03fe01f8

def z825 : W := mkw 0x42310a97091dc340 0x1108c42a5c24770d 0x0631f83ff87ff1fb 0xbc18c7e0ffe1ffc7

def z826 : W := mkw 0xfa3aa7d4a7972e42 0x5be8ea9f529e5cb9 0xf83e07c007870e04 0x43e0f81f001e1c38

def z827 : W := mkw 0xb803ad41ae82ec00 0x4ae00eb506ba0bb0 0xf83fffc1ff87fe3d 0xffe0ffff07fe1ff8

def z828 : W := mkw 0xe72918cf3bbcc902 0x9f9ca4633ceef324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z829 : W := mkw 0xa8010841ae80c800 0x0aa0042106ba0320 0xf801ffc1ff80fe3d 0xffe007ff07fe03f8

def z830 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07f1f83ffc7ff1ff 0xbc1fc7e0fff1ffc7

def z831 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf9ffffc1ff80fe3f 0xffe7ffff07fe03f8

def z832 : W := mkw 0x1095ff7b0889ffe1 0xe04257fdec2227ff 0x0001fffe0000ffc0 0x200007fff80003ff

def z833 : W := mkw 0x47fe52bc517712e7 0x251ff94af145dc4b 0x07fe003e007f01c2 0x001ff800f801fc07

def z834 : W := mkw 0xf7bcf7bc01140004 0x2fdef3def0045000 0xffffffff03b8003e 0xfffffffffc0ee000

def z835 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xffff3ffe00000026 0xcffffcfff8000000

def z836 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec631fc47ffff 0xbce7fb18c7f11fff

def z837 : W := mkw 0xf7bcf7bc01150244 0x2fdef3def0045409 0xffffffff07ff8fff 0xfffffffffc1ffe3f

def z838 : W := mkw 0xb800a500a6002400 0x0ae0029402980090 0xf801ffc1ff80fe3d 0xffe007ff07fe03f8

def z839 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xffcffffe00000028 0xefff3ffff8000000

def z840 : W := mkw 0x08430843ffffef42 0x50210c210fffffbd 0x00000001ffffffc1 0x1000000007ffffff

def z841 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xffffffff0078003f 0xfffffffffc01e000

def z842 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x3fffc63ec447ffff 0x20ffff18fb111fff

def z843 : W := mkw 0x52b4f7bc00000004 0x214ad3def0000000 0xfffffffe0000003e 0x63fffffff8000000

def z844 : W := mkw 0xef6a3108f7760006 0x0fbda8c423ddd800 0xfffe3801ffff003f 0xdffff8e007fffc00

def z845 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63107ffffff8fff 0xff18c41ffffffe3f

def z846 : W := mkw 0x47fa52be517f13c2 0x951fe94af945fc4f 0x07fe003e007f01c2 0x001ff800f801fc07

def z847 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fe0630c447ffc7 0x00e7f818c3111fff

def z848 : W := mkw 0x05c1586b58e8d980 0x84170561ad63a366 0x07c1fffff878fffb 0xbc1f07ffffe1e3ff

def z849 : W := mkw 0xa00129412a80c800 0x4a8004a504aa0320 0xc001ffc1ff80fe3d 0xff0007ff07fe03f8

def z850 : W := mkw 0xf7acf5ac00000004 0x2fdeb3d6b0000000 0xffcff9fe0000003a 0xefff3fe7f8000000

def z851 : W := mkw 0x05c1506b50e89980 0x84170541ad43a266 0xc7c107ff07f88ff7 0x731f041ffc1fe23f

def z852 : W := mkw 0xf7bcf7bc32200006 0x2fdef3def0c88000 0xfffffffe3800003e 0xeffffffff8e00000

def z853 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc631c7ffc7ffffff 0x7318c71fff1fffff

def z854 : W := mkw 0xbdcafd28fe627482 0xcef72bf4a3f989d2 0x39cef800f8007008 0x8ce73be003e001c0

def z855 : W := mkw 0xf7acf5ac00000004 0x2fdeb3d6b0000000 0xffcfffce0000003c 0xefff3fff38000000

def z856 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63007ff07ff8fc7 0x5318c01ffc1ffe3f

def z857 : W := mkw 0xe76a000073760002 0x0f9da80001cdd800 0xfffe00013bff003e 0xdffff80004effc00

def z858 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0x3ffe0001ffff000b 0x9cfff80007fffc00

def z859 : W := mkw 0xe738339c00000004 0x0f9ce0ce70000000 0xffff3ffe0000003e 0xeffffcfff8000000

def z860 : W := mkw 0x05c0582a58685180 0x84170160a961a146 0x07c0f83ff87871fb 0x9c1f03e0ffe1e1c7

def z861 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1f83ff838f1e8 0xbc1f07e0ffe0e3c7

def z862 : W := mkw 0x42310ad7099dcb40 0x1108c42b5c26772d 0xc63107fffffffff7 0x7318c41fffffffff

def z863 : W := mkw 0x1894c63084012640 0x20625318c2100499 0x39fec630c447ffdf 0x20e7fb18c3111fff

def z864 : W := mkw 0xf7bcf7bc00001084 0x2fdef3def0000042 0xfffffffe0000f1fe 0xeffffffff80003c7

def z865 : W := mkw 0xf7bcf7bc23140006 0x2fdef3def08c5000 0xfffffffe0380003e 0xeffffffff80e0000

def z866 : W := mkw 0xf7bcf7bc11340006 0x2fdef3def044d000 0xfffffffe0038003e 0xeffffffff800e000

def z867 : W := mkw 0x18d6e730c44336e1 0x20635b9cc3110cdb 0x39fffff0c447ffdf 0x20e7ffffc3111fff

def z868 : W := mkw 0xef6a2184f7760006 0x0fbda88613ddd800 0xfffe01c1ffff003f 0xdffff80707fffc00

def z869 : W := mkw 0xe7a871ac00000004 0x0f9ea1c6b0000000 0xfffff9fe0000003e 0xefffffe7f8000000

def z870 : W := mkw 0xf7bcf7bc00002404 0x2fdef3def0000090 0xfffffffe0000fe3e 0xeffffffff80003f8

def z871 : W := mkw 0xa8420000f7760002 0x0aa1080003ddd800 0xf9fe0001ffff003f 0xdfe7f80007fffc00

def z872 : W := mkw 0x08520210c44336e1 0x0021480843110cdb 0x39fe0630c447ffdf 0x20e7f818c3111fff

def z873 : W := mkw 0xf7bcf7bc01150244 0x3fdef3def0045409 0xfffffffe0007003e 0xeffffffff8001c00

def z874 : W := mkw 0x05c0582a58685180 0x84170160a961a146 0x07c0f83ef878f1db 0xac1f03e0fbe1e3c7

def z875 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c0f83ff878f1cb 0x9c1f03e0ffe1e3c7

def z876 : W := mkw 0xfa36a7d4a7972e61 0x7be8da9f529e5cb9 0xf83e07c007870e04 0x43e0f81f001e1c38

def z877 : W := mkw 0xb801ad43ae88ed00 0x4ae006b50eba23b4 0xf801ffc1fff8fffd 0xffe007ff07ffe3ff

def z878 : W := mkw 0x08010841ae80ec00 0x4020042106ba03b0 0xc001ffc1ff80fe3d 0xff0007ff07fe03f8

def z879 : W := mkw 0xef6a0000f7761082 0x0fbda80003ddd842 0xfffe0001fffff1ff 0xdffff80007ffffc7

def z880 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffff801ffff003f 0xffffffe007fffc00

def z881 : W := mkw 0xf7bcf7bc33340006 0x2fdef3def0ccd000 0xffffffff3fff003f 0xfffffffffcfffc00

def z882 : W := mkw 0xef6a0000f7762402 0x0fbda80003ddd890 0xfffe0001fffffe3f 0xdffff80007fffff8

def z883 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x0601f83ff878f1e1 0xbc1807e0ffe1e3c7

def z884 : W := mkw 0x08430843feebffe1 0xc0210c210ffbafff 0x00000001ffffffc1 0x1000000007ffffff

def z885 : W := mkw 0xf7bcf7bc000112e5 0x2fdef3def000044b 0xfffffffe000001fe 0xeffffffff8000007

def z886 : W := mkw 0xf7bcf7bc00012665 0x2fdef3def0000499 0xfffffffe00000e3e 0xeffffffff8000038

def z887 : W := mkw 0x1095eff70889ffe1 0x704257bfdc2227ff 0x0001fffe0000ffc0 0x200007fff80003ff

def z888 : W := mkw 0xef2a0000b7360002 0x0fbca80002dcd800 0xfffe00013fbf003e 0xdffff80004fefc00

def z889 : W := mkw 0xe72939cf19bcc904 0x9f9ca4e73c66f324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z890 : W := mkw 0x4a620000f7760002 0x0129880003ddd800 0xfffe0001ffff003f 0x53fff80007fffc00

def z891 : W := mkw 0xe72939cf2b9cc904 0x5f9ca4e73cae7324 0xc60139cf3bb80020 0xdf1804e73ceee000

def z892 : W := mkw 0x18c6c420c44336e1 0x20631b1083110cdb 0x39fec000c447ffdf 0x00e7fb0003111fff

def z893 : W := mkw 0x1095ffff0889dbc4 0xb04257fffc22276f 0x0001fffe0000ffc0 0x200007fff80003ff

def z894 : W := mkw 0xb58cf52800000004 0x2ed633d4a0000000 0xffcffffe0000003e 0xefff3ffff8000000

def z895 : W := mkw 0x4230029401150240 0x0108c00a50045409 0xc63107ff07ff8ff7 0x7318c41ffc1ffe3f

def z896 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc631ffff07ff8fff 0xff18c7fffc1ffe3f

def z897 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x3ffec631c47fffff 0x30fffb18c711ffff

def z898 : W := mkw 0x18d6f738c44336e5 0x20635bdce3110cdb 0x39fefe30c447ffdf 0x20e7fbf8c3111fff

def z899 : W := mkw 0x42310ad7099dcb40 0x1108c42b5c26772d 0xc6313fff3fff8ff7 0xff18c4fffcfffe3f

def z900 : W := mkw 0xfa3ea794a7172667 0x2be8fa9e529c5c99 0xf83e07c007870e04 0x43e0f81f001e1c38

def z901 : W := mkw 0xb594f73800000000 0x2ed653dce0000000 0xfffffffe0000003e 0xeffffffff8000000

def z902 : W := mkw 0x0501180b1828c100 0x841404602c60a304 0x0601f83ff878f1fb 0xbc1807e0ffe1e3c7

def z903 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0x07c1fe3ffc78ffff 0xbc1f07f8fff1e3ff

def z904 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xc001ffc1ff80fe21 0xff0007ff07fe03f8

def z905 : W := mkw 0xf7acf5ac00000004 0x2fdeb3d6b0000000 0xfffff9ce0000003e 0xcfffffe738000000

def z906 : W := mkw 0xb800ad40ae806c00 0x4ae002b502ba01b0 0xf800ffc1ff807e3d 0xdfe003ff07fe01f8

def z907 : W := mkw 0xf7bcf7bc01140004 0x2fdef3def0045000 0xfffffffe0787003e 0xeffffffff81e1c00

def z908 : W := mkw 0xef6a2100f7760002 0x0fbda88403ddd800 0xffff39c1ffff003f 0xdffffce707fffc00

def z909 : W := mkw 0xef6a318cf7760006 0x0fbda8c633ddd800 0xc60139cfffff0021 0xdf1804e73ffffc00

def z910 : W := mkw 0x05cb582b586ad182 0x84172d60ad61ab46 0x07cff83ff878f1fb 0xbc1f3fe0ffe1e3c7

def z911 : W := mkw 0xef6a1008f7760002 0x0fbda84023ddd800 0xffff380fffff003f 0xdffffce03ffffc00

def z912 : W := mkw 0x42310ad7099dcb40 0x1108c42b5c26772d 0xc631ffff07fffff7 0x7318c7fffc1fffff

def z913 : W := mkw 0xf2b4e7b400000000 0x2bcad39ed0000000 0xfffffffe0000003e 0xeffffffff8000000

def z914 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0xc7c1f83ffff8f1ff 0xff1f07e0ffffe3c7

def z915 : W := mkw 0x10d6c630404336e1 0x20435b18c1010cdb 0x39fec6300047ffde 0x20e7fb18c0011fff

def z916 : W := mkw 0xe7bc73bc00000004 0x2f9ef1cef0000000 0xffff39fe0000003e 0xcffffce7f8000000

def z917 : W := mkw 0x0581582b0808c100 0x04160560ac202304 0x07c1f83ff878f1fb 0xbc1f07e0ffe1e3c7

def z918 : W := mkw 0x1896c630840336e1 0x20625b18c2100cdb 0x39fec6300407ffde 0x20e7fb18c0101fff

def z919 : W := mkw 0xfa3ca7d4a7952e44 0x7be8f29f529e54b9 0xf83e07c007870e04 0x43e0f81f001e1c38

def z920 : W := mkw 0xb80dad41ae80ec04 0x6ae036b506ba03b0 0xf80fffc1ff80fe3d 0xffe03fff07fe03f8

def z921 : W := mkw 0x08c24020c44336e1 0x0023090083110cdb 0x39fec030c447ffdf 0x20e7fb00c3111fff

def z922 : W := mkw 0xf7bcf7bc00010244 0x2fdef3def0000409 0xfffffffe00008ffe 0xeffffffff800023f

def z923 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffe0447003f 0xeffffffff8111c00

def z924 : W := mkw 0xb801ad41ae80ec00 0x4ae006b506ba03b0 0xf801ffc1ff807e2c 0xdfe007ff07fe01f8

def z925 : W := mkw 0xea620000e7560000 0x0ba98800039d5800 0xfffe0001ffff003f 0xdffff80007fffc00

def z926 : W := mkw 0x4f620000d5760000 0x053d88000355d800 0xfffe0001ffff003f 0xdffff80007fffc00

def z927 : W := mkw 0xe7b852bc00000000 0x0f9ee14af0000000 0xfffffffe0000003e 0xeffffffff8000000

def z928 : W := mkw 0xb80bad41ae82ec02 0x4ae02eb506ba0bb0 0xf80fffc1ff80fe3d 0xffe03fff07fe03f8

def z929 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0001ffbf002c 0xdffff80007fefc00

def z930 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xfffffffec000f03f 0xeffffffffb0003c0

def z931 : W := mkw 0xe728000033340002 0x0f9ca00000ccd000 0xfffe00013fff003f 0xdffff80004fffc00

def z932 : W := mkw 0x0d420000f7760002 0x0435080003ddd800 0x3ffe0001ffff003f 0x9cfff80007fffc00

def z933 : W := mkw 0xb807ad41ae82ec21 0x6ae01eb506ba0bb0 0xf80fffc1ff80fe3d 0xffe03fff07fe03f8

def z934 : W := mkw 0xb59cf7bc00000004 0x2ed673def0000000 0x3fcffffe0000003a 0xacff3ffff8000000

def z935 : W := mkw 0xbdcef528f66234a7 0x2ef73bd4a3d988d2 0x39cef800f8007008 0x8ce73be003e001c0

def z936 : W := mkw 0x423002d6019d0b40 0x1108c00b5806742d 0xc63007fe07ff8fd7 0x6318c01ff81ffe3f

def z937 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xf9fffffe0000000c 0xefe7fffff8000000

def z938 : W := mkw 0xb59cf7bc00000004 0x2ed673def0000000 0xf9cffffe0000003c 0xefe73ffff8000000

def z939 : W := mkw 0xf7bcf7bc10200004 0x2fdef3def0408000 0xffffffff3838003e 0xfffffffffce0e000

def z940 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0xf9ffc7f0c447ffff 0x63e7ff1fc3111fff

def z941 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63107fe07ff8fc6 0x6318c41ff81ffe3f

def z942 : W := mkw 0x423002d6019d0b40 0x1108c00b5806742d 0xc63007ff07ff0ff7 0x5318c01ffc1ffc3f

def z943 : W := mkw 0xf7a8f52800000000 0x0fdea3d4a0000000 0xfffffffe0000003e 0xeffffffff8000000

def z944 : W := mkw 0xef6a0084f7760002 0x0fbda80213ddd800 0xffff01cfffff003f 0xdffffc073ffffc00

def z945 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xfffe0001ffff0007 0x53fff80007fffc00

def z946 : W := mkw 0x05c3582b586ad180 0x84170d60ad61ab46 0x07fff83ff87ff1fb 0xbc1fffe0ffe1ffc7

def z947 : W := mkw 0x05c1582b5868d180 0x84170560ad61a346 0xc7c1fffff878f1ff 0xff1f07ffffe1e3c7

def z948 : W := mkw 0x423102d7019d8b40 0x1108c40b5c06762d 0xc63107ff07ff0fe6 0x5318c41ffc1ffc3f

def z949 : W := mkw 0xb801ad43ae88ed00 0x4ae006b50eba23b4 0xfe01ffcfffb8fe3d 0xfff807ff3ffee3f8

def z950 : W := mkw 0x05c1586b58e8d980 0x84170561ad63a366 0x07c1f83ffff8fffb 0xbc1f07e0ffffe3ff

def z951 : W := mkw 0x18d6e7b4c44336e5 0x20635b9ed3110cdb 0x39fec7f0c447ffdf 0x20e7fb1fc3111fff

def z952 : W := mkw 0xf7bcf7bc00000004 0x2fdef3def0000000 0xffffffff0780003f 0xfffffffffc1e0000

def z953 : W := mkw 0x18d6c630c44336e1 0x20635b18c3110cdb 0x39fec600c447ffcd 0x00e7fb1803111fff

def z954 : W := mkw 0xef6a0000f7760002 0x0fbda80003ddd800 0xffff003fffff003f 0xfffffc00fffffc00

def z955 : W := mkw 0x08d64230c44336e1 0x20235908c3110cdb 0x39fe0030c447ffdf 0x00e7f800c3111fff

def z956 : W := mkw 0xb801ad43ae88ed00 0x4ae006b50eba23b4 0xf801ffffff80fffd 0xffe007fffffe03ff

def z957 : W := mkw 0xb001ad410880c800 0x0ac006b504220320 0xf801ffc1ff80fe3d 0xffe007ff07fe03f8

def z958 : W := mkw 0xf7bcf7bc000034a5 0x2fdef3def00000d2 0xfffffffe0000703e 0xeffffffff80001c0

def z959 : W := mkw 0x1095ffff0889ef44 0x704257fffc2227bd 0x0001fffe0000ffc0 0x200007fff80003ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z7]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z9,z2,z3,z4,z5,z6])],[(0,[z1,z2,z10,z3,z4,z5,z6])],[(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z13,z6]),(0,[z1,z2,z3,z4,z5,z6,z14]),(0,[z1,z2,z3,z4,z15,z5,z6])],[(0,[z16,z1,z17,z3,z4,z5,z6]),(0,[z18,z2,z3,z4,z19,z5,z6]),(0,[z1,z2,z20,z4,z5,z21,z6]),(0,[z1,z2,z3,z22,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z23]),(0,[z1,z2,z20,z3,z4,z21,z6]),(0,[z1,z2,z3,z24,z4,z5,z6])],[(0,[z1,z2,z3,z25,z19,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z5,z6])],[(0,[z1,z29,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z32,z5,z6]),(0,[z1,z33,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z6])],[(1,[z38,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z41]),(0,[z37,z1,z3,z42,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z45,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z48,z6])],[(0,[z49,z1,z2,z50,z4,z5,z6]),(0,[z51,z2,z3,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z42,z4,z5,z6]),(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z56,z4,z5,z6])],[(0,[z57,z2,z17,z3,z4,z5,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z60,z4,z5,z6]),(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z64,z6])],[(0,[z1,z2,z3,z4,z65,z5,z6]),(1,[z66,z1,z3,z67,z5,z6]),(0,[z1,z2,z3,z68,z4,z5,z6]),(0,[z1,z2,z3,z69,z4,z32,z5]),(0,[z1,z2,z70,z3,z4,z5,z6])]],
   [[(0,[z57,z16,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z72,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z74,z2,z3,z75,z4,z5]),(1,[z1,z2,z3,z4,z76,z77])],[(0,[z1,z2,z3,z4,z5,z6,z78]),(0,[z1,z2,z79,z3,z4,z5,z6])],[(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z6]),(0,[z1,z2,z3,z82,z4,z5,z6]),(0,[z1,z2,z3,z4,z83,z5,z6])],[(0,[z1,z84,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z85,z5,z6]),(0,[z1,z2,z3,z86,z4,z5,z6]),(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6])],[],[(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z91,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z1,z2,z3,z86,z5,z6,z96])],[(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z98,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z91,z4,z5,z6]),(0,[z100,z1,z2,z3,z52,z5,z6]),(0,[z101,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z102,z6]),(1,[z18,z2,z50,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z103]),(0,[z1,z104,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z105,z5,z6])],[(0,[z18,z1,z2,z3,z4,z5,z6]),(0,[z1,z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z107,z6])],[(0,[z1,z2,z3,z108,z4,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z32,z5,z6,z110]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z113,z3,z4,z5,z6])],[(0,[z1,z2,z114,z3,z4,z5,z6]),(0,[z1,z115,z2,z3,z4,z6,z116]),(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6])],[(0,[z1,z119,z2,z3,z4,z5,z6])],[(1,[z1,z2,z120,z4,z5,z6]),(0,[z1,z121,z2,z3,z4,z5,z6])],[(0,[z122,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z123,z4,z5,z6]),(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z125,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z126])],[(0,[z1,z2,z3,z52,z5,z6,z126]),(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z129]),(0,[z1,z2,z130,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z1,z132,z2,z3,z4,z5,z6]),(1,[z1,z133,z3,z4,z5,z6])],[(0,[z1,z134,z2,z3,z4,z5,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z138]),(1,[z1,z74,z2,z3,z75,z5])],[(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z140,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z141]),(0,[z1,z2,z3,z142,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z143,z5,z6]),(0,[z1,z144,z2,z3,z4,z5,z6])],[(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z146]),(0,[z147,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z148,z5,z6]),(0,[z1,z2,z3,z4,z149,z5,z6])],[(0,[z1,z2,z3,z150,z4,z5,z6]),(0,[z1,z2,z3,z151,z4,z5,z6])]],
   [[(0,[z1,z152,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z2,z3,z4,z5,z6,z153,z126])],[(0,[z1,z2,z154,z3,z4,z5,z6]),(0,[z18,z1,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z41]),(1,[z1,z2,z3,z4,z156,z6]),(0,[z1,z2,z3,z157,z4,z5,z6]),(0,[z1,z158,z159,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z162,z6,z39]),(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z1,z2,z3,z163,z4,z5,z6]),(0,[z164,z1,z2,z3,z69,z4,z5]),(0,[z1,z165,z2,z3,z4,z76,z6])],[(0,[z1,z2,z3,z166,z4,z5,z6]),(0,[z167,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z52,z4,z19,z5,z6]),(0,[z168,z1,z2,z3,z4,z5,z6]),(0,[z1,z169,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z170]),(0,[z1,z2,z3,z4,z171,z5,z6])],[(0,[z57,z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z172]),(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z76,z5,z110]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z175,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z176,z5,z6]),(0,[z1,z2,z3,z177,z4,z5,z6]),(0,[z1,z178,z2,z3,z4,z5,z6])]],
   [[(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z2,z3,z4,z5,z6,z182])],[(1,[z49,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z183,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z184]),(0,[z66,z1,z3,z67,z4,z5,z6]),(0,[z185,z1,z2,z3,z5,z6,z126]),(0,[z186,z1,z2,z3,z4,z5,z6]),(1,[z164,z1,z2,z69,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z187])],[(0,[z1,z2,z3,z4,z5,z6,z188]),(1,[z12,z2,z3,z4,z189,z6]),(0,[z1,z2,z3,z4,z5,z6,z110])],[(0,[z1,z190,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z5,z191]),(0,[z1,z33,z2,z3,z4,z5,z6])],[(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z100,z1,z2,z3,z19,z5,z6]),(0,[z1,z194,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z195]),(0,[z1,z196,z2,z3,z4,z32,z6]),(0,[z1,z197,z2,z3,z4,z5,z6]),(0,[z1,z165,z158,z2,z3,z4,z5])],[(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z1,z2,z3,z4,z199,z5,z6]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z66,z1,z45,z3,z4,z5,z6]),(0,[z1,z201,z158,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z202,z6])]],
   [[(0,[z1,z203,z2,z3,z4,z5,z6]),(0,[z1,z45,z2,z3,z67,z5,z6]),(0,[z1,z2,z3,z204,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z205]),(0,[z206,z1,z2,z3,z4,z5,z6])],[(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z208,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z211,z6]),(0,[z1,z2,z3,z4,z5,z6,z212])],[(0,[z1,z213,z2,z3,z4,z5,z6]),(1,[z1,z196,z2,z3,z4,z6])],[(0,[z49,z18,z2,z3,z4,z5,z6]),(0,[z214,z1,z2,z3,z4,z5,z162]),(0,[z164,z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z3,z215,z4,z5,z6])],[(0,[z216,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z189,z6]),(0,[z1,z31,z201,z3,z4,z5,z6]),(1,[z218,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z219,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z220])],[(0,[z185,z100,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z191,z110]),(0,[z221,z2,z3,z4,z5,z6,z126]),(0,[z1,z2,z3,z4,z5,z6,z153]),(0,[z1,z2,z3,z75,z137,z4,z5])]],
   [[(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z4,z5,z6])],[(1,[z57,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z225,z4,z5,z6]),(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6]),(0,[z185,z218,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z228,z6])],[(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z1,z230,z31,z3,z4,z5,z6]),(0,[z1,z3,z4,z15,z5,z6,z110])],[(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z232,z6]),(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z1,z2,z3,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z236,z4,z5,z6])],[(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z218,z1,z2,z3,z4,z5,z6])],[(0,[z185,z51,z1,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z4,z5,z39])],[(0,[z1,z2,z238,z3,z4,z5,z6]),(0,[z1,z2,z239,z3,z5,z6,z126]),(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z1,z241,z2,z3,z4,z5,z6])]],
   [[(0,[z49,z100,z2,z3,z4,z5,z6]),(0,[z1,z2,z242,z3,z4,z5,z6]),(1,[z1,z33,z2,z3,z34,z6]),(0,[z1,z2,z3,z75,z4,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6])],[(0,[z1,z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z245,z4,z5,z6]),(1,[z221,z2,z3,z4,z5,z6])],[(0,[z2,z50,z3,z52,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z5,z6]),(0,[z1,z247,z2,z3,z4,z5,z6])],[(0,[z221,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z1,z2,z249,z3,z4,z5,z6]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z76,z5,z77]),(0,[z1,z2,z3,z251,z4,z5,z6])],[(0,[z252,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z253,z6]),(0,[z1,z2,z254,z3,z4,z5,z6]),(0,[z1,z2,z3,z255,z4,z5,z6])],[(0,[z1,z2,z3,z69,z4,z5,z110])],[(0,[z1,z2,z3,z4,z5,z6,z256]),(0,[z1,z257,z2,z3,z4,z5,z6]),(0,[z1,z2,z113,z4,z5,z6,z191])]],
   [[(0,[z1,z2,z3,z4,z258,z5,z6]),(0,[z1,z2,z3,z4,z5,z259,z6]),(1,[z1,z159,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z260,z5,z6]),(0,[z1,z2,z261,z4,z5,z21,z6]),(0,[z1,z2,z3,z4,z5,z6,z77])],[(0,[z1,z2,z3,z262,z4,z5,z6]),(1,[z51,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z52,z25,z5,z6])],[(0,[z1,z2,z3,z263,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264]),(1,[z1,z165,z158,z2,z3,z4])],[(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z267,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z268,z4,z5,z6])],[(0,[z49,z1,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z261,z4,z6]),(0,[z1,z271,z2,z3,z4,z5,z6])],[(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z165,z2,z3,z4,z32,z5]),(0,[z1,z2,z3,z273,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z274,z6])],[(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z278]),(0,[z1,z201,z2,z3,z4,z32,z5])]],
   [[(0,[z279,z1,z2,z3,z4,z5,z6])],[(0,[z280,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z64]),(0,[z1,z281,z3,z42,z4,z5,z6]),(0,[z1,z2,z3,z4,z282,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6])],[(0,[z284,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z69,z4,z5,z6,z191]),(0,[z1,z2,z3,z285,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z1,z2,z3,z4,z5,z6,z286]),(0,[z1,z2,z287,z3,z4,z5,z6]),(0,[z1,z2,z288,z3,z4,z5,z6])],[(0,[z1,z2,z3,z289,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z290]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z2,z3,z292,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z293]),(0,[z1,z2,z3,z4,z294,z5,z6]),(1,[z224,z1,z2,z261,z4,z6]),(0,[z224,z1,z2,z261,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z295])],[(0,[z57,z1,z296,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z297,z5,z6]),(0,[z1,z2,z3,z4,z5,z191,z77])],[(0,[z51,z1,z2,z239,z3,z5,z6]),(1,[z298,z2,z3,z4,z13,z6]),(0,[z1,z230,z165,z2,z3,z4,z6]),(1,[z1,z299,z2,z3,z4,z5]),(0,[z300,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z1,z165,z158,z2,z3,z4,z6])],[(0,[z1,z2,z123,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z305,z5,z6]),(0,[z1,z306,z2,z3,z4,z5,z6]),(0,[z1,z2,z307,z3,z4,z5,z6])],[(0,[z1,z2,z3,z308,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z5,z6])],[(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z310,z5,z6]),(0,[z1,z2,z3,z311,z4,z5,z6]),(0,[z1,z2,z3,z312,z4,z5,z6])],[(0,[z185,z1,z2,z3,z25,z5,z6]),(0,[z1,z2,z3,z313,z4,z5,z6])],[(0,[z1,z2,z3,z4,z76,z5,z6])],[(0,[z1,z2,z281,z3,z4,z5,z6]),(0,[z1,z2,z3,z314,z4,z5,z6])]],
   [[(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z4,z5,z317,z6]),(0,[z1,z318,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z319]),(0,[z1,z2,z3,z4,z5,z320,z6])],[(0,[z321,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z322,z4,z5,z6]),(0,[z1,z299,z2,z3,z4,z15,z5]),(0,[z1,z2,z3,z4,z323,z5,z6]),(0,[z1,z2,z3,z324,z4,z5,z6]),(0,[z1,z74,z2,z3,z75,z5,z6])],[(0,[z1,z325,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z6,z77])],[(0,[z1,z2,z3,z326,z4,z5,z6]),(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z49,z2,z3,z91,z4,z5,z6]),(0,[z1,z2,z3,z328,z4,z5,z6]),(0,[z1,z2,z3,z329,z4,z5,z6]),(1,[z1,z2,z20,z4,z21,z6]),(0,[z1,z2,z3,z69,z4,z5,z77]),(1,[z1,z2,z3,z137,z5,z138])],[(0,[z1,z2,z330,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z4,z5,z6])],[(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z333]),(0,[z1,z334,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z76,z6,z77]),(0,[z335,z1,z2,z3,z4,z5,z6])],[(0,[z100,z1,z2,z120,z4,z5,z6]),(1,[z1,z115,z3,z4,z15,z6]),(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z1,z2,z3,z337,z4,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z6])]],
   [[(0,[z100,z1,z2,z123,z4,z5,z6]),(0,[z1,z2,z3,z338,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z339]),(0,[z1,z165,z2,z3,z4,z5,z77])],[(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z341,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z342,z6]),(0,[z1,z201,z2,z3,z4,z5,z77]),(0,[z1,z2,z3,z4,z343,z5,z6])],[(0,[z1,z2,z239,z50,z4,z5,z6]),(0,[z1,z2,z3,z4,z344,z5,z6]),(0,[z1,z2,z3,z345,z4,z5,z6])],[(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z1,z346,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z136,z4,z5])],[(0,[z1,z2,z3,z347,z4,z5,z6]),(0,[z1,z2,z20,z3,z4,z5,z6])],[(0,[z1,z348,z2,z3,z4,z5,z6]),(0,[z1,z349,z2,z3,z4,z5,z6])],[(0,[z296,z2,z17,z3,z4,z5,z6]),(0,[z1,z350,z2,z3,z4,z5,z6]),(0,[z1,z351,z2,z3,z4,z5,z6]),(0,[z1,z3,z67,z4,z352,z5,z6]),(0,[z1,z353,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z278])],[(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z356,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z357,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z358,z5,z6])],[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6])],[(0,[z51,z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z1,z359,z2,z3,z4,z5,z6]),(0,[z1,z119,z281,z3,z4,z5,z6]),(0,[z66,z1,z2,z3,z4,z5,z6]),(1,[z1,z45,z3,z352,z5,z6])],[(0,[z1,z2,z3,z4,z360,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z361]),(0,[z1,z2,z3,z362,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z96])],[(0,[z1,z3,z4,z15,z5,z6,z116])],[(0,[z1,z2,z363,z3,z4,z5,z6])],[(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z4,z5,z6])],[(0,[z49,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z365,z5,z6]),(0,[z1,z2,z3,z4,z5,z366,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z368,z4,z5,z6]),(0,[z1,z2,z369,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z370,z5,z6]),(0,[z1,z371,z2,z3,z4,z5,z6])],[(0,[z298,z1,z2,z3,z4,z13,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z1,z374,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z375,z6]),(0,[z16,z296,z2,z3,z4,z5,z6]),(0,[z1,z45,z2,z3,z352,z5,z6]),(0,[z1,z376,z2,z3,z4,z5,z6]),(0,[z377,z1,z2,z3,z4,z5,z6])],[(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z379,z1,z2,z3,z4,z5,z6]),(0,[z1,z380,z2,z3,z4,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6])],[(0,[z1,z2,z20,z3,z4,z5,z361]),(0,[z1,z2,z3,z382,z4,z5,z6])],[(0,[z1,z2,z3,z383,z4,z5,z6]),(0,[z384,z1,z2,z3,z4,z5,z6]),(0,[z1,z385,z2,z3,z4,z5,z6])],[(0,[z1,z2,z386,z3,z4,z5,z6]),(0,[z1,z2,z113,z3,z69,z4,z5])],[(0,[z1,z2,z3,z387,z4,z5,z6]),(0,[z1,z2,z3,z388,z4,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z390,z2,z3,z4,z5,z6]),(0,[z1,z391,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z392]),(0,[z1,z2,z3,z75,z5,z6,z138])],[(0,[z1,z2,z3,z393,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z394,z6]),(0,[z1,z2,z3,z395,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z1,z2,z20,z3,z261,z4,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z397]),(0,[z1,z2,z3,z4,z398,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z399]),(0,[z1,z2,z3,z4,z400,z5,z6]),(0,[z1,z165,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z401,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z402,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z41]),(0,[z1,z201,z2,z3,z4,z5,z6]),(0,[z1,z2,z239,z25,z4,z5,z6])],[(0,[z1,z2,z3,z403,z4,z5,z6]),(0,[z1,z2,z404,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z39]),(0,[z405,z1,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z69,z4,z5])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z74,z2,z3,z4,z5,z6]),(0,[z1,z2,z406,z3,z4,z5,z6])],[(0,[z1,z2,z3,z407,z4,z5,z6]),(1,[z214,z2,z3,z4,z5,z162]),(0,[z1,z2,z3,z4,z408,z5,z6])],[(0,[z49,z1,z2,z91,z4,z5,z6]),(0,[z164,z1,z2,z113,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z191]),(0,[z1,z133,z158,z3,z4,z5,z6])]],
   [[(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z410,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z4,z5,z6])],[(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6])],[],[(0,[z1,z2,z414,z3,z4,z5,z6])],[(1,[z280,z1,z2,z3,z5,z6]),(0,[z214,z1,z2,z3,z4,z5,z39]),(0,[z415,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z416,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z417]),(0,[z1,z2,z3,z4,z5,z6,z418]),(0,[z1,z165,z2,z3,z4,z5,z110]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z76,z5])],[(0,[z1,z2,z3,z420,z4,z5,z6]),(0,[z1,z230,z2,z3,z4,z15,z6]),(0,[z1,z201,z2,z3,z4,z5,z110]),(1,[z1,z2,z239,z25,z5,z6]),(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z422])],[(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z2,z3,z423,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z426,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z427]),(0,[z1,z428,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z429,z4,z5,z6])],[(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z2,z3,z431,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z361]),(0,[z1,z432,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z433])],[(1,[z1,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z4,z5,z6,z434])],[(0,[z1,z435,z2,z3,z4,z5,z6]),(0,[z1,z2,z436,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z437,z5,z6]),(1,[z1,z2,z3,z4,z148,z5]),(0,[z1,z2,z3,z4,z438,z5,z6]),(0,[z439,z1,z2,z3,z4,z5,z6]),(0,[z440,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z441]),(1,[z2,z3,z4,z5,z6,z153]),(0,[z1,z442,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z443,z3,z4,z5,z6]),(0,[z298,z2,z3,z4,z5,z13,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z20,z3,z136,z4,z5])],[(0,[z1,z2,z3,z4,z5,z445,z6]),(0,[z1,z2,z3,z4,z5,z6,z446]),(0,[z1,z2,z3,z4,z32,z5,z191]),(0,[z1,z447,z2,z3,z4,z5,z6])],[(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z449,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z5,z6,z126]),(0,[z1,z452,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z1,z454,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z1,z2,z3,z4,z456,z5,z6])],[(1,[z185,z1,z2,z5,z6,z126]),(0,[z1,z2,z457,z3,z4,z5,z6])],[(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z459,z2,z3,z4,z5,z6]),(0,[z1,z2,z460,z3,z4,z5,z6])],[(0,[z18,z1,z2,z50,z4,z5,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z462,z1,z2,z3,z4,z5,z6])],[(0,[z463,z1,z2,z3,z4,z5,z6]),(0,[z18,z2,z50,z3,z4,z5,z6]),(0,[z66,z1,z2,z3,z67,z5,z6]),(0,[z1,z165,z115,z2,z3,z4,z6]),(0,[z464,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z465,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z466,z5,z6]),(0,[z1,z2,z3,z4,z5,z467,z6])],[(0,[z1,z468,z2,z3,z4,z5,z6]),(0,[z1,z469,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z470,z5,z6]),(0,[z2,z3,z91,z4,z19,z5,z6]),(0,[z51,z2,z3,z91,z4,z5,z6]),(0,[z1,z31,z158,z2,z3,z4,z5]),(0,[z1,z33,z2,z3,z4,z6,z96])],[],[],[(0,[z100,z51,z2,z3,z4,z5,z6]),(1,[z100,z2,z3,z19,z5,z6]),(0,[z1,z2,z471,z3,z4,z5,z6]),(0,[z37,z1,z119,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z472,z5,z6])],[(0,[z100,z2,z50,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z1,z115,z3,z4,z15,z5,z6]),(0,[z474,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z475,z3,z4,z5,z6]),(0,[z1,z2,z3,z476,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z478,z1,z2,z3,z4,z5,z6])],[(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z480,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z481,z6]),(0,[z1,z2,z3,z4,z189,z5,z6]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z4,z32,z156,z6])],[(0,[z483,z1,z2,z3,z4,z5,z6]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z486,z6]),(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z488,z4,z5,z6]),(0,[z1,z489,z2,z3,z4,z5,z6]),(0,[z490,z1,z2,z3,z4,z5,z6])],[(0,[z51,z1,z2,z3,z52,z5,z6]),(0,[z1,z491,z2,z3,z4,z5,z6]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z1,z115,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z494,z5,z6])],[(0,[z1,z495,z2,z3,z4,z5,z6])],[(0,[z280,z1,z2,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z496])],[(0,[z16,z1,z2,z3,z4,z5,z6]),(0,[z497,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z498]),(0,[z1,z2,z3,z499,z4,z5,z6]),(0,[z1,z500,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z50,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z501,z2,z3,z4,z5,z6]),(0,[z1,z115,z2,z3,z4,z15,z6])],[(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z504,z4,z5,z6]),(0,[z1,z2,z3,z505,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z138])],[(0,[z1,z506,z2,z3,z4,z5,z6]),(0,[z507,z1,z2,z3,z4,z5,z6])],[(0,[z508,z1,z2,z3,z4,z5,z6]),(0,[z1,z509,z2,z3,z4,z5,z6]),(0,[z510,z1,z2,z3,z4,z5,z6])],[(0,[z298,z1,z2,z3,z4,z189,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(0,[z1,z2,z3,z512,z4,z5,z6]),(0,[z513,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z514,z5,z6]),(1,[z1,z230,z3,z4,z6,z116]),(0,[z1,z2,z239,z3,z25,z5,z6]),(0,[z1,z2,z3,z515,z4,z5,z6])],[(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z516,z5,z6]),(0,[z1,z2,z3,z4,z517,z5,z6])],[(0,[z518,z1,z2,z3,z4,z5,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z86,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z520,z6])],[(0,[z1,z2,z3,z4,z521,z5,z6]),(0,[z100,z1,z2,z239,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z185,z1,z2,z239,z4,z5,z6]),(0,[z1,z2,z3,z4,z523,z5,z6]),(0,[z1,z2,z3,z524,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z525])],[(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z3,z4,z527,z5,z6])],[(0,[z1,z2,z3,z4,z5,z528,z6]),(0,[z1,z2,z3,z4,z5,z6,z529]),(1,[z1,z31,z3,z4,z32,z5]),(0,[z1,z2,z3,z4,z530,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z531]),(0,[z1,z2,z3,z4,z5,z6,z532])],[(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z1,z115,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z534,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z110]),(0,[z1,z2,z3,z535,z4,z5,z6])],[(0,[z49,z1,z2,z3,z521,z5,z6]),(0,[z100,z2,z3,z4,z19,z5,z6]),(0,[z1,z536,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z42,z4,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6])]],
   [[(0,[z538,z1,z2,z3,z4,z5,z6]),(0,[z1,z115,z2,z3,z4,z148,z5]),(0,[z1,z2,z3,z4,z5,z539,z6]),(1,[z1,z2,z3,z86,z6,z96])],[(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z1,z2,z3,z4,z541,z5,z6]),(0,[z1,z542,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z543]),(0,[z38,z2,z3,z4,z5,z6,z39]),(0,[z1,z2,z3,z544,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z32,z5]),(0,[z1,z545,z2,z3,z4,z5,z6]),(0,[z1,z546,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z547,z5,z6]),(0,[z1,z2,z3,z4,z548,z5,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z2,z550,z3,z4,z5,z6]),(0,[z1,z2,z3,z86,z4,z6,z96]),(0,[z1,z2,z3,z551,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z1,z2,z3,z4,z553,z5,z6]),(0,[z1,z2,z3,z554,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z555]),(0,[z1,z556,z2,z3,z4,z5,z6])],[(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z558,z4,z5,z6]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z560,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z561,z5,z6]),(0,[z49,z2,z3,z52,z4,z5,z6]),(0,[z1,z2,z50,z4,z5,z6,z126]),(0,[z1,z2,z25,z4,z5,z6,z126]),(0,[z1,z2,z3,z4,z5,z6,z562]),(0,[z1,z563,z2,z3,z4,z5,z6]),(0,[z1,z2,z564,z3,z4,z5,z6]),(0,[z1,z2,z159,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z565,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z567,z4,z5,z6]),(0,[z1,z2,z3,z137,z5,z6,z138])],[(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z224,z1,z2,z3,z4,z21,z6])],[(1,[z1,z2,z3,z521,z5,z6]),(0,[z51,z1,z2,z3,z19,z5,z6]),(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z214,z38,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z569,z4,z5,z6]),(0,[z1,z2,z570,z3,z4,z5,z6])],[(0,[z1,z2,z571,z3,z4,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z6])],[(0,[z2,z3,z4,z189,z5,z13,z6]),(1,[z37,z1,z42,z4,z5,z6]),(0,[z1,z2,z3,z572,z4,z5,z6]),(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z299,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z574,z5,z6]),(0,[z224,z1,z2,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z575,z5,z6]),(0,[z1,z2,z3,z4,z5,z576,z6])],[(0,[z1,z577,z2,z3,z4,z5,z6]),(0,[z1,z2,z578,z3,z4,z5,z6]),(0,[z1,z230,z2,z3,z4,z5,z6]),(1,[z1,z201,z3,z4,z5,z110])],[(0,[z1,z2,z579,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580])],[(0,[z1,z2,z3,z4,z5,z6,z581]),(0,[z1,z2,z3,z4,z5,z6,z582]),(0,[z1,z583,z2,z3,z4,z5,z6])]],
   [[(0,[z12,z2,z3,z4,z189,z5,z6]),(0,[z37,z1,z2,z281,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z64]),(0,[z1,z2,z3,z4,z5,z584,z6])],[(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586]),(0,[z1,z2,z3,z4,z5,z6,z587]),(0,[z1,z33,z2,z3,z34,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z588]),(0,[z1,z2,z589,z3,z4,z5,z6])],[(0,[z1,z590,z2,z3,z4,z5,z6]),(0,[z1,z74,z2,z3,z4,z5,z138])],[(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z6]),(0,[z592,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z593,z5,z6]),(0,[z1,z119,z2,z42,z4,z5,z6]),(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z595]),(0,[z1,z596,z2,z3,z4,z5,z6])],[(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z1,z598,z2,z3,z4,z5,z6]),(0,[z1,z230,z2,z3,z4,z6,z77])],[(0,[z599,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z600,z4,z5,z6]),(0,[z1,z74,z2,z3,z137,z5,z6]),(0,[z1,z2,z3,z601,z4,z5,z6])],[(0,[z1,z2,z3,z602,z4,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z604]),(0,[z1,z2,z3,z4,z605,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z606,z6]),(0,[z1,z2,z3,z4,z607,z5,z6]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z2,z3,z261,z4,z5,z6])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z4,z609,z5,z6]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z611,z5,z6])],[(0,[z1,z2,z3,z4,z612,z5,z6]),(1,[z376,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z1,z2,z3,z613,z4,z5,z6]),(0,[z1,z2,z3,z4,z614,z5,z6])],[(0,[z1,z615,z2,z3,z4,z5,z6]),(0,[z1,z2,z91,z4,z5,z6,z126])],[(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z617,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z77]),(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z96])],[(0,[z619,z1,z2,z3,z4,z5,z6]),(0,[z620,z1,z2,z3,z4,z5,z6]),(0,[z185,z376,z2,z3,z4,z5,z6]),(0,[z621,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z622,z4,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z624,z6]),(0,[z1,z2,z3,z4,z5,z6,z625]),(0,[z1,z626,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z627,z2,z3,z4,z5,z6]),(0,[z2,z50,z3,z91,z4,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z214,z2,z3,z4,z5,z162,z6]),(0,[z185,z1,z2,z4,z5,z6,z126]),(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z156,z6])],[(0,[z1,z2,z3,z4,z631,z5,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z634]),(1,[z1,z2,z113,z4,z5,z191]),(0,[z1,z2,z3,z4,z635,z5,z6])],[(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z637,z4,z5,z6]),(0,[z1,z2,z3,z638,z4,z5,z6])],[(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z12,z298,z2,z3,z4,z5,z6]),(0,[z640,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z1,z119,z2,z281,z4,z5,z6]),(0,[z1,z2,z113,z3,z4,z5,z191]),(0,[z1,z2,z3,z4,z642,z5,z6])],[(0,[z1,z2,z3,z643,z4,z5,z6]),(0,[z644,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z645,z4,z5,z6]),(0,[z1,z2,z3,z4,z646,z5,z6]),(0,[z1,z2,z647,z3,z4,z5,z6])],[(0,[z1,z2,z648,z3,z4,z5,z6])],[(0,[z1,z2,z3,z649,z4,z5,z6]),(0,[z1,z2,z3,z650,z4,z5,z6]),(0,[z38,z1,z2,z3,z4,z5,z162]),(0,[z1,z2,z3,z651,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z652]),(0,[z1,z2,z3,z4,z15,z5,z278]),(0,[z1,z2,z3,z4,z76,z32,z5])]],
   [[(0,[z16,z1,z296,z3,z4,z5,z6]),(0,[z1,z2,z653,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z352,z5,z6]),(0,[z1,z2,z3,z4,z654,z5,z6])],[(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z66,z1,z2,z3,z352,z5,z6]),(0,[z1,z2,z3,z4,z657,z5,z6]),(0,[z1,z2,z3,z658,z4,z5,z6])],[(1,[z16,z296,z3,z4,z5,z6]),(0,[z1,z45,z3,z4,z352,z5,z6]),(0,[z1,z2,z3,z4,z5,z659,z6]),(0,[z1,z2,z3,z4,z660,z5,z6])],[(0,[z661,z1,z2,z3,z4,z5,z6])],[(0,[z1,z662,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z663,z4,z5,z6])],[(0,[z1,z296,z2,z3,z4,z5,z6]),(0,[z1,z2,z239,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z664,z5,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z1,z2,z3,z666,z4,z5,z6]),(0,[z1,z2,z3,z4,z667,z5,z6])],[(0,[z1,z2,z668,z3,z4,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z230,z3,z4,z5,z6,z116]),(0,[z670,z1,z2,z3,z4,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z673,z2,z3,z4,z5,z6]),(0,[z1,z2,z674,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z675,z6]),(0,[z1,z2,z3,z4,z5,z6,z676]),(0,[z1,z2,z3,z4,z5,z6,z677])]],
   [[(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z15,z5,z6]),(0,[z1,z201,z3,z4,z5,z6,z110])],[(0,[z1,z2,z679,z3,z4,z5,z6]),(0,[z1,z680,z2,z3,z4,z5,z6]),(0,[z1,z230,z115,z3,z4,z5,z6]),(0,[z1,z230,z2,z3,z4,z6,z116]),(0,[z1,z2,z3,z4,z5,z6,z191])],[(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z3,z4,z683,z5,z6]),(0,[z1,z2,z684,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z685,z5,z6]),(0,[z1,z2,z686,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z687]),(0,[z1,z196,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z688,z5,z6]),(0,[z689,z1,z2,z3,z4,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z691,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z13,z6]),(1,[z1,z119,z281,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z3,z693,z4,z5,z6])],[(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z1,z695,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z696,z6]),(0,[z1,z33,z2,z3,z86,z5,z6])],[(0,[z1,z2,z3,z697,z4,z5,z6]),(0,[z1,z2,z3,z698,z4,z5,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z701]),(0,[z1,z2,z3,z4,z5,z6,z702]),(0,[z1,z2,z3,z4,z703,z5,z6])],[(0,[z1,z2,z3,z4,z704,z5,z6]),(0,[z1,z2,z3,z705,z4,z5,z6]),(0,[z1,z2,z706,z3,z4,z5,z6]),(0,[z1,z230,z3,z4,z5,z6,z110]),(0,[z1,z115,z2,z3,z4,z6,z77])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z2,z3,z708,z4,z6]),(0,[z1,z709,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z710])],[(0,[z1,z2,z3,z4,z5,z711]),(0,[z1,z712,z2,z3,z5,z6]),(0,[z2,z120,z4,z19,z5,z6]),(0,[z1,z713,z3,z4,z5,z6]),(0,[z714,z2,z3,z4,z5,z6]),(0,[z1,z299,z159,z3,z4,z5])],[(0,[z1,z2,z123,z4,z5,z6]),(0,[z1,z2,z3,z715,z5,z6]),(0,[z117,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z4,z148,z5]),(0,[z1,z115,z3,z4,z15,z278])],[(0,[z1,z2,z3,z4,z716,z6]),(0,[z221,z2,z120,z4,z5,z6])]],
   [[(0,[z1,z717,z3,z4,z5,z6]),(0,[z1,z2,z3,z718,z4,z5]),(0,[z1,z133,z165,z3,z4,z6])],[(0,[z1,z2,z3,z719,z5,z6]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z298,z2,z3,z4,z13,z6]),(0,[z1,z2,z721,z4,z5,z6]),(0,[z722,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z723,z6]),(0,[z1,z159,z3,z4,z5,z191])],[(0,[z1,z2,z50,z521,z5,z6]),(0,[z221,z2,z3,z19,z5,z6]),(1,[z1,z2,z3,z724,z5])],[(0,[z1,z725,z2,z3,z5,z6]),(0,[z1,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z210,z2,z3,z19,z5,z6]),(0,[z37,z1,z42,z4,z5,z64]),(0,[z37,z1,z727,z4,z5,z6]),(0,[z1,z3,z67,z728,z5,z6]),(0,[z700,z1,z3,z4,z5,z110])]],
   [[(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z730,z5,z6]),(0,[z185,z1,z2,z5,z6,z126]),(0,[z1,z2,z3,z4,z731,z6])],[(0,[z1,z2,z91,z521,z5,z6])],[(0,[z1,z732,z2,z3,z4,z5]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z1,z376,z2,z5,z6,z126]),(0,[z1,z133,z165,z158,z3,z4])],[(0,[z1,z2,z3,z734,z5,z6]),(0,[z1,z45,z3,z728,z5,z6]),(0,[z1,z735,z3,z4,z5,z6]),(0,[z1,z165,z159,z3,z4,z5])]],
   [[(0,[z18,z2,z736,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z738,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z739,z6]),(0,[z1,z2,z3,z740,z5,z6]),(0,[z2,z91,z4,z521,z5,z6]),(0,[z597,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z741,z4,z6])],[(0,[z1,z2,z3,z742,z5,z6]),(0,[z1,z3,z4,z743,z5,z6]),(0,[z744,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z477]),(0,[z1,z3,z4,z745,z5,z6])],[(0,[z51,z2,z3,z715,z5,z6]),(0,[z746,z2,z3,z4,z5,z6]),(0,[z747,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z748])]],
   [[(0,[z1,z749,z3,z4,z5,z6]),(0,[z280,z2,z50,z3,z5,z6]),(0,[z2,z3,z4,z5,z162,z750]),(0,[z1,z2,z113,z4,z5,z191]),(0,[z1,z751,z3,z4,z5,z6])],[(0,[z1,z2,z4,z752,z5,z6]),(0,[z1,z271,z3,z4,z32,z5])],[(0,[z1,z2,z3,z728,z5,z6]),(0,[z221,z2,z239,z3,z5,z6]),(0,[z1,z133,z3,z4,z6,z77])],[(0,[z280,z1,z2,z239,z5,z6]),(0,[z1,z3,z4,z5,z748,z6]),(0,[z1,z2,z20,z4,z21,z6]),(0,[z1,z753,z3,z4,z5,z6]),(0,[z1,z754,z3,z4,z5,z6]),(0,[z1,z2,z3,z137,z5,z138])]],
   [[(0,[z2,z3,z4,z715,z5,z6])],[(0,[z1,z755,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z756,z6])],[(0,[z2,z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z758,z6]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z4,z760,z6]),(0,[z1,z115,z3,z4,z15,z6]),(0,[z1,z230,z3,z4,z6,z129]),(0,[z164,z1,z2,z69,z4,z5])],[(0,[z1,z2,z3,z4,z761,z6]),(0,[z1,z196,z3,z4,z6,z110]),(0,[z1,z2,z762,z3,z4,z5]),(0,[z1,z763,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z765,z2,z3,z4,z5]),(0,[z1,z766,z2,z3,z4,z5]),(0,[z1,z230,z3,z4,z767,z6])],[(0,[z16,z296,z3,z4,z5,z6]),(0,[z280,z1,z2,z120,z5,z6]),(0,[z1,z768,z2,z3,z4,z5]),(0,[z769,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z770,z6])],[(0,[z2,z3,z771,z4,z5,z6]),(0,[z1,z230,z674,z3,z4,z6]),(1,[z1,z2,z5,z6,z772]),(0,[z1,z2,z3,z136,z4,z5])],[(0,[z1,z2,z3,z4,z773,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z2,z3,z715,z19,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z3,z728,z4,z5,z6]),(0,[z1,z2,z69,z775,z4,z5])],[(0,[z1,z2,z120,z19,z5,z6]),(0,[z51,z2,z3,z499,z5,z6]),(0,[z2,z3,z4,z5,z750,z6]),(0,[z1,z2,z3,z4,z776,z6]),(0,[z1,z2,z3,z777,z4,z5]),(0,[z1,z2,z3,z4,z5,z278]),(0,[z1,z2,z3,z775,z4,z5]),(0,[z1,z165,z2,z778,z3,z4])],[(0,[z1,z281,z727,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z156])],[(0,[z2,z3,z52,z5,z6,z588]),(0,[z1,z230,z2,z3,z4,z278]),(0,[z779,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z477,z5,z110]),(0,[z1,z2,z3,z4,z282,z77]),(0,[z376,z2,z4,z5,z6,z126]),(0,[z1,z159,z3,z69,z4,z5])],[(0,[z57,z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z780,z4,z6]),(0,[z49,z2,z91,z521,z5,z6]),(0,[z1,z230,z3,z4,z6,z116]),(0,[z1,z610,z3,z4,z5,z110]),(0,[z1,z2,z3,z4,z156,z191])],[(0,[z218,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z419,z3,z4,z32,z5])],[(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z783,z3,z4,z5,z6]),(0,[z1,z2,z784,z4,z5,z6]),(1,[z2,z3,z715,z5,z6]),(0,[z1,z2,z3,z785,z5,z6]),(0,[z1,z115,z299,z3,z4,z15]),(0,[z1,z2,z20,z4,z21,z361])]],
   [[(0,[z1,z2,z239,z289,z5,z6]),(0,[z100,z2,z123,z19,z5,z6]),(0,[z1,z271,z2,z3,z4,z77])],[(0,[z1,z2,z3,z786,z5,z6]),(0,[z1,z787,z3,z4,z5,z6]),(0,[z1,z788,z3,z4,z5,z6]),(0,[z185,z218,z2,z5,z6,z126])],[(0,[z1,z789,z2,z3,z4,z5]),(0,[z2,z50,z4,z5,z6,z333]),(0,[z790,z2,z3,z4,z5,z6]),(0,[z1,z2,z791,z4,z5,z6]),(0,[z1,z792,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z115,z3,z4,z15,z205])]],
   [[(0,[z1,z2,z3,z794,z5,z6]),(0,[z1,z2,z3,z4,z5,z795]),(0,[z1,z2,z10,z4,z5,z191])],[(0,[z1,z796,z3,z4,z5,z6]),(0,[z1,z2,z242,z25,z5,z6]),(0,[z1,z2,z3,z797,z4,z5]),(0,[z1,z159,z3,z4,z76,z5])],[(1,[z2,z91,z521,z5,z6]),(0,[z185,z2,z5,z6,z153,z126]),(0,[z1,z798,z3,z4,z5,z6])],[(0,[z2,z3,z736,z4,z5,z6]),(0,[z49,z280,z2,z3,z5,z6]),(0,[z2,z91,z19,z5,z6,z126]),(0,[z280,z2,z3,z19,z5,z6]),(0,[z1,z2,z113,z775,z4,z5])]],
   [[(0,[z799,z2,z3,z4,z5,z6]),(0,[z1,z2,z20,z800,z4,z6]),(0,[z1,z33,z2,z3,z34,z6])],[(0,[z221,z2,z3,z4,z5,z6]),(0,[z272,z1,z2,z69,z4,z5]),(0,[z1,z74,z2,z3,z724,z5])],[(0,[z185,z221,z2,z5,z6,z126])],[(0,[z49,z2,z91,z59,z5,z6]),(0,[z280,z1,z2,z5,z6,z126]),(0,[z801,z2,z3,z4,z5,z6]),(0,[z1,z2,z778,z3,z4,z77])]],
   [[(0,[z802,z1,z2,z4,z5,z6]),(0,[z1,z2,z775,z4,z5,z191])],[(0,[z2,z3,z803,z4,z5,z6]),(0,[z690,z2,z91,z4,z5,z6]),(0,[z1,z2,z239,z120,z5,z6]),(0,[z1,z2,z804,z4,z5,z6]),(0,[z38,z2,z3,z4,z5,z39])],[(0,[z805,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z806]),(0,[z1,z2,z239,z5,z6,z772]),(1,[z1,z2,z778,z3,z4])],[(0,[z1,z807,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z2,z4,z5,z6,z772])]],
   [[(0,[z809,z2,z3,z4,z5,z6]),(0,[z1,z159,z3,z4,z5,z6]),(0,[z1,z31,z299,z3,z4,z5]),(1,[z1,z3,z4,z5,z748]),(1,[z1,z2,z800,z4,z6]),(0,[z1,z2,z261,z800,z4,z6]),(0,[z1,z2,z3,z4,z810,z5])],[(0,[z1,z2,z3,z811,z4,z5]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z115,z3,z4,z530,z6]),(0,[z1,z2,z3,z4,z5,z813])],[(0,[z1,z2,z3,z521,z5,z6]),(0,[z298,z2,z3,z4,z756,z6]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z66,z1,z3,z67,z5,z6])],[(0,[z1,z757,z3,z4,z5,z6]),(0,[z18,z2,z3,z521,z5,z6]),(0,[z1,z2,z3,z815,z4,z6]),(1,[z1,z3,z728,z5,z6]),(0,[z1,z115,z3,z4,z15,z148]),(0,[z1,z816,z3,z4,z5,z6])]],
   [[(0,[z37,z1,z42,z4,z5,z6])],[(0,[z1,z2,z3,z817,z5,z6]),(0,[z37,z1,z42,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z819,z2,z3,z4,z5,z6]),(1,[z1,z2,z775,z4,z5])],[(0,[z820,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z821,z4,z5]),(0,[z185,z221,z2,z3,z5,z6]),(0,[z1,z165,z158,z159,z3,z4])],[(0,[z280,z1,z2,z3,z5,z6]),(0,[z1,z822,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z201,z159,z3,z4,z5]),(0,[z1,z2,z3,z724,z137,z5])]],
   [[(0,[z1,z2,z3,z824,z5,z6]),(0,[z1,z2,z120,z52,z5,z6]),(0,[z1,z2,z3,z825,z5,z6]),(0,[z2,z3,z4,z756,z13,z6])],[(0,[z221,z2,z91,z4,z5,z6]),(1,[z2,z3,z4,z5,z750]),(0,[z1,z2,z3,z4,z5,z64]),(0,[z376,z2,z239,z4,z5,z6]),(0,[z1,z2,z239,z25,z5,z6]),(0,[z2,z3,z4,z5,z6,z826]),(0,[z1,z2,z3,z34,z741,z6])],[(0,[z1,z2,z3,z827,z5,z6]),(0,[z1,z3,z4,z828,z5,z6]),(0,[z1,z2,z3,z829,z5,z6]),(1,[z2,z120,z19,z5,z6]),(0,[z2,z3,z4,z5,z750,z39]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z1,z3,z727,z4,z5,z6]),(0,[z1,z2,z3,z831,z5,z6])],[(0,[z1,z832,z2,z3,z4,z6]),(0,[z1,z727,z42,z4,z5,z6]),(0,[z1,z2,z3,z833,z5,z6]),(0,[z1,z31,z196,z3,z4,z6])]],
   [[(0,[z1,z2,z727,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z224,z1,z2,z261,z4,z6])],[(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z836,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z2,z3,z838,z5,z6]),(0,[z1,z165,z2,z3,z4,z156]),(0,[z1,z2,z3,z4,z5,z361])],[(0,[z100,z2,z3,z521,z5,z6]),(0,[z1,z2,z3,z4,z5,z839]),(0,[z1,z299,z2,z3,z4,z5]),(0,[z1,z299,z3,z4,z5,z110])],[(0,[z1,z33,z2,z3,z741,z6])]],
   [[(0,[z1,z2,z120,z4,z5,z6]),(0,[z690,z100,z2,z3,z5,z6]),(0,[z1,z840,z2,z3,z4,z5])],[(0,[z296,z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z1,z842,z3,z4,z5,z6]),(0,[z1,z230,z165,z3,z4,z110]),(0,[z1,z2,z3,z4,z575,z77])],[(0,[z376,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z153]),(0,[z2,z3,z4,z756,z5,z6]),(0,[z1,z2,z3,z843,z4,z5]),(0,[z1,z2,z3,z4,z844,z6]),(0,[z1,z3,z4,z15,z767,z6]),(0,[z1,z318,z3,z4,z5,z110])],[(0,[z1,z2,z845,z4,z5,z6]),(0,[z1,z133,z3,z4,z5,z6]),(0,[z185,z376,z2,z5,z6,z126])]],
   [[(0,[z1,z2,z3,z846,z5,z6]),(0,[z510,z2,z50,z4,z5,z6]),(0,[z1,z847,z3,z4,z5,z6]),(0,[z1,z74,z2,z3,z75,z5]),(0,[z1,z2,z3,z724,z5,z138])],[(0,[z2,z3,z52,z521,z5,z6]),(0,[z1,z3,z4,z5,z767,z6]),(0,[z848,z2,z3,z4,z5,z6]),(0,[z1,z2,z778,z3,z4,z6])],[(0,[z1,z2,z3,z849,z5,z6]),(0,[z1,z2,z800,z4,z21,z6])],[(0,[z1,z2,z3,z4,z5,z850]),(0,[z100,z2,z3,z715,z5,z6]),(0,[z851,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z230,z3,z4,z5,z205])]],
   [[(0,[z1,z2,z853,z4,z5,z6]),(0,[z1,z2,z4,z854,z5,z6]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z2,z3,z4,z767,z6])],[(0,[z1,z2,z856,z4,z5,z6]),(0,[z1,z2,z3,z4,z857,z6]),(0,[z1,z2,z3,z4,z858,z6])],[(0,[z1,z2,z736,z4,z5,z6]),(0,[z1,z2,z3,z4,z859,z5]),(0,[z860,z2,z3,z4,z5,z6])],[(0,[z51,z2,z239,z91,z5,z6]),(0,[z861,z2,z3,z4,z5,z6]),(0,[z1,z201,z3,z4,z5,z748]),(0,[z1,z2,z3,z69,z4,z156])]],
   [[(0,[z1,z2,z862,z4,z5,z6]),(0,[z12,z2,z3,z4,z756,z6]),(0,[z1,z3,z728,z352,z5,z6]),(0,[z1,z31,z3,z4,z5,z608]),(0,[z1,z2,z3,z4,z156,z6]),(0,[z1,z863,z3,z4,z5,z6])],[(0,[z2,z736,z91,z4,z5,z6]),(0,[z51,z2,z120,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z864]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z2,z50,z120,z4,z5,z6]),(0,[z2,z3,z52,z715,z5,z6]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z867,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z868,z6]),(0,[z1,z2,z3,z4,z869,z5]),(0,[z100,z2,z3,z19,z5,z6]),(0,[z1,z3,z4,z767,z6,z116]),(0,[z1,z31,z3,z4,z530,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z2,z3,z871,z4,z6])],[(0,[z1,z31,z196,z3,z4,z32]),(0,[z1,z872,z3,z4,z5,z6]),(0,[z224,z1,z2,z800,z4,z6])],[(0,[z1,z2,z3,z4,z5,z873]),(0,[z214,z2,z3,z4,z5,z750]),(0,[z874,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z77]),(0,[z1,z3,z4,z32,z5,z748])],[(0,[z49,z280,z2,z91,z5,z6]),(0,[z49,z2,z90,z91,z5,z6]),(0,[z2,z50,z52,z5,z6,z126]),(0,[z875,z2,z3,z4,z5,z6])]],
   [[(1,[z757,z3,z4,z5,z6]),(0,[z100,z2,z679,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z876]),(0,[z1,z2,z3,z4,z76,z156])],[(0,[z49,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z877,z5,z6]),(0,[z1,z878,z2,z3,z5,z6]),(0,[z164,z1,z2,z775,z4,z5]),(0,[z1,z2,z3,z75,z724,z5])],[(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z2,z3,z4,z880,z6]),(0,[z12,z2,z3,z4,z189,z6]),(0,[z1,z165,z695,z2,z3,z4])],[(0,[z1,z2,z3,z4,z5,z881]),(0,[z1,z2,z3,z4,z882,z6]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z77]),(0,[z1,z165,z2,z3,z4,z148]),(0,[z1,z3,z4,z5,z748,z110]),(0,[z1,z2,z3,z800,z4,z6]),(0,[z1,z2,z778,z3,z4,z5])]],
   [[(0,[z1,z884,z2,z3,z4,z5]),(0,[z49,z2,z120,z4,z5,z6]),(0,[z2,z50,z736,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z230,z31,z3,z4,z77]),(0,[z1,z695,z3,z4,z15,z6])],[(0,[z1,z230,z144,z3,z4,z6]),(0,[z1,z2,z5,z6,z772,z126]),(0,[z1,z2,z3,z724,z4,z5])],[(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z887,z2,z3,z4,z6]),(0,[z1,z45,z3,z352,z5,z6])],[(0,[z1,z2,z3,z4,z888,z6]),(0,[z757,z17,z3,z4,z5,z6]),(0,[z100,z376,z2,z3,z5,z6]),(0,[z1,z31,z3,z4,z32,z156]),(0,[z1,z2,z775,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z889,z5,z6]),(0,[z51,z2,z3,z622,z5,z6]),(0,[z2,z3,z4,z189,z756,z6]),(0,[z1,z119,z281,z4,z5,z6]),(0,[z1,z2,z3,z890,z4,z6]),(0,[z1,z3,z4,z891,z5,z6]),(0,[z1,z892,z3,z4,z5,z6])],[(0,[z1,z893,z2,z3,z4,z6]),(0,[z1,z2,z3,z894,z4,z5]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z376,z2,z3,z25,z5,z6])],[(0,[z1,z2,z896,z4,z5,z6])],[(0,[z1,z119,z727,z4,z5,z6]),(0,[z1,z196,z2,z3,z4,z6])]],
   [[(0,[z1,z897,z3,z4,z5,z6]),(0,[z1,z2,z239,z225,z5,z6])],[(1,[z1,z727,z4,z5,z6]),(0,[z1,z898,z3,z4,z5,z6])],[(0,[z1,z2,z899,z4,z5,z6]),(0,[z16,z757,z3,z4,z5,z6]),(0,[z2,z3,z91,z521,z5,z6]),(0,[z49,z2,z736,z4,z5,z6]),(0,[z100,z2,z120,z19,z5,z6]),(0,[z51,z376,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z900])],[(0,[z1,z2,z3,z901,z4,z5]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z1,z2,z25,z5,z6,z772]),(0,[z1,z2,z20,z136,z4,z21])]],
   [[(0,[z57,z17,z3,z4,z5,z6]),(0,[z18,z2,z114,z4,z5,z6]),(0,[z221,z2,z3,z52,z5,z6]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z1,z31,z159,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z905])],[(0,[z1,z2,z3,z906,z5,z6]),(0,[z1,z2,z3,z4,z5,z907]),(0,[z66,z1,z3,z728,z5,z6]),(0,[z1,z2,z3,z4,z908,z6]),(0,[z1,z31,z3,z4,z32,z5]),(0,[z1,z2,z3,z4,z5,z909]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z778,z3,z4])],[(0,[z1,z2,z3,z4,z911,z6]),(0,[z1,z2,z912,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z376,z2,z3,z5,z6,z126]),(0,[z914,z2,z3,z4,z5,z6]),(0,[z1,z915,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z916,z5]),(0,[z1,z165,z2,z3,z4,z608]),(0,[z917,z2,z3,z4,z5,z6])],[(0,[z280,z51,z2,z3,z5,z6]),(0,[z100,z2,z239,z50,z5,z6]),(0,[z1,z918,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z919])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z920,z5,z6]),(0,[z1,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z922]),(1,[z376,z2,z5,z6,z126]),(0,[z1,z2,z416,z4,z5,z191]),(0,[z1,z2,z3,z741,z6,z96])],[(1,[z2,z736,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z923]),(0,[z1,z2,z3,z86,z6,z96])]],
   [[(0,[z1,z2,z3,z924,z5,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z1,z115,z3,z4,z767,z6])],[(0,[z1,z2,z3,z926,z4,z6]),(0,[z1,z2,z3,z4,z927,z5]),(0,[z1,z2,z3,z928,z5,z6]),(1,[z1,z3,z4,z767,z6]),(0,[z1,z201,z2,z3,z4,z156])],[(0,[z1,z2,z3,z4,z929,z6]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z185,z1,z2,z120,z5,z6]),(0,[z214,z2,z3,z4,z5,z162]),(0,[z1,z2,z3,z4,z931,z6])],[(0,[z1,z932,z2,z3,z4,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z2,z3,z934,z4,z5]),(0,[z1,z2,z4,z935,z5,z6]),(0,[z185,z1,z2,z5,z6,z772]),(1,[z1,z2,z3,z741,z6])]],
   [[(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z937]),(0,[z1,z230,z3,z4,z696,z6]),(0,[z1,z2,z3,z938,z4,z5]),(0,[z1,z2,z3,z4,z76,z77])],[(0,[z221,z2,z3,z521,z5,z6]),(0,[z1,z158,z2,z3,z345,z4]),(0,[z1,z2,z778,z3,z4,z76])],[(0,[z1,z2,z3,z4,z5,z939]),(0,[z1,z940,z3,z4,z5,z6]),(0,[z1,z2,z800,z4,z5,z6]),(0,[z1,z2,z3,z741,z86,z6])],[(0,[z1,z2,z3,z4,z148,z156]),(0,[z1,z115,z2,z3,z4,z278])]],
   [[(0,[z1,z2,z941,z4,z5,z6]),(0,[z1,z2,z942,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z2,z3,z4,z944,z6])],[(0,[z51,z2,z3,z52,z5,z6]),(1,[z2,z3,z4,z756,z6]),(0,[z1,z3,z4,z15,z5,z205]),(0,[z1,z2,z3,z741,z5,z6])],[(0,[z280,z376,z2,z3,z5,z6]),(0,[z2,z3,z120,z19,z5,z6]),(0,[z1,z2,z3,z4,z945,z6]),(0,[z1,z2,z3,z724,z5,z6]),(0,[z1,z165,z158,z2,z3,z4])],[(0,[z38,z2,z3,z4,z5,z750]),(0,[z946,z2,z3,z4,z5,z6]),(0,[z947,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z2,z3,z949,z5,z6]),(0,[z18,z2,z50,z4,z5,z6]),(0,[z1,z201,z3,z4,z5,z110]),(0,[z1,z31,z3,z4,z5,z748]),(0,[z950,z2,z3,z4,z5,z6]),(0,[z1,z2,z457,z69,z4,z5])],[(0,[z221,z2,z50,z4,z5,z6]),(0,[z1,z951,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z952])],[(0,[z1,z953,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z954,z6]),(0,[z690,z1,z2,z5,z6,z126]),(0,[z1,z2,z3,z5,z6,z772]),(0,[z1,z955,z3,z4,z5,z6])],[(0,[z1,z2,z3,z956,z5,z6]),(0,[z1,z2,z3,z957,z5,z6]),(0,[z639,z1,z2,z5,z6,z126]),(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z3,z4,z5,z205]),(0,[z1,z959,z2,z3,z4,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 568) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 568).take 378) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 946)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [568, 378] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 11).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 11] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_44666

theorem PEqualNP.Outside.L_meta_44666 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4241008768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4241008768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_44666.solve