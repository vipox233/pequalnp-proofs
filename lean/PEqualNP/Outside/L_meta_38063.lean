import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38063

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
  Nat.testBit (4278124200 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8a001819a3646452#64 ++ 0x08a001819a364645#64 ++ 0xfd08383fe76464ff#64 ++ 0x7fd08383fe76464f#64 : BitVec 256),
   (0x04044444408181a0#64 ++ 0x204044444408181a#64 ++ 0xdb94c4c4688787fe#64 ++ 0xedb94c4c4688787f#64 : BitVec 256),
   (0x0805050680a8a8c4#64 ++ 0x30805050680a8a8c#64 ++ 0xb7e7070790f8f8cd#64 ++ 0xdb7e7070790f8f8c#64 : BitVec 256),
   (0x503802a81d005609#64 ++ 0x4503802a81d00560#64 ++ 0x8ff807f81f00ff0b#64 ++ 0xf8ff807f81f00ff0#64 : BitVec 256),
   (0x603aa8001e560001#64 ++ 0x8603aa8001e56000#64 ++ 0x7f3ff8001fff0007#64 ++ 0xc7f3ff8001fff000#64 : BitVec 256),
   (0x807ff7f760000001#64 ++ 0xf807ff7f76000000#64 ++ 0xff7fffffe0000000#64 ++ 0x3ff7fffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0400404040010120 0x0040040404001012 0x4810c0c068070732 0x24810c0c06807073

def z1 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c4688787fe 0xedb94c4c4688787f

def z2 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c7c7f8ffffff 0xffff7c7c7f8fffff

def z3 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81f00ff0b 0xf8ff807f81f00ff0

def z4 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8001fff0007 0xc7f3ff8001fff000

def z5 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0000000 0x3ff7fffffe000000

def z6 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe76464ff 0x7fd08383fe76464f

def z7 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x3007000780f800c4 0x03007000780f800c

def z8 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e7070790f8f8cd 0xdb7e7070790f8f8c

def z9 : W := mkw 0x8045555760000000 0x3804555576000000 0x00000007e0000000 0x000000007e000000

def z10 : W := mkw 0x804557f760000000 0x7804557f76000000 0x804007ffe0000000 0x3804007ffe000000

def z11 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0x7007f807e0000000 0x07007f807e000000

def z12 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe0000000 0x3fd08383fe000000

def z13 : W := mkw 0x84045455608181a0 0x284045455608181a 0xff9cfcffe88787fe 0xfff9cfcffe88787f

def z14 : W := mkw 0x0801010280282844 0x1080101028028284 0x2463030390787801 0x1246303039078780

def z15 : W := mkw 0xda381ab9bf64765b 0x4da381ab9bf64765 0xfff83fffff64ffff 0xffff83fffff64fff

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000000800870a 0xc008000000800870

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x5900000000040006 0x4590000000004000

def z18 : W := mkw 0x0400404040010120 0x0040040404001012 0xd910c0c4680707fe 0x6d910c0c4680707f

def z19 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x7f3ff80000000000 0x07f3ff8000000000

def z20 : W := mkw 0x8e04545de1a1e5f2 0x28e04545de1a1e5f 0xdb94c4ffe887e7fe 0xfdb94c4ffe887e7f

def z21 : W := mkw 0x887ff7f7e0a8a8c5 0xf887ff7f7e0a8a8c 0xfffffffff0f8f8cd 0xffffffffff0f8f8c

def z22 : W := mkw 0xd07ff7ff7d005609 0xfd07ff7ff7d00560 0xffffffffff00ff0b 0xfffffffffff00ff0

def z23 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x4a3ff8001f9f0002 0x84a3ff8001f9f000

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x7d08380000000000 0x07d0838000000000

def z25 : W := mkw 0x8e045c55e2e5a1f2 0x28e045c55e2e5a1f 0x7004f807e0e700f4 0x07004f807e0e700f

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x3727000010f80005 0xc3727000010f8000

def z27 : W := mkw 0x683fad069efea8c5 0xb683fad069efea8c 0xffffff079ffff8cf 0xdffffff079ffff8c

def z28 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdff4c7c47887ffff 0xfdff4c7c47887fff

def z29 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0x008000001f64ffff 0xc008000001f64fff

def z30 : W := mkw 0x007fe7e640000001 0xf007fe7e64000000 0x0277c7c000000000 0x00277c7c00000000

def z31 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000076464ff 0x400000000076464f

def z32 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x242b380017780001 0x0242b38001778000

def z33 : W := mkw 0x0005050600888884 0x3000505060088888 0x02e7070010989800 0x802e707001098980

def z34 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x246b3b3b80000000 0x1246b3b3b8000000

def z35 : W := mkw 0x04054546408181a0 0x304054546408181a 0xfff7c7c7e88787fe 0xffff7c7c7e88787f

def z36 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7007f80000ff0004 0x07007f80000ff000

def z37 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x0237c000189b0000 0x80237c000189b000

def z38 : W := mkw 0x0c00000080a9a9e4 0x00c00000080a9a9e 0x0080000018ffffff 0xc0080000018fffff

def z39 : W := mkw 0x04054546408989a4 0x304054546408989a 0x02f7c7c0189b9b00 0x802f7c7c0189b9b0

def z40 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0x0000003b80006000 0x10000003b8000600

def z41 : W := mkw 0x0000080002440000 0x0000008000244000 0x7d08380007640007 0x47d0838000764000

def z42 : W := mkw 0xea3ab819bf766453 0x8ea3ab819bf76645 0xff3ff83fffff64ff 0xfff3ff83fffff64f

def z43 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x7f3ff800189b0000 0x87f3ff800189b000

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x2423000010780001 0x0242300001078000

def z45 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x4818f8000f070002 0x04818f8000f07000

def z46 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0x0080000010f8f8cd 0xc0080000010f8f8c

def z47 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0x4818f8f860000000 0x24818f8f86000000

def z48 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5004c004608700f4 0x05004c004608700f

def z49 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xaf7b3ffb80000000 0x3af7b3ffb8000000

def z50 : W := mkw 0x88051517a0a8a8c4 0x388051517a0a8a8c 0xffef3f3ff0f8f8cd 0xfffef3f3ff0f8f8c

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x87e007001000f809 0xd87e007001000f80

def z52 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xffe83f3ff764fcff 0xfffe83f3ff764fcf

def z53 : W := mkw 0x804557f760000000 0x7804557f76000000 0xb76707ffe0000000 0x3b76707ffe000000

def z54 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x3467030790f878c5 0x13467030790f878c

def z55 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x081800f80f000702 0x2081800f80f00070

def z56 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe88787fe 0xfffffffffe88787f

def z57 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7d18f8000f670007 0x47d18f8000f67000

def z58 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff2f383ff7fc64ff 0xfff2f383ff7fc64f

def z59 : W := mkw 0x003802a000000001 0x4003802a00000000 0x8f7807f800000000 0x38f7807f80000000

def z60 : W := mkw 0x04044444408181a0 0x204044444408181a 0x808004c4600087f8 0x2808004c4600087f

def z61 : W := mkw 0x0000000801004400 0x0000000080100440 0x8fe807381700fc0b 0xf8fe807381700fc0

def z62 : W := mkw 0x500000001c001208 0x0500000001c00120 0x0080000018009b00 0x80080000018009b0

def z63 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe800870a 0xfffffffffe800870

def z64 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff1cf83fefe764ff 0xfff1cf83fefe764f

def z65 : W := mkw 0x0000000801004400 0x0000000080100440 0x8d0800380700640b 0x78d0800380700640

def z66 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0x70003807e06400f4 0x070003807e06400f

def z67 : W := mkw 0x0800000080202040 0x0080000008020204 0xfd000007e06464ff 0x7fd000007e06464f

def z68 : W := mkw 0x583d07ae9da8fecd 0x7583d07ae9da8fec 0xbfff07ff9ff8ffcf 0xfbfff07ff9ff8ffc

def z69 : W := mkw 0x8a455fffe3646452 0x78a455fffe364645 0xfd483fffe76464ff 0x7fd483fffe76464f

def z70 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0x8fffc7f81f9bff0b 0xf8fffc7f81f9bff0

def z71 : W := mkw 0x8a041c1da3e4e4d2 0x28a041c1da3e4e4d 0xff8c3c3fe7e4e4ff 0xfff8c3c3fe7e4e4f

def z72 : W := mkw 0x804113b320000000 0x5804113b32000000 0x0040033b80000000 0x10040033b8000000

def z73 : W := mkw 0xd87ff7fffda8fecd 0xfd87ff7fffda8fec 0xfffffffffff8ffcf 0xffffffffffff8ffc

def z74 : W := mkw 0x0004040400808080 0x2000404040080808 0x93840404008080cc 0xc93840404008080c

def z75 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0x8000003fe00064f8 0x38000003fe00064f

def z76 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7f7c7c798fbfbcd 0xdb7f7c7c798fbfbc

def z77 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7d2b3800177c0007 0x47d2b3800177c000

def z78 : W := mkw 0x100002a801005608 0x4100002a80100560 0x8bd007f80800ff0a 0xf8bd007f80800ff0

def z79 : W := mkw 0x0400404040010120 0x0040040404001012 0x5b14c0c068870736 0xe5b14c0c06887073

def z80 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0x4818f8f80f070702 0x24818f8f80f07070

def z81 : W := mkw 0x100002a801005608 0x4100002a80100560 0x0040033800007800 0x1004003380000780

def z82 : W := mkw 0xa07ffff762560001 0xfa07ffff76256000 0xff7fffffe0ff0004 0x3ff7fffffe0ff000

def z83 : W := mkw 0x807d57f760000001 0x7807d57f76000000 0x8f7807ffe0000000 0x38f7807ffe000000

def z84 : W := mkw 0x04000000008181a0 0x004000000008181a 0x00800000088787fe 0xc00800000088787f

def z85 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7808383fe76404f6 0x27808383fe76404f

def z86 : W := mkw 0x2807ad0682fea8c4 0xb2807ad0682fea8c 0xf7e7ff0790fff8cd 0xdf7e7ff0790fff8c

def z87 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x93c407078080f8cc 0xd93c407078080f8c

def z88 : W := mkw 0x8200181923444412 0x0820018192344441 0x4808383867040432 0x2480838386704043

def z89 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xfd0ff83fe0000000 0x3fd0ff83fe000000

def z90 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe00404fe 0x7fd08383fe00404f

def z91 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7fffffff000003 0xfff7fffffff00000

def z92 : W := mkw 0x403aa0001c000001 0x8403aa0001c00000 0x7f3ff8001f000003 0xc7f3ff8001f00000

def z93 : W := mkw 0x8a7ffff7e2642053 0xf8a7ffff7e264205 0xff7fffffe06400f4 0x3ff7fffffe06400f

def z94 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x82f007f81800ff08 0xb82f007f81800ff0

def z95 : W := mkw 0x8000101120000000 0x0800010112000000 0x2408383b80000000 0x12408383b8000000

def z96 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdffcc7f81f87ff0f 0xfdffcc7f81f87ff0

def z97 : W := mkw 0x8e045c5de3e5e5f2 0x28e045c5de3e5e5f 0xfd0cf83fe7e764ff 0x7fd0cf83fe7e764f

def z98 : W := mkw 0x540000081d81d7a8 0x0540000081d81d7a 0x008000001f87ffff 0xc008000001f87fff

def z99 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x4f38f8001f070003 0xc4f38f8001f07000

def z100 : W := mkw 0x100002a801005608 0x4100002a80100560 0x80c007f80000ff08 0x380c007f80000ff0

def z101 : W := mkw 0x500000081d005608 0x0500000081d00560 0x008000001f00ff0b 0xc008000001f00ff0

def z102 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0xff3ff83fe0000000 0x3ff3ff83fe000000

def z103 : W := mkw 0x04044444408181a0 0x204044444408181a 0x0294c4c008838300 0x80294c4c00883830

def z104 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x2408383b87606001 0x12408383b8760600

def z105 : W := mkw 0x403800001c000001 0x0403800001c00000 0x0230000018000000 0x8023000001800000

def z106 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe08080cc 0xfffffffffe08080c

def z107 : W := mkw 0x8a051d1fa3ececd6 0x38a051d1fa3ececd 0xffef3f3ff7fcfcff 0xfffef3f3ff7fcfcf

def z108 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0xfffffff81fffff0f 0xffffffff81fffff0

def z109 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfffffffff000f809 0xffffffffff000f80

def z110 : W := mkw 0x007fe7e640000001 0xf007fe7e64000000 0x7f7fffc000000000 0x07f7fffc00000000

def z111 : W := mkw 0x04044444408181a0 0x204044444408181a 0x0294c4c0088787fe 0xc0294c4c0088787f

def z112 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x02e7070010f8f8cd 0xc02e7070010f8f8c

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0xb500000780000000 0x1b50000078000000

def z114 : W := mkw 0x0000080002440000 0x0000008000244000 0x7000380000640004 0x0700038000064000

def z115 : W := mkw 0xea3ab819bf766453 0x8ea3ab819bf76645 0x242b383b97786001 0x1242b383b9778600

def z116 : W := mkw 0xe07ffff77e560001 0xfe07ffff77e56000 0xff7fffffffff0007 0xfff7fffffffff000

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0xd900000460000000 0x2d90000046000000

def z118 : W := mkw 0x500000081d005608 0x0500000081d00560 0x8b9004c01f00ff0b 0xe8b9004c01f00ff0

def z119 : W := mkw 0x003802a000000001 0x4003802a00000000 0x0468033800000000 0x1046803380000000

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0xd9000004600404fe 0x6d9000004600404f

def z121 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xfd6b3b3fe0000000 0x3fd6b3b3fe000000

def z122 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x3737c00018fb0005 0xc3737c00018fb000

def z123 : W := mkw 0x600008001e560000 0x0600008001e56000 0x000000001fff0007 0xc000000001fff000

def z124 : W := mkw 0x500000081d005608 0x0500000081d00560 0x0000000017007801 0x0000000001700780

def z125 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xc808383fe70464fa 0x3c808383fe70464f

def z126 : W := mkw 0xda381ab9bf64765b 0x4da381ab9bf64765 0xaff83ffb9f60ff0b 0xfaff83ffb9f60ff0

def z127 : W := mkw 0x0005050600888884 0x3000505060088888 0xb7e7070790989800 0x9b7e707079098980

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x5b14c00008870006 0xc5b14c0000887000

def z129 : W := mkw 0x8e045c5de3e5e5f2 0x28e045c5de3e5e5f 0xff9cfcffefe7e7ff 0xfff9cfcffefe7e7f

def z130 : W := mkw 0x0000000801004400 0x0000000080100440 0x000000000700640b 0x4000000000700640

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x8b9004c00800870a 0xe8b9004c00800870

def z132 : W := mkw 0x543c46ec5d81d7a9 0x6543c46ec5d81d7a 0xdffcc7fc7f87ffff 0xfdffcc7fc7f87fff

def z133 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x04e803381f00ff0b 0xd04e803381f00ff0

def z134 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xc858ffffe0000000 0x3c858ffffe000000

def z135 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7007f8001fff0007 0xc7007f8001fff000

def z136 : W := mkw 0x8a7fffffe3646453 0xf8a7fffffe364645 0xff7fffffe76464ff 0x7ff7fffffe76464f

def z137 : W := mkw 0xea3ab819bf766453 0x8ea3ab819bf76645 0xfd18f83fef6764ff 0x7fd18f83fef6764f

def z138 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x02f007c018009b00 0x802f007c018009b0

def z139 : W := mkw 0x0e044c4cc3e5e5f2 0x20e044c4cc3e5e5f 0xdb94c4c46fe7e7ff 0xedb94c4c46fe7e7f

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x5b14c00000000000 0x05b14c0000000000

def z141 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0x7007c007e0ff00f4 0x07007c007e0ff00f

def z142 : W := mkw 0x0005050600888884 0x3000505060088888 0x37e7070010f89805 0xc37e7070010f8980

def z143 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c468838300 0xadb94c4c46883830

def z144 : W := mkw 0x643eec445ed781a1 0xa643eec445ed781a 0xffbffcc47fff87ff 0xeffbffcc47fff87f

def z145 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7e707c7f0f8fffd 0xfb7e707c7f0f8fff

def z146 : W := mkw 0xd47ff7ff7d81d7a9 0xfd47ff7ff7d81d7a 0xffffffffff87ffff 0xfffffffffff87fff

def z147 : W := mkw 0x0a00080883ececd6 0x00a00080883ececd 0x0080000017fcfcff 0xc0080000017fcfcf

def z148 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5294c4c4688783f4 0x85294c4c4688783f

def z149 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0c7803f81f007f03 0x30c7803f81f007f0

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x8ff007c01800ff0b 0xf8ff007c01800ff0

def z151 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0468033817007801 0x1046803381700780

def z152 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x0000000007606001 0x0000000000760600

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x8760070000000000 0x1876007000000000

def z154 : W := mkw 0x8e005859e3656572 0x08e005859e365657 0xfd18f8ffef6767ff 0x7fd18f8ffef6767f

def z155 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xfffffffff8009b00 0xbfffffffff8009b0

def z156 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7408383fe76460f5 0x17408383fe76460f

def z157 : W := mkw 0x403800001c000001 0x0403800001c00000 0x0f3800001f000003 0xc0f3800001f00000

def z158 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0x008000000000f8c8 0x0008000000000f8c

def z159 : W := mkw 0x2406ec4442d781a0 0xa2406ec4442d781a 0x7007f80460ff00f4 0x07007f80460ff00f

def z160 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xf047ffffe0000000 0x3f047ffffe000000

def z161 : W := mkw 0x100002a000001208 0x4100002a00000120 0x00c007c000009b00 0x000c007c000009b0

def z162 : W := mkw 0xe03ab8113e560001 0x8e03ab8113e56000 0xff3ff83fffff0007 0xfff3ff83fffff000

def z163 : W := mkw 0x003c46e440000001 0x6003c46e44000000 0xdf7cc7fc60000000 0x3df7cc7fc6000000

def z164 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe8838300 0xbffffffffe883830

def z165 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0xfd08383fe00064f8 0x3fd08383fe00064f

def z166 : W := mkw 0x8a47fd57e2642052 0xb8a47fd57e264205 0x7007f807e06400f4 0x07007f807e06400f

def z167 : W := mkw 0x8600585963454532 0x0860058596345453 0x4818f8f86f070732 0x24818f8f86f07073

def z168 : W := mkw 0xfa3abab9bf76765b 0xcfa3abab9bf76765 0xffffffffffffffff 0xffffffffffffffff

def z169 : W := mkw 0x0800000080202040 0x0080000008020204 0xb7e007079060f8cd 0xdb7e007079060f8c

def z170 : W := mkw 0xe23ab8193f564413 0x8e23ab8193f56441 0x4818f8386f070432 0x24818f8386f07043

def z171 : W := mkw 0x543c46ec5d81d7a9 0x6543c46ec5d81d7a 0x8ff807fc7f00fffb 0xf8ff807fc7f00fff

def z172 : W := mkw 0x583d07ae9da8fecd 0x7583d07ae9da8fec 0x8ff807ff9f00ffcb 0xf8ff807ff9f00ffc

def z173 : W := mkw 0xee3efc5dfff7e5f3 0xaee3efc5dfff7e5f 0xffbffcffffffe7ff 0xfffbffcffffffe7f

def z174 : W := mkw 0x04044444408181a0 0x204044444408181a 0x0004c00000830000 0x00004c0000083000

def z175 : W := mkw 0x483d05069ca8a8c5 0x3483d05069ca8a8c 0xbfff07079ff8f8cf 0xdbfff07079ff8f8c

def z176 : W := mkw 0x0a00080082642052 0x00a0008008264205 0x00000000006400f4 0x000000000006400f

def z177 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x80c007078000f8c8 0x180c007078000f8c

def z178 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0xff7ffff81fff0007 0xfff7ffff81fff000

def z179 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x88d807f80f00ff0a 0x388d807f80f00ff0

def z180 : W := mkw 0x007fe7e640000001 0xf007fe7e64000000 0xb777c7c780000000 0x1b777c7c78000000

def z181 : W := mkw 0x180507ae81a8fecc 0x7180507ae81a8fec 0xb7e707ff90f8ffcd 0xfb7e707ff90f8ffc

def z182 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5084c004688787fe 0xc5084c004688787f

def z183 : W := mkw 0x6a3aa8089f766453 0x86a3aa8089f76645 0x7f3ff8001fff64ff 0xc7f3ff8001fff64f

def z184 : W := mkw 0x0004040400808080 0x2000404040080808 0x97e407041080f8cd 0xd97e407041080f8c

def z185 : W := mkw 0x0804040480a8a8c4 0x20804040480a8a8c 0x9384040410f8f8cd 0xc9384040410f8f8c

def z186 : W := mkw 0x68050d069efea8c4 0x368050d069efea8c 0xb7e707079ffff8cf 0xdb7e707079ffff8c

def z187 : W := mkw 0x0001010200080804 0x1000101020008080 0x0063030010181800 0x0006303001018180

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x5004c00000870004 0x05004c0000087000

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c007000000f808 0x180c007000000f80

def z190 : W := mkw 0x403800001c000001 0x0403800001c00000 0x081800000f000002 0x0081800000f00000

def z191 : W := mkw 0x100002a801005608 0x4100002a80100560 0x000000f800000700 0x2000000f80000070

def z192 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x0237c0001fff0007 0xc0237c0001fff000

def z193 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xa4e307079078f8c9 0x1a4e307079078f8c

def z194 : W := mkw 0x0005050600000000 0x3000505060000000 0x0267070000000000 0x0026707000000000

def z195 : W := mkw 0x043ee444408181a1 0xa043ee444408181a 0xffbffcc4688787fe 0xeffbffcc4688787f

def z196 : W := mkw 0x643ee4445c9381a1 0xa643ee4445c9381a 0xdbb7c4c4789f87fe 0xedbb7c4c4789f87f

def z197 : W := mkw 0x607fefe65e560001 0xf607fefe65e56000 0x7f7fffc01fff0007 0xc7f7fffc01fff000

def z198 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0xfd18f8ffe0000000 0x3fd18f8ffe000000

def z199 : W := mkw 0x0004040400808080 0x2000404040080808 0xdb94c404088780ce 0xcdb94c404088780c

def z200 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x0008380007000000 0x0000838000700000

def z201 : W := mkw 0x507fe7e65c001209 0xf507fe7e65c00120 0x02f7c7c018009b00 0x802f7c7c018009b0

def z202 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0xfd08383fe06400f4 0x3fd08383fe06400f

def z203 : W := mkw 0x600008001e560000 0x0600008001e56000 0x5b14c0001fff0007 0xc5b14c0001fff000

def z204 : W := mkw 0xe87ffff7fefea8c5 0xfe87ffff7fefea8c 0xfffffffffffff8cf 0xffffffffffffff8c

def z205 : W := mkw 0x0805050680282844 0x3080505068028284 0xb767070790787801 0x1b76707079078780

def z206 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7ffffff89b0000 0xbff7ffffff89b000

def z207 : W := mkw 0x0801010280282844 0x1080101028028284 0xa7e307039078f809 0xda7e307039078f80

def z208 : W := mkw 0xe47ffff77ed781a1 0xfe47ffff77ed781a 0xffffffffffff87ff 0xfffffffffffff87f

def z209 : W := mkw 0x2002a00000120000 0x82002a0000012000 0x0007c000009b0000 0x00007c000009b000

def z210 : W := mkw 0x8a47fd5fe3646452 0xb8a47fd5fe364645 0xfd0ff83fe76464ff 0x7fd0ff83fe76464f

def z211 : W := mkw 0x403808001e440001 0x0403808001e44000 0x7f3838001f640007 0xc7f3838001f64000

def z212 : W := mkw 0x887ff7f7e0282845 0xf887ff7f7e028284 0xff7ffffff0787801 0x3ff7ffffff078780

def z213 : W := mkw 0x0a00000881206452 0x00a0000088120645 0x00000000000064f8 0x000000000000064f

def z214 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8d68033817007c0b 0x78d68033817007c0

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0xb7e7070010f8f80d 0xdb7e7070010f8f80

def z216 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x781ff8ffe0000000 0x2781ff8ffe000000

def z217 : W := mkw 0x0800000080202040 0x0080000008020204 0x80000007800060c8 0x180000007800060c

def z218 : W := mkw 0x600008001e560000 0x0600008001e56000 0x000000000f070002 0x0000000000f07000

def z219 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0f7803381f007803 0xd0f7803381f00780

def z220 : W := mkw 0x8447f557608181a0 0xb8447f557608181a 0xfb97fcc7e88787fe 0xefb97fcc7e88787f

def z221 : W := mkw 0xe07ffd577e560001 0xbe07ffd577e56000 0x7f3ff807ffff0007 0xc7f3ff807ffff000

def z222 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x5b1cf8000f870006 0xc5b1cf8000f87000

def z223 : W := mkw 0x04044444408181a0 0x204044444408181a 0x00000004600000f0 0x000000004600000f

def z224 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xfff7c7c7f0f8f8cd 0xffff7c7c7f0f8f8c

def z225 : W := mkw 0x683fad069efea8c5 0xb683fad069efea8c 0x7f3ff8079fff00c7 0xc7f3ff8079fff00c

def z226 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8b9804f80f00870a 0xe8b9804f80f00870

def z227 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe08700f4 0x3ff7fffffe08700f

def z228 : W := mkw 0x0005050600888884 0x3000505060088888 0x00c0070000009800 0x000c007000000980

def z229 : W := mkw 0x5c3d47eedda9ffed 0x75c3d47eedda9ffe 0xffffc7ffffffffff 0xfffffc7fffffffff

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000004600400f4 0x050000004600400f

def z231 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdff807fc7f04ffff 0xfdff807fc7f04fff

def z232 : W := mkw 0x603fad061ede8885 0xb603fad061ede888 0x7fffff001fff9807 0xc7fffff001fff980

def z233 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xf767ff07e0000000 0x1f767ff07e000000

def z234 : W := mkw 0x8043b11320000000 0x98043b1132000000 0x2003380380000000 0x0200338038000000

def z235 : W := mkw 0x0004444440000000 0x2000444444000000 0xdb14c4c460000000 0x2db14c4c46000000

def z236 : W := mkw 0x88001011a0202040 0x088001011a020204 0xfd08383fe06060cd 0x7fd08383fe06060c

def z237 : W := mkw 0x0200080803444412 0x0020008080344441 0x0000000007040432 0x0000000000704043

def z238 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff983cffef64e7ff 0xfff983cffef64e7f

def z239 : W := mkw 0x0000000801004400 0x0000000080100440 0x0408003807006001 0x1040800380700600

def z240 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xbfff07f81ff8ff0f 0xfbfff07f81ff8ff0

def z241 : W := mkw 0x847ef6f5608181a1 0xe847ef6f5608181a 0xdb9cfcfc688787fe 0xedb9cfcfc688787f

def z242 : W := mkw 0x8005151720000000 0x3800515172000000 0xff6f3f3fe0000000 0x3ff6f3f3fe000000

def z243 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x2f3b38001f780003 0xc2f3b38001f78000

def z244 : W := mkw 0x543c46e45c8193a9 0x6543c46e45c8193a 0xdbf4c7c478879ffe 0xedbf4c7c478879ff

def z245 : W := mkw 0x807ef6f560000001 0xe807ef6f56000000 0xdb1cfcfc60000000 0x2db1cfcfc6000000

def z246 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0xfffffff81f00ff0b 0xffffffff81f00ff0

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x7f37c00018ff0007 0xc7f37c00018ff000

def z248 : W := mkw 0x04044444408181a0 0x204044444408181a 0xffb7c4c478ff87ff 0xeffb7c4c478ff87f

def z249 : W := mkw 0x04040404008181a0 0x204040404008181a 0x93840404088787fe 0xc93840404088787f

def z250 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x263ff8001ffb0001 0x8263ff8001ffb000

def z251 : W := mkw 0x603eac041ed68081 0xa603eac041ed6808 0xffbffc041fff80cf 0xcffbffc041fff80c

def z252 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe00404fe 0x7ff7fffffe00404f

def z253 : W := mkw 0x8004545560000000 0x2800454556000000 0xff1cfcffe0000000 0x3ff1cfcffe000000

def z254 : W := mkw 0x844557f7608181a0 0x7844557f7608181a 0x80c007ffe00087f8 0x380c007ffe00087f

def z255 : W := mkw 0x8a05151fa1a8ecd6 0x38a05151fa1a8ecd 0x80c0073fe000fcf8 0x380c0073fe000fcf

def z256 : W := mkw 0x607fe7e65c120001 0xf607fe7e65c12000 0x0277c7c0189b0000 0x80277c7c0189b000

def z257 : W := mkw 0x0004444440000000 0x2000444444000000 0xdb14c4c4600404fe 0x6db14c4c4600404f

def z258 : W := mkw 0x04044444408181a0 0x204044444408181a 0x008004c000008300 0x0008004c00000830

def z259 : W := mkw 0x1000000801005608 0x0100000080100560 0x008000000000ff08 0x0008000000000ff0

def z260 : W := mkw 0x443c44445c8181a1 0x2443c44445c8181a 0xdfbcc4c47f8787ff 0xedfbcc4c47f8787f

def z261 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb5c007078060f8cd 0x5b5c007078060f8c

def z262 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x4818f80000000000 0x04818f8000000000

def z263 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0x0000000000f800c4 0x00000000000f800c

def z264 : W := mkw 0x6c3fed46deffa9e5 0xb6c3fed46deffa9e 0xffffffc7ffffffff 0xfffffffc7fffffff

def z265 : W := mkw 0xd07af2f97d005609 0xcd07af2f97d00560 0xcff8fff87f00ff0b 0xfcff8fff87f00ff0

def z266 : W := mkw 0x04054546408989a4 0x304054546408989a 0xdbf7c7c4789f9ffe 0xedbf7c7c4789f9ff

def z267 : W := mkw 0x827fffff63444413 0xf827fffff6344441 0xff7fffffe7040432 0x3ff7fffffe704043

def z268 : W := mkw 0x600000001c120000 0x0600000001c12000 0x00000000189b0000 0x800000000189b000

def z269 : W := mkw 0x683aa8009efea8c5 0x8683aa8009efea8c 0x7fbff8001ffff8cf 0xc7fbff8001ffff8c

def z270 : W := mkw 0x0800000080202040 0x0080000008020204 0xb5000007806060cd 0x5b5000007806060c

def z271 : W := mkw 0x000002a000000000 0x4000002a00000000 0x804007f800000000 0x3804007f80000000

def z272 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0x7f7ffb381fff7807 0xd7f7ffb381fff780

def z273 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x70003807e76464ff 0x470003807e76464f

def z274 : W := mkw 0x8a01191ba36c6c56 0x18a01191ba36c6c5 0xfd6b3b3ff77c7cff 0x7fd6b3b3ff77c7cf

def z275 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x746ffb3fe0000000 0x1746ffb3fe000000

def z276 : W := mkw 0x8447f557608181a0 0xb8447f557608181a 0x7007f807e08700f4 0x07007f807e08700f

def z277 : W := mkw 0xd07bb3bb3d005609 0xdd07bb3bb3d00560 0x246b3b3b97007801 0x1246b3b3b9700780

def z278 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x0ff807c01f009b03 0xc0ff807c01f009b0

def z279 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe00087f8 0x3ffffffffe00087f

def z280 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xfffffffff0989800 0xbfffffffff098980

def z281 : W := mkw 0x003fa50600000001 0xb003fa5060000000 0xff7fff0780000000 0x1ff7fff078000000

def z282 : W := mkw 0x603fa5061c9a8885 0xb603fa5061c9a888 0x02f7c700189b9800 0x802f7c700189b980

def z283 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0x7f3ff8f860000000 0x27f3ff8f86000000

def z284 : W := mkw 0x643eec445ed781a1 0xa643eec445ed781a 0xdb9cfcc46f8787fe 0xedb9cfcc46f8787f

def z285 : W := mkw 0x0005050600000000 0x3000505060000000 0xb767070780000000 0x1b76707078000000

def z286 : W := mkw 0x0001010200000000 0x1000101020000000 0x2463030380000000 0x1246303038000000

def z287 : W := mkw 0x500000081d005608 0x0500000081d00560 0x000000000f000702 0x0000000000f00070

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z289 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x7f3ff80010f80005 0xc7f3ff80010f8000

def z290 : W := mkw 0x583d07a69ca8bacd 0x7583d07a69ca8bac 0xb7f707c798f8fbcd 0xdb7f707c798f8fbc

def z291 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb387040780f880cc 0xcb387040780f880c

def z292 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0xb500003fe06064fd 0x7b500003fe06064f

def z293 : W := mkw 0x04044444408181a0 0x204044444408181a 0xc890c4c4680787fa 0x2c890c4c4680787f

def z294 : W := mkw 0x0800000080202040 0x0080000008020204 0x00000000006060cd 0x400000000006060c

def z295 : W := mkw 0x807ff7ff61004401 0xf807ff7ff6100440 0xff7fffffe700640b 0x7ff7fffffe700640

def z296 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0xb580000790f8f8cd 0xdb580000790f8f8c

def z297 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0f3800f81f000703 0xe0f3800f81f00070

def z298 : W := mkw 0x2000080002560000 0x0200008000256000 0x0000000000ff0004 0x00000000000ff000

def z299 : W := mkw 0x8c7ff7f7e0a9a9e5 0xf8c7ff7f7e0a9a9e 0xfffffffff8ffffff 0xffffffffff8fffff

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000001000f809 0xc008000001000f80

def z301 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7d0ff80007ff0007 0x47d0ff80007ff000

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0xdb14c004688704fe 0xedb14c004688704f

def z303 : W := mkw 0x04000000008181a0 0x004000000008181a 0x0080000008838300 0x8008000000883830

def z304 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x001000c008000300 0x0001000c00800030

def z305 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x089800f81f00ff0b 0xe089800f81f00ff0

def z306 : W := mkw 0x003802a801004401 0x4003802a80100440 0x8f7807f80700640b 0x78f7807f80700640

def z307 : W := mkw 0x583903aa9d287e4d 0x5583903aa9d287e4 0xaffb07fb9f78ff0b 0xfaffb07fb9f78ff0

def z308 : W := mkw 0xe07afaf17e560001 0xce07afaf17e56000 0x7f3ff8f87fff0007 0xe7f3ff8f87fff000

def z309 : W := mkw 0x0000404040000000 0x0000040404000000 0x4810c0c060000000 0x24810c0c06000000

def z310 : W := mkw 0x8200181923444412 0x0820018192344441 0x0008383807000000 0x0000838380700000

def z311 : W := mkw 0x0005050600888884 0x3000505060088888 0x0007000000980000 0x0000700000098000

def z312 : W := mkw 0xda381ab9bf64765b 0x4da381ab9bf64765 0xfd1838ffef6467ff 0x7fd1838ffef6467f

def z313 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x6c7bfbfbe0000000 0x36c7bfbfbe000000

def z314 : W := mkw 0x0801010280282844 0x1080101028028284 0x0040030380007800 0x1004003038000780

def z315 : W := mkw 0xea3ab819bf766453 0x8ea3ab819bf76645 0xfd2b383ff77c64ff 0x7fd2b383ff77c64f

def z316 : W := mkw 0x643aa8001ed781a1 0x8643aa8001ed781a 0x7fbff8001fff87ff 0xc7fbff8001fff87f

def z317 : W := mkw 0x0038000000000001 0x0003800000000000 0x0f38000000000000 0x00f3800000000000

def z318 : W := mkw 0x04044444408181a0 0x204044444408181a 0x8b94c4c00883870a 0xe8b94c4c00883870

def z319 : W := mkw 0x0804040480a0a0c0 0x20804040480a0a0c 0xb784040780e0e0cd 0xdb784040780e0e0c

def z320 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0x7fffffc01fff9b07 0xc7fffffc01fff9b0

def z321 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0008003807000000 0x0000800380700000

def z322 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7727f80010ff0005 0xc7727f80010ff000

def z323 : W := mkw 0xaa02b811a2762052 0x8aa02b811a276205 0x7007f807e0ff00f4 0x07007f807e0ff00f

def z324 : W := mkw 0x8a051d1fa3646452 0x38a051d1fa364645 0xff6f3f3fe76464ff 0x7ff6f3f3fe76464f

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0xdb94c4c00887870e 0xedb94c4c00887870

def z326 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7277ffc7e0000000 0x07277ffc7e000000

def z327 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0x2000380380600000 0x0200038038060000

def z328 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff0f80005 0xfff7ffffff0f8000

def z329 : W := mkw 0x0005454640000000 0x3000545464000000 0xff77c7c7e0000000 0x3ff77c7c7e000000

def z330 : W := mkw 0x0002a00000000000 0x80002a0000000000 0x7007f80000000000 0x07007f8000000000

def z331 : W := mkw 0xd2381ab93f44561b 0x4d2381ab93f44561 0x481838f86f040732 0x2481838f86f04073

def z332 : W := mkw 0x8e045c55e2e5a1f2 0x28e045c55e2e5a1f 0xfb94fcc7e8e787fe 0xefb94fcc7e8e787f

def z333 : W := mkw 0x007ba3a200000001 0xd007ba3a20000000 0x0063030000000000 0x0006303000000000

def z334 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe8870006 0xfff7fffffe887000

def z335 : W := mkw 0x543842e85d015729 0x4543842e85d01572 0x4818c0f86f070732 0x24818c0f86f07073

def z336 : W := mkw 0x0a00080883646452 0x00a0008088364645 0xd9000004676464ff 0x6d9000004676464f

def z337 : W := mkw 0x0400404040010120 0x0040040404001012 0x000000c060000730 0x2000000c06000073

def z338 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe7606001 0x3fd08383fe760600

def z339 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0xf5003807e06460fd 0x5f5003807e06460f

def z340 : W := mkw 0x04004040408181a0 0x004004040408181a 0x4890c0c0688787fe 0xe4890c0c0688787f

def z341 : W := mkw 0x503800081d005609 0x0503800081d00560 0x0fb800001f00ff0b 0xc0fb800001f00ff0

def z342 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xffe70707f0fcfcff 0xfffe70707f0fcfcf

def z343 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7237f80018ff0004 0x87237f80018ff000

def z344 : W := mkw 0x807ab2b120000001 0xc807ab2b12000000 0x0008383800000000 0x0000838380000000

def z345 : W := mkw 0x643eec445ed781a1 0xa643eec445ed781a 0x7f3ff8047fff00f7 0xc7f3ff8047fff00f

def z346 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x26e7070390f8f801 0x926e7070390f8f80

def z347 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e707078000f8c8 0x1b7e707078000f8c

def z348 : W := mkw 0x04044444408181a0 0x204044444408181a 0x8b9004c4680087fa 0xe8b9004c4680087f

def z349 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x8000003fe76464ff 0x78000003fe76464f

def z350 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x8277c7ffe0000000 0x38277c7ffe000000

def z351 : W := mkw 0x600008001e560000 0x0600008001e56000 0x0000000017780001 0x0000000001778000

def z352 : W := mkw 0x0800000881206440 0x0080000088120644 0xbd08003f876064cf 0x7bd08003f876064c

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x3500000000600005 0x4350000000060000

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0x8b1004c000000000 0x28b1004c00000000

def z355 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x7f3ff80008870006 0xc7f3ff8000887000

def z356 : W := mkw 0xaa02b819a3766452 0x8aa02b819a376645 0xfd0ff83fe7ff64ff 0x7fd0ff83fe7ff64f

def z357 : W := mkw 0xd07bb3bb3d005609 0xdd07bb3bb3d00560 0xaffb3ffb9f00ff0b 0xfaffb3ffb9f00ff0

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0x0720000010000001 0xc072000001000000

def z359 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xad08383b8760640b 0x7ad08383b8760640

def z360 : W := mkw 0x0e00080883e5e5f2 0x00e00080883e5e5f 0x008000000fe7e7ff 0xc008000000fe7e7f

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0xdb9004c4680487fe 0xedb9004c4680487f

def z362 : W := mkw 0x0047e54640000000 0xb0047e5464000000 0x0007c00000000000 0x00007c0000000000

def z363 : W := mkw 0xea3ab819bf766453 0x8ea3ab819bf76645 0x7f3ff83b9fff6007 0xd7f3ff83b9fff600

def z364 : W := mkw 0x700008081f565608 0x0700008081f56560 0x008000001fffff0f 0xc008000001fffff0

def z365 : W := mkw 0x0000080002440000 0x0000008000244000 0x0000000007640007 0x4000000000764000

def z366 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xf7e7c707f0fff8fd 0xdf7e7c707f0fff8f

def z367 : W := mkw 0x0000000801004400 0x0000000080100440 0x8f9804f80f00e70b 0xf8f9804f80f00e70

def z368 : W := mkw 0x643eec445ed781a1 0xa643eec445ed781a 0x7fbffcc01fff8307 0xc7fbffcc01fff830

def z369 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x5b37c000189f0006 0xc5b37c000189f000

def z370 : W := mkw 0x007fe7e640000001 0xf007fe7e64000000 0xdb77c7c460000000 0x2db77c7c46000000

def z371 : W := mkw 0x703aa2a01c121209 0xc703aa2a01c12120 0x02f7c7c0189b9b00 0x802f7c7c0189b9b0

def z372 : W := mkw 0x100002a801005608 0x4100002a80100560 0x8dc807f80700ff0b 0x78dc807f80700ff0

def z373 : W := mkw 0x8a4557ffe1206452 0x78a4557ffe120645 0x804007ffe00064f8 0x3804007ffe00064f

def z374 : W := mkw 0x583d07ae9da8fecd 0x7583d07ae9da8fec 0xb7ef073f97f8f8cd 0xdb7ef073f97f8f8c

def z375 : W := mkw 0x8e001819a3e5e5f2 0x08e001819a3e5e5f 0xfd88383fefe7e7ff 0xffd88383fefe7e7f

def z376 : W := mkw 0x603fad061e560001 0xb603fad061e56000 0xff7fff079fff0007 0xdff7fff079fff000

def z377 : W := mkw 0x804557f760000000 0x7804557f76000000 0xfd483fffe0000000 0x3fd483fffe000000

def z378 : W := mkw 0x140446ec4181d7a8 0x6140446ec4181d7a 0x80c007fc6000fff8 0x380c007fc6000fff

def z379 : W := mkw 0x643ae8405e570121 0x8643ae8405e57012 0x4818f8c06f070732 0x24818f8c06f07073

def z380 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xa46b3fffe0000000 0x3a46b3fffe000000

def z381 : W := mkw 0x047fe7e6408181a1 0xf047fe7e6408181a 0xdbf7c7c4688787fe 0xedbf7c7c4688787f

def z382 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x4818f8001fff0007 0xc4818f8001fff000

def z383 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0x24e3030390f8f8cd 0xd24e3030390f8f8c

def z384 : W := mkw 0x503c46ec5d005609 0x6503c46ec5d00560 0xdffcc7fc7f00ff0b 0xfdffcc7fc7f00ff0

def z385 : W := mkw 0x403800001c000001 0x0403800001c00000 0x3f3f00001ff80007 0xc3f3f00001ff8000

def z386 : W := mkw 0x0c044444c0a1a1e0 0x20c044444c0a1a1e 0xff94c4c7e8e7e7ff 0xfff94c4c7e8e7e7f

def z387 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x7d083800076464ff 0x47d083800076464f

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x890000000000040a 0x6890000000000040

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000404fe 0x400000000000404f

def z390 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb0c7070780f8f8cc 0x1b0c7070780f8f8c

def z391 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfb97c4c7e8ff87fe 0xefb97c4c7e8ff87f

def z392 : W := mkw 0x04044444408181a0 0x204044444408181a 0x808004c4688787fe 0xe808004c4688787f

def z393 : W := mkw 0x827afaf963444413 0xc827afaf96344441 0x4818f8f867040432 0x24818f8f86704043

def z394 : W := mkw 0x087fe7e6c0a8a8c5 0xf087fe7e6c0a8a8c 0xb7f7c7c790f8f8cd 0xdb7f7c7c790f8f8c

def z395 : W := mkw 0x683ba9029e7e2845 0x9683ba9029e7e284 0x7f7ffb039fff7807 0xd7f7ffb039fff780

def z396 : W := mkw 0xe07bbbb33e560001 0xde07bbbb33e56000 0x7f7ffb3b9fff0007 0xd7f7ffb3b9fff000

def z397 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x02f007c01f00ff0b 0xc02f007c01f00ff0

def z398 : W := mkw 0x503c06ac1d80d689 0x6503c06ac1d80d68 0x9ffc07fc1f80ffcf 0xf9ffc07fc1f80ffc

def z399 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x4a7ffff860000000 0x24a7ffff86000000

def z400 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x8d080038076464ff 0x78d080038076464f

def z401 : W := mkw 0x70380aa81f565609 0x470380aa81f56560 0x8ff807f81fffff0f 0xf8ff807f81fffff0

def z402 : W := mkw 0x8200181923444412 0x0820018192344441 0xd908383c670404fe 0x6d908383c670404f

def z403 : W := mkw 0xd07ff7ff7d005609 0xfd07ff7ff7d00560 0xff7ffffff7007801 0x3ff7ffffff700780

def z404 : W := mkw 0x884557f7e0a8a8c4 0x7884557f7e0a8a8c 0xb7e707fff0f8f8cd 0xfb7e707fff0f8f8c

def z405 : W := mkw 0x8e7fffffe3e5e5f3 0xf8e7fffffe3e5e5f 0xffffffffefe7e7ff 0xfffffffffefe7e7f

def z406 : W := mkw 0xd03812b93d005609 0x4d03812b93d00560 0xfff83fffff00ff0b 0xffff83fffff00ff0

def z407 : W := mkw 0x683aa8009e762041 0x8683aa8009e76204 0xff3ff8079fff60cf 0xdff3ff8079fff60c

def z408 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xb7e7070798ffffff 0xdb7e7070798fffff

def z409 : W := mkw 0x0005050600000000 0x3000505060000000 0xb7e707079000f809 0xdb7e707079000f80

def z410 : W := mkw 0x887ff7f7e0202041 0xf887ff7f7e020204 0xff7fffffe06060cd 0x7ff7fffffe06060c

def z411 : W := mkw 0xea001819bf766452 0x0ea001819bf76645 0xfd08383fffff64ff 0xffd08383fffff64f

def z412 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x242b380000000000 0x0242b38000000000

def z413 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xffffff001ffff80f 0xdffffff001ffff80

def z414 : W := mkw 0xe07bbbb33e560001 0xde07bbbb33e56000 0x246b3b3b97780001 0x1246b3b3b9778000

def z415 : W := mkw 0x807ffff762440001 0xf807ffff76244000 0xff7fffffe7640007 0x7ff7fffffe764000

def z416 : W := mkw 0x643ee4445c9381a1 0xa643ee4445c9381a 0x02b7c4c0189b8300 0x802b7c4c0189b830

def z417 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x7f7ffb3b80000000 0x17f7ffb3b8000000

def z418 : W := mkw 0x08050d0682eca8c4 0x308050d0682eca8c 0xffef3f0797fcf8cf 0xdffef3f0797fcf8c

def z419 : W := mkw 0x9a001ab9a364765a 0x49a001ab9a364765 0xfdc83fffe764ffff 0x7fdc83fffe764fff

def z420 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0x80c007c7e000fff8 0x380c007c7e000fff

def z421 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x742ff80017ff0005 0x0742ff80017ff000

def z422 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0x7f3ff8f81fff0707 0xe7f3ff8f81fff070

def z423 : W := mkw 0x003802a000000001 0x4003802a00000000 0x081800f800000000 0x2081800f80000000

def z424 : W := mkw 0x8e045c5de3e5e5f2 0x28e045c5de3e5e5f 0xfd883cffe764e7ff 0x7fd883cffe764e7f

def z425 : W := mkw 0x844557f7608181a0 0x7844557f7608181a 0xdbd4c7ffe88787fe 0xfdbd4c7ffe88787f

def z426 : W := mkw 0x783fafae9ffefecd 0xf783fafae9ffefec 0xffffffff9fffffcf 0xfffffffff9fffffc

def z427 : W := mkw 0x904557ff61005608 0x7904557ff6100560 0x80c007ffe000ff08 0x380c007ffe000ff0

def z428 : W := mkw 0x0004040400808080 0x2000404040080808 0x80800404000080c8 0x080800404000080c

def z429 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x2003380000780000 0x0200338000078000

def z430 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x00000007800000c0 0x000000007800000c

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x02e0070010009800 0x802e007001000980

def z432 : W := mkw 0xd07ff7ff7d005609 0xfd07ff7ff7d00560 0xff7fffffef000702 0x3ff7fffffef00070

def z433 : W := mkw 0x8a01191ba36c6c56 0x18a01191ba36c6c5 0x246b3b3b97787801 0x1246b3b3b9778780

def z434 : W := mkw 0x004547e640000000 0x7004547e64000000 0x004007c000000000 0x0004007c00000000

def z435 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x0010c00008030000 0x00010c0000803000

def z436 : W := mkw 0x803812b120000001 0x4803812b12000000 0xff783fffe0000000 0x3ff783fffe000000

def z437 : W := mkw 0x804557f760000000 0x7804557f76000000 0xdb54c7ffe0000000 0x3db54c7ffe000000

def z438 : W := mkw 0x003d07a600000001 0x7003d07a60000000 0xbf7f07ff80000000 0x3bf7f07ff8000000

def z439 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x0023000010180000 0x0002300001018000

def z440 : W := mkw 0x003ee44440000001 0xa003ee4444000000 0xff3ffcc460000000 0x2ff3ffcc46000000

def z441 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbff707c798f8ffcf 0xfbff707c798f8ffc

def z442 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x2408383b876464ff 0x52408383b876464f

def z443 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb767070780f800c4 0x1b767070780f800c

def z444 : W := mkw 0x003802a000000001 0x4003802a00000000 0x8ff807f80800870a 0xf8ff807f80800870

def z445 : W := mkw 0x0801010280282844 0x1080101028028284 0xb5630307907878cd 0x5b5630307907878c

def z446 : W := mkw 0x0004040400808080 0x2000404040080808 0xb7a7040410f880cd 0xcb7a7040410f880c

def z447 : W := mkw 0x0a050d0e83ececd6 0x30a050d0e83ececd 0xb7e7070797fcfcff 0xdb7e7070797fcfcf

def z448 : W := mkw 0x0004040400808080 0x2000404040080808 0x0284040000808000 0x8028404000080800

def z449 : W := mkw 0x04044444408181a0 0x204044444408181a 0x8294c4c4688387f8 0xa8294c4c4688387f

def z450 : W := mkw 0x8a7afaf9e3646453 0xc8a7afaf9e364645 0xfd18f8ffe76464ff 0x7fd18f8ffe76464f

def z451 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb14c4c4608700f4 0x2db14c4c4608700f

def z452 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xfb17fcc7e0000000 0x2fb17fcc7e000000

def z453 : W := mkw 0x0000080002440000 0x0000008000244000 0xfd083804676404ff 0x6fd083804676404f

def z454 : W := mkw 0x0400404040010120 0x0040040404001012 0x4000c00060070030 0x04000c0006007003

def z455 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0x37a7000010f8f8cd 0xc37a7000010f8f8c

def z456 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0x000000001fff64ff 0xc000000001fff64f

def z457 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xfff7c70798fff8cf 0xdfff7c70798fff8c

def z458 : W := mkw 0xea3fbd1fbffeecd7 0xbea3fbd1fbffeecd 0xffffff3ffffffcff 0xfffffff3ffffffcf

def z459 : W := mkw 0x0004444440808080 0x2000444444080808 0xdb94c4c4608080cc 0xedb94c4c4608080c

def z460 : W := mkw 0x203aa80002560001 0x8203aa8000256000 0x7f3ff80000ff0004 0x07f3ff80000ff000

def z461 : W := mkw 0xea3ab811be762053 0x8ea3ab811be76205 0x7f3ff807ffff00f7 0xc7f3ff807ffff00f

def z462 : W := mkw 0x0801010280282844 0x1080101028028284 0x3767030390f87805 0xd3767030390f8780

def z463 : W := mkw 0xe23ab8193f564413 0x8e23ab8193f56441 0x7f3ff8387fff0437 0xe7f3ff8387fff043

def z464 : W := mkw 0x807ff55760000001 0xb807ff5576000000 0x7f3ff807e0000000 0x07f3ff807e000000

def z465 : W := mkw 0x8e055d5fe3ededf6 0x38e055d5fe3ededf 0xffffffffffffffff 0xffffffffffffffff

def z466 : W := mkw 0x887bb3b3a0282845 0xd887bb3b3a028284 0x246b3b3b90787801 0x1246b3b3b9078780

def z467 : W := mkw 0x8a381ab9a3646453 0x48a381ab9a364645 0xff783fffe76464ff 0x7ff783fffe76464f

def z468 : W := mkw 0x0801010280282844 0x1080101028028284 0x2003000380780000 0x0200300038078000

def z469 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0af807f81f009f02 0xa0af807f81f009f0

def z470 : W := mkw 0x403802a01c000001 0x4403802a01c00000 0x8f7807f81f000003 0xf8f7807f81f00000

def z471 : W := mkw 0xd07d57ff7d005609 0x7d07d57ff7d00560 0x8ff807ffff00ff0b 0xf8ff807ffff00ff0

def z472 : W := mkw 0x0800000080a8a8c4 0x00800000080a8a8c 0x87e0070010f8f8cd 0xd87e0070010f8f8c

def z473 : W := mkw 0x0805050680202040 0x3080505068020204 0xb7670707806060cd 0x5b7670707806060c

def z474 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe8070732 0x3ff7fffffe807073

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000010f80005 0xc0000000010f8000

def z476 : W := mkw 0x8a051d17a2eca8d6 0x38a051d17a2eca8d 0xf7e73f07f0fcf8fd 0xdf7e73f07f0fcf8f

def z477 : W := mkw 0x503d07ae1d005609 0x7503d07ae1d00560 0xbfff07ff9f00ff0b 0xfbfff07ff9f00ff0

def z478 : W := mkw 0x503d07ae1d88de8d 0x7503d07ae1d88de8 0x8fff07f81f98ff0b 0xf8fff07f81f98ff0

def z479 : W := mkw 0x140446ec4181d7a8 0x6140446ec4181d7a 0xdbd4c7fc6887fffe 0xfdbd4c7fc6887fff

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x3727000000000000 0x0372700000000000

def z481 : W := mkw 0x8000101120000000 0x0800010112000000 0x70003807e0000000 0x070003807e000000

def z482 : W := mkw 0x5805050e9da8fecc 0x35805050e9da8fec 0xb7e707079ff8ffcf 0xdb7e707079ff8ffc

def z483 : W := mkw 0x8a001819a3ececd6 0x08a001819a3ececd 0xfd88383ff7fcfcff 0xffd88383ff7fcfcf

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d08003800000000 0x38d0800380000000

def z485 : W := mkw 0x043c46e4408181a1 0x6043c46e4408181a 0xdffcc7fc688787fe 0xfdffcc7fc688787f

def z486 : W := mkw 0x2807ad0682fea8c4 0xb2807ad0682fea8c 0x7007f80780ff00c4 0x07007f80780ff00c

def z487 : W := mkw 0x04000000008181a0 0x004000000008181a 0x00000000008700f4 0x000000000008700f

def z488 : W := mkw 0x04044444408181a0 0x204044444408181a 0x938404c4608087fc 0xe938404c4608087f

def z489 : W := mkw 0x0800000080202040 0x0080000008020204 0x2400000380606001 0x1240000038060600

def z490 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x8bf007c018009f0a 0xe8bf007c018009f0

def z491 : W := mkw 0x0400404040010120 0x0040040404001012 0x0010c0c008030300 0x00010c0c00803030

def z492 : W := mkw 0x403800001c000001 0x0403800001c00000 0x8fb804c01f00870b 0xe8fb804c01f00870

def z493 : W := mkw 0x047fe7e6408181a1 0xf047fe7e6408181a 0x02f7c7c008838300 0x802f7c7c00883830

def z494 : W := mkw 0x0004444440000000 0x2000444444000000 0xdb14c4c468870006 0xedb14c4c46887000

def z495 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x0060030010001800 0x0006003001000180

def z496 : W := mkw 0x603aa0001c120001 0x8603aa0001c12000 0x0f3fc0001f9b0003 0xc0f3fc0001f9b000

def z497 : W := mkw 0x0000000000808080 0x0000000000080808 0x00800000008080cc 0xc00800000008080c

def z498 : W := mkw 0x603aa8081f564401 0x8603aa8081f56440 0xff3ff8381fff640f 0xfff3ff8381fff640

def z499 : W := mkw 0x0800000080202040 0x0080000008020204 0xb727000790f860cd 0xdb727000790f860c

def z500 : W := mkw 0x8000101120000000 0x0800010112000000 0x8000003fe0000000 0x38000003fe000000

def z501 : W := mkw 0x804052f160000000 0x4804052f16000000 0x000000f860000000 0x2000000f86000000

def z502 : W := mkw 0x0000080002440000 0x0000008000244000 0x4808380007040002 0x0480838000704000

def z503 : W := mkw 0x86045c5d63c5c5b2 0x286045c5d63c5c5b 0xdb9cfcfc6f8787fe 0xedb9cfcfc6f8787f

def z504 : W := mkw 0x8847f557e0a8a8c4 0xb8847f557e0a8a8c 0xf7e7ff07f0f8f8cd 0xdf7e7ff07f0f8f8c

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0x8380040000008008 0xc838004000000800

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000004600004f8 0x280000004600004f

def z507 : W := mkw 0x8847f557e0a8a8c4 0xb8847f557e0a8a8c 0x7007f807e0f800c4 0x07007f807e0f800c

def z508 : W := mkw 0x04044444408181a0 0x204044444408181a 0x4a94c4c068878732 0xa4a94c4c06887873

def z509 : W := mkw 0x04000000008181a0 0x004000000008181a 0x5b94c000088787fe 0xc5b94c000088787f

def z510 : W := mkw 0x403800001c000001 0x0403800001c00000 0x8ff807001f00f80b 0xd8ff807001f00f80

def z511 : W := mkw 0x0004444440000000 0x2000444444000000 0x5004c00460000000 0x05004c0046000000

def z512 : W := mkw 0x500000081d005608 0x0500000081d00560 0x8d8800381f00ff0b 0xf8d8800381f00ff0

def z513 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0xd900003fe00464fe 0x7d900003fe00464f

def z514 : W := mkw 0x8200181923444412 0x0820018192344441 0x7d08383867640437 0x67d0838386764043

def z515 : W := mkw 0x100002a801005608 0x4100002a80100560 0x87e007f81000ff09 0xf87e007f81000ff0

def z516 : W := mkw 0x8a05151fa1a8ecd6 0x38a05151fa1a8ecd 0xb7e7073ff0f8fcfd 0xfb7e7073ff0f8fcf

def z517 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8000f070002 0x07f3ff8000f07000

def z518 : W := mkw 0x0000080803444400 0x0000008080344440 0xfd0838380764640f 0x7fd0838380764640

def z519 : W := mkw 0x543c46ec5d81d7a9 0x6543c46ec5d81d7a 0x8ffcc7f81f83ff0b 0xf8ffcc7f81f83ff0

def z520 : W := mkw 0x0005050600888884 0x3000505060088888 0x93e70704109898cc 0xc93e70704109898c

def z521 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x80c007f81f00ff0b 0xf80c007f81f00ff0

def z522 : W := mkw 0xe07ffff77e560001 0xfe07ffff77e56000 0xff7ffffff7780001 0x3ff7ffffff778000

def z523 : W := mkw 0x0000000000888884 0x0000000000088888 0x0080000010989800 0x8008000001098980

def z524 : W := mkw 0x0000080002440000 0x0000008000244000 0x7f2f380017fc0007 0xc7f2f380017fc000

def z525 : W := mkw 0x0005050600888884 0x3000505060088888 0x87e707001098f809 0xd87e707001098f80

def z526 : W := mkw 0xd07af2f97d005609 0xcd07af2f97d00560 0x4818f8f86f000702 0x24818f8f86f00070

def z527 : W := mkw 0x0800000080282844 0x0080000008028284 0x0000000010787801 0x0000000001078780

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x808004c000008708 0x2808004c00000870

def z529 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0xb76f3f3f80000000 0x1b76f3f3f8000000

def z530 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8047fff04ff 0xeff3ff8047fff04f

def z531 : W := mkw 0x743eeeec5fd7d7a9 0xe743eeeec5fd7d7a 0xfffffffc7fffffff 0xffffffffc7ffffff

def z532 : W := mkw 0x003aa00000000001 0x8003aa0000000000 0x0237c00000000000 0x00237c0000000000

def z533 : W := mkw 0x403800081d004401 0x0403800081d00440 0x8f3800381f00640b 0xf8f3800381f00640

def z534 : W := mkw 0x583802a89da8fecd 0x4583802a89da8fec 0x8ff807f81ff8ffcf 0xf8ff807f81ff8ffc

def z535 : W := mkw 0x583802a89d207649 0x4583802a89d20764 0xbff807ff9f60ffcf 0xfbff807ff9f60ffc

def z536 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0x246b3b3817787801 0x1246b3b381778780

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x0460030010007801 0x1046003001000780

def z538 : W := mkw 0x8200181923444412 0x0820018192344441 0xcd0838386704643b 0x7cd0838386704643

def z539 : W := mkw 0x0000080002440000 0x0000008000244000 0x7f1cf8000fe70007 0xc7f1cf8000fe7000

def z540 : W := mkw 0x8200101921004412 0x0820010192100441 0x0000003860000430 0x2000000386000043

def z541 : W := mkw 0x8000101120000000 0x0800010112000000 0x4808383860000000 0x2480838386000000

def z542 : W := mkw 0x8a051d1fa3ececd6 0x38a051d1fa3ececd 0xb7ef3f3f97f8f8cd 0xdb7ef3f3f97f8f8c

def z543 : W := mkw 0xda001819bf64765a 0x0da001819bf64765 0xfd88383fff64ffff 0xffd88383fff64fff

def z544 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xffbffcc01fff870f 0xeffbffcc01fff870

def z545 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x84e807f81700ff09 0x384e807f81700ff0

def z546 : W := mkw 0x0005050600000000 0x3000505060000000 0x8040070780000000 0x1804007078000000

def z547 : W := mkw 0x0004444440000000 0x2000444444000000 0x0214c4c000000000 0x00214c4c00000000

def z548 : W := mkw 0x8a3ab819a3646453 0x88a3ab819a364645 0xff3ff83fe76464ff 0x7ff3ff83fe76464f

def z549 : W := mkw 0xde3c5efdffe5f7fb 0x6de3c5efdffe5f7f 0xfffcffffffe7ffff 0xffffcffffffe7fff

def z550 : W := mkw 0x887fb7b7a0a8a8c5 0xf887fb7b7a0a8a8c 0xb7ef3f3f90f8f8cd 0xdb7ef3f3f90f8f8c

def z551 : W := mkw 0x50380aa81f445609 0x450380aa81f44560 0xfff83ff81f64ff0f 0xffff83ff81f64ff0

def z552 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xf000383fe06464fc 0x3f000383fe06464f

def z553 : W := mkw 0x0004040400808080 0x2000404040080808 0x10040004008000c4 0x010040004008000c

def z554 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd904c004608704fe 0x6d904c004608704f

def z555 : W := mkw 0x0a00080883646452 0x00a0008088364645 0xb5000007876464ff 0x5b5000007876464f

def z556 : W := mkw 0x683fad069efea8c5 0xb683fad069efea8c 0xb7ef3f0797f8f8cd 0xdb7ef3f0797f8f8c

def z557 : W := mkw 0x0800080082642040 0x0080008008264204 0xfd083807876460cf 0x5fd083807876460c

def z558 : W := mkw 0x003aa80002440001 0x8003aa8000244000 0x7f3ff80007640007 0x47f3ff8000764000

def z559 : W := mkw 0x0004040400000000 0x2000404040000000 0x9304040400000000 0x0930404040000000

def z560 : W := mkw 0x603808001e560001 0x0603808001e56000 0x0f3800001fff0007 0xc0f3800001fff000

def z561 : W := mkw 0x007fe7e640888885 0xf007fe7e64088888 0x02f7c7c010989800 0x802f7c7c01098980

def z562 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb507000780f860cd 0x5b507000780f860c

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800000060040432 0x2480000006004043

def z564 : W := mkw 0xea7fffffff766453 0xfea7fffffff76645 0xff7fffffffff64ff 0xfff7fffffffff64f

def z565 : W := mkw 0x0000000801004400 0x0000000080100440 0x0808003807000402 0x2080800380700040

def z566 : W := mkw 0x0005050600000000 0x3000505060000000 0xb767070790f80005 0xdb767070790f8000

def z567 : W := mkw 0x680008009efea8c4 0x0680008009efea8c 0x008000001ffff8cf 0xc008000001ffff8c

def z568 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x48083838676464ff 0x648083838676464f

def z569 : W := mkw 0x884557f7e0a8a8c4 0x7884557f7e0a8a8c 0x80c007ffe000f8c8 0x380c007ffe000f8c

def z570 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5814c0c4688707f6 0x25814c0c4688707f

def z571 : W := mkw 0x0000000801004400 0x0000000080100440 0x8000003800006408 0x3800000380000640

def z572 : W := mkw 0x603eec445e560001 0xa603eec445e56000 0xff3ffcc47fff0007 0xeff3ffcc47fff000

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x3007000000f80004 0x03007000000f8000

def z574 : W := mkw 0x403800001c000001 0x0403800001c00000 0x0428000017000001 0x0042800001700000

def z575 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xa408383fe76064f9 0x3a408383fe76064f

def z576 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x06f807f81f00fb01 0x906f807f81f00fb0

def z577 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0xcff8fff81f07ff0b 0xfcff8fff81f07ff0

def z578 : W := mkw 0x8a7bbbbba3646453 0xd8a7bbbbba364645 0x246b3b3b87606001 0x1246b3b3b8760600

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x0227000010980000 0x8022700001098000

def z580 : W := mkw 0x847af2f160010121 0xc847af2f16001012 0x4818f8f868070732 0x24818f8f86807073

def z581 : W := mkw 0x5a380aa89f64765b 0x45a380aa89f64765 0x8ff807f81f64ffff 0xf8ff807f81f64fff

def z582 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c4600087f8 0x2db94c4c4600087f

def z583 : W := mkw 0x683fa5069cbaa8c5 0xb683fa5069cbaa8c 0xb7f7c70798fbf8cd 0xdb7f7c70798fbf8c

def z584 : W := mkw 0x8200181122440012 0x0820018112244001 0x4000380060040030 0x0400038006004003

def z585 : W := mkw 0xe07ffff77e560001 0xfe07ffff77e56000 0xff7fffffef070002 0x3ff7fffffef07000

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b10000008000002 0xc0b1000000800000

def z587 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x32e7070790f898c4 0x832e7070790f898c

def z588 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd384c404608780fc 0xcd384c404608780f

def z589 : W := mkw 0xda3d1fbfbfecfedf 0x7da3d1fbfbfecfed 0xffff3ffffffcffff 0xfffff3ffffffcfff

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x0214c00008830000 0x80214c0000883000

def z591 : W := mkw 0x8a045c5de3646452 0x28a045c5de364645 0xff1cfcffe76464ff 0x7ff1cfcffe76464f

def z592 : W := mkw 0x003802a000000001 0x4003802a00000000 0x027007c000000000 0x0027007c00000000

def z593 : W := mkw 0xca381819bf646453 0x0ca381819bf64645 0xff38383fff6464ff 0xfff38383fff6464f

def z594 : W := mkw 0xda381ab9bf64765b 0x4da381ab9bf64765 0x24683b3b97607801 0x124683b3b9760780

def z595 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7b17f80008ff0006 0xc7b17f80008ff000

def z596 : W := mkw 0x0000000801004400 0x0000000080100440 0xdd08003c670464ff 0x7dd08003c670464f

def z597 : W := mkw 0x0005050600808080 0x3000505060080808 0xb7e70707808080cc 0xdb7e70707808080c

def z598 : W := mkw 0x503d07a61c889a8d 0x7503d07a61c889a8 0x02f707c018989b00 0x802f707c018989b0

def z599 : W := mkw 0x887ff7f7e0a8a8c5 0xf887ff7f7e0a8a8c 0xffffffffe000f8c8 0x3ffffffffe000f8c

def z600 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x372f380017f80005 0xc372f380017f8000

def z601 : W := mkw 0x8a7bbbbba3646453 0xd8a7bbbbba364645 0xfd6b3b3fe76464ff 0x7fd6b3b3fe76464f

def z602 : W := mkw 0x543842e85d015729 0x4543842e85d01572 0xcff8c7f87f07ff3b 0xfcff8c7f87f07ff3

def z603 : W := mkw 0x8a001011a0202052 0x08a001011a020205 0x00000007e00000f0 0x000000007e00000f

def z604 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x8ff807f818009b00 0xb8ff807f818009b0

def z605 : W := mkw 0x503802a01c001209 0x4503802a01c00120 0x87f007c01800fb09 0xd87f007c01800fb0

def z606 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd98004c4600487fe 0x6d98004c4600487f

def z607 : W := mkw 0x8a7ff7ffe1206453 0xf8a7ff7ffe120645 0xff7fffffe00064f8 0x3ff7fffffe00064f

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0x081000c008000702 0x2081000c00800070

def z609 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd084c4c4608787fc 0x2d084c4c4608787f

def z610 : W := mkw 0xf07fffff7f565609 0xff07fffff7f56560 0xffffffffffffff0f 0xfffffffffffffff0

def z611 : W := mkw 0x583903aa9d287e4d 0x5583903aa9d287e4 0x246b033b97787801 0x1246b033b9778780

def z612 : W := mkw 0x600008001e560000 0x0600008001e56000 0x372700001fff0007 0xc372700001fff000

def z613 : W := mkw 0x8000181122440000 0x0800018112244000 0xfd08383fe7640007 0x7fd08383fe764000

def z614 : W := mkw 0x640008001ed781a0 0x0640008001ed781a 0x008000001fff87ff 0xc008000001fff87f

def z615 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x87e007079000f8c9 0xd87e007079000f8c

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000008870006 0xc000000000887000

def z617 : W := mkw 0x887ff7f7e0a8a8c5 0xf887ff7f7e0a8a8c 0xff7fffffe0f800c4 0x3ff7fffffe0f800c

def z618 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x242b38001fff0007 0xc242b38001fff000

def z619 : W := mkw 0x003802a000000001 0x4003802a00000000 0x8ff807f81000f809 0xf8ff807f81000f80

def z620 : W := mkw 0x0404444440010120 0x2040444444001012 0xdb14c4c468070732 0x2db14c4c46807073

def z621 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x6c08383be7646433 0x36c08383be764643

def z622 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x87e807381700f809 0xd87e807381700f80

def z623 : W := mkw 0x5404444c5d81d7a8 0x25404444c5d81d7a 0xdb94c4c47f87ffff 0xedb94c4c47f87fff

def z624 : W := mkw 0x0004444440000000 0x2000444444000000 0xdb94c4c46800870a 0xedb94c4c46800870

def z625 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x3087000790f8f8cd 0xc3087000790f8f8c

def z626 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8f7807f817007801 0x38f7807f81700780

def z627 : W := mkw 0x04044444408181a0 0x204044444408181a 0x9394c4c4088383cc 0xc9394c4c4088383c

def z628 : W := mkw 0x400000001c000000 0x0400000001c00000 0x000000001f000003 0xc000000001f00000

def z629 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0x8d08003fe70064fb 0x78d08003fe70064f

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0x1304000000800004 0xc130400000080000

def z631 : W := mkw 0x8a7fffffe3ececd7 0xf8a7fffffe3ececd 0xfffffffff7fcfcff 0xffffffffff7fcfcf

def z632 : W := mkw 0x0c044444c0a9a9e4 0x20c044444c0a9a9e 0xdb94c4c478ffffff 0xedb94c4c478fffff

def z633 : W := mkw 0x9a0012b9a120765a 0x49a0012b9a120765 0x80c007ffe000fff8 0x380c007ffe000fff

def z634 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff80017780001 0x07f3ff8001778000

def z635 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x781ff8000fff0006 0x0781ff8000fff000

def z636 : W := mkw 0x8e04545de1a1e5f2 0x28e04545de1a1e5f 0x808004ffe000e7f8 0x3808004ffe000e7f

def z637 : W := mkw 0x103802a801005609 0x4103802a80100560 0x8ff807f80000ff08 0x38ff807f80000ff0

def z638 : W := mkw 0x543c46e45c8193a9 0x6543c46e45c8193a 0x02f4c7c018839b00 0x802f4c7c018839b0

def z639 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x267ffffb80000000 0x1267ffffb8000000

def z640 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x80c0070790f8f8cd 0xd80c0070790f8f8c

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x029004c008008300 0x8029004c00800830

def z642 : W := mkw 0x0400404040010120 0x0040040404001012 0xcb90c4c06807873a 0xecb90c4c06807873

def z643 : W := mkw 0x003aa2a000000001 0xc003aa2a00000000 0xff7ffff800000000 0x3ff7ffff80000000

def z644 : W := mkw 0x04000000008181a0 0x004000000008181a 0xd9800004688787fe 0xed9800004688787f

def z645 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x6c3bf8001f7f0003 0x06c3bf8001f7f000

def z646 : W := mkw 0x083fa50680a8a8c5 0xb083fa50680a8a8c 0xffffff0790f8f8cd 0xdffffff0790f8f8c

def z647 : W := mkw 0x8000101921004400 0x0800010192100440 0xfd08383fe700640b 0x7fd08383fe700640

def z648 : W := mkw 0x8a051d1fa3ececd6 0x38a051d1fa3ececd 0xfdc83f3fe764fcff 0x7fdc83f3fe764fcf

def z649 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0x7d083807e76400f7 0x47d083807e76400f

def z650 : W := mkw 0x04044c4442c581a0 0x204044c4442c581a 0xff9cfcc46fe787ff 0xeff9cfcc46fe787f

def z651 : W := mkw 0x403800001c000001 0x0403800001c00000 0x5f3cc0001f870007 0xc5f3cc0001f87000

def z652 : W := mkw 0x500000081d005608 0x0500000081d00560 0x87e007001f00ff0b 0xd87e007001f00ff0

def z653 : W := mkw 0x180507ae81a8fecc 0x7180507ae81a8fec 0x80c007ff8000ffc8 0x380c007ff8000ffc

def z654 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5b14c004688700f6 0xc5b14c004688700f

def z655 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8d1800f80f00670b 0x78d1800f80f00670

def z656 : W := mkw 0x007fe7e640000001 0xf007fe7e64000000 0x8f7fc7f800000000 0x38f7fc7f80000000

def z657 : W := mkw 0x083d07a680a8a8c5 0x7083d07a680a8a8c 0xbfff07ff90f8f8cd 0xfbfff07ff90f8f8c

def z658 : W := mkw 0xda3812b9bd20765b 0x4da3812b9bd20765 0x8ff807ffff00fffb 0xf8ff807ffff00fff

def z659 : W := mkw 0x703aaaa81f565609 0xc703aaaa81f56560 0xaffb3ff81f78ff0b 0xfaffb3ff81f78ff0

def z660 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x3727000790f800c5 0xc3727000790f800c

def z661 : W := mkw 0x04000000008181a0 0x004000000008181a 0x8b9004c0088787fe 0xe8b9004c0088787f

def z662 : W := mkw 0xe07afaf17e560001 0xce07afaf17e56000 0x4818f8f86f070002 0x24818f8f86f07000

def z663 : W := mkw 0x8042f05160000000 0x88042f0516000000 0x4000f80060000000 0x04000f8006000000

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x0d08000007000003 0x40d0800000700000

def z665 : W := mkw 0x0004444440000000 0x2000444444000000 0x800004c460000000 0x2800004c46000000

def z666 : W := mkw 0x8a7fffffe3646453 0xf8a7fffffe364645 0xff7fffffe7606001 0x3ff7fffffe760600

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x91000004000000cc 0x491000004000000c

def z668 : W := mkw 0x543802a81d81d7a9 0x4543802a81d81d7a 0x8ff807f81f87ffff 0xf8ff807f81f87fff

def z669 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5b94c4c008878306 0xc5b94c4c00887830

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x8500000000006009 0x5850000000000600

def z671 : W := mkw 0xda7fffffff64765b 0xfda7fffffff64765 0xffffffffff64ffff 0xfffffffffff64fff

def z672 : W := mkw 0x703aa8081f565609 0x8703aa8081f56560 0x7fbff8001fffff0f 0xc7fbff8001fffff0

def z673 : W := mkw 0x600008001e560000 0x0600008001e56000 0x7d0838001fff0007 0xc7d0838001fff000

def z674 : W := mkw 0x04000000008181a0 0x004000000008181a 0x00800000000087f8 0x000800000000087f

def z675 : W := mkw 0x0004040400808080 0x2000404040080808 0xdb840404608484fe 0xedb840404608484f

def z676 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xb508383f876060cd 0x5b508383f876060c

def z677 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x4000f80000070000 0x04000f8000007000

def z678 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0xf9003807e06404fe 0x6f9003807e06404f

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x4810c00008070002 0x04810c0000807000

def z680 : W := mkw 0x580000089da8fecc 0x0580000089da8fec 0x008000001ff8ffcf 0xc008000001ff8ffc

def z681 : W := mkw 0xd2381ab93f44561b 0x4d2381ab93f44561 0xcff83ff87f04ff3b 0xfcff83ff87f04ff3

def z682 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0xcf78fff860000000 0x3cf78fff86000000

def z683 : W := mkw 0x8a051d17a2eca8d6 0x38a051d17a2eca8d 0x70073807e0fc00f4 0x070073807e0fc00f

def z684 : W := mkw 0x0404444c4181c5a0 0x20404444c4181c5a 0xdf9cc4fc6f87e7ff 0xfdf9cc4fc6f87e7f

def z685 : W := mkw 0x0800000080202040 0x0080000008020204 0x30000007806000c4 0x030000007806000c

def z686 : W := mkw 0x643ae8405e570121 0x8643ae8405e57012 0x7f3ff8c07fff0737 0xe7f3ff8c07fff073

def z687 : W := mkw 0x507fe7ee5d005609 0xf507fe7ee5d00560 0x8fffc7f81f00ff0b 0xf8fffc7f81f00ff0

def z688 : W := mkw 0x683ba9029e7e2845 0x9683ba9029e7e284 0x246b3b0397787801 0x1246b3b039778780

def z689 : W := mkw 0x0000080002440000 0x0000008000244000 0x2408380007600001 0x0240838000760000

def z690 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x82e707079098f8c8 0x982e707079098f8c

def z691 : W := mkw 0x543c46ec5d81d7a9 0x6543c46ec5d81d7a 0xdb9cc4fc6f8787fe 0xedb9cc4fc6f8787f

def z692 : W := mkw 0x2406ec4442d781a0 0xa2406ec4442d781a 0xfb97fcc468ff87fe 0xefb97fcc468ff87f

def z693 : W := mkw 0x007ae2e040000001 0xc007ae2e04000000 0x0010c0c000000000 0x00010c0c00000000

def z694 : W := mkw 0x907ff7ff61005609 0xf907ff7ff6100560 0xffffffffe000ff08 0x3ffffffffe000ff0

def z695 : W := mkw 0xa047fd5762560000 0xba047fd576256000 0x7007f807e0ff0004 0x07007f807e0ff000

def z696 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7d08383b87646007 0x57d08383b8764600

def z697 : W := mkw 0x0805050e81a8ecc4 0x30805050e81a8ecc 0xbfef073f97f8fccf 0xfbfef073f97f8fcc

def z698 : W := mkw 0x0400000000010120 0x0040000000001012 0x0000000008070732 0x0000000000807073

def z699 : W := mkw 0xda381ab9bf64765b 0x4da381ab9bf64765 0xfd683b3ff7647cff 0x7fd683b3ff7647cf

def z700 : W := mkw 0x0005050600000000 0x3000505060000000 0x3007000780000000 0x0300700078000000

def z701 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xdbd4c7c7e887fffe 0xfdbd4c7c7e887fff

def z702 : W := mkw 0x8200181923444412 0x0820018192344441 0xfd08383fe7040432 0x3fd08383fe704043

def z703 : W := mkw 0x64044c445ed781a0 0x264044c445ed781a 0xdb94c4c47fff87ff 0xedb94c4c47fff87f

def z704 : W := mkw 0x0004040400808080 0x2000404040080808 0x9b9404c4088087ce 0xe9b9404c4088087c

def z705 : W := mkw 0x8a051d1fa3ececd6 0x38a051d1fa3ececd 0xfd0f383fe7fc64ff 0x7fd0f383fe7fc64f

def z706 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8f7807f80f000702 0x38f7807f80f00070

def z707 : W := mkw 0x847bb3b3208181a1 0xd847bb3b3208181a 0x24eb3b3b888787fe 0xd24eb3b3b888787f

def z708 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xfff83ff81f00ff0b 0xffff83ff81f00ff0

def z709 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e7070790f8f801 0x9b7e7070790f8f80

def z710 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xffef3f0790f8f8cd 0xdffef3f0790f8f8c

def z711 : W := mkw 0x04054546408989a4 0x304054546408989a 0xdbd4c7c468879ffe 0xedbd4c7c468879ff

def z712 : W := mkw 0x6e044c4cdff7e5f2 0x26e044c4cdff7e5f 0xdb94c4c47fffe7ff 0xedb94c4c47fffe7f

def z713 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8007fff0437 0xe7f3ff8007fff043

def z714 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0x24e303039078f8c9 0x124e303039078f8c

def z715 : W := mkw 0x04054546408181a0 0x304054546408181a 0xdbf7c7c4688787fe 0xedbf7c7c4688787f

def z716 : W := mkw 0x04044444408181a0 0x204044444408181a 0xff9cfcc4688787fe 0xeff9cfcc4688787f

def z717 : W := mkw 0x04044444408181a0 0x204044444408181a 0x8294c4c4688787fe 0xe8294c4c4688787f

def z718 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe8030300 0x3ff7fffffe803030

def z719 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbfe7070790f8fccf 0xfbfe7070790f8fcc

def z720 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7007f80017ff0005 0x07007f80017ff000

def z721 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0x2463030390f878c5 0x12463030390f878c

def z722 : W := mkw 0x0a7fefeec3646453 0xf0a7fefeec364645 0x0277c7c0076464ff 0x40277c7c0076464f

def z723 : W := mkw 0x0000080002440000 0x0000008000244000 0x7f3ff8001fff0007 0xc7f3ff8001fff000

def z724 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x50000004676464ff 0x450000004676464f

def z725 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x746ffb3b80000000 0x1746ffb3b8000000

def z726 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7f7c7c798ffffff 0xdb7f7c7c798fffff

def z727 : W := mkw 0x0a00080883e4e4d2 0x00a00080883e4e4d 0x0080000007e4e4ff 0xc0080000007e4e4f

def z728 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x8008383fe70064f8 0x38008383fe70064f

def z729 : W := mkw 0x844557f7608181a0 0x7844557f7608181a 0xfdc83fffe00487fe 0x7fdc83fffe00487f

def z730 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd1838ffef6467ff 0x7fd1838ffef6467f

def z731 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0x781ff8ffe88707f6 0x2781ff8ffe88707f

def z732 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe00004f8 0x3fd08383fe00004f

def z733 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xfd6b3b3fe00404fe 0x7fd6b3b3fe00404f

def z734 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7d0ff8001fff0007 0xc7d0ff8001fff000

def z735 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000076064f9 0x000000000076064f

def z736 : W := mkw 0x3002aaa803565608 0xc3002aaa80356560 0xf0c7fff800ffff0c 0x3f0c7fff800ffff0

def z737 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe0008708 0x3ffffffffe000870

def z738 : W := mkw 0xd047f55f7d005608 0xbd047f55f7d00560 0x7087f807ff00ff0b 0xc7087f807ff00ff0

def z739 : W := mkw 0x547fe7e65c8193a9 0xf547fe7e65c8193a 0x02f7c7c018839b00 0x802f7c7c018839b0

def z740 : W := mkw 0x5a0008089fecfede 0x05a0008089fecfed 0x008000001ffcffff 0xc008000001ffcfff

def z741 : W := mkw 0x0c014142c0292964 0x10c014142c029296 0x6c73c3c3f87f7f33 0x36c73c3c3f87f7f3

def z742 : W := mkw 0x8004545560000000 0x2800454556000000 0xfd0cf83fe0000000 0x3fd0cf83fe000000

def z743 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0xb5e3030790f8f8cd 0xdb5e3030790f8f8c

def z744 : W := mkw 0x683fad069efea8c5 0xb683fad069efea8c 0xc8d8ff078f07f8ca 0x1c8d8ff078f07f8c

def z745 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7008383fe76400f4 0x07008383fe76400f

def z746 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe0040006 0x7fd08383fe004000

def z747 : W := mkw 0x04044444408989a4 0x204044444408989a 0xdb94c4c4789f9ffe 0xedb94c4c4789f9ff

def z748 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7237f8001fff0007 0xc7237f8001fff000

def z749 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe0000730 0x3ff7fffffe000073

def z750 : W := mkw 0x0a040c0c83ececd6 0x20a040c0c83ececd 0xdb84040477fcfcff 0xedb84040477fcfcf

def z751 : W := mkw 0x8e055d57e2eda9f6 0x38e055d57e2eda9f 0x7007f807e0ff00f4 0x07007f807e0ff00f

def z752 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x246ffb3b80000000 0x1246ffb3b8000000

def z753 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x6c7bfb3b80000000 0x16c7bfb3b8000000

def z754 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xfffffffff0f89805 0xffffffffff0f8980

def z755 : W := mkw 0x647fe7e65c9381a1 0xf647fe7e65c9381a 0x02f7c7c0189b8300 0x802f7c7c0189b830

def z756 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0xc818f8ffe0000000 0x3c818f8ffe000000

def z757 : W := mkw 0x8e045c5de3e5e5f2 0x28e045c5de3e5e5f 0x269cfcfb8fe3e301 0x9269cfcfb8fe3e30

def z758 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfff83fffff64ffff 0xffff83fffff64fff

def z759 : W := mkw 0xd47ff7f77c8193a9 0xfd47ff7f77c8193a 0xfffffffff8839b00 0xbfffffffff8839b0

def z760 : W := mkw 0x8000181122440000 0x0800018112244000 0xfd08383fe76404ff 0x7fd08383fe76404f

def z761 : W := mkw 0xf07afaf97f565609 0xcf07afaf97f56560 0x4818f8f86f070702 0x24818f8f86f07070

def z762 : W := mkw 0x8a001819a36c6c56 0x08a001819a36c6c5 0xfd08383ff77c7cff 0x7fd08383ff77c7cf

def z763 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8047fff00f7 0xc7f3ff8047fff00f

def z764 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdbf4c7c478879ffe 0xedbf4c7c478879ff

def z765 : W := mkw 0x807ab2b120000001 0xc807ab2b12000000 0xfd08383fe0000000 0x3fd08383fe000000

def z766 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e7070790fcfcff 0xdb7e7070790fcfcf

def z767 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfffffffff0f8f80d 0xffffffffff0f8f80

def z768 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xa7e7070390f8f809 0xda7e7070390f8f80

def z769 : W := mkw 0x04044444408181a0 0x204044444408181a 0xfb97c4c468ff87fe 0xefb97c4c468ff87f

def z770 : W := mkw 0x780008089ffefecc 0x0780008089ffefec 0x008000001fffffcf 0xc008000001fffffc

def z771 : W := mkw 0x807ef6f560000001 0xe807ef6f56000000 0xff1cfcffe0000000 0x3ff1cfcffe000000

def z772 : W := mkw 0x04044444408181a0 0x204044444408181a 0xca94c4c4688787fa 0xaca94c4c4688787f

def z773 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c7c7f0f8fffd 0xffff7c7c7f0f8fff

def z774 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0xff78ffffe0000000 0x3ff78ffffe000000

def z775 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe88780ce 0xfffffffffe88780c

def z776 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xfff7c7c7f8f8ffcf 0xffff7c7c7f8f8ffc

def z777 : W := mkw 0x8200181923444412 0x0820018192344441 0xfd08383fe70404fe 0x7fd08383fe70404f

def z778 : W := mkw 0x8000505160000000 0x0800050516000000 0xfd18f8ffe0000000 0x3fd18f8ffe000000

def z779 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xfb57ffffe0000000 0x3fb57ffffe000000

def z780 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7fbffcc01fff8307 0xc7fbffcc01fff830

def z781 : W := mkw 0x0801010280282844 0x1080101028028284 0xb7e307079078f8cd 0xdb7e307079078f8c

def z782 : W := mkw 0x8043b11320000000 0x98043b1132000000 0xfd0b383fe0000000 0x3fd0b383fe000000

def z783 : W := mkw 0x0805050680282844 0x3080505068028284 0xa463070790787801 0x1a46307079078780

def z784 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xb77fffff80000000 0x1b77fffff8000000

def z785 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0x00000000177c64ff 0x400000000177c64f

def z786 : W := mkw 0x8000101120000000 0x0800010112000000 0xff2f383fe0000000 0x3ff2f383fe000000

def z787 : W := mkw 0x100002a801005608 0x4100002a80100560 0x8fe807f81700ff0b 0xf8fe807f81700ff0

def z788 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000070464fa 0x000000000070464f

def z789 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0xfffffff81ff8ff0f 0xffffffff81ff8ff0

def z790 : W := mkw 0x803812b120000001 0x4803812b12000000 0xaf783ffb80000000 0x3af783ffb8000000

def z791 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xbff707c7f8f8ffff 0xfbff707c7f8f8fff

def z792 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xff1ffcffe0000000 0x3ff1ffcffe000000

def z793 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xdbdcffffe88787fe 0xfdbdcffffe88787f

def z794 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8047fff0007 0xeff3ff8047fff000

def z795 : W := mkw 0x643eec445ed781a1 0xa643eec445ed781a 0xa4ab3cc4777887f9 0x2a4ab3cc4777887f

def z796 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x8bd007f81f00ff0b 0xf8bd007f81f00ff0

def z797 : W := mkw 0x803fb51720000001 0xb803fb5172000000 0xff7fff3fe0000000 0x3ff7fff3fe000000

def z798 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff8ff0007 0xfff7ffffff8ff000

def z799 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0x7f3ff83b80000000 0x17f3ff83b8000000

def z800 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8fff07f81f98ff0b 0xf8fff07f81f98ff0

def z801 : W := mkw 0xf07ff7f77c121209 0xff07ff7f77c12120 0xfffffffff89b9b00 0xbfffffffff89b9b0

def z802 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xffffc7f81fffff0f 0xfffffc7f81fffff0

def z803 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xbff7c7c798fbffcf 0xfbff7c7c798fbffc

def z804 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x80c007f81700ff09 0x380c007f81700ff0

def z805 : W := mkw 0x84045455608181a0 0x284045455608181a 0xff9cfcffe8838300 0xbff9cfcffe883830

def z806 : W := mkw 0x0a00080883ececd6 0x00a00080883ececd 0x0000000007fc64ff 0x40000000007fc64f

def z807 : W := mkw 0xe07ff7f77c9a8885 0xfe07ff7f77c9a888 0xfffffffff89b9800 0xbfffffffff89b980

def z808 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xffbffc001fff800f 0xcffbffc001fff800

def z809 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7d2ff80017ff0007 0x47d2ff80017ff000

def z810 : W := mkw 0x8000101120000000 0x0800010112000000 0x7808383fe0000000 0x27808383fe000000

def z811 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7ffffff8000000 0xbff7ffffff800000

def z812 : W := mkw 0x8002b01120000000 0x88002b0112000000 0xfd0ff83fe0000000 0x3fd0ff83fe000000

def z813 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c7c7f0fff8fd 0xffff7c7c7f0fff8f

def z814 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xfff7c7c7f8fff8cf 0xffff7c7c7f8fff8c

def z815 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe80787fa 0x3ffffffffe80787f

def z816 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe8000002 0xfff7fffffe800000

def z817 : W := mkw 0x04044444408181a0 0x204044444408181a 0xff94c4c7e88787fe 0xfff94c4c7e88787f

def z818 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe7000003 0x7fd08383fe700000

def z819 : W := mkw 0xea3ab019bd326453 0x8ea3ab019bd32645 0x8237c03ff89b64f8 0xb8237c03ff89b64f

def z820 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xd908383fe70464fe 0x7d908383fe70464f

def z821 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xaffb07f81f78ff0b 0xfaffb07f81f78ff0

def z822 : W := mkw 0x8005555760000000 0x3800555576000000 0xff7fffffe0000000 0x3ff7fffffe000000

def z823 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0x8ff8c7f81f03ff0b 0xf8ff8c7f81f03ff0

def z824 : W := mkw 0x800012b120000000 0x4800012b12000000 0xfd483fffe0000000 0x3fd483fffe000000

def z825 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x82e7070790f8f8cd 0xd82e7070790f8f8c

def z826 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xb508383fe76064fd 0x7b508383fe76064f

def z827 : W := mkw 0x847ef6f5608181a1 0xe847ef6f5608181a 0xff9cfcffe88787fe 0xfff9cfcffe88787f

def z828 : W := mkw 0x0801010280282844 0x1080101028028284 0x3767030390787801 0x1376703039078780

def z829 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe76064f9 0x3fd08383fe76064f

def z830 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7f2ff80017ff0007 0xc7f2ff80017ff000

def z831 : W := mkw 0x04044444408181a0 0x204044444408181a 0x4810c0c4680707f2 0x24810c0c4680707f

def z832 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x87e007001764fcff 0xd87e007001764fcf

def z833 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe08787fc 0x3ffffffffe08787f

def z834 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xcf78ffffe0000000 0x3cf78ffffe000000

def z835 : W := mkw 0x0a050d0e83ececd6 0x30a050d0e83ececd 0x02e7070017fcfcff 0xc02e7070017fcfcf

def z836 : W := mkw 0x0400404040010120 0x0040040404001012 0xc810c0c4680707fa 0x2c810c0c4680707f

def z837 : W := mkw 0x100002a801005608 0x4100002a80100560 0x80c007f80700ff0b 0x780c007f80700ff0

def z838 : W := mkw 0x84045455608181a0 0x284045455608181a 0xfd0cf83fe08700f4 0x3fd0cf83fe08700f

def z839 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xfff7c70790f8f8cd 0xdfff7c70790f8f8c

def z840 : W := mkw 0x8045555760000000 0x3804555576000000 0xfd08383fe0000000 0x3fd08383fe000000

def z841 : W := mkw 0x887af2f1e0a8a8c5 0xc887af2f1e0a8a8c 0x4898f8f870f8f8cd 0xe4898f8f870f8f8c

def z842 : W := mkw 0xe0455ff77e560000 0x7e0455ff77e56000 0x804007ffffff0007 0xf804007ffffff000

def z843 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x0000000017fc64ff 0xc0000000017fc64f

def z844 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x0000000007646433 0x0000000000764643

def z845 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x376f3b3b80000000 0x1376f3b3b8000000

def z846 : W := mkw 0x82051d1f23cccc96 0x382051d1f23cccc9 0x4aef3f38779c9c32 0xa4aef3f38779c9c3

def z847 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb2e7070790f8f8cc 0x9b2e7070790f8f8c

def z848 : W := mkw 0x0e004848c3656572 0x00e004848c365657 0x4810c0c06f6767ff 0x64810c0c06f6767f

def z849 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xf7e7c7c7f0fffffd 0xff7e7c7c7f0fffff

def z850 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfffffffff800ff0b 0xffffffffff800ff0

def z851 : W := mkw 0x0e00080883656572 0x00e0008088365657 0x000000000f6767ff 0x4000000000f6767f

def z852 : W := mkw 0x583d07ae9da8fecd 0x7583d07ae9da8fec 0x381f00ff8ff807c6 0x2381f00ff8ff807c

def z853 : W := mkw 0x0000000801004400 0x0000000080100440 0x8ff807f81f00ff0b 0xf8ff807f81f00ff0

def z854 : W := mkw 0x8000101120000000 0x0800010112000000 0xff183cffe0000000 0x3ff183cffe000000

def z855 : W := mkw 0x203aa80002560001 0x8203aa8000256000 0x7f3ff80007ff0007 0x47f3ff80007ff000

def z856 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfd6b3fffe0000000 0x3fd6b3fffe000000

def z857 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x5b14c0000fe764ff 0xc5b14c0000fe764f

def z858 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x34e7030790f8f8cd 0xd34e7030790f8f8c

def z859 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7b17f8001fff0007 0xc7b17f8001fff000

def z860 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7e707c7f8ffffff 0xfb7e707c7f8fffff

def z861 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000076404f6 0x000000000076404f

def z862 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xffe70707f0f8f8cd 0xfffe70707f0f8f8c

def z863 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7fffffff870007 0xfff7fffffff87000

def z864 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xffffffffff00870b 0xfffffffffff00870

def z865 : W := mkw 0x804557f760000000 0x7804557f76000000 0xc8483fffe0000000 0x3c8483fffe000000

def z866 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0xff7fff3f80000000 0x1ff7fff3f8000000

def z867 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0x746ffb3fe08700f4 0x1746ffb3fe08700f

def z868 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff18383fef6464ff 0xfff18383fef6464f

def z869 : W := mkw 0x8000101120000000 0x0800010112000000 0xa408383fe0000000 0x3a408383fe000000

def z870 : W := mkw 0x807fb7b720888885 0xf807fb7b72088888 0x26ef3f3b90989800 0x926ef3f3b9098980

def z871 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xff6fff3fe0000000 0x3ff6fff3fe000000

def z872 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xf277ffffe0000000 0x3f277ffffe000000

def z873 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xfff7c707f8fffcff 0xffff7c707f8fffcf

def z874 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xfffffffff080f8cd 0xffffffffff080f8c

def z875 : W := mkw 0xe47ff7f77c9381a1 0xfe47ff7f77c9381a 0xfffffffff89b8300 0xbfffffffff89b830

def z876 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfd1ff8ffe0000000 0x3fd1ff8ffe000000

def z877 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0x8fffc7f81f00ff0b 0xf8fffc7f81f00ff0

def z878 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0xfd7bfbffe0000000 0x3fd7bfbffe000000

def z879 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0xdb9004c47f64ffff 0xedb9004c47f64fff

def z880 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8001ffb0001 0x87f3ff8001ffb000

def z881 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff0780001 0x3ff7ffffff078000

def z882 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xb7e7070790f8fffd 0xdb7e7070790f8fff

def z883 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe0070030 0x3ff7fffffe007003

def z884 : W := mkw 0x0e044c4cc3e5e5f2 0x20e044c4cc3e5e5f 0x5004c00467e764ff 0x45004c00467e764f

def z885 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7808383fe76464ff 0x67808383fe76464f

def z886 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7fffffff9b0003 0xfff7fffffff9b000

def z887 : W := mkw 0x9a001819a364765a 0x09a001819a364765 0xfd88383fe764ffff 0x7fd88383fe764fff

def z888 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x80c807f80700ff08 0x380c807f80700ff0

def z889 : W := mkw 0x8000101120000000 0x0800010112000000 0x7408383fe0000000 0x17408383fe000000

def z890 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdf9cc4c46f8787ff 0xedf9cc4c46f8787f

def z891 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0xef7bfffbe0000000 0x3ef7bfffbe000000

def z892 : W := mkw 0xd07bb3b33c001209 0xdd07bb3b33c00120 0x246b3b3b90001800 0x1246b3b3b9000180

def z893 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x000000000fe764ff 0xc000000000fe764f

def z894 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xb56b3b3f80000000 0x1b56b3b3f8000000

def z895 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x263ff8001fff0007 0xc263ff8001fff000

def z896 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7c3ff8001fff0007 0x07c3ff8001fff000

def z897 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0x7f3ff8c01fff0307 0xc7f3ff8c01fff030

def z898 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x700ff83fe0000000 0x0700ff83fe000000

def z899 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x48000000676464ff 0x648000000676464f

def z900 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0xbf7f3fff80000000 0x3bf7f3fff8000000

def z901 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xf7e7c70790fff8cd 0xdf7e7c70790fff8c

def z902 : W := mkw 0x804113b320000000 0x5804113b32000000 0xfd483b3fe0000000 0x3fd483b3fe000000

def z903 : W := mkw 0x0801010280282844 0x1080101028028284 0x24630303907878cd 0x524630303907878c

def z904 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0x8ffb07f81f18ff0b 0xf8ffb07f81f18ff0

def z905 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x246b3b3b90780001 0x1246b3b3b9078000

def z906 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe88700f6 0xfff7fffffe88700f

def z907 : W := mkw 0x804557f760000000 0x7804557f76000000 0xff5cffffe0000000 0x3ff5cffffe000000

def z908 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xa76b3f3b80000000 0x1a76b3f3b8000000

def z909 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8bd807f80f00ff0a 0xf8bd807f80f00ff0

def z910 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7a7fffffe0000000 0x27a7fffffe000000

def z911 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xfffffffff09898cc 0xffffffffff09898c

def z912 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7fffff001fff9807 0xc7fffff001fff980

def z913 : W := mkw 0xda381ab1be64325b 0x4da381ab1be64325 0x72f03fc7f8649bf4 0x872f03fc7f8649bf

def z914 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xb7e7070790fff8fd 0xdb7e7070790fff8f

def z915 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0x7f7ffb381fff0007 0xd7f7ffb381fff000

def z916 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe7000003 0x7ff7fffffe700000

def z917 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x26e7070390f8f8cd 0xd26e7070390f8f8c

def z918 : W := mkw 0x0e00080883e5e5f2 0x00e00080883e5e5f 0x0000000007e764ff 0x40000000007e764f

def z919 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe08484fe 0xfffffffffe08484f

def z920 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81f87ff0f 0xf8ff807f81f87ff0

def z921 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x0000000007646007 0x4000000000764600

def z922 : W := mkw 0x103802a801005609 0x4103802a80100560 0x8ff807f80700ff0b 0x78ff807f80700ff0

def z923 : W := mkw 0x0e00080883ededf6 0x00e00080883ededf 0x008000001fffffff 0xc008000001ffffff

def z924 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81700ff09 0x38ff807f81700ff0

def z925 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xff7fffffe0980000 0x3ff7fffffe098000

def z926 : W := mkw 0x847bf3f360010121 0xd847bf3f36001012 0x6c7bfbfbe8070732 0x36c7bfbfbe807073

def z927 : W := mkw 0xc03810113c000001 0x0c03810113c00000 0xff38383fff000003 0xfff38383fff00000

def z928 : W := mkw 0x0801010280282844 0x1080101028028284 0x24e303039078f809 0xd24e303039078f80

def z929 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c7c7f8fbfbcd 0xffff7c7c7f8fbfbc

def z930 : W := mkw 0x100002a801005608 0x4100002a80100560 0x88c807f80700ff0a 0x388c807f80700ff0

def z931 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x04e807f81700fb01 0x104e807f81700fb0

def z932 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x06f807f81f00ff0b 0xd06f807f81f00ff0

def z933 : W := mkw 0x4a0008089f646452 0x04a0008089f64645 0x000000001f6464ff 0xc000000001f6464f

def z934 : W := mkw 0x0801010280282844 0x1080101028028284 0x2463030390f87805 0xd2463030390f8780

def z935 : W := mkw 0x04054546408181a0 0x304054546408181a 0xdbd4c7c7e88787fe 0xfdbd4c7c7e88787f

def z936 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0ef807f81f00ff03 0xb0ef807f81f00ff0

def z937 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xad08383fe76064fb 0x7ad08383fe76064f

def z938 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7e707c790f8fbcd 0xdb7e707c790f8fbc

def z939 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe0600005 0x7fd08383fe060000

def z940 : W := mkw 0xe03ab0113c120001 0x8e03ab0113c12000 0xff3ff83ff89b0000 0xbff3ff83ff89b000

def z941 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdfb4c4c4788787ff 0xedfb4c4c4788787f

def z942 : W := mkw 0x0801010280282844 0x1080101028028284 0xb767030790f878cd 0xdb767030790f878c

def z943 : W := mkw 0x04054546408989a4 0x304054546408989a 0xfff7c7c7f89f9ffe 0xffff7c7c7f89f9ff

def z944 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x7f7ffbfbe0000000 0x37f7ffbfbe000000

def z945 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe883870a 0xfffffffffe883870

def z946 : W := mkw 0x0801010280282844 0x1080101028028284 0xfd630307f07c7cff 0x7fd630307f07c7cf

def z947 : W := mkw 0x04054546408989a4 0x304054546408989a 0xfff7c7c478ff9fff 0xefff7c7c478ff9ff

def z948 : W := mkw 0x0801010280282844 0x1080101028028284 0xaff307c39878ff0b 0xfaff307c39878ff0

def z949 : W := mkw 0xd47ff7f77c8193a9 0xfd47ff7f77c8193a 0xfffffffff8879ffe 0xffffffffff8879ff

def z950 : W := mkw 0x8447f7f7608181a0 0xf8447f7f7608181a 0xfbd7ffffe88787fe 0xffbd7ffffe88787f

def z951 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x86f807f81f00ff09 0xb86f807f81f00ff0

def z952 : W := mkw 0xc07bb3b33c000001 0xdc07bb3b33c00000 0x2f7b3b3b9f000003 0xd2f7b3b3b9f00000

def z953 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5894c0c4688787fe 0xe5894c0c4688787f

def z954 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7fbff8001fff870f 0xc7fbff8001fff870

def z955 : W := mkw 0x04044444408181a0 0x204044444408181a 0xc890c4c4688787fe 0xec890c4c4688787f

def z956 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0x7f3ff8f81fff0007 0xe7f3ff8f81fff000

def z957 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfd6ffb3fe0000000 0x3fd6ffb3fe000000

def z958 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe00004f8 0x3ff7fffffe00004f

def z959 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xffffffffe807873a 0xfffffffffe807873

def z960 : W := mkw 0x04044444408181a0 0x204044444408181a 0xff94c4c468e787ff 0xeff94c4c468e787f

def z961 : W := mkw 0x0404444440010120 0x2040444444001012 0xdb14c4c4680707fe 0x6db14c4c4680707f

def z962 : W := mkw 0x8447f557608181a0 0xb8447f557608181a 0xff9ffcffe88787fe 0xfff9ffcffe88787f

def z963 : W := mkw 0x844557f7608181a0 0x7844557f7608181a 0xffdcffffe88787fe 0xfffdcffffe88787f

def z964 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xf767ffffe0000000 0x3f767ffffe000000

def z965 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbff7070798f8f8cf 0xdbff7070798f8f8c

def z966 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ffcc7f81f83ff0b 0xf8ffcc7f81f83ff0

def z967 : W := mkw 0x2a00080883766452 0x02a0008088376645 0x0000000007ff64ff 0x40000000007ff64f

def z968 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x36e7070790f8f8c5 0x936e7070790f8f8c

def z969 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0040006 0x7ff7fffffe004000

def z970 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xf7f7c7c7f8fffbfd 0xdf7f7c7c7f8fffbf

def z971 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x8dc807f81f00ff0b 0xf8dc807f81f00ff0

def z972 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd18f83fef6764ff 0x7fd18f83fef6764f

def z973 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x780ff80007ff0006 0x0780ff80007ff000

def z974 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xa46b3b3fe0000000 0x3a46b3b3fe000000

def z975 : W := mkw 0x543c46ec5d81d7a9 0x6543c46ec5d81d7a 0x546cc33c778778f5 0x1546cc33c778778f

def z976 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x87e007f81f00ff0b 0xf87e007f81f00ff0

def z977 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0xfd18f83fe0000000 0x3fd18f83fe000000

def z978 : W := mkw 0xa07ff7f760120001 0xfa07ff7f76012000 0xff7fffffe09b0000 0x3ff7fffffe09b000

def z979 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x3767030790f878c5 0xd3767030790f878c

def z980 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd294c4c4688787fc 0xad294c4c4688787f

def z981 : W := mkw 0xf23abab93f56561b 0xcf23abab93f56561 0x4818f8f86f070732 0x24818f8f86f07073

def z982 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x80483fffe0000000 0x380483fffe000000

def z983 : W := mkw 0x807fb7b720808081 0xf807fb7b72080808 0xb7ef3f3f808080cc 0xdb7ef3f3f808080c

def z984 : W := mkw 0x8000101120000000 0x0800010112000000 0xff1cf83fe8870006 0xfff1cf83fe887000

def z985 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xa67fffffe0000000 0x3a67fffffe000000

def z986 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe76404f6 0x3fd08383fe76404f

def z987 : W := mkw 0x0801010280282844 0x1080101028028284 0x7f77c30398ff7807 0xd7f77c30398ff780

def z988 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xa7eb3f3b9000f809 0xda7eb3f3b9000f80

def z989 : W := mkw 0x04004040408181a0 0x004004040408181a 0x4890c0c0680787fa 0x24890c0c0680787f

def z990 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8381fff0007 0xfff3ff8381fff000

def z991 : W := mkw 0xd07ff7f77c889a8d 0xfd07ff7f77c889a8 0xfffffffff8989b00 0xbfffffffff8989b0

def z992 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x2f7b3b3b80000000 0x12f7b3b3b8000000

def z993 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe0830000 0x3ff7fffffe083000

def z994 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8dd807f80f00ff0b 0x78dd807f80f00ff0

def z995 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0af807f81f00ff0b 0xe0af807f81f00ff0

def z996 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfdc83f3fe764fcff 0x7fdc83f3fe764fcf

def z997 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xcd08383fe70464fb 0x7cd08383fe70464f

def z998 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x746b3b3fe0000000 0x1746b3b3fe000000

def z999 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7e7c70790fbf8cd 0xdb7e7c70790fbf8c

def z1000 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0xfffffff81fff870f 0xffffffff81fff870

def z1001 : W := mkw 0x04004040408181a0 0x004004040408181a 0x4810c0c0688707f6 0x24810c0c0688707f

def z1002 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x767fffffe0000000 0x1767fffffe000000

def z1003 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff9cfcffefe7e7ff 0xfff9cfcffefe7e7f

def z1004 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e7070798f8ffcf 0xdb7e7070798f8ffc

def z1005 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c47887ffff 0xedb94c4c47887fff

def z1006 : W := mkw 0x8000101120000000 0x0800010112000000 0xff2f383ff0f80005 0xfff2f383ff0f8000

def z1007 : W := mkw 0x0801010280282844 0x1080101028028284 0xb563030790787801 0x1b56303079078780

def z1008 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0xcff8fff81f00ff0b 0xfcff8fff81f00ff0

def z1009 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe0008300 0x3ffffffffe000830

def z1010 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5a94c4c4688787f6 0xa5a94c4c4688787f

def z1011 : W := mkw 0xd03812b13c001209 0x4d03812b13c00120 0xfff83ffff8009b00 0xbfff83ffff8009b0

def z1012 : W := mkw 0xe07bb3b33c120001 0xde07bb3b33c12000 0x246b3b3b90180000 0x1246b3b3b9018000

def z1013 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x82f007f81f00ff0b 0xf82f007f81f00ff0

def z1014 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xf7e70707f0fcf8fd 0xdf7e70707f0fcf8f

def z1015 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0xffffffc01fff9f0f 0xeffffffc01fff9f0

def z1016 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8001fff600f 0xdff3ff8001fff600

def z1017 : W := mkw 0x0801010280282844 0x1080101028028284 0xb7e7070390f8f80d 0xdb7e7070390f8f80

def z1018 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x246b3b3fe0000000 0x1246b3b3fe000000

def z1019 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000076060cd 0x400000000076060c

def z1020 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0xff3ff83fe88704fe 0xfff3ff83fe88704f

def z1021 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0x000000001fff6007 0xc000000001fff600

def z1022 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xc808383fe76464ff 0x7c808383fe76464f

def z1023 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7d1ff8000fff0007 0x47d1ff8000fff000

def z1024 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0xa7e3070390f8f8cd 0xda7e3070390f8f8c

def z1025 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0xfffffff81f87ff0f 0xffffffff81f87ff0

def z1026 : W := mkw 0x04054546408181a0 0x304054546408181a 0xfb97c4c7e88787fe 0xefb97c4c7e88787f

def z1027 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7fffffef000002 0x3ff7fffffef00000

def z1028 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e7070798fff8cf 0xdb7e7070798fff8c

def z1029 : W := mkw 0x0400404040010120 0x0040040404001012 0x4810c0c0680707fe 0x64810c0c0680707f

def z1030 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe88383cc 0xfffffffffe88383c

def z1031 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfffffffff0009800 0xbfffffffff000980

def z1032 : W := mkw 0x6a0008089ffeecd6 0x06a0008089ffeecd 0x008000001ffffcff 0xc008000001ffffcf

def z1033 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x242ff80017fb0001 0x0242ff80017fb000

def z1034 : W := mkw 0x0801010280282844 0x1080101028028284 0x26e307039078f801 0x926e307039078f80

def z1035 : W := mkw 0x8a001811a2642052 0x08a001811a264205 0xfd08383fe76400f7 0x7fd08383fe76400f

def z1036 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0xfffffff81f9bff0b 0xffffffff81f9bff0

def z1037 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd883cffe764e7ff 0x7fd883cffe764e7f

def z1038 : W := mkw 0x8042f05160000000 0x88042f0516000000 0xfd08f83fe0000000 0x3fd08f83fe000000

def z1039 : W := mkw 0x0801010280282844 0x1080101028028284 0x2763030390787801 0xd276303039078780

def z1040 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd2b383ff77c64ff 0x7fd2b383ff77c64f

def z1041 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x6e3ff8001fff0003 0x86e3ff8001fff000

def z1042 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb5e307079078f8cd 0x5b5e307079078f8c

def z1043 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x37e7070390f8f805 0xd37e7070390f8f80

def z1044 : W := mkw 0x803812b120000001 0x4803812b12000000 0xfff83fffe80487fe 0xffff83fffe80487f

def z1045 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe80707fe 0x7ff7fffffe80707f

def z1046 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xff7ffffff0001800 0x3ff7ffffff000180

def z1047 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdff807f81f04ff0f 0xfdff807f81f04ff0

def z1048 : W := mkw 0x04054546408181a0 0x304054546408181a 0xfff7c7c7f887ffff 0xffff7c7c7f887fff

def z1049 : W := mkw 0x8000101120000000 0x0800010112000000 0xad08383b80000000 0x3ad08383b8000000

def z1050 : W := mkw 0xe47ff7f77c9381a1 0xfe47ff7f77c9381a 0xfffffffff89f87fe 0xffffffffff89f87f

def z1051 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x376f3b3b90f80005 0xd376f3b3b90f8000

def z1052 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdf9cc4fc688787fe 0xfdf9cc4fc688787f

def z1053 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe08087fc 0xfffffffffe08087f

def z1054 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff683f3fe76464ff 0x7ff683f3fe76464f

def z1055 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7fffffe8030000 0x3ff7fffffe803000

def z1056 : W := mkw 0x8038101120000001 0x0803810112000000 0xff38383fe0000000 0x3ff38383fe000000

def z1057 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x2408383fe76060f1 0x12408383fe76060f

def z1058 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x4a3ff8001fff0007 0xc4a3ff8001fff000

def z1059 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x84e807f81f00ff0b 0xf84e807f81f00ff0

def z1060 : W := mkw 0x04044444408181a0 0x204044444408181a 0xcb90c4c4680787fa 0xecb90c4c4680787f

def z1061 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xffffffffff009b03 0xfffffffffff009b0

def z1062 : W := mkw 0xe07bb3b33c120001 0xde07bb3b33c12000 0x267ffb3b989b0000 0x9267ffb3b989b000

def z1063 : W := mkw 0x8005151720000000 0x3800515172000000 0xfd483f3fe0000000 0x3fd483f3fe000000

def z1064 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfb1ffcffe0000000 0x2fb1ffcffe000000

def z1065 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe8830000 0xbff7fffffe883000

def z1066 : W := mkw 0x8000101120000000 0x0800010112000000 0x7d08383b80000000 0x17d08383b8000000

def z1067 : W := mkw 0x8e05555fe1a9edf6 0x38e05555fe1a9edf 0x80c007ffe000fff8 0x380c007ffe000fff

def z1068 : W := mkw 0x0801010280282844 0x1080101028028284 0xa4630307907878c9 0x1a4630307907878c

def z1069 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5b14c0c4688707f6 0xe5b14c0c4688707f

def z1070 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0x7818f8ffe0000000 0x27818f8ffe000000

def z1071 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x700ff80007ff0004 0x0700ff80007ff000

def z1072 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x008000000f64e7ff 0xc008000000f64e7f

def z1073 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xf7e7c707f0f8f8cd 0xdf7e7c707f0f8f8c

def z1074 : W := mkw 0x0400404040010120 0x0040040404001012 0xdb14c0c4688707fe 0xedb14c0c4688707f

def z1075 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e707c790f8ffcd 0xfb7e707c790f8ffc

def z1076 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb567030790f878cd 0x5b567030790f878c

def z1077 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0xdfffc7f81f9fff0f 0xfdfffc7f81f9fff0

def z1078 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbfef073f90f8f8cd 0xfbfef073f90f8f8c

def z1079 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe00000cc 0x7fd08383fe00000c

def z1080 : W := mkw 0x1a0008088364765a 0x01a0008088364765 0x008000000764ffff 0x4008000000764fff

def z1081 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81f00fb01 0xb8ff807f81f00fb0

def z1082 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe8008300 0xbffffffffe800830

def z1083 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdffcc7f81f00ff0b 0xfdffcc7f81f00ff0

def z1084 : W := mkw 0x0a00080883ececd6 0x00a00080883ececd 0x0080000017f8f8cd 0xc0080000017f8f8c

def z1085 : W := mkw 0x803d17b720000001 0x7803d17b72000000 0xff7f3fffe0000000 0x3ff7f3fffe000000

def z1086 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd683b3ff7647cff 0x7fd683b3ff7647cf

def z1087 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7e70707f0f8f8fd 0xdb7e70707f0f8f8f

def z1088 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x781ff8001fff0007 0xc781ff8001fff000

def z1089 : W := mkw 0x0a000808836c6c56 0x00a000808836c6c5 0x00000000177c7cff 0x400000000177c7cf

def z1090 : W := mkw 0x5e0008089fe5f7fa 0x05e0008089fe5f7f 0x008000001fe7ffff 0xc008000001fe7fff

def z1091 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x200b383b80000000 0x0200b383b8000000

def z1092 : W := mkw 0x0805050680282844 0x3080505068028284 0x3467030790787801 0x1346703079078780

def z1093 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe0008008 0xfffffffffe000800

def z1094 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c478ff87ff 0xedb94c4c478ff87f

def z1095 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xf85fffffe0000000 0x3f85fffffe000000

def z1096 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000006464fc 0x000000000006464f

def z1097 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x88d807f81f00ff0b 0xf88d807f81f00ff0

def z1098 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xfffffffff098f809 0xffffffffff098f80

def z1099 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd0f383fe7fc64ff 0x7fd0f383fe7fc64f

def z1100 : W := mkw 0x500002a81d005608 0x4500002a81d00560 0x80c007f80f00ff0a 0x380c007f80f00ff0

def z1101 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd914c0c4688707fe 0x6d914c0c4688707f

def z1102 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff0000001 0xfff7ffffff000000

def z1103 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe000040a 0x7fd08383fe000040

def z1104 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0x24e3030390f8f801 0x924e3030390f8f80

def z1105 : W := mkw 0x84045455608181a0 0x284045455608181a 0xfd883cffe00087f8 0x3fd883cffe00087f

def z1106 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f7ffb001fff7807 0xd7f7ffb001fff780

def z1107 : W := mkw 0x04004040408181a0 0x004004040408181a 0x5b94c0c0688787fe 0xe5b94c0c0688787f

def z1108 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0x0000000017647cff 0x40000000017647cf

def z1109 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x772ff80017ff0005 0xc772ff80017ff000

def z1110 : W := mkw 0x84001011208181a0 0x084001011208181a 0xfd88383fe88787fe 0xffd88383fe88787f

def z1111 : W := mkw 0x5a380aa89f64765b 0x45a380aa89f64765 0x02f007c01f64ffff 0xc02f007c01f64fff

def z1112 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xa4eb3fffe00087f8 0x3a4eb3fffe00087f

def z1113 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe76460f5 0x3fd08383fe76460f

def z1114 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xa0433fffe0000000 0x3a0433fffe000000

def z1115 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xf508383fe76460fd 0x5f508383fe76460f

def z1116 : W := mkw 0x0805050680282844 0x3080505068028284 0xb7670707907878cd 0x5b7670707907878c

def z1117 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xff7fffffe8000300 0x3ff7fffffe800030

def z1118 : W := mkw 0x8000101921004400 0x0800010192100440 0xfd08383fe70464ff 0x7fd08383fe70464f

def z1119 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fe70464fa 0x3fd08383fe70464f

def z1120 : W := mkw 0x0c01010280a9a9e4 0x10c01010280a9a9e 0x24e3030398ffffff 0xd24e3030398fffff

def z1121 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdff807fc7f00ff0b 0xfdff807fc7f00ff0

def z1122 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xff7ffffb80000000 0x3ff7ffffb8000000

def z1123 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x4818f8ffe0000000 0x24818f8ffe000000

def z1124 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0xf007f83fe0000000 0x3f007f83fe000000

def z1125 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0x7f7ffb001fff1807 0xc7f7ffb001fff180

def z1126 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0x242b383b80000000 0x1242b383b8000000

def z1127 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x80000004676464ff 0x680000004676464f

def z1128 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xb7e7070798fbfbcd 0xdb7e7070798fbfbc

def z1129 : W := mkw 0x803812b120000001 0x4803812b12000000 0x24683b3b80000000 0x124683b3b8000000

def z1130 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd894c4c4688787fe 0x2d894c4c4688787f

def z1131 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0x7007f8ffe0000000 0x27007f8ffe000000

def z1132 : W := mkw 0x703aa2a81d125609 0xc703aa2a81d12560 0xbfffc7f81ffbff0f 0xfbfffc7f81ffbff0

def z1133 : W := mkw 0x8000101120000000 0x0800010112000000 0x6c08383be0000000 0x36c08383be000000

def z1134 : W := mkw 0x804557f760000000 0x7804557f76000000 0xf0403fffe0000000 0x3f0403fffe000000

def z1135 : W := mkw 0x8000101120000000 0x0800010112000000 0xc808383fe0000000 0x3c808383fe000000

def z1136 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0600005 0x7ff7fffffe060000

def z1137 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xad6b3b3b80000000 0x3ad6b3b3b8000000

def z1138 : W := mkw 0x04054546408181a0 0x304054546408181a 0xfff7c7c7f8ff87ff 0xffff7c7c7f8ff87f

def z1139 : W := mkw 0xfa3abab9bf76765b 0xcfa3abab9bf76765 0x246b3b3b97787801 0x1246b3b3b9778780

def z1140 : W := mkw 0x907ff7f760001209 0xf907ff7f76000120 0xffffffffe0009b00 0x3ffffffffe0009b0

def z1141 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xaf7ffffb80000000 0x3af7ffffb8000000

def z1142 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8de807f81700ff0b 0x78de807f81700ff0

def z1143 : W := mkw 0x0801010280282844 0x1080101028028284 0xa563030390787809 0x5a56303039078780

def z1144 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x59000000076464ff 0x459000000076464f

def z1145 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7ffffff0180000 0x3ff7ffffff018000

def z1146 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xf808383fe76464fe 0x3f808383fe76464f

def z1147 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbff707c790f8f8cd 0xfbff707c790f8f8c

def z1148 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xb7f7c7c790f8f8cd 0xdb7f7c7c790f8f8c

def z1149 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x7d6b3b3b80000000 0x17d6b3b3b8000000

def z1150 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xdffcc7fc7f87ffff 0xfdffcc7fc7f87fff

def z1151 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x32e7070790f8f8cd 0xc32e7070790f8f8c

def z1152 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff883c3fe764e4ff 0xfff883c3fe764e4f

def z1153 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0x780ff83fe0000000 0x2780ff83fe000000

def z1154 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe88707f6 0x3ff7fffffe88707f

def z1155 : W := mkw 0x0400404040010120 0x0040040404001012 0x5810c0c4680707f6 0x25810c0c4680707f

def z1156 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0xff3ff8ffe0000000 0x3ff3ff8ffe000000

def z1157 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7f7ffffb80000000 0x17f7ffffb8000000

def z1158 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xffe707c7f0fcffff 0xfffe707c7f0fcfff

def z1159 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xcff807f87f04ff3b 0xfcff807f87f04ff3

def z1160 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xbfef070797f8f8cf 0xdbfef070797f8f8c

def z1161 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe887870e 0xfffffffffe887870

def z1162 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x7f7ffb3b88870006 0xd7f7ffb3b8887000

def z1163 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe88783f4 0xbffffffffe88783f

def z1164 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff2f383fe76464ff 0x7ff2f383fe76464f

def z1165 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xfd4fffffe0000000 0x3fd4fffffe000000

def z1166 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7b1ff8000fff0006 0xc7b1ff8000fff000

def z1167 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe08780fc 0xfffffffffe08780f

def z1168 : W := mkw 0x0801010280282844 0x1080101028028284 0x2667030390f87801 0x92667030390f8780

def z1169 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe00000cc 0x7ff7fffffe00000c

def z1170 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb4e7070790f8f8cd 0x1b4e7070790f8f8c

def z1171 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x681bf8fbe0000000 0x2681bf8fbe000000

def z1172 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e707079078f8c9 0x1b7e707079078f8c

def z1173 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8001fff04ff 0xc7f3ff8001fff04f

def z1174 : W := mkw 0x847ff7f7608989a5 0xf847ff7f7608989a 0xfffffffff89b9b00 0xbfffffffff89b9b0

def z1175 : W := mkw 0x0a044c4cc3646452 0x20a044c4cc364645 0xdb14c4c4676464ff 0x6db14c4c4676464f

def z1176 : W := mkw 0x0a000808836c6c56 0x00a000808836c6c5 0x0000000017787801 0x0000000001778780

def z1177 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe00080c8 0x3ffffffffe00080c

def z1178 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff1cf83fe76464ff 0x7ff1cf83fe76464f

def z1179 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0xa46b3f3f80000000 0x1a46b3f3f8000000

def z1180 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe8878732 0xbffffffffe887873

def z1181 : W := mkw 0x4a3808089f646453 0x04a3808089f64645 0x0f3800001f6464ff 0xc0f3800001f6464f

def z1182 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xbff807ff9f00ff0b 0xfbff807ff9f00ff0

def z1183 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff0007801 0x3ff7ffffff000780

def z1184 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x763ff8001fff0005 0x8763ff8001fff000

def z1185 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0xdb14c0047fff64ff 0xedb14c0047fff64f

def z1186 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81f04ffff 0xf8ff807f81f04fff

def z1187 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xffffffc01fffff0f 0xfffffffc01fffff0

def z1188 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe000040a 0x7ff7fffffe000040

def z1189 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7ffffffff80007 0xfff7ffffffff8000

def z1190 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xf408383fe76464fd 0x3f408383fe76464f

def z1191 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe00000f0 0x3ff7fffffe00000f

def z1192 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383fefe764ff 0xffd08383fefe764f

def z1193 : W := mkw 0x0a00080883ececd6 0x00a00080883ececd 0x008000000764fcff 0x4008000000764fcf

def z1194 : W := mkw 0x847af2f160010121 0xc847af2f16001012 0xfd18f8ffe80707fe 0x7fd18f8ffe80707f

def z1195 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8000fff0006 0x07f3ff8000fff000

def z1196 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x24630307907878c1 0x124630307907878c

def z1197 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0870004 0x3ff7fffffe087000

def z1198 : W := mkw 0x0000000000000000 0x0000000000000000 0xdb94c4c4688787fe 0xedb94c4c4688787f

def z1199 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff3ff83fffff64ff 0xfff3ff83fffff64f

def z1200 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x246b3b3b90007801 0x1246b3b3b9000780

def z1201 : W := mkw 0x04004040408181a0 0x004004040408181a 0xcb90c4c0688787fe 0xecb90c4c0688787f

def z1202 : W := mkw 0x04044444408181a0 0x204044444408181a 0x5294c4c4688787fe 0xc5294c4c4688787f

def z1203 : W := mkw 0x803ef45560000001 0xa803ef4556000000 0xff3ffcffe0000000 0x3ff3ffcffe000000

def z1204 : W := mkw 0x100002a801005608 0x4100002a80100560 0x84c807f80700ff09 0x384c807f80700ff0

def z1205 : W := mkw 0x0005050600000000 0x3000505060000000 0xb7e7070790f8f80d 0xdb7e7070790f8f80

def z1206 : W := mkw 0x8001111320000000 0x1800111132000000 0xfd6b3b3fe0000000 0x3fd6b3b3fe000000

def z1207 : W := mkw 0x807ff7f760080805 0xf807ff7f76008080 0xff7ffffff0181800 0x3ff7ffffff018180

def z1208 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7408383fe76464ff 0x57408383fe76464f

def z1209 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0x7047fb3fe0000000 0x17047fb3fe000000

def z1210 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7e70707f0f8fcfd 0xfb7e70707f0f8fcf

def z1211 : W := mkw 0x804557f760000000 0x7804557f76000000 0xa4483fffe0000000 0x3a4483fffe000000

def z1212 : W := mkw 0x8000101120000000 0x0800010112000000 0xff983cffe800870a 0xfff983cffe800870

def z1213 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7ffffff8fb0005 0xfff7ffffff8fb000

def z1214 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xffef3f3ff7fcfcff 0xfffef3f3ff7fcfcf

def z1215 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x008000001764fcff 0xc008000001764fcf

def z1216 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0x346f3b3f80000000 0x1346f3b3f8000000

def z1217 : W := mkw 0x8004141520000000 0x2800414152000000 0xff0c3c3fe0000000 0x3ff0c3c3fe000000

def z1218 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xf908383fe76404fe 0x6f908383fe76404f

def z1219 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xa4e307c7f078fff9 0x3a4e307c7f078fff

def z1220 : W := mkw 0x8047f55760000000 0xb8047f5576000000 0x740ff83fe0000000 0x1740ff83fe000000

def z1221 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x2f3ff8001ffb0003 0xc2f3ff8001ffb000

def z1222 : W := mkw 0x04044444408181a0 0x204044444408181a 0x4a94c4c0688787fe 0xe4a94c4c0688787f

def z1223 : W := mkw 0x08054546c0282844 0x308054546c028284 0xff77c7c7f0787801 0x3ff77c7c7f078780

def z1224 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff183cffe76464ff 0x7ff183cffe76464f

def z1225 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xfff7c70798ffffff 0xdfff7c70798fffff

def z1226 : W := mkw 0x803812b120000001 0x4803812b12000000 0xfd1838ffe0000000 0x3fd1838ffe000000

def z1227 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7d08383fe76460f7 0x57d08383fe76460f

def z1228 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0x266f3f3b80000000 0x1266f3f3b8000000

def z1229 : W := mkw 0x0801010280282844 0x1080101028028284 0xa4e307039078f809 0x1a4e307039078f80

def z1230 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb94c4c4680787fa 0x2db94c4c4680787f

def z1231 : W := mkw 0x807bb3b320080805 0xd807bb3b32008080 0x246b3b3b90181800 0x1246b3b3b9018180

def z1232 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xfffffffff8ff87ff 0xffffffffff8ff87f

def z1233 : W := mkw 0x8001111320000000 0x1800111132000000 0x246b3b3b80000000 0x1246b3b3b8000000

def z1234 : W := mkw 0x503aa2a81d005609 0xc503aa2a81d00560 0xaffb3ff81f00ff0b 0xfaffb3ff81f00ff0

def z1235 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xf46fffffe0000000 0x3f46fffffe000000

def z1236 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x740ff80007ff0005 0x0740ff80007ff000

def z1237 : W := mkw 0x5e044c4cdfe5f7fa 0x25e044c4cdfe5f7f 0xdb94c4c47fe7ffff 0xedb94c4c47fe7fff

def z1238 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0x0000000017607801 0x0000000001760780

def z1239 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdb14c4c4688707f6 0x2db14c4c4688707f

def z1240 : W := mkw 0x804557f760000000 0x7804557f76000000 0xff6f3fffe0000000 0x3ff6f3fffe000000

def z1241 : W := mkw 0x6a3aa8089f766453 0x86a3aa8089f76645 0x0237c0001fff64ff 0xc0237c0001fff64f

def z1242 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x246b3bfbe0000000 0x3246b3bfbe000000

def z1243 : W := mkw 0x8000101120000000 0x0800010112000000 0xff1cf83fe0000000 0x3ff1cf83fe000000

def z1244 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe80087fa 0xfffffffffe80087f

def z1245 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x91000004076464ff 0x491000004076464f

def z1246 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x0ff807f81f00fb03 0xd0ff807f81f00fb0

def z1247 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7a3ff8001fff0006 0x87a3ff8001fff000

def z1248 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0xfffffff81fff9b07 0xffffffff81fff9b0

def z1249 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x267ffb3b80000000 0x1267ffb3b8000000

def z1250 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xa4e3070790f8f8cd 0xda4e3070790f8f8c

def z1251 : W := mkw 0xc07bb3b33c000001 0xdc07bb3b33c00000 0x246b3b3b97000001 0x1246b3b3b9700000

def z1252 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xb7e707c7f0f8f8cd 0xfb7e707c7f0f8f8c

def z1253 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x24e307039078f801 0x124e307039078f80

def z1254 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x87f807f81f00fb09 0xd87f807f81f00fb0

def z1255 : W := mkw 0x0400404040010120 0x0040040404001012 0xdb90c4c4680787fe 0xedb90c4c4680787f

def z1256 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xec7bffffe0000000 0x3ec7bffffe000000

def z1257 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x267b3ffb80000000 0x1267b3ffb8000000

def z1258 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xff7fffffe08704fe 0x7ff7fffffe08704f

def z1259 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x3727000017fc64ff 0xc3727000017fc64f

def z1260 : W := mkw 0x847ff7f760010121 0xf847ff7f76001012 0xff7fffffe8870736 0xfff7fffffe887073

def z1261 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8079fff0007 0xdff3ff8079fff000

def z1262 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0x26f7c7c398fbfb01 0x926f7c7c398fbfb0

def z1263 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0x7f7fffc01fff0007 0xc7f7fffc01fff000

def z1264 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb767070790f878c5 0x1b767070790f878c

def z1265 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c7c798fffbcf 0xdfff7c7c798fffbc

def z1266 : W := mkw 0xd07bb3b33c001209 0xdd07bb3b33c00120 0x26fb3ffb98009b00 0x926fb3ffb98009b0

def z1267 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd08383ff7fc64ff 0xffd08383ff7fc64f

def z1268 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0x000000000f6764ff 0x4000000000f6764f

def z1269 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x9ffc07f81f80ff0f 0xf9ffc07f81f80ff0

def z1270 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7f707c798f8fbcd 0xdb7f707c798f8fbc

def z1271 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xa408383fe76464ff 0x7a408383fe76464f

def z1272 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xb7f7c7c7f8fbfffd 0xfb7f7c7c7f8fbfff

def z1273 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe8000702 0x3ff7fffffe800070

def z1274 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd88383ff764fcff 0xffd88383ff764fcf

def z1275 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xfffffffff8009f0a 0xffffffffff8009f0

def z1276 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xec08383fe76464fb 0x3ec08383fe76464f

def z1277 : W := mkw 0x6a0008089f766452 0x06a0008089f76645 0x0000000017786001 0x0000000001778600

def z1278 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x8b9004c00f64e7ff 0xe8b9004c00f64e7f

def z1279 : W := mkw 0x0801010280a8a8c4 0x10801010280a8a8c 0x37e7030390f8f8cd 0xd37e7030390f8f8c

def z1280 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7007f8000fff0006 0x07007f8000fff000

def z1281 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0x2467030390f87801 0x12467030390f8780

def z1282 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff0c383fe7e464ff 0xfff0c383fe7e464f

def z1283 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x00000000076460f5 0x000000000076460f

def z1284 : W := mkw 0x803ab01120000001 0x8803ab0112000000 0xfd2b383fe0000000 0x3fd2b383fe000000

def z1285 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xbff807f81f60ff0f 0xfbff807f81f60ff0

def z1286 : W := mkw 0x803812b120000001 0x4803812b12000000 0xfd683b3fe0000000 0x3fd683b3fe000000

def z1287 : W := mkw 0xc47ff7f77c8181a1 0xfc47ff7f77c8181a 0xffffffffff8787ff 0xfffffffffff8787f

def z1288 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xfd58ffffe0000000 0x3fd58ffffe000000

def z1289 : W := mkw 0x803c56f560000001 0x6803c56f56000000 0xff7cffffe0000000 0x3ff7cffffe000000

def z1290 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7fbff8001ffff80f 0xc7fbff8001ffff80

def z1291 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7c7ffbffe0000000 0x37c7ffbffe000000

def z1292 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8cf807f81f00ff0b 0x38cf807f81f00ff0

def z1293 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe0808000 0xbffffffffe080800

def z1294 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xfb9ffcffe88787fe 0xefb9ffcffe88787f

def z1295 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xffe7070790fcf8cf 0xdffe7070790fcf8c

def z1296 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xffe7c707f0fffcff 0xfffe7c707f0fffcf

def z1297 : W := mkw 0x0801010280282844 0x1080101028028284 0x34630307907878c5 0x134630307907878c

def z1298 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe00400f4 0x3fd08383fe00400f

def z1299 : W := mkw 0x8005151720000000 0x3800515172000000 0xfd0f383fe0000000 0x3fd0f383fe000000

def z1300 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7c08383fe76464f7 0x37c08383fe76464f

def z1301 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x646bfb3be0000000 0x1646bfb3be000000

def z1302 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x6c6b3b3be0000000 0x36c6b3b3be000000

def z1303 : W := mkw 0x04044444408181a0 0x204044444408181a 0xffb7c4c4688787fe 0xeffb7c4c4688787f

def z1304 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x6e7ffffbe0000000 0x36e7ffffbe000000

def z1305 : W := mkw 0x703aa8001e561209 0x8703aa8001e56120 0x7fbff8001fff9b07 0xc7fbff8001fff9b0

def z1306 : W := mkw 0x0e044c4cc3e5e5f2 0x20e044c4cc3e5e5f 0x808004c46764e7ff 0x6808004c46764e7f

def z1307 : W := mkw 0x8000101120000000 0x0800010112000000 0xff683f3fe0000000 0x3ff683f3fe000000

def z1308 : W := mkw 0x6002a8001e560000 0x86002a8001e56000 0x7727f8001fff0007 0xc7727f8001fff000

def z1309 : W := mkw 0x8005151720888884 0x3800515172088888 0xffef3f3ff0989800 0xbffef3f3ff098980

def z1310 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xffffffffff00f80b 0xfffffffffff00f80

def z1311 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x9ff807fc1f00ffcf 0xf9ff807fc1f00ffc

def z1312 : W := mkw 0x0a040c0c83e4e4d2 0x20a040c0c83e4e4d 0x9384040407e4e4ff 0xc9384040407e4e4f

def z1313 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe0040432 0x3fd08383fe004043

def z1314 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdff4c7c4688787fe 0xfdff4c7c4688787f

def z1315 : W := mkw 0x0805050680282844 0x3080505068028284 0x2667070390787801 0x1266707039078780

def z1316 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xb7f7c70798fbf8cd 0xdb7f7c70798fbf8c

def z1317 : W := mkw 0x8005151720000000 0x3800515172000000 0xb76f3f3f80000000 0x1b76f3f3f8000000

def z1318 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xdb5cffffe0000000 0x3db5cffffe000000

def z1319 : W := mkw 0x0801010280282844 0x1080101028028284 0xa763070390787801 0x1a76307039078780

def z1320 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ffcc01fff0007 0xeff3ffcc01fff000

def z1321 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x000000000760640b 0x4000000000760640

def z1322 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xb76f3fffe0000000 0x3b76f3fffe000000

def z1323 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xffe70707f8ffffff 0xfffe70707f8fffff

def z1324 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x4858fbfbe0000000 0x34858fbfbe000000

def z1325 : W := mkw 0x8400505160010120 0x0840050516001012 0xfd18f8ffe8070732 0x3fd18f8ffe807073

def z1326 : W := mkw 0x843ef455608181a1 0xa843ef455608181a 0xffbffcffe88787fe 0xfffbffcffe88787f

def z1327 : W := mkw 0x0805050680282844 0x3080505068028284 0xb7e707079078f809 0xdb7e707079078f80

def z1328 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807fc7f00fffb 0xf8ff807fc7f00fff

def z1329 : W := mkw 0x8000101120000000 0x0800010112000000 0xfd08383fe0006009 0x7fd08383fe000600

def z1330 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe88704fe 0xfff7fffffe88704f

def z1331 : W := mkw 0x8005151720808080 0x3800515172080808 0xffef3f3fe08484fe 0xfffef3f3fe08484f

def z1332 : W := mkw 0x0800000080202040 0x0080000008020204 0xb7e7070790f8f8cd 0xdb7e7070790f8f8c

def z1333 : W := mkw 0x0805050680282844 0x3080505068028284 0xb767070790f87805 0xdb767070790f8780

def z1334 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x742ff8001fff0007 0xc742ff8001fff000

def z1335 : W := mkw 0x8447f7f7608181a0 0xf8447f7f7608181a 0xf0c7ffffe08787fc 0x3f0c7ffffe08787f

def z1336 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x00483b3b80000000 0x100483b3b8000000

def z1337 : W := mkw 0x8047f7f760000000 0xf8047f7f76000000 0xc040ffffe0000000 0x3c040ffffe000000

def z1338 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xa7e307079078f8c9 0xda7e307079078f8c

def z1339 : W := mkw 0x807ff7f760888885 0xf807ff7f76088888 0xffffffffe0009800 0x3ffffffffe000980

def z1340 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7ffffff0980000 0xbff7ffffff098000

def z1341 : W := mkw 0x803ab2b120000001 0xc803ab2b12000000 0xff7fffffe0000000 0x3ff7fffffe000000

def z1342 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xaf7b3fffe0000000 0x3af7b3fffe000000

def z1343 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xfffffffff0f880cd 0xffffffffff0f880c

def z1344 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x373ff8001ffb0005 0xc373ff8001ffb000

def z1345 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe000f808 0x3ffffffffe000f80

def z1346 : W := mkw 0x807ab2b120000001 0xc807ab2b12000000 0x2408383b80000000 0x12408383b8000000

def z1347 : W := mkw 0x807ff55760000001 0xb807ff5576000000 0xff3ff83fe0000000 0x3ff3ff83fe000000

def z1348 : W := mkw 0x0801010280282844 0x1080101028028284 0x3563030390787805 0x5356303039078780

def z1349 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7007f80007ff0007 0x47007f80007ff000

def z1350 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7f3ff8ffe0000000 0x27f3ff8ffe000000

def z1351 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe00487fe 0x7ffffffffe00487f

def z1352 : W := mkw 0x04044444408181a0 0x204044444408181a 0xd990c4c4680787fe 0x6d990c4c4680787f

def z1353 : W := mkw 0x807d57f760000001 0x7807d57f76000000 0xff783fffe0000000 0x3ff783fffe000000

def z1354 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xaffb3ffb8800870a 0xfaffb3ffb8800870

def z1355 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd0cf83fe7e764ff 0x7fd0cf83fe7e764f

def z1356 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdbd4c7c46887fffe 0xfdbd4c7c46887fff

def z1357 : W := mkw 0x703802a81d125609 0x4703802a81d12560 0x8ff807f81f9bff0b 0xf8ff807f81f9bff0

def z1358 : W := mkw 0x804052f160000000 0x4804052f16000000 0xfd0838ffe0000000 0x3fd0838ffe000000

def z1359 : W := mkw 0x0e044c4cc3ededf6 0x20e044c4cc3ededf 0xdb94c4c47fffffff 0xedb94c4c47ffffff

def z1360 : W := mkw 0x703aaaa01e561209 0xc703aaaa01e56120 0xffffffc01ffffb0f 0xdffffffc01ffffb0

def z1361 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0800004 0xfff7fffffe080000

def z1362 : W := mkw 0xc07ff7f77c000001 0xfc07ff7f77c00000 0xff7ffffff7000001 0x3ff7ffffff700000

def z1363 : W := mkw 0x8043b11320000000 0x98043b1132000000 0x240b383b80000000 0x1240b383b8000000

def z1364 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0f80004 0x3ff7fffffe0f8000

def z1365 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe8070002 0x3ff7fffffe807000

def z1366 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xca7fffffe0000000 0x3ca7fffffe000000

def z1367 : W := mkw 0x04004040408181a0 0x004004040408181a 0xd990c0c4688787fe 0xed990c0c4688787f

def z1368 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xbfff07f81f00ff0b 0xfbfff07f81f00ff0

def z1369 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe00400f4 0x3ff7fffffe00400f

def z1370 : W := mkw 0x0e044c4cc3e5e5f2 0x20e044c4cc3e5e5f 0x0294c4c00fe7e7ff 0xc0294c4c00fe7e7f

def z1371 : W := mkw 0x04054546408989a4 0x304054546408989a 0xdb97c4c4689f87fe 0xedb97c4c4689f87f

def z1372 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xf76fff3fe0000000 0x1f76fff3fe000000

def z1373 : W := mkw 0x807fb7b720000001 0xf807fb7b72000000 0xff6f3f3fe0000000 0x3ff6f3f3fe000000

def z1374 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xa46b3ffb80000000 0x3a46b3ffb8000000

def z1375 : W := mkw 0xd07ff7f77c001209 0xfd07ff7f77c00120 0xfffffffff800fb09 0xffffffffff800fb0

def z1376 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xfff7c707f8fff8ff 0xdfff7c707f8fff8f

def z1377 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x4808383fe70404f2 0x24808383fe70404f

def z1378 : W := mkw 0x0c05050680a9a9e4 0x30c05050680a9a9e 0xbff707c798ffffff 0xfbff707c798fffff

def z1379 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff80017ff0005 0x07f3ff80017ff000

def z1380 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0040432 0x3ff7fffffe004043

def z1381 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8041fff00cf 0xcff3ff8041fff00c

def z1382 : W := mkw 0x100002a801005608 0x4100002a80100560 0x8fd807f80f00ff0b 0xf8fd807f80f00ff0

def z1383 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xfffffffff887ffff 0xffffffffff887fff

def z1384 : W := mkw 0x04054546408989a4 0x304054546408989a 0xdff7c7c4789fffff 0xfdff7c7c4789ffff

def z1385 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x35000000076464ff 0x435000000076464f

def z1386 : W := mkw 0x6e0008089ff7e5f2 0x06e0008089ff7e5f 0x008000001fffe7ff 0xc008000001fffe7f

def z1387 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xff7ffb3fe0000000 0x3ff7ffb3fe000000

def z1388 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x0d080000076464ff 0x40d080000076464f

def z1389 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdf94c4c46887e7ff 0xfdf94c4c46887e7f

def z1390 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xff7fffffe0006009 0x7ff7fffffe000600

def z1391 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f80f00ff0a 0x38ff807f80f00ff0

def z1392 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0x7467c307f0ff78f5 0x17467c307f0ff78f

def z1393 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0x008000001f60ff0b 0xc008000001f60ff0

def z1394 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0xff7b3fffe0000000 0x3ff7b3fffe000000

def z1395 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8af807f81f00ff0a 0xb8af807f81f00ff0

def z1396 : W := mkw 0x603aaaa01e560001 0xc603aaaa01e56000 0xfffffff81ffff80f 0xffffffff81ffff80

def z1397 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xffbffcc47fff87ff 0xeffbffcc47fff87f

def z1398 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x87e807f81700ff09 0xf87e807f81700ff0

def z1399 : W := mkw 0x04044444408181a0 0x204044444408181a 0xdbb7c4c4789f87fe 0xedbb7c4c4789f87f

def z1400 : W := mkw 0x8004545560000000 0x2800454556000000 0xfd083cffe0000000 0x3fd083cffe000000

def z1401 : W := mkw 0x0e00080883e5e5f2 0x00e00080883e5e5f 0x008000000764e7ff 0x4008000000764e7f

def z1402 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xff28383ff76464ff 0xfff28383ff76464f

def z1403 : W := mkw 0x847ff7f7608989a5 0xf847ff7f7608989a 0xfffffffff89f9ffe 0xffffffffff89f9ff

def z1404 : W := mkw 0x0c054546c0a9a9e4 0x30c054546c0a9a9e 0xf7e7c707f8ffffff 0xdf7e7c707f8fffff

def z1405 : W := mkw 0x843c56f5608181a1 0x6843c56f5608181a 0xfffcffffe88787fe 0xffffcffffe88787f

def z1406 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0xfd88383fef64e7ff 0xffd88383fef64e7f

def z1407 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xc8d8ffffe80787fa 0x3c8d8ffffe80787f

def z1408 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x85000000076464ff 0x585000000076464f

def z1409 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xffffffffe88087ce 0xfffffffffe88087c

def z1410 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x246b3ffb80000000 0x1246b3ffb8000000

def z1411 : W := mkw 0x8000101120000000 0x0800010112000000 0xf000383fe0000000 0x3f000383fe000000

def z1412 : W := mkw 0x2002a80002560000 0x82002a8000256000 0x7f1ff8000fff0007 0xc7f1ff8000fff000

def z1413 : W := mkw 0x84055557608181a0 0x384055557608181a 0xffffffffe88787fe 0xfffffffffe88787f

def z1414 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0xffffffffe80487fe 0xfffffffffe80487f

def z1415 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0x7f3ff8c01fff0707 0xe7f3ff8c01fff070

def z1416 : W := mkw 0x08054546c0a8a8c4 0x308054546c0a8a8c 0xfff7c7c7f0fcfcff 0xffff7c7c7f0fcfcf

def z1417 : W := mkw 0x807af2f160000001 0xc807af2f16000000 0x6c18f8fbe0000000 0x36c18f8fbe000000

def z1418 : W := mkw 0x003fa7a600000001 0xf003fa7a60000000 0xff7fffff80000000 0x3ff7fffff8000000

def z1419 : W := mkw 0x807ff7f760000001 0xf807ff7f76000000 0x7f7ffb3fe0000000 0x17f7ffb3fe000000

def z1420 : W := mkw 0x807bb3b320000001 0xd807bb3b32000000 0x2c7b3bfb80000000 0x32c7b3bfb8000000

def z1421 : W := mkw 0x807bf3f360000001 0xd807bf3f36000000 0x247bfbfb80000000 0x1247bfbfb8000000

def z1422 : W := mkw 0x8a001019a1206452 0x08a001019a120645 0xfd08383fe70064fb 0x7fd08383fe70064f

def z1423 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe88387f8 0xbffffffffe88387f

def z1424 : W := mkw 0xe07ff7f77c120001 0xfe07ff7f77c12000 0xff7ffffff89f0006 0xfff7ffffff89f000

def z1425 : W := mkw 0x5a0008089f64765a 0x05a0008089f64765 0x000000000f6467ff 0x4000000000f6467f

def z1426 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0x8ff807f81ff8ff0f 0xf8ff807f81ff8ff0

def z1427 : W := mkw 0x04044444408181a0 0x204044444408181a 0xfff7c7c478ffffff 0xffff7c7c478fffff

def z1428 : W := mkw 0x8000101120000000 0x0800010112000000 0xb508383f80000000 0x1b508383f8000000

def z1429 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff3ff8001fff040f 0xeff3ff8001fff040

def z1430 : W := mkw 0x603aa8001e560001 0x8603aa8001e56000 0xff7fff001fff0007 0xdff7fff001fff000

def z1431 : W := mkw 0x8000101120000000 0x0800010112000000 0xffe83f3ff000f809 0xfffe83f3ff000f80

def z1432 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xa6e7070790f8f8c9 0x9a6e7070790f8f8c

def z1433 : W := mkw 0x8043b3b320000000 0xd8043b3b32000000 0x20433b3b80000000 0x120433b3b8000000

def z1434 : W := mkw 0x807ff7f760808081 0xf807ff7f76080808 0xff7fffffe08000c4 0x3ff7fffffe08000c

def z1435 : W := mkw 0x503802a81d005609 0x4503802a81d00560 0xcff8c7f81f07ff0b 0xfcff8c7f81f07ff0

def z1436 : W := mkw 0x7a0008089f76765a 0x07a0008089f76765 0x008000001fffffff 0xc008000001ffffff

def z1437 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0xffffffffe8878306 0xfffffffffe887830

def z1438 : W := mkw 0x8004141520808080 0x2800414152080808 0xff8c3c3fe08080cc 0xfff8c3c3fe08080c

def z1439 : W := mkw 0x8a001819a3646452 0x08a001819a364645 0x7d08383fe76404f7 0x67d08383fe76404f

def z1440 : W := mkw 0x847ff7f7608181a1 0xf847ff7f7608181a 0x26fffffb88838300 0x926fffffb8883830

def z1441 : W := mkw 0x8447f557608181a0 0xb8447f557608181a 0xfd0ff83fe08704fe 0x7fd0ff83fe08704f

def z1442 : W := mkw 0x804113b320000000 0x5804113b32000000 0x24483b3b80000000 0x124483b3b8000000

def z1443 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xfff707c7f8fcffff 0xffff707c7f8fcfff

def z1444 : W := mkw 0xaa001819a3766452 0x0aa001819a376645 0xfd08383fe7ff64ff 0x7fd08383fe7ff64f

def z1445 : W := mkw 0x0a00080883646452 0x00a0008088364645 0x89000000076464ff 0x689000000076464f

def z1446 : W := mkw 0x0805050680a8a8c4 0x30805050680a8a8c 0xfff7c7c798ffffcf 0xffff7c7c798ffffc

def z1447 : W := mkw 0x0801010280282844 0x1080101028028284 0x3467030390f87805 0x13467030390f8780

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z9,z5,z6]),(0,[z1,z8,z3,z4,z10,z11,z6]),(0,[z1,z8,z3,z4,z12,z13,z6])],[(0,[z1,z14,z3,z4,z5,z6,z15]),(0,[z16,z1,z8,z3,z4,z5,z6])],[(0,[z17,z1,z8,z3,z4,z5,z6]),(0,[z18,z1,z8,z3,z4,z5,z6]),(0,[z19,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z6,z20])],[(0,[z1,z8,z3,z4,z21,z6,z22]),(0,[z1,z8,z3,z23,z4,z5,z6]),(0,[z24,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z25]),(1,[z26,z1,z3,z27,z5,z6]),(0,[z1,z8,z3,z4,z12,z11,z6])],[],[(0,[z1,z28,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z29,z4,z5,z6])],[(0,[z30,z1,z8,z31,z3,z4,z6])],[(0,[z1,z8,z31,z3,z32,z4,z6]),(0,[z33,z1,z8,z3,z4,z34,z6]),(0,[z19,z1,z8,z3,z4,z34,z6]),(1,[z35,z8,z3,z4,z5,z6]),(0,[z1,z8,z36,z3,z4,z5,z6])],[(0,[z1,z8,z3,z37,z4,z12,z6])],[(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z1,z39,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z40,z6]),(0,[z41,z1,z8,z3,z5,z6,z42]),(0,[z1,z8,z31,z3,z43,z4,z6])],[(0,[z44,z1,z14,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z45,z5,z6]),(0,[z1,z46,z3,z4,z47,z5,z6])],[(0,[z48,z1,z8,z3,z4,z49,z6]),(0,[z1,z8,z36,z3,z27,z5,z6]),(0,[z1,z8,z3,z4,z12,z50,z6])],[(0,[z51,z1,z8,z3,z4,z5,z52])],[(0,[z1,z8,z3,z4,z53,z5,z6])],[(0,[z1,z54,z8,z3,z4,z5,z6]),(0,[z1,z8,z55,z3,z4,z56,z6]),(0,[z1,z8,z3,z37,z4,z34,z6]),(0,[z1,z8,z3,z57,z4,z5,z6])]],
   [[(0,[z1,z14,z3,z4,z34,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z58]),(0,[z59,z1,z8,z3,z4,z5,z6])],[(0,[z60,z1,z14,z3,z4,z5,z6]),(0,[z61,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z62,z3,z4,z5,z6])],[(1,[z1,z8,z3,z4,z63,z6]),(1,[z1,z8,z3,z4,z5,z64]),(0,[z65,z1,z8,z3,z4,z5,z66])],[(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z1,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z31,z3,z68,z4,z6]),(0,[z1,z8,z3,z4,z5,z6,z69]),(0,[z1,z8,z37,z4,z70,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z71]),(0,[z1,z8,z3,z4,z72,z34,z6]),(0,[z1,z8,z3,z4,z5,z6,z73])],[(0,[z74,z1,z8,z31,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z75,z6]),(1,[z1,z76,z3,z4,z5,z6]),(0,[z1,z8,z3,z77,z4,z5,z6])],[(0,[z1,z8,z78,z3,z4,z5,z6]),(0,[z79,z1,z8,z3,z4,z5,z6])],[(0,[z51,z1,z8,z3,z4,z56,z6]),(0,[z1,z46,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z80,z5,z6])],[(1,[z74,z2,z3,z4,z5,z6]),(0,[z0,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z81,z3,z4,z5,z6]),(0,[z60,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z6,z82]),(0,[z1,z8,z3,z4,z83,z5,z6])],[(0,[z84,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z85,z6]),(0,[z1,z8,z86,z3,z4,z5,z6])],[(0,[z1,z87,z8,z3,z4,z5,z6]),(0,[z33,z1,z3,z4,z5,z88,z6]),(0,[z1,z8,z3,z4,z89,z5,z6])],[(0,[z1,z8,z3,z4,z5,z88,z66])],[(0,[z1,z8,z3,z4,z90,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z91]),(0,[z1,z8,z92,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z93]),(0,[z1,z8,z94,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z95,z12,z6])],[(0,[z1,z14,z31,z3,z4,z5,z6]),(0,[z1,z8,z3,z96,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z97]),(0,[z60,z1,z8,z3,z4,z34,z6])],[(0,[z1,z8,z3,z98,z4,z5,z6]),(0,[z1,z8,z3,z99,z4,z5,z6]),(0,[z1,z8,z100,z3,z4,z12,z6]),(1,[z1,z8,z101,z4,z11,z6]),(0,[z1,z8,z3,z4,z102,z6,z42])]],
   [[(0,[z103,z1,z8,z3,z4,z5,z104]),(0,[z1,z8,z105,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z106,z6]),(0,[z1,z8,z31,z3,z45,z4,z6]),(0,[z1,z8,z3,z4,z5,z75,z107])],[(0,[z1,z8,z3,z4,z95,z34,z6])],[],[(0,[z1,z8,z3,z32,z108,z5,z6]),(0,[z1,z8,z36,z3,z4,z56,z6]),(0,[z51,z1,z8,z3,z4,z109,z6]),(0,[z110,z1,z8,z3,z4,z5,z6]),(0,[z111,z1,z8,z3,z4,z12,z6]),(0,[z1,z112,z8,z3,z4,z5,z6])],[(0,[z1,z8,z100,z3,z4,z34,z6]),(0,[z113,z1,z8,z3,z4,z5,z6]),(0,[z114,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z115]),(0,[z1,z8,z3,z4,z12,z6,z6])],[(0,[z1,z14,z2,z3,z4,z5,z6]),(1,[z19,z1,z8,z3,z6,z116]),(0,[z117,z1,z8,z3,z4,z12,z6])],[(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z8,z118,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z21,z6,z116])],[(0,[z119,z1,z8,z3,z4,z34,z6]),(0,[z120,z1,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z121,z6]),(0,[z1,z8,z3,z122,z4,z5,z6]),(0,[z1,z8,z31,z3,z123,z4,z6]),(1,[z1,z8,z4,z70,z5,z6])],[(0,[z1,z8,z124,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z125,z6])],[(0,[z1,z8,z3,z4,z5,z6,z126]),(0,[z19,z1,z8,z3,z4,z10,z6]),(0,[z1,z8,z3,z37,z5,z75,z6]),(0,[z127,z1,z8,z31,z3,z4,z6])],[(1,[z60,z2,z3,z4,z5,z6]),(0,[z128,z1,z14,z3,z4,z5,z6]),(0,[z48,z1,z8,z31,z3,z4,z6])],[(1,[z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z129,z42]),(0,[z26,z1,z3,z4,z27,z5,z6]),(0,[z65,z1,z8,z3,z4,z5,z6]),(0,[z130,z1,z8,z31,z3,z4,z6])],[(0,[z131,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z48,z1,z8,z132,z4,z5,z6]),(0,[z1,z8,z133,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z4,z134,z6]),(1,[z1,z8,z3,z135,z5,z6]),(1,[z1,z8,z3,z4,z12,z136])],[],[(0,[z1,z8,z3,z4,z5,z6,z137]),(0,[z1,z8,z138,z4,z5,z66,z6]),(0,[z1,z8,z31,z139,z3,z4,z6])]],
   [[(0,[z140,z1,z8,z3,z4,z5,z6])],[(0,[z1,z141,z2,z3,z4,z5,z6]),(0,[z65,z1,z8,z100,z4,z5,z6])],[(0,[z128,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z108,z5,z6]),(0,[z142,z1,z8,z3,z4,z5,z6]),(0,[z143,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z144,z12,z6]),(0,[z60,z1,z145,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z6,z146]),(0,[z1,z46,z8,z3,z4,z56,z6]),(0,[z1,z3,z45,z4,z27,z5,z6]),(0,[z1,z8,z3,z45,z4,z12,z6]),(0,[z1,z8,z147,z3,z4,z5,z6]),(0,[z148,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z149,z3,z4,z5,z6]),(0,[z150,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z151,z4,z108,z5,z6]),(1,[z1,z8,z152,z3,z4,z6]),(0,[z153,z1,z8,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z154]),(0,[z60,z8,z3,z32,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z88,z6]),(0,[z1,z8,z138,z3,z4,z6,z155])],[(0,[z74,z1,z8,z3,z4,z106,z6]),(1,[z1,z8,z3,z4,z5,z156]),(0,[z1,z8,z157,z4,z108,z5,z6]),(0,[z1,z8,z3,z4,z12,z75,z6])],[(0,[z1,z158,z8,z3,z4,z5,z6]),(0,[z41,z1,z8,z3,z4,z5,z42])],[(1,[z1,z14,z31,z3,z4,z6]),(0,[z128,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z159,z3,z4,z5,z6]),(0,[z1,z8,z145,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z144,z34,z6]),(0,[z8,z3,z4,z34,z5,z56,z6]),(0,[z1,z8,z3,z4,z5,z66,z107])],[(0,[z65,z1,z8,z4,z5,z6,z15])],[],[(0,[z1,z8,z157,z3,z4,z160,z6]),(0,[z1,z8,z161,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z162])],[(0,[z163,z1,z8,z3,z4,z5,z6]),(0,[z103,z1,z8,z3,z4,z164,z6]),(0,[z1,z8,z3,z4,z5,z165,z6]),(0,[z1,z8,z3,z4,z5,z6,z166])],[(0,[z33,z1,z14,z3,z4,z5,z6]),(0,[z1,z14,z8,z31,z3,z4,z6]),(0,[z103,z1,z8,z3,z4,z5,z129]),(0,[z1,z8,z3,z4,z5,z167,z6]),(1,[z1,z8,z3,z4,z5,z52]),(0,[z1,z8,z3,z123,z4,z12,z6])],[(0,[z1,z8,z3,z4,z5,z6,z168]),(0,[z1,z169,z8,z3,z4,z5,z6]),(0,[z19,z1,z8,z3,z4,z5,z6])]],
   [[(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z170])],[(0,[z1,z2,z101,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z104,z6])],[(1,[z48,z8,z151,z4,z5,z6]),(0,[z1,z8,z3,z171,z4,z5,z6]),(0,[z1,z8,z3,z172,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z173])],[(0,[z174,z1,z8,z3,z4,z5,z6]),(0,[z120,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z123,z4,z34,z6]),(0,[z1,z8,z175,z3,z4,z5,z6]),(0,[z1,z8,z176,z31,z3,z4,z6])],[(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z131,z1,z8,z31,z3,z4,z6]),(0,[z33,z1,z8,z3,z4,z12,z6]),(1,[z1,z8,z3,z178,z5,z6])],[(0,[z1,z8,z179,z3,z4,z5,z6]),(0,[z180,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z181,z3,z4,z5,z6]),(0,[z182,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z37,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z183,z6])],[(0,[z131,z1,z8,z132,z4,z5,z6]),(0,[z184,z1,z8,z3,z4,z5,z6]),(0,[z1,z185,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z186,z5,z6])],[(0,[z1,z2,z138,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z56,z6]),(0,[z65,z1,z8,z3,z4,z56,z6])],[(0,[z187,z1,z14,z3,z4,z5,z6]),(0,[z188,z1,z8,z3,z4,z5,z6]),(0,[z189,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z190,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z12,z10,z6])],[(0,[z1,z2,z3,z132,z4,z5,z6]),(0,[z1,z8,z191,z3,z4,z5,z6]),(0,[z1,z8,z3,z192,z4,z12,z6])],[(0,[z1,z193,z8,z3,z4,z5,z6]),(0,[z194,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z36,z3,z5,z6,z116]),(0,[z1,z195,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z196,z5,z6]),(0,[z1,z8,z3,z4,z197,z5,z6])],[(0,[z1,z8,z138,z132,z4,z5,z6]),(1,[z18,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z198,z6]),(0,[z1,z8,z3,z4,z12,z66,z6])],[(0,[z44,z1,z8,z3,z4,z5,z6])]],
   [[(0,[z199,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z200,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z75,z6]),(0,[z1,z8,z3,z201,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z22]),(0,[z1,z8,z3,z4,z5,z202,z6])],[(0,[z1,z8,z3,z203,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z6,z107])],[(0,[z1,z2,z3,z68,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z204]),(0,[z59,z1,z8,z3,z135,z5,z6]),(0,[z1,z8,z138,z3,z4,z89,z6])],[(0,[z1,z8,z31,z151,z3,z4,z6]),(0,[z1,z205,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z129,z15]),(1,[z1,z8,z3,z4,z109,z6]),(0,[z1,z8,z3,z37,z4,z6,z206])],[(1,[z1,z207,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z56,z6,z208]),(0,[z1,z8,z31,z100,z3,z4,z6]),(0,[z1,z8,z209,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z210]),(0,[z1,z8,z211,z3,z4,z5,z6])],[(0,[z103,z1,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z212,z6])],[(0,[z1,z8,z213,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z47,z34,z6]),(0,[z1,z8,z214,z3,z4,z5,z6])],[(1,[z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z6])],[(0,[z215,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z10,z5,z6])],[(0,[z1,z8,z3,z4,z216,z5,z6]),(0,[z1,z217,z8,z3,z4,z5,z6]),(0,[z1,z177,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z218,z4,z5,z6])],[(0,[z1,z8,z219,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z6,z42]),(0,[z1,z8,z3,z4,z5,z220,z6]),(0,[z1,z8,z3,z4,z5,z6,z221])],[(0,[z1,z8,z3,z222,z4,z5,z6]),(0,[z223,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z224,z3,z4,z5,z6]),(0,[z1,z7,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z34,z6,z42])]],
   [[(0,[z1,z8,z3,z4,z225,z5,z6]),(0,[z1,z8,z3,z4,z12,z5,z6])],[(0,[z1,z8,z226,z3,z4,z5,z6])],[(1,[z1,z8,z3,z4,z227,z6]),(0,[z228,z1,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z11,z5,z6]),(0,[z117,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z229,z4,z5,z6]),(0,[z230,z1,z8,z3,z4,z5,z6]),(1,[z1,z8,z231,z4,z5,z6]),(0,[z1,z8,z3,z4,z232,z5,z6]),(0,[z1,z8,z31,z3,z4,z108,z6])],[(0,[z103,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z233,z5,z6]),(1,[z1,z8,z3,z4,z6,z155])],[(0,[z1,z2,z3,z32,z4,z5,z6]),(0,[z1,z8,z3,z4,z234,z34,z6]),(0,[z59,z1,z8,z3,z4,z6,z22])],[(0,[z235,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z236,z6]),(0,[z237,z1,z8,z3,z4,z5,z6])],[(0,[z8,z2,z3,z4,z144,z5,z6]),(0,[z131,z1,z8,z3,z4,z5,z238]),(0,[z239,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z6,z129]),(0,[z41,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z240,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z241,z6]),(0,[z1,z8,z3,z4,z242,z5,z6])],[(0,[z1,z14,z3,z4,z5,z66,z6]),(0,[z1,z8,z3,z4,z34,z6,z129]),(0,[z1,z8,z157,z3,z4,z12,z6])],[(1,[z1,z2,z3,z4,z12,z6]),(0,[z1,z8,z3,z243,z4,z5,z6]),(1,[z1,z8,z3,z4,z90,z6]),(0,[z51,z1,z8,z3,z4,z216,z6]),(0,[z1,z8,z3,z244,z4,z5,z6])],[(0,[z1,z14,z3,z4,z245,z5,z6]),(1,[z1,z8,z246,z4,z5,z6])],[(0,[z247,z1,z2,z3,z4,z5,z6]),(1,[z248,z8,z3,z4,z5,z6]),(0,[z249,z1,z8,z3,z4,z5,z6]),(0,[z59,z1,z8,z3,z178,z5,z6]),(0,[z1,z8,z31,z3,z4,z6,z42])],[(0,[z1,z8,z151,z3,z4,z34,z6]),(0,[z235,z1,z224,z3,z4,z5,z6]),(0,[z120,z1,z8,z3,z250,z5,z6]),(0,[z1,z8,z3,z10,z5,z6,z116])],[(0,[z1,z8,z3,z4,z251,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z238]),(0,[z235,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z252,z6]),(0,[z1,z8,z3,z4,z253,z6,z129])],[(0,[z128,z1,z8,z3,z4,z5,z6]),(0,[z59,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z254,z6]),(0,[z1,z8,z157,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z6,z255]),(0,[z1,z8,z3,z4,z256,z5,z6])]],
   [[(0,[z1,z8,z3,z4,z144,z5,z6]),(0,[z1,z8,z3,z45,z4,z5,z6]),(0,[z257,z1,z8,z3,z4,z5,z6])],[(1,[z1,z8,z3,z250,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z258,z1,z8,z3,z4,z5,z6])],[(0,[z1,z46,z8,z3,z4,z47,z6]),(0,[z1,z8,z259,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z22])],[(0,[z235,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z260,z3,z4,z5,z6])],[(1,[z1,z8,z3,z29,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z14,z7,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z6,z129]),(0,[z1,z261,z8,z3,z4,z5,z6])],[(0,[z262,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z4,z108,z5,z66,z6])],[(0,[z84,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z10,z56,z6])],[(2,[z2,z3,z4,z56,z6]),(0,[z1,z263,z8,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z264,z5,z6]),(0,[z1,z248,z8,z3,z4,z5,z6]),(0,[z1,z8,z100,z36,z3,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z265]),(0,[z33,z266,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z267,z6]),(0,[z1,z8,z3,z268,z4,z5,z6])],[(0,[z1,z8,z3,z4,z12,z56,z6]),(0,[z1,z8,z3,z4,z269,z5,z6]),(0,[z1,z270,z3,z4,z5,z6,z107])],[(0,[z1,z14,z101,z3,z4,z5,z6]),(1,[z1,z8,z179,z4,z5,z6]),(0,[z271,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z272,z5,z6]),(1,[z1,z193,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z273,z6]),(0,[z19,z1,z8,z246,z4,z5,z6])],[(0,[z1,z14,z3,z4,z5,z6,z274]),(1,[z60,z8,z3,z32,z5,z6])]],
   [[(0,[z235,z8,z3,z4,z5,z56,z6])],[(1,[z2,z3,z132,z4,z5,z6]),(0,[z131,z1,z8,z3,z4,z275,z6]),(0,[z1,z8,z3,z4,z276,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z277])],[(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z270,z14,z3,z4,z5,z6]),(0,[z33,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z278,z3,z4,z5,z6])],[],[(0,[z1,z14,z138,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z279,z6]),(1,[z1,z8,z3,z4,z5,z58]),(0,[z1,z8,z3,z4,z5,z280,z6]),(1,[z1,z8,z3,z4,z89,z6]),(0,[z19,z1,z8,z3,z5,z6,z116])],[(0,[z1,z8,z3,z4,z88,z56,z6]),(0,[z120,z103,z8,z3,z4,z5,z6])],[(0,[z1,z8,z76,z3,z4,z5,z6]),(0,[z281,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z282,z5,z6]),(0,[z1,z8,z3,z4,z283,z5,z6]),(0,[z1,z8,z3,z4,z284,z5,z6])],[(0,[z1,z8,z3,z4,z56,z6,z15]),(1,[z285,z1,z3,z4,z21,z6])],[(0,[z1,z14,z3,z132,z4,z5,z6]),(0,[z286,z1,z14,z3,z4,z5,z6]),(0,[z48,z8,z151,z3,z4,z5,z6]),(1,[z235,z8,z3,z4,z56,z6]),(0,[z1,z8,z124,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z34,z34,z6]),(0,[z1,z8,z3,z4,z34,z6,z15]),(0,[z1,z8,z287,z3,z4,z5,z6])],[(0,[z288,z1,z14,z3,z4,z5,z6]),(0,[z1,z270,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z192,z4,z5,z6])],[(0,[z1,z8,z3,z203,z4,z5,z6]),(0,[z289,z1,z8,z3,z4,z5,z6])],[],[(1,[z1,z177,z3,z45,z5,z6]),(0,[z1,z8,z3,z290,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z21,z6])],[(0,[z1,z291,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z72,z5,z6]),(0,[z51,z1,z8,z31,z3,z4,z6])],[(0,[z1,z270,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z292,z6])]],
   [[(0,[z74,z0,z8,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z56,z6]),(0,[z1,z14,z3,z68,z4,z5,z6]),(0,[z26,z293,z8,z3,z4,z5,z6]),(0,[z1,z294,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z295,z6]),(0,[z1,z296,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z108,z56,z6]),(0,[z285,z1,z46,z3,z4,z5,z6])],[(0,[z1,z46,z2,z3,z4,z5,z6]),(0,[z1,z8,z297,z3,z4,z5,z6]),(0,[z1,z8,z298,z3,z4,z5,z6])],[(0,[z33,z1,z8,z3,z4,z5,z88]),(0,[z65,z1,z8,z138,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z299]),(0,[z300,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z301,z138,z3,z5,z6])],[(0,[z286,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z31,z3,z4,z6,z15]),(0,[z302,z1,z8,z3,z4,z5,z6])],[(0,[z288,z1,z8,z3,z4,z34,z6])],[(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z56,z6]),(0,[z303,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z304,z3,z4,z5,z6]),(0,[z1,z8,z305,z3,z4,z5,z6])],[(0,[z60,z1,z8,z3,z4,z5,z6]),(0,[z128,z1,z8,z3,z4,z5,z64]),(0,[z51,z1,z8,z68,z4,z5,z6]),(1,[z1,z8,z3,z4,z6,z91])],[(0,[z306,z1,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z307,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z308])],[(0,[z309,z1,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z216,z6]),(0,[z26,z1,z177,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z310,z6]),(0,[z26,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z95,z5,z6]),(0,[z30,z1,z8,z31,z3,z4,z5])],[(0,[z1,z8,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z106,z6]),(0,[z1,z8,z3,z4,z234,z5,z6]),(0,[z311,z1,z8,z3,z4,z5,z6])],[(0,[z41,z1,z14,z3,z4,z5,z6]),(0,[z19,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z312])],[(0,[z1,z8,z3,z4,z5,z6,z146]),(0,[z1,z8,z100,z3,z4,z5,z6]),(0,[z1,z8,z31,z157,z3,z4,z6]),(1,[z41,z1,z8,z3,z5,z42])]],
   [[(1,[z1,z8,z3,z4,z49,z6])],[(0,[z1,z8,z3,z4,z313,z5,z6]),(0,[z1,z314,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z315])],[(0,[z1,z14,z3,z32,z4,z5,z6]),(0,[z119,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z100,z151,z4,z5,z6]),(0,[z1,z8,z3,z4,z316,z5,z6]),(0,[z103,z1,z8,z3,z4,z12,z6]),(0,[z59,z1,z8,z101,z4,z5,z6]),(1,[z30,z1,z8,z31,z3,z4])],[(1,[z84,z2,z3,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z8,z3,z32,z4,z144,z5,z6]),(0,[z120,z1,z8,z231,z4,z5,z6]),(0,[z26,z1,z8,z3,z4,z12,z6]),(0,[z317,z1,z8,z3,z4,z5,z6]),(0,[z59,z1,z8,z31,z3,z4,z6]),(0,[z318,z1,z8,z3,z4,z5,z6])],[(0,[z1,z319,z8,z3,z4,z5,z6]),(0,[z111,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z37,z4,z56,z6]),(0,[z1,z8,z3,z4,z320,z5,z6]),(0,[z41,z1,z8,z3,z4,z12,z6])],[(0,[z1,z8,z321,z3,z4,z5,z6]),(0,[z26,z1,z8,z240,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(1,[z131,z8,z132,z4,z5,z6]),(0,[z1,z8,z322,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z323])],[(0,[z1,z8,z3,z4,z5,z6,z324]),(0,[z1,z46,z8,z3,z4,z21,z6]),(1,[z1,z8,z147,z3,z4,z6]),(0,[z325,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z326,z5,z6])],[(0,[z1,z8,z3,z4,z5,z327,z6]),(0,[z26,z1,z8,z3,z4,z34,z6]),(1,[z1,z8,z3,z4,z328,z6]),(0,[z1,z8,z3,z4,z5,z88,z75]),(0,[z1,z8,z3,z123,z4,z10,z6])],[(0,[z329,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z151,z3,z4,z12,z6]),(1,[z51,z1,z68,z4,z5,z6]),(0,[z1,z46,z8,z31,z3,z4,z6])],[(0,[z235,z1,z8,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z4,z5,z125])],[(0,[z330,z1,z8,z3,z4,z5,z6])],[],[(0,[z1,z8,z3,z27,z108,z5,z6]),(0,[z1,z8,z3,z4,z12,z21,z6])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z331])]],
   [[(0,[z1,z8,z3,z4,z5,z6,z332])],[],[(0,[z333,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z10,z6,z22])],[(1,[z0,z14,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z11,z6])],[(0,[z1,z14,z3,z4,z27,z5,z6]),(0,[z60,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z36,z3,z123,z5,z6])],[(0,[z1,z8,z3,z4,z5,z334,z6])],[(0,[z1,z8,z3,z335,z4,z5,z6]),(0,[z1,z8,z336,z3,z4,z34,z6])],[(0,[z337,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z338,z6]),(0,[z1,z8,z3,z4,z5,z339,z6])],[(0,[z285,z340,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z10,z47,z6])],[(0,[z48,z8,z2,z3,z4,z5,z6]),(0,[z19,z1,z8,z3,z4,z6,z116]),(0,[z1,z8,z341,z3,z4,z5,z6])],[(0,[z120,z1,z342,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z66,z129]),(0,[z1,z8,z3,z343,z4,z5,z6])],[(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z8,z100,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z344,z34,z6]),(0,[z120,z1,z8,z31,z3,z4,z6])],[(0,[z1,z8,z3,z4,z345,z5,z6]),(0,[z1,z8,z3,z32,z5,z6,z42]),(1,[z1,z205,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z47,z6]),(0,[z1,z8,z101,z4,z108,z5,z6]),(0,[z1,z8,z138,z3,z320,z5,z6])],[(0,[z120,z1,z346,z3,z4,z5,z6]),(1,[z1,z8,z100,z36,z5,z6]),(0,[z1,z347,z8,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z1,z14,z55,z3,z4,z5,z6]),(1,[z1,z342,z3,z4,z5,z6]),(0,[z348,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z123,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z349,z6]),(0,[z1,z8,z3,z4,z350,z5,z6])],[(0,[z1,z8,z3,z351,z4,z5,z6]),(0,[z1,z352,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z22,z116]),(0,[z65,z1,z8,z31,z3,z4,z6]),(1,[z1,z8,z31,z3,z4,z6])]],
   [[(0,[z353,z1,z8,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z108,z5,z6]),(0,[z354,z1,z8,z3,z4,z5,z6]),(0,[z355,z1,z8,z3,z4,z5,z6]),(0,[z1,z185,z8,z3,z4,z5,z6]),(1,[z1,z346,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z356])],[(0,[z1,z8,z3,z4,z34,z6,z357]),(0,[z358,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z102,z5,z6]),(1,[z1,z8,z3,z37,z5,z75])],[(1,[z1,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z359,z6]),(0,[z1,z8,z360,z3,z4,z6,z129]),(0,[z285,z1,z3,z4,z5,z21,z6]),(0,[z361,z1,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z123,z10,z6])],[(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z362,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z363]),(0,[z1,z8,z3,z4,z364,z5,z6]),(0,[z365,z1,z8,z31,z3,z4,z6])],[(0,[z0,z60,z8,z3,z4,z5,z6]),(0,[z48,z1,z366,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z121,z5,z6]),(0,[z51,z1,z7,z3,z4,z5,z6]),(1,[z1,z8,z157,z108,z5,z6])],[(0,[z367,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z368,z5,z6]),(0,[z1,z8,z3,z369,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z75,z104]),(0,[z370,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z371,z5,z6])],[(0,[z1,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z136]),(0,[z1,z8,z38,z3,z4,z5,z6]),(0,[z103,z1,z76,z3,z4,z5,z6])],[(1,[z120,z2,z3,z4,z5,z6]),(0,[z1,z8,z372,z37,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z42]),(0,[z1,z8,z3,z4,z5,z6,z373])],[(0,[z1,z8,z3,z374,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z164,z6])],[(0,[z1,z8,z3,z4,z5,z6,z375]),(0,[z1,z8,z3,z4,z376,z5,z6])],[],[(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z128,z1,z8,z3,z4,z56,z6]),(1,[z1,z8,z3,z4,z377,z6])],[(0,[z1,z8,z378,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z144,z56,z6]),(0,[z1,z8,z3,z4,z379,z5,z6]),(0,[z1,z8,z3,z45,z4,z56,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z104,z6]),(0,[z187,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z380,z5,z6]),(0,[z1,z381,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z5,z6,z22]),(0,[z1,z8,z3,z382,z4,z5,z6]),(0,[z1,z8,z301,z3,z4,z5,z6])],[(1,[z1,z383,z3,z4,z5,z6]),(0,[z1,z8,z3,z384,z4,z5,z6]),(0,[z1,z8,z385,z3,z4,z5,z6]),(0,[z1,z8,z386,z3,z4,z5,z6]),(1,[z33,z1,z3,z4,z5,z88]),(0,[z1,z8,z31,z3,z4,z12,z6])],[(0,[z1,z14,z36,z3,z4,z5,z6]),(0,[z1,z8,z387,z3,z4,z5,z6]),(0,[z288,z1,z8,z3,z4,z12,z6]),(1,[z1,z8,z31,z3,z4,z12])],[(0,[z388,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z129]),(0,[z1,z8,z3,z4,z47,z5,z6])],[(0,[z389,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z36,z3,z144,z5,z6]),(0,[z1,z7,z8,z31,z3,z4,z6]),(0,[z1,z8,z147,z3,z4,z6,z107]),(0,[z1,z390,z8,z3,z4,z5,z6]),(1,[z1,z8,z372,z4,z5,z6])],[(0,[z84,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z36,z3,z32,z5,z6]),(0,[z1,z8,z3,z4,z56,z75,z6]),(0,[z1,z8,z391,z3,z4,z5,z6]),(0,[z392,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z393,z6])],[(0,[z1,z8,z3,z4,z34,z75,z6]),(0,[z1,z8,z31,z3,z4,z34,z6])],[(0,[z1,z8,z141,z3,z4,z5,z6]),(0,[z51,z1,z8,z3,z4,z5,z85]),(0,[z1,z8,z394,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z395,z5,z6]),(0,[z1,z8,z3,z123,z4,z56,z6]),(0,[z1,z8,z3,z4,z34,z6,z396]),(0,[z1,z8,z3,z4,z12,z6,z116]),(0,[z1,z8,z397,z3,z4,z12,z6])],[(0,[z1,z8,z3,z398,z4,z5,z6]),(0,[z1,z8,z2,z3,z4,z12,z6]),(0,[z285,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z351,z4,z56,z6]),(0,[z1,z8,z3,z4,z11,z34,z6]),(0,[z103,z1,z8,z3,z4,z121,z6])],[(0,[z1,z8,z3,z4,z399,z5,z6])],[(0,[z1,z8,z400,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z401,z5,z6])],[(0,[z1,z14,z3,z4,z5,z402,z6]),(0,[z1,z8,z3,z4,z5,z6,z403])],[(0,[z103,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z66,z104]),(0,[z1,z8,z4,z108,z5,z6,z22]),(0,[z1,z8,z3,z4,z5,z404,z6])]],
   [[(0,[z1,z14,z177,z3,z4,z5,z6]),(0,[z51,z1,z3,z68,z4,z5,z6]),(0,[z1,z7,z8,z68,z4,z5,z6])],[(0,[z1,z8,z2,z3,z4,z34,z6]),(0,[z33,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z56,z6,z405]),(0,[z1,z8,z3,z4,z70,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z406]),(0,[z1,z8,z3,z4,z12,z5,z136])],[(0,[z1,z2,z3,z4,z5,z6,z107]),(1,[z1,z8,z3,z4,z5,z238]),(0,[z285,z1,z8,z3,z4,z12,z6]),(0,[z41,z1,z8,z3,z4,z5,z6])],[],[(0,[z1,z8,z3,z4,z407,z5,z6]),(0,[z1,z8,z31,z101,z3,z4,z6])],[(0,[z1,z8,z3,z3,z4,z5,z6]),(1,[z1,z408,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z75,z129]),(0,[z1,z8,z3,z4,z12,z88,z6])],[(0,[z74,z8,z2,z3,z4,z5,z6]),(0,[z120,z1,z8,z3,z4,z252,z6]),(0,[z409,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z151,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z47,z6,z22]),(0,[z1,z8,z3,z4,z5,z410,z6]),(0,[z33,z18,z8,z3,z4,z5,z6]),(0,[z33,z1,z8,z3,z4,z198,z6]),(0,[z1,z8,z3,z4,z5,z6,z411])],[(0,[z412,z1,z8,z3,z4,z34,z6]),(0,[z285,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z413,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z414]),(0,[z1,z8,z3,z4,z5,z415,z6]),(0,[z1,z8,z3,z37,z4,z377,z6])],[(0,[z1,z8,z3,z4,z416,z5,z6]),(1,[z1,z8,z3,z4,z417,z6]),(0,[z333,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z157,z3,z4,z5,z6]),(0,[z1,z8,z418,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z136])],[(0,[z235,z84,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z252,z6]),(0,[z51,z1,z8,z55,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z419])],[(0,[z1,z420,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z5,z6])],[(0,[z131,z1,z8,z3,z421,z5,z6]),(0,[z84,z1,z205,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z422,z5,z6]),(0,[z423,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z100,z157,z4,z5,z6]),(1,[z1,z8,z3,z320,z5,z6])],[(0,[z30,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z336,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z10,z21,z6])],[(0,[z1,z8,z3,z4,z5,z6,z424]),(0,[z59,z1,z8,z4,z5,z6,z22]),(0,[z1,z8,z3,z4,z5,z425,z6])],[(0,[z1,z2,z3,z4,z12,z5,z6]),(0,[z1,z8,z3,z4,z56,z66,z6]),(0,[z84,z1,z8,z31,z3,z4,z6]),(1,[z1,z8,z301,z3,z5,z6])]],
   [[(0,[z1,z8,z3,z4,z47,z56,z6]),(0,[z1,z8,z152,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z66,z6]),(0,[z1,z8,z3,z4,z426,z5,z6]),(0,[z1,z8,z36,z3,z45,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z427])],[(0,[z428,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z429,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z104,z6])],[],[(0,[z120,z0,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z156,z6]),(0,[z1,z8,z3,z4,z5,z6,z15])],[(0,[z1,z430,z8,z3,z4,z5,z6]),(0,[z30,z1,z8,z3,z4,z12,z6])],[(0,[z1,z14,z3,z4,z5,z6,z116]),(0,[z1,z8,z151,z4,z5,z6,z15]),(1,[z1,z8,z3,z4,z380,z6]),(0,[z1,z8,z101,z3,z4,z34,z6]),(0,[z431,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z432]),(0,[z1,z177,z8,z3,z45,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z433]),(0,[z434,z1,z8,z3,z4,z5,z6])],[(0,[z0,z14,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z435,z4,z5,z6]),(0,[z1,z8,z3,z4,z436,z6,z15])],[],[(0,[z1,z8,z3,z4,z49,z5,z6]),(1,[z59,z1,z8,z4,z6,z22])],[(0,[z1,z8,z3,z144,z108,z5,z6]),(0,[z1,z8,z3,z4,z437,z5,z6])],[(0,[z30,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z31,z3,z4,z10,z6]),(0,[z237,z1,z8,z31,z3,z4,z6])],[(1,[z1,z8,z3,z4,z275,z6]),(0,[z438,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z439,z4,z5,z6]),(0,[z1,z8,z31,z138,z3,z4,z6])],[(1,[z48,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z440,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z135,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z66,z6]),(0,[z1,z8,z3,z37,z4,z5,z75])],[(0,[z0,z1,z14,z3,z4,z5,z6]),(0,[z51,z1,z8,z3,z413,z5,z6])],[(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z131,z1,z441,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z442,z6]),(0,[z1,z443,z8,z3,z4,z5,z6])]],
   [[(0,[z1,z14,z3,z4,z5,z88,z6]),(1,[z1,z8,z3,z4,z279,z6]),(0,[z1,z8,z3,z45,z108,z5,z6]),(0,[z41,z1,z8,z36,z3,z5,z6])],[(0,[z131,z1,z54,z3,z4,z5,z6]),(0,[z444,z1,z8,z3,z4,z5,z6]),(0,[z8,z3,z4,z5,z104,z6,z129])],[(0,[z128,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z34,z5,z6]),(0,[z1,z445,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z12,z6,z107])],[(0,[z1,z14,z3,z4,z5,z6,z136]),(0,[z128,z1,z193,z3,z4,z5,z6]),(0,[z446,z1,z8,z3,z4,z5,z6]),(0,[z41,z1,z8,z3,z37,z5,z6]),(0,[z1,z8,z447,z3,z4,z5,z6])],[(0,[z448,z1,z8,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z104,z6]),(0,[z0,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z157,z3,z4,z56,z6]),(0,[z120,z8,z3,z4,z5,z6,z129]),(0,[z449,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z208]),(0,[z1,z8,z3,z4,z5,z6,z450]),(0,[z451,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z253,z5,z6])],[(0,[z0,z8,z3,z132,z4,z5,z6]),(0,[z1,z8,z3,z4,z452,z5,z6]),(0,[z453,z1,z8,z3,z4,z5,z6]),(0,[z143,z1,z8,z31,z3,z4,z6])],[(0,[z454,z1,z8,z3,z4,z5,z6]),(0,[z1,z270,z8,z3,z4,z5,z6]),(1,[z1,z8,z139,z3,z4,z6])],[(0,[z235,z1,z8,z3,z4,z56,z6]),(1,[z1,z8,z3,z4,z5,z85]),(0,[z1,z455,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z102,z6])],[(0,[z0,z1,z8,z3,z4,z34,z6]),(1,[z1,z8,z3,z4,z456,z6]),(0,[z1,z8,z3,z4,z377,z5,z6]),(0,[z1,z8,z31,z447,z3,z4,z6])],[(0,[z1,z14,z3,z4,z5,z104,z6]),(0,[z1,z14,z3,z4,z5,z21,z6]),(1,[z1,z457,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z458]),(0,[z459,z1,z8,z3,z4,z5,z6])],[],[(0,[z286,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z421,z4,z5,z6]),(0,[z1,z8,z460,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z461]),(0,[z1,z8,z31,z3,z4,z5,z6])]],
   [[(0,[z288,z1,z8,z3,z4,z5,z6]),(1,[z1,z462,z3,z4,z5,z6]),(1,[z1,z445,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z463])],[(0,[z48,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z464,z5,z6]),(1,[z1,z8,z3,z4,z436,z6])],[(0,[z1,z8,z4,z5,z66,z6,z15])],[(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z465]),(0,[z1,z8,z3,z4,z5,z466,z6]),(0,[z1,z8,z101,z3,z4,z11,z6])],[(0,[z1,z8,z31,z36,z3,z4,z6]),(0,[z1,z8,z3,z4,z5,z6,z467])],[(0,[z1,z468,z14,z3,z4,z5,z6]),(0,[z84,z1,z408,z3,z4,z5,z6]),(0,[z1,z8,z469,z3,z4,z5,z6]),(0,[z33,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z100,z4,z5,z66,z6]),(0,[z19,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z470,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z471])],[(0,[z1,z472,z8,z3,z4,z5,z6]),(0,[z1,z473,z8,z3,z4,z5,z6])],[(0,[z1,z55,z3,z68,z4,z5,z6]),(0,[z1,z8,z397,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z6,z6])],[(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z1,z8,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z474,z6]),(0,[z48,z1,z8,z3,z4,z12,z6]),(0,[z475,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z476])],[(0,[z1,z8,z360,z3,z4,z5,z6])],[(0,[z1,z8,z3,z477,z4,z5,z6]),(0,[z1,z270,z8,z3,z4,z5,z88]),(0,[z1,z8,z3,z478,z4,z5,z6]),(0,[z1,z8,z479,z3,z4,z5,z6])],[(0,[z480,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z481,z12,z6])],[(0,[z1,z8,z3,z482,z4,z5,z6])],[],[(0,[z1,z14,z3,z4,z5,z6,z107]),(0,[z48,z1,z8,z3,z4,z34,z6])],[]],
   [[(0,[z355,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z483]),(0,[z33,z1,z270,z3,z4,z5,z6])],[(0,[z1,z8,z3,z250,z4,z5,z6])],[(1,[z1,z270,z3,z4,z5,z107])],[(0,[z1,z2,z3,z200,z4,z5,z6]),(0,[z293,z1,z8,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z4,z5,z6]),(0,[z484,z1,z8,z3,z4,z12,z6]),(0,[z1,z294,z8,z31,z3,z4,z6])],[(0,[z1,z14,z14,z3,z4,z5,z6]),(0,[z1,z485,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z246,z4,z5,z6])],[(1,[z1,z14,z3,z4,z12,z6]),(0,[z1,z270,z8,z3,z4,z56,z6])],[(0,[z1,z8,z3,z4,z27,z12,z6])],[(0,[z84,z0,z8,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z27,z5,z6]),(0,[z1,z8,z486,z3,z4,z5,z6])],[(0,[z1,z314,z8,z3,z4,z5,z6]),(0,[z8,z151,z3,z132,z4,z5,z6]),(0,[z487,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z4,z11,z5,z6,z22]),(0,[z1,z8,z31,z3,z4,z75,z6])],[(0,[z103,z8,z3,z4,z5,z104,z6]),(0,[z488,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z183,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z131,z1,z14,z3,z4,z5,z6]),(1,[z1,z14,z3,z4,z34,z6]),(0,[z1,z489,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z12,z5,z6]),(0,[z1,z14,z8,z3,z4,z12,z6]),(0,[z128,z8,z3,z4,z144,z5,z6]),(0,[z60,z1,z8,z31,z3,z4,z6])],[(0,[z1,z8,z3,z4,z27,z34,z6]),(0,[z1,z8,z490,z3,z4,z5,z6])],[(0,[z128,z1,z2,z3,z4,z5,z6]),(0,[z491,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z492,z3,z4,z5,z6]),(0,[z1,z493,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z357]),(0,[z1,z8,z3,z4,z95,z104,z6]),(0,[z494,z1,z8,z3,z4,z5,z6])],[(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z8,z495,z3,z4,z5,z6]),(0,[z1,z8,z3,z496,z4,z5,z6]),(0,[z19,z1,z8,z3,z123,z5,z6])],[(0,[z497,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z342,z3,z4,z5,z6]),(1,[z1,z8,z3,z413,z5,z6]),(0,[z1,z8,z100,z3,z108,z5,z6]),(0,[z1,z8,z3,z4,z498,z5,z6]),(0,[z1,z8,z213,z31,z3,z4,z6])]],
   [[(0,[z0,z1,z8,z3,z4,z474,z6]),(0,[z1,z499,z8,z3,z4,z5,z6])],[(0,[z1,z14,z8,z3,z4,z34,z6]),(1,[z1,z8,z3,z4,z334,z6]),(0,[z1,z8,z100,z101,z4,z5,z6]),(0,[z1,z8,z3,z4,z500,z12,z6])],[(0,[z131,z1,z8,z3,z4,z12,z6]),(0,[z1,z7,z8,z55,z4,z5,z6]),(0,[z1,z8,z3,z4,z501,z5,z6]),(0,[z502,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z503,z6]),(0,[z1,z8,z101,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z456,z6,z42])],[(0,[z1,z8,z3,z4,z5,z504,z6])],[(1,[z2,z3,z4,z144,z5,z6])],[(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z344,z5,z6]),(0,[z131,z8,z3,z132,z4,z5,z6])],[(0,[z505,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z229,z4,z5,z6]),(0,[z1,z8,z132,z4,z108,z5,z6]),(0,[z506,z1,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z95,z6]),(1,[z1,z8,z3,z4,z134,z6]),(0,[z1,z8,z3,z4,z5,z507,z6])],[(1,[z1,z31,z2,z3,z4,z6]),(0,[z508,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z138,z3,z4,z5,z15])],[(0,[z131,z1,z8,z3,z4,z34,z6]),(0,[z128,z1,z8,z3,z4,z380,z6]),(1,[z1,z8,z336,z3,z4,z6]),(0,[z1,z8,z3,z123,z4,z6,z116])],[(0,[z1,z8,z3,z108,z5,z75,z6]),(0,[z1,z8,z138,z3,z4,z12,z6]),(0,[z509,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z68,z4,z108,z5,z6])],[],[(0,[z1,z8,z510,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z160,z6])],[(0,[z1,z8,z3,z132,z4,z12,z6]),(0,[z511,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z512,z3,z4,z5,z6])],[(0,[z74,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z513,z6]),(0,[z103,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z514,z6]),(0,[z1,z8,z515,z3,z4,z5,z6]),(0,[z285,z35,z8,z3,z4,z5,z6])],[(0,[z26,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z138,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z6,z516])]],
   [[(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z108,z5,z6]),(0,[z1,z8,z55,z4,z108,z5,z6])],[(0,[z41,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z517,z4,z5,z6]),(0,[z518,z1,z8,z3,z4,z5,z6])],[(0,[z74,z1,z8,z3,z4,z313,z6]),(0,[z1,z2,z3,z4,z144,z5,z6]),(0,[z1,z8,z3,z519,z4,z5,z6]),(0,[z520,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z132,z4,z34,z6]),(1,[z1,z8,z3,z4,z280,z6])],[(1,[z1,z8,z521,z4,z5,z6])],[(0,[z74,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z6,z522]),(0,[z1,z8,z3,z4,z5,z6,z396]),(0,[z1,z8,z3,z68,z4,z12,z6]),(0,[z523,z1,z8,z3,z4,z5,z6]),(0,[z524,z1,z8,z3,z4,z5,z6]),(0,[z525,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z151,z3,z4,z56,z6]),(0,[z1,z346,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z276,z6]),(1,[z1,z8,z3,z4,z242,z6]),(0,[z1,z8,z3,z4,z5,z88,z42]),(0,[z1,z8,z3,z4,z5,z6,z526])],[(0,[z1,z527,z14,z3,z4,z5,z6])],[(0,[z120,z8,z2,z3,z4,z5,z6]),(0,[z528,z1,z8,z3,z4,z5,z6]),(0,[z1,z493,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z29,z4,z6,z15]),(0,[z1,z8,z3,z4,z5,z6,z162])],[(0,[z1,z8,z3,z4,z5,z212,z6]),(0,[z1,z177,z8,z3,z4,z12,z6])],[(0,[z74,z1,z8,z3,z4,z34,z6]),(0,[z0,z1,z8,z3,z4,z529,z6]),(0,[z1,z8,z3,z68,z4,z34,z6]),(0,[z1,z8,z3,z4,z530,z5,z6])],[(0,[z1,z8,z3,z4,z531,z5,z6]),(0,[z532,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z533,z3,z4,z5,z6])],[(0,[z1,z2,z3,z123,z4,z5,z6]),(0,[z1,z8,z3,z534,z4,z5,z6]),(0,[z1,z8,z3,z535,z4,z5,z6]),(0,[z1,z8,z3,z4,z536,z5,z6])],[(0,[z537,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z538,z6]),(0,[z1,z8,z3,z4,z47,z6,z116]),(0,[z1,z8,z3,z4,z242,z6,z107]),(0,[z1,z8,z3,z123,z108,z5,z6])],[(0,[z128,z1,z457,z3,z4,z5,z6]),(0,[z1,z8,z152,z3,z4,z56,z6]),(0,[z539,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z540,z6]),(0,[z1,z8,z3,z4,z541,z12,z6])]],
   [[(0,[z1,z177,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z13,z6])],[],[],[(1,[z8,z3,z4,z34,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z542])],[(0,[z1,z14,z3,z37,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z543])],[(0,[z1,z67,z8,z3,z4,z5,z6]),(0,[z48,z1,z8,z3,z4,z5,z6]),(0,[z60,z1,z8,z3,z4,z417,z6]),(0,[z1,z8,z157,z3,z4,z6,z91]),(0,[z1,z8,z36,z4,z108,z5,z6]),(0,[z1,z8,z3,z4,z11,z5,z6])],[(1,[z0,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z544,z5,z6]),(1,[z1,z8,z545,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z6,z299]),(0,[z1,z7,z55,z3,z4,z5,z6])],[(0,[z1,z8,z3,z37,z144,z5,z6]),(0,[z1,z8,z3,z32,z4,z12,z6]),(0,[z1,z8,z3,z4,z56,z6,z22]),(0,[z546,z1,z8,z3,z4,z5,z6])],[(0,[z48,z1,z8,z151,z4,z5,z6]),(0,[z1,z8,z3,z37,z32,z5,z6]),(0,[z547,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z6,z22]),(0,[z1,z8,z3,z4,z481,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z548])],[(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z1,z8,z3,z4,z5,z6,z549]),(0,[z1,z8,z3,z4,z34,z550,z6]),(0,[z1,z8,z3,z551,z4,z5,z6])],[(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z0,z8,z3,z4,z5,z56,z6]),(1,[z1,z366,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z64]),(0,[z1,z8,z3,z4,z5,z552,z6]),(0,[z1,z8,z3,z4,z5,z66,z6]),(0,[z1,z8,z31,z3,z37,z4,z6])],[(0,[z553,z1,z8,z3,z4,z5,z6]),(0,[z554,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z50,z6])],[(0,[z1,z8,z3,z32,z4,z34,z6])],[],[(0,[z1,z8,z555,z3,z4,z5,z6]),(0,[z1,z8,z3,z43,z4,z5,z6])]],
   [[(0,[z1,z8,z3,z4,z556,z5,z6]),(0,[z1,z8,z3,z4,z56,z56,z6]),(0,[z444,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z231,z4,z5,z6]),(0,[z33,z1,z8,z3,z4,z5,z107])],[(0,[z1,z8,z3,z4,z34,z56,z6]),(0,[z1,z557,z8,z3,z4,z5,z6]),(0,[z1,z8,z100,z36,z4,z5,z6]),(0,[z558,z1,z8,z3,z4,z5,z6])],[(0,[z412,z1,z8,z3,z4,z5,z6]),(0,[z285,z1,z8,z3,z4,z5,z6])],[(0,[z559,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z1,z8,z3,z560,z4,z5,z6])],[(1,[z1,z8,z96,z4,z5,z6])],[(0,[z1,z8,z3,z4,z198,z5,z6]),(0,[z1,z8,z31,z3,z4,z6,z22])],[(0,[z131,z1,z8,z3,z544,z5,z6]),(1,[z1,z8,z3,z421,z5,z6]),(0,[z60,z1,z8,z3,z144,z5,z6]),(0,[z561,z1,z8,z3,z4,z5,z6])],[(0,[z60,z1,z8,z3,z32,z5,z6]),(0,[z84,z8,z3,z4,z34,z5,z6]),(0,[z1,z562,z8,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z12,z5])],[(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z563,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z564]),(0,[z1,z8,z372,z3,z4,z5,z6]),(0,[z389,z1,z8,z31,z3,z4,z6])],[(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z120,z1,z8,z3,z4,z5,z104]),(0,[z565,z1,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z10,z5,z6]),(1,[z120,z8,z3,z4,z5,z129]),(0,[z566,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z567,z5,z6]),(0,[z1,z8,z31,z3,z4,z47,z6])],[(0,[z1,z8,z3,z4,z5,z568,z6]),(0,[z1,z8,z3,z4,z5,z569,z6])],[(0,[z1,z14,z3,z222,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z5,z6]),(0,[z51,z570,z8,z3,z4,z5,z6])],[(0,[z1,z8,z545,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z56,z6]),(0,[z1,z8,z36,z157,z3,z5,z6])],[(0,[z1,z14,z226,z3,z4,z5,z6]),(0,[z131,z1,z8,z3,z4,z5,z6]),(0,[z288,z1,z8,z3,z4,z56,z6]),(0,[z571,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z101,z3,z4,z5,z6])]],
   [[(0,[z1,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z572,z5,z6]),(0,[z1,z8,z3,z4,z5,z88,z15])],[(0,[z1,z8,z3,z4,z5,z6,z274]),(0,[z573,z1,z8,z3,z4,z5,z6])],[(0,[z8,z2,z3,z132,z4,z5,z6]),(0,[z131,z1,z8,z151,z4,z5,z6]),(0,[z1,z8,z574,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z5,z575]),(0,[z1,z8,z576,z3,z4,z5,z6]),(0,[z103,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z577,z5,z6]),(0,[z41,z1,z8,z3,z108,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z578])],[(0,[z1,z8,z55,z3,z4,z12,z6]),(0,[z579,z1,z8,z3,z4,z5,z6])],[(0,[z51,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z580,z6]),(0,[z26,z1,z8,z179,z4,z5,z6]),(0,[z30,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z581,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z6]),(0,[z582,z1,z8,z3,z4,z5,z6]),(0,[z41,z1,z8,z31,z3,z4,z6])],[(0,[z1,z8,z3,z4,z583,z5,z6])],[(0,[z1,z8,z2,z3,z4,z56,z6]),(0,[z1,z8,z100,z132,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z584,z6])],[(0,[z1,z2,z157,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z585]),(0,[z1,z8,z3,z123,z10,z5,z6])],[(1,[z1,z441,z3,z4,z5,z6]),(0,[z586,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z55,z3,z4,z34,z6]),(0,[z1,z8,z157,z3,z108,z5,z6]),(0,[z65,z1,z8,z4,z108,z5,z6]),(0,[z1,z587,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z575,z6]),(0,[z1,z8,z3,z4,z12,z6,z42])],[(1,[z1,z54,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z6,z116]),(0,[z51,z1,z8,z3,z4,z12,z6]),(0,[z588,z1,z8,z3,z4,z5,z6])],[(0,[z60,z1,z462,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z6,z116]),(0,[z1,z8,z3,z4,z5,z6,z589]),(0,[z1,z8,z3,z4,z5,z107,z42]),(0,[z1,z8,z3,z4,z5,z6,z206])],[(0,[z84,z8,z2,z3,z4,z5,z6]),(0,[z1,z8,z457,z3,z4,z5,z6]),(0,[z590,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z591]),(0,[z1,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z100,z4,z5,z6,z22]),(0,[z592,z1,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z144,z5,z6]),(0,[z1,z14,z3,z45,z4,z5,z6]),(0,[z285,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z593]),(0,[z1,z8,z3,z4,z5,z6,z594])],[(0,[z48,z1,z207,z3,z4,z5,z6]),(0,[z1,z8,z595,z3,z4,z5,z6]),(0,[z1,z8,z100,z68,z4,z5,z6])]],
   [[(0,[z596,z1,z8,z3,z4,z5,z6]),(0,[z128,z1,z8,z3,z144,z5,z6])],[(0,[z8,z2,z3,z4,z5,z56,z6]),(0,[z128,z1,z8,z3,z32,z5,z6]),(0,[z235,z1,z8,z31,z3,z4,z6]),(0,[z597,z1,z8,z3,z4,z5,z6]),(0,[z51,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z598,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z599,z6])],[(0,[z74,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z15]),(1,[z340,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z600,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z6,z601]),(0,[z1,z3,z4,z47,z5,z21,z6]),(0,[z24,z1,z8,z3,z4,z12,z6])],[(0,[z1,z270,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z602,z4,z5,z6])],[(0,[z0,z1,z8,z3,z4,z5,z6]),(1,[z65,z1,z8,z4,z5,z15])],[(0,[z1,z8,z3,z4,z5,z603,z6]),(0,[z1,z8,z3,z4,z5,z75,z6])],[(0,[z1,z8,z3,z4,z34,z88,z6]),(0,[z120,z1,z8,z3,z4,z5,z129]),(0,[z1,z8,z604,z3,z4,z5,z6])],[(0,[z1,z8,z36,z3,z4,z12,z6])],[(0,[z59,z1,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z123,z4,z5,z6]),(0,[z1,z8,z605,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z6,z116])],[(0,[z1,z8,z3,z4,z56,z6,z136]),(1,[z1,z8,z3,z4,z164,z6]),(0,[z606,z1,z8,z3,z4,z5,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z48,z1,z8,z3,z4,z227,z6]),(0,[z1,z8,z3,z4,z34,z6,z136]),(0,[z1,z8,z3,z4,z5,z6,z607])],[(0,[z608,z1,z8,z3,z4,z5,z6]),(0,[z1,z527,z8,z3,z4,z5,z6])],[],[(0,[z1,z8,z36,z3,z4,z34,z6]),(1,[z1,z8,z360,z3,z4,z6]),(0,[z609,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z610])],[(0,[z1,z8,z3,z611,z4,z5,z6]),(0,[z1,z8,z3,z612,z4,z5,z6]),(0,[z1,z8,z3,z4,z613,z5,z6])]],
   [[(0,[z1,z46,z14,z3,z4,z5,z6]),(0,[z30,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z6,z405])],[(0,[z1,z8,z3,z144,z5,z6,z42]),(0,[z1,z8,z3,z4,z614,z5,z6]),(0,[z1,z615,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z406])],[(0,[z537,z1,z8,z3,z4,z5,z6]),(0,[z616,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z21,z6]),(0,[z1,z8,z3,z4,z5,z617,z6])],[(0,[z1,z8,z31,z3,z4,z144,z6]),(0,[z1,z8,z3,z618,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z21,z6])],[(1,[z1,z8,z3,z4,z474,z6]),(0,[z1,z8,z3,z32,z4,z5,z6]),(0,[z235,z1,z383,z3,z4,z5,z6]),(0,[z619,z1,z8,z3,z4,z5,z6])],[(0,[z620,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z63,z6]),(0,[z59,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z104,z42])],[(0,[z1,z8,z3,z4,z5,z621,z6]),(0,[z1,z46,z8,z3,z4,z12,z6]),(0,[z127,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z622,z3,z4,z5,z6]),(0,[z131,z1,z8,z3,z4,z63,z6]),(0,[z1,z8,z31,z3,z4,z6,z136])],[(0,[z1,z8,z408,z3,z4,z5,z6]),(1,[z293,z8,z3,z4,z5,z6]),(0,[z33,z1,z8,z3,z4,z280,z6]),(0,[z130,z1,z8,z3,z4,z5,z6]),(0,[z41,z1,z8,z3,z4,z5,z75])],[(0,[z1,z8,z3,z108,z5,z6,z116]),(0,[z1,z8,z3,z623,z4,z5,z6]),(0,[z19,z1,z8,z521,z4,z5,z6])],[(0,[z1,z8,z521,z3,z4,z5,z6]),(0,[z1,z8,z3,z37,z4,z5,z42])],[(0,[z1,z468,z8,z3,z4,z5,z6]),(0,[z1,z270,z8,z31,z3,z4,z6]),(0,[z624,z1,z8,z3,z4,z5,z6])],[(0,[z1,z46,z8,z3,z4,z34,z6]),(0,[z1,z177,z3,z45,z4,z5,z6])],[(0,[z26,z1,z2,z3,z4,z5,z6]),(1,[z570,z8,z3,z4,z5,z6]),(0,[z1,z625,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z47,z5,z6]),(0,[z1,z8,z3,z4,z417,z5,z6]),(0,[z1,z8,z626,z3,z4,z5,z6]),(0,[z120,z1,z8,z576,z4,z5,z6]),(0,[z627,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z628,z3,z4,z5,z6]),(0,[z1,z8,z138,z3,z4,z5,z66])]],
   [[(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z245,z5,z6]),(0,[z26,z1,z8,z3,z4,z328,z6]),(0,[z1,z8,z31,z3,z4,z21,z6]),(0,[z1,z8,z3,z4,z5,z629,z6])],[(0,[z630,z1,z8,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z56,z6]),(0,[z120,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z631]),(0,[z1,z8,z632,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z633])],[(0,[z1,z2,z3,z4,z5,z6,z465]),(0,[z1,z8,z3,z4,z4,z5,z6]),(0,[z1,z8,z31,z31,z3,z4,z6])],[(0,[z1,z8,z3,z4,z5,z227,z6]),(0,[z1,z8,z3,z634,z4,z5,z6]),(1,[z1,z8,z576,z4,z5,z6]),(0,[z51,z1,z8,z3,z635,z5,z6]),(0,[z484,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z15]),(0,[z288,z1,z8,z31,z3,z4,z6])],[(0,[z1,z8,z3,z4,z56,z6,z107]),(0,[z340,z1,z8,z3,z4,z5,z6]),(0,[z1,z270,z8,z3,z4,z5,z107])],[(1,[z1,z14,z3,z4,z5,z6]),(0,[z65,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z6,z107]),(0,[z1,z8,z3,z4,z5,z6,z636]),(0,[z1,z8,z3,z4,z5,z107,z15]),(0,[z113,z1,z8,z3,z4,z12,z6])],[(0,[z1,z2,z3,z4,z5,z6,z129]),(0,[z26,z248,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z27,z5,z6]),(0,[z1,z8,z637,z3,z4,z5,z6])],[(0,[z128,z1,z8,z96,z4,z5,z6])],[(0,[z120,z1,z8,z3,z4,z12,z6])],[(1,[z1,z8,z3,z4,z313,z6]),(0,[z1,z8,z3,z638,z4,z5,z6]),(0,[z1,z8,z3,z4,z639,z5,z6]),(0,[z1,z8,z36,z3,z5,z75,z6])],[(0,[z65,z1,z8,z3,z4,z5,z15]),(0,[z1,z640,z8,z3,z4,z5,z6])],[(0,[z1,z14,z8,z3,z4,z5,z6]),(0,[z641,z1,z8,z3,z4,z5,z6]),(1,[z1,z224,z3,z4,z5,z6]),(0,[z642,z1,z8,z3,z4,z5,z6])],[(1,[z8,z2,z3,z4,z56,z6]),(0,[z643,z1,z8,z3,z4,z5,z6]),(0,[z65,z1,z8,z3,z4,z12,z6]),(1,[z1,z8,z3,z4,z12,z6])],[(0,[z1,z14,z100,z3,z4,z5,z6]),(0,[z1,z8,z118,z3,z4,z34,z6]),(0,[z1,z266,z8,z3,z4,z5,z6])],[(1,[z84,z8,z3,z4,z34,z6]),(0,[z120,z1,z8,z3,z4,z34,z6])],[(0,[z60,z1,z8,z3,z4,z279,z6]),(1,[z1,z8,z240,z4,z5,z6]),(0,[z644,z1,z8,z3,z4,z5,z6])]],
   [[(0,[z1,z8,z420,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z253,z6])],[(0,[z1,z8,z3,z4,z11,z47,z6]),(0,[z1,z8,z3,z4,z160,z5,z6]),(0,[z1,z8,z176,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z500,z5,z6])],[(0,[z1,z489,z8,z3,z4,z5,z6]),(1,[z128,z8,z3,z144,z5,z6]),(1,[z1,z8,z3,z4,z34,z6]),(0,[z65,z1,z8,z3,z4,z34,z6]),(0,[z120,z1,z8,z3,z4,z639,z6])],[(0,[z1,z8,z3,z645,z4,z5,z6]),(0,[z1,z8,z3,z4,z436,z5,z6]),(0,[z1,z8,z646,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z581,z4,z6])],[(0,[z1,z14,z157,z3,z4,z5,z6]),(0,[z48,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z11,z56,z6]),(1,[z1,z8,z3,z4,z5,z125]),(0,[z59,z1,z8,z3,z4,z11,z6])],[(0,[z1,z8,z3,z4,z647,z5,z6])],[(1,[z1,z8,z3,z4,z639,z6]),(0,[z26,z1,z8,z31,z3,z4,z6])],[(0,[z128,z1,z8,z3,z4,z334,z6]),(1,[z1,z46,z3,z4,z47,z6])],[(0,[z1,z8,z3,z4,z108,z34,z6]),(0,[z51,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z648]),(0,[z1,z8,z3,z4,z5,z649,z6])],[(0,[z1,z2,z151,z3,z4,z5,z6]),(0,[z60,z8,z2,z3,z4,z5,z6]),(0,[z1,z8,z138,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z275,z5,z6]),(0,[z1,z650,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z254,z56,z6]),(0,[z1,z8,z3,z4,z134,z5,z6])],[(0,[z131,z1,z8,z3,z4,z5,z156]),(0,[z1,z8,z138,z151,z4,z5,z6])],[(0,[z1,z8,z3,z132,z4,z5,z6]),(0,[z1,z8,z651,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z90,z5,z6]),(0,[z1,z8,z652,z3,z4,z5,z6])],[(0,[z1,z8,z653,z3,z4,z5,z6]),(0,[z26,z1,z8,z3,z4,z5,z58]),(0,[z285,z1,z8,z3,z4,z47,z6]),(0,[z654,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z104,z15])]],
   [[],[(1,[z1,z14,z3,z4,z56,z6])],[(0,[z1,z8,z3,z4,z5,z6,z299]),(0,[z1,z8,z3,z4,z27,z56,z6])],[(0,[z103,z1,z445,z3,z4,z5,z6]),(0,[z1,z7,z8,z3,z4,z12,z6]),(0,[z1,z8,z655,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z22])],[(0,[z1,z2,z3,z4,z344,z5,z6]),(0,[z1,z8,z3,z4,z5,z550,z6]),(0,[z1,z8,z152,z3,z4,z104,z6]),(0,[z656,z1,z8,z3,z4,z5,z6])],[(0,[z131,z48,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z68,z4,z5,z6]),(0,[z1,z8,z657,z3,z4,z5,z6]),(0,[z1,z8,z101,z3,z4,z6,z22])],[(0,[z1,z8,z3,z4,z5,z6,z658]),(0,[z1,z8,z152,z31,z3,z4,z6])],[(0,[z1,z14,z8,z3,z4,z56,z6]),(1,[z1,z145,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z659,z5,z6]),(0,[z1,z8,z3,z4,z12,z6,z129]),(0,[z51,z28,z8,z3,z4,z5,z6]),(0,[z1,z8,z31,z55,z3,z4,z6]),(0,[z1,z660,z8,z3,z4,z5,z6])],[],[(0,[z1,z7,z8,z3,z4,z34,z6])],[(1,[z103,z8,z3,z4,z5,z104]),(0,[z1,z8,z3,z4,z5,z6,z52]),(0,[z1,z177,z8,z3,z4,z5,z6]),(0,[z661,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z662])],[(0,[z1,z8,z366,z3,z4,z5,z6])],[(0,[z14,z8,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z56,z6]),(0,[z1,z8,z3,z4,z663,z5,z6]),(1,[z1,z8,z3,z4,z13,z6])],[(0,[z664,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z529,z5,z6]),(0,[z131,z1,z8,z3,z4,z56,z6]),(0,[z665,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z101,z3,z4,z56,z6]),(0,[z1,z177,z8,z3,z27,z5,z6]),(0,[z1,z3,z4,z5,z88,z6,z107])],[(0,[z0,z8,z3,z4,z5,z104,z6]),(0,[z1,z8,z3,z307,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z666]),(0,[z1,z8,z3,z4,z541,z5,z6]),(0,[z1,z8,z3,z4,z11,z6,z116])]],
   [[(0,[z667,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z402,z6]),(0,[z1,z8,z3,z668,z4,z5,z6])],[(0,[z120,z1,z8,z3,z530,z5,z6]),(0,[z570,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z100,z55,z4,z5,z6]),(0,[z669,z1,z8,z3,z4,z5,z6])],[],[(0,[z670,z1,z8,z3,z4,z5,z6]),(0,[z1,z35,z8,z3,z4,z5,z6]),(0,[z59,z1,z8,z3,z4,z12,z6])],[(0,[z1,z2,z3,z4,z34,z5,z6]),(1,[z1,z8,z3,z635,z5,z6])],[(0,[z84,z1,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z104,z6]),(0,[z1,z8,z138,z3,z4,z56,z6]),(1,[z1,z8,z3,z530,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z671]),(0,[z1,z8,z3,z4,z456,z5,z6])],[(0,[z1,z8,z3,z4,z34,z104,z6]),(0,[z1,z8,z3,z4,z672,z5,z6])],[(0,[z1,z8,z31,z3,z132,z4,z6]),(0,[z1,z8,z31,z3,z4,z88,z6]),(0,[z1,z8,z3,z673,z4,z5,z6])],[(0,[z1,z14,z3,z4,z5,z6,z42])],[(0,[z1,z8,z3,z132,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z109,z6])],[(0,[z674,z1,z8,z3,z4,z5,z6]),(0,[z675,z1,z8,z3,z4,z5,z6])],[(0,[z0,z48,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z676,z6]),(0,[z128,z1,z8,z545,z4,z5,z6]),(0,[z1,z8,z3,z4,z580,z56,z6]),(0,[z84,z1,z8,z3,z4,z12,z6]),(0,[z1,z8,z677,z3,z4,z5,z6])],[(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z678,z6])],[(0,[z679,z1,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z680,z4,z5,z6]),(0,[z1,z8,z101,z4,z11,z5,z6])]],
   [[(1,[z1,z8,z3,z544,z5,z6]),(0,[z597,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z12,z12,z6])],[(0,[z74,z1,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z68,z4,z56,z6])],[(0,[z1,z14,z3,z4,z5,z6,z129]),(0,[z84,z1,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z10,z34,z6]),(1,[z266,z8,z3,z4,z5,z6])],[(0,[z1,z8,z31,z3,z4,z104,z6]),(0,[z1,z8,z3,z4,z5,z6,z681]),(0,[z1,z8,z31,z604,z3,z4,z6])],[(0,[z1,z8,z3,z4,z682,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z683]),(0,[z1,z684,z8,z3,z4,z5,z6])],[(0,[z1,z685,z8,z3,z4,z5,z6])],[(0,[z1,z177,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z12,z34,z6]),(0,[z1,z8,z3,z4,z11,z21,z6])],[(0,[z1,z8,z3,z4,z686,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z116]),(0,[z1,z112,z8,z3,z4,z12,z6])],[(0,[z1,z14,z3,z4,z395,z5,z6])],[(0,[z1,z8,z3,z4,z5,z6,z155])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z8,z441,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z328,z6]),(0,[z1,z8,z3,z687,z4,z5,z6])],[(0,[z1,z8,z3,z4,z264,z5,z6]),(0,[z1,z8,z31,z2,z3,z4,z6]),(0,[z1,z527,z8,z3,z4,z56,z6])],[(0,[z1,z8,z3,z4,z688,z5,z6])],[],[(0,[z1,z8,z3,z4,z5,z6,z601])],[(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z365,z1,z8,z3,z4,z5,z6])]],
   [[(0,[z689,z1,z8,z3,z4,z5,z6])],[(0,[z247,z1,z8,z3,z4,z5,z6]),(0,[z1,z690,z8,z3,z4,z5,z6])],[(1,[z1,z8,z3,z4,z529,z6]),(0,[z1,z8,z3,z691,z4,z5,z6]),(0,[z1,z8,z139,z3,z4,z5,z6])],[(0,[z128,z60,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z32,z4,z56,z6]),(0,[z1,z383,z8,z3,z4,z5,z6]),(0,[z1,z8,z55,z3,z4,z5,z6]),(0,[z1,z8,z3,z635,z4,z5,z6]),(0,[z285,z1,z8,z3,z4,z21,z6]),(0,[z1,z8,z692,z3,z4,z5,z6])],[(0,[z693,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z694])],[(0,[z1,z14,z151,z3,z4,z5,z6]),(0,[z285,z1,z8,z31,z3,z4,z6]),(0,[z1,z8,z31,z3,z4,z6,z107]),(0,[z1,z8,z3,z4,z108,z12,z6]),(0,[z30,z1,z8,z3,z4,z5,z136])],[(0,[z8,z2,z3,z4,z5,z104,z6]),(0,[z1,z207,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z45,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z6,z695]),(0,[z1,z8,z3,z4,z5,z6,z136])],[(0,[z1,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z132,z4,z5,z6,z15])],[(0,[z128,z1,z8,z3,z4,z5,z575]),(1,[z28,z8,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z6,z206])],[(0,[z1,z8,z3,z4,z5,z696,z6]),(0,[z1,z8,z697,z3,z4,z5,z6])],[(0,[z698,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z699])],[(0,[z19,z1,z14,z3,z4,z5,z6]),(0,[z1,z462,z8,z3,z4,z5,z6]),(0,[z700,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z27,z6]),(0,[z1,z8,z701,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z702,z6])],[(0,[z1,z8,z3,z4,z703,z5,z6])],[],[(0,[z0,z8,z3,z4,z144,z5,z6]),(0,[z704,z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z705]),(0,[z1,z8,z3,z4,z5,z21,z6]),(0,[z1,z8,z706,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z178,z5,z6])],[(0,[z1,z8,z3,z5,z75,z6,z42])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z8,z100,z36,z56,z6]),(0,[z8,z3,z4,z34,z707,z6]),(0,[z1,z8,z605,z4,z5,z66]),(0,[z1,z8,z708,z4,z5,z6])],[(0,[z1,z366,z3,z4,z12,z6]),(0,[z1,z342,z3,z4,z56,z6]),(0,[z1,z709,z3,z4,z5,z6]),(0,[z215,z1,z3,z27,z5,z6])],[(0,[z1,z8,z3,z4,z380,z64]),(0,[z1,z455,z3,z4,z47,z6]),(0,[z1,z710,z3,z4,z12,z6])],[(0,[z1,z8,z545,z4,z34,z6]),(0,[z128,z8,z545,z144,z5,z6]),(0,[z582,z8,z3,z4,z56,z6]),(0,[z711,z8,z3,z4,z5,z6]),(0,[z1,z8,z101,z581,z4,z6]),(0,[z1,z8,z3,z4,z712,z6])],[(0,[z1,z2,z3,z4,z227,z6]),(0,[z1,z8,z3,z713,z5,z6]),(0,[z1,z14,z96,z4,z5,z6]),(0,[z1,z346,z3,z4,z56,z6]),(0,[z1,z714,z3,z4,z5,z6])],[(0,[z1,z8,z3,z37,z56,z75]),(0,[z715,z8,z3,z4,z5,z6])],[(0,[z2,z3,z4,z56,z6,z42]),(0,[z329,z2,z3,z4,z56,z6]),(0,[z1,z2,z231,z4,z5,z6]),(0,[z1,z14,z3,z421,z5,z6]),(0,[z716,z8,z3,z4,z5,z6]),(0,[z717,z8,z3,z4,z12,z6])],[(0,[z1,z2,z3,z4,z6,z155]),(0,[z1,z8,z3,z4,z718,z6]),(0,[z1,z719,z3,z4,z5,z6]),(0,[z1,z366,z3,z4,z34,z6]),(0,[z1,z8,z3,z144,z5,z64]),(0,[z8,z386,z3,z4,z56,z6]),(0,[z1,z8,z3,z720,z5,z6]),(0,[z1,z721,z3,z4,z5,z6]),(0,[z1,z8,z722,z3,z4,z5])],[(0,[z723,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z328,z6]),(0,[z1,z8,z724,z3,z4,z6]),(0,[z1,z8,z3,z32,z5,z64]),(0,[z570,z8,z3,z4,z34,z6]),(0,[z120,z8,z576,z4,z5,z129]),(0,[z18,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z725,z6])],[(0,[z1,z8,z3,z4,z5,z238]),(0,[z1,z8,z157,z108,z56,z6]),(0,[z1,z726,z3,z4,z5,z6])],[(0,[z1,z8,z727,z3,z4,z6]),(0,[z2,z3,z98,z4,z5,z6]),(0,[z46,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z728]),(0,[z120,z14,z3,z4,z5,z129]),(0,[z1,z8,z3,z4,z729,z6]),(0,[z18,z346,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z730]),(0,[z1,z8,z96,z4,z12,z6]),(0,[z1,z8,z652,z4,z11,z6])],[(0,[z120,z2,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z90,z6]),(0,[z1,z408,z3,z4,z5,z6]),(0,[z1,z8,z151,z4,z5,z238]),(0,[z1,z8,z3,z4,z731,z6]),(0,[z103,z8,z3,z4,z164,z104])],[(0,[z1,z2,z246,z4,z5,z6]),(0,[z286,z1,z3,z4,z212,z6]),(0,[z1,z8,z3,z421,z12,z6]),(0,[z1,z8,z3,z4,z732,z6]),(0,[z1,z8,z3,z4,z733,z6]),(0,[z451,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z734,z5,z6])],[(0,[z248,z2,z3,z4,z5,z6]),(0,[z1,z8,z31,z96,z4,z6]),(0,[z1,z8,z735,z3,z4,z575]),(0,[z8,z3,z4,z707,z56,z6]),(0,[z1,z8,z736,z157,z5,z6])],[(0,[z2,z36,z3,z4,z56,z6]),(0,[z44,z1,z3,z395,z5,z6]),(0,[z1,z8,z3,z4,z737,z6]),(0,[z120,z8,z139,z3,z4,z6]),(0,[z302,z8,z3,z4,z5,z129]),(0,[z1,z615,z3,z45,z5,z6]),(0,[z1,z8,z4,z5,z6,z738])]],
   [[(0,[z2,z3,z4,z5,z241,z6]),(0,[z1,z8,z3,z739,z4,z5]),(0,[z1,z8,z3,z740,z4,z6]),(0,[z248,z8,z3,z4,z328,z6])],[(0,[z741,z2,z3,z4,z5,z6]),(0,[z19,z1,z14,z3,z6,z116]),(0,[z1,z441,z3,z544,z5,z6]),(0,[z1,z8,z3,z4,z742,z6]),(0,[z128,z8,z96,z144,z5,z6]),(0,[z1,z8,z576,z4,z639,z6]),(0,[z120,z8,z3,z4,z12,z129])],[(0,[z661,z2,z3,z4,z5,z6]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z575]),(0,[z1,z743,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z90,z136]),(0,[z51,z28,z68,z4,z5,z6]),(0,[z1,z3,z45,z744,z5,z6])],[(0,[z1,z2,z3,z250,z5,z6]),(0,[z1,z8,z3,z4,z5,z745]),(0,[z1,z14,z3,z4,z639,z6]),(0,[z1,z8,z3,z421,z34,z6]),(0,[z1,z8,z3,z320,z5,z6])],[(0,[z8,z2,z3,z4,z13,z6]),(0,[z1,z8,z3,z4,z746,z6]),(0,[z747,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z748,z5,z6])],[(0,[z1,z383,z3,z4,z56,z6]),(0,[z120,z8,z3,z4,z253,z129]),(0,[z1,z8,z3,z4,z12,z568]),(0,[z1,z8,z736,z108,z5,z6])],[(0,[z2,z3,z4,z251,z5,z6]),(0,[z2,z3,z4,z5,z252,z6]),(0,[z1,z8,z3,z4,z749,z6]),(0,[z1,z8,z144,z70,z5,z6]),(0,[z1,z8,z750,z3,z4,z6])],[(0,[z48,z2,z3,z4,z227,z6]),(0,[z1,z2,z3,z29,z4,z6]),(0,[z1,z8,z4,z5,z6,z751]),(0,[z120,z8,z3,z4,z34,z129]),(0,[z1,z8,z3,z4,z752,z6])],[(0,[z704,z2,z3,z4,z5,z6]),(0,[z325,z8,z132,z4,z5,z6]),(0,[z508,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z530,z5,z129]),(0,[z1,z8,z3,z4,z753,z6]),(0,[z1,z8,z3,z4,z754,z6])],[(0,[z1,z457,z3,z4,z5,z64]),(0,[z1,z8,z3,z4,z12,z575]),(0,[z1,z8,z372,z4,z56,z6]),(0,[z1,z8,z240,z4,z34,z6])],[(0,[z444,z1,z8,z4,z6,z146]),(0,[z1,z8,z3,z4,z755,z56]),(0,[z1,z8,z3,z4,z134,z6]),(0,[z1,z8,z3,z4,z756,z6])],[(0,[z131,z8,z132,z4,z5,z156]),(0,[z120,z8,z3,z4,z639,z129]),(0,[z8,z3,z4,z5,z757,z129]),(0,[z35,z46,z3,z4,z5,z6])],[(0,[z2,z260,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z12,z402]),(0,[z1,z8,z336,z3,z4,z6])],[(0,[z8,z2,z3,z530,z5,z6]),(0,[z1,z8,z3,z4,z5,z758]),(0,[z1,z8,z3,z4,z6,z759]),(0,[z1,z8,z3,z4,z760,z5]),(0,[z1,z342,z231,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z761])],[(0,[z2,z3,z4,z56,z6,z146]),(0,[z1,z14,z3,z4,z5,z762]),(0,[z1,z8,z3,z763,z5,z6]),(0,[z1,z8,z336,z3,z4,z95]),(0,[z764,z8,z3,z4,z5,z6])],[(0,[z1,z2,z179,z4,z5,z6]),(0,[z1,z8,z3,z4,z34,z575]),(0,[z8,z3,z4,z56,z6,z578]),(0,[z1,z8,z3,z4,z12,z356])]],
   [[(0,[z1,z8,z3,z4,z765,z6]),(0,[z1,z441,z3,z4,z12,z6]),(0,[z60,z8,z3,z32,z417,z6]),(0,[z1,z766,z3,z4,z5,z6]),(0,[z1,z346,z231,z4,z5,z6]),(0,[z1,z35,z3,z4,z21,z6]),(0,[z266,z8,z3,z4,z280,z6]),(0,[z1,z8,z3,z4,z767,z6]),(0,[z59,z1,z8,z135,z6,z22])],[(0,[z60,z2,z3,z32,z5,z6]),(0,[z1,z768,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z90]),(0,[z769,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z450])],[(0,[z141,z2,z132,z4,z5,z6]),(0,[z14,z701,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z275,z6]),(0,[z1,z54,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z770,z6]),(0,[z1,z8,z31,z3,z4,z613])],[(0,[z1,z8,z3,z720,z56,z6])],[(0,[z1,z8,z3,z4,z771,z6]),(0,[z772,z8,z3,z4,z5,z6])],[(0,[z642,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z56,z238]),(0,[z1,z773,z3,z4,z5,z6])],[(0,[z288,z2,z3,z4,z56,z6]),(0,[z60,z2,z3,z4,z279,z6]),(0,[z1,z2,z3,z4,z89,z6]),(0,[z1,z2,z3,z4,z5,z58]),(0,[z0,z8,z152,z3,z4,z6]),(0,[z1,z8,z3,z4,z774,z6]),(0,[z248,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z775,z6]),(0,[z1,z776,z3,z4,z5,z6])],[(0,[z361,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z777]),(0,[z1,z8,z3,z4,z279,z6]),(0,[z1,z8,z3,z4,z280,z6])],[(0,[z120,z2,z231,z4,z5,z6]),(0,[z1,z8,z3,z4,z778,z6]),(0,[z1,z54,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z779,z6]),(0,[z453,z1,z8,z3,z5,z42]),(0,[z1,z408,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z328,z58]),(0,[z1,z8,z31,z3,z37,z75]),(0,[z1,z8,z213,z3,z43,z6])],[(1,[z2,z3,z4,z279,z6]),(0,[z2,z3,z4,z276,z56,z6]),(0,[z1,z8,z3,z780,z5,z6]),(0,[z1,z781,z3,z4,z5,z6]),(0,[z340,z8,z3,z4,z12,z6])],[(0,[z235,z2,z3,z4,z56,z6]),(0,[z0,z14,z31,z3,z4,z6]),(0,[z1,z14,z3,z4,z164,z6]),(0,[z1,z8,z3,z4,z782,z6]),(0,[z1,z342,z3,z250,z5,z6]),(0,[z1,z783,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z784,z6]),(0,[z1,z8,z3,z4,z785,z6]),(0,[z1,z8,z3,z4,z786,z6]),(0,[z1,z8,z787,z4,z5,z6])],[(0,[z340,z8,z3,z4,z529,z6]),(0,[z1,z8,z3,z4,z275,z156]),(0,[z1,z8,z3,z4,z90,z107]),(0,[z84,z8,z139,z3,z4,z6]),(0,[z1,z8,z788,z3,z4,z6]),(0,[z1,z8,z789,z4,z5,z6]),(0,[z1,z8,z92,z108,z5,z6]),(0,[z65,z1,z8,z4,z12,z15])],[(0,[z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z3,z4,z377,z6]),(0,[z2,z3,z4,z88,z56,z6]),(0,[z1,z346,z3,z250,z5,z6]),(0,[z1,z8,z3,z4,z790,z6]),(0,[z28,z7,z3,z4,z5,z6]),(0,[z1,z791,z3,z4,z5,z6])],[(0,[z2,z3,z4,z284,z5,z6]),(0,[z1,z14,z360,z3,z4,z6]),(0,[z1,z8,z3,z4,z792,z6]),(0,[z449,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z793,z6]),(0,[z1,z8,z3,z794,z12,z6])],[(0,[z2,z3,z4,z56,z6,z15]),(0,[z1,z8,z3,z320,z56,z6]),(0,[z1,z8,z31,z3,z4,z702])]],
   [[(0,[z2,z124,z3,z4,z56,z6]),(0,[z1,z8,z139,z3,z4,z6]),(0,[z1,z8,z336,z3,z4,z12])],[(0,[z60,z8,z3,z795,z5,z6]),(0,[z1,z8,z796,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z85]),(0,[z1,z8,z3,z4,z797,z6]),(0,[z1,z8,z3,z4,z102,z6])],[(0,[z1,z8,z3,z4,z798,z6]),(0,[z1,z8,z301,z3,z56,z6]),(0,[z65,z1,z8,z4,z34,z15]),(0,[z1,z8,z3,z4,z799,z6]),(0,[z1,z8,z800,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z801])],[(0,[z31,z2,z3,z4,z56,z6]),(0,[z1,z2,z802,z4,z5,z6]),(0,[z1,z803,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z474,z6]),(1,[z8,z3,z795,z5,z6]),(0,[z1,z8,z804,z4,z56,z6]),(0,[z333,z1,z8,z336,z3,z4])],[(0,[z1,z8,z3,z4,z805,z6]),(0,[z1,z8,z806,z3,z4,z6]),(0,[z26,z1,z3,z27,z134,z6]),(0,[z1,z8,z3,z4,z6,z807])],[(0,[z1,z8,z3,z808,z5,z6]),(0,[z1,z8,z3,z809,z5,z6]),(0,[z120,z8,z360,z3,z4,z129]),(0,[z1,z8,z3,z4,z810,z6]),(0,[z1,z8,z3,z4,z6,z811])],[(0,[z1,z462,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z812,z6]),(0,[z1,z813,z3,z4,z5,z6])],[(0,[z1,z193,z31,z3,z4,z6]),(0,[z59,z1,z8,z178,z6,z22]),(0,[z1,z8,z3,z4,z436,z6]),(0,[z1,z814,z3,z4,z5,z6])],[(0,[z2,z138,z132,z4,z5,z6]),(0,[z2,z3,z4,z108,z56,z6]),(0,[z293,z14,z3,z4,z5,z6]),(1,[z8,z3,z4,z707,z6]),(0,[z293,z8,z3,z4,z815,z6])],[(0,[z0,z8,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z6,z91]),(0,[z1,z8,z3,z4,z816,z6]),(0,[z120,z8,z3,z530,z5,z129]),(0,[z817,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z818,z6]),(0,[z41,z1,z8,z3,z5,z819])],[(0,[z1,z46,z447,z3,z4,z6]),(0,[z130,z1,z8,z581,z4,z6])],[(0,[z1,z336,z2,z3,z4,z6])],[(0,[z120,z31,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z216,z6]),(0,[z1,z14,z3,z4,z5,z820]),(0,[z1,z8,z821,z4,z5,z6]),(0,[z1,z8,z31,z231,z4,z6]),(0,[z1,z8,z3,z530,z5,z104]),(0,[z8,z3,z4,z5,z104,z757])],[(0,[z1,z2,z3,z4,z822,z6]),(0,[z1,z366,z3,z4,z5,z6]),(0,[z570,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z334,z64]),(0,[z1,z8,z190,z108,z5,z6]),(0,[z1,z8,z31,z3,z4,z58]),(0,[z1,z8,z4,z823,z5,z6]),(0,[z1,z8,z3,z4,z824,z6]),(0,[z1,z8,z246,z123,z5,z6]),(0,[z1,z825,z3,z4,z12,z6])],[(0,[z1,z2,z3,z4,z106,z6]),(0,[z1,z152,z2,z3,z4,z6]),(0,[z1,z8,z3,z4,z5,z826]),(0,[z1,z489,z3,z4,z5,z274]),(0,[z1,z31,z145,z3,z4,z6]),(0,[z224,z3,z4,z5,z56,z6]),(0,[z148,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z530,z34,z6]),(0,[z1,z8,z3,z744,z5,z6]),(0,[z33,z266,z3,z4,z5,z88]),(0,[z1,z710,z3,z4,z5,z6])]],
   [[(0,[z48,z2,z3,z4,z56,z6]),(0,[z28,z8,z3,z4,z5,z85]),(0,[z51,z1,z68,z4,z216,z6]),(0,[z293,z8,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z827,z6])],[(0,[z620,z14,z3,z4,z5,z6]),(0,[z361,z8,z132,z4,z5,z6]),(0,[z1,z8,z3,z4,z777,z56])],[(0,[z1,z2,z3,z4,z49,z6]),(0,[z2,z3,z4,z56,z6,z208]),(0,[z1,z828,z3,z4,z5,z6])],[(0,[z1,z14,z576,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z829]),(0,[z1,z8,z3,z530,z639,z6]),(0,[z293,z8,z240,z4,z5,z6])],[(0,[z1,z8,z830,z3,z5,z6]),(0,[z831,z8,z3,z4,z5,z6]),(1,[z1,z8,z246,z6,z116])],[(0,[z65,z1,z2,z4,z5,z15]),(0,[z8,z3,z4,z13,z104,z6]),(0,[z570,z8,z3,z4,z12,z6]),(0,[z1,z8,z832,z3,z4,z6]),(0,[z1,z8,z3,z4,z833,z6]),(0,[z1,z8,z100,z343,z5,z6])],[(0,[z1,z46,z3,z4,z580,z6]),(0,[z293,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z834,z6]),(0,[z1,z8,z835,z3,z4,z6]),(0,[z836,z8,z3,z4,z5,z6]),(0,[z1,z8,z31,z837,z4,z6])],[(0,[z103,z2,z3,z4,z56,z6]),(0,[z41,z1,z14,z3,z5,z42]),(0,[z1,z8,z3,z4,z838,z6]),(0,[z1,z839,z3,z4,z5,z6]),(0,[z28,z3,z68,z4,z5,z6]),(0,[z1,z8,z3,z4,z840,z6])],[(0,[z0,z207,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z12,z274]),(0,[z1,z8,z96,z4,z5,z6]),(0,[z26,z248,z3,z27,z5,z6]),(0,[z293,z8,z3,z4,z5,z125]),(0,[z1,z8,z3,z4,z12,z419])],[(0,[z1,z14,z3,z4,z313,z6]),(0,[z131,z2,z132,z4,z5,z6]),(0,[z2,z3,z4,z5,z220,z6]),(0,[z1,z8,z231,z4,z252,z6]),(1,[z1,z3,z4,z841,z6]),(0,[z1,z270,z3,z4,z5,z107]),(0,[z19,z1,z8,z3,z6,z842])],[(0,[z1,z8,z3,z421,z5,z6]),(0,[z1,z8,z576,z4,z12,z6]),(0,[z1,z8,z843,z3,z4,z6])],[(0,[z1,z8,z844,z3,z4,z6]),(0,[z1,z8,z3,z4,z845,z6]),(1,[z1,z3,z4,z5,z846]),(0,[z1,z847,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z12,z6]),(0,[z1,z8,z848,z3,z4,z6]),(0,[z1,z849,z3,z4,z5,z6]),(0,[z1,z8,z3,z192,z10,z6])],[(0,[z2,z3,z37,z4,z56,z6]),(0,[z1,z8,z3,z4,z56,z85]),(0,[z35,z3,z4,z5,z21,z6]),(0,[z1,z8,z31,z100,z36,z6])],[(0,[z1,z2,z3,z4,z850,z6]),(0,[z60,z8,z3,z600,z5,z6]),(0,[z1,z8,z851,z3,z4,z6]),(0,[z84,z14,z3,z4,z34,z6]),(0,[z182,z8,z3,z4,z34,z6]),(0,[z1,z852,z68,z4,z5,z6])],[(0,[z2,z3,z4,z56,z6,z465]),(0,[z853,z1,z2,z4,z5,z6]),(0,[z1,z14,z240,z4,z5,z6]),(0,[z1,z8,z3,z4,z854,z238]),(0,[z1,z457,z3,z4,z56,z6]),(0,[z8,z391,z3,z4,z56,z6]),(0,[z1,z8,z3,z108,z6,z91]),(0,[z1,z8,z855,z3,z5,z6]),(0,[z1,z8,z301,z3,z6,z155])]],
   [[(0,[z606,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z253,z6]),(0,[z1,z8,z3,z4,z856,z6]),(0,[z1,z8,z857,z3,z4,z6]),(0,[z1,z8,z576,z4,z34,z6]),(0,[z103,z8,z3,z4,z5,z757])],[(0,[z1,z858,z3,z4,z5,z6]),(0,[z325,z8,z3,z144,z5,z6])],[(0,[z1,z14,z3,z4,z34,z6]),(0,[z497,z2,z3,z4,z5,z6]),(0,[z128,z14,z3,z144,z5,z6]),(0,[z1,z224,z3,z4,z12,z6])],[(0,[z2,z3,z4,z56,z6,z129]),(0,[z1,z462,z3,z4,z56,z6]),(0,[z1,z445,z3,z4,z56,z6]),(0,[z1,z8,z3,z859,z34,z6])],[(0,[z0,z8,z3,z4,z227,z6]),(0,[z1,z14,z3,z4,z5,z125]),(0,[z285,z340,z3,z4,z21,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z41,z1,z8,z70,z5,z6])],[(0,[z2,z3,z244,z4,z5,z6]),(0,[z235,z383,z3,z4,z56,z6]),(0,[z1,z8,z861,z3,z4,z85]),(0,[z1,z862,z3,z4,z12,z6])],[(0,[z654,z2,z3,z4,z5,z6]),(0,[z459,z2,z3,z4,z5,z6]),(0,[z0,z8,z231,z4,z5,z6]),(0,[z1,z54,z3,z544,z5,z6]),(0,[z1,z8,z3,z4,z6,z863]),(0,[z1,z8,z3,z4,z6,z864]),(0,[z1,z8,z3,z250,z252,z6]),(0,[z1,z8,z3,z413,z5,z6]),(0,[z1,z8,z240,z4,z12,z6]),(0,[z26,z1,z3,z744,z5,z6])],[(0,[z1,z76,z3,z4,z164,z6]),(0,[z28,z468,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z865,z6])],[(0,[z150,z2,z132,z4,z5,z6]),(0,[z31,z2,z3,z4,z144,z6]),(0,[z2,z3,z200,z4,z56,z6]),(0,[z30,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z866,z6]),(0,[z1,z8,z3,z4,z867,z6]),(0,[z1,z8,z3,z4,z334,z6]),(0,[z1,z224,z3,z4,z34,z6]),(1,[z1,z8,z108,z6,z91])],[(0,[z1,z8,z3,z4,z5,z868]),(0,[z128,z8,z3,z144,z12,z6]),(0,[z1,z8,z3,z4,z755,z5]),(0,[z271,z1,z8,z4,z6,z22])],[(0,[z2,z3,z4,z5,z254,z6]),(0,[z84,z31,z2,z3,z4,z6]),(0,[z1,z270,z3,z4,z5,z846])],[(0,[z2,z3,z4,z144,z5,z6]),(0,[z1,z177,z3,z222,z5,z6]),(0,[z1,z8,z3,z4,z12,z125]),(0,[z1,z8,z3,z43,z6,z116])],[(0,[z0,z8,z3,z4,z90,z6]),(0,[z1,z8,z3,z4,z869,z6]),(0,[z1,z8,z3,z4,z870,z6]),(0,[z1,z8,z3,z4,z871,z6]),(0,[z1,z8,z372,z4,z377,z6])],[(0,[z1,z441,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z95,z6]),(0,[z1,z8,z3,z4,z872,z6]),(0,[z1,z873,z3,z4,z5,z6])],[(0,[z1,z31,z2,z3,z4,z6]),(0,[z674,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z874,z6]),(0,[z1,z8,z3,z4,z6,z875]),(0,[z1,z8,z240,z4,z5,z125]),(0,[z266,z3,z4,z5,z88,z6]),(0,[z33,z1,z3,z4,z198,z88]),(0,[z1,z8,z36,z94,z5,z6])],[(0,[z1,z54,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z338,z6]),(0,[z1,z2,z100,z36,z5,z6]),(0,[z26,z1,z3,z395,z5,z6]),(0,[z128,z8,z3,z144,z34,z6]),(0,[z1,z8,z3,z4,z876,z6]),(0,[z1,z8,z877,z4,z5,z6])]],
   [[(0,[z1,z8,z3,z4,z12,z402]),(0,[z1,z8,z3,z37,z5,z513]),(0,[z1,z31,z408,z3,z4,z6])],[(0,[z1,z8,z3,z4,z878,z6]),(0,[z1,z8,z3,z4,z34,z125]),(0,[z1,z8,z3,z879,z4,z6]),(0,[z1,z31,z76,z3,z4,z6])],[(0,[z582,z2,z3,z4,z5,z6]),(0,[z128,z8,z3,z144,z5,z575]),(0,[z142,z1,z3,z4,z5,z88]),(0,[z1,z8,z31,z3,z880,z6])],[(0,[z420,z2,z3,z4,z56,z6]),(0,[z2,z3,z4,z10,z56,z6]),(0,[z1,z14,z3,z4,z881,z6]),(0,[z1,z8,z545,z4,z5,z64]),(0,[z1,z882,z3,z4,z5,z6]),(0,[z1,z8,z31,z240,z4,z6]),(0,[z1,z8,z3,z4,z160,z6]),(0,[z143,z8,z152,z3,z4,z6])],[(0,[z2,z3,z4,z345,z5,z6]),(0,[z1,z2,z3,z37,z5,z75]),(0,[z1,z8,z3,z4,z883,z6]),(0,[z257,z8,z3,z4,z56,z6])],[(0,[z1,z2,z3,z123,z10,z6]),(0,[z1,z8,z884,z3,z4,z6]),(0,[z1,z270,z3,z4,z56,z107]),(0,[z28,z8,z3,z413,z5,z6]),(0,[z1,z8,z3,z4,z5,z885]),(0,[z1,z8,z3,z4,z6,z886])],[(0,[z340,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z887])],[(0,[z2,z3,z4,z12,z56,z6]),(0,[z1,z8,z888,z4,z5,z6]),(0,[z1,z8,z100,z595,z5,z6])],[(0,[z487,z2,z3,z4,z5,z6]),(0,[z1,z2,z157,z108,z5,z6]),(0,[z1,z8,z3,z4,z889,z6]),(0,[z1,z8,z3,z413,z5,z52]),(0,[z890,z8,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z891,z6]),(0,[z1,z8,z3,z4,z6,z892])],[(0,[z8,z3,z4,z344,z56,z6]),(0,[z1,z8,z893,z3,z4,z64]),(0,[z1,z8,z3,z4,z894,z6]),(0,[z1,z8,z4,z6,z738,z22]),(0,[z1,z8,z3,z895,z12,z6])],[(0,[z2,z3,z4,z5,z359,z6]),(0,[z2,z3,z229,z4,z56,z6]),(0,[z120,z2,z3,z4,z252,z6]),(0,[z8,z3,z4,z5,z707,z6]),(0,[z1,z8,z179,z4,z134,z6]),(0,[z1,z8,z521,z4,z5,z6]),(0,[z1,z8,z3,z320,z89,z6])],[(0,[z1,z8,z3,z896,z5,z6]),(0,[z506,z2,z3,z4,z5,z6]),(0,[z451,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z13,z6]),(0,[z1,z8,z3,z897,z5,z6])],[(0,[z67,z2,z3,z4,z5,z104]),(0,[z2,z3,z4,z5,z6,z363]),(0,[z1,z8,z3,z4,z898,z6]),(0,[z1,z8,z899,z3,z4,z6]),(0,[z1,z8,z3,z351,z254,z6]),(0,[z570,z8,z3,z635,z5,z6])],[(0,[z553,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z900,z6]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z1,z193,z3,z4,z380,z6]),(0,[z1,z8,z3,z4,z902,z6]),(0,[z1,z145,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z164,z6]),(0,[z1,z8,z3,z4,z242,z6]),(0,[z1,z8,z301,z3,z89,z6]),(0,[z1,z903,z31,z3,z4,z6])],[(0,[z2,z3,z4,z5,z279,z6]),(0,[z588,z2,z3,z4,z5,z6]),(0,[z723,z1,z8,z3,z5,z6])]],
   [[(0,[z1,z8,z4,z904,z5,z6]),(0,[z1,z8,z3,z4,z905,z6]),(0,[z1,z632,z3,z4,z47,z6]),(0,[z1,z8,z3,z4,z906,z6])],[(0,[z1,z8,z96,z4,z5,z64]),(0,[z8,z3,z4,z56,z550,z6]),(0,[z103,z8,z3,z4,z12,z104])],[(0,[z1,z31,z2,z3,z4,z12]),(0,[z1,z39,z3,z4,z5,z88]),(0,[z1,z8,z3,z4,z889,z156]),(0,[z1,z8,z3,z4,z907,z6]),(0,[z1,z8,z3,z413,z56,z6]),(0,[z1,z8,z3,z4,z908,z6]),(0,[z664,z1,z8,z108,z5,z6]),(0,[z1,z8,z3,z4,z12,z467])],[(0,[z1,z14,z909,z4,z5,z6]),(0,[z1,z8,z3,z421,z63,z6]),(0,[z1,z8,z576,z530,z5,z6]),(0,[z1,z8,z3,z4,z910,z6])],[(0,[z249,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z635,z5,z6]),(0,[z1,z366,z3,z4,z227,z6]),(0,[z1,z145,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z911,z6]),(0,[z1,z8,z3,z912,z5,z6]),(0,[z1,z8,z100,z736,z5,z6]),(0,[z1,z8,z3,z4,z5,z913])],[(0,[z644,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z530,z5,z6]),(0,[z1,z914,z3,z4,z5,z6]),(1,[z224,z3,z4,z56,z6]),(0,[z1,z8,z3,z915,z34,z6])],[(0,[z8,z3,z132,z4,z13,z6]),(0,[z1,z205,z31,z3,z4,z6])],[(0,[z2,z378,z3,z4,z5,z6]),(0,[z2,z3,z4,z144,z56,z6]),(0,[z2,z3,z45,z4,z56,z6]),(0,[z60,z8,z3,z4,z13,z6]),(0,[z1,z8,z78,z36,z5,z6]),(0,[z143,z8,z3,z4,z56,z6]),(0,[z103,z8,z3,z4,z34,z104]),(0,[z1,z8,z3,z4,z916,z6]),(0,[z1,z917,z3,z4,z12,z6])],[(0,[z1,z2,z372,z4,z5,z6]),(0,[z1,z8,z918,z3,z4,z6]),(0,[z1,z342,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z919,z6]),(1,[z1,z8,z736,z5,z6])],[(0,[z1,z8,z920,z4,z5,z6]),(0,[z1,z8,z921,z3,z4,z6]),(0,[z1,z8,z922,z4,z5,z6]),(0,[z113,z1,z3,z4,z50,z6])],[(0,[z1,z8,z923,z3,z4,z6]),(0,[z1,z8,z924,z4,z5,z6]),(0,[z60,z8,z3,z32,z279,z6]),(0,[z8,z3,z4,z34,z56,z6]),(0,[z1,z8,z3,z4,z925,z6]),(0,[z1,z112,z3,z4,z541,z6])],[(0,[z1,z8,z3,z4,z926,z6]),(0,[z392,z2,z3,z4,z5,z6]),(0,[z1,z346,z31,z3,z4,z6]),(0,[z1,z8,z3,z635,z12,z6]),(0,[z1,z8,z3,z4,z6,z927]),(0,[z1,z928,z3,z4,z5,z6]),(0,[z1,z929,z3,z4,z5,z6])],[(0,[z1,z8,z3,z530,z12,z6]),(0,[z26,z1,z31,z3,z27,z6]),(0,[z1,z8,z930,z4,z5,z6]),(0,[z1,z8,z470,z4,z6,z22]),(0,[z1,z8,z931,z4,z5,z6]),(0,[z1,z8,z932,z4,z12,z6])],[(0,[z230,z2,z3,z4,z5,z6]),(0,[z1,z8,z545,z4,z5,z6]),(0,[z1,z8,z555,z3,z4,z12]),(0,[z1,z8,z933,z3,z4,z6]),(0,[z1,z8,z4,z5,z913,z15])],[(0,[z2,z36,z3,z144,z5,z6]),(0,[z1,z8,z3,z4,z12,z442]),(0,[z1,z934,z3,z4,z5,z6])],[(0,[z1,z76,z3,z4,z34,z6]),(0,[z935,z8,z3,z4,z5,z6]),(0,[z1,z8,z4,z178,z6,z22])]],
   [[(0,[z1,z8,z936,z4,z5,z6]),(0,[z1,z14,z3,z544,z5,z6]),(0,[z285,z1,z3,z4,z466,z6])],[(0,[z1,z8,z3,z4,z5,z820]),(0,[z1,z8,z3,z4,z5,z937]),(0,[z1,z938,z3,z4,z5,z6]),(0,[z1,z8,z3,z635,z34,z6]),(0,[z1,z8,z3,z4,z939,z6]),(0,[z1,z8,z31,z157,z108,z6]),(1,[z1,z8,z3,z5,z819]),(0,[z1,z8,z3,z4,z6,z940])],[(0,[z570,z8,z3,z4,z5,z6]),(0,[z74,z2,z3,z4,z34,z6]),(0,[z266,z14,z3,z4,z5,z6]),(0,[z941,z8,z3,z4,z5,z6])],[(0,[z1,z457,z31,z3,z4,z6]),(0,[z1,z942,z3,z4,z5,z6]),(0,[z943,z8,z31,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z238]),(0,[z1,z8,z893,z3,z4,z6])],[(0,[z1,z8,z3,z4,z944,z6]),(0,[z1,z2,z3,z4,z5,z728]),(0,[z1,z8,z735,z3,z4,z6]),(0,[z8,z3,z795,z144,z5,z6]),(0,[z689,z1,z8,z3,z5,z42]),(0,[z1,z8,z3,z4,z945,z6])],[(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z441,z3,z4,z63,z6]),(0,[z717,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z842]),(0,[z947,z8,z3,z4,z5,z6])],[(0,[z1,z948,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z66,z104]),(0,[z1,z8,z3,z544,z12,z6]),(0,[z1,z8,z576,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z949]),(0,[z1,z8,z521,z4,z56,z6]),(0,[z286,z1,z3,z4,z550,z6]),(0,[z1,z8,z3,z203,z10,z6]),(0,[z1,z445,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z950,z6])],[(0,[z1,z54,z3,z4,z63,z6]),(0,[z1,z8,z951,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z952]),(0,[z953,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z5,z6]),(0,[z329,z1,z3,z4,z6,z299]),(0,[z266,z8,z3,z4,z12,z6]),(0,[z1,z8,z637,z36,z5,z6])],[(0,[z2,z3,z4,z5,z6,z146]),(0,[z1,z8,z3,z954,z5,z6]),(0,[z1,z8,z3,z859,z5,z6]),(0,[z60,z462,z3,z32,z5,z6]),(0,[z955,z8,z3,z4,z5,z6])],[(1,[z741,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z417,z6]),(1,[z1,z3,z744,z5,z6]),(0,[z1,z8,z3,z37,z377,z75])],[(0,[z1,z2,z3,z4,z252,z6]),(0,[z1,z383,z31,z3,z4,z6]),(0,[z1,z8,z3,z956,z5,z6]),(0,[z18,z8,z3,z4,z280,z6])],[(0,[z2,z3,z4,z316,z5,z6]),(0,[z449,z2,z3,z4,z5,z6]),(0,[z30,z1,z14,z31,z3,z4]),(0,[z1,z8,z3,z544,z34,z6]),(0,[z1,z8,z3,z4,z957,z6]),(0,[z1,z8,z3,z4,z958,z6]),(0,[z8,z3,z32,z795,z5,z6]),(0,[z1,z8,z3,z4,z959,z6]),(0,[z960,z8,z3,z4,z5,z6]),(0,[z961,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z962,z6])],[(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z2,z3,z320,z5,z6]),(0,[z1,z8,z3,z4,z963,z6])],[(0,[z0,z8,z3,z4,z106,z6]),(0,[z266,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z964,z6]),(0,[z1,z8,z3,z320,z6,z155])]],
   [[(0,[z8,z2,z3,z4,z56,z6])],[(0,[z1,z2,z301,z3,z5,z6]),(0,[z120,z8,z3,z4,z5,z129])],[(0,[z1,z2,z4,z5,z6,z751]),(0,[z1,z14,z3,z4,z529,z6]),(0,[z1,z965,z3,z4,z5,z6]),(0,[z1,z8,z966,z4,z5,z6]),(0,[z1,z862,z3,z4,z5,z6]),(0,[z65,z1,z8,z4,z5,z913])],[(0,[z1,z8,z240,z4,z5,z6]),(0,[z1,z8,z967,z3,z4,z6]),(0,[z1,z8,z3,z4,z12,z273]),(0,[z1,z8,z372,z37,z5,z75])],[(0,[z2,z3,z4,z5,z327,z6]),(0,[z1,z968,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z969,z6]),(0,[z1,z8,z3,z4,z253,z6]),(0,[z33,z1,z3,z4,z5,z846]),(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z8,z971,z4,z5,z6]),(0,[z1,z8,z3,z5,z6,z842]),(0,[z1,z709,z31,z3,z4,z6])],[(0,[z60,z2,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z5,z972]),(0,[z1,z8,z973,z3,z5,z6]),(0,[z1,z8,z3,z4,z974,z6])],[(0,[z1,z8,z3,z4,z34,z6]),(0,[z2,z3,z4,z5,z425,z6]),(0,[z8,z3,z975,z4,z5,z6]),(0,[z1,z8,z976,z4,z5,z6]),(0,[z1,z8,z3,z4,z977,z6]),(0,[z1,z8,z3,z4,z6,z978])],[(0,[z1,z2,z3,z4,z380,z6]),(0,[z2,z3,z4,z56,z66,z6]),(0,[z1,z979,z3,z4,z5,z6]),(0,[z1,z8,z3,z421,z5,z156]),(0,[z48,z366,z151,z4,z5,z6]),(0,[z103,z76,z3,z4,z5,z104]),(0,[z1,z8,z240,z27,z5,z6]),(0,[z980,z8,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z981]),(0,[z1,z8,z3,z123,z83,z6])],[(0,[z48,z2,z3,z4,z49,z6]),(0,[z1,z8,z3,z4,z982,z6]),(0,[z0,z8,z3,z4,z983,z6]),(0,[z28,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z6,z206]),(0,[z1,z8,z3,z4,z984,z6])],[(0,[z554,z8,z151,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z575]),(0,[z1,z8,z545,z4,z56,z6]),(0,[z1,z8,z3,z4,z985,z6]),(0,[z1,z8,z3,z4,z5,z986])],[(0,[z1,z8,z3,z4,z639,z6])],[(0,[z60,z987,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z8,z3,z4,z795,z5,z6]),(0,[z1,z8,z3,z4,z988,z6]),(0,[z1,z46,z3,z4,z47,z6])],[(0,[z31,z2,z3,z132,z4,z6]),(0,[z1,z8,z31,z3,z4,z238]),(0,[z248,z3,z4,z27,z5,z6]),(0,[z1,z8,z157,z108,z6,z91]),(0,[z989,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z990,z12,z6])],[(0,[z1,z2,z3,z4,z275,z6]),(0,[z2,z3,z4,z5,z6,z433]),(0,[z1,z366,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z109,z85]),(0,[z1,z8,z3,z4,z6,z991]),(0,[z248,z8,z3,z4,z134,z6]),(0,[z1,z8,z108,z6,z22,z116])],[(0,[z148,z2,z3,z4,z5,z6]),(0,[z1,z8,z132,z4,z5,z238]),(0,[z1,z8,z3,z4,z992,z6])],[(0,[z1,z8,z3,z4,z993,z6]),(0,[z28,z8,z3,z4,z12,z6]),(0,[z1,z8,z994,z4,z5,z6]),(0,[z1,z8,z995,z4,z12,z6])]],
   [[(0,[z59,z1,z14,z4,z6,z22]),(0,[z1,z8,z3,z4,z216,z85])],[(0,[z1,z8,z3,z4,z5,z996]),(0,[z1,z8,z3,z4,z5,z997]),(0,[z1,z8,z3,z4,z998,z6])],[(0,[z1,z2,z3,z4,z279,z6]),(0,[z19,z1,z8,z246,z6,z116])],[(0,[z111,z2,z3,z4,z12,z6]),(0,[z1,z999,z3,z4,z5,z6]),(0,[z1,z8,z3,z1000,z5,z6]),(0,[z1,z342,z3,z4,z252,z6]),(0,[z65,z1,z8,z4,z5,z419]),(0,[z1001,z8,z3,z4,z5,z6])],[(0,[z1,z46,z3,z4,z344,z6]),(0,[z606,z8,z3,z32,z5,z6]),(0,[z41,z1,z8,z3,z102,z42])],[(0,[z1,z8,z3,z4,z5,z762]),(0,[z1,z8,z3,z4,z1002,z6]),(0,[z28,z8,z3,z4,z34,z6]),(0,[z41,z1,z8,z3,z456,z42])],[(0,[z2,z100,z3,z4,z56,z6]),(0,[z1,z346,z3,z4,z252,z6]),(0,[z1,z8,z3,z4,z5,z1003])],[(0,[z381,z2,z3,z4,z5,z6]),(0,[z39,z8,z3,z4,z5,z104]),(0,[z1,z1004,z3,z4,z5,z6]),(0,[z1,z8,z96,z4,z56,z6])],[(0,[z31,z2,z3,z4,z104,z6]),(0,[z35,z14,z3,z4,z5,z6]),(0,[z1,z8,z132,z320,z5,z6]),(0,[z60,z8,z31,z3,z32,z6]),(0,[z1005,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1006,z6]),(0,[z1,z1007,z3,z4,z12,z6])],[(0,[z1,z8,z3,z421,z56,z6]),(0,[z1,z8,z1008,z4,z5,z6])],[(0,[z8,z2,z3,z4,z227,z6]),(0,[z1,z441,z3,z4,z5,z156]),(0,[z1,z193,z3,z4,z334,z6]),(0,[z1,z8,z3,z4,z1009,z6]),(0,[z103,z8,z3,z4,z121,z104]),(0,[z1010,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z1011]),(0,[z1,z8,z37,z70,z5,z75]),(0,[z1,z8,z3,z4,z6,z1012]),(0,[z1,z8,z1013,z4,z12,z6])],[(0,[z1,z2,z139,z3,z4,z6]),(0,[z1,z145,z3,z4,z5,z6]),(0,[z1,z1014,z3,z4,z5,z6]),(0,[z1,z8,z796,z4,z5,z6]),(0,[z19,z1,z8,z3,z6,z396])],[(0,[z428,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z6]),(0,[z285,z2,z3,z4,z56,z6]),(0,[z8,z2,z231,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z85]),(0,[z1,z54,z3,z4,z5,z156]),(0,[z570,z207,z3,z4,z5,z6]),(0,[z65,z1,z8,z4,z5,z15])],[(0,[z2,z321,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z798,z6]),(0,[z1,z2,z3,z4,z456,z6]),(0,[z120,z8,z3,z4,z56,z129])],[(0,[z2,z3,z4,z5,z6,z208]),(0,[z0,z205,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z777]),(0,[z1,z8,z3,z794,z5,z6]),(0,[z103,z8,z3,z4,z5,z104]),(0,[z1,z8,z3,z1015,z5,z6]),(0,[z26,z1,z240,z27,z5,z6])],[(0,[z48,z8,z622,z4,z5,z6]),(0,[z1,z8,z3,z1016,z5,z6]),(0,[z51,z1,z68,z4,z5,z85]),(0,[z35,z8,z3,z4,z12,z6]),(0,[z19,z1,z8,z3,z6,z162])]],
   [[(0,[z1,z1017,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1018,z6])],[(0,[z26,z1,z3,z27,z34,z6])],[(0,[z2,z3,z4,z5,z75,z104]),(0,[z8,z2,z3,z4,z90,z6]),(0,[z1,z14,z3,z4,z63,z6]),(0,[z1,z14,z3,z4,z5,z64])],[(0,[z1,z2,z3,z4,z436,z6]),(0,[z1,z8,z1019,z3,z4,z6]),(0,[z0,z346,z3,z4,z5,z6]),(0,[z48,z441,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1020,z6]),(0,[z1,z766,z31,z3,z4,z6])],[(0,[z48,z31,z2,z3,z4,z6]),(0,[z1,z8,z31,z3,z421,z6]),(0,[z1,z917,z3,z4,z5,z6]),(0,[z1,z8,z604,z4,z6,z22])],[(0,[z1,z8,z3,z4,z56,z575]),(0,[z1,z8,z360,z3,z4,z6]),(0,[z35,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z1021,z6]),(0,[z1,z8,z3,z4,z5,z1022]),(0,[z1,z8,z3,z4,z134,z58])],[(0,[z853,z1,z8,z4,z5,z6]),(0,[z1,z8,z470,z108,z5,z6]),(0,[z1,z8,z3,z4,z12,z548])],[(0,[z285,z1,z3,z4,z212,z6]),(0,[z1,z8,z3,z1023,z5,z6]),(0,[z1,z8,z178,z5,z6,z22])],[(0,[z74,z741,z3,z4,z5,z6]),(0,[z485,z2,z3,z4,z5,z6]),(0,[z1,z1024,z3,z4,z5,z6]),(0,[z1,z8,z1025,z4,z5,z6]),(0,[z1026,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z1027])],[(0,[z48,z2,z132,z4,z5,z6]),(0,[z1,z457,z3,z4,z380,z6]),(0,[z1,z1028,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z64]),(0,[z1,z8,z3,z530,z5,z6]),(0,[z355,z1,z8,z3,z6,z116]),(0,[z1029,z8,z31,z3,z4,z6])],[],[(0,[z1,z8,z3,z4,z474,z6]),(1,[z2,z3,z530,z5,z6]),(0,[z2,z3,z4,z5,z466,z6]),(0,[z1,z8,z3,z4,z1030,z6])],[(0,[z74,z2,z3,z4,z313,z6]),(0,[z1,z441,z3,z4,z56,z6]),(0,[z1,z76,z3,z4,z12,z6])],[(0,[z1,z8,z3,z4,z1031,z6]),(0,[z1,z8,z3,z4,z1032,z6]),(0,[z1,z8,z3,z5,z75,z819])],[(0,[z1,z54,z3,z4,z56,z6]),(0,[z1,z8,z3,z1033,z5,z6]),(0,[z1,z1034,z3,z4,z5,z6]),(0,[z1,z825,z3,z4,z5,z6])],[(0,[z74,z2,z3,z4,z12,z6]),(0,[z1,z14,z3,z4,z227,z6]),(0,[z1,z14,z101,z4,z11,z6]),(0,[z1,z8,z3,z4,z34,z64]),(0,[z128,z8,z3,z144,z5,z64]),(0,[z1,z8,z3,z4,z5,z1035]),(0,[z1,z8,z4,z1036,z5,z6])]],
   [[(0,[z293,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z1037]),(0,[z1,z207,z3,z4,z34,z6]),(0,[z51,z1,z852,z4,z5,z6])],[(0,[z286,z1,z3,z4,z21,z6]),(0,[z1,z8,z3,z4,z56,z762]),(0,[z1,z8,z3,z4,z1038,z6]),(0,[z1,z1039,z3,z4,z5,z6])],[(0,[z2,z3,z4,z56,z75,z6]),(0,[z309,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z413,z109,z6])],[(0,[z257,z2,z3,z4,z5,z6]),(0,[z51,z2,z3,z4,z56,z6]),(0,[z1,z14,z3,z4,z5,z1040])],[(0,[z1,z8,z3,z1041,z5,z6]),(0,[z1,z8,z3,z544,z5,z6]),(0,[z1,z1042,z3,z4,z5,z6]),(0,[z1,z1043,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z85])],[(0,[z2,z3,z4,z395,z5,z6]),(0,[z2,z3,z123,z4,z56,z6]),(0,[z329,z1,z3,z4,z21,z6]),(0,[z1,z8,z3,z4,z1044,z6]),(0,[z340,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z413,z216,z6]),(0,[z1,z8,z3,z4,z1045,z6]),(0,[z1,z8,z31,z301,z3,z6])],[(0,[z2,z3,z398,z4,z5,z6]),(0,[z2,z3,z351,z4,z56,z6]),(0,[z1,z8,z3,z4,z6,z1046]),(0,[z1,z8,z1047,z4,z5,z6]),(0,[z1,z8,z3,z4,z786,z58])],[(0,[z1,z8,z151,z544,z5,z6]),(0,[z131,z8,z132,z4,z5,z238]),(0,[z28,z8,z3,z635,z5,z6]),(0,[z1048,z8,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z121,z6]),(0,[z1,z14,z4,z70,z5,z6]),(0,[z1,z8,z3,z4,z1049,z6]),(0,[z642,z8,z3,z4,z56,z6]),(0,[z65,z1,z8,z4,z56,z15]),(0,[z1,z8,z3,z4,z6,z1050]),(0,[z1,z8,z3,z4,z1051,z6]),(0,[z248,z177,z3,z4,z5,z6]),(0,[z1052,z8,z3,z4,z12,z6])],[(0,[z285,z1,z3,z4,z50,z6]),(0,[z24,z1,z8,z3,z6,z162])],[(0,[z1,z462,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z1053,z6])],[(0,[z1,z8,z3,z4,z5,z1054]),(0,[z1,z8,z320,z5,z66,z6]),(0,[z1,z8,z3,z5,z819,z42])],[(0,[z2,z3,z4,z56,z6,z405]),(0,[z1,z8,z231,z4,z5,z104]),(0,[z1,z8,z3,z4,z815,z6])],[(0,[z1,z14,z3,z135,z5,z6]),(0,[z1,z14,z3,z4,z12,z136]),(0,[z79,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z6,z1055]),(0,[z1,z3,z4,z5,z841,z6]),(0,[z1,z8,z3,z4,z1056,z6])],[(0,[z84,z224,z3,z4,z5,z6]),(0,[z624,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z1057]),(0,[z1,z8,z3,z1058,z12,z6])],[(0,[z1,z8,z3,z4,z12,z274]),(0,[z1,z193,z545,z4,z5,z6]),(0,[z1,z8,z4,z70,z12,z6])]],
   [[(0,[z1,z8,z3,z4,z313,z6]),(0,[z1,z8,z1059,z4,z5,z6]),(0,[z1,z8,z387,z3,z4,z12])],[(0,[z1,z2,z3,z413,z5,z6])],[(0,[z420,z2,z3,z144,z5,z6]),(0,[z60,z2,z3,z4,z12,z6]),(0,[z1,z224,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z90,z104]),(0,[z120,z8,z3,z4,z13,z6]),(0,[z1060,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z1061])],[(0,[z1,z8,z3,z4,z12,z6]),(0,[z1,z2,z3,z4,z334,z6]),(0,[z1,z8,z3,z4,z6,z1062]),(0,[z1,z8,z3,z4,z1063,z6])],[(0,[z1,z14,z152,z3,z4,z6]),(0,[z1,z14,z3,z4,z1064,z6]),(0,[z1,z8,z3,z4,z1065,z6]),(0,[z1,z8,z3,z4,z1066,z6]),(0,[z1,z8,z118,z4,z11,z6]),(0,[z51,z1,z68,z413,z5,z6]),(0,[z1,z8,z3,z135,z12,z6])],[(0,[z1,z8,z3,z5,z6,z1067]),(0,[z84,z8,z3,z4,z34,z6]),(0,[z1,z8,z4,z70,z34,z6]),(0,[z1,z8,z3,z4,z12,z649]),(0,[z1,z1068,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z529,z6]),(0,[z1,z14,z3,z4,z5,z156]),(0,[z41,z1,z8,z3,z4,z90]),(0,[z1,z8,z3,z4,z95,z601]),(0,[z120,z8,z3,z250,z5,z129]),(0,[z30,z1,z8,z722,z3,z4])],[(0,[z570,z8,z3,z4,z5,z52]),(0,[z1069,z8,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z95,z6]),(0,[z597,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z6]),(0,[z1,z8,z3,z4,z275,z238]),(0,[z494,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1070,z6])],[(0,[z1,z8,z3,z1071,z5,z6]),(0,[z1,z8,z1072,z3,z4,z238]),(0,[z1,z1073,z3,z4,z5,z6]),(0,[z128,z8,z3,z144,z5,z6]),(0,[z1074,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z990,z5,z6]),(0,[z484,z1,z8,z4,z6,z406])],[(0,[z509,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z135,z34,z6])],[(0,[z1,z2,z3,z4,z5,z758]),(0,[z2,z3,z4,z47,z56,z6]),(0,[z1,z67,z3,z4,z5,z107]),(0,[z1,z46,z3,z4,z245,z6]),(0,[z1,z1075,z3,z4,z5,z6]),(0,[z1,z1076,z3,z4,z5,z6]),(0,[z8,z151,z975,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z591]),(0,[z1,z8,z4,z1077,z5,z6]),(0,[z1,z8,z3,z4,z5,z125]),(0,[z1,z1078,z3,z4,z12,z6])],[(0,[z152,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z104,z6]),(0,[z0,z8,z3,z4,z252,z6]),(0,[z60,z14,z3,z32,z5,z6]),(0,[z293,z8,z3,z4,z56,z6]),(0,[z1,z8,z995,z4,z5,z6]),(0,[z1,z270,z31,z3,z4,z107])],[(0,[z1,z8,z3,z4,z1079,z6]),(0,[z48,z948,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z156]),(0,[z1,z193,z96,z4,z5,z6]),(0,[z215,z1,z68,z4,z5,z6]),(0,[z33,z18,z3,z4,z5,z88]),(0,[z1,z8,z1080,z3,z4,z6])],[(0,[z1,z2,z3,z4,z160,z6]),(0,[z1,z14,z3,z4,z5,z52]),(0,[z1,z8,z1081,z4,z5,z6])],[(0,[z1,z8,z3,z4,z1082,z6]),(0,[z1,z8,z1083,z4,z5,z6]),(0,[z1,z8,z3,z250,z639,z6]),(0,[z1,z8,z1084,z3,z4,z6]),(0,[z1,z8,z3,z4,z1085,z6])]],
   [[(0,[z111,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z1086]),(0,[z131,z8,z132,z4,z275,z6]),(0,[z1,z1087,z3,z4,z5,z6]),(0,[z1,z8,z3,z1088,z5,z6])],[(0,[z1,z14,z1089,z3,z4,z6]),(0,[z1,z8,z3,z1090,z4,z6]),(0,[z570,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1091,z6]),(0,[z1,z8,z736,z3,z5,z6]),(0,[z1,z1092,z3,z4,z5,z6]),(0,[z1,z8,z400,z3,z4,z12])],[(0,[z1,z8,z3,z4,z1093,z6]),(0,[z1,z2,z888,z4,z5,z6])],[(0,[z1,z8,z3,z4,z34,z156]),(0,[z1094,z8,z3,z4,z5,z6])],[(0,[z2,z3,z144,z108,z5,z6]),(0,[z620,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1095,z6]),(0,[z1,z8,z1096,z3,z4,z6]),(0,[z65,z1,z8,z31,z4,z15])],[(0,[z8,z2,z3,z4,z106,z6]),(0,[z128,z2,z3,z4,z56,z6]),(0,[z8,z152,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z280,z6]),(0,[z1,z14,z3,z178,z5,z6]),(0,[z1,z8,z3,z4,z12,z52]),(0,[z1,z8,z1097,z4,z5,z6]),(0,[z1,z8,z843,z3,z4,z58]),(0,[z1,z1007,z3,z4,z5,z6])],[(0,[z1,z2,z521,z4,z5,z6]),(0,[z19,z1,z2,z3,z6,z116]),(0,[z1,z8,z576,z4,z56,z6]),(0,[z1,z499,z3,z4,z5,z107]),(0,[z1,z8,z3,z4,z1098,z6])],[(0,[z1,z8,z3,z4,z5,z1099]),(0,[z1,z8,z1100,z4,z5,z6]),(0,[z1,z8,z1013,z4,z5,z6])],[(0,[z1,z14,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z898,z6]),(0,[z1101,z8,z3,z4,z5,z6])],[(0,[z948,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z242,z6]),(0,[z48,z8,z151,z4,z12,z6]),(0,[z60,z8,z3,z32,z34,z6]),(0,[z1,z8,z3,z4,z1102,z6]),(0,[z1,z472,z3,z4,z47,z6])],[(0,[z1,z8,z3,z4,z881,z6]),(0,[z1,z8,z3,z4,z1103,z6]),(0,[z1,z8,z3,z895,z5,z6]),(0,[z1,z8,z231,z4,z5,z129]),(0,[z1,z1104,z3,z4,z5,z6])],[(0,[z2,z3,z132,z4,z34,z6]),(0,[z1,z8,z3,z4,z1105,z6]),(0,[z1,z8,z3,z4,z34,z52])],[(0,[z35,z8,z3,z4,z5,z6]),(0,[z1,z14,z3,z1106,z5,z6]),(0,[z195,z8,z3,z4,z34,z6]),(0,[z1107,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z371,z5,z75]),(0,[z1,z8,z3,z178,z12,z6])],[(0,[z150,z1,z68,z4,z5,z6]),(0,[z1,z8,z3,z544,z63,z6]),(0,[z1,z8,z3,z1108,z4,z6])],[(0,[z2,z151,z3,z4,z56,z6]),(0,[z120,z2,z3,z4,z5,z104]),(0,[z1,z8,z3,z1109,z5,z6]),(0,[z18,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z198,z6]),(0,[z1,z224,z3,z4,z56,z6]),(0,[z570,z8,z3,z4,z109,z6]),(0,[z26,z1,z3,z27,z12,z6]),(0,[z35,z527,z3,z4,z5,z6])],[(0,[z48,z8,z151,z4,z34,z6]),(0,[z1,z8,z3,z915,z5,z6]),(0,[z65,z1,z8,z3,z4,z90]),(0,[z1,z8,z3,z4,z1110,z6]),(0,[z1,z8,z278,z108,z5,z6]),(0,[z1,z8,z3,z1111,z4,z6]),(0,[z1,z8,z3,z5,z6,z819])]],
   [[(0,[z2,z157,z3,z4,z56,z6]),(0,[z1,z441,z31,z3,z4,z6]),(0,[z1,z8,z3,z795,z5,z6]),(0,[z1,z8,z3,z4,z1112,z6]),(0,[z1,z8,z3,z4,z90,z129]),(0,[z28,z8,z3,z4,z1091,z6]),(0,[z1,z8,z70,z5,z75,z6])],[(0,[z1,z8,z3,z4,z5,z1113]),(0,[z1,z8,z3,z4,z1114,z6]),(0,[z84,z8,z3,z4,z707,z6])],[(0,[z1,z8,z3,z4,z5,z1115]),(0,[z1,z8,z240,z4,z56,z6]),(0,[z1,z1116,z3,z4,z5,z6]),(0,[z1,z8,z3,z178,z34,z6]),(0,[z1,z8,z3,z4,z6,z1117]),(0,[z127,z1,z3,z4,z21,z6])],[(0,[z1,z8,z3,z4,z13,z6]),(0,[z1,z8,z3,z4,z1118,z56]),(0,[z1,z8,z68,z413,z5,z6]),(0,[z1,z8,z3,z4,z5,z1119]),(0,[z1,z8,z3,z123,z183,z6])],[(0,[z2,z3,z4,z531,z5,z6]),(0,[z1,z462,z3,z4,z417,z6])],[(0,[z1,z1120,z3,z4,z5,z6]),(0,[z1,z2,z923,z3,z4,z6]),(1,[z2,z3,z4,z13,z6]),(0,[z520,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z109,z6]),(0,[z1,z366,z3,z4,z49,z6]),(0,[z128,z8,z3,z144,z56,z6]),(0,[z1,z8,z3,z4,z707,z6]),(0,[z1,z76,z3,z4,z121,z6]),(0,[z18,z8,z3,z4,z12,z6]),(0,[z65,z1,z8,z29,z4,z15]),(0,[z1,z8,z1121,z4,z12,z6]),(0,[z1,z8,z397,z4,z481,z6])],[(0,[z1,z8,z3,z4,z63,z6]),(0,[z1,z8,z3,z4,z1122,z6]),(0,[z1,z8,z3,z4,z5,z64]),(0,[z26,z1,z3,z27,z5,z125]),(0,[z1,z8,z31,z3,z135,z6])],[(0,[z1,z8,z3,z4,z56,z125])],[(0,[z1,z2,z545,z4,z5,z6]),(0,[z355,z2,z3,z4,z56,z6]),(0,[z0,z2,z3,z4,z56,z6]),(0,[z128,z8,z31,z3,z144,z6]),(0,[z1,z8,z3,z4,z1123,z6]),(0,[z1,z8,z31,z246,z4,z6]),(0,[z1,z8,z3,z4,z1124,z6])],[(0,[z26,z2,z3,z4,z56,z6]),(0,[z1,z76,z3,z4,z5,z6]),(0,[z14,z386,z3,z4,z5,z6]),(0,[z103,z8,z152,z3,z4,z104]),(0,[z340,z8,z31,z3,z4,z6])],[(0,[z1,z8,z909,z4,z5,z6]),(0,[z1,z8,z3,z1125,z5,z6]),(0,[z1,z8,z31,z3,z4,z375]),(0,[z59,z1,z8,z4,z6,z406])],[(0,[z14,z741,z3,z4,z5,z6]),(0,[z18,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z1126,z6]),(0,[z1,z8,z3,z635,z5,z6])],[(0,[z74,z2,z3,z4,z5,z6]),(0,[z270,z2,z3,z4,z56,z6]),(0,[z1,z8,z1127,z3,z4,z6]),(0,[z1,z8,z932,z4,z5,z6]),(0,[z1,z1128,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1129,z6])],[(0,[z444,z2,z3,z4,z56,z6]),(0,[z1,z207,z3,z4,z12,z6])],[(0,[z14,z391,z3,z4,z5,z6]),(0,[z60,z145,z3,z32,z5,z6]),(0,[z119,z1,z8,z4,z6,z357]),(0,[z1130,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1131,z6]),(0,[z1,z8,z4,z1132,z5,z6])],[(0,[z1,z8,z3,z4,z1133,z6]),(0,[z314,z2,z3,z4,z5,z6]),(0,[z2,z3,z37,z144,z5,z6]),(0,[z2,z3,z4,z56,z6,z22]),(0,[z1,z8,z3,z4,z1134,z6]),(0,[z1,z8,z31,z372,z4,z6])]],
   [[(0,[z1,z8,z3,z4,z1135,z125])],[(0,[z1,z8,z3,z123,z254,z6]),(0,[z539,z1,z8,z3,z5,z42]),(0,[z1,z8,z3,z4,z1136,z6]),(0,[z1,z8,z3,z4,z1137,z6])],[(0,[z14,z2,z3,z4,z12,z6]),(0,[z389,z2,z3,z4,z5,z6]),(0,[z0,z462,z3,z4,z5,z6]),(0,[z1,z8,z3,z1000,z56,z6]),(0,[z51,z1,z31,z68,z4,z6]),(0,[z1138,z8,z3,z4,z5,z6])],[(0,[z8,z3,z4,z5,z6,z1139]),(0,[z1,z8,z3,z4,z6,z1140])],[(0,[z1,z14,z231,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z913])],[(0,[z2,z479,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z6,z155]),(0,[z1,z8,z3,z4,z1141,z6]),(0,[z1,z8,z1142,z4,z5,z6]),(0,[z1052,z8,z3,z4,z5,z6]),(0,[z1,z1143,z3,z4,z5,z6])],[(0,[z1,z2,z96,z4,z5,z6]),(0,[z1,z14,z3,z4,z328,z6]),(0,[z1,z8,z1144,z3,z4,z6]),(0,[z33,z1,z3,z4,z88,z56])],[(0,[z1,z8,z3,z4,z6,z1145]),(0,[z1,z8,z3,z4,z5,z1146])],[(0,[z14,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z421,z5,z6]),(0,[z2,z3,z4,z56,z56,z6]),(0,[z2,z3,z231,z4,z5,z6]),(0,[z1,z420,z3,z200,z5,z6]),(0,[z131,z8,z132,z421,z5,z6]),(0,[z1,z270,z147,z3,z4,z107])],[(0,[z2,z3,z4,z34,z56,z6]),(0,[z266,z8,z3,z4,z5,z6]),(0,[z1,z1147,z3,z4,z5,z6]),(0,[z409,z1,z3,z4,z21,z6])],[(0,[z1,z14,z3,z4,z90,z6]),(0,[z537,z1,z307,z4,z5,z6]),(0,[z1,z145,z3,z4,z56,z6])],[(0,[z184,z2,z3,z4,z5,z6]),(0,[z1,z14,z246,z4,z5,z6]),(0,[z1,z8,z231,z4,z12,z6]),(0,[z361,z8,z3,z4,z5,z129])],[(0,[z120,z2,z3,z4,z5,z129]),(0,[z248,z14,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z121,z6]),(0,[z8,z3,z4,z34,z220,z6]),(0,[z120,z8,z231,z4,z5,z129]),(0,[z1,z8,z510,z108,z5,z6]),(0,[z1,z8,z4,z108,z6,z91]),(0,[z1,z8,z4,z70,z5,z6]),(0,[z1,z684,z8,z4,z5,z15])],[(0,[z1,z1148,z3,z4,z5,z6]),(0,[z103,z8,z3,z4,z56,z104]),(0,[z1,z8,z124,z4,z276,z6]),(0,[z1,z8,z3,z635,z5,z52]),(0,[z561,z1,z8,z31,z3,z4]),(0,[z1,z8,z3,z4,z1149,z6]),(0,[z1,z8,z1150,z4,z5,z6]),(0,[z1,z1151,z3,z4,z12,z6])],[(0,[z1,z8,z3,z4,z5,z1152]),(0,[z1,z8,z3,z4,z1153,z6])],[(0,[z60,z2,z3,z4,z5,z6]),(0,[z1,z8,z576,z250,z5,z6]),(0,[z570,z8,z3,z4,z1154,z6]),(0,[z1155,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z37,z75,z206])]],
   [[(0,[z1,z8,z3,z4,z5,z6]),(0,[z1,z8,z240,z4,z328,z6]),(0,[z1,z8,z3,z4,z1156,z6]),(0,[z33,z1,z3,z4,z280,z88]),(0,[z1,z8,z3,z178,z11,z6])],[(0,[z554,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z250,z5,z6]),(0,[z1,z8,z3,z544,z5,z156]),(0,[z1,z8,z96,z4,z380,z6]),(0,[z453,z1,z8,z3,z4,z12]),(0,[z1,z8,z3,z4,z1157,z6]),(0,[z1,z8,z231,z4,z34,z6]),(0,[z293,z8,z179,z4,z5,z6]),(0,[z1,z8,z31,z3,z320,z6])],[(0,[z8,z3,z623,z4,z56,z6]),(0,[z1,z8,z246,z4,z12,z6])],[(0,[z248,z8,z3,z4,z12,z6]),(0,[z1,z1158,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z575]),(0,[z1,z8,z1159,z4,z5,z6]),(0,[z1,z8,z3,z4,z810,z85]),(0,[z1,z1160,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1161,z6])],[(0,[z84,z8,z3,z4,z529,z6]),(0,[z1,z14,z3,z29,z4,z6]),(0,[z1,z8,z3,z4,z1162,z6]),(0,[z1,z8,z231,z4,z639,z6]),(0,[z570,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z1163,z6]),(0,[z1,z8,z31,z3,z4,z411])],[(0,[z1,z8,z96,z144,z5,z6]),(0,[z8,z3,z4,z34,z241,z6]),(0,[z248,z8,z240,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z1164]),(0,[z1,z8,z3,z4,z1165,z6])],[(0,[z1,z987,z3,z4,z5,z6]),(0,[z1,z8,z574,z108,z5,z6]),(0,[z1,z8,z3,z635,z56,z6]),(0,[z1,z8,z1025,z4,z56,z6]),(0,[z1,z294,z447,z3,z4,z6])],[(0,[z2,z3,z4,z95,z104,z6]),(0,[z1,z14,z3,z1166,z5,z6]),(0,[z1,z8,z3,z530,z56,z6]),(0,[z1,z8,z246,z4,z34,z6]),(0,[z1,z8,z3,z250,z12,z6]),(0,[z1,z8,z3,z4,z1167,z6]),(0,[z293,z8,z3,z4,z5,z58]),(0,[z1,z1078,z3,z4,z5,z6]),(0,[z1,z1168,z3,z4,z5,z6])],[(0,[z247,z8,z3,z144,z5,z6]),(0,[z8,z632,z3,z4,z56,z6]),(0,[z1,z527,z3,z4,z580,z6]),(0,[z684,z8,z3,z4,z56,z6]),(0,[z248,z8,z3,z4,z34,z6])],[(0,[z1,z8,z3,z4,z1169,z6]),(0,[z2,z3,z4,z5,z6,z578])],[(0,[z131,z441,z132,z4,z5,z6]),(0,[z1,z1170,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1171,z6]),(0,[z1,z1172,z3,z4,z5,z6]),(0,[z1,z8,z3,z1173,z5,z6]),(0,[z120,z76,z3,z4,z5,z6]),(0,[z248,z8,z3,z4,z5,z125]),(0,[z1,z8,z4,z70,z6,z206])],[(0,[z41,z1,z2,z3,z5,z42]),(0,[z1,z8,z31,z576,z4,z6]),(0,[z1,z112,z3,z4,z47,z6]),(0,[z1,z8,z3,z4,z5,z819])],[(0,[z2,z3,z4,z5,z503,z6]),(0,[z346,z2,z3,z4,z5,z6]),(0,[z0,z14,z3,z4,z34,z6]),(0,[z1,z14,z179,z4,z5,z6]),(0,[z131,z54,z132,z4,z5,z6]),(0,[z661,z8,z3,z4,z34,z6]),(0,[z525,z1,z3,z4,z5,z88])],[(0,[z1,z8,z3,z4,z1174,z6]),(0,[z1,z8,z1175,z3,z4,z6]),(0,[z1,z8,z3,z250,z34,z6])],[(0,[z2,z100,z132,z4,z5,z6]),(0,[z28,z8,z3,z4,z5,z6]),(0,[z596,z1,z8,z4,z5,z15]),(0,[z1,z8,z31,z3,z530,z6]),(0,[z1,z8,z3,z4,z6,z206])]],
   [[(0,[z493,z2,z3,z4,z56,z6]),(0,[z1,z8,z31,z545,z4,z6]),(0,[z1,z8,z1176,z3,z4,z6]),(0,[z1,z493,z8,z31,z3,z4]),(0,[z51,z570,z68,z4,z5,z6]),(0,[z1,z8,z138,z4,z12,z66]),(0,[z1,z8,z31,z3,z1173,z6])],[(0,[z1,z8,z3,z4,z1177,z6]),(0,[z2,z132,z4,z108,z5,z6]),(0,[z1,z8,z3,z4,z5,z1178]),(0,[z1,z8,z3,z4,z1179,z6])],[(0,[z39,z2,z3,z4,z5,z104]),(0,[z1,z8,z852,z4,z5,z6]),(0,[z1,z8,z3,z4,z1180,z6]),(0,[z1,z8,z1181,z3,z4,z6]),(0,[z1,z8,z1182,z4,z12,z6])],[(0,[z2,z3,z4,z56,z6,z116]),(0,[z1,z14,z3,z4,z1183,z6]),(0,[z1,z8,z3,z544,z56,z6]),(0,[z120,z342,z3,z4,z5,z129])],[(0,[z120,z2,z576,z4,z5,z6]),(0,[z340,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z89,z6]),(0,[z1,z8,z3,z4,z5,z1086]),(0,[z1,z14,z3,z4,z5,z58]),(0,[z1,z8,z3,z1184,z5,z6]),(0,[z120,z8,z31,z3,z4,z129]),(0,[z1,z8,z179,z4,z12,z6])],[(0,[z247,z2,z3,z4,z56,z6]),(0,[z1,z8,z651,z108,z5,z6]),(0,[z1,z193,z3,z4,z12,z6]),(0,[z266,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1185,z6]),(0,[z285,z35,z3,z4,z21,z6])],[(0,[z2,z3,z4,z5,z6,z594]),(0,[z60,z8,z3,z32,z12,z6]),(0,[z1,z8,z1186,z4,z5,z6]),(0,[z120,z346,z3,z4,z5,z129]),(0,[z367,z1,z8,z4,z5,z15])],[(0,[z1,z8,z3,z1187,z5,z6]),(0,[z1,z8,z3,z4,z1188,z6]),(0,[z1,z8,z3,z4,z6,z1189])],[(0,[z2,z3,z132,z4,z12,z6]),(0,[z199,z2,z3,z4,z5,z6]),(0,[z235,z14,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z1190]),(0,[z1,z8,z3,z4,z1191,z6]),(0,[z1,z457,z96,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z1192]),(0,[z1,z8,z1193,z3,z4,z6])],[(0,[z8,z152,z139,z3,z4,z6])],[(0,[z41,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1194,z6]),(0,[z1,z8,z179,z4,z34,z6]),(0,[z18,z8,z3,z4,z1045,z6])],[(0,[z302,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z377,z6]),(0,[z1,z193,z3,z4,z34,z6]),(0,[z128,z193,z3,z144,z5,z6]),(0,[z1,z8,z3,z1195,z5,z6]),(0,[z26,z1,z3,z27,z5,z6]),(0,[z1,z8,z3,z4,z12,z58]),(0,[z1,z8,z31,z3,z4,z236])],[(0,[z1,z2,z3,z4,z164,z6]),(0,[z1,z8,z31,z3,z4,z575]),(0,[z1,z342,z3,z4,z639,z6]),(0,[z1,z8,z179,z4,z5,z125]),(0,[z1,z46,z3,z4,z841,z6]),(0,[z1,z1196,z3,z4,z5,z6])],[(0,[z289,z1,z8,z3,z6,z116])],[(0,[z1,z8,z3,z4,z1197,z6]),(0,[z1,z193,z3,z4,z5,z575]),(0,[z235,z224,z3,z4,z56,z6]),(0,[z8,z3,z4,z56,z6,z277]),(0,[z1,z8,z240,z4,z5,z58]),(0,[z1198,z8,z3,z4,z5,z6])],[(0,[z285,z1,z3,z4,z6,z299]),(1,[z8,z975,z4,z5,z6]),(0,[z1,z346,z3,z4,z639,z6]),(0,[z1,z8,z722,z3,z4,z6])]],
   [[(0,[z468,z2,z3,z4,z5,z6]),(0,[z1,z2,z360,z3,z4,z6]),(0,[z1,z8,z3,z4,z5,z1199]),(0,[z1,z8,z3,z1106,z5,z6]),(0,[z1,z8,z3,z4,z1200,z6])],[(0,[z1,z8,z3,z4,z34,z58]),(0,[z285,z1,z3,z4,z550,z6]),(0,[z28,z8,z3,z4,z5,z52]),(0,[z1201,z8,z3,z4,z5,z6]),(0,[z1,z8,z36,z736,z5,z6]),(0,[z1202,z8,z3,z4,z12,z6])],[(0,[z2,z3,z4,z5,z276,z6]),(0,[z8,z2,z3,z4,z252,z6]),(0,[z1,z8,z3,z4,z1118,z5]),(0,[z1,z8,z3,z4,z1203,z6]),(0,[z650,z8,z3,z4,z56,z6]),(0,[z1,z8,z1204,z4,z5,z6])],[(0,[z120,z2,z3,z4,z34,z6]),(0,[z235,z8,z3,z4,z13,z6]),(0,[z1,z177,z3,z45,z12,z6])],[(0,[z1,z8,z231,z530,z5,z6]),(0,[z570,z8,z3,z4,z216,z6]),(0,[z1,z8,z3,z413,z5,z85])],[(0,[z2,z3,z4,z5,z212,z6]),(0,[z0,z8,z3,z4,z279,z6]),(0,[z1,z54,z31,z3,z4,z6]),(0,[z235,z8,z3,z4,z707,z6])],[(0,[z2,z3,z4,z530,z5,z6]),(0,[z1,z2,z3,z4,z474,z6]),(0,[z1205,z1,z3,z4,z5,z6]),(0,[z1,z650,z8,z3,z5,z42]),(0,[z1,z8,z31,z722,z3,z4])],[(0,[z120,z2,z3,z4,z639,z6]),(0,[z597,z2,z3,z4,z56,z6]),(1,[z8,z3,z4,z5,z757])],[(0,[z1,z14,z3,z4,z1206,z6]),(0,[z1,z14,z3,z4,z6,z91]),(0,[z1,z8,z3,z638,z4,z12]),(0,[z1,z457,z3,z4,z334,z6]),(0,[z1,z8,z138,z3,z4,z90]),(0,[z1,z8,z31,z3,z4,z165])],[(0,[z1,z14,z3,z4,z1207,z6]),(0,[z1,z8,z3,z4,z5,z1208]),(0,[z340,z205,z3,z4,z5,z6]),(0,[z1,z8,z31,z3,z4,z338]),(0,[z1,z177,z3,z45,z34,z6]),(0,[z1,z8,z108,z5,z552,z6])],[(0,[z1,z207,z3,z4,z5,z6]),(0,[z2,z3,z4,z56,z21,z6]),(0,[z1,z8,z3,z4,z1209,z6]),(0,[z1,z1210,z3,z4,z5,z6]),(0,[z1,z46,z3,z4,z241,z6]),(0,[z1,z8,z246,z4,z10,z6])],[(0,[z152,z2,z3,z4,z56,z6]),(0,[z2,z3,z4,z5,z13,z6]),(0,[z293,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z216,z6]),(0,[z596,z1,z8,z3,z4,z12]),(0,[z28,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1211,z6])],[(0,[z2,z3,z4,z344,z56,z6]),(0,[z1,z8,z3,z4,z1212,z6]),(0,[z1,z8,z3,z4,z6,z1213]),(0,[z1,z8,z3,z4,z5,z1214])],[(0,[z1,z14,z3,z4,z106,z6]),(0,[z1,z8,z1215,z3,z4,z6]),(0,[z1,z8,z3,z4,z1216,z6]),(0,[z293,z8,z3,z4,z328,z6]),(0,[z1,z8,z3,z6,z842,z116])],[(0,[z2,z3,z4,z5,z104,z42]),(0,[z444,z1,z8,z4,z6,z22]),(0,[z1,z8,z3,z37,z5,z819])],[(0,[z14,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1217,z6]),(0,[z1,z147,z2,z3,z4,z6]),(0,[z627,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z5,z1218]),(0,[z643,z1,z8,z3,z6,z116])]],
   [[(0,[z1,z1219,z3,z4,z5,z6]),(0,[z570,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z49,z6]),(0,[z1,z8,z3,z4,z1220,z6]),(0,[z1,z8,z157,z108,z160,z6]),(0,[z1,z8,z3,z10,z6,z842])],[(0,[z2,z3,z4,z56,z6,z299]),(0,[z348,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z1221,z5,z6]),(0,[z1,z8,z32,z70,z5,z6]),(0,[z103,z8,z31,z3,z4,z104]),(0,[z1222,z8,z3,z4,z12,z6])],[(0,[z0,z14,z3,z4,z474,z6])],[(0,[z65,z2,z3,z4,z56,z6]),(0,[z1223,z2,z3,z4,z5,z6]),(0,[z182,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z421,z5,z238]),(0,[z1,z8,z3,z4,z5,z1224]),(0,[z1,z8,z3,z4,z63,z156]),(0,[z1,z1225,z3,z4,z5,z6])],[(0,[z1,z8,z3,z203,z72,z6]),(0,[z1,z8,z3,z4,z1226,z6]),(0,[z1,z3,z4,z744,z5,z6])],[(0,[z1,z2,z576,z4,z5,z6]),(0,[z14,z3,z4,z34,z56,z6]),(0,[z1,z8,z3,z4,z5,z1227]),(0,[z1,z8,z3,z4,z1228,z6]),(0,[z1,z1229,z3,z4,z5,z6])],[(0,[z8,z3,z4,z529,z56,z6]),(0,[z1,z8,z3,z4,z227,z6]),(0,[z1,z8,z545,z4,z380,z6]),(0,[z1230,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1231,z6]),(0,[z1,z8,z101,z4,z11,z6]),(0,[z41,z1,z8,z3,z12,z42])],[(0,[z1,z741,z3,z4,z5,z6]),(0,[z131,z14,z132,z4,z5,z6]),(0,[z26,z1,z3,z27,z56,z6])],[(1,[z2,z3,z4,z227,z6]),(0,[z67,z2,z3,z4,z56,z6]),(0,[z1,z14,z147,z3,z4,z6]),(0,[z1,z8,z118,z4,z234,z6]),(0,[z35,z8,z3,z4,z47,z6]),(0,[z1,z8,z628,z108,z5,z6])],[(0,[z48,z8,z3,z4,z13,z6]),(0,[z1,z8,z3,z4,z1232,z6]),(0,[z1,z8,z3,z4,z1233,z6]),(0,[z1,z8,z1234,z4,z34,z6])],[(0,[z84,z2,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z1040])],[(0,[z1,z2,z3,z4,z313,z6]),(0,[z35,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1235,z6]),(0,[z1,z342,z3,z530,z5,z6]),(0,[z1,z8,z1236,z3,z5,z6]),(0,[z566,z1,z3,z4,z21,z6])],[(0,[z41,z1,z8,z3,z34,z42]),(0,[z1,z8,z3,z4,z12,z601]),(0,[z1,z8,z3,z1237,z4,z6])],[(0,[z1,z8,z3,z1238,z4,z6]),(0,[z1239,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1240,z6]),(0,[z19,z1,z8,z3,z6,z116]),(0,[z1,z8,z3,z4,z1241,z6])],[(0,[z1,z2,z3,z4,z12,z6]),(0,[z1,z420,z3,z45,z5,z6]),(0,[z1,z462,z3,z4,z279,z6]),(0,[z1,z346,z3,z530,z5,z6]),(0,[z1,z8,z3,z4,z1242,z6]),(0,[z1,z8,z3,z1058,z5,z6]),(0,[z1,z8,z31,z3,z4,z483])],[(0,[z120,z8,z3,z4,z252,z129]),(0,[z1,z8,z246,z4,z5,z6])]],
   [[(0,[z84,z2,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z1243,z6]),(0,[z1,z8,z515,z36,z5,z6])],[(0,[z1,z2,z240,z4,z5,z6]),(0,[z131,z8,z31,z132,z4,z6]),(0,[z51,z1,z68,z4,z12,z6]),(0,[z35,z8,z3,z4,z344,z6]),(0,[z1,z8,z3,z4,z1244,z6])],[(0,[z1,z8,z1245,z3,z4,z6]),(0,[z1,z2,z3,z4,z253,z6]),(0,[z1,z8,z1246,z4,z5,z6]),(0,[z1,z445,z3,z4,z164,z6]),(0,[z1,z8,z31,z3,z178,z6])],[(0,[z293,z8,z31,z3,z4,z6])],[(0,[z1,z2,z3,z4,z34,z6]),(0,[z128,z2,z3,z144,z5,z6]),(0,[z1,z2,z3,z1071,z5,z6]),(0,[z131,z8,z132,z4,z34,z6]),(0,[z1,z8,z3,z1247,z5,z6]),(0,[z1,z3,z4,z5,z88,z846]),(0,[z1,z8,z3,z122,z5,z75]),(0,[z1,z8,z3,z135,z5,z6]),(0,[z1,z8,z3,z4,z12,z136])],[(0,[z1,z8,z3,z250,z5,z6]),(0,[z1,z8,z3,z4,z56,z64]),(0,[z1,z8,z31,z3,z1248,z6])],[(0,[z120,z2,z3,z530,z5,z6]),(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z4,z5,z125]),(0,[z1,z441,z3,z4,z5,z238]),(0,[z1,z8,z3,z4,z854,z6]),(0,[z1,z8,z3,z4,z1249,z6])],[(0,[z247,z1,z3,z27,z5,z6]),(0,[z1,z1250,z3,z4,z5,z6]),(0,[z1,z8,z492,z108,z5,z6]),(0,[z51,z1,z68,z4,z34,z6]),(0,[z1,z8,z3,z4,z6,z1251])],[(0,[z1,z2,z3,z4,z639,z6]),(0,[z1,z54,z3,z4,z5,z238]),(0,[z1,z1252,z3,z4,z5,z6]),(0,[z1,z76,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z328,z125])],[(0,[z609,z2,z3,z4,z5,z6]),(0,[z1,z8,z301,z3,z34,z6]),(0,[z1,z1253,z3,z4,z5,z6])],[(0,[z1,z8,z1254,z4,z5,z6]),(0,[z0,z14,z3,z4,z12,z6]),(0,[z1,z8,z96,z32,z5,z6]),(0,[z1255,z8,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z846,z6])],[(0,[z1,z8,z3,z4,z1256,z6]),(0,[z74,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1064,z6]),(0,[z1,z8,z152,z3,z4,z6])],[(0,[z2,z3,z4,z11,z56,z6]),(0,[z1,z8,z3,z421,z275,z6]),(0,[z1,z342,z576,z4,z5,z6]),(0,[z1,z8,z3,z4,z1257,z6])],[(0,[z1,z38,z3,z4,z344,z6]),(0,[z0,z14,z3,z4,z529,z6]),(0,[z1,z14,z100,z36,z5,z6]),(0,[z1,z8,z3,z4,z5,z156]),(0,[z1,z457,z545,z4,z5,z6]),(0,[z1,z8,z3,z4,z1258,z6])],[(0,[z1,z8,z1259,z3,z4,z6]),(0,[z1,z8,z3,z4,z1260,z6])],[(0,[z1,z14,z31,z3,z4,z6]),(0,[z1,z346,z576,z4,z5,z6]),(0,[z1,z8,z3,z1261,z12,z6])]],
   [[(0,[z1262,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z1263,z5,z6])],[(0,[z667,z2,z3,z4,z5,z6]),(0,[z1,z1264,z3,z4,z5,z6]),(0,[z1,z8,z3,z369,z5,z75]),(0,[z1,z8,z179,z4,z5,z6]),(0,[z1,z1265,z3,z4,z5,z6])],[(0,[z2,z2,z3,z4,z56,z6]),(0,[z1,z1223,z3,z4,z5,z6]),(0,[z1,z14,z3,z37,z5,z75]),(0,[z1,z8,z3,z4,z380,z575]),(0,[z1,z8,z3,z4,z6,z1266]),(0,[z1,z8,z3,z4,z5,z1267])],[(0,[z527,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z254,z56,z6]),(0,[z1,z14,z3,z123,z10,z6]),(0,[z60,z8,z3,z32,z5,z6]),(0,[z1,z205,z3,z4,z12,z6]),(0,[z1,z3,z744,z27,z5,z6]),(0,[z1,z8,z3,z4,z1268,z6])],[(0,[z1,z31,z366,z3,z4,z6]),(0,[z266,z270,z3,z4,z5,z6]),(0,[z1,z8,z100,z36,z12,z6]),(0,[z389,z8,z139,z3,z4,z6])],[(0,[z2,z3,z132,z4,z5,z6]),(0,[z1,z224,z31,z3,z4,z6]),(0,[z84,z205,z3,z4,z34,z6]),(0,[z1,z342,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z5,z52])],[(0,[z1,z8,z1269,z4,z5,z6]),(0,[z1,z14,z157,z108,z5,z6]),(0,[z1,z1270,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z1271]),(0,[z1,z1272,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z104,z15]),(0,[z1,z8,z3,z4,z1273,z6]),(0,[z1,z8,z3,z635,z109,z6]),(0,[z1,z8,z3,z4,z5,z1274]),(0,[z1,z8,z31,z3,z4,z256])],[(0,[z1,z8,z1089,z3,z4,z6]),(0,[z1,z346,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z6,z1275])],[(0,[z48,z8,z151,z4,z5,z6]),(0,[z1,z8,z3,z4,z90,z405]),(0,[z1,z205,z3,z4,z34,z6]),(0,[z1,z8,z3,z37,z12,z75])],[(0,[z1,z8,z3,z4,z5,z1276]),(0,[z8,z139,z3,z4,z56,z6]),(0,[z1,z8,z100,z36,z34,z6]),(0,[z1,z8,z3,z635,z216,z6]),(0,[z1,z3,z852,z4,z5,z6])],[(0,[z1,z8,z4,z70,z56,z6]),(0,[z1,z342,z3,z4,z34,z6]),(0,[z285,z1,z3,z4,z21,z6]),(0,[z1,z169,z3,z4,z5,z107])],[(0,[z103,z2,z3,z4,z5,z104]),(0,[z152,z31,z2,z3,z4,z6]),(0,[z8,z3,z4,z144,z13,z6]),(0,[z235,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z178,z5,z6])],[(0,[z1,z8,z3,z4,z1277,z6]),(0,[z1,z8,z157,z108,z12,z6]),(0,[z1,z8,z3,z192,z500,z6])],[(0,[z60,z2,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z13,z6]),(0,[z1,z527,z3,z4,z47,z6]),(0,[z1,z8,z1278,z3,z4,z6]),(0,[z1,z346,z3,z4,z34,z6]),(0,[z1,z8,z31,z3,z4,z125]),(0,[z266,z8,z3,z4,z198,z6]),(0,[z1,z8,z31,z1186,z4,z6]),(0,[z1,z31,z929,z3,z4,z6])],[(0,[z1,z8,z3,z4,z56,z6]),(0,[z1,z441,z3,z4,z275,z6]),(0,[z1,z1279,z3,z4,z5,z6]),(0,[z1,z8,z3,z37,z34,z75]),(0,[z1,z8,z3,z1280,z5,z6]),(0,[z111,z8,z3,z4,z95,z6])]],
   [[(0,[z453,z2,z3,z4,z5,z6]),(0,[z120,z2,z3,z4,z12,z6]),(0,[z65,z1,z14,z4,z5,z15]),(0,[z1,z207,z3,z4,z227,z6]),(0,[z1,z8,z3,z135,z56,z6]),(0,[z1,z8,z385,z108,z5,z6]),(0,[z1,z177,z3,z45,z5,z6]),(0,[z1,z1281,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z1282]),(1,[z2,z3,z4,z56,z6]),(0,[z1,z54,z3,z4,z275,z6]),(0,[z1,z8,z1283,z3,z4,z6]),(0,[z1,z8,z3,z4,z1284,z6]),(0,[z8,z3,z4,z5,z6,z757]),(0,[z1,z8,z1285,z4,z5,z6]),(0,[z1,z8,z3,z4,z12,z69])],[(0,[z1,z8,z3,z4,z1286,z6]),(0,[z1,z8,z92,z3,z6,z116]),(0,[z1,z8,z3,z4,z12,z210])],[(0,[z1,z14,z31,z3,z4,z12]),(0,[z8,z701,z3,z4,z56,z6]),(0,[z1,z8,z157,z108,z34,z6])],[(0,[z2,z3,z4,z5,z56,z6]),(0,[z60,z457,z3,z4,z5,z6]),(0,[z8,z3,z4,z703,z56,z6]),(0,[z1,z177,z3,z744,z5,z6])],[(0,[z18,z8,z3,z4,z5,z6]),(0,[z2,z3,z4,z56,z6,z136]),(0,[z59,z1,z2,z4,z6,z22]),(0,[z1,z8,z802,z4,z5,z6]),(0,[z508,z14,z3,z4,z5,z6]),(0,[z1,z8,z1121,z4,z5,z6]),(0,[z1,z8,z3,z4,z6,z1287]),(0,[z1,z8,z3,z4,z1288,z6]),(0,[z1,z8,z3,z4,z198,z6]),(0,[z1,z8,z3,z123,z6,z842])],[(0,[z2,z101,z3,z4,z56,z6]),(0,[z1,z2,z3,z635,z5,z6]),(0,[z1,z14,z372,z4,z5,z6]),(0,[z1,z8,z3,z4,z1289,z6]),(0,[z1,z457,z3,z4,z34,z6]),(0,[z1,z8,z3,z1290,z5,z6])],[(0,[z1,z8,z3,z4,z1291,z6]),(0,[z1,z8,z1292,z4,z5,z6]),(0,[z1,z8,z3,z4,z1293,z6]),(0,[z2,z3,z307,z4,z5,z6]),(0,[z1,z2,z3,z530,z5,z6]),(0,[z2,z3,z4,z5,z6,z666]),(0,[z1,z8,z3,z530,z252,z6]),(0,[z1,z8,z861,z3,z4,z6]),(0,[z1,z8,z3,z4,z1294,z6])],[(0,[z2,z3,z668,z4,z5,z6]),(0,[z684,z2,z3,z4,z5,z6]),(0,[z1,z1295,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1135,z6]),(0,[z1,z1296,z3,z4,z5,z6]),(0,[z1,z1297,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z56,z156]),(0,[z1,z457,z3,z4,z5,z575]),(0,[z1,z8,z3,z4,z1243,z64]),(0,[z1,z383,z3,z4,z12,z6]),(0,[z51,z1,z68,z635,z5,z6])],[(0,[z2,z3,z611,z4,z5,z6]),(0,[z1,z8,z3,z4,z1298,z6]),(0,[z1,z445,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z1299,z6]),(0,[z619,z1,z8,z4,z6,z22]),(0,[z41,z1,z8,z3,z5,z356])],[(0,[z1,z8,z3,z4,z5,z1300]),(0,[z1,z8,z3,z880,z5,z6]),(0,[z1,z8,z3,z4,z1301,z6]),(0,[z1,z8,z3,z4,z1302,z6])],[(0,[z2,z3,z144,z5,z6,z42]),(0,[z2,z3,z4,z614,z5,z6]),(0,[z239,z1,z8,z4,z5,z15]),(0,[z1,z8,z101,z4,z276,z6]),(0,[z1,z8,z3,z4,z109,z6]),(0,[z26,z1,z179,z27,z5,z6])],[(0,[z2,z3,z4,z56,z104,z6]),(0,[z1303,z8,z3,z4,z5,z6]),(0,[z35,z8,z3,z4,z21,z6]),(0,[z1,z8,z372,z4,z12,z6])],[(0,[z2,z3,z4,z34,z104,z6]),(0,[z302,z8,z3,z144,z5,z6])],[(0,[z1,z8,z3,z4,z1304,z6]),(0,[z527,z2,z3,z4,z56,z6]),(0,[z446,z2,z3,z4,z5,z6]),(0,[z48,z8,z31,z151,z4,z6]),(0,[z1,z383,z3,z4,z34,z6]),(0,[z33,z1,z3,z4,z34,z88]),(0,[z249,z8,z3,z4,z34,z6])]],
   [[(0,[z1,z8,z1234,z4,z5,z6]),(0,[z644,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z1305,z5,z6])],[(0,[z1,z8,z3,z4,z56,z52]),(0,[z1,z8,z100,z4,z6,z91]),(0,[z41,z1,z8,z31,z3,z42])],[(0,[z2,z3,z4,z5,z621,z6]),(0,[z1,z2,z3,z544,z5,z6]),(0,[z38,z2,z3,z4,z56,z6]),(0,[z1,z14,z3,z4,z5,z238]),(0,[z1,z314,z3,z222,z5,z6]),(0,[z131,z8,z132,z544,z5,z6]),(0,[z1,z8,z545,z4,z334,z6]),(0,[z1,z8,z31,z3,z4,z543])],[(1,[z152,z2,z3,z4,z6]),(0,[z1,z8,z1306,z3,z4,z6]),(0,[z1,z8,z372,z4,z34,z6]),(0,[z41,z1,z8,z3,z5,z42])],[(0,[z266,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z580,z56,z6]),(0,[z1,z8,z3,z4,z1307,z6]),(0,[z1,z8,z3,z1308,z5,z6])],[(0,[z2,z3,z623,z4,z5,z6]),(0,[z48,z8,z151,z4,z56,z6]),(0,[z1,z8,z3,z4,z1309,z6]),(0,[z1,z8,z736,z4,z5,z6])],[(0,[z392,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z6,z1310]),(0,[z1,z8,z722,z3,z4,z12])],[(0,[z1,z8,z1311,z4,z5,z6]),(0,[z1,z8,z1312,z3,z4,z6]),(0,[z1,z8,z3,z4,z1313,z6]),(0,[z1314,z8,z3,z4,z5,z6]),(0,[z330,z1,z8,z3,z6,z116]),(0,[z1,z8,z3,z4,z6,z738]),(0,[z1,z1315,z3,z4,z5,z6])],[(0,[z1,z1316,z3,z4,z5,z6]),(0,[z1,z8,z3,z178,z56,z6]),(0,[z1,z8,z576,z4,z252,z6]),(0,[z1,z8,z55,z413,z5,z6])],[(0,[z489,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z417,z6]),(0,[z1,z8,z3,z4,z12,z238]),(0,[z59,z1,z8,z4,z6,z357]),(0,[z1,z8,z3,z4,z1317,z6]),(0,[z248,z8,z3,z4,z1232,z6])],[(0,[z1,z8,z3,z4,z983,z6]),(0,[z1,z14,z3,z4,z252,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z4,z279,z6]),(0,[z329,z8,z3,z4,z56,z6]),(0,[z675,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z1318,z6]),(0,[z1,z8,z231,z4,z5,z6]),(0,[z1,z193,z3,z4,z5,z64]),(0,[z28,z8,z3,z4,z109,z6]),(0,[z1,z1319,z3,z4,z5,z6])],[(0,[z74,z31,z2,z3,z4,z6]),(0,[z19,z2,z3,z4,z56,z6]),(0,[z150,z1,z229,z4,z5,z6]),(0,[z1,z14,z3,z320,z5,z6]),(0,[z1,z408,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z6,z155])],[(1,[z2,z231,z4,z5,z6]),(0,[z1,z8,z3,z1320,z5,z6]),(0,[z1,z8,z1321,z3,z4,z6]),(0,[z30,z1,z8,z336,z3,z4]),(0,[z1,z8,z3,z4,z328,z6]),(0,[z1,z1151,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z227,z6]),(0,[z1,z1262,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1322,z6]),(0,[z51,z1,z68,z4,z5,z6]),(0,[z1,z8,z3,z4,z109,z52]),(0,[z1,z8,z31,z179,z4,z6]),(0,[z1,z1323,z3,z4,z5,z6])],[(0,[z2,z3,z4,z56,z6,z107]),(0,[z1,z14,z301,z3,z5,z6]),(0,[z1,z8,z3,z4,z34,z238]),(0,[z1,z8,z3,z4,z1324,z6])]],
   [[(0,[z1,z8,z3,z4,z850,z6]),(0,[z1,z8,z3,z4,z1325,z6]),(0,[z1,z8,z96,z4,z334,z6]),(1,[z1,z8,z4,z6,z738])],[(0,[z650,z2,z3,z4,z5,z6]),(0,[z131,z8,z132,z4,z12,z6]),(0,[z1,z8,z3,z4,z90,z6]),(0,[z18,z8,z3,z4,z56,z6]),(0,[z1,z8,z31,z3,z4,z647]),(0,[z65,z1,z8,z4,z436,z15]),(0,[z19,z1,z8,z521,z6,z116]),(0,[z1,z8,z3,z4,z1326,z6])],[(0,[z389,z31,z2,z3,z4,z6]),(0,[z1,z1327,z3,z4,z5,z6]),(0,[z1,z8,z1328,z4,z5,z6]),(0,[z1,z408,z3,z4,z34,z6]),(0,[z103,z445,z3,z4,z5,z104]),(0,[z1,z8,z3,z4,z1329,z6]),(0,[z1,z8,z1215,z3,z4,z52]),(0,[z1,z8,z3,z4,z1330,z6])],[(1,[z2,z3,z4,z90,z6]),(0,[z1,z2,z3,z5,z6,z1067]),(0,[z248,z8,z3,z4,z5,z6]),(0,[z48,z207,z151,z4,z5,z6]),(0,[z1,z8,z3,z4,z1331,z6]),(0,[z1,z1332,z3,z4,z5,z6]),(0,[z1,z8,z3,z320,z12,z6])],[(0,[z2,z3,z4,z688,z5,z6]),(0,[z1,z2,z3,z4,z529,z6]),(0,[z8,z224,z3,z4,z56,z6]),(0,[z1,z8,z246,z5,z6,z116])],[(0,[z1,z14,z3,z4,z380,z6]),(0,[z1,z1333,z3,z4,z5,z6]),(0,[z348,z8,z3,z32,z5,z6]),(0,[z355,z1,z8,z3,z6,z208]),(0,[z8,z3,z4,z56,z6,z414])],[(0,[z1,z8,z3,z4,z1307,z52]),(0,[z1,z8,z301,z3,z12,z6])],[(0,[z0,z14,z3,z4,z5,z6]),(0,[z223,z2,z3,z4,z5,z6]),(0,[z1,z38,z3,z4,z47,z6]),(0,[z1,z8,z3,z1334,z5,z6]),(0,[z18,z8,z3,z4,z198,z6])],[(0,[z51,z1,z307,z4,z5,z6]),(0,[z1,z8,z3,z4,z1335,z6]),(0,[z1,z8,z3,z4,z1336,z6]),(0,[z8,z3,z4,z95,z13,z6]),(0,[z1,z903,z3,z4,z5,z6])],[(0,[z1,z207,z3,z4,z56,z6]),(0,[z1,z8,z3,z320,z34,z6]),(0,[z1,z8,z3,z4,z1337,z6])],[(0,[z28,z2,z3,z4,z5,z6]),(0,[z596,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z206]),(0,[z1,z1338,z3,z4,z5,z6]),(0,[z1,z8,z36,z3,z6,z91])],[(0,[z2,z3,z32,z4,z56,z6]),(0,[z59,z2,z3,z4,z56,z6]),(0,[z1,z67,z3,z4,z5,z465]),(0,[z1,z14,z3,z4,z275,z6]),(0,[z654,z8,z151,z4,z5,z6]),(0,[z412,z1,z8,z3,z6,z396]),(0,[z1,z8,z31,z3,z413,z6]),(0,[z1,z8,z3,z4,z1339,z6])],[(0,[z247,z1,z3,z264,z5,z6]),(0,[z1,z8,z132,z544,z5,z6]),(0,[z8,z3,z4,z34,z425,z6]),(0,[z1,z8,z3,z4,z1340,z6]),(0,[z1,z8,z3,z1261,z5,z6]),(0,[z1,z8,z3,z612,z10,z6]),(0,[z266,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z1341,z6]),(0,[z1,z8,z3,z29,z4,z6]),(0,[z1,z8,z176,z604,z4,z6])],[(0,[z1,z14,z3,z4,z771,z6]),(0,[z76,z3,z4,z5,z104,z6]),(0,[z1,z8,z3,z4,z1154,z6]),(0,[z1,z8,z240,z4,z134,z6])],[(0,[z14,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1342,z6]),(0,[z1,z8,z3,z4,z334,z575]),(0,[z1,z8,z3,z4,z1343,z6]),(0,[z1,z8,z31,z3,z635,z6])],[(0,[z60,z31,z2,z3,z4,z6]),(0,[z1,z8,z3,z1166,z5,z6]),(0,[z48,z8,z151,z4,z227,z6])]],
   [[(0,[z1,z14,z3,z4,z279,z6]),(0,[z1,z8,z336,z3,z4,z104]),(0,[z1,z8,z100,z460,z5,z6])],[(0,[z84,z1223,z3,z4,z5,z6]),(0,[z1,z8,z3,z1344,z5,z6])],[(0,[z1,z2,z3,z1187,z5,z6]),(0,[z488,z2,z3,z4,z5,z6]),(0,[z1,z342,z3,z4,z5,z6]),(0,[z128,z8,z3,z144,z380,z6]),(0,[z1,z8,z3,z4,z869,z575]),(0,[z1,z8,z3,z4,z90,z88]),(0,[z1,z8,z1182,z4,z5,z6]),(0,[z365,z1,z8,z3,z183,z6])],[(0,[z1,z8,z31,z3,z4,z6]),(0,[z570,z8,z3,z4,z5,z85]),(0,[z1,z8,z3,z4,z1345,z6]),(0,[z266,z8,z3,z4,z1346,z6])],[(0,[z48,z2,z3,z4,z12,z6]),(0,[z293,z462,z3,z4,z5,z6])],[(0,[z1,z193,z3,z4,z5,z6]),(0,[z1,z346,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1347,z6])],[(0,[z1,z8,z3,z4,z12,z629]),(0,[z1,z8,z3,z560,z10,z6])],[(0,[z1,z8,z231,z4,z56,z6]),(1,[z35,z3,z4,z21,z6]),(0,[z1,z270,z3,z4,z242,z107])],[(0,[z2,z3,z4,z90,z5,z6]),(0,[z1,z8,z975,z4,z5,z6]),(0,[z128,z8,z3,z795,z5,z6]),(0,[z26,z1,z3,z27,z328,z6]),(0,[z1,z177,z31,z3,z45,z6]),(0,[z1,z1348,z3,z4,z5,z6])],[(0,[z141,z2,z3,z4,z56,z6]),(0,[z1,z14,z139,z3,z4,z6])],[(0,[z48,z2,z3,z4,z34,z6]),(0,[z35,z2,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z102,z6]),(0,[z1,z8,z3,z4,z1183,z6]),(0,[z1,z270,z3,z4,z5,z274]),(0,[z1,z14,z3,z4,z5,z85]),(0,[z1,z8,z3,z4,z1346,z6]),(0,[z18,z8,z3,z4,z1228,z6]),(0,[z1,z8,z1349,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1199]),(0,[z1,z14,z3,z4,z456,z6]),(0,[z1,z145,z3,z4,z417,z6]),(0,[z1,z8,z3,z4,z1350,z6]),(0,[z1,z8,z3,z4,z5,z58]),(0,[z1,z8,z3,z4,z89,z6]),(0,[z1,z8,z3,z4,z1351,z6])],[(0,[z1352,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1353,z6])],[(0,[z120,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z27,z56,z6]),(0,[z1,z8,z3,z4,z1354,z6]),(0,[z1,z8,z3,z4,z5,z1355]),(0,[z1356,z8,z3,z4,z5,z6]),(0,[z1,z8,z4,z1357,z5,z6])],[(0,[z1,z527,z3,z4,z245,z6]),(0,[z1,z8,z246,z4,z56,z6]),(0,[z1,z8,z4,z70,z377,z6])],[(0,[z248,z8,z3,z4,z56,z6])]],
   [[(0,[z74,z2,z3,z4,z106,z6]),(0,[z120,z1262,z3,z4,z5,z6]),(0,[z152,z2,z3,z4,z104,z6])],[(0,[z1,z14,z3,z4,z436,z6]),(0,[z1,z8,z3,z4,z12,z85]),(0,[z1202,z8,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z40,z6]),(0,[z381,z8,z3,z4,z34,z6]),(0,[z1,z185,z3,z4,z47,z6]),(0,[z28,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z1358,z6]),(0,[z1,z8,z1359,z3,z4,z6]),(0,[z1,z8,z3,z1360,z5,z6]),(0,[z1,z8,z3,z4,z377,z6]),(0,[z1,z8,z3,z4,z12,z349])],[(0,[z1,z8,z3,z4,z1361,z6]),(0,[z1,z457,z3,z4,z12,z6]),(0,[z597,z1,z3,z4,z21,z6])],[(0,[z1,z2,z3,z4,z63,z6]),(0,[z1,z2,z3,z4,z5,z64]),(0,[z131,z8,z132,z4,z63,z6]),(0,[z1,z8,z3,z4,z6,z1362]),(0,[z1,z8,z3,z250,z56,z6]),(0,[z1,z8,z3,z4,z1363,z6]),(0,[z1,z8,z3,z4,z1364,z6]),(0,[z1,z8,z788,z3,z4,z125])],[(0,[z1,z39,z3,z4,z5,z310]),(0,[z1,z8,z3,z4,z1365,z6]),(0,[z457,z3,z4,z144,z5,z6]),(0,[z1,z8,z3,z4,z1366,z6]),(0,[z1367,z8,z3,z4,z5,z6])],[(0,[z1,z14,z821,z4,z5,z6]),(0,[z1,z8,z1368,z4,z5,z6])],[(0,[z1,z8,z3,z4,z1369,z6]),(0,[z1,z462,z3,z4,z12,z6]),(0,[z1,z8,z3,z4,z34,z85]),(0,[z1,z8,z1370,z3,z4,z6]),(0,[z1,z445,z3,z4,z12,z6]),(0,[z1,z8,z31,z3,z4,z12])],[(0,[z33,z1,z3,z4,z5,z402]),(0,[z1371,z8,z3,z4,z5,z6])],[(0,[z128,z457,z3,z144,z5,z6])],[(0,[z33,z2,z3,z4,z56,z6]),(0,[z597,z1,z3,z4,z6,z299]),(0,[z817,z8,z3,z4,z12,z6])],[(0,[z2,z3,z4,z5,z402,z6]),(0,[z1,z8,z3,z4,z1372,z6]),(0,[z1,z8,z3,z4,z1373,z6]),(0,[z1,z185,z3,z4,z344,z6]),(0,[z1,z8,z101,z178,z5,z6])],[(0,[z1,z8,z3,z4,z5,z846])],[(0,[z177,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z544,z5,z238]),(0,[z1,z462,z3,z4,z34,z6])],[(0,[z0,z8,z3,z4,z13,z6]),(0,[z1,z8,z1283,z3,z4,z156]),(0,[z1,z8,z336,z3,z4,z129]),(0,[z1,z8,z240,z45,z5,z6])],[(0,[z1,z8,z3,z4,z1206,z6]),(0,[z1,z8,z3,z4,z6,z91]),(0,[z643,z1,z8,z4,z6,z22]),(0,[z1,z8,z3,z4,z1374,z6])]],
   [[(0,[z2,z138,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z1207,z6]),(0,[z1,z8,z179,z4,z56,z6]),(0,[z8,z3,z4,z56,z466,z6]),(0,[z26,z293,z3,z27,z5,z6]),(0,[z1,z8,z3,z4,z6,z1375]),(0,[z1,z1376,z3,z4,z5,z6])],[(0,[z1,z2,z101,z4,z11,z6]),(0,[z1,z193,z3,z4,z56,z6]),(0,[z1222,z8,z3,z4,z5,z6])],[(0,[z1,z145,z3,z4,z279,z6]),(0,[z60,z8,z3,z32,z56,z6]),(0,[z1,z8,z3,z4,z216,z6]),(0,[z35,z8,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z5,z1377]),(0,[z1,z8,z3,z178,z6,z22]),(0,[z1,z1378,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z822,z6]),(0,[z1,z8,z3,z1379,z5,z6]),(0,[z1,z8,z545,z4,z5,z575]),(0,[z1,z493,z8,z152,z3,z4]),(0,[z485,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z12,z324]),(0,[z1,z8,z708,z4,z12,z6])],[(0,[z1,z8,z3,z4,z106,z6]),(0,[z2,z3,z132,z4,z56,z6]),(0,[z2,z3,z4,z90,z56,z6]),(0,[z1,z8,z3,z4,z1380,z6])],[(0,[z1,z8,z3,z1381,z5,z6]),(0,[z1,z8,z1382,z4,z5,z6])],[(1,[z2,z3,z4,z106,z6]),(0,[z35,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z1218]),(0,[z1,z8,z3,z4,z1383,z6]),(0,[z26,z1,z3,z27,z5,z58])],[(0,[z30,z1,z31,z2,z3,z4]),(0,[z0,z8,z3,z530,z5,z6]),(0,[z1,z8,z3,z4,z49,z6]),(0,[z1,z8,z3,z4,z56,z58]),(0,[z285,z1,z3,z4,z841,z6]),(0,[z1384,z8,z3,z4,z5,z6])],[(0,[z14,z632,z3,z4,z5,z6]),(0,[z570,z8,z3,z413,z5,z6])],[(0,[z2,z3,z4,z5,z106,z6]),(0,[z1,z270,z3,z4,z12,z107]),(0,[z1,z8,z31,z3,z4,z202]),(0,[z1,z8,z246,z4,z6,z116]),(0,[z1,z8,z372,z4,z6,z206]),(0,[z716,z8,z3,z4,z12,z6]),(0,[z30,z1,z8,z31,z3,z4]),(0,[z1,z8,z31,z1349,z3,z6])],[(0,[z84,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z310,z56,z6]),(0,[z1,z2,z3,z4,z121,z6]),(0,[z1,z2,z4,z70,z5,z6]),(0,[z293,z8,z3,z4,z134,z6])],[(0,[z1,z8,z31,z3,z544,z6]),(0,[z1,z8,z1385,z3,z4,z6]),(1,[z1,z8,z178,z6,z22])],[(0,[z60,z2,z3,z4,z417,z6]),(0,[z2,z3,z68,z4,z56,z6]),(0,[z1,z8,z31,z3,z4,z64]),(0,[z1,z8,z3,z4,z1386,z6]),(0,[z1,z8,z3,z4,z1387,z6]),(0,[z1,z8,z1388,z3,z4,z6]),(0,[z1,z726,z3,z4,z12,z6])],[(0,[z2,z3,z4,z5,z6,z115]),(0,[z207,z2,z3,z4,z5,z6]),(0,[z1,z207,z31,z3,z4,z6]),(0,[z1,z8,z3,z4,z417,z6]),(0,[z1,z8,z397,z4,z11,z6])],[(0,[z131,z8,z132,z4,z5,z6]),(0,[z1,z8,z96,z4,z34,z6]),(0,[z1,z8,z3,z4,z252,z6]),(0,[z1389,z8,z3,z4,z5,z6]),(0,[z1,z8,z31,z1081,z4,z6])],[(0,[z14,z31,z2,z3,z4,z6]),(0,[z1,z2,z3,z135,z5,z6]),(0,[z1,z2,z3,z4,z12,z136]),(0,[z1,z8,z3,z4,z1318,z6]),(0,[z1,z14,z3,z413,z5,z6]),(0,[z1,z177,z3,z45,z56,z6]),(0,[z1,z270,z3,z4,z34,z107]),(0,[z1,z8,z3,z4,z1390,z6]),(0,[z1,z8,z1391,z4,z5,z6]),(0,[z1,z8,z147,z3,z4,z6])]],
   [[(0,[z1,z1392,z3,z4,z5,z6]),(0,[z131,z2,z3,z4,z56,z6]),(1,[z2,z3,z4,z252,z6]),(0,[z1,z8,z231,z250,z5,z6])],[(0,[z1,z14,z3,z4,z334,z6]),(0,[z131,z8,z975,z4,z5,z6]),(0,[z1,z8,z96,z4,z5,z575]),(0,[z1,z8,z3,z739,z4,z56]),(0,[z84,z408,z3,z4,z34,z6]),(0,[z1,z8,z3,z1393,z4,z6]),(0,[z28,z8,z3,z4,z216,z6])],[(0,[z2,z3,z4,z5,z6,z126]),(0,[z462,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1394,z6]),(0,[z120,z8,z3,z4,z5,z757]),(0,[z1,z8,z1395,z4,z5,z6]),(0,[z1,z8,z3,z1396,z5,z6]),(0,[z1,z8,z3,z1397,z5,z6])],[(0,[z1,z8,z1398,z4,z5,z6]),(0,[z1,z8,z151,z320,z5,z6]),(0,[z1399,z8,z3,z4,z5,z6]),(0,[z1,z8,z301,z3,z5,z6])],[(0,[z1,z8,z3,z4,z1400,z6]),(0,[z1,z8,z1401,z3,z4,z6]),(0,[z1,z8,z3,z4,z5,z1402]),(0,[z1,z8,z3,z4,z216,z52]),(0,[z1,z8,z837,z4,z5,z6])],[(0,[z1,z8,z804,z4,z5,z6]),(0,[z28,z8,z3,z4,z1383,z6]),(0,[z1,z3,z4,z841,z21,z6]),(0,[z266,z8,z3,z4,z1403,z6]),(0,[z1,z1404,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1405,z6])],[(0,[z1,z14,z3,z4,z95,z6]),(0,[z1,z14,z3,z4,z134,z6]),(0,[z1,z8,z3,z544,z275,z6]),(0,[z1,z8,z3,z4,z5,z1406]),(0,[z1,z8,z3,z4,z1407,z6]),(0,[z1,z8,z3,z413,z12,z6]),(0,[z1,z8,z101,z4,z6,z738])],[(0,[z247,z2,z3,z144,z5,z6]),(0,[z1,z8,z1408,z3,z4,z6]),(0,[z1,z8,z3,z748,z12,z6])],[(0,[z1,z2,z3,z4,z5,z156]),(0,[z1,z14,z336,z3,z4,z6]),(0,[z1,z8,z3,z4,z1409,z6]),(0,[z248,z8,z3,z4,z1336,z6])],[(0,[z1,z8,z3,z4,z380,z6]),(0,[z1,z8,z152,z3,z4,z90]),(0,[z1,z8,z3,z635,z5,z85])],[(0,[z187,z1,z3,z4,z5,z402]),(0,[z1,z441,z3,z421,z5,z6]),(0,[z1,z8,z3,z37,z4,z90]),(0,[z1,z8,z3,z4,z1410,z6]),(0,[z117,z8,z3,z4,z13,z6])],[(0,[z2,z3,z4,z144,z12,z6])],[(0,[z1,z2,z3,z4,z1174,z6]),(0,[z1,z14,z3,z4,z160,z6]),(0,[z1,z54,z3,z421,z5,z6]),(0,[z8,z975,z132,z4,z5,z6]),(0,[z1,z8,z3,z4,z1403,z6]),(0,[z1,z8,z3,z413,z34,z6]),(0,[z59,z1,z8,z4,z6,z22]),(0,[z1,z8,z3,z1248,z5,z6])],[(0,[z60,z2,z3,z144,z5,z6]),(0,[z2,z3,z691,z4,z5,z6]),(0,[z150,z8,z132,z4,z5,z6]),(0,[z48,z8,z151,z4,z49,z6]),(0,[z1,z8,z3,z4,z1411,z6])],[(0,[z2,z692,z3,z4,z5,z6]),(0,[z1,z8,z1412,z3,z5,z6]),(0,[z128,z8,z3,z144,z334,z6]),(0,[z1,z8,z3,z4,z760,z56]),(0,[z318,z8,z3,z4,z5,z104]),(0,[z1,z8,z179,z4,z328,z6])],[(0,[z150,z2,z3,z4,z56,z6]),(0,[z340,z14,z3,z4,z5,z6]),(0,[z8,z139,z3,z4,z104,z6]),(0,[z1,z8,z3,z4,z1413,z6])]],
   [[(0,[z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z52]),(0,[z1,z8,z1072,z3,z4,z6]),(0,[z1,z8,z3,z4,z1414,z6]),(0,[z1,z8,z31,z4,z70,z6])],[(0,[z48,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z144,z34,z6]),(0,[z195,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z1415,z5,z6])],[(0,[z2,z132,z4,z5,z6,z15]),(0,[z41,z1,z8,z3,z56,z42]),(0,[z61,z1,z8,z4,z5,z15]),(0,[z1,z1416,z3,z4,z5,z6])],[(0,[z1,z205,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z280,z6]),(0,[z1,z441,z3,z4,z34,z6]),(0,[z51,z1,z68,z4,z5,z52]),(0,[z1029,z8,z3,z4,z5,z6])],[(0,[z48,z2,z151,z4,z5,z6]),(0,[z2,z3,z4,z5,z696,z6]),(0,[z1,z14,z521,z4,z5,z6]),(0,[z1,z8,z3,z4,z1417,z6]),(0,[z570,z8,z3,z4,z908,z6]),(0,[z248,z8,z179,z4,z5,z6]),(0,[z1,z8,z100,z36,z5,z6]),(0,[z1,z8,z31,z4,z1036,z6])],[(0,[z509,z8,z3,z4,z34,z6]),(0,[z1418,z1,z8,z3,z4,z6]),(0,[z1,z8,z3,z4,z134,z125])],[(0,[z84,z2,z3,z4,z56,z6])],[(0,[z1,z2,z3,z178,z5,z6]),(0,[z2,z3,z4,z703,z5,z6]),(0,[z79,z14,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z242,z6]),(0,[z1,z8,z3,z4,z1419,z6]),(0,[z1,z8,z31,z521,z4,z6])],[],[(0,[z2,z3,z4,z5,z104,z6]),(0,[z205,z2,z3,z4,z5,z6]),(0,[z1,z8,z496,z108,z5,z6]),(0,[z1,z8,z3,z37,z5,z75])],[(0,[z1,z2,z3,z4,z56,z6]),(0,[z131,z8,z132,z4,z56,z6]),(0,[z1,z8,z3,z123,z10,z6])],[(0,[z2,z3,z4,z12,z13,z6]),(0,[z111,z8,z3,z4,z34,z6]),(0,[z1,z8,z31,z3,z250,z6]),(0,[z1,z8,z3,z4,z1420,z6]),(0,[z248,z8,z3,z4,z5,z58]),(0,[z1,z8,z3,z4,z1421,z6]),(0,[z1,z8,z3,z4,z5,z1422]),(0,[z1,z8,z341,z4,z11,z6]),(0,[z1,z8,z521,z4,z12,z6]),(1,[z1,z8,z3,z6,z842]),(0,[z1,z8,z3,z4,z1423,z6])],[(0,[z340,z8,z3,z4,z34,z6]),(0,[z1,z8,z3,z4,z6,z1424]),(0,[z1,z8,z3,z1425,z4,z6]),(0,[z1,z8,z260,z108,z5,z6]),(0,[z1,z8,z175,z108,z5,z6])],[(0,[z8,z741,z3,z4,z5,z6]),(0,[z51,z1,z68,z4,z56,z6]),(0,[z1,z8,z1426,z4,z5,z6]),(0,[z524,z1,z8,z3,z5,z42]),(0,[z1,z8,z157,z108,z5,z6]),(0,[z1427,z8,z3,z4,z5,z6]),(0,[z127,z237,z1,z3,z4,z6])],[(0,[z1,z8,z3,z4,z1428,z6]),(0,[z8,z3,z4,z983,z56,z6]),(0,[z1,z8,z3,z1429,z5,z6]),(0,[z65,z1,z8,z320,z5,z6])],[(0,[z1,z8,z3,z4,z63,z238]),(0,[z669,z8,z3,z4,z5,z104]),(0,[z248,z314,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z456,z6]),(1,[z1,z8,z722,z3,z4])]],
   [[(0,[z1,z457,z3,z4,z5,z6]),(0,[z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z198,z6]),(0,[z1,z8,z31,z3,z4,z156]),(0,[z1,z445,z3,z4,z121,z6]),(0,[z1,z8,z3,z1430,z5,z6]),(0,[z1,z8,z3,z4,z1431,z6]),(0,[z943,z8,z3,z4,z5,z6])],[(0,[z1,z207,z3,z4,z49,z6]),(0,[z1,z1432,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z1433,z6]),(0,[z1,z8,z521,z4,z34,z6]),(0,[z1,z3,z4,z47,z841,z6])],[(0,[z1,z8,z3,z4,z1434,z6]),(0,[z2,z3,z4,z264,z56,z6]),(0,[z120,z2,z3,z250,z5,z6]),(0,[z1,z8,z1435,z4,z5,z6]),(0,[z120,z8,z3,z4,z5,z154]),(0,[z441,z3,z132,z4,z5,z6]),(0,[z1,z8,z3,z4,z1436,z6]),(0,[z1,z8,z31,z3,z201,z4]),(0,[z1,z8,z3,z4,z1437,z6])],[(0,[z1,z8,z3,z4,z1438,z6]),(0,[z7,z2,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z757]),(0,[z1,z8,z101,z4,z464,z6]),(0,[z1,z8,z722,z3,z4,z136])],[(0,[z1,z445,z3,z4,z5,z6])],[(0,[z2,z3,z4,z196,z5,z6]),(0,[z1,z3,z4,z5,z846,z107])],[(0,[z0,z14,z3,z4,z56,z6]),(0,[z1,z14,z545,z4,z5,z6])],[(0,[z1,z2,z3,z4,z109,z6]),(0,[z459,z8,z3,z4,z56,z6]),(0,[z1,z8,z3,z4,z5,z1439]),(0,[z1,z8,z4,z11,z6,z738])],[(0,[z1,z8,z3,z4,z1440,z6]),(0,[z1,z8,z3,z4,z1441,z6]),(0,[z1,z8,z3,z4,z1442,z6]),(0,[z1,z8,z31,z3,z4,z52]),(0,[z1,z1443,z3,z4,z5,z6]),(0,[z1,z8,z3,z246,z6,z116])],[(0,[z1,z383,z3,z4,z5,z6]),(0,[z1,z8,z100,z322,z5,z6]),(0,[z33,z1,z3,z4,z5,z88]),(0,[z266,z489,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z1444])],[(0,[z2,z55,z3,z4,z56,z6]),(0,[z1,z8,z1445,z3,z4,z6]),(0,[z1,z8,z3,z4,z416,z12]),(0,[z51,z1,z68,z4,z109,z6]),(0,[z1,z8,z108,z5,z6,z91])],[(0,[z103,z8,z3,z4,z95,z104]),(0,[z293,z8,z3,z4,z845,z6])],[(0,[z1,z8,z179,z4,z5,z58])],[(0,[z39,z2,z3,z4,z56,z6]),(0,[z1,z8,z545,z4,z12,z6]),(0,[z1,z8,z3,z4,z841,z6]),(0,[z1,z8,z372,z4,z5,z6]),(0,[z59,z1,z8,z4,z6,z738])],[(0,[z987,z2,z3,z4,z5,z6]),(0,[z48,z8,z975,z4,z5,z6]),(0,[z8,z3,z4,z34,z13,z6]),(0,[z1,z1446,z3,z4,z5,z6])],[(0,[z1,z205,z3,z4,z56,z6]),(0,[z1,z1447,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 468) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 468).take 475) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 943).take 475) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1418).take 183) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1601)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [468, 475, 475, 183] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 71).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 146).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 237).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 315).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 396).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 477).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [71, 75, 91, 78, 81, 81, 35] = true :=
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

end PEqualNP.Outside.L_meta_38063

theorem PEqualNP.Outside.L_meta_38063 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38063.solve