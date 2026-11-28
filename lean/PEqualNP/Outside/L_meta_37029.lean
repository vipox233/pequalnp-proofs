import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37029

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x6800048635044c62#64 ++ 0x340002431a822631#64 ++ 0xf7013d8e7d1cfce7#64 ++ 0xfb809ec73e8e7e73#64 : BitVec 256),
   (0x100650308a11218d#64 ++ 0x08032818450890c6#64 ++ 0xef8ed2718e1327ff#64 ++ 0xf7c76938c70993ff#64 : BitVec 256),
   (0xa030a3815162c630#64 ++ 0x501851c0a8b16318#64 ++ 0xdf70e381f3e3c739#64 ++ 0x6fb871c0f9f1e39c#64 : BitVec 256),
   (0xc0db03da03bc07c0#64 ++ 0x606d81ed01de03e0#64 ++ 0xbcff03fe03fc07c1#64 ++ 0xde7f81ff01fe03e0#64 : BitVec 256),
   (0x006ff80002dbb001#64 ++ 0x8037fc00016dd800#64 ++ 0x7e7ffc0003fff801#64 ++ 0x3f3ffe0001fffc00#64 : BitVec 256),
   (0x017dff6dec000000#64 ++ 0x00beffb6f6000000#64 ++ 0xfdfffffffc000000#64 ++ 0xfefffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [7, 9]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7e7ffc0003fff801 0x3f3ffe0001fffc00

def z1 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc000000 0xfefffffffe000000

def z2 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xef8ed2718e1327ff 0xf7c76938c70993ff

def z3 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf7013d8e7d1cfce7 0xfb809ec73e8e7e73

def z4 : W := mkw 0xa000008011204630 0x5000004008902318 0x0000000000000738 0x000000000000039c

def z5 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70e381f3e3c739 0x6fb871c0f9f1e39c

def z6 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff03fe03fc07c1 0xde7f81ff01fe03e0

def z7 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfffffe718fffffff 0xffffff38c7ffffff

def z8 : W := mkw 0x117fff7dee11218d 0x08bfffbef70890c6 0xfffffffffe1327ff 0xffffffffff0993ff

def z9 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x10712c0001ecd800 0x0838960000f66c00

def z10 : W := mkw 0x100450208801200d 0x0802281044009006 0x4300d0018c03203e 0x21806800c601901f

def z11 : W := mkw 0x007ffb0142dbb001 0x803ffd80a16dd800 0xff7fff81f3fff801 0x7fbfffc0f9fffc00

def z12 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x30ff01fe01fc00c0 0x987f80ff00fe0060

def z13 : W := mkw 0x0020a00000428000 0x0010500000214000 0x5e70e00003e3c001 0x2f38700001f1e000

def z14 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xffffffffffe3c001 0xfffffffffff1e000

def z15 : W := mkw 0x0004502088000000 0x0002281044000000 0xed8ed2718c000000 0xf6c76938c6000000

def z16 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0x10712d8e70000000 0x083896c738000000

def z17 : W := mkw 0xa17dffedfd62c630 0x50befff6feb16318 0xffffffffffe3c739 0xfffffffffff1e39c

def z18 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0x7e7ffc0003ffffff 0x3f3ffe0001ffffff

def z19 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffc000ffffce7 0xffbffe0007fffe73

def z20 : W := mkw 0x780654b6bf156def 0x3c032a5b5f8ab6f7 0xf78f3dfe7d1cfce7 0xfbc79eff3e8e7e73

def z21 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0x8100038ffc0007fe 0xc08001c7fe0003ff

def z22 : W := mkw 0x0024f8000043b001 0x80127c000021d800 0x4200fc000003f800 0x21007e000001fc00

def z23 : W := mkw 0xc0fffbda03ffb7c1 0xe07ffded01ffdbe0 0xfefffffe03ffffc1 0xff7fffff01ffffe0

def z24 : W := mkw 0x0059034800000000 0x002c81a400000000 0xbcff03fe00000000 0xde7f81ff00000000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0xe70010000c1024e7 0xf380080006081273

def z26 : W := mkw 0x2020a0015042c030 0x10105000a8216018 0x4300e001f003c038 0x21807000f801e01c

def z27 : W := mkw 0x40cf585a029d31c1 0xa067ac2d014e98e0 0x208f1c7e001c38c0 0x90478e3f000e1c60

def z28 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7c7ffc0002e30000 0x3e3ffe0001718000

def z29 : W := mkw 0x40c9004a008c0040 0x2064802500460020 0x0001000e000c0000 0x0000800700060000

def z30 : W := mkw 0x4000008201040440 0x2000004100820220 0xb401018e011c04c1 0xda0080c7008e0260

def z31 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0x08fe027002e00300 0x047f013801700180

def z32 : W := mkw 0x0159076dec000000 0x00ac83b6f6000000 0xbdff03fffc000000 0xdeff81fffe000000

def z33 : W := mkw 0x0000040424000000 0x0000020212000000 0xf5013d8e7c000000 0xfa809ec73e000000

def z34 : W := mkw 0x6800008211044c62 0x3400004108822631 0x02000000011cfce7 0x01000000008e7e73

def z35 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0x208f1c7e0c000000 0x90478e3f06000000

def z36 : W := mkw 0x0030a30140000000 0x00185180a0000000 0xdd70e381f0000000 0x6eb871c0f8000000

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0xcf00c20182030739 0x67806100c101839c

def z38 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x1070218071e0c000 0x083810c038f06000

def z39 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0xed8fde7f8c000000 0xf6c7ef3fc6000000

def z40 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0xac8f027e021c07c1 0xd647813f010e03e0

def z41 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x3c7f2c0003fcd801 0x1e3f960001fe6c00

def z42 : W := mkw 0x2000008011004420 0x1000004008802210 0xd70021807100c421 0x6b8010c038806210

def z43 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x0870c20182e30318 0x04386100c171818c

def z44 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0xbcffc3ff80000000 0xde7fe1ffc0000000

def z45 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x7c7ffc0001ecd800 0x3e3ffe0000f66c00

def z46 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0x08fec27180000000 0x047f6138c0000000

def z47 : W := mkw 0x697dffeffd044c62 0x34befff7fe822631 0xfffffffffd1cfce7 0xfffffffffe8e7e73

def z48 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x088ec27182030318 0x04476138c101818c

def z49 : W := mkw 0x901653b08b31278d 0x480b29d8459893c6 0xfffed3f18ff327ff 0xffff69f8c7f993ff

def z50 : W := mkw 0x4000008201040440 0x2000004100820220 0x8000018e000004c0 0xc00000c700000260

def z51 : W := mkw 0x004b000002980000 0x00258000014c0000 0x200f0000001c0000 0x10078000000e0000

def z52 : W := mkw 0x006df80000000000 0x0036fc0000000000 0x7c7ffc0000000000 0x3e3ffe0000000000

def z53 : W := mkw 0x017fff6deedbb001 0x80bfffb6f76dd800 0xfffffffffffff801 0xfffffffffffffc00

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x76013c00011cf801 0x3b009e00008e7c00

def z55 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x898ec2718e0307fe 0xc4c76138c70183ff

def z56 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0xa18f1ffffc000000 0xd0c78ffffe000000

def z57 : W := mkw 0x016dfc6cac000000 0x00b6fe3656000000 0x7cfffc7e0c000000 0xbe7ffe3f06000000

def z58 : W := mkw 0x000650208a112001 0x0003281045089000 0xef8ed2718e132001 0xf7c76938c7099000

def z59 : W := mkw 0x0000002088000000 0x0000001044000000 0x818002718c000000 0xc0c00138c6000000

def z60 : W := mkw 0x780654b6bf156def 0x3c032a5b5f8ab6f7 0xff8fffffff1fffff 0xffc7ffffff8fffff

def z61 : W := mkw 0xb01653b1db3167bd 0x580b29d8ed98b3de 0xef8ed3f1fe1327ff 0xf7c769f8ff0993ff

def z62 : W := mkw 0x1026f8308a53b18d 0x88137c184529d8c6 0xef8efe718e13ffff 0xf7c77f38c709ffff

def z63 : W := mkw 0xc09003da012407c0 0x604801ed009203e0 0x808003fe000007c0 0xc04001ff000003e0

def z64 : W := mkw 0x694d5ceebd044c62 0x34a6ae775e822631 0xf78f3dfe7d1cfce7 0xfbc79eff3e8e7e73

def z65 : W := mkw 0x0002001002100180 0x00010008010800c0 0xef8ec271821307f9 0xf7c76138c10983fc

def z66 : W := mkw 0x691007effd044c62 0x348803f7fe822631 0x818003fffc0004e6 0xc0c001fffe000273

def z67 : W := mkw 0x500650b28b1525cd 0x28032859458a92e6 0xff8fd3ff8f1f27ff 0xffc7e9ffc78f93ff

def z68 : W := mkw 0x100000308800018c 0x08000018440000c6 0x008000700c0000c6 0x8040003806000063

def z69 : W := mkw 0x6800048635044c62 0x340002431a822631 0x22011c0e0d1cfce7 0x91008e07068e7e73

def z70 : W := mkw 0x805903c801200600 0x402c81e400900300 0xbcff03fe03e00701 0xde7f81ff01f00380

def z71 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x187fec0003efd800 0x0c3ff60001f7ec00

def z72 : W := mkw 0xb036f3b1db73e7bd 0x581b79d8edb9f3de 0xfffef3f1fff3e7ff 0xffff79f8fff9f3ff

def z73 : W := mkw 0x0110076dec000000 0x008803b6f6000000 0x818003fffc000000 0xc0c001fffe000000

def z74 : W := mkw 0x00045424ac000000 0x00022a1256000000 0xfd8ffffffc000000 0xfec7fffffe000000

def z75 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x0070000000e00000 0x0038000000700000

def z76 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x30ff3dfe7c000000 0x987f9eff3e000000

def z77 : W := mkw 0x0034f321c8000000 0x001a7990e4000000 0xfdfef3f1fc000000 0xfeff79f8fe000000

def z78 : W := mkw 0x000000000043b001 0x800000000021d800 0x020000000003f800 0x010000000001fc00

def z79 : W := mkw 0xc0d903da012407c0 0x606c81ed009203e0 0xbcff03fe000007c0 0xde7f81ff000003e0

def z80 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8ffe718f1fffff 0xffc7ff38c78fffff

def z81 : W := mkw 0xa00000801162c630 0x5000004008b16318 0x0200000003e3c739 0x0100000001f1e39c

def z82 : W := mkw 0x6800048635044c62 0x340002431a822631 0x8100018e7c0004e6 0xc08000c73e000273

def z83 : W := mkw 0xa010038151204630 0x500801c0a8902318 0x81000381f0000738 0x408001c0f800039c

def z84 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x5e71ec0003efd801 0x2f38f60001f7ec00

def z85 : W := mkw 0x6800048635044c62 0x340002431a822631 0x10012d8e710cd800 0x080096c738866c00

def z86 : W := mkw 0x017dff6decca9000 0x80beffb6f6654800 0xfdfffffffdecd800 0xfefffffffef66c00

def z87 : W := mkw 0x01045c24ac000000 0x00822e1256000000 0x00001c000c000000 0x00000e0006000000

def z88 : W := mkw 0x0002000002dbb001 0x80010000016dd800 0x0200000003fff801 0x0100000001fffc00

def z89 : W := mkw 0x0124fc25ec000000 0x00927e12f6000000 0x4100fc01fc000000 0x20807e00fe000000

def z90 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0x1071018e01ec0000 0x083880c700f60000

def z91 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xa08f03fe001c07c0 0xd04781ff000e03e0

def z92 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x76713c0001fcf801 0x3b389e0000fe7c00

def z93 : W := mkw 0x006df82088000000 0x0036fc1044000000 0xfdfffe718c000000 0xfeffff38c6000000

def z94 : W := mkw 0xe8ffffde37ffffe3 0xf47fffef1bfffff1 0xfffffffe7fffffe7 0xffffffff3ffffff3

def z95 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0xfffffe718ffff801 0xffffff38c7fffc00

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0xb401018e00000000 0xda0080c700000000

def z97 : W := mkw 0x0010030000000000 0x0008018000000000 0x9c70038000000000 0x4e3801c000000000

def z98 : W := mkw 0x0000040424000000 0x0000020212000000 0xf7013d8e7d1cf801 0xfb809ec73e8e7c00

def z99 : W := mkw 0x6800048635044c62 0x340002431a822631 0x0000018e70000000 0x000000c738000000

def z100 : W := mkw 0x484f5c06269d3843 0xa427ae03134e9c21 0x200f1c0e0c1c38c6 0x90078e07060e1c63

def z101 : W := mkw 0x81ffff7deeb80380 0x40ffffbef75c01c0 0xfdfffffffee00300 0xfeffffffff700180

def z102 : W := mkw 0xd0df53fa8bbd27cd 0x686fa9fd45de93e6 0xffffd3ff8fff27ff 0xffffe9ffc7ff93ff

def z103 : W := mkw 0xe0fba3db53fec7f0 0x707dd1eda9ff63f8 0xffffe3fff3ffc7f9 0xfffff1fff9ffe3fc

def z104 : W := mkw 0x117dff6dec01200d 0x08beffb6f6009006 0xfffffffffc03203e 0xfffffffffe01901f

def z105 : W := mkw 0x8010038001200600 0x400801c000900300 0x9c70038003e00701 0x4e3801c001f00380

def z106 : W := mkw 0x0024f80000000000 0x00127c0000000000 0x4000fc0000000000 0x20007e0000000000

def z107 : W := mkw 0x0002001002100180 0x00010008010800c0 0x088e027002000300 0x0447013801000180

def z108 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x208e10700c1020c6 0x9047083806081063

def z109 : W := mkw 0x0002000002112001 0x0001000001089000 0x0200000002132001 0x0100000001099000

def z110 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xbeff03fe03fcffe7 0xdf7f81ff01fe7ff3

def z111 : W := mkw 0x007ffb4802dbb001 0x803ffda4016dd800 0xfefffffe03fff801 0xff7fffff01fffc00

def z112 : W := mkw 0x6800048635044c62 0x340002431a822631 0xb4012d8e711cdcc1 0xda0096c7388e6e60

def z113 : W := mkw 0x0069a80000000000 0x0034d40000000000 0x10712c0000000000 0x0838960000000000

def z114 : W := mkw 0x6820a4863546cc62 0x341052431aa36631 0xff71fd8e7ffffce7 0xffb8fec73ffffe73

def z115 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0xdd71ef8ff0000000 0x6eb8f7c7f8000000

def z116 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x087ec00002e30000 0x043f600001718000

def z117 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0x208f007e001c00c0 0x9047803f000e0060

def z118 : W := mkw 0x006ff80002993001 0x8037fc00014c9800 0x7c7ffc00001c3800 0x3e3ffe00000e1c00

def z119 : W := mkw 0xa030a38151204630 0x501851c0a8902318 0xdd70e381f0000738 0x6eb871c0f800039c

def z120 : W := mkw 0xc082009203bc07c0 0x6041004901de03e0 0x0000000003fc07c1 0x0000000001fe03e0

def z121 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x89fec3fffc000000 0xc4ff61fffe000000

def z122 : W := mkw 0x8010030140200210 0x40080180a0100108 0x0000020180000318 0x00000100c000018c

def z123 : W := mkw 0x8090035800200380 0x404801ac001001c0 0x0080027000000300 0x0040013800000180

def z124 : W := mkw 0x0030a30140000000 0x00185180a0000000 0x1070218070000000 0x083810c038000000

def z125 : W := mkw 0x100200100211218d 0x08010008010890c6 0x0000000002030318 0x000000000101818c

def z126 : W := mkw 0x2800040434004822 0x140002021a002411 0x43003c007c00f826 0x21801e003e007c13

def z127 : W := mkw 0x017fff6dee112001 0x00bfffb6f7089000 0xfffffffffe132001 0xffffffffff099000

def z128 : W := mkw 0x786ffcb6bfdffdef 0xbc37fe5b5feffef7 0xffffffffffffffff 0xffffffffffffffff

def z129 : W := mkw 0xa17dffedfd204630 0x50befff6fe902318 0xfdfffffffc000738 0xfefffffffe00039c

def z130 : W := mkw 0xa00000801162c630 0x5000004008b16318 0xcf00c20183e3c739 0x67806100c1f1e39c

def z131 : W := mkw 0x50cf507a8a9d21cd 0x2867a83d454e90e6 0xef8fd27f8e1f27ff 0xf7c7e93fc70f93ff

def z132 : W := mkw 0x006df80000000000 0x0036fc0000000000 0x087ec00000000000 0x043f600000000000

def z133 : W := mkw 0xc0fffbda03bc07c0 0x607ffded01de03e0 0xfcfffffe03fc07c1 0xfe7fffff01fe03e0

def z134 : W := mkw 0x2000000010004020 0x1000000008002010 0x430020007000c020 0x2180100038006010

def z135 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xcf8ec27182030739 0x67c76138c101839c

def z136 : W := mkw 0xe0fffbdb53fff7f1 0xf07ffdeda9fffbf8 0xfffffffff3fffff9 0xfffffffff9fffffc

def z137 : W := mkw 0xc09203da033407c0 0x604901ed019a03e0 0xac8e03fe021007c1 0xd64701ff010803e0

def z138 : W := mkw 0xe8db07de37bc4fe2 0x746d83ef1bde27f1 0xffff3ffe7ffcffe7 0xffff9fff3ffe7ff3

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x20011c00001c3800 0x10008e00000e1c00

def z140 : W := mkw 0x004b000002980000 0x00258000014c0000 0x7e7f3c0003fcf801 0x3f3f9e0001fe7c00

def z141 : W := mkw 0x0110074d64000000 0x008803a6b2000000 0x0000018e70000000 0x000000c738000000

def z142 : W := mkw 0x0114576dec000000 0x008a2bb6f6000000 0xed8ed3fffc000000 0xf6c769fffe000000

def z143 : W := mkw 0x004b000002980000 0x00258000014c0000 0x3c7f000003fc0001 0x1e3f800001fe0000

def z144 : W := mkw 0xe89007de35244fe2 0x744803ef1a9227f1 0x818003fe7c0007e6 0xc0c001ff3e0003f3

def z145 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0x7cfffe7180000000 0x3e7fff38c0000000

def z146 : W := mkw 0xa06ff88013fbf631 0xd037fc4009fdfb18 0x7e7ffc0003ffff39 0x3f3ffe0001ffff9c

def z147 : W := mkw 0xa07ffb8153fbf631 0xd03ffdc0a9fdfb18 0xdf7ee381f3e3c739 0x6fbf71c0f9f1e39c

def z148 : W := mkw 0x4800040624040842 0x2400020312020421 0x20011c0e0c1c38c6 0x90008e07060e1c63

def z149 : W := mkw 0x404b0082039c0440 0x2025804101ce0220 0xbc7f018e03fc04c1 0xde3f80c701fe0260

def z150 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x1071018e03fc07c1 0x083880c701fe03e0

def z151 : W := mkw 0xc080008201ac0640 0x6040004100d60320 0x0000000001ec0000 0x0000000000f60000

def z152 : W := mkw 0xa179afcd7562c630 0x50bcd7e6bab16318 0xdf71ef8ff3e3c739 0x6fb8f7c7f9f1e39c

def z153 : W := mkw 0x0059034800000000 0x002c81a400000000 0x08fe027000000000 0x047f013800000000

def z154 : W := mkw 0x004f580002dbb001 0x8027ac00016dd800 0x220f1c0003fff801 0x11078e0001fffc00

def z155 : W := mkw 0x0049004800000000 0x0024802400000000 0x208f007e00000000 0x9047803f00000000

def z156 : W := mkw 0xc092039203bc07c0 0x604901c901de03e0 0x9c70038003fc07c1 0x4e3801c001fe03e0

def z157 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff01ff8fff1fffff 0xff80ffc7ff8fffff

def z158 : W := mkw 0x4800040624040842 0x2400020312020421 0xe7011c0e0c1c3ce7 0xf3808e07060e1e73

def z159 : W := mkw 0x217dff6dfc42c030 0x10beffb6fe216018 0xfffffffffc03c038 0xfffffffffe01e01c

def z160 : W := mkw 0xa079ab8151ead630 0xd03cd5c0a8f56b18 0xdf71ef81f3efdf39 0x6fb8f7c0f9f7ef9c

def z161 : W := mkw 0x684f5c86379d7c63 0xb427ae431bcebe31 0xf70f3d8e7d1cfce7 0xfb879ec73e8e7e73

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0xe50010000c000000 0xf280080006000000

def z163 : W := mkw 0x685907ce35044c62 0x342c83e71a822631 0xffff3ffe7d1cfce7 0xffff9fff3e8e7e73

def z164 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x288ed2718e1323de 0x94476938c70991ef

def z165 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffe0183ffff39 0x7fbfff00c1ffff9c

def z166 : W := mkw 0x100450208801200d 0x0802281044009006 0xcf00d2018e03273f 0x67806900c701939f

def z167 : W := mkw 0xc0df5bda03bd37c1 0xe06faded01de9be0 0xbcff1ffe03fc3fc1 0xde7f8fff01fe1fe0

def z168 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xdf70e381f3ffffff 0x6fb871c0f9ffffff

def z169 : W := mkw 0x0002001002100180 0x00010008010800c0 0xac8e0270021007c1 0xd6470138010803e0

def z170 : W := mkw 0x100000100000018c 0x08000008000000c6 0x00000000000007fe 0x00000000000003ff

def z171 : W := mkw 0xc09003ca01240640 0x604801e500920320 0x0000018e00000000 0x000000c700000000

def z172 : W := mkw 0xd09653fa8b3527cd 0x684b29fd459a93e6 0xef8ed3ff8e1327ff 0xf7c769ffc70993ff

def z173 : W := mkw 0xe1fffffffffec7f0 0x70ffffffffff63f8 0xffffffffffffc7f9 0xffffffffffffe3fc

def z174 : W := mkw 0x006df8000043b001 0x8036fc000021d800 0x7e7ffc000003f800 0x3f3ffe000001fc00

def z175 : W := mkw 0xc0d903da01ac07c0 0x606c81ed00d603e0 0x90f103fe01ec07c0 0xc87881ff00f603e0

def z176 : W := mkw 0x0020a80000429000 0x8010540000214800 0x00002c000000d800 0x0000160000006c00

def z177 : W := mkw 0x100200100211218d 0x08010008010890c6 0x02000000021327ff 0x01000000010993ff

def z178 : W := mkw 0xd0db03da03bd27cd 0x686d81ed01de93e6 0xbeff03fe03ff27ff 0xdf7f81ff01ff93ff

def z179 : W := mkw 0x494d5c6eac040842 0x24a6ae3756020421 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z180 : W := mkw 0x50cf507a8a9d21cd 0x2867a83d454e90e6 0x208f107e0c1c20c6 0x9047883f060e1063

def z181 : W := mkw 0x004b000002980000 0x00258000014c0000 0x087e000002e00000 0x043f000001700000

def z182 : W := mkw 0x01490c4c24000000 0x00a4862612000000 0x00010c0e00000000 0x0000860700000000

def z183 : W := mkw 0x8030a30140628210 0x40185180a0314108 0xcf70c20182e30739 0x67b86100c171839c

def z184 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x0070000000e00000 0x0038000000700000

def z185 : W := mkw 0xc0fbabda03fe97c0 0xe07dd5ed01ff4be0 0xbcff2ffe03fcdfc1 0xde7f97ff01fe6fe0

def z186 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0x3cff007e03fc00c1 0x9e7f803f01fe0060

def z187 : W := mkw 0x7802009213156def 0x3c010049098ab6f7 0x02000000031fffff 0x01000000018fffff

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x74013c0000000000 0x3a009e0000000000

def z189 : W := mkw 0x0000040424000000 0x0000020212000000 0x41003c007c000000 0x20801e003e000000

def z190 : W := mkw 0xe97dffeffd66ce72 0x74befff7feb36739 0xffffffffffffffff 0xffffffffffffffff

def z191 : W := mkw 0xf836f7b7ff77efff 0x7c1b7bdbffbbf7ff 0xffffffffffffffff 0xffffffffffffffff

def z192 : W := mkw 0x117fff7dee11218d 0x08bfffbef70890c6 0xfdfffffffc1020c6 0xfefffffffe081063

def z193 : W := mkw 0x0124fc25ec43b001 0x80927e12f621d800 0x4300fc01fc03f800 0x21807e00fe01fc00

def z194 : W := mkw 0x0179af6dec000000 0x00bcd7b6f6000000 0x91f12ffffc000000 0xc8f897fffe000000

def z195 : W := mkw 0x0020a00000428000 0x0010500000214000 0x1070200001e0c000 0x0838100000f06000

def z196 : W := mkw 0xe830a7877566ce72 0x741853c3bab36739 0xff71ff8fffffffff 0xffb8ffc7ffffffff

def z197 : W := mkw 0x6800048635044c62 0x340002431a822631 0x30013d8e7d1cf8c6 0x98009ec73e8e7c63

def z198 : W := mkw 0x80db03d803b80780 0x406d81ec01dc03c0 0x9cfe03f003e00701 0x4e7f01f801f00380

def z199 : W := mkw 0x004b001002980180 0x00258008014c00c0 0xbcff027003fc07c1 0xde7f813801fe03e0

def z200 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0xbcff03fe01ec0000 0xde7f81ff00f60000

def z201 : W := mkw 0x2124fc25fc42c030 0x10927e12fe216018 0x4300fc01fc03c038 0x21807e00fe01e01c

def z202 : W := mkw 0x8030a38141200600 0x401851c0a0900300 0xdd70e381f3e00701 0x6eb871c0f9f00380

def z203 : W := mkw 0x2800040434004822 0x140002021a002411 0xf7013d8e7c00f826 0xfb809ec73e007c13

def z204 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x5271fc0001eff800 0x2938fe0000f7fc00

def z205 : W := mkw 0x106ff8308a11218d 0x0837fc18450890c6 0xfffffe718e1327ff 0xffffff38c70993ff

def z206 : W := mkw 0xa010038151204630 0x500801c0a8902318 0x0000018070000000 0x000000c038000000

def z207 : W := mkw 0x0004502088000000 0x0002281044000000 0xef8ed2718e030739 0xf7c76938c701839c

def z208 : W := mkw 0xe80004863566ce72 0x740002431ab36739 0xf7013d8e7fffffff 0xfb809ec73fffffff

def z209 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffc700ffff8c7 0xbf7ffe3807fffc63

def z210 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0xfefffe7003ffffc1 0xff7fff3801ffffe0

def z211 : W := mkw 0x006ff80002112001 0x0037fc0001089000 0x7e7ffc0002132001 0x3f3ffe0001099000

def z212 : W := mkw 0x0049000000000000 0x0024800000000000 0x3c7f000000000000 0x1e3f800000000000

def z213 : W := mkw 0x697fffefffdffc63 0xb4bffff7ffeffe31 0xfffffffffffffce7 0xfffffffffffffe73

def z214 : W := mkw 0x100000308800018c 0x08000018440000c6 0x0080027180000318 0x00400138c000018c

def z215 : W := mkw 0x0030a30140000000 0x00185180a0000000 0xdf70e381f2030739 0x6fb871c0f901839c

def z216 : W := mkw 0xc1df5ffeafbc07c0 0x60efafff57de03e0 0xbcff1ffe0ffc07c1 0xde7f8fff07fe03e0

def z217 : W := mkw 0x0000000000000000 0x0000000000000000 0xc700000000000421 0x6380000000000210

def z218 : W := mkw 0x2800040434004822 0x140002021a002411 0x010000007c000026 0x008000003e000013

def z219 : W := mkw 0xc09003da012407c0 0x604801ed009203e0 0x9cf003fe03e007c1 0xce7801ff01f003e0

def z220 : W := mkw 0x0020a00000428000 0x0010500000214000 0x0870c00002e30000 0x0438600001718000

def z221 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0xbcff03fe02e00300 0xde7f81ff01700180

def z222 : W := mkw 0x1002001002dbb18d 0x88010008016dd8c6 0x0200000003ffffff 0x0100000001ffffff

def z223 : W := mkw 0x0049080000881000 0x8024840000440800 0x00010c00000c1800 0x0000860000060c00

def z224 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x200f1c00001c3800 0x10078e00000e1c00

def z225 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xffff13fe0ffc27e7 0xffff89ff07fe13f3

def z226 : W := mkw 0xa010038011204620 0x500801c008902310 0xdf70238073e0c721 0x6fb811c039f06390

def z227 : W := mkw 0x6800048635044c62 0x340002431a822631 0xe700118e7c1024e7 0xf38008c73e081273

def z228 : W := mkw 0x2000008011004420 0x1000004008802210 0xf7013d80711cfc21 0x7b809ec0388e7e10

def z229 : W := mkw 0x100200100211218d 0x08010008010890c6 0xae8e0270021327ff 0xd7470138010993ff

def z230 : W := mkw 0x0006500002112001 0x0003280001089000 0x6e0ed00002132001 0x3707680001099000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z232 : W := mkw 0x0000000000000000 0x0000000000000000 0x10012c00010cd800 0x0800960000866c00

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0x430010000c002026 0x2180080006001013

def z234 : W := mkw 0x797fffffff156def 0x3cbfffffff8ab6f7 0xffffffffff1fffff 0xffffffffff8fffff

def z235 : W := mkw 0xc0db07de27bc07c0 0x606d83ef13de03e0 0xfdff3ffe7ffc07c1 0xfeff9fff3ffe03e0

def z236 : W := mkw 0xe8fba7df77fecff2 0x747dd3efbbff67f9 0xffffffffffffffff 0xffffffffffffffff

def z237 : W := mkw 0x4080005a000401c0 0x2040002d000200e0 0x0080007e000000c0 0x8040003f00000060

def z238 : W := mkw 0xe082009213fec7f0 0x7041004909ff63f8 0x0200000003ffc7f9 0x0100000001ffe3fc

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000002030739 0x010000000101839c

def z240 : W := mkw 0x2000008011004420 0x1000004008802210 0x020000000100c421 0x0100000000806210

def z241 : W := mkw 0x2000048435004420 0x100002421a802210 0xf7013d8e7d00c421 0xfb809ec73e806210

def z242 : W := mkw 0x817dff6dec628210 0x40beffb6f6314108 0xfdfffffffee30318 0xfeffffffff71818c

def z243 : W := mkw 0xa020a0815162c630 0x50105040a8b16318 0x4300e001f3e3c739 0x21807000f9f1e39c

def z244 : W := mkw 0x01000425ec000000 0x00800212f6000000 0x01000001fc000000 0x00800000fe000000

def z245 : W := mkw 0xa17dffedfd62c630 0x50befff6feb16318 0xfdfffffffde0c000 0xfefffffffef06000

def z246 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x620ffc00001ff800 0x3107fe00000ffc00

def z247 : W := mkw 0x2030a3015042c030 0x10185180a8216018 0xdf70e381f003c038 0x6fb871c0f801e01c

def z248 : W := mkw 0x807ffb0142fbb211 0xc03ffd80a17dd908 0x7e7ffe0183fffb19 0x3f3fff00c1fffd8c

def z249 : W := mkw 0x80fffb5802fbb381 0xc07ffdac017dd9c0 0x7efffe7003fffb01 0x3f7fff3801fffd80

def z250 : W := mkw 0xa00000801162c630 0x5000004008b16318 0xd700218073e3c739 0x6b8010c039f1e39c

def z251 : W := mkw 0x9036f331ca73a39d 0x481b7998e539d1ce 0xeffed2718ef327ff 0xf7ff6938c77993ff

def z252 : W := mkw 0x0120ac0564000000 0x00905602b2000000 0x00002c0070000000 0x0000160038000000

def z253 : W := mkw 0x0006500002112001 0x0003280001089000 0xef0ed0000e1324e7 0xf787680007099273

def z254 : W := mkw 0xc0800092012407c0 0x60400049009203e0 0x00000000000007c0 0x00000000000003e0

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7013c000d1cfce7 0xfb809e00068e7e73

def z256 : W := mkw 0x100200308a10018c 0x08010018450800c6 0xad8e02718e1007ff 0xd6c70138c70803ff

def z257 : W := mkw 0x4800000200040842 0x2400000100020421 0x00000000001c38c6 0x00000000000e1c63

def z258 : W := mkw 0x4800040624040842 0x2400020312020421 0xf5013d8e7c1c38c6 0xfa809ec73e0e1c63

def z259 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xffff23fe73fcc7e1 0xffff91ff39fe63f0

def z260 : W := mkw 0xc8db07de27bc0fc2 0x646d83ef13de07e1 0xbcff1ffe0ffc3fc7 0xde7f8fff07fe1fe3

def z261 : W := mkw 0x0010034800000000 0x000801a400000000 0x808003fe00000000 0xc04001ff00000000

def z262 : W := mkw 0x6979afcf75044c62 0x34bcd7e7ba822631 0x10712d8e710cd800 0x083896c738866c00

def z263 : W := mkw 0xc1f9afcf65ac0640 0x60fcd7e7b2d60320 0x10712d8e71ec0000 0x083896c738f60000

def z264 : W := mkw 0xd0df53fa8bbd27cd 0x686fa9fd45de93e6 0xbcffc3ff83ff07d9 0xde7fe1ffc1ff83ec

def z265 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xff71e38ff3ffc7f9 0xffb8f1c7f9ffe3fc

def z266 : W := mkw 0xa830a7857562ce32 0x541853c2bab16719 0xdf70ff81ffe3ff3f 0x6fb87fc0fff1ff9f

def z267 : W := mkw 0xc1ffffffefbc07c0 0x60fffffff7de03e0 0xfdfffffffffc07c1 0xfefffffffffe03e0

def z268 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x307f3c0001fcf800 0x183f9e0000fe7c00

def z269 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x760f3c00011cf801 0x3b079e00008e7c00

def z270 : W := mkw 0x68cb04de379c4de2 0x3465826f1bce26f1 0xf78f3dfe7d1cfce7 0xfbc79eff3e8e7e73

def z271 : W := mkw 0x100000308800018c 0x08000018440000c6 0x818002718c0007fe 0xc0c00138c60003ff

def z272 : W := mkw 0xe0b0a3db5166c7f0 0x705851eda8b363f8 0xdff0e3fff3e3c7f9 0xeff871fff9f1e3fc

def z273 : W := mkw 0xa07ffb8153fbf631 0xd03ffdc0a9fdfb18 0xff7fff81f3ffff39 0x7fbfffc0f9ffff9c

def z274 : W := mkw 0x686ffc8637dffc63 0xb437fe431beffe31 0xff7ffd8e7ffffce7 0xffbffec73ffffe73

def z275 : W := mkw 0x100000000001200d 0x0800000000009006 0x020000000003203e 0x010000000001901f

def z276 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x28ffde7f8c000000 0x947fef3fc6000000

def z277 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x49fefe71fc000000 0x24ff7f38fe000000

def z278 : W := mkw 0x2020a0815142c430 0x10105040a8a16218 0xd700e181f103c439 0x6b8070c0f881e21c

def z279 : W := mkw 0x4800040624040842 0x2400020312020421 0x0000000e0c0000c6 0x8000000706000063

def z280 : W := mkw 0xc082009203ffb7c1 0xe041004901ffdbe0 0x0200000003ffffc1 0x0100000001ffffe0

def z281 : W := mkw 0x80d9034800a80200 0x406c81a400540100 0x0070000000e00000 0x0038000000700000

def z282 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0xf5713d8e7c000000 0xfab89ec73e000000

def z283 : W := mkw 0x0000000000ca9000 0x8000000000654800 0x0000000001ecd800 0x0000000000f66c00

def z284 : W := mkw 0x0002000002100000 0x0001000001080000 0x2c0e000002100001 0x1607000001080000

def z285 : W := mkw 0x0006500002dbb001 0x80032800016dd800 0x6e0ed00003fff801 0x3707680001fffc00

def z286 : W := mkw 0x6800048635044c62 0x340002431a822631 0x43003c007d1cfce7 0x21801e003e8e7e73

def z287 : W := mkw 0xa010038151204630 0x500801c0a8902318 0xcf00c381f2030739 0x678061c0f901839c

def z288 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc1024e7 0xfffffffffe081273

def z289 : W := mkw 0x0020a00000428000 0x0010500000214000 0xdf70e20183e3c739 0x6fb87100c1f1e39c

def z290 : W := mkw 0x4000008201040440 0x2000004100820220 0xf6013d8e011cfcc1 0xfb009ec7008e7e60

def z291 : W := mkw 0x1124fc25ec01200d 0x08927e12f6009006 0x4300fc01fc03203e 0x21807e00fe01901f

def z292 : W := mkw 0x9036f331ca73a39d 0x481b7998e539d1ce 0x08fec27182e30318 0x047f6138c171818c

def z293 : W := mkw 0x100650308adbb18d 0x88032818456dd8c6 0xef8ed2718fffffff 0xf7c76938c7ffffff

def z294 : W := mkw 0x1110077dec00018c 0x088803bef60000c6 0x818003fffc0007fe 0xc0c001fffe0003ff

def z295 : W := mkw 0x6924fca7fd044c62 0x34927e53fe822631 0xf701fd8ffd1cfce7 0xfb80fec7fe8e7e73

def z296 : W := mkw 0x686ff88213dffc63 0xb437fc4109effe31 0x7e7ffc0003fffce7 0x3f3ffe0001fffe73

def z297 : W := mkw 0x2000008011004420 0x1000004008802210 0xdf00e381f303c739 0x6f8071c0f981e39c

def z298 : W := mkw 0x0179af4d64ca9000 0x80bcd7a6b2654800 0x10712d8e71ecd800 0x083896c738f66c00

def z299 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x0a7ec00003fff801 0x053f600001fffc00

def z300 : W := mkw 0xe8d907ce35ac4e62 0x746c83e71ad62731 0x10712d8e71ecd800 0x083896c738f66c00

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x6600100000102001 0x3300080000081000

def z302 : W := mkw 0x1036f331ca11218d 0x081b7998e50890c6 0xfffef3f1fe1327ff 0xffff79f8ff0993ff

def z303 : W := mkw 0x0024f8000043b001 0x80127c000021d800 0x7601fc00011ff801 0x3b00fe00008ffc00

def z304 : W := mkw 0x0000040424000000 0x0000020212000000 0x8100018e7c000000 0xc08000c73e000000

def z305 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffe030739 0xffffffffff01839c

def z306 : W := mkw 0x0002000002980000 0x00010000014c0000 0x0000000003fc0001 0x0000000001fe0000

def z307 : W := mkw 0x017fff4d66dbb001 0x80bfffa6b36dd800 0x7e7ffd8e73fff801 0x3f3ffec739fffc00

def z308 : W := mkw 0x4000008201040440 0x2000004100820220 0x00000000011c04c1 0x00000000008e0260

def z309 : W := mkw 0xe0db03da13fec7f0 0x706d81ed09ff63f8 0xbeff03fe03ffc7f9 0xdf7f81ff01ffe3fc

def z310 : W := mkw 0x105f53788a11218d 0x082fa9bc450890c6 0xffffd3ff8e1327ff 0xffffe9ffc70993ff

def z311 : W := mkw 0x4000048625040440 0x2000024312820220 0xf5013d8e7d1c04c1 0xfa809ec73e8e0260

def z312 : W := mkw 0xb034f3a1d963e63d 0x581a79d0ecb1f31e 0xdf70f381ffe3e73f 0x6fb879c0fff1f39f

def z313 : W := mkw 0x48cb045e269c09c2 0x2465822f134e04e1 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z314 : W := mkw 0x017fff6dee980000 0x00bfffb6f74c0000 0xfdfffffffffc0001 0xfefffffffffe0000

def z315 : W := mkw 0x0030a30140000000 0x00185180a0000000 0x0870c20180000000 0x04386100c0000000

def z316 : W := mkw 0x8000008001200600 0x4000004000900300 0x0000000003e00701 0x0000000001f00380

def z317 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0x4b70e201f2e3c338 0x25b87100f971e19c

def z318 : W := mkw 0x100000208800000c 0x0800001044000006 0x010000018c00003e 0x00800000c600001f

def z319 : W := mkw 0x0004502088000000 0x0002281044000000 0x208e10700c000000 0x9047083806000000

def z320 : W := mkw 0x58065436ae1529cf 0x2c032a1b570a94e7 0xef8fde7f8e1f3fff 0xf7c7ef3fc70f9fff

def z321 : W := mkw 0x0124fc25ec000000 0x00927e12f6000000 0xf501fd8ffc000000 0xfa80fec7fe000000

def z322 : W := mkw 0x0020a00000000000 0x0010500000000000 0x5c70e00000000000 0x2e38700000000000

def z323 : W := mkw 0x10065434ae11218d 0x08032a1a570890c6 0xff8ffffffe1327ff 0xffc7ffffff0993ff

def z324 : W := mkw 0xe882009213bc4fe2 0x7441004909de27f1 0x0200000003fcffe7 0x0100000001fe7ff3

def z325 : W := mkw 0x6800048635044c62 0x340002431a822631 0x76013d8e711cf801 0x3b009ec7388e7c00

def z326 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x1870e381f3e3c318 0x0c3871c0f9f1e18c

def z327 : W := mkw 0x0030a30140428000 0x00185180a0214000 0xdf70e381f3e3c001 0x6fb871c0f9f1e000

def z328 : W := mkw 0x0000040424000000 0x0000020212000000 0x10012d8e70000000 0x080096c738000000

def z329 : W := mkw 0x8030a38141628610 0x401851c0a0b14308 0x9c70c38183e30719 0x4e3861c0c1f1838c

def z330 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x5e70e18073e3c001 0x2f3870c039f1e000

def z331 : W := mkw 0x2024f8015043f031 0x90127c00a821f818 0x4300fc01f003f838 0x21807e00f801fc1c

def z332 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x18ff03fe03ec0300 0x0c7f81ff01f60180

def z333 : W := mkw 0xe830a7877566ce72 0x741853c3bab36739 0xdf71ef8ff3efdf39 0x6fb8f7c7f9f7ef9c

def z334 : W := mkw 0xc010038201240640 0x600801c100920320 0xbc71038e03fc07c1 0xde3881c701fe03e0

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x34010000011c0001 0x1a008000008e0000

def z336 : W := mkw 0x0110076dec000000 0x008803b6f6000000 0xf5813ffffc000000 0xfac09ffffe000000

def z337 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xed8ed2718e030318 0xf6c76938c701818c

def z338 : W := mkw 0x6800008211044c62 0x3400004108822631 0x00000000010cd800 0x0000000000866c00

def z339 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf5013d8e7d0cd800 0xfa809ec73e866c00

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0xa4000000001004c1 0xd200000000080260

def z341 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xffffc3ff83ff07f9 0xffffe1ffc1ff83fc

def z342 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x88fe03fe02e007c0 0xc47f01ff017003e0

def z343 : W := mkw 0xb00650b09b73e7bd 0x580328584db9f3de 0xef8ed2718ff3e7ff 0xf7c76938c7f9f3ff

def z344 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffe7183fffb19 0x3f7fff38c1fffd8c

def z345 : W := mkw 0x2000008011004420 0x1000004008802210 0x100021807100c000 0x080010c038806000

def z346 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0x28ff027e02fc03c0 0x947f813f017e01e0

def z347 : W := mkw 0xc0fba3db43bc07c0 0x607dd1eda1de03e0 0xfdffe3fff3fc07c1 0xfefff1fff9fe03e0

def z348 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfeff3ffe03fcffc1 0xff7f9fff01fe7fe0

def z349 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x0a70c20183e3c739 0x05386100c1f1e39c

def z350 : W := mkw 0x6800008211044c62 0x3400004108822631 0x00000000000004e6 0x0000000000000273

def z351 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf5013d8e7c0004e6 0xfa809ec73e000273

def z352 : W := mkw 0x8010038001200600 0x400801c000900300 0x8000038000000700 0x400001c000000380

def z353 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x4a7efc0002e3f800 0x253f7e000171fc00

def z354 : W := mkw 0xa17fffedfffbf631 0xd0bffff6fffdfb18 0xffffffffffffff39 0xffffffffffffff9c

def z355 : W := mkw 0x8030a30140628210 0x40185180a0314108 0xdd70e381f2e30318 0x6eb871c0f971818c

def z356 : W := mkw 0xe830a7877566ce72 0x741853c3bab36739 0xf7713d8e7dfcfce7 0xfbb89ec73efe7e73

def z357 : W := mkw 0x005b034802980000 0x002d81a4014c0000 0xbcff03fe03fc0001 0xde7f81ff01fe0000

def z358 : W := mkw 0xa01003801162c630 0x500801c008b16318 0x9e70038003e3c739 0x4f3801c001f1e39c

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x200010000c1020c6 0x9000080006081063

def z360 : W := mkw 0xb030a3b1d962c7bc 0x581851d8ecb163de 0xdff0e3f1ffe3c7ff 0xeff871f8fff1e3ff

def z361 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x08fe027003fc07c1 0x047f013801fe03e0

def z362 : W := mkw 0x0004502088000000 0x0002281044000000 0xef8ed2718c1024e7 0xf7c76938c6081273

def z363 : W := mkw 0x2924fc25fc004822 0x14927e12fe002411 0x4300fc01fc00f826 0x21807e00fe007c13

def z364 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff70f381fff3e7ff 0xffb879c0fff9f3ff

def z365 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x008e007000000000 0x0047003800000000

def z366 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0x7f7ffc018ffff83f 0x3fbffe00c7fffc1f

def z367 : W := mkw 0x016ffc25eedbb001 0x80b7fe12f76dd800 0x7f7ffc01fffff801 0x3fbffe00fffffc00

def z368 : W := mkw 0x58065436ae1529cf 0x2c032a1b570a94e7 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z369 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xac8ec271821307d9 0xd6476138c10983ec

def z370 : W := mkw 0x015d5f6cac000000 0x00aeafb656000000 0xbcff1ffe0c000000 0xde7f8fff06000000

def z371 : W := mkw 0x004b000002dbb001 0x80258000016dd800 0x3e7f000003fff801 0x1f3f800001fffc00

def z372 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffd1cf801 0xfffffffffe8e7c00

def z373 : W := mkw 0x117fff7dee11218d 0x08bfffbef70890c6 0xfdfffffffe030318 0xfeffffffff01818c

def z374 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0xb471018e01fc04c1 0xda3880c700fe0260

def z375 : W := mkw 0xa030a7857562c630 0x501853c2bab16318 0xff71ff8fffe3c739 0xffb8ffc7fff1e39c

def z376 : W := mkw 0x017ffb69cadbb001 0x80bffdb4e56dd800 0x7efffe7183fff801 0x3f7fff38c1fffc00

def z377 : W := mkw 0xe80000821166ce72 0x7400004108b36739 0x0200000003ffffff 0x0100000001ffffff

def z378 : W := mkw 0x6830a78775044c62 0x341853c3ba822631 0xff71ff8ffd1cfce7 0xffb8ffc7fe8e7e73

def z379 : W := mkw 0xd09003fa892407cc 0x684801fd449203e6 0x818003ff8c0007fe 0xc0c001ffc60003ff

def z380 : W := mkw 0x0020a00140428010 0x00105000a0214008 0x0000c00180030018 0x00006000c001800c

def z381 : W := mkw 0x00cb005802980180 0x0065802c014c00c0 0x008e007000000000 0x0047003800000000

def z382 : W := mkw 0x81fffb79cab80380 0x40fffdbce55c01c0 0x08fec27182e00300 0x047f6138c1700180

def z383 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0xf58f3dfe7c000000 0xfac79eff3e000000

def z384 : W := mkw 0xa020a0801162c630 0x5010504008b16318 0x5e70e00003e3c739 0x2f38700001f1e39c

def z385 : W := mkw 0x006dfc0424000000 0x0036fe0212000000 0xfd7ffd8e7c000000 0xfebffec73e000000

def z386 : W := mkw 0x100200100211218d 0x08010008010890c6 0xe70010000e1327ff 0xf3800800070993ff

def z387 : W := mkw 0xe0f9a3cb51eec670 0x707cd1e5a8f76338 0x1071218e71ecc000 0x083890c738f66000

def z388 : W := mkw 0x2800000010004822 0x1400000008002411 0x020000000000f826 0x0100000000007c13

def z389 : W := mkw 0x006ff80002980000 0x0037fc00014c0000 0x7c7ffc0003fc0001 0x3e3ffe0001fe0000

def z390 : W := mkw 0x6802049637144de2 0x3401024b1b8a26f1 0xff8f3ffe7f1cffe7 0xffc79fff3f8e7ff3

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000001024e7 0x0100000000081273

def z392 : W := mkw 0xc0fffbca03ffb641 0xe07ffde501ffdb20 0x7e7ffd8e03fff801 0x3f3ffec701fffc00

def z393 : W := mkw 0xa034f3a1d962c630 0x501a79d0ecb16318 0xfffef3f1ffe3c739 0xffff79f8fff1e39c

def z394 : W := mkw 0xc19007ffed2407c0 0x60c803fff69203e0 0x818003fffc0007c0 0xc0c001fffe0003e0

def z395 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xed8ed2718c1020c6 0xf6c76938c6081063

def z396 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xa18e12718c1027fe 0xd0c70938c60813ff

def z397 : W := mkw 0xa01003815162c630 0x500801c0a8b16318 0x83000381f3e3c739 0x418001c0f9f1e39c

def z398 : W := mkw 0xe0db03db53bc47f0 0x706d81eda9de23f8 0xbdff03fff3fc07f9 0xdeff81fff9fe03fc

def z399 : W := mkw 0x104f50308a99218d 0x0827a818454c90c6 0xffffd2718fff27ff 0xffffe938c7ff93ff

def z400 : W := mkw 0xd1ffffffefbd27cd 0x68fffffff7de93e6 0xffffffffffff27ff 0xffffffffffff93ff

def z401 : W := mkw 0xd08650b28bbd27cd 0x6843285945de93e6 0xef8ed2718fff27ff 0xf7c76938c7ff93ff

def z402 : W := mkw 0x300650b09b1165ad 0x180328584d88b2d6 0xff8ef3f1ff13e7ff 0xffc779f8ff89f3ff

def z403 : W := mkw 0x206ff80152dbf031 0x9037fc00a96df818 0x7f7ffc01f3fff839 0x3fbffe00f9fffc1c

def z404 : W := mkw 0x0024f8000043b001 0x80127c000021d800 0x5e70fc0003e3f801 0x2f387e0001f1fc00

def z405 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0x3cff027003fc0301 0x1e7f813801fe0180

def z406 : W := mkw 0xa179afcd7562c630 0x50bcd7e6bab16318 0x10712d8e71e0c000 0x083896c738f06000

def z407 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0xedfed2718c000000 0xf6ff6938c6000000

def z408 : W := mkw 0xc1db07ffefbc07c0 0x60ed83fff7de03e0 0xbdff03fffffc07c1 0xdeff81fffffe03e0

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00c00002030001 0x2700600001018000

def z410 : W := mkw 0x0059074c24000000 0x002c83a612000000 0xfdff3ffe7c000000 0xfeff9fff3e000000

def z411 : W := mkw 0x6800048635044c62 0x340002431a822631 0x8300018e7d1cfce7 0xc18000c73e8e7e73

def z412 : W := mkw 0xa079a3c95162c630 0x503cd1e4a8b16318 0xffffe3fff3e3c739 0xfffff1fff9f1e39c

def z413 : W := mkw 0x100450208801200d 0x0802281044009006 0x0000c00180030018 0x00006000c001800c

def z414 : W := mkw 0xe87fff8777fffe73 0xf43fffc3bbffff39 0xff7fff8fffffffff 0xffbfffc7ffffffff

def z415 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0xbcff2ffe70000000 0xde7f97ff38000000

def z416 : W := mkw 0x780004b6bd044dee 0x3c00025b5e8226f7 0xf7813ffffd1cffff 0xfbc09ffffe8e7fff

def z417 : W := mkw 0x100000308800018c 0x08000018440000c6 0xcf80c2718e0307ff 0xe7c06138c70183ff

def z418 : W := mkw 0x2800040434004822 0x140002021a002411 0x77013c007d1cf827 0x3b809e003e8e7c13

def z419 : W := mkw 0xa07dfb815162c630 0x503efdc0a8b16318 0xff7fff81f3e3c739 0x7fbfffc0f9f1e39c

def z420 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff71ff81f3ffff39 0x7fb8ffc0f9ffff9c

def z421 : W := mkw 0x104f58308a99318d 0x8827ac18454c98c6 0x208f1c700c1c38c6 0x90478e38060e1c63

def z422 : W := mkw 0x8012039003300780 0x400901c8019803c0 0xbcfe03f003f007c1 0xde7f01f801f803e0

def z423 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00d2018e1327ff 0xf7806900c70993ff

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c70000003e00001 0x0e38000001f00000

def z425 : W := mkw 0x0002001002100180 0x00010008010800c0 0xef8e12700e1027e7 0xf7c70938070813f3

def z426 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x8970c381f2e30738 0x44b861c0f971839c

def z427 : W := mkw 0x0020a00000428000 0x0010500000214000 0x4200e0000003c000 0x210070000001e000

def z428 : W := mkw 0x90df53788ab9238d 0x486fa9bc455c91c6 0xeffed2718ef327ff 0xf7ff6938c77993ff

def z429 : W := mkw 0x6000008211044460 0x3000004108822230 0xf701218e711cc4e1 0xfb8090c7388e6270

def z430 : W := mkw 0xf8df57febfbd6fef 0x7c6fabff5fdeb7f7 0xffffffffffffffff 0xffffffffffffffff

def z431 : W := mkw 0x3024f021d843e03d 0x18127810ec21f01e 0x4300f001fc03e03e 0x21807800fe01f01f

def z432 : W := mkw 0x6800008211044c62 0x3400004108822631 0xe70010000d1cfce7 0xf3800800068e7e73

def z433 : W := mkw 0x0020a00000428000 0x0010500000214000 0x7e71fc0003fff801 0x3f38fe0001fffc00

def z434 : W := mkw 0xa0fba3d953fac7b0 0x507dd1eca9fd63d8 0xdffee3f1f3e3c739 0x6fff71f8f9f1e39c

def z435 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x638ed0718c1320fe 0xb1c76838c609907f

def z436 : W := mkw 0x0010030140000000 0x00080180a0000000 0x81000381f0000000 0x408001c0f8000000

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00020002000701 0x4600010001000380

def z438 : W := mkw 0x2000008011004420 0x1000004008802210 0xf70031807d10e4e7 0xfb8018c03e887273

def z439 : W := mkw 0x206ff88013dbf421 0x9037fc4009edfa10 0xff7ffd8073fffc21 0x7fbffec039fffe10

def z440 : W := mkw 0x100200308a11218d 0x08010018450890c6 0x838002718e1327ff 0xc1c00138c70993ff

def z441 : W := mkw 0x0130a76dec000000 0x009853b6f6000000 0xddf0e3fffc000000 0xeef871fffe000000

def z442 : W := mkw 0x0004502088000000 0x0002281044000000 0x4100d0018c000000 0x20806800c6000000

def z443 : W := mkw 0x0026f8000253b001 0x80137c000129d800 0x6e0efc000213f801 0x37077e000109fc00

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x810000000c0004e6 0xc080000006000273

def z445 : W := mkw 0x0079a34940000000 0x003cd1a4a0000000 0xfdffe3fff0000000 0xfefff1fff8000000

def z446 : W := mkw 0xa032a38153fbf631 0xd01951c0a9fdfb18 0xdf70e381f3ffff39 0x6fb871c0f9ffff9c

def z447 : W := mkw 0x100000308800018c 0x08000018440000c6 0xe78012718c1027ff 0xf3c00938c60813ff

def z448 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x5e70e20183e3c319 0x2f387100c1f1e18c

def z449 : W := mkw 0x405903ca01040440 0x202c81e500820220 0xbcff03fe011c04c1 0xde7f81ff008e0260

def z450 : W := mkw 0x007dfb0140000000 0x003efd80a0000000 0xfd7fff81f0000000 0x7ebfffc0f8000000

def z451 : W := mkw 0x0006500002112001 0x0003280001089000 0xef0ed20182132739 0x77876900c109939c

def z452 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xd770218071e0c421 0x6bb810c038f06210

def z453 : W := mkw 0x0026f0000253a001 0x001378000129d000 0x7e7ef00003f3e001 0x3f3f780001f9f000

def z454 : W := mkw 0xa11007edfd204630 0x508803f6fe902318 0x818003fffc000738 0xc0c001fffe00039c

def z455 : W := mkw 0x000650308a100180 0x00032818450800c0 0xed8ed2718e1007c1 0xf6c76938c70803e0

def z456 : W := mkw 0x807ffb8003fbb601 0xc03ffdc001fddb00 0xfe7fff8003ffff01 0x7f3fffc001ffff80

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x42003c000000f800 0x21001e0000007c00

def z458 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xc300e381f003c738 0x618071c0f801e39c

def z459 : W := mkw 0x017dff6dec43b001 0x80beffb6f621d800 0xfffffffffc03f800 0xfffffffffe01fc00

def z460 : W := mkw 0xa002008013fbf631 0xd001004009fdfb18 0x0200000003ffff39 0x0100000001ffff9c

def z461 : W := mkw 0x117ffb79ca11218d 0x08bffdbce50890c6 0xeffed2718e1327ff 0xf7ff6938c70993ff

def z462 : W := mkw 0x0026f80002dbb001 0x80137c00016dd800 0x4200fc0003fff801 0x21007e0001fffc00

def z463 : W := mkw 0x90df53788ab9238d 0x486fa9bc455c91c6 0x08fec27182e30318 0x047f6138c171818c

def z464 : W := mkw 0xe89007de35244fe2 0x744803ef1a9227f1 0xf7813ffe7d1cffe7 0xfbc09fff3e8e7ff3

def z465 : W := mkw 0x005d536888000000 0x002ea9b444000000 0xfdffd3ff8c000000 0xfeffe9ffc6000000

def z466 : W := mkw 0xc0eff89203ffb7c1 0xe077fc4901ffdbe0 0x7e7ffc0003ffffc1 0x3f3ffe0001ffffe0

def z467 : W := mkw 0x014f5c6cae993001 0x80a7ae36574c9800 0x208f1c7e0c1c3800 0x90478e3f060e1c00

def z468 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x6e8ed27182132319 0x37476938c109918c

def z469 : W := mkw 0xc0cb00da03bc07c0 0x6065806d01de03e0 0x208f007e03fc07c1 0x9047803f01fe03e0

def z470 : W := mkw 0x1126fc35ee11218d 0x08937e1af70890c6 0xef8efe71fe1327ff 0xf7c77f38ff0993ff

def z471 : W := mkw 0x4800040624040842 0x2400020312020421 0x76013c0e0d1cf8c7 0xbb009e07068e7c63

def z472 : W := mkw 0xc082009203bc07c0 0x6041004901de03e0 0xb401018e03fc07c1 0xda0080c701fe03e0

def z473 : W := mkw 0xb036f3b1db73e7bd 0x581b79d8edb9f3de 0xdffee3f1f3e3c739 0x6fff71f8f9f1e39c

def z474 : W := mkw 0x6800008211044c62 0x3400004108822631 0xb601018e011cfce7 0xdb0080c7008e7e73

def z475 : W := mkw 0x0024f8000043b001 0x80127c000021d800 0x0000c00000030000 0x0000600000018000

def z476 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x12712c0003fff801 0x0938960001fffc00

def z477 : W := mkw 0x0006500002112001 0x0003280001089000 0x7e0ffc00031ff801 0x3f07fe00018ffc00

def z478 : W := mkw 0x80fba35942fa8390 0x407dd1aca17d41c8 0x08fec27182e30318 0x047f6138c171818c

def z479 : W := mkw 0xa010038151204630 0x500801c0a8902318 0xd7002381f100c739 0x6b8011c0f880639c

def z480 : W := mkw 0x6824fc863547fc63 0xb4127e431aa3fe31 0xf701fd8e7d1ffce7 0xfb80fec73e8ffe73

def z481 : W := mkw 0x41cf5c7eae9c01c0 0x20e7ae3f574e00e0 0x208f1c7e0c1c00c0 0x90478e3f060e0060

def z482 : W := mkw 0xb00200901373e7bd 0x5801004809b9f3de 0x0200000003f3e7ff 0x0100000001f9f3ff

def z483 : W := mkw 0x0100046cac000000 0x0080023656000000 0x0080007e0c000000 0x8040003f06000000

def z484 : W := mkw 0x780654b6bf156def 0x3c032a5b5f8ab6f7 0xef8ed3fffe1327ff 0xf7c769ffff0993ff

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0xac8e027000000000 0xd647013800000000

def z486 : W := mkw 0x297dff6dfc004822 0x14beffb6fe002411 0xfffffffffc00f826 0xfffffffffe007c13

def z487 : W := mkw 0x817dfb69c8628210 0x40befdb4e4314108 0x08fec27182e30318 0x047f6138c171818c

def z488 : W := mkw 0x0004500000012001 0x0002280000009000 0x4200d00000032000 0x2100680000019000

def z489 : W := mkw 0xe8db07de37bc4fe2 0x746d83ef1bde27f1 0xbdff03fe7ffc07e7 0xdeff81ff3ffe03f3

def z490 : W := mkw 0x6800048635044c62 0x340002431a822631 0xb501018e7d1c04e7 0xda8080c73e8e0273

def z491 : W := mkw 0xc1fffbfbcbbc07c0 0x60fffdfde5de03e0 0xbcffc3ff83fc07c1 0xde7fe1ffc1fe03e0

def z492 : W := mkw 0x406ff88203dfb441 0xa037fc4101efda20 0xfe7ffd8e03fffcc1 0xff3ffec701fffe60

def z493 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x08fec27182e30318 0x047f6138c171818c

def z494 : W := mkw 0x0059034800000000 0x002c81a400000000 0x1071018e00000000 0x083880c700000000

def z495 : W := mkw 0x780650b29b156def 0x3c0328594d8ab6f7 0xef8ed2718f1fffff 0xf7c76938c78fffff

def z496 : W := mkw 0xa034fb815163f631 0xd01a7dc0a8b1fb18 0xdf70ff81f3e3ff39 0x6fb87fc0f9f1ff9c

def z497 : W := mkw 0x0179ab4940000000 0x00bcd5a4a0000000 0x0070000000000000 0x0038000000000000

def z498 : W := mkw 0x6802048637dffc63 0xb40102431beffe31 0xf7013d8e7ffffce7 0xfb809ec73ffffe73

def z499 : W := mkw 0x0004580000013001 0x80022c0000009800 0x00001c0000003800 0x00000e0000001c00

def z500 : W := mkw 0x007dfb4800000000 0x003efda400000000 0xfcfffffe00000000 0xfe7fffff00000000

def z501 : W := mkw 0xf0fff3fbdbffe7fd 0x787ff9fdedfff3fe 0xfffff3ffffffe7ff 0xfffff9fffffff3ff

def z502 : W := mkw 0x6800048635044c62 0x340002431a822631 0x12012d8e711cfce7 0x090096c7388e7e73

def z503 : W := mkw 0x2020a0015042c030 0x10105000a8216018 0xcf00e201f203c739 0x67807100f901e39c

def z504 : W := mkw 0x0800040424000802 0x0400020212000401 0x00001c000c003806 0x00000e0006001c03

def z505 : W := mkw 0xe09003db512447f0 0x704801eda89223f8 0x818003fff00007f8 0xc0c001fff80003fc

def z506 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xac8e12700e1027c7 0xd6470938070813e3

def z507 : W := mkw 0x100200100211218d 0x08010008010890c6 0xcf00c201821327ff 0x67806100c10993ff

def z508 : W := mkw 0x697dffeffd044c62 0x34befff7fe822631 0xfdfffffffc0004e6 0xfefffffffe000273

def z509 : W := mkw 0x114f5c7cae11218d 0x08a7ae3e570890c6 0x208f1c7e0c1020c6 0x90478e3f06081063

def z510 : W := mkw 0x40db035a029c01c0 0x206d81ad014e00e0 0xbcff03fe001c00c0 0xde7f81ff000e0060

def z511 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x5e7ee00003e3c001 0x2f3f700001f1e000

def z512 : W := mkw 0x6800048635044c62 0x340002431a822631 0x91012d8e7d0cdce6 0xc88096c73e866e73

def z513 : W := mkw 0x684b0486379c4c62 0x342582431bce2631 0xff7f3d8e7ffcfce7 0xffbf9ec73ffe7e73

def z514 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x9c70238073e0c701 0x4e3811c039f06380

def z515 : W := mkw 0x6800040634044862 0x340002031a022431 0x63013c0e7c1cf8e6 0xb1809e073e0e7c73

def z516 : W := mkw 0x117fff7deedbb18d 0x88bfffbef76dd8c6 0xffffffffffffffff 0xffffffffffffffff

def z517 : W := mkw 0x0002000002dbb001 0x80010000016dd800 0x76013c0003fff801 0x3b009e0001fffc00

def z518 : W := mkw 0x7802049637156def 0x3c01024b1b8ab6f7 0xf7013d8e7f1fffff 0xfb809ec73f8fffff

def z519 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x18ffeffff0000000 0x0c7ff7fff8000000

def z520 : W := mkw 0x6800048635044c62 0x340002431a822631 0x53013d8e7d0cf826 0x29809ec73e867c13

def z521 : W := mkw 0x6806548637156c63 0x34032a431b8ab631 0xff0ffd8e7f1ffce7 0xff87fec73f8ffe73

def z522 : W := mkw 0x016dfc6dec000000 0x00b6fe36f6000000 0x618ffc7ffc000000 0xb0c7fe3ffe000000

def z523 : W := mkw 0x0000000000428000 0x0000000000214000 0x0200000003e3c001 0x0100000001f1e000

def z524 : W := mkw 0xe830a7877566ce72 0x741853c3bab36739 0xdf70e38fffe3c7ff 0xefb871c7fff1e3ff

def z525 : W := mkw 0x217dffedfd004420 0x10befff6fe802210 0xfffffffffd00c421 0xfffffffffe806210

def z526 : W := mkw 0x6800008211044c62 0x3400004108822631 0x76013c00011cfce7 0x3b009e00008e7e73

def z527 : W := mkw 0x0124f821c8000000 0x00927c10e4000000 0x0000c00180000000 0x00006000c0000000

def z528 : W := mkw 0xd0df53fa8bbd27cd 0x686fa9fd45de93e6 0xbcff13fe0ffc27c7 0xde7f89ff07fe13e3

def z529 : W := mkw 0xa07ffb8153fbf631 0xd03ffdc0a9fdfb18 0x7e7ffd8073fff801 0x3f3ffec039fffc00

def z530 : W := mkw 0xc1ffffffefffb7c1 0xe0fffffff7ffdbe0 0xffffffffffffffc1 0xffffffffffffffe0

def z531 : W := mkw 0xa07ba38153fac630 0x503dd1c0a9fd6318 0xff7fe381f3ffc739 0x7fbff1c0f9ffe39c

def z532 : W := mkw 0x4800048625040c42 0x2400024312820621 0xb4011d8e0d1c3cc7 0xda008ec7068e1e63

def z533 : W := mkw 0x100450308801218d 0x08022818440090c6 0xc380d2718c0327fe 0xe1c06938c60193ff

def z534 : W := mkw 0x117ffb79ca11218d 0x08bffdbce50890c6 0x08fec27182030318 0x047f6138c101818c

def z535 : W := mkw 0x0030a70564000000 0x00185382b2000000 0xfd71ff8ffc000000 0xfeb8ffc7fe000000

def z536 : W := mkw 0xa032a3915372c7b0 0x501951c8a9b963d8 0xfffee3f1f3f3c7f9 0xffff71f8f9f9e3fc

def z537 : W := mkw 0x4000000200040040 0x2000000100020020 0x2001000e001c00c0 0x90008007000e0060

def z538 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x6e8ed0700e1320c7 0xb747683807099063

def z539 : W := mkw 0xb17ffffdff73e7bd 0x58bffffeffb9f3de 0xfffffffffff3e7ff 0xfffffffffff9f3ff

def z540 : W := mkw 0x2800040434004822 0x140002021a002411 0x00002c007000d800 0x0000160038006c00

def z541 : W := mkw 0x100450308800018c 0x08022818440000c6 0xed8ed2718c0007fe 0xf6c76938c60003ff

def z542 : W := mkw 0x01100369c8000000 0x008801b4e4000000 0x0080027180000000 0x00400138c0000000

def z543 : W := mkw 0xb07ffbb1dbfbf7bd 0xd83ffdd8edfdfbde 0xfffffff1ffffffff 0xfffffff8ffffffff

def z544 : W := mkw 0x2824fc043443f823 0x94127e021a21fc11 0x4300fc007c03f826 0x21807e003e01fc13

def z545 : W := mkw 0x2020a0015042c030 0x10105000a8216018 0x5f70e001f3e3c039 0x2fb87000f9f1e01c

def z546 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x228e10700e1327ff 0x91470838070993ff

def z547 : W := mkw 0x2020a0015042c030 0x10105000a8216018 0x000020007000c000 0x0000100038006000

def z548 : W := mkw 0x2820a4057442c832 0x14105202ba216419 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z549 : W := mkw 0x497dff6fec040842 0x24beffb7f6020421 0xfdfffffffc1c38c6 0xfefffffffe0e1c63

def z550 : W := mkw 0x0134ff6dec000000 0x009a7fb6f6000000 0xc180fffffc000000 0xe0c07ffffe000000

def z551 : W := mkw 0x0006500002112001 0x0003280001089000 0x200e100000102000 0x1007080000081000

def z552 : W := mkw 0x780454a6bd056c6f 0x3c022a535e82b637 0xf701fd8ffd1ffcff 0xfb80fec7fe8ffe7f

def z553 : W := mkw 0xd0db03fa8bbc07cc 0x686d81fd45de03e6 0xbdff03ff8ffc07ff 0xdeff81ffc7fe03ff

def z554 : W := mkw 0x40820012029c01c0 0x20410009014e00e0 0x00000000001c00c0 0x00000000000e0060

def z555 : W := mkw 0x100450208801200d 0x0802281044009006 0x000010000c002006 0x0000080006001003

def z556 : W := mkw 0x807ffb0142fbb211 0xc03ffd80a17dd908 0x087ec20182e30318 0x043f6100c171818c

def z557 : W := mkw 0x80fffb5802fbb381 0xc07ffdac017dd9c0 0x08fec27002e30300 0x047f613801718180

def z558 : W := mkw 0xc0f9abca01ee9640 0xe07cd5e500f74b20 0x10712d8e01ecd800 0x083896c700f66c00

def z559 : W := mkw 0x0004502088000000 0x0002281044000000 0x088ec27180000000 0x04476138c0000000

def z560 : W := mkw 0x0000040424000000 0x0000020212000000 0x20011c0e0c000000 0x90008e0706000000

def z561 : W := mkw 0x6802008213dffc63 0xb401004109effe31 0x0200000003fffce7 0x0100000001fffe73

def z562 : W := mkw 0x1116577dee11218d 0x088b2bbef70890c6 0xef8ed3fffe1327ff 0xf7c769ffff0993ff

def z563 : W := mkw 0x200000001042c030 0x1000000008216018 0x020000000003c038 0x010000000001e01c

def z564 : W := mkw 0x8010030000200200 0x4008018000100100 0x0870020002e00300 0x0438010001700180

def z565 : W := mkw 0x6820a4877546cc72 0x34105243baa36639 0xf701fd8ffd1ffcff 0xfb80fec7fe8ffe7f

def z566 : W := mkw 0xc1fbafdf67bc07c0 0x60fdd7efb3de03e0 0xbcff2ffe73fc07c1 0xde7f97ff39fe03e0

def z567 : W := mkw 0xe8d907ce35ac4e62 0x746c83e71ad62731 0xf7713d8e7dfcfce7 0xfbb89ec73efe7e73

def z568 : W := mkw 0xa079ab8151ead630 0xd03cd5c0a8f56b18 0x10712d8071ecd800 0x083896c038f66c00

def z569 : W := mkw 0x6800048635044c62 0x340002431a822631 0xa1011d8e7c1c3ce6 0xd0808ec73e0e1e73

def z570 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xe78e10700c1024e7 0xf3c7083806081273

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000011cf801 0x01000000008e7c00

def z572 : W := mkw 0x2020a0801142c420 0x1010504008a16210 0xdf70e18073e3c421 0x6fb870c039f1e210

def z573 : W := mkw 0xa010038151204630 0x500801c0a8902318 0x9d700381f3e00739 0x4eb801c0f9f0039c

def z574 : W := mkw 0xc0cb009203bc07c0 0x6065804901de03e0 0x3c7f000003fc07c1 0x1e3f800001fe03e0

def z575 : W := mkw 0x680454a6bd044c62 0x34022a535e822631 0xff8ffffffd1cfce7 0xffc7fffffe8e7e73

def z576 : W := mkw 0x016ffc6caedbb001 0x80b7fe36576dd800 0x7efffc7e0ffff801 0xbf7ffe3f07fffc00

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x4300c00180030038 0x21806000c001801c

def z578 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0xddfee3f1f0000000 0x6eff71f8f8000000

def z579 : W := mkw 0x417dffefed040440 0x20befff7f6820220 0xfdfffffffd1c04c1 0xfefffffffe8e0260

def z580 : W := mkw 0x805b038003b80600 0x402d81c001dc0300 0xbc7f038003fc0701 0x5e3f81c001fe0380

def z581 : W := mkw 0x8000000000628210 0x4000000000314108 0x0000000002e30318 0x000000000171818c

def z582 : W := mkw 0x006df80000428000 0x0036fc0000214000 0x7e7ffc0003e3c001 0x3f3ffe0001f1e000

def z583 : W := mkw 0x1024f8208843b00d 0x88127c104421d806 0x4300fc018c03f83e 0x21807e00c601fc1f

def z584 : W := mkw 0x38045424bc01682f 0x1c022a125e00b417 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z585 : W := mkw 0xc1fdffefedac0640 0x60fefff7f6d60320 0xfdfffffffdec0000 0xfefffffffef60000

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd00c20180000000 0x66806100c0000000

def z587 : W := mkw 0x2030a38151004420 0x101851c0a8802210 0xdf70e381f100c421 0x6fb871c0f8806210

def z588 : W := mkw 0x38065434be1169af 0x1c032a1a5f08b4d7 0xef8efe71fe13ffff 0xf7c77f38ff09ffff

def z589 : W := mkw 0x104f58308a99318d 0x8827ac18454c98c6 0xef8fde718e1f3fff 0xf7c7ef38c70f9fff

def z590 : W := mkw 0xe8db07de37bc4fe2 0x746d83ef1bde27f1 0xbcff2ffe73fcdfc1 0xde7f97ff39fe6fe0

def z591 : W := mkw 0x3026f031da53e1bd 0x18137818ed29f0de 0xef8ef271fe13e7ff 0xf7c77938ff09f3ff

def z592 : W := mkw 0x0000040424000000 0x0000020212000000 0xf7013d8e7c1024e7 0xfb809ec73e081273

def z593 : W := mkw 0xc0df53da03bd27c1 0x606fa9ed01de93e0 0xfeffd3fe03ff27c1 0xff7fe9ff01ff93e0

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xd500218070000000 0x6a8010c038000000

def z595 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x5171fd8ffc000000 0x28b8fec7fe000000

def z596 : W := mkw 0x286ffc0436dbf823 0x9437fe021b6dfc11 0x7f7ffc007ffff827 0x3fbffe003ffffc13

def z597 : W := mkw 0x017ffb69cadbb001 0x80bffdb4e56dd800 0x08fec27182e30000 0x047f6138c1718000

def z598 : W := mkw 0x100650100211218d 0x08032808010890c6 0x6e0ed000021327ff 0x37076800010993ff

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100020180000738 0x40800100c000039c

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x560020000100c001 0x2b00100000806000

def z601 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x000e000000000000 0x0007000000000000

def z602 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x1270218073e3c739 0x093810c039f1e39c

def z603 : W := mkw 0x0020a00140000000 0x00105000a0000000 0x4100e001f0000000 0x20807000f8000000

def z604 : W := mkw 0xc0fba3da03fe87c0 0x607dd1ed01ff43e0 0xfeffe3fe03ffc7c1 0xff7ff1ff01ffe3e0

def z605 : W := mkw 0x686ffc8637dffc63 0xb437fe431beffe31 0x7e7ffd8e73fff801 0x3f3ffec739fffc00

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800c20182030318 0x04006100c101818c

def z607 : W := mkw 0x8010038001200600 0x400801c000900300 0x1070018001e00000 0x083800c000f00000

def z608 : W := mkw 0xe0f9a3cb51eec670 0x707cd1e5a8f76338 0xdf71e38ff3efc739 0x6fb8f1c7f9f7e39c

def z609 : W := mkw 0x40eff85a02dfb1c1 0xa077fc2d016fd8e0 0x7efffc7e03fff8c1 0xbf7ffe3f01fffc60

def z610 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdd70e381f1e0c000 0x6eb871c0f8f06000

def z611 : W := mkw 0x100450208801200d 0x0802281044009006 0xe700d0018c1324ff 0xf3806800c609927f

def z612 : W := mkw 0x817dffeded200600 0x40befff6f6900300 0xfdffffffffe00701 0xfefffffffff00380

def z613 : W := mkw 0x0004500000000000 0x0002280000000000 0x6c0ed00000000000 0x3607680000000000

def z614 : W := mkw 0x8030a38001628600 0x401851c000b14300 0xde70e38003e3c701 0x6f3871c001f1e380

def z615 : W := mkw 0x100450208801200d 0x0802281044009006 0xef8ed2718c03203e 0xf7c76938c601901f

def z616 : W := mkw 0x6800048635044c62 0x340002431a822631 0xd7012d8e710cdc21 0x6b8096c738866e10

def z617 : W := mkw 0xb032a3915373e7bd 0x581951c8a9b9f3de 0xdf70e381f3f3e7ff 0x6fb871c0f9f9f3ff

def z618 : W := mkw 0x014d586888000000 0x00a6ac3444000000 0x008e007000000000 0x0047003800000000

def z619 : W := mkw 0x0022a00002dbb001 0x80115000016dd800 0x5e70e00003fff801 0x2f38700001fffc00

def z620 : W := mkw 0x2800040434004822 0x140002021a002411 0xe7003c007c10fce7 0xf3801e003e087e73

def z621 : W := mkw 0x4000008201040440 0x2000004100820220 0xf701118e0d1c24e7 0xfb8088c7068e1273

def z622 : W := mkw 0xc0fffbda03ffb7c1 0xe07ffded01ffdbe0 0xbcffc3fe03ff07c1 0xde7fe1ff01ff83e0

def z623 : W := mkw 0x2800048435004c22 0x140002421a802611 0xd7003d807d00fc27 0x6b801ec03e807e13

def z624 : W := mkw 0xa130a7edfd62c630 0x509853f6feb16318 0xdff0e3ffffe3c739 0xeff871fffff1e39c

def z625 : W := mkw 0x6869ac8635cedc62 0xb434d6431ae76e31 0xf7713d8e7dfcfce7 0xfbb89ec73efe7e73

def z626 : W := mkw 0x117dff7dec00018c 0x08beffbef60000c6 0xfdfffffffc0007fe 0xfefffffffe0003ff

def z627 : W := mkw 0xc1fdffffed2407c0 0x60fefffff69203e0 0xfdfffffffc0007c0 0xfefffffffe0003e0

def z628 : W := mkw 0x6800008211044c62 0x3400004108822631 0xd7002180711cfce7 0x6b8010c0388e7e73

def z629 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x4300d0018e1327ff 0x21806800c70993ff

def z630 : W := mkw 0xb01003b1d92047bc 0x580801d8ec9023de 0x818003f1fc0007fe 0xc0c001f8fe0003ff

def z631 : W := mkw 0x691007effd044c62 0x348803f7fe822631 0xf7813ffffd1cfce7 0xfbc09ffffe8e7e73

def z632 : W := mkw 0x0006500002112001 0x0003280001089000 0x080ec00002030000 0x0407600001018000

def z633 : W := mkw 0xe9ffffffffbc4fe2 0x74ffffffffde27f1 0xfffffffffffcffe7 0xfffffffffffe7ff3

def z634 : W := mkw 0x114f5c7cae11218d 0x08a7ae3e570890c6 0xef8fde7f8e1327ff 0xf7c7ef3fc70993ff

def z635 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x4b8ed2718e03233e 0x25c76938c701919f

def z636 : W := mkw 0xc0df53fa8bbc07c0 0x606fa9fd45de03e0 0xfdffd3ff8ffc07c1 0xfeffe9ffc7fe03e0

def z637 : W := mkw 0xc082009203bc07c0 0x6041004901de03e0 0xac8e027003fc07c1 0xd647013801fe03e0

def z638 : W := mkw 0x006df80000000000 0x0036fc0000000000 0x7e7ffc00011cf801 0x3f3ffe00008e7c00

def z639 : W := mkw 0xc0db03da03ffb7c1 0xe06d81ed01ffdbe0 0xbeff03fe03ffffc1 0xdf7f81ff01ffffe0

def z640 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xeffed2718ef327ff 0xf7ff6938c77993ff

def z641 : W := mkw 0x0124fc25ec000000 0x00927e12f6000000 0xed8efe71fc000000 0xf6c77f38fe000000

def z642 : W := mkw 0x0002001002100180 0x00010008010800c0 0x00000000021007c1 0x00000000010803e0

def z643 : W := mkw 0xa134ffa5fd62c630 0x509a7fd2feb16318 0xdf70ff81ffe3c739 0x6fb87fc0fff1e39c

def z644 : W := mkw 0x8082001002b80380 0x40410008015c01c0 0x0000000002e00300 0x0000000001700180

def z645 : W := mkw 0xe882049637bc4fe2 0x7441024b1bde27f1 0xf7013d8e7ffcffe7 0xfb809ec73ffe7ff3

def z646 : W := mkw 0xe810078635244e62 0x740803c31a922731 0xff713f8e7ffcffe7 0xffb89fc73ffe7ff3

def z647 : W := mkw 0x41ffff7fee9c01c0 0x20ffffbff74e00e0 0xfdfffffffc1c00c0 0xfefffffffe0e0060

def z648 : W := mkw 0x6800048635044c62 0x340002431a822631 0xd700218e7d00c4e7 0xeb8010c73e806273

def z649 : W := mkw 0x0049000000880000 0x0024800000440000 0x1071000001ec0000 0x0838800000f60000

def z650 : W := mkw 0x006ba00002da8000 0x0035d000016d4000 0x7e7fe00003ffc001 0x3f3ff00001ffe000

def z651 : W := mkw 0x686dfc8635044c62 0x3436fe431a822631 0xff7ffd8e7d1cfce7 0xffbffec73e8e7e73

def z652 : W := mkw 0x697dffeffd044c62 0x34befff7fe822631 0xfdfffffffd0cd800 0xfefffffffe866c00

def z653 : W := mkw 0x486ffc0626dfb843 0xa437fe03136fdc21 0x7e7ffc0e0ffff8c7 0xbf3ffe0707fffc63

def z654 : W := mkw 0xa036f3815373e631 0x501b79c0a9b9f318 0xff7ef381f3f3e739 0x7fbf79c0f9f9f39c

def z655 : W := mkw 0x2000000150004030 0x10000000a8002018 0x01000001f0000038 0x00800000f800001c

def z656 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x0a8ec271821327ff 0x05476138c10993ff

def z657 : W := mkw 0xc0db03ca03bc0640 0x606d81e501de0320 0x3c7f018e03fc0001 0x1e3f80c701fe0000

def z658 : W := mkw 0x017fff6dee993001 0x80bfffb6f74c9800 0xfdfffffffc1c3800 0xfefffffffe0e1c00

def z659 : W := mkw 0x0000001000000180 0x00000008000000c0 0x80800270000007c0 0xc0400138000003e0

def z660 : W := mkw 0x6869ac8635cedc62 0xb434d6431ae76e31 0x10712d8e71ecd800 0x083896c738f66c00

def z661 : W := mkw 0x0006501002112181 0x00032808010890c0 0xee8ed270021327c1 0xf7476938010993e0

def z662 : W := mkw 0xe0fba3db53fec7f0 0x707dd1eda9ff63f8 0xbcff23fe73fcc7c1 0xde7f91ff39fe63e0

def z663 : W := mkw 0x005b035802100180 0x002d81ac010800c0 0xbcff03fe021007c1 0xde7f81ff010803e0

def z664 : W := mkw 0xc09003da012407c0 0x604801ed009203e0 0xb48103fe011c07c1 0xda4081ff008e03e0

def z665 : W := mkw 0xd0fffbfa8bffb7cd 0xe87ffdfd45ffdbe6 0xffffffff8fffffff 0xffffffffc7ffffff

def z666 : W := mkw 0x0002000002dbb001 0x80010000016dd800 0x0000000002e30000 0x0000000001718000

def z667 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x6e7ed00002f32001 0x373f680001799000

def z668 : W := mkw 0x006ffc0426dbb001 0x8037fe02136dd800 0xff7ffd8e7ffff801 0xffbffec73ffffc00

def z669 : W := mkw 0x017fff6deedbb001 0x80bfffb6f76dd800 0xfdfffffffee30000 0xfeffffffff718000

def z670 : W := mkw 0xa17dfbe9d962c630 0x50befdf4ecb16318 0xdffee3f1f3e3c739 0x6fff71f8f9f1e39c

def z671 : W := mkw 0x004d580000000000 0x0026ac0000000000 0x200f1c0000000000 0x10078e0000000000

def z672 : W := mkw 0x100200100211218d 0x08010008010890c6 0x00000000001020c6 0x0000000000081063

def z673 : W := mkw 0x8010038001200600 0x400801c000900300 0xdf70c38183e30739 0x6fb861c0c1f1839c

def z674 : W := mkw 0xe0b2a39353fec7f0 0x705951c9a9ff63f8 0xdf70e381f3ffc7f9 0x6fb871c0f9ffe3fc

def z675 : W := mkw 0x0002001002100180 0x00010008010800c0 0x208e0070001000c0 0x9047003800080060

def z676 : W := mkw 0x0000008001000400 0x0000004000800200 0x9400018001000401 0x4a0000c000800200

def z677 : W := mkw 0x2000008011004420 0x1000004008802210 0x8100018070000420 0x408000c038000210

def z678 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0x9c71038e03ec0701 0x4e3881c701f60380

def z679 : W := mkw 0x40cb00da039c05c0 0x2065806d01ce02e0 0xb48f01fe011c04c1 0xda4780ff008e0260

def z680 : W := mkw 0x016dfc25ec000000 0x00b6fe12f6000000 0x7d7ffc01fc000000 0x3ebffe00fe000000

def z681 : W := mkw 0x780004b6bd044dee 0x3c00025b5e8226f7 0x818003fffc0007fe 0xc0c001fffe0003ff

def z682 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x3c7fc00003ff0001 0x1e3fe00001ff8000

def z683 : W := mkw 0x4000008201040440 0x2000004100820220 0x1001018e010c0000 0x080080c700860000

def z684 : W := mkw 0x40020092031405c0 0x20010049018a02e0 0xbc8f03fe031c07c1 0xde4781ff018e03e0

def z685 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x6e0fdc00021f3801 0x3707ee00010f9c00

def z686 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x287fdc0002ff3800 0x143fee00017f9c00

def z687 : W := mkw 0xc09203da03bc07c0 0x604901ed01de03e0 0x808003fe03fc07c1 0xc04001ff01fe03e0

def z688 : W := mkw 0x017dff4d64000000 0x00beffa6b2000000 0x7c7ffd8e70000000 0x3e3ffec738000000

def z689 : W := mkw 0x6979afcf75044c62 0x34bcd7e7ba822631 0xf7713d8e7d1cfce7 0xfbb89ec73e8e7e73

def z690 : W := mkw 0x017fff7dee100180 0x00bfffbef70800c0 0xfdfffffffe1007c1 0xfeffffffff0803e0

def z691 : W := mkw 0x004f500002992001 0x0027a800014c9000 0x7e7fd00003ff2001 0x3f3fe80001ff9000

def z692 : W := mkw 0xd082009203bd27cd 0x6841004901de93e6 0x0200000003ff27ff 0x0100000001ff93ff

def z693 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0xf7013f8ffd1cffff 0xfb809fc7fe8e7fff

def z694 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x5370e181f1e3c038 0x29b870c0f8f1e01c

def z695 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0xacfe027002f007c1 0xd67f0138017803e0

def z696 : W := mkw 0x1026f0308a53a18d 0x081378184529d0c6 0xfffef2718ff3e7ff 0xffff7938c7f9f3ff

def z697 : W := mkw 0xa00000801162c630 0x5000004008b16318 0x0000000001e0c000 0x0000000000f06000

def z698 : W := mkw 0xe830a7877566ce72 0x741853c3bab36739 0x10712d8e71ecd800 0x083896c738f66c00

def z699 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x3c7f1c0003fc3801 0x1e3f8e0001fe1c00

def z700 : W := mkw 0x0134ff25ec000000 0x009a7f92f6000000 0xdd70ff81fc000000 0x6eb87fc0fe000000

def z701 : W := mkw 0x0002000002993001 0x80010000014c9800 0x00000000001c3800 0x00000000000e1c00

def z702 : W := mkw 0x100650208a11200d 0x0803281045089006 0x6f0ed0018e13203f 0x37876800c709901f

def z703 : W := mkw 0x6800048635044c62 0x340002431a822631 0xc3003d8e7c00fce6 0xe1801ec73e007e73

def z704 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x91702381f1e0c738 0x48b811c0f8f0639c

def z705 : W := mkw 0x4800040624040842 0x2400020312020421 0x00010c0e000c1800 0x0000860700060c00

def z706 : W := mkw 0xc0fba3db43fe87d0 0x607dd1eda1ff43e8 0xbcffc3ff83ff07d9 0xde7fe1ffc1ff83ec

def z707 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0xbcff027e03fc07c1 0xde7f813f01fe03e0

def z708 : W := mkw 0xa010038151204630 0x500801c0a8902318 0xdf70c381f3e30739 0x6fb861c0f9f1839c

def z709 : W := mkw 0x780654b6bf156def 0x3c032a5b5f8ab6f7 0x188feffff30fdb18 0x0c47f7fff987ed8c

def z710 : W := mkw 0xe89007de35244fe2 0x744803ef1a9227f1 0x808003fe700007c0 0xc04001ff380003e0

def z711 : W := mkw 0x0000040424000000 0x0000020212000000 0xf7013d8e7d1cfce7 0xfb809ec73e8e7e73

def z712 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x98ff03fe03ec07c0 0xcc7f81ff01f603e0

def z713 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x5271fc0003fff801 0x2938fe0001fffc00

def z714 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xff70f381ffffffff 0xffb879c0ffffffff

def z715 : W := mkw 0xc1a6fcb7efbc07c0 0x60d37e5bf7de03e0 0x4100fc01fffc07c1 0x20807e00fffe03e0

def z716 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff013f8e7f1cffe7 0xff809fc73f8e7ff3

def z717 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbeff03fe03ff07f9 0xdf7f81ff01ff83fc

def z718 : W := mkw 0x015d5f6cac000000 0x00aeafb656000000 0xfdff3ffe7c000000 0xfeff9fff3e000000

def z719 : W := mkw 0x017dff6dec429000 0x80beffb6f6214800 0xfdfffffffc00d800 0xfefffffffe006c00

def z720 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0xf58f3ffffc000000 0xfac79ffffe000000

def z721 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x1870e381f2e30318 0x0c3871c0f971818c

def z722 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfffffe718ffffb19 0xffffff38c7fffd8c

def z723 : W := mkw 0xc830a70764668a52 0x64185383b2334529 0x2871de0f8eff3bde 0x9438ef07c77f9def

def z724 : W := mkw 0x004b000002dbb001 0x80258000016dd800 0x7e7f3c0003fff801 0x3f3f9e0001fffc00

def z725 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x7671fc0001fff801 0x3b38fe0000fffc00

def z726 : W := mkw 0x0030a30140428000 0x00185180a0214000 0xdf70e381f3e3c739 0x6fb871c0f9f1e39c

def z727 : W := mkw 0x0124fc25ec429000 0x80927e12f6214800 0x4100fc01fc00d800 0x20807e00fe006c00

def z728 : W := mkw 0x007dfb4940000000 0x003efda4a0000000 0xfdfffffff0000000 0xfefffffff8000000

def z729 : W := mkw 0xa020a0815162c630 0x50105040a8b16318 0x5f70e001f3e3c739 0x2fb87000f9f1e39c

def z730 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfeffc3fe03ff07c1 0xff7fe1ff01ff83e0

def z731 : W := mkw 0x7802009213dffdef 0xbc01004909effef7 0x0200000003ffffff 0x0100000001ffffff

def z732 : W := mkw 0xc0db0bda03bc17c0 0xe06d85ed01de0be0 0xbcff0ffe03fc1fc1 0xde7f87ff01fe0fe0

def z733 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xdf70e38ff3e3c7f9 0xefb871c7f9f1e3fc

def z734 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff8f3ffe7d1cfce7 0xffc79fff3e8e7e73

def z735 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0xff7ffc000fffffff 0xffbffe0007ffffff

def z736 : W := mkw 0x817dff6dec628210 0x40beffb6f6314108 0xfffffffffee30739 0xffffffffff71839c

def z737 : W := mkw 0xf80200921377efff 0x7c01004909bbf7ff 0x0200000003ffffff 0x0100000001ffffff

def z738 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0x18ff2ffe70000000 0x0c7f97ff38000000

def z739 : W := mkw 0x60eba05b52dec1f0 0x3075d02da96f60f8 0x638fe07ff01fc0f8 0xb1c7f03ff80fe07c

def z740 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x10713c0001ecf800 0x08389e0000f67c00

def z741 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xa98ed2718e1327fe 0xd4c76938c70993ff

def z742 : W := mkw 0x017dff6dec428010 0x00beffb6f6214008 0xfdfffffffc030018 0xfefffffffe01800c

def z743 : W := mkw 0xa8db075c36b84ba2 0x546d83ae1b5c25d1 0x4bfe3e707ee0fb26 0x25ff1f383f707d93

def z744 : W := mkw 0x3824fc24bc43f82f 0x9c127e125e21fc17 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z745 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70f381ffe3e73f 0x6fb879c0fff1f39f

def z746 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x88fe03fe03fc07c1 0xc47f01ff01fe03e0

def z747 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x28ff027e03fc07c1 0x947f813f01fe03e0

def z748 : W := mkw 0x0004502088000000 0x0002281044000000 0xef8ed2718e1327ff 0xf7c76938c70993ff

def z749 : W := mkw 0xb036f3b1db73e7bd 0x581b79d8edb9f3de 0x30fe31f07df0e0c6 0x987f18f83ef87063

def z750 : W := mkw 0x0110076dec000000 0x008803b6f6000000 0xad8e03fffc000000 0xd6c701fffe000000

def z751 : W := mkw 0x0114576dec000000 0x008a2bb6f6000000 0xfd8ffffffc000000 0xfec7fffffe000000

def z752 : W := mkw 0x0059074c24000000 0x002c83a612000000 0xbdff03fe7c000000 0xdeff81ff3e000000

def z753 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0xbdff1ffffc000000 0xdeff8ffffe000000

def z754 : W := mkw 0xc0db03da03bd37c1 0xe06d81ed01de9be0 0xbcff03fe03fc3fc1 0xde7f81ff01fe1fe0

def z755 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xdf71e38ff3efc739 0x6fb8f1c7f9f7e39c

def z756 : W := mkw 0xd0dd53ea89ad264d 0x686ea9f544d69326 0x5371d18f8def203e 0x29b8e8c7c6f7901f

def z757 : W := mkw 0x117baf5d6611218d 0x08bdd7aeb30890c6 0x12712d8e721327ff 0x093896c7390993ff

def z758 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffc700fffffff 0xbf7ffe3807ffffff

def z759 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x52713c0001ecf800 0x29389e0000f67c00

def z760 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xacfe03fe02f007c1 0xd67f01ff017803e0

def z761 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8fd3ff8e1327ff 0xffc7e9ffc70993ff

def z762 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0xef00d38ffe1327ff 0xf78069c7ff0993ff

def z763 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0xfdff3ffe7c000000 0xfeff9fff3e000000

def z764 : W := mkw 0x017dfb69c8000000 0x00befdb4e4000000 0xfdffe3fff0000000 0xfefff1fff8000000

def z765 : W := mkw 0xd0db03da03bd27cd 0x686d81ed01de93e6 0xffff13fe0fff27ff 0xffff89ff07ff93ff

def z766 : W := mkw 0x1069a83088ca918c 0x8834d418446548c6 0x91f12e718decdffe 0xc8f89738c6f66fff

def z767 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0x0000018e70000000 0x000000c738000000

def z768 : W := mkw 0x0114576dec000000 0x008a2bb6f6000000 0x898ec3fffc000000 0xc4c761fffe000000

def z769 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbdff03ff83fc07f9 0xdeff81ffc1fe03fc

def z770 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff70e381f3f3c7f9 0xffb871c0f9f9e3fc

def z771 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0x20ff007e00fc00c0 0x907f803f007e0060

def z772 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff70f381f3f3e739 0x7fb879c0f9f9f39c

def z773 : W := mkw 0x0159076dec000000 0x00ac83b6f6000000 0xfdff3ffffc000000 0xfeff9ffffe000000

def z774 : W := mkw 0x8030a30140628210 0x40185180a0314108 0xdf70e381f2e30739 0x6fb871c0f971839c

def z775 : W := mkw 0x80d9034800a80200 0x406c81a400540100 0xbcff03fe00e00000 0xde7f81ff00700000

def z776 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x7e71fc0003fff801 0x3f38fe0001fffc00

def z777 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0x30ff2dfe70000000 0x987f96ff38000000

def z778 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xffff3ffe0ffcffe7 0xffff9fff07fe7ff3

def z779 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xbdff03fe73fc07e1 0xdeff81ff39fe03f0

def z780 : W := mkw 0x404b0092039c05c0 0x2025804901ce02e0 0xbcff03fe03fc07c1 0xde7f81ff01fe03e0

def z781 : W := mkw 0x0059034800880000 0x002c81a400440000 0xbcff03fe01ec0000 0xde7f81ff00f60000

def z782 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x08fe03fe02e00300 0x047f01ff01700180

def z783 : W := mkw 0xc0db03db43bc07d0 0x606d81eda1de03e8 0xbcff03ff83fc07d9 0xde7f81ffc1fe03ec

def z784 : W := mkw 0x80db03d803b80780 0x406d81ec01dc03c0 0xbcff03fe03e00701 0xde7f81ff01f00380

def z785 : W := mkw 0x117dff6dec01200d 0x08beffb6f6009006 0xfffffffffc1324ff 0xfffffffffe09927f

def z786 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x18ffee7183efdb18 0x0c7ff738c1f7ed8c

def z787 : W := mkw 0x0134ff6dec000000 0x009a7fb6f6000000 0xed8efffffc000000 0xf6c77ffffe000000

def z788 : W := mkw 0xa14d5cecbd62c630 0x50a6ae765eb16318 0x228f1c7e0fe3c739 0x91478e3f07f1e39c

def z789 : W := mkw 0x017dff6decca9000 0x80beffb6f6654800 0xffffffffffefd801 0xfffffffffff7ec00

def z790 : W := mkw 0xe0db03db53bc47f0 0x706d81eda9de23f8 0xbcff03fe73fc07c1 0xde7f81ff39fe03e0

def z791 : W := mkw 0x817dff6dec628210 0x40beffb6f6314108 0xfdfffffffce00000 0xfefffffffe700000

def z792 : W := mkw 0x2924fc25fc42c832 0x14927e12fe216419 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z793 : W := mkw 0x0059034800000000 0x002c81a400000000 0xfdff23fe70000000 0xfeff91ff38000000

def z794 : W := mkw 0x2020a0015042c030 0x10105000a8216018 0xdf70e201f3e3c739 0x6fb87100f9f1e39c

def z795 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff71ff81f3e3c739 0x7fb8ffc0f9f1e39c

def z796 : W := mkw 0x100650308a99218d 0x08032818454c90c6 0xef8ed2718fff27ff 0xf7c76938c7ff93ff

def z797 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x30ff01fe03fc07c1 0x987f80ff01fe03e0

def z798 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xbcff03fe03fcdfc1 0xde7f81ff01fe6fe0

def z799 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0x88fe03fe02e00300 0xc47f01ff01700180

def z800 : W := mkw 0x0124fc25ec000000 0x00927e12f6000000 0xfd8ffffffc000000 0xfec7fffffe000000

def z801 : W := mkw 0xe89007ce35244e62 0x744803e71a922731 0x8100018e7c0004e6 0xc08000c73e000273

def z802 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x1871ec0003efd800 0x0c38f60001f7ec00

def z803 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xbcff3ffe7c000000 0xde7f9fff3e000000

def z804 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xcf70c381f2e30739 0x67b861c0f971839c

def z805 : W := mkw 0x697dfbebd9044c62 0x34befdf5ec822631 0x0afec271811cfce7 0x057f6138c08e7e73

def z806 : W := mkw 0x004f580002dbb001 0x8027ac00016dd800 0x3e7f1c0003fff801 0x1f3f8e0001fffc00

def z807 : W := mkw 0xa030a3c95162c630 0x501851e4a8b16318 0xdff0e3fff3e3c739 0xeff871fff9f1e39c

def z808 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x9d70c381f3e30739 0x4eb861c0f9f1839c

def z809 : W := mkw 0x017dff6dec880000 0x00beffb6f6440000 0xfdfffffffdec0000 0xfefffffffef60000

def z810 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x0870c381f2e30318 0x043861c0f971818c

def z811 : W := mkw 0xe89207de37344fe2 0x744903ef1b9a27f1 0xef8e13fe7e1027e7 0xf7c709ff3f0813f3

def z812 : W := mkw 0x8030a38141200600 0x401851c0a0900300 0xdf70e381f3e30739 0x6fb871c0f9f1839c

def z813 : W := mkw 0x114f5c7cae99318d 0x88a7ae3e574c98c6 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z814 : W := mkw 0x6800048635044c62 0x340002431a822631 0x53013d8e7d1cfce7 0x29809ec73e8e7e73

def z815 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0xfefffe7003ffffff 0xff7fff3801ffffff

def z816 : W := mkw 0xe810078635244e62 0x740803c31a922731 0x8100038e7c0007e6 0xc08001c73e0003f3

def z817 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbeff03fe03fcffc1 0xdf7f81ff01fe7fe0

def z818 : W := mkw 0x686ffc8637dffc63 0xb437fe431beffe31 0x897ec18e7ee304e6 0xc4bf60c73f718273

def z819 : W := mkw 0x017dff6decca9000 0x80beffb6f6654800 0xfffffffffdfcf801 0xfffffffffefe7c00

def z820 : W := mkw 0xe99007fffd244fe2 0x74c803fffe9227f1 0x818003fffc0007e6 0xc0c001fffe0003f3

def z821 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xc9fefffffc000000 0xe4ff7ffffe000000

def z822 : W := mkw 0xc0b4fbda0167b7c1 0xe05a7ded00b3dbe0 0xc280fffe0003ffc0 0xe1407fff0001ffe0

def z823 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf7013d8e7f1fffff 0xfb809ec73f8fffff

def z824 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffd1cfce7 0xfffffffffe8e7e73

def z825 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xfe7ffd8e03fff801 0xff3ffec701fffc00

def z826 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x30713c0001fcf800 0x18389e0000fe7c00

def z827 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc000738 0xfefffffffe00039c

def z828 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x9cfe03fe03e007c1 0xce7f01ff01f003e0

def z829 : W := mkw 0x0024f8000043b001 0x80127c000021d800 0x7e71fc0003fff801 0x3f38fe0001fffc00

def z830 : W := mkw 0x0059034940000000 0x002c81a4a0000000 0xbdff03fff0000000 0xdeff81fff8000000

def z831 : W := mkw 0x0112076deedbb001 0x808903b6f76dd800 0x838003fffffff801 0xc1c001fffffffc00

def z832 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xff71ff81f3ffffff 0x7fb8ffc0f9ffffff

def z833 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xfdfffffffde0c000 0xfefffffffef06000

def z834 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff70f381ffe3c739 0xffb879c0fff1e39c

def z835 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbeff03fe03fc27e7 0xdf7f81ff01fe13f3

def z836 : W := mkw 0x8059034800200200 0x402c81a400100100 0xbcff03fe02e00300 0xde7f81ff01700180

def z837 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffe030001 0xffffffffff018000

def z838 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff01ff8ffd1cfce7 0xff80ffc7fe8e7e73

def z839 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0x7efffe7003fffb01 0x3f7fff3801fffd80

def z840 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xcb70e381f2e3c738 0x65b871c0f971e39c

def z841 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xffff13fe0ffcffe7 0xffff89ff07fe7ff3

def z842 : W := mkw 0x100650308a99318d 0x88032818454c98c6 0xef8ed2718e1f3fff 0xf7c76938c70f9fff

def z843 : W := mkw 0xe882009213ffffe3 0xf441004909fffff1 0x0200000003ffffe7 0x0100000001fffff3

def z844 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x5370e181f3e3c739 0x29b870c0f9f1e39c

def z845 : W := mkw 0x40db035a029c01c0 0x206d81ad014e00e0 0xbcff03fe03fc00c1 0xde7f81ff01fe0060

def z846 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdffffffffe00001 0xfefffffffff00000

def z847 : W := mkw 0xe882009213bc4fe2 0x7441004909de27f1 0x0000000003fcdfc1 0x0000000001fe6fe0

def z848 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70e381f3ffff39 0x6fb871c0f9ffff9c

def z849 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc000421 0xfffffffffe000210

def z850 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xddfee3fffc000000 0xeeff71fffe000000

def z851 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8fd2718f1f27ff 0xffc7e938c78f93ff

def z852 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xfffee3f1f3e3c739 0xffff71f8f9f1e39c

def z853 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x3e7f2c0003fff801 0x1f3f960001fffc00

def z854 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x9cff03fe03ec0701 0x4e7f81ff01f60380

def z855 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x3cff01fe03fc00c1 0x9e7f80ff01fe0060

def z856 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x10712c0001fcf800 0x0838960000fe7c00

def z857 : W := mkw 0x006ff8308adbb181 0x8037fc18456dd8c0 0xfffffe718fffffc1 0xffffff38c7ffffe0

def z858 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7e7ffc000ffff8c7 0xbf3ffe0007fffc63

def z859 : W := mkw 0x006dfc24ac000000 0x0036fe1256000000 0xfdfffffffc000000 0xfefffffffe000000

def z860 : W := mkw 0x584f5c36ae9d39cf 0xac27ae1b574e9ce7 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z861 : W := mkw 0x015d576dec000000 0x00aeabb6f6000000 0xfdffd3fffc000000 0xfeffe9fffe000000

def z862 : W := mkw 0xe882009213bc4fe2 0x7441004909de27f1 0x0000000003fc07e7 0x0000000001fe03f3

def z863 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x56712c0001ecd801 0x2b38960000f66c00

def z864 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc1c3800 0xfefffffffe0e1c00

def z865 : W := mkw 0xa05f5b8153b97631 0xd02fadc0a9dcbb18 0xa10f1f81f01c3f38 0x50878fc0f80e1f9c

def z866 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x08fec3fff0000000 0x047f61fff8000000

def z867 : W := mkw 0x100204142611218d 0x0801020a130890c6 0xf7013d8e7e1327ff 0xfb809ec73f0993ff

def z868 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x4b70e201f3e3c739 0x25b87100f9f1e39c

def z869 : W := mkw 0x104f50308a99218d 0x0827a818454c90c6 0xfffffe718fffffff 0xffffff38c7ffffff

def z870 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf71ef81f3efdf39 0x6fb8f7c0f9f7ef9c

def z871 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfcff3ffe03fc07c1 0xfe7f9fff01fe03e0

def z872 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x2a7fdc0003fff801 0x153fee0001fffc00

def z873 : W := mkw 0xe8f9a7cf75eece72 0x747cd3e7baf76739 0x10712d8e71ecd800 0x083896c738f66c00

def z874 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x76713c0003fff801 0x3b389e0001fffc00

def z875 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xb0ff03fe01fc07c0 0xd87f81ff00fe03e0

def z876 : W := mkw 0x017dff6decca9000 0x80beffb6f6654800 0xfdfffffffce00000 0xfefffffffe700000

def z877 : W := mkw 0x117dff6dec01200d 0x08beffb6f6009006 0xfffffffffe03273f 0xffffffffff01939f

def z878 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xa8ff03fe02fc07c0 0xd47f81ff017e03e0

def z879 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffc000ffff801 0xffbffe0007fffc00

def z880 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf5013d8e7d1cf8c6 0xfa809ec73e8e7c63

def z881 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc1020c6 0xfefffffffe081063

def z882 : W := mkw 0x68820092139c4de2 0x3441004909ce26f1 0x02000000011cfce7 0x01000000008e7e73

def z883 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xfdfffffffee30000 0xfeffffffff718000

def z884 : W := mkw 0x6800048635044c62 0x340002431a822631 0xe3013d8e7c1cfce6 0xf1809ec73e0e7e73

def z885 : W := mkw 0xc0d903da012407c0 0x606c81ed009203e0 0xbcff03fe03e007c1 0xde7f81ff01f003e0

def z886 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xcb8ed2718e0327fe 0xe5c76938c70193ff

def z887 : W := mkw 0xe800048635244e62 0x740002431a922731 0xf7013d8e7ffcffe7 0xfb809ec73ffe7ff3

def z888 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x1c712c0003ecd801 0x0e38960001f66c00

def z889 : W := mkw 0xe0b0a3cb5166c670 0x705851e5a8b36338 0xdf70e38ff3e3c739 0x6fb871c7f9f1e39c

def z890 : W := mkw 0x006ff80002da9000 0x8037fc00016d4800 0x7c7ffc0003fcd801 0x3e3ffe0001fe6c00

def z891 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7f7ffc000ffff827 0x3fbffe0007fffc13

def z892 : W := mkw 0x6800048635044c62 0x340002431a822631 0xb4013d8e7d1cfcc7 0xda009ec73e8e7e63

def z893 : W := mkw 0xf81657b7ff356fff 0x7c0b2bdbff9ab7ff 0xef8ed3fffe1327ff 0xf7c769ffff0993ff

def z894 : W := mkw 0x017dff6deccbb001 0x80beffb6f665d800 0xfffffffffdeff800 0xfffffffffef7fc00

def z895 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xedfed3fffc000000 0xf6ff69fffe000000

def z896 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xffffe3fff3ffc7f9 0xfffff1fff9ffe3fc

def z897 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xfe7ffe0003ffff01 0x7f3fff0001ffff80

def z898 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfffffc700ffffce7 0xfffffe3807fffe73

def z899 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x10712c0003efd800 0x0838960001f7ec00

def z900 : W := mkw 0x8030a38141628610 0x401851c0a0b14308 0xdd70e381f3e30719 0x6eb871c0f9f1838c

def z901 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7ffffe718ffffb3f 0x3fffff38c7fffd9f

def z902 : W := mkw 0xc0db03ca03bc0640 0x606d81e501de0320 0xbcff03fe03fc0001 0xde7f81ff01fe0000

def z903 : W := mkw 0x004b000002980000 0x00258000014c0000 0x3c7f2c0003fcd801 0x1e3f960001fe6c00

def z904 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0x7e7ffc000ffff807 0x3f3ffe0007fffc03

def z905 : W := mkw 0x6800048635044c62 0x340002431a822631 0x76013d8e7d1cf8c7 0xbb009ec73e8e7c63

def z906 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0xfffffe718ffff83f 0xffffff38c7fffc1f

def z907 : W := mkw 0x817dff6dec628210 0x40beffb6f6314108 0xffffffffffe3c319 0xfffffffffff1e18c

def z908 : W := mkw 0x817dff6dec200200 0x40beffb6f6100100 0xfdfffffffee00300 0xfeffffffff700180

def z909 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0x30ff007e01fc00c0 0x987f803f00fe0060

def z910 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x30ff3c700dfcf8c6 0x987f9e3806fe7c63

def z911 : W := mkw 0x004b001002980180 0x00258008014c00c0 0xffff3e700ffcffe7 0xffff9f3807fe7ff3

def z912 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfdff13fe0ffc07c1 0xfeff89ff07fe03e0

def z913 : W := mkw 0xa830a3815162ce32 0x541851c0a8b16719 0xdf70e381f3e3ff3f 0x6fb871c0f9f1ff9f

def z914 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x1a70e381f3e3c739 0x0d3871c0f9f1e39c

def z915 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7ffffc718ffff8ff 0xbffffe38c7fffc7f

def z916 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff03fe03ec0300 0xde7f81ff01f60180

def z917 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0x7e7ffc0003ffffc1 0x3f3ffe0001ffffe0

def z918 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x10712c0003fcd801 0x0838960001fe6c00

def z919 : W := mkw 0x017dff6dec43b001 0x80beffb6f621d800 0xffffffffffe3f801 0xfffffffffff1fc00

def z920 : W := mkw 0x0179af4d64000000 0x00bcd7a6b2000000 0xfdffeffff0000000 0xfefff7fff8000000

def z921 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xbcff23fe73fcc7c1 0xde7f91ff39fe63e0

def z922 : W := mkw 0x117dff6dec43b00d 0x88beffb6f621d806 0xfffffffffc03f83e 0xfffffffffe01fc1f

def z923 : W := mkw 0x117dff6dec00000c 0x08beffb6f6000006 0xfdfffffffc00003e 0xfefffffffe00001f

def z924 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffd1c0001 0xfefffffffe8e0000

def z925 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xffff3ffe73fcffe1 0xffff9fff39fe7ff0

def z926 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xfefffe7003fff801 0xff7fff3801fffc00

def z927 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x34712c0001fcd801 0x1a38960000fe6c00

def z928 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xff71ff8ff3fffff9 0xffb8ffc7f9fffffc

def z929 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8ffe718e1327ff 0xffc7ff38c70993ff

def z930 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xad8ec2718e1307ff 0xd6c76138c70983ff

def z931 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x327f3c0003fff801 0x193f9e0001fffc00

def z932 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x4a7efc0003fff801 0x253f7e0001fffc00

def z933 : W := mkw 0xc05903ca01240640 0x602c81e500920320 0xbcff03fe03fc07c1 0xde7f81ff01fe03e0

def z934 : W := mkw 0xd0db03da03bc07cc 0x686d81ed01de03e6 0xbcff03fe03fc07ff 0xde7f81ff01fe03ff

def z935 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff03fe01fc00c0 0xde7f81ff00fe0060

def z936 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0xbcff03fe02fc03c0 0xde7f81ff017e01e0

def z937 : W := mkw 0xa010038011204620 0x500801c008902310 0xdf70e381f3e3c739 0x6fb871c0f9f1e39c

def z938 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7f7ffc0183fff839 0x3fbffe00c1fffc1c

def z939 : W := mkw 0x58cf547eae9d29cf 0x2c67aa3f574e94e7 0x208f1c7e0c1c38c6 0x90478e3f060e1c63

def z940 : W := mkw 0x005d576cac000000 0x002eabb656000000 0xfdfffffffc000000 0xfefffffffe000000

def z941 : W := mkw 0x005b035802980180 0x002d81ac014c00c0 0xbcff03fe03fc07c1 0xde7f81ff01fe03e0

def z942 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8ef3f1fe1327ff 0xffc779f8ff0993ff

def z943 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x5e7fec0003efd801 0x2f3ff60001f7ec00

def z944 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf701fd8ffd1ffcff 0xfb80fec7fe8ffe7f

def z945 : W := mkw 0x8030a30140628210 0x40185180a0314108 0xdf70e381f3e3c319 0x6fb871c0f9f1e18c

def z946 : W := mkw 0xe89007ce35244e62 0x744803e71a922731 0x0000018e70000000 0x000000c738000000

def z947 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70ff81f3e3ff39 0x6fb87fc0f9f1ff9c

def z948 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0xfffffe718fffff39 0xffffff38c7ffff9c

def z949 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7e7ffe0183fffb19 0x3f3fff00c1fffd8c

def z950 : W := mkw 0xe882009213fecff2 0x7441004909ff67f9 0x0200000003ffffff 0x0100000001ffffff

def z951 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc00f800 0xfffffffffe007c00

def z952 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0x7efffc7003fff8c1 0xbf7ffe3801fffc60

def z953 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0xfffffe718ffffce7 0xffffff38c7fffe73

def z954 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xbcffeffff0000000 0xde7ff7fff8000000

def z955 : W := mkw 0x007df369c8000000 0x003ef9b4e4000000 0xfdfff3fffc000000 0xfefff9fffe000000

def z956 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff03fe02e007c0 0xde7f81ff017003e0

def z957 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xfeff3ffe03fcffe7 0xff7f9fff01fe7ff3

def z958 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xdf70e381f3efdf39 0x6fb871c0f9f7ef9c

def z959 : W := mkw 0x006ba81002da9180 0x8035d408016d48c0 0xbcff2e7003fcdfc1 0xde7f973801fe6fe0

def z960 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff2ffe03fcdfc1 0xde7f97ff01fe6fe0

def z961 : W := mkw 0x817dff6dec200210 0x40beffb6f6100108 0xfdfffffffc000318 0xfefffffffe00018c

def z962 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xe38ed2718c1327fe 0xf1c76938c60993ff

def z963 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0x7e7ffc0003fff8c7 0x3f3ffe0001fffc63

def z964 : W := mkw 0x006df80000428000 0x0036fc0000214000 0x7e7ffc0003fff801 0x3f3ffe0001fffc00

def z965 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xffff03fe03fc07e1 0xffff81ff01fe03f0

def z966 : W := mkw 0x106ba81002dbb18d 0x8835d408016dd8c6 0x12712c0003ffffff 0x0938960001ffffff

def z967 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0x08fe027e02e003c0 0x847f013f017001e0

def z968 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xff71e38ff3ffffff 0xffb8f1c7f9ffffff

def z969 : W := mkw 0x0159076dec000000 0x00ac83b6f6000000 0xa18f03fffc000000 0xd0c781fffe000000

def z970 : W := mkw 0xc09203da033407c0 0x604901ed019a03e0 0xbcfe03fe03f007c1 0xde7f01ff01f803e0

def z971 : W := mkw 0x005b034802980000 0x002d81a4014c0000 0xbcff03fe02e00000 0xde7f81ff01700000

def z972 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffe0183fff801 0x7fbfff00c1fffc00

def z973 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x38fffffffc000000 0x9c7ffffffe000000

def z974 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffe030318 0xfeffffffff01818c

def z975 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0x308f3dfe7c000000 0x98479eff3e000000

def z976 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc030038 0xfffffffffe01801c

def z977 : W := mkw 0x0134f76dec000000 0x009a7bb6f6000000 0xfdfef3fffc000000 0xfeff79fffe000000

def z978 : W := mkw 0xe0db03db53bc47f0 0x706d81eda9de23f8 0xffffc3fff3ff07f9 0xffffe1fff9ff83fc

def z979 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x4b8ed2718e1327ff 0x25c76938c70993ff

def z980 : W := mkw 0x00045424ac000000 0x00022a1256000000 0xf58f3dfe7c000000 0xfac79eff3e000000

def z981 : W := mkw 0x0124fc25ec428010 0x00927e12f6214008 0x4100fc01fc030018 0x20807e00fe01800c

def z982 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcffc3ff83ff07d9 0xde7fe1ffc1ff83ec

def z983 : W := mkw 0x117dff6dec01200d 0x08beffb6f6009006 0xfdfffffffc002006 0xfefffffffe001003

def z984 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0x7e7ffc0003fffb19 0x3f3ffe0001fffd8c

def z985 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff713d8e7ffcfce7 0xffb89ec73ffe7e73

def z986 : W := mkw 0x0020a00000428000 0x0010500000214000 0x5e71ec0003efd801 0x2f38f60001f7ec00

def z987 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0x08ff027e02ec0300 0x047f813f01760180

def z988 : W := mkw 0x3124fc25fc43e03d 0x18927e12fe21f01e 0x4300fc01fc03e03e 0x21807e00fe01f01f

def z989 : W := mkw 0x106ff80002dbb00d 0x8837fc00016dd806 0x7e7ffc0003fff83f 0x3f3ffe0001fffc1f

def z990 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x5c71ec0001ecd800 0x2e38f60000f66c00

def z991 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x10ff2dfe70000000 0x087f96ff38000000

def z992 : W := mkw 0x017dff6dec43b001 0x80beffb6f621d800 0xfffffffffd1ff801 0xfffffffffe8ffc00

def z993 : W := mkw 0x1026f0308a53a18d 0x081378184529d0c6 0xfffffe718fffffff 0xffffff38c7ffffff

def z994 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7e7ffc0003ffff39 0x3f3ffe0001ffff9c

def z995 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x2a8ed2718e1327ff 0x95476938c70993ff

def z996 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xfe7ffc0003fffcc1 0xff3ffe0001fffe60

def z997 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x5a7ffc0003eff800 0x2d3ffe0001f7fc00

def z998 : W := mkw 0xf082009213ffe7fd 0x7841004909fff3fe 0x0200000003ffe7ff 0x0100000001fff3ff

def z999 : W := mkw 0x0002001002100180 0x00010008010800c0 0xef8ed2718e1327ff 0xf7c76938c70993ff

def z1000 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xbeff03fe03fcc7e1 0xdf7f81ff01fe63f0

def z1001 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x3c7fec0003ffd801 0x1e3ff60001ffec00

def z1002 : W := mkw 0x2020a0801142c420 0x1010504008a16210 0xdf70e381f3e3c739 0x6fb871c0f9f1e39c

def z1003 : W := mkw 0x00045424ac000000 0x00022a1256000000 0xed8ed3fffc000000 0xf6c769fffe000000

def z1004 : W := mkw 0x0059034800000000 0x002c81a400000000 0xbcff03fe03e00001 0xde7f81ff01f00000

def z1005 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7e7ffc0003fffce7 0x3f3ffe0001fffe73

def z1006 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x7e7ffc0001eff800 0x3f3ffe0000f7fc00

def z1007 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0xff7ffe018fffff3f 0x7fbfff00c7ffff9f

def z1008 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffd00c001 0xfffffffffe806000

def z1009 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdd70e381f2e30738 0x6eb871c0f971839c

def z1010 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff1ffe03fc3fc1 0xde7f8fff01fe1fe0

def z1011 : W := mkw 0x0020a00000428000 0x0010500000214000 0x76713c0001fcf801 0x3b389e0000fe7c00

def z1012 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xf5ff3dfe7c000000 0xfaff9eff3e000000

def z1013 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xff8ef2718f13e7ff 0xffc77938c789f3ff

def z1014 : W := mkw 0x805b03d803300780 0x402d81ec019803c0 0xbcff03fe03f007c1 0xde7f81ff01f803e0

def z1015 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7f7ffc018fffffff 0x3fbffe00c7ffffff

def z1016 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x7e7fec0003ffd801 0x3f3ff60001ffec00

def z1017 : W := mkw 0x117ffb79cadbb18d 0x88bffdbce56dd8c6 0x08fec27182e30318 0x047f6138c171818c

def z1018 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x18ff03fe03fc07c1 0x0c7f81ff01fe03e0

def z1019 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffc0003fffc21 0x7fbffe0001fffe10

def z1020 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0xff7ffc018ffffcff 0xffbffe00c7fffe7f

def z1021 : W := mkw 0x0179af6dec000000 0x00bcd7b6f6000000 0xbdff2ffffc000000 0xdeff97fffe000000

def z1022 : W := mkw 0x0159074d64000000 0x00ac83a6b2000000 0xbcff03fe70000000 0xde7f81ff38000000

def z1023 : W := mkw 0xa030ab815162d630 0xd01855c0a8b16b18 0xdf70ef81f3e3df39 0x6fb877c0f9f1ef9c

def z1024 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x7e7ffc0001fcf801 0x3f3ffe0000fe7c00

def z1025 : W := mkw 0x0114576dec000000 0x008a2bb6f6000000 0xa18e13fffc000000 0xd0c709fffe000000

def z1026 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x10ff01fe01ec0000 0x087f80ff00f60000

def z1027 : W := mkw 0xe89007df75244ff2 0x744803efba9227f9 0x818003fffc0007fe 0xc0c001fffe0003ff

def z1028 : W := mkw 0x0124fc25ec43b001 0x80927e12f621d800 0x4100fc01fc030000 0x20807e00fe018000

def z1029 : W := mkw 0x0020a00000428000 0x0010500000214000 0x10712c0001ecd800 0x0838960000f66c00

def z1030 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfdff23fe73fc07c1 0xfeff91ff39fe03e0

def z1031 : W := mkw 0x0069a80000cbb001 0x8034d4000065d800 0x12712c0001eff800 0x0938960000f7fc00

def z1032 : W := mkw 0x117dff6dec01200d 0x08beffb6f6009006 0xfdfffffffc030018 0xfefffffffe01800c

def z1033 : W := mkw 0xe979afcf7566ce72 0x74bcd7e7bab36739 0x10712d8e71ecd800 0x083896c738f66c00

def z1034 : W := mkw 0xf81007b7fd244ffe 0x7c0803dbfe9227ff 0x818003fffc0007fe 0xc0c001fffe0003ff

def z1035 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x727ffc0001fff800 0x393ffe0000fffc00

def z1036 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0xed8fdffffc000000 0xf6c7effffe000000

def z1037 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xfffffffffc03c000 0xfffffffffe01e000

def z1038 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xdf70e381f3ffc7f9 0x6fb871c0f9ffe3fc

def z1039 : W := mkw 0xe0db03da13bc47f0 0x706d81ed09de23f8 0xbcff03fe03fc07f9 0xde7f81ff01fe03fc

def z1040 : W := mkw 0xe082009213bc47f0 0x7041004909de23f8 0x0000000003fc07f9 0x0000000001fe03fc

def z1041 : W := mkw 0x805903c801200600 0x402c81e400900300 0xbcff03fe01e00000 0xde7f81ff00f00000

def z1042 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x8970c381f2e30318 0x44b861c0f971818c

def z1043 : W := mkw 0x1124fc25ec43b00d 0x88927e12f621d806 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z1044 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x99ffeffffc000000 0xccfff7fffe000000

def z1045 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffd0cd800 0xfefffffffe866c00

def z1046 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x187fec0001ecd800 0x0c3ff60000f66c00

def z1047 : W := mkw 0xe082009213bc47e0 0x7041004909de23f0 0x0200000003fcc7e1 0x0100000001fe63f0

def z1048 : W := mkw 0xf89657febf356fef 0x7c4b2bff5f9ab7f7 0xef8ed3fffe1327ff 0xf7c769ffff0993ff

def z1049 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc1004c1 0xfefffffffe080260

def z1050 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xcf8ec2718e0307ff 0xe7c76138c70183ff

def z1051 : W := mkw 0x0049000000880000 0x0024800000440000 0x76713c0001fcf801 0x3b389e0000fe7c00

def z1052 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x7cfffffff0000000 0x3e7ffffff8000000

def z1053 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x74713c0001ecd800 0x3a389e0000f66c00

def z1054 : W := mkw 0x0124fc24ac43b001 0x80927e125621d800 0x4200fc000c03f800 0x21007e000601fc00

def z1055 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x387ffc0003fff800 0x1c3ffe0001fffc00

def z1056 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0x208f1dfe7c000000 0x90478eff3e000000

def z1057 : W := mkw 0x0022a00002dbb001 0x80115000016dd800 0x7e71fc0003fff801 0x3f38fe0001fffc00

def z1058 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0xdf70e381f2e3c338 0x6fb871c0f971e19c

def z1059 : W := mkw 0xc0db03da03bd27c1 0x606d81ed01de93e0 0xbeff03fe03ff27c1 0xdf7f81ff01ff93e0

def z1060 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x7e7ffc0003efd801 0x3f3ffe0001f7ec00

def z1061 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0x18ff03fe01ec0000 0x0c7f81ff00f60000

def z1062 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x5071fc0001ecd800 0x2838fe0000f66c00

def z1063 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbdff03fe0ffc07e7 0xdeff81ff07fe03f3

def z1064 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0xdf71ee0183efdf39 0x6fb8f700c1f7ef9c

def z1065 : W := mkw 0xe082009213fff7f1 0xf041004909fffbf8 0x0200000003fffff9 0x0100000001fffffc

def z1066 : W := mkw 0x006ff80142dbb001 0x8037fc00a16dd800 0x7f7ffc01f3fff801 0x3fbffe00f9fffc00

def z1067 : W := mkw 0x00eff85802dbb181 0x8077fc2c016dd8c0 0x7efffc7003fff801 0x3f7ffe3801fffc00

def z1068 : W := mkw 0x0049000000880000 0x0024800000440000 0x10712c0001ecd800 0x0838960000f66c00

def z1069 : W := mkw 0x106ff81002dbb18d 0x8837fc08016dd8c6 0xff7ffe0183ffffff 0x7fbfff00c1ffffff

def z1070 : W := mkw 0x6800040634044862 0x340002031a022431 0xf7013d8e7c1cf8e6 0xfb809ec73e0e7c73

def z1071 : W := mkw 0xe830a3835166ce72 0x741851c1a8b36739 0xdf70e381f3e3c7ff 0x6fb871c0f9f1e3ff

def z1072 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff71ff81ffffffff 0xffb8ffc0ffffffff

def z1073 : W := mkw 0xd0db03da03bd27cd 0x686d81ed01de93e6 0xffffc3ff83ff27ff 0xffffe1ffc1ff93ff

def z1074 : W := mkw 0x017dff6dec881000 0x80beffb6f6440800 0xfdfffffffc0c1800 0xfefffffffe060c00

def z1075 : W := mkw 0x100650308a11218d 0x08032818450890c6 0x8b8ec2718e1327ff 0xc5c76138c70993ff

def z1076 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xa9ffdffffc000000 0xd4ffeffffe000000

def z1077 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0xa18f1dfe7c000000 0xd0c78eff3e000000

def z1078 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0x5f70e201f3e3c339 0x2fb87100f9f1e19c

def z1079 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x38ff03fe03fc03c0 0x9c7f81ff01fe01e0

def z1080 : W := mkw 0x7802009213156def 0x3c010049098ab6f7 0x02000000011cfce7 0x01000000008e7e73

def z1081 : W := mkw 0x680450a299044c62 0x340228514c822631 0xef8ed2718d1cfce7 0xf7c76938c68e7e73

def z1082 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0xbcff03fe03ec0701 0xde7f81ff01f60380

def z1083 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0xbcff03fe03fc0301 0xde7f81ff01fe0180

def z1084 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xfffffffffffff801 0xfffffffffffffc00

def z1085 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0x0870e201f2e3c318 0x04387100f971e18c

def z1086 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfefffe7183ffffd9 0xff7fff38c1ffffec

def z1087 : W := mkw 0x7802009213156def 0x3c010049098ab6f7 0x02000000021327ff 0x01000000010993ff

def z1088 : W := mkw 0x0079a74d64000000 0x003cd3a6b2000000 0xfdfffffffc000000 0xfefffffffe000000

def z1089 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffe7183ffffff 0x3f7fff38c1ffffff

def z1090 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xef8fde718e1f3fff 0xf7c7ef38c70f9fff

def z1091 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0x7efffc700ffff801 0xbf7ffe3807fffc00

def z1092 : W := mkw 0xe800048635244e72 0x740002431a922739 0xf7013d8e7d1cffff 0xfb809ec73e8e7fff

def z1093 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfeff13fe03fc27c1 0xff7f89ff01fe13e0

def z1094 : W := mkw 0xc0db03db43bc07c0 0x606d81eda1de03e0 0xbdff03fff3fc07c1 0xdeff81fff9fe03e0

def z1095 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0xbcff03fe01fc04c1 0xde7f81ff00fe0260

def z1096 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xbdffc3fffc000000 0xdeffe1fffe000000

def z1097 : W := mkw 0x016ff8688adbb001 0x80b7fc34456dd800 0x7efffc7003fff801 0x3f7ffe3801fffc00

def z1098 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffc0004e6 0xfefffffffe000273

def z1099 : W := mkw 0x6800048635044c62 0x340002431a822631 0xf7013f8ffd1cffff 0xfb809fc7fe8e7fff

def z1100 : W := mkw 0x014d5c6cac000000 0x00a6ae3656000000 0xfd8ffffffc000000 0xfec7fffffe000000

def z1101 : W := mkw 0x106ff8208adbb00d 0x8837fc10456dd806 0x7e7ffc0183fff819 0x3f3ffe00c1fffc0c

def z1102 : W := mkw 0xe0db03da13bc47e0 0x706d81ed09de23f0 0xffff33fe7ffce7e7 0xffff99ff3ffe73f3

def z1103 : W := mkw 0xe030a3835166c670 0x701851c1a8b36338 0xff71f38fffffe7ff 0xffb8f9c7fffff3ff

def z1104 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xef8efe718e13ffff 0xf7c77f38c709ffff

def z1105 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xffff23fe73fcffe7 0xffff91ff39fe7ff3

def z1106 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x767f3c0001fcf801 0x3b3f9e0000fe7c00

def z1107 : W := mkw 0x0079a34940000000 0x003cd1a4a0000000 0xbcff23fe70000000 0xde7f91ff38000000

def z1108 : W := mkw 0x015d5f6dec000000 0x00aeafb6f6000000 0x818e03fffc000000 0xc0c701fffe000000

def z1109 : W := mkw 0x006ff84802dbb001 0x8037fc24016dd800 0x7efffc7e03fff801 0xbf7ffe3f01fffc00

def z1110 : W := mkw 0xc0d903da01ac07c0 0x606c81ed00d603e0 0xbcff03fe01ec07c0 0xde7f81ff00f603e0

def z1111 : W := mkw 0x805b03c803b80600 0x402d81e401dc0300 0xbcff03fe03fc0701 0xde7f81ff01fe0380

def z1112 : W := mkw 0x0179a76dec000000 0x00bcd3b6f6000000 0xfdffe3fffc000000 0xfefff1fffe000000

def z1113 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffc7003fff801 0x3f7ffe3801fffc00

def z1114 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xddffeffff0000000 0x6efff7fff8000000

def z1115 : W := mkw 0x6800048635044c62 0x340002431a822631 0xff01fd8e7f1ffce7 0xff80fec73f8ffe73

def z1116 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff71e381f3ffc739 0x7fb8f1c0f9ffe39c

def z1117 : W := mkw 0x006ff80002980000 0x0037fc00014c0000 0x7e7ffc0003fcf801 0x3f3ffe0001fe7c00

def z1118 : W := mkw 0xe082009213fec7f0 0x7041004909ff63f8 0x0000000003fcc7c1 0x0000000001fe63e0

def z1119 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x107f2c0001ecd800 0x083f960000f66c00

def z1120 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xff71e38ff3e3c739 0xffb8f1c7f9f1e39c

def z1121 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x3c7f3c0003fcf801 0x1e3f9e0001fe7c00

def z1122 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffe1327ff 0xffffffffff0993ff

def z1123 : W := mkw 0x0000040424000000 0x0000020212000000 0xfd8f3ffe7c000000 0xfec79fff3e000000

def z1124 : W := mkw 0x40cb005a029c01c0 0x2065802d014e00e0 0x28ff007e02fc00c0 0x947f803f017e0060

def z1125 : W := mkw 0x0124fc25ec428000 0x00927e12f6214000 0x4300fc01fc03c000 0x21807e00fe01e000

def z1126 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0x7f7ffc018ffff801 0x3fbffe00c7fffc00

def z1127 : W := mkw 0x0000000000000000 0x0000000000000000 0x7e713c0003fcf801 0x3f389e0001fe7c00

def z1128 : W := mkw 0x81fdff6deca80200 0x40feffb6f6540100 0xfdfffffffce00000 0xfefffffffe700000

def z1129 : W := mkw 0x405b03ca039c0440 0x202d81e501ce0220 0xbcff03fe03fc04c1 0xde7f81ff01fe0260

def z1130 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x59fffffffc000000 0x2cfffffffe000000

def z1131 : W := mkw 0xc0cb00da03bc07c0 0x6065806d01de03e0 0x3cff007e03fc07c1 0x9e7f803f01fe03e0

def z1132 : W := mkw 0xd0db03da03bd27cd 0x686d81ed01de93e6 0xbcff03fe03ff07d9 0xde7f81ff01ff83ec

def z1133 : W := mkw 0x017dff6dec013001 0x80beffb6f6009800 0xfdfffffffc003800 0xfefffffffe001c00

def z1134 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0x28ff027e02e00300 0x947f813f01700180

def z1135 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x7e7f3c0003fcf801 0x3f3f9e0001fe7c00

def z1136 : W := mkw 0x0049044c24000000 0x0024822612000000 0xf58f3dfe7c000000 0xfac79eff3e000000

def z1137 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0xf7713c000dfcfce7 0xfbb89e0006fe7e73

def z1138 : W := mkw 0x0159076dec000000 0x00ac83b6f6000000 0x89fe03fffc000000 0xc4ff01fffe000000

def z1139 : W := mkw 0x2924fc25fc43f823 0x94927e12fe21fc11 0x4300fc01fc03f826 0x21807e00fe01fc13

def z1140 : W := mkw 0x017dff6dec428000 0x00beffb6f6214000 0xffffffffffe3c739 0xfffffffffff1e39c

def z1141 : W := mkw 0x004b004802980000 0x00258024014c0000 0x3cff007e03fc0001 0x9e7f803f01fe0000

def z1142 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0xfffffe700fffffe7 0xffffff3807fffff3

def z1143 : W := mkw 0x0020a00000428000 0x0010500000214000 0xff71fe018fffffff 0xffb8ff00c7ffffff

def z1144 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0x7efffe718ffffbdf 0xbf7fff38c7fffdef

def z1145 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdd70e381f3e3c318 0x6eb871c0f9f1e18c

def z1146 : W := mkw 0xf8db03da13bd6fef 0x7c6d81ed09deb7f7 0xbeff03fe03ffffff 0xdf7f81ff01ffffff

def z1147 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xffffd3ff8fff27ff 0xffffe9ffc7ff93ff

def z1148 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70e381ffe3c7ff 0xefb871c0fff1e3ff

def z1149 : W := mkw 0x4800040624040842 0x2400020312020421 0xf7013d8e7d1cf8c7 0xfb809ec73e8e7c63

def z1150 : W := mkw 0x100200308a10018c 0x08010018450800c6 0xef8ec2718e1307ff 0xf7c76138c70983ff

def z1151 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0xacff027e02fc07c1 0xd67f813f017e03e0

def z1152 : W := mkw 0x0034f725ec000000 0x001a7b92f6000000 0xfdfffffffc000000 0xfefffffffe000000

def z1153 : W := mkw 0x006ff80142dbb011 0x8037fc00a16dd808 0x7e7ffc0183fff819 0x3f3ffe00c1fffc0c

def z1154 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x187f2c0003ecd800 0x0c3f960001f66c00

def z1155 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x1071ec0001efd800 0x0838f60000f7ec00

def z1156 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0x0970c201f2e30338 0x04b86100f971819c

def z1157 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x71fffdfffc000000 0xb8fffefffe000000

def z1158 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc102001 0xfffffffffe081000

def z1159 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x3c7f2c0001ecd800 0x1e3f960000f66c00

def z1160 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xef8ed2718f1fffff 0xf7c76938c78fffff

def z1161 : W := mkw 0x100450308801218d 0x08022818440090c6 0xef8ed2718c0327fe 0xf7c76938c60193ff

def z1162 : W := mkw 0x0026f80002dbb001 0x80137c00016dd800 0x5e70fc0003fff801 0x2f387e0001fffc00

def z1163 : W := mkw 0x006ba00002da8000 0x0035d000016d4000 0x7e7ffc0003fff801 0x3f3ffe0001fffc00

def z1164 : W := mkw 0x006df82088ca9000 0x8036fc1044654800 0xfdfffe718decd800 0xfeffff38c6f66c00

def z1165 : W := mkw 0x006ff8208adbb001 0x8037fc10456dd800 0x7efffe7183fff801 0x3f7fff38c1fffc00

def z1166 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffd8073fff801 0x7fbffec039fffc00

def z1167 : W := mkw 0x007dff4c24000000 0x003effa612000000 0xfdfffffe7c000000 0xfeffffff3e000000

def z1168 : W := mkw 0x6802009213144de2 0x34010049098a26f1 0x02000000031cffe7 0x01000000018e7ff3

def z1169 : W := mkw 0x2124fc25fc43f031 0x90927e12fe21f818 0x4300fc01fc03f838 0x21807e00fe01fc1c

def z1170 : W := mkw 0xf89007febd244fee 0x7c4803ff5e9227f7 0x818003fffc0007fe 0xc0c001fffe0003ff

def z1171 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x5271ec0001efd800 0x2938f60000f7ec00

def z1172 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xbcff13fe0ffc27c7 0xde7f89ff07fe13e3

def z1173 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0x3cff03fe03fc0301 0x1e7f81ff01fe0180

def z1174 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x12712c0001fcf801 0x0938960000fe7c00

def z1175 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xe18ffffffc000000 0xf0c7fffffe000000

def z1176 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xfffed2718ff327ff 0xffff6938c7f993ff

def z1177 : W := mkw 0xc8db03da03bc0fc2 0x646d81ed01de07e1 0xbcff03fe03fc3fc7 0xde7f81ff01fe1fe3

def z1178 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x5b70e381f3e3c338 0x2db871c0f9f1e19c

def z1179 : W := mkw 0x3824f425fc43e83f 0x1c127a12fe21f41f 0x4300fc01fc03f83e 0x21807e00fe01fc1f

def z1180 : W := mkw 0x0059074c24000000 0x002c83a612000000 0xbcff2ffe70000000 0xde7f97ff38000000

def z1181 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0x8100018e7c0004e6 0xc08000c73e000273

def z1182 : W := mkw 0x006ff81002dbb181 0x8037fc08016dd8c0 0xfffffe7183fffff9 0xffffff38c1fffffc

def z1183 : W := mkw 0x40cb00da039c05c0 0x2065806d01ce02e0 0xbcff01fe03fc04c1 0xde7f80ff01fe0260

def z1184 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfdffc3ff83fc07c1 0xfeffe1ffc1fe03e0

def z1185 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x9970e381f3e3c738 0x4cb871c0f9f1e39c

def z1186 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x8b70c381f3e3c739 0x45b861c0f9f1e39c

def z1187 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xb4ff01fe01fc04c1 0xda7f80ff00fe0260

def z1188 : W := mkw 0x006ba80002da9000 0x8035d400016d4800 0x307f2c0001fcd800 0x183f960000fe6c00

def z1189 : W := mkw 0x006ba80002dbb001 0x8035d400016dd800 0x5e71ec0003fff801 0x2f38f60001fffc00

def z1190 : W := mkw 0xe8db03da13bc4fe2 0x746d81ed09de27f1 0xbcff03fe03fc07e7 0xde7f81ff01fe03f3

def z1191 : W := mkw 0xc0db035a02bc03c0 0x606d81ad015e01e0 0x3cff027e03fc03c1 0x9e7f813f01fe01e0

def z1192 : W := mkw 0x100658308a11318d 0x88032c18450898c6 0xef8ede718e133fff 0xf7c76f38c7099fff

def z1193 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfffffe7183ffff39 0x7fffff38c1ffff9c

def z1194 : W := mkw 0x016dfc6cac000000 0x00b6fe3656000000 0xfdfffdfe7c000000 0xfefffeff3e000000

def z1195 : W := mkw 0x0069a80000ca9000 0x8034d40000654800 0x12712c0003efd801 0x0938960001f7ec00

def z1196 : W := mkw 0x0026f0000253a001 0x001378000129d000 0x7e7ffc0003fff801 0x3f3ffe0001fffc00

def z1197 : W := mkw 0x016dfc6dec000000 0x00b6fe36f6000000 0xf58ffdfffc000000 0xfac7fefffe000000

def z1198 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0xbcff03fe02f007c1 0xde7f81ff017803e0

def z1199 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfffffffffc002026 0xfffffffffe001013

def z1200 : W := mkw 0x017dff6dec43b001 0x80beffb6f621d800 0xfdfffffffc030000 0xfefffffffe018000

def z1201 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7c7ffc0001fcf800 0x3e3ffe0000fe7c00

def z1202 : W := mkw 0x017dff6dec012001 0x00beffb6f6009000 0xfffffffffc032000 0xfffffffffe019000

def z1203 : W := mkw 0xc0db03da03bc07c0 0x606d81ed01de03e0 0xfeff23fe03fcc7c1 0xff7f91ff01fe63e0

def z1204 : W := mkw 0x004f580002993001 0x8027ac00014c9800 0x7e7f3c0003fcf801 0x3f3f9e0001fe7c00

def z1205 : W := mkw 0x80db035802b80380 0x406d81ac015c01c0 0x18ff03fe02e00300 0x0c7f81ff01700180

def z1206 : W := mkw 0x097dff6dec000802 0x04beffb6f6000401 0xfdfffffffc003806 0xfefffffffe001c03

def z1207 : W := mkw 0x2124fc25fc42c030 0x10927e12fe216018 0x4100fc01fc00c000 0x20807e00fe006000

def z1208 : W := mkw 0xd0db03da03bd27cd 0x686d81ed01de93e6 0xbcff03fe03fc27c7 0xde7f81ff01fe13e3

def z1209 : W := mkw 0x006df80000ca9000 0x8036fc0000654800 0x307f3c0001ecd800 0x183f9e0000f66c00

def z1210 : W := mkw 0xc0d903ca01ac0640 0x606c81e500d60320 0x30ff01fe01ec0000 0x987f80ff00f60000

def z1211 : W := mkw 0x8030a30140628210 0x40185180a0314108 0x4970e201f2e30318 0x24b87100f971818c

def z1212 : W := mkw 0x016ff821cadbb001 0x80b7fc10e56dd800 0x7e7ffc0183fff801 0x3f3ffe00c1fffc00

def z1213 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0x7cfffdfe7c000000 0xbe7ffeff3e000000

def z1214 : W := mkw 0x017dff4d64000000 0x00beffa6b2000000 0xfcfffffe70000000 0xfe7fffff38000000

def z1215 : W := mkw 0xe0db03db53bc47f0 0x706d81eda9de23f8 0xffff23fff3fcc7f9 0xffff91fff9fe63fc

def z1216 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0xdf70e381f3f3e7ff 0x6fb871c0f9f9f3ff

def z1217 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xfdfffffffe000701 0xfeffffffff000380

def z1218 : W := mkw 0x006df80000cbb001 0x8036fc000065d800 0x5e71fc0003eff801 0x2f38fe0001f7fc00

def z1219 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0xff7ffe018fffffff 0xffbfff00c7ffffff

def z1220 : W := mkw 0xe810078775244e72 0x740803c3ba922739 0x8100038ff0000738 0x408001c7f800039c

def z1221 : W := mkw 0x6800048635044c62 0x340002431a822631 0xb1013d8e7d1cfce6 0xd8809ec73e8e7e73

def z1222 : W := mkw 0x51cf5c7eae9d21cd 0x28e7ae3f574e90e6 0x208f1c7e0c1c20c6 0x90478e3f060e1063

def z1223 : W := mkw 0x004f500002992001 0x0027a800014c9000 0x7e7ffc0003fff801 0x3f3ffe0001fffc00

def z1224 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x1a7fec0003fff801 0x0d3ff60001fffc00

def z1225 : W := mkw 0x006ff80002dbb001 0x8037fc00016dd800 0x7c7ffc0003efd800 0x3e3ffe0001f7ec00

def z1226 : W := mkw 0xf882009213bd6fef 0x7c41004909deb7f7 0x0200000003ffffff 0x0100000001ffffff

def z1227 : W := mkw 0xa030a3015062c230 0x50185180a8316118 0xcf70e201f2e3c739 0x67b87100f971e39c

def z1228 : W := mkw 0x100450308800018c 0x08022818440000c6 0xef8ed2718e0307ff 0xf7c76938c70183ff

def z1229 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x5e70e381f3e3c319 0x2f3871c0f9f1e18c

def z1230 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfffffe718ffff8c7 0xffffff38c7fffc63

def z1231 : W := mkw 0x6800048635044c62 0x340002431a822631 0x73013d8e7d1cf8e6 0xb9809ec73e8e7c73

def z1232 : W := mkw 0xe91007effd244e72 0x748803f7fe922739 0x818003fffc0007fe 0xc0c001fffe0003ff

def z1233 : W := mkw 0xc0120392033407c0 0x600901c9019a03e0 0xbcff03fe03fc07c1 0xde7f81ff01fe03e0

def z1234 : W := mkw 0x106df82088cbb00d 0x8836fc104465d806 0x5371fc018deff83e 0x29b8fe00c6f7fc1f

def z1235 : W := mkw 0xa030a3815162c630 0x501851c0a8b16318 0x9c70e381f3e3c719 0x4e3871c0f9f1e38c

def z1236 : W := mkw 0x100650308a11218d 0x08032818450890c6 0xed8ed2718e0307fe 0xf6c76938c70183ff

def z1237 : W := mkw 0x017dff6dec000000 0x00beffb6f6000000 0xb1ff3ffffc000000 0xd8ff9ffffe000000

def z1238 : W := mkw 0x106ff8308adbb18d 0x8837fc18456dd8c6 0xfefffe700fffffc7 0xff7fff3807ffffe3

def z1239 : W := mkw 0x6800048635044c62 0x340002431a822631 0x32013d8e7d1cfce7 0x99009ec73e8e7e73

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z8,z3,z5,z6]),(0,[z9,z1,z10,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z12])],[(0,[z13,z0,z14,z2,z3,z5,z6]),(0,[z15,z0,z16,z2,z3,z5,z6]),(0,[z0,z16,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z18,z3,z5,z6]),(1,[z19,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z20,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z21])],[(0,[z22,z0,z1,z2,z3,z5,z23]),(0,[z24,z0,z2,z8,z3,z5,z6]),(0,[z25,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z26,z3,z5,z6]),(1,[z0,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z27,z3,z5,z6]),(0,[z28,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z29,z3,z5,z6]),(0,[z0,z1,z2,z30,z3,z31,z5])],[(1,[z0,z32,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z34,z5,z6]),(0,[z0,z35,z2,z34,z3,z5,z6]),(0,[z36,z0,z2,z3,z5,z17,z6]),(0,[z37,z0,z1,z2,z3,z38,z6]),(0,[z0,z39,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z40,z3,z5,z6]),(1,[z41,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z43,z6]),(0,[z0,z44,z1,z2,z3,z5,z6])],[(1,[z45,z1,z2,z3,z5,z6]),(0,[z0,z46,z1,z2,z47,z5,z6])],[(1,[z1,z48,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z49,z5,z6])],[(0,[z0,z1,z2,z50,z3,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z52,z0,z53,z2,z3,z5,z6]),(0,[z54,z0,z1,z55,z3,z5,z6]),(0,[z0,z56,z1,z2,z3,z5,z6]),(0,[z0,z57,z1,z2,z3,z5,z6])],[(0,[z58,z0,z1,z2,z3,z5,z6]),(0,[z59,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z3,z60,z5,z6]),(0,[z0,z1,z2,z3,z5,z61,z6]),(0,[z0,z1,z2,z62,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z63,z6]),(0,[z0,z1,z2,z3,z64,z5,z6]),(0,[z65,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z66,z5,z6]),(0,[z0,z1,z2,z67,z3,z5,z6])],[(0,[z0,z1,z68,z2,z3,z5,z6]),(0,[z0,z1,z2,z69,z3,z5,z6]),(1,[z0,z1,z2,z3,z70,z5]),(0,[z25,z71,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z3,z5,z72,z6])],[(0,[z0,z73,z46,z2,z3,z5,z6]),(0,[z74,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z75,z5,z6]),(0,[z0,z76,z1,z2,z3,z5,z6]),(0,[z77,z0,z1,z2,z3,z5,z6])],[(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z79,z6]),(0,[z54,z0,z1,z80,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z81,z6])],[(0,[z1,z2,z82,z3,z83,z5,z6]),(0,[z84,z0,z1,z2,z3,z5,z6])],[(0,[z9,z1,z2,z85,z3,z5,z6]),(1,[z0,z86,z2,z3,z5,z6]),(0,[z0,z87,z1,z2,z3,z5,z6]),(0,[z0,z1,z85,z3,z60,z5,z6])]],
   [[(0,[z88,z0,z1,z2,z3,z5,z6]),(0,[z37,z9,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z31,z5,z6]),(0,[z13,z9,z1,z2,z3,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z90]),(0,[z0,z1,z2,z3,z31,z5,z6])],[(0,[z0,z1,z2,z3,z5,z91,z6]),(0,[z92,z1,z48,z2,z3,z5,z6])],[(1,[z9,z1,z2,z3,z5,z6]),(0,[z93,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z94]),(0,[z0,z95,z1,z2,z3,z5,z6]),(0,[z96,z0,z1,z2,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z5,z6])],[(0,[z98,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z99,z3,z5,z6]),(0,[z0,z1,z2,z100,z3,z5,z6]),(0,[z0,z1,z2,z3,z101,z5,z6])],[(0,[z9,z0,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z23]),(0,[z0,z1,z2,z3,z5,z102,z103]),(1,[z0,z2,z104,z3,z5,z6]),(1,[z0,z1,z2,z3,z105,z103])],[(0,[z106,z0,z1,z2,z3,z5,z6]),(0,[z0,z73,z2,z3,z47,z5,z6]),(0,[z107,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z108,z3,z38,z6]),(0,[z0,z1,z2,z3,z43,z6,z103])],[(0,[z109,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z34,z3,z5,z110]),(0,[z0,z111,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z112,z3,z5,z6])],[(0,[z113,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z114,z5,z6]),(0,[z0,z115,z1,z2,z3,z5,z6])]],
   [[(0,[z37,z1,z2,z7,z3,z5,z6]),(0,[z116,z1,z2,z7,z3,z5,z6]),(0,[z13,z1,z2,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z6,z23]),(0,[z54,z13,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z117,z3,z5]),(0,[z118,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z119,z5,z6]),(0,[z9,z1,z2,z3,z5,z120,z6]),(1,[z0,z121,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z122,z5,z6]),(0,[z0,z1,z2,z3,z123,z5,z6]),(0,[z22,z24,z0,z1,z2,z3,z5]),(0,[z124,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z125,z2,z3,z5,z6]),(1,[z0,z1,z2,z126,z31,z5])],[(0,[z0,z1,z127,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z128,z5,z6]),(0,[z0,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z2,z3,z130,z5,z6]),(0,[z0,z1,z2,z131,z3,z5,z6])],[(0,[z132,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z133]),(0,[z84,z1,z108,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z5,z6]),(0,[z0,z1,z135,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z136]),(0,[z0,z1,z2,z3,z5,z12,z6])],[(0,[z9,z1,z2,z3,z5,z137,z6]),(0,[z9,z1,z2,z3,z5,z6,z138]),(0,[z139,z0,z1,z2,z3,z5,z6]),(0,[z140,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z3,z5,z6,z138])],[(0,[z141,z1,z2,z7,z3,z5,z6]),(0,[z0,z142,z1,z2,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z6,z23]),(1,[z1,z2,z3,z5,z6,z144]),(0,[z1,z2,z3,z5,z6,z144,z138])],[(0,[z0,z145,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z146,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z147,z6]),(0,[z25,z0,z1,z48,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z90,z103])],[(1,[z88,z73,z2,z3,z5,z6]),(0,[z1,z2,z7,z148,z3,z5,z6]),(0,[z0,z1,z2,z149,z3,z5,z6]),(0,[z22,z0,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z150,z6])],[],[(1,[z0,z1,z55,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z151,z6])],[(0,[z93,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z152,z6]),(0,[z153,z0,z1,z2,z3,z5,z6]),(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z17,z6]),(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z156,z6]),(0,[z0,z1,z2,z3,z157,z5,z6]),(0,[z0,z1,z2,z158,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z138]),(0,[z0,z1,z2,z159,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z160,z6]),(0,[z0,z1,z2,z3,z161,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z23]),(0,[z162,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z163,z5,z6]),(0,[z0,z1,z164,z2,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z63,z6]),(0,[z0,z2,z8,z3,z47,z5,z6]),(0,[z37,z165,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z30,z5,z6,z138]),(0,[z0,z1,z166,z2,z3,z5,z6])],[(0,[z13,z0,z56,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z167]),(0,[z0,z1,z2,z34,z3,z6,z168]),(0,[z169,z0,z1,z2,z3,z5,z90])]],
   [[(0,[z0,z1,z170,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z171,z6]),(0,[z1,z2,z7,z42,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z172]),(0,[z0,z1,z2,z3,z5,z6,z173]),(0,[z174,z0,z1,z2,z3,z5,z6]),(1,[z165,z1,z2,z3,z5,z6]),(0,[z0,z10,z2,z104,z3,z5,z6])],[(0,[z0,z73,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z175,z6]),(0,[z176,z9,z1,z2,z3,z5,z6]),(1,[z0,z56,z2,z3,z5,z6]),(0,[z0,z1,z177,z2,z3,z5,z178]),(0,[z0,z1,z2,z179,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z180,z3,z5,z6])],[(0,[z181,z0,z1,z2,z3,z5,z6]),(0,[z0,z182,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z183,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z9,z0,z1,z2,z3,z5,z6]),(0,[z1,z177,z2,z7,z3,z5,z6]),(0,[z184,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z185]),(1,[z0,z1,z2,z186,z3,z5]),(0,[z22,z0,z89,z1,z2,z3,z5]),(0,[z0,z2,z3,z187,z60,z5,z6]),(0,[z0,z1,z2,z3,z5,z90,z6])],[(0,[z188,z0,z1,z2,z3,z5,z6]),(0,[z15,z9,z1,z2,z3,z5,z6]),(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z190]),(0,[z24,z0,z1,z2,z3,z5,z90]),(0,[z0,z1,z2,z3,z5,z6,z191]),(0,[z0,z1,z2,z192,z3,z5,z6])],[(1,[z0,z193,z1,z2,z3,z5]),(0,[z0,z194,z1,z2,z3,z5,z6]),(0,[z195,z9,z1,z2,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z6,z196]),(0,[z0,z1,z2,z197,z3,z5,z6]),(0,[z0,z1,z108,z3,z38,z5,z6]),(0,[z0,z1,z2,z42,z5,z6,z196]),(0,[z0,z1,z2,z3,z198,z5,z6])],[(0,[z199,z1,z2,z7,z3,z5,z6]),(0,[z13,z1,z2,z82,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z200,z6]),(1,[z0,z1,z2,z201,z3,z5]),(0,[z0,z1,z2,z3,z202,z5,z6]),(0,[z0,z1,z2,z203,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z90,z6]),(0,[z36,z9,z1,z2,z3,z5,z6]),(0,[z0,z46,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z60,z5,z6,z196]),(0,[z169,z204,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z205,z3,z5,z6]),(0,[z0,z1,z2,z3,z206,z5,z6]),(0,[z33,z0,z177,z2,z3,z5,z6]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z208]),(0,[z1,z108,z2,z209,z3,z5,z6]),(1,[z210,z1,z2,z3,z5,z6])],[(0,[z88,z0,z73,z2,z3,z5,z6]),(0,[z211,z0,z1,z2,z3,z5,z6]),(0,[z204,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z90])],[(0,[z212,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z213,z5,z6]),(0,[z0,z1,z214,z2,z3,z5,z6])],[(0,[z9,z35,z1,z2,z3,z5,z6]),(0,[z215,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z178]),(0,[z0,z1,z2,z3,z5,z6,z216]),(0,[z217,z0,z1,z2,z3,z5,z6])],[(0,[z15,z1,z2,z7,z3,z5,z6]),(0,[z9,z1,z2,z34,z3,z5,z6]),(0,[z9,z116,z1,z2,z3,z5,z6]),(0,[z0,z1,z177,z2,z3,z5,z200]),(0,[z0,z1,z2,z3,z60,z5,z6])],[(0,[z0,z1,z2,z218,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z219,z6])],[(0,[z220,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z221,z5]),(0,[z0,z1,z2,z30,z3,z5,z138])],[(0,[z1,z222,z2,z7,z3,z5,z6]),(0,[z36,z1,z2,z7,z3,z5,z6]),(0,[z223,z0,z1,z2,z3,z5,z6]),(1,[z224,z1,z2,z3,z83,z6]),(0,[z0,z1,z2,z3,z5,z6,z225]),(0,[z0,z1,z2,z3,z226,z5,z6]),(0,[z0,z1,z2,z26,z3,z5,z103])]],
   [[(0,[z1,z2,z7,z3,z60,z5,z6]),(0,[z9,z1,z2,z227,z3,z5,z6]),(0,[z0,z1,z2,z228,z3,z5,z6]),(0,[z0,z1,z229,z2,z3,z5,z6]),(0,[z0,z1,z108,z2,z3,z5,z6])],[(0,[z230,z9,z1,z2,z3,z5,z6]),(0,[z1,z48,z2,z7,z3,z5,z6]),(0,[z231,z9,z1,z2,z3,z5,z6]),(0,[z232,z9,z1,z2,z3,z5,z6]),(0,[z233,z0,z1,z2,z3,z5,z6])],[(0,[z24,z0,z53,z2,z3,z5,z6]),(1,[z0,z142,z2,z3,z5,z6]),(0,[z0,z2,z8,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z234,z5,z6])],[(0,[z143,z0,z1,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z235]),(0,[z0,z1,z2,z3,z5,z6,z236])],[(0,[z0,z1,z2,z237,z3,z5,z6]),(0,[z143,z24,z0,z1,z2,z3,z5]),(1,[z0,z2,z3,z5,z6,z238])],[(0,[z0,z53,z2,z3,z47,z5,z6]),(0,[z239,z0,z1,z2,z3,z5,z6])],[(1,[z9,z1,z7,z3,z5,z6]),(0,[z33,z24,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z240,z3,z5,z6]),(0,[z0,z1,z2,z241,z3,z5,z6]),(0,[z0,z1,z10,z3,z5,z90,z6]),(0,[z0,z1,z2,z3,z242,z5,z6])],[(0,[z9,z1,z2,z8,z3,z5,z6]),(0,[z0,z1,z2,z8,z3,z5,z6]),(0,[z0,z16,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z243,z5,z6]),(0,[z0,z1,z2,z3,z43,z5,z6]),(1,[z140,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z244,z1,z2,z3,z5,z6]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z102]),(0,[z0,z1,z2,z3,z5,z245,z6]),(0,[z0,z1,z2,z148,z3,z43,z6]),(0,[z246,z0,z1,z2,z3,z5,z6])],[(0,[z230,z1,z2,z7,z3,z5,z6]),(0,[z231,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z247,z3,z5,z6]),(0,[z0,z1,z2,z3,z248,z5,z6]),(0,[z0,z1,z2,z3,z249,z5,z6])],[(0,[z9,z1,z2,z26,z3,z5,z6]),(0,[z0,z1,z2,z3,z250,z5,z6]),(0,[z36,z0,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z251,z5,z6]),(0,[z0,z1,z2,z26,z3,z5,z6])],[(0,[z1,z2,z7,z3,z43,z5,z6]),(0,[z24,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z5,z23]),(0,[z0,z252,z1,z2,z3,z5,z6]),(0,[z0,z46,z2,z34,z3,z5,z6])],[(0,[z253,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z254,z6]),(0,[z255,z0,z1,z2,z3,z5,z6]),(0,[z25,z0,z1,z2,z60,z5,z6])],[(0,[z9,z16,z1,z2,z3,z5,z6]),(0,[z0,z1,z256,z2,z3,z5,z6]),(0,[z0,z16,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z257,z3,z5,z6]),(0,[z0,z1,z2,z258,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z259]),(0,[z0,z1,z2,z3,z5,z6,z260])],[(0,[z261,z0,z1,z2,z3,z5,z6]),(1,[z22,z1,z2,z3,z5,z63]),(0,[z0,z1,z2,z3,z262,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z263]),(0,[z0,z1,z2,z3,z5,z6,z264]),(1,[z0,z1,z2,z3,z6,z265]),(0,[z0,z1,z2,z3,z5,z266,z6])]],
   [[(0,[z24,z0,z89,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z120,z6,z267]),(0,[z268,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z72,z6]),(0,[z269,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z270,z5,z6])],[(0,[z0,z1,z271,z2,z3,z5,z6]),(0,[z9,z1,z271,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z272]),(0,[z0,z1,z10,z2,z3,z5,z90])],[(0,[z0,z193,z1,z53,z2,z3,z5]),(0,[z9,z1,z2,z3,z5,z273,z6]),(0,[z0,z1,z2,z3,z5,z273,z6])],[(0,[z24,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z274,z5,z6]),(0,[z0,z1,z275,z2,z3,z5,z6]),(0,[z0,z276,z1,z2,z3,z5,z6]),(0,[z0,z277,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z278,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z72,z6]),(0,[z0,z1,z2,z279,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z280,z6]),(0,[z0,z1,z2,z3,z281,z5,z6]),(1,[z92,z1,z2,z3,z5,z6]),(0,[z0,z282,z1,z2,z3,z5,z6])],[(0,[z283,z0,z1,z2,z3,z5,z6]),(0,[z284,z0,z1,z2,z3,z5,z6]),(0,[z285,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z286,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z273,z6]),(0,[z9,z1,z2,z3,z287,z5,z6]),(0,[z0,z1,z2,z3,z287,z5,z6]),(0,[z25,z0,z288,z2,z3,z5,z6])],[(0,[z289,z1,z2,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z274,z5,z6]),(0,[z54,z143,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z290,z3,z5,z6]),(0,[z0,z1,z2,z291,z3,z5,z6]),(0,[z0,z1,z2,z3,z292,z5,z6])]],
   [[(1,[z52,z53,z2,z3,z5,z6]),(0,[z0,z1,z2,z293,z3,z5,z6]),(0,[z0,z1,z2,z294,z3,z5,z6]),(0,[z0,z1,z2,z3,z295,z5,z6])],[(0,[z0,z53,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z296,z5,z6]),(0,[z0,z1,z2,z297,z3,z5,z6])],[(0,[z0,z298,z1,z2,z3,z5,z6]),(0,[z0,z35,z2,z8,z3,z5,z6]),(0,[z299,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z70,z5,z6]),(0,[z25,z0,z1,z2,z85,z5,z6]),(1,[z0,z2,z3,z187,z5,z6])],[(0,[z88,z73,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z300])],[(0,[z301,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z5,z6]),(0,[z224,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z302,z3,z5,z6]),(0,[z303,z0,z1,z2,z3,z5,z6])],[(0,[z304,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z305,z2,z3,z5,z6])],[(0,[z306,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z186,z3,z5,z6]),(1,[z95,z1,z2,z3,z5,z6]),(0,[z0,z1,z307,z2,z3,z5,z6]),(0,[z1,z177,z2,z18,z3,z5,z6]),(0,[z0,z1,z2,z308,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z309]),(0,[z0,z1,z2,z310,z3,z5,z6]),(0,[z0,z1,z2,z311,z3,z5,z6])],[(0,[z88,z52,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z6,z23]),(0,[z0,z1,z2,z3,z5,z312,z6]),(0,[z0,z1,z2,z313,z3,z5,z6])]],
   [[(0,[z0,z1,z314,z2,z3,z5,z6]),(0,[z315,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z316,z5,z6]),(0,[z25,z0,z1,z2,z3,z5,z225]),(1,[z0,z1,z2,z3,z317,z6])],[(0,[z1,z2,z7,z3,z5,z17,z6]),(0,[z0,z1,z318,z2,z3,z5,z6]),(0,[z319,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z201,z3,z5,z17]),(0,[z0,z1,z2,z3,z31,z5,z90]),(0,[z0,z1,z2,z320,z3,z5,z6]),(0,[z0,z321,z1,z2,z3,z5,z6])],[(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z323,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z324])],[(0,[z0,z1,z2,z325,z3,z5,z6]),(0,[z24,z0,z16,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z326,z6])],[(0,[z52,z1,z2,z7,z3,z5,z6]),(0,[z327,z0,z1,z2,z3,z5,z6]),(0,[z328,z0,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z102]),(0,[z169,z210,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z329,z5,z6])],[(1,[z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z330,z5,z6]),(0,[z54,z116,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z331,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z332]),(0,[z0,z1,z2,z3,z5,z6,z333]),(0,[z0,z1,z2,z3,z5,z334,z6])],[(0,[z1,z2,z7,z3,z5,z6,z102]),(0,[z335,z0,z1,z2,z3,z5,z6]),(0,[z0,z336,z1,z2,z3,z5,z6]),(0,[z0,z1,z337,z2,z3,z5,z6]),(0,[z0,z89,z1,z2,z26,z3,z5])],[(0,[z0,z1,z2,z338,z3,z5,z6]),(0,[z0,z1,z2,z339,z3,z5,z6]),(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z3,z5,z341])]],
   [[(0,[z9,z1,z2,z148,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z342,z6]),(0,[z33,z0,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z343,z6]),(0,[z1,z48,z2,z344,z3,z5,z6]),(0,[z0,z1,z2,z345,z3,z5,z6]),(0,[z0,z1,z2,z148,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z5,z346])],[(0,[z9,z142,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z347]),(1,[z0,z1,z2,z3,z5,z341]),(0,[z0,z1,z3,z38,z5,z72,z6]),(0,[z0,z1,z2,z209,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z6,z196])],[(0,[z1,z108,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z348]),(0,[z0,z1,z2,z3,z349,z5,z6])],[(0,[z0,z1,z2,z350,z3,z5,z6]),(0,[z0,z1,z2,z351,z3,z5,z6]),(0,[z0,z1,z2,z3,z352,z5,z6]),(0,[z33,z0,z2,z3,z5,z17,z6]),(0,[z0,z89,z1,z2,z3,z105,z5]),(0,[z74,z0,z2,z3,z60,z5,z6]),(0,[z353,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z354,z6]),(1,[z0,z1,z2,z3,z355,z6]),(0,[z0,z1,z2,z3,z5,z6,z356])],[(0,[z1,z53,z2,z7,z3,z5,z6]),(0,[z357,z0,z1,z53,z2,z3,z5]),(0,[z1,z271,z2,z7,z3,z5,z6]),(0,[z9,z1,z177,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z63,z6]),(0,[z0,z1,z2,z3,z5,z63,z6]),(0,[z0,z1,z177,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z358,z5,z6]),(0,[z359,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z360,z6]),(0,[z0,z1,z2,z3,z5,z361,z6]),(0,[z362,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z363,z3,z5,z6]),(1,[z0,z1,z2,z3,z364,z6]),(0,[z0,z1,z365,z2,z3,z5,z6]),(1,[z1,z2,z366,z3,z5,z6])],[(0,[z88,z0,z53,z2,z3,z5,z6]),(0,[z0,z73,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z5,z171,z6]),(0,[z9,z1,z2,z42,z3,z5,z6]),(0,[z0,z1,z271,z48,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z90,z138])]],
   [[(0,[z9,z1,z2,z3,z5,z160,z6]),(0,[z45,z0,z1,z2,z3,z5,z6]),(0,[z0,z367,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z0,z1,z369,z2,z3,z5,z6]),(0,[z0,z370,z1,z2,z3,z5,z6])],[(0,[z371,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z372,z2,z3,z5,z6]),(0,[z0,z1,z2,z373,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z374,z6])],[(1,[z0,z1,z80,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z375,z6]),(0,[z0,z1,z376,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z377])],[(0,[z0,z1,z2,z3,z378,z5,z6]),(0,[z0,z1,z288,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z379]),(0,[z380,z0,z1,z2,z3,z5,z6])],[(0,[z116,z0,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z103,z138])],[(0,[z0,z73,z1,z2,z3,z5,z6]),(0,[z9,z73,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z6,z185]),(0,[z9,z1,z2,z3,z5,z90,z6]),(0,[z0,z2,z3,z81,z5,z120,z6]),(0,[z0,z381,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z382,z5,z6]),(1,[z0,z383,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z384,z5,z6]),(0,[z385,z0,z1,z2,z3,z5,z6]),(0,[z15,z95,z1,z2,z3,z5,z6]),(0,[z15,z0,z1,z177,z3,z5,z6]),(0,[z0,z16,z1,z177,z3,z5,z6]),(0,[z0,z177,z2,z34,z3,z5,z6]),(0,[z0,z1,z386,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z387])],[(0,[z0,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z388,z3,z5,z6]),(0,[z389,z0,z1,z2,z3,z5,z6])],[(0,[z9,z52,z1,z2,z3,z5,z6]),(0,[z9,z46,z1,z2,z3,z5,z6]),(0,[z22,z9,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z83,z5,z273,z6]),(0,[z0,z1,z2,z3,z390,z5,z6])],[(0,[z391,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z76,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z392])],[(0,[z113,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z393,z6]),(1,[z36,z0,z2,z3,z17,z6]),(0,[z0,z1,z2,z3,z5,z6,z394])],[(0,[z73,z1,z53,z2,z3,z5,z6]),(0,[z0,z1,z395,z2,z3,z5,z6]),(0,[z0,z1,z48,z85,z3,z5,z6]),(1,[z0,z76,z2,z3,z5,z6])],[(0,[z0,z1,z396,z2,z3,z5,z6]),(0,[z24,z0,z2,z3,z5,z6,z267]),(1,[z0,z1,z2,z42,z6,z196])],[(0,[z0,z1,z2,z3,z397,z5,z6]),(0,[z0,z1,z53,z2,z3,z5,z6]),(0,[z9,z1,z53,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z60,z5,z6]),(1,[z0,z1,z2,z3,z5,z398]),(0,[z0,z1,z2,z399,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z400]),(0,[z0,z1,z2,z3,z5,z6,z401]),(0,[z0,z1,z2,z402,z3,z5,z6]),(0,[z0,z1,z2,z403,z3,z5,z6]),(0,[z404,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z405,z5,z6]),(0,[z0,z2,z8,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z5,z406,z6]),(1,[z71,z1,z2,z3,z5,z6]),(0,[z0,z407,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z126,z30,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z408]),(0,[z409,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z10,z2,z3,z5,z102]),(0,[z410,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z411,z3,z5,z6]),(0,[z22,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z23,z138]),(0,[z0,z1,z2,z3,z5,z412,z6]),(0,[z24,z0,z1,z2,z26,z3,z5])],[(0,[z9,z1,z108,z2,z3,z5,z6]),(0,[z0,z177,z2,z8,z3,z5,z6]),(0,[z0,z1,z413,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z414]),(0,[z37,z0,z1,z108,z3,z5,z6]),(0,[z0,z415,z10,z2,z3,z5,z6])],[(0,[z9,z1,z86,z2,z3,z5,z6]),(0,[z0,z1,z86,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z416,z5,z6]),(0,[z0,z1,z417,z2,z3,z5,z6]),(0,[z0,z1,z2,z418,z3,z5,z6]),(0,[z0,z89,z2,z3,z5,z120,z6])],[(0,[z0,z1,z2,z3,z5,z419,z6]),(0,[z54,z0,z1,z2,z3,z420,z6]),(0,[z33,z0,z1,z2,z47,z5,z6]),(0,[z0,z2,z34,z3,z5,z17,z6])],[(0,[z230,z0,z1,z7,z3,z5,z6]),(0,[z1,z2,z421,z7,z3,z5,z6]),(0,[z0,z1,z48,z7,z3,z5,z6]),(0,[z9,z0,z1,z271,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z105,z5]),(0,[z0,z1,z2,z3,z422,z5,z6]),(0,[z423,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z26,z3,z6,z196])]],
   [[],[(0,[z169,z9,z1,z2,z3,z5,z6]),(0,[z13,z224,z1,z2,z3,z5,z6]),(0,[z424,z0,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z103]),(1,[z0,z1,z2,z3,z5,z200]),(0,[z425,z0,z1,z2,z3,z5,z6])],[(0,[z9,z1,z2,z3,z43,z5,z6]),(0,[z54,z0,z1,z2,z3,z426,z6]),(0,[z427,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z197,z5,z6]),(0,[z0,z1,z2,z104,z3,z5,z6]),(0,[z0,z383,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z428,z5,z6]),(0,[z0,z1,z2,z429,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z430]),(0,[z0,z1,z2,z431,z3,z5,z6])],[(0,[z0,z1,z2,z432,z3,z5,z6]),(0,[z0,z1,z2,z3,z47,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z6]),(1,[z1,z2,z344,z3,z5,z6]),(1,[z0,z1,z2,z197,z5,z6]),(1,[z433,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z434,z6]),(0,[z0,z1,z435,z2,z3,z5,z6])],[(0,[z436,z0,z1,z2,z3,z5,z6]),(0,[z437,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z438,z3,z5,z6]),(0,[z0,z1,z2,z439,z3,z5,z6])],[(0,[z0,z1,z440,z2,z3,z5,z6]),(0,[z176,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z82,z5,z6]),(0,[z0,z441,z1,z2,z3,z5,z6]),(0,[z442,z0,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z6,z196]),(0,[z443,z0,z1,z2,z3,z5,z6])],[(0,[z0,z141,z1,z2,z3,z5,z6]),(0,[z444,z0,z1,z2,z3,z5,z6]),(0,[z22,z143,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z63]),(0,[z0,z1,z2,z3,z5,z346,z6]),(0,[z0,z445,z2,z3,z5,z6,z103])]],
   [[(0,[z0,z193,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z47,z5,z6]),(0,[z9,z0,z86,z2,z3,z5,z6]),(1,[z1,z2,z18,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z21])],[(0,[z0,z1,z2,z3,z5,z446,z6]),(0,[z169,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z447,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z448,z5,z6]),(0,[z15,z0,z1,z2,z3,z5,z6]),(0,[z33,z0,z46,z2,z3,z5,z6]),(0,[z0,z1,z2,z449,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z5,z102])],[(0,[z0,z35,z53,z2,z3,z5,z6]),(0,[z9,z1,z2,z126,z3,z5,z6]),(0,[z195,z0,z1,z2,z3,z5,z6]),(0,[z0,z450,z1,z2,z3,z5,z6]),(0,[z451,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z453,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z43,z242,z5,z6]),(0,[z0,z1,z2,z126,z3,z5,z6])],[(0,[z9,z1,z2,z3,z5,z72,z6]),(0,[z0,z16,z177,z2,z3,z5,z6]),(0,[z0,z46,z1,z2,z34,z5,z6]),(0,[z0,z1,z2,z3,z5,z454,z6]),(0,[z455,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z456,z5,z6]),(0,[z0,z1,z2,z26,z117,z3,z5])],[(0,[z457,z0,z1,z2,z3,z5,z6]),(0,[z13,z1,z2,z3,z5,z273,z6]),(0,[z36,z0,z1,z2,z3,z5,z6]),(0,[z25,z0,z1,z3,z60,z5,z6])],[(0,[z0,z1,z2,z3,z458,z5,z6])],[(0,[z1,z2,z7,z126,z3,z5,z6]),(0,[z33,z9,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z274,z5,z6]),(0,[z54,z1,z2,z3,z5,z63,z6]),(1,[z0,z459,z2,z3,z5,z6]),(0,[z169,z0,z1,z3,z5,z6,z102])],[(0,[z0,z53,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z460,z5,z6]),(0,[z0,z1,z2,z461,z3,z5,z6]),(0,[z462,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z463,z5,z6])]],
   [[(1,[z1,z7,z3,z60,z5,z6]),(0,[z9,z1,z2,z3,z83,z5,z6]),(0,[z0,z1,z2,z3,z83,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z464]),(0,[z465,z0,z1,z2,z3,z5,z6])],[(0,[z73,z1,z2,z7,z3,z5,z6]),(0,[z143,z0,z89,z1,z2,z3,z5]),(0,[z0,z46,z2,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z466])],[(0,[z0,z467,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z5,z348]),(0,[z33,z0,z2,z3,z47,z5,z6]),(1,[z0,z1,z2,z26,z117,z3])],[(0,[z0,z1,z468,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z0,z1,z2,z470,z3,z5,z6]),(0,[z0,z1,z2,z126,z3,z31,z5])],[(0,[z1,z2,z7,z3,z83,z5,z6]),(0,[z0,z1,z2,z471,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z472,z6]),(1,[z0,z1,z2,z3,z5,z110]),(0,[z25,z19,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z473,z6])],[(0,[z1,z10,z2,z7,z3,z5,z6]),(0,[z143,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z474,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z265])],[(0,[z231,z0,z1,z2,z3,z5,z6]),(0,[z230,z0,z1,z2,z3,z5,z6]),(0,[z33,z1,z2,z7,z3,z5,z6]),(0,[z9,z1,z48,z2,z3,z5,z6]),(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z475,z0,z1,z2,z3,z5,z6]),(0,[z15,z476,z1,z2,z3,z5,z6]),(0,[z477,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z478,z5,z6])],[(0,[z1,z2,z7,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z105,z5,z6]),(0,[z1,z2,z7,z3,z5,z6,z103]),(0,[z0,z1,z2,z3,z479,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z144])]],
   [[(0,[z9,z1,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z83,z5,z398]),(0,[z0,z16,z1,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z482,z6])],[(0,[z0,z483,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z420,z6]),(0,[z54,z0,z1,z2,z3,z5,z342]),(0,[z0,z1,z2,z3,z484,z5,z6]),(0,[z0,z32,z1,z2,z3,z5,z6]),(0,[z485,z0,z1,z2,z3,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z267]),(1,[z0,z1,z2,z30,z5,z138]),(0,[z0,z1,z2,z486,z3,z5,z6])],[(0,[z46,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z487,z5,z6]),(0,[z169,z0,z1,z10,z3,z5,z6]),(0,[z169,z0,z1,z2,z3,z5,z102])],[],[(0,[z488,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z489]),(0,[z0,z1,z2,z490,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z491]),(0,[z0,z415,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z492,z3,z5,z6])],[(0,[z1,z2,z493,z7,z3,z5,z6]),(0,[z143,z1,z2,z7,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z6,z102]),(0,[z15,z0,z2,z34,z3,z5,z6]),(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z495,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z102]),(0,[z0,z1,z2,z148,z3,z6,z196])],[(0,[z224,z0,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z5,z496,z6]),(0,[z0,z497,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z102,z138])],[(0,[z0,z1,z2,z3,z498,z5,z6]),(0,[z116,z0,z1,z2,z82,z5,z6]),(0,[z0,z1,z2,z3,z38,z5,z6]),(0,[z0,z1,z2,z26,z117,z3,z6])]],
   [[(0,[z1,z2,z82,z3,z5,z63,z6]),(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z63,z6,z23]),(0,[z0,z500,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z157,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z501]),(0,[z0,z1,z2,z30,z3,z317,z6]),(0,[z0,z1,z2,z3,z317,z5,z6])],[(0,[z0,z1,z2,z3,z5,z63,z138]),(0,[z0,z1,z2,z502,z3,z5,z6]),(0,[z0,z165,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z503,z3,z5,z6]),(0,[z0,z1,z504,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z505]),(0,[z0,z1,z506,z2,z3,z5,z6])],[(0,[z89,z1,z2,z7,z3,z5,z6]),(0,[z45,z1,z177,z2,z3,z5,z6]),(0,[z0,z1,z507,z2,z3,z5,z6]),(1,[z0,z1,z2,z157,z5,z6])],[(0,[z357,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z38,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z0,z1,z2,z148,z60,z5,z6]),(0,[z0,z1,z48,z2,z85,z5,z6])],[(0,[z289,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z509,z3,z5,z6]),(0,[z0,z1,z2,z510,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z102]),(0,[z511,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z512,z3,z5,z6]),(0,[z25,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z513,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z178]),(1,[z0,z1,z2,z3,z6,z168]),(0,[z0,z1,z2,z3,z514,z5,z6]),(0,[z0,z1,z2,z515,z3,z5,z6])],[(0,[z1,z2,z7,z516,z3,z5,z6]),(0,[z0,z1,z2,z80,z3,z5,z6]),(0,[z517,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z42,z148,z5,z6])],[(0,[z0,z1,z2,z3,z518,z5,z6]),(1,[z0,z519,z2,z3,z5,z6]),(0,[z0,z1,z2,z520,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z521,z5,z6]),(0,[z15,z0,z2,z8,z3,z5,z6]),(1,[z0,z35,z2,z3,z81,z6]),(1,[z37,z0,z1,z3,z72,z6]),(0,[z0,z522,z1,z2,z3,z5,z6])],[(0,[z523,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z117,z3,z5,z6]),(1,[z9,z1,z271,z3,z5,z6]),(0,[z0,z1,z2,z82,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z524]),(0,[z0,z210,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z525,z3,z5,z6]),(0,[z0,z1,z2,z126,z31,z5,z6])],[(0,[z15,z0,z73,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z24,z0,z2,z3,z81,z5,z6]),(0,[z0,z1,z3,z5,z90,z6,z102]),(0,[z0,z1,z2,z3,z5,z6,z238])],[(0,[z0,z1,z2,z526,z3,z5,z6]),(0,[z476,z0,z1,z2,z3,z5,z6]),(0,[z0,z35,z16,z2,z3,z5,z6]),(0,[z0,z527,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z528]),(0,[z0,z1,z2,z3,z5,z529,z6]),(1,[z0,z1,z2,z3,z5,z346])],[(0,[z0,z1,z2,z3,z5,z6,z530]),(0,[z0,z1,z2,z3,z5,z531,z6]),(1,[z0,z46,z2,z34,z5,z6]),(0,[z0,z1,z2,z3,z105,z6,z103]),(0,[z0,z1,z2,z532,z3,z5,z6])],[(0,[z25,z1,z2,z7,z3,z5,z6]),(0,[z1,z2,z7,z82,z3,z5,z6]),(0,[z0,z1,z55,z2,z3,z5,z6]),(0,[z0,z1,z533,z2,z3,z5,z6]),(0,[z0,z1,z2,z534,z3,z5,z6]),(0,[z0,z2,z34,z3,z47,z5,z6]),(0,[z25,z0,z1,z2,z3,z5,z332]),(0,[z535,z0,z1,z2,z3,z5,z6])],[(0,[z54,z0,z1,z2,z274,z5,z6]),(1,[z0,z89,z2,z3,z5,z120]),(0,[z0,z1,z2,z3,z5,z536,z6]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z0,z1,z2,z148,z43,z5,z6])],[(0,[z0,z1,z538,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z539,z6]),(0,[z0,z1,z2,z540,z3,z5,z6])]],
   [[(0,[z0,z1,z541,z2,z3,z5,z6]),(0,[z0,z542,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z543,z6]),(0,[z0,z1,z2,z544,z3,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z546,z2,z3,z5,z6]),(0,[z0,z1,z2,z148,z85,z5,z6]),(0,[z0,z1,z2,z547,z3,z5,z6])],[(0,[z52,z0,z1,z2,z3,z5,z6]),(1,[z357,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z548,z3,z5,z6]),(0,[z0,z1,z2,z549,z3,z5,z6])],[(1,[z9,z86,z2,z3,z5,z6]),(0,[z0,z550,z1,z2,z3,z5,z6])],[(0,[z88,z9,z1,z2,z3,z5,z6]),(0,[z0,z73,z177,z2,z3,z5,z6]),(0,[z551,z0,z1,z2,z3,z5,z6]),(0,[z9,z0,z142,z2,z3,z5,z6]),(0,[z143,z1,z2,z82,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z267]),(0,[z0,z1,z2,z3,z552,z5,z6])],[(0,[z1,z2,z7,z3,z5,z543,z6]),(0,[z0,z1,z2,z3,z5,z6,z553]),(0,[z24,z0,z2,z34,z3,z5,z6]),(0,[z0,z1,z2,z554,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z5,z364,z6]),(0,[z0,z1,z555,z2,z3,z5,z6])],[(0,[z0,z1,z2,z493,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z267])],[(0,[z0,z1,z2,z3,z426,z5,z6]),(0,[z0,z1,z2,z3,z556,z5,z6]),(0,[z0,z1,z2,z3,z557,z5,z6])],[(0,[z1,z2,z7,z3,z5,z6,z267]),(0,[z54,z1,z2,z3,z274,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z558]),(0,[z559,z0,z1,z2,z3,z5,z6]),(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z41,z1,z10,z2,z3,z5,z6]),(1,[z0,z1,z10,z3,z5,z90])]],
   [[(0,[z0,z1,z2,z3,z561,z5,z6]),(0,[z0,z1,z2,z34,z3,z221,z5]),(0,[z0,z1,z2,z3,z5,z6,z259])],[(0,[z0,z1,z2,z562,z3,z5,z6]),(0,[z54,z1,z2,z3,z83,z5,z6]),(0,[z224,z1,z2,z3,z83,z5,z6]),(0,[z0,z1,z2,z563,z3,z5,z6]),(0,[z0,z1,z2,z3,z564,z5,z6]),(0,[z410,z0,z2,z3,z5,z6,z138])],[(0,[z0,z1,z2,z3,z70,z5,z17]),(0,[z0,z1,z2,z3,z565,z5,z6])],[(0,[z88,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z566]),(0,[z37,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z567])],[(0,[z0,z1,z2,z3,z5,z568,z6]),(0,[z0,z2,z3,z5,z6,z238,z103])],[(0,[z0,z1,z2,z569,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z19,z1,z2,z3,z5,z6]),(0,[z0,z1,z10,z2,z3,z5,z6]),(0,[z0,z1,z570,z2,z3,z5,z6])],[(0,[z571,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z572,z3,z5,z6]),(0,[z36,z0,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z6,z103])],[(1,[z476,z1,z2,z3,z5,z6]),(0,[z33,z15,z0,z2,z3,z5,z6])]],
   [[(1,[z13,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z573,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z138]),(0,[z0,z1,z2,z3,z187,z5,z6]),(1,[z204,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z574,z6]),(0,[z24,z0,z73,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z575,z5,z6]),(0,[z0,z576,z1,z2,z3,z5,z6]),(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z0,z578,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z579,z3,z5,z6])],[(0,[z1,z2,z2,z7,z3,z5,z6]),(0,[z0,z1,z222,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z580,z5,z6]),(0,[z0,z1,z2,z3,z31,z5,z103])],[(0,[z0,z1,z2,z3,z5,z6,z110]),(0,[z0,z1,z108,z2,z3,z72,z6]),(0,[z433,z1,z2,z3,z5,z6,z196])],[(0,[z0,z1,z2,z3,z581,z5,z6]),(0,[z582,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z583,z3,z5,z6]),(0,[z224,z0,z1,z2,z3,z83,z6]),(1,[z0,z1,z2,z3,z5,z225]),(0,[z0,z1,z2,z584,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z585])],[(0,[z586,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z587,z3,z5,z6]),(0,[z37,z268,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z126,z3,z5,z138]),(0,[z0,z1,z2,z588,z3,z5,z6])],[(0,[z9,z1,z2,z3,z47,z5,z6]),(0,[z9,z89,z1,z2,z3,z5,z6]),(0,[z116,z0,z1,z2,z274,z5,z6]),(0,[z0,z1,z2,z589,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z590]),(0,[z0,z1,z2,z117,z3,z105,z5]),(0,[z0,z1,z2,z591,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z31,z5,z63]),(0,[z592,z0,z1,z2,z3,z5,z6]),(1,[z268,z1,z2,z3,z5,z6])],[(0,[z0,z46,z53,z2,z3,z5,z6]),(0,[z1,z2,z82,z3,z274,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z593]),(0,[z594,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z72,z6]),(0,[z0,z595,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z596,z3,z5,z6])],[(0,[z0,z1,z597,z2,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z17,z6]),(0,[z0,z1,z2,z3,z105,z5,z103])],[(0,[z0,z1,z598,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z273,z6]),(0,[z0,z1,z2,z85,z3,z5,z6]),(1,[z25,z0,z1,z60,z5,z6])],[(0,[z599,z0,z1,z2,z3,z5,z6]),(0,[z600,z0,z1,z2,z3,z5,z6]),(0,[z601,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z83,z6,z196]),(0,[z0,z1,z2,z3,z602,z5,z6]),(0,[z603,z0,z1,z2,z3,z5,z6])],[(0,[z9,z9,z1,z2,z3,z5,z6]),(0,[z184,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z604]),(0,[z0,z1,z2,z3,z605,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z72,z6,z196]),(0,[z0,z1,z108,z2,z3,z38,z6])]],
   [[(1,[z230,z1,z7,z3,z5,z6]),(0,[z1,z2,z7,z85,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z43,z6]),(0,[z0,z89,z1,z2,z3,z31,z5]),(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z607,z5,z6]),(1,[z0,z2,z3,z242,z5,z6])],[(0,[z1,z2,z7,z3,z31,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z608]),(1,[z0,z1,z2,z148,z43,z6]),(0,[z0,z445,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z609,z3,z5,z6])],[(0,[z52,z0,z73,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z610,z5,z6]),(0,[z0,z1,z2,z3,z326,z5,z6]),(0,[z0,z1,z2,z30,z3,z6,z265]),(0,[z0,z1,z611,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z612,z5,z6])],[(0,[z613,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z271,z3,z60,z5,z6]),(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z615,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z341]),(0,[z0,z1,z2,z616,z3,z5,z6])],[(0,[z1,z2,z7,z99,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z617,z6]),(0,[z0,z618,z1,z2,z3,z5,z6]),(0,[z619,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z620,z3,z5,z6])],[(0,[z0,z1,z2,z85,z5,z6,z196]),(0,[z0,z1,z2,z621,z3,z5,z6])],[(0,[z9,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z421,z3,z5,z6]),(0,[z9,z1,z2,z3,z105,z5,z6]),(0,[z9,z1,z2,z3,z5,z6,z103]),(0,[z0,z1,z2,z3,z5,z6,z622]),(0,[z0,z1,z2,z3,z221,z5,z6]),(0,[z0,z1,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z43,z38,z6]),(0,[z0,z1,z2,z3,z105,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z103]),(0,[z0,z1,z2,z623,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z624,z6]),(0,[z9,z1,z2,z3,z625,z5,z6]),(0,[z0,z1,z2,z3,z625,z5,z6]),(0,[z0,z1,z2,z626,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z627]),(0,[z0,z1,z2,z628,z3,z5,z6]),(0,[z0,z1,z629,z2,z3,z5,z6]),(1,[z24,z0,z2,z3,z5,z267]),(0,[z0,z519,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z630,z6])]],
   [[(0,[z0,z1,z2,z3,z631,z5,z6]),(0,[z632,z0,z1,z2,z3,z5,z6]),(1,[z15,z0,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z633]),(0,[z0,z1,z2,z634,z3,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z120]),(0,[z0,z1,z635,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z636]),(0,[z0,z1,z2,z3,z5,z637,z6]),(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z2,z60,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z639]),(0,[z1,z2,z7,z3,z5,z120,z6]),(0,[z223,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z137,z6]),(0,[z0,z1,z2,z640,z3,z5,z6]),(0,[z0,z641,z1,z2,z3,z5,z6])],[(0,[z0,z53,z177,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z128,z5,z6]),(1,[z54,z1,z2,z274,z5,z6]),(0,[z15,z0,z1,z8,z3,z5,z6]),(0,[z642,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z643,z6])],[(0,[z0,z1,z2,z3,z644,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z138]),(0,[z0,z1,z2,z3,z5,z6,z645]),(0,[z0,z1,z2,z3,z38,z6,z196]),(0,[z0,z1,z2,z3,z5,z6,z646]),(0,[z0,z1,z2,z647,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(1,[z9,z142,z2,z3,z5,z6]),(0,[z0,z1,z2,z648,z3,z5,z6]),(0,[z0,z1,z2,z3,z355,z5,z6]),(1,[z0,z1,z48,z85,z5,z6])],[(0,[z1,z2,z7,z3,z5,z6,z138]),(0,[z649,z9,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z83,z6]),(0,[z169,z0,z1,z2,z3,z5,z6]),(1,[z410,z0,z2,z3,z5,z6]),(0,[z650,z0,z1,z2,z3,z5,z6])],[(0,[z36,z24,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z366,z3,z5,z6]),(0,[z0,z1,z2,z26,z3,z43,z6])]],
   [[(0,[z0,z1,z2,z3,z651,z5,z6]),(0,[z15,z0,z53,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z426,z6]),(1,[z143,z1,z2,z3,z5,z23])],[(0,[z54,z0,z372,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z3,z652,z5,z6]),(0,[z1,z10,z2,z366,z3,z5,z6]),(0,[z0,z1,z2,z653,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z654,z6]),(0,[z9,z1,z2,z3,z38,z5,z6]),(0,[z0,z1,z2,z655,z3,z5,z6]),(0,[z0,z1,z656,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z5,z6])],[(0,[z0,z73,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z657,z6]),(0,[z0,z1,z658,z2,z3,z5,z6])],[(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z660,z5,z6]),(0,[z661,z0,z1,z2,z3,z5,z6]),(0,[z0,z16,z46,z2,z3,z5,z6]),(0,[z33,z0,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z5,z6,z662]),(0,[z0,z383,z2,z3,z43,z5,z6])],[(0,[z0,z1,z2,z516,z3,z5,z6]),(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z332,z6]),(0,[z37,z0,z305,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z664,z6]),(0,[z0,z1,z2,z34,z3,z355,z6])],[(0,[z0,z1,z2,z3,z5,z6,z665]),(0,[z9,z1,z2,z3,z81,z5,z6]),(0,[z0,z1,z2,z3,z5,z420,z6]),(0,[z143,z0,z1,z2,z3,z5,z103]),(0,[z0,z1,z2,z3,z81,z5,z6]),(1,[z0,z305,z2,z3,z5,z6])]],
   [[(0,[z666,z0,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z117,z3,z5,z6]),(0,[z667,z0,z1,z2,z3,z5,z6]),(1,[z1,z2,z209,z3,z5,z6]),(0,[z140,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z398]),(0,[z0,z668,z1,z2,z3,z5,z6]),(0,[z92,z0,z1,z2,z3,z5,z6]),(1,[z169,z0,z1,z3,z5,z102])],[(0,[z230,z0,z1,z271,z3,z5,z6]),(0,[z0,z1,z669,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z670,z6])],[(0,[z1,z2,z7,z3,z81,z5,z6]),(0,[z1,z2,z7,z3,z5,z6,z665]),(0,[z116,z1,z2,z82,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z5,z6]),(1,[z74,z0,z2,z3,z5,z6])],[(0,[z9,z1,z2,z82,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z31,z5]),(1,[z0,z2,z3,z5,z6,z324]),(0,[z0,z2,z3,z5,z6,z324,z138])],[(0,[z671,z0,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z2,z3,z5,z6]),(0,[z0,z121,z1,z2,z3,z5,z6]),(1,[z116,z1,z2,z82,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z63]),(0,[z0,z16,z2,z3,z47,z5,z6]),(0,[z0,z1,z672,z2,z3,z5,z6]),(1,[z33,z0,z2,z47,z5,z6]),(0,[z0,z2,z3,z81,z5,z17,z6])],[(0,[z22,z0,z459,z2,z3,z5,z6]),(0,[z25,z0,z1,z2,z3,z326,z6]),(0,[z0,z1,z2,z3,z673,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z674]),(0,[z675,z0,z1,z2,z3,z5,z6]),(0,[z676,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z255,z1,z2,z7,z3,z5,z6]),(0,[z283,z9,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z348]),(0,[z0,z1,z2,z677,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z678,z6])],[(0,[z1,z2,z7,z3,z206,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z34,z3,z5,z6]),(0,[z0,z1,z2,z201,z3,z5,z6]),(0,[z0,z1,z2,z679,z3,z5,z6]),(0,[z0,z1,z2,z31,z5,z6,z138]),(0,[z0,z1,z2,z117,z3,z31,z5])],[(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z680,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z681,z5,z6]),(0,[z682,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z26,z3,z105,z6])],[(0,[z0,z1,z2,z3,z43,z83,z6]),(0,[z0,z1,z2,z3,z5,z6,z168]),(0,[z0,z1,z2,z683,z3,z5,z6])],[(0,[z24,z0,z1,z2,z3,z5,z120]),(0,[z0,z1,z2,z684,z3,z5,z6]),(0,[z685,z0,z1,z2,z3,z5,z6]),(0,[z686,z0,z1,z2,z3,z5,z6]),(0,[z433,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z34,z3,z5,z6]),(0,[z0,z1,z2,z227,z3,z5,z6]),(0,[z0,z1,z2,z3,z273,z6,z196])],[(0,[z0,z1,z2,z3,z5,z687,z6]),(0,[z9,z1,z2,z3,z5,z6,z267]),(0,[z0,z688,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z186,z3,z83,z5])],[(0,[z54,z9,z1,z2,z3,z5,z6]),(0,[z224,z9,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z342]),(0,[z0,z1,z2,z3,z689,z5,z6]),(0,[z25,z0,z519,z2,z3,z5,z6]),(0,[z0,z1,z690,z2,z3,z5,z6])]],
   [[(0,[z649,z0,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z3,z72,z6]),(0,[z691,z0,z1,z2,z3,z5,z6])],[(0,[z35,z1,z2,z7,z3,z5,z6]),(0,[z25,z0,z1,z2,z3,z364,z6]),(0,[z0,z1,z2,z3,z5,z6,z692])],[(0,[z9,z1,z2,z3,z5,z6,z196]),(0,[z9,z1,z2,z30,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z5,z6,z693]),(0,[z0,z35,z2,z3,z81,z5,z6]),(0,[z0,z1,z2,z3,z694,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z196]),(0,[z0,z1,z2,z30,z3,z5,z6])],[(0,[z1,z2,z583,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z695,z5,z6]),(0,[z0,z1,z2,z42,z3,z5,z259]),(1,[z0,z445,z2,z3,z5,z6])],[(0,[z16,z1,z2,z7,z3,z5,z6]),(1,[z0,z372,z2,z3,z5,z6]),(0,[z0,z1,z2,z696,z3,z5,z6]),(0,[z0,z1,z459,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z697,z5,z6]),(1,[z84,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z21,z196]),(0,[z0,z1,z2,z3,z5,z6,z698]),(0,[z0,z1,z2,z3,z6,z103,z196]),(0,[z699,z0,z1,z2,z3,z5,z6]),(0,[z0,z700,z1,z2,z3,z5,z6])],[(0,[z52,z1,z53,z2,z3,z5,z6]),(0,[z701,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z702,z2,z3,z5,z6]),(0,[z0,z1,z2,z344,z3,z5,z6]),(1,[z0,z415,z2,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z6,z196]),(0,[z1,z2,z7,z30,z3,z5,z6]),(0,[z54,z0,z121,z2,z3,z5,z6]),(0,[z0,z1,z2,z703,z3,z5,z6]),(1,[z0,z288,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z5,z6,z196])],[(0,[z0,z1,z2,z3,z704,z5,z6]),(0,[z54,z1,z2,z7,z3,z5,z6]),(0,[z224,z1,z2,z7,z3,z5,z6]),(0,[z0,z2,z34,z3,z5,z120,z6]),(0,[z0,z1,z2,z705,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z7,z707,z3,z5]),(0,[z2,z7,z3,z5,z6,z238]),(0,[z9,z1,z2,z3,z221,z5]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z25,z0,z1,z709,z5,z6]),(0,[z1,z2,z3,z5,z6,z710]),(0,[z0,z1,z570,z3,z38,z6])],[(0,[z711,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z712]),(0,[z1,z55,z7,z3,z5,z6]),(0,[z713,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z714]),(0,[z0,z1,z2,z3,z168,z110]),(1,[z0,z2,z3,z5,z715]),(0,[z0,z1,z2,z716,z5,z6]),(0,[z0,z1,z2,z3,z226,z103]),(0,[z0,z445,z2,z3,z105,z5])],[(0,[z459,z2,z7,z3,z5,z6]),(0,[z283,z142,z2,z3,z5,z6]),(0,[z54,z1,z2,z274,z5,z6]),(0,[z1,z2,z3,z5,z6,z144]),(0,[z0,z1,z2,z3,z5,z717]),(0,[z37,z0,z1,z157,z72,z6]),(0,[z0,z445,z2,z3,z43,z6])],[(0,[z1,z538,z7,z3,z5,z6]),(0,[z22,z32,z2,z3,z5,z63]),(0,[z0,z2,z34,z3,z70,z5]),(0,[z0,z1,z229,z3,z5,z102]),(0,[z19,z1,z48,z3,z5,z6]),(0,[z0,z718,z2,z3,z5,z6])],[(0,[z9,z719,z2,z3,z5,z6]),(0,[z116,z1,z2,z227,z5,z6]),(0,[z0,z720,z2,z3,z5,z6]),(0,[z269,z1,z2,z3,z83,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z1,z2,z722,z3,z5,z6]),(0,[z0,z2,z3,z5,z120,z309]),(0,[z0,z1,z48,z709,z5,z6]),(0,[z0,z1,z2,z5,z6,z723])],[(0,[z1,z2,z7,z3,z5,z178]),(0,[z0,z1,z2,z3,z420,z342]),(0,[z410,z0,z2,z3,z5,z6]),(0,[z724,z1,z2,z3,z5,z6]),(0,[z725,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z103,z646])],[(0,[z726,z1,z2,z7,z3,z6]),(0,[z9,z727,z86,z2,z3,z5]),(0,[z9,z1,z399,z3,z5,z6]),(0,[z0,z728,z2,z3,z5,z6]),(0,[z24,z0,z2,z3,z5,z566]),(0,[z25,z0,z1,z60,z5,z225])],[(0,[z0,z1,z2,z3,z729,z6]),(0,[z476,z73,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z730]),(0,[z2,z7,z3,z731,z5,z6]),(0,[z9,z1,z2,z3,z5,z732]),(0,[z0,z1,z2,z3,z6,z733])]],
   [[(0,[z1,z2,z7,z3,z221,z5]),(0,[z0,z1,z2,z734,z5,z6]),(0,[z1,z2,z735,z3,z5,z6]),(0,[z0,z2,z3,z736,z5,z6])],[(0,[z357,z52,z53,z2,z3,z5]),(0,[z0,z2,z3,z5,z6,z737]),(0,[z415,z2,z366,z3,z5,z6]),(0,[z0,z738,z2,z3,z5,z6]),(0,[z0,z1,z2,z739,z3,z5]),(0,[z740,z1,z2,z3,z5,z6])],[(0,[z36,z0,z2,z3,z242,z6])],[(0,[z0,z1,z741,z3,z5,z6]),(0,[z0,z742,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z743,z138])],[(0,[z165,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z744,z3,z5]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z2,z148,z183,z6])],[(0,[z0,z1,z2,z3,z5,z746]),(0,[z37,z165,z1,z3,z72,z6])],[(0,[z33,z0,z2,z575,z5,z6]),(0,[z0,z1,z2,z3,z5,z747]),(0,[z748,z0,z1,z3,z5,z6]),(0,[z24,z0,z2,z3,z5,z110]),(1,[z0,z1,z3,z749,z6]),(0,[z0,z750,z2,z3,z5,z6])],[(0,[z1,z2,z209,z3,z5,z6]),(0,[z9,z751,z2,z3,z5,z6]),(0,[z752,z0,z2,z3,z5,z6]),(0,[z0,z753,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z754]),(0,[z9,z1,z2,z3,z5,z259]),(0,[z0,z2,z34,z487,z5,z6]),(0,[z0,z1,z2,z3,z6,z755])],[(0,[z0,z193,z459,z2,z3,z5]),(0,[z9,z1,z2,z3,z6,z265]),(0,[z0,z1,z3,z5,z756,z102])],[(0,[z74,z0,z2,z3,z5,z6]),(0,[z0,z1,z757,z3,z5,z6]),(0,[z1,z2,z758,z3,z5,z6]),(0,[z0,z1,z2,z201,z3,z5]),(0,[z165,z76,z2,z3,z5,z6]),(0,[z759,z1,z2,z3,z5,z6])],[(0,[z9,z1,z2,z3,z5,z760]),(0,[z9,z1,z589,z3,z5,z6]),(0,[z0,z1,z761,z3,z5,z6])],[(0,[z210,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z762]),(0,[z33,z0,z2,z47,z5,z6]),(0,[z0,z763,z2,z3,z5,z6]),(0,[z0,z764,z2,z3,z5,z6]),(0,[z2,z3,z5,z6,z324,z144]),(0,[z0,z1,z2,z739,z3,z105])],[(0,[z199,z1,z2,z3,z5,z665]),(0,[z14,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z765]),(0,[z0,z1,z2,z532,z43,z6])],[(0,[z0,z1,z766,z3,z5,z6]),(0,[z2,z7,z3,z187,z5,z6]),(0,[z1,z2,z3,z5,z6,z767]),(0,[z143,z1,z2,z609,z3,z5]),(0,[z0,z768,z2,z3,z5,z6])],[(0,[z193,z1,z2,z7,z3,z5]),(0,[z1,z7,z3,z625,z5,z6]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z2,z3,z5,z348]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z1,z2,z3,z5,z771]),(0,[z0,z1,z2,z157,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z772,z6]),(0,[z35,z2,z7,z3,z81,z6]),(0,[z1,z2,z493,z99,z5,z6]),(0,[z1,z2,z7,z3,z5,z259]),(0,[z0,z773,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z774,z6]),(0,[z0,z2,z3,z187,z775,z5]),(0,[z776,z1,z2,z3,z5,z6]),(0,[z140,z1,z2,z3,z5,z103]),(0,[z0,z777,z2,z3,z5,z6])],[(0,[z1,z2,z7,z3,z6,z265]),(0,[z92,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z778]),(0,[z9,z1,z2,z26,z117,z3]),(0,[z54,z1,z2,z513,z5,z6]),(0,[z0,z1,z2,z3,z5,z779]),(0,[z36,z0,z2,z3,z70,z5]),(0,[z0,z1,z2,z3,z105,z412]),(0,[z0,z305,z2,z3,z5,z12])],[(0,[z0,z1,z2,z780,z3,z5]),(0,[z781,z9,z1,z2,z3,z5]),(0,[z0,z1,z2,z623,z31,z5])],[(0,[z98,z0,z2,z47,z5,z6]),(0,[z1,z435,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z782]),(0,[z9,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z5,z783]),(0,[z224,z1,z2,z3,z83,z6]),(0,[z0,z1,z2,z3,z784,z5]),(0,[z0,z2,z785,z3,z5,z6])],[(0,[z1,z2,z786,z3,z5,z6]),(0,[z1,z7,z3,z484,z5,z6]),(0,[z9,z787,z2,z3,z5,z6]),(0,[z9,z2,z3,z187,z5,z6]),(0,[z9,z1,z447,z3,z5,z6]),(0,[z433,z1,z2,z3,z83,z6]),(0,[z36,z0,z2,z3,z788,z6]),(0,[z84,z789,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z90,z756])],[(0,[z619,z73,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z790]),(0,[z9,z1,z256,z3,z5,z6]),(0,[z19,z519,z2,z3,z5,z6]),(0,[z0,z2,z3,z791,z5,z6]),(0,[z0,z1,z2,z157,z38,z6]),(0,[z37,z0,z1,z3,z72,z12])],[(0,[z0,z142,z2,z3,z5,z6]),(0,[z140,z1,z2,z3,z5,z63]),(0,[z0,z1,z2,z792,z3,z5]),(0,[z793,z0,z2,z3,z5,z259]),(1,[z0,z1,z2,z5,z743])],[(0,[z1,z2,z7,z794,z3,z6]),(0,[z19,z1,z2,z3,z364,z6]),(0,[z0,z2,z30,z5,z324,z138])]],
   [[(0,[z0,z1,z2,z3,z795,z6]),(0,[z0,z1,z796,z3,z5,z6]),(0,[z1,z598,z7,z3,z5,z6]),(0,[z255,z1,z2,z128,z5,z6]),(0,[z0,z1,z2,z3,z5,z797]),(0,[z0,z1,z2,z3,z5,z798]),(0,[z0,z16,z2,z3,z5,z200]),(0,[z0,z2,z3,z5,z6,z238])],[(0,[z0,z1,z2,z3,z799,z5]),(0,[z1,z2,z7,z26,z117,z3]),(0,[z781,z0,z86,z2,z3,z5]),(0,[z54,z1,z2,z186,z3,z5]),(0,[z0,z1,z2,z228,z6,z196]),(0,[z0,z800,z2,z3,z5,z6]),(0,[z165,z1,z2,z197,z5,z6]),(0,[z1,z2,z3,z5,z6,z801]),(0,[z802,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z429,z5,z138])],[(0,[z9,z1,z7,z3,z5,z6]),(0,[z16,z177,z7,z3,z5,z6]),(0,[z184,z1,z7,z3,z5,z6]),(0,[z0,z445,z2,z3,z5,z6]),(0,[z0,z803,z2,z3,z5,z6]),(0,[z0,z1,z2,z429,z6,z196])],[(0,[z142,z53,z2,z3,z5,z6]),(0,[z0,z372,z2,z3,z5,z6]),(0,[z1,z108,z7,z3,z38,z6]),(0,[z9,z1,z2,z3,z804,z6]),(0,[z140,z1,z2,z3,z5,z6]),(0,[z224,z1,z2,z3,z83,z398]),(0,[z0,z46,z2,z805,z5,z6]),(0,[z37,z0,z1,z3,z749,z6])],[(0,[z268,z305,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z265])],[(0,[z1,z2,z3,z83,z420,z6]),(0,[z806,z1,z2,z3,z5,z6])],[(0,[z65,z1,z7,z3,z5,z6])],[(0,[z0,z1,z2,z3,z807,z6]),(0,[z1,z615,z7,z3,z5,z6]),(0,[z0,z2,z3,z731,z5,z6]),(0,[z0,z1,z2,z3,z808,z6])]],
   [[(0,[z19,z1,z2,z3,z5,z6]),(0,[z224,z1,z2,z3,z287,z6]),(0,[z0,z809,z2,z3,z5,z6]),(0,[z24,z0,z2,z563,z3,z5]),(1,[z0,z1,z2,z739,z3])],[(0,[z56,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z810,z6]),(0,[z142,z86,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z811]),(0,[z0,z1,z2,z3,z812,z6]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z0,z415,z10,z3,z5,z90])],[(0,[z0,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z813,z3,z6]),(0,[z1,z468,z7,z3,z5,z6]),(0,[z0,z1,z2,z814,z5,z6]),(0,[z1,z2,z815,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z816])],[(0,[z0,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z817]),(0,[z1,z2,z583,z3,z5,z63]),(0,[z9,z1,z2,z3,z5,z341]),(0,[z37,z9,z1,z3,z72,z6]),(0,[z1,z2,z3,z818,z5,z6]),(0,[z0,z819,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z265]),(0,[z0,z445,z2,z3,z31,z5])],[(0,[z649,z1,z2,z3,z5,z185]),(0,[z9,z1,z2,z3,z6,z168]),(0,[z1,z2,z3,z5,z6,z820]),(0,[z65,z0,z1,z3,z5,z102])],[(0,[z1,z48,z7,z60,z5,z6]),(0,[z9,z86,z271,z3,z5,z6]),(0,[z0,z821,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z822,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z33,z0,z2,z805,z5,z6]),(0,[z1,z2,z30,z5,z144,z138])],[(0,[z824,z2,z7,z3,z5,z6]),(0,[z9,z519,z2,z3,z5,z6]),(0,[z825,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z355,z17,z6]),(0,[z826,z1,z2,z3,z5,z6])],[(0,[z9,z35,z2,z3,z81,z6]),(0,[z0,z827,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z828]),(0,[z829,z1,z2,z3,z5,z6]),(0,[z410,z0,z2,z30,z5,z138])]],
   [[(0,[z92,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z364,z6]),(0,[z54,z1,z2,z274,z426,z6]),(0,[z830,z0,z2,z3,z5,z6]),(0,[z0,z1,z709,z60,z5,z6]),(0,[z41,z1,z10,z3,z5,z90])],[(1,[z831,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z832]),(0,[z9,z833,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z2,z3,z5,z835]),(0,[z0,z1,z2,z3,z836,z5])],[(0,[z0,z837,z2,z3,z5,z6]),(0,[z661,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z36,z0,z2,z201,z3,z17]),(0,[z839,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z341]),(0,[z9,z46,z2,z34,z5,z6]),(0,[z0,z1,z2,z3,z840,z6]),(0,[z22,z1,z2,z3,z5,z505]),(0,[z0,z1,z2,z3,z5,z841]),(0,[z41,z415,z2,z3,z5,z6])],[(0,[z357,z9,z1,z2,z3,z5]),(0,[z0,z1,z842,z3,z5,z6]),(0,[z1,z271,z766,z3,z5,z6]),(0,[z54,z1,z2,z818,z5,z6]),(0,[z0,z2,z3,z5,z6,z843]),(0,[z0,z1,z2,z3,z844,z6]),(0,[z0,z519,z2,z3,z326,z6]),(1,[z0,z1,z3,z5,z756]),(0,[z0,z1,z2,z30,z5,z743])],[(0,[z0,z1,z2,z845,z3,z5]),(0,[z9,z1,z80,z3,z5,z6]),(0,[z9,z89,z2,z3,z5,z120]),(0,[z184,z1,z80,z3,z5,z6]),(0,[z0,z846,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z775,z5]),(0,[z0,z2,z3,z5,z6,z847])],[(0,[z0,z1,z2,z3,z848,z6]),(0,[z73,z86,z2,z3,z5,z6]),(0,[z1,z656,z7,z3,z5,z6]),(0,[z0,z519,z2,z3,z5,z332]),(0,[z0,z849,z2,z3,z5,z6])],[(0,[z0,z824,z2,z3,z5,z6]),(0,[z0,z850,z2,z3,z5,z6]),(0,[z0,z1,z851,z3,z5,z6]),(0,[z0,z1,z2,z3,z852,z6]),(1,[z0,z2,z3,z788,z6])]],
   [[(0,[z174,z53,z2,z3,z5,z6]),(0,[z517,z73,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z364,z6]),(0,[z13,z14,z2,z3,z273,z6]),(0,[z853,z1,z2,z3,z5,z6]),(0,[z0,z288,z2,z3,z5,z225]),(0,[z0,z1,z2,z3,z364,z332]),(0,[z0,z1,z2,z3,z5,z854])],[(0,[z9,z1,z2,z3,z5,z6]),(0,[z9,z383,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z855]),(0,[z856,z1,z2,z3,z5,z6])],[(0,[z0,z46,z2,z526,z5,z6]),(0,[z1,z48,z7,z85,z5,z6]),(0,[z36,z0,z2,z3,z412,z6]),(0,[z857,z1,z2,z3,z5,z6]),(0,[z858,z1,z2,z3,z5,z6])],[(0,[z519,z2,z7,z3,z5,z6]),(0,[z859,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z860,z3,z6]),(0,[z0,z861,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z862]),(0,[z0,z1,z2,z3,z43,z398]),(0,[z863,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z105,z103])],[(0,[z1,z7,z562,z3,z5,z6]),(0,[z15,z7,z8,z3,z5,z6]),(0,[z89,z2,z7,z3,z5,z120]),(0,[z0,z864,z2,z3,z5,z6]),(0,[z1,z2,z3,z83,z865,z6]),(0,[z0,z1,z2,z3,z317,z6])],[(0,[z476,z53,z2,z3,z5,z6]),(0,[z0,z866,z2,z3,z5,z6]),(0,[z0,z867,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z868,z6]),(0,[z268,z1,z2,z3,z5,z12]),(0,[z1,z2,z869,z3,z5,z6])],[(0,[z0,z1,z2,z3,z870,z6])],[(0,[z0,z1,z2,z3,z5,z871]),(0,[z362,z0,z8,z3,z5,z6]),(0,[z872,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z326,z6]),(0,[z165,z1,z2,z157,z5,z6]),(0,[z0,z1,z3,z5,z6,z873])]],
   [[(0,[z0,z121,z2,z3,z5,z6]),(0,[z169,z1,z7,z3,z5,z102]),(0,[z9,z1,z2,z42,z6,z196]),(0,[z54,z1,z2,z274,z5,z348]),(0,[z874,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z221,z168]),(0,[z25,z74,z0,z60,z5,z6])],[(0,[z1,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z875]),(0,[z9,z876,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z137]),(0,[z9,z1,z2,z3,z5,z398]),(0,[z0,z1,z2,z3,z5,z332]),(0,[z0,z2,z877,z3,z5,z6])],[(0,[z37,z1,z7,z3,z72,z6]),(0,[z199,z1,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z878]),(0,[z879,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z880,z5,z6]),(0,[z0,z46,z2,z34,z355,z6]),(0,[z0,z881,z2,z3,z5,z6]),(0,[z0,z2,z3,z882,z5,z6])],[(0,[z0,z883,z2,z3,z5,z6]),(0,[z0,z1,z2,z884,z5,z6]),(0,[z24,z0,z2,z3,z5,z235]),(0,[z0,z1,z2,z42,z346,z196]),(0,[z0,z1,z2,z43,z6,z723])],[(0,[z0,z1,z2,z3,z5,z885]),(0,[z0,z1,z886,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z887]),(0,[z0,z1,z2,z6,z723,z196])],[(0,[z0,z1,z2,z3,z426,z348]),(1,[z1,z2,z818,z5,z6]),(0,[z0,z1,z2,z3,z5,z341]),(0,[z888,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z3,z6,z889]),(0,[z1,z7,z3,z49,z5,z6]),(0,[z253,z1,z7,z3,z5,z6]),(0,[z890,z1,z2,z3,z5,z6]),(0,[z891,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z892,z5,z6]),(0,[z1,z2,z3,z5,z6,z893])],[(0,[z54,z1,z2,z274,z5,z342]),(0,[z0,z894,z2,z3,z5,z6]),(0,[z793,z0,z2,z3,z5,z6])]],
   [[(0,[z88,z73,z2,z3,z5,z6]),(0,[z1,z2,z7,z42,z6,z196]),(0,[z372,z2,z7,z3,z5,z6]),(0,[z9,z1,z696,z3,z5,z6]),(0,[z0,z895,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z355,z6]),(0,[z71,z1,z2,z3,z326,z6]),(0,[z0,z1,z2,z3,z5,z896]),(0,[z897,z1,z2,z3,z5,z6]),(0,[z1,z2,z898,z3,z5,z6])],[(0,[z1,z7,z3,z5,z61,z6]),(0,[z1,z7,z588,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z398]),(0,[z899,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z900,z6]),(0,[z1,z2,z901,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z902]),(0,[z0,z1,z55,z3,z5,z6]),(0,[z1,z7,z67,z3,z5,z6]),(0,[z143,z1,z80,z3,z5,z6]),(0,[z71,z1,z2,z3,z5,z332]),(0,[z903,z1,z2,z3,z5,z6]),(0,[z1,z2,z904,z3,z5,z6]),(0,[z41,z2,z104,z3,z5,z6])],[(0,[z582,z53,z2,z3,z5,z6]),(0,[z230,z1,z766,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z200]),(0,[z54,z1,z2,z625,z5,z6]),(0,[z0,z1,z2,z905,z5,z6]),(0,[z207,z0,z8,z3,z5,z6]),(0,[z1,z2,z906,z3,z5,z6]),(0,[z0,z1,z85,z709,z5,z6]),(0,[z0,z76,z2,z3,z5,z341])],[(0,[z9,z1,z417,z3,z5,z6]),(0,[z54,z372,z2,z274,z5,z6]),(0,[z0,z1,z2,z3,z426,z342])],[(0,[z45,z73,z2,z3,z5,z6]),(0,[z86,z2,z7,z3,z5,z6]),(0,[z0,z372,z2,z3,z420,z6]),(0,[z0,z2,z3,z907,z5,z6]),(0,[z0,z1,z2,z3,z43,z259]),(0,[z0,z2,z3,z908,z5,z6]),(0,[z140,z1,z2,z30,z5,z138])],[(0,[z9,z1,z2,z197,z5,z6]),(0,[z410,z0,z2,z3,z5,z90])],[(0,[z25,z9,z1,z60,z5,z6]),(0,[z0,z1,z2,z909,z3,z5]),(0,[z24,z0,z2,z3,z5,z263])]],
   [[(0,[z0,z56,z2,z3,z5,z6]),(0,[z1,z2,z910,z3,z5,z6]),(0,[z33,z0,z2,z3,z5,z200])],[(0,[z0,z831,z2,z3,z5,z6]),(0,[z911,z1,z2,z3,z5,z6]),(0,[z121,z2,z7,z3,z5,z6]),(0,[z1,z702,z7,z3,z5,z6]),(0,[z0,z372,z2,z3,z426,z6]),(0,[z1,z2,z3,z5,z63,z348]),(0,[z0,z1,z2,z3,z5,z912]),(0,[z0,z2,z8,z3,z70,z5]),(0,[z0,z1,z2,z3,z913,z6])],[(0,[z0,z1,z2,z186,z3,z5]),(0,[z0,z1,z2,z3,z914,z6]),(0,[z36,z0,z2,z3,z70,z17]),(0,[z24,z0,z2,z3,z5,z715]),(0,[z25,z0,z187,z60,z5,z6]),(0,[z1,z2,z915,z3,z5,z6])],[(0,[z0,z73,z2,z3,z70,z5]),(0,[z1,z2,z7,z3,z5,z200]),(0,[z0,z1,z2,z3,z5,z916]),(0,[z917,z1,z2,z3,z5,z6]),(0,[z918,z1,z2,z3,z5,z6]),(0,[z71,z1,z2,z3,z364,z6])],[(0,[z0,z193,z1,z2,z3,z5]),(0,[z232,z1,z2,z625,z5,z6]),(0,[z0,z1,z2,z157,z72,z6]),(0,[z0,z919,z2,z3,z5,z6])],[(0,[z0,z1,z2,z707,z3,z5]),(0,[z15,z476,z8,z3,z5,z6]),(0,[z0,z35,z2,z3,z242,z6]),(0,[z0,z920,z2,z3,z5,z6])],[(0,[z1,z2,z7,z197,z5,z6]),(0,[z1,z2,z421,z3,z206,z6]),(0,[z13,z1,z80,z3,z5,z6]),(0,[z0,z2,z3,z805,z5,z6]),(0,[z0,z89,z2,z3,z5,z692]),(0,[z0,z1,z2,z3,z5,z921]),(0,[z425,z0,z1,z3,z5,z102])],[(0,[z0,z2,z922,z3,z5,z6]),(0,[z0,z2,z923,z3,z5,z6]),(0,[z0,z924,z2,z3,z5,z6]),(0,[z1,z2,z186,z82,z3,z5]),(0,[z0,z1,z2,z3,z5,z925]),(0,[z926,z1,z2,z3,z5,z6]),(0,[z0,z46,z2,z34,z221,z5]),(0,[z927,z1,z2,z3,z5,z6])]],
   [[(0,[z9,z1,z2,z148,z43,z6]),(0,[z9,z142,z271,z3,z5,z6]),(0,[z9,z459,z2,z3,z5,z6]),(0,[z116,z1,z80,z3,z5,z6]),(0,[z13,z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z3,z6,z928]),(0,[z36,z0,z2,z3,z17,z6]),(0,[z37,z268,z1,z3,z72,z6])],[(0,[z0,z1,z929,z3,z5,z6]),(0,[z0,z1,z930,z3,z5,z6]),(0,[z931,z1,z2,z3,z5,z6]),(0,[z0,z76,z2,z3,z5,z6]),(0,[z932,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z933]),(0,[z169,z0,z1,z3,z5,z756])],[(0,[z0,z1,z2,z3,z5,z934]),(0,[z24,z9,z2,z3,z5,z267]),(0,[z0,z1,z2,z3,z5,z178]),(0,[z0,z1,z2,z3,z5,z935]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z165,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z197,z5,z341]),(0,[z938,z1,z2,z3,z5,z6]),(0,[z410,z2,z3,z5,z6,z144])],[(0,[z15,z9,z8,z3,z5,z6]),(0,[z25,z0,z1,z60,z5,z332]),(0,[z0,z1,z2,z939,z3,z6]),(0,[z92,z1,z48,z85,z5,z6])],[(0,[z0,z2,z291,z3,z5,z120]),(0,[z940,z0,z2,z3,z5,z6])],[(0,[z941,z1,z2,z7,z3,z5]),(0,[z289,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z221,z5]),(0,[z140,z2,z3,z5,z6,z324])],[(0,[z93,z53,z2,z3,z5,z6]),(0,[z13,z56,z2,z3,z273,z6]),(0,[z0,z1,z942,z3,z5,z6]),(0,[z140,z24,z1,z2,z3,z5]),(0,[z943,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z944,z5,z6]),(0,[z0,z445,z2,z3,z5,z138])],[(0,[z0,z1,z2,z3,z945,z6]),(0,[z1,z493,z7,z60,z5,z6]),(0,[z1,z2,z3,z5,z6,z946]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z948,z1,z2,z3,z5,z6]),(0,[z204,z750,z2,z3,z5,z6]),(0,[z0,z445,z2,z3,z6,z196])]],
   [[(0,[z9,z727,z1,z2,z3,z5]),(0,[z1,z2,z82,z5,z6,z693]),(0,[z0,z2,z34,z518,z5,z6]),(0,[z25,z0,z519,z60,z5,z6])],[(0,[z7,z3,z187,z60,z5,z6]),(0,[z410,z9,z2,z3,z5,z6]),(0,[z0,z719,z2,z3,z5,z6]),(0,[z0,z372,z2,z3,z5,z348]),(0,[z1,z48,z344,z85,z5,z6]),(0,[z949,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z950])],[(0,[z0,z951,z2,z3,z5,z6]),(0,[z24,z0,z2,z3,z5,z324]),(0,[z0,z1,z2,z438,z6,z196]),(0,[z952,z1,z2,z3,z5,z6])],[(0,[z9,z1,z2,z30,z5,z138]),(0,[z0,z727,z86,z2,z3,z5]),(0,[z9,z1,z2,z3,z420,z6]),(0,[z953,z1,z2,z3,z5,z6]),(0,[z0,z954,z2,z3,z5,z6]),(0,[z423,z0,z1,z60,z5,z6]),(0,[z0,z955,z2,z3,z5,z6]),(0,[z0,z1,z2,z42,z259,z196])],[(0,[z0,z1,z2,z3,z5,z956]),(0,[z0,z1,z2,z3,z5,z957]),(0,[z9,z1,z48,z85,z5,z6]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z0,z1,z2,z3,z398,z196]),(0,[z0,z1,z2,z3,z6,z958])],[(0,[z0,z1,z2,z818,z5,z6]),(0,[z0,z1,z2,z418,z31,z5]),(0,[z0,z1,z2,z31,z5,z743])],[(0,[z1,z2,z7,z3,z5,z110]),(0,[z25,z1,z7,z60,z5,z6]),(0,[z255,z1,z7,z60,z5,z6]),(0,[z959,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z960]),(0,[z0,z2,z3,z961,z5,z6]),(0,[z0,z1,z2,z30,z317,z138])],[(0,[z1,z7,z3,z660,z5,z6]),(0,[z9,z1,z2,z3,z426,z6]),(0,[z0,z1,z2,z117,z3,z458]),(0,[z0,z35,z2,z3,z788,z6])]],
   [[(0,[z0,z372,z2,z3,z5,z342]),(0,[z433,z1,z2,z3,z5,z6])],[(0,[z9,z1,z640,z3,z5,z6]),(0,[z0,z1,z962,z3,z5,z6]),(0,[z1,z2,z3,z5,z865,z6]),(0,[z1,z2,z963,z3,z5,z6]),(0,[z964,z1,z2,z3,z5,z6]),(0,[z24,z0,z2,z3,z5,z347])],[(0,[z0,z121,z2,z3,z420,z6]),(0,[z0,z1,z2,z3,z355,z221]),(0,[z0,z1,z2,z3,z5,z965]),(0,[z0,z1,z3,z38,z749,z6])],[(0,[z1,z2,z966,z3,z5,z6]),(0,[z1,z2,z7,z30,z5,z138]),(0,[z1,z2,z7,z3,z420,z6]),(0,[z0,z1,z2,z3,z5,z967]),(0,[z0,z445,z2,z3,z5,z90])],[(0,[z9,z1,z2,z157,z5,z6]),(0,[z169,z9,z1,z3,z5,z102]),(0,[z0,z751,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z21]),(0,[z0,z2,z3,z355,z120,z6]),(0,[z0,z1,z2,z3,z6,z968]),(0,[z0,z969,z2,z3,z5,z6])],[(0,[z451,z1,z7,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z970]),(0,[z971,z0,z1,z2,z3,z5]),(0,[z972,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z355,z110]),(0,[z0,z2,z3,z5,z715,z267]),(0,[z0,z415,z2,z3,z5,z90]),(0,[z0,z1,z2,z3,z5,z259]),(0,[z0,z1,z2,z30,z265,z138])],[(0,[z74,z9,z2,z3,z5,z6]),(0,[z9,z305,z2,z3,z5,z6]),(0,[z476,z142,z2,z3,z5,z6]),(0,[z0,z121,z2,z3,z426,z6]),(0,[z116,z1,z2,z818,z5,z6]),(0,[z22,z1,z2,z3,z5,z63]),(0,[z0,z973,z2,z3,z5,z6]),(0,[z0,z974,z2,z3,z5,z6]),(0,[z0,z975,z2,z3,z5,z6]),(0,[z0,z76,z2,z197,z5,z6]),(0,[z0,z976,z2,z3,z5,z6])],[(0,[z327,z0,z2,z3,z17,z6]),(0,[z1,z7,z60,z5,z6,z196]),(0,[z1,z135,z7,z3,z5,z6]),(0,[z1,z635,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z426,z6]),(0,[z9,z977,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z978]),(0,[z0,z1,z979,z3,z5,z6]),(0,[z0,z1,z2,z345,z6,z196]),(0,[z980,z0,z2,z3,z5,z6]),(0,[z433,z1,z2,z42,z6,z196]),(0,[z0,z981,z2,z3,z242,z5])]],
   [[(0,[z76,z2,z7,z3,z5,z6]),(0,[z33,z9,z2,z47,z5,z6]),(0,[z0,z1,z2,z3,z5,z760]),(0,[z25,z71,z1,z60,z5,z6]),(0,[z0,z1,z3,z709,z5,z6])],[(0,[z0,z2,z3,z5,z120,z110]),(0,[z0,z1,z2,z3,z5,z982]),(0,[z0,z2,z983,z3,z5,z6])],[(0,[z1,z2,z984,z3,z5,z6])],[(0,[z9,z2,z3,z5,z6,z324]),(0,[z1,z80,z3,z5,z63,z6]),(0,[z54,z1,z55,z274,z5,z6]),(0,[z0,z1,z2,z985,z5,z6]),(0,[z1,z2,z18,z3,z5,z178]),(0,[z986,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z157,z5,z6]),(0,[z0,z1,z2,z794,z3,z6]),(0,[z0,z1,z55,z3,z420,z6]),(1,[z1,z2,z3,z865,z6]),(0,[z19,z288,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z987])],[(0,[z9,z1,z2,z3,z5,z346]),(0,[z0,z1,z2,z988,z3,z5])],[(0,[z1,z2,z989,z3,z5,z6]),(0,[z990,z1,z2,z3,z5,z6]),(0,[z0,z991,z2,z3,z5,z6]),(0,[z0,z992,z2,z3,z5,z6]),(0,[z0,z1,z2,z26,z117,z3])],[(0,[z52,z53,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z6,z168]),(0,[z1,z2,z993,z3,z5,z6]),(0,[z0,z1,z2,z148,z6,z723])]],
   [[(0,[z0,z1,z55,z3,z426,z6]),(0,[z994,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z110]),(0,[z0,z1,z995,z3,z5,z6]),(0,[z996,z1,z2,z3,z5,z6]),(0,[z997,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z157,z5,z341]),(0,[z0,z2,z3,z5,z6,z998]),(0,[z999,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z117,z739,z3])],[(0,[z15,z0,z562,z3,z5,z6]),(0,[z0,z787,z2,z3,z5,z6]),(0,[z0,z1,z80,z3,z420,z6]),(0,[z0,z2,z3,z187,z5,z6]),(0,[z0,z2,z34,z3,z5,z200])],[(0,[z9,z1,z396,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1000]),(0,[z1001,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z1002,z3,z6]),(0,[z781,z0,z1,z2,z3,z5])],[(0,[z9,z1,z205,z3,z5,z6]),(0,[z1003,z0,z2,z3,z5,z6]),(0,[z1004,z0,z14,z2,z3,z5]),(0,[z1005,z1,z2,z3,z5,z6]),(0,[z1006,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z503,z117,z3]),(0,[z1,z2,z1007,z3,z5,z6])],[(0,[z52,z86,z2,z3,z5,z6]),(0,[z95,z1,z2,z3,z5,z6]),(0,[z207,z1,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z346]),(0,[z0,z1008,z2,z3,z5,z6])],[(0,[z638,z53,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z342]),(0,[z0,z121,z2,z3,z5,z348]),(0,[z1,z2,z18,z3,z5,z200]),(0,[z19,z1,z2,z3,z5,z225]),(0,[z37,z0,z1,z3,z72,z341])],[(0,[z0,z1,z2,z3,z1009,z6]),(0,[z9,z86,z7,z3,z5,z6]),(1,[z0,z1,z709,z5,z6]),(0,[z0,z1,z2,z3,z265,z138])]],
   [[(0,[z0,z1,z2,z3,z804,z6]),(0,[z0,z1,z2,z3,z5,z1010]),(0,[z1011,z1,z2,z3,z5,z6])],[(0,[z24,z0,z2,z3,z5,z408]),(0,[z9,z1,z10,z3,z5,z90]),(0,[z0,z1012,z2,z3,z5,z6])],[(0,[z142,z2,z7,z3,z5,z6]),(0,[z0,z1,z1013,z3,z5,z6]),(0,[z0,z1,z2,z3,z1014,z5]),(0,[z0,z519,z2,z3,z364,z6])],[(0,[z45,z53,z2,z3,z5,z6]),(0,[z1,z2,z3,z865,z273,z6]),(0,[z1,z2,z1015,z3,z5,z6]),(0,[z1016,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z1017,z5,z6]),(0,[z9,z415,z2,z3,z5,z6]),(0,[z13,z1,z2,z3,z420,z6]),(0,[z0,z1,z2,z3,z5,z1018]),(0,[z1019,z1,z2,z3,z5,z6]),(0,[z165,z305,z2,z3,z5,z6]),(0,[z0,z1,z108,z3,z749,z6])],[(0,[z9,z288,z2,z3,z5,z6]),(0,[z0,z121,z2,z3,z5,z342]),(0,[z0,z1,z2,z805,z5,z6]),(0,[z25,z0,z288,z60,z5,z6]),(0,[z0,z1,z135,z85,z5,z6]),(0,[z0,z1,z2,z621,z5,z138]),(0,[z1,z2,z1020,z3,z5,z6])],[(0,[z0,z1021,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z342]),(0,[z0,z1022,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z1023,z6]),(0,[z1024,z1,z2,z3,z5,z6]),(0,[z0,z1025,z2,z3,z5,z6]),(0,[z84,z1,z108,z3,z38,z6]),(0,[z0,z1,z2,z3,z5,z1026])],[(0,[z9,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z970]),(0,[z1,z2,z3,z5,z6,z1027])]],
   [[(0,[z0,z1,z55,z3,z5,z348]),(0,[z0,z1028,z1,z2,z3,z5]),(0,[z0,z1,z3,z5,z749,z6])],[(0,[z0,z53,z2,z3,z70,z5]),(0,[z1029,z1,z2,z3,z5,z6]),(0,[z45,z86,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z168]),(0,[z0,z1,z2,z3,z5,z1030]),(0,[z1031,z1,z2,z3,z5,z6]),(0,[z0,z2,z1032,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z743])],[(0,[z1,z2,z583,z3,z5,z171]),(0,[z113,z86,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1033]),(0,[z0,z1,z2,z628,z6,z196]),(0,[z1,z2,z3,z5,z6,z1034]),(0,[z1035,z1,z2,z3,z5,z6])],[(0,[z9,z1036,z2,z3,z5,z6]),(0,[z54,z1,z2,z114,z5,z6]),(0,[z1,z2,z3,z5,z63,z489]),(0,[z0,z1037,z2,z3,z5,z6]),(0,[z0,z519,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1038]),(0,[z0,z288,z2,z3,z326,z6])],[(0,[z0,z1,z2,z3,z5,z1039]),(0,[z462,z73,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1040,z398]),(0,[z0,z35,z2,z3,z81,z6]),(0,[z0,z76,z2,z157,z5,z6]),(0,[z0,z1,z2,z3,z1041,z5]),(0,[z0,z1,z2,z5,z743,z6])],[(0,[z0,z1,z2,z3,z1042,z6]),(0,[z9,z1,z271,z3,z5,z6]),(0,[z1,z2,z7,z1043,z3,z5]),(0,[z1,z2,z366,z3,z5,z6]),(0,[z22,z459,z2,z3,z5,z63]),(0,[z0,z288,z2,z3,z5,z332]),(0,[z0,z1,z2,z3,z364,z6])],[(0,[z0,z1044,z2,z3,z5,z6]),(0,[z9,z1045,z2,z3,z5,z6]),(0,[z0,z833,z2,z3,z5,z6]),(0,[z143,z111,z1,z2,z3,z5])],[(0,[z1,z2,z7,z3,z5,z12]),(0,[z9,z1,z2,z3,z5,z225]),(0,[z0,z1,z55,z3,z5,z342]),(0,[z1046,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z81,z6,z674]),(0,[z0,z789,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1047]),(0,[z1,z2,z3,z5,z6,z1048])]],
   [[(0,[z303,z1,z2,z3,z5,z63]),(0,[z0,z46,z2,z34,z5,z6]),(0,[z0,z1049,z2,z3,z5,z6])],[(0,[z24,z0,z2,z3,z612,z5])],[(0,[z831,z1,z2,z3,z5,z6]),(0,[z24,z2,z7,z3,z5,z267]),(0,[z0,z1,z80,z3,z5,z6]),(0,[z9,z1,z2,z3,z70,z5]),(0,[z433,z1,z2,z3,z420,z6]),(0,[z0,z1,z1050,z3,z5,z6]),(0,[z0,z89,z2,z3,z5,z120]),(0,[z1051,z1,z2,z3,z5,z6])],[(0,[z176,z1,z2,z3,z5,z137]),(0,[z0,z1052,z2,z3,z5,z6]),(0,[z1053,z1,z2,z3,z5,z6]),(0,[z0,z1054,z1,z2,z3,z5]),(0,[z0,z1,z2,z278,z117,z3])],[(0,[z73,z831,z2,z3,z5,z6]),(0,[z2,z7,z3,z242,z5,z6]),(0,[z255,z1,z2,z274,z5,z6]),(0,[z0,z1,z2,z3,z865,z6]),(0,[z71,z519,z2,z3,z5,z6]),(0,[z1055,z1,z2,z3,z5,z6])],[(0,[z357,z0,z1,z2,z3,z5]),(0,[z941,z0,z1,z2,z3,z5]),(0,[z1056,z2,z7,z3,z5,z6]),(0,[z1,z2,z493,z82,z5,z6]),(0,[z1057,z1,z2,z3,z5,z6]),(0,[z0,z2,z34,z5,z6,z645]),(0,[z0,z1,z2,z3,z1058,z6]),(0,[z0,z1,z2,z3,z326,z225])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1059]),(0,[z9,z86,z2,z3,z5,z6]),(0,[z1060,z1,z2,z3,z5,z6]),(0,[z0,z383,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1061])],[(0,[z1,z2,z7,z3,z5,z225]),(0,[z592,z0,z2,z47,z5,z6]),(0,[z1062,z1,z2,z3,z5,z6]),(0,[z0,z10,z104,z3,z5,z90])]],
   [[(0,[z52,z831,z2,z3,z5,z6]),(0,[z1,z323,z7,z3,z5,z6]),(0,[z9,z1,z62,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1063]),(0,[z204,z894,z2,z3,z5,z6])],[(0,[z1064,z1,z2,z3,z5,z6]),(0,[z1,z7,z320,z3,z5,z6]),(0,[z410,z2,z7,z3,z5,z6]),(0,[z140,z1,z2,z3,z5,z23]),(0,[z33,z0,z2,z64,z5,z6]),(0,[z0,z2,z34,z805,z5,z6]),(0,[z0,z1,z2,z3,z259,z196])],[(0,[z9,z2,z3,z242,z5,z6]),(0,[z0,z2,z3,z5,z6,z1065]),(0,[z1066,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z85,z364,z6]),(0,[z0,z1,z10,z3,z5,z756]),(0,[z1067,z1,z2,z3,z5,z6])],[(0,[z58,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z889]),(0,[z9,z2,z104,z3,z5,z6]),(0,[z1068,z1,z2,z3,z5,z6]),(0,[z0,z615,z8,z3,z5,z6]),(0,[z1,z2,z1069,z3,z5,z6]),(0,[z0,z1,z2,z1070,z5,z6]),(0,[z0,z1,z629,z3,z5,z90]),(0,[z0,z1,z2,z3,z5,z756])],[(0,[z9,z1,z108,z3,z38,z6]),(0,[z1,z80,z3,z274,z5,z6]),(0,[z25,z0,z1,z60,z326,z6])],[(0,[z0,z1,z2,z3,z6,z1071]),(0,[z0,z35,z2,z3,z384,z6]),(0,[z1,z2,z7,z3,z1072,z6]),(0,[z0,z46,z2,z432,z5,z6]),(0,[z0,z1,z2,z3,z5,z1073]),(0,[z0,z415,z2,z3,z5,z102]),(0,[z0,z1,z2,z42,z6,z196])],[(0,[z184,z1,z2,z227,z5,z6]),(0,[z9,z1074,z2,z3,z5,z6]),(0,[z0,z876,z2,z3,z5,z6]),(0,[z1,z80,z3,z83,z5,z6]),(0,[z0,z1,z2,z3,z5,z398]),(0,[z268,z1,z2,z3,z5,z341])],[(0,[z0,z1,z1075,z3,z5,z6]),(0,[z0,z1,z2,z1043,z3,z5]),(0,[z88,z831,z2,z3,z5,z6]),(0,[z71,z1,z2,z3,z5,z6]),(0,[z0,z1076,z2,z3,z5,z6]),(0,[z0,z1077,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z0,z1,z2,z3,z5,z1079]),(0,[z0,z2,z3,z1080,z5,z6])]],
   [[(0,[z357,z1,z2,z7,z3,z5]),(0,[z9,z1,z2,z126,z31,z5]),(0,[z0,z2,z3,z1081,z5,z6]),(0,[z0,z1,z2,z3,z364,z225])],[(0,[z0,z2,z3,z5,z6,z1040]),(0,[z22,z1,z2,z3,z5,z822]),(0,[z0,z1,z2,z3,z5,z1082])],[(0,[z0,z1,z2,z3,z1083,z5]),(0,[z433,z1084,z2,z3,z5,z6])],[(0,[z476,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z148,z43,z6]),(0,[z9,z1,z2,z3,z708,z6]),(0,[z1,z2,z3,z5,z822,z23]),(0,[z0,z1,z2,z3,z1085,z6]),(0,[z1,z2,z1086,z3,z5,z6])],[(0,[z140,z1,z2,z3,z5,z348]),(0,[z0,z2,z3,z1087,z5,z6]),(1,[z1,z2,z3,z5,z822]),(0,[z0,z1088,z2,z3,z5,z6]),(0,[z0,z1,z2,z126,z5,z743])],[(0,[z866,z2,z7,z3,z5,z6]),(0,[z1,z2,z1089,z3,z5,z6]),(0,[z0,z1,z2,z402,z6,z196])],[(0,[z74,z2,z7,z3,z5,z6]),(0,[z0,z1,z1090,z3,z5,z6]),(0,[z1091,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z5,z6,z1092]),(0,[z0,z1,z2,z3,z5,z1093]),(0,[z1004,z0,z1,z2,z3,z5]),(0,[z0,z89,z2,z3,z5,z715]),(0,[z25,z0,z1,z60,z364,z6]),(0,[z0,z76,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z5,z1094]),(0,[z33,z2,z7,z47,z5,z6]),(0,[z1,z2,z7,z126,z31,z5]),(0,[z224,z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z3,z5,z200]),(0,[z0,z1,z2,z3,z5,z1095]),(0,[z0,z2,z805,z47,z5,z6])],[(0,[z52,z193,z53,z2,z3,z5]),(0,[z0,z1096,z2,z3,z5,z6]),(0,[z1097,z1,z2,z3,z5,z6])],[(0,[z9,z142,z7,z3,z5,z6]),(0,[z0,z1098,z2,z3,z5,z6]),(0,[z0,z16,z2,z3,z70,z5]),(0,[z0,z981,z1,z2,z3,z5])],[(0,[z1,z7,z3,z5,z6,z172]),(0,[z1,z2,z344,z3,z5,z6]),(0,[z0,z1056,z2,z3,z5,z6]),(0,[z0,z1,z2,z1099,z5,z6]),(0,[z0,z1,z2,z197,z5,z6]),(0,[z0,z1100,z2,z3,z5,z6]),(0,[z423,z0,z1,z3,z72,z6])],[(0,[z268,z1,z2,z3,z5,z6]),(0,[z54,z121,z2,z274,z5,z6]),(0,[z1,z2,z1101,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1102])],[(0,[z24,z0,z193,z2,z3,z5]),(0,[z45,z1,z2,z3,z5,z178]),(0,[z0,z1,z2,z3,z6,z1103])],[(0,[z0,z1,z1104,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1105]),(0,[z1106,z1,z2,z3,z5,z6]),(0,[z37,z0,z76,z3,z72,z6]),(0,[z0,z1107,z2,z3,z5,z6]),(0,[z0,z1108,z2,z3,z5,z6])],[(0,[z1,z2,z18,z3,z5,z6]),(0,[z88,z142,z2,z3,z5,z6]),(0,[z140,z1,z2,z117,z3,z5])]],
   [[(0,[z2,z7,z3,z5,z6,z324]),(0,[z1,z7,z3,z5,z6,z387]),(0,[z255,z0,z1,z60,z5,z6]),(0,[z1109,z1,z2,z3,z5,z6]),(0,[z25,z0,z1,z60,z5,z6])],[(0,[z0,z193,z2,z3,z5,z120]),(0,[z0,z1,z2,z3,z5,z1110]),(0,[z0,z2,z148,z43,z242,z6])],[(0,[z0,z1,z2,z3,z1111,z5]),(0,[z1,z2,z421,z3,z83,z6]),(0,[z0,z1112,z2,z3,z5,z6]),(0,[z19,z1,z3,z60,z5,z6]),(0,[z71,z1,z2,z3,z5,z225]),(0,[z1,z2,z1113,z3,z5,z6]),(0,[z268,z76,z2,z3,z5,z6])],[(0,[z0,z1114,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1047,z259])],[(0,[z230,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z1115,z5,z6]),(0,[z477,z1,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z1116,z6]),(0,[z0,z2,z3,z242,z5,z6]),(0,[z1117,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1118])],[(0,[z0,z459,z2,z3,z5,z6]),(0,[z1,z766,z7,z3,z5,z6]),(0,[z223,z1,z2,z3,z287,z6]),(0,[z9,z1,z2,z201,z3,z5]),(0,[z33,z0,z2,z163,z5,z6]),(0,[z0,z46,z2,z34,z5,z110]),(0,[z0,z2,z3,z5,z120,z715]),(0,[z0,z1,z2,z148,z43,z6]),(0,[z0,z383,z2,z148,z43,z6])],[(0,[z24,z0,z2,z3,z202,z5])],[(0,[z1,z7,z3,z5,z6,z401]),(0,[z1,z7,z3,z60,z5,z6]),(0,[z1,z2,z7,z744,z3,z5]),(0,[z0,z89,z2,z3,z5,z324]),(0,[z1119,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1120,z6]),(0,[z1121,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z749,z6])],[(0,[z9,z1,z766,z3,z5,z6]),(0,[z0,z35,z2,z3,z6,z377]),(0,[z0,z445,z2,z26,z3,z5])],[(0,[z9,z1,z2,z3,z5,z348]),(0,[z0,z1122,z2,z3,z5,z6])],[(0,[z54,z1,z80,z274,z5,z6]),(0,[z0,z2,z3,z70,z81,z5]),(0,[z1123,z0,z2,z3,z5,z6])],[(0,[z1,z164,z7,z3,z5,z6]),(0,[z1,z369,z7,z3,z5,z6]),(0,[z0,z1,z2,z1124,z3,z5]),(0,[z0,z1125,z14,z2,z3,z5]),(0,[z15,z0,z8,z3,z5,z6]),(0,[z1126,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z324,z110]),(0,[z0,z1,z2,z3,z5,z715]),(0,[z24,z0,z2,z3,z101,z5]),(0,[z1127,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z105,z238,z103])],[(0,[z632,z1,z7,z3,z5,z6]),(0,[z1,z2,z7,z201,z3,z5]),(0,[z415,z2,z7,z3,z5,z6]),(0,[z0,z727,z1,z2,z3,z5]),(0,[z0,z35,z2,z3,z355,z6]),(0,[z0,z2,z3,z1128,z5,z6]),(0,[z0,z305,z2,z3,z5,z341]),(0,[z169,z210,z1,z3,z5,z102])],[(0,[z0,z1,z2,z1129,z3,z5]),(0,[z73,z222,z2,z3,z5,z6]),(0,[z224,z1,z2,z186,z3,z83]),(0,[z0,z1130,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1131]),(0,[z143,z1,z2,z3,z5,z822]),(0,[z0,z1,z2,z3,z5,z1132]),(0,[z0,z1,z2,z42,z6,z723])]],
   [[(0,[z781,z9,z86,z2,z3,z5]),(0,[z0,z1,z2,z3,z420,z6]),(0,[z0,z1,z80,z3,z426,z6]),(0,[z0,z1133,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z715]),(0,[z0,z1,z2,z30,z5,z138])],[(0,[z9,z142,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1134,z5]),(0,[z0,z1,z48,z85,z5,z6]),(0,[z1135,z1,z2,z3,z5,z6]),(0,[z268,z1,z2,z197,z5,z6]),(0,[z410,z0,z2,z3,z5,z102]),(0,[z1136,z0,z2,z3,z5,z6])],[(0,[z1137,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z348]),(0,[z13,z1,z2,z3,z160,z6]),(0,[z24,z0,z2,z3,z5,z400]),(0,[z0,z1,z2,z26,z3,z643]),(0,[z140,z89,z1,z2,z3,z5]),(0,[z0,z1138,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1139,z3,z5]),(0,[z289,z1,z2,z3,z543,z6]),(0,[z0,z1140,z2,z3,z5,z6]),(0,[z9,z2,z3,z5,z6,z238]),(0,[z0,z1,z2,z3,z5,z960]),(0,[z433,z1108,z2,z3,z5,z6])],[(0,[z288,z2,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z5,z778]),(0,[z0,z1,z2,z3,z426,z6]),(0,[z143,z1,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z822]),(0,[z1141,z0,z1,z2,z3,z5]),(0,[z1142,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z780,z3,z5]),(0,[z1143,z1,z2,z3,z5,z6]),(0,[z9,z445,z2,z3,z5,z6]),(0,[z92,z819,z2,z3,z5,z6]),(0,[z1,z2,z1144,z3,z5,z6])],[(0,[z1,z2,z7,z3,z5,z782]),(0,[z9,z372,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z0,z46,z2,z34,z6,z168]),(0,[z0,z1,z2,z26,z739,z3])],[(0,[z92,z1,z271,z3,z5,z6]),(0,[z0,z2,z8,z3,z5,z200]),(0,[z25,z19,z1,z60,z5,z6]),(0,[z0,z2,z3,z187,z5,z1146]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z0,z445,z2,z3,z105,z103])]],
   [[(0,[z1,z2,z7,z3,z5,z790]),(0,[z0,z1,z2,z3,z1148,z6])],[(0,[z0,z1,z2,z1149,z5,z6]),(0,[z0,z73,z2,z3,z5,z200]),(0,[z711,z1,z2,z7,z5,z6]),(0,[z0,z1,z1150,z3,z5,z6]),(0,[z0,z1,z2,z157,z5,z6]),(0,[z0,z1,z2,z3,z5,z1151])],[(1,[z0,z2,z805,z5,z6]),(0,[z1152,z0,z2,z3,z5,z6]),(0,[z1153,z1,z2,z3,z5,z6]),(0,[z1154,z1,z2,z3,z5,z6])],[(0,[z9,z809,z2,z3,z5,z6]),(0,[z0,z305,z2,z3,z5,z6]),(0,[z1155,z1,z2,z3,z5,z6])],[(0,[z93,z2,z516,z3,z5,z6]),(0,[z0,z977,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z978]),(0,[z0,z1,z2,z3,z573,z103]),(0,[z0,z2,z3,z836,z242,z5])],[(0,[z9,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1156,z6]),(0,[z24,z0,z2,z3,z5,z585]),(0,[z0,z1157,z2,z3,z5,z6]),(0,[z169,z0,z1,z3,z5,z102]),(1,[z0,z1,z2,z6,z723])],[(0,[z0,z1158,z2,z3,z5,z6]),(0,[z9,z32,z2,z3,z5,z6]),(0,[z0,z177,z3,z495,z5,z6]),(0,[z1159,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1160,z3,z5,z6]),(0,[z0,z1,z1161,z3,z5,z6]),(0,[z859,z2,z7,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z348]),(0,[z1162,z1,z2,z3,z5,z6]),(0,[z37,z0,z1,z3,z72,z6]),(0,[z1163,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z739,z3,z103])]],
   [[(0,[z1164,z1,z2,z3,z5,z6]),(0,[z305,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z1002,z3,z6]),(0,[z0,z1,z80,z3,z5,z348]),(0,[z0,z2,z3,z5,z6,z324]),(0,[z0,z1,z2,z60,z364,z6]),(0,[z0,z1,z2,z297,z6,z196]),(0,[z84,z1025,z2,z3,z5,z6]),(0,[z169,z204,z1,z3,z5,z102]),(0,[z0,z1084,z2,z3,z5,z6]),(0,[z0,z1,z2,z26,z679,z3])],[(0,[z9,z1,z541,z3,z5,z6]),(0,[z116,z1,z2,z82,z5,z6]),(0,[z1165,z1,z2,z3,z5,z6]),(0,[z1166,z1,z2,z3,z5,z6]),(0,[z19,z1,z2,z3,z326,z6])],[(0,[z0,z1167,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z788,z6]),(0,[z0,z2,z3,z1168,z5,z6]),(0,[z0,z1,z3,z5,z6,z756]),(0,[z0,z1,z2,z3,z5,z346])],[(0,[z0,z1,z2,z1169,z3,z5]),(0,[z19,z1,z2,z3,z5,z332]),(0,[z1,z2,z3,z5,z6,z1170])],[(0,[z1,z2,z7,z3,z810,z6]),(0,[z1171,z1,z2,z3,z5,z6])],[(0,[z1,z2,z7,z813,z3,z6]),(0,[z0,z1,z2,z3,z5,z1172])],[(0,[z0,z1,z2,z3,z5,z1173]),(0,[z1174,z1,z2,z3,z5,z6])],[(0,[z141,z222,z2,z3,z5,z6]),(0,[z1022,z2,z7,z3,z5,z6]),(0,[z0,z372,z55,z3,z5,z6]),(0,[z0,z1,z80,z3,z5,z342]),(0,[z0,z1175,z2,z3,z5,z6]),(0,[z0,z1,z1176,z3,z5,z6]),(0,[z15,z0,z323,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1177])]],
   [[(0,[z1,z2,z766,z3,z5,z6]),(0,[z2,z7,z104,z3,z5,z6]),(0,[z195,z1,z2,z3,z160,z6]),(0,[z0,z1,z2,z69,z43,z6]),(0,[z0,z1,z2,z3,z1178,z6]),(0,[z0,z1,z2,z1179,z3,z5]),(0,[z1180,z0,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1181]),(0,[z1182,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1017,z5,z6]),(0,[z74,z7,z3,z60,z5,z6]),(0,[z0,z1,z2,z1183,z3,z5]),(0,[z0,z1,z2,z3,z5,z1184]),(0,[z0,z1,z2,z286,z31,z5]),(0,[z0,z288,z2,z3,z364,z6])],[(0,[z0,z1,z2,z3,z1185,z6]),(0,[z33,z0,z2,z3,z70,z5]),(0,[z0,z1,z2,z739,z3,z6])],[(0,[z0,z1,z2,z3,z1186,z6]),(0,[z143,z1,z2,z3,z5,z185]),(0,[z0,z1,z2,z3,z5,z342]),(0,[z0,z1,z2,z3,z5,z1187])],[(0,[z0,z372,z80,z3,z5,z6]),(0,[z0,z2,z3,z788,z17,z6]),(0,[z1188,z1,z2,z3,z5,z6])],[(0,[z1,z7,z3,z495,z5,z6]),(0,[z1,z2,z7,z3,z70,z5]),(0,[z22,z367,z1,z2,z3,z5]),(0,[z22,z0,z445,z2,z3,z5]),(0,[z15,z95,z8,z3,z5,z6])],[(0,[z9,z861,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z105,z103]),(0,[z24,z0,z2,z3,z355,z6]),(0,[z0,z1,z10,z3,z5,z90]),(0,[z0,z445,z2,z3,z5,z102])],[(0,[z9,z1,z293,z3,z5,z6]),(0,[z9,z1,z2,z3,z317,z6]),(0,[z0,z2,z757,z3,z5,z6]),(0,[z268,z1,z2,z157,z5,z6]),(0,[z0,z1,z2,z3,z673,z103])]],
   [[(0,[z84,z1,z2,z3,z5,z6]),(0,[z1137,z1,z48,z3,z5,z6]),(0,[z1,z10,z7,z3,z5,z90]),(0,[z24,z0,z459,z2,z3,z5]),(0,[z1189,z1,z2,z3,z5,z6]),(0,[z0,z35,z2,z3,z130,z6]),(0,[z0,z2,z3,z355,z242,z6]),(0,[z0,z305,z2,z197,z5,z6])],[(0,[z9,z1,z2,z3,z870,z6]),(0,[z0,z415,z2,z3,z5,z6]),(0,[z0,z519,z2,z3,z5,z225]),(0,[z0,z1,z2,z3,z564,z103]),(0,[z140,z410,z2,z3,z5,z6])],[(0,[z9,z1,z2,z3,z326,z6]),(0,[z0,z288,z2,z3,z5,z6]),(0,[z37,z0,z305,z3,z72,z6])],[(0,[z0,z1,z2,z3,z5,z1190]),(0,[z1,z7,z148,z60,z5,z6]),(0,[z0,z1,z2,z3,z1023,z6]),(0,[z9,z121,z2,z3,z5,z6]),(0,[z1,z2,z82,z818,z5,z6]),(0,[z0,z1,z2,z3,z5,z1191]),(0,[z0,z1,z2,z290,z5,z138]),(0,[z0,z1,z2,z158,z43,z6])],[(0,[z1,z80,z7,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z332]),(0,[z92,z1,z55,z3,z5,z6]),(0,[z0,z1,z1192,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1146]),(0,[z0,z1,z2,z3,z5,z12]),(0,[z37,z0,z1,z197,z72,z6]),(0,[z1,z2,z1193,z3,z5,z6])],[(0,[z0,z1194,z2,z3,z5,z6]),(0,[z0,z1,z611,z3,z5,z90])],[(0,[z1,z2,z7,z860,z3,z6]),(0,[z383,z2,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z105,z103]),(0,[z15,z0,z757,z3,z5,z6]),(0,[z1195,z1,z2,z3,z5,z6]),(0,[z1196,z1,z2,z3,z5,z6]),(0,[z0,z1197,z2,z3,z5,z6])],[(0,[z204,z1,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z317,z6]),(0,[z1,z2,z3,z83,z6,z524]),(0,[z13,z1,z2,z3,z273,z6]),(0,[z0,z1125,z1,z2,z3,z5]),(0,[z215,z0,z2,z3,z17,z6]),(0,[z1,z2,z42,z6,z21,z196])]],
   [[(0,[z1,z7,z3,z521,z5,z6]),(0,[z41,z1,z2,z3,z5,z6]),(0,[z0,z1036,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1198,z5]),(0,[z0,z1199,z2,z3,z5,z6]),(0,[z2,z366,z104,z3,z5,z6]),(0,[z0,z1,z2,z620,z31,z5]),(0,[z0,z1,z2,z3,z334,z103])],[(0,[z45,z1,z2,z3,z5,z6]),(0,[z831,z53,z2,z3,z5,z6]),(0,[z298,z1,z7,z3,z5,z6]),(0,[z54,z1,z2,z274,z420,z6]),(0,[z0,z1200,z2,z3,z5,z6]),(0,[z1201,z1,z2,z3,z5,z6]),(0,[z1,z10,z366,z3,z5,z90])],[(0,[z0,z1202,z2,z3,z5,z6]),(0,[z1,z48,z7,z3,z5,z6]),(0,[z1,z2,z7,z3,z326,z6]),(0,[z0,z1,z2,z3,z5,z1203]),(0,[z0,z1,z2,z3,z326,z332]),(0,[z1204,z1,z2,z3,z5,z6])],[(0,[z9,z895,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z355,z6]),(0,[z0,z1045,z2,z3,z5,z6]),(0,[z71,z288,z2,z3,z5,z6]),(0,[z0,z1,z3,z749,z72,z6])],[(0,[z36,z2,z7,z3,z17,z6]),(0,[z1,z2,z7,z3,z5,z332]),(0,[z9,z1,z533,z3,z5,z6]),(0,[z0,z1,z2,z3,z1205,z5]),(0,[z0,z1,z2,z3,z5,z225]),(0,[z0,z1206,z2,z3,z5,z6])],[(0,[z9,z1,z55,z3,z5,z6]),(0,[z0,z1,z2,z1207,z3,z5])],[(0,[z1137,z1,z7,z3,z5,z6]),(0,[z24,z0,z314,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1208])],[(0,[z46,z2,z7,z34,z5,z6]),(0,[z0,z1,z2,z3,z70,z5]),(0,[z1209,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1210]),(0,[z0,z1,z2,z3,z1211,z6])]],
   [[(0,[z1212,z1,z2,z3,z5,z6])],[(0,[z0,z1213,z2,z3,z5,z6]),(0,[z0,z1214,z2,z3,z5,z6]),(0,[z1,z108,z209,z3,z38,z6])],[(0,[z445,z2,z7,z3,z5,z6]),(0,[z0,z1,z2,z3,z1072,z6]),(0,[z9,z1,z2,z909,z3,z5]),(0,[z0,z1,z2,z3,z5,z1215]),(0,[z0,z89,z459,z2,z3,z5]),(0,[z0,z1,z2,z3,z1216,z6]),(0,[z0,z1,z2,z3,z788,z6])],[(0,[z0,z86,z2,z3,z5,z6]),(0,[z1,z2,z7,z3,z355,z6]),(0,[z9,z56,z2,z3,z5,z6]),(0,[z92,z768,z2,z3,z5,z6]),(0,[z0,z1217,z2,z3,z5,z6]),(0,[z1218,z1,z2,z3,z5,z6]),(0,[z1219,z1,z2,z3,z5,z6])],[(0,[z2,z7,z922,z3,z5,z6]),(0,[z0,z1,z48,z325,z5,z6]),(0,[z0,z121,z55,z3,z5,z6]),(0,[z0,z1,z2,z474,z5,z138]),(0,[z1,z2,z3,z5,z6,z1220])],[(0,[z9,z1,z440,z3,z5,z6]),(0,[z1,z337,z7,z3,z5,z6]),(0,[z9,z1,z2,z186,z3,z5]),(0,[z433,z1,z2,z3,z273,z6]),(0,[z830,z0,z2,z3,z5,z398]),(0,[z0,z1,z2,z3,z6,z723])],[(0,[z0,z1,z2,z1221,z5,z6]),(1,[z1,z766,z3,z5,z6]),(0,[z1,z2,z82,z5,z6,z464]),(0,[z0,z35,z2,z3,z349,z6])],[(0,[z9,z193,z1,z2,z3,z5]),(0,[z1140,z2,z7,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z558]),(0,[z36,z9,z2,z3,z17,z6]),(0,[z0,z89,z2,z159,z3,z5])]],
   [[(0,[z0,z2,z104,z3,z5,z6]),(0,[z0,z1,z2,z1222,z3,z6]),(0,[z1223,z1,z2,z3,z5,z6])],[(0,[z0,z121,z80,z3,z5,z6]),(0,[z1224,z1,z2,z3,z5,z6]),(0,[z1225,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1226]),(0,[z0,z1,z108,z3,z38,z6]),(0,[z0,z1,z2,z197,z5,z12])],[(0,[z1,z7,z402,z3,z5,z6]),(0,[z0,z1,z2,z3,z1227,z6]),(0,[z0,z1,z166,z3,z5,z90])],[(0,[z726,z0,z1,z2,z3,z6]),(0,[z0,z1,z1228,z3,z5,z6]),(0,[z1,z7,z3,z5,z406,z6]),(0,[z0,z1074,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1229,z6]),(0,[z143,z0,z445,z2,z3,z5]),(0,[z45,z1,z2,z3,z5,z200]),(0,[z1,z2,z1230,z3,z5,z6]),(0,[z0,z1,z2,z1231,z5,z6])],[(0,[z1,z7,z3,z5,z568,z6]),(0,[z9,z76,z2,z3,z5,z6]),(0,[z0,z757,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1232]),(0,[z0,z2,z3,z81,z788,z6]),(0,[z0,z1,z2,z3,z5,z1233])],[(0,[z1,z2,z1234,z3,z5,z6]),(0,[z1,z2,z7,z186,z3,z5]),(0,[z32,z2,z7,z3,z5,z6]),(0,[z9,z1,z2,z3,z5,z178]),(0,[z0,z1,z2,z3,z1235,z6]),(0,[z0,z1,z2,z126,z31,z5])],[(0,[z0,z1,z1236,z3,z5,z6]),(0,[z0,z1237,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z420,z348]),(0,[z1,z2,z818,z274,z5,z6]),(0,[z1,z2,z3,z5,z63,z822]),(0,[z24,z0,z2,z3,z5,z267]),(0,[z165,z1,z2,z3,z5,z341]),(0,[z0,z305,z2,z157,z5,z6]),(0,[z1,z2,z1238,z3,z5,z6])],[(0,[z0,z53,z2,z3,z5,z200]),(0,[z0,z1,z2,z471,z43,z6]),(0,[z0,z1,z2,z1239,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 225) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1271)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 523, 225] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 94).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 201).take 55).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [94, 107, 55] = true :=
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

end PEqualNP.Outside.L_meta_37029

theorem PEqualNP.Outside.L_meta_37029 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37029.solve