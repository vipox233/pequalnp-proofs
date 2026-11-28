import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38087

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
  Nat.testBit (4278124264 * 2 ^ 32 + 4277075624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20800410a0040944#64 ++ 0x1082001042801025#64 ++ 0x77420c31e24c1fff#64 ++ 0xbddd0830c789307f#64 : BitVec 256),
   (0x0300104640922480#64 ++ 0xa00c004119024892#64 ++ 0xeee430ce65b264ef#64 ++ 0x7bbb90c33996c993#64 : BitVec 256),
   (0x4a00c10b09c28608#64 ++ 0xc12803042c270a18#64 ++ 0xddd9c30f99c3871a#64 ++ 0xf777670c3e670e1c#64 : BitVec 256),
   (0x900e02a016015022#64 ++ 0x0240380a80580540#64 ++ 0xc3fe03f01e03f839#64 ++ 0xef0ff80fc0780fe0#64 : BitVec 256),
   (0x1c0f68001f680033#64 ++ 0x04703da0007da000#64 ++ 0x3fcffc001ffc0007#64 ++ 0xe0ff3ff0007ff000#64 : BitVec 256),
   (0xe02fbffde000003c#64 ++ 0x0780befff7800000#64 ++ 0xffefffffe0000000#64 ++ 0x1fffbfffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x2ec4300005b00007 0x60bb10c00016c000

def z1 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b264ef 0x7bbb90c33996c993

def z2 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffc0007 0xe0ff3ff0007ff000

def z3 : W := mkw 0x20800410a0040944 0x1082001042801025 0x7fc63c31e7fc1fff 0xfdff18f0c79ff07f

def z4 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99c3871a 0xf777670c3e670e1c

def z5 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e03f839 0xef0ff80fc0780fe0

def z6 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0000000 0x1fffbfffff800000

def z7 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e24c1fff 0xbddd0830c789307f

def z8 : W := mkw 0x4800c10909408208 0x4120030424250208 0xd1d9c30198438318 0xe747670c06610e0c

def z9 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0001fc0006 0x00f007f00007f000

def z10 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x88adf3ce00000000 0x0222b7cf38000000

def z11 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0x88bdc3ce1d83e000 0x4222f70f38760f80

def z12 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc2f403f00403f839 0x6f0bd00fc0100fe0

def z13 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xffe63cffe7fe7fff 0xffff98f3ff9ff9ff

def z14 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xfffffff01ffff83f 0xefffffffc07fffe0

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x4342003002001839 0xad0d0800c0080060

def z16 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefe630fe67b27cff 0xffbf98c3f99ec9f3

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2e400c004026029 0x6b0b900300100980

def z18 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1d19c30f99c18712 0x9474670c3e67061c

def z19 : W := mkw 0x980e42a01f415022 0x0260390a807d0540 0xdfffc3f01fc3f83b 0xef7fff0fc07f0fe0

def z20 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x000000001ffc0007 0xe0000000007ff000

def z21 : W := mkw 0x20800410a0040944 0x1082001042801025 0x22020c30620c18e5 0x08880830c1883063

def z22 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xddedf3cf80000000 0x1777b7cf3e000000

def z23 : W := mkw 0x0300000200922480 0xa00c000008024892 0xccc0000e05b264ef 0x733300003816c993

def z24 : W := mkw 0x0300104640922480 0xa00c004119024892 0x88a430ce05b26000 0x422290c33816c980

def z25 : W := mkw 0x20800410a0040944 0x1082001042801025 0x11020c31824c1b10 0x84440830c609306c

def z26 : W := mkw 0xf02e97fdf601502e 0x03c0ba5ff7d80540 0xc3fe03fffe03f839 0xff0ff80ffff80fe0

def z27 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc2fc03c01c03e029 0x6b0bf00f00700f80

def z28 : W := mkw 0x0200104640820400 0x8008004119020810 0xeee430ce6182040a 0x7bbb90c339860810

def z29 : W := mkw 0xb02f3ef4f6015036 0x06c0bcfbd3d80540 0x22263cf066007821 0x088898f3c19801e0

def z30 : W := mkw 0x1000000016015002 0x0040000000580540 0x001000001e03f839 0xe000400000780fe0

def z31 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0x3fcffc0fe0000000 0x10ff3ff03f800000

def z32 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1fff 0xbfffbfffff89307f

def z33 : W := mkw 0x0300104640922480 0xa00c004119024892 0xc02000ce600264e8 0x1b00800339800993

def z34 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0xffeffcce7ffe64ef 0xfbffbff339fff993

def z35 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x111bcf301a4d9810 0x84446f3cc0693660

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x554000018040071a 0xb55500000601001c

def z37 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c3871a 0xe000400000670e1c

def z38 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3c01fc0fe0000000 0x10f007f03f800000

def z39 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe7fe03f07e03fcff 0xff9ff80fc1f80ff3

def z40 : W := mkw 0x0000104440000000 0x0000004111000000 0xeee430ce60000000 0x1bbb90c339800000

def z41 : W := mkw 0x0401280000280011 0x041004a00000a000 0x20003c00003c0004 0x008000f00000f000

def z42 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0xf7fe0ff1fe4fffff 0xffdff83fc7f93fff

def z43 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0x77663cf1e0000000 0x1ddd98f3c7800000

def z44 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xeffe33f01fb3f83f 0xefbff8cfc07ecfe0

def z45 : W := mkw 0x1e0f68021fea0433 0x84783da0087fa810 0xffcffc0e1ffe040f 0xf3ff3ff0387ff810

def z46 : W := mkw 0x0100104440102080 0x2004004111004082 0x222430c0643060e5 0x088890c30190c183

def z47 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80000000 0x1777270c3e000000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x37420c00024c0007 0xa0dd083000093000

def z49 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xc8adf3ffe0000000 0x1f22b7cfff800000

def z50 : W := mkw 0x0800400009400000 0x0020010000250000 0x1dc9c00019c00002 0xe077270000670000

def z51 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x022600f006007821 0x08089803c01801e0

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002001839 0xa000000000080060

def z53 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xddcbcf3f80000000 0x17772f3cfe000000

def z54 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x011a03301a019810 0x8404680cc0680660

def z55 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffe000001 0xffffbffffff80000

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000040071a 0xa00000000001001c

def z57 : W := mkw 0x0800400009400000 0x0020010000250000 0xddd9c30019c3801a 0xe777670c00670e00

def z58 : W := mkw 0x1f0050465ffa2483 0xa07c0141197fe892 0xeee430ce7ffe64ef 0xfbbb90c339fff993

def z59 : W := mkw 0x1000000016015002 0x0040000000580540 0x0000000006007821 0x00000000001801e0

def z60 : W := mkw 0x1300000216937482 0xa04c0000085a4dd2 0x001000001fb3fcff 0xe0004000007ecff3

def z61 : W := mkw 0x2c816c10a96c0955 0x14b205b042a5b025 0x3c01fc01e1fc07c6 0x10f007f00787f01f

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x77420c30024c183f 0xaddd0830c0093060

def z63 : W := mkw 0x0080000000040940 0x1002000000001025 0x00000000020c18e5 0x0000000000083063

def z64 : W := mkw 0xf02fafb9b601503e 0x07c0bebee6d80540 0xd3ffcff19e03f839 0xef4fff3fc6780fe0

def z65 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x82be03f01e03f821 0x4a0af80fc0780fe0

def z66 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3c01fc001ffc0007 0xe0f007f0007ff000

def z67 : W := mkw 0x800e02a000000020 0x0200380a80000000 0xc3ee03f000000000 0x0f0fb80fc0000000

def z68 : W := mkw 0x0300000200922480 0xa00c000008024892 0x0000000005b264ef 0x600000000016c993

def z69 : W := mkw 0x348f2c10b62c0977 0x14d23cb042d8b025 0x22063c30663c18e5 0x088818f0c198f063

def z70 : W := mkw 0x100e000016000022 0x0040380000580000 0x0206000006000001 0x0008180000180000

def z71 : W := mkw 0xea2fffffe9c2863c 0xc7a8bfffffa70a18 0xfffffffff9c3871a 0xffffffffffe70e1c

def z72 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x110bcc001a4c0000 0x80442f3000693000

def z73 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe03f839 0xfffffffffff80fe0

def z74 : W := mkw 0x20000410a0000004 0x0080001042800000 0x40000031e0000000 0x1d000000c7800000

def z75 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3ee03f006007821 0x0f0fb80fc01801e0

def z76 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x88bdf3ce1c03e000 0x4222f7cf38700f80

def z77 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe5b00007 0x7fffbfffff96c000

def z78 : W := mkw 0xa02f2eb0a0000034 0x0680bcbac2800000 0x00020c3000000000 0x00000830c0000000

def z79 : W := mkw 0xfc2ffffdff68003f 0x07f0bffff7fda000 0xffeffffffffc0007 0xffffbffffffff000

def z80 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0xffdbcf3ffbcf9fff 0xffff6f3cffef3e7f

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0xccc0000e00000000 0x1333000038000000

def z82 : W := mkw 0xca2ffbef49c28638 0xc728bfefbd270a18 0x88bdf3ce19838000 0x4222f7cf38660e00

def z83 : W := mkw 0x0200000200828600 0xc008000008020a18 0x0010000000038718 0x0000400000000e1c

def z84 : W := mkw 0x20800410a0040944 0x1082001042801025 0x40000031e0001ff8 0x1d000000c780007f

def z85 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0xdfffc3ff9fc3ff3b 0xff7fff0ffe7f0ffc

def z86 : W := mkw 0x1080000016055942 0x1042000000581565 0x001000001e4fffff 0xe000400000793fff

def z87 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x198ffc001ffc0000 0xc0663ff0007ff000

def z88 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0xeee63cfe60000000 0x1bbb98f3f9800000

def z89 : W := mkw 0x1f0f68021ffa24b3 0xa47c3da0087fe892 0x3fcffc001ffe64ef 0xe0ff3ff0007ff993

def z90 : W := mkw 0x0080000000040940 0x1002000000001025 0x00000000004c07c6 0x000000000001301f

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x66400000600004ef 0x3999000001800013

def z92 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2c00300e61b004c6 0x10b000c03986c013

def z93 : W := mkw 0xa00e06b0a0000024 0x0280381ac2800000 0xf7ee0ff1e0000000 0x1fdfb83fc7800000

def z94 : W := mkw 0x30800410b6055946 0x10c2001042d81565 0x77520c31fe4fffff 0xfddd4830c7f93fff

def z95 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xc010030f80038718 0x1700400c3e000e1c

def z96 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0xffdfff0f9fff871f 0xf7ff7ffc3e7ffe1c

def z97 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3fcffc0001fc0006 0x00ff3ff00007f000

def z98 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0x110bcf3180000000 0x04442f3cc6000000

def z99 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01c03e000 0x4f0ff80fc0700f80

def z100 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0xdfefc3ff80000000 0x1f7fbf0ffe000000

def z101 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xfee5f0cfe5f267ef 0x7bfb97c33f97c99f

def z102 : W := mkw 0x0100104440102080 0x2004004111004082 0x666430c0643064ef 0x399990c30190c193

def z103 : W := mkw 0x4e01e90b09ea8619 0xc53807a42c27aa18 0xfdd9ff0f99ff871e 0xf7f767fc3e67fe1c

def z104 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xbfffffc01fffe007 0xe2ffffff007fff80

def z105 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x001000001fc3ff3b 0xe0004000007f0ffc

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00300001b00006 0x00b000c00006c000

def z107 : W := mkw 0x000f280000000030 0x04003ca000000000 0x3fcffc0000000000 0x00ff3ff000000000

def z108 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xeefdf3ce7db3e4ef 0x7bbbf7cf39f6cf93

def z109 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x5d41c00f81c0071a 0xb57507003e07001c

def z110 : W := mkw 0x910e12e4561170a2 0x2244384b915845c2 0xe3fe33f07e33f8fd 0xef8ff8cfc1f8cfe3

def z111 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0xeffe33fe7fb3fcff 0xffbff8cff9fecff3

def z112 : W := mkw 0x100e000016000022 0x0040380000580000 0x37ce0c001e4c0007 0xe0df383000793000

def z113 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xc02003ffe0000000 0x1f00800fff800000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z115 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffdfff001fff801f 0xe7ff7ffc007ffe00

def z116 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xbfefffce00000000 0x02ffbfff38000000

def z117 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x001000001fff871f 0xe0004000007ffe1c

def z118 : W := mkw 0xbc2f7ef4ff680037 0x06f0bdfbd3fda000 0x3feffcf07ffc0007 0xe8ffbff3c1fff000

def z119 : W := mkw 0x0100104440102080 0x2004004111004082 0x002430c004306000 0x000090c30010c180

def z120 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x332ffff1e0000000 0x0cccbfffc7800000

def z121 : W := mkw 0x20800410a0040944 0x1082001042801025 0x43420031e2001ff9 0xbd0d0800c788007f

def z122 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffffffffe003f838 0x1fffffffff800fe0

def z123 : W := mkw 0x0300104640922480 0xa00c004119024892 0xc2e400ce640264e9 0x7b0b900339900993

def z124 : W := mkw 0x20800410a0040944 0x1082001042801025 0x0000003180001b10 0x04000000c600006c

def z125 : W := mkw 0x800e02a000000020 0x0200380a80000000 0xc3ee03f004026029 0x6f0fb80fc0100980

def z126 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe24c0007 0xbfffbfffff893000

def z127 : W := mkw 0x200f2c10a0000034 0x04803cb042800000 0x7fcffc31e0000000 0x1dff3ff0c7800000

def z128 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xccd9c30e1983840a 0x7333670c38660e10

def z129 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x088df0001db00000 0x402237c00076c000

def z130 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x7fcffc31fffc1fff 0xfdff3ff0c7fff07f

def z131 : W := mkw 0xfcaffffdff6c097f 0x17f2bffff7fdb025 0xffeffffffffc1fff 0xffffbffffffff07f

def z132 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc03003f00003f838 0x0f00c00fc0000fe0

def z133 : W := mkw 0xb02f3ef4f6015036 0x06c0bcfbd3d80540 0xe3fe3ff07e03f839 0xef8ff8ffc1f80fe0

def z134 : W := mkw 0x4800c10909408208 0x4120030424250208 0x1119c30198418310 0x8444670c0661060c

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000180000718 0x150000000600001c

def z136 : W := mkw 0x0300104640922480 0xa00c004119024892 0xcae430ce05b26029 0x6b2b90c33816c980

def z137 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x80bc03c01c03e000 0x4202f00f00700f80

def z138 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3e07fc0007fc0007 0x00f81ff0001ff000

def z139 : W := mkw 0x20800410a0040944 0x1082001042801025 0x76400c01e04c07ef 0x39d900300781301f

def z140 : W := mkw 0x20800410a0040944 0x1082001042801025 0x62020c31e20c1ffd 0x1d880830c788307f

def z141 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x8899c30e19838000 0x4222670c38660e00

def z142 : W := mkw 0xf02fafb9b601503e 0x07c0bebee6d80540 0x111bcf319a019810 0x84446f3cc6680660

def z143 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xddd9c30f80038718 0x1777670c3e000e1c

def z144 : W := mkw 0x6880c519a9448b4c 0x51a2031466a5122d 0x775bcf31fa4d9fff 0xbddd6f3cc7e9367f

def z145 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x7f43fc3fe24c1fff 0xbdfd0ff0ff89307f

def z146 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xfffdf3cffdf3e7ff 0xfffff7cf3ff7cf9f

def z147 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffa019810 0x9fffffffffe80660

def z148 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0x3c01cc0fe1cc07c6 0x10f007303f87301f

def z149 : W := mkw 0x0300000200922480 0xa00c000008024892 0x0000000001b004c6 0x000000000006c013

def z150 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x0002003002001800 0x00000800c0080060

def z151 : W := mkw 0x100e000016000022 0x0040380000580000 0x43ce00301e001839 0xed0f3800c0780060

def z152 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc007ffc04ef 0xf9ff3ff001fff013

def z153 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1c01c00f81c00702 0x107007003e07001c

def z154 : W := mkw 0x4000810900000008 0x0100020424000000 0xc000030f80000000 0x1700000c3e000000

def z155 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd119c30f98438718 0x9744670c3e610e1c

def z156 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x81be03f01e03f810 0xc606f80fc0780fe0

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8030018038018 0xe707600c00600e00

def z158 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3e27fcffe0000000 0x18f89ff3ff800000

def z159 : W := mkw 0x20213c54e0000014 0x048084f153800000 0x20003c0060000000 0x008000f001800000

def z160 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x330ffc001e7c0005 0x80cc3ff00079f000

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x22020c00020c0005 0x0088083000083000

def z162 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9c99c30f99c38702 0x5272670c3e670e1c

def z163 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x37420c001ffc0007 0xe0dd0830007ff000

def z164 : W := mkw 0x0c00400009680001 0x003001000025a000 0x0000000001fc0006 0x000000000007f000

def z165 : W := mkw 0x0300104640922480 0xa00c004119024892 0x0000000e600004c0 0x1000000039800013

def z166 : W := mkw 0x20800410a0040944 0x1082001042801025 0x11020c31824c1fff 0xa4440830c609307f

def z167 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffd9c30ff9c387ff 0xffff670c3fe70e1f

def z168 : W := mkw 0x908e02a016055962 0x1242380a80581565 0xc3fe03f01e4fffff 0xef0ff80fc0793fff

def z169 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfee5fccfe0000000 0x1bfb97f33f800000

def z170 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x22063c00063c0005 0x008818f00018f000

def z171 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xe3fe3ff01e3ff83d 0xef8ff8ffc078ffe0

def z172 : W := mkw 0xe0afafb9a004097c 0x1782bebee6801025 0x110bcf31824c1b10 0x84442f3cc609306c

def z173 : W := mkw 0x60808519a004094c 0x1182021466801025 0xffcbcf3fe24c1fff 0xbfff2f3cff89307f

def z174 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x001000001df3e7ff 0xe00040000077cf9f

def z175 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xddfdf3cf9df3e71a 0xf777f7cf3e77cf9c

def z176 : W := mkw 0x0001280000000010 0x040004a000000000 0x3c01fc0000000000 0x00f007f000000000

def z177 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xeee63cfe67be7cef 0x7bbb98f3f99ef9f3

def z178 : W := mkw 0x4000810900000008 0x0100020424000000 0xddd9c30f98038018 0xf777670c3e600e00

def z179 : W := mkw 0x0100000000102080 0x2004000000004082 0x00000000043060e5 0x000000000010c183

def z180 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01a019810 0x8f0ff80fc0680660

def z181 : W := mkw 0x5c0fe9091f68003b 0x05703fa4247da000 0xffcfff0f9ffc0007 0xf7ff3ffc3e7ff000

def z182 : W := mkw 0x0000104440000000 0x0000004111000000 0x222430c060000000 0x088890c301800000

def z183 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7e60cf1e64e7fff 0xffdf9833c79939ff

def z184 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffefffffe63c0005 0x1fffbfffff98f000

def z185 : W := mkw 0x308e0410b6040966 0x10c2381042d81025 0x77ce0c31fe4c1fff 0xfddf3830c7f9307f

def z186 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x000000001ffe64ef 0xe0000000007ff993

def z187 : W := mkw 0x0f01784649fa2491 0xa43c05e11927e892 0xfee5fcce65fe64ef 0x7bfb97f33997f993

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x2640000000000007 0x2099000000000000

def z189 : W := mkw 0x0300104640922480 0xa00c004119024892 0xc8a430ce65b264e8 0x5b2290c33996c993

def z190 : W := mkw 0x4000914d40000008 0x0100024535000000 0xffedf3cfe0000000 0x1fffb7cf3f800000

def z191 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x88bdf3c01db3e000 0x4222f7cf0076cf80

def z192 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xd12bcfffe0000000 0x1f44af3fff800000

def z193 : W := mkw 0x100e000016015022 0x0040380000580540 0x03de00001e03f839 0xe00f780000780fe0

def z194 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x77520c31fbcf9fff 0xfddd4830c7ef3e7f

def z195 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x3fcffc319ffc1b17 0xe4ff3ff0c67ff06c

def z196 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0x3fcffc0e7ffc04c7 0xf0ff3ff039fff013

def z197 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe04c07c6 0x1fffbfffff81301f

def z198 : W := mkw 0x000f280000000030 0x04003ca000000000 0x3fcffc00024c0007 0xa0ff3ff000093000

def z199 : W := mkw 0x3f8f7c56fffe2df7 0xb4fe3df15bfff8b7 0xffeffcfffffe7fff 0xffffbff3fffff9ff

def z200 : W := mkw 0x28804410a9440944 0x10a2011042a51025 0x7fcbcc31fbcc1fff 0xfdff2f30c7ef307f

def z201 : W := mkw 0x1c8f68001f6c0973 0x14723da0007db025 0x3fcffc001ffc1fff 0xe0ff3ff0007ff07f

def z202 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc13a03f01a03f838 0x8f04e80fc0680fe0

def z203 : W := mkw 0x20000410a0000004 0x0080001042800000 0x77420c31e0000000 0x1ddd0830c7800000

def z204 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3feffcf01ffc7827 0xe8ffbff3c07ff1e0

def z205 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xccd0030f8183871a 0x7733400c3e060e1c

def z206 : W := mkw 0x800e02a000000020 0x0200380a80000000 0xc3ee03f002001839 0xaf0fb80fc0080060

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x5742003182401f3b 0xbd5d0800c609007c

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6e400c0640264ef 0x7b9b900301900993

def z209 : W := mkw 0x0300000200922480 0xa00c000008024892 0xc2e400c005b264ef 0x6b0b90030016c993

def z210 : W := mkw 0xe32fbfffe09224bc 0xa78cbeffff824892 0xffefffffe5b264ef 0x7fffbfffff96c993

def z211 : W := mkw 0x60008519a000000c 0x0180021466800000 0xffcbcf3fe0000000 0x1fff2f3cff800000

def z212 : W := mkw 0x4000810900000008 0x0100020424000000 0x8889c30e00000000 0x0222270c38000000

def z213 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc0bc03f01c03f838 0x4f02f00fc0700fe0

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee430c005b2602f 0x6bbb90c30016c980

def z215 : W := mkw 0xb00e06b0b6015026 0x02c0381ac2d80540 0xf7fe0ff1fe03f839 0xffdff83fc7f80fe0

def z216 : W := mkw 0xfa2fffffffc3d63e 0xc7e8bfffffff0f58 0xffffffffffc3ff3b 0xffffffffffff0ffc

def z217 : W := mkw 0x0300000200922480 0xa00c000008024892 0x00000000000264e8 0x0000000000000993

def z218 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001a4c0000 0x80ff3ff000693000

def z219 : W := mkw 0x4800c10909408208 0x4120030424250208 0xddd9c30f98418310 0x9777670c3e61060c

def z220 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x0801f00001b00000 0x002007c00006c000

def z221 : W := mkw 0x800e02a000000020 0x0200380a80000000 0x80ac03c000000000 0x0202b00f00000000

def z222 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3dc9fc0019fc0006 0xe0f727f00067f000

def z223 : W := mkw 0x7c2ffd5dff68003f 0x05f0bff577fda000 0x3fcffc0ffffc0007 0xf0ff3ff03ffff000

def z224 : W := mkw 0x0080000000040940 0x1002000000001025 0x00000000024c1b10 0x800000000009306c

def z225 : W := mkw 0x0080000000040940 0x1002000000001025 0x37420c00024c1fff 0xa0dd08300009307f

def z226 : W := mkw 0xea2fffffe9c2863c 0xc7a8bfffffa70a18 0xfffffffff9838000 0x5fffffffffe60e00

def z227 : W := mkw 0xc02093ed40000008 0x0300824fb5000000 0x802003ce00000000 0x0200800f38000000

def z228 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0000000001c00702 0x000000000007001c

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x80a400c004026000 0x4202900300100980

def z230 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0x88bc33ce1db3e000 0x4222f0cf3876cf80

def z231 : W := mkw 0xec2ffffde968003d 0x07b0bffff7a5a000 0xffefffffe1fc0006 0x1fffbfffff87f000

def z232 : W := mkw 0x4300914f40922488 0xa10c02453d024892 0xffedf3cfe5b264ef 0x7fffb7cf3f96c993

def z233 : W := mkw 0x6c21fd5de968001d 0x05b087f577a5a000 0x3c01fc0fe1fc0006 0x10f007f03f87f000

def z234 : W := mkw 0xeaafffffe9c68f7c 0xd7aabfffffa71a3d 0xfffffffffbcf9fff 0xffffffffffef3e7f

def z235 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0x3fcfff3180000000 0x04ff3ffcc6000000

def z236 : W := mkw 0xe0afafb9a004097c 0x1782bebee6801025 0x774bcf31e24c1fff 0xbddd2f3cc789307f

def z237 : W := mkw 0x0300104640922480 0xa00c004119024892 0xe66000ce600264ef 0x3b99800339800993

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000018038018 0xe000400000600e00

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x22000000600000e5 0x0888000001800003

def z240 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3d0bff3fe0000000 0x14f42ffcff800000

def z241 : W := mkw 0xe32fbfffe09224bc 0xa78cbeffff824892 0xffefffffe00264e8 0x1fffbfffff800993

def z242 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xf7fe0ff01e4ff83f 0xefdff83fc0793fe0

def z243 : W := mkw 0x4800c10909408208 0x4120030424250208 0x1dd9c30199c18312 0xe477670c0667060c

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x24000000600004c6 0x1090000001800013

def z245 : W := mkw 0x6a21fd5fe9c2861c 0xc5a887f57fa70a18 0xfdd9ff0ff9c3871a 0xf7f767fc3fe70e1c

def z246 : W := mkw 0x0800400009408200 0x4020010000250208 0x0010000018418310 0x800040000061060c

def z247 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1dc9c00f99c00702 0xf07727003e67001c

def z248 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3fdfff301ffd9817 0xe4ff7ffcc07ff660

def z249 : W := mkw 0x0300104640922480 0xa00c004119024892 0x802000ce00026000 0x0200800338000980

def z250 : W := mkw 0x0200000200820400 0x8008000008020810 0xeec0000e618204ef 0x7bbb000039860813

def z251 : W := mkw 0x5a0ec10b1fc2862a 0xc1683b042c7f0a18 0xdfdfc30f9fc3871b 0xf77f7f0c3e7f0e1c

def z252 : W := mkw 0x0300000200922480 0xa00c000008024892 0x6640000065b264ef 0x799900000196c993

def z253 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdffdc3cf9dc3e73b 0xff7ff70f3e770f9c

def z254 : W := mkw 0x6020955de000000c 0x0180825577800000 0x0000000fe0000000 0x100000003f800000

def z255 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019838000 0x4000400000660e00

def z256 : W := mkw 0x20800410a0040944 0x1082001042801025 0x36020c31e24c1fe7 0x18d80830c789307f

def z257 : W := mkw 0x5f0ff94f5ffaa6bb 0xe57c3fe53d7fea9a 0xffffffcfffffe7ff 0xffffffff3fffff9f

def z258 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xf7620cffe24e7fff 0xbfdd8833ff8939ff

def z259 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3ec5fc0005fc0007 0x60fb17f00017f000

def z260 : W := mkw 0xe3afbfffe0962dfc 0xb78ebeffff8258b7 0xffefffffe7fe7fff 0xffffbfffff9ff9ff

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x1540000000400002 0xa055000000010000

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x4342003000000000 0x0d0d0800c0000000

def z263 : W := mkw 0x0200000200820400 0x8008000008020810 0xccc0000e0182040a 0x7333000038060810

def z264 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfdc9ff0fe0000000 0x17f727fc3f800000

def z265 : W := mkw 0x20000410a0000004 0x0080001042800000 0x22020c3060000000 0x08880830c1800000

def z266 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe20c18e5 0x1fffbfffff883063

def z267 : W := mkw 0x0200000200820400 0x8008000008020810 0x8880000e01820000 0x4222000038060800

def z268 : W := mkw 0x100e000016000022 0x0040380000580000 0x03ce00001e000001 0xe00f380000780000

def z269 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xfc21ffffe0000000 0x1ff087ffff800000

def z270 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xddd9c30f9df3e7ff 0xf777670c3e77cf9f

def z271 : W := mkw 0x0080000000040940 0x1002000000001025 0x00000000024c1fff 0xa00000000009307f

def z272 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0x22263cf0063c7825 0x088898f3c018f1e0

def z273 : W := mkw 0xe02e97fde000002c 0x0380ba5ff7800000 0xc3ee03ffe0000000 0x1f0fb80fff800000

def z274 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xccd0000e19c3871a 0xf333400038670e1c

def z275 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xdde9c3ffe0000000 0x1f77a70fff800000

def z276 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xfee43ccfe5fe67ef 0x7bfb90f33f97f99f

def z277 : W := mkw 0x0b00504649d2a680 0xe02c014119274a9a 0xeef430ce7df3e7ff 0xfbbbd0c339f7cf9f

def z278 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xaaaffffe60000000 0x0aaabffff9800000

def z279 : W := mkw 0x1c0040001f695003 0x00700100007da540 0x001000001ffff83f 0xe0004000007fffe0

def z280 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3c01fc0fe04c07c6 0x10f007f03f81301f

def z281 : W := mkw 0x0300104640922480 0xa00c004119024892 0x222430c065b264ef 0x688890c30196c993

def z282 : W := mkw 0x4000810900000008 0x0100020424000000 0x1c01c00f80000000 0x107007003e000000

def z283 : W := mkw 0x4a00d14f49c28608 0xc12803453d270a18 0xfffdf3cff9c3871a 0xfffff7cf3fe70e1c

def z284 : W := mkw 0x1c8040001f6c0943 0x10720100007db025 0x000000001ffc1fff 0xe0000000007ff07f

def z285 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0x22263cf060000000 0x088898f3c1800000

def z286 : W := mkw 0x0300104640922480 0xa00c004119024892 0xec2030ce61b264ee 0x1bb080c33986c993

def z287 : W := mkw 0x000e000000000020 0x0000380000000000 0x03ce000000000000 0x000f380000000000

def z288 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x0801f00e00000000 0x002007c038000000

def z289 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdbcf0f9bcf871f 0xf7ff6f3c3e6f3e1c

def z290 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1b10 0x9fffbfffff89306c

def z291 : W := mkw 0x20800410a0040944 0x1082001042801025 0x00020c30020c1800 0x00000830c0083060

def z292 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0xfdd9cf0ff9cf87de 0xf7f7673c3fe73e1f

def z293 : W := mkw 0x0200000200820400 0x8008000008020810 0xc000000e00020408 0x1300000038000810

def z294 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1da03301a039818 0xe707680cc0680e60

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x5540000180000000 0x1555000006000000

def z296 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x99afffff80000000 0x0666bffffe000000

def z297 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0xd3fe0ff19e4ffb39 0xef4ff83fc6793fec

def z298 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f8040071a 0xb777270c3e01001c

def z299 : W := mkw 0x0200000200820400 0x8008000008020810 0xcee400ce0582642b 0x7b3b900338160990

def z300 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc23603f00603f839 0x0f08d80fc0180fe0

def z301 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0xc3fe03f1fe03fff9 0xff0ff80fc7f80fff

def z302 : W := mkw 0x20800410a0040944 0x1082001042801025 0x40000031e24c1fff 0xbd000000c789307f

def z303 : W := mkw 0x20800410a0040944 0x1082001042801025 0x51020c31e24c1ff8 0x9d440830c789307f

def z304 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9999c30f99c38310 0xc666670c3e670e0c

def z305 : W := mkw 0x9f0f7ae65ffb74b3 0xa67c3deb997fedd2 0xfffffffe7ffffcff 0xfffffffff9fffff3

def z306 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0xeefc33ce7db3e4ef 0x7bbbf0cf39f6cf93

def z307 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc899c30f99838718 0x5722670c3e660e1c

def z308 : W := mkw 0x20800410a0040944 0x1082001042801025 0x34000c01e04c07c6 0x10d000300781301f

def z309 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc301ffc183f 0xedff3ff0c07ff060

def z310 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffe4fffff 0xfffffffffff93fff

def z311 : W := mkw 0x0800400009400000 0x0020010000250000 0x1c01c00001c00002 0x0070070000070000

def z312 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xfffffff01e03f839 0xefffffffc0780fe0

def z313 : W := mkw 0x0f01784649fa2491 0xa43c05e11927e892 0x3c01fc0e61fc04c6 0x10f007f03987f013

def z314 : W := mkw 0x0300104640922480 0xa00c004119024892 0x88a430ce05b264ef 0x622290c33816c993

def z315 : W := mkw 0x0200000200820400 0x8008000008020810 0x0c00000e01800402 0x1030000038060010

def z316 : W := mkw 0x0080000000040940 0x1002000000001025 0x66400000624c1fff 0xb99900000189307f

def z317 : W := mkw 0x9c0e42a01f695023 0x0270390a807da540 0xc3fe03f01ffff83f 0xef0ff80fc07fffe0

def z318 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x088df0001ffc0007 0xe02237c0007ff000

def z319 : W := mkw 0xe02087b9a000000c 0x0380821ee6800000 0x0000033180000000 0x0400000cc6000000

def z320 : W := mkw 0x20800410a0040944 0x1082001042801025 0x53420c31824c1b39 0xad4d0830c609306c

def z321 : W := mkw 0x348f2c10b62c0977 0x14d23cb042d8b025 0x77463c31e67c1fff 0xbddd18f0c799f07f

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x77420c00624c04ef 0xb9dd083001893013

def z323 : W := mkw 0xe82ffffde940003c 0x07a0bffff7a50000 0xffeffffff9c00002 0xffffbfffffe70000

def z324 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x033e03f01e01f831 0x8c0cf80fc07807e0

def z325 : W := mkw 0x23001456e0922484 0xa08c00515b824892 0xffe63cffe5b264ef 0x7fff98f3ff96c993

def z326 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0xc3fe03f01fc3ff3b 0xef0ff80fc07f0ffc

def z327 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xeee433ffe0000000 0x1fbb90cfff800000

def z328 : W := mkw 0x0000104440000000 0x0000004111000000 0xeee430ce600004ef 0x3bbb90c339800013

def z329 : W := mkw 0x830012e640937480 0xa20c004b99024dd2 0xeef433fe65b3fcff 0x7fbbd0cff996cff3

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3fc03c01c03e039 0xef0ff00f00700f80

def z331 : W := mkw 0x000f280000000030 0x04003ca000000000 0x3fcffc0005b00007 0x60ff3ff00016c000

def z332 : W := mkw 0x20800410a0040944 0x1082001042801025 0x00000030600018e0 0x08000000c1800063

def z333 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0xdddbcf3f9bcf9f1a 0xf7776f3cfe6f3e7c

def z334 : W := mkw 0x2c816c10a96c0955 0x14b205b042a5b025 0x7f43fc31e3fc1fff 0xbdfd0ff0c78ff07f

def z335 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0x111a0f319a4d9b10 0x8444683cc669366c

def z336 : W := mkw 0xc20083ab0083d608 0xc308020eac020f58 0xc03003ff8003ff38 0x1f00c00ffe000ffc

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x11020c00024c0000 0x8044083000093000

def z338 : W := mkw 0xdc2ffbed5f68003b 0x0770bfefb57da000 0xbfefffce1ffc0007 0xe2ffbfff387ff000

def z339 : W := mkw 0x20800410a0040944 0x1082001042801025 0x22020c30624c1fff 0xa8880830c189307f

def z340 : W := mkw 0x0000104440000000 0x0000004111000000 0x88a430ce00000000 0x022290c338000000

def z341 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffeffcc01ffe602f 0xebffbff3007ff980

def z342 : W := mkw 0x5c0fe9091f68823b 0x45703fa4247da208 0x111bcf019a4d8310 0x84446f3c0669360c

def z343 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3f43fc0003fc0007 0xa0fd0ff0000ff000

def z344 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffc03e000 0x5ffffffffff00f80

def z345 : W := mkw 0xeb2fffffe9d2a6bc 0xe7acbfffffa74a9a 0xfffffffffdf3e7ff 0xfffffffffff7cf9f

def z346 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce61b004c6 0x1bbb90c33986c013

def z347 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xcbeff3fe00000000 0x0f2fbfcff8000000

def z348 : W := mkw 0xa32f3ef6e09224b4 0xa68cbcfbdb824892 0xeee63cfe65b264ef 0x7bbb98f3f996c993

def z349 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddc9c30f81c00702 0x1777270c3e07001c

def z350 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe040071a 0xbfffbfffff81001c

def z351 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99838000 0x5777670c3e660e00

def z352 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0x7f43cc3fe3cc1fff 0xbdfd0f30ff8f307f

def z353 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffefffffe6007821 0x1fffbfffff9801e0

def z354 : W := mkw 0xfc2ffffdff69503f 0x07f0bffff7fda540 0xfffffffffffff83f 0xffffffffffffffe0

def z355 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc019ffc071f 0xf5ff3ff0067ff01c

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x0118030018018010 0x8404600c00600600

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c8000018000000 0xe007200000600000

def z358 : W := mkw 0xd80ec3a91f41d22a 0x43603b0ea47d0748 0xd3ffc3f19e43fb39 0xef4fff0fc6790fec

def z359 : W := mkw 0x1000000016015002 0x0040000000580540 0x001000001c03e000 0x4000400000700f80

def z360 : W := mkw 0x6321bd5fe092249c 0xa58c86f57f824892 0xfee5fccfe5b264ef 0x7bfb97f33f96c993

def z361 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x3fcffc01fffc07c7 0xf0ff3ff007fff01f

def z362 : W := mkw 0xe0a097fde004094c 0x1382825ff7801025 0xc02003ffe0001ff8 0x1f00800fff80007f

def z363 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbcadffcfe0000000 0x12f2b7ff3f800000

def z364 : W := mkw 0x3c0f6c10bf680037 0x04f03db042fda000 0x7fcffc31fffc0007 0xfdff3ff0c7fff000

def z365 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe4026029 0x7fffbfffff900980

def z366 : W := mkw 0x0200000200820400 0x8008000008020810 0xcdd8030e1983841a 0xf737600c38660e10

def z367 : W := mkw 0x180e40001f400022 0x00603900007d0000 0x1fcfc0001fc00003 0xe07f3f00007f0000

def z368 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0x3c003c0fe1fc07c6 0x10f000f03f87f01f

def z369 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7da0f31fa4f9fff 0xffdf683cc7e93e7f

def z370 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2c00300e65b264ef 0x70b000c03996c993

def z371 : W := mkw 0x4800c10909400008 0x0120030424250000 0xddc9c30f99c00002 0xf777270c3e670000

def z372 : W := mkw 0x0000104440000000 0x0000004111000000 0xeee430ce64026029 0x7bbb90c339900980

def z373 : W := mkw 0x0800400009400000 0x0020010000250000 0x0000000019c00002 0xe000000000670000

def z374 : W := mkw 0x20800410a0040944 0x1082001042801025 0x74000c31e04c1ffe 0x1dd00030c781307f

def z375 : W := mkw 0x4a0fe90b09c28638 0xc5283fa42c270a18 0xffdfff0f99c3871a 0xf7ff7ffc3e670e1c

def z376 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001db00000 0x40ff3ff00076c000

def z377 : W := mkw 0x830e12e6409224a0 0xa20c384b99024892 0xefee33fe65b264ef 0x7fbfb8cff996c993

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x022400c004006021 0x0808900300100180

def z379 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0xbfeffcce1ffe6007 0xe2ffbff3387ff980

def z380 : W := mkw 0x20800410a0040944 0x1082001042801025 0x35020c31e24c1fd6 0x94d40830c789307f

def z381 : W := mkw 0xde0febab1febd63b 0xc7783faeac7faf58 0xffffffff9fffff3f 0xfffffffffe7ffffc

def z382 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b26000 0x5bbb90c33996c980

def z383 : W := mkw 0x000f384440000030 0x04003ce111000000 0xffeffcce60000000 0x1bffbff339800000

def z384 : W := mkw 0x23800412a0962dc4 0xb08e00104a8258b7 0x77420c31e7fe7fff 0xfddd0830c79ff9ff

def z385 : W := mkw 0xe22fbfffe082863c 0xc788beffff820a18 0xffffffffe0038718 0x1fffffffff800e1c

def z386 : W := mkw 0x0000104440000000 0x0000004111000000 0x2c00300e60000000 0x10b000c039800000

def z387 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xe2263fffe0000000 0x1f8898ffff800000

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0xc010030000038018 0x0700400c00000e00

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c0000000020008 0x6303000000000800

def z390 : W := mkw 0xa0af3ef4e0040974 0x1682bcfbd3801025 0x77663cf1e24c1fff 0xbddd98f3c789307f

def z391 : W := mkw 0x20800410a0040944 0x1082001042801025 0x10000c01804c0300 0x004000300601300c

def z392 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3d0bfc001bfc0006 0x80f42ff0006ff000

def z393 : W := mkw 0x800f2aa000000030 0x06003caa80000000 0xffeffff000000000 0x0fffbfffc0000000

def z394 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfdbc33f9bc39f3b 0xff7f6f0cfe6f0e7c

def z395 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0xddd9c33ff9c39ffa 0xff77670cffe70e7f

def z396 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x03de03301e019811 0xe40f780cc0780660

def z397 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeffc33ce7db3e4ff 0xffbff0cf39f6cf93

def z398 : W := mkw 0x800002a000015000 0x0200000a80000540 0x0010033000019810 0x0400400cc0000660

def z399 : W := mkw 0xb42f3ef4f6280037 0x06d0bcfbd3d8a000 0x22263cf0663c0005 0x088898f3c198f000

def z400 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xeeedf3ce60000000 0x1bbbb7cf39800000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x0342000002000001 0xa00d080000080000

def z402 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0x889df30e1db38000 0x422277cc3876ce00

def z403 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x0018030018018000 0x0000600c00600600

def z404 : W := mkw 0xa08e06b0a0040964 0x1282381ac2801025 0xf7ee0ff1e24c1fff 0xbfdfb83fc789307f

def z405 : W := mkw 0xff2ffffffffa24bf 0xa7fcbfffffffe892 0xffeffffffffe64ef 0xffffbffffffff993

def z406 : W := mkw 0xc02faba900000038 0x0700beaea4000000 0x0009c30000000000 0x0000270c00000000

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc0000001800002 0x6033000000060000

def z408 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x13cfcc001e4c0001 0xe04f3f3000793000

def z409 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x011a03301e03f839 0xe404680cc0780fe0

def z410 : W := mkw 0x1e0f68021fea8633 0xc4783da0087faa18 0x3fdffc001fff871f 0xe0ff7ff0007ffe1c

def z411 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2ec4300e65b004c7 0x70bb10c03996c013

def z412 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc1f803f01803f838 0xef07e00fc0600fe0

def z413 : W := mkw 0x802f3ae440000030 0x0600bceb91000000 0x002430c000000000 0x000090c300000000

def z414 : W := mkw 0x100f280016000032 0x04403ca000580000 0x3fcffc001e000001 0xe0ff3ff000780000

def z415 : W := mkw 0x100e000016000022 0x0040380000580000 0x2fce30001fb00007 0xe0bf38c0007ec000

def z416 : W := mkw 0x1c0f78445f680033 0x04703de1117da000 0xffeffcce7ffc0007 0xfbffbff339fff000

def z417 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x001000001bcf9fff 0xe0004000006f3e7f

def z418 : W := mkw 0xe32fbfffe09224bc 0xa78cbeffff824892 0xffefffffe1b004c6 0x1fffbfffff86c013

def z419 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xdfffc3ff9e03f839 0xff7fff0ffe780fe0

def z420 : W := mkw 0x5a00c10b1fc3d60a 0xc16803042c7f0f58 0xddd9c30f9fc3ff3b 0xf777670c3e7f0ffc

def z421 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0xeee630fe67b27cef 0x7bbb98c3f99ec9f3

def z422 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0x8010030e00038000 0x0200400c38000e00

def z423 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0x3c01f00fe1f007c6 0x10f007c03f87c01f

def z424 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xcbfff3fe1e03f839 0xef2fffcff8780fe0

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0x444000000000040a 0x3111000000000010

def z426 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x3fcffc307ffc18e7 0xe8ff3ff0c1fff063

def z427 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffddf30f9df3871f 0xf7ff77cc3e77ce1c

def z428 : W := mkw 0x1d0f78445f7820b3 0x24743de1117de082 0x3feffcc07ffc60e7 0xe8ffbff301fff183

def z429 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe43060e5 0x1fffbfffff90c183

def z430 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x023600f01e03f839 0xe808d803c0780fe0

def z431 : W := mkw 0x7e8fed1bbfee8f7f 0xd5fa3fb46effba3d 0xffdfff3fffff9fff 0xffff7ffcfffffe7f

def z432 : W := mkw 0x0300104640922480 0xa00c004119024892 0xcce000ce618264ea 0x7b33800339860993

def z433 : W := mkw 0x1000000016015002 0x0040000000580540 0xc1d803001e03f839 0xe707600c00780fe0

def z434 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2e2430ce65b064e7 0x18b890c33996c193

def z435 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xc1d8030019c3871a 0xe707600c00670e1c

def z436 : W := mkw 0x100e000016000022 0x0040380000580000 0xc3de03001e038019 0xe70f780c00780e00

def z437 : W := mkw 0x4000810900000008 0x0100020424000000 0x1109c30180000000 0x0444270c06000000

def z438 : W := mkw 0x800e02a000000020 0x0200380a80000000 0x010a033000000000 0x0404280cc0000000

def z439 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x0004300004300000 0x000010c00010c000

def z440 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x1001cc00004c0000 0x0040073000013000

def z441 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0x77660cf1e64c7fff 0xbddd9833c79931ff

def z442 : W := mkw 0x0300000200922480 0xa00c000008024892 0x2ec4300005b264ef 0x60bb10c00016c993

def z443 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffff8038018 0xffffffffffe00e00

def z444 : W := mkw 0x000f280000000030 0x04003ca000000000 0x088df00000000000 0x002237c000000000

def z445 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37420c01e24c07c7 0xb0dd08300789301f

def z446 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2001839 0xbfffbfffff880060

def z447 : W := mkw 0x6280851ba0868f4c 0xd18a02146e821a3d 0xc010033fe0039ff8 0x1f00400cff800e7f

def z448 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x8899c30e19c3871a 0xe222670c38670e1c

def z449 : W := mkw 0x6a21fd5fe9c2861c 0xc5a887f57fa70a18 0x3c01fc0fe1c00702 0x10f007f03f87001c

def z450 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0xffeffff01ffc0007 0xefffbfffc07ff000

def z451 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdcc1c00f81c2070a 0x737307003e07081c

def z452 : W := mkw 0xa08006b0a0055944 0x1282001ac2801565 0xf7720ff1e24fffff 0xbfddc83fc7893fff

def z453 : W := mkw 0x1400000016280003 0x005000000058a000 0x00000000063c0005 0x000000000018f000

def z454 : W := mkw 0xe0a097fde004094c 0x1382825ff7801025 0xf7620fffe24c1fff 0xbfdd883fff89307f

def z455 : W := mkw 0x0080000000040940 0x1002000000001025 0x43420030024c1fff 0xad0d0800c009307f

def z456 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0xeeedf0ce7db264ef 0x7bbbb7c339f6c993

def z457 : W := mkw 0x20801454e0040944 0x1082005153801025 0xffe63cffe24c1fff 0xbfff98f3ff89307f

def z458 : W := mkw 0x1000000016015002 0x0040000000580540 0xc2f400c01e03f839 0xeb0bd00300780fe0

def z459 : W := mkw 0x0080000000040940 0x1002000000001025 0x0000000000001ff8 0x000000000000007f

def z460 : W := mkw 0xd80ec3a91f41d22a 0x43603b0ea47d0748 0x111bc3319a419b10 0x84446f0cc669066c

def z461 : W := mkw 0x800e02a000000020 0x0200380a80000000 0x022600f000000000 0x08089803c0000000

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x2ec4300000000000 0x00bb10c000000000

def z463 : W := mkw 0x0800400009400000 0x0020010000250000 0x0889c00019800000 0x4022270000660000

def z464 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc03003f01e03f839 0xef00c00fc0780fe0

def z465 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaee430ce05b26007 0x62bb90c33816c980

def z466 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe00004ef 0x3fffbfffff800013

def z467 : W := mkw 0x20800410a0040944 0x1082001042801025 0x75400c01e04c07de 0xb5d500300781301f

def z468 : W := mkw 0x0100104440102080 0x2004004111004082 0xeee430ce643060e5 0x1bbb90c33990c183

def z469 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37420c31824c1b17 0xa4dd0830c609306c

def z470 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xc02000ffe0027ff8 0x1f008003ff8009ff

def z471 : W := mkw 0xfa8ec7bbbfc7df6e 0xd3ea3b1eeeff1f7d 0xffffcfffffcfffff 0xffffff3fffff3fff

def z472 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0x775a0f31fa4d9fff 0xbddd683cc7e9367f

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1c8030000000000 0x0707200c00000000

def z474 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe0001ff8 0x1fffbfffff80007f

def z475 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x1dd9c00019c3871a 0xe077670000670e1c

def z476 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0xcbffc3fe1f83f839 0xef2fff0ff87e0fe0

def z477 : W := mkw 0x1c0e40001f680023 0x00703900007da000 0x03ce00001ffc0007 0xe00f3800007ff000

def z478 : W := mkw 0x100e000016000022 0x0040380000580000 0x010a00001a000000 0x8004280000680000

def z479 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x5550000199c3871a 0xf555400006670e1c

def z480 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc010030f99c3871a 0xf700400c3e670e1c

def z481 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce600264e8 0x1bbb90c339800993

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000024c0007 0xa000000000093000

def z483 : W := mkw 0x900e02a016000022 0x0240380a80580000 0xc3ee03f01e000001 0xef0fb80fc0780000

def z484 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x002400c004006000 0x0000900300100180

def z485 : W := mkw 0xea20d7ffe9c2860c 0xc3a8835fffa70a18 0xddf9c3fff9c3871a 0xff77e70fffe70e1c

def z486 : W := mkw 0x0200000200820400 0x8008000008020810 0xeec4300e05b2040f 0x73bb10c03816c810

def z487 : W := mkw 0x800002a000000000 0x0200000a80000000 0xc02003f000000000 0x0f00800fc0000000

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400000180400702 0x105000000601001c

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3da03301a039839 0xef0f680cc0680e60

def z490 : W := mkw 0x0100104440102080 0x2004004111004082 0x002000c0600060e0 0x0800800301800183

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x4240000000000029 0x2909000000000000

def z492 : W := mkw 0x130e1046569224a2 0xa04c3841195a4892 0xefee30ce7fb264ef 0xfbbfb8c339fec993

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000005b00007 0x600000000016c000

def z494 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0xcbfe33fe1fb3f839 0xef2ff8cff87ecfe0

def z495 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0x774bcf31e0000000 0x1ddd2f3cc7800000

def z496 : W := mkw 0x20000410a0000004 0x0080001042800000 0x77420c31e00004ef 0x3ddd0830c7800013

def z497 : W := mkw 0x030f3846409224b0 0xa40c3ce119024892 0xffeffcce65b264ef 0x7bffbff33996c993

def z498 : W := mkw 0xe32097ffe092248c 0xa38c825fff824892 0xeee433ffe5b264ef 0x7fbb90cfff96c993

def z499 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xd7fe03f19e43ff3b 0xff5ff80fc6790ffc

def z500 : W := mkw 0xe82fefb9a940823c 0x47a0bfbee6a50208 0x111bcf3198418310 0x84446f3cc661060c

def z501 : W := mkw 0x20000410a0000004 0x0080001042800000 0x77420c31e2001839 0xbddd0830c7880060

def z502 : W := mkw 0x0000000000015000 0x0000000000000540 0x001000000003f838 0x0000400000000fe0

def z503 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x0009c00018000000 0x0000270000600000

def z504 : W := mkw 0x150f3844563820b3 0x24543ce11158e082 0x22263cc0663c60e5 0x088898f30198f183

def z505 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x00020c00020c0000 0x0000083000083000

def z506 : W := mkw 0x1000000016015002 0x0040000000580540 0x435200301e03f839 0xed0d4800c0780fe0

def z507 : W := mkw 0xf32fbffff69374be 0xa7ccbeffffda4dd2 0xffffffffffb3fcff 0xfffffffffffecff3

def z508 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xfdd9f30ff9f387de 0xf7f767cc3fe7ce1f

def z509 : W := mkw 0xfe2fffffffea863f 0xc7f8bfffffffaa18 0xffffffffffff871f 0xfffffffffffffe1c

def z510 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2ecdf0001db00007 0x60bb37c00076c000

def z511 : W := mkw 0xfc2fefb9bf68003f 0x07f0bfbee6fda000 0x3fcfff319ffc0007 0xe4ff3ffcc67ff000

def z512 : W := mkw 0x20000410a0000004 0x0080001042800000 0x77420c31e24c0007 0xbddd0830c7893000

def z513 : W := mkw 0xca0ec3ab09c28628 0xc3283b0eac270a18 0xdfffc3ff99c3871a 0xff7fff0ffe670e1c

def z514 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x2ec63c0007bc0007 0x60bb18f0001ef000

def z515 : W := mkw 0x21801454e01429c4 0x30860051538050a7 0x22263cf0663c78e5 0x088898f3c198f1e3

def z516 : W := mkw 0x3c804410bf6c0947 0x10f2011042fdb025 0x77420c31fffc1fff 0xfddd0830c7fff07f

def z517 : W := mkw 0x000f280000000030 0x04003ca000000000 0x22063c0000000000 0x008818f000000000

def z518 : W := mkw 0x0800400009400000 0x0020010000250000 0x1109c00018400000 0x8044270000610000

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fc63c0007fc0007 0xe0ff18f0001ff000

def z520 : W := mkw 0x0200000200820400 0x8008000008020810 0x000000000182040a 0x6000000000060810

def z521 : W := mkw 0x6021ad19a000001c 0x058086b466800000 0x1001cc0180000000 0x0040073006000000

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000600004e8 0x1900000001800013

def z523 : W := mkw 0x0300104640922480 0xa00c004119024892 0xc02000ce65b264ef 0x7b0080033996c993

def z524 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0x3fdffc001ffff83f 0xe0ff7ff0007fffe0

def z525 : W := mkw 0x0800400009400000 0x0020010000250000 0x3fcdf0001df00007 0xe0ff37c00077c000

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0xd5d803019843871a 0xf757600c06610e1c

def z527 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x435a03301a019839 0xad0d680cc0680660

def z528 : W := mkw 0x170f384656ba24b3 0xa45c3ce1195ae892 0xeee63cce67be64ef 0x7bbb98f3399ef993

def z529 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x23ce3c001e3c0005 0xe08f38f00078f000

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x0202003002001821 0x08080800c0080060

def z531 : W := mkw 0xbc8f6eb0bf6d5977 0x16f23dbac2fdb565 0xfffffff1ffffffff 0xffffffffc7ffffff

def z532 : W := mkw 0x800e02a000015020 0x0200380a80000540 0xc3fe03f00003f838 0x0f0ff80fc0000fe0

def z533 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e20c18e5 0x1ddd0830c7883063

def z534 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0x0000000f80000700 0x100000003e00001c

def z535 : W := mkw 0xe02097fde001500c 0x0380825ff7800540 0xc03003ffe003f838 0x1f00c00fff800fe0

def z536 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaaa430ce65b260e5 0x4aaa90c33996c983

def z537 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2a8ffc001fbc0005 0x40aa3ff0007ef000

def z538 : W := mkw 0xa0af3ef4e0040974 0x1682bcfbd3801025 0x22263cf0620c18e5 0x088898f3c1883063

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x0102003002001810 0x84040800c0080060

def z540 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe63cce67fe64ef 0xfbff98f3399ff993

def z541 : W := mkw 0x0000104440000000 0x0000004111000000 0xc02000ce60000000 0x1b00800339800000

def z542 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7f43fc3fe0000000 0x1dfd0ff0ff800000

def z543 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x000000001a4c0000 0x8000000000693000

def z544 : W := mkw 0x800e02a000000020 0x0200380a80000000 0xc3fe03f018038018 0xef0ff80fc0600e00

def z545 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0xeee430ffe5b27fff 0x7fbb90c3ff96c9ff

def z546 : W := mkw 0x920e02a216835422 0x8248380a885a0d50 0xcffe03fe1f83fc3b 0xff3ff80ff87e0ff0

def z547 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xc1d8030f98038718 0xf707600c3e600e1c

def z548 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x1dc9c0001ffc0007 0xe0772700007ff000

def z549 : W := mkw 0x0080000000040940 0x1002000000001025 0x55400001824c1fff 0xb55500000609307f

def z550 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x2ec430001ffc0007 0xe0bb10c0007ff000

def z551 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xcbfff3f01fb3f839 0xef2fffcfc07ecfe0

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x2204300004300005 0x008810c00010c000

def z553 : W := mkw 0x20000410a0000004 0x0080001042800000 0x34000c01e0000000 0x10d0003007800000

def z554 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0xe3fe0ff07e0ff8fd 0xef8ff83fc1f83fe3

def z555 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xd550030f8043871a 0xb755400c3e010e1c

def z556 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaca430ce65b264c6 0x52b290c33996c993

def z557 : W := mkw 0x6b80d55fe9d6afcc 0xf1ae03557fa75abf 0xffffffffffffffff 0xffffffffffffffff

def z558 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc2e600f006027829 0x6b0b9803c01809e0

def z559 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc9d9c30e19838018 0xe727670c38660e00

def z560 : W := mkw 0x4800c10909408208 0x4120030424250208 0x0019c30018018000 0x0000670c00600600

def z561 : W := mkw 0x830012e640937480 0xa20c004b99024dd2 0xc03003fe6003fcf8 0x1f00c00ff9800ff3

def z562 : W := mkw 0xb38e16f6f6977de6 0xb2ce385bdbda5df7 0xfffe3fffffffffff 0xfffff8ffffffffff

def z563 : W := mkw 0xe32fbfffe09224bc 0xa78cbeffff824892 0xffefffffe5b26000 0x5fffbfffff96c980

def z564 : W := mkw 0xa08006b0a0055944 0x1282001ac2801565 0xc03003f1e003fff8 0x1f00c00fc7800fff

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0x34000c00004c0006 0x00d0003000013000

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0xc02000c000026028 0x0b00800300000980

def z567 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1fc03c01c03e018 0xe707f00f00700f80

def z568 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x37463c00067c0007 0xa0dd18f00019f000

def z569 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x22063c001ffc0007 0xe08818f0007ff000

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x4140000000000018 0xa505000000000000

def z571 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1c11c00f99c3871a 0xf07047003e670e1c

def z572 : W := mkw 0xc32fbbef409224b8 0xa70cbeefbd024892 0x88adf3ce05b26000 0x4222b7cf3816c980

def z573 : W := mkw 0x0200000200820400 0x8008000008020810 0xddc0000f81c2071a 0xf77700003e07081c

def z574 : W := mkw 0x6a00c51ba9c2860c 0xc1a803146ea70a18 0xffdbcf3ff9c3871a 0xffff6f3cffe70e1c

def z575 : W := mkw 0x080f680009400030 0x04203da000250000 0x3fcffc0019c00002 0xe0ff3ff000670000

def z576 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0xddfdc3cf9dc3e71a 0xf777f70f3e770f9c

def z577 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x03ee00f01e007821 0xe80fb803c07801e0

def z578 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0x3feffcf060000000 0x08ffbff3c1800000

def z579 : W := mkw 0x400fa90900000038 0x05003ea424000000 0xffcfff0f80000000 0x17ff3ffc3e000000

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dc9c00000000000 0x0077270000000000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x77420c01824c071f 0xb5dd08300609301c

def z582 : W := mkw 0x800002a000015000 0x0200000a80000540 0x002000f000007820 0x08008003c00001e0

def z583 : W := mkw 0x20000410a0000004 0x0080001042800000 0x77420c31e040071a 0xbddd0830c781001c

def z584 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0x7f423c3fe3fc1fff 0xbdfd08f0ff8ff07f

def z585 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0x22260cf0660c78e5 0x08889833c19831e3

def z586 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xd3efcff180000000 0x0f4fbf3fc6000000

def z587 : W := mkw 0x0800400009400000 0x0020010000250000 0x3fcbcc001bcc0007 0xe0ff2f30006f3000

def z588 : W := mkw 0x20800410a0040944 0x1082001042801025 0x63420c30620c18fd 0xad8d0830c1883063

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3e600f006027839 0xef0f9803c01809e0

def z590 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x83fe03c01e03e001 0xe20ff80f00780f80

def z591 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0x3fcffc0f9ffc0707 0xf0ff3ff03e7ff01c

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000004ef 0x2000000000000013

def z593 : W := mkw 0xca2ffbef49c28638 0xc728bfefbd270a18 0xddfdf3cf99c3871a 0xf777f7cf3e670e1c

def z594 : W := mkw 0x5c0fe9091f68823b 0x45703fa4247da208 0x3fdfff019ffd8317 0xe4ff7ffc067ff60c

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x6742003062001cff 0xbd9d0800c1880073

def z596 : W := mkw 0x800002a000015000 0x0200000a80000540 0x803003c00003e000 0x0200c00f00000f80

def z597 : W := mkw 0x0300104640922480 0xa00c004119024892 0xecc0300e61b204ce 0x73b300c03986c813

def z598 : W := mkw 0x4000810900008208 0x4100020424000208 0x0010030180018310 0x0400400c0600060c

def z599 : W := mkw 0xe22fbfffe082043c 0x8788beffff820810 0xffefffffe182040a 0x7fffbfffff860810

def z600 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x1dcbcc001bcc0002 0xe0772f30006f3000

def z601 : W := mkw 0x4a80c10b09c68f48 0xd12a03042c271a3d 0xddd9c30f9bcf9fff 0xf777670c3e6f3e7f

def z602 : W := mkw 0x4300914f4092a688 0xe10c02453d024a9a 0xc03003cfe003e7f8 0x1f00c00f3f800f9f

def z603 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0x88bdf3ce1db3e000 0x4222f7cf3876cf80

def z604 : W := mkw 0x0a00400209c20400 0x8028010008270810 0xddc9c00e19c2040a 0xf377270038670810

def z605 : W := mkw 0x0b00504649d22480 0xa02c014119274892 0xffedf0ce7df264ef 0xfbffb7c339f7c993

def z606 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x1dcdf0001df00002 0xe07737c00077c000

def z607 : W := mkw 0x20800410a0040944 0x1082001042801025 0x66400031e0001fff 0x3d990000c780007f

def z608 : W := mkw 0x20800410a0040944 0x1082001042801025 0x55420c31824c1f1a 0xb5550830c609307c

def z609 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e0001ff8 0x1ddd0830c780007f

def z610 : W := mkw 0x0380104640962dc0 0xb00e0041190258b7 0xeee430ce67fe7fff 0xfbbb90c3399ff9ff

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2e400c000000000 0x0b0b900300000000

def z612 : W := mkw 0xe32097ffe092248c 0xa38c825fff824892 0xc02003ffe00264e8 0x1f00800fff800993

def z613 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0x88adf0ce1db26000 0x4222b7c33876c980

def z614 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3c8dfc001dfc0006 0x40f237f00077f000

def z615 : W := mkw 0x6880c519a9448b4c 0x51a2031466a5122d 0x111bcf319a4d9b10 0x84446f3cc669366c

def z616 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e04c07c6 0x1ddd0830c781301f

def z617 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0xdddbcf0f9bcf871a 0xf7776f3c3e6f3e1c

def z618 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e24c1b10 0x9ddd0830c789306c

def z619 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x0801c00e01800000 0x0020070038060000

def z620 : W := mkw 0xfc2fefb9bf68003f 0x07f0bfbee6fda000 0x110bcf319a4c0000 0x84442f3cc6693000

def z621 : W := mkw 0x6280851ba0868f4c 0xd18a02146e821a3d 0xf7520f3fe24f9fff 0xbfdd483cff893e7f

def z622 : W := mkw 0xc32fbbef409224b8 0xa70cbeefbd024892 0xeeedf3ce65b264ef 0x7bbbb7cf3996c993

def z623 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x3fcffc00063c0005 0x00ff3ff00018f000

def z624 : W := mkw 0x208f2c10a0040974 0x14823cb042801025 0x7fcffc31e24c1fff 0xbdff3ff0c789307f

def z625 : W := mkw 0x20800410a0040944 0x1082001042801025 0x00000001e00007c0 0x100000000780001f

def z626 : W := mkw 0x100e000016000022 0x0040380000580000 0x008c00001c000000 0x4002300000700000

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x77400001e04007ff 0xbddd00000781001f

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004026029 0x6000000000100980

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000003000001838 0x0d000000c0000060

def z630 : W := mkw 0x0380000200962dc0 0xb00e0000080258b7 0x0000000007fe7fff 0xe0000000001ff9ff

def z631 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x374bcc001a4c0007 0xa0dd2f3000693000

def z632 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xd3ffcff01e4ff839 0xef4fff3fc0793fe0

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x1100000180400310 0x844400000601000c

def z634 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe430cfe5f267ff 0xffff90c33f97c99f

def z635 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x110bcc001ffc0007 0xe0442f30007ff000

def z636 : W := mkw 0x4200810b00820408 0x810802042c020810 0xddc9c30f8182040a 0x7777270c3e060810

def z637 : W := mkw 0x000f280000000030 0x04003ca000000000 0x110bcc0000000000 0x00442f3000000000

def z638 : W := mkw 0x0800400009400000 0x0020010000250000 0x5dc9c00199c0071a 0xf57727000667001c

def z639 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9dd9c30e19c38002 0xe277670c38670e00

def z640 : W := mkw 0xe22097ffe082860c 0xc388825fff820a18 0xc03003ffe0038718 0x1f00c00fff800e1c

def z641 : W := mkw 0x0300104640922480 0xa00c004119024892 0xe22430ce643264ed 0x1b8890c33990c993

def z642 : W := mkw 0x0100104440102080 0x2004004111004082 0xe2e430c0643260ed 0x6b8b90c30190c983

def z643 : W := mkw 0x930e02a2169374a2 0xa24c380a885a4dd2 0xc3fe03f01fb3fcff 0xef0ff80fc07ecff3

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0x6640000060000000 0x1999000001800000

def z645 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0xbfdfff0e1fff8007 0xe2ff7ffc387ffe00

def z646 : W := mkw 0x1c0040001f680003 0x00700100007da000 0x000000001db00000 0x400000000076c000

def z647 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37420c30624c18e7 0xa8dd0830c1893063

def z648 : W := mkw 0xa12f3ef4e01020b4 0x2684bcfbd3804082 0x22263cf0643060e5 0x088898f3c190c183

def z649 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x80bc03c01e03f839 0xe202f00f00780fe0

def z650 : W := mkw 0x900e12e456015022 0x0240384b91580540 0xeffe33fe7e03f839 0xffbff8cff9f80fe0

def z651 : W := mkw 0xea2fffffe9c2863c 0xc7a8bfffffa70a18 0xffefffffe1c00702 0x1fffbfffff87001c

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x37420c0000000000 0x00dd083000000000

def z653 : W := mkw 0x20000410a0000004 0x0080001042800000 0x11020c3180000000 0x04440830c6000000

def z654 : W := mkw 0x5e0fe90b1fea863b 0xc5783fa42c7faa18 0xddddf30f9df3871a 0xf77777cc3e77ce1c

def z655 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0xc3fe03fe7e03fcf9 0xff0ff80ff9f80ff3

def z656 : W := mkw 0x22800412a0860d44 0x908a00104a821835 0xffc20c3fe3ce1fff 0xffff0830ff8f387f

def z657 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x774bcc31fa4c1fff 0xbddd2f30c7e9307f

def z658 : W := mkw 0x0100104440102080 0x2004004111004082 0x20003000603000c4 0x008000c00180c003

def z659 : W := mkw 0xe82ffffde940823c 0x47a0bffff7a50208 0xfffffffff8418310 0x9fffffffffe1060c

def z660 : W := mkw 0xea2fefbba9c2863c 0xc7a8bfbeeea70a18 0xdddbcf3f99c3871a 0xf7776f3cfe670e1c

def z661 : W := mkw 0x0100104440102080 0x2004004111004082 0x2ee430c065b060e7 0x68bb90c30196c183

def z662 : W := mkw 0x5e00c10b1fea860b 0xc17803042c7faa18 0xddd9c30f9fff871f 0xf777670c3e7ffe1c

def z663 : W := mkw 0x4e01e90b09ea8619 0xc53807a42c27aa18 0x3c01fc0f81fc0706 0x10f007f03e07f01c

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x02c4000004000001 0x600b100000100000

def z665 : W := mkw 0x20001454e0000004 0x0080005153800000 0xffe63cffe0000000 0x1fff98f3ff800000

def z666 : W := mkw 0x6321bd5fe092249c 0xa58c86f57f824892 0x3c01fc0fe1b004c6 0x10f007f03f86c013

def z667 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x0bcff0001fb00001 0xe02f3fc0007ec000

def z668 : W := mkw 0x20800410a0040944 0x1082001042801025 0x34000c01e24c1fff 0xb0d000300789307f

def z669 : W := mkw 0xdb0ed3ef5fd3f6aa 0xe36c3b4fbd7f4fda 0xfffff3fffff3ffff 0xffffffcfffffcfff

def z670 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x436600f006007839 0xad0d9803c01801e0

def z671 : W := mkw 0x4300914f4092a688 0xe10c02453d024a9a 0xeef433cfe5b3e7ff 0x7fbbd0cf3f96cf9f

def z672 : W := mkw 0x1000000016000002 0x0040000000580000 0x000000001e000001 0xe000000000780000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ec4300065b004ef 0x79bb10c00196c013

def z674 : W := mkw 0xfc2ffffdff68003f 0x07f0bffff7fda000 0xffeffffffdb00000 0x5fffbffffff6c000

def z675 : W := mkw 0x20800410a0040944 0x1082001042801025 0x66420c30620c1cef 0x39990830c1883073

def z676 : W := mkw 0x4800c10909408208 0x4120030424250208 0x5559c3019841871a 0xb555670c0661061c

def z677 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0xdddbc33f9bc39f1a 0xf7776f0cfe6f0e7c

def z678 : W := mkw 0x1000000016015002 0x0040000000580540 0x001000001a019810 0x8000400000680660

def z679 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1119c30199c3871a 0xe444670c06670e1c

def z680 : W := mkw 0x0300104640922480 0xa00c004119024892 0xcce430ce05b2640a 0x733390c33816c990

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x0884300005b00000 0x402210c00016c000

def z682 : W := mkw 0x800e12e440000020 0x0200384b91000000 0xefee33fe60000000 0x1fbfb8cff9800000

def z683 : W := mkw 0x20800410a0040944 0x1082001042801025 0x55400031e0401ffa 0xbd550000c781007f

def z684 : W := mkw 0x0300104640922480 0xa00c004119024892 0x6e40300e61b004ef 0x39b900c03986c013

def z685 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0xe3ee3ff060000000 0x0f8fb8ffc1800000

def z686 : W := mkw 0x100e000016000022 0x0040380000580000 0xc3ee00c01e026029 0xeb0fb80300780980

def z687 : W := mkw 0xca00c3ab09c3d608 0xc328030eac270f58 0xddf9c3ff99c3ff3a 0xff77e70ffe670ffc

def z688 : W := mkw 0xa02016f4e0000004 0x0280805bd3800000 0x002000f060000000 0x08008003c1800000

def z689 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdc11c30f81c3871a 0x1770470c3e070e1c

def z690 : W := mkw 0x0000104440000000 0x0000004111000000 0xeee430ce65b00007 0x7bbb90c33996c000

def z691 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xf7620fffe0000000 0x1fdd883fff800000

def z692 : W := mkw 0x0300000200922480 0xa00c000008024892 0x0000000005b26000 0x400000000016c980

def z693 : W := mkw 0xdc2ffbed5f68003b 0x0770bfefb57da000 0x88adf3ce1db00000 0x4222b7cf3876c000

def z694 : W := mkw 0x20800410a0040944 0x1082001042801025 0x20000c00600c00c4 0x0080003001803003

def z695 : W := mkw 0x0300104640922480 0xa00c004119024892 0x0800300e01b00000 0x002000c03806c000

def z696 : W := mkw 0x4800c10909408208 0x4120030424250208 0x1001c00180400300 0x004007000601000c

def z697 : W := mkw 0x1300104656937482 0xa04c0041195a4dd2 0xeef430ce7fb3fcff 0xfbbbd0c339fecff3

def z698 : W := mkw 0xfc2ffffdff68003f 0x07f0bffff7fda000 0xffeffffffa4c0000 0x9fffbfffffe93000

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x8098030018038000 0x4202600c00600e00

def z700 : W := mkw 0xd20e83ab1683d62a 0xc3483a0eac5a0f58 0xc3fe03ff9e03ff39 0xff0ff80ffe780ffc

def z701 : W := mkw 0x21801454e01429c4 0x30860051538050a7 0x77663cf1e67c7fff 0xbddd98f3c799f1ff

def z702 : W := mkw 0x910e12e4561170a2 0x2244384b915845c2 0x222630f0663078e5 0x088898c3c198c1e3

def z703 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc37203f00203f839 0xaf0dc80fc0080fe0

def z704 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x110bcc319a4c1b10 0x84442f30c669306c

def z705 : W := mkw 0x20800410a0040944 0x1082001042801025 0x33020c31e24c1bf5 0x8ccc0830c789306f

def z706 : W := mkw 0x4b00d14f49d2a688 0xe12c03453d274a9a 0xddf9c3cff9c3e7fa 0xff77e70f3fe70f9f

def z707 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x001000001df3e71a 0xe00040000077cf9c

def z708 : W := mkw 0xfc20d7fdff68000f 0x03f0835ff7fda000 0xc02003fffffc0007 0xff00800ffffff000

def z709 : W := mkw 0x140f280016280033 0x04503ca00058a000 0x3fcffc0007bc0007 0x60ff3ff0001ef000

def z710 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffffffffe0019810 0x1fffffffff800660

def z711 : W := mkw 0xb08e06b0b6055966 0x12c2381ac2d81565 0xb4bc0fc1fc4fe7c6 0x52d2f03f07f13f9f

def z712 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdbcf3f9bcf9f3f 0xffff6f3cfe6f3e7c

def z713 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0000000001800000 0x0000000000060000

def z714 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xc0d0000019c3871a 0xe303400000670e1c

def z715 : W := mkw 0x20800410a0040944 0x1082001042801025 0x7fc63c31e24c1fff 0xbdff18f0c789307f

def z716 : W := mkw 0x930e12e6569374a2 0xa24c384b995a4dd2 0x2d1a333e7bb19cd6 0x94b468ccf9eec673

def z717 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x8098030019838000 0x4202600c00660e00

def z718 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3c8dfc0001fc0006 0x00f237f00007f000

def z719 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xd10bcf3f80000000 0x17442f3cfe000000

def z720 : W := mkw 0x4000810900000008 0x0100020424000000 0xffcdf30f85b00007 0x77ff37cc3e16c000

def z721 : W := mkw 0x4000810900000008 0x0100020424000000 0x1dc9c00f80000000 0x107727003e000000

def z722 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc0007fc0007 0x00ff3ff0001ff000

def z723 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe00000e5 0x1fffbfffff800003

def z724 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xfffdf3cf9df3e73f 0xfffff7cf3e77cf9c

def z725 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3c01fc0fe00c00c4 0x10f007f03f803003

def z726 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0000718 0x1fffbfffff80001c

def z727 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xc9edf3ce00000000 0x0727b7cf38000000

def z728 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xfffffff01e4ff83f 0xefffffffc0793fe0

def z729 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3fcffc0003fc0007 0xa0ff3ff0000ff000

def z730 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xeefdf3ce7c03e029 0x7bbbf7cf39f00f80

def z731 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaee430ce65b260e7 0x6abb90c33996c983

def z732 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3ec7fc0007fc0007 0x60fb1ff0001ff000

def z733 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x912bcfff80000000 0x0644af3ffe000000

def z734 : W := mkw 0x4000810900000008 0x0100020424000000 0x9c89c30f80000000 0x1272270c3e000000

def z735 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3c01fc0fe04c0300 0x10f007f03f81300c

def z736 : W := mkw 0x702fbd5df600003e 0x05c0bef577d80000 0x3fcffc0ffe000001 0xf0ff3ff03ff80000

def z737 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3e03fc0003fc0007 0x00f80ff0000ff000

def z738 : W := mkw 0x7021bd5df601501e 0x05c086f577d80540 0x3c11fc0ffe03f839 0xf0f047f03ff80fe0

def z739 : W := mkw 0xaa2f7ef6e9c28634 0xc6a8bdfbdba70a18 0x22363cf079c3871a 0xe888d8f3c1e70e1c

def z740 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c387ff 0xe000400000670e1f

def z741 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7f43fc3fe2001839 0xbdfd0ff0ff880060

def z742 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1fa03f01a03f838 0xef07e80fc0680fe0

def z743 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xc1d8030019838018 0xe707600c00660e00

def z744 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0003fc0007 0xa0f007f0000ff000

def z745 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xd7fe03f19e03f839 0xff5ff80fc6780fe0

def z746 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xdffdc3cf9df3e7ff 0xff7ff70f3e77cf9f

def z747 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefe430ce65b264ff 0xffbf90c33996c993

def z748 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0x3fdffc001fffe007 0xe0ff7ff0007fff80

def z749 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xffefffffe60c78e5 0x1fffbfffff9831e3

def z750 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xfffffff01e3ff83d 0xefffffffc078ffe0

def z751 : W := mkw 0x000f280000000030 0x04003ca000000000 0x3fcffc0007fc0007 0xe0ff3ff0001ff000

def z752 : W := mkw 0x4000810900000008 0x0100020424000000 0x0801c00e00000000 0x0020070038000000

def z753 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x1110000199c3871a 0xe444400006670e1c

def z754 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9119c30f98438310 0x8644670c3e610e0c

def z755 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b264c6 0x5bbb90c33996c993

def z756 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc019c30f98038718 0x1700670c3e600e1c

def z757 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0x3fcfff301ffc0007 0xe4ff3ffcc07ff000

def z758 : W := mkw 0x900f3ae456015032 0x06403ceb91580540 0xfffffffe7e03f839 0xfffffffff9f80fe0

def z759 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0xfffffff01fff801f 0xefffffffc07ffe00

def z760 : W := mkw 0xf52fbffdf63820bf 0x27d4befff7d8e082 0xffefffffe63c60e5 0x1fffbfffff98f183

def z761 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3f43fc0fe24c0007 0xb0fd0ff03f893000

def z762 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3ec5fc001ffc0007 0xe0fb17f0007ff000

def z763 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xfdd9cf0f99cf871e 0xf7f7673c3e673e1c

def z764 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3f0ffc001ffc0007 0x80fc3ff0007ff000

def z765 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfdcbff3fe0000000 0x17f72ffcff800000

def z766 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffffffffe203f839 0xbfffffffff880fe0

def z767 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x7c01fc3fe0001ff8 0x1df007f0ff80007f

def z768 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xebfffff01fbff83d 0xefafffffc07effe0

def z769 : W := mkw 0x4000810900000008 0x0100020424000000 0x1d09c30f80000000 0x1474270c3e000000

def z770 : W := mkw 0x4000810900008208 0x4100020424000208 0xddd9c30f80018310 0x1777670c3e00060c

def z771 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffefffffe6007839 0xbfffbfffff9801e0

def z772 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc9d9c30f99838718 0xf727670c3e660e1c

def z773 : W := mkw 0x8c016aa009695011 0x063005aa8025a540 0xfc31fff001fff83e 0x0ff0c7ffc007ffe0

def z774 : W := mkw 0x0c01680009680011 0x043005a00025a000 0xfdd9ff0019ff801e 0xe7f767fc0067fe00

def z775 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0xffeffff01ffc183f 0xefffbfffc07ff060

def z776 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xf7fe3ff01e7ff83f 0xefdff8ffc079ffe0

def z777 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc301ffc1827 0xe8ff3ff0c07ff060

def z778 : W := mkw 0x20800410a0040944 0x1082001042801025 0x75420c31e24c1fde 0xb5d50830c789307f

def z779 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe03f810 0xdffffffffff80fe0

def z780 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe5b2602f 0x7fffbfffff96c980

def z781 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x83fe03f01e03f811 0xe60ff80fc0780fe0

def z782 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xbca5fccfe0000000 0x12f297f33f800000

def z783 : W := mkw 0x20800410a0040944 0x1082001042801025 0x7fc20c31e3cc1fff 0xfdff0830c78f307f

def z784 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3ec5fc0fe0000000 0x10fb17f03f800000

def z785 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x8899c30f99838310 0x4622670c3e660e0c

def z786 : W := mkw 0xd42fbbed5628003b 0x0750beefb558a000 0x88adf3ce04300000 0x0222b7cf3810c000

def z787 : W := mkw 0xda0ec3ab1fc3d62a 0xc3683b0eac7f0f58 0x1e27c0ff87c07f23 0x18789f03fe1f01fc

def z788 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0xfffffcc01ffff83f 0xebfffff3007fffe0

def z789 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xefeff3fe60000000 0x1fbfbfcff9800000

def z790 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0xffe7fcffe24c1fff 0xbfff9ff3ff89307f

def z791 : W := mkw 0x742fbd5df628003f 0x05d0bef577d8a000 0x3e07fc0fe63c0005 0x10f81ff03f98f000

def z792 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe1b00006 0x1fffbfffff86c000

def z793 : W := mkw 0x1e8040021fee8f43 0xd07a0100087fba3d 0x001000001fff9fff 0xe0004000007ffe7f

def z794 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000001c3871a 0x0000400000070e1c

def z795 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x34100c01f9cf87de 0xf0d0403007e73e1f

def z796 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe24c183f 0xbfffbfffff893060

def z797 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e03f821 0x4f0ff80fc0780fe0

def z798 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x1410000199c3871a 0xf050400006670e1c

def z799 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc2fc03f01c03f839 0x6f0bf00fc0700fe0

def z800 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xdfffc3ff9e43ff3b 0xff7fff0ffe790ffc

def z801 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0xd12bccce7a4e64e8 0x9b44af3339e93993

def z802 : W := mkw 0x0c01680009680011 0x043005a00025a000 0xfee5fcc005fe602f 0x6bfb97f30017f980

def z803 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x0801f00fe0000000 0x102007c03f800000

def z804 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x88adf3ce04026000 0x4222b7cf38100980

def z805 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80400702 0x1777270c3e01001c

def z806 : W := mkw 0xe32fafbba09224bc 0xa78cbebeee824892 0x110bcf3185b264ef 0x64442f3cc616c993

def z807 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddfdc3cf9dc3e71a 0xf777f70f3e770f9c

def z808 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffefffffffb00007 0xffffbffffffec000

def z809 : W := mkw 0xf08e87b9b605596e 0x13c23a1ee6d81565 0xffffcffffe4fffff 0xffffff3ffff93fff

def z810 : W := mkw 0x1e0040021febd603 0xc0780100087faf58 0x001000001fffff3f 0xe0004000007ffffc

def z811 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xfffffff01fffe007 0xefffffffc07fff80

def z812 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc3fc03f01c03f839 0xef0ff00fc0700fe0

def z813 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0x3fdffc001ffd9817 0xe0ff7ff0007ff660

def z814 : W := mkw 0x20800410a0040944 0x1082001042801025 0xffe63cf1e7fe7fff 0xffff98f3c79ff9ff

def z815 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xddedf3cf8040071a 0xb777b7cf3e01001c

def z816 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xffffffc01fffe02f 0xebffffff007fff80

def z817 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x2ed430001df3871f 0xe0bb50c00077ce1c

def z818 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0x99afffff824c1b10 0x8666bffffe09306c

def z819 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xbfeffcc01ffe6007 0xe2ffbff3007ff980

def z820 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2001cff 0xbfffbfffff880073

def z821 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3dc9fc0001fc0006 0x00f727f00007f000

def z822 : W := mkw 0xc0afbbed40040978 0x1702beefb5001025 0x88adf3ce024c1fff 0xa222b7cf3809307f

def z823 : W := mkw 0x4000914d40000008 0x0100024535000000 0xdde9c3cfe0000000 0x1f77a70f3f800000

def z824 : W := mkw 0xc02093ed40000008 0x0300824fb5000000 0x88a9c3ce00000000 0x0222a70f38000000

def z825 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe03fcff 0xfffffffffff80ff3

def z826 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77660cf1e64c7fff 0xbddd9833c79931ff

def z827 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0x80bc03c01dc3e71a 0xe202f00f00770f9c

def z828 : W := mkw 0x560fa90b16aa863b 0xc5583ea42c5aaa18 0xe2163f0f863f871d 0x178858fc3e18fe1c

def z829 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe03f821 0x5ffffffffff80fe0

def z830 : W := mkw 0x4000914d40000008 0x0100024535000000 0x3c01f00fe0000000 0x10f007c03f800000

def z831 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc019ffc0007 0xf5ff3ff0067ff000

def z832 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001fbc0005 0x40ff3ff0007ef000

def z833 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xeeedf3ffe0000000 0x1fbbb7cfff800000

def z834 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0x3fcffc001ffc7827 0xe0ff3ff0007ff1e0

def z835 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f07e03fcf9 0xff0ff80fc1f80ff3

def z836 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xdfffc3f01e03f839 0xef7fff0fc0780fe0

def z837 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2401f3b 0xbfffbfffff89007c

def z838 : W := mkw 0xe02fbffde000823c 0x4780befff7800208 0xffffffffe0018310 0x1fffffffff80060c

def z839 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019838718 0x4000400000660e1c

def z840 : W := mkw 0x0000104440000000 0x0000004111000000 0xffedf0ce60000000 0x1bffb7c339800000

def z841 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xcffe03fe1e03f839 0xff3ff80ff8780fe0

def z842 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0x3e07fc0fe0000000 0x10f81ff03f800000

def z843 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3cc1fc0001fc0006 0x60f307f00007f000

def z844 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7ca0f31e24c1fff 0xbfdf283cc789307f

def z845 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc03003f01803f838 0xef00c00fc0600fe0

def z846 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce67b27cff 0xfbbb90c3399ec9f3

def z847 : W := mkw 0x23801456e0962dc4 0xb08e00515b8258b7 0x99a63cff87fe7b10 0xc66698f3fe1ff9ec

def z848 : W := mkw 0xe02e97fde000002c 0x0380ba5ff7800000 0xdfefc3ffe0000000 0x1f7fbf0fff800000

def z849 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe4006021 0x1fffbfffff900180

def z850 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01c03f838 0x4f0ff80fc0700fe0

def z851 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeef430ce7db3e4ff 0xfbbbd0c339f6cf93

def z852 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe20c18fd 0xbfffbfffff883063

def z853 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3ec5fc0fe5b00007 0x70fb17f03f96c000

def z854 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe4ff83f 0xfffffffffff93fe0

def z855 : W := mkw 0x000f384440000030 0x04003ce111000000 0xeeedf0ce60000000 0x1bbbb7c339800000

def z856 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3c01fc0fe00007c0 0x10f007f03f80001f

def z857 : W := mkw 0x20800410a0040944 0x1082001042801025 0x53420c31e24c1ff9 0xbd4d0830c789307f

def z858 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99c38310 0xd777670c3e670e0c

def z859 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2bcffc001fbc0005 0xe0af3ff0007ef000

def z860 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xffefffcf80000000 0x17ffbfff3e000000

def z861 : W := mkw 0xe1afbffde01429fc 0x3786befff78050a7 0xffefffffe67c7fff 0xbfffbfffff99f1ff

def z862 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffefffffe0007820 0x1fffbfffff8001e0

def z863 : W := mkw 0x20800410a0040944 0x1082001042801025 0x11020c31e24c1fd0 0x94440830c789307f

def z864 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001dfc0006 0x40ff3ff00077f000

def z865 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1b39 0xbfffbfffff89306c

def z866 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0x3c8dfc0fe0000000 0x10f237f03f800000

def z867 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xffedf3ffe0000000 0x1fffb7cfff800000

def z868 : W := mkw 0x4000810900000008 0x0100020424000000 0xc9c9c30e00000000 0x0727270c38000000

def z869 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3d09fc0019fc0006 0x80f427f00067f000

def z870 : W := mkw 0x60afbd5de004097c 0x1582bef577801025 0x7fcffc3fe24c1fff 0xbdff3ff0ff89307f

def z871 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80000018 0xb777270c3e000000

def z872 : W := mkw 0x1a8040021fc7df42 0xd06a0100087f1f7d 0x001000001fcfffff 0xe0004000007f3fff

def z873 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37420c31e24c1fe7 0xb8dd0830c789307f

def z874 : W := mkw 0x4000810900000008 0x0100020424000000 0xddd9c30f9843871a 0xf777670c3e610e1c

def z875 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x9cadf3cf80000000 0x1272b7cf3e000000

def z876 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xaabffffe7e03f821 0x4aaafffff9f80fe0

def z877 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe5b00000 0x5fffbfffff96c000

def z878 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xfffe3ff01ffff83f 0xeffff8ffc07fffe0

def z879 : W := mkw 0x4000810900000008 0x0100020424000000 0xffcbcf0f824c0007 0xb7ff2f3c3e093000

def z880 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xffefffce60000000 0x1bffbfff39800000

def z881 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xcffe03f01f83f83b 0xef3ff80fc07e0fe0

def z882 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffeffffffe007821 0xffffbffffff801e0

def z883 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x001000001fff8007 0xe0004000007ffe00

def z884 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3d41fc0001fc0006 0xa0f507f00007f000

def z885 : W := mkw 0xe0afbffde005597c 0x1782befff7801565 0xffffffffe003fff8 0x1fffffffff800fff

def z886 : W := mkw 0x4800c10909408208 0x4120030424250208 0x1d19c30f98418310 0x9474670c3e61060c

def z887 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3dc9fc0fe0000000 0x10f727f03f800000

def z888 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x8899c30f99838700 0x5222670c3e660e1c

def z889 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c07c7 0xbfffbfffff89301f

def z890 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x5d59c30f99c1871a 0xb575670c3e67061c

def z891 : W := mkw 0xf42fbffdf629503f 0x07d0befff7d8a540 0xffefffffe63c7825 0x1fffbfffff98f1e0

def z892 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe000040a 0x3fffbfffff800010

def z893 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x001000001bcf9f1a 0xe0004000006f3e7c

def z894 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xffedffcfe0000000 0x1fffb7ff3f800000

def z895 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xeffff3fe7e03f839 0xffbfffcff9f80fe0

def z896 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0xfee5fccfe04c07ef 0x3bfb97f33f81301f

def z897 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffffffffffb3f83f 0xfffffffffffecfe0

def z898 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x77420c007ffe64ef 0xf9dd083001fff993

def z899 : W := mkw 0x4000810900000008 0x0100020424000000 0xffc9c30fe0000000 0x1fff270c3f800000

def z900 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x7f4bff3fe0000000 0x1dfd2ffcff800000

def z901 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xaaafffce00000000 0x02aabfff38000000

def z902 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffc03e029 0x7ffffffffff00f80

def z903 : W := mkw 0x0300104640922480 0xa00c004119024892 0xcae430ce65b264e9 0x7b2b90c33996c993

def z904 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe0001fff 0x3fffbfffff80007f

def z905 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7c20c31e24e1fff 0xffdf0830c789387f

def z906 : W := mkw 0xb0af3ef4f6055976 0x16c2bcfbd3d81565 0x22263cf0660c78e5 0x088898f3c19831e3

def z907 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe24c0000 0x9fffbfffff893000

def z908 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xffd9c30ffdf3e7ff 0xffff670c3ff7cf9f

def z909 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x4010000199c3871a 0xf500400006670e1c

def z910 : W := mkw 0x400fa90900000038 0x05003ea424000000 0xddcbcf0f80000000 0x17772f3c3e000000

def z911 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x6650000079c387ff 0xf999400001e70e1f

def z912 : W := mkw 0x4000810900000008 0x0100020424000000 0xdfedc3cf80000000 0x1f7fb70f3e000000

def z913 : W := mkw 0x0a00400209c3d600 0xc028010008270f58 0x0010000019c3ff3a 0xe000400000670ffc

def z914 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xffcbcf3fe0000000 0x1fff2f3cff800000

def z915 : W := mkw 0xc00e93ed40000028 0x03003a4fb5000000 0xffeff3ffe0000000 0x1fffbfcfff800000

def z916 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xeffe3ff01fbff83f 0xefbff8ffc07effe0

def z917 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfdbc30f9bc3871b 0xf77f6f0c3e6f0e1c

def z918 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3fcffc0005fc0007 0x60ff3ff00017f000

def z919 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffff8018000 0x1fffffffffe00600

def z920 : W := mkw 0x1a0e40021fc28622 0xc0683900087f0a18 0x03de00001fc3871b 0xe00f7800007f0e1c

def z921 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe430cfe5b264ef 0x7fff90c33f96c993

def z922 : W := mkw 0x540fa9091628003b 0x05503ea42458a000 0xffcfff0f863c0005 0x17ff3ffc3e18f000

def z923 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0001838 0x1fffbfffff800060

def z924 : W := mkw 0xf12fbffdf61170be 0x27c4befff7d845c2 0xfffffffffe33f8fd 0xfffffffffff8cfe3

def z925 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x80bc03f01c03f820 0x4a02f00fc0700fe0

def z926 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x82be03f01e03f839 0xea0af80fc0780fe0

def z927 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1ff8 0x9fffbfffff89307f

def z928 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xc8adf3cf80000000 0x1722b7cf3e000000

def z929 : W := mkw 0x0300104640922480 0xa00c004119024892 0xc8a430ce65b264ef 0x7b2290c33996c993

def z930 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xfffffff01ffd9817 0xefffffffc07ff660

def z931 : W := mkw 0x1c0050445f680003 0x00700141117da000 0xeee430ce7ffc0007 0xfbbb90c339fff000

def z932 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3e8ffc001ffc0007 0x40fa3ff0007ff000

def z933 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3fcdfc001dfc0007 0xe0ff37f00077f000

def z934 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3c8dfc001ffc0007 0xe0f237f0007ff000

def z935 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffffa039839 0xffffffffffe80e60

def z936 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c18712 0x800040000067061c

def z937 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x198ffc001ffc0007 0xe0663ff0007ff000

def z938 : W := mkw 0x3c8f6c10bf6c0977 0x14f23db042fdb025 0x488df031fdb01ff8 0x5d2237c0c7f6c07f

def z939 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffe001839 0xffffbffffff80060

def z940 : W := mkw 0x000f384440000030 0x04003ce111000000 0x88adf0ce00000000 0x0222b7c338000000

def z941 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xbcbdffc01dffe006 0x42f2f7ff0077ff80

def z942 : W := mkw 0xe3a097ffe0962dcc 0xb38e825fff8258b7 0xc02003ffe0027ff8 0x1f00800fff8009ff

def z943 : W := mkw 0x1e0040021fea0403 0x80780100087fa810 0x000000001ffe040f 0xe0000000007ff810

def z944 : W := mkw 0x4000914d40000008 0x0100024535000000 0xfdc9f30fe0000000 0x17f727cc3f800000

def z945 : W := mkw 0x60008519a000000c 0x0180021466800000 0x7f43cc3fe0000000 0x1dfd0f30ff800000

def z946 : W := mkw 0x6b80d55fe9d6afcc 0xf1ae03557fa75abf 0x3c01fc0fe1fc07c6 0x10f007f03f87f01f

def z947 : W := mkw 0x6380955fe096afcc 0xf18e02557f825abf 0xc03003ffe003fff8 0x1f00c00fff800fff

def z948 : W := mkw 0x60afbd5de004097c 0x1582bef577801025 0x3fcffc0fe24c07c7 0xb0ff3ff03f89301f

def z949 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xddfdf3cf9c03e018 0xf777f7cf3e700f80

def z950 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2a2430ce65b060e5 0x08a890c33996c183

def z951 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbfefffcfe0000000 0x12ffbfff3f800000

def z952 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xddd9c30f99f387de 0xf777670c3e67ce1f

def z953 : W := mkw 0x60008519a000000c 0x0180021466800000 0xddc9c33fe0000000 0x1f77270cff800000

def z954 : W := mkw 0x0300104640922480 0xa00c004119024892 0x88a430ce65b264c0 0x522290c33996c993

def z955 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd119c30f99c3871a 0xf744670c3e670e1c

def z956 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3e07fc001ffc0007 0xe0f81ff0007ff000

def z957 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc001ffc001f 0xe5ff3ff0007ff000

def z958 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3c01fc001dfc0006 0x40f007f00077f000

def z959 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x40100031f9c39ffa 0xfd004000c7e70e7f

def z960 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd999c30f99c38718 0xd766670c3e670e1c

def z961 : W := mkw 0x20800410a0040944 0x1082001042801025 0x7f423c31e3fc1fff 0xbdfd08f0c78ff07f

def z962 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3ffffff01ffdf837 0xecffffffc07ff7e0

def z963 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe7fc1fff 0xffffbfffff9ff07f

def z964 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe01f831 0x9ffffffffff807e0

def z965 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x7f43fc3003fc183f 0xadfd0ff0c00ff060

def z966 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffc03f838 0x5ffffffffff00fe0

def z967 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2a8ffc001ffc0007 0xe0aa3ff0007ff000

def z968 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefe630ce67b264ef 0xfbbf98c3399ec993

def z969 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x033e03f01e03f839 0xec0cf80fc0780fe0

def z970 : W := mkw 0x4000914d40000008 0x0100024535000000 0xfee5f0cfe0000000 0x1bfb97c33f800000

def z971 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xfffffff07ffffcff 0xffffffffc1fffff3

def z972 : W := mkw 0x000f280000000030 0x04003ca000000000 0xffcffc0e00000000 0x13ff3ff038000000

def z973 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e24c1fd6 0x9ddd0830c789307f

def z974 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffefffffe20c0000 0x1fffbfffff883000

def z975 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xcbeff3ffe0000000 0x1f2fbfcfff800000

def z976 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xfdd9f30f99f3871e 0xf7f767cc3e67ce1c

def z977 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe63cce65b264ef 0x7bff98f33996c993

def z978 : W := mkw 0x6a80c51ba9c68f4c 0xd1aa03146ea71a3d 0xaa9bcf3e7b8f98e5 0x4aaa6f3cf9ee3e63

def z979 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xbc89ff0fe0000000 0x12f227fc3f800000

def z980 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefe630fe65b264ef 0x7fbf98c3f996c993

def z981 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xbcadffcfe04c07c6 0x12f2b7ff3f81301f

def z982 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc2fe03f01e03f829 0x6b0bf80fc0780fe0

def z983 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x88affffe00000000 0x0222bffff8000000

def z984 : W := mkw 0x1e0f68021fea8633 0xc4783da0087faa18 0x22163c001fff871f 0xe08858f0007ffe1c

def z985 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0xffcbff3fe24c1fff 0xbfff2ffcff89307f

def z986 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3fdfff001ffd8007 0xe0ff7ffc007ff600

def z987 : W := mkw 0xe0afafb9a004097c 0x1782bebee6801025 0xffcbcf3fe24c1fff 0xbfff2f3cff89307f

def z988 : W := mkw 0x4000810900000008 0x0100020424000000 0xdfcbc33f80000000 0x1f7f2f0cfe000000

def z989 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3e25fccfe0000000 0x18f897f33f800000

def z990 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfee5fccfe4026029 0x7bfb97f33f900980

def z991 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe00018e0 0x1fffbfffff800063

def z992 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99c18712 0x9777670c3e67061c

def z993 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeaa430ce65b264ed 0x5baa90c33996c993

def z994 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x8aaff3fe00000000 0x0a2abfcff8000000

def z995 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xddfdc3cf9c03e000 0x5777f70f3e700f80

def z996 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc33e03f01e03f839 0x8f0cf80fc0780fe0

def z997 : W := mkw 0x000f384440000030 0x04003ce111000000 0xbfeffcce00000000 0x02ffbff338000000

def z998 : W := mkw 0xe42fbffde028003d 0x0790befff780a000 0xffefffffe03c0004 0x1fffbfffff80f000

def z999 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefec33ce65b264ef 0x7fbfb0cf3996c993

def z1000 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x1550000019c3871a 0xe055400000670e1c

def z1001 : W := mkw 0x940e02a016295023 0x0250380a8058a540 0xc3fe03f01e3ff83d 0xef0ff80fc078ffe0

def z1002 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0005fc0007 0x60f007f00017f000

def z1003 : W := mkw 0x6020955de000000c 0x0180825577800000 0xddc9c30fe0000000 0x1777270c3f800000

def z1004 : W := mkw 0x0300104640922480 0xa00c004119024892 0xe22430ce65b264ef 0x7b8890c33996c993

def z1005 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdd19c30f99c3871a 0x9774670c3e670e1c

def z1006 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x000000001db264ef 0x600000000076c993

def z1007 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc319ffc1f3f 0xfdff3ff0c67ff07c

def z1008 : W := mkw 0x1a0040021fc28602 0xc0680100087f0a18 0x001000001fc3871b 0xe0004000007f0e1c

def z1009 : W := mkw 0x0b80400209d6afc0 0xf02e010008275abf 0x001000001fffffff 0xe0004000007fffff

def z1010 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xffeffffe00000000 0x0fffbffff8000000

def z1011 : W := mkw 0xd00e93ed5601502a 0x03403a4fb5580540 0xfffff3fffe03f839 0xffffffcffff80fe0

def z1012 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x01d8000019c3871a 0xe007600000670e1c

def z1013 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x1400000181c00702 0x105000000607001c

def z1014 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x88adf3cfe0000000 0x1222b7cf3f800000

def z1015 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xc029c3ffe0000000 0x1f00a70fff800000

def z1016 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x7feffcf01ffc783f 0xedffbff3c07ff1e0

def z1017 : W := mkw 0x4800c10909408208 0x4120030424250208 0xddd9c30f98438318 0xf777670c3e610e0c

def z1018 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xd13bcffffa03f838 0x9f44ef3fffe80fe0

def z1019 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77c60c31e64c1fff 0xfddf1830c799307f

def z1020 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7d41fc0fe040071a 0xb5f507f03f81001c

def z1021 : W := mkw 0x4000810900000008 0x0100020424000000 0xffcdf30f80000000 0x17ff37cc3e000000

def z1022 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99c38702 0x5777670c3e670e1c

def z1023 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xfffffffff803f838 0xffffffffffe00fe0

def z1024 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfdedffcfe0000000 0x17f7b7ff3f800000

def z1025 : W := mkw 0xc00faba900000038 0x07003eaea4000000 0xffefffff80000000 0x1fffbffffe000000

def z1026 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c89fc0019fc0006 0x40f227f00067f000

def z1027 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f9bcf871f 0xf777670c3e6f3e1c

def z1028 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3d09ff0fe0000000 0x14f427fc3f800000

def z1029 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0xddcbc33f80000000 0x17772f0cfe000000

def z1030 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2c2430ce65b064c6 0x10b090c33996c193

def z1031 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fdffc001fff801f 0xe0ff7ff0007ffe00

def z1032 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xd3fe03f19e43fb39 0xef4ff80fc6790fec

def z1033 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3dc9fc001ffc0007 0xe0f727f0007ff000

def z1034 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xf76bcfffe24c1fff 0xbfddaf3fff89307f

def z1035 : W := mkw 0x8c0f6aa009680031 0x06303daa8025a000 0xffeffff001fc0006 0x0fffbfffc007f000

def z1036 : W := mkw 0xe00e87b9a000002c 0x03803a1ee6800000 0xffefcfffe0000000 0x1fffbf3fff800000

def z1037 : W := mkw 0x4000810900000008 0x0100020424000000 0x5d41c00f8040071a 0xb57507003e01001c

def z1038 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x0809f30e00000000 0x002027cc38000000

def z1039 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f8000040a 0x3777270c3e000010

def z1040 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xff63ffffe0000000 0x1ffd8fffff800000

def z1041 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xd5d8030199c3871a 0xf757600c06670e1c

def z1042 : W := mkw 0x0b00504649d2a680 0xe02c014119274a9a 0x223430c07df3e7ff 0xe888d0c301f7cf9f

def z1043 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe3fe33f01e33f83d 0xef8ff8cfc078cfe0

def z1044 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0x3c01ff3fe0000000 0x14f007fcff800000

def z1045 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c85fc0005fc0006 0x40f217f00017f000

def z1046 : W := mkw 0x030010464092a680 0xe00c004119024a9a 0xeef430ce65b3e7ff 0x7bbbd0c33996cf9f

def z1047 : W := mkw 0x60008519a000000c 0x0180021466800000 0xffdbcf3ffa039839 0xffff6f3cffe80e60

def z1048 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x88bdf3ce18018000 0x0222f7cf38600600

def z1049 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc0b803f01803f838 0x4f02e00fc0600fe0

def z1050 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc23603f01e03f839 0xef08d80fc0780fe0

def z1051 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0000007 0x3fffbfffff800000

def z1052 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3ffffcf01ffff83f 0xe8fffff3c07fffe0

def z1053 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xc2f400c01dc3e73b 0xeb0bd00300770f9c

def z1054 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x0010000019c39ffa 0xe000400000670e7f

def z1055 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x7d41fc0181fc071e 0xb5f507f00607f01c

def z1056 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xffcfff3f80000000 0x17ff3ffcfe000000

def z1057 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfdd9ff0ff8038018 0xf7f767fc3fe00e00

def z1058 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xddd9c30f9df3e71a 0xf777670c3e77cf9c

def z1059 : W := mkw 0x4000810900000008 0x0100020424000000 0xddd9c30f98018010 0x9777670c3e600600

def z1060 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3b8ffc001ffc0005 0xc0ee3ff0007ff000

def z1061 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe6027839 0xffffbfffff9809e0

def z1062 : W := mkw 0x1b0040021fd3f682 0xe06c0100087f4fda 0x001000001ff3ffff 0xe0004000007fcfff

def z1063 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1f1a 0xbfffbfffff89307c

def z1064 : W := mkw 0x402fb94d40000038 0x0500bee535000000 0x088df00e00000000 0x002237c038000000

def z1065 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x001000001f83f839 0xe0004000007e0fe0

def z1066 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c38702 0x4000400000670e1c

def z1067 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbfefffff80000000 0x06ffbffffe000000

def z1068 : W := mkw 0x1c0f68001f688233 0x44703da0007da208 0x3fdffc001ffd8317 0xe0ff7ff0007ff60c

def z1069 : W := mkw 0x1f0e40021ffa24a3 0xa07c3900087fe892 0xc3ee00c01ffe64ef 0xeb0fb803007ff993

def z1070 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbbafffffe0000000 0x0eeebfffff800000

def z1071 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c38310 0xc000400000670e0c

def z1072 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0x99bfffff9e03f810 0xc666fffffe780fe0

def z1073 : W := mkw 0x4800c10909408208 0x4120030424250208 0xd119c30f98418310 0x9744670c3e61060c

def z1074 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xaeedf3ce00000000 0x02bbb7cf38000000

def z1075 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3fdfff301ffff83f 0xe4ff7ffcc07fffe0

def z1076 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaea430ce65b264e7 0x5aba90c33996c993

def z1077 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0xc3fe03f01f83f839 0xef0ff80fc07e0fe0

def z1078 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xfffffff01fb3f83f 0xefffffffc07ecfe0

def z1079 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0061fc04c6 0x10f007f00187f013

def z1080 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc007ffc0007 0xf9ff3ff001fff000

def z1081 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x89aff3fe00000000 0x0626bfcff8000000

def z1082 : W := mkw 0x0300104640922480 0xa00c004119024892 0x6e6430ce65b064ef 0x39b990c33996c193

def z1083 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e24c1fe7 0x1ddd0830c789307f

def z1084 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffffffffe0038018 0x1fffffffff800e00

def z1085 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeefc33ce7db3e4ef 0x7bbbf0cf39f6cf93

def z1086 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x22120c307bcf9fff 0xe8884830c1ef3e7f

def z1087 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3feffcc01ffc6007 0xe0ffbff3007ff180

def z1088 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbfeffffe60000000 0x0affbffff9800000

def z1089 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe43ff3b 0xfffffffffff90ffc

def z1090 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x4150000019c3871a 0xe505400000670e1c

def z1091 : W := mkw 0x4000810900000008 0x0100020424000000 0xddd9c30f98038000 0x5777670c3e600e00

def z1092 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xfdd9c30ff9c387de 0xf7f7670c3fe70e1f

def z1093 : W := mkw 0x1c0168001f695013 0x047005a0007da540 0x3c11fc001ffff83f 0xe0f047f0007fffe0

def z1094 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0xdfefc3ff82401f3b 0xbf7fbf0ffe09007c

def z1095 : W := mkw 0x60008519a000000c 0x0180021466800000 0xddcbcf3f80000000 0x17772f3cfe000000

def z1096 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xbffffff01ffff817 0xe6ffffffc07fffe0

def z1097 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xffeffcf01ffe782f 0xebffbff3c07ff9e0

def z1098 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xfffffffe1e03f839 0xeffffffff8780fe0

def z1099 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7520f31e24f9fff 0xbfdd483cc7893e7f

def z1100 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffdfff301fff983f 0xefff7ffcc07ffe60

def z1101 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1fe7 0x1fffbfffff89307f

def z1102 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x001000001bcf871a 0xe0004000006f3e1c

def z1103 : W := mkw 0xe08e87b9a004096c 0x13823a1ee6801025 0xffefcfffe24c1fff 0xbfffbf3fff89307f

def z1104 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xddedf3ffe0000000 0x1f77b7cfff800000

def z1105 : W := mkw 0x600fad19a000003c 0x05803eb466800000 0xffcfff3fe0000000 0x1fff3ffcff800000

def z1106 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe7fe03f07e03f839 0xff9ff80fc1f80fe0

def z1107 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaaa430ce65b264ef 0x6aaa90c33996c993

def z1108 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x3c01fc0e00000000 0x00f007f038000000

def z1109 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0x80bc03c01d83e000 0x4202f00f00760f80

def z1110 : W := mkw 0xd00faba91601503a 0x07403eaea4580540 0xffffffff9e03f839 0xfffffffffe780fe0

def z1111 : W := mkw 0x1f8040021ffe2dc3 0xb07e0100087ff8b7 0x000000001ffe7fff 0xe0000000007ff9ff

def z1112 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffa039818 0xffffffffffe80e60

def z1113 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2001821 0x1fffbfffff880060

def z1114 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x001000001db3e4ef 0x600040000076cf93

def z1115 : W := mkw 0x150f3844563820b3 0x24543ce11158e082 0xffeffcce663c60e5 0x1bffbff33998f183

def z1116 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdddbc33f9bc39f1a 0xf7776f0cfe6f0e7c

def z1117 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffeffffffe3c0005 0xffffbffffff8f000

def z1118 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffc04ef 0xe0ff3ff0007ff013

def z1119 : W := mkw 0x6020955de000000c 0x0180825577800000 0x1c01c00fe0000000 0x107007003f800000

def z1120 : W := mkw 0x4000810900000008 0x0100020424000000 0xc889c30f80000000 0x1722270c3e000000

def z1121 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x88adf3ff80000000 0x0622b7cffe000000

def z1122 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffc071f 0xe0ff3ff0007ff01c

def z1123 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe4000001 0x7fffbfffff900000

def z1124 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2ee430ce65b064e7 0x78bb90c33996c193

def z1125 : W := mkw 0x60808519a004094c 0x1182021466801025 0xffcbcf3fe20c18e5 0x1fff2f3cff883063

def z1126 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xbfffffce1e03e001 0xe2ffffff38780f80

def z1127 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xdddbc33f9a019810 0x97776f0cfe680660

def z1128 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xebeffffe60000000 0x0fafbffff9800000

def z1129 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffcffc0e1ffc0007 0xf3ff3ff0387ff000

def z1130 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc2f403f01e03f839 0xef0bd00fc0780fe0

def z1131 : W := mkw 0x400e810900000028 0x01003a0424000000 0xdfcfc30f80000000 0x177f3f0c3e000000

def z1132 : W := mkw 0xc02fbbed40015038 0x0700beefb5000540 0xc8bdf3fe0003f838 0x0f22f7cff8000fe0

def z1133 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc019ffc0707 0xf0ff3ff0067ff01c

def z1134 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xfee5ffffe0000000 0x1ffb97ffff800000

def z1135 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7fe0ff1fe4fffff 0xffdff83fc7f93fff

def z1136 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xcaedf3ce00000000 0x0b2bb7cf38000000

def z1137 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0000000001c0071a 0xa00000000007001c

def z1138 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x80be03f01e03f800 0x4202f80fc0780fe0

def z1139 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xc3fe33f01e33f839 0xef0ff8cfc078cfe0

def z1140 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3e27fcf007fc7827 0x08f89ff3c01ff1e0

def z1141 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe04c0006 0x1fffbfffff813000

def z1142 : W := mkw 0x0300104640922480 0xa00c004119024892 0xfffc33cffdf3e7ff 0xfffff0cf3ff7cf9f

def z1143 : W := mkw 0xe1afbffde01429fc 0x3786befff78050a7 0xffefffffe63c78e5 0x1fffbfffff98f1e3

def z1144 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77520c31fa4f9fff 0xfddd4830c7e93e7f

def z1145 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xf7fe0ff19e4fff3f 0xffdff83fc6793ffc

def z1146 : W := mkw 0x4800c10909408208 0x4120030424250208 0xddd9c30f9841871a 0xb777670c3e61061c

def z1147 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd559c30f9843871a 0xb755670c3e610e1c

def z1148 : W := mkw 0x4900d14d4950a288 0x612403453525428a 0x333df3c1fc71e3f5 0x8cccf7cf07f1c78f

def z1149 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2a07fc0007bc0005 0x00a81ff0001ef000

def z1150 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x0000000005f267ef 0x600000000017c99f

def z1151 : W := mkw 0x4000914d40000008 0x0100024535000000 0xfffdf3cffc03e039 0xfffff7cf3ff00f80

def z1152 : W := mkw 0x6421bd5de028001d 0x059086f57780a000 0x3c01fc0fe03c0004 0x10f007f03f80f000

def z1153 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30ff9c387fa 0xff77670c3fe70e1f

def z1154 : W := mkw 0x3a804412bfc7df46 0xd0ea01104aff1f7d 0x77520c31ffcfffff 0xfddd4830c7ff3fff

def z1155 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000018438718 0x8000400000610e1c

def z1156 : W := mkw 0xc02faba900000038 0x0700beaea4000000 0xddc9c30f80000000 0x1777270c3e000000

def z1157 : W := mkw 0x0001384440000010 0x040004e111000000 0xfee5fcce60000000 0x1bfb97f339800000

def z1158 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01a03f838 0x8f0ff80fc0680fe0

def z1159 : W := mkw 0x9f0e42a21ffb74a3 0xa27c390a887fedd2 0xc3fe03f01ffffcff 0xef0ff80fc07ffff3

def z1160 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0x3d0bff3fe24c1fd6 0x94f42ffcff89307f

def z1161 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffcfff001ffc0007 0xe7ff3ffc007ff000

def z1162 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xbfefffce024c0007 0xa2ffbfff38093000

def z1163 : W := mkw 0x0300104640922480 0xa00c004119024892 0x2e2430ce65b264ef 0x78b890c33996c993

def z1164 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x1001cc0fe0000000 0x104007303f800000

def z1165 : W := mkw 0x4200810b00828608 0xc10802042c020a18 0xddd9c30f98038718 0xf777670c3e600e1c

def z1166 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3e03fc3fe20c18e5 0x18f80ff0ff883063

def z1167 : W := mkw 0x3e804412bfee8f47 0xd0fa01104affba3d 0x77520c31ffff9fff 0xfddd4830c7fffe7f

def z1168 : W := mkw 0xc021bbed40000018 0x070086efb5000000 0x8821f3ce00000000 0x022087cf38000000

def z1169 : W := mkw 0x4001a90900000018 0x050006a424000000 0xfdc9ff0f80000000 0x17f727fc3e000000

def z1170 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x99afffce00000000 0x0266bfff38000000

def z1171 : W := mkw 0xc02fbbed40015038 0x0700beefb5000540 0x88bdf3ce0003e000 0x0222f7cf38000f80

def z1172 : W := mkw 0x4001a90900000018 0x050006a424000000 0x3c01fc0f80000000 0x10f007f03e000000

def z1173 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x2801fc0e60000000 0x00a007f039800000

def z1174 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdddbcf0f9bcf871a 0xf7776f3c3e6f3e1c

def z1175 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xc899c30f99c3871a 0xf722670c3e670e1c

def z1176 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x0000000001cc07c6 0x000000000007301f

def z1177 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x88adf3ce04006000 0x0222b7cf38100180

def z1178 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77463c31e67c1fff 0xbddd18f0c799f07f

def z1179 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9dd9c30f99c38312 0xe677670c3e670e0c

def z1180 : W := mkw 0x4100914d40102088 0x2104024535004082 0xffedf3cfe43060e5 0x1fffb7cf3f90c183

def z1181 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x001000001dc3e73b 0xe000400000770f9c

def z1182 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019c38002 0xe000400000670e00

def z1183 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0000029 0x3fffbfffff800000

def z1184 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x0825f0ce00000000 0x002097c338000000

def z1185 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x190bff3f80000000 0x04642ffcfe000000

def z1186 : W := mkw 0x000f384440000030 0x04003ce111000000 0xffeffcce624c04ef 0xbbffbff339893013

def z1187 : W := mkw 0x20800410a0040944 0x1082001042801025 0x51020c31e24c1fff 0xbd440830c789307f

def z1188 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x89bff3fe1a019810 0x8626ffcff8680660

def z1189 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0xffcfff0fe0000000 0x17ff3ffc3f800000

def z1190 : W := mkw 0x20800410a0040944 0x1082001042801025 0x7fcbcc31e24c1fff 0xbdff2f30c789307f

def z1191 : W := mkw 0x1f0040021ffaa683 0xe07c0100087fea9a 0x001000001fffe7ff 0xe0004000007fff9f

def z1192 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x0010000019c3e7fa 0xe000400000670f9f

def z1193 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfd9c30f99c3873b 0xff7f670c3e670e1c

def z1194 : W := mkw 0x0b00400209d22480 0xa02c010008274892 0x000000001df264ef 0xe00000000077c993

def z1195 : W := mkw 0x0e00400209ea8601 0xc03801000827aa18 0x0010000019ff871e 0xe00040000067fe1c

def z1196 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdc99c30f99c3871a 0x5772670c3e670e1c

def z1197 : W := mkw 0x8a0e42a209c28620 0xc228390a88270a18 0xc3fe03f019c3871a 0xef0ff80fc0670e1c

def z1198 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc0bc03f01e03f839 0xef02f00fc0780fe0

def z1199 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3fe03f01e03f839 0xef0ff80fc0780fe0

def z1200 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc307ffc1cff 0xfdff3ff0c1fff073

def z1201 : W := mkw 0x1f0040021ffb7483 0xa07c0100087fedd2 0x001000001ffffcff 0xe0004000007ffff3

def z1202 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddddf30f9df3871a 0xf77777cc3e77ce1c

def z1203 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x330ffc001ffc0007 0xe0cc3ff0007ff000

def z1204 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01fb3f83f 0xef0ff80fc07ecfe0

def z1205 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x2ecffc001fbc0007 0x60bb3ff0007ef000

def z1206 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3e05fc0005fc0007 0x00f817f00017f000

def z1207 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xacadf3ce60000000 0x12b2b7cf39800000

def z1208 : W := mkw 0x60008519a000000c 0x0180021466800000 0x3c01cc0fe0000000 0x10f007303f800000

def z1209 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3c03fc3fe0000000 0x10f00ff0ff800000

def z1210 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x000000001ffc0707 0xe0000000007ff01c

def z1211 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1b17 0xbfffbfffff89306c

def z1212 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3f4bfc001bfc0007 0xa0fd2ff0006ff000

def z1213 : W := mkw 0xf42fbffdf629503f 0x07d0befff7d8a540 0xfffffffffe3ff83d 0xfffffffffff8ffe0

def z1214 : W := mkw 0x60808519a004094c 0x1182021466801025 0x7f43cc3fe24c1fff 0xbdfd0f30ff89307f

def z1215 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x83fe03f01e03f821 0xea0ff80fc0780fe0

def z1216 : W := mkw 0x20800410a0040944 0x1082001042801025 0x55420c31e24c1ffa 0xbd550830c789307f

def z1217 : W := mkw 0x0300104640922480 0xa00c004119024892 0xece430ce65b264ce 0x73b390c33996c993

def z1218 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0026028 0x1fffbfffff800980

def z1219 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x37520c001bcf871f 0xe0dd4830006f3e1c

def z1220 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x088ffc001fbc0000 0x40223ff0007ef000

def z1221 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0xc010030019c3871a 0xe700400c00670e1c

def z1222 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3e07fc0001fc0006 0x00f81ff00007f000

def z1223 : W := mkw 0xf4afbffdf62c097f 0x17d2befff7d8b025 0xffefffffe67c1fff 0xbfffbfffff99f07f

def z1224 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0x7fcffc3fe0000000 0x1dff3ff0ff800000

def z1225 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc1f803f01e03f839 0xef07e00fc0780fe0

def z1226 : W := mkw 0x400fa90900000038 0x05003ea424000000 0xbfcfff0e00000000 0x02ff3ffc38000000

def z1227 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xebfffffe7e03f839 0xefaffffff9f80fe0

def z1228 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x190bfc001bfc0000 0x80642ff0006ff000

def z1229 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3f47fc0007fc0007 0xa0fd1ff0001ff000

def z1230 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xcbfe33f01fb3f839 0xef2ff8cfc07ecfe0

def z1231 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe019811 0xfffffffffff80660

def z1232 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x001000001bcf871f 0xe0004000006f3e1c

def z1233 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xbfdfff001fff8007 0xe2ff7ffc007ffe00

def z1234 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xfffdc3cffdc3e7ff 0xfffff70f3ff70f9f

def z1235 : W := mkw 0x0300104640922480 0xa00c004119024892 0xfee43cce65fe64ef 0x7bfb90f33997f993

def z1236 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x2801fc0001bc0004 0x00a007f00006f000

def z1237 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e7fc1fff 0xfddd0830c79ff07f

def z1238 : W := mkw 0xf02fafb9b601503e 0x07c0bebee6d80540 0xdddbcf3f9a039818 0xf7776f3cfe680e60

def z1239 : W := mkw 0x0f00400209fa2481 0xa03c01000827e892 0x0000000005fe64ef 0x600000000017f993

def z1240 : W := mkw 0x400fa90900000038 0x05003ea424000000 0x3fcffc0f80000000 0x10ff3ff03e000000

def z1241 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1dd9c30f99c18712 0xf477670c3e67061c

def z1242 : W := mkw 0x4000810900000008 0x0100020424000000 0xddd9c30f80038018 0x1777670c3e000e00

def z1243 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7d41fc0fe0000000 0x15f507f03f800000

def z1244 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0xffeffff01ffe602f 0xefffbfffc07ff980

def z1245 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1be03f01e03f838 0xcf06f80fc0780fe0

def z1246 : W := mkw 0x4000810900000008 0x0100020424000000 0x5d41c00f80000000 0x157507003e000000

def z1247 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffe026029 0xffffbffffff80980

def z1248 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe64e7fff 0xffffbfffff9939ff

def z1249 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80000718 0x1777270c3e00001c

def z1250 : W := mkw 0xe02097fde001500c 0x0380825ff7800540 0xddf9c3fff803f838 0xff77e70fffe00fe0

def z1251 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xc8a9c3ffe0000000 0x1f22a70fff800000

def z1252 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0xffeffccfe0000000 0x1bffbff33f800000

def z1253 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7e41fc0fe0000000 0x19f907f03f800000

def z1254 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1d19c30f99c3871a 0xf474670c3e670e1c

def z1255 : W := mkw 0x500e81091600002a 0x01403a0424580000 0xdfcfc30f9e000001 0xf77f3f0c3e780000

def z1256 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0x7fdffc301ffff83f 0xedff7ff0c07fffe0

def z1257 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffa000000 0x9fffbfffffe80000

def z1258 : W := mkw 0x4000810900000008 0x0100020424000000 0xccc9c30e00000000 0x1333270c38000000

def z1259 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1fd6 0x9fffbfffff89307f

def z1260 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001bfc0006 0x80ff3ff0006ff000

def z1261 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xfffffff19fffff3f 0xffffffffc67ffffc

def z1262 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x81be03f01e03f839 0xe606f80fc0780fe0

def z1263 : W := mkw 0x20800410a0040944 0x1082001042801025 0x33020c31e24c1fff 0xaccc0830c789307f

def z1264 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e03f810 0xcf0ff80fc0780fe0

def z1265 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfffc3ff9fc3ff3b 0xff7fff0ffe7f0ffc

def z1266 : W := mkw 0xe0a097fde004094c 0x1382825ff7801025 0xffebcfffe24c1fff 0xbfffaf3fff89307f

def z1267 : W := mkw 0x9a8e42a21fc7df62 0xd26a390a887f1f7d 0xc3fe03f01fcfffff 0xef0ff80fc07f3fff

def z1268 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbeafffffe0000000 0x1afabfffff800000

def z1269 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd9d9c30f99c38318 0xe767670c3e670e0c

def z1270 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffe4c0007 0xffffbffffff93000

def z1271 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x8aaff3fe06007821 0x0a2abfcff81801e0

def z1272 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0xddedc3cf80000000 0x1777b70f3e000000

def z1273 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe3fe03f07e03f8fd 0xef8ff80fc1f80fe3

def z1274 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe5b004ef 0x7fffbfffff96c013

def z1275 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xdbefffff80000000 0x0f6fbffffe000000

def z1276 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3feffcffe0000000 0x18ffbff3ff800000

def z1277 : W := mkw 0x4000810900000008 0x0100020424000000 0x9989c30f80000000 0x0666270c3e000000

def z1278 : W := mkw 0x20800410a0040944 0x1082001042801025 0x76020c31e24c1fff 0x1dd80830c789307f

def z1279 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffa019839 0xbfffffffffe80660

def z1280 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3c01fc0fe24c1fff 0xb0f007f03f89307f

def z1281 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffefffffe6027829 0x7fffbfffff9809e0

def z1282 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffeffcc01ffc0007 0xebffbff3007ff000

def z1283 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc37203f01e03f839 0xef0dc80fc0780fe0

def z1284 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe43260ed 0x7fffbfffff90c983

def z1285 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc01fffc07ff 0xfdff3ff007fff01f

def z1286 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe24c04ef 0xbfffbfffff893013

def z1287 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x813a03f01a03f810 0x8604e80fc0680fe0

def z1288 : W := mkw 0x500081091601500a 0x0140020424580540 0xddd9c30f9e03f839 0xf777670c3e780fe0

def z1289 : W := mkw 0x20800410a0040944 0x1082001042801025 0x73020c31e24c1ffd 0x9dcc0830c789307f

def z1290 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe00007c0 0x1fffbfffff80001f

def z1291 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x8beff3ce00000000 0x022fbfcf38000000

def z1292 : W := mkw 0x4000810900000008 0x0100020424000000 0xffcbcf0f80000000 0x17ff2f3c3e000000

def z1293 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe03000c4 0x1fffbfffff80c003

def z1294 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xd021cfffe0000000 0x1f40873fff800000

def z1295 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x001000001d83e000 0x4000400000760f80

def z1296 : W := mkw 0x60808519a004094c 0x1182021466801025 0xffdbcf3ffa4f9fff 0xffff6f3cffe93e7f

def z1297 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3f43fc0fe0000000 0x10fd0ff03f800000

def z1298 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3c09ff0fe0000000 0x10f027fc3f800000

def z1299 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xeaafffffe0000000 0x1faabfffff800000

def z1300 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x001000001bc39f3b 0xe0004000006f0e7c

def z1301 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3c01fc0007fc0007 0x00f007f0001ff000

def z1302 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x1dcffc001ffc0002 0xe0773ff0007ff000

def z1303 : W := mkw 0x4000810900000008 0x0100020424000000 0xdfcbc33f82001839 0xbf7f2f0cfe080060

def z1304 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfee7fcffe0000000 0x1bfb9ff3ff800000

def z1305 : W := mkw 0x800f3ae440000030 0x06003ceb91000000 0xffeffffe60000000 0x1fffbffff9800000

def z1306 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc03803f01803f838 0x0f00e00fc0600fe0

def z1307 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x1801fc0001fc0000 0x006007f00007f000

def z1308 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xd3fe0ff01e4ff839 0xef4ff83fc0793fe0

def z1309 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3f43fc0001fc0006 0x00fd0ff00007f000

def z1310 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x88bdf3ce18038000 0x4222f7cf38600e00

def z1311 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3c03fc0003fc0006 0x00f00ff0000ff000

def z1312 : W := mkw 0xd02fbbed5600003a 0x0740beefb5580000 0x8beff3ce1e000001 0xe22fbfcf38780000

def z1313 : W := mkw 0xd02fbbed5600003a 0x0740beefb5580000 0x88adf3ce1c000000 0x4222b7cf38700000

def z1314 : W := mkw 0x400fa90900000038 0x05003ea424000000 0xffcfff0f824c071f 0xb7ff3ffc3e09301c

def z1315 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x8029c3ce00000000 0x0200a70f38000000

def z1316 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffa03f838 0x9fffffffffe80fe0

def z1317 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdcd9c30f99c3870a 0x7373670c3e670e1c

def z1318 : W := mkw 0x6021ad19a000001c 0x058086b466800000 0xddc9cf0f80000000 0x1777273c3e000000

def z1319 : W := mkw 0x4000914d40000008 0x0100024535000000 0xffedf3cfe04007ff 0xbfffb7cf3f81001f

def z1320 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce67fe64ef 0xfbbb90c3399ff993

def z1321 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc13803f01803f838 0x8f04e00fc0600fe0

def z1322 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffc03e018 0xfffffffffff00f80

def z1323 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xffcbff3fe0000000 0x1fff2ffcff800000

def z1324 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xfde9ffffe0000000 0x1ff7a7ffff800000

def z1325 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc03003f01c03f838 0x4f00c00fc0700fe0

def z1326 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0400002 0xbfffbfffff810000

def z1327 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe20c1800 0x1fffbfffff883060

def z1328 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x110bcf3fe0000000 0x14442f3cff800000

def z1329 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3c01fc001bfc0006 0x80f007f0006ff000

def z1330 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x2c01f00e60000000 0x10b007c039800000

def z1331 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9d99c30f99c38712 0xd676670c3e670e1c

def z1332 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f9bc39f3b 0xf777670c3e6f0e7c

def z1333 : W := mkw 0x940f2aa016295033 0x06503caa8058a540 0xc3fe0ff01e0ff839 0xef0ff83fc0783fe0

def z1334 : W := mkw 0xc12fbbed401020b8 0x2704beefb5004082 0xaaadf3ce643060e5 0x0aaab7cf3990c183

def z1335 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f9df3871f 0xf777670c3e77ce1c

def z1336 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7e60cf1e24c1fff 0xbfdf9833c789307f

def z1337 : W := mkw 0x800002a000015000 0x0200000a80000540 0xc3fa03f01a03f839 0xef0fe80fc0680fe0

def z1338 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffedf0ce65b264ef 0x7bffb7c33996c993

def z1339 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0xf7da0f31fbcf9fff 0xffdf683cc7ef3e7f

def z1340 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1fc03f01c03f838 0xef07f00fc0700fe0

def z1341 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc301ffc1817 0xe4ff3ff0c07ff060

def z1342 : W := mkw 0x4000810900000008 0x0100020424000000 0x9dc9c30e00000000 0x0277270c38000000

def z1343 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xddd9c30f99c3e7fa 0xf777670c3e670f9f

def z1344 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3feffcc01ffc6027 0xe8ffbff3007ff180

def z1345 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x0000000001f007c6 0x000000000007c01f

def z1346 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3c01fc0fe1b00006 0x10f007f03f86c000

def z1347 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xbdafffffe0000000 0x16f6bfffff800000

def z1348 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe04c07ef 0x3fffbfffff81301f

def z1349 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe00060e0 0x1fffbfffff800183

def z1350 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffffffffe603f839 0x1fffffffff980fe0

def z1351 : W := mkw 0x100f384456000032 0x04403ce111580000 0xffeffcce7e026029 0xfbffbff339f80980

def z1352 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffefffffe67c0007 0xbfffbfffff99f000

def z1353 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc7fe03f01e03fc3b 0xff1ff80fc0780ff0

def z1354 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f81800002 0x7777270c3e060000

def z1355 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0cd0000019c3871a 0xe033400000670e1c

def z1356 : W := mkw 0x602fbd5de000003c 0x0580bef577800000 0x3d0bfc0fe0000000 0x10f42ff03f800000

def z1357 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdffdc3cf99c3871a 0xff7ff70f3e670e1c

def z1358 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xdbffffff9e03f839 0xef6ffffffe780fe0

def z1359 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x001000001df3871a 0xe00040000077ce1c

def z1360 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddf9c3cf99c3e73a 0xff77e70f3e670f9c

def z1361 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1119c30f98418710 0x9444670c3e61061c

def z1362 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x34000c01e1cc07c6 0x10d000300787301f

def z1363 : W := mkw 0x0100104440102080 0x2004004111004082 0xeee430ce65b060e7 0x7bbb90c33996c183

def z1364 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0xcbefc3fe00000000 0x0f2fbf0ff8000000

def z1365 : W := mkw 0x608fad19a004097c 0x15823eb466801025 0xffcfff3fe24c1fff 0xbfff3ffcff89307f

def z1366 : W := mkw 0x60808519a004094c 0x1182021466801025 0xfdc9cf0fe04c07c6 0x17f7273c3f81301f

def z1367 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xe3fe3ff01e03f839 0xef8ff8ffc0780fe0

def z1368 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x0010030199c3871a 0xe400400c06670e1c

def z1369 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x1c01f00f80000000 0x107007c03e000000

def z1370 : W := mkw 0x4800c10909408208 0x4120030424250208 0x9999c30f98418310 0x8666670c3e61060c

def z1371 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffe03fff9 0xfffffffffff80fff

def z1372 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xdfefc3ff86007821 0x1f7fbf0ffe1801e0

def z1373 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xd7fe03f01e43f83b 0xef5ff80fc0790fe0

def z1374 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffff843871a 0xffffffffffe10e1c

def z1375 : W := mkw 0x4080810900040948 0x1102020424001025 0xddc9c30f824c1fff 0xb777270c3e09307f

def z1376 : W := mkw 0x20800410a0040944 0x1082001042801025 0x35020c31e24c1fff 0xb4d40830c789307f

def z1377 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x1801fc0f80000000 0x006007f03e000000

def z1378 : W := mkw 0x6121bd5de010209c 0x258486f577804082 0x3e25fccfe43060e5 0x18f897f33f90c183

def z1379 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0000000019c00702 0xe00000000067001c

def z1380 : W := mkw 0x9e0e42a21febd623 0xc278390a887faf58 0xc3fe03f01fffff3f 0xef0ff80fc07ffffc

def z1381 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xffeffff01ffc7827 0xefffbfffc07ff1e0

def z1382 : W := mkw 0x3f804412bffe2dc7 0xb0fe01104afff8b7 0x77420c31fffe7fff 0xfddd0830c7fff9ff

def z1383 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x001000001df3871f 0xe00040000077ce1c

def z1384 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xc8adf3ffe0001ff8 0x1f22b7cfff80007f

def z1385 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfeedffcfe0000000 0x1bfbb7ff3f800000

def z1386 : W := mkw 0x4000810900000008 0x0100020424000000 0xc9d9c30e18038018 0xe727670c38600e00

def z1387 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c33f99c39f3a 0xff77670cfe670e7c

def z1388 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x288dfc001dbc0004 0x40a237f00076f000

def z1389 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xbcadffce00000000 0x02f2b7ff38000000

def z1390 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x0000000003cc1fff 0xa0000000000f307f

def z1391 : W := mkw 0xd42fbbed5628003b 0x0750beefb558a000 0xaaafffce063c0005 0x02aabfff3818f000

def z1392 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xfffffffffa4f9fff 0xffffffffffe93e7f

def z1393 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe4306000 0x1fffbfffff90c180

def z1394 : W := mkw 0x6080955de004094c 0x1182025577801025 0xffefffffe24c1fff 0xbfffbfffff89307f

def z1395 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0xbfefffc01ffc0007 0xe2ffbfff007ff000

def z1396 : W := mkw 0x6021ad19a000001c 0x058086b466800000 0x1c01cc0f80000000 0x107007303e000000

def z1397 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe5b060e7 0x7fffbfffff96c183

def z1398 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe4300005 0x1fffbfffff90c000

def z1399 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xccedf3ce00000000 0x1333b7cf38000000

def z1400 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3fcffc0019fc0006 0xe0ff3ff00067f000

def z1401 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xc8adf3ce60000000 0x1b22b7cf39800000

def z1402 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xddebcfffe0000000 0x1f77af3fff800000

def z1403 : W := mkw 0xc02093ed40000008 0x0300824fb5000000 0xdde9c3cf80000000 0x1777a70f3e000000

def z1404 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3e03fc3fe0000000 0x18f80ff0ff800000

def z1405 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e4ff83f 0xef0ff80fc0793fe0

def z1406 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x000000001ffc04c7 0xe0000000007ff013

def z1407 : W := mkw 0x4e00c10b09ea8609 0xc13803042c27aa18 0xddd9c30f99ff871e 0xf777670c3e67fe1c

def z1408 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x001000001db3e000 0x400040000076cf80

def z1409 : W := mkw 0xe021bffde001501c 0x078086fff7800540 0xfc31ffffe003f838 0x1ff0c7ffff800fe0

def z1410 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffc0000 0xc0ff3ff0007ff000

def z1411 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe63cfe67fe7cff 0xffff98f3f99ff9f3

def z1412 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xd3efcfffe0000000 0x1f4fbf3fff800000

def z1413 : W := mkw 0xa02f3ef4e0000034 0x0680bcfbd3800000 0xffeffcfe60000000 0x1bffbff3f9800000

def z1414 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xbc21ffcfe0000000 0x12f087ff3f800000

def z1415 : W := mkw 0x4000810900000008 0x0100020424000000 0xffc9c30fe00004ef 0x3fff270c3f800013

def z1416 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99838718 0x5777670c3e660e1c

def z1417 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffdfff019fff871f 0xf7ff7ffc067ffe1c

def z1418 : W := mkw 0x0001384440000010 0x040004e111000000 0x3c01fc0e60000000 0x10f007f039800000

def z1419 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc019ffc0317 0xe4ff3ff0067ff00c

def z1420 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe24c071f 0xbfffbfffff89301c

def z1421 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xdc21c3ffe0000000 0x1f70870fff800000

def z1422 : W := mkw 0x9c0f6aa01f680033 0x06703daa807da000 0x3feffcf01ffc0007 0xe8ffbff3c07ff000

def z1423 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfdbc33f99c3871a 0xff7f6f0cfe670e1c

def z1424 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x77520c019fff871f 0xf5dd4830067ffe1c

def z1425 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3c25fccfe0000000 0x10f097f33f800000

def z1426 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0x0010000019cf87de 0xe000400000673e1f

def z1427 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0x7f4bff3fe24c1fff 0xbdfd2ffcff89307f

def z1428 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xaabffff01fbff825 0x4aaaffffc07effe0

def z1429 : W := mkw 0x2a004412a9c28604 0xc0a801104aa70a18 0x77520c31f9c3871a 0xfddd4830c7e70e1c

def z1430 : W := mkw 0x4021b94d40000018 0x050086e535000000 0xeee5f0ce60000000 0x1bbb97c339800000

def z1431 : W := mkw 0x0f00400209fa2481 0xa03c01000827e892 0x0000000001fc04c6 0x000000000007f013

def z1432 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffa4d9fff 0xbfffffffffe9367f

def z1433 : W := mkw 0x800e02a000015020 0x0200380a80000540 0xc3fe03f01803f838 0xef0ff80fc0600fe0

def z1434 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xd1d9c30f98438718 0xf747670c3e610e1c

def z1435 : W := mkw 0x60808519a004094c 0x1182021466801025 0x3c01cc0fe04c07c6 0x10f007303f81301f

def z1436 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9dd9c30f99c38702 0xf277670c3e670e1c

def z1437 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0xcbffc3fe1e03f839 0xef2fff0ff8780fe0

def z1438 : W := mkw 0x0c0f680009680031 0x04303da00025a000 0x3d0bfc0001fc0006 0x00f42ff00007f000

def z1439 : W := mkw 0x4800c10909408208 0x4120030424250208 0xddd9c30f99c18312 0xf777670c3e67060c

def z1440 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3f2fffffe0000000 0x1cfcbfffff800000

def z1441 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffddf30f99c3871a 0xf7ff77cc3e670e1c

def z1442 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xdbfffff01ffff839 0xef6fffffc07fffe0

def z1443 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430fe65b27cff 0x7fbb90c3f996c9f3

def z1444 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f19e03ff39 0xff0ff80fc6780ffc

def z1445 : W := mkw 0x200f3c54e0000034 0x04803cf153800000 0xffeffcffe0000000 0x1fffbff3ff800000

def z1446 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x435200301bc39f3b 0xed0d4800c06f0e7c

def z1447 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0020008 0x7fffbfffff800800

def z1448 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0118030019c3871a 0xe404600c00670e1c

def z1449 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3dcdfc001dfc0006 0xe0f737f00077f000

def z1450 : W := mkw 0x4021b94d40000018 0x050086e535000000 0xddc9f30f80000000 0x177727cc3e000000

def z1451 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x7e41fc0061fc04ef 0x39f907f00187f013

def z1452 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65f267ff 0xfbbb90c33997c99f

def z1453 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc001ffc002f 0xe9ff3ff0007ff000

def z1454 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x8889f30e00000000 0x022227cc38000000

def z1455 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0x3d1bff3ffa019810 0x94f46ffcffe80660

def z1456 : W := mkw 0xf4afbffdf62c097f 0x17d2befff7d8b025 0xffefffffe63c18e5 0x1fffbfffff98f063

def z1457 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x77500001fdf3e7ff 0xfddd400007f7cf9f

def z1458 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e64e7fff 0xfddd0830c79939ff

def z1459 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x77420c31e3cc1fff 0xbddd0830c78f307f

def z1460 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0181fc0706 0x10f007f00607f01c

def z1461 : W := mkw 0xd00e83a91601502a 0x03403a0ea4580540 0x88bdc3ce1c03e000 0x4222f70f38700f80

def z1462 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xffedf3cfe0000000 0x1fffb7cf3f800000

def z1463 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3c01fc0019fc0006 0xe0f007f00067f000

def z1464 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfe27ffffe0000000 0x1ff89fffff800000

def z1465 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xeffe33f07fb3fcff 0xffbff8cfc1fecff3

def z1466 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xffffffc01fffe01f 0xe7ffffff007fff80

def z1467 : W := mkw 0x1c0168001f680013 0x047005a0007da000 0x3f43fc001ffc0007 0xe0fd0ff0007ff000

def z1468 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffffffffe003e000 0x1fffffffff800f80

def z1469 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xd3ffcff01e03f839 0xef4fff3fc0780fe0

def z1470 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xbffffff01ffff827 0xeaffffffc07fffe0

def z1471 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7e41fc0fe00004ef 0x39f907f03f800013

def z1472 : W := mkw 0x0300104640922480 0xa00c004119024892 0xee2430ce65b264ef 0x1bb890c33996c993

def z1473 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffefffffe4006000 0x1fffbfffff900180

def z1474 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3dcbfc001bfc0006 0xe0f72ff0006ff000

def z1475 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x575200319fc3ff3b 0xfd5d4800c67f0ffc

def z1476 : W := mkw 0x20800410a0040944 0x1082001042801025 0xffc20c3fe24c1fff 0xbfff0830ff89307f

def z1477 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0xd7fe03f19fc3ff3b 0xff5ff80fc67f0ffc

def z1478 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdbc33ffbc39fff 0xffff6f0cffef0e7f

def z1479 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x7f67fcffe0000000 0x1dfd9ff3ff800000

def z1480 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80020008 0x7777270c3e000800

def z1481 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e03fcff 0xef0ff80fc0780ff3

def z1482 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xd3ffcffffe03f839 0xff4fff3ffff80fe0

def z1483 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x7fdfff301ffd983f 0xedff7ffcc07ff660

def z1484 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaca430ce65b264ef 0x72b290c33996c993

def z1485 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c1bf5 0x9fffbfffff89306f

def z1486 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xfffffffffe03e001 0xfffffffffff80f80

def z1487 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3d03fc0003fc0006 0x80f40ff0000ff000

def z1488 : W := mkw 0xba8e46b2bfc7df66 0xd2ea391acaff1f7d 0xf7fe0ff1ffcfffff 0xffdff83fc7ff3fff

def z1489 : W := mkw 0x500fa9091600003a 0x05403ea424580000 0xffdfff0f9e038019 0xf7ff7ffc3e780e00

def z1490 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xa8adffce60000000 0x02a2b7ff39800000

def z1491 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfcc1fc0fe0000000 0x13f307f03f800000

def z1492 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xc8adf3fe00000000 0x0f22b7cff8000000

def z1493 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc3fe03f01e43ff3b 0xef0ff80fc0790ffc

def z1494 : W := mkw 0x20800410a0040944 0x1082001042801025 0x36020c31e24c1fff 0xb8d80830c789307f

def z1495 : W := mkw 0xc12fbbed401020b8 0x2704beefb5004082 0x88adf3ce04306000 0x0222b7cf3810c180

def z1496 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xaaadf3ce60000000 0x0aaab7cf39800000

def z1497 : W := mkw 0x4021b94d40000018 0x050086e535000000 0x88a5f0ce00000000 0x022297c338000000

def z1498 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2001810 0x9fffbfffff880060

def z1499 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xd12bcfffe24c1ff8 0x9f44af3fff89307f

def z1500 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77ca0c31fa4c1fff 0xfddf2830c7e9307f

def z1501 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe40264ef 0x7fffbfffff900993

def z1502 : W := mkw 0x2a804412a9c68f44 0xd0aa01104aa71a3d 0x11120c319bcf9f1a 0xe4444830c66f3e7c

def z1503 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80400002 0xb777270c3e010000

def z1504 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe2001ff9 0xbfffbfffff88007f

def z1505 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc007ffc00e7 0xe8ff3ff001fff003

def z1506 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x2a27fcfe60000000 0x08a89ff3f9800000

def z1507 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xddefffff80000000 0x1777bffffe000000

def z1508 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe00004c6 0x1fffbfffff800013

def z1509 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc1fe03f01e03f818 0xe707f80fc0780fe0

def z1510 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0xc821f3ffe0000000 0x1f2087cfff800000

def z1511 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37020c31e24c1ff7 0x9cdc0830c789307f

def z1512 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xd9afffffe0000000 0x1f66bfffff800000

def z1513 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x83be03f01e03f831 0xce0ef80fc0780fe0

def z1514 : W := mkw 0x60808519a004094c 0x1182021466801025 0xddcbcf3f824c1b10 0x97772f3cfe09306c

def z1515 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe04007ff 0xbfffbfffff81001f

def z1516 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3c01fc0fe04c0006 0x10f007f03f813000

def z1517 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe20c1ffd 0x1fffbfffff88307f

def z1518 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xdfeff3ff80000000 0x1f7fbfcffe000000

def z1519 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdbcf0ffbcf87ff 0xffff6f3c3fef3e1f

def z1520 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0400702 0x1fffbfffff81001c

def z1521 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9899c30f99c38300 0x4262670c3e670e0c

def z1522 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xf76bcfffe0000000 0x1fddaf3fff800000

def z1523 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0x3e27fcffe6007821 0x18f89ff3ff9801e0

def z1524 : W := mkw 0xf12fbffdf61170be 0x27c4befff7d845c2 0xffefffffe63078e5 0x1fffbfffff98c1e3

def z1525 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3fcbfc001bfc0007 0xe0ff2ff0006ff000

def z1526 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe7fc0007 0xffffbfffff9ff000

def z1527 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x001000001bc39f1a 0xe0004000006f0e7c

def z1528 : W := mkw 0xc00083a900000008 0x0300020ea4000000 0xdde9c3ff80000000 0x1f77a70ffe000000

def z1529 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee63cce67be64ef 0x7bbb98f3399ef993

def z1530 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xfffffffffe038019 0xfffffffffff80e00

def z1531 : W := mkw 0xe0a1bffde004095c 0x178286fff7801025 0xff63ffffe24c1fff 0xbffd8fffff89307f

def z1532 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xcbeff3fe02001839 0xaf2fbfcff8080060

def z1533 : W := mkw 0xe0a1bffde004095c 0x178286fff7801025 0xfc21ffffe04c1ffe 0x1ff087ffff81307f

def z1534 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe00c00c4 0x1fffbfffff803003

def z1535 : W := mkw 0xe0afbffde005597c 0x1782befff7801565 0xffffffffe24fffff 0xbfffffffff893fff

def z1536 : W := mkw 0x4000810900000008 0x0100020424000000 0xd109c30f80000000 0x1744270c3e000000

def z1537 : W := mkw 0x030f2802009224b0 0xa40c3ca008024892 0x3fcffc0005b264ef 0x60ff3ff00016c993

def z1538 : W := mkw 0x8a0042a209c3d600 0xc228010a88270f58 0xc03003f019c3ff3a 0xef00c00fc0670ffc

def z1539 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xffefffffe64c7fff 0xbfffbfffff9931ff

def z1540 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xaeedf3ce05b00007 0x62bbb7cf3816c000

def z1541 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3fc7fc0007fc0007 0xe0ff1ff0001ff000

def z1542 : W := mkw 0x900e02a016015022 0x0240380a80580540 0x80bc03f01c03f810 0x4602f00fc0700fe0

def z1543 : W := mkw 0x0a80400209c68f40 0xd02a010008271a3d 0xc3da03301bcf9fff 0xef0f680cc06f3e7f

def z1544 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0x023600f01fc3ff3b 0xe808d803c07f0ffc

def z1545 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0x1d0bcf3f80000000 0x14742f3cfe000000

def z1546 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe04c0300 0x1fffbfffff81300c

def z1547 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffcffc001ffe000f 0xe3ff3ff0007ff800

def z1548 : W := mkw 0x9b0e42a21fd3f6a2 0xe26c390a887f4fda 0xc3fe03f01ff3ffff 0xef0ff80fc07fcfff

def z1549 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xf7fe0ff07e4ffcff 0xffdff83fc1f93ff3

def z1550 : W := mkw 0x0300104640922480 0xa00c004119024892 0x88a430ce65b260e0 0x4a2290c33996c983

def z1551 : W := mkw 0x60008519a000000c 0x0180021466800000 0xfdc9cf0fe0000000 0x17f7273c3f800000

def z1552 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0x7f67fcffe24c1fff 0xbdfd9ff3ff89307f

def z1553 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x000000001db26000 0x400000000076c980

def z1554 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0000018 0xbfffbfffff800000

def z1555 : W := mkw 0xe02087b9a000000c 0x0380821ee6800000 0xddc9c33f80000000 0x1777270cfe000000

def z1556 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc37a03f01a03f839 0xaf0de80fc0680fe0

def z1557 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe1800002 0x7fffbfffff860000

def z1558 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffddf30ffdf387ff 0xffff77cc3ff7ce1f

def z1559 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe0001b10 0x1fffbfffff80006c

def z1560 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x8098030019c3871a 0xe202600c00670e1c

def z1561 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffd9c30f99c3871f 0xf7ff670c3e670e1c

def z1562 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xbcbdffcffc03e000 0x52f2f7ff3ff00f80

def z1563 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1919c30f99c18310 0x8464670c3e67060c

def z1564 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f98438718 0x9777670c3e610e1c

def z1565 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x88adf3fe60000000 0x0a22b7cff9800000

def z1566 : W := mkw 0x900002a016015002 0x0240000a80580540 0xc03003f01a03f838 0x8f00c00fc0680fe0

def z1567 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xffe7fcffe0000000 0x1fff9ff3ff800000

def z1568 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x001000001983840a 0x6000400000660e10

def z1569 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe63ccfe7fe67ff 0xffff98f33f9ff99f

def z1570 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x88adf3ce05b00000 0x4222b7cf3816c000

def z1571 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdfff0f9fff871f 0xf7ff7ffc3e7ffe1c

def z1572 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0x0010000019f387de 0xe00040000067ce1f

def z1573 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b064e7 0x1bbb90c33996c193

def z1574 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x99bffff01ffff810 0xc666ffffc07fffe0

def z1575 : W := mkw 0x4000810900000008 0x0100020424000000 0xdcc1c00f80000000 0x137307003e000000

def z1576 : W := mkw 0x900f2aa016015032 0x06403caa80580540 0xcbfff3f01e03f839 0xef2fffcfc0780fe0

def z1577 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0010000019838018 0xe000400000660e00

def z1578 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3e41fc0001fc0007 0x20f907f00007f000

def z1579 : W := mkw 0x0300104640922480 0xa00c004119024892 0xfee430cfe5f267ef 0x7bfb90c33f97c99f

def z1580 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffefffffe7bc0007 0x7fffbfffff9ef000

def z1581 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x3fcfff3fe0000000 0x14ff3ffcff800000

def z1582 : W := mkw 0x6121bd5de010209c 0x258486f577804082 0x3c01fc0fe03000c4 0x10f007f03f80c003

def z1583 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9c99c30f99c3871a 0xf272670c3e670e1c

def z1584 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xccd9c30f9983871a 0x7733670c3e660e1c

def z1585 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x5540000181c0071a 0xb55500000607001c

def z1586 : W := mkw 0x20800410a0040944 0x1082001042801025 0x75020c31e24c1ffe 0x9dd40830c789307f

def z1587 : W := mkw 0xc00083a900015008 0x0300020ea4000540 0xddf9c3ff8003f838 0x1f77e70ffe000fe0

def z1588 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeffe33fe7fb3fcff 0xffbff8cff9fecff3

def z1589 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x0000000001c2070a 0x600000000007081c

def z1590 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffffffc01fffe03f 0xefffffff007fff80

def z1591 : W := mkw 0x402fb94d40000038 0x0500bee535000000 0x3fcffc0e00000000 0x00ff3ff038000000

def z1592 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xd129c3ffe0000000 0x1f44a70fff800000

def z1593 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffe602f 0xe0ff3ff0007ff980

def z1594 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffd9c30ff9c3871a 0xffff670c3fe70e1c

def z1595 : W := mkw 0xc02faba900000038 0x0700beaea4000000 0x8889c30e00000000 0x0222270c38000000

def z1596 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffff8038000 0x5fffffffffe00e00

def z1597 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xc9fdf3ce18038018 0xe727f7cf38600e00

def z1598 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0xfdc9ff0fe04c07de 0xb7f727fc3f81301f

def z1599 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xffdfff301fff981f 0xe7ff7ffcc07ffe60

def z1600 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3d0bfc001ffc0007 0xe0f42ff0007ff000

def z1601 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffeffffffc000000 0x5fffbffffff00000

def z1602 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0xdffff3ff9e03f839 0xff7fffcffe780fe0

def z1603 : W := mkw 0x4000810900000008 0x0100020424000000 0xdfedc3cf84026029 0x7f7fb70f3e100980

def z1604 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfc01ff0fe0000000 0x17f007fc3f800000

def z1605 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3c01fc0fe00004c6 0x10f007f03f800013

def z1606 : W := mkw 0xf02e97fdf601502e 0x03c0ba5ff7d80540 0xdfffc3fffe03f839 0xff7fff0ffff80fe0

def z1607 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeef433ce65b3e4ff 0x7fbbd0cf3996cf93

def z1608 : W := mkw 0x4000914d40000008 0x0100024535000000 0xeeedf3ce60000000 0x1bbbb7cf39800000

def z1609 : W := mkw 0x0000000000000000 0x0000000000000000 0xddc9c00e00000000 0x1377270038000000

def z1610 : W := mkw 0x0e00400209ea8601 0xc03801000827aa18 0x0000000001fc0706 0x000000000007f01c

def z1611 : W := mkw 0x1e0e40021fea8623 0xc0783900087faa18 0xc3de03001fff871f 0xe70f780c007ffe1c

def z1612 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffe0ff8fd 0xfffffffffff83fe3

def z1613 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0x98adffcf80000000 0x0262b7ff3e000000

def z1614 : W := mkw 0x0c01680009680011 0x043005a00025a000 0x3ec5fc0001fc0006 0x00fb17f00007f000

def z1615 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x1c19c30f99c18702 0x1070670c3e67061c

def z1616 : W := mkw 0x0300104640922480 0xa00c004119024892 0xaee430ce65b264c7 0x72bb90c33996c993

def z1617 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe24c18e7 0xbfffbfffff893063

def z1618 : W := mkw 0x4000810900000008 0x0100020424000000 0xdc01c30f80000000 0x1770070c3e000000

def z1619 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee630fe67b27cef 0x7bbb98c3f99ec9f3

def z1620 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xf7fe0ff01e03f839 0xefdff83fc0780fe0

def z1621 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430cfe5b267ff 0x7fbb90c33f96c99f

def z1622 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3c01fc0fe0400702 0x10f007f03f81001c

def z1623 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fdfff001ffd8017 0xe4ff7ffc007ff600

def z1624 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffe4ffb39 0xfffffffffff93fec

def z1625 : W := mkw 0x20800410a0040944 0x1082001042801025 0x76420c31e24c1fef 0x39d90830c789307f

def z1626 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0xdfefcfff80000000 0x1f7fbf3ffe000000

def z1627 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe00004e8 0x1fffbfffff800013

def z1628 : W := mkw 0x0b00400209d2a680 0xe02c010008274a9a 0xc3fc03c01df3e7ff 0xef0ff00f0077cf9f

def z1629 : W := mkw 0x20800410a0040944 0x1082001042801025 0x34020c31e24c1fc6 0x10d00830c789307f

def z1630 : W := mkw 0x9a0e42a21fc3d622 0xc268390a887f0f58 0x011a03301bc39f1a 0xe404680cc06f0e7c

def z1631 : W := mkw 0xf0afbffdf605597e 0x17c2befff7d81565 0xfffffffffa4d9b10 0x9fffffffffe9366c

def z1632 : W := mkw 0x1a0040021fc3d602 0xc0680100087f0f58 0x001000001dc3e71a 0xe000400000770f9c

def z1633 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc13a03f01e03f839 0xef04e80fc0780fe0

def z1634 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x7c01fc3fe0000000 0x1df007f0ff800000

def z1635 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3d8ffc001ffc0006 0xc0f63ff0007ff000

def z1636 : W := mkw 0x0300104640922480 0xa00c004119024892 0xa8a430ce65b260c4 0x42a290c33996c983

def z1637 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfd2bffffe0000000 0x1ff4afffff800000

def z1638 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffeffffff8000000 0xffffbfffffe00000

def z1639 : W := mkw 0x0a00400209c20400 0x8028010008270810 0x0000000019c2040a 0xe000000000670810

def z1640 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeca430ce65b264ee 0x5bb290c33996c993

def z1641 : W := mkw 0x4000810900000008 0x0100020424000000 0x8899c30e18038000 0x4222670c38600e00

def z1642 : W := mkw 0xd02fbbed5601503a 0x0740beefb5580540 0x88bdf3ce1e03f839 0xe222f7cf38780fe0

def z1643 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe20c0005 0x1fffbfffff883000

def z1644 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0xbfffffc01ffff83f 0xe2ffffff007fffe0

def z1645 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe3fe0ff01e0ff83d 0xef8ff83fc0783fe0

def z1646 : W := mkw 0x20800410a0040944 0x1082001042801025 0x62020c31e24c1fff 0xbd880830c789307f

def z1647 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe04c1ffe 0x1fffbfffff81307f

def z1648 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f99c387ff 0xf777670c3e670e1f

def z1649 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3fcffc301ffc1807 0xe0ff3ff0c07ff060

def z1650 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xf32fffffe0000000 0x1fccbfffff800000

def z1651 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0xfc21fccfe0000000 0x1bf087f33f800000

def z1652 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe20c1cef 0x3fffbfffff883073

def z1653 : W := mkw 0x400fa90900000038 0x05003ea424000000 0xddcdf30f80000000 0x177737cc3e000000

def z1654 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xeeedf3ce600004ef 0x3bbbb7cf39800013

def z1655 : W := mkw 0x400fa90900000038 0x05003ea424000000 0x888df30e00000000 0x022237cc38000000

def z1656 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc001ffc183f 0xe0ff3ff0007ff060

def z1657 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xaaaffffe620c18e5 0x0aaabffff9883063

def z1658 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0x3e27fcffe24c1fe7 0x18f89ff3ff89307f

def z1659 : W := mkw 0x0300104640922480 0xa00c004119024892 0xcce430ce65b264ea 0x7b3390c33996c993

def z1660 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe630ffe7f27fff 0xffff98c3ff9fc9ff

def z1661 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc301ffc0007 0xedff3ff0c07ff000

def z1662 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0xcaedf3ce04026029 0x6b2bb7cf38100980

def z1663 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x7fcffc001ffc040f 0xf1ff3ff0007ff010

def z1664 : W := mkw 0xf0afbffdf604097e 0x17c2befff7d81025 0xffeffffffe4c1fff 0xffffbffffff9307f

def z1665 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0x9999c30f99c3871a 0xe666670c3e670e1c

def z1666 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xdfddc30f9dc3871b 0xf77f770c3e770e1c

def z1667 : W := mkw 0x20800410a0040944 0x1082001042801025 0x775a0f31fa4d9fff 0xbddd683cc7e9367f

def z1668 : W := mkw 0xf00e87b9b601502e 0x03c03a1ee6d80540 0xffffcffffe03f839 0xffffff3ffff80fe0

def z1669 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b260e5 0x5bbb90c33996c983

def z1670 : W := mkw 0x0800400009400000 0x0020010000250000 0x3fcffc001ffc0007 0xe0ff3ff0007ff000

def z1671 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xddd9c30f9dc3e73b 0xf777670c3e770f9c

def z1672 : W := mkw 0x0300104640922480 0xa00c004119024892 0xefec30ce7db264ef 0xfbbfb0c339f6c993

def z1673 : W := mkw 0x60808519a004094c 0x1182021466801025 0xddc9c33fe0001ff8 0x1f77270cff80007f

def z1674 : W := mkw 0xe0a097fde004094c 0x1382825ff7801025 0xdde9c3ffe0401ffa 0xbf77a70fff81007f

def z1675 : W := mkw 0x0a00400209c28600 0xc028010008270a18 0x4450000019c3871a 0xf111400000670e1c

def z1676 : W := mkw 0x4000914d40000008 0x0100024535000000 0xddedf3cf80000000 0x1777b7cf3e000000

def z1677 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3c09fc0019fc0006 0x00f027f00067f000

def z1678 : W := mkw 0x4000914d40000008 0x0100024535000000 0x88adf3ce00000000 0x0222b7cf38000000

def z1679 : W := mkw 0x6021bd5de000001c 0x058086f577800000 0x3d03fc3fe0000000 0x14f40ff0ff800000

def z1680 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x1bcffc001ffc0001 0xe06f3ff0007ff000

def z1681 : W := mkw 0x60a1bd5de004095c 0x158286f577801025 0x3d03fc3fe24c1b10 0x94f40ff0ff89306c

def z1682 : W := mkw 0x4a00c10b09c28608 0xc12803042c270a18 0xffdbcf0f99c3871a 0xf7ff6f3c3e670e1c

def z1683 : W := mkw 0x6000955de000000c 0x0180025577800000 0xffefffffe0000000 0x1fffbfffff800000

def z1684 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f80400310 0x9777270c3e01000c

def z1685 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeae430ce65b260ed 0x6bab90c33996c983

def z1686 : W := mkw 0xe021bffde000001c 0x078086fff7800000 0x3c21fcffe0000000 0x18f087f3ff800000

def z1687 : W := mkw 0xf02fbffdf600003e 0x07c0befff7d80000 0xffefffffe6000001 0x1fffbfffff980000

def z1688 : W := mkw 0x1e0040021fea8603 0xc0780100087faa18 0x001000001db38000 0x400040000076ce00

def z1689 : W := mkw 0xf42fbffdf628003f 0x07d0befff7d8a000 0xffefffffe4300000 0x1fffbfffff90c000

def z1690 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3c05fc0005fc0006 0x00f017f00017f000

def z1691 : W := mkw 0x1c0f68001f695033 0x04703da0007da540 0xffdfff001ffff83f 0xe7ff7ffc007fffe0

def z1692 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffffc03e039 0xfffffffffff00f80

def z1693 : W := mkw 0x208f3c54e0040974 0x14823cf153801025 0xffeffcffe24c1fff 0xbfffbff3ff89307f

def z1694 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xffefffffe2001800 0x1fffbfffff880060

def z1695 : W := mkw 0xc00e83a900000028 0x03003a0ea4000000 0x88adc3ce00000000 0x0222b70f38000000

def z1696 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfffffffff8018010 0x9fffffffffe00600

def z1697 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffeffcc07ffe64ef 0xfbffbff301fff993

def z1698 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x99adf3cf80000000 0x0666b7cf3e000000

def z1699 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xf7fe03f1fe43ffff 0xffdff80fc7f90fff

def z1700 : W := mkw 0xf02fafb9b601503e 0x07c0bebee6d80540 0xdfffcfff9e03f839 0xff7fff3ffe780fe0

def z1701 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe4026000 0x5fffbfffff900980

def z1702 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe04c07de 0xbfffbfffff81301f

def z1703 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xe7fe03f01e03f83f 0xef9ff80fc0780fe0

def z1704 : W := mkw 0x1f0f78465ffa24b3 0xa47c3de1197fe892 0x22263cc07ffe64ef 0xe88898f301fff993

def z1705 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xcbfff3fffe03f839 0xff2fffcffff80fe0

def z1706 : W := mkw 0xf02fbffdf601503e 0x07c0befff7d80540 0xc8bdf3fffc03f838 0x5f22f7cffff00fe0

def z1707 : W := mkw 0x0300104640922480 0xa00c004119024892 0xeee430ce65b264e8 0x5bbb90c33996c993

def z1708 : W := mkw 0xe12fbffde01020bc 0x2784befff7804082 0xffefffffe43064ef 0x3fffbfffff90c193

def z1709 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xeeeffffe60000000 0x1bbbbffff9800000

def z1710 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0xffeffcf01ffe783f 0xefffbff3c07ff9e0

def z1711 : W := mkw 0xe0afafb9a004097c 0x1782bebee6801025 0xddcbcf3f824c1f1a 0xb7772f3cfe09307c

def z1712 : W := mkw 0xc02fbbed40000038 0x0700beefb5000000 0x9dedf3ce00000000 0x0277b7cf38000000

def z1713 : W := mkw 0x20800410a0040944 0x1082001042801025 0x77420c31e24c1ff8 0x9ddd0830c789307f

def z1714 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe0400310 0x9fffbfffff81000c

def z1715 : W := mkw 0x000f384440000030 0x04003ce111000000 0x3fcffc0e60000000 0x10ff3ff039800000

def z1716 : W := mkw 0x20800410a0040944 0x1082001042801025 0x37420c31e24c1fd7 0xb4dd0830c789307f

def z1717 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xc2be03f01e03f839 0x4f0af80fc0780fe0

def z1718 : W := mkw 0xe02097fde000000c 0x0380825ff7800000 0xffebcfffe0000000 0x1fffaf3fff800000

def z1719 : W := mkw 0x400fb94d40000038 0x05003ee535000000 0xffefffcfe0000000 0x1fffbfff3f800000

def z1720 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xffefffffe2000001 0xbfffbfffff880000

def z1721 : W := mkw 0xe02fafb9a000003c 0x0780bebee6800000 0x998bcf3f80000000 0x06662f3cfe000000

def z1722 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3fcffc007ffc04c7 0xf0ff3ff001fff013

def z1723 : W := mkw 0xe02fbffde000003c 0x0780befff7800000 0xfcadffffe0000000 0x1ff2b7ffff800000

def z1724 : W := mkw 0x900e02a016015022 0x0240380a80580540 0xeffe33f01e03f839 0xefbff8cfc0780fe0

def z1725 : W := mkw 0x9c0f6aa01f695033 0x06703daa807da540 0x3d1bff301bfd9816 0x84f46ffcc06ff660

def z1726 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x3ecdfc001dfc0007 0x60fb37f00077f000

def z1727 : W := mkw 0xe0afbffde004097c 0x1782befff7801025 0xffefffffe0401ffa 0xbfffbfffff81007f

def z1728 : W := mkw 0x2b804412a9d6afc4 0xf0ae01104aa75abf 0x77520c31ffffffff 0xfddd4830c7ffffff

def z1729 : W := mkw 0x4000810900000008 0x0100020424000000 0x1c01c00f80400702 0x107007003e01001c

def z1730 : W := mkw 0xe02fbffde001503c 0x0780befff7800540 0xffffffffe403f839 0x7fffffffff900fe0

def z1731 : W := mkw 0x0300104640922480 0xa00c004119024892 0xffe430ce65f264ef 0xfbff90c33997c993

def z1732 : W := mkw 0x1f0040021ffa2483 0xa07c0100087fe892 0x000000001ffe6007 0xe0000000007ff980

def z1733 : W := mkw 0x4000810900000008 0x0100020424000000 0xddc9c30f98000000 0xf777270c3e600000

def z1734 : W := mkw 0x4b00c10b09d2a688 0xe12c03042c274a9a 0xffddf30f9df3e7ff 0xf7ff77cc3e77cf9f

def z1735 : W := mkw 0x1c0f68001f680033 0x04703da0007da000 0x188dfc001dfc0000 0x406237f00077f000

def z1736 : W := mkw 0x20800410a0040944 0x1082001042801025 0xf7620cf1e24e7fff 0xbfdd8833c78939ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z8,z4,z5,z6]),(0,[z1,z9,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z11,z6])],[(0,[z1,z2,z7,z4,z12,z5,z6]),(0,[z1,z7,z13,z4,z5,z14,z6]),(0,[z15,z16,z2,z7,z4,z5,z6])],[(0,[z17,z1,z2,z7,z18,z5,z6]),(0,[z1,z2,z7,z4,z5,z19,z6]),(0,[z1,z20,z2,z7,z4,z5,z6]),(0,[z1,z2,z21,z7,z4,z5,z22]),(0,[z23,z1,z2,z7,z4,z5,z6])],[(0,[z24,z1,z2,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z26])],[(0,[z1,z2,z7,z4,z27,z5,z6]),(0,[z28,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z29,z6])],[(0,[z1,z30,z2,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z31,z5,z6]),(0,[z1,z20,z2,z7,z4,z5,z32])],[(0,[z33,z1,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z35,z6]),(0,[z36,z1,z37,z2,z7,z4,z5]),(0,[z1,z37,z2,z7,z4,z38,z5])],[(0,[z1,z2,z7,z4,z5,z39,z6]),(0,[z40,z1,z2,z7,z4,z5,z10]),(0,[z1,z41,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z6])],[(0,[z1,z7,z4,z5,z14,z14,z6]),(0,[z1,z9,z7,z4,z5,z42,z6]),(0,[z1,z2,z7,z4,z5,z43,z6])],[(1,[z1,z2,z7,z4,z44,z6]),(0,[z1,z2,z45,z7,z4,z5,z6]),(0,[z46,z1,z2,z7,z47,z4,z5]),(0,[z48,z1,z2,z7,z4,z5,z49]),(0,[z1,z50,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z51,z5,z14,z6]),(0,[z52,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z53]),(0,[z1,z2,z7,z4,z54,z42,z6]),(0,[z1,z2,z7,z4,z5,z6,z55]),(0,[z1,z2,z7,z4,z38,z5,z32]),(0,[z56,z1,z37,z2,z7,z4,z5])],[(0,[z1,z57,z2,z7,z4,z5,z6]),(0,[z1,z2,z58,z7,z4,z5,z6]),(0,[z1,z59,z2,z7,z4,z5,z6])],[(0,[z1,z60,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z61,z4,z5,z6]),(0,[z1,z50,z2,z7,z4,z5,z32]),(0,[z62,z1,z7,z4,z5,z14,z6]),(1,[z1,z9,z7,z4,z14,z6]),(0,[z63,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z64]),(1,[z1,z2,z7,z4,z65,z6]),(0,[z1,z66,z7,z4,z67,z5,z6])],[(0,[z68,z1,z9,z7,z4,z5,z6])],[(0,[z24,z1,z2,z7,z4,z38,z5]),(0,[z17,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z69,z4,z5,z6]),(0,[z1,z70,z2,z7,z4,z5,z6]),(0,[z1,z9,z2,z7,z4,z38,z5]),(1,[z15,z1,z2,z4,z42,z6]),(0,[z1,z2,z7,z4,z5,z32,z71])]],
   [[(0,[z1,z72,z7,z4,z5,z14,z6]),(0,[z46,z1,z2,z7,z4,z5,z73]),(0,[z1,z7,z4,z54,z5,z14,z6]),(0,[z1,z2,z7,z4,z54,z5,z32]),(0,[z1,z2,z74,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z75,z5]),(0,[z1,z2,z7,z4,z5,z76,z6])],[(1,[z1,z2,z7,z4,z5,z77]),(0,[z1,z2,z7,z4,z5,z78,z6]),(0,[z1,z2,z7,z4,z5,z10,z79]),(0,[z1,z2,z7,z4,z80,z5,z6])],[(0,[z81,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z4,z5,z10,z6,z32]),(0,[z1,z2,z7,z4,z5,z82,z6]),(0,[z83,z1,z37,z2,z7,z4,z5])],[(0,[z1,z2,z84,z7,z4,z5,z10]),(1,[z1,z7,z4,z14,z42,z6]),(0,[z1,z2,z7,z80,z5,z85,z6]),(0,[z1,z86,z2,z7,z4,z5,z6])],[(0,[z1,z87,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z88,z6]),(0,[z1,z2,z89,z7,z4,z5,z6]),(0,[z90,z1,z2,z7,z4,z5,z6])],[(0,[z91,z1,z9,z7,z4,z5,z6]),(0,[z92,z1,z2,z7,z4,z38,z5])],[(0,[z40,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z93,z6]),(0,[z1,z2,z7,z94,z4,z5,z6])],[(0,[z33,z72,z2,z7,z4,z5,z6]),(0,[z48,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z95,z4,z5,z6]),(0,[z1,z9,z7,z4,z96,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z10]),(0,[z1,z97,z30,z7,z4,z5,z6])],[(0,[z68,z1,z2,z7,z4,z5,z98]),(0,[z1,z2,z7,z4,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z100,z85]),(0,[z1,z2,z7,z4,z101,z5,z6])],[(0,[z1,z2,z7,z4,z5,z14,z32]),(0,[z102,z1,z2,z7,z4,z5,z6])],[(0,[z48,z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z103,z5,z6]),(0,[z1,z2,z7,z4,z5,z104,z6]),(0,[z1,z2,z7,z47,z5,z6,z71])],[(0,[z36,z1,z2,z7,z47,z4,z5]),(0,[z1,z105,z2,z7,z4,z5,z6])],[(0,[z106,z1,z2,z7,z4,z5,z6]),(0,[z107,z1,z20,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z108,z5,z6]),(0,[z1,z2,z7,z109,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z110,z6]),(0,[z1,z2,z7,z47,z4,z5,z111]),(0,[z1,z9,z84,z7,z4,z5,z6]),(0,[z1,z112,z2,z7,z4,z5,z6])],[(0,[z1,z2,z84,z13,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z113,z6]),(0,[z114,z1,z9,z7,z4,z5,z6])],[(0,[z1,z2,z115,z7,z4,z5,z6])]],
   [[(0,[z1,z34,z7,z4,z5,z14,z6]),(0,[z81,z1,z2,z7,z47,z4,z5])],[(0,[z24,z1,z2,z7,z4,z5,z73]),(0,[z1,z2,z84,z7,z4,z5,z116]),(1,[z1,z2,z117,z7,z4,z5]),(0,[z1,z9,z7,z4,z5,z10,z6]),(0,[z1,z2,z7,z4,z5,z118,z6])],[(0,[z119,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z120,z6]),(0,[z1,z2,z84,z7,z4,z38,z5]),(0,[z36,z1,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z4,z65,z5,z6])],[(0,[z1,z9,z121,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z122])],[(0,[z1,z2,z13,z4,z5,z42,z6]),(0,[z46,z1,z2,z7,z4,z5,z53]),(0,[z46,z2,z7,z4,z5,z111,z6]),(1,[z1,z2,z7,z4,z5,z116]),(0,[z123,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z124,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z125,z5,z6]),(1,[z1,z2,z7,z4,z5,z126]),(0,[z1,z2,z127,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z38,z5])],[(0,[z1,z2,z7,z128,z4,z5,z6]),(0,[z1,z129,z2,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z131]),(0,[z1,z9,z2,z7,z4,z132,z6]),(0,[z1,z2,z7,z4,z5,z133,z6])],[(0,[z1,z2,z7,z134,z4,z5,z6]),(0,[z135,z1,z2,z7,z4,z5,z6]),(0,[z136,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z137,z5]),(0,[z1,z138,z2,z7,z4,z5,z6])],[(0,[z1,z2,z139,z7,z4,z5,z6]),(0,[z1,z2,z140,z7,z4,z5,z6]),(1,[z1,z2,z21,z141,z5,z6]),(0,[z1,z2,z7,z4,z5,z142,z73])],[(0,[z1,z2,z7,z143,z4,z5,z6])],[(0,[z1,z2,z7,z4,z144,z5,z6]),(0,[z107,z1,z37,z2,z7,z4,z5]),(0,[z15,z1,z37,z2,z7,z4,z5]),(1,[z1,z2,z7,z4,z145,z5])],[(0,[z2,z7,z4,z146,z5,z111,z6]),(0,[z1,z2,z7,z4,z54,z5,z147]),(0,[z1,z2,z7,z4,z5,z113,z6]),(0,[z1,z2,z7,z4,z148,z5,z6]),(0,[z149,z1,z2,z7,z4,z5,z73])],[(0,[z1,z2,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z150,z5,z6]),(0,[z1,z2,z7,z4,z5,z111,z6]),(0,[z1,z151,z2,z7,z4,z5,z6])],[(0,[z91,z1,z152,z7,z4,z5,z6]),(0,[z1,z2,z7,z153,z141,z5,z6]),(0,[z1,z2,z7,z154,z47,z4,z5])],[(0,[z1,z2,z7,z4,z5,z113,z32]),(0,[z1,z2,z21,z4,z5,z42,z6]),(0,[z1,z37,z2,z7,z4,z5,z42])]],
   [[(0,[z1,z2,z34,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z111,z32])],[(0,[z0,z1,z2,z7,z155,z5,z6]),(1,[z1,z2,z7,z4,z156,z6]),(0,[z1,z2,z7,z4,z5,z49,z6]),(0,[z157,z1,z2,z7,z4,z5,z158]),(0,[z1,z2,z159,z7,z4,z5,z6])],[(0,[z1,z160,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z132,z111,z6]),(0,[z161,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z162,z4,z5,z6]),(0,[z1,z163,z2,z7,z4,z5,z6]),(0,[z1,z164,z2,z7,z4,z5,z73])],[(0,[z165,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z166,z7,z4,z5,z6])],[(0,[z91,z1,z2,z7,z167,z5,z6]),(0,[z1,z2,z7,z4,z132,z137,z6]),(0,[z107,z1,z2,z7,z4,z5,z32]),(0,[z15,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z168,z6])],[(0,[z24,z2,z34,z7,z4,z5,z6]),(0,[z24,z2,z7,z4,z5,z111,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z169,z5,z6]),(0,[z1,z170,z2,z7,z4,z171,z6]),(0,[z1,z7,z4,z38,z5,z14,z6]),(1,[z1,z2,z7,z4,z5,z22])],[(0,[z1,z2,z7,z4,z5,z6,z172])],[(1,[z1,z2,z7,z4,z173,z5])],[(1,[z1,z174,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z122]),(0,[z36,z1,z2,z7,z4,z65,z6]),(0,[z1,z37,z2,z7,z4,z5,z10])],[(0,[z1,z2,z7,z4,z175,z5,z6]),(0,[z176,z1,z2,z7,z4,z5,z6])],[(0,[z157,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z177,z4,z5,z6]),(0,[z1,z2,z7,z178,z4,z5,z6])],[(0,[z91,z2,z7,z13,z4,z5,z6]),(0,[z179,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z180,z5,z6]),(0,[z1,z50,z2,z7,z95,z5,z6]),(0,[z1,z2,z7,z47,z4,z181,z5])],[(0,[z1,z2,z7,z146,z5,z85,z6]),(0,[z1,z2,z7,z4,z146,z38,z5]),(0,[z1,z2,z7,z47,z4,z96,z5]),(1,[z1,z7,z4,z137,z14,z6])],[(0,[z182,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z183,z4,z5,z6]),(1,[z48,z1,z130,z4,z5,z6]),(0,[z1,z170,z2,z7,z4,z5,z184]),(0,[z1,z2,z7,z185,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z6,z73]),(0,[z107,z1,z2,z7,z47,z4,z5])],[(0,[z1,z2,z186,z7,z4,z5,z6]),(0,[z46,z1,z2,z7,z4,z38,z5]),(0,[z1,z9,z187,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z47,z4,z5])],[(0,[z188,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z186,z34,z7,z4,z5]),(0,[z189,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z14,z6,z73]),(0,[z1,z2,z7,z4,z137,z85,z6])],[(0,[z24,z1,z2,z7,z4,z5,z10])],[(0,[z1,z2,z7,z190,z4,z146,z5]),(0,[z1,z2,z7,z4,z5,z191,z6]),(0,[z36,z1,z2,z7,z4,z5,z10])],[(0,[z0,z1,z2,z7,z4,z5,z192]),(0,[z1,z50,z37,z2,z7,z4,z5]),(0,[z1,z193,z2,z7,z4,z5,z6])],[(0,[z1,z37,z2,z7,z194,z4,z5])],[(0,[z1,z2,z7,z195,z4,z5,z6]),(0,[z1,z2,z196,z7,z4,z5,z6]),(0,[z1,z30,z7,z4,z5,z14,z6]),(0,[z107,z1,z2,z7,z4,z5,z73]),(0,[z15,z1,z2,z7,z4,z5,z73]),(1,[z1,z2,z7,z4,z5,z197]),(0,[z198,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z199,z4,z5,z6]),(0,[z1,z2,z7,z200,z4,z5,z6]),(0,[z1,z2,z201,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z73])],[(0,[z1,z2,z7,z4,z202,z5,z6]),(0,[z92,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z153,z80,z5,z6]),(0,[z1,z2,z203,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z158,z6]),(0,[z1,z2,z7,z4,z5,z204,z6])],[(0,[z198,z1,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z205,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z98,z73]),(0,[z1,z2,z7,z4,z206,z5,z6])],[(0,[z1,z2,z21,z7,z80,z5,z6]),(0,[z1,z2,z203,z7,z4,z5,z32]),(0,[z207,z1,z2,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z67,z5])],[(0,[z208,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z186,z7,z4,z5]),(0,[z24,z1,z2,z13,z4,z5,z6]),(0,[z1,z25,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z6,z73]),(0,[z209,z1,z2,z7,z4,z38,z5])],[(1,[z40,z2,z7,z4,z5,z210]),(0,[z1,z2,z7,z4,z211,z5,z6]),(0,[z157,z1,z2,z7,z153,z5,z6]),(0,[z1,z2,z7,z212,z47,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z146,z5,z73]),(0,[z1,z2,z7,z4,z213,z5,z6]),(0,[z214,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z215,z6]),(0,[z1,z2,z7,z4,z5,z73,z216])],[(0,[z217,z1,z2,z7,z4,z5,z6]),(0,[z1,z218,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z219,z5,z6]),(0,[z1,z220,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z221,z5,z10]),(0,[z1,z222,z7,z4,z51,z5,z6])],[(0,[z48,z1,z37,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z132,z6,z73]),(0,[z1,z20,z2,z7,z47,z4,z5]),(0,[z36,z1,z2,z7,z4,z38,z5]),(0,[z157,z1,z2,z7,z4,z85,z6]),(0,[z1,z2,z7,z4,z223,z5,z6])],[(0,[z224,z1,z2,z7,z4,z5,z6]),(0,[z225,z1,z2,z7,z4,z5,z6])],[(0,[z1,z37,z2,z25,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z226]),(0,[z1,z2,z7,z4,z5,z227,z10]),(0,[z1,z228,z2,z7,z4,z5,z6])],[(0,[z229,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z230,z6]),(0,[z1,z37,z2,z7,z4,z5,z210]),(0,[z1,z2,z7,z4,z5,z6,z231])],[(0,[z1,z72,z7,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z80,z5,z32]),(0,[z1,z2,z203,z7,z47,z4,z5]),(0,[z1,z2,z7,z47,z232,z4,z5])],[(0,[z1,z2,z7,z4,z5,z6,z147]),(0,[z1,z9,z2,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z233,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z234])],[(0,[z1,z2,z7,z4,z5,z235,z6]),(0,[z1,z2,z7,z4,z5,z6,z236]),(0,[z237,z1,z2,z7,z4,z5,z6]),(0,[z238,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z216])],[(0,[z239,z1,z2,z7,z4,z5,z6]),(0,[z17,z1,z2,z7,z4,z5,z240]),(0,[z1,z50,z2,z7,z47,z4,z5]),(0,[z1,z7,z95,z4,z96,z5,z6]),(0,[z1,z20,z2,z7,z4,z5,z73]),(1,[z1,z2,z7,z4,z5,z10]),(0,[z1,z37,z2,z7,z47,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z241]),(1,[z1,z2,z7,z4,z242,z6])],[(0,[z1,z2,z7,z243,z4,z5,z6]),(0,[z244,z1,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z6,z79])],[(0,[z33,z2,z7,z13,z4,z5,z6]),(0,[z1,z2,z7,z130,z4,z5,z6]),(0,[z1,z2,z7,z95,z4,z5,z32]),(0,[z1,z2,z7,z4,z42,z85,z6])],[(0,[z1,z2,z7,z4,z38,z245,z5])],[(0,[z1,z246,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z247,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z73])]],
   [[(0,[z1,z2,z7,z4,z5,z248,z6]),(0,[z1,z2,z7,z130,z4,z5,z32]),(0,[z1,z222,z2,z7,z4,z5,z6])],[(0,[z1,z50,z2,z7,z4,z5,z73])],[(0,[z249,z1,z2,z7,z4,z5,z6]),(0,[z1,z9,z129,z7,z4,z5,z6]),(0,[z250,z1,z2,z7,z4,z5,z6])],[(0,[z46,z2,z7,z134,z4,z5,z6]),(0,[z1,z7,z4,z5,z111,z14,z6]),(0,[z1,z2,z7,z4,z251,z5,z6]),(0,[z252,z1,z2,z7,z4,z5,z10])],[(1,[z1,z2,z7,z253,z5,z6]),(0,[z1,z2,z7,z4,z254,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z79]),(1,[z1,z255,z2,z7,z4,z5]),(0,[z1,z2,z256,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z257,z5,z6]),(0,[z1,z2,z7,z258,z4,z5,z6]),(0,[z1,z2,z7,z4,z111,z14,z6]),(0,[z1,z259,z7,z4,z54,z5,z6]),(0,[z1,z2,z7,z4,z54,z5,z73]),(0,[z1,z2,z7,z4,z5,z32,z260])],[(0,[z1,z2,z7,z47,z134,z4,z5]),(0,[z40,z1,z2,z7,z4,z5,z210]),(0,[z261,z1,z2,z7,z4,z5,z6]),(0,[z1,z170,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z80,z5,z14,z6]),(1,[z1,z2,z7,z194,z4,z5])],[(0,[z1,z34,z7,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z98,z79]),(0,[z262,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z155,z5,z6]),(1,[z263,z2,z7,z146,z5,z6]),(0,[z48,z1,z2,z7,z47,z4,z5]),(1,[z1,z2,z7,z4,z31,z5]),(0,[z1,z2,z7,z4,z264,z5,z6]),(0,[z1,z2,z7,z4,z5,z76,z73])],[(0,[z1,z170,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z80,z5,z73]),(0,[z1,z2,z265,z7,z4,z5,z6]),(0,[z1,z2,z21,z7,z4,z5,z266]),(0,[z15,z1,z2,z7,z4,z5,z10])],[(0,[z1,z2,z7,z4,z5,z6,z77]),(0,[z1,z2,z7,z4,z5,z6,z79]),(0,[z1,z2,z7,z141,z4,z5,z6]),(0,[z1,z255,z2,z7,z4,z5,z6]),(0,[z157,z1,z2,z7,z5,z85,z6])],[(0,[z267,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z240,z6])],[(0,[z1,z268,z2,z7,z4,z5,z269]),(0,[z1,z2,z7,z4,z67,z6,z73]),(0,[z90,z1,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z4,z270,z5,z6]),(0,[z271,z1,z7,z4,z5,z14,z6]),(0,[z1,z255,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z134,z4,z5,z32]),(0,[z1,z7,z4,z5,z272,z14,z6]),(0,[z1,z2,z7,z4,z5,z14,z73]),(0,[z1,z2,z7,z4,z5,z273,z6])],[(0,[z1,z274,z2,z7,z4,z5,z6]),(0,[z48,z1,z2,z7,z4,z5,z73]),(0,[z1,z50,z2,z7,z96,z5,z6]),(0,[z1,z170,z2,z7,z4,z5,z275]),(0,[z1,z2,z7,z95,z4,z5,z73]),(0,[z1,z37,z268,z2,z7,z4,z5]),(0,[z1,z2,z7,z276,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z71,z73]),(0,[z1,z277,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z47,z141,z4,z5])],[(0,[z1,z2,z7,z4,z5,z278,z6])],[(0,[z1,z2,z7,z4,z146,z5,z10]),(0,[z1,z279,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z280,z5,z6]),(0,[z281,z1,z2,z7,z4,z5,z6])],[(0,[z15,z1,z2,z4,z5,z42,z6])],[(0,[z1,z2,z21,z7,z141,z5,z6]),(0,[z1,z2,z7,z282,z4,z5,z6])],[(0,[z1,z2,z152,z7,z4,z5,z6]),(0,[z46,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z283,z5,z6]),(0,[z1,z2,z284,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z285,z6]),(0,[z1,z2,z7,z4,z280,z5,z32])],[(0,[z1,z2,z7,z4,z5,z10,z210]),(0,[z286,z1,z2,z7,z4,z5,z6]),(0,[z1,z20,z2,z7,z4,z5,z79])],[(0,[z1,z9,z7,z4,z5,z98,z6]),(0,[z1,z2,z159,z7,z4,z38,z5])],[(0,[z33,z1,z9,z7,z4,z5,z6]),(0,[z2,z25,z7,z13,z4,z5,z6]),(0,[z1,z9,z268,z7,z4,z5,z6]),(0,[z287,z1,z2,z7,z4,z5,z6]),(0,[z107,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z141,z5,z85,z6]),(0,[z1,z2,z7,z212,z4,z5,z10]),(0,[z1,z2,z7,z288,z4,z5,z10])],[(0,[z1,z2,z7,z47,z4,z38,z5])],[(0,[z0,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z7,z4,z5,z6]),(0,[z92,z24,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z289,z5,z6]),(1,[z1,z50,z7,z96,z5,z6])],[(1,[z1,z2,z7,z4,z5,z290]),(0,[z17,z1,z2,z183,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z79])],[(1,[z1,z2,z7,z4,z5,z192]),(0,[z1,z2,z291,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z146,z5,z6]),(0,[z1,z20,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z292,z5,z6]),(0,[z271,z1,z2,z4,z5,z10,z6])],[(0,[z293,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z294,z5,z6]),(0,[z295,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z34,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z296,z6]),(0,[z1,z2,z7,z4,z5,z297,z6]),(0,[z1,z2,z7,z96,z80,z5,z6]),(0,[z1,z2,z7,z212,z141,z4,z5]),(0,[z1,z2,z7,z298,z4,z5,z6]),(0,[z299,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z126]),(0,[z1,z2,z7,z4,z300,z5,z6]),(0,[z1,z7,z4,z51,z5,z204,z6])]],
   [[(0,[z1,z2,z7,z134,z4,z5,z73]),(0,[z281,z1,z2,z7,z47,z4,z5])],[(0,[z1,z2,z7,z298,z4,z5,z32]),(0,[z1,z2,z7,z4,z38,z5,z10])],[(1,[z1,z2,z7,z4,z5,z100])],[(0,[z46,z1,z2,z7,z146,z5,z6]),(0,[z1,z2,z7,z4,z5,z301,z6]),(0,[z1,z50,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z285,z6])],[(0,[z1,z2,z302,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z113,z73])],[(0,[z1,z2,z303,z7,z4,z5,z6]),(0,[z1,z2,z34,z7,z4,z5,z73]),(1,[z1,z2,z7,z304,z5,z6]),(0,[z1,z2,z7,z4,z5,z111,z73]),(1,[z1,z2,z7,z4,z213,z6]),(0,[z1,z7,z4,z5,z14,z305,z6]),(0,[z1,z2,z7,z4,z5,z306,z6])],[(0,[z1,z174,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z307,z5,z6]),(2,[z1,z7,z4,z14,z73]),(0,[z1,z2,z308,z4,z80,z5,z6]),(0,[z1,z2,z309,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z42,z310]),(0,[z1,z2,z7,z4,z5,z285,z32])],[(0,[z1,z2,z25,z308,z4,z5,z6]),(0,[z1,z2,z7,z4,z54,z5,z10]),(0,[z1,z129,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z288,z4,z38,z5])],[(0,[z0,z1,z72,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z73,z73])],[(0,[z263,z1,z2,z7,z4,z5,z6]),(0,[z1,z311,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z312,z6])],[(0,[z1,z129,z2,z7,z4,z5,z32]),(0,[z1,z2,z4,z80,z5,z42,z6])],[(0,[z1,z313,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z38,z5,z6]),(0,[z1,z20,z2,z7,z4,z38,z5]),(0,[z314,z1,z2,z7,z4,z5,z6])],[(0,[z263,z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z47,z4,z173,z5])],[(0,[z2,z34,z7,z13,z4,z5,z6]),(0,[z315,z1,z2,z7,z4,z5,z6]),(1,[z1,z228,z2,z7,z4,z5])],[(0,[z1,z2,z7,z134,z96,z5,z6]),(0,[z316,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z317,z6]),(0,[z1,z37,z2,z7,z4,z80,z5]),(0,[z1,z2,z7,z4,z137,z5,z6]),(0,[z1,z318,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z319,z6]),(0,[z1,z2,z320,z7,z4,z5,z6]),(0,[z1,z2,z7,z321,z4,z5,z6])]],
   [[(0,[z322,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z323]),(0,[z1,z2,z7,z4,z5,z14,z10]),(0,[z1,z2,z7,z4,z38,z38,z5])],[(0,[z0,z1,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z290]),(0,[z1,z2,z7,z4,z324,z5,z6]),(0,[z1,z7,z4,z146,z5,z14,z6]),(0,[z1,z9,z7,z4,z54,z5,z6]),(0,[z48,z1,z2,z7,z4,z5,z10]),(0,[z1,z37,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z325,z4,z5,z6]),(0,[z1,z2,z7,z4,z206,z5,z32]),(0,[z1,z37,z2,z7,z4,z5,z326]),(0,[z1,z228,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z327,z6]),(0,[z1,z50,z2,z7,z4,z38,z5]),(0,[z328,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z305,z6]),(0,[z1,z2,z7,z4,z329,z5,z6])],[(0,[z330,z1,z2,z7,z4,z5,z6])],[(0,[z2,z7,z134,z4,z146,z5,z6]),(0,[z331,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z332,z7,z4,z5,z6]),(0,[z328,z1,z2,z7,z4,z5,z32]),(0,[z238,z1,z37,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z38,z145,z5])],[(1,[z1,z2,z7,z4,z132,z73])],[(0,[z1,z2,z7,z4,z333,z5,z6]),(0,[z1,z2,z7,z334,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z335,z6])],[(0,[z1,z2,z7,z4,z5,z336,z6]),(0,[z1,z97,z2,z7,z4,z5,z6])],[(0,[z337,z1,z2,z7,z4,z5,z6]),(1,[z1,z7,z4,z38,z5,z14]),(0,[z1,z2,z7,z4,z5,z10,z338])],[(0,[z1,z50,z7,z4,z96,z5,z6]),(0,[z1,z170,z2,z7,z95,z5,z6]),(0,[z1,z9,z7,z4,z5,z14,z6]),(0,[z1,z2,z21,z308,z4,z5,z6]),(0,[z1,z2,z339,z7,z4,z5,z6])],[(0,[z340,z1,z2,z7,z4,z5,z6]),(0,[z17,z1,z341,z7,z4,z5,z6]),(0,[z1,z246,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z54,z14,z6]),(0,[z40,z2,z7,z4,z5,z6,z210]),(0,[z1,z37,z129,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z342,z5,z6]),(0,[z1,z343,z7,z4,z137,z5,z6]),(1,[z1,z2,z7,z4,z5,z344])],[(0,[z1,z2,z7,z4,z5,z6,z345]),(0,[z1,z7,z4,z54,z5,z248,z6]),(0,[z346,z1,z2,z7,z4,z5,z6]),(1,[z1,z30,z2,z7,z4,z38])],[(0,[z107,z68,z1,z2,z7,z4,z5]),(0,[z1,z7,z4,z5,z35,z14,z6]),(0,[z1,z9,z7,z4,z103,z5,z6]),(1,[z1,z2,z7,z4,z5,z347]),(0,[z1,z2,z7,z4,z5,z348,z6]),(0,[z1,z2,z7,z349,z4,z5,z6])],[(0,[z1,z37,z72,z2,z7,z4,z5]),(1,[z1,z2,z7,z4,z5,z350]),(0,[z1,z2,z7,z351,z4,z5,z6]),(0,[z157,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z352,z5,z6]),(1,[z1,z2,z7,z4,z5,z353]),(0,[z1,z2,z7,z4,z5,z29,z73])]],
   [[(0,[z92,z1,z7,z4,z5,z14,z6]),(0,[z48,z1,z2,z7,z4,z5,z126]),(0,[z48,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z95,z4,z38,z5]),(0,[z1,z7,z4,z5,z14,z6,z354]),(0,[z1,z2,z7,z4,z5,z6,z197])],[(1,[z1,z2,z7,z4,z5,z296]),(0,[z40,z1,z7,z4,z5,z14,z6]),(1,[z1,z355,z7,z4,z5,z6]),(0,[z1,z2,z203,z7,z4,z5,z73]),(0,[z1,z37,z2,z7,z153,z4,z5])],[(0,[z1,z2,z7,z47,z4,z5,z42]),(0,[z157,z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z10,z85])],[(1,[z1,z2,z7,z4,z39,z6]),(0,[z356,z1,z2,z7,z4,z5,z6])],[(0,[z357,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z73,z79])],[(0,[z1,z2,z7,z4,z5,z358,z6]),(0,[z1,z2,z341,z7,z4,z5,z6]),(0,[z1,z359,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z360,z5])],[(0,[z46,z24,z2,z7,z4,z5,z6]),(0,[z107,z1,z2,z7,z4,z5,z79]),(0,[z1,z37,z2,z7,z4,z51,z5]),(0,[z1,z255,z37,z2,z7,z4,z5])],[(0,[z1,z2,z34,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z167,z5,z6]),(0,[z1,z2,z7,z4,z5,z111,z10])],[(0,[z1,z9,z72,z7,z4,z5,z6]),(0,[z1,z2,z7,z361,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z362])],[(0,[z1,z2,z7,z4,z5,z363,z6])],[(0,[z1,z7,z4,z67,z5,z14,z6]),(0,[z1,z2,z7,z364,z4,z5,z6])],[(0,[z17,z1,z2,z7,z4,z5,z365]),(0,[z366,z1,z2,z7,z4,z5,z6]),(0,[z1,z367,z2,z7,z4,z5,z6])],[(0,[z107,z1,z2,z7,z4,z5,z10])],[(0,[z1,z163,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z47,z4,z5,z10]),(0,[z1,z228,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z368,z4,z5,z6]),(0,[z1,z2,z7,z130,z47,z4,z5]),(1,[z1,z2,z369,z4,z5,z6])],[(0,[z370,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z7,z4,z5,z113,z6,z79]),(0,[z1,z2,z7,z371,z4,z5,z6]),(0,[z1,z2,z7,z141,z4,z5,z32]),(0,[z1,z2,z7,z288,z4,z5,z42]),(0,[z372,z1,z2,z7,z4,z5,z6])],[(0,[z1,z9,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z134,z4,z38,z5]),(0,[z1,z9,z7,z4,z5,z111,z6]),(1,[z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z32,z32]),(0,[z1,z2,z7,z4,z51,z5,z6]),(1,[z1,z2,z7,z4,z5,z326])],[],[(0,[z1,z21,z7,z4,z5,z14,z6]),(0,[z271,z1,z9,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z38,z6])],[(0,[z68,z1,z2,z7,z4,z5,z6])],[(0,[z17,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z130,z4,z5,z73]),(0,[z1,z37,z2,z7,z4,z5,z113])],[(0,[z1,z2,z34,z7,z4,z38,z5]),(0,[z1,z373,z2,z7,z4,z5,z6]),(0,[z1,z2,z374,z7,z4,z5,z6])],[(0,[z68,z1,z2,z7,z4,z5,z32]),(0,[z1,z170,z2,z7,z47,z4,z5]),(0,[z1,z9,z7,z47,z4,z5,z6]),(0,[z1,z2,z7,z4,z375,z5,z6])],[(0,[z17,z1,z2,z7,z4,z5,z32]),(0,[z92,z1,z2,z7,z4,z111,z6]),(0,[z1,z376,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z377,z5,z6])],[(0,[z378,z1,z2,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z98,z6,z210]),(0,[z1,z2,z7,z4,z38,z5,z42])],[(0,[z1,z2,z379,z7,z4,z5,z6]),(0,[z46,z1,z2,z7,z134,z5,z6]),(0,[z17,z1,z2,z380,z4,z5,z6]),(0,[z48,z1,z2,z84,z4,z5,z6])],[(0,[z91,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z146,z5,z6]),(0,[z1,z7,z4,z5,z14,z381,z6]),(0,[z382,z1,z2,z7,z4,z5,z6])],[(0,[z383,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z384,z4,z5,z6])],[(0,[z383,z1,z2,z34,z7,z4,z5]),(0,[z48,z1,z2,z7,z307,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z385])],[(1,[z0,z34,z7,z4,z5,z6]),(0,[z91,z1,z2,z7,z4,z5,z32]),(0,[z1,z37,z2,z84,z7,z4,z5]),(0,[z1,z170,z2,z7,z4,z5,z73])],[(0,[z386,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z387,z6]),(0,[z388,z1,z2,z7,z4,z5,z6]),(1,[z1,z20,z7,z4,z5,z113]),(1,[z1,z2,z7,z162,z5,z6]),(0,[z157,z1,z2,z7,z4,z51,z6]),(0,[z1,z2,z7,z47,z4,z67,z5])]],
   [[(0,[z0,z1,z9,z7,z4,z5,z6]),(0,[z389,z1,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z6,z32]),(0,[z1,z2,z7,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z390,z6])],[(0,[z1,z2,z391,z7,z4,z5,z6]),(0,[z263,z2,z7,z4,z146,z5,z6]),(0,[z1,z7,z4,z5,z14,z6,z210])],[(0,[z17,z1,z392,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z393,z5,z6]),(0,[z1,z2,z7,z4,z394,z5,z6])],[(0,[z1,z2,z203,z7,z4,z5,z10]),(1,[z1,z2,z4,z5,z10,z32])],[(0,[z114,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z395,z5,z6]),(0,[z176,z1,z2,z7,z4,z38,z5])],[(0,[z1,z2,z7,z4,z396,z5,z6]),(1,[z24,z2,z25,z4,z5,z6]),(0,[z263,z1,z37,z2,z7,z4,z5]),(1,[z1,z7,z47,z4,z5,z14]),(0,[z1,z37,z2,z7,z4,z5,z85]),(0,[z1,z2,z7,z282,z47,z4,z5])],[(0,[z91,z1,z87,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z14,z73]),(0,[z114,z1,z2,z7,z4,z5,z32]),(0,[z157,z397,z2,z7,z4,z5,z6])],[],[(0,[z1,z2,z7,z47,z4,z5,z210]),(0,[z1,z2,z7,z4,z5,z381,z6])],[(0,[z1,z2,z7,z4,z398,z5,z6]),(0,[z1,z2,z7,z4,z5,z399,z6])],[(0,[z1,z2,z25,z7,z4,z5,z400]),(0,[z401,z1,z2,z7,z4,z5,z6])],[(0,[z72,z2,z34,z7,z4,z5,z6]),(0,[z46,z1,z7,z4,z5,z14,z6]),(0,[z1,z170,z2,z7,z96,z5,z6]),(0,[z1,z2,z7,z4,z402,z5,z6]),(0,[z36,z1,z2,z7,z4,z5,z350])],[(0,[z1,z2,z7,z4,z403,z5,z6]),(0,[z1,z9,z203,z7,z4,z5,z6]),(0,[z1,z343,z2,z7,z4,z5,z6])],[(0,[z36,z1,z355,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z80,z5,z10]),(0,[z15,z1,z2,z7,z162,z5,z6]),(0,[z295,z1,z2,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z404,z6])],[(0,[z1,z2,z7,z4,z5,z6,z405]),(0,[z1,z2,z7,z4,z5,z406,z6]),(0,[z1,z2,z7,z4,z5,z6,z210])]],
   [[(0,[z407,z1,z2,z7,z4,z5,z6]),(0,[z1,z408,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z141,z96,z5,z6])],[(0,[z1,z2,z7,z4,z409,z5,z6]),(0,[z1,z2,z410,z7,z4,z5,z6])],[(0,[z40,z107,z1,z2,z7,z4,z5]),(1,[z1,z7,z153,z4,z14,z6]),(0,[z1,z2,z203,z7,z4,z38,z5]),(0,[z114,z1,z2,z7,z47,z4,z5])],[(0,[z1,z37,z2,z7,z5,z285,z6])],[(0,[z1,z2,z7,z95,z4,z5,z10]),(0,[z1,z2,z7,z4,z137,z5,z32])],[(0,[z48,z1,z2,z7,z4,z242,z6]),(0,[z1,z129,z7,z4,z96,z5,z6]),(0,[z1,z308,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z10,z113])],[(0,[z411,z1,z2,z7,z4,z5,z6]),(0,[z36,z1,z2,z7,z141,z5,z6]),(0,[z1,z2,z7,z153,z4,z85,z6]),(0,[z1,z2,z7,z4,z38,z67,z5])],[(0,[z1,z2,z7,z130,z4,z5,z10]),(1,[z1,z2,z7,z4,z412,z6]),(0,[z1,z2,z7,z4,z413,z5,z6]),(0,[z1,z2,z7,z178,z4,z5,z73]),(0,[z1,z414,z2,z7,z4,z5,z6])],[(0,[z1,z415,z2,z7,z4,z5,z6]),(0,[z1,z2,z416,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z210,z73]),(0,[z1,z129,z2,z7,z47,z4,z5]),(0,[z1,z9,z7,z4,z80,z5,z6]),(1,[z1,z417,z2,z7,z4,z5])],[(0,[z1,z2,z7,z146,z96,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z418]),(0,[z271,z1,z2,z203,z4,z5,z6])],[(0,[z263,z1,z2,z7,z47,z4,z5]),(1,[z1,z2,z7,z4,z5,z419])],[(0,[z33,z1,z2,z7,z4,z5,z6]),(0,[z15,z1,z2,z7,z4,z137,z6]),(0,[z157,z1,z37,z2,z7,z4,z5]),(0,[z1,z37,z2,z7,z4,z5,z285]),(0,[z1,z2,z7,z4,z5,z285,z73])],[],[(0,[z24,z1,z7,z4,z5,z14,z6]),(0,[z1,z37,z2,z7,z4,z146,z5]),(1,[z1,z2,z7,z270,z5,z6]),(0,[z1,z7,z95,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z420,z5,z6])],[(0,[z33,z1,z2,z7,z4,z5,z32]),(0,[z1,z9,z7,z95,z4,z5,z6]),(0,[z36,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z421,z6]),(0,[z1,z37,z2,z7,z4,z5,z71])],[(0,[z46,z92,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z422,z4,z5,z6]),(0,[z1,z129,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z5,z32,z131])]],
   [[(0,[z1,z2,z7,z4,z38,z5,z210]),(0,[z1,z170,z2,z7,z4,z5,z10]),(0,[z1,z9,z9,z7,z4,z5,z6])],[(0,[z263,z1,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z423,z5,z6]),(0,[z68,z1,z20,z2,z7,z4,z5]),(0,[z1,z9,z7,z130,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z266]),(0,[z1,z2,z7,z4,z5,z424,z6])],[(0,[z425,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z95,z146,z5,z6]),(0,[z1,z37,z2,z7,z4,z54,z5]),(0,[z1,z2,z7,z426,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z310])],[(0,[z1,z2,z7,z4,z427,z5,z6]),(0,[z1,z2,z428,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z429]),(0,[z1,z2,z7,z4,z430,z5,z6])],[(0,[z1,z2,z7,z190,z4,z5,z6]),(1,[z1,z138,z7,z4,z5,z6])],[(0,[z1,z2,z7,z134,z4,z5,z10]),(0,[z1,z84,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z145,z5,z6])],[(0,[z1,z2,z7,z130,z4,z38,z5]),(0,[z1,z2,z7,z4,z137,z5,z73]),(1,[z1,z2,z7,z298,z4,z5]),(1,[z1,z2,z256,z4,z5,z6])],[(0,[z40,z1,z9,z7,z4,z5,z6]),(0,[z68,z2,z7,z4,z5,z98,z6]),(0,[z1,z2,z7,z4,z431,z5,z6]),(0,[z1,z129,z2,z84,z4,z5,z6]),(0,[z432,z1,z2,z7,z4,z5,z6]),(0,[z1,z433,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z73,z354])],[(0,[z1,z268,z2,z7,z4,z5,z6]),(0,[z1,z417,z2,z7,z4,z80,z5]),(1,[z434,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z153,z51,z5,z6]),(1,[z1,z97,z7,z4,z5,z6]),(1,[z1,z435,z2,z7,z4,z5])],[(1,[z1,z2,z7,z18,z5,z6]),(0,[z1,z7,z4,z5,z14,z85,z6]),(0,[z1,z2,z141,z4,z80,z5,z6]),(0,[z1,z255,z2,z7,z141,z4,z5]),(0,[z1,z2,z7,z4,z5,z347,z6])],[(0,[z1,z392,z2,z7,z4,z5,z6]),(0,[z1,z436,z2,z7,z4,z5,z6]),(0,[z1,z359,z2,z7,z4,z5,z32]),(0,[z1,z2,z339,z7,z47,z4,z5])],[(0,[z1,z268,z2,z7,z4,z5,z32]),(0,[z1,z2,z308,z7,z4,z42,z6])],[(0,[z1,z2,z7,z437,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z51,z5]),(0,[z1,z2,z7,z4,z254,z38,z5])],[],[(0,[z1,z9,z7,z134,z4,z5,z6]),(0,[z1,z2,z7,z4,z438,z5,z6]),(0,[z1,z170,z2,z7,z4,z38,z5]),(0,[z1,z2,z308,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z326,z6])]],
   [[(0,[z68,z1,z37,z2,z7,z4,z5]),(0,[z157,z1,z2,z7,z47,z4,z5])],[(0,[z17,z1,z37,z2,z7,z4,z5]),(0,[z40,z1,z2,z7,z4,z5,z98]),(0,[z1,z439,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z354]),(0,[z1,z440,z9,z7,z4,z5,z6]),(0,[z36,z1,z2,z7,z80,z5,z6]),(0,[z1,z2,z7,z4,z51,z42,z6]),(1,[z1,z2,z7,z288,z4,z5]),(0,[z1,z2,z7,z4,z5,z441,z6]),(0,[z1,z37,z2,z7,z4,z4,z5])],[(0,[z1,z2,z7,z47,z134,z5,z6]),(1,[z189,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z272,z6]),(0,[z1,z2,z308,z7,z4,z5,z32]),(0,[z1,z373,z37,z2,z7,z4,z5])],[(0,[z48,z1,z129,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z113,z6]),(0,[z442,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z141,z4,z38,z5]),(1,[z1,z2,z7,z4,z5,z443])],[(0,[z1,z2,z7,z4,z5,z210,z79]),(0,[z444,z1,z2,z7,z4,z5,z6])],[(0,[z91,z1,z2,z25,z4,z5,z6]),(0,[z1,z2,z25,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z344])],[(0,[z1,z2,z445,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z446]),(0,[z1,z2,z7,z4,z5,z10,z424])],[(0,[z91,z1,z37,z2,z7,z4,z5]),(1,[z1,z7,z4,z5,z14,z32]),(0,[z1,z2,z7,z4,z5,z6,z266]),(0,[z1,z2,z7,z4,z51,z5,z32]),(0,[z157,z1,z2,z7,z4,z5,z73])],[(0,[z62,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z350]),(0,[z1,z2,z7,z4,z447,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z310]),(1,[z1,z7,z4,z5,z104,z6]),(0,[z1,z2,z7,z448,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z85,z6]),(0,[z1,z2,z7,z4,z5,z6,z353]),(0,[z1,z2,z7,z4,z449,z5,z6])],[(0,[z1,z2,z7,z155,z4,z5,z6]),(0,[z1,z2,z7,z4,z54,z137,z6]),(0,[z1,z2,z7,z4,z5,z450,z6]),(0,[z1,z30,z2,z7,z4,z67,z6])],[(0,[z1,z2,z7,z451,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z452,z6])],[(0,[z1,z2,z7,z4,z5,z85,z32])],[(0,[z1,z72,z2,z7,z4,z5,z6]),(0,[z1,z453,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z454]),(0,[z1,z2,z7,z4,z38,z5,z113]),(0,[z1,z37,z30,z2,z7,z4,z5]),(0,[z455,z1,z2,z7,z4,z5,z6])],[(0,[z1,z268,z2,z7,z4,z5,z55]),(0,[z1,z2,z7,z4,z5,z285,z10]),(1,[z1,z115,z7,z4,z5,z6]),(0,[z1,z2,z7,z282,z4,z38,z5])],[(0,[z46,z1,z2,z7,z4,z5,z429]),(0,[z1,z2,z456,z7,z4,z5,z6]),(0,[z1,z2,z117,z7,z4,z5,z6]),(1,[z1,z343,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z71])],[(0,[z1,z72,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z13,z4,z5,z6]),(0,[z48,z1,z2,z7,z4,z213,z6])]],
   [[(0,[z1,z2,z7,z457,z4,z5,z6]),(0,[z114,z1,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z10,z98]),(0,[z1,z458,z2,z7,z4,z5,z6]),(0,[z1,z129,z2,z7,z4,z5,z10]),(0,[z459,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z80,z5]),(0,[z1,z2,z7,z4,z5,z460,z6]),(0,[z1,z2,z7,z4,z461,z5,z6])],[(0,[z1,z2,z2,z7,z4,z5,z6])],[(0,[z462,z1,z2,z7,z4,z5,z6]),(0,[z263,z1,z2,z7,z4,z5,z10]),(0,[z1,z463,z2,z7,z4,z5,z6]),(0,[z15,z1,z7,z4,z5,z14,z6]),(0,[z107,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z464,z5,z6]),(0,[z1,z2,z308,z4,z137,z5,z6])],[(0,[z465,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z466]),(0,[z1,z2,z7,z4,z5,z113,z210]),(0,[z68,z1,z2,z7,z47,z4,z5]),(0,[z1,z9,z30,z7,z4,z5,z6]),(0,[z1,z2,z7,z141,z4,z5,z73]),(0,[z15,z1,z2,z7,z4,z5,z446]),(0,[z1,z2,z467,z7,z4,z5,z6]),(0,[z386,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z360,z5,z6])],[(0,[z17,z1,z2,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z32,z73]),(0,[z468,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z469,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z285,z6])],[(0,[z1,z2,z7,z470,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z471]),(0,[z372,z1,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z4,z5,z472,z6]),(0,[z1,z2,z117,z7,z4,z96,z5]),(1,[z1,z7,z4,z5,z14,z73]),(0,[z1,z2,z7,z4,z51,z5,z73])],[(1,[z1,z2,z7,z47,z134,z5]),(0,[z473,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z419,z6])],[],[(0,[z91,z1,z2,z7,z47,z4,z5]),(0,[z68,z1,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z38,z5,z85])],[(0,[z17,z1,z2,z7,z4,z5,z73])],[(0,[z92,z2,z7,z13,z4,z5,z6])],[(0,[z1,z37,z2,z7,z13,z4,z5])]],
   [[(1,[z1,z152,z7,z4,z5,z6]),(0,[z1,z129,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z32,z234]),(0,[z1,z2,z7,z4,z38,z5,z5])],[(0,[z17,z1,z2,z7,z4,z54,z6]),(0,[z1,z2,z7,z4,z38,z6,z73])],[(0,[z1,z2,z25,z7,z4,z5,z6]),(0,[z263,z1,z2,z7,z4,z38,z5]),(0,[z46,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z75,z5,z6])],[(0,[z91,z1,z2,z7,z4,z5,z73]),(1,[z1,z2,z7,z4,z5,z400]),(0,[z1,z2,z84,z7,z4,z5,z474]),(0,[z1,z475,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z100,z6])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z476,z6]),(0,[z1,z2,z7,z47,z153,z4,z5]),(0,[z1,z477,z2,z7,z4,z5,z6])],[(0,[z1,z478,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z400,z6]),(0,[z1,z2,z7,z4,z5,z171,z6]),(0,[z1,z9,z7,z4,z5,z6,z73]),(0,[z340,z1,z2,z7,z4,z5,z10])],[(0,[z1,z20,z7,z4,z5,z14,z6]),(1,[z1,z2,z7,z4,z5,z363])],[(0,[z33,z1,z37,z2,z7,z4,z5]),(1,[z1,z2,z7,z167,z5,z6]),(0,[z1,z479,z2,z7,z4,z5,z6])],[(1,[z36,z1,z2,z80,z5,z6]),(0,[z1,z2,z7,z4,z38,z80,z5])],[(0,[z1,z2,z7,z95,z134,z5,z6]),(0,[z1,z2,z7,z4,z5,z362,z32]),(0,[z1,z2,z7,z47,z4,z51,z5])],[(0,[z1,z37,z9,z7,z4,z5,z6]),(0,[z1,z37,z9,z2,z7,z4,z5]),(0,[z1,z2,z7,z480,z4,z5,z6]),(0,[z481,z1,z2,z7,z4,z5,z6])],[(0,[z24,z2,z25,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z427,z5,z6]),(0,[z482,z1,z2,z7,z4,z5,z6]),(1,[z1,z129,z84,z4,z5,z6]),(0,[z1,z2,z7,z4,z483,z5,z6]),(0,[z1,z2,z7,z4,z484,z5,z6]),(0,[z114,z1,z2,z7,z4,z5,z73])],[(0,[z1,z50,z7,z4,z5,z14,z6]),(0,[z1,z9,z7,z4,z5,z6,z231]),(0,[z1,z2,z7,z4,z5,z6,z485])],[(0,[z1,z129,z84,z7,z4,z5,z6])],[(0,[z486,z1,z2,z7,z4,z5,z6]),(0,[z1,z57,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z67,z5,z6])]],
   [[(1,[z1,z7,z4,z14,z6,z73]),(0,[z1,z105,z2,z7,z4,z5,z85])],[(0,[z1,z2,z7,z4,z487,z5,z6]),(0,[z488,z1,z2,z7,z4,z5,z6]),(0,[z489,z1,z2,z7,z4,z5,z6]),(0,[z15,z1,z2,z308,z4,z5,z6])],[(0,[z490,z1,z2,z7,z4,z5,z6]),(0,[z17,z2,z7,z4,z5,z111,z6]),(0,[z1,z2,z7,z4,z5,z32,z79]),(0,[z1,z2,z7,z4,z5,z22,z6]),(0,[z1,z2,z7,z153,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z285])],[(0,[z491,z1,z2,z7,z4,z5,z6]),(0,[z24,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z95,z141,z5,z6])],[(1,[z91,z2,z13,z4,z5,z6]),(0,[z2,z7,z13,z4,z146,z5,z6]),(0,[z1,z37,z2,z7,z4,z5,z98]),(0,[z36,z1,z9,z7,z4,z5,z6])],[(0,[z1,z37,z2,z7,z95,z4,z5]),(0,[z1,z492,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z312,z6]),(0,[z1,z2,z7,z4,z38,z5,z71])],[],[(0,[z493,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z494,z6]),(0,[z1,z37,z2,z7,z4,z132,z5]),(0,[z107,z1,z2,z7,z4,z5,z113]),(0,[z1,z2,z7,z141,z4,z5,z10]),(0,[z1,z2,z4,z137,z5,z42,z6]),(1,[z1,z7,z4,z5,z204,z6])],[(0,[z1,z2,z7,z4,z5,z495,z6]),(0,[z1,z2,z496,z7,z4,z5,z6]),(0,[z1,z497,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z498]),(0,[z1,z2,z7,z47,z4,z5,z113]),(0,[z1,z2,z7,z4,z5,z499,z6]),(0,[z157,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z6,z500])],[(0,[z92,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z54,z5]),(0,[z1,z2,z7,z194,z4,z5,z6])],[(0,[z1,z2,z501,z7,z4,z5,z6])],[(0,[z48,z1,z7,z4,z5,z14,z6]),(0,[z502,z1,z2,z7,z4,z5,z6])],[(0,[z33,z1,z2,z7,z47,z4,z5]),(0,[z1,z503,z2,z7,z4,z5,z6]),(0,[z1,z84,z7,z130,z4,z5,z6]),(0,[z1,z20,z7,z4,z5,z113,z6])],[(0,[z1,z2,z7,z4,z4,z5,z6]),(1,[z1,z259,z7,z4,z5,z6]),(1,[z1,z2,z7,z289,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z419])],[],[(0,[z17,z1,z2,z7,z4,z5,z10]),(0,[z1,z311,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z158]),(0,[z1,z414,z2,z7,z4,z5,z73])]],
   [[(0,[z1,z504,z2,z7,z4,z5,z6]),(0,[z1,z505,z2,z7,z4,z5,z6]),(0,[z1,z506,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z507]),(0,[z1,z2,z7,z4,z508,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z509]),(0,[z1,z9,z7,z141,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z6,z79]),(0,[z1,z435,z2,z7,z4,z5,z6])],[(0,[z1,z510,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z511]),(0,[z1,z7,z153,z4,z5,z14,z6]),(1,[z1,z2,z7,z394,z5,z6]),(0,[z1,z2,z7,z4,z5,z73,z310])],[(0,[z33,z1,z2,z7,z4,z5,z73]),(0,[z1,z7,z4,z5,z14,z42,z6]),(0,[z1,z30,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z134,z141,z5,z6]),(0,[z1,z2,z512,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z513,z6])],[(0,[z0,z1,z2,z7,z4,z202,z6]),(0,[z91,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z141,z146,z5,z6]),(0,[z1,z7,z4,z132,z5,z14,z6]),(0,[z1,z164,z9,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z273,z6])],[(0,[z1,z514,z2,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z515,z4,z5,z6]),(0,[z1,z2,z7,z516,z4,z5,z6]),(0,[z1,z2,z7,z7,z4,z5,z10])],[(0,[z517,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z85]),(0,[z1,z2,z7,z232,z4,z5,z6])],[(0,[z1,z518,z2,z7,z4,z5,z6]),(0,[z17,z1,z2,z7,z253,z5,z6]),(1,[z1,z2,z7,z4,z5,z424]),(0,[z1,z2,z7,z4,z38,z223,z5])],[(0,[z46,z2,z7,z13,z4,z5,z6]),(1,[z1,z9,z7,z4,z5,z6]),(0,[z1,z268,z2,z7,z47,z4,z5]),(0,[z1,z20,z2,z7,z4,z5,z113])],[(0,[z519,z1,z2,z7,z4,z5,z6]),(0,[z520,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z429]),(0,[z1,z2,z7,z4,z521,z5,z6])],[(0,[z522,z1,z2,z7,z4,z5,z6]),(0,[z68,z1,z2,z7,z4,z38,z5]),(1,[z1,z9,z7,z4,z5,z32]),(1,[z1,z37,z9,z7,z4,z5])],[(0,[z17,z1,z2,z7,z4,z38,z5]),(1,[z1,z7,z4,z5,z248,z6]),(0,[z1,z2,z7,z95,z80,z5,z6]),(0,[z523,z1,z2,z7,z4,z5,z6]),(0,[z114,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z437,z47,z4,z5]),(0,[z1,z2,z524,z7,z4,z5,z6])],[(0,[z1,z525,z2,z7,z4,z5,z6]),(0,[z526,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z91,z1,z2,z13,z4,z5,z6]),(0,[z1,z2,z7,z4,z527,z5,z6]),(0,[z1,z2,z380,z7,z4,z5,z6]),(0,[z1,z528,z2,z7,z4,z5,z6]),(0,[z157,z1,z2,z7,z4,z132,z6]),(0,[z1,z2,z308,z7,z47,z4,z5]),(0,[z1,z529,z2,z7,z4,z5,z6])],[(0,[z1,z2,z13,z130,z4,z5,z6]),(0,[z1,z268,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z5,z42,z6]),(1,[z157,z1,z2,z7,z85,z6])],[(1,[z1,z2,z7,z4,z5,z240]),(0,[z1,z170,z129,z7,z4,z5,z6]),(0,[z1,z2,z7,z153,z4,z51,z6]),(0,[z468,z1,z37,z2,z7,z4,z5])],[(1,[z1,z7,z4,z111,z14,z6])],[(0,[z91,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z5,z6])],[(0,[z1,z2,z7,z13,z4,z5,z32])],[(0,[z1,z7,z4,z137,z5,z14,z6]),(0,[z1,z2,z7,z4,z132,z42,z6]),(0,[z530,z1,z2,z7,z4,z5,z6])],[(0,[z1,z7,z4,z5,z14,z531,z6]),(0,[z1,z2,z7,z4,z532,z5,z6]),(0,[z1,z2,z308,z7,z4,z5,z73])],[(0,[z165,z1,z7,z4,z5,z14,z6]),(1,[z1,z9,z7,z47,z4,z5]),(0,[z1,z2,z533,z7,z4,z5,z6])],[(0,[z1,z2,z7,z534,z4,z5,z6]),(0,[z1,z2,z7,z4,z132,z5,z6]),(0,[z1,z7,z4,z5,z14,z6,z71]),(0,[z15,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z535,z6])],[(0,[z36,z1,z2,z21,z4,z5,z6])],[(0,[z1,z2,z7,z4,z137,z5,z10])],[(0,[z1,z2,z7,z4,z132,z5,z32]),(0,[z36,z536,z2,z7,z4,z5,z6]),(1,[z1,z537,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z538,z6]),(0,[z1,z2,z7,z4,z5,z6,z443]),(0,[z1,z2,z7,z47,z4,z430,z5])],[(0,[z1,z72,z2,z7,z47,z4,z5]),(0,[z539,z1,z2,z7,z4,z5,z6]),(0,[z1,z540,z2,z7,z4,z5,z6]),(0,[z1,z37,z2,z308,z7,z4,z5]),(0,[z114,z1,z2,z7,z4,z38,z5])],[(0,[z541,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z542,z5,z6]),(0,[z1,z2,z7,z4,z264,z51,z5]),(0,[z1,z2,z7,z47,z4,z5,z285])],[(0,[z91,z1,z2,z7,z4,z156,z6]),(0,[z1,z2,z7,z134,z80,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z446])]],
   [[(0,[z1,z2,z7,z13,z47,z4,z5]),(0,[z1,z2,z7,z47,z4,z146,z5]),(0,[z1,z2,z7,z4,z96,z5,z6]),(0,[z1,z2,z7,z4,z5,z85,z73])],[(0,[z1,z543,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z413,z5,z10]),(0,[z1,z2,z7,z47,z4,z5,z71]),(0,[z1,z2,z7,z4,z544,z5,z6])],[(0,[z1,z2,z7,z545,z4,z5,z6]),(0,[z1,z37,z170,z2,z7,z4,z5])],[(1,[z1,z2,z7,z427,z5,z6]),(0,[z1,z9,z7,z4,z5,z6,z210]),(0,[z1,z2,z7,z4,z96,z5,z32])],[(0,[z1,z72,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z5,z546,z6]),(0,[z263,z1,z2,z7,z146,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z98]),(0,[z1,z2,z7,z547,z4,z5,z6])],[(0,[z1,z2,z7,z18,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z54,z5]),(0,[z1,z9,z7,z4,z137,z5,z6]),(0,[z1,z548,z2,z7,z4,z5,z6]),(0,[z549,z1,z2,z7,z4,z5,z6])],[],[(0,[z1,z550,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z71])],[(0,[z1,z2,z25,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z551,z6]),(0,[z1,z2,z21,z141,z4,z5,z6])],[(0,[z271,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z76])],[(0,[z552,z1,z2,z7,z4,z5,z6]),(0,[z1,z259,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z474]),(1,[z1,z2,z7,z4,z280,z5])],[(0,[z1,z9,z170,z7,z4,z5,z6]),(0,[z1,z7,z47,z4,z5,z14,z6]),(1,[z1,z2,z7,z4,z464,z6]),(0,[z473,z1,z2,z7,z47,z4,z5])],[(0,[z1,z7,z4,z5,z191,z14,z6]),(0,[z1,z2,z553,z7,z4,z5,z6]),(0,[z271,z1,z2,z7,z4,z5,z32]),(0,[z157,z1,z2,z7,z4,z5,z10])],[(0,[z1,z170,z2,z7,z4,z412,z6]),(0,[z1,z2,z121,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z554,z6])],[(0,[z1,z2,z7,z4,z5,z6,z466]),(0,[z1,z279,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z334,z4,z5,z6])],[(0,[z1,z2,z7,z555,z4,z5,z6]),(0,[z536,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z0,z33,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z137,z14,z6])],[(1,[z1,z268,z7,z4,z14,z6]),(0,[z1,z41,z9,z7,z4,z5,z6]),(0,[z36,z1,z2,z4,z80,z5,z6]),(0,[z556,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z557,z5,z6]),(0,[z1,z2,z7,z4,z132,z54,z6]),(0,[z1,z2,z7,z4,z5,z116,z6]),(1,[z536,z2,z7,z4,z5,z6])],[(0,[z1,z2,z25,z7,z47,z4,z5]),(1,[z1,z2,z183,z4,z5,z6]),(0,[z1,z37,z2,z7,z130,z4,z5]),(0,[z1,z50,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z275,z6]),(1,[z1,z2,z7,z4,z5,z269]),(0,[z1,z268,z2,z7,z4,z5,z10]),(1,[z1,z2,z203,z4,z5,z32])],[(0,[z33,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z558,z5,z6]),(0,[z214,z1,z7,z4,z5,z14,z6]),(1,[z1,z309,z7,z4,z5,z6]),(0,[z1,z2,z7,z559,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z4,z5])],[(0,[z1,z2,z7,z560,z4,z5,z6]),(0,[z1,z2,z7,z4,z561,z5,z6]),(0,[z1,z2,z7,z4,z67,z5,z32])],[(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z1,z129,z72,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z562,z6]),(0,[z1,z2,z7,z4,z5,z6,z563]),(0,[z1,z7,z4,z254,z5,z14,z6]),(1,[z556,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z564,z6])],[(0,[z1,z2,z21,z7,z4,z5,z6]),(0,[z15,z1,z2,z7,z4,z5,z363]),(0,[z1,z2,z7,z153,z4,z5,z32])],[(0,[z0,z1,z2,z7,z4,z5,z32]),(0,[z68,z1,z2,z7,z219,z5,z6]),(0,[z1,z2,z308,z7,z4,z5,z10])],[(0,[z565,z1,z9,z7,z4,z5,z6])],[(0,[z566,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z98]),(0,[z1,z2,z21,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z73,z507])],[(1,[z1,z2,z7,z4,z202,z6]),(0,[z48,z189,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z567,z5,z6]),(0,[z1,z568,z2,z7,z4,z5,z6]),(0,[z1,z569,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z44,z6]),(1,[z540,z2,z7,z4,z5,z6]),(0,[z1,z7,z130,z4,z96,z5,z6]),(0,[z570,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z219,z4,z5,z6]),(1,[z1,z7,z4,z5,z14,z10]),(0,[z444,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z51,z5,z10]),(0,[z1,z2,z7,z571,z4,z5,z6])],[(1,[z271,z1,z2,z4,z5,z10]),(0,[z1,z30,z524,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z304,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z572,z6]),(0,[z1,z2,z7,z4,z5,z6,z474])],[(0,[z573,z1,z2,z7,z4,z5,z6]),(0,[z68,z1,z2,z7,z4,z5,z10]),(0,[z48,z1,z9,z7,z4,z5,z6]),(0,[z157,z1,z2,z7,z4,z14,z6])],[(0,[z1,z7,z134,z4,z5,z14,z6]),(0,[z48,z1,z7,z130,z4,z5,z6]),(0,[z1,z268,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z574,z5,z6])],[(0,[z1,z9,z308,z7,z4,z5,z6]),(0,[z15,z1,z309,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z542,z5]),(0,[z1,z575,z2,z7,z4,z5,z6])],[(0,[z1,z2,z308,z13,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z5,z14]),(0,[z1,z2,z7,z4,z5,z576,z6])],[(0,[z1,z7,z4,z96,z5,z14,z6]),(1,[z1,z2,z7,z4,z38,z73])],[(0,[z1,z72,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z577,z5,z6]),(0,[z1,z2,z21,z7,z47,z4,z5]),(0,[z15,z556,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z578,z6]),(0,[z107,z1,z2,z7,z4,z312,z6]),(0,[z520,z1,z37,z2,z7,z4,z5])],[(1,[z1,z2,z7,z579,z4,z5]),(0,[z1,z2,z7,z4,z14,z42,z6]),(0,[z1,z9,z7,z4,z51,z5,z6]),(0,[z1,z2,z308,z7,z4,z38,z5])],[(1,[z1,z2,z7,z190,z4,z5]),(0,[z36,z1,z537,z7,z4,z5,z6]),(0,[z1,z228,z2,z7,z153,z4,z5])],[(1,[z1,z7,z4,z54,z14,z6]),(0,[z1,z170,z7,z4,z5,z14,z6]),(0,[z1,z7,z4,z393,z5,z14,z6]),(0,[z1,z2,z7,z153,z4,z5,z73])],[(0,[z580,z1,z2,z7,z4,z5,z6]),(0,[z581,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z582,z5,z6]),(0,[z1,z2,z583,z7,z4,z5,z6])],[(0,[z1,z2,z7,z584,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z85,z6])],[(1,[z1,z2,z7,z4,z5,z278]),(0,[z1,z2,z7,z4,z5,z585,z6]),(0,[z1,z37,z2,z7,z4,z5,z6])],[(0,[z1,z37,z2,z34,z7,z4,z5]),(0,[z91,z1,z2,z7,z4,z39,z6]),(0,[z1,z2,z7,z134,z5,z285,z6]),(0,[z1,z2,z7,z4,z5,z586,z6]),(0,[z1,z587,z2,z7,z4,z5,z6]),(0,[z1,z2,z588,z7,z4,z5,z6])],[(0,[z123,z1,z9,z7,z4,z5,z6])]],
   [[(1,[z1,z9,z7,z4,z38,z5]),(0,[z1,z37,z2,z7,z4,z5,z32])],[(0,[z589,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z499,z6]),(1,[z1,z2,z7,z4,z211,z5])],[(0,[z1,z2,z7,z4,z590,z5,z6]),(0,[z1,z2,z7,z4,z591,z5,z6]),(0,[z1,z2,z501,z7,z4,z5,z73])],[(1,[z1,z341,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z53,z6]),(0,[z15,z1,z2,z7,z394,z5,z6]),(0,[z1,z30,z2,z7,z47,z4,z5])],[(0,[z1,z72,z2,z7,z4,z38,z5]),(0,[z1,z2,z203,z4,z5,z6,z32]),(0,[z455,z1,z2,z7,z4,z38,z5])],[(0,[z24,z1,z2,z7,z4,z5,z6]),(0,[z592,z1,z2,z7,z4,z5,z6]),(0,[z1,z9,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z542,z137,z5]),(0,[z1,z2,z7,z4,z5,z593,z6])],[(0,[z1,z2,z7,z4,z594,z5,z6]),(0,[z595,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z32,z210]),(0,[z1,z2,z7,z4,z596,z5,z6]),(0,[z1,z2,z7,z4,z5,z42,z32])],[(0,[z1,z2,z7,z13,z4,z38,z5]),(0,[z597,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z598,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z599]),(0,[z1,z600,z2,z7,z4,z5,z6]),(0,[z1,z9,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z601,z5,z6])],[(0,[z1,z2,z7,z602,z4,z5,z6]),(0,[z1,z2,z7,z4,z603,z5,z6]),(0,[z1,z268,z2,z7,z4,z132,z6])],[(0,[z263,z1,z2,z7,z134,z5,z6]),(0,[z1,z2,z7,z369,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z245,z5,z6])],[(0,[z1,z604,z2,z7,z4,z5,z6]),(0,[z92,z1,z2,z7,z4,z5,z6]),(0,[z1,z605,z2,z7,z4,z5,z6]),(0,[z107,z1,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z406,z10])],[(0,[z40,z1,z2,z7,z4,z5,z6]),(0,[z68,z1,z2,z7,z4,z5,z210]),(0,[z1,z2,z7,z4,z132,z5,z122]),(0,[z1,z606,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z137,z5,z104,z6]),(0,[z1,z2,z7,z4,z137,z5,z344]),(1,[z1,z2,z7,z282,z4,z5]),(0,[z1,z37,z2,z533,z7,z4,z5])],[(0,[z1,z2,z607,z7,z4,z5,z6]),(0,[z1,z2,z608,z7,z4,z5,z6])],[(0,[z1,z7,z4,z5,z14,z10,z6]),(0,[z1,z2,z609,z7,z4,z5,z6]),(0,[z1,z610,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z192,z6]),(0,[z40,z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z113,z98])],[(0,[z149,z1,z2,z7,z4,z5,z6]),(0,[z1,z479,z2,z7,z4,z5,z10])],[(0,[z611,z1,z2,z7,z4,z5,z6]),(1,[z17,z2,z7,z4,z111,z6]),(1,[z1,z9,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z5,z538,z32])],[(1,[z1,z2,z7,z4,z5,z365]),(0,[z1,z2,z7,z4,z5,z6,z612]),(0,[z1,z2,z7,z579,z4,z5,z6])],[],[(0,[z176,z1,z9,z7,z4,z5,z6]),(0,[z271,z1,z37,z2,z7,z4,z5])],[(0,[z1,z2,z613,z7,z4,z5,z6]),(1,[z1,z614,z7,z4,z5,z6])],[(0,[z1,z440,z2,z7,z4,z5,z6])],[(0,[z33,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z531,z6]),(0,[z1,z2,z7,z4,z5,z227,z6]),(0,[z1,z2,z7,z47,z95,z4,z5]),(0,[z1,z164,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z593]),(0,[z1,z2,z7,z282,z153,z4,z5])],[(0,[z1,z2,z84,z7,z4,z5,z6]),(1,[z107,z1,z7,z4,z5,z79]),(0,[z1,z2,z7,z4,z615,z5,z6]),(0,[z1,z2,z7,z4,z5,z42,z73]),(0,[z1,z2,z308,z7,z4,z5,z197]),(0,[z1,z2,z616,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z617,z5,z6]),(0,[z1,z2,z7,z13,z4,z5,z73]),(0,[z1,z2,z7,z146,z80,z5,z6]),(0,[z1,z2,z7,z47,z4,z132,z5]),(0,[z107,z1,z7,z4,z5,z6,z79])],[(0,[z1,z2,z25,z7,z4,z38,z5]),(0,[z1,z2,z618,z7,z4,z5,z6]),(0,[z1,z129,z7,z4,z5,z14,z6]),(0,[z1,z37,z2,z21,z7,z4,z5]),(0,[z1,z37,z2,z203,z7,z4,z5])],[(0,[z2,z7,z13,z4,z5,z111,z6]),(0,[z1,z2,z7,z4,z169,z54,z5]),(0,[z1,z2,z84,z7,z4,z5,z32]),(0,[z1,z2,z7,z619,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z5,z73])],[(1,[z1,z2,z7,z4,z5,z6]),(0,[z263,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z6,z620]),(0,[z1,z2,z7,z4,z5,z10,z6]),(0,[z1,z477,z2,z7,z4,z38,z5])],[(0,[z17,z1,z2,z7,z4,z111,z6])],[(0,[z1,z2,z7,z4,z621,z5,z6]),(0,[z1,z2,z7,z4,z5,z622,z6]),(0,[z1,z37,z623,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z7,z624,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z10,z32])],[(0,[z1,z625,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z132,z5,z73]),(0,[z1,z2,z7,z4,z5,z535,z73])],[(0,[z0,z1,z37,z2,z7,z4,z5]),(1,[z1,z2,z380,z4,z5,z6]),(0,[z1,z626,z2,z7,z4,z5,z6])],[(0,[z91,z1,z2,z7,z304,z5,z6]),(0,[z627,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z211,z80,z5])],[(0,[z628,z1,z2,z7,z4,z5,z6]),(0,[z40,z68,z2,z7,z4,z5,z6])],[(0,[z629,z1,z2,z7,z4,z5,z6]),(0,[z1,z397,z2,z7,z4,z5,z6])],[(0,[z1,z630,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z275]),(1,[z1,z170,z7,z95,z5,z6])],[(0,[z1,z631,z2,z7,z4,z5,z6]),(0,[z48,z1,z2,z7,z289,z5,z6]),(0,[z1,z2,z84,z7,z47,z4,z5]),(0,[z1,z187,z2,z7,z4,z5,z6])],[(1,[z1,z87,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z96,z5,z73])],[(0,[z91,z24,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z632,z6]),(1,[z1,z392,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z5,z111]),(0,[z1,z37,z20,z2,z7,z4,z5]),(0,[z36,z1,z2,z7,z4,z5,z278]),(0,[z271,z1,z2,z7,z47,z4,z5]),(0,[z1,z506,z2,z7,z4,z5,z10])],[(0,[z2,z7,z4,z54,z5,z111,z6]),(0,[z1,z2,z7,z153,z4,z38,z5])],[(0,[z633,z1,z2,z7,z4,z5,z6]),(0,[z1,z220,z9,z7,z4,z5,z6]),(0,[z1,z634,z2,z7,z4,z5,z6]),(0,[z15,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z260]),(0,[z1,z2,z25,z7,z4,z5,z73]),(0,[z1,z635,z2,z7,z4,z5,z6]),(0,[z107,z1,z2,z7,z4,z464,z6]),(0,[z1,z30,z2,z7,z4,z5,z10])],[(0,[z36,z1,z2,z7,z4,z499,z6])],[(0,[z1,z2,z7,z636,z4,z5,z6]),(0,[z1,z2,z7,z4,z31,z132,z5]),(1,[z16,z2,z7,z4,z5,z6])]],
   [[(0,[z637,z1,z2,z7,z4,z5,z6]),(0,[z1,z638,z2,z7,z4,z5,z6]),(0,[z157,z1,z2,z369,z4,z5,z6])],[(0,[z1,z2,z7,z4,z253,z5,z6]),(1,[z1,z2,z7,z4,z169,z5]),(1,[z1,z2,z7,z4,z171,z6]),(1,[z1,z2,z7,z4,z5,z55]),(0,[z1,z2,z7,z4,z38,z132,z5]),(0,[z271,z1,z2,z7,z4,z5,z73])],[(0,[z1,z129,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z639,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z640])],[(0,[z157,z1,z7,z4,z5,z14,z6]),(0,[z1,z9,z20,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z51,z5,z353])],[(0,[z641,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z269,z6]),(1,[z1,z9,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z172,z32]),(0,[z642,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z25,z84,z4,z5,z6]),(0,[z1,z2,z7,z4,z146,z5,z6]),(0,[z1,z2,z7,z4,z5,z643,z6]),(0,[z1,z37,z2,z7,z4,z137,z5])],[(0,[z0,z1,z2,z303,z4,z5,z6]),(0,[z644,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z645,z5,z6]),(0,[z1,z2,z7,z51,z5,z85,z6])],[(0,[z0,z1,z2,z7,z47,z4,z5]),(0,[z1,z37,z2,z410,z7,z4,z5])],[(0,[z46,z263,z2,z7,z4,z5,z6]),(0,[z46,z1,z2,z7,z4,z5,z6]),(0,[z1,z646,z2,z7,z4,z5,z6]),(1,[z1,z37,z2,z7,z47,z5])],[(1,[z383,z1,z2,z7,z4,z5]),(0,[z1,z2,z647,z7,z4,z5,z6]),(0,[z106,z1,z9,z7,z4,z5,z6]),(1,[z1,z479,z2,z7,z4,z5]),(0,[z1,z37,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z137,z111,z6]),(0,[z40,z1,z20,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z648,z6]),(1,[z1,z2,z7,z4,z5,z184]),(0,[z1,z2,z7,z4,z649,z5,z6]),(0,[z1,z2,z7,z4,z67,z5,z73]),(0,[z1,z435,z2,z7,z4,z38,z5])],[(0,[z46,z1,z2,z7,z4,z5,z32]),(0,[z1,z268,z2,z7,z4,z14,z6]),(0,[z1,z614,z2,z7,z4,z5,z6]),(0,[z1,z646,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z13,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z650,z6]),(0,[z1,z2,z7,z4,z5,z6,z142]),(0,[z1,z30,z2,z7,z4,z38,z5])],[(0,[z1,z569,z2,z7,z47,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z73]),(0,[z24,z2,z7,z4,z146,z5,z6]),(0,[z1,z170,z7,z95,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z651])],[(0,[z91,z1,z2,z7,z4,z5,z296]),(0,[z1,z2,z7,z4,z5,z242,z6]),(0,[z652,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z653,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z654,z5,z6]),(0,[z1,z7,z534,z4,z5,z14,z6]),(0,[z1,z2,z21,z7,z4,z5,z73]),(1,[z1,z105,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z655,z6]),(0,[z1,z170,z7,z130,z4,z5,z6])],[(0,[z24,z1,z37,z2,z7,z4,z5]),(0,[z1,z2,z7,z656,z4,z5,z6])],[(0,[z24,z33,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z657,z4,z5,z6]),(0,[z658,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z132,z5,z10]),(0,[z1,z2,z7,z153,z4,z132,z6]),(0,[z1,z2,z355,z7,z4,z5,z6]),(1,[z1,z37,z2,z7,z5,z285])],[(0,[z92,z2,z7,z4,z146,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z659]),(0,[z1,z2,z7,z4,z5,z6,z660]),(0,[z661,z1,z2,z7,z4,z5,z6]),(0,[z434,z1,z2,z7,z4,z5,z6])],[(1,[z397,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z521,z38,z5]),(0,[z209,z1,z2,z7,z4,z5,z6])],[(0,[z1,z9,z7,z13,z4,z5,z6]),(0,[z1,z2,z7,z4,z662,z5,z6])],[],[(0,[z92,z1,z37,z2,z7,z4,z5]),(0,[z68,z1,z7,z4,z5,z14,z6]),(0,[z1,z9,z7,z4,z5,z5,z6])],[(0,[z1,z2,z7,z146,z5,z285,z6]),(0,[z17,z1,z7,z4,z5,z14,z6]),(0,[z40,z1,z37,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z338,z6])],[(0,[z1,z2,z7,z4,z54,z5,z6]),(0,[z1,z2,z7,z4,z96,z5,z10]),(0,[z1,z2,z7,z4,z663,z5,z6]),(0,[z36,z1,z2,z7,z4,z5,z6])],[(0,[z664,z1,z2,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z96,z5]),(0,[z1,z2,z7,z4,z412,z5,z6])],[(0,[z24,z1,z2,z7,z4,z5,z32]),(1,[z634,z2,z7,z4,z5,z6]),(0,[z580,z1,z2,z7,z47,z4,z5])],[(0,[z1,z2,z665,z7,z4,z5,z6]),(0,[z565,z1,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z132,z5,z6]),(0,[z36,z1,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z4,z156,z5,z6]),(0,[z1,z2,z7,z4,z666,z5,z6]),(0,[z56,z1,z2,z7,z4,z5,z6]),(0,[z1,z667,z2,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z47,z4,z5])],[(0,[z91,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z25,z7,z4,z5,z10])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z184]),(1,[z1,z37,z7,z4,z5,z14]),(0,[z1,z7,z4,z67,z5,z450,z6]),(0,[z1,z2,z668,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z669,z6]),(0,[z1,z7,z4,z5,z5,z14,z6])],[(0,[z0,z1,z2,z7,z4,z44,z6]),(0,[z92,z1,z2,z7,z4,z5,z32]),(1,[z1,z2,z7,z4,z5,z49]),(0,[z1,z2,z625,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z670,z5,z6]),(0,[z1,z16,z2,z7,z4,z5,z6])],[(0,[z0,z2,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z111,z42,z6]),(1,[z157,z1,z7,z4,z14,z6]),(0,[z271,z1,z2,z7,z4,z5,z10]),(1,[z1,z2,z7,z4,z264,z5])],[(0,[z1,z2,z7,z671,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z132,z6])],[(0,[z1,z37,z2,z7,z4,z5,z73])],[(0,[z83,z1,z2,z7,z4,z5,z6])],[(0,[z24,z1,z2,z7,z47,z4,z5]),(0,[z1,z672,z2,z7,z4,z5,z6]),(0,[z1,z9,z2,z7,z47,z4,z5]),(1,[z1,z7,z4,z5,z450,z6])],[(0,[z1,z2,z7,z134,z153,z5,z6]),(0,[z114,z1,z7,z4,z5,z14,z6]),(0,[z1,z9,z7,z547,z4,z5,z6]),(0,[z1,z417,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z221,z5,z6])],[(0,[z1,z9,z25,z7,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z42,z6]),(0,[z92,z2,z7,z4,z54,z5,z6]),(0,[z1,z2,z7,z4,z96,z38,z5]),(1,[z1,z37,z2,z7,z4,z5]),(1,[z1,z524,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z5,z77]),(1,[z1,z2,z7,z47,z146,z5])],[(0,[z1,z9,z7,z4,z5,z6,z71]),(1,[z1,z9,z7,z4,z132,z6]),(0,[z1,z2,z308,z7,z4,z137,z6]),(1,[z1,z2,z7,z47,z5,z71])],[(0,[z17,z92,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z67,z5,z10])],[(0,[z92,z1,z2,z7,z47,z4,z5]),(0,[z1,z2,z7,z154,z4,z5,z6]),(1,[z1,z2,z7,z178,z4,z5])],[(0,[z40,z1,z2,z7,z47,z4,z5]),(0,[z1,z50,z170,z7,z4,z5,z6]),(0,[z1,z9,z2,z7,z4,z5,z73])],[(0,[z673,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z153,z4,z5,z10])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z10]),(0,[z91,z1,z2,z7,z4,z5,z466]),(0,[z1,z2,z7,z4,z51,z137,z6])],[(0,[z1,z2,z7,z4,z5,z6,z674]),(0,[z1,z2,z7,z579,z4,z96,z5])],[(0,[z1,z2,z21,z7,z4,z5,z10]),(0,[z271,z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z181,z5,z6])],[(0,[z263,z1,z9,z7,z4,z5,z6])],[(0,[z1,z2,z675,z7,z4,z5,z6]),(0,[z92,z1,z2,z7,z4,z5,z73]),(0,[z1,z37,z277,z2,z7,z4,z5])],[(0,[z1,z2,z7,z676,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z677,z6]),(0,[z1,z678,z2,z7,z4,z5,z6]),(0,[z40,z1,z2,z7,z4,z5,z73]),(0,[z1,z7,z4,z5,z14,z98,z6]),(0,[z1,z2,z7,z307,z4,z5,z6]),(0,[z1,z2,z553,z7,z4,z38,z5])],[(0,[z1,z174,z2,z7,z4,z146,z5]),(0,[z1,z9,z7,z4,z67,z5,z6]),(0,[z157,z1,z138,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z173,z5,z6])],[(0,[z1,z2,z7,z679,z4,z5,z6]),(0,[z48,z540,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z14]),(0,[z680,z1,z2,z7,z4,z5,z6])],[(0,[z681,z1,z2,z7,z4,z5,z6]),(0,[z92,z1,z2,z7,z4,z54,z6]),(0,[z15,z1,z614,z7,z4,z5,z6]),(0,[z157,z1,z2,z256,z4,z5,z6])],[(0,[z1,z9,z7,z153,z4,z5,z6]),(0,[z252,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z682,z5,z6]),(0,[z1,z2,z683,z7,z4,z5,z6])],[(0,[z1,z7,z4,z5,z14,z6,z32]),(0,[z684,z1,z2,z7,z4,z5,z6]),(0,[z157,z434,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z365]),(0,[z1,z9,z21,z7,z4,z5,z6]),(0,[z15,z1,z2,z7,z4,z42,z6]),(0,[z1,z2,z7,z4,z5,z10,z622])],[(1,[z1,z2,z303,z4,z5,z6]),(0,[z1,z2,z7,z153,z146,z5,z6]),(0,[z1,z2,z7,z4,z5,z685,z6])],[(0,[z1,z686,z2,z7,z4,z5,z6]),(1,[z1,z30,z7,z4,z14,z6]),(1,[z1,z2,z7,z47,z4,z5]),(1,[z1,z66,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z38,z5]),(0,[z33,z1,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z687,z6]),(0,[z107,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z25,z7,z4,z5,z290]),(0,[z1,z7,z130,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z688,z6]),(0,[z1,z2,z7,z689,z4,z5,z6]),(0,[z690,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z308,z7,z4,z5,z347]),(0,[z1,z2,z7,z47,z4,z5,z6]),(0,[z1,z66,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z38,z5,z111]),(0,[z1,z2,z7,z4,z5,z691,z6]),(0,[z1,z2,z84,z7,z4,z5,z73]),(0,[z1,z37,z2,z7,z4,z5,z79]),(0,[z1,z2,z21,z7,z4,z38,z5])],[(0,[z692,z1,z2,z7,z4,z5,z6]),(0,[z1,z203,z7,z4,z5,z14,z6]),(1,[z1,z2,z7,z212,z4,z5]),(0,[z15,z1,z2,z7,z4,z5,z32])],[(0,[z1,z2,z7,z134,z5,z85,z6]),(0,[z1,z37,z2,z7,z134,z4,z5]),(0,[z1,z2,z7,z4,z5,z98,z6]),(0,[z1,z2,z7,z4,z5,z693,z6]),(0,[z1,z2,z694,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z32,z310]),(0,[z1,z2,z7,z47,z4,z5,z32]),(1,[z1,z222,z7,z4,z5,z6])],[(0,[z695,z1,z2,z7,z4,z5,z6]),(0,[z46,z1,z37,z2,z7,z4,z5]),(0,[z68,z1,z2,z7,z270,z5,z6]),(0,[z1,z2,z7,z153,z4,z14,z6])],[(0,[z1,z2,z7,z696,z4,z5,z6]),(0,[z692,z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z10,z73]),(0,[z157,z1,z2,z7,z4,z5,z443]),(1,[z1,z2,z7,z4,z5,z73]),(0,[z1,z697,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z698]),(0,[z1,z2,z7,z4,z5,z6,z6]),(0,[z1,z2,z7,z4,z5,z98,z32]),(0,[z1,z7,z141,z4,z5,z14,z6]),(0,[z699,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z700,z6])],[(0,[z1,z2,z7,z5,z285,z6,z71])],[(0,[z36,z634,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z32])],[(0,[z1,z2,z7,z701,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z702,z6]),(0,[z48,z1,z2,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z703,z5,z6])],[(0,[z1,z2,z7,z4,z146,z5,z32])],[(0,[z1,z537,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z137,z5]),(0,[z1,z623,z2,z7,z4,z5,z6])],[(0,[z33,z1,z72,z7,z4,z5,z6]),(0,[z1,z2,z7,z704,z4,z5,z6]),(0,[z1,z268,z7,z4,z5,z14,z6]),(0,[z1,z37,z2,z7,z141,z4,z5]),(0,[z15,z1,z2,z7,z47,z4,z5])],[(0,[z1,z2,z705,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z5,z14]),(0,[z1,z2,z7,z212,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z42,z10]),(0,[z1,z2,z7,z288,z4,z5,z6]),(1,[z1,z2,z308,z4,z137,z6]),(1,[z1,z2,z7,z4,z67,z73])],[(0,[z1,z2,z7,z4,z706,z5,z6]),(1,[z1,z2,z7,z4,z5,z147]),(0,[z157,z1,z115,z7,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z2,z7,z4,z5]),(0,[z1,z7,z18,z5,z14,z6]),(0,[z157,z1,z256,z4,z14,z6]),(0,[z1,z37,z9,z7,z47,z5]),(1,[z1,z7,z4,z5,z708]),(0,[z1,z37,z709,z7,z4,z5])],[(0,[z383,z1,z9,z7,z4,z5]),(0,[z1,z479,z9,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z419])],[(0,[z1,z2,z7,z4,z5,z710]),(0,[z157,z434,z7,z4,z14,z6])],[(0,[z356,z1,z7,z4,z14,z6]),(0,[z1,z21,z141,z5,z14,z6]),(0,[z397,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z282,z4,z430])],[(0,[z1,z2,z25,z4,z39,z6]),(0,[z1,z2,z7,z304,z5,z73]),(0,[z1,z2,z7,z270,z5,z6]),(0,[z1,z7,z4,z14,z6,z73]),(0,[z1,z2,z4,z137,z711,z6])],[(0,[z1,z2,z7,z712,z5,z6]),(0,[z107,z1,z7,z4,z312,z79]),(0,[z16,z2,z7,z4,z137,z6])],[(0,[z1,z7,z4,z14,z215,z6]),(0,[z1,z713,z2,z7,z4,z5]),(1,[z1,z2,z369,z85,z6])],[(0,[z1,z2,z7,z18,z5,z365]),(0,[z1,z714,z2,z7,z4,z5]),(0,[z634,z7,z4,z5,z14,z6]),(0,[z556,z2,z7,z4,z5,z363])],[(0,[z1,z2,z715,z4,z5,z6]),(0,[z1,z7,z4,z211,z5,z14])],[(0,[z1,z2,z7,z155,z5,z10]),(0,[z1,z7,z4,z5,z14,z77]),(0,[z1,z2,z7,z4,z716,z6]),(0,[z1,z2,z7,z4,z312,z6]),(0,[z1,z717,z2,z7,z4,z5]),(0,[z434,z37,z2,z7,z4,z5])],[(0,[z1,z4,z5,z14,z10,z32]),(0,[z1,z718,z7,z4,z5,z6])],[(0,[z1,z37,z2,z7,z4,z39]),(0,[z1,z7,z4,z5,z204,z6]),(0,[z1,z2,z7,z4,z5,z719]),(0,[z1,z268,z7,z4,z14,z269]),(0,[z1,z37,z9,z7,z5,z285]),(0,[z1,z30,z2,z7,z4,z326])],[(0,[z1,z2,z7,z720,z4,z5]),(0,[z1,z2,z13,z4,z39,z6]),(0,[z1,z341,z7,z4,z5,z240]),(0,[z1,z151,z7,z4,z14,z6]),(0,[z1,z2,z7,z721,z4,z5])],[(0,[z48,z1,z130,z307,z5,z6]),(0,[z157,z1,z7,z4,z14,z443]),(0,[z1,z2,z7,z4,z168,z73]),(0,[z1,z722,z7,z4,z5,z6])],[(0,[z0,z34,z7,z4,z44,z6]),(0,[z1,z7,z4,z14,z6,z147]),(0,[z1,z2,z7,z4,z38,z26]),(0,[z1,z355,z7,z4,z38,z5])],[(0,[z1,z72,z7,z4,z44,z6]),(0,[z1,z2,z7,z4,z5,z723]),(0,[z1,z2,z656,z4,z5,z32]),(0,[z1,z2,z7,z724,z5,z6]),(0,[z1,z2,z7,z4,z725,z5])],[(0,[z1,z2,z7,z4,z254,z312])],[(0,[z1,z2,z7,z18,z5,z6]),(0,[z1,z2,z7,z4,z5,z726]),(0,[z1,z2,z7,z4,z5,z727])],[(0,[z595,z1,z2,z4,z42,z6]),(0,[z1,z50,z37,z7,z96,z5]),(0,[z157,z1,z2,z7,z10,z85])],[(0,[z1,z2,z7,z4,z728,z32]),(0,[z1,z97,z7,z4,z5,z32])],[(0,[z1,z9,z7,z4,z5,z365]),(0,[z1,z2,z7,z47,z547,z5]),(0,[z1,z729,z7,z4,z5,z32])],[(0,[z244,z2,z13,z4,z5,z6])],[(0,[z0,z34,z7,z4,z5,z77]),(0,[z1,z2,z380,z18,z5,z6]),(0,[z1,z7,z4,z590,z14,z6]),(0,[z1,z501,z7,z4,z14,z73]),(0,[z1,z9,z7,z4,z38,z132])],[],[(0,[z1,z2,z7,z155,z38,z5]),(0,[z1,z2,z7,z4,z5,z730]),(0,[z731,z2,z7,z4,z5,z6])],[(0,[z189,z2,z7,z4,z5,z6]),(0,[z1,z732,z7,z4,z5,z6]),(0,[z1,z7,z219,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z733]),(0,[z1,z2,z7,z734,z162,z5]),(0,[z157,z1,z2,z7,z4,z419])],[(0,[z1,z2,z7,z4,z735,z5]),(0,[z1,z2,z7,z4,z54,z419])],[(0,[z1,z7,z304,z5,z14,z6]),(0,[z1,z50,z7,z96,z5,z10]),(0,[z157,z397,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z736,z132])],[(0,[z1,z7,z4,z5,z14,z122]),(0,[z1,z737,z7,z4,z5,z6]),(0,[z1,z222,z7,z4,z5,z353]),(0,[z1,z30,z2,z7,z4,z738])],[(0,[z1,z2,z7,z4,z19,z73]),(0,[z1,z2,z7,z4,z5,z446]),(0,[z1,z2,z7,z47,z5,z739])],[(0,[z1,z9,z7,z4,z5,z6]),(0,[z1,z740,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z741,z5])],[(0,[z1,z2,z7,z4,z742,z6]),(0,[z1,z7,z369,z4,z14,z6]),(0,[z1,z743,z2,z7,z4,z5]),(0,[z1,z744,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z745]),(0,[z1,z7,z4,z450,z6,z73]),(0,[z1,z2,z7,z746,z38,z5])]],
   [[(0,[z1,z2,z7,z178,z134,z5]),(0,[z747,z2,z7,z4,z5,z6]),(0,[z1,z748,z7,z4,z5,z6]),(0,[z1,z138,z7,z4,z5,z73])],[(0,[z46,z2,z7,z47,z134,z5]),(0,[z1,z458,z2,z7,z4,z38]),(0,[z1,z7,z4,z264,z5,z14]),(0,[z1,z2,z7,z4,z5,z749])],[(0,[z1,z2,z7,z4,z39,z73]),(0,[z1,z7,z4,z14,z142,z73]),(0,[z15,z1,z2,z4,z711,z6]),(0,[z1,z2,z256,z4,z5,z73]),(0,[z1,z37,z2,z7,z4,z750])],[(0,[z1,z7,z4,z546,z14,z6]),(0,[z1,z9,z380,z4,z5,z6]),(0,[z556,z2,z7,z394,z5,z6])],[(0,[z751,z1,z7,z4,z5,z6]),(0,[z1,z7,z4,z14,z14,z73]),(0,[z1,z2,z7,z752,z4,z5])],[(0,[z1,z753,z2,z7,z4,z5]),(0,[z1,z2,z7,z754,z5,z6]),(0,[z755,z2,z7,z4,z5,z6]),(0,[z434,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z304,z5,z10]),(0,[z1,z2,z7,z756,z5,z6]),(0,[z1,z7,z4,z5,z757,z6]),(0,[z536,z2,z7,z4,z5,z278])],[(0,[z1,z2,z7,z4,z5,z758]),(0,[z7,z4,z146,z111,z14,z6]),(0,[z1,z7,z4,z111,z14,z6]),(0,[z690,z2,z7,z4,z5,z210]),(0,[z189,z2,z7,z47,z4,z5]),(0,[z1,z115,z7,z4,z5,z32]),(0,[z1,z7,z4,z5,z759,z6])],[(0,[z1,z2,z7,z4,z5,z760]),(0,[z1,z2,z7,z307,z242,z6]),(1,[z1,z7,z4,z14,z310]),(0,[z1,z343,z7,z4,z5,z32])],[(0,[z1,z2,z7,z4,z761,z5])],[(0,[z1,z7,z270,z5,z14,z6]),(0,[z36,z1,z80,z5,z14,z6]),(0,[z1,z37,z7,z4,z14,z73]),(0,[z1,z20,z7,z4,z5,z535]),(0,[z536,z2,z7,z4,z499,z6])],[(0,[z1,z2,z7,z155,z5,z192]),(0,[z1,z2,z380,z4,z5,z240])],[(0,[z1,z762,z7,z4,z5,z6]),(0,[z1,z7,z153,z4,z204,z6])],[(0,[z1,z2,z7,z763,z5,z6]),(0,[z1,z2,z369,z4,z5,z73]),(1,[z1,z2,z7,z4,z738])],[(0,[z1,z7,z13,z4,z14,z73]),(0,[z1,z2,z21,z559,z5,z6])],[],[(0,[z1,z764,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z765]),(0,[z1,z37,z2,z7,z5,z648]),(0,[z1,z7,z619,z4,z14,z6]),(0,[z1,z7,z4,z5,z14,z73])],[(0,[z1,z2,z7,z146,z5,z100])],[(0,[z1,z9,z7,z4,z169,z5]),(0,[z1,z9,z7,z4,z551,z6]),(0,[z1,z9,z7,z4,z5,z55])],[(0,[z1,z2,z7,z134,z5,z53]),(0,[z1,z2,z7,z4,z5,z766]),(0,[z1,z2,z7,z4,z767,z5]),(0,[z1,z7,z4,z5,z768,z6])],[(0,[z1,z183,z4,z5,z14,z6]),(0,[z1,z2,z7,z769,z4,z5]),(0,[z540,z2,z130,z4,z5,z6])],[],[(0,[z1,z2,z7,z770,z4,z5]),(0,[z1,z20,z7,z4,z312,z6]),(0,[z1,z2,z7,z4,z65,z350]),(0,[z1,z2,z7,z4,z5,z771])],[(0,[z1,z7,z4,z655,z14,z6]),(0,[z1,z2,z7,z772,z5,z6]),(0,[z1,z2,z7,z4,z773,z6]),(0,[z1,z774,z7,z4,z5,z6]),(0,[z1,z57,z7,z5,z381,z6])],[(0,[z1,z37,z355,z7,z4,z5]),(0,[z1,z355,z7,z4,z65,z6]),(0,[z15,z1,z2,z4,z42,z310]),(0,[z1,z7,z4,z5,z775,z32])],[(0,[z1,z506,z7,z4,z14,z10])],[(0,[z1,z152,z7,z4,z5,z32]),(0,[z1,z7,z4,z5,z14,z147]),(0,[z1,z2,z7,z4,z776,z6])],[(0,[z1,z777,z7,z4,z5,z6]),(0,[z397,z2,z7,z4,z5,z158]),(0,[z1,z2,z7,z5,z739,z6]),(0,[z1,z2,z7,z4,z738,z6])],[(0,[z1,z2,z778,z4,z5,z6]),(0,[z17,z2,z183,z4,z111,z6]),(0,[z468,z2,z7,z4,z5,z210]),(0,[z1,z7,z4,z96,z14,z73]),(0,[z1,z7,z4,z14,z42,z310])],[(0,[z1,z72,z3,z4,z5,z6]),(0,[z0,z34,z7,z4,z5,z73]),(0,[z1,z2,z7,z4,z5,z779]),(0,[z24,z2,z25,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z363])],[(0,[z1,z2,z7,z167,z5,z6]),(0,[z1,z7,z4,z14,z73,z73]),(0,[z1,z2,z7,z4,z5,z780]),(0,[z1,z2,z445,z4,z137,z6]),(0,[z1,z2,z7,z162,z5,z73]),(0,[z1,z2,z7,z4,z280,z5]),(0,[z1,z2,z668,z4,z5,z10])],[(0,[z1,z2,z7,z4,z781,z6]),(0,[z1,z174,z9,z7,z4,z5]),(0,[z36,z1,z2,z80,z5,z6]),(0,[z1,z2,z4,z80,z499,z6])]],
   [[(0,[z1,z2,z7,z304,z156,z6]),(0,[z1,z4,z80,z14,z42,z6]),(0,[z1,z9,z7,z47,z103,z5]),(0,[z1,z2,z4,z5,z693,z32])],[(0,[z1,z2,z7,z47,z18,z5]),(0,[z526,z1,z2,z80,z5,z6])],[(0,[z1,z2,z7,z4,z782,z5]),(0,[z1,z138,z7,z4,z5,z10])],[(0,[z1,z2,z783,z4,z5,z6]),(0,[z1,z2,z7,z4,z784,z5]),(0,[z1,z2,z7,z785,z5,z6])],[(0,[z1,z2,z7,z4,z39,z10]),(0,[z1,z2,z7,z4,z5,z786])],[(0,[z1,z7,z4,z5,z14,z53]),(0,[z157,z1,z2,z7,z787,z6])],[(0,[z1,z788,z7,z4,z5,z6]),(0,[z1,z129,z84,z4,z5,z32])],[(0,[z1,z2,z7,z4,z5,z789]),(0,[z1,z2,z7,z4,z790,z5]),(0,[z1,z2,z7,z4,z791,z5]),(0,[z1,z2,z203,z4,z5,z32]),(0,[z56,z1,z2,z194,z4,z5])],[(0,[z1,z2,z7,z4,z5,z792])],[(0,[z1,z87,z7,z167,z5,z6]),(0,[z263,z2,z7,z190,z146,z5]),(0,[z1,z2,z793,z7,z4,z5]),(0,[z1,z794,z2,z7,z4,z5]),(0,[z1,z7,z4,z14,z73,z216]),(0,[z536,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z795,z4,z5])],[],[(0,[z91,z2,z13,z4,z5,z6]),(0,[z556,z2,z7,z4,z5,z6])],[(0,[z1,z7,z4,z169,z54,z14]),(0,[z1,z2,z7,z47,z270,z5]),(0,[z316,z1,z2,z4,z5,z10]),(0,[z1,z7,z4,z5,z14,z796])],[(0,[z634,z9,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z4,z797])],[(0,[z1,z2,z308,z4,z27,z6]),(0,[z1,z7,z4,z67,z14,z73]),(0,[z1,z798,z2,z7,z4,z5])],[(0,[z34,z13,z130,z4,z5,z6]),(0,[z15,z1,z4,z14,z42,z6]),(0,[z1,z2,z7,z4,z312,z32]),(0,[z1,z2,z369,z4,z5,z10])],[(0,[z1,z2,z7,z4,z799,z6]),(1,[z1,z7,z4,z312,z79]),(0,[z1,z2,z7,z4,z5,z800])],[(0,[z540,z2,z7,z4,z5,z6]),(0,[z1,z7,z153,z4,z14,z73]),(0,[z1,z2,z21,z141,z5,z266]),(0,[z1,z7,z4,z5,z204,z32]),(0,[z1,z138,z7,z4,z38,z5])],[(0,[z1,z478,z7,z4,z14,z6]),(0,[z1,z2,z7,z307,z213,z6]),(0,[z1,z7,z4,z5,z14,z10])],[(0,[z2,z801,z7,z4,z5,z6]),(0,[z1,z802,z7,z4,z54,z6]),(0,[z48,z540,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z803,z5]),(0,[z1,z311,z7,z4,z171,z6]),(0,[z1,z537,z7,z4,z5,z278]),(0,[z1,z2,z256,z4,z38,z5])],[(0,[z1,z392,z183,z4,z5,z6]),(0,[z1,z9,z7,z4,z264,z5])],[(0,[z1,z2,z7,z4,z5,z804]),(0,[z189,z37,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z787,z6])],[(0,[z91,z87,z13,z4,z5,z6]),(0,[z1,z2,z7,z394,z42,z6]),(0,[z1,z2,z7,z47,z394,z5]),(0,[z434,z2,z7,z4,z38,z5]),(0,[z1,z97,z7,z4,z38,z5])],[(0,[z1,z279,z7,z4,z14,z73]),(0,[z1,z537,z7,z4,z499,z6])],[(0,[z15,z1,z2,z162,z42,z6]),(0,[z1,z2,z7,z805,z4,z5])],[(0,[z1,z2,z496,z4,z5,z32]),(0,[z1,z2,z7,z394,z5,z6]),(0,[z397,z2,z7,z153,z5,z6])],[(0,[z2,z7,z4,z5,z806,z210]),(0,[z68,z1,z7,z4,z14,z73]),(0,[z1,z37,z2,z7,z289,z5]),(0,[z1,z7,z4,z14,z73,z79]),(0,[z565,z1,z334,z4,z5,z6]),(0,[z1,z20,z7,z4,z5,z708])],[(0,[z1,z34,z7,z4,z44,z6]),(0,[z1,z2,z7,z807,z5,z6])],[(0,[z1,z2,z7,z4,z156,z296]),(0,[z1,z2,z7,z4,z5,z808]),(0,[z1,z2,z7,z270,z5,z73]),(0,[z1,z228,z37,z7,z4,z14]),(0,[z530,z1,z2,z4,z42,z6])],[(0,[z1,z2,z7,z190,z4,z5]),(0,[z1,z2,z7,z4,z42,z424]),(0,[z1,z2,z7,z4,z5,z809])],[(0,[z1,z129,z7,z4,z242,z6]),(0,[z1,z810,z7,z4,z5,z14]),(0,[z1,z9,z7,z178,z4,z5]),(0,[z1,z2,z7,z4,z280,z137]),(0,[z1,z7,z4,z5,z811,z6]),(0,[z1,z228,z2,z7,z4,z75])],[(0,[z0,z34,z7,z4,z5,z10]),(0,[z40,z1,z7,z4,z14,z73])]],
   [[(0,[z1,z2,z7,z4,z812,z6]),(0,[z1,z813,z7,z4,z5,z6]),(0,[z1,z7,z4,z650,z14,z6]),(0,[z1,z814,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z815]),(0,[z1,z2,z7,z162,z5,z10])],[(0,[z1,z7,z4,z5,z816,z6]),(0,[z1,z7,z4,z14,z76,z73])],[(0,[z1,z817,z2,z7,z4,z5]),(0,[z1,z7,z4,z156,z14,z6]),(0,[z1,z2,z7,z134,z173,z5]),(0,[z1,z259,z7,z47,z4,z5]),(0,[z1,z638,z7,z96,z5,z6]),(0,[z1,z9,z7,z4,z5,z122])],[(0,[z1,z2,z7,z4,z5,z818]),(0,[z1,z819,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z820]),(0,[z1,z20,z7,z4,z5,z273]),(0,[z1,z821,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z132,z344]),(0,[z1,z2,z4,z5,z10,z822])],[(0,[z34,z7,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z248,z6]),(0,[z1,z2,z7,z823,z4,z5])],[(0,[z1,z50,z7,z47,z96,z5])],[(0,[z1,z341,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z824])],[(0,[z1,z2,z7,z4,z39,z825]),(0,[z1,z2,z826,z4,z5,z6]),(0,[z1,z259,z7,z4,z169,z5]),(0,[z1,z7,z4,z14,z71,z73]),(0,[z1,z2,z7,z4,z5,z827]),(0,[z157,z1,z2,z7,z85,z6])],[(0,[z1,z2,z7,z18,z5,z73]),(0,[z1,z7,z828,z96,z5,z6]),(0,[z107,z1,z7,z4,z5,z231]),(0,[z1,z2,z7,z4,z5,z829])],[(0,[z1,z2,z7,z830,z4,z5]),(0,[z1,z7,z153,z272,z14,z6]),(0,[z62,z1,z2,z4,z42,z6]),(0,[z1,z831,z7,z4,z5,z6]),(0,[z1,z832,z7,z4,z5,z6]),(0,[z1,z115,z7,z4,z38,z5])],[(0,[z1,z2,z7,z4,z5,z833]),(1,[z2,z183,z4,z111,z6]),(0,[z1,z834,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z835,z6]),(0,[z1,z7,z134,z153,z14,z6]),(0,[z1,z341,z380,z4,z5,z6]),(0,[z1,z2,z7,z4,z836,z6]),(0,[z1,z2,z7,z4,z5,z837])],[(0,[z1,z2,z7,z4,z5,z838]),(0,[z1,z7,z4,z111,z14,z32]),(0,[z1,z839,z2,z7,z307,z5]),(0,[z840,z1,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z841,z6]),(0,[z1,z7,z4,z111,z104,z6]),(0,[z1,z2,z7,z4,z842,z412]),(0,[z1,z2,z7,z47,z4,z499]),(0,[z1,z30,z2,z7,z4,z280]),(0,[z1,z506,z2,z7,z4,z38])],[(0,[z1,z843,z7,z4,z5,z6]),(0,[z92,z2,z7,z253,z5,z6]),(0,[z1,z2,z844,z4,z5,z6]),(0,[z1,z2,z7,z4,z845,z6])],[(0,[z1,z7,z200,z96,z5,z6]),(0,[z846,z2,z7,z4,z5,z6])],[(0,[z24,z2,z847,z4,z5,z6]),(0,[z189,z2,z7,z4,z5,z73]),(0,[z1,z821,z7,z47,z4,z5])],[],[(0,[z1,z7,z4,z5,z14,z290]),(0,[z1,z7,z95,z828,z5,z6]),(0,[z1,z7,z724,z5,z14,z6]),(0,[z1,z7,z153,z4,z14,z10]),(0,[z1,z9,z7,z4,z5,z848])],[(0,[z1,z7,z4,z5,z14,z192])],[(0,[z24,z2,z7,z4,z39,z6]),(0,[z1,z646,z7,z4,z5,z362]),(0,[z1,z7,z4,z38,z5,z204])],[(0,[z1,z2,z7,z4,z5,z849]),(0,[z1,z9,z7,z4,z5,z73]),(0,[z1,z537,z7,z4,z5,z32]),(0,[z1,z343,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z850,z6]),(0,[z1,z2,z4,z5,z711,z6]),(0,[z1,z7,z4,z5,z104,z73])],[(0,[z1,z313,z7,z4,z14,z6]),(0,[z1,z7,z534,z4,z14,z73]),(0,[z851,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z852])],[(0,[z337,z1,z130,z4,z5,z6])],[(0,[z1,z2,z7,z427,z5,z6]),(0,[z1,z2,z7,z4,z853,z5]),(0,[z627,z2,z13,z4,z5,z6]),(0,[z1,z37,z2,z7,z270,z5]),(0,[z1,z2,z7,z4,z5,z854]),(0,[z855,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z856,z5])],[(0,[z1,z2,z857,z4,z5,z6]),(0,[z1,z2,z7,z858,z5,z6])],[(0,[z1,z7,z4,z14,z301,z6]),(0,[z1,z859,z7,z4,z5,z6]),(0,[z1,z479,z2,z7,z47,z5])],[(0,[z1,z7,z4,z14,z113,z73]),(0,[z107,z1,z7,z4,z5,z79]),(0,[z1,z479,z2,z7,z80,z5]),(0,[z1,z2,z4,z711,z42,z6])],[(0,[z1,z2,z7,z270,z5,z10]),(0,[z1,z2,z7,z4,z5,z860]),(0,[z1,z7,z4,z132,z773,z6])],[(0,[z519,z1,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z861]),(0,[z1,z9,z308,z4,z137,z6])]],
   [[(0,[z1,z2,z183,z4,z5,z365]),(0,[z1,z9,z7,z4,z5,z147]),(0,[z1,z2,z7,z4,z5,z862]),(0,[z1,z2,z863,z4,z5,z6]),(0,[z1,z864,z7,z4,z5,z6])],[(0,[z0,z34,z7,z4,z5,z192]),(0,[z1,z7,z153,z146,z14,z6]),(0,[z1,z2,z7,z4,z5,z865]),(0,[z1,z2,z7,z4,z866,z5])],[(0,[z1,z2,z7,z4,z464,z6]),(0,[z1,z7,z4,z5,z14,z197])],[(0,[z17,z392,z7,z4,z111,z6])],[(0,[z1,z9,z7,z4,z632,z6]),(0,[z1,z37,z2,z7,z307,z5]),(0,[z1,z2,z308,z4,z145,z5]),(0,[z1,z718,z7,z4,z5,z10])],[(0,[z1,z2,z7,z4,z5,z867]),(0,[z91,z2,z847,z4,z5,z6]),(0,[z1,z84,z7,z4,z14,z73]),(0,[z1,z2,z7,z868,z4,z5])],[(0,[z1,z2,z380,z4,z5,z6]),(0,[z1,z869,z7,z4,z5,z6]),(0,[z540,z2,z7,z4,z5,z49]),(0,[z1,z228,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z870,z5])],[(0,[z556,z37,z2,z7,z4,z5]),(0,[z556,z614,z7,z4,z5,z6]),(0,[z1,z2,z7,z871,z4,z5])],[(0,[z1,z2,z7,z47,z4,z44]),(0,[z1,z309,z7,z4,z42,z6])],[(0,[z1,z34,z3,z4,z5,z6]),(0,[z1,z2,z7,z146,z5,z419]),(0,[z1,z872,z2,z7,z4,z5])],[(0,[z40,z7,z4,z5,z14,z210]),(0,[z1,z2,z873,z4,z5,z6]),(0,[z1,z2,z7,z874,z4,z5])],[(0,[z1,z2,z7,z579,z146,z5]),(0,[z1,z9,z7,z4,z5,z53]),(0,[z1,z2,z7,z18,z5,z10]),(0,[z1,z37,z2,z7,z298,z5]),(0,[z1,z2,z7,z4,z5,z875])],[(0,[z1,z2,z7,z4,z5,z876])],[(0,[z1,z2,z7,z270,z38,z5]),(0,[z540,z37,z2,z7,z4,z5]),(0,[z271,z1,z4,z5,z14,z10])],[],[(0,[z15,z1,z2,z4,z42,z446])],[(0,[z1,z2,z7,z4,z5,z877]),(0,[z1,z2,z7,z4,z878,z6]),(0,[z1,z7,z307,z5,z14,z6]),(0,[z1,z7,z4,z14,z335,z6])],[(0,[z1,z2,z7,z879,z4,z5]),(0,[z556,z2,z7,z4,z5,z32]),(0,[z1,z433,z2,z7,z4,z38])],[(0,[z1,z2,z308,z4,z173,z5])],[(0,[z1,z2,z7,z4,z202,z6]),(0,[z1,z2,z7,z4,z5,z880]),(0,[z189,z2,z7,z4,z5,z10]),(0,[z1,z255,z2,z533,z4,z5])],[(0,[z1,z2,z7,z4,z881,z6]),(0,[z383,z1,z7,z4,z5,z14]),(0,[z189,z2,z7,z4,z242,z6]),(0,[z1,z2,z7,z4,z5,z882]),(0,[z1,z479,z7,z4,z5,z14])],[(0,[z1,z2,z7,z4,z171,z6]),(0,[z1,z2,z200,z4,z5,z32]),(0,[z1,z2,z7,z4,z14,z344])],[(0,[z1,z2,z7,z167,z5,z73]),(0,[z1,z2,z883,z7,z4,z5]),(0,[z271,z1,z2,z4,z5,z10]),(0,[z1,z2,z7,z5,z285,z739])],[(0,[z465,z2,z25,z4,z5,z6]),(0,[z1,z274,z2,z7,z47,z5]),(0,[z540,z2,z7,z4,z5,z32]),(0,[z536,z2,z7,z47,z4,z5]),(0,[z1,z884,z7,z4,z65,z6]),(0,[z36,z1,z2,z80,z5,z73]),(0,[z1,z2,z7,z4,z5,z885])],[(0,[z1,z7,z4,z27,z14,z6]),(0,[z1,z2,z183,z47,z4,z5]),(0,[z1,z9,z7,z4,z5,z10]),(0,[z1,z2,z7,z47,z4,z464]),(0,[z1,z2,z7,z886,z5,z6])],[(0,[z1,z2,z7,z4,z887,z5]),(0,[z1,z50,z117,z7,z96,z5]),(0,[z1,z7,z888,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z889]),(0,[z1,z309,z7,z47,z4,z5]),(0,[z1,z7,z4,z5,z104,z10])],[(0,[z1,z2,z7,z890,z5,z6]),(0,[z1,z2,z7,z18,z38,z5]),(0,[z1,z2,z7,z289,z5,z126])],[(0,[z1,z105,z7,z4,z5,z14])],[(0,[z1,z37,z2,z7,z4,z499])],[(0,[z1,z2,z7,z4,z5,z891]),(0,[z1,z37,z2,z7,z143,z5])],[(0,[z1,z2,z7,z4,z5,z892]),(0,[z1,z893,z2,z7,z4,z5]),(0,[z330,z2,z7,z4,z111,z6]),(0,[z1,z2,z7,z4,z894,z5]),(0,[z1,z2,z7,z4,z5,z184]),(0,[z1,z170,z7,z95,z171,z6]),(0,[z1,z492,z7,z4,z14,z6]),(0,[z1,z7,z4,z14,z73,z354])],[(0,[z1,z2,z7,z4,z5,z895]),(0,[z1,z2,z7,z4,z896,z5]),(0,[z1,z2,z7,z579,z4,z5]),(0,[z1,z2,z308,z4,z38,z137])]],
   [[(0,[z1,z2,z7,z4,z5,z897]),(0,[z1,z2,z898,z7,z4,z5]),(0,[z1,z2,z7,z899,z167,z5]),(0,[z1,z2,z7,z4,z5,z900]),(0,[z1,z2,z7,z4,z487,z73])],[(0,[z1,z2,z7,z4,z5,z901])],[(0,[z1,z2,z7,z4,z5,z902]),(0,[z189,z2,z7,z4,z38,z5]),(0,[z903,z9,z7,z4,z5,z6])],[(0,[z1,z2,z7,z427,z44,z6]),(0,[z1,z2,z7,z4,z5,z904]),(0,[z91,z2,z13,z4,z5,z73]),(0,[z1,z2,z905,z4,z5,z6]),(0,[z1,z2,z183,z4,z54,z6]),(0,[z1,z2,z7,z5,z906,z32])],[(0,[z1,z2,z7,z4,z5,z278])],[(0,[z1,z2,z7,z4,z5,z907]),(0,[z1,z2,z7,z908,z5,z6])],[(0,[z1,z909,z2,z7,z4,z5])],[(0,[z1,z2,z7,z910,z4,z5]),(0,[z1,z911,z2,z7,z4,z5]),(0,[z1,z2,z7,z912,z4,z5]),(0,[z1,z170,z7,z95,z5,z184]),(0,[z1,z9,z7,z4,z38,z5]),(0,[z1,z913,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z914]),(0,[z1,z2,z7,z4,z5,z915]),(0,[z1,z2,z7,z4,z916,z6]),(0,[z214,z2,z7,z4,z111,z6]),(0,[z1,z2,z7,z917,z5,z6]),(0,[z1,z2,z7,z4,z499,z6]),(0,[z1,z2,z7,z4,z211,z5])],[(0,[z1,z918,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z206,z73]),(0,[z1,z2,z7,z153,z51,z73]),(0,[z580,z1,z7,z4,z181,z5])],[(0,[z1,z7,z94,z4,z14,z6])],[(0,[z1,z7,z47,z134,z5,z14])],[(0,[z1,z2,z7,z4,z5,z919]),(0,[z1,z259,z7,z4,z5,z73]),(0,[z1,z2,z7,z289,z5,z73]),(0,[z1,z920,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z736,z5]),(0,[z1,z7,z4,z38,z137,z14]),(0,[z1,z414,z7,z4,z14,z6]),(0,[z1,z255,z9,z7,z4,z5]),(0,[z1,z9,z7,z4,z145,z5]),(0,[z397,z2,z7,z4,z5,z32])],[(0,[z152,z7,z13,z4,z5,z6]),(0,[z1,z341,z7,z4,z5,z32]),(0,[z921,z2,z7,z4,z5,z6])],[(0,[z48,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z922,z5]),(0,[z1,z2,z302,z4,z5,z10])],[(0,[z1,z2,z7,z4,z5,z923]),(0,[z15,z1,z2,z4,z42,z363])],[(0,[z1,z2,z7,z304,z5,z296]),(0,[z1,z2,z7,z4,z5,z924]),(0,[z1,z2,z7,z4,z925,z6]),(0,[z1,z7,z109,z4,z14,z6])],[(0,[z1,z2,z7,z4,z926,z6]),(0,[z1,z2,z21,z7,z178,z5]),(0,[z1,z2,z7,z394,z5,z73]),(0,[z1,z569,z7,z154,z4,z5])],[(0,[z1,z2,z303,z4,z5,z927]),(0,[z1,z9,z7,z4,z156,z6]),(0,[z1,z268,z7,z47,z4,z14])],[(0,[z1,z2,z7,z4,z5,z928])],[(0,[z0,z37,z34,z7,z4,z5]),(0,[z48,z1,z130,z289,z5,z6]),(0,[z851,z37,z2,z7,z4,z5])],[(0,[z1,z2,z618,z4,z5,z32])],[(0,[z1,z2,z7,z4,z5,z49]),(0,[z929,z2,z7,z4,z5,z6]),(0,[z536,z2,z7,z4,z65,z6])],[(0,[z1,z7,z4,z5,z930,z6]),(0,[z157,z1,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z264,z5])],[(0,[z1,z2,z7,z167,z5,z10])],[(0,[z1,z37,z129,z84,z4,z5]),(0,[z36,z1,z2,z80,z5,z10])],[(0,[z1,z9,z7,z4,z173,z5])],[(0,[z1,z931,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z132,z443]),(0,[z1,z20,z7,z4,z5,z26]),(0,[z1,z932,z7,z4,z5,z6])],[(0,[z1,z152,z13,z4,z5,z6]),(0,[z1,z933,z7,z4,z5,z6])],[(0,[z1,z7,z4,z5,z248,z73]),(0,[z1,z614,z7,z4,z5,z6])],[(0,[z1,z246,z2,z7,z47,z5]),(0,[z189,z2,z7,z4,z213,z6]),(0,[z1,z57,z7,z96,z5,z6]),(0,[z1,z2,z7,z4,z132,z424]),(0,[z1,z934,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z450,z32])],[(0,[z1,z2,z308,z194,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z156,z466]),(0,[z1,z2,z7,z4,z5,z935]),(0,[z157,z1,z2,z7,z85,z73])],[(0,[z1,z936,z2,z7,z18,z5]),(0,[z1,z2,z203,z4,z5,z822])],[(0,[z1,z937,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z8,z5]),(0,[z1,z7,z938,z4,z5,z6]),(0,[z1,z9,z7,z4,z132,z32])],[(0,[z1,z2,z7,z4,z5,z939])],[(0,[z1,z2,z7,z4,z202,z77]),(0,[z940,z1,z2,z7,z4,z5]),(0,[z372,z2,z7,z4,z5,z210]),(0,[z1,z7,z4,z5,z941,z6]),(0,[z1,z537,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z137,z326])],[(0,[z91,z2,z13,z4,z5,z10])],[(0,[z1,z343,z7,z4,z132,z6]),(0,[z1,z2,z7,z4,z38,z649])],[(0,[z1,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z167,z38,z5]),(0,[z1,z7,z4,z5,z248,z147]),(0,[z225,z1,z2,z4,z5,z10]),(0,[z1,z7,z4,z5,z32,z942])],[(0,[z1,z9,z7,z4,z5,z197]),(0,[z1,z2,z7,z47,z5,z485])],[(0,[z1,z2,z7,z4,z44,z897]),(0,[z1,z802,z7,z4,z14,z6])],[(0,[z1,z2,z943,z7,z4,z5]),(0,[z1,z129,z7,z4,z14,z73])],[(0,[z1,z2,z7,z944,z4,z5]),(0,[z581,z1,z130,z4,z5,z6]),(0,[z1,z129,z84,z4,z5,z116]),(0,[z15,z1,z2,z394,z42,z6]),(0,[z1,z2,z7,z4,z945,z5])],[(0,[z1,z2,z7,z4,z946,z6]),(0,[z1,z7,z696,z4,z14,z6]),(0,[z1,z2,z380,z4,z5,z32])],[(0,[z1,z7,z4,z947,z5,z6]),(0,[z1,z7,z4,z272,z14,z73]),(0,[z1,z2,z7,z4,z948,z5]),(0,[z1,z2,z7,z4,z5,z949]),(0,[z950,z2,z7,z4,z5,z6])],[(0,[z1,z259,z7,z4,z5,z10]),(0,[z1,z2,z7,z289,z5,z10]),(0,[z1,z2,z7,z4,z5,z951])],[(0,[z1,z9,z186,z7,z4,z5]),(0,[z1,z37,z341,z7,z4,z5]),(0,[z1,z2,z7,z952,z5,z6]),(0,[z1,z2,z7,z289,z242,z6]),(0,[z1,z2,z7,z4,z953,z5]),(0,[z954,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z955,z5,z6]),(0,[z40,z9,z7,z4,z5,z210]),(0,[z1,z170,z7,z95,z5,z32]),(0,[z1,z956,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z156,z779]),(0,[z1,z7,z4,z14,z210,z73]),(0,[z1,z957,z7,z4,z5,z6]),(0,[z1,z958,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z450,z73]),(0,[z1,z2,z501,z4,z5,z310])],[(0,[z1,z2,z7,z427,z5,z73]),(0,[z1,z87,z7,z4,z5,z32]),(0,[z1,z2,z7,z167,z156,z6]),(0,[z17,z2,z7,z4,z716,z6]),(0,[z328,z2,z7,z4,z5,z210]),(0,[z1,z2,z7,z959,z4,z5]),(0,[z1,z66,z7,z4,z5,z6]),(0,[z1,z30,z7,z4,z14,z6])],[(0,[z1,z2,z7,z960,z5,z6]),(0,[z1,z2,z961,z4,z5,z6]),(0,[z1,z7,z4,z5,z962,z6]),(0,[z627,z1,z2,z80,z5,z6]),(0,[z634,z2,z7,z4,z5,z278]),(0,[z1,z2,z7,z394,z5,z10]),(0,[z1,z2,z7,z47,z5,z500])],[(0,[z91,z2,z13,z4,z38,z5]),(0,[z1,z355,z7,z141,z5,z6]),(0,[z556,z2,z7,z4,z38,z5])],[],[(0,[z1,z2,z7,z4,z5,z963]),(0,[z16,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z264,z5,z204])],[],[(0,[z1,z2,z7,z4,z5,z964]),(0,[z1,z965,z7,z4,z137,z6])],[(0,[z1,z2,z7,z4,z213,z966]),(0,[z1,z138,z369,z4,z5,z6])],[(0,[z540,z2,z7,z4,z38,z5]),(0,[z1,z7,z4,z5,z14,z310]),(0,[z1,z7,z4,z14,z424,z6]),(0,[z1,z57,z7,z153,z14,z6]),(0,[z1,z7,z4,z5,z14,z353]),(0,[z1,z2,z7,z4,z464,z73])],[(0,[z1,z967,z7,z47,z4,z5])],[(0,[z1,z152,z7,z304,z5,z6]),(0,[z1,z7,z4,z5,z14,z296]),(0,[z968,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z969,z6]),(0,[z1,z2,z7,z219,z5,z98]),(0,[z1,z7,z153,z80,z14,z6]),(0,[z1,z2,z7,z970,z4,z5])],[(0,[z1,z7,z162,z5,z14,z6]),(0,[z1,z228,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z31,z73]),(0,[z1,z2,z7,z4,z132,z76]),(0,[z434,z2,z369,z4,z5,z6])],[(0,[z1,z7,z4,z39,z971,z6]),(0,[z91,z2,z13,z4,z156,z6]),(0,[z1,z392,z7,z47,z4,z5]),(0,[z1,z7,z4,z5,z248,z10])]],
   [[(0,[z972,z1,z2,z7,z4,z5]),(0,[z1,z2,z973,z4,z5,z6]),(0,[z1,z268,z7,z4,z14,z73]),(0,[z1,z479,z2,z7,z4,z5]),(0,[z1,z479,z2,z7,z413,z5])],[(0,[z434,z7,z4,z5,z14,z6])],[(0,[z1,z2,z7,z4,z5,z974]),(0,[z1,z2,z183,z4,z5,z73]),(0,[z1,z7,z194,z4,z5,z14]),(0,[z1,z2,z7,z394,z38,z5]),(1,[z1,z2,z4,z711,z6]),(0,[z1,z2,z4,z173,z5,z42])],[(0,[z1,z537,z7,z4,z65,z6]),(0,[z1,z309,z7,z4,z5,z73])],[(0,[z1,z7,z4,z146,z14,z73]),(0,[z1,z7,z4,z213,z14,z6]),(0,[z1,z9,z7,z4,z5,z975]),(0,[z1,z2,z339,z212,z4,z5])],[(0,[z1,z9,z7,z976,z5,z6])],[(0,[z1,z268,z7,z4,z773,z6])],[(0,[z977,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z194,z4,z5]),(0,[z1,z2,z141,z978,z5,z6]),(0,[z1,z2,z7,z4,z979,z5]),(0,[z980,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z981])],[(0,[z1,z2,z7,z4,z982,z6]),(0,[z1,z7,z4,z14,z73,z310]),(0,[z1,z20,z410,z7,z4,z5])],[(0,[z1,z9,z7,z155,z5,z6]),(0,[z1,z2,z7,z4,z38,z499])],[(0,[z214,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z983]),(0,[z1,z37,z2,z7,z5,z285])],[(0,[z1,z2,z7,z4,z202,z73]),(0,[z1,z2,z7,z4,z803,z242]),(0,[z1,z2,z984,z7,z4,z5])],[(0,[z1,z2,z7,z4,z14,z443]),(0,[z1,z2,z7,z4,z985,z5]),(0,[z1,z2,z7,z4,z738,z67])],[(0,[z1,z2,z7,z4,z171,z73]),(0,[z1,z2,z7,z4,z137,z419])],[(0,[z1,z7,z4,z5,z986,z6]),(0,[z1,z2,z7,z4,z5,z987])],[(0,[z1,z7,z4,z14,z10,z424]),(0,[z1,z2,z7,z4,z14,z424])],[(0,[z1,z9,z7,z4,z12,z6]),(0,[z1,z341,z7,z4,z38,z5]),(0,[z1,z170,z7,z828,z5,z6]),(0,[z1,z2,z7,z988,z4,z5]),(0,[z15,z1,z2,z47,z4,z42])],[(0,[z1,z2,z7,z4,z989,z5]),(0,[z1,z2,z7,z4,z990,z5]),(0,[z1,z2,z7,z4,z5,z991]),(0,[z1,z2,z810,z7,z4,z5])],[(0,[z1,z2,z7,z992,z5,z6]),(0,[z993,z2,z7,z4,z5,z6]),(0,[z1,z115,z369,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z994])],[(0,[z1,z2,z7,z47,z4,z202]),(0,[z1,z9,z7,z4,z14,z32])],[(0,[z1,z2,z7,z427,z5,z10]),(0,[z1,z7,z4,z39,z14,z6]),(0,[z540,z2,z84,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z995])],[(0,[z1,z2,z7,z4,z996,z6]),(0,[z997,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z242,z854]),(0,[z1,z9,z7,z4,z5,z998]),(0,[z999,z2,z7,z4,z5,z6])],[(0,[z91,z37,z2,z13,z4,z5]),(0,[z634,z2,z7,z4,z5,z32]),(0,[z1,z2,z978,z80,z5,z6])],[(0,[z17,z2,z7,z4,z38,z111]),(0,[z1,z1000,z2,z7,z4,z5]),(1,[z1,z7,z4,z14,z55]),(0,[z1,z343,z7,z4,z14,z6]),(0,[z36,z1,z537,z80,z5,z6])],[(0,[z1,z2,z7,z4,z1001,z6]),(0,[z1,z7,z4,z393,z5,z79])],[(0,[z1,z7,z4,z54,z14,z73]),(0,[z107,z1,z2,z7,z219,z5]),(0,[z1,z2,z7,z289,z213,z6])],[(0,[z1,z152,z7,z4,z39,z6]),(0,[z1,z1002,z7,z4,z5,z6]),(0,[z1,z7,z4,z1003,z5,z14]),(0,[z397,z2,z7,z47,z4,z5]),(0,[z1004,z2,z7,z47,z4,z5])],[(0,[z1,z2,z7,z1005,z5,z6]),(0,[z1,z2,z7,z4,z125,z73]),(0,[z1,z2,z7,z298,z5,z234])],[(0,[z1,z2,z1006,z7,z4,z5]),(0,[z1,z2,z7,z4,z464,z10]),(0,[z1,z1007,z7,z4,z5,z6])],[(0,[z1,z1008,z2,z7,z4,z5])],[],[(0,[z1,z1009,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1010]),(0,[z1,z7,z4,z14,z32,z73]),(0,[z1,z37,z2,z7,z371,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z1011]),(0,[z1,z2,z130,z4,z173,z5]),(0,[z1,z524,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z499,z73])],[(0,[z1,z2,z7,z4,z5,z806]),(0,[z1,z9,z7,z4,z532,z6])],[(0,[z1,z1012,z2,z7,z4,z5]),(0,[z1,z268,z7,z4,z14,z10]),(0,[z1,z7,z4,z5,z312,z79]),(0,[z1,z1013,z2,z7,z4,z5])],[(0,[z1,z2,z7,z427,z38,z5]),(0,[z1,z2,z7,z134,z5,z419]),(0,[z1,z7,z4,z54,z14,z147]),(0,[z1,z2,z7,z4,z180,z73]),(0,[z1,z2,z7,z4,z5,z1014]),(0,[z1,z9,z7,z4,z5,z100]),(0,[z36,z1,z2,z38,z80,z5])],[(0,[z1,z2,z183,z4,z5,z10]),(0,[z1,z37,z7,z5,z14,z285]),(0,[z1,z414,z7,z4,z14,z73])],[(0,[z1,z2,z7,z212,z146,z5]),(0,[z903,z2,z7,z4,z5,z6]),(0,[z1,z309,z7,z4,z5,z10])],[(0,[z1,z9,z7,z304,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1015]),(0,[z1,z2,z938,z4,z5,z6]),(0,[z1,z7,z4,z5,z1016,z6])],[(0,[z1,z2,z7,z1017,z5,z6])],[(0,[z2,z7,z13,z4,z39,z6])],[(0,[z1,z2,z705,z4,z5,z32]),(0,[z263,z174,z2,z7,z146,z5])],[(0,[z1,z2,z7,z4,z5,z1018]),(0,[z1,z2,z7,z47,z4,z969])],[(0,[z1,z2,z1019,z4,z5,z6]),(0,[z1,z50,z7,z4,z171,z6]),(0,[z1,z2,z7,z4,z1020,z5])],[(0,[z1,z2,z7,z1021,z4,z5]),(0,[z1,z2,z7,z4,z202,z10]),(0,[z1,z343,z7,z4,z213,z6]),(0,[z1,z222,z7,z4,z264,z5])],[(0,[z1,z2,z183,z253,z5,z6]),(0,[z15,z1,z37,z2,z4,z42])],[(0,[z1,z2,z380,z4,z38,z5]),(0,[z1,z2,z7,z4,z171,z10]),(0,[z157,z1,z7,z4,z14,z73]),(0,[z1,z37,z9,z7,z4,z14]),(0,[z1,z2,z7,z4,z14,z76]),(0,[z1,z2,z7,z1022,z5,z6])],[(0,[z1,z37,z7,z4,z54,z14]),(0,[z1,z2,z7,z4,z412,z1023]),(0,[z1,z2,z7,z4,z5,z1024])],[(0,[z267,z2,z7,z146,z5,z6]),(0,[z1,z7,z4,z294,z14,z6]),(0,[z1,z2,z7,z4,z5,z1025]),(0,[z1,z1026,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z351,z5])],[(0,[z1,z2,z7,z1027,z5,z6]),(0,[z1,z2,z7,z4,z31,z464]),(0,[z16,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1028,z5]),(0,[z1,z7,z534,z5,z272,z6]),(0,[z1,z7,z178,z4,z14,z6])],[(0,[z1,z2,z303,z4,z5,z6]),(0,[z40,z497,z2,z7,z4,z5]),(0,[z1,z2,z512,z4,z5,z32]),(0,[z1,z2,z7,z369,z85,z6])],[(0,[z1,z2,z7,z4,z5,z1029]),(0,[z1,z7,z4,z5,z14,z419]),(0,[z1030,z2,z7,z4,z5,z6]),(0,[z1,z614,z7,z4,z5,z73])],[(0,[z1,z2,z7,z427,z5,z192]),(0,[z1,z37,z152,z7,z4,z5]),(0,[z1,z2,z7,z47,z4,z213]),(0,[z36,z1,z417,z2,z80,z5]),(0,[z1,z2,z7,z874,z5,z6]),(0,[z1,z37,z7,z4,z5,z104]),(0,[z1,z1031,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1032,z6]),(0,[z1,z1033,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1034]),(0,[z1,z30,z7,z4,z14,z32]),(0,[z1,z7,z4,z1035,z5,z6]),(0,[z1,z2,z7,z4,z5,z1036]),(0,[z1,z66,z7,z4,z5,z32]),(0,[z1,z2,z7,z1037,z4,z5])],[(0,[z1,z34,z7,z4,z14,z73]),(0,[z1,z2,z7,z212,z4,z5]),(0,[z1,z37,z2,z7,z153,z51])],[(0,[z1,z2,z7,z4,z5,z1038]),(0,[z1,z2,z7,z4,z1003,z5])],[(0,[z1,z2,z7,z1039,z4,z5]),(0,[z1,z7,z4,z54,z14,z10]),(0,[z1,z2,z7,z4,z5,z1040]),(0,[z1,z1041,z2,z7,z4,z5])],[(0,[z1,z1042,z2,z7,z146,z5]),(0,[z238,z1,z37,z7,z4,z14]),(0,[z1,z2,z7,z4,z65,z829])],[(0,[z1,z2,z7,z4,z1043,z6]),(0,[z1,z7,z4,z14,z562,z6]),(0,[z1,z222,z7,z4,z5,z32])],[(0,[z1,z2,z7,z4,z5,z1044]),(0,[z1,z1045,z7,z4,z5,z6]),(0,[z1,z174,z2,z7,z4,z5])],[(0,[z1,z9,z7,z4,z19,z6]),(0,[z1,z2,z7,z908,z5,z10])]],
   [[(0,[z1,z9,z7,z4,z5,z353])],[(0,[z1,z2,z21,z47,z141,z5]),(0,[z1,z2,z7,z886,z38,z5])],[(0,[z1,z9,z7,z4,z5,z296]),(0,[z1046,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z137,z14,z6]),(0,[z1,z2,z7,z4,z499,z10])],[(0,[z1,z255,z2,z21,z141,z5])],[(0,[z1,z9,z7,z4,z39,z6]),(0,[z1,z343,z7,z4,z5,z344])],[(0,[z24,z152,z7,z4,z5,z6]),(0,[z1,z7,z4,z324,z14,z6]),(0,[z1,z2,z7,z4,z1047,z5]),(0,[z1,z2,z21,z212,z141,z5])],[(0,[z1,z2,z7,z4,z5,z1048]),(0,[z372,z2,z7,z4,z5,z507]),(0,[z1,z2,z7,z4,z38,z738])],[(0,[z434,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1049,z6]),(0,[z1,z2,z7,z47,z4,z1050])],[(0,[z1,z2,z308,z4,z137,z32])],[(0,[z1,z2,z7,z4,z5,z1051]),(0,[z1,z7,z47,z4,z5,z1052])],[(0,[z1,z30,z7,z4,z14,z73]),(0,[z1,z66,z7,z4,z5,z73]),(0,[z455,z1,z2,z288,z4,z5])],[(0,[z1,z1053,z2,z7,z4,z5]),(0,[z1,z1054,z2,z7,z4,z5]),(0,[z1,z1055,z7,z4,z5,z6]),(0,[z1,z506,z2,z7,z288,z4]),(0,[z157,z1,z138,z7,z85,z6])],[(0,[z1,z2,z7,z4,z5,z1056]),(0,[z1,z2,z7,z4,z546,z73])],[(0,[z189,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z1057,z5])],[(0,[z331,z1,z7,z4,z5,z79]),(0,[z16,z2,z7,z4,z5,z73]),(0,[z1,z2,z7,z1058,z5,z32])],[(0,[z1,z2,z7,z4,z202,z192]),(0,[z1,z9,z369,z4,z5,z6])],[(0,[z1,z1042,z2,z7,z4,z5])],[(0,[z1,z7,z4,z5,z14,z446]),(0,[z157,z1,z7,z4,z14,z10])],[(0,[z1,z2,z186,z7,z4,z5]),(0,[z1,z2,z7,z1059,z4,z5])],[(0,[z91,z2,z13,z304,z5,z6]),(0,[z17,z2,z7,z4,z111,z10])],[(0,[z1,z1060,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1061]),(0,[z1,z2,z7,z4,z65,z6])],[],[(0,[z1,z7,z47,z4,z14,z42])],[(0,[z1,z1062,z2,z7,z4,z5]),(0,[z1,z7,z47,z4,z5,z248]),(0,[z1,z614,z7,z4,z5,z10])],[],[(0,[z1,z2,z7,z4,z5,z1063]),(0,[z1,z2,z7,z1064,z4,z5]),(0,[z634,z2,z7,z4,z38,z5]),(0,[z1,z1065,z2,z7,z4,z5]),(0,[z1,z1066,z2,z7,z4,z5]),(0,[z15,z1,z2,z4,z42,z32]),(0,[z157,z1,z2,z7,z38,z85]),(0,[z1,z7,z4,z38,z5,z450])],[(0,[z1,z2,z7,z4,z5,z1067]),(0,[z540,z2,z7,z307,z5,z6])],[(0,[z107,z1,z7,z4,z223,z5]),(0,[z1,z37,z1068,z7,z4,z5])],[],[(0,[z17,z2,z7,z253,z111,z6]),(0,[z1,z7,z4,z14,z42,z32])],[],[(0,[z1,z2,z1069,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1070]),(0,[z1,z1071,z2,z7,z4,z5]),(0,[z1,z37,z2,z7,z4,z171])]],
   [[(0,[z1,z2,z7,z47,z4,z412]),(0,[z1,z7,z4,z80,z14,z73]),(0,[z1,z9,z7,z162,z5,z6]),(0,[z1,z2,z7,z4,z5,z739])],[(0,[z1,z2,z7,z4,z5,z1072]),(0,[z1,z2,z7,z4,z5,z822])],[(0,[z1,z2,z7,z167,z5,z296]),(0,[z1,z2,z7,z1073,z5,z6])],[(0,[z1,z2,z303,z4,z5,z1074]),(0,[z1,z7,z4,z5,z1075,z6])],[(0,[z1,z2,z7,z47,z283,z5]),(0,[z1,z9,z4,z5,z10,z32]),(0,[z1,z2,z7,z4,z738,z5])],[(0,[z1,z2,z7,z394,z137,z6])],[(0,[z1,z7,z95,z4,z14,z73]),(0,[z1076,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1077]),(0,[z1,z614,z7,z4,z38,z5])],[(0,[z1,z37,z2,z7,z662,z5])],[(0,[z1,z2,z7,z976,z5,z6]),(0,[z1,z2,z7,z4,z1078,z6]),(0,[z1,z2,z117,z7,z4,z5]),(0,[z536,z2,z7,z4,z5,z350])],[],[(0,[z1,z1079,z7,z4,z5,z6]),(0,[z397,z2,z7,z4,z132,z6]),(0,[z536,z355,z7,z4,z5,z6]),(0,[z1,z2,z7,z194,z4,z5])],[(0,[z1,z740,z2,z7,z167,z5]),(0,[z1,z1080,z7,z4,z5,z6]),(0,[z1,z392,z7,z4,z5,z10]),(0,[z1,z2,z7,z253,z5,z32]),(0,[z1,z2,z7,z4,z5,z1081]),(0,[z1,z2,z7,z4,z38,z650]),(0,[z1082,z2,z7,z4,z5,z6]),(0,[z1,z37,z2,z1083,z4,z5])],[(0,[z1,z2,z7,z4,z5,z116]),(0,[z1,z2,z7,z4,z5,z1084]),(0,[z1,z2,z7,z4,z137,z424]),(0,[z1,z2,z339,z4,z5,z10])],[(0,[z1,z2,z7,z4,z5,z126]),(0,[z1,z7,z4,z38,z14,z42]),(0,[z1085,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z448,z5])],[(0,[z1,z7,z4,z38,z5,z248]),(0,[z1,z2,z7,z1086,z4,z5]),(0,[z1,z7,z4,z5,z1087,z6])],[(0,[z91,z2,z13,z4,z5,z296]),(0,[z1,z2,z7,z4,z5,z1088]),(0,[z1,z2,z7,z4,z499,z1089]),(0,[z1,z1090,z2,z7,z4,z5]),(0,[z1,z2,z7,z1091,z4,z5])],[(0,[z1,z37,z87,z7,z4,z5]),(0,[z1,z170,z7,z47,z95,z5]),(0,[z1,z7,z4,z254,z14,z73]),(0,[z1,z2,z21,z141,z5,z6]),(0,[z16,z2,z7,z4,z5,z10])],[(0,[z1,z2,z7,z1092,z5,z6]),(0,[z1,z7,z4,z5,z14,z363]),(0,[z1,z1093,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1094])],[(0,[z1,z2,z7,z4,z1095,z5]),(0,[z1,z7,z4,z5,z14,z780])],[(0,[z1,z7,z4,z5,z1096,z6]),(0,[z1,z7,z4,z5,z1097,z6]),(0,[z1,z2,z7,z4,z206,z310])],[(0,[z1,z311,z7,z4,z14,z6]),(0,[z526,z1,z2,z7,z47,z5])],[(0,[z1,z392,z7,z253,z5,z6]),(0,[z1,z37,z2,z7,z4,z242]),(0,[z1,z2,z7,z4,z99,z73])],[(0,[z2,z7,z47,z134,z146,z5]),(0,[z1,z7,z4,z14,z554,z6])],[(0,[z1,z7,z134,z4,z14,z73]),(0,[z1,z2,z7,z4,z5,z1098]),(0,[z176,z1,z7,z4,z5,z231])],[(0,[z33,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z998]),(0,[z1,z2,z1099,z4,z5,z6]),(0,[z1,z1100,z7,z4,z5,z6]),(0,[z1,z524,z7,z4,z5,z73])],[(0,[z24,z2,z469,z4,z5,z6]),(0,[z1,z2,z7,z888,z5,z6]),(0,[z1,z2,z7,z47,z5,z593])],[(0,[z1,z138,z7,z4,z5,z158])],[(0,[z1,z2,z7,z4,z156,z32]),(0,[z1,z9,z7,z4,z5,z419]),(0,[z1,z66,z7,z4,z38,z5])],[(0,[z1,z152,z7,z4,z5,z466]),(0,[z1,z514,z7,z95,z5,z6]),(0,[z157,z1,z7,z4,z38,z14]),(0,[z1,z2,z4,z5,z76,z310]),(0,[z1,z2,z256,z4,z5,z158]),(1,[z1,z2,z7,z5,z739])],[(0,[z1,z9,z7,z47,z4,z14]),(0,[z1,z2,z256,z4,z5,z1101])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z1102,z7,z4,z5]),(0,[z1,z9,z7,z270,z5,z6]),(0,[z1,z625,z4,z5,z191,z6]),(0,[z106,z187,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z22]),(0,[z1,z2,z7,z4,z5,z1103]),(0,[z1,z37,z222,z7,z4,z5]),(0,[z1046,z37,z2,z7,z4,z5])],[(0,[z16,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z162,z5,z363]),(0,[z434,z2,z7,z4,z5,z158])]],
   [[(0,[z1,z2,z7,z47,z4,z312]),(0,[z1,z222,z7,z4,z38,z5])],[(0,[z1,z2,z7,z4,z44,z77]),(0,[z1,z7,z4,z403,z14,z6]),(0,[z1,z2,z7,z4,z5,z1104])],[(0,[z24,z2,z25,z4,z5,z400]),(0,[z1,z2,z7,z4,z1105,z5]),(0,[z1,z112,z7,z4,z14,z6])],[(0,[z1,z2,z7,z4,z1106,z6]),(0,[z634,z2,z7,z4,z65,z6])],[(0,[z1107,z2,z7,z47,z4,z5])],[(0,[z540,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z1108,z4,z5]),(0,[z488,z1,z2,z80,z5,z6])],[(0,[z1,z2,z7,z4,z5,z100]),(0,[z1,z2,z7,z4,z5,z1109])],[(0,[z1,z2,z7,z4,z499,z350]),(0,[z1,z2,z4,z978,z5,z6])],[(0,[z1,z7,z4,z137,z14,z32]),(0,[z1,z2,z7,z47,z571,z5])],[(0,[z1,z2,z7,z304,z5,z6]),(0,[z1,z2,z7,z4,z5,z1110]),(0,[z1,z355,z7,z4,z499,z6])],[(0,[z1,z2,z1111,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1112]),(0,[z92,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z307,z5,z6]),(0,[z1,z2,z7,z4,z5,z1113]),(0,[z1,z1114,z2,z7,z4,z5])],[(0,[z1,z9,z7,z18,z5,z6]),(0,[z1,z7,z178,z4,z14,z73]),(0,[z176,z1,z7,z4,z5,z79])],[(0,[z1,z2,z3,z47,z4,z5]),(0,[z1,z2,z303,z4,z5,z73]),(0,[z1,z1115,z2,z7,z4,z5]),(0,[z1,z2,z7,z1116,z5,z6]),(0,[z1,z164,z7,z4,z5,z273]),(0,[z1,z479,z2,z7,z141,z5]),(0,[z1,z7,z4,z204,z42,z6]),(0,[z1,z2,z7,z4,z5,z1117])],[(0,[z1,z1118,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1119,z5]),(0,[z556,z2,z7,z162,z5,z6])],[(0,[z1,z2,z7,z1120,z307,z5]),(0,[z1,z9,z7,z47,z547,z5]),(0,[z1,z2,z7,z874,z5,z73])],[(0,[z1,z2,z7,z4,z5,z1121]),(0,[z1,z2,z7,z47,z5,z660]),(0,[z1,z311,z7,z103,z5,z6]),(0,[z1,z37,z1122,z7,z4,z5])],[(0,[z540,z129,z7,z4,z5,z6]),(0,[z1,z37,z2,z7,z162,z5]),(0,[z157,z1,z2,z7,z298,z5]),(0,[z157,z434,z2,z7,z85,z6])],[(0,[z1,z2,z7,z4,z5,z1123]),(0,[z1124,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1125,z5])],[(0,[z519,z34,z7,z4,z5,z6]),(0,[z1,z9,z7,z288,z4,z5])],[(0,[z189,z9,z7,z4,z5,z6]),(0,[z1,z115,z7,z4,z5,z158])],[(0,[z1,z87,z7,z304,z5,z6]),(0,[z366,z2,z7,z146,z5,z6])],[(0,[z48,z1,z130,z47,z4,z5]),(0,[z1,z537,z7,z4,z5,z350])],[(0,[z1,z2,z7,z47,z155,z5]),(0,[z1,z2,z7,z47,z676,z5]),(0,[z1,z2,z7,z4,z5,z1126])],[(0,[z1,z2,z7,z912,z253,z5]),(0,[z1,z2,z7,z4,z5,z1127]),(0,[z1,z30,z7,z4,z38,z14]),(0,[z1,z9,z7,z4,z5,z446]),(0,[z36,z1,z355,z80,z5,z6]),(0,[z1,z2,z7,z4,z5,z1128]),(0,[z1,z309,z7,z4,z137,z6]),(0,[z1,z1129,z7,z47,z4,z5]),(0,[z1,z7,z4,z5,z1052,z6])],[(0,[z1,z2,z7,z4,z1130,z6]),(0,[z1,z2,z7,z1131,z4,z5]),(0,[z1,z2,z7,z4,z5,z1132]),(0,[z1,z1133,z7,z4,z5,z6]),(0,[z1,z97,z30,z7,z4,z38])],[(0,[z1,z2,z7,z4,z5,z1134]),(0,[z1,z2,z1135,z4,z5,z6]),(0,[z1,z2,z7,z4,z132,z55])],[(0,[z1,z2,z380,z4,z5,z1136]),(0,[z1,z2,z4,z5,z572,z32]),(0,[z1,z524,z7,z4,z5,z10])],[(0,[z91,z13,z4,z5,z14,z6]),(0,[z165,z1,z7,z4,z14,z73]),(0,[z397,z2,z7,z4,z14,z6]),(0,[z1,z1137,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1138,z6]),(0,[z1,z2,z7,z4,z1139,z6]),(0,[z1,z7,z4,z1140,z14,z6]),(0,[z1,z9,z7,z4,z5,z1141]),(0,[z1142,z2,z7,z4,z5,z6]),(0,[z1,z228,z2,z7,z4,z326])],[(0,[z1,z2,z7,z4,z5,z1143]),(0,[z1,z7,z153,z51,z14,z6]),(0,[z1,z37,z2,z1144,z4,z5])],[(0,[z1,z2,z7,z4,z1145,z6])],[(0,[z2,z847,z13,z4,z5,z6]),(0,[z1,z2,z7,z1146,z5,z6]),(0,[z1,z2,z140,z4,z5,z32]),(0,[z1,z256,z4,z5,z14,z6])]],
   [[(0,[z1,z2,z7,z1147,z5,z6]),(0,[z1,z7,z4,z5,z971,z6]),(0,[z2,z7,z1148,z146,z5,z6]),(0,[z1,z1149,z7,z4,z5,z6]),(0,[z1,z1150,z2,z7,z4,z5])],[(1,[z34,z3,z4,z5,z6]),(0,[z1,z2,z7,z1151,z4,z5]),(0,[z1,z2,z7,z4,z1152,z5])],[(0,[z1,z2,z7,z4,z242,z6])],[(0,[z1,z2,z7,z1153,z5,z6]),(0,[z1,z2,z847,z4,z5,z6]),(0,[z62,z1,z4,z14,z42,z6]),(0,[z1,z2,z7,z1154,z4,z5])],[(0,[z1,z1155,z2,z7,z4,z5]),(0,[z1,z2,z4,z5,z390,z10])],[(0,[z1,z2,z7,z4,z5,z1156])],[(0,[z1,z9,z7,z4,z5,z466]),(0,[z1157,z1,z9,z7,z4,z5])],[(0,[z1,z2,z3,z4,z44,z6]),(0,[z1,z2,z7,z4,z39,z6]),(0,[z15,z16,z2,z4,z42,z6])],[(0,[z157,z1,z2,z7,z100,z85])],[(0,[z1,z2,z7,z4,z1158,z6]),(0,[z1,z2,z369,z4,z85,z6]),(0,[z1,z524,z7,z4,z38,z5])],[],[(0,[z322,z1,z130,z4,z5,z6]),(0,[z1,z97,z7,z4,z464,z6]),(0,[z1,z255,z2,z7,z4,z5]),(0,[z1,z2,z308,z394,z5,z6]),(1,[z1,z2,z394,z42,z6])],[(0,[z1,z2,z7,z4,z5,z1159]),(0,[z1,z2,z7,z4,z38,z171]),(0,[z1,z2,z7,z80,z499,z6]),(0,[z1,z2,z7,z4,z65,z73])],[(0,[z1,z2,z7,z4,z5,z1160]),(0,[z1,z435,z2,z159,z7,z5])],[(0,[z1,z2,z303,z4,z5,z10]),(0,[z1,z7,z451,z4,z14,z6]),(0,[z699,z1,z2,z7,z85,z6])],[(0,[z1,z2,z3,z4,z5,z77]),(0,[z263,z2,z7,z146,z5,z6]),(0,[z1,z2,z7,z4,z31,z5]),(0,[z1,z2,z7,z47,z4,z65]),(0,[z1,z1161,z7,z4,z5,z6]),(0,[z1,z2,z553,z4,z145,z5])],[],[(0,[z1,z9,z7,z4,z773,z6])],[(0,[z1,z2,z7,z155,z5,z32]),(0,[z1,z87,z7,z4,z39,z6]),(0,[z1,z2,z7,z4,z5,z1162]),(0,[z1,z2,z4,z5,z404,z10]),(0,[z1163,z2,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z1164,z44]),(0,[z1,z341,z7,z4,z111,z6]),(0,[z1,z9,z7,z1165,z5,z6]),(0,[z1,z2,z7,z4,z1166,z5])],[(0,[z442,z2,z7,z4,z5,z98])],[(0,[z1,z2,z7,z1167,z4,z5]),(0,[z1,z2,z7,z4,z5,z1168]),(0,[z1,z2,z7,z4,z5,z326])],[(0,[z1,z9,z7,z1169,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1170]),(0,[z7,z13,z4,z111,z14,z6]),(0,[z1,z9,z7,z4,z5,z363]),(0,[z1,z2,z7,z4,z5,z1171])],[(0,[z1,z9,z7,z167,z5,z6]),(0,[z1,z2,z7,z1172,z4,z5]),(0,[z1,z369,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z1173,z5])],[(0,[z1,z2,z7,z1174,z5,z6]),(0,[z1,z678,z7,z4,z14,z6]),(0,[z1,z2,z7,z1175,z5,z6]),(0,[z1,z7,z141,z4,z14,z73]),(0,[z1,z1176,z2,z7,z4,z5])],[(0,[z1,z7,z4,z5,z113,z708]),(0,[z1,z2,z7,z4,z5,z1177])],[(0,[z0,z34,z7,z427,z5,z6])],[(0,[z1,z2,z1178,z4,z5,z6]),(0,[z1,z863,z4,z5,z14,z6])],[(0,[z1,z2,z303,z4,z38,z5]),(0,[z1,z2,z7,z1179,z5,z6]),(0,[z1,z2,z7,z1180,z4,z5]),(0,[z16,z2,z4,z5,z42,z6]),(0,[z1,z2,z7,z4,z38,z424]),(0,[z1,z1161,z7,z47,z4,z5])],[(0,[z1,z1181,z2,z7,z253,z5]),(0,[z1,z20,z2,z7,z219,z5]),(0,[z1,z2,z4,z145,z5,z42])],[(0,[z1,z440,z7,z4,z44,z6])]],
   [[(0,[z522,z2,z13,z4,z5,z6])],[(0,[z48,z1,z334,z4,z5,z6]),(0,[z1,z9,z203,z4,z5,z32]),(0,[z1,z435,z2,z7,z5,z85])],[(0,[z1,z2,z7,z4,z38,z242]),(0,[z1,z1182,z2,z7,z4,z5]),(0,[z1,z9,z7,z4,z5,z792])],[(0,[z1,z2,z7,z4,z5,z1183]),(0,[z62,z1,z4,z5,z531,z6]),(0,[z1,z2,z7,z162,z5,z6]),(0,[z1,z2,z7,z4,z5,z1184])],[(0,[z1,z7,z155,z5,z14,z6]),(0,[z1,z50,z7,z96,z5,z32]),(0,[z157,z1,z7,z14,z85,z6]),(0,[z556,z2,z7,z4,z5,z446]),(0,[z1,z2,z7,z4,z5,z1185])],[(0,[z91,z9,z13,z4,z5,z6]),(0,[z1,z436,z7,z4,z14,z6])],[(0,[z1186,z1,z2,z7,z4,z5]),(0,[z7,z4,z54,z111,z14,z6]),(0,[z1,z2,z7,z47,z574,z5])],[],[(0,[z1,z2,z21,z141,z5,z73])],[(0,[z2,z7,z47,z146,z5,z111]),(0,[z1,z7,z4,z14,z32,z310]),(0,[z1,z2,z4,z145,z5,z10])],[(0,[z1,z2,z7,z4,z44,z10]),(0,[z1,z2,z7,z134,z211,z5]),(0,[z1,z2,z7,z4,z14,z55]),(0,[z1,z2,z7,z298,z80,z5])],[(0,[z1,z2,z1187,z4,z5,z6]),(0,[z1,z7,z712,z5,z14,z6]),(0,[z1,z228,z7,z4,z5,z14])],[(0,[z24,z2,z7,z47,z146,z5]),(0,[z1,z2,z7,z4,z213,z6]),(0,[z1,z37,z7,z4,z5,z204]),(0,[z1,z435,z2,z7,z47,z5])],[(0,[z1,z525,z7,z96,z5,z6]),(0,[z1,z2,z7,z4,z5,z1188]),(0,[z48,z1,z130,z4,z5,z126]),(0,[z1,z2,z7,z4,z1189,z5]),(0,[z1,z7,z4,z14,z700,z6]),(0,[z1,z2,z7,z178,z95,z5])],[(0,[z1,z9,z7,z289,z5,z6]),(0,[z1,z2,z1190,z4,z5,z6]),(0,[z1,z2,z7,z4,z65,z10])],[(0,[z1,z2,z7,z304,z5,z32]),(0,[z1,z7,z4,z137,z248,z6]),(0,[z1,z7,z130,z289,z5,z6]),(0,[z1,z20,z7,z4,z254,z5])],[(0,[z1,z2,z1191,z7,z4,z5]),(0,[z1,z1192,z2,z7,z4,z5]),(0,[z1,z129,z607,z4,z5,z6]),(0,[z1,z7,z4,z483,z14,z6]),(0,[z1,z9,z7,z4,z5,z158]),(0,[z1,z2,z7,z153,z4,z326]),(0,[z386,z2,z7,z4,z360,z5])],[(0,[z1,z2,z7,z1193,z5,z6]),(0,[z1,z1194,z2,z7,z4,z5]),(0,[z1,z7,z4,z5,z14,z891])],[(0,[z1,z7,z4,z5,z14,z184]),(0,[z1,z2,z7,z394,z5,z446]),(0,[z1,z2,z308,z4,z5,z76])],[(0,[z1,z9,z1195,z7,z4,z5]),(0,[z1,z9,z7,z394,z5,z6])],[(1,[z152,z13,z4,z5,z6]),(0,[z1,z2,z7,z1196,z5,z6]),(0,[z36,z1,z2,z4,z173,z5]),(0,[z1,z2,z7,z4,z1197,z5])],[(0,[z1,z7,z4,z14,z6,z142]),(0,[z1,z2,z7,z47,z4,z836])],[(0,[z1,z2,z3,z4,z5,z73]),(0,[z1,z2,z7,z899,z4,z5]),(0,[z1,z2,z7,z4,z1198,z6]),(0,[z1,z7,z153,z4,z14,z6]),(0,[z1,z255,z2,z194,z4,z5])],[(0,[z1199,z1,z2,z7,z4,z6]),(0,[z1,z9,z7,z190,z4,z5]),(0,[z1,z1200,z7,z4,z5,z6]),(0,[z1,z7,z212,z4,z5,z14]),(0,[z1,z7,z288,z4,z5,z14]),(0,[z1,z435,z2,z7,z5,z285])],[(0,[z1,z2,z1201,z7,z4,z5]),(0,[z1,z7,z4,z5,z14,z278])],[(0,[z15,z556,z2,z4,z42,z6])],[],[(0,[z2,z13,z4,z111,z42,z6]),(0,[z1,z2,z7,z579,z134,z5]),(0,[z1,z2,z7,z4,z412,z6])],[(0,[z1,z2,z7,z47,z4,z156]),(0,[z1,z2,z1190,z47,z4,z5])],[(0,[z1,z129,z84,z4,z5,z474]),(0,[z1,z2,z7,z4,z132,z73])],[(0,[z573,z2,z7,z146,z5,z6]),(0,[z68,z1,z2,z7,z4,z312]),(0,[z1,z7,z4,z31,z5,z14])],[(0,[z1,z2,z7,z1202,z5,z6]),(0,[z48,z1,z130,z4,z5,z73]),(0,[z1,z1203,z7,z47,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z1204,z6]),(0,[z1,z2,z7,z47,z706,z5]),(0,[z1,z1205,z7,z4,z5,z6]),(0,[z1,z1206,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1207]),(0,[z1,z2,z84,z4,z173,z5])],[(0,[z1,z7,z253,z5,z14,z6]),(0,[z1,z7,z4,z169,z5,z248]),(0,[z1,z2,z7,z4,z1208,z5])],[(0,[z1,z2,z7,z4,z5,z1209]),(0,[z1,z2,z7,z47,z219,z5]),(0,[z1,z2,z7,z307,z5,z73]),(0,[z1,z2,z80,z42,z85,z6])],[(0,[z1,z170,z7,z4,z14,z73]),(0,[z36,z536,z2,z80,z5,z6]),(0,[z1,z2,z7,z4,z5,z344]),(0,[z1,z2,z1210,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1211]),(0,[z1,z1212,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z171,z1213]),(0,[z1,z170,z7,z95,z412,z6]),(0,[z1,z435,z7,z4,z5,z14])],[(0,[z91,z2,z13,z167,z5,z6]),(0,[z1,z57,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z5,z266]),(0,[z1,z2,z7,z4,z5,z347])],[(0,[z1,z7,z4,z14,z76,z6]),(0,[z1,z2,z7,z4,z1214,z5])],[(0,[z1,z2,z7,z4,z132,z147]),(1,[z1,z7,z4,z773,z6])],[(0,[z1,z2,z7,z4,z242,z126]),(0,[z1,z2,z7,z4,z1215,z6]),(0,[z157,z1,z369,z4,z14,z6]),(0,[z36,z1,z2,z7,z178,z5])],[(0,[z1,z2,z1216,z4,z5,z6]),(0,[z1,z9,z30,z7,z4,z38]),(0,[z1217,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1218]),(0,[z1,z7,z4,z5,z14,z49]),(0,[z1,z1219,z2,z7,z4,z5]),(0,[z1,z2,z21,z141,z5,z10])],[(0,[z2,z34,z3,z4,z5,z6]),(0,[z1,z1220,z7,z4,z5,z6]),(0,[z1,z1221,z2,z7,z4,z5]),(0,[z1,z138,z7,z4,z5,z32]),(0,[z1,z1222,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z44,z192])],[(0,[z1,z2,z7,z4,z39,z32]),(0,[z1,z2,z7,z4,z5,z1223]),(0,[z1,z2,z256,z4,z5,z32])],[(0,[z1,z2,z7,z4,z1224,z5]),(0,[z1,z2,z7,z4,z1225,z6]),(0,[z1,z2,z7,z1226,z4,z5])],[(0,[z1,z246,z2,z7,z219,z5]),(0,[z1,z7,z4,z449,z14,z6]),(0,[z1,z7,z4,z312,z6,z79]),(0,[z1,z2,z7,z4,z5,z1227]),(0,[z1,z1228,z7,z4,z5,z6])],[(0,[z1,z2,z7,z47,z243,z5]),(0,[z1,z2,z7,z282,z134,z5]),(0,[z434,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z280,z73])],[(0,[z1,z7,z4,z773,z14,z6]),(0,[z1,z1229,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1230,z6]),(0,[z1,z2,z7,z394,z5,z363]),(0,[z1,z2,z501,z4,z5,z32])],[(0,[z1,z2,z7,z4,z5,z1231])],[(0,[z1,z9,z7,z427,z5,z6]),(0,[z1,z7,z4,z527,z14,z6]),(0,[z1,z1232,z2,z7,z4,z5]),(0,[z1,z1233,z7,z4,z5,z6])],[(0,[z1,z37,z30,z7,z4,z14]),(0,[z1,z9,z857,z4,z5,z6]),(0,[z1,z2,z7,z1234,z5,z6]),(0,[z1,z2,z7,z288,z4,z5])],[(0,[z1235,z9,z7,z4,z5,z6]),(0,[z1,z1236,z7,z4,z5,z6]),(0,[z1,z355,z7,z47,z4,z5])],[(0,[z1,z2,z1237,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1238]),(0,[z1,z2,z183,z18,z5,z6]),(0,[z1,z9,z1239,z7,z4,z5])],[(0,[z1,z2,z3,z4,z5,z10]),(0,[z322,z2,z13,z4,z5,z6]),(0,[z1,z2,z369,z4,z5,z32])],[(0,[z589,z1,z2,z4,z42,z6]),(0,[z1,z2,z21,z141,z38,z5]),(0,[z1,z2,z7,z1240,z4,z5]),(0,[z1,z2,z7,z153,z4,z419])],[(0,[z1,z2,z7,z1241,z5,z6]),(0,[z1,z550,z7,z4,z5,z113]),(0,[z1,z2,z7,z4,z242,z73]),(0,[z1,z9,z7,z4,z5,z76]),(0,[z1,z2,z7,z1242,z4,z5]),(0,[z1,z2,z7,z4,z1243,z65])],[(0,[z1,z13,z4,z14,z42,z6]),(0,[z1,z308,z7,z4,z14,z73]),(0,[z1,z7,z4,z5,z14,z32])],[(0,[z1,z7,z4,z5,z1244,z6]),(0,[z1,z7,z4,z5,z104,z6]),(0,[z1,z9,z7,z4,z464,z6])],[(0,[z1,z2,z7,z4,z1245,z6]),(0,[z1,z7,z4,z156,z1096,z6]),(0,[z699,z1,z7,z4,z14,z6]),(0,[z1,z2,z7,z1246,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1247]),(0,[z1,z2,z7,z4,z5,z1248]),(0,[z1,z2,z7,z1249,z4,z5]),(0,[z1,z2,z7,z178,z96,z5]),(0,[z1,z9,z7,z47,z4,z132])],[(0,[z1,z2,z303,z155,z5,z6]),(0,[z1,z2,z7,z4,z5,z1141]),(0,[z1,z2,z7,z4,z5,z1250]),(0,[z1,z1122,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1251]),(0,[z1,z614,z7,z162,z5,z6]),(0,[z1,z37,z2,z256,z4,z5])]],
   [[(0,[z92,z2,z7,z4,z38,z54]),(0,[z1,z7,z4,z51,z14,z73])],[(0,[z1,z2,z7,z4,z1252,z5]),(0,[z2,z7,z146,z5,z546,z6]),(0,[z540,z2,z7,z289,z5,z6]),(0,[z48,z1,z130,z4,z5,z10]),(0,[z1,z7,z95,z5,z272,z6]),(0,[z36,z1,z2,z194,z4,z5])],[(0,[z48,z1,z130,z4,z242,z6])],[(0,[z1,z2,z7,z4,z1253,z5]),(0,[z1,z2,z7,z1254,z5,z6]),(0,[z1,z37,z7,z4,z137,z14]),(0,[z954,z7,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z67,z424])],[(0,[z1,z9,z183,z4,z5,z6]),(0,[z1,z2,z7,z307,z5,z10]),(0,[z1,z170,z7,z555,z5,z6])],[(0,[z1,z1155,z2,z7,z155,z5]),(0,[z1,z2,z13,z4,z173,z5]),(0,[z1,z2,z7,z47,z253,z5]),(0,[z1,z7,z4,z544,z14,z6]),(0,[z1,z2,z21,z4,z499,z6])],[(0,[z107,z1,z416,z7,z4,z5]),(0,[z1,z2,z7,z4,z233,z73])],[(0,[z1,z2,z3,z4,z38,z5]),(0,[z24,z2,z320,z4,z5,z6]),(0,[z263,z2,z7,z146,z5,z73]),(0,[z1,z50,z7,z96,z38,z5]),(0,[z1,z2,z7,z4,z1255,z5]),(0,[z1,z37,z614,z7,z4,z5]),(0,[z1,z2,z7,z4,z280,z42]),(0,[z1,z1256,z7,z4,z5,z6])],[(0,[z0,z34,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z1257]),(0,[z1,z2,z7,z1258,z4,z5]),(0,[z1,z2,z7,z4,z5,z1259]),(0,[z1,z1260,z7,z4,z5,z6]),(0,[z1,z7,z547,z4,z14,z6]),(0,[z1,z1239,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z466]),(0,[z1,z2,z7,z162,z5,z32])],[(0,[z1,z37,z2,z7,z167,z5]),(0,[z16,z7,z4,z5,z14,z6]),(0,[z1,z7,z4,z499,z1261,z6])],[(0,[z1,z2,z7,z4,z1262,z6])],[(0,[z24,z2,z25,z4,z5,z6]),(0,[z1,z2,z183,z4,z5,z240]),(0,[z1,z2,z308,z4,z542,z137]),(0,[z1,z2,z1263,z47,z4,z5]),(0,[z1,z37,z2,z7,z5,z29])],[(0,[z1,z9,z7,z4,z202,z6]),(0,[z1,z2,z380,z4,z5,z1259]),(0,[z1,z435,z2,z7,z153,z5])],[(0,[z1,z2,z7,z4,z1264,z6]),(0,[z1,z2,z7,z4,z14,z73])],[(0,[z2,z13,z4,z5,z39,z6]),(0,[z1,z37,z2,z7,z636,z5]),(0,[z1,z2,z7,z4,z1119,z171]),(0,[z1,z9,z7,z4,z171,z6])],[(0,[z1,z2,z7,z1265,z5,z6]),(0,[z1,z7,z4,z169,z5,z14]),(0,[z1,z7,z130,z4,z171,z6]),(0,[z1,z2,z7,z4,z5,z1266]),(0,[z1,z2,z7,z4,z5,z1267]),(0,[z1,z2,z7,z4,z711,z6]),(0,[z397,z138,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z966]),(0,[z1,z2,z7,z4,z5,z1268])],[(0,[z1,z2,z7,z304,z38,z5]),(0,[z1,z2,z7,z1269,z5,z6]),(0,[z1,z2,z7,z4,z213,z126]),(0,[z1,z2,z7,z178,z4,z14]),(0,[z397,z2,z256,z4,z5,z6])],[(0,[z1,z2,z7,z219,z5,z10]),(0,[z1,z2,z7,z307,z38,z5]),(0,[z1,z2,z7,z4,z5,z1270])],[(0,[z1,z87,z7,z4,z5,z466]),(0,[z1,z359,z7,z4,z14,z32]),(1,[z1,z369,z4,z14,z6]),(0,[z1,z9,z7,z4,z542,z5]),(0,[z1,z2,z7,z4,z5,z1271])],[(0,[z536,z537,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1272])],[(0,[z1,z2,z7,z4,z1273,z6]),(0,[z1,z2,z7,z1165,z5,z6])],[(0,[z1,z802,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z14,z147]),(0,[z1,z2,z7,z4,z5,z1274]),(0,[z1,z9,z7,z4,z5,z184]),(0,[z16,z2,z7,z162,z5,z6]),(0,[z1,z30,z7,z4,z450,z6])],[(0,[z1,z9,z7,z579,z4,z5]),(0,[z1,z2,z7,z1169,z4,z5])],[(0,[z1,z2,z3,z4,z5,z192]),(0,[z1,z186,z7,z4,z5,z14]),(0,[z1,z1071,z2,z7,z304,z5])],[],[(0,[z1,z2,z7,z146,z5,z53]),(0,[z1,z2,z7,z4,z242,z10]),(0,[z1,z7,z153,z4,z14,z32])],[],[(0,[z2,z152,z13,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z278]),(0,[z1,z30,z2,z7,z4,z31])],[(0,[z1,z2,z7,z4,z5,z1275]),(0,[z1,z2,z7,z4,z483,z73]),(0,[z634,z2,z7,z141,z5,z6]),(0,[z397,z2,z7,z4,z5,z443]),(0,[z1,z435,z2,z7,z282,z5]),(0,[z1,z2,z7,z47,z4,z926])]],
   [[(0,[z1,z2,z7,z4,z842,z5])],[(0,[z1,z7,z4,z14,z98,z73]),(0,[z1,z2,z7,z4,z5,z1276])],[(0,[z1,z9,z7,z4,z499,z6]),(0,[z1,z9,z7,z4,z211,z5])],[(0,[z1,z2,z7,z1277,z4,z5])],[(0,[z1,z2,z7,z4,z213,z73]),(0,[z1,z2,z1278,z4,z5,z6]),(0,[z1,z309,z7,z4,z5,z363])],[(0,[z1,z440,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z5,z1279]),(0,[z1,z2,z7,z47,z5,z345]),(0,[z1,z2,z7,z253,z5,z10]),(0,[z1,z7,z47,z4,z54,z14]),(0,[z1,z2,z7,z4,z1280,z5])],[(0,[z17,z2,z7,z18,z111,z6]),(0,[z1,z7,z4,z14,z6,z64])],[(0,[z1,z2,z7,z270,z5,z32]),(0,[z1,z2,z588,z141,z5,z6])],[(0,[z16,z2,z308,z4,z5,z6]),(0,[z1,z37,z2,z7,z5,z739])],[(0,[z263,z2,z7,z146,z5,z10]),(0,[z1,z2,z7,z4,z38,z215]),(0,[z397,z115,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z429]),(0,[z1,z2,z7,z4,z5,z1281]),(0,[z1,z1282,z7,z4,z5,z6]),(0,[z1,z7,z4,z577,z14,z6]),(0,[z1,z2,z7,z4,z1283,z10]),(0,[z157,z1,z105,z2,z7,z85])],[(0,[z1,z2,z7,z1021,z427,z5]),(0,[z1,z7,z4,z44,z14,z6]),(0,[z189,z2,z7,z4,z5,z49]),(0,[z1,z2,z7,z4,z5,z1284])],[(0,[z1,z1285,z7,z4,z5,z6]),(0,[z48,z1,z130,z4,z213,z6])],[(0,[z1,z2,z7,z4,z5,z1286]),(0,[z1,z2,z7,z298,z4,z5]),(0,[z81,z2,z7,z232,z4,z5])],[(0,[z1,z2,z7,z4,z1287,z6]),(0,[z1,z9,z7,z282,z4,z5]),(0,[z1,z2,z7,z4,z1288,z5])],[(0,[z1,z2,z1289,z4,z5,z6]),(0,[z1,z7,z4,z5,z6,z942]),(0,[z1,z2,z7,z219,z5,z210])],[(0,[z1,z9,z7,z4,z5,z49]),(0,[z1,z2,z7,z4,z5,z1290]),(0,[z1,z2,z7,z4,z728,z6])],[(0,[z1,z259,z7,z4,z5,z6]),(0,[z1,z2,z7,z289,z5,z6]),(0,[z1,z729,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1291]),(0,[z556,z309,z7,z4,z5,z6])],[(0,[z1,z37,z2,z7,z253,z5]),(0,[z17,z9,z7,z4,z111,z6]),(0,[z366,z1,z7,z4,z14,z6]),(0,[z1,z37,z259,z7,z4,z5]),(0,[z1,z2,z7,z4,z412,z73]),(0,[z1,z7,z4,z5,z14,z1010]),(0,[z107,z1,z7,z4,z181,z5]),(0,[z1,z2,z7,z4,z5,z158])],[(0,[z1,z2,z7,z18,z5,z32]),(0,[z1,z2,z7,z1292,z4,z5]),(0,[z1,z2,z7,z4,z5,z1101]),(0,[z1,z2,z7,z47,z4,z841])],[(0,[z1,z2,z7,z4,z38,z39]),(0,[z1,z2,z7,z4,z5,z1293]),(0,[z1,z2,z7,z4,z5,z1294]),(0,[z1,z1295,z2,z7,z4,z5])],[(0,[z1,z614,z7,z4,z5,z446]),(0,[z1,z2,z7,z4,z1296,z5])],[(0,[z46,z7,z4,z111,z14,z6]),(0,[z1,z7,z4,z5,z14,z1014])],[(0,[z263,z2,z7,z146,z38,z5]),(0,[z1,z2,z7,z4,z1297,z5]),(0,[z1,z2,z7,z874,z5,z310])],[(0,[z1,z2,z7,z4,z5,z1298]),(0,[z1,z2,z7,z4,z5,z1299]),(0,[z1,z2,z7,z4,z1297,z213]),(0,[z1,z138,z7,z47,z4,z5])],[(0,[z1,z1300,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z443])],[(0,[z17,z2,z7,z4,z111,z240]),(0,[z1,z2,z369,z4,z38,z5]),(0,[z1,z2,z256,z47,z4,z5]),(0,[z1,z1301,z7,z4,z5,z6])],[(0,[z1,z1302,z7,z4,z5,z6]),(0,[z189,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z1303,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1304]),(0,[z1,z7,z4,z1305,z5,z14]),(0,[z15,z1,z614,z4,z42,z6]),(0,[z1,z2,z7,z4,z5,z424])],[(0,[z434,z2,z7,z47,z4,z5]),(0,[z1,z97,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z1306,z6]),(0,[z1,z709,z7,z4,z5,z6]),(0,[z36,z1,z2,z80,z5,z278])]],
   [[(1,[z1,z7,z4,z14,z419]),(0,[z1,z355,z7,z4,z5,z73]),(0,[z1,z309,z7,z394,z5,z6])],[(0,[z1,z9,z7,z4,z5,z32]),(0,[z1,z37,z9,z7,z4,z5])],[(0,[z1,z1307,z7,z4,z39,z6]),(0,[z136,z2,z25,z4,z5,z6]),(0,[z1,z279,z7,z4,z5,z113]),(0,[z1,z7,z4,z5,z104,z32])],[(0,[z1,z2,z7,z4,z1305,z5]),(0,[z250,z2,z7,z146,z5,z6]),(0,[z36,z1,z2,z80,z499,z6]),(0,[z1,z748,z7,z4,z5,z32])],[(0,[z1,z2,z7,z4,z1308,z6]),(0,[z1,z529,z7,z4,z14,z6]),(0,[z1,z2,z308,z4,z137,z344]),(0,[z1,z1309,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1310])],[(0,[z1,z343,z7,z4,z5,z6]),(1,[z1,z7,z4,z14,z344]),(0,[z1,z7,z4,z5,z14,z1025])],[(0,[z1,z1311,z7,z4,z5,z6]),(0,[z46,z2,z7,z8,z5,z6]),(0,[z1,z2,z7,z4,z213,z10]),(0,[z1,z2,z7,z4,z5,z1312]),(0,[z1,z2,z308,z4,z137,z347])],[(0,[z1,z9,z7,z4,z5,z275]),(0,[z1,z2,z7,z4,z5,z1313]),(0,[z1,z884,z7,z4,z5,z6]),(0,[z751,z1,z7,z4,z5,z32])],[(0,[z1,z50,z7,z103,z5,z6]),(0,[z1,z2,z7,z1314,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1315]),(0,[z1,z2,z3,z155,z5,z6]),(0,[z176,z1,z7,z4,z223,z5])],[],[(0,[z0,z34,z7,z4,z38,z5]),(0,[z1,z686,z7,z4,z14,z6]),(0,[z1,z2,z7,z146,z173,z5]),(0,[z1,z7,z4,z280,z5,z14])],[(0,[z1,z2,z7,z4,z5,z1316]),(0,[z1,z2,z7,z1317,z5,z6]),(0,[z1,z37,z2,z7,z18,z5]),(0,[z7,z4,z111,z35,z14,z6]),(0,[z1,z2,z7,z4,z1318,z5]),(0,[z1,z2,z7,z162,z38,z5])],[(0,[z1,z341,z183,z4,z5,z6]),(0,[z2,z7,z183,z4,z111,z6]),(0,[z1,z7,z282,z4,z5,z14]),(0,[z1,z9,z961,z4,z5,z6])],[(0,[z1,z2,z7,z1319,z4,z5]),(0,[z1320,z2,z7,z4,z5,z6]),(0,[z1,z279,z7,z4,z254,z5]),(0,[z1,z37,z524,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1321,z6]),(0,[z16,z2,z7,z4,z5,z446])],[(0,[z1,z7,z289,z5,z14,z6]),(0,[z16,z9,z7,z4,z5,z6])],[(0,[z1,z2,z7,z47,z134,z5]),(0,[z1,z587,z7,z96,z5,z6])],[(0,[z1,z115,z7,z47,z4,z5])],[(0,[z46,z1,z7,z4,z14,z73]),(0,[z1,z392,z7,z4,z5,z240]),(0,[z114,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z5,z1322])],[(0,[z1,z7,z4,z14,z297,z6]),(0,[z1,z2,z7,z4,z1323,z5]),(0,[z1,z2,z21,z978,z5,z6])],[(0,[z0,z34,z303,z4,z5,z6]),(0,[z1,z2,z7,z212,z134,z5]),(0,[z1,z2,z7,z4,z5,z1324]),(0,[z1,z2,z7,z4,z412,z10]),(0,[z1,z7,z4,z132,z14,z73]),(0,[z1,z2,z7,z4,z1325,z6]),(0,[z1,z7,z4,z5,z775,z6])],[(0,[z1,z2,z7,z4,z5,z1326]),(0,[z1,z7,z4,z542,z137,z14]),(0,[z1,z2,z7,z4,z745,z6]),(0,[z1,z614,z7,z4,z5,z363])],[(0,[z1,z152,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1327]),(0,[z1,z7,z298,z4,z5,z14]),(0,[z1,z2,z7,z4,z5,z1328])],[(0,[z1,z510,z84,z4,z5,z6])],[(0,[z0,z1,z7,z4,z14,z73]),(0,[z1,z1329,z7,z4,z5,z6]),(0,[z1235,z2,z7,z4,z5,z6]),(0,[z1,z2,z533,z4,z5,z32])],[(0,[z1,z2,z7,z4,z5,z400]),(0,[z1,z2,z7,z1330,z4,z5])],[(0,[z1,z2,z7,z1331,z5,z6]),(0,[z107,z1,z7,z4,z464,z79]),(0,[z1,z2,z7,z1332,z5,z6])],[(0,[z1,z2,z7,z4,z1333,z6]),(0,[z238,z1,z2,z7,z4,z326])],[(0,[z1,z2,z7,z4,z5,z76]),(0,[z1,z2,z7,z4,z750,z6])],[(0,[z1,z2,z7,z4,z5,z1334]),(0,[z1,z2,z7,z4,z5,z474])],[(0,[z1,z2,z7,z1335,z5,z6]),(0,[z1,z2,z1336,z4,z5,z6]),(0,[z1,z2,z7,z4,z1337,z6]),(0,[z1338,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z1339,z4,z5])]],
   [[(0,[z2,z7,z13,z47,z146,z5]),(0,[z229,z2,z7,z4,z111,z6]),(0,[z1,z2,z7,z4,z1340,z6])],[(0,[z1,z2,z7,z167,z5,z32]),(0,[z1,z25,z7,z4,z14,z73]),(0,[z1,z37,z2,z7,z394,z5]),(0,[z198,z1,z7,z4,z5,z131])],[(0,[z1,z355,z7,z4,z5,z10]),(0,[z36,z1,z2,z80,z5,z32])],[(0,[z1,z129,z84,z4,z5,z6]),(0,[z1,z7,z4,z567,z14,z6]),(0,[z1,z7,z4,z168,z14,z6])],[(0,[z24,z2,z25,z4,z5,z73]),(0,[z1,z1341,z7,z4,z5,z6]),(0,[z1,z2,z7,z1342,z4,z5])],[(0,[z1,z152,z7,z47,z4,z5]),(0,[z1,z268,z7,z4,z14,z6])],[(0,[z1,z2,z7,z1343,z5,z6]),(0,[z536,z2,z7,z4,z5,z6]),(0,[z1,z1344,z7,z4,z5,z6]),(0,[z1,z2,z7,z289,z5,z49])],[(0,[z1,z2,z183,z4,z5,z6]),(0,[z1,z1345,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z269]),(1,[z16,z2,z4,z42,z6])],[(0,[z1,z2,z7,z4,z324,z73]),(0,[z1,z309,z7,z4,z5,z6]),(0,[z1,z7,z282,z153,z4,z14])],[(0,[z1,z2,z7,z427,z202,z6]),(0,[z1,z2,z7,z4,z1346,z5]),(0,[z2,z7,z4,z716,z111,z6]),(0,[z157,z1,z7,z4,z14,z158])],[(0,[z1,z2,z7,z4,z5,z1347]),(0,[z1,z2,z4,z5,z10,z236]),(0,[z1,z2,z80,z5,z499,z6])],[],[(0,[z673,z34,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1348]),(0,[z1338,z2,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1349]),(0,[z91,z2,z13,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z1350]),(0,[z1,z7,z4,z649,z14,z6]),(0,[z1,z414,z7,z4,z5,z79]),(0,[z1,z2,z7,z1165,z5,z73])],[(0,[z1,z7,z4,z14,z6,z231]),(0,[z16,z2,z7,z4,z5,z363])],[(0,[z1,z1351,z2,z7,z4,z5])],[(0,[z1,z129,z84,z47,z4,z5]),(0,[z1,z187,z7,z4,z14,z6])],[(0,[z1,z614,z7,z394,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1352])],[(0,[z1,z37,z2,z303,z4,z5]),(0,[z1,z21,z7,z4,z14,z73])],[(0,[z1,z2,z7,z4,z1353,z6]),(0,[z23,z2,z7,z146,z5,z6]),(0,[z1,z2,z647,z141,z5,z6]),(0,[z1,z7,z4,z14,z29,z73])],[(0,[z1,z2,z7,z1354,z4,z5]),(0,[z1,z1355,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z1356,z5]),(0,[z1,z2,z7,z1357,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1358]),(0,[z1,z259,z7,z4,z5,z32]),(0,[z1,z2,z7,z289,z5,z32]),(0,[z1,z2,z1359,z7,z4,z5]),(0,[z15,z1,z9,z4,z42,z6]),(0,[z1,z2,z7,z4,z542,z5])],[(0,[z1,z9,z7,z4,z31,z132])],[(0,[z1,z2,z7,z1360,z5,z6]),(0,[z1,z268,z7,z4,z14,z55])],[(0,[z1,z7,z1361,z5,z14,z6]),(0,[z1,z2,z7,z1362,z4,z5])],[(0,[z1,z9,z7,z47,z146,z5]),(0,[z1,z380,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z38,z64]),(0,[z1363,z2,z7,z4,z5,z6]),(0,[z1,z7,z153,z4,z38,z14])],[(0,[z17,z341,z7,z4,z111,z6]),(0,[z1,z9,z7,z47,z5,z71]),(0,[z1,z2,z7,z4,z5,z1364]),(0,[z1,z2,z7,z394,z5,z32]),(0,[z1,z2,z4,z5,z822,z6])],[(0,[z595,z2,z13,z4,z5,z6]),(0,[z1,z2,z7,z282,z146,z5]),(0,[z1,z2,z7,z4,z1365,z5]),(0,[z1,z2,z4,z5,z76,z32])],[(0,[z1,z7,z4,z54,z14,z6]),(0,[z1,z7,z4,z663,z14,z6])],[(0,[z1,z7,z4,z412,z14,z6]),(0,[z1,z2,z7,z4,z1366,z5]),(0,[z1,z2,z4,z5,z82,z32])]],
   [[(0,[z1,z7,z4,z5,z14,z116])],[(0,[z1,z7,z4,z5,z14,z126]),(0,[z1,z2,z7,z4,z1367,z6]),(0,[z1,z1256,z7,z4,z5,z10]),(1,[z1,z7,z4,z450,z73])],[(0,[z1,z2,z7,z4,z5,z927]),(0,[z1,z2,z7,z1368,z4,z5])],[(0,[z1,z2,z94,z4,z5,z32])],[(0,[z1,z2,z7,z4,z784,z202]),(0,[z1,z7,z4,z137,z14,z344]),(0,[z1,z2,z624,z4,z5,z10]),(0,[z1,z163,z7,z4,z5,z227])],[(0,[z1,z50,z7,z4,z14,z73]),(0,[z1,z86,z7,z4,z14,z6]),(0,[z1157,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z1369,z4,z5])],[(0,[z24,z2,z25,z4,z5,z10]),(0,[z1,z2,z7,z4,z317,z73])],[(0,[z157,z1,z7,z153,z14,z6]),(0,[z1,z2,z7,z4,z132,z310]),(0,[z1,z2,z308,z47,z4,z137]),(0,[z1,z2,z7,z1370,z5,z6])],[(0,[z1,z2,z7,z134,z5,z100]),(0,[z1,z7,z4,z5,z248,z32]),(0,[z62,z1,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1371]),(0,[z489,z1,z7,z4,z14,z6]),(0,[z1,z2,z7,z288,z4,z424]),(0,[z1,z2,z7,z4,z5,z1372]),(0,[z1,z2,z7,z4,z38,z133]),(0,[z1,z97,z7,z4,z5,z73])],[(0,[z1,z2,z7,z4,z5,z240]),(0,[z1,z2,z7,z4,z1373,z6]),(0,[z1,z138,z7,z4,z132,z6]),(0,[z1,z2,z7,z4,z5,z1374]),(0,[z1,z2,z7,z1375,z4,z5])],[(0,[z642,z2,z7,z134,z5,z6]),(0,[z1,z2,z1376,z4,z5,z6]),(0,[z1,z2,z7,z4,z393,z73])],[(0,[z1,z2,z7,z4,z1377,z5]),(0,[z1,z2,z7,z4,z1378,z5]),(0,[z1,z1379,z2,z7,z4,z5]),(0,[z16,z2,z7,z394,z5,z6]),(0,[z157,z1,z2,z7,z85,z32])],[(0,[z17,z2,z7,z4,z111,z365]),(0,[z1,z2,z7,z4,z5,z1380]),(0,[z1,z2,z7,z5,z787,z6]),(0,[z1,z7,z4,z5,z1381,z6])],[(0,[z0,z34,z7,z155,z5,z6]),(0,[z1,z2,z7,z1382,z4,z5])],[(0,[z1,z9,z303,z4,z5,z6]),(0,[z1,z1383,z2,z7,z4,z5]),(0,[z1,z97,z7,z4,z132,z6])],[(0,[z1,z2,z7,z304,z39,z6]),(0,[z1,z2,z7,z47,z289,z5]),(0,[z1,z2,z7,z4,z171,z184]),(0,[z1,z9,z7,z47,z4,z5]),(0,[z1,z37,z7,z4,z5,z1381])],[(0,[z1,z2,z7,z4,z5,z708]),(0,[z1,z37,z7,z4,z5,z450])],[(0,[z1,z152,z25,z4,z5,z6]),(0,[z1,z2,z7,z282,z4,z5])],[(0,[z1,z7,z4,z5,z14,z22]),(0,[z1,z2,z308,z4,z567,z6]),(0,[z1,z37,z309,z7,z4,z5]),(0,[z1,z37,z2,z369,z4,z5])],[(0,[z1,z37,z2,z7,z4,z44]),(0,[z1,z259,z7,z4,z5,z147]),(0,[z1,z537,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1384]),(0,[z1,z9,z7,z212,z4,z5]),(0,[z1,z2,z7,z178,z4,z132])],[(0,[z1,z2,z7,z4,z5,z1385]),(0,[z1,z7,z47,z146,z5,z14]),(0,[z1,z2,z7,z988,z394,z5]),(0,[z1,z2,z7,z1386,z4,z5]),(0,[z397,z2,z7,z5,z85,z6])],[(0,[z24,z2,z25,z4,z38,z5]),(0,[z1,z2,z7,z1387,z5,z6]),(0,[z1,z1388,z7,z4,z5,z6])],[(0,[z17,z2,z7,z4,z111,z6]),(0,[z1,z2,z369,z4,z132,z6]),(1,[z1,z2,z4,z5,z822]),(0,[z1,z255,z2,z7,z5,z538])],[],[(0,[z1,z2,z7,z4,z5,z1389])],[],[(0,[z1,z7,z4,z5,z14,z100]),(0,[z1,z2,z7,z4,z280,z310]),(0,[z1,z1390,z2,z7,z4,z5])],[(1,[z2,z847,z4,z5,z6]),(0,[z17,z2,z380,z4,z111,z6]),(0,[z1,z2,z7,z4,z5,z1391]),(0,[z1,z2,z7,z4,z1325,z32]),(0,[z1,z2,z369,z4,z5,z1392])],[(0,[z1,z2,z7,z4,z5,z1393]),(0,[z1,z2,z7,z4,z1394,z5]),(1,[z1,z7,z4,z14,z443]),(0,[z1,z7,z4,z5,z1395,z6]),(0,[z1,z115,z7,z4,z5,z73])],[(0,[z1,z2,z7,z427,z5,z32]),(0,[z1,z343,z7,z4,z5,z73])],[],[(0,[z0,z34,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z1396,z5]),(0,[z1,z2,z7,z4,z5,z1397]),(1,[z1,z7,z4,z14,z424]),(0,[z1,z9,z7,z4,z67,z73]),(0,[z1,z956,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z1398]),(0,[z33,z1,z7,z4,z14,z73]),(0,[z2,z7,z847,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1399])],[(0,[z1,z626,z7,z4,z14,z6])],[(0,[z536,z37,z2,z7,z4,z5])],[(0,[z1,z37,z2,z7,z4,z464])],[(0,[z1,z392,z7,z4,z5,z365]),(0,[z1,z7,z689,z4,z14,z6]),(0,[z1,z37,z7,z4,z14,z42]),(0,[z1,z1400,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1401]),(0,[z1,z37,z7,z4,z5,z248]),(0,[z1,z2,z7,z4,z464,z32]),(0,[z1,z37,z1031,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1402]),(0,[z263,z1,z7,z4,z14,z73]),(0,[z48,z1,z37,z130,z4,z5]),(0,[z1,z343,z308,z4,z137,z6])],[(0,[z24,z2,z25,z4,z5,z290]),(0,[z1,z2,z7,z4,z5,z1403]),(0,[z1,z355,z7,z4,z5,z350]),(0,[z1,z2,z7,z4,z1404,z5]),(0,[z1,z2,z256,z4,z5,z10])],[(0,[z1,z2,z7,z4,z1405,z6]),(0,[z1,z2,z7,z4,z499,z278])],[],[(0,[z1,z9,z7,z4,z44,z6]),(0,[z1,z2,z7,z4,z1253,z156]),(0,[z1,z2,z1406,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z275]),(0,[z526,z1,z7,z4,z14,z6]),(1,[z397,z7,z4,z14,z6]),(0,[z1,z2,z7,z1407,z5,z6]),(0,[z1,z967,z7,z4,z5,z6]),(0,[z434,z2,z7,z4,z5,z10]),(0,[z1,z97,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z449,z73]),(0,[z1,z37,z2,z7,z349,z5])],[(0,[z237,z72,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z39,z296]),(0,[z1,z1408,z2,z7,z4,z5]),(0,[z1,z1181,z2,z7,z4,z5]),(0,[z1,z268,z7,z4,z14,z32]),(0,[z1,z2,z7,z4,z5,z1409])],[],[(0,[z330,z1,z2,z7,z85,z6]),(0,[z1,z2,z183,z4,z5,z32])],[(0,[z1,z392,z7,z4,z5,z6]),(0,[z1,z1410,z7,z4,z5,z6]),(0,[z1411,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z65,z6]),(0,[z1,z309,z7,z4,z5,z32])],[(0,[z1,z152,z7,z4,z5,z73])],[],[(0,[z263,z2,z7,z1148,z5,z6]),(0,[z1,z2,z7,z1148,z5,z6]),(0,[z1,z7,z4,z14,z285,z73])],[(0,[z1,z2,z7,z4,z5,z1412]),(0,[z1,z9,z7,z4,z5,z77]),(0,[z1,z7,z47,z4,z111,z14]),(0,[z1,z414,z7,z4,z5,z354])],[(0,[z1,z2,z7,z4,z5,z1413]),(0,[z1,z392,z380,z4,z5,z6]),(0,[z1,z170,z7,z95,z5,z275]),(0,[z1,z37,z170,z7,z95,z5]),(0,[z1,z2,z288,z4,z145,z5]),(0,[z455,z1,z2,z4,z5,z10])],[(0,[z1,z2,z7,z4,z5,z1414]),(0,[z634,z2,z7,z4,z499,z6])],[(0,[z1,z2,z7,z1415,z4,z5]),(0,[z1,z2,z7,z1416,z5,z6]),(0,[z1,z1417,z7,z4,z5,z6]),(1,[z1,z2,z7,z874,z5]),(0,[z1,z2,z7,z178,z5,z85])],[(0,[z1,z2,z7,z4,z202,z32]),(0,[z1,z672,z7,z4,z14,z6])],[(0,[z1418,z1,z2,z7,z4,z5]),(1,[z1,z938,z4,z5,z6]),(0,[z1363,z37,z2,z7,z4,z5])],[(0,[z315,z2,z7,z146,z5,z6]),(0,[z1,z174,z2,z7,z270,z5]),(0,[z1,z7,z4,z230,z14,z6]),(0,[z1,z2,z7,z4,z171,z32]),(0,[z1,z2,z7,z4,z14,z310]),(0,[z1,z37,z2,z21,z141,z5])],[(0,[z1,z1419,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z307,z5]),(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z2,z7,z298,z141,z5]),(0,[z271,z1,z2,z4,z5,z822])],[(0,[z1,z259,z7,z4,z38,z5]),(0,[z1,z2,z7,z289,z38,z5]),(0,[z1,z2,z7,z4,z5,z1420]),(0,[z1,z138,z7,z4,z14,z6])],[(0,[z1,z129,z84,z4,z5,z73])],[(0,[z91,z2,z13,z47,z4,z5]),(0,[z556,z2,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z1421]),(0,[z1,z37,z2,z7,z47,z5]),(0,[z1,z2,z7,z4,z38,z430]),(0,[z1,z2,z7,z4,z38,z73])],[(0,[z383,z1,z2,z7,z4,z5]),(0,[z1,z7,z190,z4,z5,z14]),(0,[z16,z309,z7,z4,z5,z6]),(0,[z1,z2,z7,z787,z85,z6]),(0,[z1,z7,z4,z5,z1422,z6])],[(0,[z1,z2,z7,z4,z171,z275]),(0,[z1,z7,z4,z145,z5,z14]),(0,[z536,z2,z7,z4,z5,z73]),(0,[z1,z115,z7,z4,z5,z10])],[(1,[z1,z7,z4,z14,z76]),(0,[z1,z97,z7,z4,z14,z6]),(0,[z1,z2,z7,z1423,z5,z6]),(0,[z1,z343,z7,z4,z5,z10])]],
   [[(0,[z1,z341,z7,z4,z5,z365]),(0,[z1,z7,z61,z4,z14,z6]),(0,[z1,z2,z7,z5,z906,z6]),(0,[z1,z228,z2,z7,z5,z29])],[(0,[z1,z2,z1424,z7,z4,z5]),(0,[z1,z2,z212,z4,z173,z5]),(0,[z1,z7,z47,z4,z5,z204]),(0,[z295,z1,z2,z4,z173,z5])],[(0,[z540,z2,z7,z47,z4,z5]),(0,[z189,z2,z7,z4,z5,z126]),(0,[z1,z9,z117,z7,z4,z5]),(0,[z1,z228,z2,z7,z4,z14]),(0,[z1,z2,z7,z4,z132,z419]),(0,[z634,z537,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1425]),(0,[z1,z1426,z2,z7,z4,z5]),(0,[z1,z2,z4,z5,z822,z32]),(0,[z271,z1,z2,z194,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1427]),(0,[z1,z7,z4,z5,z1428,z6])],[(0,[z1,z7,z4,z54,z14,z32]),(0,[z1,z2,z7,z4,z312,z73]),(0,[z1,z105,z2,z7,z4,z5])],[(0,[z1,z7,z4,z54,z104,z6]),(0,[z1,z2,z7,z1361,z5,z6]),(0,[z1,z2,z7,z282,z4,z419])],[(0,[z1,z9,z7,z4,z5,z116]),(0,[z1,z7,z4,z5,z204,z73]),(0,[z1,z2,z7,z4,z75,z73])],[(0,[z1,z9,z7,z4,z5,z126]),(0,[z1,z2,z369,z4,z14,z6])],[(0,[z1,z7,z4,z5,z326,z14]),(0,[z15,z1,z309,z4,z42,z6])],[(0,[z397,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z38,z111,z14]),(0,[z1004,z2,z7,z4,z5,z6])],[(0,[z1,z9,z21,z141,z5,z6]),(0,[z1,z2,z4,z173,z5,z10])],[(1,[z1,z7,z828,z5,z6]),(0,[z1,z7,z4,z14,z6,z344]),(0,[z1,z2,z7,z4,z499,z32]),(0,[z1,z2,z7,z1429,z4,z5])],[(0,[z1,z7,z4,z99,z14,z6]),(0,[z1,z7,z4,z101,z14,z6]),(0,[z1,z355,z7,z80,z5,z6])],[(0,[z1,z2,z7,z1430,z4,z5]),(0,[z1,z37,z2,z308,z4,z137])],[(0,[z1,z343,z7,z4,z38,z5])],[(0,[z1,z1431,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1432]),(0,[z36,z1,z2,z80,z65,z6])],[(0,[z0,z383,z34,z7,z4,z5]),(1,[z1,z228,z7,z4,z14]),(0,[z1,z2,z7,z47,z5,z585])],[(0,[z1,z152,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z1433,z6])],[(0,[z1,z9,z7,z1434,z5,z6]),(0,[z1,z2,z7,z4,z1435,z5])],[(0,[z1,z2,z7,z1436,z5,z6]),(0,[z1,z9,z105,z7,z4,z5])],[(0,[z1,z37,z7,z4,z5,z14]),(0,[z1,z2,z7,z978,z5,z6]),(0,[z1,z2,z7,z4,z5,z1437]),(0,[z1,z2,z369,z4,z5,z1184])],[(0,[z2,z7,z1148,z4,z5,z6]),(0,[z357,z1,z7,z4,z14,z6])],[(0,[z1,z1438,z7,z4,z5,z6])],[(0,[z1,z117,z7,z4,z5,z14]),(0,[z1,z7,z4,z65,z14,z6])],[(0,[z1,z9,z3,z4,z5,z6]),(0,[z1,z341,z7,z47,z4,z5]),(0,[z1,z9,z7,z4,z5,z22])],[],[(0,[z1,z2,z7,z1439,z5,z6]),(0,[z1,z2,z7,z4,z5,z1440]),(0,[z2,z7,z47,z232,z134,z5]),(0,[z1,z2,z7,z4,z5,z365]),(0,[z1,z7,z4,z35,z14,z73]),(0,[z157,z1,z7,z4,z14,z32])],[(0,[z1,z7,z4,z248,z42,z6]),(0,[z1,z7,z4,z5,z450,z6]),(0,[z1,z831,z7,z47,z4,z5])],[(0,[z1,z2,z7,z1441,z5,z6]),(0,[z17,z2,z7,z4,z111,z32])],[(0,[z1,z7,z4,z5,z1442,z6]),(0,[z1,z129,z84,z4,z5,z10]),(0,[z1,z220,z121,z4,z5,z6])],[(0,[z1,z2,z7,z1277,z304,z5]),(0,[z263,z2,z7,z47,z146,z5]),(0,[z1,z2,z7,z47,z146,z5]),(0,[z1443,z2,z7,z4,z5,z6]),(0,[z15,z1,z7,z4,z14,z73]),(0,[z1,z965,z7,z4,z14,z6]),(0,[z1,z625,z7,z4,z14,z73])],[(0,[z1,z2,z380,z4,z5,z365]),(0,[z17,z2,z7,z47,z4,z111]),(0,[z1,z7,z4,z14,z472,z6]),(0,[z189,z2,z7,z307,z5,z6]),(0,[z1,z138,z7,z4,z412,z6]),(0,[z1,z9,z7,z4,z132,z6]),(0,[z1,z2,z7,z47,z5,z71])]],
   [[(0,[z1,z2,z7,z4,z38,z44]),(0,[z1,z152,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z1444,z6]),(0,[z1,z7,z4,z148,z14,z6]),(0,[z1,z7,z4,z14,z419,z6]),(0,[z1,z2,z7,z4,z312,z79]),(0,[z536,z2,z7,z4,z5,z10]),(0,[z1,z614,z7,z4,z5,z32]),(0,[z1,z2,z844,z47,z4,z5])],[(0,[z1,z3,z4,z5,z14,z6]),(0,[z1,z37,z2,z183,z4,z5]),(1,[z1,z2,z80,z499,z6])],[(0,[z1,z7,z4,z111,z14,z73])],[(0,[z1,z341,z7,z4,z54,z6]),(0,[z1,z1195,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z6]),(0,[z0,z801,z7,z4,z5,z6]),(0,[z1,z2,z1445,z7,z4,z5]),(0,[z1,z9,z7,z307,z5,z6]),(0,[z1,z193,z7,z4,z14,z6]),(0,[z1,z37,z2,z7,z5,z399]),(0,[z1,z1446,z2,z7,z4,z5]),(0,[z1,z37,z2,z7,z420,z5])],[(0,[z1,z2,z7,z4,z5,z1447]),(0,[z486,z2,z7,z146,z5,z6]),(0,[z1,z7,z4,z171,z14,z6])],[(0,[z1,z1448,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z300,z73]),(0,[z1,z2,z7,z4,z312,z10]),(0,[z1,z1449,z7,z4,z5,z6]),(0,[z207,z1,z2,z4,z42,z6]),(0,[z1,z2,z7,z1450,z4,z5])],[(0,[z1,z1451,z7,z4,z5,z6]),(0,[z198,z1,z7,z4,z5,z79]),(0,[z1452,z2,z7,z4,z5,z6]),(0,[z1,z277,z2,z7,z47,z5])],[(0,[z1,z1453,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z204,z10])],[],[(0,[z1,z2,z303,z427,z5,z6]),(0,[z1,z2,z675,z141,z5,z6]),(0,[z1,z2,z7,z1454,z4,z5]),(0,[z1,z479,z2,z7,z5,z285])],[(0,[z1,z152,z7,z4,z156,z6]),(0,[z589,z2,z7,z4,z111,z6]),(0,[z1,z2,z7,z4,z5,z1455]),(0,[z1,z2,z7,z4,z5,z1456]),(0,[z1,z537,z7,z4,z5,z73])],[(0,[z1,z1457,z2,z7,z4,z5]),(0,[z1,z2,z1458,z4,z5,z6]),(0,[z1,z129,z84,z4,z38,z5]),(0,[z1,z164,z7,z4,z14,z6])],[(0,[z1,z170,z7,z95,z5,z6]),(0,[z1,z2,z7,z1459,z4,z5])],[(0,[z17,z2,z7,z4,z111,z73])],[(0,[z1,z87,z7,z4,z5,z6]),(0,[z1,z37,z7,z153,z4,z14]),(0,[z536,z2,z7,z4,z38,z5]),(0,[z16,z614,z7,z4,z5,z6])],[(0,[z1,z2,z183,z4,z38,z5]),(0,[z157,z1,z37,z7,z4,z14]),(0,[z1,z2,z7,z4,z38,z464])],[(0,[z1,z2,z7,z304,z5,z466]),(0,[z1,z7,z4,z180,z14,z6]),(0,[z1,z309,z7,z4,z38,z5])],[(0,[z1,z2,z7,z47,z4,z5]),(0,[z1,z1460,z7,z4,z5,z6]),(0,[z1,z2,z203,z4,z145,z5])],[(0,[z1,z9,z7,z219,z5,z6]),(0,[z1,z2,z7,z4,z14,z419])],[(0,[z1,z392,z7,z4,z5,z32]),(0,[z1,z7,z185,z4,z14,z6]),(0,[z1,z958,z7,z4,z5,z32]),(0,[z444,z1,z7,z4,z5,z338]),(0,[z1,z2,z7,z4,z5,z1461])],[(0,[z1,z2,z7,z4,z5,z1462]),(0,[z1,z2,z7,z4,z703,z73]),(0,[z1,z228,z9,z7,z4,z5]),(0,[z36,z634,z2,z80,z5,z6]),(0,[z1,z2,z583,z4,z5,z32]),(0,[z1,z1463,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1464]),(0,[z1,z2,z7,z4,z738,z73])],[(0,[z1,z2,z380,z47,z4,z5]),(0,[z1,z7,z4,z5,z14,z344]),(0,[z157,z1,z7,z4,z1140,z6])],[(0,[z1,z2,z7,z4,z169,z5]),(0,[z1,z2,z7,z4,z1465,z6]),(0,[z1,z2,z7,z4,z5,z55]),(0,[z1,z7,z47,z4,z137,z14]),(0,[z1,z7,z4,z5,z1466,z6]),(0,[z1,z1467,z7,z4,z5,z6])],[(0,[z1,z7,z4,z5,z14,z266]),(0,[z1,z7,z4,z5,z14,z347]),(0,[z16,z2,z7,z4,z5,z32]),(0,[z1,z2,z7,z4,z221,z424])],[(0,[z40,z2,z7,z4,z5,z806]),(0,[z540,z2,z7,z4,z5,z126]),(0,[z1,z2,z7,z4,z5,z1468]),(0,[z1,z7,z4,z5,z14,z350])],[(0,[z1,z30,z7,z4,z1035,z6])],[(0,[z1,z2,z7,z4,z1469,z6]),(0,[z330,z1,z7,z4,z14,z6]),(0,[z1,z9,z7,z4,z242,z6]),(0,[z1,z7,z47,z4,z14,z73]),(0,[z1,z7,z4,z5,z1470,z6])],[(0,[z1,z7,z4,z202,z14,z6]),(0,[z1,z87,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z1471,z5]),(0,[z1,z7,z130,z4,z242,z6]),(0,[z1472,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1473])],[(0,[z1,z37,z2,z7,z4,z202])],[(0,[z1,z1474,z7,z4,z5,z6]),(0,[z1,z1475,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z183,z4,z5,z1038]),(0,[z36,z1,z7,z4,z14,z73]),(0,[z1,z2,z203,z4,z173,z5])],[(0,[z1,z2,z1476,z4,z5,z6]),(0,[z1,z2,z7,z1370,z5,z10]),(0,[z1,z2,z7,z178,z153,z5]),(0,[z1,z37,z832,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1477]),(0,[z1,z2,z7,z4,z67,z73]),(0,[z1,z2,z7,z1407,z5,z73])],[(0,[z1,z2,z303,z4,z202,z6])],[(0,[z1,z7,z4,z111,z14,z10]),(0,[z1,z7,z4,z14,z305,z73])],[(0,[z1,z9,z7,z253,z5,z6]),(0,[z397,z37,z2,z7,z4,z5])],[(0,[z1,z392,z7,z4,z5,z73]),(0,[z1,z2,z7,z1478,z5,z6]),(0,[z1,z2,z7,z47,z103,z5]),(0,[z1,z2,z7,z4,z5,z1479]),(0,[z556,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z1480,z4,z5]),(0,[z1,z7,z4,z14,z6,z507])],[(0,[z1,z2,z7,z4,z1481,z6]),(0,[z1,z37,z1463,z7,z4,z5])],[(0,[z263,z9,z7,z146,z5,z6]),(0,[z1,z839,z2,z7,z4,z5]),(0,[z1,z9,z7,z4,z31,z5]),(0,[z1,z475,z2,z7,z47,z5])],[(0,[z1,z2,z7,z4,z5,z1482]),(0,[z1,z7,z4,z5,z1483,z6]),(0,[z1,z2,z7,z4,z111,z419]),(0,[z1,z268,z7,z4,z38,z14]),(0,[z1484,z2,z7,z4,z5,z6])],[],[(0,[z263,z37,z2,z7,z146,z5]),(0,[z40,z2,z7,z4,z5,z622]),(0,[z540,z2,z7,z4,z5,z73])],[(0,[z1,z2,z7,z4,z44,z6]),(0,[z1,z2,z7,z4,z5,z1485]),(0,[z1,z2,z7,z253,z5,z240]),(0,[z17,z37,z2,z7,z4,z111]),(0,[z1,z2,z4,z5,z10,z454]),(0,[z1,z537,z7,z4,z5,z10])],[(0,[z1,z2,z7,z427,z5,z77]),(0,[z208,z2,z13,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1486]),(0,[z1,z435,z9,z7,z4,z5])],[(0,[z1,z2,z7,z4,z39,z466]),(0,[z1,z1487,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z326]),(0,[z1,z2,z7,z4,z5,z1488]),(0,[z1,z2,z1476,z47,z4,z5])],[(0,[z1,z2,z7,z178,z146,z5]),(0,[z1,z2,z7,z4,z1489,z5]),(0,[z1,z9,z7,z4,z14,z6]),(0,[z1,z2,z7,z4,z5,z1490])],[(0,[z1,z2,z7,z4,z1491,z5]),(0,[z1,z7,z4,z14,z6,z310]),(0,[z1,z2,z7,z4,z5,z1492]),(0,[z473,z1,z2,z7,z4,z419]),(0,[z1,z2,z7,z178,z5,z71])],[(0,[z1,z2,z7,z4,z38,z409]),(0,[z1,z30,z524,z7,z4,z38])],[(0,[z1,z2,z7,z4,z5,z1074]),(0,[z634,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z38,z14,z73]),(0,[z1,z2,z7,z4,z1493,z6]),(0,[z157,z1,z115,z7,z85,z6]),(0,[z1,z2,z1494,z4,z5,z6])],[],[(0,[z1,z2,z7,z4,z5,z77]),(0,[z1,z259,z7,z4,z132,z6])],[(0,[z1,z2,z7,z4,z5,z1495]),(0,[z1,z7,z4,z5,z1395,z10])],[(0,[z681,z34,z7,z4,z5,z6]),(0,[z1,z479,z2,z7,z212,z5])],[(0,[z1,z2,z7,z4,z5,z1496]),(0,[z1,z2,z7,z5,z906,z73])],[],[(0,[z1,z2,z7,z1497,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1498])],[(0,[z1,z9,z7,z4,z5,z290]),(0,[z1,z537,z7,z4,z38,z5]),(0,[z1,z2,z7,z162,z5,z446])],[(0,[z1,z9,z7,z4,z5,z192]),(0,[z1,z7,z4,z5,z14,z466]),(0,[z1,z174,z2,z7,z47,z5])],[(0,[z1,z2,z7,z4,z5,z1499]),(0,[z1,z2,z1500,z4,z5,z6]),(0,[z921,z2,z7,z47,z4,z5])],[(0,[z1,z7,z4,z773,z5,z6])]],
   [[(0,[z1,z37,z2,z7,z4,z5]),(0,[z539,z1,z2,z4,z42,z6]),(0,[z1,z2,z7,z4,z5,z1501])],[(0,[z1,z2,z7,z167,z39,z6]),(0,[z1,z2,z7,z1502,z4,z5]),(0,[z1,z37,z2,z7,z4,z213]),(0,[z1,z2,z7,z1503,z4,z5]),(0,[z634,z2,z7,z47,z4,z5]),(0,[z397,z2,z7,z4,z5,z73]),(0,[z1,z2,z1494,z47,z4,z5])],[(0,[z1,z341,z7,z4,z5,z73]),(0,[z1,z7,z4,z14,z6,z443])],[(0,[z238,z1,z7,z4,z14,z6]),(0,[z1,z9,z7,z4,z132,z122]),(0,[z1,z524,z7,z4,z5,z32]),(0,[z1452,z37,z2,z7,z4,z5])],[(0,[z40,z2,z7,z232,z4,z5]),(0,[z107,z1,z7,z4,z5,z354]),(0,[z1,z2,z4,z5,z42,z76]),(0,[z1,z2,z7,z178,z4,z5])],[(0,[z1,z7,z153,z141,z14,z6]),(0,[z107,z1,z7,z4,z5,z338])],[(0,[z1,z9,z7,z4,z213,z6]),(0,[z1,z7,z4,z14,z85,z73]),(0,[z1,z9,z7,z4,z5,z1504]),(0,[z36,z1,z2,z47,z80,z5])],[(0,[z1,z7,z4,z542,z5,z14]),(0,[z1,z37,z97,z7,z4,z5])],[(0,[z1,z1505,z7,z4,z5,z6]),(0,[z1,z174,z2,z7,z5,z285]),(0,[z1,z2,z7,z4,z5,z122]),(0,[z556,z2,z7,z4,z5,z10])],[(0,[z1,z2,z384,z4,z5,z32]),(0,[z1,z2,z4,z394,z42,z6]),(0,[z1,z2,z7,z4,z5,z1506])],[(0,[z1,z2,z7,z4,z5,z1507]),(0,[z1,z2,z7,z4,z5,z1508]),(0,[z1,z2,z7,z4,z326,z73])],[(0,[z1,z7,z4,z494,z14,z6])],[(0,[z1,z2,z7,z4,z1509,z6]),(0,[z149,z1,z7,z4,z14,z73]),(0,[z1,z7,z4,z5,z708,z79]),(0,[z1,z16,z2,z4,z42,z6])],[(0,[z1,z2,z7,z4,z666,z73]),(0,[z1,z2,z7,z4,z5,z1510])],[(0,[z91,z2,z13,z4,z39,z6]),(0,[z1,z2,z1511,z4,z5,z6]),(0,[z1,z37,z392,z7,z4,z5]),(0,[z540,z2,z7,z4,z5,z10]),(0,[z1,z614,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1512]),(0,[z1,z1042,z2,z7,z47,z5]),(0,[z540,z2,z7,z4,z242,z6])],[(0,[z1,z72,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z1513,z6]),(0,[z1,z2,z7,z4,z1514,z5])],[(0,[z1,z801,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1515]),(0,[z1,z2,z7,z4,z1516,z5]),(0,[z1,z138,z256,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1517]),(0,[z1,z2,z7,z4,z5,z1518]),(0,[z1,z37,z2,z7,z178,z5])],[(0,[z1,z2,z7,z1519,z5,z6]),(0,[z1,z2,z7,z4,z5,z1520]),(0,[z1107,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z450,z73])],[(0,[z1,z2,z3,z427,z5,z6]),(0,[z1,z2,z7,z1521,z5,z6]),(0,[z1,z2,z7,z4,z254,z73]),(0,[z1,z2,z7,z4,z65,z278]),(0,[z434,z138,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1522]),(0,[z1,z2,z7,z1434,z5,z6]),(0,[z24,z7,z4,z111,z14,z6]),(0,[z1,z174,z7,z4,z5,z14]),(0,[z1,z20,z89,z7,z4,z5]),(0,[z1,z9,z7,z4,z412,z6]),(0,[z1,z2,z7,z4,z5,z1523])],[(0,[z1,z255,z2,z7,z298,z5]),(0,[z16,z2,z7,z4,z42,z6]),(0,[z434,z2,z256,z4,z5,z6])],[(0,[z1,z2,z303,z4,z5,z32]),(0,[z1,z392,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z1524]),(0,[z1,z9,z7,z4,z132,z73])],[(0,[z2,z25,z847,z4,z5,z6]),(0,[z1,z1525,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1526]),(0,[z24,z37,z2,z25,z4,z5]),(0,[z1,z1527,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z848]),(0,[z1,z2,z7,z874,z5,z32])],[(0,[z2,z7,z253,z5,z111,z6]),(0,[z1,z222,z7,z4,z5,z6]),(0,[z1,z7,z4,z14,z381,z73]),(0,[z1,z2,z7,z4,z5,z1528])],[(0,[z1,z2,z7,z155,z202,z6])],[(0,[z1,z2,z7,z4,z5,z73])],[(0,[z1529,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1530]),(0,[z1,z9,z7,z4,z5,z344]),(0,[z1,z2,z7,z4,z1243,z5])],[(0,[z263,z7,z146,z5,z14,z6]),(0,[z1,z7,z4,z5,z14,z429]),(0,[z1,z568,z7,z95,z5,z6]),(0,[z1,z2,z7,z4,z5,z1531]),(0,[z1,z2,z7,z4,z5,z1532]),(0,[z1,z7,z4,z5,z104,z344]),(0,[z1,z138,z7,z4,z5,z443])],[(0,[z1,z2,z7,z4,z5,z1533]),(0,[z1,z9,z7,z4,z5,z266]),(0,[z1,z9,z7,z4,z5,z347]),(0,[z1,z2,z7,z4,z5,z1534])]],
   [[(0,[z1,z2,z139,z4,z137,z6]),(0,[z1,z4,z137,z14,z42,z6]),(0,[z1,z9,z7,z4,z5,z350]),(0,[z1,z417,z9,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1535]),(0,[z1,z2,z256,z4,z5,z443])],[(0,[z1,z2,z7,z1536,z4,z5]),(0,[z1,z2,z380,z4,z5,z73]),(0,[z1,z7,z4,z14,z73,z507]),(0,[z1,z2,z7,z4,z326,z42])],[(0,[z214,z7,z4,z111,z14,z6]),(0,[z1,z1537,z2,z7,z4,z5]),(0,[z1,z2,z308,z4,z711,z6])],[(1,[z540,z130,z4,z5,z6]),(0,[z1,z228,z2,z7,z4,z132]),(0,[z1,z2,z7,z4,z1538,z5]),(0,[z1,z2,z7,z4,z5,z1539]),(0,[z397,z2,z7,z4,z5,z10]),(0,[z434,z2,z7,z4,z5,z443]),(0,[z1,z66,z7,z47,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1540]),(0,[z1,z341,z7,z4,z5,z10]),(0,[z48,z1,z130,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z1290]),(0,[z157,z1,z7,z47,z4,z14]),(0,[z1,z164,z7,z4,z14,z73]),(0,[z36,z1,z37,z2,z80,z5]),(0,[z1,z2,z369,z4,z5,z158])],[(0,[z1,z1541,z7,z4,z5,z6]),(0,[z1,z84,z4,z5,z191,z6]),(0,[z1,z170,z7,z95,z5,z73]),(0,[z1,z2,z308,z4,z137,z6])],[(0,[z1,z1129,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z147]),(0,[z1,z259,z7,z4,z14,z6]),(0,[z1,z7,z4,z542,z5,z104])],[(0,[z1,z2,z7,z4,z1542,z6]),(0,[z1,z87,z7,z4,z5,z73]),(0,[z1,z7,z4,z5,z14,z158]),(0,[z1,z1543,z2,z7,z4,z5]),(0,[z16,z2,z7,z47,z4,z5]),(0,[z1,z2,z7,z4,z5,z1544]),(0,[z1,z2,z7,z4,z5,z1545])],[(0,[z1,z2,z7,z4,z5,z1546]),(0,[z1,z1547,z7,z4,z5,z6]),(0,[z15,z1,z2,z4,z38,z42]),(0,[z1,z222,z7,z47,z4,z5]),(0,[z1,z373,z410,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1548]),(0,[z1,z2,z7,z298,z134,z5])],[(0,[z1,z2,z7,z4,z1549,z6]),(0,[z1550,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z306,z14,z6]),(0,[z1,z115,z256,z4,z5,z6])],[(0,[z1,z2,z7,z4,z38,z202]),(0,[z1,z2,z7,z1058,z5,z6]),(0,[z1,z37,z2,z7,z4,z412]),(0,[z1,z7,z334,z4,z14,z6]),(0,[z1,z2,z7,z4,z1551,z5]),(0,[z1,z2,z369,z4,z5,z443])],[(0,[z24,z2,z7,z167,z5,z6]),(0,[z1,z2,z7,z47,z5,z659]),(0,[z1,z2,z7,z4,z5,z1552])],[(0,[z1,z2,z3,z4,z202,z6]),(0,[z1,z2,z1553,z7,z4,z5]),(0,[z434,z115,z7,z4,z5,z6]),(0,[z157,z1,z7,z4,z204,z6])],[(0,[z1,z341,z7,z253,z5,z6]),(0,[z1,z1232,z2,z7,z289,z5]),(0,[z1,z7,z4,z5,z14,z443])],[(0,[z48,z189,z130,z4,z5,z6]),(0,[z1,z7,z4,z233,z14,z6]),(0,[z634,z37,z2,z7,z4,z5]),(0,[z157,z1,z37,z2,z7,z85])],[(0,[z1,z415,z7,z4,z14,z6]),(0,[z1,z129,z7,z289,z5,z6]),(0,[z1,z2,z7,z4,z551,z73])],[(0,[z24,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z5,z53]),(0,[z1,z7,z4,z5,z14,z424]),(0,[z1,z7,z4,z67,z450,z73])],[(0,[z0,z187,z7,z4,z5,z6]),(0,[z1,z7,z349,z4,z14,z6]),(0,[z1,z164,z7,z4,z5,z113]),(0,[z397,z2,z7,z4,z38,z5])],[(0,[z1,z2,z7,z4,z44,z32]),(0,[z17,z7,z4,z111,z14,z6]),(0,[z1,z7,z4,z352,z14,z6]),(0,[z107,z1,z7,z4,z14,z73]),(0,[z1,z2,z194,z4,z5,z32]),(0,[z1,z66,z7,z4,z67,z73])],[(0,[z1,z2,z7,z4,z5,z1554]),(0,[z1,z2,z7,z4,z1173,z499])],[(0,[z1,z2,z7,z4,z5,z1555]),(0,[z1,z2,z7,z4,z1050,z6]),(0,[z1,z203,z7,z4,z14,z73]),(0,[z1,z7,z4,z5,z450,z10])],[(0,[z1,z2,z7,z219,z5,z6]),(0,[z15,z1,z2,z4,z42,z6]),(0,[z340,z2,z7,z4,z5,z622])],[(0,[z1,z2,z7,z4,z1556,z6]),(0,[z2,z7,z4,z5,z6,z806]),(0,[z1,z2,z7,z4,z65,z32]),(0,[z1,z115,z7,z4,z5,z443])],[(0,[z1,z7,z4,z312,z14,z6]),(0,[z1,z2,z7,z4,z5,z796]),(0,[z489,z1,z2,z4,z42,z6])],[(0,[z1,z2,z7,z4,z5,z1557]),(0,[z540,z2,z7,z4,z213,z6]),(0,[z1,z2,z7,z1558,z5,z6]),(0,[z1,z9,z7,z4,z132,z10])],[(0,[z1,z7,z4,z14,z42,z6]),(0,[z1,z37,z343,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1559]),(0,[z1,z152,z7,z4,z5,z296]),(0,[z40,z2,z7,z4,z360,z5]),(0,[z1,z1560,z2,z7,z4,z5])],[(0,[z1,z2,z7,z1561,z5,z6]),(0,[z1,z2,z7,z4,z5,z1562]),(0,[z1,z2,z616,z4,z5,z32])],[(0,[z1,z4,z191,z14,z42,z6]),(0,[z1,z37,z2,z7,z4,z845])],[(0,[z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z253,z5,z365]),(0,[z214,z1,z7,z4,z14,z73])],[(0,[z1,z37,z2,z3,z4,z5]),(0,[z281,z2,z7,z47,z134,z5]),(0,[z1,z30,z7,z47,z4,z14]),(0,[z1,z2,z7,z1563,z5,z6])]],
   [[(0,[z1,z2,z7,z1564,z5,z6])],[(0,[z1,z2,z7,z47,z679,z5]),(0,[z1,z2,z7,z4,z5,z1565]),(0,[z1,z2,z7,z4,z312,z113]),(0,[z1,z2,z516,z4,z5,z32]),(0,[z36,z1,z2,z80,z5,z350]),(0,[z1163,z2,z7,z4,z5,z6])],[(0,[z1,z2,z369,z153,z5,z6])],[(0,[z1,z2,z380,z4,z5,z10])],[(0,[z1,z7,z288,z4,z14,z42])],[(0,[z1,z2,z7,z4,z44,z73]),(0,[z91,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z223,z73])],[(0,[z24,z9,z25,z4,z5,z6]),(0,[z999,z2,z7,z47,z4,z5])],[(1,[z2,z13,z4,z39,z6]),(0,[z1,z2,z7,z4,z1566,z6]),(0,[z1,z170,z7,z95,z5,z10]),(0,[z1,z2,z7,z4,z797,z6]),(0,[z157,z1,z2,z256,z85,z6])],[(0,[z1,z2,z7,z253,z5,z6]),(0,[z1,z129,z683,z4,z5,z6]),(0,[z1,z9,z7,z4,z14,z73])],[(0,[z1,z87,z7,z4,z5,z10]),(0,[z1,z7,z130,z4,z14,z73])],[(0,[z90,z1,z2,z4,z5,z76])],[(0,[z1,z7,z4,z5,z14,z1328]),(0,[z1,z37,z2,z7,z4,z312]),(0,[z634,z2,z7,z4,z5,z73]),(0,[z36,z1,z2,z978,z5,z6])],[(0,[z1,z2,z7,z4,z1567,z5]),(0,[z1,z1568,z2,z7,z4,z5]),(0,[z1,z7,z579,z4,z5,z14]),(0,[z1569,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z5,z1570]),(0,[z1,z2,z380,z253,z5,z6]),(0,[z1,z2,z7,z4,z1283,z6])],[(0,[z1,z7,z4,z5,z14,z400]),(0,[z1,z2,z7,z4,z38,z213])],[(0,[z1,z2,z7,z1571,z5,z6]),(0,[z17,z1,z7,z4,z14,z73]),(0,[z1,z170,z7,z547,z5,z6]),(0,[z1,z397,z7,z4,z14,z6]),(0,[z1,z37,z2,z7,z4,z1493])],[(0,[z1,z1572,z2,z7,z4,z5]),(0,[z1,z463,z7,z96,z5,z6]),(0,[z214,z7,z4,z5,z305,z6]),(0,[z1,z2,z141,z4,z173,z5]),(0,[z1573,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z204,z353])],[(0,[z1,z7,z4,z5,z1574,z6]),(0,[z1,z7,z4,z5,z14,z76]),(0,[z1,z524,z7,z47,z4,z5])],[(0,[z1,z936,z2,z7,z4,z5]),(0,[z208,z2,z7,z4,z111,z6]),(0,[z1,z2,z7,z1575,z4,z5]),(0,[z1,z2,z7,z4,z1576,z6]),(0,[z1,z7,z4,z5,z14,z474]),(0,[z1,z2,z7,z4,z145,z5]),(0,[z1,z1577,z2,z7,z4,z5]),(0,[z1,z1467,z7,z4,z5,z10])],[(0,[z1,z2,z21,z141,z5,z32]),(0,[z83,z1,z623,z7,z4,z5])],[(0,[z1,z1578,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z171]),(0,[z1579,z2,z7,z4,z5,z6])],[],[(0,[z1,z2,z7,z4,z5,z1580]),(0,[z1,z170,z7,z95,z38,z5]),(0,[z90,z1,z7,z4,z14,z73])],[(0,[z1,z7,z4,z14,z535,z73])],[(0,[z1,z2,z7,z4,z5,z1581]),(0,[z1,z2,z7,z4,z156,z6]),(0,[z1,z87,z7,z4,z38,z5]),(0,[z1,z2,z7,z4,z1582,z5]),(0,[z1,z2,z7,z1583,z5,z6]),(0,[z1,z2,z7,z4,z544,z73])],[(0,[z1,z7,z4,z396,z14,z6]),(0,[z48,z1,z130,z4,z5,z49])],[(0,[z536,z7,z4,z5,z14,z6]),(0,[z1,z623,z7,z4,z5,z79]),(0,[z1,z2,z256,z4,z5,z727])],[(0,[z1,z2,z7,z1584,z5,z6]),(0,[z1,z7,z4,z5,z14,z269]),(0,[z1,z1585,z2,z7,z4,z5])],[(0,[z1,z2,z7,z307,z5,z49]),(0,[z1,z129,z121,z4,z5,z6])],[(0,[z1,z2,z1586,z4,z5,z6])],[(0,[z24,z25,z4,z5,z14,z6]),(0,[z1,z2,z7,z828,z5,z6]),(0,[z1,z2,z7,z4,z5,z1587])],[(0,[z1,z1307,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z290]),(0,[z157,z1,z2,z7,z687,z6]),(0,[z1588,z2,z7,z4,z5,z6]),(0,[z1,z2,z394,z5,z42,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z192]),(0,[z1,z2,z7,z769,z18,z5]),(0,[z36,z1,z9,z80,z5,z6]),(0,[z1,z20,z7,z4,z5,z362]),(0,[z1,z2,z7,z4,z173,z5])],[(0,[z1,z2,z3,z4,z5,z32]),(0,[z1,z37,z2,z7,z155,z5])],[(0,[z1,z2,z7,z4,z5,z825]),(0,[z1,z1589,z2,z7,z4,z5])],[(0,[z1,z87,z7,z4,z156,z6]),(0,[z1,z2,z7,z167,z5,z466]),(0,[z673,z2,z13,z4,z5,z6]),(0,[z1,z1590,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z310]),(0,[z1,z2,z7,z1591,z4,z5])],[(0,[z1,z9,z7,z4,z5,z429]),(0,[z1,z2,z7,z4,z5,z1592]),(0,[z1,z1593,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z6,z708])],[(0,[z1,z2,z303,z47,z4,z5]),(0,[z1,z2,z7,z1594,z5,z6]),(0,[z1,z2,z7,z4,z5,z1595]),(0,[z1,z7,z4,z409,z14,z6]),(0,[z1,z2,z7,z47,z375,z5]),(0,[z1,z7,z47,z4,z5,z450])],[(0,[z24,z2,z608,z4,z5,z6]),(0,[z189,z2,z7,z289,z5,z6]),(0,[z1,z2,z7,z734,z4,z5])],[(0,[z1,z203,z4,z5,z14,z32]),(0,[z1,z9,z7,z298,z4,z5]),(0,[z1,z9,z256,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1596]),(0,[z1,z2,z7,z4,z5,z1597])],[(0,[z1,z9,z7,z4,z317,z6]),(0,[z1,z2,z7,z4,z1598,z5])],[(0,[z1,z2,z7,z4,z5,z1504])],[(0,[z1,z7,z4,z5,z1599,z6]),(0,[z1,z1600,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z242]),(0,[z48,z1,z130,z4,z5,z32]),(0,[z1,z2,z7,z4,z5,z1601]),(0,[z1,z9,z7,z4,z14,z10]),(0,[z372,z1,z7,z4,z14,z73]),(0,[z1,z2,z7,z4,z5,z1602]),(0,[z1,z309,z7,z162,z5,z6]),(0,[z1,z2,z7,z952,z5,z73])],[(0,[z1,z2,z7,z1603,z4,z5]),(0,[z1,z2,z7,z4,z1604,z5]),(0,[z1,z2,z7,z4,z5,z1089])],[(0,[z1,z1383,z2,z7,z427,z5]),(0,[z1,z569,z7,z4,z5,z113])],[(0,[z1,z2,z7,z307,z5,z32]),(0,[z634,z2,z7,z4,z5,z10])],[(0,[z1,z1203,z7,z4,z5,z6]),(0,[z92,z2,z183,z4,z5,z6]),(0,[z1,z2,z7,z1292,z289,z5]),(0,[z1,z2,z7,z4,z5,z197])],[],[(0,[z1,z2,z3,z4,z5,z963]),(0,[z91,z2,z13,z4,z5,z466])],[(0,[z0,z34,z7,z4,z202,z6]),(0,[z1,z2,z7,z4,z1605,z5]),(0,[z1,z129,z7,z4,z171,z6]),(0,[z1,z2,z7,z4,z5,z1606])],[(0,[z1,z458,z7,z4,z14,z6]),(0,[z1,z222,z7,z4,z5,z73])],[(0,[z1,z2,z7,z146,z211,z5]),(0,[z1,z2,z183,z4,z111,z6]),(0,[z1607,z2,z7,z4,z5,z6]),(0,[z1,z193,z2,z7,z4,z38]),(0,[z1,z2,z7,z1608,z4,z5])],[(0,[z1,z2,z7,z4,z242,z49]),(0,[z1,z9,z7,z4,z5,z443])],[(0,[z1,z7,z4,z423,z14,z6])],[(0,[z1609,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z1377,z39]),(0,[z40,z2,z7,z4,z5,z210]),(0,[z1,z164,z7,z4,z5,z535])],[(0,[z1,z1610,z2,z7,z4,z5]),(0,[z1,z2,z1611,z7,z4,z5]),(0,[z1,z7,z4,z430,z14,z6]),(0,[z1,z9,z7,z4,z5,z424]),(0,[z1,z2,z7,z4,z5,z1612])],[(0,[z801,z34,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1613]),(0,[z1,z1614,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z38,z412])],[(0,[z1,z2,z7,z1615,z5,z6])],[(0,[z1616,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1617]),(0,[z1,z2,z7,z1618,z4,z5]),(0,[z1,z37,z2,z7,z4,z65]),(0,[z1619,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1620,z6])],[(0,[z1,z2,z7,z219,z5,z32]),(0,[z1621,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1622,z5])],[(0,[z1,z1623,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z240]),(0,[z1,z2,z308,z4,z137,z73])],[(1,[z1,z7,z4,z14,z73])],[(0,[z1,z7,z4,z393,z5,z354]),(0,[z1,z2,z7,z298,z51,z5])]],
   [[(0,[z1,z2,z303,z4,z44,z6]),(0,[z1,z2,z7,z4,z5,z1624]),(0,[z1,z2,z1625,z4,z5,z6]),(0,[z40,z1,z2,z7,z4,z312])],[(0,[z1,z2,z457,z4,z5,z10]),(0,[z1,z2,z7,z4,z38,z419])],[(0,[z1,z2,z7,z1536,z155,z5]),(0,[z1,z2,z7,z4,z632,z73]),(0,[z1,z2,z7,z4,z5,z1626]),(0,[z1,z255,z7,z4,z5,z14]),(1,[z1,z7,z178,z4,z14]),(0,[z1,z164,z7,z4,z312,z6]),(0,[z1,z2,z7,z1146,z5,z32])],[(0,[z1,z228,z7,z153,z4,z14]),(0,[z1,z2,z7,z4,z5,z350])],[(0,[z1,z2,z7,z4,z5,z1627]),(0,[z1,z1628,z2,z7,z4,z5])],[(0,[z1,z2,z1629,z4,z5,z6]),(0,[z92,z7,z4,z54,z14,z6]),(0,[z1,z2,z7,z4,z242,z32]),(0,[z1,z355,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z162,z5])],[],[],[(0,[z1,z2,z303,z4,z5,z77]),(1,[z1,z7,z4,z14,z147]),(0,[z1,z2,z7,z4,z5,z1630]),(0,[z1,z7,z4,z5,z317,z113])],[(0,[z1,z7,z4,z828,z5,z6]),(0,[z157,z1,z9,z7,z85,z6])],[(0,[z1,z37,z2,z380,z4,z5]),(0,[z1,z2,z166,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z975]),(0,[z1,z2,z7,z4,z5,z1631]),(0,[z1,z1632,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1633,z6]),(0,[z1,z9,z7,z47,z134,z5])],[(0,[z1,z2,z7,z4,z1634,z5]),(0,[z1573,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z47,z304,z5]),(0,[z2,z7,z4,z5,z716,z6]),(0,[z1,z2,z7,z4,z643,z73]),(0,[z1,z37,z268,z7,z4,z14]),(0,[z1,z359,z2,z7,z4,z280])],[(0,[z1,z1635,z7,z4,z5,z6]),(0,[z1,z2,z7,z219,z5,z73]),(0,[z36,z1,z2,z211,z80,z5]),(0,[z15,z1,z2,z4,z42,z73]),(0,[z1636,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z155,z5,z6]),(0,[z1,z2,z7,z4,z5,z1315]),(0,[z1,z30,z7,z4,z14,z10]),(0,[z1,z66,z7,z4,z5,z10])],[(0,[z1,z7,z4,z312,z14,z73])],[(0,[z2,z7,z656,z146,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1637]),(0,[z263,z2,z7,z146,z5,z32]),(0,[z1,z2,z7,z4,z5,z1638]),(0,[z1,z7,z4,z14,z42,z73])],[(0,[z1,z1639,z2,z7,z4,z5])],[(0,[z1,z9,z7,z4,z5,z400]),(0,[z1,z222,z7,z4,z5,z10])],[(0,[z1640,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z412,z184]),(0,[z1,z9,z7,z4,z38,z14]),(0,[z1,z477,z7,z4,z5,z113]),(0,[z271,z1,z2,z4,z5,z76])],[(0,[z1,z1201,z7,z4,z5,z14]),(0,[z1,z2,z7,z1641,z4,z5]),(0,[z1,z2,z7,z4,z5,z1642]),(0,[z1,z2,z7,z746,z5,z6])],[(0,[z1,z308,z4,z137,z14,z6]),(0,[z1,z7,z4,z464,z14,z6]),(0,[z1,z2,z7,z282,z245,z5])],[(0,[z1,z2,z7,z4,z5,z1643]),(0,[z1,z9,z7,z4,z5,z474]),(0,[z1,z2,z7,z4,z38,z312]),(0,[z1,z7,z4,z137,z204,z6])],[(0,[z1,z7,z4,z5,z1644,z6])],[(0,[z1,z2,z25,z4,z173,z5]),(0,[z1,z2,z7,z4,z1645,z6])],[(0,[z1,z2,z1263,z4,z5,z6]),(0,[z1,z2,z1646,z4,z5,z6]),(0,[z1,z2,z1083,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1647]),(0,[z1,z2,z7,z5,z739,z71])],[(0,[z1,z2,z7,z1648,z5,z6]),(0,[z1,z7,z4,z5,z1649,z6])],[(0,[z1,z2,z7,z4,z5,z1650]),(0,[z1,z2,z7,z4,z213,z49]),(0,[z1,z84,z938,z4,z5,z6]),(0,[z1,z7,z4,z5,z14,z275]),(0,[z1,z1300,z2,z7,z394,z5])],[(0,[z1,z2,z7,z4,z1651,z5]),(0,[z1,z2,z7,z4,z5,z1652]),(0,[z1,z7,z4,z643,z14,z6]),(0,[z1,z7,z4,z173,z5,z14]),(0,[z1,z2,z308,z4,z137,z10])]],
   [[(0,[z1,z2,z7,z253,z5,z73]),(0,[z1,z2,z7,z1653,z4,z5]),(0,[z536,z9,z7,z4,z5,z6]),(0,[z1,z2,z7,z212,z5,z593]),(0,[z1,z2,z369,z5,z85,z6])],[(0,[z1,z50,z7,z96,z5,z6]),(0,[z1,z9,z7,z4,z5,z269]),(0,[z271,z1,z7,z4,z14,z73]),(0,[z1,z309,z7,z4,z5,z446]),(0,[z1,z477,z7,z4,z254,z5])],[(0,[z1,z2,z7,z4,z5,z1654]),(0,[z556,z7,z4,z5,z14,z6]),(0,[z1411,z7,z4,z5,z14,z6]),(0,[z1,z697,z7,z4,z14,z6]),(0,[z1,z2,z7,z5,z906,z310])],[(0,[z1,z2,z7,z1017,z5,z73])],[(0,[z1,z2,z183,z4,z5,z1248]),(0,[z1,z2,z7,z1655,z4,z5]),(0,[z1,z1656,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z5,z513])],[(0,[z1,z41,z7,z547,z5,z6]),(0,[z1,z2,z7,z4,z5,z1657])],[(0,[z1,z7,z4,z14,z531,z73]),(0,[z1,z9,z7,z4,z312,z6]),(0,[z1,z2,z7,z4,z5,z1658])],[(0,[z1,z37,z2,z7,z4,z156])],[(0,[z1659,z2,z7,z4,z5,z6]),(0,[z1,z355,z7,z4,z5,z278])],[(0,[z1,z7,z47,z4,z5,z14]),(0,[z1,z1066,z2,z7,z162,z5]),(0,[z1660,z2,z7,z4,z5,z6]),(0,[z1,z2,z1646,z47,z4,z5])],[],[(0,[z1,z7,z427,z5,z14,z6]),(0,[z1,z2,z7,z47,z508,z5]),(0,[z1,z7,z4,z499,z14,z6]),(0,[z1,z7,z4,z14,z10,z73]),(0,[z1,z1661,z7,z4,z5,z6])],[(0,[z1,z7,z394,z5,z14,z6])],[(0,[z1,z37,z2,z7,z219,z5]),(0,[z48,z1,z130,z4,z38,z5]),(0,[z207,z1,z2,z80,z5,z6]),(0,[z1,z2,z7,z4,z5,z1392])],[(0,[z1,z2,z7,z4,z5,z1662]),(0,[z1,z7,z4,z393,z14,z73])],[(0,[z1,z2,z7,z4,z213,z32])],[(0,[z1,z1663,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z156,z73]),(0,[z1,z2,z7,z4,z5,z1664]),(0,[z1,z2,z194,z141,z4,z5]),(0,[z15,z1,z2,z4,z42,z10]),(0,[z328,z2,z7,z4,z5,z260])],[(0,[z1,z152,z7,z167,z5,z6])],[(0,[z1,z2,z7,z1665,z5,z6]),(0,[z634,z2,z7,z4,z5,z350]),(0,[z1,z2,z369,z4,z51,z6])],[(0,[z1,z2,z7,z1666,z5,z6]),(0,[z1,z2,z1667,z4,z5,z6]),(0,[z1,z417,z7,z4,z5,z14]),(0,[z1,z2,z7,z4,z5,z1668])],[(0,[z299,z2,z7,z146,z5,z6]),(0,[z581,z1,z2,z80,z5,z6]),(0,[z1,z7,z4,z14,z42,z10]),(0,[z634,z355,z7,z4,z5,z6]),(0,[z1,z2,z7,z141,z499,z6]),(0,[z1669,z2,z7,z4,z5,z6]),(0,[z1,z228,z2,z7,z4,z5])],[(0,[z1,z1670,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z1140,z6]),(0,[z107,z1,z7,z4,z5,z708])],[(0,[z1,z2,z7,z298,z146,z5]),(0,[z1,z2,z7,z18,z5,z240]),(0,[z1,z2,z7,z1671,z5,z6])],[(0,[z1672,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z14,z6,z651]),(0,[z271,z1,z9,z4,z5,z10]),(0,[z1,z2,z7,z298,z5,z71]),(0,[z157,z1,z2,z7,z85,z158])],[(0,[z1,z2,z7,z155,z44,z6]),(0,[z1,z2,z7,z4,z5,z1136]),(0,[z1,z37,z537,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1673,z5]),(0,[z1,z2,z7,z4,z5,z1674]),(0,[z1,z7,z4,z14,z6,z26])],[(0,[z1,z1236,z7,z4,z499,z6]),(0,[z397,z2,z369,z4,z5,z6])],[(0,[z1,z37,z2,z7,z304,z5]),(0,[z1,z1675,z2,z7,z4,z5]),(0,[z1,z7,z4,z191,z14,z73])],[(0,[z1,z2,z7,z1676,z4,z5])],[(0,[z1,z1677,z7,z4,z5,z6]),(0,[z1,z7,z4,z137,z14,z73]),(0,[z397,z7,z4,z5,z14,z6])],[(0,[z91,z152,z13,z4,z5,z6]),(0,[z1,z2,z7,z4,z412,z32]),(0,[z157,z1,z2,z7,z85,z443])],[(0,[z1,z2,z7,z219,z38,z5]),(0,[z1,z220,z7,z4,z242,z6]),(0,[z1,z506,z7,z4,z14,z6])]],
   [[(0,[z1,z2,z7,z155,z5,z77]),(0,[z2,z7,z13,z167,z5,z6]),(0,[z1,z2,z7,z1678,z4,z5]),(0,[z1,z7,z4,z14,z6,z55]),(0,[z1,z7,z4,z38,z5,z14]),(0,[z157,z1,z2,z7,z47,z85])],[(0,[z1,z2,z7,z4,z1679,z5]),(0,[z1,z7,z47,z4,z14,z419]),(0,[z468,z246,z2,z7,z4,z5])],[(0,[z1,z1680,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1681,z5])],[(0,[z1,z9,z7,z4,z5,z240]),(0,[z1,z2,z7,z1682,z5,z6]),(0,[z1,z37,z138,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1683,z5]),(0,[z1,z2,z7,z1684,z4,z5]),(0,[z1,z2,z7,z4,z412,z275]),(0,[z1,z7,z47,z153,z4,z14]),(0,[z1685,z2,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z38])],[],[(0,[z1,z2,z7,z4,z5,z310]),(0,[z1,z2,z7,z4,z5,z353]),(0,[z1,z228,z2,z7,z178,z5])],[(0,[z48,z1,z938,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1686]),(0,[z1,z2,z7,z4,z5,z1687]),(0,[z1,z2,z7,z4,z38,z65]),(0,[z1,z2,z7,z4,z67,z419])],[(0,[z1,z2,z7,z4,z5,z296]),(0,[z1,z138,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z300,z6]),(0,[z1,z2,z7,z874,z5,z42]),(0,[z1,z7,z47,z4,z5,z104])],[(0,[z1,z2,z1688,z7,z4,z5]),(0,[z1,z37,z2,z7,z601,z5])],[(0,[z1,z2,z7,z4,z5,z1689]),(0,[z1,z9,z7,z763,z5,z6]),(0,[z1,z2,z256,z4,z5,z6]),(0,[z1,z1690,z7,z4,z5,z6])],[(0,[z1,z355,z7,z4,z5,z32]),(0,[z1,z1691,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1692]),(0,[z1,z2,z7,z4,z1576,z10]),(0,[z157,z397,z2,z7,z85,z6])],[(0,[z434,z2,z7,z4,z5,z6]),(0,[z1,z97,z7,z4,z5,z6]),(0,[z1,z435,z2,z7,z4,z5])],[(0,[z1,z2,z7,z1693,z4,z5]),(0,[z1,z7,z4,z5,z14,z365]),(0,[z1,z7,z4,z242,z14,z6]),(0,[z1,z938,z130,z4,z5,z6]),(0,[z1,z37,z115,z7,z4,z5])],[(0,[z1,z2,z308,z4,z137,z197])],[(0,[z1,z2,z7,z47,z427,z5]),(0,[z2,z183,z4,z5,z111,z6])],[(0,[z1,z2,z7,z4,z5,z1694]),(0,[z1,z2,z7,z253,z38,z5])],[(0,[z1,z2,z7,z4,z156,z10]),(0,[z1,z25,z4,z14,z42,z6]),(0,[z1,z9,z7,z4,z5,z1389])],[(0,[z1,z87,z7,z4,z5,z296]),(0,[z1,z220,z7,z4,z14,z6]),(0,[z1,z37,z9,z7,z4,z132])],[(0,[z1,z2,z7,z47,z175,z5]),(0,[z1,z7,z4,z5,z1261,z6]),(0,[z1,z37,z7,z47,z5,z14]),(0,[z1,z9,z7,z772,z5,z6])],[(0,[z33,z631,z7,z4,z5,z6]),(0,[z1,z50,z7,z828,z5,z6]),(0,[z1,z2,z369,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1695])],[(0,[z1,z2,z7,z4,z5,z1696]),(0,[z1,z2,z7,z4,z5,z1023]),(0,[z489,z1,z2,z7,z85,z6]),(0,[z1,z1697,z7,z4,z5,z6])],[(0,[z1,z9,z7,z4,z703,z6]),(0,[z634,z2,z7,z80,z5,z6]),(0,[z1,z37,z66,z7,z4,z5])],[(0,[z1,z7,z4,z5,z14,z6]),(0,[z1,z60,z7,z4,z14,z6]),(0,[z1,z20,z7,z4,z14,z73])],[(0,[z1,z2,z7,z4,z5,z1698]),(0,[z1,z7,z4,z38,z54,z14])],[(0,[z1,z2,z7,z4,z1699,z6]),(0,[z1,z2,z7,z4,z5,z1700]),(0,[z157,z1,z2,z369,z85,z6])],[(0,[z1,z2,z7,z4,z5,z1701]),(0,[z1,z392,z7,z18,z5,z6]),(0,[z1,z9,z7,z4,z280,z5])],[(0,[z1,z7,z4,z110,z14,z6]),(0,[z107,z1,z7,z4,z233,z5]),(0,[z1,z163,z7,z4,z5,z113]),(0,[z1,z2,z467,z4,z137,z6])],[(0,[z1,z2,z7,z4,z1164,z5]),(0,[z1,z2,z7,z47,z4,z39]),(0,[z1,z7,z4,z14,z133,z6])],[(0,[z1,z2,z7,z47,z480,z5]),(0,[z1,z308,z4,z137,z104,z6]),(0,[z1,z2,z7,z4,z5,z1702])],[(0,[z1,z2,z7,z4,z1703,z6]),(0,[z1,z7,z4,z137,z14,z10]),(0,[z1,z7,z4,z38,z5,z104])]],
   [[(0,[z1,z259,z7,z4,z202,z6]),(0,[z1,z2,z1704,z7,z4,z5]),(0,[z1,z37,z7,z4,z111,z14])],[(0,[z1,z7,z167,z5,z14,z6]),(0,[z1,z115,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1705]),(0,[z1,z433,z7,z4,z14,z6]),(0,[z1,z2,z194,z4,z5,z42])],[(0,[z1,z303,z4,z5,z14,z6]),(0,[z1,z2,z7,z4,z5,z1706]),(0,[z1,z129,z938,z4,z5,z6]),(0,[z1,z2,z369,z47,z4,z5])],[(0,[z1707,z2,z7,z4,z5,z6]),(0,[z1,z9,z7,z1407,z5,z6]),(0,[z1,z2,z7,z4,z5,z1708])],[(0,[z0,z34,z7,z4,z5,z6]),(0,[z92,z2,z7,z47,z146,z5]),(0,[z1,z21,z4,z14,z42,z6])],[(0,[z1,z2,z7,z4,z5,z1709]),(0,[z1,z20,z7,z4,z5,z113])],[(0,[z1,z2,z7,z155,z5,z73]),(0,[z1,z1710,z7,z4,z5,z6]),(0,[z1,z2,z1144,z4,z5,z6])],[(0,[z1,z1578,z7,z4,z156,z6]),(0,[z1,z540,z130,z4,z5,z6]),(0,[z556,z9,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1711]),(0,[z1,z2,z7,z4,z5,z1712]),(1,[z1,z2,z978,z5,z6])],[(0,[z1,z2,z1713,z4,z5,z6]),(0,[z1,z2,z7,z1120,z4,z5]),(0,[z1,z7,z4,z1035,z14,z6]),(0,[z1,z2,z21,z141,z5,z22]),(0,[z1,z2,z4,z5,z10,z32])],[(0,[z1,z37,z2,z7,z5,z538])],[(0,[z1,z2,z7,z4,z5,z1714]),(0,[z1715,z1,z2,z7,z4,z5]),(0,[z1,z7,z4,z5,z14,z55]),(0,[z1,z965,z7,z4,z5,z6]),(0,[z1,z9,z7,z4,z5,z1412])],[(0,[z1,z2,z1716,z4,z5,z6]),(0,[z1,z2,z7,z4,z1717,z6]),(0,[z1,z2,z7,z4,z5,z1718]),(0,[z1,z7,z95,z4,z171,z6]),(0,[z549,z1,z2,z4,z5,z10])],[(0,[z1,z2,z7,z4,z12,z73]),(0,[z1,z1068,z7,z4,z5,z6]),(0,[z540,z9,z7,z4,z5,z6])],[(0,[z1,z2,z7,z1719,z4,z5]),(0,[z24,z2,z25,z4,z5,z32]),(0,[z540,z7,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1720]),(0,[z1,z2,z7,z4,z5,z1721])],[(0,[z1,z1722,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1723]),(0,[z1,z50,z7,z579,z96,z5]),(0,[z157,z1,z2,z7,z4,z326]),(0,[z1669,z37,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1724,z6]),(0,[z1,z7,z4,z5,z1725,z6]),(0,[z1,z359,z7,z4,z14,z6])],[(0,[z62,z1,z7,z4,z14,z73])],[(0,[z1,z2,z303,z4,z5,z192]),(0,[z0,z34,z7,z47,z4,z5]),(0,[z1,z1726,z7,z4,z5,z6]),(0,[z1,z2,z7,z307,z5,z126]),(0,[z1,z2,z7,z4,z5,z1727]),(0,[z1,z2,z7,z4,z5,z1213]),(0,[z15,z1,z2,z288,z4,z42]),(0,[z1,z2,z7,z178,z5,z216])],[(0,[z1,z2,z7,z4,z38,z156]),(0,[z1,z2,z7,z1728,z4,z5])],[(0,[z1,z7,z178,z4,z5,z14])],[(0,[z1,z9,z7,z4,z38,z73]),(0,[z1,z37,z722,z7,z4,z5])],[(0,[z1,z341,z7,z18,z5,z6]),(0,[z1,z2,z7,z1729,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1730]),(0,[z1731,z2,z7,z4,z5,z6]),(0,[z526,z1,z2,z7,z85,z6]),(0,[z1,z2,z7,z47,z245,z5])],[(0,[z1,z50,z7,z96,z5,z73])],[(0,[z0,z186,z34,z7,z4,z5]),(0,[z1,z2,z1732,z7,z4,z5]),(0,[z1,z2,z609,z4,z5,z32])],[(0,[z1,z2,z7,z4,z202,z1316]),(0,[z1,z2,z7,z4,z736,z73]),(0,[z1,z343,z7,z4,z542,z5])],[(0,[z1,z2,z7,z1733,z4,z5]),(0,[z1,z7,z47,z4,z430,z14]),(0,[z1,z7,z47,z5,z14,z71]),(0,[z1,z2,z7,z1734,z5,z6])],[],[(0,[z1,z37,z2,z7,z427,z5]),(0,[z1,z1735,z7,z4,z5,z6]),(0,[z1,z7,z4,z65,z1470,z6]),(0,[z1,z2,z7,z4,z42,z419])],[(0,[z1,z2,z1736,z4,z5,z6]),(0,[z1,z2,z7,z47,z167,z5]),(0,[z1,z2,z7,z4,z532,z73]),(0,[z1,z417,z2,z7,z4,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 32 1024 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 455) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 915).take 445) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1360).take 446) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1806)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 455, 445, 446] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 96).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 216).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 339).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 453).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 559).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 669).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 784).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc8 : chunkOK 5 ((bkB.flatten.drop 890).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc9 : chunkOK 5 ((bkB.flatten.drop 1007).take 17).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 1024)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [96, 120, 123, 114, 106, 110, 115, 106, 117, 17] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_cons pc8 (windowsF_cons pc9 (windowsF_nil pcend))))))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 32) (nb2 := 1024) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38087

theorem PEqualNP.Outside.L_meta_38087 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277075624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277075624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38087.solve