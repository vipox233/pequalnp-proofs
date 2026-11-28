import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36260

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2000030a81856630#64 ++ 0x42000030a8185663#64 ++ 0xd0288f1f838fe67d#64 ++ 0xfd0288f1f838fe67#64 : BitVec 256),
   (0x444349660cb33858#64 ++ 0x1444349660cb3385#64 ++ 0xbcd749e61cf3387b#64 ++ 0x7bcd749e61cf3387#64 : BitVec 256),
   (0x811811b820dc2a81#64 ++ 0x1811811b820dc2a8#64 ++ 0x771871f860fc3f87#64 ++ 0xd771871f860fc3f8#64 : BitVec 256),
   (0x02e06e0057001562#64 ++ 0x602e06e005700156#64 ++ 0xf3e07e007f003fff#64 ++ 0xcf3e07e007f003ff#64 : BitVec 256),
   (0x03bd80007a6a8003#64 ++ 0x803bd80007a6a800#64 ++ 0xfbff80007fffc00f#64 ++ 0x3fbff80007fffc00#64 : BitVec 256),
   (0x03fefcd50000000c#64 ++ 0x003fefcd50000000#64 ++ 0xffffffff80000000#64 ++ 0xfffffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00406e0005001560 0x600406e000500156 0x00007e0000003ff0 0xc00007e0000003ff

def z1 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0x081f800000ffc000 0x3081f800000ffc00

def z2 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07e007f003fff 0xcf3e07e007f003ff

def z3 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80000000 0xfffffffff8000000

def z4 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288f1f838fe67d 0xfd0288f1f838fe67

def z5 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e61cf3387b 0x7bcd749e61cf3387

def z6 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771871f860fc3f87 0xd771871f860fc3f8

def z7 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff80007fffc00f 0x3fbff80007fffc00

def z8 : W := mkw 0x03fffcd5286a800d 0x803fffcd5286a800 0xffffffff80ffc000 0xfffffffff80ffc00

def z9 : W := mkw 0x444348460c231058 0x0444348460c23105 0x88c708061c030078 0x288c708061c03007

def z10 : W := mkw 0x46e36f665fb33d7a 0x746e36f665fb33d7 0xfff77fe67ff33fff 0xffff77fe67ff33ff

def z11 : W := mkw 0x83bd91b87afeaa83 0x983bd91b87afeaa8 0x7fdf71f87cfc3f87 0xd7fdf71f87cfc3f8

def z12 : W := mkw 0x82e07fb857943fe2 0x782e07fb857943fe 0xf7e07ff87f003fff 0xcf7e07ff87f003ff

def z13 : W := mkw 0xc44359fe0cb73ad8 0x1c44359fe0cb73ad 0xbcd779fe1cf33ffb 0xfbcd779fe1cf33ff

def z14 : W := mkw 0x80000008204c0281 0x080000008204c028 0x00000000600c0784 0x000000000600c078

def z15 : W := mkw 0x03fefed55700156e 0x603fefed55700156 0xffffffffff003fff 0xfffffffffff003ff

def z16 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x00000000038fe67d 0x000000000038fe67

def z17 : W := mkw 0x4401012208b32810 0x14401012208b3281 0x0000000000f30000 0x00000000000f3000

def z18 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0x8ce7ffff80000000 0xe8ce7ffff8000000

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x4028861980000000 0x8402886198000000

def z20 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x80208e07838fe67d 0x280208e07838fe67

def z21 : W := mkw 0x03bc800020480001 0x003bc80002048000 0xfbff800060fc0007 0x3fbff800060fc000

def z22 : W := mkw 0x81181098204c0281 0x081181098204c028 0x43083018600c0784 0x843083018600c078

def z23 : W := mkw 0x811810b020580881 0x1811810b02058088 0x271070e060701982 0x0271070e06070198

def z24 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xcbefbe1f80000000 0xacbefbe1f8000000

def z25 : W := mkw 0x0040480004001040 0x0004048000400104 0xf3c078007c003fff 0xcf3c078007c003ff

def z26 : W := mkw 0xc55b59fe2cff3ad9 0x1c55b59fe2cff3ad 0xffdf79fe7cff3fff 0xfffdf79fe7cff3ff

def z27 : W := mkw 0x02a0260053000522 0x602a026005300052 0x4320360063000784 0x8432036006300078

def z28 : W := mkw 0x64434b6e8db77e78 0x564434b6e8db77e7 0xfcffcfff9ffffe7f 0xffcffcfff9ffffe7

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000000000830009 0x3900000000083000

def z30 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e00e007f00007f 0x0f3e00e007f00007

def z31 : W := mkw 0x0118109000000000 0x0011810900000000 0x771871f800000000 0xd771871f80000000

def z32 : W := mkw 0x83fefdfd20dc2a8d 0x183fefdfd20dc2a8 0xffffffffe0fc3f87 0xfffffffffe0fc3f8

def z33 : W := mkw 0x03bc800072488003 0x803bc80007248800 0x7338800063fcc007 0x17338800063fcc00

def z34 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x88ff80001fffc008 0x388ff80001fffc00

def z35 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x040049e61cf3387b 0x4040049e61cf3387

def z36 : W := mkw 0x0001000008220000 0x0000100000822000 0xb8d700001cf3000b 0x3b8d700001cf3000

def z37 : W := mkw 0x03fffcd57a6a800f 0x803fffcd57a6a800 0xffffffffffffc00f 0xfffffffffffffc00

def z38 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x2bd700007c700002 0x02bd700007c70000

def z39 : W := mkw 0x23bd830afbefe633 0xc23bd830afbefe63 0xfbff8f1fffffe67f 0xffbff8f1fffffe67

def z40 : W := mkw 0x2001030afbefe633 0xc2001030afbefe63 0x000000007fffe67f 0x0000000007fffe67

def z41 : W := mkw 0x440101220cb33850 0x1440101220cb3385 0x000000001cf3387b 0x0000000001cf3387

def z42 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x0000000060fc3f87 0x00000000060fc3f8

def z43 : W := mkw 0x2000030ad7857772 0x62000030ad785777 0x000000007f8fffff 0x0000000007f8ffff

def z44 : W := mkw 0x46e7c9665eb3b85a 0x946e7c9665eb3b85 0xbcf7c9e61ff3f87b 0x7bcf7c9e61ff3f87

def z45 : W := mkw 0x83bd90987a6e8283 0x883bd90987a6e828 0xfbffb0187fffc78f 0xbfbffb0187fffc78

def z46 : W := mkw 0x811810b020580881 0x1811810b02058088 0x041000e000700000 0x0041000e00070000

def z47 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x8cff8fff80000000 0x38cff8fff8000000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x7300700060003f87 0xc7300700060003f8

def z49 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x8cd709e61cf30078 0x38cd709e61cf3007

def z50 : W := mkw 0x0118000020480001 0x0011800002048000 0x7318000060fc0007 0x17318000060fc000

def z51 : W := mkw 0x83bd91b87afeaa83 0x983bd91b87afeaa8 0xfffff1f87fffff8f 0xffffff1f87fffff8

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0288f1f80000000 0xfd0288f1f8000000

def z53 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x23c070007f003fff 0x023c070007f003ff

def z54 : W := mkw 0x46e7ed670cb3385c 0x146e7ed670cb3385 0xbcf7cfe79cf3387b 0x7bcf7cfe79cf3387

def z55 : W := mkw 0x02e06f0257813572 0x602e06f025781357 0xf3e07f067f833fff 0xff3e07f067f833ff

def z56 : W := mkw 0x03fefed50100042c 0x403fefed50100042 0xffffffff8300267d 0xfffffffff8300267

def z57 : W := mkw 0x4402016600912818 0x1440201660091281 0x040001e600000000 0x0040001e60000000

def z58 : W := mkw 0x0000260001000520 0x6000026000100052 0x0000360000000780 0x8000036000000078

def z59 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0x2fd770e07c001982 0x02fd770e07c00198

def z60 : W := mkw 0x03bcb69153000526 0x603bcb6915300052 0x4328b619e3000784 0x84328b619e300078

def z61 : W := mkw 0x444349667efbb85b 0x9444349667efbb85 0xbcd749e67ffff87f 0x7bcd749e67ffff87

def z62 : W := mkw 0x811810b020580881 0x1811810b02058088 0x771870e060fc1987 0x1771870e060fc198

def z63 : W := mkw 0x2118030aa1cd6631 0x42118030aa1cd663 0xf3388f1fe3ffe67f 0xff3388f1fe3ffe67

def z64 : W := mkw 0x03bc800000000000 0x003bc80000000000 0xfbff8000038fc00d 0x3fbff8000038fc00

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0xd02000000300000d 0x0d02000000300000

def z66 : W := mkw 0x444149220cb33850 0x1444149220cb3385 0xb0c048001cf3387b 0x4b0c048001cf3387

def z67 : W := mkw 0x8118109020480081 0x0811810902048008 0x0300300060000180 0x0030030006000018

def z68 : W := mkw 0x02e06f2057903d62 0x702e06f2057903d6 0xf7f07fe07ff03fff 0xdf7f07fe07ff03ff

def z69 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x0c1f81ff80000000 0x30c1f81ff8000000

def z70 : W := mkw 0x03fefed55300052e 0x603fefed55300052 0xffffffffe3000784 0xfffffffffe300078

def z71 : W := mkw 0x0001000008220000 0x0000100000822000 0x000000001cf3000b 0x0000000001cf3000

def z72 : W := mkw 0x0001010208a32010 0x00001010208a3201 0xb8d709061cf3207b 0x7b8d709061cf3207

def z73 : W := mkw 0x03bcb49100000004 0x003bcb4910000000 0xfbffb61980000000 0xbfbffb6198000000

def z74 : W := mkw 0x811810b020580881 0x1811810b02058088 0x771871f860701982 0xd771871f86070198

def z75 : W := mkw 0x015a58d400000008 0x0015a58d40000000 0xffdf79fe00000000 0xfffdf79fe0000000

def z76 : W := mkw 0x22e06f0ad7857772 0x622e06f0ad785777 0xf3e8ff1fff8fffff 0xff3e8ff1fff8ffff

def z77 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x00000f1f80002670 0xc00000f1f8000267

def z78 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0xbcd77fff80000000 0xfbcd77fff8000000

def z79 : W := mkw 0x03bc800072488003 0x803bc80007248800 0x43288000630cc004 0x043288000630cc00

def z80 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0x041881ff80ffc000 0x3041881ff80ffc00

def z81 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x7fdf71f800000000 0xd7fdf71f80000000

def z82 : W := mkw 0x2000020a81054630 0x42000020a8105463 0xc0288e1f830fc67c 0xac0288e1f830fc67

def z83 : W := mkw 0x0000012000902800 0x1000001200090280 0x341041e000f03803 0x5341041e000f0380

def z84 : W := mkw 0x0000030801842620 0x4000003080184262 0xd0280f18038c267d 0xdd0280f18038c267

def z85 : W := mkw 0x455b49662cfb3859 0x1455b49662cfb385 0xffdf49e67cff387f 0x7ffdf49e67cff387

def z86 : W := mkw 0x02a580005a228002 0x802a580005a22800 0x88e780001f03c008 0x288e780001f03c00

def z87 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x040071f800003f80 0xc040071f800003f8

def z88 : W := mkw 0x03feec450000000c 0x003feec450000000 0xfbff8e0780000000 0x3fbff8e078000000

def z89 : W := mkw 0xa000032aa1dd6eb1 0x5a000032aa1dd6eb 0xd0288f1fe3ffffff 0xfd0288f1fe3fffff

def z90 : W := mkw 0x00406c0004001140 0x200406c000400114 0x0000700000001980 0x0000070000000198

def z91 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0x88e78e0780000000 0x288e78e078000000

def z92 : W := mkw 0x03bca60073488523 0xe03bca6007348852 0x4328b600630cc784 0x84328b600630cc78

def z93 : W := mkw 0x00426c450000000c 0x000426c450000000 0x00000e0780000000 0x000000e078000000

def z94 : W := mkw 0xa3f87fbaf7dd7ff3 0x7a3f87fbaf7dd7ff 0xf7f8ffffffffffff 0xff7f8fffffffffff

def z95 : W := mkw 0x2000010a80856210 0x02000010a8085621 0x0008811f808fc000 0x30008811f808fc00

def z96 : W := mkw 0x2000020281014430 0x4200002028101443 0x80208e078303c078 0x280208e078303c07

def z97 : W := mkw 0x02e06c0052000002 0x002e06c005200000 0xf3e07e007f00000f 0xcf3e07e007f00000

def z98 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff838fc00d 0xfffffffff838fc00

def z99 : W := mkw 0xc51b11fe28ff2a99 0x1c51b11fe28ff2a9 0x0c1f01fe00ff0000 0x30c1f01fe00ff000

def z100 : W := mkw 0x00010000286a8001 0x800010000286a800 0x0000000000ffc000 0x00000000000ffc00

def z101 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0x000000007fffc00f 0x0000000007fffc00

def z102 : W := mkw 0x2000020881044620 0x4200002088104462 0xd0288619838fc60d 0xbd0288619838fc60

def z103 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x4028871f838fc604 0xb4028871f838fc60

def z104 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x2fd770e000000000 0x02fd770e00000000

def z105 : W := mkw 0x8000032877dc3fe3 0x78000032877dc3fe 0x000000007ffc3fff 0x0000000007ffc3ff

def z106 : W := mkw 0x2000020881044620 0x4200002088104462 0xd0288f1f830cc604 0xfd0288f1f830cc60

def z107 : W := mkw 0x440100020c231050 0x0440100020c23105 0x000000001c030078 0x0000000001c03007

def z108 : W := mkw 0xc55b58f42c7a18c9 0x1c55b58f42c7a18c 0x2fd770e07c701982 0x02fd770e07c70198

def z109 : W := mkw 0x03fcee0057001562 0x603fcee005700156 0xfbfffe007f003fff 0xffbfffe007f003ff

def z110 : W := mkw 0x22e6ee478101443c 0x422e6ee478101443 0x88e78e078303c078 0x288e78e078303c07

def z111 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x341041e060fc3f87 0x5341041e060fc3f8

def z112 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x041801f800fc0000 0x1041801f800fc000

def z113 : W := mkw 0x23feffdf8185663c 0x423feffdf8185663 0xffffffff838fe67d 0xfffffffff838fe67

def z114 : W := mkw 0x4403006408320808 0x1440300640832080 0x0c1700e000700000 0x00c1700e00070000

def z115 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0xdc3f8fff80000000 0xfdc3f8fff8000000

def z116 : W := mkw 0x2000020881044620 0x4200002088104462 0x40288619830cc604 0x840288619830cc60

def z117 : W := mkw 0x444348640c321848 0x1444348640c32184 0x2cd740e01c701802 0x02cd740e01c70180

def z118 : W := mkw 0x47fffcf50c32184c 0x147fffcf50c32184 0xffffffff9c701802 0xfffffffff9c70180

def z119 : W := mkw 0x811d91b828feaa81 0x9811d91b828feaa8 0x7f1ff1f860ffff87 0xf7f1ff1f860ffff8

def z120 : W := mkw 0x2001030afbefe633 0xc2001030afbefe63 0xd0288f1fffffe67f 0xfd0288f1fffffe67

def z121 : W := mkw 0x67ffcb6efffffe7b 0xd67ffcb6efffffe7 0xffffcffffffffe7f 0xfffffcffffffffe7

def z122 : W := mkw 0xa3bd93bafbffeeb3 0xda3bd93bafbffeeb 0xffffffffffffffff 0xffffffffffffffff

def z123 : W := mkw 0x0000000200010010 0x0000000020001001 0x8000080600030078 0x2800008060003007

def z124 : W := mkw 0x64424b6e85957e78 0x564424b6e85957e7 0x04004fff80003e70 0xc04004fff80003e7

def z125 : W := mkw 0x004148000c221040 0x0004148000c22104 0xb8d748001cf3387b 0x7b8d748001cf3387

def z126 : W := mkw 0x2000030ad7857772 0x62000030ad785777 0xd0288f1fff8fffff 0xfd0288f1fff8ffff

def z127 : W := mkw 0x0000020057001562 0x6000002005700156 0x000000007f003fff 0x0000000007f003ff

def z128 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x4728ffff80000000 0xc4728ffff8000000

def z129 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0xd8ef8f1f80000000 0xfd8ef8f1f8000000

def z130 : W := mkw 0x80407fb805943fe0 0x780407fb805943fe 0x04007ff800003ff0 0xc04007ff800003ff

def z131 : W := mkw 0x0000012000902800 0x1000001200090280 0x040041e000003800 0x4040041e00000380

def z132 : W := mkw 0x83fefcdd204c028d 0x083fefcdd204c028 0xffffffffe00c0784 0xfffffffffe00c078

def z133 : W := mkw 0x00406e0005001560 0x600406e000500156 0x00000e0000000070 0x000000e000000007

def z134 : W := mkw 0x4442496604913858 0x1444249660491385 0x040049e600003870 0x4040049e60000387

def z135 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xd0e00e001f00267d 0xcd0e00e001f00267

def z136 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0x04007fff80000000 0xc04007fff8000000

def z137 : W := mkw 0x22a58202db23c432 0xc22a58202db23c43 0x88e78e079f03c078 0x288e78e079f03c07

def z138 : W := mkw 0x03bc800072488003 0x803bc80007248800 0xfbff8000630cc004 0x3fbff8000630cc00

def z139 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xfffff1f87fffc00f 0xffffff1f87fffc00

def z140 : W := mkw 0x03bcb49100000004 0x003bcb4910000000 0x7738f7f980000000 0xd7738f7f98000000

def z141 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffffe0fc0007 0xfffffffffe0fc000

def z142 : W := mkw 0x811811b020d82881 0x1811811b020d8288 0x371071e060f03983 0x5371071e060f0398

def z143 : W := mkw 0x0000000020480001 0x0000000002048000 0x0000000060fc0007 0x00000000060fc000

def z144 : W := mkw 0x47fffdf70cb3385c 0x147fffdf70cb3385 0xffffffff9cf3387b 0xfffffffff9cf3387

def z145 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xfcdf49fe1cff3e7f 0xffcdf49fe1cff3e7

def z146 : W := mkw 0x20404b0a85857670 0x420404b0a8585767 0xf0e8cf1f9f8ffe7f 0xff0e8cf1f9f8ffe7

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8d7000000000000 0x3b8d700000000000

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0288000038fc00d 0x3d0288000038fc00

def z149 : W := mkw 0x0042484400000008 0x0004248440000000 0xbcd749e600000000 0x7bcd749e60000000

def z150 : W := mkw 0x6401032a8db77e70 0x56401032a8db77e7 0x000000001ffffe7f 0x0000000001ffffe7

def z151 : W := mkw 0x0000010200812010 0x0000001020081201 0x0000010600830000 0x3000001060083000

def z152 : W := mkw 0x47ffc9667efbb85b 0x947ffc9667efbb85 0xffffc9e67ffff87f 0x7ffffc9e67ffff87

def z153 : W := mkw 0xa11813baa1dd6eb1 0x5a11813baa1dd6eb 0xf738ffffe3ffffff 0xff738ffffe3fffff

def z154 : W := mkw 0x03fefcd50400104c 0x003fefcd50400104 0xffffffff9c00387b 0xfffffffff9c00387

def z155 : W := mkw 0x02a0260057001562 0x602a026005700156 0x432036007f003fff 0x8432036007f003ff

def z156 : W := mkw 0x02e6ee455700156e 0x602e6ee455700156 0xfbe7fe07ff003fff 0xefbe7fe07ff003ff

def z157 : W := mkw 0x22e6ef4f8185663c 0x422e6ef4f8185663 0xd8ef8f1f838fe67d 0xfd8ef8f1f838fe67

def z158 : W := mkw 0x02a0000052000002 0x002a000005200000 0xf3e000007f00000f 0x0f3e000007f00000

def z159 : W := mkw 0x0000010800842200 0x0000001080084220 0xd0288118038fe60d 0xfd0288118038fe60

def z160 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf328ff1fe38fffff 0xff328ff1fe38ffff

def z161 : W := mkw 0x011f90d5286a800d 0x8011f90d5286a800 0x0c1f81ff80ffc000 0x30c1f81ff80ffc00

def z162 : W := mkw 0x0002004400000008 0x0000200440000000 0x0c1701e600000000 0x30c1701e60000000

def z163 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0xf3e07e007c001982 0xcf3e07e007c00198

def z164 : W := mkw 0x0000010200812010 0x0000001020081201 0xd0288f1f80832079 0xfd0288f1f8083207

def z165 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xc3e03e007f0007fc 0x8c3e03e007f0007f

def z166 : W := mkw 0x02e5ee005f229562 0xe02e5ee005f22956 0x88e78e001f03c078 0x288e78e001f03c07

def z167 : W := mkw 0x0118012020d82801 0x10118012020d8280 0x771841e060fc3807 0x5771841e060fc380

def z168 : W := mkw 0x2000020281014430 0x4200002028101443 0x000000000303c078 0x0000000000303c07

def z169 : W := mkw 0x44434b660db33c78 0x544434b660db33c7 0xfcf74fe61ff33e7f 0xffcf74fe61ff33e7

def z170 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0xb3c078007c0039fb 0x4b3c078007c0039f

def z171 : W := mkw 0x0000010800842200 0x0000001080084220 0x50080118008c2605 0xd50080118008c260

def z172 : W := mkw 0xc401012a2cff3ad1 0x1c401012a2cff3ad 0x000000007cff3fff 0x0000000007cff3ff

def z173 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0x23c070007c001982 0x023c070007c00198

def z174 : W := mkw 0x03fdec007e6a9143 0xa03fdec007e6a914 0xfbfff0007fffd98f 0x3fbfff0007fffd98

def z175 : W := mkw 0x22a5830adba7e632 0xc22a5830adba7e63 0xd8ef8f1f9f8fe67d 0xfd8ef8f1f9f8fe67

def z176 : W := mkw 0x0042484400000008 0x0004248440000000 0xfcffcfff80000000 0xffcffcfff8000000

def z177 : W := mkw 0x23fefedd8104462c 0x423fefedd8104462 0xffffffff830cc604 0xfffffffff830cc60

def z178 : W := mkw 0x03fdec007e6a9143 0xa03fdec007e6a914 0x2bd770007c701982 0x02bd770007c70198

def z179 : W := mkw 0x00406c0000000000 0x000406c000000000 0x00007e0000000000 0xc00007e000000000

def z180 : W := mkw 0x2000010a80856210 0x02000010a8085621 0xd028811f838fc00d 0x3d028811f838fc00

def z181 : W := mkw 0x0000000004001040 0x0000000000400104 0x000000001c00387b 0x0000000001c00387

def z182 : W := mkw 0x81181098204c0281 0x081181098204c028 0x00080018000c0000 0x000080018000c000

def z183 : W := mkw 0x03fffcd57a6a800f 0x803fffcd57a6a800 0x2fd770e07c700002 0x02fd770e07c70000

def z184 : W := mkw 0xc7ffd9fe7effbadb 0x9c7ffd9fe7effbad 0xfffff9fe7fffffff 0xffffff9fe7ffffff

def z185 : W := mkw 0x0118000020480001 0x0011800002048000 0xf338800063ffc00f 0x3f338800063ffc00

def z186 : W := mkw 0x02e06c0000000000 0x002e06c000000000 0xf3e07e0000000000 0xcf3e07e000000000

def z187 : W := mkw 0x444348660c331858 0x1444348660c33185 0xacd748e61c73187a 0x2acd748e61c73187

def z188 : W := mkw 0x211e93df8185663c 0x4211e93df8185663 0xdc3f8fff838fe67d 0xfdc3f8fff838fe67

def z189 : W := mkw 0x02a580005a228002 0x802a580005a22800 0xfbe780007f03c00f 0x2fbe780007f03c00

def z190 : W := mkw 0x47fefdf70491385c 0x147fefdf70491385 0xffffffff80003870 0xfffffffff8000387

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0288f1f838fc00d 0xfd0288f1f838fc00

def z192 : W := mkw 0x02a0020057001562 0x602a002005700156 0xf3e000007f003fff 0x0f3e000007f003ff

def z193 : W := mkw 0x8118012820dc2a81 0x18118012820dc2a8 0x7318000060fc3f87 0x17318000060fc3f8

def z194 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x2bd700007fffc00f 0x02bd700007fffc00

def z195 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x50080118038fe67d 0xd50080118038fe67

def z196 : W := mkw 0x03bc800000000000 0x003bc80000000000 0xfbff800000000000 0x3fbff80000000000

def z197 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xbfd779e600000000 0x7bfd779e60000000

def z198 : W := mkw 0x2000032a81956e30 0x52000032a81956e3 0xf438cfff83fffe7f 0xff438cfff83fffe7

def z199 : W := mkw 0x0000020001000420 0x4000002000100042 0x4020060003000604 0x8402006000300060

def z200 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xbcdfc9ff9cfff87b 0x7bcdfc9ff9cfff87

def z201 : W := mkw 0x03bcb49100000004 0x003bcb4910000000 0x4328b61980000000 0x84328b6198000000

def z202 : W := mkw 0x03bdb4917a6a8007 0x803bdb4917a6a800 0xfbffb619ffffc00f 0xbfbffb619ffffc00

def z203 : W := mkw 0x0118109000000000 0x0011810900000000 0x771871f860003f87 0xd771871f860003f8

def z204 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x80e00e001f000078 0x080e00e001f00007

def z205 : W := mkw 0x03f86e0077481563 0x603f86e007748156 0xf3f87e007ffc3fff 0xdf3f87e007ffc3ff

def z206 : W := mkw 0x0040480004001040 0x0004048000400104 0xb0c048001c00387b 0x4b0c048001c00387

def z207 : W := mkw 0x2000010a80856210 0x02000010a8085621 0x9008891f808fe079 0x79008891f808fe07

def z208 : W := mkw 0x83f87fb877dc3fe3 0x783f87fb877dc3fe 0xf7f87ff87ffc3fff 0xdf7f87ff87ffc3ff

def z209 : W := mkw 0x03fefed55700156e 0x603fefed55700156 0xffffffff9f000078 0xfffffffff9f00007

def z210 : W := mkw 0x64434a468d235478 0x464434a468d23547 0x88e78e079f03c078 0x288e78e079f03c07

def z211 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x0c1749e600f33870 0x70c1749e600f3387

def z212 : W := mkw 0x0000020001000420 0x4000002000100042 0x000000000300267d 0x0000000000300267

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000400000003803 0x4300040000000380

def z214 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbfff0007fffff8f 0xffbfff0007fffff8

def z215 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x90000f1f80832679 0xf90000f1f8083267

def z216 : W := mkw 0x0040492004903840 0x1004049200490384 0xb4d049e01cf0387b 0x5b4d049e01cf0387

def z217 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcffc9e61ffff87f 0x7fcffc9e61ffff87

def z218 : W := mkw 0x83bc91b872dcaa83 0x983bc91b872dcaa8 0x7738f1f863fcff87 0xd7738f1f863fcff8

def z219 : W := mkw 0x0000010200812010 0x0000001020081201 0x9000090600832079 0x7900009060083207

def z220 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0xb8df80001cffc00b 0x3b8df80001cffc00

def z221 : W := mkw 0x03bda6007b6a8523 0xe03bda6007b6a852 0xfbffb6007fffc78f 0xbfbffb6007fffc78

def z222 : W := mkw 0x4403016608b32818 0x14403016608b3281 0x0c1701e600f30000 0x30c1701e600f3000

def z223 : W := mkw 0x83bc91b820dc2a81 0x183bc91b820dc2a8 0xfffff1f860fc3f87 0xffffff1f860fc3f8

def z224 : W := mkw 0x0040480000000000 0x0004048000000000 0xb0c0480000000000 0x4b0c048000000000

def z225 : W := mkw 0xc55b59fe2cff3ad9 0x1c55b59fe2cff3ad 0xbcdf49fe1cff387b 0x7bcdf49fe1cff387

def z226 : W := mkw 0x22a02608d3044722 0x622a02608d304472 0x4328b619e30cc784 0x84328b619e30cc78

def z227 : W := mkw 0x2000000280014010 0x0200000028001401 0x000080078003c000 0x2000080078003c00

def z228 : W := mkw 0x0000109000000000 0x0000010900000000 0x040071f800000000 0xc040071f80000000

def z229 : W := mkw 0x02e26e445700156a 0x602e26e445700156 0xfff77fe67f003fff 0xffff77fe67f003ff

def z230 : W := mkw 0x02e06f0857843762 0x602e06f085784376 0xf3e87f187f8c3fff 0xdf3e87f187f8c3ff

def z231 : W := mkw 0x811810b020580881 0x1811810b02058088 0x771070e060703f87 0xc771070e060703f8

def z232 : W := mkw 0x02e06e0005001560 0x602e06e000500156 0xf3e07e0000003ff0 0xcf3e07e0000003ff

def z233 : W := mkw 0x444348640c321848 0x1444348640c32184 0xbcd740e01cf3180b 0x3bcd740e01cf3180

def z234 : W := mkw 0x444348640c321848 0x1444348640c32184 0xbcd748e01c70387b 0x4bcd748e01c70387

def z235 : W := mkw 0x02a0000052000002 0x002a000005200000 0xf3e880007f8fc00f 0x3f3e880007f8fc00

def z236 : W := mkw 0x44427df70491385c 0x144427df70491385 0x04007fff80003870 0xc04007fff8000387

def z237 : W := mkw 0x83fffdfd7afeaa8f 0x983fffdfd7afeaa8 0xffffffffffffff8f 0xfffffffffffffff8

def z238 : W := mkw 0x23bc8208f34cc623 0xc23bc8208f34cc62 0x43288619e30cc604 0x843288619e30cc60

def z239 : W := mkw 0xc51911ba2cff3ad1 0x1c51911ba2cff3ad 0x771871f87cff3fff 0xd771871f87cff3ff

def z240 : W := mkw 0x2000030281816430 0x4200003028181643 0x90208f078383e079 0x790208f078383e07

def z241 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffffe0003f87 0xfffffffffe0003f8

def z242 : W := mkw 0x0042484400000008 0x0004248440000000 0x040049e600000000 0x4040049e60000000

def z243 : W := mkw 0x02a0000052000002 0x002a000005200000 0xf3e070007f003f8f 0xcf3e070007f003f8

def z244 : W := mkw 0x0000000800040200 0x0000000080004020 0x40080018000c0604 0x840080018000c060

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z246 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0x0c1fffff80000000 0xf0c1fffff8000000

def z247 : W := mkw 0x0000020001000420 0x4000002000100042 0xd0200e000300267d 0xcd0200e000300267

def z248 : W := mkw 0x02e06c0000000000 0x002e06c000000000 0xf3e8ff1f80000000 0xff3e8ff1f8000000

def z249 : W := mkw 0x0000012000902800 0x1000001200090280 0x771071e060f03f87 0xd771071e060f03f8

def z250 : W := mkw 0x0001000008220000 0x0000100000822000 0x88c700001c030008 0x288c700001c03000

def z251 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8ff1fff003fff 0xff3e8ff1fff003ff

def z252 : W := mkw 0x83f87cb0765819c3 0x383f87cb0765819c 0x27d070e07c701982 0x027d070e07c70198

def z253 : W := mkw 0x4442496604913858 0x1444249660491385 0xbcd749e600003870 0x7bcd749e60000387

def z254 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0x040070e000000000 0x0040070e00000000

def z255 : W := mkw 0x03fcee0077489563 0xe03fcee007748956 0xf3e8fe007f0cffff 0xcf3e8fe007f0cfff

def z256 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x6ffff6f980000000 0x86ffff6f98000000

def z257 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771801f860fc0007 0x1771801f860fc000

def z258 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x7300700060fc3f87 0xc7300700060fc3f8

def z259 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x341841f800fc3803 0x5341841f800fc380

def z260 : W := mkw 0x03bcb49100000004 0x003bcb4910000000 0xd328bf1f80000000 0xfd328bf1f8000000

def z261 : W := mkw 0x000102007f6a9563 0xe000102007f6a956 0x000000007fffffff 0x0000000007ffffff

def z262 : W := mkw 0x83bd91b87afeaa83 0x983bd91b87afeaa8 0xffff81f87fffc00f 0x3ffff81f87fffc00

def z263 : W := mkw 0xa3feffffa1dd6ebd 0x5a3feffffa1dd6eb 0xffffffffe3ffffff 0xfffffffffe3fffff

def z264 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xcbef80007f0fc00c 0x2cbef80007f0fc00

def z265 : W := mkw 0x03fdee007f6a9563 0xe03fdee007f6a956 0xfbfffe007fffffff 0xffbfffe007ffffff

def z266 : W := mkw 0x2000020881044620 0x4200002088104462 0xd0288e19830ce67d 0xcd0288e19830ce67

def z267 : W := mkw 0x0000010800842200 0x0000001080084220 0x0000011800002600 0xc000001180000260

def z268 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcffcfff9cf3387b 0xffcffcfff9cf3387

def z269 : W := mkw 0x00406e0005001560 0x600406e000500156 0xd0207e0003003ffd 0xcd0207e0003003ff

def z270 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x40288f1f830ce674 0xc40288f1f830ce67

def z271 : W := mkw 0x811811b800942a80 0x1811811b800942a8 0x771871f800003f80 0xd771871f800003f8

def z272 : W := mkw 0x03beb4d50000000c 0x003beb4d50000000 0x4f3fb7ff80000000 0xb4f3fb7ff8000000

def z273 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271070e060fc3f87 0x0271070e060fc3f8

def z274 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd749e61c703872 0x42cd749e61c70387

def z275 : W := mkw 0x0005800008228000 0x8000580000822800 0x080780000003c000 0x2080780000003c00

def z276 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271071f860703f82 0xc271071f860703f8

def z277 : W := mkw 0x83bd90b07a7a8883 0x983bd90b07a7a888 0x2fd770e07c701982 0x02fd770e07c70198

def z278 : W := mkw 0x2000020281014430 0x4200002028101443 0xd0288f1f8303c078 0xfd0288f1f8303c07

def z279 : W := mkw 0x64434b668db37c78 0x564434b668db37c7 0xbcf7cfe79ff3f87b 0x7bcf7cfe79ff3f87

def z280 : W := mkw 0x02a580005a228002 0x802a580005a22800 0xb8f780001ff3c00b 0x3b8f780001ff3c00

def z281 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd740e01cf3387b 0x02cd740e01cf3387

def z282 : W := mkw 0x0118000020480001 0x0011800002048000 0x2310000060700002 0x0231000006070000

def z283 : W := mkw 0x440100200c321840 0x1440100200c32184 0x000000001c701802 0x0000000001c70180

def z284 : W := mkw 0x455fd9f70cb3385c 0x1455fd9f70cb3385 0xbcdfc9ff9cf3387b 0x7bcdfc9ff9cf3387

def z285 : W := mkw 0x015ed8d50000000c 0x0015ed8d50000000 0xbcdfc9ff80000000 0x7bcdfc9ff8000000

def z286 : W := mkw 0x03fffcd57a6a800f 0x803fffcd57a6a800 0xfffffffffc700002 0xffffffffffc70000

def z287 : W := mkw 0x0000012000902800 0x1000001200090280 0x0000000000f03803 0x00000000000f0380

def z288 : W := mkw 0x01190000286a0001 0x001190000286a000 0xfbdf00007cff000f 0x3fbdf00007cff000

def z289 : W := mkw 0x47ffc9660cb33858 0x147ffc9660cb3385 0xffffc9e61cf3387b 0x7ffffc9e61cf3387

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000f1f80000000 0xc00000f1f8000000

def z291 : W := mkw 0xa00013ba81956eb0 0x5a00013ba81956eb 0xd428ffff838ffffd 0xfd428ffff838ffff

def z292 : W := mkw 0x47fffdf70cb3385c 0x147fffdf70cb3385 0xbfd779e61cf3387b 0x7bfd779e61cf3387

def z293 : W := mkw 0x0000010800842200 0x0000001080084220 0x00000000008c2605 0x000000000008c260

def z294 : W := mkw 0x000680450000000c 0x0000680450000000 0x0807800780000000 0x2080780078000000

def z295 : W := mkw 0x0000349100000004 0x0000034910000000 0x0000361980000000 0x8000036198000000

def z296 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x041801f860fc3f87 0x1041801f860fc3f8

def z297 : W := mkw 0x0118010820cc2201 0x00118010820cc220 0x7318011860fc2607 0xd7318011860fc260

def z298 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x23c07e007c003ff2 0xc23c07e007c003ff

def z299 : W := mkw 0x4442484604011058 0x0444248460401105 0x0000080600000070 0x0000008060000007

def z300 : W := mkw 0x0042484400000008 0x0004248440000000 0x2cd740e000000000 0x02cd740e00000000

def z301 : W := mkw 0x02e27cd50000000c 0x002e27cd50000000 0xf7e07fff80000000 0xcf7e07fff8000000

def z302 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x0008811f838fe67d 0x30008811f838fe67

def z303 : W := mkw 0x46e26f6657913d7a 0x746e26f6657913d7 0xf7e07fe67f003fff 0xcf7e07fe67f003ff

def z304 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0xf71879fe60ff3fff 0xff71879fe60ff3ff

def z305 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771871f800fc0000 0xd771871f800fc000

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x00088000008fc000 0x300088000008fc00

def z307 : W := mkw 0x0000030201812430 0x4000003020181243 0xd0200f060383267d 0xfd0200f060383267

def z308 : W := mkw 0x03bd81207afaa803 0x903bd81207afaa80 0xffffc1e07ffff80f 0x7ffffc1e07ffff80

def z309 : W := mkw 0x811e91fd20dc2a8d 0x1811e91fd20dc2a8 0x7f1ff1ffe0fc3f87 0xf7f1ff1ffe0fc3f8

def z310 : W := mkw 0x46e36d665eb3395a 0x346e36d665eb3395 0xbfd779e67cf339fb 0x7bfd779e67cf339f

def z311 : W := mkw 0x000100005a228002 0x8000100005a22800 0x000000001f03c008 0x0000000001f03c00

def z312 : W := mkw 0x444349460ca33058 0x0444349460ca3305 0x98c709061c832079 0x798c709061c83207

def z313 : W := mkw 0x44436f660db33d78 0x744436f660db33d7 0xbcd77fe61cf33ffb 0xfbcd77fe61cf33ff

def z314 : W := mkw 0x00427ed50500156c 0x600427ed50500156 0x04007fff80003ff0 0xc04007fff80003ff

def z315 : W := mkw 0x02a0000052000002 0x002a000005200000 0x23c000007c000002 0x023c000007c00000

def z316 : W := mkw 0x44434b665fb33d7a 0x744434b665fb33d7 0xbcd749e67ff33fff 0x7bcd749e67ff33ff

def z317 : W := mkw 0x47fffdf77efbb85f 0x947fffdf77efbb85 0xfffffffffffff87f 0xffffffffffffff87

def z318 : W := mkw 0x00406e0057001562 0x600406e005700156 0x00007e007f003fff 0xc00007e007f003ff

def z319 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xffffffffff00000f 0xfffffffffff00000

def z320 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0200f1f8300267d 0xcd0200f1f8300267

def z321 : W := mkw 0x23bc830a81856630 0x423bc830a8185663 0xfbff8f1f838fe67d 0xffbff8f1f838fe67

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x40288000030cc004 0x040288000030cc00

def z323 : W := mkw 0x47ffc8647e7a984b 0x947ffc8647e7a984 0x2fd740e07c701802 0x02fd740e07c70180

def z324 : W := mkw 0x811d91b828feaa81 0x9811d91b828feaa8 0x0c1f81f800ffc000 0x30c1f81f800ffc00

def z325 : W := mkw 0x47bd81227efbb853 0x947bd81227efbb85 0xfbff80007ffff87f 0x3fbff80007ffff87

def z326 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x00088f1f808fe670 0xf00088f1f808fe67

def z327 : W := mkw 0x02a100005a220002 0x002a100005a22000 0xfbf700007ff3000f 0x3fbf700007ff3000

def z328 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288000038fe67d 0x3d0288000038fe67

def z329 : W := mkw 0x6403016e88b76a18 0x16403016e88b76a1 0x0c1f81ff80ffc000 0x30c1f81ff80ffc00

def z330 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x540871f8008c3f85 0xd540871f8008c3f8

def z331 : W := mkw 0x03fefcd57248800f 0x803fefcd57248800 0xffffffffe30cc004 0xfffffffffe30cc00

def z332 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf738ffffe0fc3f87 0xff738ffffe0fc3f8

def z333 : W := mkw 0x0000020057001562 0x6000002005700156 0x730070007f003fff 0xc730070007f003ff

def z334 : W := mkw 0x47ffc8647e7a984b 0x947ffc8647e7a984 0xffffc0e07fffd80f 0x3ffffc0e07fffd80

def z335 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd741e61cf31802 0x32cd741e61cf3180

def z336 : W := mkw 0x23bcb79b81856634 0x423bcb79b8185663 0xd328bf1f838fe67d 0xfd328bf1f838fe67

def z337 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0xbcf7cfe780000000 0x7bcf7cfe78000000

def z338 : W := mkw 0x000210d50000000c 0x0000210d50000000 0x040001ff80000000 0x0040001ff8000000

def z339 : W := mkw 0x83fdffb87ffebfe3 0xf83fdffb87ffebfe 0xfffffff87fffffff 0xffffffff87ffffff

def z340 : W := mkw 0x4442496604913858 0x1444249660491385 0x341049e600f03873 0x5341049e600f0387

def z341 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0x88e780007fffc00f 0x288e780007fffc00

def z342 : W := mkw 0x83f87db820dc2a81 0x183f87db820dc2a8 0xf7f87ff860fc3f87 0xdf7f87ff860fc3f8

def z343 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff8f1fffffc00f 0xffbff8f1fffffc00

def z344 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xaff7fee780000000 0x2aff7fee78000000

def z345 : W := mkw 0x0000010a00852210 0x00000010a0085221 0xd008091e008f267d 0xfd008091e008f267

def z346 : W := mkw 0x0000000052000002 0x0000000005200000 0x000000007f00000f 0x0000000007f00000

def z347 : W := mkw 0x011900007a6a8003 0x8011900007a6a800 0x731800007fffc00f 0x1731800007fffc00

def z348 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xb0e04e001f00387b 0x4b0e04e001f00387

def z349 : W := mkw 0x83bd81287afeaa83 0x983bd81287afeaa8 0xfbff80007fffff8f 0x3fbff80007fffff8

def z350 : W := mkw 0x440103225fb33d72 0x7440103225fb33d7 0x000000007ff33fff 0x0000000007ff33ff

def z351 : W := mkw 0x03bc800072488003 0x803bc80007248800 0x0300000060000000 0x0030000006000000

def z352 : W := mkw 0x03bd81087aeea203 0x803bd81087aeea20 0xfbff81187fffe60f 0xffbff81187fffe60

def z353 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf738f1f863ffff8f 0xff738f1f863ffff8

def z354 : W := mkw 0x00404a0057001562 0x600404a005700156 0xb0c048007f003fff 0x4b0c048007f003ff

def z355 : W := mkw 0x440301660cb33858 0x1440301660cb3385 0x0c1701e61cf3387b 0x30c1701e61cf3387

def z356 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0xb8d700007fffc00f 0x3b8d700007fffc00

def z357 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0xfffffffffc001982 0xffffffffffc00198

def z358 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x432880007fffc00f 0x0432880007fffc00

def z359 : W := mkw 0x23fefed78101443c 0x423fefed78101443 0xffffffff8303c078 0xfffffffff8303c07

def z360 : W := mkw 0x451f91f708b3281c 0x1451f91f708b3281 0x0c1f81ff80f30000 0x30c1f81ff80f3000

def z361 : W := mkw 0x03fdec007a6a8003 0x803fdec007a6a800 0xfbfffe007fffc00f 0xffbfffe007fffc00

def z362 : W := mkw 0x03bf90d57a6a800f 0x803bf90d57a6a800 0xffff81ffffffc00f 0x3ffff81ffffffc00

def z363 : W := mkw 0x0000000072488003 0x8000000007248800 0x00000000630cc004 0x000000000630cc00

def z364 : W := mkw 0x4443496608b32818 0x14443496608b3281 0xbcd749e600f30000 0x7bcd749e600f3000

def z365 : W := mkw 0x20427fdf8185663c 0x420427fdf8185663 0xd428ffff838fe67d 0xfd428ffff838fe67

def z366 : W := mkw 0x0118109000000000 0x0011810900000000 0x4308301800000000 0x8430830180000000

def z367 : W := mkw 0x46e36e465f23157a 0x646e36e465f23157 0x88e70e061f030078 0x288e70e061f03007

def z368 : W := mkw 0x02a0260053000522 0x602a026005300052 0x7320760063003f87 0xc7320760063003f8

def z369 : W := mkw 0xa118139aa1cd66b1 0x4a118139aa1cd66b 0xd328bf1fe38fe7fd 0xfd328bf1fe38fe7f

def z370 : W := mkw 0x6403036e89b76e38 0x56403036e89b76e3 0xdc3f8fff83ffe67d 0xfdc3f8fff83ffe67

def z371 : W := mkw 0x440101220cb33850 0x1440101220cb3385 0xb8d700001cf3387b 0x3b8d700001cf3387

def z372 : W := mkw 0x455fc9662cfbb859 0x9455fc9662cfbb85 0xbcdfc9e61cfff87b 0x7bcdfc9e61cfff87

def z373 : W := mkw 0x23bd830afbefe633 0xc23bd830afbefe63 0xfbff80007fffe67f 0x3fbff80007fffe67

def z374 : W := mkw 0x83fefcf52058088d 0x183fefcf52058088 0x2fd770e060701982 0x02fd770e06070198

def z375 : W := mkw 0x0001000008220000 0x0000100000822000 0xf8ff80001fffc00f 0x3f8ff80001fffc00

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0c000001c00000b 0x0b0c000001c00000

def z377 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x2bdf80007cffc002 0x32bdf80007cffc00

def z378 : W := mkw 0x03bc800000000000 0x003bc80000000000 0x2bd7000000000000 0x02bd700000000000

def z379 : W := mkw 0xc55a59fe24dd3ad9 0x1c55a59fe24dd3ad 0x771879fe60fc3ff7 0xd771879fe60fc3ff

def z380 : W := mkw 0x02e06e0053000522 0x602e06e005300052 0xf3e07e0063000784 0xcf3e07e006300078

def z381 : W := mkw 0x011c800000000000 0x0011c80000000000 0x081f800000000000 0x3081f80000000000

def z382 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xabf780007f73c00a 0x2abf780007f73c00

def z383 : W := mkw 0x22e06e02d7015572 0x622e06e02d701557 0x80e08e079f03c078 0x280e08e079f03c07

def z384 : W := mkw 0x23fefddf8085621c 0x023fefddf8085621 0xffffffff808fc000 0xfffffffff808fc00

def z385 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x671870f8607c1f86 0x8671870f8607c1f8

def z386 : W := mkw 0x4403016608b32818 0x14403016608b3281 0x9c1709e600f32079 0x79c1709e600f3207

def z387 : W := mkw 0x80427dfd00942a8c 0x180427dfd00942a8 0x04007fff80003f80 0xc04007fff80003f8

def z388 : W := mkw 0x211d830aa9efe631 0xc211d830aa9efe63 0xd83f8f1f83ffe67d 0xfd83f8f1f83ffe67

def z389 : W := mkw 0x0042494600812018 0x0004249460081201 0xbcd749e600832079 0x7bcd749e60083207

def z390 : W := mkw 0x02a4a40100000004 0x002a4a4010000000 0x0020860180000000 0x0002086018000000

def z391 : W := mkw 0x02e06c0000000000 0x002e06c000000000 0xf3e07e0060003f87 0xcf3e07e0060003f8

def z392 : W := mkw 0x0001000008220000 0x0000100000822000 0x0817000000f30000 0x30817000000f3000

def z393 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0xd02880007fffc00f 0x3d02880007fffc00

def z394 : W := mkw 0x0000000056001142 0x2000000005600114 0x000000007c001982 0x0000000007c00198

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x5008011800000000 0xd500801180000000

def z396 : W := mkw 0x47fffcd70c23105c 0x047fffcd70c23105 0xffffffff9c030078 0xfffffffff9c03007

def z397 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xffd779e67cf33fff 0xfffd779e67cf33ff

def z398 : W := mkw 0x2000000880044200 0x0200000088004420 0x00088019800cc000 0x000088019800cc00

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0200e0000000000 0xcd0200e000000000

def z400 : W := mkw 0x2000020881044620 0x4200002088104462 0x0000061980000600 0x8000006198000060

def z401 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x80288f1f838fc078 0x380288f1f838fc07

def z402 : W := mkw 0x03ffec457a6a800f 0x803ffec457a6a800 0xfbff8e07ffffc00f 0x3fbff8e07ffffc00

def z403 : W := mkw 0x444348460c231058 0x0444348460c23105 0xbcd749e61c030078 0x7bcd749e61c03007

def z404 : W := mkw 0x0000002000100800 0x1000000200010080 0x241040e000701802 0x0241040e00070180

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000080000002079 0x4900008000000207

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x2300700060001982 0x0230070006000198

def z407 : W := mkw 0x815859b824dc3ac1 0x1815859b824dc3ac 0xf7d879f87cfc3fff 0xdf7d879f87cfc3ff

def z408 : W := mkw 0x03fffcd55a22800e 0x803fffcd55a22800 0xffffffff9f03c008 0xfffffffff9f03c00

def z409 : W := mkw 0x47bf81667afba81b 0x947bf81667afba81 0xffff81e67fffc00f 0x3ffff81e67fffc00

def z410 : W := mkw 0x0000010200812010 0x0000001020081201 0xd0288906038fe07d 0x7d0288906038fe07

def z411 : W := mkw 0x8000002020580881 0x1800000202058088 0x0000000060701982 0x0000000006070198

def z412 : W := mkw 0x46e36f665fb33d7a 0x746e36f665fb33d7 0xbcf74fe61ff3387b 0x7bcf74fe61ff3387

def z413 : W := mkw 0x03fffcd50822000c 0x003fffcd50822000 0xffffffff9cf3000b 0xfffffffff9cf3000

def z414 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xbbd700007cf3000b 0x3bbd700007cf3000

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x50080000008c0005 0x150080000008c000

def z416 : W := mkw 0x0118109000000000 0x0011810900000000 0x041801f800000000 0x1041801f80000000

def z417 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x40288619838fe67d 0x840288619838fe67

def z418 : W := mkw 0x211e91df8085621c 0x0211e91df8085621 0x0c1f81ff808fc000 0x30c1f81ff808fc00

def z419 : W := mkw 0x64434b6e8db77e78 0x564434b6e8db77e7 0xbcd749e61ffffe7f 0x7bcd749e61ffffe7

def z420 : W := mkw 0x0000012800942a00 0x10000012800942a0 0x741841f800fc3e07 0xd741841f800fc3e0

def z421 : W := mkw 0x02a0240052000102 0x202a024005200010 0x0300300060000180 0x0030030006000018

def z422 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xfffff0e000000000 0x3fffff0e00000000

def z423 : W := mkw 0x0001012008b22800 0x10001012008b2280 0xbcd741e01cf3380b 0x7bcd741e01cf3380

def z424 : W := mkw 0x2000020081004420 0x4200002008100442 0x002086018300c000 0x0002086018300c00

def z425 : W := mkw 0x2000020281014430 0x4200002028101443 0xd0288e07838fc07d 0x3d0288e07838fc07

def z426 : W := mkw 0x0118109020480001 0x0011810902048000 0x771871f860fc0007 0xd771871f860fc000

def z427 : W := mkw 0x0000010000802000 0x0000001000080200 0x1000010000802001 0x5100001000080200

def z428 : W := mkw 0x0000020001000420 0x4000002000100042 0xd0288e00038fe67d 0xfd0288e00038fe67

def z429 : W := mkw 0x20427fdf8185663c 0x420427fdf8185663 0x04007fff80002670 0xc04007fff8000267

def z430 : W := mkw 0x03bd800008220000 0x003bd80000822000 0xfbff80001cf3000b 0x3fbff80001cf3000

def z431 : W := mkw 0x81181098204c0281 0x081181098204c028 0x771871f8600c0784 0xd771871f8600c078

def z432 : W := mkw 0x03fffed57f6a956f 0xe03fffed57f6a956 0xffffffffffffffff 0xffffffffffffffff

def z433 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x040001f800000000 0x0040001f80000000

def z434 : W := mkw 0x02e27ed55700156e 0x602e27ed55700156 0xf7e07fffff003fff 0xcf7e07fffff003ff

def z435 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x6bff80007f7cc006 0x06bff80007f7cc00

def z436 : W := mkw 0xc55b59fc2cfe3ac9 0x1c55b59fc2cfe3ac 0x7fdf71f87cfc3f87 0xd7fdf71f87cfc3f8

def z437 : W := mkw 0x0000020005001560 0x6000002000500156 0x0000000000003ff0 0x00000000000003ff

def z438 : W := mkw 0x2000030881846620 0x4200003088184662 0x50288719838ce605 0xd50288719838ce60

def z439 : W := mkw 0x02a0020053000422 0x402a002005300042 0xf3e00e007f00267f 0xcf3e00e007f00267

def z440 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0xd428ffff80000000 0xfd428ffff8000000

def z441 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x5008011860fc3f87 0xd5008011860fc3f8

def z442 : W := mkw 0x81181098204c0281 0x081181098204c028 0x7318301860fc0787 0x97318301860fc078

def z443 : W := mkw 0xa000032aa1dd6eb1 0x5a000032aa1dd6eb 0x0000000063ffffff 0x00000000063fffff

def z444 : W := mkw 0xc51b11fe28ff2a99 0x1c51b11fe28ff2a9 0x7f1f71fe60ff3f87 0xf7f1f71fe60ff3f8

def z445 : W := mkw 0x451f816628fba819 0x9451f816628fba81 0x0c1f81e600ffc000 0x30c1f81e600ffc00

def z446 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x88c708061cf3387b 0x288c708061cf3387

def z447 : W := mkw 0x02a0000052000002 0x002a000005200000 0x80e000001f000008 0x080e000001f00000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008811f80000000 0x30008811f8000000

def z449 : W := mkw 0x0000012000902800 0x1000001200090280 0x041001e000f00000 0x1041001e000f0000

def z450 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07e001f000078 0xcf3e07e001f00007

def z451 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xfff77ee000000000 0xcfff77ee00000000

def z452 : W := mkw 0x23ffffdffbefe63f 0xc23ffffdffbefe63 0xffffffffffffe67f 0xfffffffffffffe67

def z453 : W := mkw 0x02e5ee005f229562 0xe02e5ee005f22956 0xfbe7fe007f03ffff 0xefbe7fe007f03fff

def z454 : W := mkw 0x67ffffff8db77e7c 0x567ffffff8db77e7 0xffffffff9ffffe7f 0xfffffffff9ffffe7

def z455 : W := mkw 0x23feffdfd785777e 0x623feffdfd785777 0xffffffffff8fffff 0xfffffffffff8ffff

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x80208e0780000000 0x280208e078000000

def z457 : W := mkw 0x22a0270ad3856732 0x622a0270ad385673 0xd328bf1fe38fe7fd 0xfd328bf1fe38fe7f

def z458 : W := mkw 0x83b83698734c07a3 0x683b83698734c07a 0x43283618630c0784 0x843283618630c078

def z459 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0x000000007c700002 0x0000000007c70000

def z460 : W := mkw 0x800010b000100880 0x1800010b00010088 0x040070e000001980 0x0040070e00000198

def z461 : W := mkw 0x02e0480056001042 0x002e048005600104 0xf3e048007f00387f 0x4f3e048007f00387

def z462 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0x73c070007c003f87 0xc73c070007c003f8

def z463 : W := mkw 0x2000010a80856210 0x02000010a8085621 0x0000011f80000000 0x00000011f8000000

def z464 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0x7718f1ffe0ffff87 0xf7718f1ffe0ffff8

def z465 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0x7b1f800060ffc007 0x37b1f800060ffc00

def z466 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0200e00038fe67d 0xcd0200e00038fe67

def z467 : W := mkw 0x2001030a89a76630 0x42001030a89a7663 0xf8ff8f1f9fffe67f 0xff8ff8f1f9fffe67

def z468 : W := mkw 0x03bc909000000000 0x003bc90900000000 0xfffff1f800000000 0xffffff1f80000000

def z469 : W := mkw 0x811e91fd20dc2a8d 0x1811e91fd20dc2a8 0x0c1f81ff80fc0000 0x30c1f81ff80fc000

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000700000003f80 0xc0000700000003f8

def z471 : W := mkw 0x83bcb499204c0285 0x083bcb499204c028 0x4328b619e00c0784 0x84328b619e00c078

def z472 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x7bdf00007cfc0007 0x17bdf00007cfc000

def z473 : W := mkw 0xc55b59f62cfb38d9 0x1c55b59f62cfb38d 0xbfd779e67cf339fb 0x7bfd779e67cf339f

def z474 : W := mkw 0x22e06f0a81856630 0x422e06f0a8185663 0xf3e8ff1f838fe67d 0xff3e8ff1f838fe67

def z475 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbf700007f70000f 0x0fbf700007f70000

def z476 : W := mkw 0x811911b87afeaa83 0x9811911b87afeaa8 0x771871f87fffff8f 0xd771871f87fffff8

def z477 : W := mkw 0x66e36f6edfb77f7a 0x766e36f6edfb77f7 0xffffffffffffffff 0xffffffffffffffff

def z478 : W := mkw 0x83fefffd77dc3fef 0x783fefffd77dc3fe 0xfffffffffffc3fff 0xffffffffffffc3ff

def z479 : W := mkw 0x811911b828fe2a81 0x1811911b828fe2a8 0xffdf71f87cff3f8f 0xfffdf71f87cff3f8

def z480 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff80007c700002 0x3fbff80007c70000

def z481 : W := mkw 0x0040480004001040 0x0004048000400104 0x20c040001c001802 0x020c040001c00180

def z482 : W := mkw 0x03fdee007f6a9563 0xe03fdee007f6a956 0xfbff8e007fffc07f 0x3fbff8e007fffc07

def z483 : W := mkw 0x4442486404101848 0x1444248640410184 0x040040e000001800 0x0040040e00000180

def z484 : W := mkw 0x0000010200812010 0x0000001020081201 0x0000090600002070 0x4000009060000207

def z485 : W := mkw 0x81181098204c0281 0x081181098204c028 0x73087018600c3f87 0xc73087018600c3f8

def z486 : W := mkw 0x4403016608b32818 0x14403016608b3281 0xbcd701e61cf3000b 0x3bcd701e61cf3000

def z487 : W := mkw 0x64434b6e8db77e78 0x564434b6e8db77e7 0xbcd74fff9cf33e7b 0xfbcd74fff9cf33e7

def z488 : W := mkw 0xa11813baa1dd6eb1 0x5a11813baa1dd6eb 0x771871f863ffffff 0xd771871f863fffff

def z489 : W := mkw 0x0042484400000008 0x0004248440000000 0x88c7080600000000 0x288c708060000000

def z490 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x4b3f800063ffc004 0x34b3f800063ffc00

def z491 : W := mkw 0xa11813baa1dd6eb1 0x5a11813baa1dd6eb 0x77187fffe0fc3ff7 0xd77187fffe0fc3ff

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x7300700000000000 0xc730070000000000

def z493 : W := mkw 0x47fffdf708b3281c 0x147fffdf708b3281 0xffffffff80f30000 0xfffffffff80f3000

def z494 : W := mkw 0x800011b820dc2a81 0x1800011b820dc2a8 0x040071f860fc3f87 0xc040071f860fc3f8

def z495 : W := mkw 0x800101287afeaa83 0x9800101287afeaa8 0x000000007fffff8f 0x0000000007fffff8

def z496 : W := mkw 0x0000012200912810 0x1000001220091281 0xb41049e600f3387b 0x7b41049e600f3387

def z497 : W := mkw 0xa1181298a14c46a1 0x4a1181298a14c46a 0x4328b619e30cc784 0x84328b619e30cc78

def z498 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x2fd77fff80000000 0xc2fd77fff8000000

def z499 : W := mkw 0x03bd80005a228002 0x803bd80005a22800 0xfbff80001f03c008 0x3fbff80001f03c00

def z500 : W := mkw 0x47ffc8467e6b905b 0x847ffc8467e6b905 0xfbff88067fffc07f 0x3fbff88067fffc07

def z501 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x041871f800fc3f80 0xd041871f800fc3f8

def z502 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x471831f860fc0784 0x9471831f860fc078

def z503 : W := mkw 0x2118139a81856630 0x42118139a8185663 0xf738ffff838fe67d 0xff738ffff838fe67

def z504 : W := mkw 0x0118000020480001 0x0011800002048000 0x7318700060fc3f87 0xd7318700060fc3f8

def z505 : W := mkw 0x0000020001000420 0x4000002000100042 0x00000e0000002670 0xc00000e000000267

def z506 : W := mkw 0x81587fb825dc3fe1 0x781587fb825dc3fe 0x77187ff860fc3ff7 0xd77187ff860fc3ff

def z507 : W := mkw 0x0043484408220008 0x0004348440822000 0xbcd749e61cf3000b 0x7bcd749e61cf3000

def z508 : W := mkw 0x47fffff75fb33d7e 0x747fffff75fb33d7 0xfffffffffff33fff 0xffffffffffff33ff

def z509 : W := mkw 0x03bd82007f6a9563 0xe03bd82007f6a956 0xfbff80007fffffff 0x3fbff80007ffffff

def z510 : W := mkw 0x03bc800000000000 0x003bc80000000000 0xfbff8f1f80000000 0xffbff8f1f8000000

def z511 : W := mkw 0x02e16e005f221562 0x602e16e005f22156 0xfbf77e007ff33fff 0xffbf77e007ff33ff

def z512 : W := mkw 0x00406e0005001560 0x600406e000500156 0xb0c07e001c003ffb 0xcb0c07e001c003ff

def z513 : W := mkw 0x02a0260053000522 0x602a026005300052 0xf3e036007f00078f 0x8f3e036007f00078

def z514 : W := mkw 0xc443496e2cff3ad9 0x1c443496e2cff3ad 0xbcd749e67cff3fff 0x7bcd749e67cff3ff

def z515 : W := mkw 0x811813b821dc2ea1 0x5811813b821dc2ea 0xf7387ff863fc3fff 0xdf7387ff863fc3ff

def z516 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x90000906038fe67d 0x790000906038fe67

def z517 : W := mkw 0x011c909100000004 0x0011c90910000000 0x0008801980000000 0x0000880198000000

def z518 : W := mkw 0x0000020057001562 0x6000002005700156 0xd0200e007f003fff 0xcd0200e007f003ff

def z519 : W := mkw 0x20424b4e81856638 0x420424b4e8185663 0xfcffcfff838fe67d 0xffcffcfff838fe67

def z520 : W := mkw 0x0118000000000000 0x0011800000000000 0x7318000000000000 0x1731800000000000

def z521 : W := mkw 0x0040480004001040 0x0004048000400104 0x0000480000003870 0x4000048000000387

def z522 : W := mkw 0x03bc800000000000 0x003bc80000000000 0x4328800000000000 0x0432880000000000

def z523 : W := mkw 0x0118109000000000 0x0011810900000000 0x271070e000000000 0x0271070e00000000

def z524 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8fe007f8fffff 0xff3e8fe007f8ffff

def z525 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xa3e07e007f0019fa 0x0a3e07e007f0019f

def z526 : W := mkw 0x03fefddd0084220c 0x003fefddd0084220 0xffffffff808c2605 0xfffffffff808c260

def z527 : W := mkw 0x2000020881044620 0x4200002088104462 0x00000000030cc604 0x000000000030cc60

def z528 : W := mkw 0x83f87eb077581de3 0x783f87eb077581de 0xf7f07ee07f703fff 0xcf7f07ee07f703ff

def z529 : W := mkw 0x02e7ec455a22800e 0x802e7ec455a22800 0x88e78e079f03c008 0x288e78e079f03c00

def z530 : W := mkw 0x011811b000902800 0x1011811b00090280 0x771871f800f03803 0xd771871f800f0380

def z531 : W := mkw 0x0000020001000420 0x4000002000100042 0xf3207e0063003fff 0xcf3207e0063003ff

def z532 : W := mkw 0x02a100007a6a8003 0x802a100007a6a800 0xf3e000007fffc00f 0x0f3e000007fffc00

def z533 : W := mkw 0x83f87db876dc3bc3 0x383f87db876dc3bc 0x77d871f87cfc3f87 0xd77d871f87cfc3f8

def z534 : W := mkw 0x440101227efbb853 0x9440101227efbb85 0x000000007ffff87f 0x0000000007ffff87

def z535 : W := mkw 0x0118119800842200 0x0011811980084220 0x771871f8008c2605 0xd771871f8008c260

def z536 : W := mkw 0x20406f0a85857770 0x620406f0a8585777 0xd028ff1f838ffffd 0xfd028ff1f838ffff

def z537 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x7f1ff1ff80000000 0xf7f1ff1ff8000000

def z538 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x470871f8600c3f84 0xc470871f8600c3f8

def z539 : W := mkw 0x83b811b872dc2a83 0x183b811b872dc2a8 0xf7f871f87ffc3f8f 0xdf7f871f87ffc3f8

def z540 : W := mkw 0x22e06f0ad7857772 0x622e06f0ad785777 0xf3e07f1fff003fff 0xcf3e07f1fff003ff

def z541 : W := mkw 0x02a0260053000522 0x602a026005300052 0xd3203e00630027fd 0xcd3203e00630027f

def z542 : W := mkw 0x2000020281014430 0x4200002028101443 0xd0208e078303e67d 0xed0208e078303e67

def z543 : W := mkw 0x8000012800942a80 0x18000012800942a8 0x0000000000003f80 0x00000000000003f8

def z544 : W := mkw 0x03ffc8447a6a800b 0x803ffc8447a6a800 0xffffc9e67fffc00f 0x7ffffc9e67fffc00

def z545 : W := mkw 0x015a7cd50000000c 0x0015a7cd50000000 0x77187fff80000000 0xd77187fff8000000

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0x341041e000000000 0x5341041e00000000

def z547 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x4308301860fc3f87 0x84308301860fc3f8

def z548 : W := mkw 0x23bcb69981044624 0x423bcb6998104462 0x4328b619830cc604 0x84328b619830cc60

def z549 : W := mkw 0x02a0260053000522 0x602a026005300052 0x0020060003000000 0x0002006000300000

def z550 : W := mkw 0x03fffcd57a6a800f 0x803fffcd57a6a800 0xfffff0e07fffc00f 0x3fffff0e07fffc00

def z551 : W := mkw 0x23bd8202fb6bc433 0xc23bd8202fb6bc43 0xfbff8e07ffffc07f 0x3fbff8e07ffffc07

def z552 : W := mkw 0x83bd90b07a7a8883 0x983bd90b07a7a888 0xfffff0e07fffd98f 0x3fffff0e07fffd98

def z553 : W := mkw 0x83fefdfd20dc2a8d 0x183fefdfd20dc2a8 0xffffffff80fc0000 0xfffffffff80fc000

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0xd028800000000000 0x3d02880000000000

def z555 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x80208f1f8303e678 0xe80208f1f8303e67

def z556 : W := mkw 0x0000020053000522 0x6000002005300052 0x0000000063000784 0x0000000006300078

def z557 : W := mkw 0x22e06f0ad7857772 0x622e06f0ad785777 0xd0e88f1f9f8fe67d 0xfd0e88f1f9f8fe67

def z558 : W := mkw 0xa11813baa1dd6eb1 0x5a11813baa1dd6eb 0xd4388fff83ffe67d 0xfd4388fff83ffe67

def z559 : W := mkw 0x0000020001000420 0x4000002000100042 0xd0288f1f8300267d 0xfd0288f1f8300267

def z560 : W := mkw 0x0000020001000420 0x4000002000100042 0x80200e0003000078 0x080200e000300007

def z561 : W := mkw 0x0040490204813050 0x0004049020481305 0xb0c049061c83387b 0x7b0c049061c83387

def z562 : W := mkw 0x02a4800000000000 0x002a480000000000 0x88e7800000000000 0x288e780000000000

def z563 : W := mkw 0x03bcb49100000004 0x003bcb4910000000 0x0300300000000000 0x0030030000000000

def z564 : W := mkw 0x02e16e007f6a9563 0xe02e16e007f6a956 0xf3e07e007fffffff 0xcf3e07e007ffffff

def z565 : W := mkw 0x815a7dfd20dc2a8d 0x1815a7dfd20dc2a8 0x77187fffe0fc3f87 0xd77187fffe0fc3f8

def z566 : W := mkw 0x444349640cb23848 0x1444349640cb2384 0x3cd741e01cf03803 0x53cd741e01cf0380

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000060003f87 0x00000000060003f8

def z568 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x0000000000002670 0x0000000000000267

def z569 : W := mkw 0x02e06c0000000000 0x002e06c000000000 0x80e00e0000000000 0x080e00e000000000

def z570 : W := mkw 0x03bc800052000002 0x003bc80005200000 0xfbff80007f00000f 0x3fbff80007f00000

def z571 : W := mkw 0x0042484404001048 0x0004248440400104 0xbcd749e61c00387b 0x7bcd749e61c00387

def z572 : W := mkw 0x0000010800842200 0x0000001080084220 0x73087118608c3f87 0xd73087118608c3f8

def z573 : W := mkw 0x00406e0005001560 0x600406e000500156 0x73007e0060003ff7 0xc73007e0060003ff

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000090600000000 0x7900009060000000

def z575 : W := mkw 0x011c800020488001 0x8011c80002048800 0x00088000000cc000 0x000088000000cc00

def z576 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x80e07e001f003ff8 0xc80e07e001f003ff

def z577 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x0000000000fc0000 0x00000000000fc000

def z578 : W := mkw 0x4442496604913858 0x1444249660491385 0xb4c049e61c00387b 0x4b4c049e61c00387

def z579 : W := mkw 0x03fefed55700156e 0x603fefed55700156 0xfff77ee07f003fff 0xcfff77ee07f003ff

def z580 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0xd83f800003ffc00d 0x3d83f800003ffc00

def z581 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x541801f800fc2605 0xd541801f800fc260

def z582 : W := mkw 0x211d810aa8efe211 0x8211d810aa8efe21 0x081f811f80ffc000 0x3081f811f80ffc00

def z583 : W := mkw 0x47ffef667ffbbd7b 0xf47ffef667ffbbd7 0xffffffe67fffffff 0xfffffffe67ffffff

def z584 : W := mkw 0x82e06f2877dc3fe3 0x782e06f2877dc3fe 0xf3e07e007ffc3fff 0xcf3e07e007ffc3ff

def z585 : W := mkw 0x03fefed50500156c 0x603fefed50500156 0xffffffff80003ff0 0xfffffffff80003ff

def z586 : W := mkw 0x83fefdfd00942a8c 0x183fefdfd00942a8 0xffffffff80003f80 0xfffffffff80003f8

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x7300000060000007 0x0730000006000000

def z588 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x00000f1f838fe67d 0xc00000f1f838fe67

def z589 : W := mkw 0x47ffc9667efbb85b 0x947ffc9667efbb85 0xbfd749e67cf3387b 0x7bfd749e67cf3387

def z590 : W := mkw 0x8118119820cc2281 0x08118119820cc228 0x53083118608c2785 0xd53083118608c278

def z591 : W := mkw 0x2000010a80856210 0x02000010a8085621 0x00000000008fc000 0x000000000008fc00

def z592 : W := mkw 0x20406f0a85857770 0x620406f0a8585777 0x00007f1f80003ff0 0xc00007f1f80003ff

def z593 : W := mkw 0x815a59fc20dc2a89 0x1815a59fc20dc2a8 0xffdf79fe60fc3f87 0xfffdf79fe60fc3f8

def z594 : W := mkw 0x00404a0005001460 0x400404a000500146 0xf0e04e001f003e7f 0xcf0e04e001f003e7

def z595 : W := mkw 0xa00013ba81956eb0 0x5a00013ba81956eb 0x04007fff80003ff0 0xc04007fff80003ff

def z596 : W := mkw 0x4400012204913850 0x1440001220491385 0x0000000000003870 0x0000000000000387

def z597 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271871f860fc1982 0x1271871f860fc198

def z598 : W := mkw 0x03fdee007f6a9563 0xe03fdee007f6a956 0xfbf77e007f703fff 0xcfbf77e007f703ff

def z599 : W := mkw 0x47fffcf50c32184c 0x147fffcf50c32184 0x2fd770e01c701802 0x02fd770e01c70180

def z600 : W := mkw 0x23bd8208fb6ec623 0xc23bd8208fb6ec62 0xfbff8619ffffc60f 0xbfbff8619ffffc60

def z601 : W := mkw 0xc7fb7ffe7fff3ffb 0x7c7fb7ffe7fff3ff 0xffff7ffe7fff3fff 0xfffff7ffe7fff3ff

def z602 : W := mkw 0x8000109800040280 0x0800010980004028 0x0000301800000780 0x8000030180000078

def z603 : W := mkw 0x0000010200812010 0x0000001020081201 0x0000000000832079 0x0000000000083207

def z604 : W := mkw 0x03fcec0000000000 0x003fcec000000000 0xfbfffe0000000000 0xffbfffe000000000

def z605 : W := mkw 0x03be90d50000000c 0x003be90d50000000 0xffff81ff80000000 0x3ffff81ff8000000

def z606 : W := mkw 0x0000010800842200 0x0000001080084220 0x00080118008c0000 0x100080118008c000

def z607 : W := mkw 0x4403004608230018 0x0440300460823001 0x0807000600030000 0x2080700060003000

def z608 : W := mkw 0x02e06c0004001040 0x002e06c000400104 0xf3e07e001c00387b 0xcf3e07e001c00387

def z609 : W := mkw 0x6401032a8db77e70 0x56401032a8db77e7 0xd0288f1f9ffffe7f 0xfd0288f1f9ffffe7

def z610 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x63e076007f001f86 0x863e076007f001f8

def z611 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x2fdff1ff80000000 0x32fdff1ff8000000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x802080000303c008 0x2802080000303c00

def z613 : W := mkw 0x23bc830af3cde633 0xc23bc830af3cde63 0xd3288f1fe38fe67d 0xfd3288f1fe38fe67

def z614 : W := mkw 0x02a4800052008002 0x802a480005200800 0x002080000300c000 0x0002080000300c00

def z615 : W := mkw 0xc7fffdff2cff3add 0x1c7fffdff2cff3ad 0xfffffffffcff3fff 0xffffffffffcff3ff

def z616 : W := mkw 0x23fdef0affeff773 0xe23fdef0affeff77 0xfbffff1fffffffff 0xffbffff1ffffffff

def z617 : W := mkw 0x03bd8000286a8001 0x803bd8000286a800 0xfbff800000ffc000 0x3fbff800000ffc00

def z618 : W := mkw 0x0000010800842200 0x0000001080084220 0xd0288f1f808c2605 0xfd0288f1f808c260

def z619 : W := mkw 0x02a580005a228002 0x802a580005a22800 0xd8ef80001f8fc00d 0x3d8ef80001f8fc00

def z620 : W := mkw 0x03fdc8007e6a9043 0x803fdc8007e6a904 0xfbffc8007ffff87f 0x7fbffc8007ffff87

def z621 : W := mkw 0x46e36c645e32194a 0x346e36c645e32194 0x2fd770e07c701982 0x02fd770e07c70198

def z622 : W := mkw 0x83b837b873dc2fa3 0x783b837b873dc2fa 0x773877f863fc3f87 0xd773877f863fc3f8

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000038fc00d 0x000000000038fc00

def z624 : W := mkw 0x0118000020480001 0x0011800002048000 0x43080000600c0004 0x043080000600c000

def z625 : W := mkw 0x444348460c231058 0x0444348460c23105 0xb8c748061c03387b 0x6b8c748061c03387

def z626 : W := mkw 0x44437df70cb3385c 0x144437df70cb3385 0xbcd77fff9cf3387b 0xfbcd77fff9cf3387

def z627 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x8cc749e61c033878 0x68cc749e61c03387

def z628 : W := mkw 0x02e06e0001000420 0x402e06e000100042 0xf3e07e000300267d 0xcf3e07e000300267

def z629 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0x08c7000000000000 0x008c700000000000

def z630 : W := mkw 0x440101220cb33850 0x1440101220cb3385 0x341041e01cf3387b 0x5341041e01cf3387

def z631 : W := mkw 0x46e36e465f23157a 0x646e36e465f23157 0xfbe77e067f033fff 0xefbe77e067f033ff

def z632 : W := mkw 0x46e36d660cb33858 0x146e36d660cb3385 0xfff77fe61cf3387b 0xffff77fe61cf3387

def z633 : W := mkw 0x0000020057001562 0x6000002005700156 0x000000001f000078 0x0000000001f00007

def z634 : W := mkw 0x03bc800072488003 0x803bc80007248800 0xf3e880007f0cc00f 0x0f3e880007f0cc00

def z635 : W := mkw 0x03fec84400000008 0x003fec8440000000 0xffffc9e600000000 0x7ffffc9e60000000

def z636 : W := mkw 0x03fefdd70081201c 0x003fefdd70081201 0xffffffff80832079 0xfffffffff8083207

def z637 : W := mkw 0x46e349665eb3385a 0x146e349665eb3385 0xfff749e67ff3387f 0x7fff749e67ff3387

def z638 : W := mkw 0x011d80007a6a8003 0x8011d80007a6a800 0x081f80007fffc00f 0x3081f80007fffc00

def z639 : W := mkw 0x0001000008220000 0x0000100000822000 0x28d700001c700002 0x028d700001c70000

def z640 : W := mkw 0x83fefdfd20dc2a8d 0x183fefdfd20dc2a8 0x7fdf71f860fc3f87 0xd7fdf71f860fc3f8

def z641 : W := mkw 0x83bcb5b920dc2a85 0x183bcb5b920dc2a8 0x7738f7f9e0fc3f87 0xd7738f7f9e0fc3f8

def z642 : W := mkw 0x455b59f60cb33858 0x1455b59f60cb3385 0xffdf79fe1cf3387b 0xfffdf79fe1cf3387

def z643 : W := mkw 0xc44259fe04953ad8 0x1c44259fe04953ad 0x040079fe00003ff0 0xc040079fe00003ff

def z644 : W := mkw 0xe55b5bfeadff7ef9 0x5e55b5bfeadff7ef 0xffffffffffffffff 0xffffffffffffffff

def z645 : W := mkw 0x03fefdf50090280c 0x103fefdf50090280 0xffffffff80f03803 0xfffffffff80f0380

def z646 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288f1f80002670 0xfd0288f1f8000267

def z647 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0x00c000001c000000 0x000c000001c00000

def z648 : W := mkw 0x46e16f225fb33d72 0x746e16f225fb33d7 0xf3e07e007ff33fff 0xcf3e07e007ff33ff

def z649 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x43207e0063003ff4 0xc43207e0063003ff

def z650 : W := mkw 0x83bc9098724c8283 0x883bc9098724c828 0x4328b018630cc784 0x84328b018630cc78

def z651 : W := mkw 0x440101220cb33850 0x1440101220cb3385 0x900009061cf3387b 0x7900009061cf3387

def z652 : W := mkw 0x0042496400902808 0x1004249640090280 0xbcd749e600f03803 0x7bcd749e600f0380

def z653 : W := mkw 0x4403016608b32818 0x14403016608b3281 0x3c1741e600f33803 0x73c1741e600f3380

def z654 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0xfbe7fe0780000000 0xefbe7fe078000000

def z655 : W := mkw 0x03bcb49172488007 0x803bcb4917248800 0x4328b619e30cc004 0x84328b619e30cc00

def z656 : W := mkw 0x444348460c231058 0x0444348460c23105 0xb8d708061cf3007b 0x3b8d708061cf3007

def z657 : W := mkw 0x03fcfe9157001566 0x603fcfe915700156 0xf3e8fe19ff003fff 0xcf3e8fe19ff003ff

def z658 : W := mkw 0x03bd82007b6a8423 0xc03bd82007b6a842 0xfbff8e007fffe67f 0xffbff8e007fffe67

def z659 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0x0817000000700000 0x0081700000070000

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000000000002605 0xc500000000000260

def z661 : W := mkw 0x0040480004001040 0x0004048000400104 0x80c008001c000078 0x080c008001c00007

def z662 : W := mkw 0x44426f6605913d78 0x744426f6605913d7 0x04007fe600003ff0 0xc04007fe600003ff

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x3010000000f00003 0x13010000000f0000

def z664 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x341071f800f03f83 0xd341071f800f03f8

def z665 : W := mkw 0x22e06e02d7015572 0x622e06e02d701557 0xf3e0fe07ff03ffff 0xef3e0fe07ff03fff

def z666 : W := mkw 0x46e7c8465e23905a 0x846e7c8465e23905 0x88e788061f03c078 0x288e788061f03c07

def z667 : W := mkw 0xa11813b8a1dc6ea1 0x5a11813b8a1dc6ea 0x7738f7f9e3fcff87 0xd7738f7f9e3fcff8

def z668 : W := mkw 0x83fefcf52058088d 0x183fefcf52058088 0xffffffffe0701982 0xfffffffffe070198

def z669 : W := mkw 0x02e06c0000000000 0x002e06c000000000 0x23c0700000000000 0x023c070000000000

def z670 : W := mkw 0x64424b6e85957e78 0x564424b6e85957e7 0xd428cfff838ffe7d 0xfd428cfff838ffe7

def z671 : W := mkw 0x46e7ec470c23105c 0x046e7ec470c23105 0x88e78e079c030078 0x288e78e079c03007

def z672 : W := mkw 0x03fcfc9100000004 0x003fcfc910000000 0xf3e8fe1980000000 0xcf3e8fe198000000

def z673 : W := mkw 0x46e36e645f321d6a 0x746e36e645f321d6 0xfff77ee07f703fff 0xcfff77ee07f703ff

def z674 : W := mkw 0x02a0000052000002 0x002a000005200000 0x4320000063000004 0x0432000006300000

def z675 : W := mkw 0x2000010a80856210 0x02000010a8085621 0xd0288f1f808fc000 0xfd0288f1f808fc00

def z676 : W := mkw 0x2000020281014430 0x4200002028101443 0x00000e0780000070 0x000000e078000007

def z677 : W := mkw 0x22e06f0ad7857772 0x622e06f0ad785777 0xf3e07e007f8fffff 0xcf3e07e007f8ffff

def z678 : W := mkw 0x03bd81027aeba013 0x803bd81027aeba01 0xfbff89067fffe07f 0x7fbff89067fffe07

def z679 : W := mkw 0x02a0240000000000 0x002a024000000000 0x4320360000000000 0x8432036000000000

def z680 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0xf3e070007f00198f 0x0f3e070007f00198

def z681 : W := mkw 0x23feffdf8185663c 0x423feffdf8185663 0xffffffff80002670 0xfffffffff8000267

def z682 : W := mkw 0x03f87e9057001562 0x603f87e905700156 0xf7f87ff87f003fff 0xdf7f87ff87f003ff

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x4300300060000784 0x8430030006000078

def z684 : W := mkw 0x444348640c321848 0x1444348640c32184 0xbcd749e61c701802 0x7bcd749e61c70180

def z685 : W := mkw 0x23bd810afaefe213 0x823bd810afaefe21 0xfbff811fffffc00f 0x3fbff811fffffc00

def z686 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x50080f1f808c2675 0xd50080f1f808c267

def z687 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x80e00e007f003fff 0x080e00e007f003ff

def z688 : W := mkw 0x02e6ee455700156e 0x602e6ee455700156 0x88e78e079f000078 0x288e78e079f00007

def z689 : W := mkw 0x444348440c221048 0x0444348440c22104 0x08c700001c000000 0x008c700001c00000

def z690 : W := mkw 0x0118000020480001 0x0011800002048000 0x0018000000fc0000 0x10018000000fc000

def z691 : W := mkw 0x83f87e98774c17e3 0x683f87e98774c17e 0xf3e87e187f0c3fff 0xcf3e87e187f0c3ff

def z692 : W := mkw 0x03b8000072480003 0x003b800007248000 0xf3f800007ffc000f 0x1f3f800007ffc000

def z693 : W := mkw 0x2000010a80856210 0x02000010a8085621 0x5008811f808fe605 0xf5008811f808fe60

def z694 : W := mkw 0x64434b4e8da77678 0x464434b4e8da7767 0xd8ef8f1f9f8fe67d 0xfd8ef8f1f9f8fe67

def z695 : W := mkw 0x02e26c4400000008 0x002e26c440000000 0xfff77fe600000000 0xffff77fe60000000

def z696 : W := mkw 0x03f87c9000000000 0x003f87c900000000 0xf7f87ff800000000 0xdf7f87ff80000000

def z697 : W := mkw 0x4442496604913858 0x1444249660491385 0x940049e600833879 0x7940049e60083387

def z698 : W := mkw 0x02a580005a228002 0x802a580005a22800 0x08c700001c000000 0x008c700001c00000

def z699 : W := mkw 0x03bc800072488003 0x803bc80007248800 0xd3288000638fc00d 0x3d3288000638fc00

def z700 : W := mkw 0x22e06e08d7045762 0x622e06e08d704576 0xf3e8fe19ff0cffff 0xcf3e8fe19ff0cfff

def z701 : W := mkw 0x0118109000000000 0x0011810900000000 0xf738ffff80000000 0xff738ffff8000000

def z702 : W := mkw 0x811813b877dc3fe3 0x7811813b877dc3fe 0x771871f87ffc3fff 0xd771871f87ffc3ff

def z703 : W := mkw 0x02a0000000000000 0x002a000000000000 0xf3e0000000000000 0x0f3e000000000000

def z704 : W := mkw 0x22a0030ad3856632 0x422a0030ad385663 0xf3e88f1fff8fe67f 0xff3e88f1fff8fe67

def z705 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x770071f860003f87 0xc770071f860003f8

def z706 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x0c1700e000000000 0x00c1700e00000000

def z707 : W := mkw 0x800011b800942a80 0x1800011b800942a8 0x771071f860f03f87 0xd771071f860f03f8

def z708 : W := mkw 0x811810b020580881 0x1811810b02058088 0x271070e060703f87 0x0271070e060703f8

def z709 : W := mkw 0x46a327665bb32d3a 0x746a327665bb32d3 0x4f3737e663f30784 0xb4f3737e663f3078

def z710 : W := mkw 0x64434a6c8d365e68 0x564434a6c8d365e6 0x6cffc6f99f7cde06 0x86cffc6f99f7cde0

def z711 : W := mkw 0x03fefcd57248800f 0x803fefcd57248800 0xffffffffe3fcc007 0xfffffffffe3fcc00

def z712 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271871f860fc3f82 0xd271871f860fc3f8

def z713 : W := mkw 0x440101220cb33850 0x1440101220cb3385 0xbcd741e01cf3387b 0x7bcd741e01cf3387

def z714 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xb3c078007f003fff 0x4b3c078007f003ff

def z715 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf71871f860ff3f8f 0xff71871f860ff3f8

def z716 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf7d871f87cfc3f8f 0xdf7d871f87cfc3f8

def z717 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xfcffc9ff9ffff87f 0x7fcffc9ff9ffff87

def z718 : W := mkw 0x23bd830afbefe633 0xc23bd830afbefe63 0x2bd70f1ffc702672 0xc2bd70f1ffc70267

def z719 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x7738f7f9e0fc3f87 0xd7738f7f9e0fc3f8

def z720 : W := mkw 0x011d80007a6a8003 0x8011d80007a6a800 0xb8df80007fffc00f 0x3b8df80007fffc00

def z721 : W := mkw 0x22e06d0ad6857352 0x222e06d0ad685735 0x23c8f11ffc8fd982 0x323c8f11ffc8fd98

def z722 : W := mkw 0x03fefcd50400104c 0x003fefcd50400104 0xffffffff9c000078 0xfffffffff9c00007

def z723 : W := mkw 0x03fefcd57248000f 0x003fefcd57248000 0xfffffffffffc000f 0xffffffffffffc000

def z724 : W := mkw 0x2000032a81956e30 0x52000032a81956e3 0xd0288f1f83fffe7f 0xfd0288f1f83fffe7

def z725 : W := mkw 0x6401032adfb77f72 0x76401032adfb77f7 0x000000007fffffff 0x0000000007ffffff

def z726 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x23c07e007f003fff 0xc23c07e007f003ff

def z727 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x8cd749e61cf33878 0x78cd749e61cf3387

def z728 : W := mkw 0x444348640c321848 0x1444348640c32184 0x2cd740e01c70387b 0x02cd740e01c70387

def z729 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x6bff80007fffc00f 0x06bff80007fffc00

def z730 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x471871f860fc3f84 0xd471871f860fc3f8

def z731 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff9c00000b 0xfffffffff9c00000

def z732 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x771870f8607c3f87 0xc771870f8607c3f8

def z733 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8fe007f003fff 0xff3e8fe007f003ff

def z734 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x7718f1ffe0fc3f87 0xf7718f1ffe0fc3f8

def z735 : W := mkw 0x02a0020057001562 0x602a002005700156 0xf3e070007f003fff 0xcf3e070007f003ff

def z736 : W := mkw 0x03bd800008220000 0x003bd80000822000 0xfbff80001fffc00f 0x3fbff80001fffc00

def z737 : W := mkw 0x82a591b85ab6aa82 0x982a591b85ab6aa8 0x8ce7f1f81f03ff88 0xe8ce7f1f81f03ff8

def z738 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff8303c008 0xfffffffff8303c00

def z739 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd779e61cf33ffb 0xfbcd779e61cf33ff

def z740 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0xffe7ffff80000000 0xeffe7ffff8000000

def z741 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd749e61cf3387b 0x42cd749e61cf3387

def z742 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf3288f1fe38fe67f 0xff3288f1fe38fe67

def z743 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff80001fffc008 0x3fbff80001fffc00

def z744 : W := mkw 0x03fefcd57248800f 0x803fefcd57248800 0xffffffffff0cc00f 0xfffffffffff0cc00

def z745 : W := mkw 0xa001032afbffeeb3 0xda001032afbffeeb 0x000000007fffffff 0x0000000007ffffff

def z746 : W := mkw 0xc55b58de2c6f12d9 0x0c55b58de2c6f12d 0xcbcf381e7c0f07fc 0xacbcf381e7c0f07f

def z747 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcdfc9ff9cf3387b 0x7bcdfc9ff9cf3387

def z748 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07f1fff003fff 0xcf3e07f1fff003ff

def z749 : W := mkw 0x23feffdf8185663c 0x423feffdf8185663 0x2fd770e0038fe67d 0x02fd770e0038fe67

def z750 : W := mkw 0x2000020a81054630 0x42000020a8105463 0xd0288f1f830fc67c 0xfd0288f1f830fc67

def z751 : W := mkw 0x00404a0005001460 0x400404a000500146 0xf3e07e007f003fff 0xcf3e07e007f003ff

def z752 : W := mkw 0x02e6ec450000000c 0x002e6ec450000000 0xfcffcfff80000000 0xffcffcfff8000000

def z753 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x4f3fffff80000000 0xf4f3fffff8000000

def z754 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf328ff1f838fe67d 0xff328ff1f838fe67

def z755 : W := mkw 0xa11d91baa8ffea91 0x9a11d91baa8ffea9 0x0c1f81ff80ffc000 0x30c1f81ff80ffc00

def z756 : W := mkw 0x0001000008220000 0x0000100000822000 0xb8d700001fffc00f 0x3b8d700001fffc00

def z757 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff88007fffe07f 0x7fbff88007fffe07

def z758 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x73c070007f003fff 0xc73c070007f003ff

def z759 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0xbcdfffff80000000 0xfbcdfffff8000000

def z760 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771070e060fc3f87 0xc771070e060fc3f8

def z761 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0xf738f1ffe3ffff8f 0xff738f1ffe3ffff8

def z762 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271871f860fc3f87 0x1271871f860fc3f8

def z763 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff81187fffc00f 0xffbff81187fffc00

def z764 : W := mkw 0x015dee002d6a9561 0xe015dee002d6a956 0x081ffe0000fffff0 0xf081ffe0000fffff

def z765 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff808fc000 0xfffffffff808fc00

def z766 : W := mkw 0x02e4ee0057001562 0x602e4ee005700156 0xfbe7fe007f003fff 0xefbe7fe007f003ff

def z767 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffffe0700002 0xfffffffffe070000

def z768 : W := mkw 0x004348440c221048 0x0004348440c22104 0xbcd749e61cf3387b 0x7bcd749e61cf3387

def z769 : W := mkw 0x46e7ee465f23957a 0xe46e7ee465f23957 0x88e78e061f03c078 0x288e78e061f03c07

def z770 : W := mkw 0x811810b020580881 0x1811810b02058088 0x271070e060703f82 0xc271070e060703f8

def z771 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffffe0000784 0xfffffffffe000078

def z772 : W := mkw 0x02a0020053000422 0x402a002005300042 0xf3e07e007f003fff 0xcf3e07e007f003ff

def z773 : W := mkw 0x02e7ee455f22956e 0xe02e7ee455f22956 0x88e78e079f03c078 0x288e78e079f03c07

def z774 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x771870f860fc1f87 0x9771870f860fc1f8

def z775 : W := mkw 0x47fec96676d9b85b 0x947fec96676d9b85 0x4728c9e6630cf874 0x44728c9e6630cf87

def z776 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff8619ffffc00f 0xbfbff8619ffffc00

def z777 : W := mkw 0x2000032a81956e30 0x52000032a81956e3 0xd4388fff83ffe67d 0xfd4388fff83ffe67

def z778 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xffffffffff003f8f 0xfffffffffff003f8

def z779 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e87f187f003fff 0xdf3e87f187f003ff

def z780 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288f1fe38fffff 0xfd0288f1fe38ffff

def z781 : W := mkw 0x46e36e445f22156a 0x646e36e445f22156 0x88e70e001f000078 0x088e70e001f00007

def z782 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xc0288f1f838fc67c 0xbc0288f1f838fc67

def z783 : W := mkw 0x2000020281014430 0x4200002028101443 0xd0288f1f838fc07d 0xfd0288f1f838fc07

def z784 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xb3c07e007c003ffb 0xcb3c07e007c003ff

def z785 : W := mkw 0x03beb4d50000000c 0x003beb4d50000000 0x7f3ff7ff80000000 0xf7f3ff7ff8000000

def z786 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xafffffff80000000 0x3afffffff8000000

def z787 : W := mkw 0x02e26e445700156a 0x602e26e445700156 0xfff77ee07f003fff 0xcfff77ee07f003ff

def z788 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd028ff1f838ffffd 0xfd028ff1f838ffff

def z789 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd741e61cf3387b 0x32cd741e61cf3387

def z790 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771871f863ffff8f 0xd771871f863ffff8

def z791 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xbcd749e61cfff87b 0x7bcd749e61cfff87

def z792 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271070e060703f82 0x0271070e060703f8

def z793 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x77187fffe0fc3f87 0xd77187fffe0fc3f8

def z794 : W := mkw 0x02e6ee455700156e 0x602e6ee455700156 0xfbefff1fff003fff 0xffbefff1fff003ff

def z795 : W := mkw 0x0000012800942a00 0x10000012800942a0 0x771871f860fc3f87 0xd771871f860fc3f8

def z796 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0xfffffffffc0039fb 0xffffffffffc0039f

def z797 : W := mkw 0x02e4ee0057009562 0xe02e4ee005700956 0xf3e0fe007f00ffff 0xcf3e0fe007f00fff

def z798 : W := mkw 0x0000020001000420 0x4000002000100042 0xd0288f1f838fe67d 0xfd0288f1f838fe67

def z799 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff80007fffff8f 0x3fbff80007fffff8

def z800 : W := mkw 0x8000012820dc2a81 0x18000012820dc2a8 0x771071e060fc3f87 0xd771071e060fc3f8

def z801 : W := mkw 0x03fefcd50400104c 0x003fefcd50400104 0xffffffff9c001802 0xfffffffff9c00180

def z802 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbffb0007fffc78f 0xbfbffb0007fffc78

def z803 : W := mkw 0x47bdb5b30cb33854 0x147bdb5b30cb3385 0x4328b6199cf3387b 0x84328b6199cf3387

def z804 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0xffffffff9c000000 0xfffffffff9c00000

def z805 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcf749e61ff3387f 0x7fcf749e61ff3387

def z806 : W := mkw 0x03fec84400000008 0x003fec8440000000 0xffffcfff80000000 0xfffffcfff8000000

def z807 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0x771871fe60ff3f87 0xf771871fe60ff3f8

def z808 : W := mkw 0x83f87fb877dc3fe3 0x783f87fb877dc3fe 0x84f80ff81ffc0078 0x184f80ff81ffc007

def z809 : W := mkw 0x00437cd57a6a800f 0x800437cd57a6a800 0x04007fffffffc00f 0xc04007fffffffc00

def z810 : W := mkw 0xe51b11fea8ff6a99 0x1e51b11fea8ff6a9 0x0c1f81ff80ffc000 0x30c1f81ff80ffc00

def z811 : W := mkw 0xa11812b2a1594cb1 0x5a11812b2a1594cb 0xa730fee7e373d9fa 0x2a730fee7e373d9f

def z812 : W := mkw 0x444348640c321848 0x1444348640c32184 0xbcd748e01cf3387b 0x7bcd748e01cf3387

def z813 : W := mkw 0x03bc909000000000 0x003bc90900000000 0xffffffff80000000 0xfffffffff8000000

def z814 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xbcd749e61cff3e7f 0x7bcd749e61cff3e7

def z815 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff830cc004 0xfffffffff830cc00

def z816 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e61cf30078 0x7bcd749e61cf3007

def z817 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf71879f860fc3fff 0xdf71879f860fc3ff

def z818 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x3cd749e61cf03873 0x53cd749e61cf0387

def z819 : W := mkw 0x811c91b820dcaa81 0x9811c91b820dcaa8 0x7718f1f860fcff87 0xd7718f1f860fcff8

def z820 : W := mkw 0x6401032a8db77e70 0x56401032a8db77e7 0x000000001cf33e7b 0x0000000001cf33e7

def z821 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x771871f8607c1f86 0xd771871f8607c1f8

def z822 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcf7cfe79cf3387b 0x7bcf7cfe79cf3387

def z823 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x80288f1f838fe67d 0x380288f1f838fe67

def z824 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xaff7ffff80000000 0xeaff7ffff8000000

def z825 : W := mkw 0x02e4ee0157001566 0x602e4ee015700156 0xf3e0fe01ff003fff 0xcf3e0fe01ff003ff

def z826 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0x88e780001fffc008 0x288e780001fffc00

def z827 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07e007f8fffff 0xcf3e07e007f8ffff

def z828 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xbbd700007fffc00f 0x3bbd700007fffc00

def z829 : W := mkw 0x02e26c4400000008 0x002e26c440000000 0xffffffff80000000 0xfffffffff8000000

def z830 : W := mkw 0x02e26e445700156a 0x602e26e445700156 0xfbe77e067f003fff 0xefbe77e067f003ff

def z831 : W := mkw 0x82e6ed6d20dc2a8d 0x182e6ed6d20dc2a8 0x88e78e07e0fc3f87 0x288e78e07e0fc3f8

def z832 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0xfbe780007fffc00f 0x2fbe780007fffc00

def z833 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x3cd741e01cf3387b 0x53cd741e01cf3387

def z834 : W := mkw 0x02a0260057001562 0x602a026005700156 0xd3203e007f003fff 0xcd3203e007f003ff

def z835 : W := mkw 0x23bcb699f34cc627 0xc23bcb699f34cc62 0x4328b619e30cc604 0x84328b619e30cc60

def z836 : W := mkw 0x03fefcd55600104e 0x003fefcd55600104 0xffffffffff00387f 0xfffffffffff00387

def z837 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771071f860703f87 0xc771071f860703f8

def z838 : W := mkw 0x444349640cb23848 0x1444349640cb2384 0xbcd749e01cf0387b 0x5bcd749e01cf0387

def z839 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e61ffff87f 0x7bcd749e61ffff87

def z840 : W := mkw 0x0042496404903848 0x1004249640490384 0xbcd749e61cf0387b 0x7bcd749e61cf0387

def z841 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf0388f1f83ffe67f 0xff0388f1f83ffe67

def z842 : W := mkw 0x03fefcd57248800f 0x803fefcd57248800 0xffffffffe0000000 0xfffffffffe000000

def z843 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3f07e007ff03fff 0xdf3f07e007ff03ff

def z844 : W := mkw 0x00404a0057001562 0x600404a005700156 0xf3c078007f003fff 0xcf3c078007f003ff

def z845 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffffe0000007 0xfffffffffe000000

def z846 : W := mkw 0x0118012020d82801 0x10118012020d8280 0x771871e060fc3f87 0xd771871e060fc3f8

def z847 : W := mkw 0x03beb4d50000000c 0x003beb4d50000000 0xffffb7ff80000000 0xbffffb7ff8000000

def z848 : W := mkw 0x64427fff85957e7c 0x564427fff85957e7 0x04007fff80003e70 0xc04007fff80003e7

def z849 : W := mkw 0x444348640c321848 0x1444348640c32184 0x2cd748e01c703872 0x42cd748e01c70387

def z850 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbfff0007fffc00f 0xffbfff0007fffc00

def z851 : W := mkw 0x02e26e445700156a 0x602e26e445700156 0xffffffffff003fff 0xfffffffffff003ff

def z852 : W := mkw 0x2000032a81956e30 0x52000032a81956e3 0xd428cfff838ffe7d 0xfd428cfff838ffe7

def z853 : W := mkw 0x444348460c231058 0x0444348460c23105 0xbcd749e61cf3007b 0x7bcd749e61cf3007

def z854 : W := mkw 0x03bda4007a6a8003 0x803bda4007a6a800 0xfbffb6007fffc00f 0xbfbffb6007fffc00

def z855 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x88ff80007fffc00f 0x388ff80007fffc00

def z856 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xfcdfc9ff9cfffe7f 0xffcdfc9ff9cfffe7

def z857 : W := mkw 0x03fefcd50400104c 0x003fefcd50400104 0xfffffffffc003fff 0xffffffffffc003ff

def z858 : W := mkw 0x02e06c0004001040 0x002e06c000400104 0xf3e07e007c003fff 0xcf3e07e007c003ff

def z859 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x8c3f8fff80000000 0x38c3f8fff8000000

def z860 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf8ff8f1f838fe67d 0xff8ff8f1f838fe67

def z861 : W := mkw 0x2000032a81956e30 0x52000032a81956e3 0xf738ffffe3ffffff 0xff738ffffe3fffff

def z862 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xbcd749fe1cf33e7b 0xfbcd749fe1cf33e7

def z863 : W := mkw 0x0000000004001040 0x0000000000400104 0x730070007c003fff 0xc730070007c003ff

def z864 : W := mkw 0x440301660cb33858 0x1440301660cb3385 0xbcd701e61cf3387b 0x3bcd701e61cf3387

def z865 : W := mkw 0x811810b020580881 0x1811810b02058088 0x771870e060fc3f87 0xd771870e060fc3f8

def z866 : W := mkw 0x0002004400000008 0x0000200440000000 0xdc3f8fff80000000 0xfdc3f8fff8000000

def z867 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xfff77fff80000000 0xcfff77fff8000000

def z868 : W := mkw 0x444348660c331858 0x1444348660c33185 0xbcd748e61c73387b 0x6bcd748e61c73387

def z869 : W := mkw 0x2000020a81054630 0x42000020a8105463 0xd0288e1f830fe67d 0xed0288e1f830fe67

def z870 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0xd8ef80007fffc00f 0x3d8ef80007fffc00

def z871 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcdfc9e61cfff87b 0x7bcdfc9e61cfff87

def z872 : W := mkw 0x02e6ee455700156e 0x602e6ee455700156 0xfff7ffe7ff003fff 0xffff7ffe7ff003ff

def z873 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x8cd709e61cf3387b 0x38cd709e61cf3387

def z874 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xfbf77e007f003fff 0xffbf77e007f003ff

def z875 : W := mkw 0xa3bc9298f34cc6a3 0xca3bc9298f34cc6a 0x4328b619e30cc784 0x84328b619e30cc78

def z876 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xc3e07e007f003ffc 0xcc3e07e007f003ff

def z877 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xffdf71f860fc3f87 0xfffdf71f860fc3f8

def z878 : W := mkw 0x4403016608b32818 0x14403016608b3281 0xbcd709e61cf3207b 0x7bcd709e61cf3207

def z879 : W := mkw 0x03bd90917a6a8007 0x803bd90917a6a800 0xfbff8019ffffc00f 0x3fbff8019ffffc00

def z880 : W := mkw 0x02a0260057001562 0x602a026005700156 0xf3e036007f003fff 0x8f3e036007f003ff

def z881 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0xfffffffffc003f87 0xffffffffffc003f8

def z882 : W := mkw 0x02e26e455700156e 0x602e26e455700156 0xf3e07e07ff003fff 0xcf3e07e07ff003ff

def z883 : W := mkw 0x44436d670cb3385c 0x144436d670cb3385 0xbcd74fe79cf3387b 0x7bcd74fe79cf3387

def z884 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xfffff0e07fffc00f 0x3fffff0e07fffc00

def z885 : W := mkw 0x46e7ee475f23157e 0x646e7ee475f23157 0x88e78e079f030078 0x288e78e079f03007

def z886 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771870e060fc3f87 0x1771870e060fc3f8

def z887 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd74fff9cf3387b 0xfbcd74fff9cf3387

def z888 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffffe3ffc00f 0xfffffffffe3ffc00

def z889 : W := mkw 0x03fefcd50400114c 0x203fefcd50400114 0xffffffff80001980 0xfffffffff8000198

def z890 : W := mkw 0x22e06e00d7005562 0x622e06e00d700556 0xf3e0fe01ff00ffff 0xcf3e0fe01ff00fff

def z891 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e61c70387b 0x4bcd749e61c70387

def z892 : W := mkw 0x011e92d55700156e 0x6011e92d55700156 0x0c1f81ffff003fff 0x30c1f81ffff003ff

def z893 : W := mkw 0x64426f6e85957f78 0x764426f6e85957f7 0x04007fff80003ff0 0xc04007fff80003ff

def z894 : W := mkw 0x66e36e46df23557a 0x666e36e46df23557 0x88e78e079f03c078 0x288e78e079f03c07

def z895 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xfcffc9fe1ffffe7f 0xffcffc9fe1ffffe7

def z896 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xffffffffffffc00f 0xfffffffffffffc00

def z897 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x6bff80007fffc006 0x36bff80007fffc00

def z898 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xacd748e61cf3387b 0x2acd748e61cf3387

def z899 : W := mkw 0x02a0260057001562 0x602a026005700156 0x030030007f003fff 0x0030030007f003ff

def z900 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd749e61cf33872 0x72cd749e61cf3387

def z901 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x4c3f87ff80000000 0xb4c3f87ff8000000

def z902 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x671870f860fc3f87 0x8671870f860fc3f8

def z903 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0x88c700007fffc00f 0x288c700007fffc00

def z904 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0x771879fe60fc3ff7 0xd771879fe60fc3ff

def z905 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xabf780007fffc00f 0x2abf780007fffc00

def z906 : W := mkw 0x444348660c331858 0x1444348660c33185 0x8cd708e61c730078 0x28cd708e61c73007

def z907 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e67cf33fff 0x7bcd749e67cf33ff

def z908 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xd8ff80001fffc00d 0x3d8ff80001fffc00

def z909 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf738ffffe3ffff8f 0xff738ffffe3ffff8

def z910 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xcbef80007fffc00f 0x2cbef80007fffc00

def z911 : W := mkw 0xc51f91ff28ff2a9d 0x1c51f91ff28ff2a9 0x0c1f81ff80ff0000 0x30c1f81ff80ff000

def z912 : W := mkw 0x03bdb4917a6a8007 0x803bdb4917a6a800 0xfffff7f9ffffc00f 0xffffff7f9ffffc00

def z913 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffff8fff80000000 0x3ffff8fff8000000

def z914 : W := mkw 0x011811b000902800 0x1011811b00090280 0x771871f860f03f87 0xd771871f860f03f8

def z915 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xc3e03e007f003fff 0x8c3e03e007f003ff

def z916 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0xf718f9ffe0ffffff 0xff718f9ffe0fffff

def z917 : W := mkw 0x02a0260057001562 0x602a026005700156 0x732076007f003fff 0xc732076007f003ff

def z918 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288f1f838fc07d 0x3d0288f1f838fc07

def z919 : W := mkw 0x02a100007a6a8003 0x802a100007a6a800 0xfbf700007fffc00f 0x3fbf700007fffc00

def z920 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07e007f833fff 0xff3e07e007f833ff

def z921 : W := mkw 0x811810b020580881 0x1811810b02058088 0x771871f860703f87 0xd771871f860703f8

def z922 : W := mkw 0x02e06c0056001142 0x202e06c005600114 0xf3c078007c003fff 0xcf3c078007c003ff

def z923 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xcfffbfff80000000 0xbcfffbfff8000000

def z924 : W := mkw 0x02e26e445700156a 0x602e26e445700156 0xf7e07fe67f003fff 0xcf7e07fe67f003ff

def z925 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffff80fc0000 0xfffffffff80fc000

def z926 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcd749e61cf33e7f 0xffcd749e61cf33e7

def z927 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e87e007f8c3fff 0xdf3e87e007f8c3ff

def z928 : W := mkw 0xa11811b8a0dc6a81 0x1a11811b8a0dc6a8 0x7718f1f9e0fcff87 0xd7718f1f9e0fcff8

def z929 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80830009 0xfffffffff8083000

def z930 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0xf8ff80007fffc00f 0x3f8ff80007fffc00

def z931 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8fe19ff003fff 0xcf3e8fe19ff003ff

def z932 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x6ffff7ff80000000 0xb6ffff7ff8000000

def z933 : W := mkw 0x0046fcd50000000c 0x00046fcd50000000 0x0c07ffff80000000 0xe0c07ffff8000000

def z934 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x671871f8607c3f86 0xc671871f8607c3f8

def z935 : W := mkw 0x03bdb4917a6a8007 0x803bdb4917a6a800 0xfbffb0007fffc00f 0x3fbffb0007fffc00

def z936 : W := mkw 0xc443496e0cb73ad8 0x1c443496e0cb73ad 0xbcd749e61cf33ffb 0x7bcd749e61cf33ff

def z937 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd709e61cf3007b 0x3bcd709e61cf3007

def z938 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xffffc1e07fffc00f 0x7ffffc1e07fffc00

def z939 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf438cfff838fe67d 0xff438cfff838fe67

def z940 : W := mkw 0x03fefcd57248800f 0x803fefcd57248800 0xffffffffe38fc00d 0xfffffffffe38fc00

def z941 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0x8cc77fff80000000 0xe8cc77fff8000000

def z942 : W := mkw 0x0043494608a32018 0x00043494608a3201 0xbcd749e61cf3207b 0x7bcd749e61cf3207

def z943 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xbfd77fff80000000 0xfbfd77fff8000000

def z944 : W := mkw 0x02e27cd50000000c 0x002e27cd50000000 0xfff77fff80000000 0xffff77fff8000000

def z945 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbfd779e67cf339fb 0x7bfd779e67cf339f

def z946 : W := mkw 0x811811b020d82881 0x1811811b020d8288 0x771071e060f03f87 0xd771071e060f03f8

def z947 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcffc9e61cf3387b 0x7fcffc9e61cf3387

def z948 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbffc0007ffff80f 0x7fbffc0007ffff80

def z949 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffffe00c0004 0xfffffffffe00c000

def z950 : W := mkw 0x83fefcd52048008d 0x083fefcd52048008 0xffffffffe0000180 0xfffffffffe000018

def z951 : W := mkw 0x03fefcd52048800d 0x803fefcd52048800 0xffffffff800cc000 0xfffffffff800cc00

def z952 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xcfefffff80000000 0xecfefffff8000000

def z953 : W := mkw 0x0000010200812010 0x0000001020081201 0xd0288f1f838fe07d 0xfd0288f1f838fe07

def z954 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e0fe007f03ffff 0xef3e0fe007f03fff

def z955 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x63e07e007f003ff6 0xc63e07e007f003ff

def z956 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x371071e060fc3f87 0x5371071e060fc3f8

def z957 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x43207e007f003fff 0xc43207e007f003ff

def z958 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xa3e07e007f003fff 0x0a3e07e007f003ff

def z959 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf738f1f860fc3f87 0xff738f1f860fc3f8

def z960 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xacd749e61c73387a 0x6acd749e61c73387

def z961 : W := mkw 0xe4425bfe85957ef8 0x5e4425bfe85957ef 0x04007fff80003ff0 0xc04007fff80003ff

def z962 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x80288f1f838fe678 0xf80288f1f838fe67

def z963 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd740e01cf3387b 0x3bcd740e01cf3387

def z964 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf7f07fe07f003fff 0xdf7f07fe07f003ff

def z965 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0x08c700007fffc00f 0x008c700007fffc00

def z966 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xffd779e61cf3387b 0xfffd779e61cf3387

def z967 : W := mkw 0x011eb4d50000000c 0x0011eb4d50000000 0x0c1fb7ff80000000 0xb0c1fb7ff8000000

def z968 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80002079 0xfffffffff8000207

def z969 : W := mkw 0x0001012208b32810 0x10001012208b3281 0xbcd749e61cf3387b 0x7bcd749e61cf3387

def z970 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff8300000d 0xfffffffff8300000

def z971 : W := mkw 0x02a580005a228002 0x802a580005a22800 0xf8ff80001fffc00f 0x3f8ff80001fffc00

def z972 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x470871f860fc3f87 0xc470871f860fc3f8

def z973 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x6fffffff80000000 0xc6fffffff8000000

def z974 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80003f80 0xfffffffff80003f8

def z975 : W := mkw 0x644349668cb37858 0x1644349668cb3785 0xbcd7c9e79cf3f87b 0x7bcd7c9e79cf3f87

def z976 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x271071f860fc3f87 0xc271071f860fc3f8

def z977 : W := mkw 0xa000032a81956eb0 0x5a000032a81956eb 0xd0288f1f838ffffd 0xfd0288f1f838ffff

def z978 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0x0c1f8fff80000000 0x30c1f8fff8000000

def z979 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff89067fffc00f 0x7fbff89067fffc00

def z980 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xfcffcfff9cfff87b 0xffcffcfff9cfff87

def z981 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0x0c177fff80000000 0xc0c177fff8000000

def z982 : W := mkw 0x83bd90907a6a8083 0x883bd90907a6a808 0xfbffb0007fffc18f 0x3fbffb0007fffc18

def z983 : W := mkw 0x0000020057001562 0x6000002005700156 0xf3207e007f003fff 0xcf3207e007f003ff

def z984 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e070007f003fff 0x0f3e070007f003ff

def z985 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff8e07ffffc00f 0x3fbff8e07ffffc00

def z986 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff808c0005 0xfffffffff808c000

def z987 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0xdc3fffff80000000 0xfdc3fffff8000000

def z988 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x2cd740e01c703872 0x02cd740e01c70387

def z989 : W := mkw 0x03fefcd52048000d 0x003fefcd52048000 0xffffffffe0fc3f87 0xfffffffffe0fc3f8

def z990 : W := mkw 0x83bcb698734c87a3 0xe83bcb698734c87a 0x4328b618630cc784 0x84328b618630cc78

def z991 : W := mkw 0x44436d660cb33958 0x344436d660cb3395 0xbcd779e61cf339fb 0x7bcd779e61cf339f

def z992 : W := mkw 0x011d8000286a8001 0x8011d8000286a800 0xf8ff80001fffc00f 0x3f8ff80001fffc00

def z993 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xc0288e1f838fe67d 0xac0288e1f838fe67

def z994 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x771871f860703f82 0xd771871f860703f8

def z995 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07f067f003fff 0xff3e07f067f003ff

def z996 : W := mkw 0xc51911ba28ff2a91 0x1c51911ba28ff2a9 0x041801f800ff0000 0x1041801f800ff000

def z997 : W := mkw 0x03bda4007a6a8103 0xa03bda4007a6a810 0xfbffb0007fffc18f 0x3fbffb0007fffc18

def z998 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xbcdf49fe1cff387b 0x7bcdf49fe1cff387

def z999 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0xbcf7ffff80000000 0xfbcf7ffff8000000

def z1000 : W := mkw 0x011900007a6a8003 0x8011900007a6a800 0xfbdf00007fffc00f 0x3fbdf00007fffc00

def z1001 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xfcffcfff9cff3e7f 0xffcffcfff9cff3e7

def z1002 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x63e076007f003fff 0x863e076007f003ff

def z1003 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf028cf1f838ffe7f 0xff028cf1f838ffe7

def z1004 : W := mkw 0x2000020a81054630 0x42000020a8105463 0x80288e1f830fc078 0x280288e1f830fc07

def z1005 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xfffffffffc000002 0xffffffffffc00000

def z1006 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x8cffffff80000000 0xf8cffffff8000000

def z1007 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf7387ff860fc3f87 0xdf7387ff860fc3f8

def z1008 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xb8ff80001fffc00b 0x3b8ff80001fffc00

def z1009 : W := mkw 0x00406e0057001562 0x600406e005700156 0x73007e007f003fff 0xc73007e007f003ff

def z1010 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e07e007c003ff2 0xcf3e07e007c003ff

def z1011 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8ff1fff8fffff 0xff3e8ff1fff8ffff

def z1012 : W := mkw 0x03beb4d50000000c 0x003beb4d50000000 0x0c3f87ff80000000 0x30c3f87ff8000000

def z1013 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0xdcefffff80000000 0xfdcefffff8000000

def z1014 : W := mkw 0x03bda4017a6a8007 0x803bda4017a6a800 0xfbff8601ffffc00f 0x3fbff8601ffffc00

def z1015 : W := mkw 0x0118109020480001 0x0011810902048000 0x771871f860fc3f87 0xd771871f860fc3f8

def z1016 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0xff3fffff80000000 0xfff3fffff8000000

def z1017 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0xf738f9fe63ffffff 0xff738f9fe63fffff

def z1018 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcf7c9e61ff3f87b 0x7bcf7c9e61ff3f87

def z1019 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xcbff80007fffc00c 0x3cbff80007fffc00

def z1020 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0x771871f860ff3fff 0xd771871f860ff3ff

def z1021 : W := mkw 0x444348660c331858 0x1444348660c33185 0xbcd749e61c73187a 0x7bcd749e61c73187

def z1022 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd749e61c703872 0x7bcd749e61c70387

def z1023 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcffcfff9ffff87f 0xffcffcfff9ffff87

def z1024 : W := mkw 0x03fffcd57e6a914f 0xa03fffcd57e6a914 0x2fd770e07c701982 0x02fd770e07c70198

def z1025 : W := mkw 0x03fefcd50400104c 0x003fefcd50400104 0xffffffff80003870 0xfffffffff8000387

def z1026 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0x0c177fff80000000 0xf0c177fff8000000

def z1027 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xc0288f1f830fe67c 0xec0288f1f830fe67

def z1028 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xffffffff9f000008 0xfffffffff9f00000

def z1029 : W := mkw 0x811810b020580881 0x1811810b02058088 0x671070e060701f86 0x8671070e060701f8

def z1030 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x7738f1f863fcff87 0xd7738f1f863fcff8

def z1031 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf71879fe60fc3f87 0xff71879fe60fc3f8

def z1032 : W := mkw 0x00406e0005001560 0x600406e000500156 0xf3c07e007c003fff 0xcf3c07e007c003ff

def z1033 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbf700007fffc00f 0x0fbf700007fffc00

def z1034 : W := mkw 0x811c91b920dc2a85 0x1811c91b920dc2a8 0x7718f1f9e0fc3f87 0xd7718f1f9e0fc3f8

def z1035 : W := mkw 0x000100007a6a8003 0x8000100007a6a800 0x28d700007fffc00f 0x028d700007fffc00

def z1036 : W := mkw 0x0000020057001562 0x6000002005700156 0x430030007f003fff 0x8430030007f003ff

def z1037 : W := mkw 0x02e6ee455700156e 0x602e6ee455700156 0xfbe77e007f003fff 0xcfbe77e007f003ff

def z1038 : W := mkw 0x015a58d400000008 0x0015a58d40000000 0xffffffff80000000 0xfffffffff8000000

def z1039 : W := mkw 0x47fffcf57e7a984f 0x947fffcf57e7a984 0x2fd770e07c701802 0x02fd770e07c70180

def z1040 : W := mkw 0x015efcd50000000c 0x0015efcd50000000 0x7f1fffff80000000 0xf7f1fffff8000000

def z1041 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xbcd748e01cf3387b 0x4bcd748e01cf3387

def z1042 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xa3e07e007f003ffa 0xca3e07e007f003ff

def z1043 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x271070e0607c1f86 0x0271070e0607c1f8

def z1044 : W := mkw 0x800011b820dc2a81 0x1800011b820dc2a8 0x770071f860fc3f87 0xc770071f860fc3f8

def z1045 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e0fe07ff003fff 0xef3e0fe07ff003ff

def z1046 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80003803 0xfffffffff8000380

def z1047 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x371071f860f03f83 0xd371071f860f03f8

def z1048 : W := mkw 0x004149200cb23840 0x1004149200cb2384 0xbcd749e01cf3387b 0x7bcd749e01cf3387

def z1049 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80002605 0xfffffffff8000260

def z1050 : W := mkw 0x015a7cd50000000c 0x0015a7cd50000000 0xffdf7fff80000000 0xfffdf7fff8000000

def z1051 : W := mkw 0x2000020a81054630 0x42000020a8105463 0xd0288e1f838fc67d 0xbd0288e1f838fc67

def z1052 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xacd749e61cf3187a 0x3acd749e61cf3187

def z1053 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff8e007fffc00f 0xffbff8e007fffc00

def z1054 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0x0cc77fff80000000 0xc0cc77fff8000000

def z1055 : W := mkw 0x011e90d50000000c 0x0011e90d50000000 0x0c1f8fff80000000 0xf0c1f8fff8000000

def z1056 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0x9cd709e61cf32079 0x79cd709e61cf3207

def z1057 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbfff0007fffd98f 0x3fbfff0007fffd98

def z1058 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x2fdfffff80000000 0xf2fdfffff8000000

def z1059 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd0288f1f838fc078 0xfd0288f1f838fc07

def z1060 : W := mkw 0x444348660c331858 0x1444348660c33185 0xbcd748e61cf3187b 0x3bcd748e61cf3187

def z1061 : W := mkw 0x0000002000100800 0x1000000200010080 0x771070e060703f87 0xc771070e060703f8

def z1062 : W := mkw 0x03bdb4917a6a8007 0x803bdb4917a6a800 0xfbffbf1fffffc00f 0xffbffbf1fffffc00

def z1063 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcf74fe61cf3387b 0xffcf74fe61cf3387

def z1064 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x2bdf80007fffc00f 0x32bdf80007fffc00

def z1065 : W := mkw 0x02a580007a6a8003 0x802a580007a6a800 0xb8f780007fffc00f 0x3b8f780007fffc00

def z1066 : W := mkw 0x64424b6e85957e78 0x564424b6e85957e7 0x040049e600003e70 0x4040049e600003e7

def z1067 : W := mkw 0x02e6fcd50000000c 0x002e6fcd50000000 0x8ce78fff80000000 0x28ce78fff8000000

def z1068 : W := mkw 0x6401032afffffe73 0xd6401032afffffe7 0x000000007ffffe7f 0x0000000007ffffe7

def z1069 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0xf3e8fe007f0cffff 0xcf3e8fe007f0cfff

def z1070 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcdf49e61cff387f 0x7fcdf49e61cff387

def z1071 : W := mkw 0x0042484400000008 0x0004248440000000 0xbcd74fff80000000 0xfbcd74fff8000000

def z1072 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0x2cd77fff80000000 0xc2cd77fff8000000

def z1073 : W := mkw 0x0000020057001562 0x6000002005700156 0x230070007f003fff 0x0230070007f003ff

def z1074 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xd328bf1fe38fe7fd 0xfd328bf1fe38fe7f

def z1075 : W := mkw 0x02e0480056001042 0x002e048005600104 0xf3e078007f003fff 0xcf3e078007f003ff

def z1076 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0x771871ffe0fc3f87 0xd771871ffe0fc3f8

def z1077 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x7718f1f860ffff87 0xf7718f1f860ffff8

def z1078 : W := mkw 0x444348640c321848 0x1444348640c32184 0xbcd749e61c70387b 0x7bcd749e61c70387

def z1079 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0x671871f860fc1f86 0x9671871f860fc1f8

def z1080 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffffe0001982 0xfffffffffe000198

def z1081 : W := mkw 0x00427cd50000000c 0x000427cd50000000 0xfcffffff80000000 0xffcffffff8000000

def z1082 : W := mkw 0x02a100005a220002 0x002a100005a22000 0xfbff80007fffc00f 0x3fbff80007fffc00

def z1083 : W := mkw 0x03fefcd55200010e 0x203fefcd55200010 0xffffffffe0000180 0xfffffffffe000018

def z1084 : W := mkw 0x2000030a81856630 0x42000030a8185663 0xf0e88f1f9f8fe67f 0xff0e88f1f9f8fe67

def z1085 : W := mkw 0x44436d660cb33858 0x144436d660cb3385 0xbcd77fe61cf3387b 0xfbcd77fe61cf3387

def z1086 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0x7bdf00007fffc00f 0x17bdf00007fffc00

def z1087 : W := mkw 0x444348660c331858 0x1444348660c33185 0x2cd748e61c701872 0x02cd748e61c70187

def z1088 : W := mkw 0x03beb4d50000000c 0x003beb4d50000000 0xdf3fbfff80000000 0xfdf3fbfff8000000

def z1089 : W := mkw 0x811811b820dc2a81 0x1811811b820dc2a8 0xf73871f863fc3f8f 0xdf73871f863fc3f8

def z1090 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x90288f1f838fe079 0x790288f1f838fe07

def z1091 : W := mkw 0x811c91b820dc2a81 0x1811c91b820dc2a8 0x7f1ff1f860fc3f87 0xf7f1ff1f860fc3f8

def z1092 : W := mkw 0x83bcb699734c07a7 0x683bcb699734c07a 0x4328b619e30c0784 0x84328b619e30c078

def z1093 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x23c070007c003ff2 0x023c070007c003ff

def z1094 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x40288f1f838fe67d 0xc40288f1f838fe67

def z1095 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0x7fdf7fff80000000 0xd7fdf7fff8000000

def z1096 : W := mkw 0x2000030a81856630 0x42000030a8185663 0x40288f1f838fe674 0xf40288f1f838fe67

def z1097 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0x771871f860ffff87 0xd771871f860ffff8

def z1098 : W := mkw 0x444348660c331858 0x1444348660c33185 0x2cd740e01c73187a 0x02cd740e01c73187

def z1099 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xbcffcfff80000000 0x7bcffcfff8000000

def z1100 : W := mkw 0x6401032a89b76e30 0x56401032a89b76e3 0x0000000003ffe67d 0x00000000003ffe67

def z1101 : W := mkw 0x444348640c321848 0x1444348640c32184 0xacd748e01c70187a 0x0acd748e01c70187

def z1102 : W := mkw 0xa11811baa0dd6a91 0x1a11811baa0dd6a9 0xf738ffffe0ffff87 0xff738ffffe0ffff8

def z1103 : W := mkw 0x03bcb69173488527 0xe03bcb6917348852 0x4328b619e30cc784 0x84328b619e30cc78

def z1104 : W := mkw 0x03fefcd55600114e 0x203fefcd55600114 0xffffffffff00198f 0xfffffffffff00198

def z1105 : W := mkw 0xe401032aadff7ef1 0x5e401032aadff7ef 0x000000007fffffff 0x0000000007ffffff

def z1106 : W := mkw 0x01190000286a0001 0x001190000286a000 0xfbff80007fffc00f 0x3fbff80007fffc00

def z1107 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xffffffffff8fc00f 0xfffffffffff8fc00

def z1108 : W := mkw 0x6443496e8cb77a58 0x16443496e8cb77a5 0xbcd749ff9cf3387b 0x7bcd749ff9cf3387

def z1109 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xabff80007fffc00a 0x3abff80007fffc00

def z1110 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xfcdf49fe1cf3387b 0xffcdf49fe1cf3387

def z1111 : W := mkw 0x03fefcd55200000e 0x003fefcd55200000 0xffffffffe3000004 0xfffffffffe300000

def z1112 : W := mkw 0x444349660cb33858 0x1444349660cb3385 0xffd749e67cf3387f 0x7ffd749e67cf3387

def z1113 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xffff81f87fffc00f 0x3ffff81f87fffc00

def z1114 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff80007fffe60f 0xffbff80007fffe60

def z1115 : W := mkw 0x811810b8205c0a81 0x1811810b8205c0a8 0x271070f860701f82 0x8271070f860701f8

def z1116 : W := mkw 0xc51f91fe28ffaa99 0x9c51f91fe28ffaa9 0x0c1f81fe00ffc000 0x30c1f81fe00ffc00

def z1117 : W := mkw 0x015ed8d50000000c 0x0015ed8d50000000 0xfcffcfff80000000 0xffcffcfff8000000

def z1118 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xfffff1f87fffff8f 0xffffff1f87fffff8

def z1119 : W := mkw 0x03fefcd55200800e 0x803fefcd55200800 0xffffffff8300c000 0xfffffffff8300c00

def z1120 : W := mkw 0x4443496e0cb73a58 0x14443496e0cb73a5 0xffdf79fe7cff3fff 0xfffdf79fe7cff3ff

def z1121 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xffffffff80f00003 0xfffffffff80f0000

def z1122 : W := mkw 0x03bd90907a6a8003 0x803bd90907a6a800 0xfbffb0187fffc00f 0xbfbffb0187fffc00

def z1123 : W := mkw 0x03fefcd50000000c 0x003fefcd50000000 0xdcff8fff80000000 0xfdcff8fff8000000

def z1124 : W := mkw 0x03be90d50000000c 0x003be90d50000000 0xffff8fff80000000 0xfffff8fff8000000

def z1125 : W := mkw 0x02e06e0057001562 0x602e06e005700156 0x73c07e007c003ff7 0xc73c07e007c003ff

def z1126 : W := mkw 0x03bd80007a6a8003 0x803bd80007a6a800 0xfbff811fffffc00f 0x3fbff811fffffc00

def z1127 : W := mkw 0x811811ba20dd2a91 0x1811811ba20dd2a9 0xf738ffffe0ff3fff 0xff738ffffe0ff3ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z8,z4,z5,z6]),(0,[z2,z7,z3,z4,z9,z10,z6]),(0,[z2,z7,z3,z4,z5,z6,z11]),(0,[z2,z7,z3,z4,z5,z6,z12]),(0,[z2,z7,z3,z4,z5,z6,z13]),(0,[z2,z7,z3,z4,z5,z14,z6])],[(0,[z2,z7,z15,z16,z4,z5,z6]),(0,[z2,z7,z3,z4,z17,z5,z6]),(1,[z2,z18,z7,z4,z5,z6]),(0,[z19,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z20,z4,z5,z6]),(0,[z2,z21,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z22,z23]),(0,[z2,z7,z24,z3,z4,z5,z6]),(0,[z25,z7,z3,z4,z5,z6,z26])],[(0,[z27,z2,z7,z3,z4,z28,z6]),(0,[z29,z2,z7,z3,z4,z5,z6]),(0,[z30,z2,z7,z3,z4,z5,z6]),(0,[z31,z2,z7,z4,z5,z6,z32]),(0,[z2,z33,z7,z3,z4,z5,z6])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(1,[z2,z34,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z35,z5,z6]),(0,[z36,z2,z3,z37,z4,z5,z6]),(0,[z2,z38,z7,z3,z39,z5,z6]),(0,[z2,z7,z3,z4,z40,z5,z6]),(0,[z2,z7,z3,z4,z41,z5,z6]),(0,[z2,z7,z3,z4,z5,z42,z6])],[(0,[z2,z7,z3,z4,z43,z5,z6]),(0,[z2,z7,z3,z4,z5,z44,z6]),(0,[z2,z7,z3,z4,z5,z6,z45])],[(0,[z2,z7,z3,z4,z5,z46,z6]),(1,[z2,z7,z47,z4,z5,z6]),(0,[z48,z2,z7,z3,z4,z49,z6]),(0,[z50,z2,z7,z3,z4,z5,z51]),(0,[z52,z53,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z54,z6]),(0,[z2,z55,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z56,z4,z5,z6])],[(0,[z2,z7,z3,z4,z57,z5,z6]),(0,[z58,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z59,z4,z5,z6])]],
   [[(0,[z2,z60,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z61,z6]),(0,[z2,z7,z3,z4,z5,z62,z6]),(0,[z2,z7,z3,z4,z63,z5,z6]),(0,[z2,z64,z7,z3,z4,z5,z6])],[(0,[z65,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z66,z5,z6]),(1,[z31,z2,z7,z4,z5,z32]),(0,[z2,z7,z3,z4,z5,z67,z6]),(0,[z2,z68,z7,z3,z4,z5,z6])],[(0,[z69,z2,z7,z37,z4,z5,z6]),(0,[z2,z7,z3,z70,z4,z5,z6]),(0,[z71,z2,z7,z3,z4,z5,z6]),(0,[z72,z2,z7,z3,z4,z5,z6]),(0,[z2,z73,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z74,z6]),(0,[z75,z2,z7,z3,z4,z5,z6])],[(0,[z7,z3,z15,z4,z76,z5,z6]),(0,[z36,z2,z3,z77,z4,z5,z6]),(0,[z78,z2,z79,z7,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z80]),(0,[z2,z7,z81,z3,z4,z5,z6]),(0,[z2,z7,z3,z82,z4,z5,z6]),(1,[z83,z2,z7,z3,z4,z26])],[(0,[z84,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z85,z6]),(0,[z86,z2,z7,z3,z4,z5,z87])],[(0,[z2,z7,z88,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z89])],[(0,[z90,z2,z7,z3,z4,z5,z6]),(0,[z2,z91,z7,z15,z4,z5,z6])]],
   [[(0,[z2,z92,z7,z3,z4,z5,z6]),(0,[z93,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z94]),(0,[z2,z7,z3,z95,z96,z5,z6]),(0,[z97,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z98,z4,z5,z6]),(1,[z7,z3,z4,z5,z6,z99])],[(0,[z100,z2,z7,z3,z4,z5,z6]),(0,[z101,z2,z3,z4,z39,z5,z6]),(0,[z2,z7,z3,z102,z4,z5,z6]),(0,[z2,z7,z3,z4,z9,z5,z22])],[(0,[z2,z7,z3,z103,z4,z5,z6]),(0,[z2,z7,z104,z37,z4,z5,z6]),(0,[z2,z79,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z105,z6]),(0,[z2,z7,z3,z106,z4,z5,z6]),(0,[z2,z7,z3,z4,z107,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z108])],[(0,[z2,z7,z109,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z110,z5,z6]),(0,[z2,z7,z3,z4,z5,z111,z6]),(0,[z2,z7,z3,z4,z28,z6,z26])],[],[(0,[z2,z7,z3,z4,z5,z112,z6]),(0,[z2,z7,z104,z3,z113,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z114,z5,z6]),(1,[z115,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z116,z117,z5,z6]),(0,[z2,z7,z3,z4,z5,z118,z6])],[(0,[z2,z7,z3,z4,z5,z6,z119]),(0,[z2,z7,z3,z4,z120,z5,z6]),(0,[z2,z7,z3,z4,z5,z121,z6]),(0,[z2,z7,z3,z4,z5,z6,z122]),(0,[z2,z7,z3,z4,z5,z87,z6]),(0,[z123,z2,z7,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z124,z28,z6])],[(0,[z125,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z126,z5,z6]),(0,[z127,z69,z7,z3,z4,z5,z6]),(0,[z2,z7,z128,z3,z4,z5,z6]),(0,[z2,z129,z7,z3,z4,z5,z6])],[(0,[z2,z2,z7,z3,z4,z5,z6]),(0,[z27,z2,z7,z3,z4,z10,z6]),(0,[z2,z7,z3,z4,z5,z130,z6]),(0,[z131,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z132])],[(0,[z133,z2,z7,z3,z4,z5,z6]),(0,[z2,z3,z37,z4,z134,z5,z6]),(0,[z135,z2,z7,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z136,z2,z7,z4,z113,z5,z6]),(0,[z2,z7,z3,z4,z137,z5,z6]),(0,[z2,z138,z7,z3,z4,z5,z6]),(1,[z2,z139,z3,z4,z5,z6]),(0,[z2,z140,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z141,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z142,z6])],[(0,[z143,z2,z7,z3,z4,z5,z6]),(1,[z2,z79,z3,z4,z134,z6]),(0,[z53,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z117,z144,z6]),(0,[z2,z7,z3,z4,z5,z145,z6])]],
   [[(0,[z127,z7,z3,z4,z5,z10,z6]),(0,[z2,z7,z3,z4,z146,z5,z6]),(0,[z147,z2,z7,z3,z4,z5,z6]),(0,[z148,z2,z7,z3,z4,z5,z6]),(0,[z52,z149,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z23,z32]),(1,[z2,z7,z4,z5,z150,z6])],[(0,[z151,z2,z7,z3,z4,z5,z6]),(0,[z148,z2,z38,z3,z4,z5,z6]),(0,[z36,z2,z7,z3,z4,z152,z6]),(0,[z2,z7,z3,z96,z4,z5,z6])],[(0,[z2,z7,z3,z95,z5,z6,z153]),(0,[z2,z7,z3,z154,z4,z5,z6]),(0,[z155,z2,z7,z3,z4,z5,z6]),(0,[z2,z156,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z157,z5,z6])],[],[(0,[z158,z2,z7,z3,z4,z5,z6]),(0,[z159,z2,z7,z3,z4,z5,z6])],[(1,[z2,z7,z3,z160,z5,z6]),(0,[z161,z2,z7,z3,z4,z5,z6]),(1,[z2,z7,z104,z16,z5,z6])],[(0,[z162,z2,z7,z3,z4,z5,z6]),(0,[z163,z2,z7,z3,z4,z5,z6]),(0,[z164,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z117,z6,z26]),(0,[z165,z2,z7,z3,z4,z5,z6])],[(0,[z2,z166,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z4,z5,z6]),(1,[z50,z2,z3,z4,z5,z51])]],
   [[(0,[z167,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z168,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z169,z6]),(0,[z170,z2,z7,z3,z4,z5,z6]),(1,[z171,z2,z7,z3,z5,z153]),(0,[z2,z7,z3,z4,z5,z6,z172])],[(0,[z173,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z174,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z175,z5,z6]),(1,[z176,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z177,z5,z6]),(0,[z2,z7,z3,z4,z9,z117,z6])],[(0,[z2,z7,z178,z3,z4,z5,z6]),(0,[z179,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z180,z4,z5,z6]),(0,[z48,z7,z3,z15,z4,z5,z6]),(0,[z181,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z182,z6]),(0,[z2,z7,z3,z183,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z184]),(0,[z185,z2,z7,z3,z4,z5,z6])],[(0,[z186,z7,z3,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z32]),(0,[z171,z2,z7,z3,z4,z187,z6])],[(0,[z2,z7,z3,z4,z188,z5,z6]),(0,[z173,z7,z3,z95,z4,z5,z6]),(0,[z2,z34,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z49,z5,z6]),(0,[z189,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z190,z6]),(0,[z149,z2,z7,z3,z4,z144,z6])],[(0,[z48,z2,z7,z3,z4,z5,z112]),(0,[z191,z2,z7,z3,z4,z5,z6]),(0,[z192,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z193,z6]),(1,[z2,z194,z3,z4,z5,z6]),(0,[z2,z7,z3,z195,z4,z5,z6]),(0,[z2,z7,z3,z116,z4,z5,z6])],[(0,[z2,z196,z7,z37,z4,z5,z6]),(0,[z2,z91,z7,z3,z4,z5,z42]),(0,[z2,z7,z197,z3,z4,z5,z6]),(1,[z2,z7,z3,z198,z5,z6])]],
   [[(0,[z2,z7,z7,z3,z4,z5,z6]),(0,[z199,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z95,z4,z200,z6]),(0,[z2,z201,z202,z3,z4,z5,z6])],[(0,[z203,z2,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z49,z6]),(1,[z204,z7,z3,z4,z5,z112]),(0,[z136,z2,z91,z7,z4,z5,z6]),(0,[z2,z7,z205,z3,z4,z5,z6]),(0,[z149,z2,z7,z3,z4,z41,z6])],[(0,[z206,z2,z7,z154,z4,z5,z6]),(0,[z2,z7,z3,z207,z4,z5,z6]),(1,[z48,z7,z3,z4,z5,z208]),(0,[z2,z7,z3,z209,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z87,z153]),(0,[z2,z7,z3,z4,z5,z210,z6]),(0,[z7,z3,z4,z5,z6,z99,z26])],[(0,[z2,z7,z3,z4,z211,z5,z6]),(0,[z212,z2,z7,z3,z4,z5,z6]),(0,[z7,z3,z95,z4,z76,z5,z6]),(0,[z213,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z214,z3,z4,z5,z6]),(0,[z48,z2,z7,z3,z4,z5,z208]),(0,[z2,z7,z3,z215,z4,z5,z6])],[(0,[z216,z2,z7,z3,z4,z5,z6]),(0,[z148,z2,z7,z3,z4,z217,z6]),(0,[z2,z7,z3,z4,z5,z6,z218]),(0,[z219,z2,z7,z3,z5,z28,z6]),(1,[z25,z7,z3,z4,z5,z6])],[(0,[z127,z186,z7,z3,z4,z5,z6]),(0,[z69,z2,z91,z7,z4,z5,z6]),(0,[z220,z2,z7,z3,z4,z5,z6]),(1,[z2,z38,z3,z77,z5,z6]),(0,[z50,z2,z18,z7,z4,z5,z6])],[(0,[z2,z7,z221,z3,z4,z5,z6]),(0,[z48,z7,z3,z4,z222,z5,z6]),(0,[z204,z2,z7,z3,z4,z9,z5]),(0,[z2,z7,z3,z4,z5,z6,z223])],[(0,[z224,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z225]),(0,[z171,z2,z7,z3,z96,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z226,z5,z6]),(0,[z2,z7,z3,z227,z4,z5,z6]),(0,[z228,z2,z7,z3,z4,z5,z6]),(0,[z149,z229,z7,z3,z4,z5,z6]),(0,[z2,z230,z7,z3,z4,z5,z6]),(0,[z171,z2,z7,z3,z4,z145,z6])],[(0,[z127,z173,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z5,z231]),(0,[z232,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z233,z5,z6])],[(1,[z2,z7,z3,z4,z234,z6]),(0,[z2,z7,z3,z4,z5,z23,z51])],[(0,[z235,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z236,z5,z6]),(0,[z83,z2,z7,z3,z4,z5,z22])],[(0,[z2,z7,z3,z4,z5,z6,z237]),(0,[z136,z2,z7,z4,z41,z5,z6]),(0,[z2,z7,z3,z4,z238,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z239]),(0,[z2,z7,z3,z240,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z200,z6]),(0,[z2,z7,z3,z241,z4,z5,z6]),(0,[z242,z2,z7,z3,z4,z5,z6]),(0,[z149,z136,z2,z7,z4,z5,z6]),(0,[z148,z2,z7,z3,z77,z5,z6]),(0,[z243,z2,z7,z3,z4,z5,z6]),(0,[z244,z2,z7,z3,z4,z5,z6])],[(0,[z245,z2,z7,z3,z4,z5,z6]),(0,[z246,z2,z7,z3,z4,z5,z6]),(0,[z247,z173,z7,z3,z4,z5,z6]),(0,[z248,z2,z7,z3,z4,z5,z6]),(0,[z249,z2,z7,z3,z4,z5,z6]),(1,[z2,z196,z37,z4,z5,z6]),(0,[z2,z91,z7,z37,z4,z5,z6]),(0,[z148,z2,z3,z4,z39,z5,z6]),(0,[z250,z2,z7,z3,z4,z5,z6]),(0,[z52,z251,z7,z3,z4,z5,z6])],[(0,[z69,z2,z7,z4,z5,z144,z6]),(0,[z2,z7,z3,z4,z5,z6,z252]),(0,[z2,z7,z3,z4,z253,z5,z6]),(0,[z254,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z255,z3,z4,z5,z6]),(0,[z2,z7,z256,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z198,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z5,z257,z6]),(0,[z2,z7,z3,z4,z5,z258,z6]),(0,[z2,z7,z3,z95,z4,z5,z231]),(0,[z2,z7,z3,z4,z5,z259,z6]),(0,[z2,z260,z7,z3,z4,z5,z6])],[(0,[z261,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z95,z4,z234,z6]),(0,[z2,z7,z3,z4,z5,z6,z262]),(0,[z2,z7,z3,z4,z5,z6,z263]),(0,[z2,z264,z7,z3,z4,z5,z6])],[(0,[z7,z265,z3,z4,z76,z5,z6]),(0,[z2,z7,z3,z266,z4,z5,z6]),(0,[z267,z2,z7,z3,z4,z5,z6]),(0,[z52,z2,z7,z3,z4,z268,z6])],[(0,[z269,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z270,z4,z5,z6]),(0,[z2,z201,z7,z3,z4,z5,z6])],[(0,[z0,z173,z7,z3,z4,z5,z6]),(0,[z206,z2,z7,z3,z4,z222,z6]),(0,[z2,z7,z3,z4,z5,z271,z6])],[(0,[z69,z2,z7,z16,z4,z5,z6]),(1,[z2,z7,z272,z4,z5,z6]),(0,[z27,z2,z7,z3,z4,z117,z6]),(0,[z2,z7,z3,z4,z5,z273,z6])],[(0,[z2,z7,z3,z4,z274,z5,z6]),(0,[z2,z7,z3,z4,z117,z152,z6]),(0,[z2,z7,z3,z4,z5,z6,z51]),(0,[z2,z7,z3,z5,z23,z6,z153])],[(0,[z275,z2,z7,z3,z4,z5,z6]),(0,[z48,z2,z7,z3,z4,z5,z153]),(0,[z2,z7,z3,z4,z5,z276,z6]),(0,[z148,z2,z7,z3,z39,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z277]),(1,[z2,z202,z3,z4,z5,z6]),(0,[z31,z2,z7,z3,z4,z5,z32]),(0,[z2,z7,z3,z278,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z279,z6]),(0,[z280,z2,z7,z3,z4,z5,z6])]],
   [[(1,[z2,z7,z3,z4,z281,z6]),(0,[z171,z2,z7,z3,z5,z6,z153])],[(0,[z282,z2,z7,z3,z4,z5,z6]),(0,[z52,z2,z7,z3,z113,z5,z6]),(0,[z2,z7,z3,z4,z283,z5,z6])],[(0,[z2,z7,z3,z4,z5,z284,z6]),(0,[z285,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z286,z4,z5,z6]),(0,[z2,z7,z3,z4,z41,z28,z6])],[(0,[z287,z2,z7,z3,z4,z5,z6]),(0,[z288,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z289,z6]),(0,[z290,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z291]),(0,[z2,z7,z3,z4,z5,z292,z6]),(0,[z293,z2,z7,z3,z4,z5,z6])],[(0,[z136,z2,z7,z3,z4,z5,z6])],[(0,[z86,z2,z265,z3,z4,z5,z6]),(0,[z294,z2,z7,z3,z4,z5,z6]),(0,[z295,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z39,z5,z6])],[(0,[z0,z158,z7,z3,z4,z5,z6]),(1,[z246,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z296,z6]),(0,[z297,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z298,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z299,z5,z6])],[(0,[z69,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z222,z9,z6]),(0,[z300,z2,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z96,z5,z23])],[(0,[z2,z301,z7,z3,z4,z5,z6]),(0,[z149,z155,z7,z3,z4,z5,z6]),(0,[z2,z7,z4,z5,z42,z6,z32])],[(0,[z2,z7,z3,z302,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z303,z6]),(0,[z86,z2,z7,z3,z4,z5,z51]),(0,[z52,z2,z7,z3,z4,z5,z273]),(1,[z2,z7,z3,z4,z5,z304])],[(0,[z2,z7,z3,z4,z5,z305,z6]),(0,[z2,z7,z3,z4,z9,z5,z26])],[(0,[z306,z2,z7,z3,z4,z5,z6]),(0,[z307,z2,z7,z3,z4,z5,z6]),(0,[z101,z136,z2,z7,z4,z5,z6]),(0,[z2,z201,z7,z3,z4,z41,z6]),(0,[z2,z7,z308,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z309]),(0,[z2,z7,z3,z4,z5,z310,z6]),(0,[z311,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z312,z5,z6])],[(0,[z2,z7,z3,z4,z5,z313,z6]),(0,[z314,z2,z7,z3,z4,z5,z6]),(0,[z48,z2,z7,z241,z4,z5,z6]),(1,[z2,z7,z98,z4,z5,z6]),(0,[z2,z3,z77,z4,z134,z5,z6])]],
   [[(1,[z298,z7,z3,z4,z5,z6])],[(0,[z315,z2,z7,z3,z4,z5,z6]),(0,[z52,z2,z7,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z316,z6]),(0,[z69,z2,z201,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z317,z6])],[(1,[z2,z7,z3,z4,z5,z6]),(0,[z318,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z319,z4,z5,z6]),(0,[z2,z7,z3,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z32,z153])],[(0,[z246,z158,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z320,z4,z5,z6]),(1,[z247,z7,z3,z76,z5,z6]),(0,[z2,z7,z3,z4,z321,z5,z6]),(0,[z322,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z323,z6]),(0,[z2,z7,z3,z4,z5,z6,z324]),(0,[z2,z7,z3,z4,z5,z325,z6]),(0,[z219,z2,z7,z3,z4,z5,z304])],[(0,[z2,z7,z3,z326,z4,z5,z6]),(0,[z7,z3,z4,z222,z5,z10,z6]),(0,[z327,z2,z7,z3,z4,z5,z6]),(1,[z2,z214,z3,z4,z5,z6]),(0,[z2,z7,z3,z328,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z329,z6]),(0,[z2,z7,z3,z4,z9,z5,z6])],[(0,[z2,z7,z3,z4,z5,z330,z6]),(0,[z2,z79,z7,z331,z4,z5,z6]),(0,[z2,z7,z3,z4,z134,z28,z6]),(0,[z2,z7,z3,z4,z134,z117,z6]),(1,[z2,z7,z3,z4,z5,z332]),(1,[z333,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z334,z6])],[(0,[z2,z7,z3,z4,z335,z5,z6]),(0,[z36,z2,z3,z4,z5,z152,z6]),(0,[z2,z7,z3,z4,z336,z5,z6]),(0,[z2,z7,z3,z4,z5,z42,z153]),(0,[z2,z337,z7,z3,z4,z5,z6])]],
   [[(0,[z338,z2,z7,z3,z4,z5,z6]),(0,[z69,z186,z2,z7,z4,z5,z6]),(0,[z148,z2,z7,z98,z4,z5,z6]),(0,[z2,z79,z7,z3,z4,z134,z6]),(0,[z2,z7,z3,z4,z5,z87,z23]),(0,[z2,z7,z202,z3,z4,z5,z6]),(0,[z2,z7,z4,z5,z150,z28,z6])],[(0,[z2,z7,z3,z4,z5,z6,z339]),(0,[z127,z69,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z95,z4,z5,z6]),(1,[z206,z7,z3,z4,z10,z6]),(0,[z148,z298,z7,z3,z4,z5,z6]),(0,[z50,z2,z3,z4,z5,z6,z51]),(0,[z2,z7,z3,z4,z340,z5,z6]),(0,[z31,z341,z2,z3,z4,z5,z6]),(1,[z156,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z117,z5,z28,z6]),(1,[z2,z7,z3,z82,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z342]),(0,[z101,z2,z196,z3,z4,z5,z6]),(1,[z148,z2,z3,z39,z5,z6]),(1,[z2,z7,z331,z4,z5,z6]),(1,[z2,z343,z3,z4,z5,z6]),(0,[z2,z7,z344,z3,z4,z5,z6]),(0,[z345,z2,z7,z3,z4,z5,z6])],[(0,[z346,z2,z7,z3,z4,z5,z6]),(0,[z347,z2,z7,z3,z4,z5,z6]),(0,[z219,z2,z7,z3,z4,z5,z6]),(0,[z348,z2,z7,z3,z4,z5,z6])],[(0,[z136,z2,z3,z37,z4,z5,z6]),(0,[z36,z2,z79,z3,z4,z5,z6]),(1,[z2,z7,z141,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z349])],[(0,[z2,z7,z3,z4,z350,z5,z6]),(0,[z136,z2,z7,z4,z5,z6,z32]),(0,[z2,z351,z7,z3,z4,z5,z6]),(0,[z2,z7,z352,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z222,z5,z6]),(0,[z148,z2,z7,z3,z4,z5,z353]),(0,[z354,z2,z7,z3,z4,z5,z6])],[(0,[z2,z3,z4,z134,z5,z152,z6])]],
   [[(0,[z2,z7,z3,z4,z355,z5,z6]),(0,[z2,z7,z15,z4,z5,z6,z32]),(1,[z2,z7,z154,z4,z5,z6]),(1,[z249,z2,z7,z3,z4,z5]),(0,[z2,z7,z3,z4,z152,z28,z6]),(1,[z356,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z96,z4,z5,z23])],[(1,[z186,z7,z15,z4,z5,z6]),(0,[z127,z7,z3,z4,z5,z112,z6]),(0,[z2,z7,z3,z357,z4,z5,z6]),(0,[z2,z358,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z359,z5,z6])],[(0,[z173,z7,z3,z15,z4,z5,z6]),(0,[z204,z7,z3,z4,z5,z112,z6]),(0,[z2,z7,z3,z4,z5,z360,z6]),(0,[z31,z2,z139,z3,z4,z5,z6])],[(0,[z2,z7,z361,z3,z4,z5,z6]),(0,[z2,z7,z362,z3,z4,z5,z6]),(0,[z206,z2,z7,z3,z4,z28,z6]),(0,[z363,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z364,z5,z6]),(0,[z2,z7,z3,z4,z365,z5,z6]),(1,[z2,z7,z3,z4,z274,z6]),(0,[z366,z2,z7,z3,z4,z5,z6])],[(0,[z127,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z76,z5,z6,z153]),(0,[z2,z7,z3,z4,z5,z367,z6]),(0,[z52,z2,z7,z104,z4,z5,z6]),(0,[z368,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z369])],[(0,[z2,z7,z3,z4,z5,z5,z6]),(0,[z2,z7,z3,z4,z5,z370,z6]),(0,[z204,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z371,z5,z6]),(1,[z2,z7,z3,z4,z217,z6]),(0,[z2,z194,z7,z3,z4,z5,z6])],[(0,[z2,z265,z3,z4,z5,z6,z51]),(0,[z2,z7,z3,z4,z5,z372,z6]),(0,[z2,z7,z3,z4,z373,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z374]),(1,[z375,z2,z3,z4,z5,z6])]],
   [[(0,[z376,z2,z7,z3,z4,z5,z6]),(0,[z127,z27,z7,z3,z4,z5,z6])],[(0,[z2,z377,z7,z3,z4,z5,z6]),(0,[z2,z378,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z379]),(0,[z380,z2,z7,z3,z4,z5,z6]),(0,[z83,z2,z7,z3,z4,z9,z6])],[(0,[z381,z2,z7,z3,z4,z5,z6]),(0,[z247,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z4,z41,z5,z144,z6]),(0,[z2,z382,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z383,z5,z6]),(0,[z2,z7,z3,z4,z384,z5,z6]),(1,[z229,z7,z3,z4,z5,z6])],[(1,[z2,z201,z7,z4,z41,z6]),(0,[z2,z7,z3,z4,z5,z385,z6])],[(0,[z2,z7,z3,z4,z386,z5,z6]),(0,[z48,z2,z7,z3,z4,z5,z23]),(0,[z148,z2,z7,z3,z4,z274,z6]),(0,[z2,z201,z7,z4,z41,z5,z6]),(0,[z2,z7,z3,z4,z5,z387,z6]),(0,[z2,z7,z3,z4,z187,z5,z6])],[(0,[z2,z7,z3,z4,z388,z5,z6]),(0,[z186,z2,z7,z15,z4,z5,z6]),(0,[z2,z196,z7,z3,z4,z5,z6]),(0,[z2,z7,z37,z4,z113,z5,z6]),(0,[z389,z2,z7,z3,z4,z5,z6]),(0,[z390,z2,z7,z3,z4,z5,z6]),(0,[z391,z2,z7,z3,z4,z5,z6])],[(0,[z392,z2,z7,z3,z4,z5,z6]),(1,[z86,z2,z3,z4,z5,z87]),(0,[z393,z2,z7,z3,z4,z5,z6]),(0,[z2,z229,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z153,z26]),(0,[z2,z7,z3,z4,z5,z22,z6])]],
   [[(0,[z0,z2,z7,z3,z4,z5,z6]),(0,[z394,z2,z7,z3,z4,z5,z6]),(0,[z27,z2,z7,z3,z4,z5,z6])],[(0,[z395,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z396,z6])],[(0,[z2,z7,z3,z4,z5,z231,z6]),(0,[z48,z2,z7,z3,z4,z397,z6]),(0,[z50,z86,z2,z3,z4,z5,z6]),(0,[z356,z2,z201,z3,z4,z5,z6]),(0,[z341,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z222,z6,z26]),(0,[z2,z7,z343,z3,z4,z5,z6])],[(0,[z2,z7,z3,z398,z4,z5,z6]),(0,[z2,z7,z16,z4,z113,z5,z6])],[(0,[z399,z2,z7,z3,z4,z5,z6]),(1,[z27,z7,z3,z4,z222,z6]),(0,[z2,z7,z3,z400,z4,z5,z6]),(0,[z2,z7,z3,z96,z4,z5,z153]),(0,[z83,z2,z7,z3,z4,z5,z26])],[(1,[z173,z7,z3,z95,z5,z6])],[(0,[z173,z2,z7,z357,z4,z5,z6]),(0,[z48,z2,z7,z3,z401,z5,z6]),(0,[z2,z7,z3,z402,z4,z5,z6]),(0,[z2,z7,z3,z4,z403,z5,z6]),(0,[z404,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z405,z2,z7,z3,z4,z5,z6]),(0,[z406,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z407]),(0,[z2,z7,z3,z408,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z409,z6]),(0,[z410,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z411,z6])],[(0,[z173,z2,z7,z3,z95,z5,z6]),(0,[z2,z7,z3,z4,z5,z412,z6]),(0,[z2,z7,z3,z4,z5,z217,z6]),(0,[z2,z7,z3,z413,z4,z5,z6]),(1,[z78,z2,z7,z4,z5,z6]),(0,[z86,z2,z3,z4,z5,z87,z6]),(0,[z2,z414,z7,z3,z4,z5,z6])],[(1,[z2,z7,z241,z4,z5,z6]),(0,[z415,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z26])],[(0,[z416,z2,z7,z3,z4,z5,z6]),(0,[z206,z2,z7,z3,z4,z10,z6]),(0,[z2,z7,z3,z417,z4,z5,z6])],[(0,[z2,z7,z3,z4,z418,z5,z6]),(0,[z2,z7,z3,z4,z5,z419,z6]),(0,[z2,z91,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z304]),(0,[z420,z2,z7,z3,z4,z5,z6])],[(0,[z421,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z422,z3,z4,z5,z6]),(0,[z423,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z424,z4,z5,z6]),(0,[z83,z2,z7,z3,z4,z5,z6])],[(0,[z148,z36,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z425,z4,z5,z6]),(0,[z2,z7,z104,z3,z16,z5,z6]),(1,[z2,z7,z3,z116,z117,z6]),(0,[z171,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z96,z76,z5,z6]),(0,[z426,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z281,z5,z6]),(0,[z427,z2,z7,z3,z4,z5,z6])],[(0,[z428,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z429,z5,z6]),(0,[z2,z430,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z431,z6])],[(0,[z1,z7,z265,z3,z4,z5,z6]),(0,[z2,z7,z3,z432,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z433,z6]),(0,[z2,z7,z3,z4,z10,z6,z26]),(0,[z2,z7,z3,z37,z4,z5,z6]),(0,[z2,z434,z7,z3,z4,z5,z6]),(0,[z2,z435,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z5,z385]),(0,[z2,z7,z3,z4,z5,z6,z436])],[(0,[z437,z2,z7,z3,z4,z5,z6]),(0,[z2,z79,z7,z3,z4,z152,z6]),(0,[z31,z2,z91,z7,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z6]),(0,[z2,z7,z3,z438,z4,z5,z6])],[(0,[z2,z7,z3,z401,z4,z5,z6]),(0,[z2,z196,z3,z37,z4,z5,z6]),(0,[z439,z2,z7,z3,z4,z5,z6]),(0,[z440,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z441,z6]),(0,[z2,z7,z3,z4,z41,z117,z6]),(0,[z2,z7,z3,z4,z5,z42,z23])],[(0,[z7,z3,z15,z4,z5,z10,z6]),(0,[z2,z7,z3,z4,z76,z5,z6]),(0,[z2,z3,z37,z4,z5,z6,z51]),(0,[z2,z7,z3,z4,z5,z442,z6]),(0,[z50,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z443])],[(0,[z2,z7,z3,z4,z5,z6,z444]),(0,[z2,z7,z3,z4,z5,z445,z6]),(0,[z2,z7,z3,z4,z446,z5,z6]),(0,[z375,z2,z3,z4,z5,z28,z6])]],
   [[(0,[z447,z2,z7,z3,z4,z5,z6]),(0,[z448,z2,z7,z3,z4,z5,z6]),(0,[z115,z2,z7,z3,z4,z5,z6]),(1,[z53,z7,z3,z4,z5,z6])],[(0,[z69,z7,z3,z15,z4,z5,z6]),(0,[z173,z2,z7,z3,z76,z5,z6]),(0,[z449,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z104,z16,z4,z5,z6]),(0,[z450,z2,z7,z3,z4,z5,z6])],[(0,[z48,z206,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z77,z4,z5,z6])],[(0,[z2,z7,z451,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z452,z5,z6]),(0,[z2,z453,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z454,z6]),(0,[z219,z2,z7,z3,z4,z5,z385])],[(0,[z2,z7,z3,z4,z455,z5,z6]),(0,[z206,z7,z3,z4,z5,z10,z6]),(0,[z48,z2,z34,z3,z4,z5,z6]),(0,[z456,z2,z7,z3,z4,z5,z6]),(0,[z2,z201,z7,z3,z4,z144,z6]),(0,[z31,z2,z7,z3,z4,z5,z42])],[(0,[z2,z7,z3,z4,z457,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z458]),(0,[z149,z2,z7,z37,z4,z5,z6]),(0,[z2,z7,z37,z4,z41,z5,z6]),(0,[z459,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z460,z6]),(0,[z461,z2,z7,z3,z4,z5,z6]),(0,[z462,z2,z7,z3,z4,z5,z6])],[(0,[z158,z2,z265,z3,z4,z5,z6]),(0,[z2,z7,z3,z463,z4,z5,z6]),(0,[z48,z2,z7,z47,z4,z5,z6]),(0,[z2,z3,z37,z4,z39,z5,z6])],[(1,[z2,z7,z3,z4,z5,z464]),(0,[z465,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z150,z6])]],
   [[(0,[z27,z2,z7,z3,z4,z222,z6]),(0,[z101,z2,z3,z4,z134,z5,z6]),(0,[z50,z2,z7,z141,z4,z5,z6])],[(0,[z2,z7,z3,z466,z4,z5,z6]),(0,[z2,z7,z3,z4,z467,z5,z6]),(0,[z86,z2,z7,z3,z4,z5,z6]),(0,[z2,z468,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z469]),(0,[z25,z2,z7,z3,z4,z5,z6])],[(0,[z470,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z471]),(0,[z2,z472,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z473])],[(0,[z2,z7,z3,z4,z474,z5,z6]),(0,[z2,z475,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z112,z6,z208]),(0,[z2,z7,z16,z4,z41,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z476])],[(0,[z2,z7,z3,z4,z5,z477,z6]),(0,[z2,z7,z104,z3,z4,z5,z6]),(0,[z91,z156,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z478]),(0,[z2,z7,z3,z95,z4,z5,z464]),(0,[z2,z7,z3,z4,z5,z6,z479]),(0,[z2,z480,z7,z3,z4,z5,z6]),(0,[z83,z2,z7,z3,z198,z5,z6])],[(0,[z481,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z482,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z483,z5,z6]),(0,[z484,z2,z7,z3,z4,z5,z6]),(0,[z52,z2,z7,z4,z113,z5,z6]),(0,[z176,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z5,z485,z6]),(1,[z2,z7,z3,z4,z5,z353]),(0,[z2,z7,z3,z4,z5,z51,z153]),(0,[z171,z2,z7,z3,z4,z5,z153])],[(0,[z2,z7,z3,z4,z486,z5,z6]),(0,[z2,z7,z3,z4,z5,z487,z6]),(0,[z2,z7,z3,z4,z5,z6,z488]),(0,[z489,z2,z7,z3,z4,z5,z6])],[(0,[z2,z490,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z491])],[(1,[z158,z265,z3,z4,z5,z6]),(0,[z115,z173,z2,z7,z4,z5,z6]),(0,[z52,z2,z194,z3,z4,z5,z6])],[(0,[z492,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z493,z6]),(0,[z48,z7,z3,z4,z5,z6,z208]),(0,[z2,z7,z3,z4,z5,z494,z6]),(0,[z2,z7,z3,z4,z5,z495,z6]),(0,[z496,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z497])],[(0,[z2,z7,z498,z3,z4,z5,z6]),(0,[z2,z499,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z500,z6])],[(0,[z2,z7,z3,z4,z5,z501,z6]),(0,[z2,z7,z3,z4,z5,z502,z6]),(0,[z7,z3,z4,z222,z5,z112,z6]),(1,[z2,z7,z3,z4,z397,z6]),(0,[z2,z7,z3,z4,z503,z5,z6])],[(0,[z504,z2,z7,z3,z4,z5,z6]),(0,[z505,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z506]),(0,[z2,z7,z3,z4,z5,z367,z10]),(0,[z31,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z0,z7,z3,z4,z76,z5,z6]),(0,[z507,z2,z7,z3,z4,z5,z6]),(0,[z2,z18,z7,z3,z4,z5,z6])],[(0,[z36,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z9,z22,z6])],[(0,[z2,z7,z3,z4,z5,z508,z6]),(0,[z2,z7,z509,z3,z4,z5,z6]),(0,[z2,z510,z7,z3,z4,z5,z6]),(0,[z2,z511,z7,z3,z4,z5,z6]),(0,[z512,z2,z7,z3,z4,z5,z6]),(0,[z513,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z514])],[(0,[z158,z7,z265,z3,z4,z5,z6]),(1,[z127,z69,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z515]),(0,[z2,z7,z3,z516,z4,z5,z6])],[(0,[z517,z2,z7,z3,z4,z5,z6]),(0,[z69,z2,z7,z4,z5,z6,z32]),(0,[z518,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z519,z5,z6])],[(0,[z520,z2,z7,z3,z4,z5,z6]),(0,[z101,z2,z7,z37,z4,z5,z6])],[(0,[z158,z2,z7,z319,z4,z5,z6]),(0,[z206,z2,z7,z3,z4,z117,z6])],[(0,[z521,z2,z7,z3,z4,z5,z6]),(1,[z2,z7,z357,z4,z5,z6]),(0,[z2,z522,z7,z3,z4,z5,z6]),(0,[z523,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z2,z524,z7,z3,z4,z5,z6]),(0,[z525,z2,z7,z3,z4,z5,z6])],[(0,[z173,z7,z265,z3,z4,z5,z6]),(0,[z204,z2,z7,z3,z4,z5,z112]),(0,[z2,z7,z3,z526,z4,z5,z6])],[(0,[z101,z2,z38,z3,z4,z5,z6]),(0,[z2,z7,z3,z527,z4,z5,z6])],[(0,[z48,z2,z7,z3,z4,z9,z5]),(0,[z2,z7,z3,z4,z5,z6,z528])],[(0,[z2,z529,z7,z3,z4,z5,z6]),(0,[z530,z2,z7,z3,z4,z5,z6]),(0,[z531,z2,z7,z3,z4,z5,z6])],[(0,[z532,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z533]),(0,[z204,z2,z7,z3,z4,z5,z23]),(0,[z148,z524,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z534,z5,z6]),(0,[z535,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z536,z5,z6]),(0,[z48,z2,z7,z3,z160,z5,z6]),(0,[z204,z2,z7,z3,z4,z5,z208]),(0,[z2,z38,z7,z3,z77,z5,z6])],[(0,[z537,z2,z7,z3,z4,z5,z6]),(0,[z2,z79,z3,z4,z134,z5,z6]),(0,[z2,z91,z7,z4,z5,z42,z6])]],
   [[(0,[z27,z7,z3,z15,z4,z5,z6]),(0,[z2,z7,z15,z4,z5,z144,z6]),(0,[z2,z7,z3,z4,z5,z538,z6]),(0,[z2,z7,z3,z116,z4,z28,z6])],[(0,[z2,z7,z3,z4,z5,z6,z539]),(0,[z52,z2,z7,z3,z16,z5,z6])],[(0,[z2,z7,z3,z4,z540,z5,z6]),(0,[z541,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z23,z26])],[(0,[z249,z2,z7,z3,z4,z5,z10]),(0,[z2,z7,z3,z542,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z543,z6]),(0,[z2,z7,z3,z544,z4,z5,z6])],[(0,[z545,z2,z7,z3,z4,z5,z6]),(0,[z546,z2,z7,z3,z4,z5,z6])],[(0,[z1,z158,z2,z3,z4,z5,z6]),(0,[z52,z2,z7,z3,z4,z281,z6]),(0,[z2,z7,z3,z4,z5,z547,z6]),(0,[z2,z7,z3,z96,z5,z23,z6])],[(0,[z2,z7,z37,z4,z5,z6,z32]),(0,[z52,z2,z7,z4,z41,z5,z6]),(0,[z2,z7,z3,z4,z22,z6,z26])],[(0,[z50,z2,z7,z3,z4,z5,z87]),(0,[z2,z7,z3,z4,z548,z5,z6]),(0,[z2,z7,z3,z4,z5,z144,z6])]],
   [[(0,[z549,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z550,z4,z5,z6]),(0,[z2,z7,z3,z4,z551,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z552])],[(0,[z2,z7,z3,z4,z5,z6,z553]),(0,[z554,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z555,z4,z5,z6])],[(0,[z48,z204,z7,z3,z4,z5,z6]),(1,[z2,z7,z498,z4,z5,z6])],[(0,[z556,z2,z7,z3,z4,z5,z6]),(0,[z52,z69,z2,z7,z4,z5,z6]),(0,[z27,z7,z3,z4,z222,z5,z6]),(0,[z2,z7,z3,z4,z557,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z558]),(0,[z219,z2,z7,z3,z116,z5,z6]),(0,[z2,z7,z3,z4,z5,z23,z6])],[(0,[z559,z2,z7,z3,z4,z5,z6]),(0,[z560,z2,z7,z3,z4,z5,z6]),(0,[z561,z2,z7,z3,z4,z5,z6]),(0,[z562,z2,z7,z3,z4,z5,z6]),(0,[z148,z2,z3,z4,z134,z5,z6]),(0,[z2,z563,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z96,z116,z5,z6])],[(0,[z2,z564,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z565]),(0,[z2,z7,z3,z16,z4,z5,z6])],[(0,[z2,z7,z15,z37,z4,z5,z6]),(0,[z48,z83,z2,z7,z3,z4,z5]),(0,[z176,z2,z7,z4,z5,z28,z6])],[(0,[z101,z2,z3,z4,z5,z6,z51]),(0,[z375,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z566,z5,z6])]],
   [[(0,[z567,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z568,z4,z5,z6]),(1,[z2,z7,z3,z4,z145,z6])],[(0,[z569,z2,z7,z3,z4,z5,z6]),(0,[z2,z570,z7,z3,z4,z5,z6]),(0,[z571,z2,z7,z3,z4,z5,z6]),(0,[z572,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z464]),(0,[z573,z2,z7,z3,z4,z5,z6]),(1,[z251,z7,z3,z4,z5,z6]),(0,[z574,z2,z7,z3,z4,z5,z6])],[(0,[z575,z2,z7,z3,z4,z5,z6]),(0,[z247,z2,z7,z3,z95,z5,z6]),(0,[z204,z2,z7,z3,z4,z5,z153]),(0,[z576,z2,z7,z3,z4,z5,z6]),(0,[z149,z2,z7,z4,z5,z144,z6])],[(0,[z2,z7,z3,z4,z5,z577,z6]),(0,[z148,z2,z7,z498,z4,z5,z6])],[(0,[z2,z7,z3,z4,z578,z5,z6]),(0,[z206,z2,z7,z272,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z2,z201,z7,z15,z4,z5,z6]),(0,[z48,z127,z7,z3,z4,z5,z6]),(0,[z2,z251,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z268,z6]),(0,[z2,z7,z3,z579,z4,z5,z6])],[(0,[z580,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z581,z6]),(0,[z2,z7,z3,z4,z5,z10,z6]),(0,[z2,z7,z3,z4,z582,z5,z6]),(0,[z2,z7,z3,z4,z117,z5,z6]),(0,[z171,z2,z7,z3,z4,z5,z23])],[(0,[z2,z7,z3,z4,z5,z583,z6]),(0,[z52,z2,z7,z3,z4,z5,z6])]],
   [[(0,[z149,z2,z7,z16,z4,z5,z6]),(1,[z155,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z584]),(0,[z83,z2,z7,z3,z82,z5,z6])],[(0,[z2,z7,z3,z585,z4,z5,z6]),(0,[z2,z7,z3,z3,z4,z5,z6]),(0,[z2,z3,z77,z4,z39,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z586]),(1,[z341,z2,z3,z4,z5,z6])],[(0,[z587,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z588,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z353]),(0,[z2,z7,z3,z4,z5,z589,z6]),(0,[z2,z7,z3,z4,z5,z590,z6]),(0,[z2,z7,z3,z4,z5,z6,z99])],[(0,[z2,z7,z3,z591,z4,z5,z6]),(0,[z2,z7,z3,z4,z592,z5,z6]),(0,[z2,z3,z4,z5,z87,z6,z51]),(0,[z52,z2,z7,z3,z4,z5,z332]),(0,[z2,z7,z3,z4,z5,z6,z332]),(0,[z2,z7,z3,z4,z5,z6,z593]),(0,[z333,z2,z7,z3,z4,z5,z6]),(0,[z594,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z595]),(0,[z2,z7,z3,z4,z5,z22,z153])],[(0,[z2,z7,z3,z4,z5,z6,z208]),(0,[z2,z7,z3,z4,z596,z5,z6]),(0,[z2,z7,z3,z4,z134,z5,z6])],[(0,[z2,z7,z3,z4,z5,z597,z6]),(0,[z2,z7,z47,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z124,z6])],[(0,[z1,z2,z3,z4,z5,z6,z51]),(0,[z2,z7,z598,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z599,z6]),(0,[z356,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z600,z5,z6])],[(0,[z7,z3,z15,z4,z5,z112,z6]),(0,[z136,z2,z7,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z601]),(0,[z52,z2,z343,z3,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z5,z602,z6]),(0,[z603,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z604,z3,z4,z5,z6]),(0,[z2,z7,z605,z3,z4,z5,z6]),(0,[z247,z2,z7,z3,z76,z5,z6]),(0,[z606,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z607,z5,z6]),(0,[z2,z7,z3,z331,z4,z5,z6]),(0,[z608,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z609,z6]),(0,[z610,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z144,z28,z6])],[(0,[z2,z7,z611,z3,z4,z5,z6]),(0,[z612,z2,z7,z3,z4,z5,z6])],[(0,[z136,z2,z196,z7,z4,z5,z6]),(0,[z2,z38,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z613,z5,z6]),(0,[z614,z2,z7,z3,z4,z5,z6]),(0,[z149,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z615]),(0,[z2,z7,z3,z5,z28,z6,z153])],[(0,[z2,z7,z3,z4,z616,z5,z6]),(0,[z2,z617,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z234,z5,z6]),(0,[z206,z7,z3,z4,z5,z112,z6]),(1,[z101,z136,z2,z4,z5,z6]),(0,[z618,z2,z7,z3,z4,z5,z6])],[(1,[z2,z7,z3,z4,z5,z273]),(0,[z619,z2,z7,z3,z4,z5,z6]),(0,[z83,z2,z7,z3,z4,z6,z26])],[(0,[z2,z7,z620,z3,z4,z5,z6])]],
   [[(0,[z127,z7,z3,z4,z76,z5,z6]),(0,[z2,z7,z3,z4,z5,z621,z6]),(0,[z2,z7,z3,z4,z5,z6,z622]),(0,[z623,z2,z7,z3,z4,z5,z6]),(0,[z101,z86,z2,z3,z4,z5,z6]),(0,[z624,z2,z7,z3,z4,z5,z6])],[(0,[z206,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z625,z5,z6]),(0,[z2,z7,z3,z4,z5,z626,z6]),(0,[z2,z7,z3,z4,z627,z5,z6]),(0,[z2,z7,z3,z4,z5,z268,z6]),(0,[z628,z2,z7,z3,z4,z5,z6]),(0,[z2,z629,z7,z3,z4,z5,z6])],[(0,[z2,z91,z7,z3,z4,z5,z32]),(0,[z2,z7,z3,z4,z630,z5,z6]),(0,[z2,z7,z3,z4,z5,z631,z6])],[(0,[z2,z7,z3,z4,z5,z632,z6]),(0,[z633,z2,z7,z3,z4,z5,z6])],[(1,[z2,z7,z319,z4,z5,z6]),(0,[z206,z27,z7,z3,z4,z5,z6]),(0,[z2,z634,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z5,z276]),(0,[z2,z7,z635,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z113,z5,z6]),(0,[z149,z2,z201,z7,z4,z5,z6]),(0,[z2,z7,z3,z636,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z637,z6]),(0,[z2,z7,z265,z3,z4,z5,z6]),(0,[z638,z2,z7,z3,z4,z5,z6]),(0,[z247,z7,z3,z4,z76,z5,z6]),(0,[z639,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z640]),(0,[z2,z7,z3,z4,z5,z6,z641]),(0,[z2,z7,z3,z4,z5,z642,z6]),(0,[z2,z7,z3,z4,z5,z6,z643])],[(1,[z2,z7,z3,z4,z200,z6]),(0,[z2,z7,z3,z4,z5,z152,z6]),(0,[z2,z7,z3,z4,z5,z6,z644]),(0,[z2,z7,z3,z645,z4,z5,z6])],[(0,[z2,z7,z3,z646,z4,z5,z6]),(0,[z2,z7,z3,z4,z9,z28,z6])]],
   [[(0,[z647,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z648,z6]),(0,[z2,z7,z3,z4,z5,z6,z153])],[(0,[z649,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z650]),(0,[z2,z7,z3,z4,z651,z5,z6]),(0,[z652,z2,z7,z3,z4,z5,z6])],[(0,[z0,z2,z265,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z653,z5,z6]),(0,[z2,z654,z7,z3,z4,z5,z6]),(0,[z2,z655,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z656,z5,z6]),(0,[z2,z7,z657,z3,z4,z5,z6])],[(0,[z2,z7,z658,z3,z4,z5,z6]),(0,[z48,z2,z7,z3,z4,z5,z6]),(0,[z136,z2,z7,z104,z4,z5,z6])],[(0,[z659,z2,z7,z3,z4,z5,z6]),(0,[z186,z2,z7,z3,z4,z5,z6]),(0,[z660,z2,z7,z3,z4,z5,z6]),(0,[z661,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z662,z5,z6]),(0,[z663,z2,z7,z3,z4,z5,z6]),(0,[z78,z2,z7,z3,z4,z5,z6])],[(0,[z83,z204,z2,z7,z3,z4,z5]),(0,[z148,z2,z7,z3,z4,z5,z276]),(0,[z2,z7,z3,z4,z5,z664,z6]),(0,[z219,z2,z7,z3,z4,z117,z6]),(0,[z219,z2,z7,z3,z4,z28,z6]),(0,[z2,z7,z3,z4,z665,z5,z6])],[(0,[z48,z2,z214,z3,z4,z5,z6]),(1,[z2,z7,z3,z401,z5,z6]),(0,[z2,z7,z3,z4,z5,z124,z6])],[(0,[z1,z86,z2,z3,z4,z5,z6]),(1,[z524,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z666,z6]),(0,[z2,z7,z3,z4,z5,z6,z667]),(0,[z2,z7,z3,z116,z5,z6,z153]),(0,[z2,z7,z3,z4,z5,z6,z668])]],
   [[(0,[z669,z2,z7,z3,z4,z5,z6]),(0,[z36,z101,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z670,z6]),(0,[z2,z7,z3,z4,z5,z671,z6])],[(0,[z2,z7,z672,z3,z4,z5,z6]),(0,[z101,z136,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z673,z6])],[(0,[z674,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z675,z4,z5,z6]),(0,[z2,z7,z3,z4,z160,z5,z6]),(0,[z2,z7,z3,z676,z4,z5,z6]),(0,[z2,z7,z3,z4,z677,z5,z6]),(0,[z2,z7,z678,z3,z4,z5,z6]),(0,[z2,z7,z3,z96,z5,z28,z6])],[(0,[z679,z2,z7,z3,z4,z5,z6]),(0,[z2,z38,z3,z37,z4,z5,z6]),(0,[z86,z2,z3,z37,z4,z5,z6]),(0,[z2,z7,z139,z3,z4,z5,z6])],[(0,[z101,z2,z7,z3,z4,z5,z6])],[(0,[z680,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z681,z5,z6]),(0,[z2,z7,z682,z3,z4,z5,z6])],[(0,[z683,z2,z7,z3,z4,z5,z6]),(0,[z36,z2,z7,z3,z4,z134,z6]),(1,[z36,z2,z3,z4,z152,z6])],[(0,[z127,z2,z7,z15,z4,z5,z6]),(0,[z2,z7,z272,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z684,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z685,z5,z6]),(0,[z2,z7,z3,z686,z4,z5,z6]),(0,[z687,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z28,z6])],[(0,[z2,z688,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z689,z5,z6])],[(0,[z690,z2,z7,z3,z4,z5,z6]),(0,[z333,z91,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z6,z691])],[(0,[z2,z692,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z693,z4,z5,z6]),(0,[z2,z38,z3,z77,z4,z5,z6]),(0,[z2,z7,z3,z116,z4,z117,z6]),(0,[z2,z7,z3,z4,z5,z694,z6])],[(0,[z2,z695,z7,z3,z4,z5,z6]),(0,[z2,z7,z696,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z697,z5,z6]),(0,[z698,z2,z7,z3,z4,z5,z6]),(1,[z149,z2,z7,z4,z144,z6]),(1,[z219,z2,z7,z3,z28,z6]),(0,[z2,z699,z7,z3,z4,z5,z6])],[(1,[z2,z7,z3,z4,z5,z367]),(0,[z2,z7,z3,z4,z5,z397,z6]),(0,[z2,z7,z3,z4,z700,z5,z6]),(0,[z701,z2,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z6,z702]),(0,[z136,z69,z2,z7,z4,z5,z6]),(1,[z52,z2,z7,z113,z5,z6])],[(0,[z703,z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z704,z5,z6]),(0,[z2,z7,z3,z4,z5,z705,z6]),(0,[z706,z2,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z4,z187,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z2,z7,z3,z4,z5,z707]),(0,[z2,z7,z3,z4,z5,z708]),(0,[z69,z2,z202,z4,z5,z6]),(0,[z2,z7,z3,z4,z709,z6]),(0,[z249,z2,z7,z3,z4,z9]),(0,[z2,z34,z3,z4,z49,z6]),(0,[z2,z139,z3,z4,z5,z6]),(0,[z2,z7,z3,z710,z28,z6]),(0,[z2,z7,z711,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z712]),(0,[z48,z34,z3,z4,z5,z208])],[(0,[z608,z7,z15,z4,z5,z6]),(0,[z2,z7,z47,z4,z49,z6]),(0,[z2,z79,z3,z4,z134,z6]),(0,[z149,z229,z7,z4,z144,z6]),(0,[z219,z2,z7,z150,z28,z6])],[(0,[z27,z7,z3,z4,z709,z6]),(0,[z48,z7,z47,z4,z5,z208]),(0,[z2,z7,z3,z4,z713,z6]),(0,[z714,z7,z3,z4,z5,z6]),(0,[z2,z7,z4,z5,z150,z6]),(0,[z2,z7,z3,z4,z117,z304])],[(0,[z48,z7,z3,z4,z5,z407]),(0,[z2,z7,z3,z4,z5,z715])],[(0,[z2,z7,z3,z4,z5,z716]),(0,[z2,z7,z3,z4,z717,z6]),(0,[z679,z7,z15,z4,z5,z6]),(0,[z115,z53,z7,z4,z5,z6]),(0,[z2,z3,z718,z39,z5,z6]),(0,[z2,z7,z3,z4,z5,z719]),(0,[z149,z155,z7,z4,z144,z6])],[(0,[z720,z2,z3,z4,z5,z6])]],
   [[(0,[z147,z2,z37,z4,z5,z6]),(0,[z2,z7,z98,z4,z5,z276]),(0,[z2,z7,z3,z5,z28,z304]),(0,[z2,z7,z3,z4,z145,z153])],[(0,[z7,z3,z4,z721,z5,z6]),(0,[z2,z7,z3,z160,z5,z6]),(0,[z2,z7,z722,z4,z5,z6]),(0,[z2,z7,z723,z4,z5,z6]),(0,[z298,z7,z3,z4,z5,z276]),(0,[z2,z7,z104,z16,z5,z6])],[],[(0,[z249,z206,z7,z3,z4,z5]),(0,[z2,z7,z3,z4,z5,z276]),(0,[z2,z79,z331,z4,z134,z6]),(0,[z50,z2,z3,z4,z5,z51]),(0,[z2,z7,z3,z724,z5,z6]),(0,[z2,z7,z3,z198,z5,z22])],[(0,[z2,z7,z4,z5,z725,z6]),(0,[z173,z7,z3,z721,z5,z6]),(0,[z2,z214,z3,z160,z5,z6]),(0,[z83,z7,z3,z4,z99,z26])],[(0,[z7,z3,z15,z4,z397,z6]),(0,[z2,z7,z3,z4,z200,z6]),(0,[z726,z7,z3,z4,z5,z6]),(0,[z2,z38,z3,z646,z5,z6]),(0,[z78,z2,z79,z4,z134,z6]),(0,[z2,z343,z3,z4,z5,z273]),(0,[z171,z2,z7,z3,z5,z153])],[(0,[z2,z7,z3,z4,z727,z6]),(0,[z2,z7,z3,z4,z728,z6]),(0,[z2,z729,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z730]),(0,[z2,z7,z15,z4,z5,z332]),(0,[z333,z7,z15,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z96,z5,z231]),(0,[z229,z7,z37,z4,z5,z6])],[],[(0,[z2,z7,z731,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z732]),(0,[z733,z7,z3,z4,z5,z6]),(0,[z2,z194,z3,z4,z5,z6]),(0,[z148,z524,z3,z39,z5,z6])],[(0,[z2,z343,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z734]),(0,[z735,z7,z3,z4,z5,z6]),(0,[z524,z7,z98,z4,z5,z6]),(0,[z148,z298,z3,z39,z5,z6]),(0,[z148,z2,z3,z39,z5,z276]),(0,[z52,z2,z7,z113,z281,z6])],[(0,[z2,z7,z3,z4,z397,z23]),(0,[z2,z736,z3,z4,z5,z6])],[(0,[z204,z7,z3,z4,z5,z112]),(0,[z2,z3,z4,z134,z487,z6]),(0,[z86,z2,z3,z4,z5,z737]),(0,[z345,z2,z7,z3,z28,z6])],[(0,[z2,z7,z738,z4,z5,z6])],[(0,[z2,z7,z3,z4,z739,z6]),(0,[z2,z740,z7,z4,z5,z6]),(1,[z2,z3,z718,z5,z6])]],
   [[(0,[z428,z7,z3,z76,z5,z6]),(0,[z25,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z222,z397,z6]),(0,[z2,z7,z3,z4,z741,z6]),(1,[z2,z7,z3,z28,z304])],[(0,[z2,z7,z3,z742,z5,z6]),(0,[z2,z743,z3,z4,z5,z6]),(0,[z354,z69,z7,z4,z5,z6]),(0,[z2,z7,z154,z4,z28,z6]),(0,[z2,z7,z154,z4,z117,z6]),(0,[z2,z7,z3,z401,z5,z23]),(0,[z524,z7,z3,z4,z5,z353]),(0,[z2,z38,z3,z77,z5,z6]),(0,[z375,z2,z4,z5,z150,z6])],[(0,[z2,z7,z744,z4,z5,z6])],[(0,[z2,z7,z4,z5,z6,z745]),(0,[z2,z7,z3,z4,z746,z26])],[(0,[z688,z7,z3,z4,z5,z112]),(0,[z2,z7,z3,z4,z747,z6]),(0,[z204,z2,z7,z3,z198,z5]),(0,[z748,z7,z3,z4,z5,z6]),(0,[z2,z7,z16,z749,z5,z6]),(0,[z2,z7,z3,z750,z5,z6]),(0,[z219,z2,z7,z3,z28,z304]),(0,[z751,z7,z3,z4,z5,z6]),(0,[z2,z752,z7,z4,z5,z6])],[(0,[z2,z7,z753,z4,z5,z6]),(0,[z2,z7,z3,z754,z5,z6]),(0,[z2,z201,z7,z4,z66,z6]),(0,[z2,z7,z3,z4,z274,z276]),(0,[z7,z3,z4,z5,z6,z755]),(0,[z36,z2,z3,z4,z152,z6])],[(0,[z2,z7,z3,z4,z234,z6]),(0,[z206,z7,z3,z4,z367,z10]),(0,[z756,z2,z3,z4,z5,z6])],[(0,[z2,z757,z3,z4,z5,z6]),(0,[z101,z545,z2,z4,z5,z6]),(0,[z2,z7,z3,z4,z217,z276]),(0,[z758,z7,z3,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z28,z153,z26])],[(0,[z759,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z760])],[(0,[z2,z7,z3,z4,z5,z761]),(0,[z2,z7,z3,z4,z5,z762]),(0,[z48,z7,z3,z4,z607,z5]),(0,[z2,z763,z3,z4,z5,z6])],[(0,[z0,z764,z3,z4,z5,z6]),(0,[z2,z7,z765,z4,z5,z6]),(0,[z2,z7,z3,z160,z49,z6]),(0,[z766,z7,z3,z4,z5,z6]),(0,[z2,z7,z767,z4,z5,z6]),(0,[z219,z2,z7,z3,z28,z6])],[(0,[z768,z2,z7,z3,z4,z6]),(0,[z2,z7,z3,z4,z5,z769]),(0,[z2,z7,z3,z4,z5,z770]),(0,[z2,z7,z3,z4,z5,z367]),(0,[z2,z7,z771,z4,z5,z6]),(0,[z48,z7,z3,z160,z5,z208]),(0,[z219,z176,z2,z7,z28,z6])],[(0,[z206,z7,z3,z4,z673,z6]),(0,[z772,z7,z3,z4,z5,z6]),(0,[z52,z2,z7,z113,z5,z6])],[(0,[z27,z7,z3,z4,z364,z6])],[(0,[z2,z773,z7,z3,z4,z5]),(0,[z2,z570,z37,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z774]),(0,[z36,z2,z3,z4,z775,z6]),(0,[z2,z343,z104,z4,z5,z6]),(0,[z2,z776,z3,z4,z5,z6]),(0,[z2,z7,z16,z5,z609,z6]),(0,[z2,z201,z202,z4,z41,z6])]],
   [[(0,[z2,z7,z3,z777,z5,z6]),(0,[z2,z18,z7,z4,z5,z6]),(0,[z2,z468,z37,z4,z5,z6]),(0,[z524,z7,z3,z4,z274,z6]),(0,[z2,z7,z778,z4,z5,z6]),(0,[z779,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z749,z5,z6])],[(0,[z2,z7,z272,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z737]),(0,[z52,z2,z7,z113,z5,z332])],[(0,[z2,z7,z3,z780,z5,z6]),(0,[z2,z7,z3,z4,z5,z781])],[(0,[z2,z7,z3,z782,z5,z6]),(0,[z2,z7,z3,z783,z5,z6]),(0,[z784,z7,z3,z4,z5,z6])],[(0,[z2,z7,z785,z4,z5,z6])],[(0,[z2,z7,z786,z4,z5,z6]),(0,[z787,z7,z3,z4,z5,z6]),(0,[z2,z260,z7,z4,z41,z6]),(0,[z2,z91,z139,z4,z5,z6])],[(0,[z2,z7,z3,z788,z5,z6]),(0,[z2,z7,z3,z4,z789,z6]),(0,[z2,z7,z3,z401,z5,z153]),(0,[z426,z2,z3,z4,z5,z51]),(0,[z2,z7,z3,z4,z5,z790]),(0,[z2,z7,z3,z28,z6,z304])],[(0,[z2,z7,z3,z4,z791,z6]),(0,[z2,z7,z3,z207,z28,z6]),(0,[z2,z7,z3,z4,z5,z792]),(0,[z2,z7,z3,z4,z5,z793]),(0,[z2,z7,z498,z4,z5,z353]),(0,[z52,z53,z7,z113,z5,z6]),(0,[z794,z7,z3,z4,z5,z6])]],
   [[(0,[z795,z2,z7,z3,z4,z5]),(0,[z206,z7,z272,z4,z10,z6]),(0,[z27,z7,z3,z4,z329,z6]),(0,[z333,z7,z47,z4,z5,z6]),(0,[z48,z7,z3,z4,z49,z208]),(0,[z2,z7,z796,z4,z5,z6])],[(0,[z173,z7,z3,z95,z200,z6]),(0,[z206,z7,z3,z4,z397,z6]),(0,[z251,z7,z3,z4,z5,z273])],[(0,[z797,z7,z3,z4,z5,z6])],[(0,[z7,z3,z4,z709,z10,z6]),(0,[z83,z2,z7,z3,z4,z26])],[(0,[z798,z2,z7,z3,z5,z6]),(0,[z2,z799,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z800]),(0,[z136,z347,z2,z4,z5,z6])],[(0,[z2,z7,z801,z4,z5,z6]),(0,[z2,z802,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z268,z273]),(0,[z149,z2,z7,z4,z803,z6])],[(0,[z2,z7,z804,z4,z5,z6]),(0,[z2,z7,z3,z4,z145,z23])],[(0,[z2,z7,z3,z4,z805,z6]),(0,[z2,z7,z806,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z304])]],
   [[(0,[z1,z764,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z807]),(1,[z7,z3,z4,z5,z808]),(0,[z48,z7,z3,z4,z5,z528]),(0,[z809,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z810]),(1,[z2,z7,z3,z5,z811])],[(0,[z2,z7,z3,z4,z812,z6]),(0,[z2,z378,z37,z4,z5,z6])],[(0,[z7,z3,z4,z5,z6,z808]),(0,[z2,z813,z7,z4,z5,z6]),(0,[z2,z7,z3,z425,z5,z23]),(0,[z2,z7,z3,z4,z814,z6])],[(0,[z2,z7,z15,z4,z268,z6]),(0,[z2,z7,z815,z4,z5,z6]),(0,[z2,z7,z4,z749,z5,z6])],[(0,[z2,z7,z3,z4,z816,z6]),(0,[z69,z53,z7,z4,z5,z6]),(0,[z2,z38,z98,z4,z5,z6]),(0,[z50,z2,z3,z4,z5,z737]),(0,[z2,z7,z3,z117,z710,z6])],[(0,[z2,z7,z3,z4,z5,z817]),(0,[z7,z3,z4,z5,z112,z444]),(0,[z2,z7,z3,z4,z818,z6])],[(0,[z2,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z819]),(0,[z2,z7,z241,z401,z5,z6]),(0,[z2,z7,z4,z5,z820,z6]),(0,[z2,z7,z3,z4,z5,z821]),(0,[z2,z7,z4,z5,z803,z6]),(0,[z375,z176,z2,z4,z5,z6])],[(0,[z115,z7,z15,z4,z5,z6]),(0,[z36,z2,z3,z4,z61,z6]),(0,[z2,z7,z3,z4,z822,z6])]],
   [[(0,[z2,z7,z3,z823,z5,z6]),(0,[z2,z7,z3,z721,z5,z6]),(0,[z2,z7,z3,z4,z234,z231]),(0,[z2,z7,z104,z328,z5,z6]),(0,[z2,z7,z824,z4,z5,z6]),(0,[z2,z38,z3,z718,z5,z6]),(0,[z50,z2,z18,z4,z5,z51]),(0,[z2,z7,z749,z113,z5,z6]),(0,[z825,z7,z3,z4,z5,z6])],[(0,[z2,z214,z3,z4,z5,z6]),(0,[z826,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z198,z9,z6])],[(0,[z7,z15,z4,z5,z632,z6]),(0,[z827,z7,z3,z4,z5,z6]),(0,[z2,z828,z3,z4,z5,z6])],[(0,[z2,z829,z7,z4,z5,z6]),(0,[z7,z3,z95,z721,z5,z6]),(0,[z2,z194,z3,z4,z281,z6]),(0,[z830,z7,z3,z4,z5,z6]),(0,[z2,z7,z4,z5,z6,z831])],[(0,[z832,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z833,z6]),(0,[z834,z7,z3,z4,z5,z6])],[(1,[z764,z3,z4,z5,z6]),(0,[z156,z7,z3,z4,z5,z6]),(0,[z206,z7,z3,z4,z10,z6]),(0,[z2,z7,z3,z4,z835,z6]),(0,[z149,z2,z7,z4,z626,z6]),(0,[z2,z7,z836,z4,z5,z6]),(0,[z149,z2,z7,z4,z268,z6]),(0,[z229,z7,z4,z5,z144,z6]),(0,[z2,z7,z3,z82,z5,z6])],[(0,[z2,z7,z331,z4,z5,z6]),(0,[z148,z2,z3,z39,z5,z6])],[(0,[z2,z7,z3,z4,z5,z837]),(0,[z2,z7,z3,z4,z838,z6]),(0,[z2,z7,z3,z4,z839,z6])]],
   [[(0,[z840,z2,z7,z3,z4,z6]),(0,[z2,z7,z3,z841,z5,z6]),(0,[z53,z194,z3,z4,z5,z6]),(0,[z2,z7,z3,z96,z5,z142])],[(0,[z7,z3,z15,z160,z5,z6]),(0,[z2,z7,z842,z4,z5,z6]),(0,[z843,z7,z3,z4,z5,z6]),(0,[z844,z7,z3,z4,z5,z6])],[(0,[z2,z7,z845,z4,z5,z6]),(0,[z846,z2,z7,z3,z4,z5]),(0,[z2,z7,z847,z4,z5,z6]),(0,[z2,z7,z3,z4,z200,z464]),(0,[z2,z3,z4,z5,z848,z6])],[(0,[z2,z7,z3,z4,z849,z6]),(0,[z2,z850,z3,z4,z5,z6]),(0,[z176,z851,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z6,z746])],[(0,[z249,z2,z7,z3,z4,z5]),(0,[z7,z3,z4,z222,z709,z6]),(0,[z356,z2,z3,z4,z5,z6]),(0,[z136,z809,z2,z4,z5,z6]),(0,[z2,z7,z3,z852,z5,z6])],[(0,[z7,z3,z4,z5,z808,z208]),(0,[z2,z7,z3,z4,z853,z6]),(0,[z2,z7,z3,z278,z5,z23]),(0,[z2,z7,z3,z198,z5,z26])],[],[(0,[z764,z7,z3,z4,z5,z6]),(0,[z2,z854,z3,z4,z5,z6]),(0,[z2,z855,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z9,z485]),(0,[z2,z7,z3,z4,z856,z6]),(0,[z496,z2,z7,z3,z28,z6]),(0,[z25,z7,z857,z4,z5,z6])]],
   [[(0,[z858,z7,z3,z4,z5,z6])],[(0,[z176,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z106,z117,z6]),(0,[z859,z2,z7,z4,z5,z6])],[(0,[z7,z3,z4,z222,z6,z225]),(0,[z2,z7,z3,z4,z9,z397]),(0,[z204,z7,z3,z4,z5,z80]),(0,[z2,z7,z3,z860,z5,z6]),(0,[z2,z73,z37,z4,z5,z6]),(0,[z2,z7,z3,z4,z217,z6]),(0,[z52,z2,z7,z749,z5,z6]),(0,[z2,z7,z3,z4,z710,z6])],[(0,[z571,z2,z7,z4,z144,z6]),(0,[z249,z2,z7,z3,z861,z5]),(0,[z2,z34,z241,z4,z5,z6]),(0,[z101,z809,z2,z4,z5,z6]),(0,[z375,z2,z3,z4,z5,z6]),(0,[z219,z2,z7,z3,z28,z385])],[(0,[z158,z265,z319,z4,z5,z6]),(0,[z7,z3,z4,z5,z709,z6]),(0,[z2,z7,z3,z4,z862,z6]),(0,[z863,z7,z3,z4,z5,z6]),(1,[z2,z7,z3,z198,z26])],[(0,[z2,z7,z3,z4,z864,z6]),(1,[z2,z3,z4,z775,z6])],[(0,[z86,z2,z3,z4,z5,z705]),(0,[z2,z3,z4,z5,z737,z51]),(0,[z2,z7,z3,z198,z5,z6]),(0,[z2,z7,z3,z145,z6,z153])],[(0,[z2,z7,z3,z4,z5,z865]),(0,[z866,z2,z7,z4,z5,z6]),(0,[z368,z7,z3,z4,z222,z6])]],
   [[(0,[z2,z7,z867,z4,z5,z6]),(0,[z2,z7,z3,z4,z868,z6]),(0,[z2,z7,z3,z4,z49,z6]),(0,[z2,z7,z3,z869,z5,z6]),(0,[z50,z2,z141,z4,z5,z51]),(0,[z870,z2,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z871,z6]),(0,[z48,z7,z3,z4,z5,z208]),(0,[z2,z343,z4,z113,z5,z6]),(0,[z2,z194,z3,z4,z5,z332]),(0,[z872,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z873,z6]),(0,[z874,z7,z3,z4,z5,z6]),(0,[z148,z2,z3,z39,z217,z6]),(0,[z2,z7,z3,z4,z6,z875]),(0,[z876,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z234,z464]),(0,[z2,z214,z3,z4,z49,z6]),(0,[z48,z2,z7,z3,z198,z5]),(0,[z2,z7,z3,z4,z5,z877])],[(0,[z2,z7,z3,z4,z878,z6]),(0,[z48,z214,z3,z4,z5,z208]),(0,[z2,z655,z7,z4,z41,z6]),(0,[z619,z2,z3,z4,z5,z87]),(0,[z2,z139,z4,z5,z6,z32])],[(0,[z2,z879,z3,z4,z5,z6]),(0,[z204,z7,z3,z4,z5,z808]),(0,[z2,z202,z4,z41,z5,z6]),(0,[z83,z25,z7,z3,z4,z5])],[(0,[z571,z7,z3,z4,z10,z6]),(0,[z2,z7,z3,z693,z5,z153]),(0,[z149,z2,z202,z4,z5,z6])],[(0,[z235,z265,z3,z4,z5,z6]),(0,[z880,z7,z3,z4,z5,z6]),(0,[z229,z201,z7,z4,z5,z6]),(0,[z176,z2,z7,z4,z144,z6]),(0,[z164,z2,z7,z3,z28,z6]),(0,[z2,z7,z881,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z5,z231]),(0,[z882,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z883,z6]),(0,[z2,z884,z3,z4,z5,z6])],[(0,[z27,z7,z3,z4,z222,z6]),(0,[z2,z7,z3,z401,z397,z6])],[(0,[z2,z7,z3,z4,z5,z885]),(0,[z48,z7,z154,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z886])],[(0,[z2,z7,z3,z4,z887,z6]),(0,[z148,z2,z3,z718,z5,z6]),(0,[z251,z7,z3,z4,z268,z6]),(0,[z52,z251,z7,z113,z5,z6]),(0,[z176,z2,z7,z4,z41,z6]),(0,[z2,z7,z888,z4,z5,z6])],[(0,[z2,z7,z889,z4,z5,z6]),(0,[z2,z3,z4,z134,z775,z6]),(0,[z2,z4,z5,z150,z124,z6]),(0,[z2,z7,z3,z438,z117,z6])],[(0,[z206,z7,z3,z4,z709,z6]),(0,[z83,z2,z7,z3,z4,z397]),(0,[z2,z196,z37,z4,z5,z6]),(0,[z7,z3,z4,z890,z5,z6])],[(0,[z2,z7,z3,z4,z891,z6]),(0,[z892,z7,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z893,z6]),(0,[z249,z2,z7,z3,z4,z26]),(0,[z78,z2,z7,z4,z5,z6]),(0,[z31,z341,z2,z4,z5,z32])],[(0,[z2,z7,z3,z4,z5,z894]),(0,[z375,z2,z3,z4,z217,z6])]],
   [[(0,[z2,z7,z3,z4,z895,z6]),(0,[z2,z896,z3,z4,z5,z6])],[(0,[z246,z158,z265,z4,z5,z6]),(0,[z249,z7,z3,z15,z4,z5]),(0,[z2,z897,z3,z4,z5,z6]),(0,[z2,z138,z37,z4,z5,z6]),(0,[z2,z3,z77,z5,z670,z6]),(0,[z2,z7,z3,z4,z898,z6]),(0,[z176,z899,z7,z4,z5,z6])],[(0,[z892,z2,z7,z4,z5,z6])],[(0,[z2,z7,z3,z4,z900,z6]),(0,[z2,z141,z4,z5,z6,z51]),(0,[z2,z7,z3,z116,z117,z6]),(0,[z2,z7,z3,z198,z6,z26])],[(0,[z48,z216,z7,z3,z4,z5]),(0,[z901,z2,z7,z4,z5,z6])],[],[(0,[z52,z2,z7,z188,z5,z6]),(0,[z2,z202,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z902]),(0,[z2,z7,z3,z4,z5,z385])],[(0,[z2,z699,z3,z4,z134,z6]),(0,[z2,z7,z3,z4,z281,z6]),(0,[z903,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z721,z76,z5,z6]),(0,[z2,z7,z3,z4,z5,z904]),(0,[z2,z905,z3,z4,z5,z6])],[(0,[z892,z186,z7,z4,z5,z6]),(0,[z2,z7,z3,z240,z5,z23])],[(0,[z572,z2,z7,z3,z5,z153]),(0,[z2,z7,z3,z4,z906,z6]),(0,[z2,z98,z4,z39,z5,z6])],[],[(0,[z504,z2,z3,z4,z5,z51]),(0,[z53,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z907,z6]),(0,[z136,z532,z2,z4,z5,z6]),(0,[z25,z7,z3,z4,z5,z153])],[(0,[z2,z908,z3,z4,z5,z6]),(0,[z2,z7,z241,z160,z5,z6]),(0,[z204,z7,z3,z4,z5,z631]),(0,[z2,z7,z3,z4,z5,z909]),(0,[z2,z7,z857,z4,z5,z6])],[(0,[z246,z2,z7,z4,z5,z6]),(0,[z2,z34,z3,z4,z397,z6]),(0,[z2,z910,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z911]),(0,[z2,z912,z3,z4,z5,z6])],[(0,[z2,z7,z913,z4,z5,z6]),(0,[z914,z2,z7,z3,z4,z5]),(0,[z86,z2,z141,z4,z5,z6]),(0,[z83,z25,z7,z3,z4,z26])]],
   [[(0,[z2,z7,z47,z4,z397,z6]),(0,[z915,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z96,z5,z23])],[(0,[z69,z2,z7,z4,z5,z332]),(0,[z2,z3,z4,z718,z5,z6])],[(0,[z2,z7,z3,z4,z5,z916]),(0,[z917,z7,z3,z4,z5,z6]),(0,[z899,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z918,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z464]),(0,[z25,z7,z3,z4,z222,z6]),(0,[z2,z34,z3,z401,z5,z6]),(0,[z2,z64,z37,z4,z5,z6]),(0,[z920,z7,z3,z4,z5,z6]),(0,[z2,z79,z3,z4,z775,z6]),(1,[z2,z3,z4,z5,z737])],[(0,[z298,z7,z98,z4,z5,z6]),(0,[z420,z2,z7,z3,z5,z153])],[(0,[z764,z158,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z921]),(0,[z2,z7,z47,z401,z5,z6]),(0,[z922,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z5,z23,z811])],[(0,[z2,z7,z923,z4,z5,z6]),(0,[z2,z7,z98,z4,z5,z6]),(0,[z924,z7,z3,z4,z5,z6]),(0,[z524,z7,z498,z4,z5,z6])],[(0,[z298,z7,z3,z4,z5,z6]),(0,[z2,z7,z925,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z926,z6]),(0,[z927,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z928]),(0,[z2,z7,z241,z4,z49,z6]),(0,[z2,z7,z929,z4,z5,z6]),(0,[z930,z2,z3,z4,z5,z6])],[(0,[z7,z47,z15,z4,z5,z6]),(0,[z48,z7,z241,z4,z5,z208]),(0,[z2,z7,z3,z718,z5,z6])],[(0,[z48,z7,z3,z4,z5,z702]),(0,[z247,z7,z3,z76,z5,z6]),(0,[z931,z7,z3,z4,z5,z6]),(0,[z2,z7,z4,z5,z831,z32])],[(0,[z2,z7,z932,z4,z5,z6]),(0,[z173,z7,z3,z95,z5,z231]),(0,[z933,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z353])],[(0,[z333,z7,z3,z4,z5,z6]),(0,[z127,z115,z7,z4,z5,z6]),(0,[z173,z7,z3,z95,z234,z6]),(0,[z2,z7,z3,z4,z5,z934]),(0,[z2,z3,z4,z5,z6,z737]),(0,[z2,z194,z3,z4,z268,z6]),(0,[z2,z7,z3,z4,z5,z332]),(0,[z2,z935,z3,z4,z5,z6])],[(0,[z148,z2,z98,z39,z5,z6])],[(0,[z158,z265,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z6,z936]),(0,[z2,z7,z4,z41,z419,z6])]],
   [[(0,[z2,z7,z3,z4,z937,z6]),(0,[z2,z7,z3,z4,z5,z831])],[(0,[z2,z343,z3,z4,z5,z6]),(0,[z2,z938,z3,z4,z5,z6]),(0,[z2,z7,z3,z939,z5,z6]),(0,[z2,z7,z940,z4,z5,z6]),(0,[z2,z7,z3,z5,z6,z811]),(0,[z941,z2,z7,z4,z5,z6])],[(0,[z942,z2,z7,z3,z4,z6]),(0,[z2,z7,z943,z4,z5,z6])],[(0,[z2,z944,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z945,z6]),(0,[z2,z7,z141,z4,z5,z6]),(0,[z52,z229,z7,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z946]),(0,[z2,z7,z3,z4,z947,z6]),(0,[z148,z2,z3,z39,z5,z353])],[(0,[z2,z948,z3,z4,z5,z6]),(0,[z2,z7,z949,z4,z5,z6]),(0,[z52,z2,z194,z113,z5,z6])],[(0,[z229,z7,z16,z4,z5,z6]),(0,[z2,z7,z4,z5,z6,z950])],[(0,[z127,z69,z7,z4,z5,z6]),(0,[z2,z7,z154,z4,z5,z6])]],
   [[(0,[z2,z7,z951,z4,z5,z6]),(0,[z186,z7,z15,z4,z5,z6]),(0,[z101,z2,z128,z4,z5,z6]),(0,[z2,z7,z98,z4,z274,z6]),(0,[z2,z7,z952,z4,z5,z6])],[(0,[z953,z2,z7,z3,z5,z6]),(0,[z298,z7,z3,z4,z274,z6]),(0,[z954,z7,z3,z4,z5,z6]),(0,[z148,z2,z3,z467,z5,z6]),(0,[z701,z2,z7,z4,z5,z32]),(0,[z2,z7,z3,z96,z5,z811])],[(0,[z27,z7,z154,z4,z5,z6]),(0,[z2,z34,z47,z4,z5,z6]),(0,[z2,z7,z98,z4,z217,z6]),(0,[z955,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z956]),(0,[z2,z7,z3,z5,z145,z153])],[(0,[z957,z7,z3,z4,z5,z6]),(0,[z298,z7,z3,z4,z217,z6]),(0,[z2,z7,z3,z4,z274,z6]),(0,[z2,z7,z3,z102,z117,z6]),(0,[z958,z7,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z5,z959]),(0,[z2,z7,z3,z4,z960,z6]),(0,[z2,z3,z4,z5,z6,z961])],[(0,[z2,z7,z3,z962,z5,z6]),(0,[z2,z7,z3,z4,z963,z6]),(0,[z964,z7,z3,z4,z5,z6])],[(0,[z69,z892,z7,z4,z5,z6]),(0,[z206,z7,z154,z4,z10,z6]),(0,[z2,z194,z3,z4,z5,z273]),(0,[z965,z2,z3,z4,z5,z6])],[(0,[z2,z7,z3,z4,z966,z6]),(0,[z654,z7,z15,z4,z5,z6]),(0,[z391,z7,z15,z4,z5,z6]),(0,[z967,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z116,z5,z304]),(0,[z171,z2,z7,z3,z5,z811])]],
   [[(0,[z2,z7,z968,z4,z5,z6]),(0,[z249,z2,z7,z3,z4,z397]),(0,[z2,z7,z3,z160,z397,z6]),(0,[z2,z7,z3,z4,z217,z353]),(0,[z969,z2,z7,z3,z4,z6]),(0,[z52,z2,z7,z113,z268,z6])],[(0,[z2,z7,z970,z4,z5,z6]),(0,[z173,z7,z3,z675,z5,z6]),(0,[z2,z7,z3,z5,z710,z6])],[(0,[z229,z7,z3,z4,z5,z6]),(1,[z2,z7,z4,z803,z6]),(0,[z971,z2,z3,z4,z5,z6])],[(1,[z892,z7,z4,z5,z6]),(0,[z148,z2,z3,z39,z274,z6]),(0,[z2,z201,z7,z4,z41,z6])],[(0,[z48,z7,z3,z4,z5,z808]),(0,[z809,z2,z7,z4,z5,z6]),(0,[z149,z2,z343,z4,z5,z6]),(0,[z851,z7,z3,z4,z5,z6])],[(0,[z2,z214,z3,z4,z5,z153]),(0,[z2,z7,z3,z4,z5,z972]),(0,[z2,z7,z973,z4,z5,z6])],[(0,[z2,z7,z974,z4,z5,z6]),(0,[z2,z7,z3,z4,z975,z6]),(0,[z2,z7,z3,z4,z5,z976]),(0,[z86,z2,z3,z4,z5,z87])],[(0,[z2,z7,z3,z96,z145,z6])]],
   [[(0,[z2,z7,z3,z5,z6,z977]),(0,[z524,z7,z3,z4,z5,z276]),(0,[z375,z2,z3,z4,z134,z6]),(0,[z978,z2,z7,z4,z5,z6]),(0,[z2,z979,z3,z4,z5,z6])],[(0,[z163,z7,z15,z4,z5,z6]),(0,[z2,z7,z59,z16,z5,z6]),(1,[z809,z2,z4,z5,z6]),(0,[z2,z7,z3,z4,z803,z6])],[(0,[z2,z7,z3,z4,z980,z6]),(0,[z981,z2,z7,z4,z5,z6]),(0,[z219,z2,z3,z124,z28,z6]),(0,[z25,z7,z3,z4,z28,z6]),(1,[z2,z7,z3,z145,z153]),(0,[z25,z7,z3,z4,z5,z23])],[(0,[z2,z37,z4,z35,z5,z6]),(0,[z2,z7,z4,z803,z144,z6]),(0,[z2,z3,z4,z5,z6,z982])],[(0,[z983,z7,z3,z4,z5,z6]),(0,[z345,z2,z7,z3,z5,z153])],[(0,[z69,z2,z7,z4,z268,z6]),(0,[z173,z7,z3,z95,z5,z6]),(0,[z531,z7,z3,z76,z5,z6]),(0,[z48,z7,z3,z4,z397,z208]),(0,[z984,z7,z3,z4,z5,z6]),(0,[z53,z7,z3,z4,z281,z6]),(0,[z2,z985,z3,z4,z5,z6])],[(0,[z2,z7,z986,z4,z5,z6])],[(0,[z987,z2,z7,z4,z5,z6]),(0,[z25,z7,z3,z4,z397,z6]),(0,[z2,z7,z3,z4,z988,z6])]],
   [[(0,[z2,z7,z989,z4,z5,z6]),(0,[z2,z7,z3,z4,z6,z990]),(0,[z2,z7,z3,z4,z991,z6]),(0,[z7,z154,z4,z5,z10,z6])],[(0,[z695,z7,z15,z4,z5,z6]),(0,[z115,z173,z7,z95,z5,z6]),(0,[z52,z2,z7,z113,z5,z273]),(0,[z2,z201,z7,z4,z803,z6])],[(0,[z2,z7,z241,z4,z5,z6]),(0,[z992,z2,z3,z4,z5,z6]),(0,[z136,z2,z358,z4,z5,z6]),(0,[z2,z7,z3,z993,z5,z6])],[(0,[z249,z206,z7,z3,z4,z10]),(0,[z2,z7,z3,z4,z5,z994]),(0,[z995,z7,z3,z4,z5,z6])],[(0,[z127,z285,z7,z4,z5,z6]),(0,[z462,z7,z3,z95,z5,z6]),(0,[z7,z3,z4,z5,z6,z996])],[(0,[z2,z997,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z998,z6]),(0,[z2,z214,z241,z4,z5,z6]),(0,[z48,z68,z7,z3,z4,z5]),(0,[z36,z2,z331,z4,z5,z6]),(0,[z2,z999,z7,z4,z5,z6]),(0,[z1000,z2,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z1001,z6]),(0,[z219,z2,z7,z3,z710,z6])],[(0,[z809,z2,z37,z4,z5,z6]),(0,[z1002,z7,z3,z4,z5,z6]),(0,[z123,z2,z7,z3,z28,z6])],[(0,[z127,z7,z3,z4,z397,z6]),(1,[z7,z3,z721,z5,z6]),(0,[z2,z7,z3,z1003,z5,z6]),(0,[z249,z2,z7,z3,z1004,z5])]],
   [[(0,[z2,z7,z1005,z4,z5,z6]),(0,[z2,z7,z1006,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1007]),(0,[z2,z1008,z3,z4,z5,z6]),(0,[z1009,z7,z3,z4,z5,z6]),(0,[z2,z510,z37,z4,z5,z6]),(0,[z1010,z7,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z1011,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z268,z6]),(0,[z618,z2,z7,z3,z5,z153]),(0,[z25,z7,z1012,z4,z5,z6])],[(0,[z2,z34,z3,z160,z5,z6]),(0,[z171,z2,z7,z3,z187,z153])],[(1,[z7,z3,z4,z709,z6]),(0,[z2,z1013,z7,z4,z5,z6]),(0,[z2,z1014,z3,z4,z5,z6])],[(0,[z1015,z2,z7,z3,z4,z5]),(0,[z173,z7,z3,z180,z5,z6]),(0,[z573,z1,z3,z4,z5,z6]),(0,[z155,z7,z3,z4,z5,z6]),(0,[z562,z2,z37,z4,z5,z6])],[],[(0,[z249,z127,z7,z3,z4,z5]),(0,[z1016,z2,z7,z4,z5,z6]),(0,[z2,z7,z498,z4,z5,z276]),(0,[z2,z7,z3,z4,z5,z1017]),(0,[z2,z7,z3,z4,z281,z332])],[(0,[z191,z2,z7,z113,z5,z6]),(0,[z136,z156,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z1018,z6])]],
   [[(0,[z2,z1019,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1020]),(0,[z2,z7,z3,z4,z1021,z6])],[(0,[z249,z7,z3,z4,z222,z5]),(0,[z2,z7,z3,z4,z1022,z6]),(0,[z36,z2,z3,z4,z217,z6])],[(0,[z2,z7,z3,z4,z1023,z6]),(0,[z2,z343,z3,z4,z281,z6])],[(0,[z2,z7,z3,z1024,z5,z6]),(0,[z2,z7,z1025,z4,z5,z6]),(0,[z25,z7,z3,z4,z10,z6]),(0,[z1026,z2,z7,z4,z5,z6]),(0,[z426,z2,z7,z4,z5,z32]),(0,[z2,z7,z3,z1027,z5,z6]),(0,[z53,z7,z3,z4,z5,z332]),(0,[z2,z343,z4,z41,z5,z6])],[(0,[z2,z7,z1028,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1029])],[(0,[z2,z7,z3,z96,z200,z6]),(0,[z191,z2,z3,z39,z5,z6]),(0,[z2,z7,z3,z4,z5,z1030]),(0,[z2,z7,z3,z4,z5,z1031])],[(0,[z1032,z7,z3,z4,z5,z6]),(0,[z404,z2,z7,z3,z4,z26]),(0,[z171,z2,z7,z3,z145,z153])],[(0,[z2,z1033,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1034]),(0,[z2,z21,z37,z4,z5,z6]),(0,[z53,z343,z3,z4,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z1036,z7,z3,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z4,z775,z6]),(0,[z1037,z7,z3,z4,z5,z6]),(0,[z1038,z2,z7,z4,z5,z6])],[(0,[z764,z265,z3,z4,z5,z6]),(0,[z101,z136,z2,z4,z5,z6]),(0,[z2,z7,z3,z5,z1039,z6]),(0,[z2,z7,z3,z4,z28,z304])],[(0,[z1040,z2,z7,z4,z5,z6]),(0,[z2,z7,z3,z4,z1041,z6]),(0,[z136,z229,z7,z4,z5,z6]),(0,[z1042,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z273]),(0,[z2,z7,z3,z4,z5,z1043])],[(0,[z2,z7,z3,z4,z5,z1044]),(0,[z48,z7,z3,z4,z222,z9]),(0,[z2,z7,z241,z4,z5,z153]),(0,[z1045,z7,z3,z4,z5,z6])],[(0,[z2,z7,z1046,z4,z5,z6]),(0,[z2,z7,z98,z4,z5,z353]),(0,[z2,z7,z3,z4,z5,z1047]),(0,[z251,z194,z3,z4,z5,z6]),(0,[z176,z2,z7,z4,z268,z6])],[(0,[z7,z3,z4,z5,z112,z808]),(0,[z298,z7,z3,z4,z5,z353])],[(0,[z393,z136,z2,z4,z5,z6]),(0,[z2,z7,z104,z749,z5,z6]),(0,[z2,z7,z3,z116,z566,z6])],[(0,[z1048,z2,z7,z3,z4,z6]),(0,[z2,z7,z1049,z4,z5,z6]),(0,[z1050,z2,z7,z4,z5,z6]),(0,[z176,z2,z4,z5,z124,z6])]],
   [[(0,[z2,z7,z319,z4,z5,z6]),(0,[z2,z7,z3,z1051,z5,z6])],[(0,[z2,z7,z3,z4,z1052,z6]),(0,[z2,z7,z3,z4,z5,z808])],[(0,[z2,z1053,z3,z4,z5,z6]),(0,[z2,z3,z4,z775,z152,z6]),(0,[z2,z1054,z7,z4,z5,z6]),(0,[z496,z2,z7,z3,z4,z26])],[(0,[z127,z892,z7,z4,z5,z6]),(0,[z127,z7,z47,z4,z5,z6]),(0,[z2,z214,z3,z4,z5,z23]),(0,[z1055,z2,z7,z4,z5,z6]),(0,[z375,z2,z3,z4,z152,z6])],[],[(0,[z2,z7,z3,z4,z1056,z6]),(0,[z2,z7,z3,z4,z397,z6])],[(0,[z2,z1057,z3,z4,z5,z6])],[(0,[z2,z7,z1058,z4,z5,z6]),(0,[z86,z2,z3,z4,z5,z271]),(0,[z2,z3,z4,z5,z87,z737])]],
   [[(0,[z2,z7,z3,z1059,z5,z6]),(0,[z2,z214,z3,z4,z397,z6]),(0,[z2,z7,z3,z4,z1060,z6]),(0,[z2,z343,z3,z4,z5,z332]),(0,[z1061,z2,z7,z3,z4,z5]),(0,[z2,z1062,z3,z4,z5,z6])],[(0,[z410,z2,z7,z3,z28,z6])],[(0,[z2,z7,z3,z401,z5,z6])],[(0,[z524,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z1063,z6]),(0,[z2,z7,z4,z41,z803,z6])],[(0,[z2,z1064,z3,z4,z5,z6])],[(0,[z2,z214,z3,z401,z5,z6]),(0,[z1065,z2,z3,z4,z5,z6])],[(0,[z2,z7,z357,z4,z5,z6]),(0,[z2,z37,z4,z5,z6,z223])],[(0,[z2,z3,z4,z5,z1066,z6]),(0,[z2,z7,z1012,z4,z5,z6])]],
   [[(0,[z2,z1067,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z1068,z6]),(0,[z83,z2,z7,z3,z82,z26])],[(0,[z1069,z7,z3,z4,z5,z6]),(0,[z2,z7,z3,z4,z274,z353]),(0,[z2,z7,z3,z4,z1070,z6]),(0,[z1071,z2,z7,z4,z5,z6]),(0,[z1072,z2,z7,z4,z5,z6])],[(0,[z31,z2,z7,z4,z5,z831]),(0,[z1073,z7,z3,z4,z5,z6])],[(0,[z247,z7,z3,z721,z5,z6]),(0,[z2,z7,z3,z1074,z5,z6]),(0,[z1075,z7,z3,z4,z5,z6]),(0,[z244,z2,z7,z3,z5,z153])],[(0,[z2,z7,z3,z4,z5,z1076])],[(0,[z2,z7,z3,z4,z5,z1077]),(0,[z2,z7,z3,z4,z1078,z6]),(0,[z2,z7,z3,z4,z5,z1079])],[(0,[z2,z7,z1080,z4,z5,z6]),(0,[z1081,z2,z7,z4,z5,z6]),(0,[z251,z7,z3,z4,z281,z6]),(1,[z2,z7,z749,z5,z6])],[(0,[z1082,z2,z3,z4,z5,z6]),(0,[z2,z7,z1083,z4,z5,z6])]],
   [[(0,[z2,z7,z3,z1084,z5,z6]),(0,[z2,z7,z3,z4,z1085,z6]),(0,[z2,z1086,z3,z4,z5,z6]),(0,[z149,z2,z7,z4,z144,z6]),(0,[z25,z7,z3,z4,z9,z5])],[(0,[z2,z7,z3,z4,z5,z811])],[(0,[z173,z7,z3,z95,z5,z464]),(0,[z2,z7,z3,z4,z1087,z6]),(0,[z420,z2,z7,z3,z4,z26])],[(0,[z97,z7,z15,z4,z5,z6]),(0,[z2,z7,z1088,z4,z5,z6]),(0,[z809,z2,z196,z4,z5,z6]),(0,[z2,z7,z4,z41,z268,z6]),(0,[z356,z2,z201,z4,z41,z6]),(0,[z2,z7,z3,z4,z187,z6]),(0,[z219,z375,z2,z3,z28,z6])],[(0,[z0,z580,z3,z4,z5,z6]),(0,[z2,z3,z77,z718,z5,z6]),(0,[z185,z2,z3,z4,z5,z51])],[(0,[z2,z7,z3,z4,z5,z1089]),(0,[z2,z7,z3,z1090,z5,z6]),(0,[z36,z2,z98,z4,z5,z6]),(0,[z25,z7,z3,z4,z117,z6])],[(0,[z2,z7,z3,z4,z5,z1091]),(0,[z2,z7,z3,z4,z6,z1092]),(0,[z2,z7,z3,z4,z397,z153]),(0,[z1093,z7,z3,z4,z5,z6]),(0,[z2,z331,z4,z134,z5,z6]),(0,[z159,z2,z7,z3,z5,z153])],[(0,[z2,z34,z3,z4,z5,z6]),(0,[z2,z7,z3,z1094,z5,z6]),(0,[z524,z7,z3,z4,z217,z6]),(0,[z298,z7,z498,z4,z5,z6]),(0,[z2,z7,z1095,z4,z5,z6]),(0,[z53,z7,z3,z4,z268,z6]),(0,[z2,z7,z3,z5,z811,z153])]],
   [[(0,[z2,z7,z3,z1096,z5,z6]),(0,[z83,z2,z7,z3,z4,z746])],[(0,[z2,z7,z47,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1097]),(0,[z2,z7,z498,z4,z5,z6]),(0,[z2,z7,z3,z4,z1098,z6])],[(0,[z2,z7,z3,z4,z5,z746])],[(0,[z127,z7,z3,z160,z5,z6])],[(0,[z2,z7,z3,z4,z200,z231]),(0,[z2,z7,z3,z1004,z5,z6]),(0,[z2,z7,z1099,z4,z5,z6]),(0,[z2,z7,z4,z5,z1100,z6]),(0,[z2,z214,z47,z4,z5,z6]),(0,[z2,z7,z3,z401,z49,z6]),(0,[z2,z7,z3,z4,z1101,z6]),(1,[z2,z7,z3,z710,z6])],[(0,[z2,z7,z3,z4,z5,z1102]),(0,[z2,z7,z3,z5,z231,z153]),(0,[z48,z7,z3,z401,z5,z208]),(0,[z101,z440,z2,z4,z5,z6]),(0,[z52,z2,z7,z519,z5,z6]),(0,[z31,z2,z7,z4,z5,z32]),(0,[z83,z2,z7,z3,z198,z26])],[(0,[z2,z1103,z7,z3,z4,z6]),(0,[z2,z7,z1104,z4,z5,z6]),(0,[z2,z7,z4,z5,z6,z1105])],[(0,[z764,z2,z3,z4,z5,z6]),(0,[z52,z2,z343,z113,z5,z6]),(0,[z2,z7,z3,z4,z145,z6]),(0,[z1106,z2,z3,z4,z5,z6])]],
   [[(0,[z243,z265,z3,z4,z5,z6]),(0,[z892,z7,z15,z4,z5,z6]),(0,[z251,z7,z3,z4,z5,z6]),(0,[z2,z7,z1107,z4,z5,z6]),(0,[z2,z655,z3,z4,z134,z6])],[(0,[z7,z154,z4,z5,z112,z6]),(0,[z2,z7,z241,z4,z5,z23]),(0,[z148,z2,z498,z39,z5,z6])],[(0,[z2,z7,z3,z4,z1108,z6]),(0,[z559,z7,z3,z76,z5,z6])],[(0,[z2,z1109,z3,z4,z5,z6]),(0,[z2,z7,z3,z861,z5,z6]),(0,[z2,z7,z3,z4,z281,z273]),(0,[z2,z7,z3,z4,z1110,z6])],[(0,[z2,z7,z1111,z4,z5,z6]),(0,[z2,z7,z3,z4,z1112,z6]),(0,[z203,z2,z7,z4,z5,z32]),(0,[z2,z1113,z3,z4,z5,z6]),(0,[z333,z69,z7,z4,z5,z6]),(0,[z2,z1114,z3,z4,z5,z6]),(0,[z2,z7,z3,z401,z5,z231]),(0,[z2,z7,z3,z4,z5,z1115]),(0,[z251,z7,z3,z4,z5,z332])],[(0,[z7,z3,z4,z5,z6,z99]),(0,[z7,z3,z4,z5,z6,z1116]),(0,[z2,z7,z3,z116,z710,z6])],[(0,[z1117,z2,z7,z4,z5,z6]),(0,[z2,z7,z241,z4,z397,z6]),(0,[z2,z3,z4,z134,z217,z6])],[(0,[z2,z1118,z3,z4,z5,z6]),(0,[z69,z192,z7,z4,z5,z6]),(0,[z2,z7,z47,z160,z5,z6]),(0,[z2,z7,z1119,z4,z5,z6])]],
   [[(0,[z2,z202,z15,z4,z5,z6]),(0,[z2,z7,z3,z200,z6,z153]),(0,[z341,z2,z3,z4,z5,z6]),(0,[z2,z98,z4,z134,z5,z6]),(0,[z251,z343,z3,z4,z5,z6]),(0,[z53,z7,z3,z4,z5,z273]),(0,[z2,z7,z3,z4,z268,z332]),(0,[z31,z2,z139,z4,z5,z32])],[(0,[z2,z7,z3,z4,z1120,z6]),(0,[z2,z7,z1121,z4,z5,z6]),(0,[z2,z1122,z3,z4,z5,z6])],[(0,[z173,z7,z357,z95,z5,z6]),(0,[z2,z7,z1123,z4,z5,z6])],[(0,[z2,z7,z1124,z4,z5,z6]),(0,[z2,z7,z498,z4,z274,z6]),(0,[z1125,z7,z3,z4,z5,z6])],[(0,[z115,z2,z7,z4,z5,z6]),(0,[z69,z2,z343,z4,z5,z6]),(0,[z2,z7,z3,z103,z117,z6]),(0,[z2,z37,z4,z321,z5,z6]),(0,[z2,z3,z4,z5,z124,z6]),(0,[z2,z343,z3,z4,z268,z6])],[(0,[z2,z1126,z3,z4,z5,z6]),(0,[z2,z7,z498,z4,z217,z6]),(0,[z2,z7,z3,z4,z198,z26])],[(0,[z53,z7,z15,z4,z5,z6]),(0,[z156,z7,z37,z4,z5,z6]),(0,[z2,z3,z4,z5,z775,z6])],[(0,[z248,z7,z15,z4,z5,z6]),(0,[z2,z7,z3,z4,z5,z1127])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 547) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 547).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1090).take 6) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1096)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [547, 543, 6] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 125).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 125).take 131).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [125, 131] = true :=
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

end PEqualNP.Outside.L_meta_36260

theorem PEqualNP.Outside.L_meta_36260 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36260.solve