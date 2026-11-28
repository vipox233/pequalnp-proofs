import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37287

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4206946496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1000c413142f06f2#64 ++ 0x84003104c50bc1bc#64 ++ 0xec05cd37347f0ff3#64 ++ 0xfb01734dcd1fc3fc#64 : BitVec 256),
   (0x2008504148615157#64 ++ 0x0802141052185455#64 ++ 0xdf1a72c9c863f1ff#64 ++ 0xf7c69cb27218fc7f#64 : BitVec 256),
   (0x4063830e0582aa28#64 ++ 0x5018e0c38160aa8a#64 ++ 0xbee3830e0f83fe3f#64 ++ 0x6fb8e0c383e0ff8f#64 : BitVec 256),
   (0x81bc03f00ad43d80#64 ++ 0x606f00fc02b50f60#64 ++ 0x7ffc03f00ffc3fc2#64 ++ 0xdfff00fc03ff0ff0#64 : BitVec 256),
   (0x02dffc000f7bc003#64 ++ 0x80b7ff0003def000#64 ++ 0xfafffc000fffc002#64 ++ 0x3ebfff0003fff000#64 : BitVec 256),
   (0x00f72baca0000000#64 ++ 0x003dcaeb28000000#64 ++ 0xf9fffffff0000001#64 ++ 0xfe7ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf9fffffff0000001 0xfe7ffffffc000000

def z1 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc000fffc002 0x3ebfff0003fff000

def z2 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec05cd37347f0ff3 0xfb01734dcd1fc3fc

def z3 : W := mkw 0x2000500140214057 0x0800140050085015 0x00007001c0000000 0x00001c0070000000

def z4 : W := mkw 0x2008504148615157 0x0802141052185455 0xdf1a72c9c863f1ff 0xf7c69cb27218fc7f

def z5 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee3830e0f83fe3f 0x6fb8e0c383e0ff8f

def z6 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc03f00ffc3fc2 0xdfff00fc03ff0ff0

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0xe805cc0000000000 0x3a01730000000000

def z8 : W := mkw 0x81ff03fc0ad43d80 0x607fc0ff02b50f60 0xffff83fe0ffc3fc3 0xffffe0ff83ff0ff0

def z9 : W := mkw 0x42dffc020ffbea2b 0xd0b7ff0083fefa8a 0xfefffc000ffffe3e 0x3fbfff0003ffff8f

def z10 : W := mkw 0x0043c400052b8002 0x8010f100014ae000 0xfae7cc000fffc002 0x3eb9f30003fff000

def z11 : W := mkw 0x5063c71f15afaefa 0xd418f1c7c56bebbe 0xfee7cf3f3fffffff 0xffb9f3cfcfffffff

def z12 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x20e58d3630000000 0x0839634d8c000000

def z13 : W := mkw 0x40f7abaea582aa28 0x503deaeba960aa8a 0xffffffffff83fe3f 0xffffffffffe0ff8f

def z14 : W := mkw 0x0094000002100000 0x0025000000840000 0x20e40000079c0000 0x0839000001e70000

def z15 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x20e58c00079c0000 0x0839630001e70000

def z16 : W := mkw 0x224bfc414d6bd157 0x8892ff10535af455 0xdf1bfec9c863f1ff 0xf7c6ffb27218fc7f

def z17 : W := mkw 0x0243fc00052bc003 0x8090ff00014af000 0x8003fc000003c000 0x2000ff000000f000

def z18 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x050003f000003fc0 0xc14000fc00000ff0

def z19 : W := mkw 0x0008004008401100 0x0002001002100440 0x5f1802c0086031c2 0xd7c600b002180c70

def z20 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0x20058d36341c0e00 0x0801634d8d070380

def z21 : W := mkw 0x81bc03e00ad03900 0x606f00f802b40e40 0x13f802c00b803000 0x04fe00b002e00c00

def z22 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0x40044c31307c01c0 0x9001130c4c1f0070

def z23 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0x12e202080b80f00c 0x04b8808202e03c03

def z24 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfbfffec9cfffc003 0xfeffffb273fff000

def z25 : W := mkw 0xc1ffabfeafd6bfa8 0x707feaffabf5afea 0xffffffffffffffff 0xffffffffffffffff

def z26 : W := mkw 0x6028534f48e17b7f 0x580a14d3d2385edf 0xdf1a73cfc863ffff 0xf7c69cf3f218ffff

def z27 : W := mkw 0x00d7280ca0000000 0x0035ca0328000000 0xf8fffc0ff0000001 0x3e3fff03fc000000

def z28 : W := mkw 0x02ffffacaf7bc003 0x80bfffeb2bdef000 0xfbffffffffffc003 0xfefffffffffff000

def z29 : W := mkw 0x819c00f00ad43d80 0x6067003c02b50f60 0x471c00f00ffc3fc2 0x91c7003c03ff0ff0

def z30 : W := mkw 0x009c00100a540480 0x0027000402950120 0x7efc01300ffc0fc2 0xdfbf004c03ff03f0

def z31 : W := mkw 0x91bcc7f31eff3ff2 0xe46f31fcc7bfcffc 0xfffdcff73fff3ff3 0xffff73fdcfffcffc

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x9e0202080803f03f 0x678080820200fc0f

def z33 : W := mkw 0x83ffffe00ffbf903 0xe0fffff803fefe40 0xfbfffec00ffff002 0x3effffb003fffc00

def z34 : W := mkw 0x810800500ad43d80 0x6042001402b50f60 0x060000000ffc3fc2 0x0180000003ff0ff0

def z35 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x20e40130079c0e00 0x0839004c01e70380

def z36 : W := mkw 0x2000500140214057 0x0800140050085015 0x80027009c003c03d 0x20009c027000f00f

def z37 : W := mkw 0x002003aca0000000 0x000800eb28000000 0x010003fff0000001 0xc04000fffc000000

def z38 : W := mkw 0x0208d4000f7bc003 0x8082350003def000 0x020000000fffc002 0x0080000003fff000

def z39 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0x00000000041c0e00 0x0000000001070380

def z40 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0x411c7cf1f0000000 0x90471f3c7c000000

def z41 : W := mkw 0x10008413140e06f0 0x84002104c50381bc 0x24058d37341c0ff1 0xc901634dcd0703fc

def z42 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0x7afc7c000ffc0002 0x1ebf1f0003ff0000

def z43 : W := mkw 0x4043800e05028228 0x1010e0038140a08a 0x8003800e0003c03d 0x2000e0038000f00f

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x010002c9c0000001 0xc04000b270000000

def z45 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x12fa30000fffc002 0x04be8c0003fff000

def z46 : W := mkw 0x10f7efbfb42f06f2 0x843dfbefed0bc1bc 0xfdfffffff47f0ff3 0xff7ffffffd1fc3fc

def z47 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffec9cffff1ff 0xffffffb273fffc7f

def z48 : W := mkw 0x4063c70e05abaa2a 0xd018f1c3816aea8a 0xfee7cf0e0ffffe3f 0x7fb9f3c383ffff8f

def z49 : W := mkw 0x819c00f00a541580 0x2067003c02950560 0x7bfc00f00ffc01c2 0x9eff003c03ff0070

def z50 : W := mkw 0x5043c40f152b827a 0x9410f103c54ae09e 0x8003cc0f3003c03d 0x2000f303cc00f00f

def z51 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x24058d36347f0ff2 0x0901634d8d1fc3fc

def z52 : W := mkw 0x12dffc131f7fc6f3 0x84b7ff04c7dff1bc 0xfefffd373fffcff3 0xffbfff4dcffff3fc

def z53 : W := mkw 0x42ffff0e0ffbea2b 0xd0bfffc383fefa8a 0xfeffff0e0ffffe3f 0x7fbfffc383ffff8f

def z54 : W := mkw 0x4020030c00802808 0x500800c300200a02 0x000002080000300c 0x0000008200000c03

def z55 : W := mkw 0x0008500008614003 0x0002140002185000 0x4018700000600000 0x10061c0000180000

def z56 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0x8001cc0730030031 0x20007301cc00c00c

def z57 : W := mkw 0x12dffc031f7bc273 0x84b7ff00c7def09c 0xfafffc073fffc033 0x3ebfff01cffff00c

def z58 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0x6c058d36347c0fc2 0xdb01634d8d1f03f0

def z59 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1ffffff863f1ff 0xffc7fffffe18fc7f

def z60 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0xdf1a72c9cc7fffff 0xf7c69cb2731fffff

def z61 : W := mkw 0x40f72baca180a808 0x503dcaeb28602a02 0xfbfffffffb80f00d 0xfefffffffee03c03

def z62 : W := mkw 0x0008500008614003 0x0002140002185000 0xdb1a72c9c863c003 0xf6c69cb27218f000

def z63 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7afc00000ffc0002 0x1ebf000003ff0000

def z64 : W := mkw 0x00b403a000000000 0x002d00e800000000 0x79fc03f000000000 0xde7f00fc00000000

def z65 : W := mkw 0x4020030e00802a28 0x500800c380200a8a 0x3ee0030e0f803e3f 0x4fb800c383e00f8f

def z66 : W := mkw 0x2008504148615157 0x0802141052185455 0xc11a70c9c063c1fd 0xb0469c327018f07f

def z67 : W := mkw 0x4063ab0ea582aa28 0x5018eac3a960aa8a 0xbee3ff0fff83fe3f 0x6fb8ffc3ffe0ff8f

def z68 : W := mkw 0x0000001000040480 0x0000000400010120 0x6c040130047c0fc2 0xdb01004c011f03f0

def z69 : W := mkw 0x20ff7bede8615157 0x083fdefb7a185455 0xf9fffffff06001c1 0xfe7ffffffc180070

def z70 : W := mkw 0x4000000200802a28 0x5000000080200a8a 0x0400000000003e3c 0x0100000000000f8f

def z71 : W := mkw 0x00d7a80005028000 0x0035ea000140a000 0xfafffc000f83c002 0x3ebfff0003e0f000

def z72 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0x12fa30000b80c000 0x04be8c0002e03000

def z73 : W := mkw 0x209c50414a715157 0x08271410529c5455 0xfffe72c9cffff1ff 0xffff9cb273fffc7f

def z74 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0xf8fffc0000000000 0x3e3fff0000000000

def z75 : W := mkw 0x2008504148615157 0x0802141052185455 0x171a32c8c863f1fe 0x05c68cb23218fc7f

def z76 : W := mkw 0x0000400100210052 0x0000100040084014 0xdd1a72c9c06301f3 0xf7469cb27018c07c

def z77 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x04000000047f0ff2 0x01000000011fc3fc

def z78 : W := mkw 0x2008504148615157 0x0802141052185455 0x060000000863f1fe 0x018000000218fc7f

def z79 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfefffc000ffff1fe 0x3fbfff0003fffc7f

def z80 : W := mkw 0x0000c400042b0002 0x80003100010ac000 0xe805cc00047f0002 0x3a017300011fc000

def z81 : W := mkw 0x0043800005028000 0x0010e0000140a000 0xbee382080f83f03f 0x6fb8e08203e0fc0f

def z82 : W := mkw 0x0000800204020220 0x0000200081008088 0xac01810604030e33 0x6b0060418100c38c

def z83 : W := mkw 0x819c00500ad43d80 0x6067001402b50f60 0x7efc00000ffc3fc2 0x1fbf000003ff0ff0

def z84 : W := mkw 0x20ff7bede8615157 0x083fdefb7a185455 0xdffa72c9c863f1ff 0xf7fe9cb27218fc7f

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0xd91a72c9c0000001 0xf6469cb270000000

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z87 : W := mkw 0x83fffff00ffffd83 0xe0fffffc03ffff60 0xfffffff00fffffc2 0xfffffffc03fffff0

def z88 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x20e1810607800e00 0x0838604181e00380

def z89 : W := mkw 0x606bd34f4de3fb7f 0x581af4d3d378fedf 0xfffbf3cfcfe3ffff 0xfffefcf3f3f8ffff

def z90 : W := mkw 0x0020030000802800 0x400800c000200a00 0x20e0010007800e00 0x0838004001e00380

def z91 : W := mkw 0x42ffffaeaffbea2b 0xd0bfffebabfefa8a 0xfffffffffffffe3f 0xffffffffffffff8f

def z92 : W := mkw 0x00bc03e008401100 0x002f00f802100440 0x7ffc03f0086031c2 0xdfff00fc02180c70

def z93 : W := mkw 0x006303aca0000000 0x0018c0eb28000000 0xb9e383fff0000001 0xee78e0fffc000000

def z94 : W := mkw 0x1043ec0fb42b0272 0x8410fb03ed0ac09c 0x8003fc0ff0030031 0x2000ff03fc00c00c

def z95 : W := mkw 0x4043800e0582aa28 0x5010e0038160aa8a 0x8603800e0f83fe3f 0x2180e00383e0ff8f

def z96 : W := mkw 0x4020030e00802a28 0x500800c380200a8a 0x9e02030e0803fe3f 0x678080c38200ff8f

def z97 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbae381060f83ce02 0x2eb8e04183e0f380

def z98 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0x00e0000003800000 0x0038000000e00000

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0xe805cd3730000001 0xfa01734dcc000000

def z100 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x11fa32c8c0000000 0x047e8cb230000000

def z101 : W := mkw 0x0008500008614003 0x0002140002185000 0xda1a70000863c002 0x36869c000218f000

def z102 : W := mkw 0x2008104048405105 0x0802041012101441 0x131a32c8c800f00c 0x04c68cb232003c03

def z103 : W := mkw 0x819c00f00a541580 0x2067003c02950560 0x411c00f0007c01c0 0x9047003c001f0070

def z104 : W := mkw 0xc1ff83fe0fd6bfa8 0x707fe0ff83f5afea 0xffff83fe0fffffff 0xffffe0ff83ffffff

def z105 : W := mkw 0x2000004140001154 0x0800001050000455 0x04000000000031fc 0x0100000000000c7f

def z106 : W := mkw 0x2008504148615157 0x0802141052185455 0x5f1802c00863f1fe 0xd7c600b00218fc7f

def z107 : W := mkw 0x002003a000000000 0x000800e800000000 0x010003f000000000 0xc04000fc00000000

def z108 : W := mkw 0x0000400100210052 0x0000100040084014 0xcc004001006301f3 0xf30010004018c07c

def z109 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0xff1ffffffc7fffff 0xffc7ffffff1fffff

def z110 : W := mkw 0x0000000200000220 0x0000000080000088 0x0400010600000e31 0x410000418000038c

def z111 : W := mkw 0xa3fffff14ffffdd7 0xe8fffffc53ffff75 0xfffffff9cfffffff 0xfffffffe73ffffff

def z112 : W := mkw 0x10000410100c0480 0x8400010404030120 0x00040c30301c0000 0x0001030c0c070000

def z113 : W := mkw 0x10008402140a0220 0x8400210085028088 0x00018c0630000000 0x000063018c000000

def z114 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfafffc09cfffc03f 0x3ebfff0273fff00f

def z115 : W := mkw 0x02d7fc00052bc003 0x80b5ff00014af000 0xf8fffc000003c000 0x3e3fff000000f000

def z116 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0x401c7c00007c0000 0x10071f00001f0000

def z117 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0xbae3830e0b80f00d 0x6eb8e0c382e03c03

def z118 : W := mkw 0x10000013100406f0 0x04000004c40101bc 0x0400013730000ff1 0xc100004dcc0003fc

def z119 : W := mkw 0x4063831e0586aea8 0x5018e0c78161abaa 0xfee7833e0fffffff 0xffb9e0cf83ffffff

def z120 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x61fc01f007fc0fc0 0x987f007c01ff03f0

def z121 : W := mkw 0x00df80000f528000 0x0037e00003d4a000 0xfaff80000fffc002 0x3ebfe00003fff000

def z122 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee7cf3f3f83fe3f 0xffb9f3cfcfe0ff8f

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0xf91ffffff0000001 0xfe47fffffc000000

def z124 : W := mkw 0x2043780de0214057 0x0810de0378085015 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z125 : W := mkw 0x81ff2bfcaad43d80 0x607fcaff2ab50f60 0xfffffffffffc3fc3 0xffffffffffff0ff0

def z126 : W := mkw 0x029cd4000f7bc003 0x80a7350003def000 0x7afc00000fffc002 0x1ebf000003fff000

def z127 : W := mkw 0x1208d4131f7fc6f3 0x84823504c7dff1bc 0xee05cd373fffcff3 0xfb81734dcffff3fc

def z128 : W := mkw 0x81bc03e00ad03900 0x606f00f802b40e40 0x7bfc03f00b803000 0xdeff00fc02e00c00

def z129 : W := mkw 0x0008004008401100 0x0002001002100440 0xdf1a72c9c86031c3 0xf7c69cb272180c70

def z130 : W := mkw 0x0000400100210052 0x0000100040084014 0x40004001006001c0 0x9000100040180070

def z131 : W := mkw 0x229c7c414a795157 0x88a71f10529e5455 0x411c7cc1c07c01c0 0x90471f30701f0070

def z132 : W := mkw 0x2000004140001154 0x0800001050000455 0x050002c9c00031fd 0xc14000b270000c7f

def z133 : W := mkw 0x0020030000802800 0x400800c000200a00 0x12e002000b803000 0x04b8008002e00c00

def z134 : W := mkw 0x81bc03fcaad43d80 0x606f00ff2ab50f60 0x7ffc03fffffc3fc3 0xdfff00ffffff0ff0

def z135 : W := mkw 0x400080020582aa28 0x500020008160aa8a 0xae0181060f83fe3f 0x6b80604183e0ff8f

def z136 : W := mkw 0x20df784148615157 0x0837de1052185455 0xfffffec9c863f1ff 0xffffffb27218fc7f

def z137 : W := mkw 0x1243fc03152bc273 0x8490ff00c54af09c 0x8003fc073003c031 0x2000ff01cc00f00c

def z138 : W := mkw 0x91b4c7b316bf2ef2 0xe46d31ecc5afcbbc 0xece5cd3737ff0ff3 0xfb39734dcdffc3fc

def z139 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0x7afe30000ffcc002 0x1ebf8c0003ff3000

def z140 : W := mkw 0x606b134c49c0f90d 0x581ac4d312703e43 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z141 : W := mkw 0x81f72bbca2942c80 0x607dcaef28a50b20 0xf9fffffff79c0e01 0xfe7ffffffde70380

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000000803f03e 0x018000000200fc0f

def z143 : W := mkw 0x024bd4000f7bc003 0x8092f50003def000 0xbae380000fffc002 0x2eb8e00003fff000

def z144 : W := mkw 0x0094280000000000 0x00250a0000000000 0x401c7c0000000000 0x10071f0000000000

def z145 : W := mkw 0x0008000008400000 0x0002000002100000 0x5a18000008600002 0x1686000002180000

def z146 : W := mkw 0x404380020582aa28 0x5010e0008160aa8a 0xbee380000f83fe3e 0x2fb8e00003e0ff8f

def z147 : W := mkw 0x0020030000802800 0x400800c000200a00 0x3ee003000f803e02 0x4fb800c003e00f80

def z148 : W := mkw 0x029c7ca0aa794003 0x80a71f282a9e5000 0x411c7cf1f07c0000 0x90471f3c7c1f0000

def z149 : W := mkw 0x1043c413152f86f2 0x8410f104c54be1bc 0xfee7cd373fffcff3 0xffb9f34dcffff3fc

def z150 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfffffec00ffff1c2 0xffffffb003fffc70

def z151 : W := mkw 0x20ff7bede8615157 0x083fdefb7a185455 0xfffffffff863f1ff 0xfffffffffe18fc7f

def z152 : W := mkw 0x2008504148615157 0x0802141052185455 0x471870c1c863f1fe 0x91c61c307218fc7f

def z153 : W := mkw 0x812803500ad43d80 0x604a00d402b50f60 0x3ee003000ffc3fc2 0x4fb800c003ff0ff0

def z154 : W := mkw 0x0008500008614003 0x0002140002185000 0xde1a72080863f03f 0x77869c820218fc0f

def z155 : W := mkw 0x42f7af0e079aaa28 0xd0bdebc381e6aa8a 0x20e58d06079c0e00 0x0839634181e70380

def z156 : W := mkw 0x4043800e05028228 0x1010e0038140a08a 0x0001800600000000 0x0000600180000000

def z157 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfd1ffffff47f0ff3 0xff47fffffd1fc3fc

def z158 : W := mkw 0x00632baca0000000 0x0018caeb28000000 0x8103fffff0000001 0xe040fffffc000000

def z159 : W := mkw 0x006383000582a800 0x4018e0c00160aa00 0xbee383000f83fe02 0x6fb8e0c003e0ff80

def z160 : W := mkw 0x009cc4000e7b0002 0x80273100039ec000 0xfafdcc000fff0002 0x3ebf730003ffc000

def z161 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfffffffff803f03f 0xfffffffffe00fc0f

def z162 : W := mkw 0x81b403f000843d80 0x606d00fc00210f60 0x7dfc03f000003fc0 0xdf7f00fc00000ff0

def z163 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x17f802c00ffc3fc2 0x05fe00b003ff0ff0

def z164 : W := mkw 0x12dffc131f7fc6f3 0x84b7ff04c7dff1bc 0xfefffc000fffcff2 0x3fbfff0003fff3fc

def z165 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x44044c31347f0ff2 0x9101130c4d1fc3fc

def z166 : W := mkw 0x400080020582aa28 0x500020008160aa8a 0x060000000f83fe3e 0x0180000003e0ff8f

def z167 : W := mkw 0x81bc43f10af53dd2 0x606f10fc42bd4f74 0xfffc43f10fff3ff3 0xffff10fc43ffcffc

def z168 : W := mkw 0x42ffff0c0ffbe80b 0xd0bfffc303fefa02 0xfafffe080ffff00e 0x3ebfff8203fffc03

def z169 : W := mkw 0x10f7efbfb42f06f2 0x843dfbefed0bc1bc 0xece5cd37347f0ff3 0xfb39734dcd1fc3fc

def z170 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0xb8e3830e00000001 0x6e38e0c380000000

def z171 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf8fffd3630000000 0x3e3fff4d8c000000

def z172 : W := mkw 0xb1bcd7f35eff7ff7 0xec6f35fcd7bfdffd 0xffffffffffffffff 0xffffffffffffffff

def z173 : W := mkw 0x406b834e0dc2bb28 0x501ae0d38370aeca 0xfffb83ce0fe3ffff 0xfffee0f383f8ffff

def z174 : W := mkw 0x209c78e1e8615157 0x08271e387a185455 0xdf1e7ef9f863f1ff 0xf7c79fbe7e18fc7f

def z175 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0x8003fc0ff0000001 0x2000ff03fc000000

def z176 : W := mkw 0x2243fc01452bc057 0x8890ff00514af015 0x8003fc09c003c03d 0x2000ff027000f00f

def z177 : W := mkw 0x0000800204020220 0x0000200081008088 0x2001810604000e00 0x0800604181000380

def z178 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x451c03f0007c3fc0 0xd14700fc001f0ff0

def z179 : W := mkw 0x0020030000802800 0x400800c000200a00 0xbee203080f83fe3f 0x6fb880c203e0ff8f

def z180 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0x7afd8c000ffc0002 0x1ebf630003ff0000

def z181 : W := mkw 0x00f72baca0802800 0x403dcaeb28200a00 0xffffffffff803e03 0xffffffffffe00f80

def z182 : W := mkw 0x40f7abaea5028228 0x103deaeba940a08a 0xf9fffffff003c03d 0xfe7ffffffc00f00f

def z183 : W := mkw 0x00b403b000040480 0x002d00ec00010120 0x7dfc03f0047c0fc2 0xdf7f00fc011f03f0

def z184 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0xf9fffec9c0000001 0xfe7fffb270000000

def z185 : W := mkw 0x109cc4131e7f06f2 0x84273104c79fc1bc 0xfefdcd373fff0ff3 0xffbf734dcfffc3fc

def z186 : W := mkw 0x8100005000843d80 0x6040001400210f60 0x0400000000003fc0 0x0100000000000ff0

def z187 : W := mkw 0x0000800004020000 0x0000200001008000 0xa801800004030002 0x2a0060000100c000

def z188 : W := mkw 0x400080020582aa28 0x500020008160aa8a 0x0000000007800e00 0x0000000001e00380

def z189 : W := mkw 0x81bc03f00a541580 0x206f00fc02950560 0x79fc03f0007c01c0 0xde7f00fc001f0070

def z190 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x11fa33fff0000001 0xc47e8cfffc000000

def z191 : W := mkw 0x009c00000a500000 0x0027000002940000 0x401c0000007c0000 0x10070000001f0000

def z192 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0xe805cc07347f0033 0x3a017301cd1fc00c

def z193 : W := mkw 0x2000404140211156 0x0800101050084455 0xcd0042c9c06331ff 0xf34010b27018cc7f

def z194 : W := mkw 0x0000c401042b0052 0x80003100410ac014 0xec05cc01047f01f3 0xfb017300411fc07c

def z195 : W := mkw 0x3000d413542f46f7 0x8c003504d50bd1bd 0xec07fd3ff47fcfff 0xfb01ff4ffd1ff3ff

def z196 : W := mkw 0x91bc03f31ad43ff0 0x646f00fcc6b50ffc 0x7ffc03f73ffc3ff3 0xdfff00fdcfff0ffc

def z197 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xc005cc37307f01f1 0xb001730dcc1fc07c

def z198 : W := mkw 0xc1f783be0796aea8 0x707de0ef81e5abaa 0x20e58136079c0e00 0x0839604d81e70380

def z199 : W := mkw 0x20ff3bece8405105 0x083fcefb3a101441 0x13fa32c8c800f00c 0x04fe8cb232003c03

def z200 : W := mkw 0x10000013100406f0 0x04000004c40101bc 0x6c040137347c0ff3 0xdb01004dcd1f03fc

def z201 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfefffc010fffc1f3 0xffbfff0043fff07c

def z202 : W := mkw 0x10f76fbdb02d04d2 0x843ddbef6c0b4134 0xf9fffffff07c01c1 0xfe7ffffffc1f0070

def z203 : W := mkw 0x0008004008401100 0x0002001002100440 0x411800c0006001c0 0x9046003000180070

def z204 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0x32ffbc000f9cc000 0x0cbfef0003e73000

def z205 : W := mkw 0x02dffc100f7fc483 0x80b7ff0403dff120 0xfefffd300fffcfc2 0xffbfff4c03fff3f0

def z206 : W := mkw 0x00bc03a00a500000 0x002f00e802940000 0x7bfc03f00ffc0002 0xdeff00fc03ff0000

def z207 : W := mkw 0x10004413102d06f2 0x84001104c40b41bc 0x44044d37307c0ff1 0xd101134dcc1f03fc

def z208 : W := mkw 0x0043800005028000 0x0010e0000140a000 0xbae380000f83c002 0x2eb8e00003e0f000

def z209 : W := mkw 0x206b534d48615157 0x081ad4d352185455 0xfffbf3cfc863f1ff 0xfffefcf3f218fc7f

def z210 : W := mkw 0x0000440000290002 0x80001100000a4000 0x40044c00007c0000 0x10011300001f0000

def z211 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xf8fffc00079c0000 0x3e3fff0001e70000

def z212 : W := mkw 0xa1bc03f14ad43dd4 0x686f00fc52b50f75 0x7ffc03f9cffc3fff 0xdfff00fe73ff0fff

def z213 : W := mkw 0x4020030e00802a28 0x500800c380200a8a 0x0400030e00003e3d 0x410000c380000f8f

def z214 : W := mkw 0xc12003fe00843fa8 0x704800ff80210fea 0x050003fe00003ffd 0xc14000ff80000fff

def z215 : W := mkw 0x812003fca0843d80 0x604800ff28210f60 0x050003fff0003fc1 0xc14000fffc000ff0

def z216 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe73f9cffc3fc3 0xffff9cfe73ff0ff0

def z217 : W := mkw 0x00df28000a500000 0x0037ca0002940000 0xfafffc000ffc0002 0x3ebfff0003ff0000

def z218 : W := mkw 0x009c00400a501100 0x0027001002940440 0x7ffc02c00ffc31c2 0xdfff00b003ff0c70

def z219 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0xd91bfecff0000001 0xf646ffb3fc000000

def z220 : W := mkw 0x406383aea582aa28 0x5018e0eba960aa8a 0xbfe383ffff83fe3f 0xeff8e0ffffe0ff8f

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x40044c3130000000 0x9001130c4c000000

def z222 : W := mkw 0x30fffffffc6f57f7 0x8c3fffffff1bd5fd 0xfffffffffc7fffff 0xffffffffff1fffff

def z223 : W := mkw 0x02dffca0af7bc003 0x80b7ff282bdef000 0xfbfffcf1ffffc002 0xbeffff3c7ffff000

def z224 : W := mkw 0x0094000000000000 0x0025000000000000 0x78fc000000000000 0x1e3f000000000000

def z225 : W := mkw 0x00d728a0a0000000 0x0035ca2828000000 0xf9fffcf1f0000000 0xbe7fff3c7c000000

def z226 : W := mkw 0x912003f310843ff0 0x644800fcc4210ffc 0x050003f730003ff1 0xc14000fdcc000ffc

def z227 : W := mkw 0x00d728aca0000000 0x0035ca2b28000000 0xc11ffcfff0000001 0xb047ff3ffc000000

def z228 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0x00023008c0000000 0x00008c0230000000

def z229 : W := mkw 0x2008104048405105 0x0802041012101441 0x9f1a32c8c803f03f 0x67c68cb23200fc0f

def z230 : W := mkw 0x0000001000040480 0x0000000400010120 0x40040030007c01c0 0x9001000c001f0070

def z231 : W := mkw 0x4063030e00802a28 0x5018c0c380200a8a 0xbce3830e00003e3d 0x6f38e0c380000f8f

def z232 : W := mkw 0x00b403aca0000000 0x002d00eb28000000 0x79fc03fff0000001 0xde7f00fffc000000

def z233 : W := mkw 0x4043000c01008008 0x1010c00300402002 0x000200080000c00c 0x0000800200003003

def z234 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0xda1e7c00087fc002 0x36879f00021ff000

def z235 : W := mkw 0x2028534148e17957 0x480a14d052385e55 0xfffa73c9cfe3ffff 0xfffe9cf273f8ffff

def z236 : W := mkw 0x81bcc7f00eff3d82 0xe06f31fc03bfcf60 0xfffdcff00fff3fc2 0xffff73fc03ffcff0

def z237 : W := mkw 0x2008504148615157 0x0802141052185455 0x411870c1c06001c0 0x90461c3070180070

def z238 : W := mkw 0x812003b000842c80 0x604800ec00210b20 0x0000013000000e00 0x0000004c00000380

def z239 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfefffd060fffce33 0x7fbfff4183fff38c

def z240 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x26e401300ffc3fc2 0x09b9004c03ff0ff0

def z241 : W := mkw 0x0043800205028220 0x0010e0008140a088 0xbee381060f83ce33 0x6fb8e04183e0f38c

def z242 : W := mkw 0x604bd04f4d63d37f 0x1812f413d358f4df 0xdf1bf2cfc863f1ff 0xf7c6fcb3f218fc7f

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0xd81a700000000000 0x36069c0000000000

def z244 : W := mkw 0x202853ede8615157 0x080a14fb7a185455 0xdf1a73fff863f1ff 0xf7c69cfffe18fc7f

def z245 : W := mkw 0x40f7ab0e0582aa28 0x503deac38160aa8a 0xfeffff0e0f83fe3f 0x7fbfffc383e0ff8f

def z246 : W := mkw 0x02942c0002180000 0x80a50b0000860000 0x00040c00001c0000 0x0001030000070000

def z247 : W := mkw 0x0000800204020220 0x0000200081008088 0xbe03830e0c03fe3f 0x6f80e0c38300ff8f

def z248 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x6ce4013007fc0fc2 0xdb39004c01ff03f0

def z249 : W := mkw 0x029cfc000e7b4003 0x80a73f00039ed000 0xe81dfc00047f0002 0x3a077f00011fc000

def z250 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6005cd37347c0fc0 0x9801734dcd1f03f0

def z251 : W := mkw 0x2008104048405105 0x0802041012101441 0x5f1a32c8c860f1ce 0xd7c68cb232183c73

def z252 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x61fdfdf7f0000000 0x987f7f7dfc000000

def z253 : W := mkw 0x10946cb1b02d04d2 0x84251b2c6c0b4134 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z254 : W := mkw 0x202003ede0001154 0x080800fb78000455 0x050003fff00031fd 0xc14000fffc000c7f

def z255 : W := mkw 0x00f72ba000000000 0x003dcae800000000 0xf9fffff000000000 0xfe7ffffc00000000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x20058d3630000000 0x0801634d8c000000

def z257 : W := mkw 0x81ff2bfcaad43d80 0x607fcaff2ab50f60 0x7ffe33f8cffc3fc2 0xdfff8cfe33ff0ff0

def z258 : W := mkw 0x2008004148401154 0x0802001052100455 0x5f1802c9c86031ff 0xd7c600b272180c7f

def z259 : W := mkw 0xa12853f148e57dd7 0x684a14fc52395f75 0xdf1a73f9c863ffff 0xf7c69cfe7218ffff

def z260 : W := mkw 0x2000500140214057 0x0800140050085015 0x9e027209c803f03f 0x67809c827200fc0f

def z261 : W := mkw 0x91bc87f21ede3fa0 0xe46f21fc87b78fe8 0x7ffd8ff63ffc3fc2 0xdfff63fd8fff0ff0

def z262 : W := mkw 0x2008504148615157 0x0802141052185455 0x531a72c9c860f1cc 0x94c69cb272183c73

def z263 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe03f80fffffff 0xffff80fe03ffffff

def z264 : W := mkw 0x0243fc00052bc003 0x8090ff00014af000 0xbae3fc000f83c002 0x2eb8ff0003e0f000

def z265 : W := mkw 0x1043ec1fb42f06f2 0x8410fb07ed0bc1bc 0xec07fd3ff47f0ff3 0xfb01ff4ffd1fc3fc

def z266 : W := mkw 0x42ffbb0e0fd2ea29 0x50bfeec383f4ba8a 0xbefbb30e0f83fe3f 0x6fbeecc383e0ff8f

def z267 : W := mkw 0x00ff7baca8614003 0x003fdeeb2a185000 0xfbfffffff863c003 0xfefffffffe18f000

def z268 : W := mkw 0x00f7abaea4020220 0x003deaeba9008088 0xfdfffffff4030e33 0xff7ffffffd00c38c

def z269 : W := mkw 0x00d7ec00042b0002 0x8035fb00010ac000 0xf8fffc00047f0002 0x3e3fff00011fc000

def z270 : W := mkw 0x83dffc500ffffd83 0xe0f7ff1403ffff60 0xfefffc000fffffc2 0x3fbfff0003fffff0

def z271 : W := mkw 0xa1bc53f14af57dd7 0x686f14fc52bd5f75 0xfffe73f9cfffffff 0xffff9cfe73ffffff

def z272 : W := mkw 0x20f77bade0214057 0x083ddeeb78085015 0xf9fffffff003c03d 0xfe7ffffffc00f00f

def z273 : W := mkw 0x0008004008401100 0x0002001002100440 0xdf1a02c80863f1ff 0xf7c680b20218fc7f

def z274 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0x20e58c0000000000 0x0839630000000000

def z275 : W := mkw 0x2008d4414c6b5157 0x88023510531ad455 0xff1ffec9cc7ff1ff 0xffc7ffb2731ffc7f

def z276 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfbfffec8cffff00e 0x3effffb233fffc03

def z277 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0xfafffc000b80c000 0x3ebfff0002e03000

def z278 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0x00040c3030000000 0x0001030c0c000000

def z279 : W := mkw 0x00df780008614003 0x0037de0002185000 0xfafffc000863c002 0x3ebfff000218f000

def z280 : W := mkw 0x81ff83f00fd6bd80 0x607fe0fc03f5af60 0xffff83f00fffffc2 0xffffe0fc03fffff0

def z281 : W := mkw 0xa1bc13f04ad47d85 0x686f04fc12b51f61 0x7ffe33f8cffcffce 0xdfff8cfe33ff3ff3

def z282 : W := mkw 0x02dffc0caf7bc003 0x80b7ff032bdef000 0xfafffc0fffffc003 0x3ebfff03fffff000

def z283 : W := mkw 0x83ff3be00bd0f901 0x60ffcef802f43e40 0x13fa32c00b80f000 0x04fe8cb002e03c00

def z284 : W := mkw 0x2008d0434c635377 0x08023410d318d4dd 0xff1bf3cfcc63ffff 0xffc6fcf3f318ffff

def z285 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x26e181060f83fe3e 0x09b8604183e0ff8f

def z286 : W := mkw 0x810000f000041580 0x2040003c00010560 0x010000f0000001c0 0x8040003c00000070

def z287 : W := mkw 0x2000500140214057 0x0800140050085015 0xcc027009c063c1ff 0xf3009c027018f07f

def z288 : W := mkw 0x12d7ac12171e86a0 0x84b5eb0485c7a1a8 0x20e58d36379c0e00 0x0839634d8de70380

def z289 : W := mkw 0x5020031f10842ef8 0x540800c7c4210bbe 0x0400033f30003ffd 0xc10000cfcc000fff

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001cc0730000001 0x20007301cc000000

def z291 : W := mkw 0x1243fc13152fc6f3 0x8490ff04c54bf1bc 0xec07fd37347fcff3 0xfb01ff4dcd1ff3fc

def z292 : W := mkw 0x2008504148615157 0x0802141052185455 0xcd1870c1c06301f3 0xf3461c307018c07c

def z293 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x92e3820e0b83f03d 0x24b8e08382e0fc0f

def z294 : W := mkw 0x40f7abaea582aa28 0x503deaeba960aa8a 0xf9fffffff7800e01 0xfe7ffffffde00380

def z295 : W := mkw 0x00b403a000000000 0x002d00e800000000 0xf9fe73f9c0000001 0xfe7f9cfe70000000

def z296 : W := mkw 0x6063d30f45a3ea7f 0x5818f4c3d168fa9f 0xbee3f30fcf83fe3f 0x6fb8fcc3f3e0ff8f

def z297 : W := mkw 0x0000000000802800 0x4000000000200a00 0x060000000f803e02 0x0180000003e00f80

def z298 : W := mkw 0x812803f008c43d80 0x604a00fc02310f60 0x5f1803f008603fc2 0xd7c600fc02180ff0

def z299 : W := mkw 0x93fffff31ffffff3 0xe4fffffcc7fffffc 0xfffffff73ffffff3 0xfffffffdcffffffc

def z300 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xa0e3810e0783ce3d 0x2838e04381e0f38f

def z301 : W := mkw 0x4063830c0582a808 0x5018e0c30160aa02 0xbae382080f83f00e 0x2eb8e08203e0fc03

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00000000030033 0x630000000000c00c

def z303 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0xe91dfdf7f0000001 0xfa477f7dfc000000

def z304 : W := mkw 0xc1ff03fc0bd4bd88 0x707fc0ff02f52f62 0x7ffe03f80ffcffce 0xdfff80fe03ff3ff3

def z305 : W := mkw 0x1063c71f142f06f2 0x8418f1c7c50bc1bc 0xfce7cf3f347f0ff3 0xff39f3cfcd1fc3fc

def z306 : W := mkw 0x406bd30e0de3ea2b 0x501af4c38378fa8a 0xfefbf30e0fe3fe3f 0x7fbefcc383f8ff8f

def z307 : W := mkw 0x706bd75f5defffff 0xdc1af5d7d77bffff 0xffffffffffffffff 0xffffffffffffffff

def z308 : W := mkw 0x5063871e158eaea8 0xd418e1c78563abaa 0xbee78f3e3f9ffe3f 0x6fb9e3cf8fe7ff8f

def z309 : W := mkw 0x2008104048405105 0x0802041012101441 0x020000000800f00c 0x0080000002003c03

def z310 : W := mkw 0x810800400ad03900 0x6042001002b40e40 0x020000000b803000 0x0080000002e00c00

def z311 : W := mkw 0x32dffc535f7fd7f7 0x8cb7ff14d7dff5fd 0xffffffffffffffff 0xffffffffffffffff

def z312 : W := mkw 0x6008d0434de3fb7f 0x58023410d378fedf 0x060000000fe3fffe 0x0180000003f8ffff

def z313 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0xac01cd0734030e33 0x6b007341cd00c38c

def z314 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xb8e3830e07800e01 0x6e38e0c381e00380

def z315 : W := mkw 0x029c38000a504001 0x00a70e0002941000 0x0018300000000000 0x00060c0000000000

def z316 : W := mkw 0x10008013140606f0 0x04002004c50181bc 0xac01813734030ff3 0xeb00604dcd00c3fc

def z317 : W := mkw 0x5000c41315afaefa 0xd4003104c56bebbe 0xee05cd373fffffff 0xfb81734dcfffffff

def z318 : W := mkw 0x812003e000803900 0x604800f800200e40 0x010002c000003000 0x004000b000000c00

def z319 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0x9ee202080b83f03f 0x67b8808202e0fc0f

def z320 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0x52fe7c000bfcc000 0x14bf9f0002ff3000

def z321 : W := mkw 0x606b534d49e1f95f 0x581ad4d352787e57 0xdffa72c9cbe3f1ff 0xf7fe9cb272f8fc7f

def z322 : W := mkw 0x819c00f00a541580 0x2067003c02950560 0x6d1c01f0047c0fc2 0xdb47007c011f03f0

def z323 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfe07cf3f3c7fffff 0xff81f3cfcf1fffff

def z324 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x8401cd3730030ff1 0xe100734dcc00c3fc

def z325 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0xe807fd3ff0000001 0xfa01ff4ffc000000

def z326 : W := mkw 0x0000800005028000 0x000020000140a000 0x020000000f83c002 0x0080000003e0f000

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x411870c1c0000000 0x90461c3070000000

def z328 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0xee05cd373c7fffff 0xfb81734dcf1fffff

def z329 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf9fffec8c0000000 0x3e7fffb230000000

def z330 : W := mkw 0x22df38404b50d105 0x08b7ce1012d43441 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z331 : W := mkw 0xa1ff7bfdeaf57dd7 0x687fdeff7abd5f75 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x00f7efaca42b0002 0x803dfbeb290ac000 0xf9fffffff47f0003 0xfe7ffffffd1fc000

def z333 : W := mkw 0x0000500000214003 0x0000140000085000 0x800270000003c000 0x20009c000000f000

def z334 : W := mkw 0x81f72bfca0843d80 0x607dcaff28210f60 0xfdfffffff0003fc1 0xff7ffffffc000ff0

def z335 : W := mkw 0x0243fc00052bc003 0x8090ff00014af000 0xe807fc00047fc002 0x3a01ff00011ff000

def z336 : W := mkw 0xa1bc13e04ad07905 0x686f04f812b41e41 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z337 : W := mkw 0xc1f783be0796aea8 0x707de0ef81e5abaa 0xbee7833e0f9ffe3f 0x6fb9e0cf83e7ff8f

def z338 : W := mkw 0x62ffff4f4ffbfb7f 0xd8bfffd3d3fefedf 0xffffffcfcfffffff 0xfffffff3f3ffffff

def z339 : W := mkw 0xa10850514af57dd7 0x6842141452bd5f75 0x060000000ffffffe 0x0180000003ffffff

def z340 : W := mkw 0x0000001000040480 0x0000000400010120 0x0400013000000fc0 0xc100004c000003f0

def z341 : W := mkw 0x00f7abaca5028000 0x003deaeb2940a000 0xfbffffffff83c003 0xfeffffffffe0f000

def z342 : W := mkw 0x10d7ec13142f06f2 0x8435fb04c50bc1bc 0xfcfffd37347f0ff3 0xff3fff4dcd1fc3fc

def z343 : W := mkw 0x22ffffedef7bd157 0x88bffffb7bdef455 0xfffffffffffff1ff 0xfffffffffffffc7f

def z344 : W := mkw 0x0020030000802800 0x400800c000200a00 0x0400030000003e00 0x410000c000000f80

def z345 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x92fbfc000b83c000 0x24beff0002e0f000

def z346 : W := mkw 0x9108c4531eff3ff2 0xe4423114c7bfcffc 0x060000000fff3ff2 0x0180000003ffcffc

def z347 : W := mkw 0x81ff2bf00ad43d80 0x607fcafc02b50f60 0xfffffff00ffc3fc2 0xfffffffc03ff0ff0

def z348 : W := mkw 0x229c7c414a795157 0x88a71f10529e5455 0xdf1e7ec9c87ff1ff 0xf7c79fb2721ffc7f

def z349 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfbfffcc1cfffc1c2 0xbeffff3073fff070

def z350 : W := mkw 0x40f7abaea582aa28 0x503deaeba960aa8a 0xbffbb3cecf83fe3f 0x6ffeecf3b3e0ff8f

def z351 : W := mkw 0x0028034008c03900 0x400a00d002300e40 0x7ff803c00fe03fc2 0xdffe00f003f80ff0

def z352 : W := mkw 0x919cc4f31e7f17f2 0xa467313cc79fc5fc 0xed1dcdf7347f0ff3 0xfb47737dcd1fc3fc

def z353 : W := mkw 0x0008004008401100 0x0002001002100440 0x131802c008003000 0x04c600b002000c00

def z354 : W := mkw 0x0000001000040480 0x0000000400010120 0x20040130041c0e00 0x0801004c01070380

def z355 : W := mkw 0x0063830e04020220 0x0018e0c381008088 0xbce3830e04030e33 0x6f38e0c38100c38c

def z356 : W := mkw 0x606bd34f4de3fb7f 0x581af4d3d378fedf 0xbee3830e0fe3ffff 0x6fb8e0c383f8ffff

def z357 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x22e58c000fffc002 0x08b9630003fff000

def z358 : W := mkw 0x00008400040a0000 0x8000210001028000 0x20058c00041c0000 0x0801630001070000

def z359 : W := mkw 0x81bc03e00ad03900 0x606f00f802b40e40 0x3ff803c00f803e02 0x4ffe00f003e00f80

def z360 : W := mkw 0x12ffffbfbf7fc6f3 0x84bfffefefdff1bc 0xffffffffffffcff3 0xfffffffffffff3fc

def z361 : W := mkw 0x60fffbefede3fb7f 0x583ffefbfb78fedf 0xffffffffffe3ffff 0xfffffffffff8ffff

def z362 : W := mkw 0x20bc53e148615157 0x082f14f852185455 0xfffe73f9c863f1ff 0xffff9cfe7218fc7f

def z363 : W := mkw 0x2000000140000054 0x0800000050000015 0x00000009c000003d 0x000000027000000f

def z364 : W := mkw 0x12dffc121f7fc6a3 0x84b7ff0487dff1a8 0xfafffd363fffce02 0x3ebfff4d8ffff380

def z365 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffd373fffc003 0xfebfff4dcffff000

def z366 : W := mkw 0x40f7abaea582aa28 0x503deaeba960aa8a 0xbee78f3e3f83fe3f 0x6fb9e3cf8fe0ff8f

def z367 : W := mkw 0x1000c411142f04d2 0x84003104450bc134 0xe805cc31347f01c2 0xba01730c4d1fc070

def z368 : W := mkw 0x02d7280003108000 0x00b5ca0000c42000 0x00e0000003800000 0x0038000000e00000

def z369 : W := mkw 0x0043000000000000 0x0010c00000000000 0xb8e3800000000000 0x2e38e00000000000

def z370 : W := mkw 0x810800500a541580 0x2042001402950560 0x00000000007c01c0 0x00000000001f0070

def z371 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0xf8fffd3730000001 0xfe3fff4dcc000000

def z372 : W := mkw 0x81bc53f00af57d83 0x606f14fc02bd5f60 0xfffe73f00fffffc2 0xffff9cfc03fffff0

def z373 : W := mkw 0x0000000100000050 0x0000000040000014 0x04000001000001f1 0xc10000004000007c

def z374 : W := mkw 0x4020030e00802a28 0x500800c380200a8a 0x0000010600000e00 0x0000004180000380

def z375 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x79fd8ff630000000 0xde7f63fd8c000000

def z376 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0x6c044d31347c0fc2 0xdb01134c4d1f03f0

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804013000000000 0xda01004c00000000

def z378 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x17f803f00b803fc0 0xc5fe00fc02e00ff0

def z379 : W := mkw 0x000800000a500000 0x0002000002940000 0x020000000ffc0002 0x0080000003ff0000

def z380 : W := mkw 0x4043800e05028228 0x1010e0038140a08a 0x9e03820e0803f03f 0x6780e0838200fc0f

def z381 : W := mkw 0x009400a000000000 0x0025002800000000 0x411c00f000000000 0x9047003c00000000

def z382 : W := mkw 0x40f783ae0582aa28 0x503de0eb8160aa8a 0xffff83fe0f83fe3f 0xffffe0ff83e0ff8f

def z383 : W := mkw 0x0008500108614053 0x0002140042185014 0xde1a70010863c1f3 0xf7869c004218f07c

def z384 : W := mkw 0x0020031000842c80 0x400800c400210b20 0x7ee403300ffc3fc2 0xdfb900cc03ff0ff0

def z385 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffdcff73ffc3fc3 0xffff73fdcfff0ff0

def z386 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0x011830c0c0000000 0x00460c3030000000

def z387 : W := mkw 0x0000800204020220 0x0000200081008088 0x8001800600030031 0x200060018000c00c

def z388 : W := mkw 0x6043d00f4523c27f 0x1810f403d148f09f 0x8003f00fc003c03d 0x2000fc03f000f00f

def z389 : W := mkw 0xa12003f140843dd4 0x684800fc50210f75 0x050003f9c0003ffd 0xc14000fe70000fff

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x68040000047c0002 0x1a010000011f0000

def z391 : W := mkw 0x4263ff0e05abea2b 0xd098ffc3816afa8a 0xbee3ff0e0f83fe3f 0x6fb8ffc383e0ff8f

def z392 : W := mkw 0x2008104048405105 0x0802041012101441 0xdb1a72c9c800f00d 0xf6c69cb272003c03

def z393 : W := mkw 0x2208d4414f7bd157 0x8882351053def455 0x060000000ffff1fe 0x0180000003fffc7f

def z394 : W := mkw 0x009c00000a500000 0x0027000002940000 0x12f800000b800000 0x04be000002e00000

def z395 : W := mkw 0x2000500140214057 0x0800140050085015 0x000000000003c03c 0x000000000000f00f

def z396 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0x20e1810600000000 0x0838604180000000

def z397 : W := mkw 0x0000004000001100 0x0000001000000440 0x050002c0000031c0 0xc14000b000000c70

def z398 : W := mkw 0x6020034f40803b7c 0x580800d3d0200edf 0x050003cfc0003ffd 0xc14000f3f0000fff

def z399 : W := mkw 0x400080020582aa28 0x500020008160aa8a 0x9e0202080f83fe3f 0x6780808203e0ff8f

def z400 : W := mkw 0x002003aca0000000 0x000800eb28000000 0x0000013630000000 0x0000004d8c000000

def z401 : W := mkw 0x0200d400052bc003 0x80803500014af000 0x000000000003c000 0x000000000000f000

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0xdf1a72c9c803f03f 0xf7c69cb27200fc0f

def z403 : W := mkw 0x81b403f002943d80 0x606d00fc00a50f60 0x25e403f0079c3fc0 0xc97900fc01e70ff0

def z404 : W := mkw 0x1000440110290052 0x84001100440a4014 0x00004c0130000000 0x000013004c000000

def z405 : W := mkw 0xc1ff83ee0fd2bb28 0x707fe0fb83f4aeca 0xbffb83ce0f83fe3f 0x6ffee0f383e0ff8f

def z406 : W := mkw 0x0000001000040480 0x0000000400010120 0xec05cd37347c0fc3 0xfb01734dcd1f03f0

def z407 : W := mkw 0x10000011100404d0 0x0400000444010134 0x00000031300001c0 0x8000000c4c000070

def z408 : W := mkw 0x83ffaff00fdebd80 0xe0ffebfc03f7af60 0x7ffd8ff00ffc3fc2 0xdfff63fc03ff0ff0

def z409 : W := mkw 0x0008504008615103 0x0002141002185440 0xdf1a72c00863f1c2 0xf7c69cb00218fc70

def z410 : W := mkw 0x024338000100c001 0x0090ce0000403000 0x000230000000c000 0x00008c0000003000

def z411 : W := mkw 0x02dfb8000f52c001 0x00b7ee0003d4b000 0xbafbb0000f83c002 0x2ebeec0003e0f000

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800400100000001 0xf200100040000000

def z413 : W := mkw 0x81bc03b00ad42c80 0x606f00ec02b50b20 0x7afc01300ffc0e02 0x1ebf004c03ff0380

def z414 : W := mkw 0x4020830e04822a28 0x500820c381208a8a 0xac01830e04033e3f 0x6b0060c38100cf8f

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ae000000f800002 0x0eb8000003e00000

def z416 : W := mkw 0x0000c400042b0002 0x80003100010ac000 0xe805cd37347f0003 0xfa01734dcd1fc000

def z417 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x00e0000000000000 0x0038000000000000

def z418 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfffbf3cfcf83fe3f 0xfffefcf3f3e0ff8f

def z419 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0xe8e5cc0007ff0002 0x3a39730001ffc000

def z420 : W := mkw 0x12dffc111f7fc4d3 0x84b7ff0447dff134 0xfafffc313fffc1c2 0xbebfff0c4ffff070

def z421 : W := mkw 0x00f72bbca0040480 0x003dcaef28010120 0xfdfffffff47c0fc3 0xff7ffffffd1f03f0

def z422 : W := mkw 0x009c50000a714003 0x00271400029c5000 0xfafe70000fffc002 0x3ebf9c0003fff000

def z423 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xc01ffc00007fc000 0x3007ff00001ff000

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x111a32c8c0000000 0x04468cb230000000

def z425 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x79fc03f0079c0e00 0xde7f00fc01e70380

def z426 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x33fc03f00f9c3e00 0x0cff00fc03e70f80

def z427 : W := mkw 0x81ff2bfcaad43d80 0x607fcaff2ab50f60 0x7ffd8ff63ffc3fc2 0xdfff63fd8fff0ff0

def z428 : W := mkw 0x30000053500417f4 0x0c000014d40105fd 0x050003fff0003ffd 0xc14000fffc000fff

def z429 : W := mkw 0x20085051486555d7 0x0802141452195575 0xff1e73f9cc7fffff 0xffc79cfe731fffff

def z430 : W := mkw 0x029cfc000f7bc003 0x80a73f0003def000 0x421c7c000fffc002 0x10871f0003fff000

def z431 : W := mkw 0x4000800205028228 0x100020008140a08a 0x000000000003c03c 0x000000000000f00f

def z432 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0x060000000c7ffffe 0x01800000031fffff

def z433 : W := mkw 0x2008500148614057 0x0802140052185015 0xda1a7009c863c03f 0x36869c027218f00f

def z434 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xace1810607830e33 0x6b38604181e0c38c

def z435 : W := mkw 0xa1bc53f14af57dd7 0x686f14fc52bd5f75 0x7ffc73f1cffc3fc2 0xdfff1cfc73ff0ff0

def z436 : W := mkw 0x819c00f00a541580 0x2067003c02950560 0x5f1c02f0087c31c2 0xd7c700bc021f0c70

def z437 : W := mkw 0x02ff3bacab50c001 0x00bfceeb2ad43000 0xfbfffffffb80c001 0xfefffffffee03000

def z438 : W := mkw 0x10004013102506f2 0x04001004c40941bc 0xcc00413730630ff3 0xf300104dcc18c3fc

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0xa801810600000001 0x6a00604180000000

def z440 : W := mkw 0x02ffffacaf7bc003 0x80bfffeb2bdef000 0xfbfffec8cfffc002 0x3effffb233fff000

def z441 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0x00000000007c01c0 0x00000000001f0070

def z442 : W := mkw 0x0000001000040480 0x0000000400010120 0x04000000047c0fc2 0x01000000011f03f0

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x591802c000000000 0xd64600b000000000

def z444 : W := mkw 0x10000012100406a0 0x04000004840101a8 0x0000013630000e00 0x0000004d8c000380

def z445 : W := mkw 0x91bc47f11afd3dd2 0xe46f11fc46bf4f74 0x7ffc4ff13ffc3fc2 0xdfff13fc4fff0ff0

def z446 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0x10fa300000000000 0x043e8c0000000000

def z447 : W := mkw 0x02df7c000a794003 0x80b7df00029e5000 0xf8fffc00007c0000 0x3e3fff00001f0000

def z448 : W := mkw 0x42dffc0e0f7bc22b 0x90b7ff0383def08a 0xfafffc0e0fffc03f 0x3ebfff0383fff00f

def z449 : W := mkw 0x000000a0a0000000 0x0000002828000000 0x010000f1f0000000 0x8040003c7c000000

def z450 : W := mkw 0x40ff830e0fd2aa28 0x503fe0c383f4aa8a 0xfeff830e0ffffe3f 0x7fbfe0c383ffff8f

def z451 : W := mkw 0x83fffffcaffffd83 0xe0ffffff2bffff60 0xffffffffffffffc3 0xfffffffffffffff0

def z452 : W := mkw 0x0000400100210052 0x0000100040084014 0x8000400100030031 0x200010004000c00c

def z453 : W := mkw 0x00b42ba0a0000000 0x002d0ae828000000 0x79fc7ff1f0000000 0xde7f1ffc7c000000

def z454 : W := mkw 0x2008504148615157 0x0802141052185455 0x5f1872c1c86031c2 0xd7c61cb072180c70

def z455 : W := mkw 0x8308d4500ffffd83 0xe0c2351403ffff60 0x060000000fffffc2 0x0180000003fffff0

def z456 : W := mkw 0x810800500ad43d80 0x6042001402b50f60 0x5f1802c00ffc3fc2 0xd7c600b003ff0ff0

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c000000006001c2 0xd300000000180070

def z458 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0xbee3830e0803f03f 0x6fb8e0c38200fc0f

def z459 : W := mkw 0x0043000c00000000 0x0010c00300000000 0x8003800e00000001 0x2000e00380000000

def z460 : W := mkw 0x4043a80ea5028228 0x1010ea03a940a08a 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z461 : W := mkw 0x2000500140214057 0x0800140050085015 0xd91a72c9c003c03d 0xf6469cb27000f00f

def z462 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xcc004001047f0ff3 0xf3001000411fc3fc

def z463 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x60fdfc0007fc0000 0x183f7f0001ff0000

def z464 : W := mkw 0x00f72b0c00000000 0x003dcac300000000 0xf8ffff0e00000001 0x7e3fffc380000000

def z465 : W := mkw 0x4000000e00000228 0x100000038000008a 0x0000000e0000003d 0x000000038000000f

def z466 : W := mkw 0xa1bc53f14af57dd7 0x686f14fc52bd5f75 0x7ffc03f00ffffffe 0xdfff00fc03ffffff

def z467 : W := mkw 0x002003aca0000000 0x000800eb28000000 0xe905cffff0000001 0xfa4173fffc000000

def z468 : W := mkw 0x02008400071a8000 0x8080210001c6a000 0x00000000079c0000 0x0000000001e70000

def z469 : W := mkw 0x4063c30f05a3aa7a 0x5018f0c3c168ea9e 0xfee3c30f0fe3ffff 0xffb8f0c3c3f8ffff

def z470 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffe080ffff03f 0x7fbfff8203fffc0f

def z471 : W := mkw 0xa19c50f14a7555d7 0x2867143c529d5575 0x411c70f1c07c01c0 0x90471c3c701f0070

def z472 : W := mkw 0x606b934e4dc2fb2d 0x581ae4d39370becb 0xbffbb3cecf83fe3f 0x6ffeecf3b3e0ff8f

def z473 : W := mkw 0x02ff3bacab50c001 0x00bfceeb2ad43000 0x13fa32c8cb80c000 0x04fe8cb232e03000

def z474 : W := mkw 0x2008104148405155 0x0802041052101455 0x171a32c9c800f1fd 0xc5c68cb272003c7f

def z475 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x3ee403300f9c3e02 0x4fb900cc03e70f80

def z476 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xa0e7fd3ff0000001 0x2839ff4ffc000000

def z477 : W := mkw 0x81ff2bfcaa541580 0x207fcaff2a950560 0xf9fffffff07c01c1 0xfe7ffffffc1f0070

def z478 : W := mkw 0x20ff3bece8405105 0x083fcefb3a101441 0xfbfffffff800f00d 0xfefffffffe003c03

def z479 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x51fe7ef9f0000000 0x947f9fbe7c000000

def z480 : W := mkw 0x0208d4000f7bc003 0x8082350003def000 0xea05cc000fffc002 0x3a81730003fff000

def z481 : W := mkw 0x83bc7ff00afd7d83 0xe0ef1ffc02bf5f60 0x7ffc7ff00ffc3fc2 0xdfff1ffc03ff0ff0

def z482 : W := mkw 0x10f7afbeb40e06a0 0x843debefad0381a8 0xf9fffffff41c0e01 0xfe7ffffffd070380

def z483 : W := mkw 0x2008504148615157 0x0802141052185455 0x00000000006001c0 0x0000000000180070

def z484 : W := mkw 0x129cfc131e7f46f3 0x84a73f04c79fd1bc 0xec1dfd37347f0ff3 0xfb077f4dcd1fc3fc

def z485 : W := mkw 0x919c44f11a7d15d2 0xa467113c469f4574 0x411c4cf1307c01c0 0x9047133c4c1f0070

def z486 : W := mkw 0xa10850514af57dd7 0x6842141452bd5f75 0xdf1a72c9cfffffff 0xf7c69cb273ffffff

def z487 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x32e3830e0f80fe0c 0x0cb8e0c383e03f83

def z488 : W := mkw 0x91b487b2169e2ea0 0xe46d21ec85a78ba8 0x20e58d36379c0e00 0x0839634d8de70380

def z489 : W := mkw 0x0000c400042b0002 0x80003100010ac000 0x00000000047f0002 0x00000000011fc000

def z490 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x6d0403f0047c3fc2 0xdb4100fc011f0ff0

def z491 : W := mkw 0x204bd0414d63d157 0x0812f4105358f455 0xfffbf2c9cfe3f1ff 0xfffefcb273f8fc7f

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802020800000001 0x6600808200000000

def z493 : W := mkw 0xc1bc03fe0ad43fa8 0x706f00ff82b50fea 0x7ffc03fe0ffc3fff 0xdfff00ff83ff0fff

def z494 : W := mkw 0x02df78000b71c003 0x00b7de0002dc7000 0xdafa70000be3c002 0x36be9c0002f8f000

def z495 : W := mkw 0x81ff2becaad03900 0x607fcafb2ab40e40 0x13fa32c8cb803000 0x04fe8cb232e00c00

def z496 : W := mkw 0x1008c4531c6f17f2 0x84023114c71bc5fc 0xff1dcff73c7f3ff3 0xffc773fdcf1fcffc

def z497 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x04000137347f0ff3 0xc100004dcd1fc3fc

def z498 : W := mkw 0x002003aca0000000 0x000800eb28000000 0xd91a73fff0000001 0xf6469cfffc000000

def z499 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0xcc044c31307f01f3 0xf301130c4c1fc07c

def z500 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0xcc01cc07306301f3 0xf3007301cc18c07c

def z501 : W := mkw 0x0008500008614003 0x0002140002185000 0x020000000863c002 0x008000000218f000

def z502 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xe8e5cd3730000001 0xfa39734dcc000000

def z503 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xbae78c000f9fc002 0x2eb9e30003e7f000

def z504 : W := mkw 0x0043000001008000 0x0010c00000402000 0x12e200000b80c000 0x04b8800002e03000

def z505 : W := mkw 0x83ffffb00fffec83 0xe0ffffec03fffb20 0xfafffd300fffce02 0x3ebfff4c03fff380

def z506 : W := mkw 0x91ffefffbeff3ff2 0xe47ffbffefbfcffc 0xffffffffffff3ff3 0xffffffffffffcffc

def z507 : W := mkw 0x4063030e0180aa28 0x5018c0c380602a8a 0x16e2030e0b80fe3d 0x45b880c382e03f8f

def z508 : W := mkw 0x0008d4000c6b4003 0x80023500031ad000 0xfa1ffc000c7fc002 0x3e87ff00031ff000

def z509 : W := mkw 0x00ff2beca8401100 0x003fcafb2a100440 0xfffffffff86031c3 0xfffffffffe180c70

def z510 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0xa0e7fc00079fc000 0x2839ff0001e7f000

def z511 : W := mkw 0x4020830e0582aa28 0x500820c38160aa8a 0x0600030e0f83fe3f 0x418000c383e0ff8f

def z512 : W := mkw 0x0000400100210052 0x0000100040084014 0x04000000006301f2 0x010000000018c07c

def z513 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x31ffbffef0000000 0x0c7fefffbc000000

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x120202080800f00c 0x0480808202003c03

def z515 : W := mkw 0x00b403a000000000 0x002d00e800000000 0xf9fdcff730000001 0xfe7f73fdcc000000

def z516 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0x3ee203080f80fe0e 0x4fb880c203e03f83

def z517 : W := mkw 0x00b403a000802800 0x402d00e800200a00 0x7ffc03f00f803e02 0xdfff00fc03e00f80

def z518 : W := mkw 0x2000100040004005 0x0800040010001001 0x00023008c000c00c 0x00008c0230003003

def z519 : W := mkw 0x0000c00304230272 0x00003000c108c09c 0xec01c10704630ff3 0xfb007041c118c3fc

def z520 : W := mkw 0x81bc2bf0aad43d80 0x606f0afc2ab50f60 0x7ffc7ff1fffc3fc2 0xdfff1ffc7fff0ff0

def z521 : W := mkw 0x0020830204822a20 0x400820c081208a88 0xbee183060f833e33 0x6fb860c183e0cf8c

def z522 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0xd91e7ef9f0000001 0xf6479fbe7c000000

def z523 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xac018106047f0ff3 0x6b006041811fc3fc

def z524 : W := mkw 0x42f7af0e079aaa28 0xd0bdebc381e6aa8a 0xbee78f0e0f9ffe3f 0x6fb9e3c383e7ff8f

def z525 : W := mkw 0x839c7cf00a7d5583 0xa0e71f3c029f5560 0x411c7cf0007c01c0 0x90471f3c001f0070

def z526 : W := mkw 0x402083020582aa28 0x500820c08160aa8a 0x3ee003000f83fe3e 0x4fb800c003e0ff8f

def z527 : W := mkw 0x30085451586d55d7 0x8c021514561b5575 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z528 : W := mkw 0xe1ffd3ff4ff7ffff 0x787ff4ffd3fdffff 0xfffff3ffcfffffff 0xfffffcfff3ffffff

def z529 : W := mkw 0xc1ff03ec0bd0b908 0x707fc0fb02f42e42 0x13fa02c80b80f00c 0x04fe80b202e03c03

def z530 : W := mkw 0x1020c7bfb42f06f2 0x840831efed0bc1bc 0xed05cffff47f0ff3 0xfb4173fffd1fc3fc

def z531 : W := mkw 0x0008004008401100 0x0002001002100440 0x06000000086031c2 0x0180000002180c70

def z532 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0xf8e7cf3f30000001 0xfe39f3cfcc000000

def z533 : W := mkw 0x819c28f0aa541580 0x20670a3c2a950560 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z534 : W := mkw 0x81bc03e00ad03900 0x606f00f802b40e40 0x5ff802c00be031c2 0xd7fe00b002f80c70

def z535 : W := mkw 0x402003aea0802a28 0x500800eba8200a8a 0x050003fff0003e3d 0xc14000fffc000f8f

def z536 : W := mkw 0x9108c4531eff3ff2 0xe4423114c7bfcffc 0xee05cd373fff3ff3 0xfb81734dcfffcffc

def z537 : W := mkw 0xc16b835e0fd6bfa8 0x705ae0d783f5afea 0xbee3830e0fffffff 0x6fb8e0c383ffffff

def z538 : W := mkw 0x00632b0ca0000000 0x0018cac328000000 0xb8e3ff0ff0000001 0x6e38ffc3fc000000

def z539 : W := mkw 0x020854000a794003 0x80821500029e5000 0x00000000007c0000 0x00000000001f0000

def z540 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x16e202080f83fe3e 0x05b8808203e0ff8f

def z541 : W := mkw 0x2008504148615157 0x0802141052185455 0x86027009c863f1ff 0x21809c027218fc7f

def z542 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x91fbfecff0000001 0x247effb3fc000000

def z543 : W := mkw 0x4043800e05028228 0x1010e0038140a08a 0xac03810e0403ce3f 0x6b00e0438100f38f

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x80027009c0000001 0x20009c0270000000

def z545 : W := mkw 0x024bfc000f7bc003 0x8092ff0003def000 0x8203fc000fffc002 0x2080ff0003fff000

def z546 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x8401cc07347f0ff3 0x21007301cd1fc3fc

def z547 : W := mkw 0xd1ffc7ff1fffbffa 0xf47ff1ffc7ffeffe 0xffffcfff3fffffff 0xfffff3ffcfffffff

def z548 : W := mkw 0x002003aca0000000 0x000800eb28000000 0x010002c8c0000000 0x004000b230000000

def z549 : W := mkw 0x020810000b50c001 0x0082040002d43000 0x020000000b80c000 0x0080000002e03000

def z550 : W := mkw 0x00b42baca0000000 0x002d0aeb28000000 0x411c7ffff0000001 0xd0471ffffc000000

def z551 : W := mkw 0x4063830e05028228 0x1018e0c38140a08a 0xb8e3830e0003c03d 0x6e38e0c38000f00f

def z552 : W := mkw 0x22df78414b71d157 0x08b7de1052dc7455 0xdffa72c9cbe3f1ff 0xf7fe9cb272f8fc7f

def z553 : W := mkw 0x2008504148615157 0x0802141052185455 0xce0040010863f1ff 0xf38010004218fc7f

def z554 : W := mkw 0x2008504148615157 0x0802141052185455 0xd91a72c9c06001c1 0xf6469cb270180070

def z555 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0xe805cd37307c01c1 0xfa01734dcc1f0070

def z556 : W := mkw 0x819400b002140480 0x2065002c00850120 0x00040030001c0000 0x0001000c00070000

def z557 : W := mkw 0xc10880520fd6bfa8 0x7042201483f5afea 0x060000000ffffffe 0x0180000003ffffff

def z558 : W := mkw 0x0243ac00050a8000 0x8090eb000142a000 0x00018c0000000000 0x0000630000000000

def z559 : W := mkw 0x30085451586d55d7 0x8c021514561b5575 0xdf1e7ef9f87ff1ff 0xf7c79fbe7e1ffc7f

def z560 : W := mkw 0x02f7afaca71a8000 0x80bdebeb29c6a000 0x20e58d36379c0000 0x0839634d8de70000

def z561 : W := mkw 0x02ffff0c0f7bc003 0x80bfffc303def000 0xfaffff0e0fffc003 0x7ebfffc383fff000

def z562 : W := mkw 0x0000c400042b0002 0x80003100010ac000 0x8001cc0000030000 0x200073000000c000

def z563 : W := mkw 0x1094ecb3b42f06f2 0x84253b2ced0bc1bc 0xed1dfdf7f47f0ff3 0xfb477f7dfd1fc3fc

def z564 : W := mkw 0x52ffff1f1fffeefb 0xd4bfffc7c7fffbbe 0xfeffff3f3fffffff 0xffbfffcfcfffffff

def z565 : W := mkw 0x10f7afbeb40e06a0 0x843debefad0381a8 0x20e58d36341c0e00 0x0839634d8d070380

def z566 : W := mkw 0x30085053586557f7 0x0c021414d61955fd 0xdf1a73fff863ffff 0xf7c69cfffe18ffff

def z567 : W := mkw 0x02f7ffaca52bc003 0x80bdffeb294af000 0xf9fffffff003c001 0xfe7ffffffc00f000

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00010004000e02 0x4b00004001000380

def z569 : W := mkw 0x2000504140215157 0x0800141050085455 0x850272c9c003f1fd 0xe1409cb27000fc7f

def z570 : W := mkw 0x42ff3b0c0bd0e809 0x50bfcec302f43a02 0x12fa32080b80f00c 0x04be8c8202e03c03

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000013730000001 0xc000004dcc000000

def z572 : W := mkw 0x426bd70e0ffbea2b 0xd09af5c383fefa8a 0xbee3830e0ffffe3f 0x6fb8e0c383ffff8f

def z573 : W := mkw 0x81bc03e00ad03900 0x606f00f802b40e40 0x7bfc02c00ffc3002 0x1eff00b003ff0c00

def z574 : W := mkw 0x0008005008441580 0x0002001402110560 0x7f1c03f00c7c3fc2 0xdfc700fc031f0ff0

def z575 : W := mkw 0x1008d4131c6f46f3 0x84023504c71bd1bc 0xfe1ffd373c7fcff3 0xff87ff4dcf1ff3fc

def z576 : W := mkw 0x83dffcf00f7fd583 0xa0f7ff3c03dff560 0xfbfffcf00fffc1c2 0xbeffff3c03fff070

def z577 : W := mkw 0x83bcd7f00ffffd83 0xe0ef35fc03ffff60 0x7ffc03f00fffffc2 0xdfff00fc03fffff0

def z578 : W := mkw 0x0020030000000000 0x000800c000000000 0x38e0030000000000 0x4e3800c000000000

def z579 : W := mkw 0xc3fffffe0fffffab 0xf0ffffff83ffffea 0xfffffffe0fffffff 0xffffffff83ffffff

def z580 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xb8e78f3e30000001 0x6e39e3cf8c000000

def z581 : W := mkw 0x00b403a000000000 0x002d00e800000000 0x11f802c000000000 0x047e00b000000000

def z582 : W := mkw 0x8100001002942c80 0x6040000400a50b20 0x00000000079c0e00 0x0000000001e70380

def z583 : W := mkw 0x2000004040001104 0x0800001010000441 0x010002c8c000300c 0x004000b230000c03

def z584 : W := mkw 0x0000c402042b0222 0x80003100810ac088 0xec05cd06047f0e33 0x7b017341811fc38c

def z585 : W := mkw 0x00bc03000ad02800 0x402f00c002b40a00 0x7efc03000ffc3e02 0x5fbf00c003ff0f80

def z586 : W := mkw 0x5063871e158eaea8 0xd418e1c78563abaa 0x20e58d36379c0e00 0x0839634d8de70380

def z587 : W := mkw 0x4043800e05028228 0x1010e0038140a08a 0xbae3800e0f83c03f 0x2eb8e00383e0f00f

def z588 : W := mkw 0x0000400100210052 0x0000100040084014 0xec05cd37306301f3 0xfb01734dcc18c07c

def z589 : W := mkw 0x0208d4000f7bc003 0x8082350003def000 0xda1a70000fffc002 0x36869c0003fff000

def z590 : W := mkw 0x00f76bada0210052 0x003ddaeb68084014 0xfdfffffff06301f3 0xff7ffffffc18c07c

def z591 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x53fc02f00bfc31c0 0x94ff00bc02ff0c70

def z592 : W := mkw 0x5063c71f15afaefa 0xd418f1c7c56bebbe 0xece5cd3737ff0ff3 0xfb39734dcdffc3fc

def z593 : W := mkw 0x3008d4435c6b5377 0x8c023510d71ad4dd 0xdf1bfecff863f1ff 0xf7c6ffb3fe18fc7f

def z594 : W := mkw 0x0063030c00802800 0x4018c0c300200a00 0xbee3830e0f803e03 0x6fb8e0c383e00f80

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e00020008003002 0x4780008002000c00

def z596 : W := mkw 0xa19c50f14a7555d7 0x2867143c529d5575 0xdf1e72f9c87ff1ff 0xf7c79cbe721ffc7f

def z597 : W := mkw 0x6008d0434de3fb7f 0x58023410d378fedf 0xdf1a72c9cfe3ffff 0xf7c69cb273f8ffff

def z598 : W := mkw 0x0000800204020220 0x0000200081008088 0xec05cd3734030e33 0xfb01734dcd00c38c

def z599 : W := mkw 0x819c00e00a501100 0x2067003802940440 0x011800c000000000 0x0046003000000000

def z600 : W := mkw 0x10b4c7b3142f06f2 0x842d31ecc50bc1bc 0xfdfdcff7347f0ff3 0xff7f73fdcd1fc3fc

def z601 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0xe805cd3730030031 0xfa01734dcc00c00c

def z602 : W := mkw 0x2000004140001154 0x0800001050000455 0x010000c1c00001c0 0x8040003070000070

def z603 : W := mkw 0x5000c41315afaefa 0xd4003104c56bebbe 0x060000000ffffffe 0x0180000003ffffff

def z604 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0x10e2020800000000 0x0438808200000000

def z605 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x3ee183060f803e02 0x4fb860c183e00f80

def z606 : W := mkw 0x00008012040606a0 0x00002004810181a8 0xec058136047f0ff3 0xfb01604d811fc3fc

def z607 : W := mkw 0x5043c41f152f86fa 0x9410f107c54be1be 0xec07cd3f347fcfff 0xfb01f34fcd1ff3ff

def z608 : W := mkw 0x209c78e1e8615157 0x08271e387a185455 0x411c7cf1f06001c0 0x90471f3c7c180070

def z609 : W := mkw 0xc1ff83fe0fd6bfa8 0x707fe0ff83f5afea 0x7ffd83f60ffc3fc2 0xdfff60fd83ff0ff0

def z610 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0x00018c0630000000 0x000063018c000000

def z611 : W := mkw 0x83f7afb0079eac80 0xe0fdebec01e7ab20 0x20e58d30079c0e00 0x0839634c01e70380

def z612 : W := mkw 0x9120c7f314af3ff2 0xe44831fcc52bcffc 0xed05cff7347f3ff3 0xfb4173fdcd1fcffc

def z613 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x79fe33f8c0000000 0xde7f8cfe30000000

def z614 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x24e1830e07803e3d 0x493860c381e00f8f

def z615 : W := mkw 0x2000004140001154 0x0800001050000455 0x9f0202c9c803f1ff 0xe7c080b27200fc7f

def z616 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6c040130047f0ff2 0xdb01004c011fc3fc

def z617 : W := mkw 0x40f72baea0802a28 0x503dcaeba8200a8a 0xfdfffffff0003e3d 0xff7ffffffc000f8f

def z618 : W := mkw 0x0063830c05028000 0x0018e0c30140a000 0xbae3830e0f83c003 0x6eb8e0c383e0f000

def z619 : W := mkw 0x1208d4131f7fc6f3 0x84823504c7dff1bc 0x060000000fffcff2 0x0180000003fff3fc

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x040002080000303d 0x4100008200000c0f

def z621 : W := mkw 0xa1bc53e14af17957 0x686f14f852bc5e55 0xdffa72c9cbe3f1ff 0xf7fe9cb272f8fc7f

def z622 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0xf9fbf3cfc0000001 0xfe7efcf3f0000000

def z623 : W := mkw 0x102003bfb00406f0 0x040800efec0101bc 0x050003fff0000ff1 0xc14000fffc0003fc

def z624 : W := mkw 0x6063834f4582bb7c 0x5818e0d3d160aedf 0xbfe383cfcf83ffff 0xeff8e0f3f3e0ffff

def z625 : W := mkw 0x4243fc0e052bc22b 0x9090ff03814af08a 0x8003fc0e0003c03d 0x2000ff038000f00f

def z626 : W := mkw 0x0000c410042f0482 0x80003104010bc120 0xec05cd30047f0fc2 0xfb01734c011fc3f0

def z627 : W := mkw 0x91bcc7f31eff3ff2 0xe46f31fcc7bfcffc 0x7ffc03f00fff3ff2 0xdfff00fc03ffcffc

def z628 : W := mkw 0x81f72bbca2942c80 0x607dcaef28a50b20 0x20e58d36379c0e00 0x0839634d8de70380

def z629 : W := mkw 0x129c7c111a7d44d3 0x84a71f04469f5134 0x401c7c31307c01c0 0x90071f0c4c1f0070

def z630 : W := mkw 0x20f72bede0001154 0x083dcafb78000455 0xfdfffffff00031fd 0xff7ffffffc000c7f

def z631 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x8403830e0003fe3d 0x6100e0c38000ff8f

def z632 : W := mkw 0x81bc83f20ed63fa0 0x606f20fc83b58fe8 0xfffd83f60fff3ff3 0xffff60fd83ffcffc

def z633 : W := mkw 0x2008504148615157 0x0802141052185455 0x070002c9c863f1ff 0xc1c000b27218fc7f

def z634 : W := mkw 0x400000000180a808 0x5000000000602a02 0x020000000b80f00c 0x0080000002e03c03

def z635 : W := mkw 0x40f7abaea582aa28 0x503deaeba960aa8a 0x20e58d3637800e00 0x0839634d8de00380

def z636 : W := mkw 0x5063c71f15afaefa 0xd418f1c7c56bebbe 0xbee3830e0fffffff 0x6fb8e0c383ffffff

def z637 : W := mkw 0x10f72bbfb00406f0 0x043dcaefec0101bc 0xfdfffffff0000ff1 0xff7ffffffc0003fc

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a0200000803c002 0x268080000200f000

def z639 : W := mkw 0x5063c70f15abaa7a 0xd418f1c3c56aea9e 0xbee3cf0f3f83fe3f 0x6fb8f3c3cfe0ff8f

def z640 : W := mkw 0x50f7efbfb5afaefa 0xd43dfbefed6bebbe 0xffffffffffffffff 0xffffffffffffffff

def z641 : W := mkw 0x02ff7facaa794003 0x80bfdfeb2a9e5000 0xf9fffffff07c0001 0xfe7ffffffc1f0000

def z642 : W := mkw 0x02007c0000294003 0x80801f00000a5000 0x00007c0000000000 0x00001f0000000000

def z643 : W := mkw 0x00ff2bacaa500000 0x003fcaeb2a940000 0xfbfffffffffc0003 0xfeffffffffff0000

def z644 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xd9fa72c9c0000001 0xf67e9cb270000000

def z645 : W := mkw 0x0000000ca0000000 0x0000000328000000 0x0000000ff0000001 0x00000003fc000000

def z646 : W := mkw 0x1000c403142b0272 0x84003100c50ac09c 0x0000000000030030 0x000000000000c00c

def z647 : W := mkw 0x40f72baca180a808 0x503dcaeb28602a02 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z648 : W := mkw 0x2008504048615107 0x0802141012185441 0xdb1a72c8c863f00e 0x36c69cb23218fc03

def z649 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xa005cd37341f0e31 0x2801734dcd07c38c

def z650 : W := mkw 0x2008504148615157 0x0802141052185455 0xde1a70000863f1fe 0x37869c000218fc7f

def z651 : W := mkw 0x810800500ad43d80 0x6042001402b50f60 0x6e0401300ffc3fc2 0xdb81004c03ff0ff0

def z652 : W := mkw 0x2008504148615157 0x0802141052185455 0x9e0202080863f1ff 0x678080820218fc7f

def z653 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x21e58ffff0000001 0xc87963fffc000000

def z654 : W := mkw 0x1000c412142f06a2 0x84003104850bc1a8 0xe805cd36347f0e02 0x3a01734d8d1fc380

def z655 : W := mkw 0x2000004140001154 0x0800001050000455 0xdd1a72c9c00031fd 0xf7469cb270000c7f

def z656 : W := mkw 0x0043800005028000 0x0010e0000140a000 0x800380000003c000 0x2000e0000000f000

def z657 : W := mkw 0x10000013100406f0 0x04000004c40101bc 0xec05cd3730000ff1 0xfb01734dcc0003fc

def z658 : W := mkw 0x02f7afaca71a8000 0x80bdebeb29c6a000 0xf9fffffff79c0001 0xfe7ffffffde70000

def z659 : W := mkw 0x81b403a002902800 0x606d00e800a40a00 0x00e0000003800000 0x0038000000e00000

def z660 : W := mkw 0x42ffff0e0ffbea2b 0xd0bfffc383fefa8a 0xfafffd060fffce02 0x3ebfff4183fff380

def z661 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0xed1dfdf7f47f0ff3 0xfb477f7dfd1fc3fc

def z662 : W := mkw 0x204b784de8615157 0x0812de137a185455 0xdf1bfecff863f1ff 0xf7c6ffb3fe18fc7f

def z663 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x3fe003f00f803fc2 0xcff800fc03e00ff0

def z664 : W := mkw 0x5020c71f14af2efa 0xd40831c7c52bcbbe 0xec05cf3f347f3fff 0xfb0173cfcd1fcfff

def z665 : W := mkw 0x0043280000000000 0x0010ca0000000000 0x8003fc0000000000 0x2000ff0000000000

def z666 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec05cc00047f0ff2 0x3b017300011fc3fc

def z667 : W := mkw 0x0008100008404001 0x0002040002101000 0x121a30000800c000 0x04868c0002003000

def z668 : W := mkw 0x2008504148615157 0x0802141052185455 0xdb1a70c1c863c1c2 0xb6c69c307218f070

def z669 : W := mkw 0x02ffffa00f7bc003 0x80bfffe803def000 0xfbfffff00fffc002 0xfefffffc03fff000

def z670 : W := mkw 0x0043800005028000 0x0010e0000140a000 0x20e1800007800000 0x0838600001e00000

def z671 : W := mkw 0x0000400100210052 0x0000100040084014 0xde0242090863f1ff 0xf78090824218fc7f

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x800200080003c03d 0x200080020000f00f

def z673 : W := mkw 0x00f703ac00000000 0x003dc0eb00000000 0xf9ff83fe00000001 0xfe7fe0ff80000000

def z674 : W := mkw 0x812803f00ad43d80 0x604a00fc02b50f60 0x070003f00ffc3fc2 0xc1c000fc03ff0ff0

def z675 : W := mkw 0x0020030c00000000 0x000800c300000000 0x0000030e00000001 0x400000c380000000

def z676 : W := mkw 0x2208d4414f7bd157 0x8882351053def455 0xdf1a72c9cffff1ff 0xf7c69cb273fffc7f

def z677 : W := mkw 0x0000800204020220 0x0000200081008088 0x0400000004030e32 0x010000000100c38c

def z678 : W := mkw 0x5063831f1586aef8 0x5418e0c7c561abbe 0xbee3833f3f83ffff 0xefb8e0cfcfe0ffff

def z679 : W := mkw 0x2008504148615157 0x0802141052185455 0x451872c9c06031fd 0xd1461cb270180c7f

def z680 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xb9fbb3cec0000001 0x6e7eecf3b0000000

def z681 : W := mkw 0x0008404108611152 0x0002101042184454 0xdf1842c1086331f3 0xf7c610b04218cc7c

def z682 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0xac058d36341f0e33 0x6b01634d8d07c38c

def z683 : W := mkw 0x1020c71314af2ef2 0xc40831c4c52bcbbc 0xfee5cf373fff3ff3 0xffb973cdcfffcffc

def z684 : W := mkw 0x0243fc0ca52bc003 0x8090ff03294af000 0x8003fc0ff003c001 0x2000ff03fc00f000

def z685 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0xe805cd37341c0e01 0xfa01734dcd070380

def z686 : W := mkw 0x004bd0000d63c003 0x0012f4000358f000 0xfafbf0000fe3c002 0x3ebefc0003f8f000

def z687 : W := mkw 0x00004011002504d2 0x0000100440094134 0xec044131047f0ff3 0xfb01104c411fc3fc

def z688 : W := mkw 0x00b403a000000000 0x002d00e800000000 0x20e4013000000000 0x0839004c00000000

def z689 : W := mkw 0x2008104048405105 0x0802041012101441 0x011830c0c0000000 0x00460c3030000000

def z690 : W := mkw 0xc1bc83f20fd6bfa8 0x706f20fc83f5afea 0x7ffc03f00ffffffe 0xdfff00fc03ffffff

def z691 : W := mkw 0x83ff3bf00bd4fd81 0x60ffcefc02f53f60 0x7ffe33f00ffcffc2 0xdfff8cfc03ff3ff0

def z692 : W := mkw 0x3000c453542f17f6 0x8c003114d50bc5fd 0xed05cffff47f3fff 0xfb4173fffd1fcfff

def z693 : W := mkw 0x81ff2becaad03900 0x607fcafb2ab40e40 0xfbfffffffb803001 0xfefffffffee00c00

def z694 : W := mkw 0x024bfc000d6bc003 0x8092ff00035af000 0xda1bfc000863c002 0x3686ff000218f000

def z695 : W := mkw 0xc16383fe0586bfa8 0x7058e0ff8161afea 0xbfe383fe0f83ffff 0xeff8e0ff83e0ffff

def z696 : W := mkw 0x12d7ec13173f86f2 0x84b5fb04c5cfe1bc 0xece5cd3737ff0ff3 0xfb39734dcdffc3fc

def z697 : W := mkw 0x3000d403542b4277 0x8c003500d50ad09d 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z698 : W := mkw 0x1000000310000270 0x04000000c400009c 0x0000000730000031 0x00000001cc00000c

def z699 : W := mkw 0x00002800a0000000 0x00000a0028000000 0x00007c01f0000000 0x00001f007c000000

def z700 : W := mkw 0x10f7efafb42b0272 0x843dfbebed0ac09c 0xf9fffffff0030031 0xfe7ffffffc00c00c

def z701 : W := mkw 0x0000400000210002 0x0000100000084000 0xc800400000630002 0x320010000018c000

def z702 : W := mkw 0x02ffffacaf7bc003 0x80bfffeb2bdef000 0xfafffd363fffc002 0x3ebfff4d8ffff000

def z703 : W := mkw 0x4208d4020ffbea2b 0xd082350083fefa8a 0x060000000ffffe3e 0x0180000003ffff8f

def z704 : W := mkw 0x10000013100406f0 0x04000004c40101bc 0x0400000000000ff0 0x01000000000003fc

def z705 : W := mkw 0x2008504148615157 0x0802141052185455 0x931a72c9c803f03d 0x24c69cb27200fc0f

def z706 : W := mkw 0x02ffff000ffbe803 0xc0bfffc003fefa00 0xfeffff000ffffe02 0x7fbfffc003ffff80

def z707 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x5d1803f000003fc0 0xd74600fc00000ff0

def z708 : W := mkw 0x02dffc00af7bc003 0x80b7ff002bdef000 0xfafffc01ffffc002 0x3ebfff007ffff000

def z709 : W := mkw 0x00df28000a500000 0x0037ca0002940000 0x7afe30000ffc0002 0x1ebf8c0003ff0000

def z710 : W := mkw 0x004b80000f528000 0x0012e00003d4a000 0xbae380000fffc002 0x2eb8e00003fff000

def z711 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x72fffc000ffcc000 0x1cbfff0003ff3000

def z712 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee3cf0f3f83fe3f 0x6fb8f3c3cfe0ff8f

def z713 : W := mkw 0x5043c40f152b827a 0x9410f103c54ae09e 0x8003800e0003c03d 0x2000e0038000f00f

def z714 : W := mkw 0xa12003fde0843dd4 0x684800ff78210f75 0x050003fff0003ffd 0xc14000fffc000fff

def z715 : W := mkw 0x81bc03fcaad43d80 0x606f00ff2ab50f60 0x7ffc03f63ffc3fc2 0xdfff00fd8fff0ff0

def z716 : W := mkw 0x00438400050a8000 0x8010e1000142a000 0x20e58c00079c0000 0x0839630001e70000

def z717 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7efc01000ffc0e02 0x5fbf004003ff0380

def z718 : W := mkw 0x00dfd0000f73c003 0x0037f40003dcf000 0xfafff0000fffc002 0x3ebffc0003fff000

def z719 : W := mkw 0x00df28000a500000 0x0037ca0002940000 0x7afd8c000ffc0002 0x1ebf630003ff0000

def z720 : W := mkw 0x81bc2bf0aad43d80 0x606f0afc2ab50f60 0xfffdfff7fffc3fc3 0xffff7ffdffff0ff0

def z721 : W := mkw 0x00d7280002100000 0x0035ca0000840000 0xf8fffc00079c0000 0x3e3fff0001e70000

def z722 : W := mkw 0x81bc2bf0aad43d80 0x606f0afc2ab50f60 0xfffe7ff9fffc3fc3 0xffff9ffe7fff0ff0

def z723 : W := mkw 0x81632bfca0843d80 0x6058caff28210f60 0x8503fffff0003fc1 0xe140fffffc000ff0

def z724 : W := mkw 0x00d7800007128000 0x0035e00001c4a000 0x20e58000079c0000 0x0839600001e70000

def z725 : W := mkw 0x814b285caad43d80 0x6052ca172ab50f60 0x8603fc0ffffc3fc3 0x2180ff03ffff0ff0

def z726 : W := mkw 0x024bd4000f7bc003 0x8092f50003def000 0x12e200000fffc002 0x04b8800003fff000

def z727 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x6ee401300ffc3fc2 0xdbb9004c03ff0ff0

def z728 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc03f00ffffffe 0xdfff00fc03ffffff

def z729 : W := mkw 0x1043c403152b8272 0x8410f100c54ae09c 0x8003cc073003c031 0x2000f301cc00f00c

def z730 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x60e4013007fc0fc0 0x9839004c01ff03f0

def z731 : W := mkw 0x0000400100210052 0x0000100040084014 0xdf1a72c9c863f1ff 0xf7c69cb27218fc7f

def z732 : W := mkw 0x812003fca0843d80 0x604800ff28210f60 0x050003f8c0003fc0 0xc14000fe30000ff0

def z733 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc09cfffc003 0x3ebfff0273fff000

def z734 : W := mkw 0x2008104148405155 0x0802041052101455 0x9f1a32c9c803f1ff 0xe7c68cb27200fc7f

def z735 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec05cf3f347f3fff 0xfb0173cfcd1fcfff

def z736 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x4d0003f000603fc2 0xd34000fc00180ff0

def z737 : W := mkw 0x10f7efbfb42f06f2 0x843dfbefed0bc1bc 0x15fa32c8c47f0ff2 0x057e8cb2311fc3fc

def z738 : W := mkw 0x1200d413152fc6f3 0x84803504c54bf1bc 0xec05cd37347fcff3 0xfb01734dcd1ff3fc

def z739 : W := mkw 0x81bc2bf00ad43d80 0x606f0afc02b50f60 0x7ffc7ff00ffc3fc2 0xdfff1ffc03ff0ff0

def z740 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xb8e78c00079c0000 0x2e39e30001e70000

def z741 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0x22e58c000ffc0002 0x08b9630003ff0000

def z742 : W := mkw 0x10008413140e06f0 0x84002104c50381bc 0x6c058d37347c0ff3 0xdb01634dcd1f03fc

def z743 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfdfffffff000303d 0xff7ffffffc000c0f

def z744 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffec1cffff1c2 0xffffffb073fffc70

def z745 : W := mkw 0x81bc2bf0aad43d80 0x606f0afc2ab50f60 0x7ffc0ff03ffc3fc2 0xdfff03fc0fff0ff0

def z746 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0xc11dfcf7f0000001 0xb0477f3dfc000000

def z747 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffcc1cffff1fe 0xbfffff3073fffc7f

def z748 : W := mkw 0x81bc2bfcaad43d80 0x606f0aff2ab50f60 0x7ffc7ffffffc3fc3 0xdfff1fffffff0ff0

def z749 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfdfffffff4000e03 0xff7ffffffd000380

def z750 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xfafffc000f9fc002 0x3ebfff0003e7f000

def z751 : W := mkw 0x209c50014a714057 0x08271400529c5015 0xfafe7009cfffc03f 0x3ebf9c0273fff00f

def z752 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x6d0403f000003fc0 0xdb4100fc00000ff0

def z753 : W := mkw 0xd12003ff10843ff8 0x744800ffc4210ffe 0x050003ff30003ffd 0xc14000ffcc000fff

def z754 : W := mkw 0xb12003f350843ff4 0x6c4800fcd4210ffd 0x050003fff0003ffd 0xc14000fffc000fff

def z755 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0x60fc7c0007fc0000 0x183f1f0001ff0000

def z756 : W := mkw 0x10438013150686f0 0x0410e004c541a1bc 0xbee381373f83cff3 0xefb8e04dcfe0f3fc

def z757 : W := mkw 0x22d7ac41471a9154 0x88b5eb1051c6a455 0x25e58ec9c79c31fd 0xc97963b271e70c7f

def z758 : W := mkw 0x00f72baca0802800 0x403dcaeb28200a00 0xfdfffffff0003e01 0xff7ffffffc000f80

def z759 : W := mkw 0x8120035000843d80 0x604800d400210f60 0x0400030000003fc0 0x410000c000000ff0

def z760 : W := mkw 0x8363fff005affd83 0xe0d8fffc016bff60 0x8503fff00003ffc0 0xe140fffc0000fff0

def z761 : W := mkw 0x00bc03100ad42c80 0x402f00c402b50b20 0x7efc03300ffc3fc2 0xdfbf00cc03ff0ff0

def z762 : W := mkw 0x002003aca0000000 0x000800eb28000000 0xf91ffffff0000001 0xfe47fffffc000000

def z763 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee7830e0ffffe3f 0x7fb9e0c383ffff8f

def z764 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0x7affbc000ffcc002 0x1ebfef0003ff3000

def z765 : W := mkw 0x81f72baca2902800 0x607dcaeb28a40a00 0xf9fffffff3800001 0xfe7ffffffce00000

def z766 : W := mkw 0xa19c50f14a7555d7 0x2867143c529d5575 0x411c00f0007c01c0 0x9047003c001f0070

def z767 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee3830e0fe3ffff 0xffb8e0c383f8ffff

def z768 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0xed05cff730003fc1 0xfb4173fdcc000ff0

def z769 : W := mkw 0x02dffc0caf7bc003 0x80b7ff032bdef000 0xfafffc08cfffc002 0x3ebfff0233fff000

def z770 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0xfafffc000ffcc002 0x3ebfff0003ff3000

def z771 : W := mkw 0x912003b210842ea0 0x644800ec84210ba8 0x0000013630000e00 0x0000004d8c000380

def z772 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xbae78c000fffc002 0x2eb9e30003fff000

def z773 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0x17fa32c8cffff1fe 0x05fe8cb233fffc7f

def z774 : W := mkw 0x02f72baca3108000 0x00bdcaeb28c42000 0xf9fffffff3800001 0xfe7ffffffce00000

def z775 : W := mkw 0x006383000582a800 0x4018e0c00160aa00 0xbee383080f83fe3f 0x6fb8e0c203e0ff8f

def z776 : W := mkw 0x00df80000f528000 0x0037e00003d4a000 0x7afd80000ffc0002 0x1ebf600003ff0000

def z777 : W := mkw 0x5063870e158aaa28 0xd418e1c38562aa8a 0xbee38f0e3f83fe3f 0x6fb8e3c38fe0ff8f

def z778 : W := mkw 0xa12003f140843dd4 0x684800fc50210f75 0x050003f1c0003fc0 0xc14000fc70000ff0

def z779 : W := mkw 0x4063ab0e0582aa28 0x5018eac38160aa8a 0xbee3ff0e0f83fe3f 0x6fb8ffc383e0ff8f

def z780 : W := mkw 0x6243fc0f452bc27f 0x9890ff03d14af09f 0x8003fc0fc003c03d 0x2000ff03f000f00f

def z781 : W := mkw 0x029cfc000f7bc003 0x80a73f0003def000 0x7afc7c000fffc002 0x1ebf1f0003fff000

def z782 : W := mkw 0x42bc7f0e0af96a2b 0xd0af1fc382be5a8a 0x441c7f0e007c3e3d 0x51071fc3801f0f8f

def z783 : W := mkw 0xa12853f148e57dd7 0x684a14fc52395f75 0x070003f00863fffe 0xc1c000fc0218ffff

def z784 : W := mkw 0x009c00500a541580 0x0027001402950560 0x7ffc03f00ffc3fc2 0xdfff00fc03ff0ff0

def z785 : W := mkw 0x1243ec03152b8272 0x8490fb00c54ae09c 0x8001cc0730030031 0x20007301cc00c00c

def z786 : W := mkw 0x3000d413542f46f7 0x8c003504d50bd1bd 0xec05fd37f47f0ff3 0xfb017f4dfd1fc3fc

def z787 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xe805cd37347c0fc1 0xfa01734dcd1f03f0

def z788 : W := mkw 0x812043f100a53dd2 0x604810fc40294f74 0xcd0043f100633ff3 0xf34010fc4018cffc

def z789 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0x32fe30000f9cc000 0x0cbf8c0003e73000

def z790 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x96e3830e0b83fe3d 0x65b8e0c382e0ff8f

def z791 : W := mkw 0x4063870e058aaa28 0xd018e1c38162aa8a 0xbee78f0e0f9ffe3f 0x6fb9e3c383e7ff8f

def z792 : W := mkw 0x819c00e00a501100 0x2067003802940440 0x7bfc00c00ffc0002 0x1eff003003ff0000

def z793 : W := mkw 0x81bc03fcaad43d80 0x606f00ff2ab50f60 0xfffe73fffffc3fc3 0xffff9cffffff0ff0

def z794 : W := mkw 0x02d7ac02071a8220 0x80b5eb0081c6a088 0x20e58d06079c0e00 0x0839634181e70380

def z795 : W := mkw 0x91bcc7e31efb3b72 0xe46f31f8c7becedc 0x93f9cec73b833031 0x24fe73b1cee0cc0c

def z796 : W := mkw 0x42d7ac0e071a8228 0x90b5eb0381c6a08a 0x20e58c06079c0000 0x0839630181e70000

def z797 : W := mkw 0x02dffca0af7bc003 0x80b7ff282bdef000 0xfbfffdf7ffffc003 0xfeffff7dfffff000

def z798 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc4ff13ffc3fc2 0xdfff13fc4fff0ff0

def z799 : W := mkw 0x02d7bc00071ac001 0x80b5ef0001c6b000 0x20e7bc00079cc000 0x0839ef0001e73000

def z800 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfbfffcc1cfffc002 0xbeffff3073fff000

def z801 : W := mkw 0x4094a8a2a582aa28 0x50252a28a960aa8a 0x471c7cf1ff83fe3e 0x91c71f3c7fe0ff8f

def z802 : W := mkw 0x009c50000a714003 0x00271400029c5000 0x7afc00000fffc002 0x1ebf000003fff000

def z803 : W := mkw 0x00f72baca2100000 0x003dcaeb28840000 0xf9fffffff79c0001 0xfe7ffffffde70000

def z804 : W := mkw 0x1243fc03152bc273 0x8490ff00c54af09c 0x8003fc000003c030 0x2000ff000000f00c

def z805 : W := mkw 0x22dffc434f7bd377 0x88b7ff10d3def4dd 0xffffffcfcfffffff 0xfffffff3f3ffffff

def z806 : W := mkw 0x81bc03f0aad43d80 0x606f00fc2ab50f60 0x7ffc03f1fffc3fc2 0xdfff00fc7fff0ff0

def z807 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffd300fffc002 0xfebfff4c03fff000

def z808 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xb1fffffff0000001 0x2c7ffffffc000000

def z809 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee3c30f0f83fe3f 0xffb8f0c3c3e0ff8f

def z810 : W := mkw 0x812003f0a0843d80 0x604800fc28210f60 0x050003f1f0003fc0 0xc14000fc7c000ff0

def z811 : W := mkw 0x2008504148615157 0x0802141052185455 0x171a32c9c863f1ff 0xc5c68cb27218fc7f

def z812 : W := mkw 0x812803f00ad43d80 0x604a00fc02b50f60 0x3fe003f00ffc3fc2 0xcff800fc03ff0ff0

def z813 : W := mkw 0x400080020582aa28 0x500020008160aa8a 0x3ee000000f83fe3e 0x0fb8000003e0ff8f

def z814 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffffffffff1ff 0xfffffffffffffc7f

def z815 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x7afe30000fffc002 0x1ebf8c0003fff000

def z816 : W := mkw 0x0043800005028000 0x0010e0000140a000 0xfae780000fffc002 0x3eb9e00003fff000

def z817 : W := mkw 0x10004413102d06f2 0x84001104c40b41bc 0xec05cd37307c0ff1 0xfb01734dcc1f03fc

def z818 : W := mkw 0x4063abaea582aa28 0x5018eaeba960aa8a 0xbfe3ffffff83fe3f 0xeff8ffffffe0ff8f

def z819 : W := mkw 0x12dffc011f7bc053 0x84b7ff0047def014 0xfafffc013fffc002 0x3ebfff004ffff000

def z820 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x79fdfff7f0000000 0xde7f7ffdfc000000

def z821 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x010002f0000031c0 0x804000bc00000c70

def z822 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xe8fdfc0007ff0002 0x3a3f7f0001ffc000

def z823 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbffbb3cecf83fe3f 0x6ffeecf3b3e0ff8f

def z824 : W := mkw 0x912003f210843fa0 0x644800fc84210fe8 0x050003f630003fc0 0xc14000fd8c000ff0

def z825 : W := mkw 0x00dfec000e7b0002 0x8037fb00039ec000 0xfafffc000fff0002 0x3ebfff0003ffc000

def z826 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffffffffffc3fc3 0xffffffffffff0ff0

def z827 : W := mkw 0x300894525c4e57a5 0x8c022514971395e9 0x331fbffefc1cfe0c 0x0cc7efffbf073f83

def z828 : W := mkw 0xc12003fc00843d88 0x704800ff00210f62 0x050003f800003fcc 0xc14000fe00000ff3

def z829 : W := mkw 0x00008012040606a0 0x00002004810181a8 0xec05cd37347f0ff3 0xfb01734dcd1fc3fc

def z830 : W := mkw 0xa12003f040843d84 0x684800fc10210f61 0x050003f8c0003fcc 0xc14000fe30000ff3

def z831 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0x22e58c000f9cc000 0x08b9630003e73000

def z832 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee382080f83fe3e 0x2fb8e08203e0ff8f

def z833 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xa6e3810e0f83fe3f 0x29b8e04383e0ff8f

def z834 : W := mkw 0x000800000a500000 0x0002000002940000 0x3ae000000ffc0002 0x0eb8000003ff0000

def z835 : W := mkw 0x819c00500ad43d80 0x6067001402b50f60 0x26e400000ffc3fc2 0x09b9000003ff0ff0

def z836 : W := mkw 0x009c50000a714003 0x00271400029c5000 0x7afc70000ffc0002 0x1ebf1c0003ff0000

def z837 : W := mkw 0x81bc13f00ad47d81 0x606f04fc02b51f60 0x7ffe33f00ffcffc2 0xdfff8cfc03ff3ff0

def z838 : W := mkw 0x02dffc0caf7bc003 0x80b7ff032bdef000 0xfafffd3fffffc003 0xfebfff4ffffff000

def z839 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xe8e5cc00079c0000 0x3a39730001e70000

def z840 : W := mkw 0x209c10404a505105 0x0827041012941441 0x7bfe32c8cffcf00e 0x1eff8cb233ff3c03

def z841 : W := mkw 0x0020031000842c80 0x400800c400210b20 0x0400033000003fc0 0xc10000cc00000ff0

def z842 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x96e3820e0f83fe3f 0x25b8e08383e0ff8f

def z843 : W := mkw 0x812003bca0842c80 0x604800ef28210b20 0x010003fff0000e01 0xc04000fffc000380

def z844 : W := mkw 0xa1b453b142b56cd7 0x686d14ec50ad5b35 0xa0e67139c79fce3d 0x28399c4e71e7f38f

def z845 : W := mkw 0x200850414a715157 0x08021410529c5455 0xdf1a72c9cffff1ff 0xf7c69cb273fffc7f

def z846 : W := mkw 0x0094000002100000 0x0025000000840000 0x68e4000007fc0002 0x1a39000001ff0000

def z847 : W := mkw 0x40f72baca180a808 0x503dcaeb28602a02 0xf9fffffff3800001 0xfe7ffffffce00000

def z848 : W := mkw 0x406383ae0582aa28 0x5018e0eb8160aa8a 0xbfe383fe0f83fe3f 0xeff8e0ff83e0ff8f

def z849 : W := mkw 0x0094001002140480 0x0025000400850120 0x6ce4013007fc0fc2 0xdb39004c01ff03f0

def z850 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x06e000000f83fe3e 0x01b8000003e0ff8f

def z851 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0x40fc7c0003fc0000 0x103f1f0000ff0000

def z852 : W := mkw 0x0020031000842c80 0x400800c400210b20 0x6ce4013007fc0fc2 0xdb39004c01ff03f0

def z853 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x26e1830e0f83fe3f 0x49b860c383e0ff8f

def z854 : W := mkw 0x4063830ea582aa28 0x5018e0c3a960aa8a 0xbee3830fff83fe3f 0x6fb8e0c3ffe0ff8f

def z855 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xf9fffec9c79c0001 0xfe7fffb271e70000

def z856 : W := mkw 0x812003fca0843d80 0x604800ff28210f60 0x050003f630003fc0 0xc14000fd8c000ff0

def z857 : W := mkw 0x12df38131b54c6f1 0x04b7ce04c6d531bc 0x16fa31373b80cff1 0xc5be8c4dcee033fc

def z858 : W := mkw 0x1000d413142f46f3 0x84003504c50bd1bc 0xec07fd37347fcff3 0xfb01ff4dcd1ff3fc

def z859 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfbfffffff803c003 0xfefffffffe00f000

def z860 : W := mkw 0x32dffc435f7bd377 0x8cb7ff10d7def4dd 0xfffffecffffff1ff 0xffffffb3fffffc7f

def z861 : W := mkw 0x2008504148615157 0x0802141052185455 0xfffa72c9cfe3f1ff 0xfffe9cb273f8fc7f

def z862 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xb2fffc000f9fc000 0x2cbfff0003e7f000

def z863 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffc000fffc033 0x7fbfff0003fff00c

def z864 : W := mkw 0x029cd4000f7bc003 0x80a7350003def000 0x12f800000fffc002 0x04be000003fff000

def z865 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6405cd37347f0ff2 0x9901734dcd1fc3fc

def z866 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1e72c9cc7ff1ff 0xffc79cb2731ffc7f

def z867 : W := mkw 0x5063471d11adacda 0xd418d1c7446b6b36 0x52e64e393bfcf1cc 0x94b9938e4eff3c73

def z868 : W := mkw 0x0000000000000000 0x0000000000000000 0xe91dfdf7f0000001 0xfa477f7dfc000000

def z869 : W := mkw 0x5043c40f152b827a 0x9410f103c54ae09e 0xfae7cc0f3fffc03f 0x3eb9f303cffff00f

def z870 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x010001f000000fc0 0x8040007c000003f0

def z871 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x06e000000ffc3fc2 0x01b8000003ff0ff0

def z872 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x7afdfc000ffc0002 0x1ebf7f0003ff0000

def z873 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6c058d36347f0ff2 0xdb01634d8d1fc3fc

def z874 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0xec05cd37347c0fc3 0xfb01734dcd1f03f0

def z875 : W := mkw 0x00632baca0000000 0x0018caeb28000000 0xd91bfffff0000001 0xf646fffffc000000

def z876 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x6dfc01f007fc0fc2 0xdb7f007c01ff03f0

def z877 : W := mkw 0x009c10000a504001 0x0027040002941000 0x7afe30000ffcc002 0x1ebf8c0003ff3000

def z878 : W := mkw 0x404380020582aa28 0x5010e0008160aa8a 0xbee382080f83fe3f 0x6fb8e08203e0ff8f

def z879 : W := mkw 0x1243fc0fb52bc273 0x8490ff03ed4af09c 0x8003fc0ff003c031 0x2000ff03fc00f00c

def z880 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xeae5cc000fffc002 0x3ab9730003fff000

def z881 : W := mkw 0x00f72baca0802800 0x403dcaeb28200a00 0xffffffffff83fe3f 0xffffffffffe0ff8f

def z882 : W := mkw 0x4263af0e058aaa28 0xd098ebc38162aa8a 0xbee38f0e0f83fe3f 0x6fb8e3c383e0ff8f

def z883 : W := mkw 0xc1df80fe0f5697a8 0x3077e03f83d5a5ea 0xc11f80fe007fc1fd 0xb047e03f801ff07f

def z884 : W := mkw 0x0228d7acaf7bc003 0x808a35eb2bdef000 0x030003ffffffc003 0xc0c000fffffff000

def z885 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x9f0203f80803ffff 0xe7c080fe0200ffff

def z886 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc010fffc003 0xfebfff0043fff000

def z887 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfefffc010ffff1ff 0xffbfff0043fffc7f

def z888 : W := mkw 0x4063030e0180aa28 0x5018c0c380602a8a 0x9ee2030e0b83fe3f 0x67b880c382e0ff8f

def z889 : W := mkw 0x009c00100a540480 0x0027000402950120 0x7efc00000ffc0fc2 0x1fbf000003ff03f0

def z890 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0x20e58c0007ff0002 0x0839630001ffc000

def z891 : W := mkw 0x3008544158695157 0x8c021510561a5455 0xdf1a7ec9f863f1ff 0xf7c69fb27e18fc7f

def z892 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x91fbfffff0000001 0xe47efffffc000000

def z893 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7afc01300ffc0002 0xdebf004c03ff0000

def z894 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x5ff802c00ffc3fc2 0xd7fe00b003ff0ff0

def z895 : W := mkw 0x812003fc00843d80 0x604800ff00210f60 0x050003fe00003fc1 0xc14000ff80000ff0

def z896 : W := mkw 0x009c28a0aa500000 0x00270a282a940000 0x7bfc7cf1fffc0002 0x9eff1f3c7fff0000

def z897 : W := mkw 0x2008504148615157 0x0802141052185455 0x971a72c9c803f1fd 0xe5c69cb27200fc7f

def z898 : W := mkw 0x404380020582aa28 0x5010e0008160aa8a 0x26e180000f83fe3e 0x09b8600003e0ff8f

def z899 : W := mkw 0x812003bca0842c80 0x604800ef28210b20 0x0000013630000e00 0x0000004d8c000380

def z900 : W := mkw 0x9120c7f314af3ff2 0xe44831fcc52bcffc 0x8501cff730033ff1 0xe14073fdcc00cffc

def z901 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfafffc010fffc033 0x3ebfff0043fff00c

def z902 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfbfffec9cffff1ce 0xbeffffb273fffc73

def z903 : W := mkw 0x0043280ca0000000 0x0010ca0328000000 0xf91ffffff0000001 0xfe47fffffc000000

def z904 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7efc01300ffc3fc2 0x1fbf004c03ff0ff0

def z905 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffd000fffce02 0x7fbfff4003fff380

def z906 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfefe02080ffff03f 0x7fbf808203fffc0f

def z907 : W := mkw 0x3243fc03552bc277 0x8c90ff00d54af09d 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z908 : W := mkw 0x819c00f00a541580 0x2067003c02950560 0x7ffc01f00ffc0fc2 0xdfff007c03ff03f0

def z909 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0x611dfdf7f0000000 0x98477f7dfc000000

def z910 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0x20e5fc00079c0000 0x08397f0001e70000

def z911 : W := mkw 0x812803500ad43d80 0x604a00d402b50f60 0x7ff803c00ffc3fc2 0xdffe00f003ff0ff0

def z912 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7bfc02c00ffc0002 0xdeff00b003ff0000

def z913 : W := mkw 0x81ff2becaad03900 0x607fcafb2ab40e40 0x13f802c00b803000 0x04fe00b002e00c00

def z914 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x78fd8c00079c0000 0x1e3f630001e70000

def z915 : W := mkw 0x12dffc031f7bc273 0x84b7ff00c7def09c 0xfefffc073fffc1f3 0xffbfff01cffff07c

def z916 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0xbaffbc000f9fc002 0x2ebfef0003e7f000

def z917 : W := mkw 0x22df7c414b79d157 0x88b7df1052de7455 0xdffe7ec9cbfff1ff 0xf7ff9fb272fffc7f

def z918 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x7ee403300ffc3fc2 0xdfb900cc03ff0ff0

def z919 : W := mkw 0x02dffca0af7bc003 0x80b7ff282bdef000 0xfbfffcc0cfffc002 0x3effff3033fff000

def z920 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfffffec80ffff1ff 0xffffffb203fffc7f

def z921 : W := mkw 0x0008004008401100 0x0002001002100440 0xdf1a72c9c863f1ff 0xf7c69cb27218fc7f

def z922 : W := mkw 0x229cd4414f7bd157 0x88a7351053def455 0xfffe72c9cffff1ff 0xffff9cb273fffc7f

def z923 : W := mkw 0x229c7c414a795157 0x88a71f10529e5455 0xfffe7ec9cffff1ff 0xffff9fb273fffc7f

def z924 : W := mkw 0x4063ab0ea582aa28 0x5018eac3a960aa8a 0xbee3b30ecf83fe3f 0x6fb8ecc3b3e0ff8f

def z925 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0x60fd8c0007fc0000 0x183f630001ff0000

def z926 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffd83f60ffc3fc3 0xffff60fd83ff0ff0

def z927 : W := mkw 0x02df78000b71c003 0x00b7de0002dc7000 0xfafe70000fffc002 0x3ebf9c0003fff000

def z928 : W := mkw 0x3008d4535c6f57f7 0x8c023514d71bd5fd 0x04000000047f0ff2 0x01000000011fc3fc

def z929 : W := mkw 0x5020031f10842ef8 0x540800c7c4210bbe 0x0400013730000ff1 0xc100004dcc0003fc

def z930 : W := mkw 0x606bd34f4de3fb7f 0x581af4d3d378fedf 0x61f9f1c7c7e00fc0 0x987e7c71f1f803f0

def z931 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe03f80ffc3fc3 0xffff80fe03ff0ff0

def z932 : W := mkw 0x812003f100843dd0 0x604800fc40210f74 0x050003f100003ff1 0xc14000fc40000ffc

def z933 : W := mkw 0x42dffc0c0f7bc00b 0x90b7ff0303def002 0xfafffc080fffc00e 0x3ebfff0203fff003

def z934 : W := mkw 0x52dffc0f1f7bc27b 0x94b7ff03c7def09e 0xfafffc0f3fffc03f 0x3ebfff03cffff00f

def z935 : W := mkw 0x00df00000b508000 0x0037c00002d42000 0x7afe00000ffcc002 0x1ebf800003ff3000

def z936 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xd1fffefff0000001 0xb47fffbffc000000

def z937 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfbfffec00ffff002 0x3effffb003fffc00

def z938 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfe05cf373c7f3ff3 0xff8173cdcf1fcffc

def z939 : W := mkw 0x00f72baca0802800 0x403dcaeb28200a00 0xf9fffffff7800e01 0xfe7ffffffde00380

def z940 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc313fffc002 0xbebfff0c4ffff000

def z941 : W := mkw 0x224bd4414f7bd157 0x8892f51053def455 0xbee382080ffff1ff 0x6fb8e08203fffc7f

def z942 : W := mkw 0x02df3c000b58c001 0x80b7cf0002d63000 0x12fe3c000b9cc000 0x04bf8f0002e73000

def z943 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0xe8e7fc0007ffc002 0x3a39ff0001fff000

def z944 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xff1ffffffc7fffff 0xffc7ffffff1fffff

def z945 : W := mkw 0x009c40000a710002 0x00271000029c4000 0xfafc40000fff0002 0x3ebf100003ffc000

def z946 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x7afd8c000fffc002 0x1ebf630003fff000

def z947 : W := mkw 0x4020830e0582aa28 0x500820c38160aa8a 0x3ee0030e0f83fe3f 0x4fb800c383e0ff8f

def z948 : W := mkw 0x20dfd0414f73d157 0x0837f41053dcf455 0xfffff2c9cffff1ff 0xfffffcb273fffc7f

def z949 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffd363fffc002 0x3ebfff4d8ffff000

def z950 : W := mkw 0x22dffce1ef7bd157 0x88b7ff387bdef455 0xfbfffcf1ffffc1c2 0xbeffff3c7ffff070

def z951 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x79fc03f007fc0fc0 0xde7f00fc01ff03f0

def z952 : W := mkw 0x20df78414a715157 0x0837de10529c5455 0xfffffec9cffff1ff 0xffffffb273fffc7f

def z953 : W := mkw 0x02d7ac02071a8220 0x80b5eb0081c6a088 0xace58d06079f0e33 0x6b39634181e7c38c

def z954 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffe33f8cffc3fc2 0xdfff8cfe33ff0ff0

def z955 : W := mkw 0x02dffca0af7bc003 0x80b7ff282bdef000 0xfafffc303fffc002 0x3ebfff0c0ffff000

def z956 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfffffec9cffff1c3 0xffffffb273fffc70

def z957 : W := mkw 0x0000000000000000 0x0000000000000000 0x7ae400000ffc0002 0x1eb9000003ff0000

def z958 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xc11ffffff0000001 0xf047fffffc000000

def z959 : W := mkw 0x83ff3becabd0f901 0x60ffcefb2af43e40 0x13fa32c8cb80f000 0x04fe8cb232e03c00

def z960 : W := mkw 0xa12853f148e57dd7 0x684a14fc52395f75 0x451873f1c0603fc0 0xd1461cfc70180ff0

def z961 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfefffc000fffc1f2 0x3fbfff0003fff07c

def z962 : W := mkw 0x00dfc4000f7b8002 0x8037f10003dee000 0xfaffcc000fffc002 0x3ebff30003fff000

def z963 : W := mkw 0x009c40010a710052 0x00271000429c4014 0xfefc40010fff01f3 0xffbf100043ffc07c

def z964 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xbafbb0000fffc002 0x2ebeec0003fff000

def z965 : W := mkw 0x009c28000a500000 0x00270a0002940000 0x7afc7c000ffc0002 0x1ebf1f0003ff0000

def z966 : W := mkw 0x81bc03fc0ad43d80 0x606f00ff02b50f60 0x7ffc03fe0ffc3fc3 0xdfff00ff83ff0ff0

def z967 : W := mkw 0x0043800205028220 0x0010e0008140a088 0xbee3830e0f83fe3f 0x6fb8e0c383e0ff8f

def z968 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfbffffffff800003 0xfeffffffffe00000

def z969 : W := mkw 0x40f72baca180a808 0x503dcaeb28602a02 0xffffffffff80fe0f 0xffffffffffe03f83

def z970 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec07fd3ff47f0ff3 0xfb01ff4ffd1fc3fc

def z971 : W := mkw 0x20ff7bede8615157 0x083fdefb7a185455 0x26e58d363863f1fe 0x09b9634d8e18fc7f

def z972 : W := mkw 0x22dffce1ef7bd157 0x88b7ff387bdef455 0xfffffef9fffff1ff 0xffffffbe7ffffc7f

def z973 : W := mkw 0x00df28400a501100 0x0037ca1002940440 0xfffffec9cffc31c3 0xffffffb273ff0c70

def z974 : W := mkw 0x812853f008e57d83 0x604a14fc02395f60 0xdf1a73f00863ffc2 0xf7c69cfc0218fff0

def z975 : W := mkw 0x0094c400063b0002 0x80253100018ec000 0xe8e5cc0007ff0002 0x3a39730001ffc000

def z976 : W := mkw 0x0094000002100000 0x0025000000840000 0x78fc0000079c0000 0x1e3f000001e70000

def z977 : W := mkw 0x024bfc000f7bc003 0x8092ff0003def000 0xbae3fc000fffc002 0x2eb8ff0003fff000

def z978 : W := mkw 0x0000c400042b0002 0x80003100010ac000 0xfae5cc000fff0002 0x3eb9730003ffc000

def z979 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xf8fffc0007fc0000 0x3e3fff0001ff0000

def z980 : W := mkw 0x02dfac400f5a9100 0x80b7eb1003d6a440 0x7ffd8ec00ffc31c2 0xdfff63b003ff0c70

def z981 : W := mkw 0xc1f7abbea796aea8 0x707deaefa9e5abaa 0x20e58d36379c0e00 0x0839634d8de70380

def z982 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0xdafe7c000bffc002 0x36bf9f0002fff000

def z983 : W := mkw 0x00d728aca0000000 0x0035ca2b28000000 0xe91ffdfff0000001 0xfa47ff7ffc000000

def z984 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfefbf30e0f83fe3f 0x7fbefcc383e0ff8f

def z985 : W := mkw 0x0043c400052b8002 0x8010f100014ae000 0xbae380000fffc002 0x2eb8e00003fff000

def z986 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0x20e58c00079fc000 0x0839630001e7f000

def z987 : W := mkw 0x812003b000842c80 0x604800ec00210b20 0x0400013000000fc0 0xc100004c000003f0

def z988 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0xfafe7c000fffc002 0x3ebf9f0003fff000

def z989 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0x12fa30000bfcc000 0x04be8c0002ff3000

def z990 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0x12fa30000f9cc000 0x04be8c0003e73000

def z991 : W := mkw 0x406383aea582aa28 0x5018e0eba960aa8a 0xffe7cfffff83fe3f 0xfff9f3ffffe0ff8f

def z992 : W := mkw 0x7043d40f552bc27f 0x9c10f503d54af09f 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z993 : W := mkw 0x209c50414a715157 0x08271410529c5455 0x7efc00000ffff1fe 0x1fbf000003fffc7f

def z994 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x61fdfffff0000001 0xd87f7ffffc000000

def z995 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffd060fffc003 0x7ebfff4183fff000

def z996 : W := mkw 0x00bc03400ad03900 0x402f00d002b40e40 0x7ffc03c00ffc3fc2 0xdfff00f003ff0ff0

def z997 : W := mkw 0x009c00000a500000 0x0027000002940000 0x52fc00000bfc0000 0x14bf000002ff0000

def z998 : W := mkw 0x1000c412142f06a2 0x84003104850bc1a8 0xec05cd36347f0fc2 0xfb01734d8d1fc3f0

def z999 : W := mkw 0x42d7ac0e071a8228 0x90b5eb0381c6a08a 0xa0e78c0e079fc03d 0x2839e30381e7f00f

def z1000 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfbfffec9cffff00f 0xfeffffb273fffc03

def z1001 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfee5cd373fff0ff3 0xffb9734dcfffc3fc

def z1002 : W := mkw 0x62dffc4f4f7bd37f 0x98b7ff13d3def4df 0xfffffecfcffff1ff 0xffffffb3f3fffc7f

def z1003 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xffffffffff83fe3f 0xffffffffffe0ff8f

def z1004 : W := mkw 0x02438400071a8000 0x8090e10001c6a000 0x20e18000079c0000 0x0838600001e70000

def z1005 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc02c00ffc3fc2 0x1fff00b003ff0ff0

def z1006 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xe8e5cd37379c0001 0xfa39734dcde70000

def z1007 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x27e403f00ffc3fc2 0xc9f900fc03ff0ff0

def z1008 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc073fffc003 0x3ebfff01cffff000

def z1009 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7efc00000ffc01c2 0xdfbf000003ff0070

def z1010 : W := mkw 0xa12853fde8e57dd7 0x684a14ff7a395f75 0xdf1a73fff863ffff 0xf7c69cfffe18ffff

def z1011 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xc405cd37307f0ff1 0xf101734dcc1fc3fc

def z1012 : W := mkw 0x3000d413542f46f7 0x8c003504d50bd1bd 0xfd1ffffff47fcfff 0xff47fffffd1ff3ff

def z1013 : W := mkw 0x406383aea582aa28 0x5018e0eba960aa8a 0xfffbf3ffff83fe3f 0xfffefcffffe0ff8f

def z1014 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xdafa70000fffc002 0x36be9c0003fff000

def z1015 : W := mkw 0x812003b000842c80 0x604800ec00210b20 0x010003f000000e00 0xc04000fc00000380

def z1016 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfefffc09cfffc1ff 0xffbfff0273fff07f

def z1017 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfefffc000fffce32 0x3fbfff0003fff38c

def z1018 : W := mkw 0x229cd4414f7bd157 0x88a7351053def455 0x7ffc02c00ffff1fe 0xdfff00b003fffc7f

def z1019 : W := mkw 0x819c00500ad43d80 0x6067001402b50f60 0x7efc01300ffc3fc2 0xdfbf004c03ff0ff0

def z1020 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x3ff803c00ffc3fc2 0x4ffe00f003ff0ff0

def z1021 : W := mkw 0x009c00a00a500000 0x0027002802940000 0x7bfc00f00ffc0002 0x9eff003c03ff0000

def z1022 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x050003f9c0003fc1 0xc14000fe70000ff0

def z1023 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfc07cf3f347f0ff3 0xff01f3cfcd1fc3fc

def z1024 : W := mkw 0x12dffc021f7bc223 0x84b7ff0087def088 0xfafffc063fffc002 0x3ebfff018ffff000

def z1025 : W := mkw 0xa1bc13f04ad47d85 0x686f04fc12b51f61 0xfffe33f8cfffffff 0xffff8cfe33ffffff

def z1026 : W := mkw 0x2008504148615157 0x0802141052185455 0xdf1e7ef9f863f1ff 0xf7c79fbe7e18fc7f

def z1027 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0x26e58c000ffff1fe 0x09b9630003fffc7f

def z1028 : W := mkw 0x109cc4031e7b0272 0x84273100c79ec09c 0xfafdcc073fff0033 0x3ebf7301cfffc00c

def z1029 : W := mkw 0x406383020582aa28 0x5018e0c08160aa8a 0xbee383000f83fe3e 0x6fb8e0c003e0ff8f

def z1030 : W := mkw 0x4020030e00802a28 0x500800c380200a8a 0xbee2030e0f83fe3f 0x6fb880c383e0ff8f

def z1031 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x050002c000003fc0 0x014000b000000ff0

def z1032 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffc000fffc1c2 0xffbfff0003fff070

def z1033 : W := mkw 0x4063030c0180a808 0x5018c0c300602a02 0xbee203080f83fe3f 0x6fb880c203e0ff8f

def z1034 : W := mkw 0x912003f110843dd0 0x644800fc44210f74 0x050003f130003fc0 0xc14000fc4c000ff0

def z1035 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffd8ff63ffc3fc2 0xdfff63fd8fff0ff0

def z1036 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfffffec9cffff03f 0xffffffb273fffc0f

def z1037 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfefffc09cffff1ff 0x3fbfff0273fffc7f

def z1038 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee7cf0e0f83fe3f 0x7fb9f3c383e0ff8f

def z1039 : W := mkw 0x819c00500ad43d80 0x6067001402b50f60 0x7ffc02c00ffc3fc2 0xdfff00b003ff0ff0

def z1040 : W := mkw 0x5243fc0f152bc27b 0x9490ff03c54af09e 0x8003fc0f3003c03d 0x2000ff03cc00f00f

def z1041 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x9ee202080f83fe3f 0x67b8808203e0ff8f

def z1042 : W := mkw 0x406383aea582aa28 0x5018e0eba960aa8a 0xbee3833e3f83fe3f 0x6fb8e0cf8fe0ff8f

def z1043 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xe9fdfdf7f0000001 0xfa7f7f7dfc000000

def z1044 : W := mkw 0x024bd4000f7bc003 0x8092f50003def000 0x22e180000fffc002 0x08b8600003fff000

def z1045 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfffffffff8003003 0xfffffffffe000c00

def z1046 : W := mkw 0x62dffc0f4f7bc27f 0x98b7ff03d3def09f 0xfafffc0fcfffc03f 0x3ebfff03f3fff00f

def z1047 : W := mkw 0x22dffc4def7bd157 0x88b7ff137bdef455 0xfffffecffffff1ff 0xffffffb3fffffc7f

def z1048 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x050003f800003ffd 0xc14000fe00000fff

def z1049 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x57fc02f00ffc3fc2 0x95ff00bc03ff0ff0

def z1050 : W := mkw 0x0063030c00000000 0x0018c0c300000000 0xf9fffffff0000001 0xfe7ffffffc000000

def z1051 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x7dfc03f007fc0fc2 0xdf7f00fc01ff03f0

def z1052 : W := mkw 0x02dffc0caf7bc003 0x80b7ff032bdef000 0xfafffc063fffc002 0x3ebfff018ffff000

def z1053 : W := mkw 0x2008504148615157 0x0802141052185455 0xdf1a72c8c863f1fe 0x37c69cb23218fc7f

def z1054 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x20058d36347c0fc0 0x0801634d8d1f03f0

def z1055 : W := mkw 0x4043800e0582aa28 0x5010e0038160aa8a 0xbee3800e0f83fe3f 0x2fb8e00383e0ff8f

def z1056 : W := mkw 0x402083020582aa28 0x500820c08160aa8a 0x26e001000f83fe3e 0x09b8004003e0ff8f

def z1057 : W := mkw 0x00d728aca0000000 0x0035ca2b28000000 0xf9fffcfff0000001 0xbe7fff3ffc000000

def z1058 : W := mkw 0x009c00400a501100 0x0027001002940440 0x7bfc00c00ffc01c2 0x9eff003003ff0070

def z1059 : W := mkw 0x7008d4535defffff 0xdc023514d77bffff 0x060000000ffffffe 0x0180000003ffffff

def z1060 : W := mkw 0xb12853f358e57ff7 0x6c4a14fcd6395ffd 0xdf1a73fff863ffff 0xf7c69cfffe18ffff

def z1061 : W := mkw 0x029c10000b50c001 0x00a7040002d43000 0x7afc00000ffcc002 0x1ebf000003ff3000

def z1062 : W := mkw 0x402083020582aa28 0x500820c08160aa8a 0x16e002000f83fe3e 0x05b8008003e0ff8f

def z1063 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x17f803f00ffc3fc2 0xc5fe00fc03ff0ff0

def z1064 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfbfffffff800f00d 0xfefffffffe003c03

def z1065 : W := mkw 0x812803500ad43d80 0x604a00d402b50f60 0x26e001000ffc3fc2 0x09b8004003ff0ff0

def z1066 : W := mkw 0x812803500ad43d80 0x604a00d402b50f60 0x7ee403300ffc3fc2 0xdfb900cc03ff0ff0

def z1067 : W := mkw 0x02df7c000a794003 0x80b7df00029e5000 0xfafffc000ffc0002 0x3ebfff0003ff0000

def z1068 : W := mkw 0x7020035f50843ffc 0x5c0800d7d4210fff 0x050003fff0003ffd 0xc14000fffc000fff

def z1069 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xaee181060f83fe3f 0x6bb8604183e0ff8f

def z1070 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xac058d36347f0ff3 0x6b01634d8d1fc3fc

def z1071 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0xfafffc000ffc0002 0x3ebfff0003ff0000

def z1072 : W := mkw 0x00d728a0a0000000 0x0035ca2828000000 0xf9fffdf7f0000001 0xfe7fff7dfc000000

def z1073 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfafffc01cfffc002 0x3ebfff0073fff000

def z1074 : W := mkw 0x42dffc0eaf7bc22b 0x90b7ff03abdef08a 0xfafffc0fffffc03f 0x3ebfff03fffff00f

def z1075 : W := mkw 0x00d728aca0000000 0x0035ca2b28000000 0x411dfcf7f0000000 0x90477f3dfc000000

def z1076 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfafffc010fffc1c2 0xbebfff0043fff070

def z1077 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x7fe403f00ffc3fc2 0xdff900fc03ff0ff0

def z1078 : W := mkw 0x02dffc0c0f7bc003 0x80b7ff0303def000 0xfafffc0e0fffc003 0x3ebfff0383fff000

def z1079 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x22e58c000f9fc002 0x08b9630003e7f000

def z1080 : W := mkw 0x81b42bf0a0843d80 0x606d0afc28210f60 0x451c7ff1f0003fc0 0xd1471ffc7c000ff0

def z1081 : W := mkw 0x009c44000a790002 0x80271100029e4000 0x7afc4c000ffc0002 0x1ebf130003ff0000

def z1082 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee3833f3f83fe3f 0xefb8e0cfcfe0ff8f

def z1083 : W := mkw 0x009cc4000e7b0002 0x80273100039ec000 0x7afc00000fff0002 0x1ebf000003ffc000

def z1084 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffec00ffff1fe 0xffffffb003fffc7f

def z1085 : W := mkw 0x32dffc035f7bc277 0x8cb7ff00d7def09d 0xfafffc0fffffc03f 0x3ebfff03fffff00f

def z1086 : W := mkw 0x009c00000a500000 0x0027000002940000 0x22e400000ffc0002 0x08b9000003ff0000

def z1087 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0x60058d36347c0fc0 0x9801634d8d1f03f0

def z1088 : W := mkw 0x812003b000842c80 0x604800ec00210b20 0x0400033000003e00 0x410000cc00000f80

def z1089 : W := mkw 0x229c7c414a795157 0x88a71f10529e5455 0x7ffc7ec1cffc31c2 0xdfff1fb073ff0c70

def z1090 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfefffe09cffff03f 0x7fbfff8273fffc0f

def z1091 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0x71fffffff0000000 0x9c7ffffffc000000

def z1092 : W := mkw 0x209cd4414e7b5157 0x88273510539ed455 0xfffffec9cffff1ff 0xffffffb273fffc7f

def z1093 : W := mkw 0x42dffc0e0f7bc22b 0x90b7ff0383def08a 0xfafffc060fffc002 0x3ebfff0183fff000

def z1094 : W := mkw 0xc16383fe0586bfa8 0x7058e0ff8161afea 0x850383fe0003fffd 0xe140e0ff8000ffff

def z1095 : W := mkw 0x810800500ad43d80 0x6042001402b50f60 0x3ee000000ffc3fc2 0x0fb8000003ff0ff0

def z1096 : W := mkw 0x42dffc0e0f7bc22b 0x90b7ff0383def08a 0xfefffe0e0ffff03f 0x7fbfff8383fffc0f

def z1097 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xee05cd373c7fffff 0xfb81734dcf1fffff

def z1098 : W := mkw 0x2008544148695157 0x88021510521a5455 0xdf1e7ec9c87ff1ff 0xf7c79fb2721ffc7f

def z1099 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0xec058d36347f0ff3 0xfb01634d8d1fc3fc

def z1100 : W := mkw 0x404380020582aa28 0x5010e0008160aa8a 0x16e200000f83fe3e 0x05b8800003e0ff8f

def z1101 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffcc1cfffc1f3 0xffffff3073fff07c

def z1102 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x20e4013007fc0fc0 0x0839004c01ff03f0

def z1103 : W := mkw 0x009c00000a500000 0x0027000002940000 0x12f800000ffc0002 0x04be000003ff0000

def z1104 : W := mkw 0x2000004140001154 0x0800001050000455 0xdf1a72c9c803f1ff 0xf7c69cb27200fc7f

def z1105 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xe005cd37347f0ff1 0xb801734dcd1fc3fc

def z1106 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee3f30fcf83fe3f 0x6fb8fcc3f3e0ff8f

def z1107 : W := mkw 0x81b403f000843d80 0x606d00fc00210f60 0x451c03f000003fc0 0xd14700fc00000ff0

def z1108 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xa0e7fc00079c0000 0x2839ff0001e70000

def z1109 : W := mkw 0x00d7280000000000 0x0035ca0000000000 0xf9fffffff0000001 0xfe7ffffffc000000

def z1110 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfafe70000ffc0002 0x3ebf9c0003ff0000

def z1111 : W := mkw 0x029cd4000f7bc003 0x80a7350003def000 0xfafe70000fffc002 0x3ebf9c0003fff000

def z1112 : W := mkw 0x02d7ec01073b8052 0x80b5fb0041cee014 0xece5cc0107ff01f3 0xfb39730041ffc07c

def z1113 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0x32fd8c000f9c0000 0x0cbf630003e70000

def z1114 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x0400013000003fc0 0x0100004c00000ff0

def z1115 : W := mkw 0x02dffc410f7bd153 0x80b7ff1043def454 0xfffffec10ffff1f3 0xffffffb043fffc7c

def z1116 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfffffec8cffff1ce 0xffffffb233fffc73

def z1117 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfafffc060fffc033 0x3ebfff0183fff00c

def z1118 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1e73f9c863f1ff 0xffc79cfe7218fc7f

def z1119 : W := mkw 0x2008104048405105 0x0802041012101441 0xdf1a32c8c863f1ff 0xf7c68cb23218fc7f

def z1120 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7bfc01f00ffc0fc2 0x9eff007c03ff03f0

def z1121 : W := mkw 0xa39c7cf14a7d55d7 0xa8e71f3c529f5575 0x411c7cf1c07c01c0 0x90471f3c701f0070

def z1122 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfefffd373fffc1f3 0xffbfff4dcffff07c

def z1123 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xed05cffff47f0ff3 0xfb4173fffd1fc3fc

def z1124 : W := mkw 0x009cd4000e7b4003 0x80273500039ed000 0xfafffc000fffc002 0x3ebfff0003fff000

def z1125 : W := mkw 0x2008504148615157 0x0802141052185455 0xdf1a73fff863f1ff 0xf7c69cfffe18fc7f

def z1126 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfafdcd373ffc0003 0xfebf734dcfff0000

def z1127 : W := mkw 0x12dffc0fbf7bc273 0x84b7ff03efdef09c 0xfafffc0fffffc033 0x3ebfff03fffff00c

def z1128 : W := mkw 0x12dffc031f7bc273 0x84b7ff00c7def09c 0xfafffc000fffc032 0x3ebfff0003fff00c

def z1129 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0xbae7fc000f9fc002 0x2eb9ff0003e7f000

def z1130 : W := mkw 0x10000013100406f0 0x04000004c40101bc 0xec05cd37347c0ff3 0xfb01734dcd1f03fc

def z1131 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffe080ffff00e 0x3ebfff8203fffc03

def z1132 : W := mkw 0xa1bc13f04ad47d85 0x686f04fc12b51f61 0x7ffc33f0cffc3fc2 0xdfff0cfc33ff0ff0

def z1133 : W := mkw 0x00dfa8000f528000 0x0037ea0003d4a000 0xfafffc000fffc002 0x3ebfff0003fff000

def z1134 : W := mkw 0x00948400061a0000 0x8025210001868000 0x20e58c00079c0000 0x0839630001e70000

def z1135 : W := mkw 0x029cd4000f7bc003 0x80a7350003def000 0xfafdcc000fffc002 0x3ebf730003fff000

def z1136 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfbfe72c9cffc0003 0xfeff9cb273ff0000

def z1137 : W := mkw 0x02438400071a8000 0x8090e10001c6a000 0xbae380000f9fc002 0x2eb8e00003e7f000

def z1138 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0x7afe7c000ffcc002 0x1ebf9f0003ff3000

def z1139 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffe03f80ffcffce 0xdfff80fe03ff3ff3

def z1140 : W := mkw 0x029c38000a504001 0x00a70e0002941000 0x7afc30000ffc0002 0x1ebf0c0003ff0000

def z1141 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0x60e5cc0007fc0000 0x1839730001ff0000

def z1142 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc03f9cffc3fc3 0xdfff00fe73ff0ff0

def z1143 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x2d0003f004003fc2 0xcb4000fc01000ff0

def z1144 : W := mkw 0x02dffca00f7bc003 0x80b7ff2803def000 0xfbfffcf00fffc002 0xbeffff3c03fff000

def z1145 : W := mkw 0x10008412140e06a0 0x84002104850381a8 0x24058d36347c0fc2 0x0901634d8d1f03f0

def z1146 : W := mkw 0x2008504148615157 0x0802141052185455 0xc51a72c9c063f1fd 0xf1469cb27018fc7f

def z1147 : W := mkw 0x12dffc031f7bc273 0x84b7ff00c7def09c 0xfefffd073fffce33 0x7fbfff41cffff38c

def z1148 : W := mkw 0xe12003ff40843ffc 0x784800ffd0210fff 0x050003ffc0003ffd 0xc14000fff0000fff

def z1149 : W := mkw 0x02dfac000f5a8000 0x80b7eb0003d6a000 0xfaff8c000fffc002 0x3ebfe30003fff000

def z1150 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfafdcc000ffc0002 0x3ebf730003ff0000

def z1151 : W := mkw 0x00f72baca1008000 0x003dcaeb28402000 0xfbfffffffb80c001 0xfefffffffee03000

def z1152 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf9fffdf7f0000000 0xbe7fff7dfc000000

def z1153 : W := mkw 0x009c80000e520000 0x0027200003948000 0xfafd80000fff0002 0x3ebf600003ffc000

def z1154 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfbffffffffffc003 0xfefffffffffff000

def z1155 : W := mkw 0x4020031e00842ea8 0x500800c780210baa 0x0400033e00003ffd 0xc10000cf80000fff

def z1156 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x36e3830e0f83fe3e 0x0db8e0c383e0ff8f

def z1157 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf9fffffff47c0003 0xfe7ffffffd1f0000

def z1158 : W := mkw 0x5020031e10842ea8 0x540800c784210baa 0x0000013630000e00 0x0000004d8c000380

def z1159 : W := mkw 0x00004011002504d2 0x0000100440094134 0xec05cd37347f0ff3 0xfb01734dcd1fc3fc

def z1160 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xbee78e080f9ff03f 0x6fb9e38203e7fc0f

def z1161 : W := mkw 0x3000c413542f06f6 0x8c003104d50bc1bd 0xec05cd3ff47f0fff 0xfb01734ffd1fc3ff

def z1162 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x010003f000003e00 0x004000fc00000f80

def z1163 : W := mkw 0xa12813f048c47d85 0x684a04fc12311f61 0x171a33f8c800ffcc 0xc5c68cfe32003ff3

def z1164 : W := mkw 0x4063ab0ea582aa28 0x5018eac3a960aa8a 0xfffbffcfff83fe3f 0xfffefff3ffe0ff8f

def z1165 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfbfffcc9cfffc1ff 0xbeffff3273fff07f

def z1166 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfbfffec8cfffc002 0x3effffb233fff000

def z1167 : W := mkw 0x5020031e10842ea8 0x540800c784210baa 0x0400033e30003e3d 0x410000cf8c000f8f

def z1168 : W := mkw 0x2008504148615157 0x0802141052185455 0xd31a72c9c863f1fd 0xb4c69cb27218fc7f

def z1169 : W := mkw 0x02df7c000b79c003 0x80b7df0002de7000 0xfafffc000bfcc000 0x3ebfff0002ff3000

def z1170 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xa405cd37347f0ff3 0x2901734dcd1fc3fc

def z1171 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0xfafffc000f9cc000 0x3ebfff0003e73000

def z1172 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc03f80ffc3fff 0xdfff00fe03ff0fff

def z1173 : W := mkw 0x0020830204822a20 0x400820c081208a88 0xbee3830e0f83fe3f 0x6fb8e0c383e0ff8f

def z1174 : W := mkw 0x0208d4000f7bc003 0x8082350003def000 0x3ae000000fffc002 0x0eb8000003fff000

def z1175 : W := mkw 0x009c00000a500000 0x0027000002940000 0x7efc02000ffc3002 0x5fbf008003ff0c00

def z1176 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc03f73ffc3fc3 0xdfff00fdcfff0ff0

def z1177 : W := mkw 0x5020031f10842ef8 0x540800c7c4210bbe 0x0400030e00003ffd 0x410000c380000fff

def z1178 : W := mkw 0x02dffcacaf7bc003 0x80b7ff2b2bdef000 0xfbfffcffffffc003 0xbeffff3ffffff000

def z1179 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x30ffbc00079c0000 0x0c3fef0001e70000

def z1180 : W := mkw 0x02dfd4000f7bc003 0x80b7f50003def000 0xfaff80000fffc002 0x3ebfe00003fff000

def z1181 : W := mkw 0x5020431f10a52efa 0x540810c7c4294bbe 0xde02433f3863ffff 0xf78090cfce18ffff

def z1182 : W := mkw 0x1020031310842ef0 0x440800c4c4210bbc 0x0400033730003ff1 0xc10000cdcc000ffc

def z1183 : W := mkw 0x02df28000b508000 0x00b7ca0002d42000 0x7afc00000ffc0002 0x1ebf000003ff0000

def z1184 : W := mkw 0x009428a0a0000000 0x00250a2828000000 0xf91ffffff0000001 0xfe47fffffc000000

def z1185 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xa0e78c00079fc000 0x2839e30001e7f000

def z1186 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfffb83ce0f83fe3f 0xfffee0f383e0ff8f

def z1187 : W := mkw 0x329c7c515a7d55d7 0x8ca71f14569f5575 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z1188 : W := mkw 0x024bd4000f7bc003 0x8092f50003def000 0xfae7cc000fffc002 0x3eb9f30003fff000

def z1189 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x37fc03f00ffc3fc2 0x0dff00fc03ff0ff0

def z1190 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xb2e3830e0f83fe3d 0x2cb8e0c383e0ff8f

def z1191 : W := mkw 0x83dffce00f7bd103 0xa0f7ff3803def440 0xfbfffcc00fffc002 0x3effff3003fff000

def z1192 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x68e58c0007fc0002 0x1a39630001ff0000

def z1193 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfefffd373fffce33 0xffbfff4dcffff38c

def z1194 : W := mkw 0x0043c400052b8002 0x8010f100014ae000 0xe8e5cc0007ff0002 0x3a39730001ffc000

def z1195 : W := mkw 0x0020031000842c80 0x400800c400210b20 0x3ee003000ffc3fc2 0x4fb800c003ff0ff0

def z1196 : W := mkw 0xa1bc13f04ad47d85 0x686f04fc12b51f61 0xfffe73f9cffcffcf 0xffff9cfe73ff3ff3

def z1197 : W := mkw 0x02dfb8000f52c001 0x00b7ee0003d4b000 0xfaffb0000fffc002 0x3ebfec0003fff000

def z1198 : W := mkw 0x812803500ad43d80 0x604a00d402b50f60 0x16e002000ffc3fc2 0x05b8008003ff0ff0

def z1199 : W := mkw 0x2000504140215157 0x0800141050085455 0xdd1a72c9c003f1fd 0xf7469cb27000fc7f

def z1200 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfafffc000ffff00e 0x3ebfff0003fffc03

def z1201 : W := mkw 0x009c00000a500000 0x0027000002940000 0xfafe00000fffc002 0x3ebf800003fff000

def z1202 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x32ffbc000fffc002 0x0cbfef0003fff000

def z1203 : W := mkw 0x009c00000a500000 0x0027000002940000 0x32fc00000f9c0000 0x0cbf000003e70000

def z1204 : W := mkw 0x2008504148615157 0x0802141052185455 0x571a72c9c863f1fe 0x95c69cb27218fc7f

def z1205 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfbfffec9cfffc03f 0xfeffffb273fff00f

def z1206 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x65fc03f007fc3fc0 0xd97f00fc01ff0ff0

def z1207 : W := mkw 0xb108d4535eff7ff7 0xec423514d7bfdffd 0x060000000ffffffe 0x0180000003ffffff

def z1208 : W := mkw 0x81b403b002942c80 0x606d00ec00a50b20 0x24e4013007fc0fc2 0x0939004c01ff03f0

def z1209 : W := mkw 0x12dffc031f7bc273 0x84b7ff00c7def09c 0xfafffd373fffc033 0xfebfff4dcffff00c

def z1210 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfefffe090ffff1ff 0xffbfff8243fffc7f

def z1211 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0xf8fffc0007ff0002 0x3e3fff0001ffc000

def z1212 : W := mkw 0x02d7280003108000 0x00b5ca0000c42000 0x20e40000079c0000 0x0839000001e70000

def z1213 : W := mkw 0x009c00400a501100 0x0027001002940440 0x7bfc02c00ffc3002 0x1eff00b003ff0c00

def z1214 : W := mkw 0xc12003fe00843fa8 0x704800ff80210fea 0x050003f600003fc0 0xc14000fd80000ff0

def z1215 : W := mkw 0x502003bfb0842ef8 0x540800efec210bbe 0x050003fff0003ffd 0xc14000fffc000fff

def z1216 : W := mkw 0x0028035008c43d80 0x400a00d402310f60 0x7ffc03f00ffc3fc2 0xdfff00fc03ff0ff0

def z1217 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0x61fdfcc1c7fc01c0 0x987f7f3071ff0070

def z1218 : W := mkw 0x812003f200843fa0 0x604800fc80210fe8 0x050003f600003ff1 0xc14000fd80000ffc

def z1219 : W := mkw 0x0000001000040480 0x0000000400010120 0x6c058d36347c0fc2 0xdb01634d8d1f03f0

def z1220 : W := mkw 0x5043c40f152b827a 0x9410f103c54ae09e 0x8001cc0730030031 0x20007301cc00c00c

def z1221 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfbfffec9cffff03f 0x3effffb273fffc0f

def z1222 : W := mkw 0x42dffc0e0f7bc22b 0x90b7ff0383def08a 0xfefffd0e0fffce3f 0x7fbfff4383fff38f

def z1223 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfc1ffd37347f0ff3 0xff07ff4dcd1fc3fc

def z1224 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x32e78c000f9cc000 0x0cb9e30003e73000

def z1225 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0x52fe30000bfcc000 0x14bf8c0002ff3000

def z1226 : W := mkw 0x0043c401052b8052 0x8010f100414ae014 0xfee7ce090ffff1ff 0xffb9f38243fffc7f

def z1227 : W := mkw 0x3208d4535f7fd7f7 0x8c823514d7dff5fd 0x060000000ffffffe 0x0180000003ffffff

def z1228 : W := mkw 0x00f72baca0802800 0x403dcaeb28200a00 0xfbfffffffb803001 0xfefffffffee00c00

def z1229 : W := mkw 0x00438400050a8000 0x8010e1000142a000 0xbae78c000f9fc002 0x2eb9e30003e7f000

def z1230 : W := mkw 0x02d7ac0ca71a8000 0x80b5eb0329c6a000 0xa0e7fc0ff79c0001 0x2839ff03fde70000

def z1231 : W := mkw 0x029c2c000a580000 0x80a70b0002960000 0x7afc0c000ffc0002 0x1ebf030003ff0000

def z1232 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfffffec8cffff1fe 0x3fffffb233fffc7f

def z1233 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe73f00ffc3fc2 0xffff9cfc03ff0ff0

def z1234 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffe080fffc003 0x7ebfff8203fff000

def z1235 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xa2e7fc000fffc002 0x28b9ff0003fff000

def z1236 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xe805cd37347f0fc2 0xba01734dcd1fc3f0

def z1237 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe03f00fffffc2 0xffff80fc03fffff0

def z1238 : W := mkw 0x00d7800007128000 0x0035e00001c4a000 0xbae780000f9fc002 0x2eb9e00003e7f000

def z1239 : W := mkw 0x40f72baca180a808 0x503dcaeb28602a02 0xfffffffffb83f03f 0xfffffffffee0fc0f

def z1240 : W := mkw 0xc120035e00843fa8 0x704800d780210fea 0x0400030e00003ffd 0x410000c380000fff

def z1241 : W := mkw 0xc1ff2becabd0b908 0x707fcafb2af42e42 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z1242 : W := mkw 0x009cc4410e7b1152 0x80273110439ec454 0xfffdcec10fff31f3 0xffff73b043ffcc7c

def z1243 : W := mkw 0x204bd4414d6bd157 0x8812f510535af455 0xfffffec9cffff1ff 0xffffffb273fffc7f

def z1244 : W := mkw 0x00b42ba0a0000000 0x002d0ae828000000 0xf9fdfff7f0000001 0xfe7f7ffdfc000000

def z1245 : W := mkw 0x402083020582aa28 0x500820c08160aa8a 0xbee203080f83fe3f 0x6fb880c203e0ff8f

def z1246 : W := mkw 0x02dfec000f7b8002 0x80b7fb0003dee000 0xfafdcc000fff0002 0x3ebf730003ffc000

def z1247 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfbfffec9cfffc1c3 0xfeffffb273fff070

def z1248 : W := mkw 0x812803f008c43d80 0x604a00fc02310f60 0x070003f008603fc2 0xc1c000fc02180ff0

def z1249 : W := mkw 0x42dffc020f7bc22b 0x90b7ff0083def08a 0xfafffc000fffc03e 0x3ebfff0003fff00f

def z1250 : W := mkw 0x00b42baca0000000 0x002d0aeb28000000 0xe91dfffff0000001 0xfa477ffffc000000

def z1251 : W := mkw 0x5043ec0fb52b827a 0x9410fb03ed4ae09e 0x8003fc0ff003c03d 0x2000ff03fc00f00f

def z1252 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfafffd060fffce02 0x3ebfff4183fff380

def z1253 : W := mkw 0x40f72baca1008008 0x103dcaeb28402002 0xf9fffffff000c00d 0xfe7ffffffc003003

def z1254 : W := mkw 0x220854414a795157 0x88821510529e5455 0xdf1a72c9c87ff1ff 0xf7c69cb2721ffc7f

def z1255 : W := mkw 0x3000d413542f46f7 0x8c003504d50bd1bd 0xec05cd37347fcfff 0xfb01734dcd1ff3ff

def z1256 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6405cd37347c0ff1 0xd901734dcd1f03fc

def z1257 : W := mkw 0xc12003be00842ea8 0x704800ef80210baa 0x0000013600000e00 0x0000004d80000380

def z1258 : W := mkw 0x009c00000a500000 0x0027000002940000 0x60fc000007fc0000 0x183f000001ff0000

def z1259 : W := mkw 0x029c54000a794003 0x80a71500029e5000 0x7afc00000ffc0002 0x1ebf000003ff0000

def z1260 : W := mkw 0x81bc03b00ad42c80 0x606f00ec02b50b20 0x7efc01300ffc0fc2 0xdfbf004c03ff03f0

def z1261 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffc03f00fff3ff3 0xffff00fc03ffcffc

def z1262 : W := mkw 0x029c84000f5a8000 0x80a7210003d6a000 0x7afc00000ffc0002 0x1ebf000003ff0000

def z1263 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x02e000000fffc002 0x00b8000003fff000

def z1264 : W := mkw 0x81b403f002943d80 0x606d00fc00a50f60 0x6de403f007fc3fc2 0xdb7900fc01ff0ff0

def z1265 : W := mkw 0x209c50414a715157 0x08271410529c5455 0x7bfc70c1cffc01c2 0x9eff1c3073ff0070

def z1266 : W := mkw 0x02942c0002180000 0x80a50b0000860000 0x20e40c00079c0000 0x0839030001e70000

def z1267 : W := mkw 0x4063ab0ea582aa28 0x5018eac3a960aa8a 0xbee38f0e3f83fe3f 0x6fb8e3c38fe0ff8f

def z1268 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x52fe7c000fffc002 0x14bf9f0003fff000

def z1269 : W := mkw 0x81bc03500ad43d80 0x606f00d402b50f60 0x7efc03000ffc3fc2 0x5fbf00c003ff0ff0

def z1270 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1bf3cfc863f1ff 0xffc6fcf3f218fc7f

def z1271 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1ffec9c863f1ff 0xffc7ffb27218fc7f

def z1272 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x60fdfc00079c0000 0x183f7f0001e70000

def z1273 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x050003f730003fc1 0xc14000fdcc000ff0

def z1274 : W := mkw 0x402083020582aa28 0x500820c08160aa8a 0xbee183060f83fe3f 0x6fb860c183e0ff8f

def z1275 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0xdd1a73f9c0003fc1 0xf7469cfe70000ff0

def z1276 : W := mkw 0x4063ab0ea582aa28 0x5018eac3a960aa8a 0xfee7ff3fff83fe3f 0xffb9ffcfffe0ff8f

def z1277 : W := mkw 0x2008504148615157 0x0802141052185455 0x5f1a32c8c863f1fe 0xd7c68cb23218fc7f

def z1278 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x3ee403300ffc3fc2 0x4fb900cc03ff0ff0

def z1279 : W := mkw 0x83bc3bf00ad47d81 0x60ef0efc02b51f60 0x7ffc33f00ffc3fc2 0xdfff0cfc03ff0ff0

def z1280 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfdfffffff0030033 0xff7ffffffc00c00c

def z1281 : W := mkw 0x009c84000e5a0000 0x8027210003968000 0x7afd8c000ffc0002 0x1ebf630003ff0000

def z1282 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0xa0e5cc00079f0000 0x2839730001e7c000

def z1283 : W := mkw 0x00b403b000842c80 0x402d00ec00210b20 0x7ffc03f00ffc3fc2 0xdfff00fc03ff0ff0

def z1284 : W := mkw 0x2008504148615157 0x0802141052185455 0xdf1bfecff863f1ff 0xf7c6ffb3fe18fc7f

def z1285 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec07cd3f347fcfff 0xfb01f34fcd1ff3ff

def z1286 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x6c05cd37347c0fc2 0xdb01734dcd1f03f0

def z1287 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffe000ffff002 0x7fbfff8003fffc00

def z1288 : W := mkw 0x812803fca8c43d80 0x604a00ff2a310f60 0xdf1a73fff8603fc3 0xf7c69cfffe180ff0

def z1289 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x20e58c0007fc0000 0x0839630001ff0000

def z1290 : W := mkw 0x912843f318e53ff2 0x644a10fcc6394ffc 0xdf1843f738633ff3 0xf7c610fdce18cffc

def z1291 : W := mkw 0x22df38404b50d105 0x08b7ce1012d43441 0x7ffe32c8cffcf1ce 0xdfff8cb233ff3c73

def z1292 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xd2fffc000bffc000 0x34bfff0002fff000

def z1293 : W := mkw 0xc12003be00842ea8 0x704800ef80210baa 0x0400033e00003e3d 0x410000cf80000f8f

def z1294 : W := mkw 0x00df78000a714003 0x0037de00029c5000 0xfafffc000fffc002 0x3ebfff0003fff000

def z1295 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xf9fffffff003c03d 0xfe7ffffffc00f00f

def z1296 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee78f3e3f83fe3f 0x6fb9e3cf8fe0ff8f

def z1297 : W := mkw 0xa19c78f1ea7555d7 0x28671e3c7a9d5575 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z1298 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xdffa72c9cffff1ff 0xf7fe9cb273fffc7f

def z1299 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xfee7833e0f83fe3f 0xffb9e0cf83e0ff8f

def z1300 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x00e00000079c0000 0x0038000001e70000

def z1301 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x62fdfc000fffc002 0x18bf7f0003fff000

def z1302 : W := mkw 0x00d7280002100000 0x0035ca0000840000 0x20e58c00079c0000 0x0839630001e70000

def z1303 : W := mkw 0x1000c413152f86f2 0x84003104c54be1bc 0xee05cd373fffcff3 0xfb81734dcffff3fc

def z1304 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfefffc000ffff1c2 0x3fbfff0003fffc70

def z1305 : W := mkw 0x81bc03fcaad43d80 0x606f00ff2ab50f60 0xfffdcffffffc3fc3 0xffff73ffffff0ff0

def z1306 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xe1fffdfff0000001 0xb87fff7ffc000000

def z1307 : W := mkw 0x0000c410042f0482 0x80003104010bc120 0xec05cd37347f0fc3 0xfb01734dcd1fc3f0

def z1308 : W := mkw 0x404380020582aa28 0x5010e0008160aa8a 0xbee381060f83fe3f 0x6fb8e04183e0ff8f

def z1309 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xed1dfdf7f47f0ff3 0xfb477f7dfd1fc3fc

def z1310 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfbfffcc0cfffc002 0x3effff3033fff000

def z1311 : W := mkw 0x009c00400a501100 0x0027001002940440 0x7efc00000ffc31c2 0x1fbf000003ff0c70

def z1312 : W := mkw 0x812803f008c43d80 0x604a00fc02310f60 0x171803f008003fc0 0xc5c600fc02000ff0

def z1313 : W := mkw 0xa1bc13f04ad47d85 0x686f04fc12b51f61 0x7ffc03f00ffcffce 0xdfff00fc03ff3ff3

def z1314 : W := mkw 0x40f72baca0802808 0x503dcaeb28200a02 0xf9fffffff000300d 0xfe7ffffffc000c03

def z1315 : W := mkw 0xb19c54f15a7d55d7 0xac67153c569f5575 0x411c7cf1f07c01c0 0x90471f3c7c1f0070

def z1316 : W := mkw 0x812003f000843d80 0x604800fc00210f60 0x1f0003f008003fc2 0xc7c000fc02000ff0

def z1317 : W := mkw 0x02dffca0af7bc003 0x80b7ff282bdef000 0xfbfffef9ffffc003 0xfeffffbe7ffff000

def z1318 : W := mkw 0x02dffc030f7bc273 0x80b7ff00c3def09c 0xfefffd070fffcff3 0xffbfff41c3fff3fc

def z1319 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x20e58d36379c0000 0x0839634d8de70000

def z1320 : W := mkw 0x2008504148615157 0x0802141052185455 0x971a72c9c863f1ff 0x25c69cb27218fc7f

def z1321 : W := mkw 0x02dffc010f7bc053 0x80b7ff0043def014 0xfffffec9cfffc1f3 0xffffffb273fff07c

def z1322 : W := mkw 0x912003b310842ef0 0x644800ecc4210bbc 0x0400013730000ff1 0xc100004dcc0003fc

def z1323 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0x24058d37347f0ff3 0xc901634dcd1fc3fc

def z1324 : W := mkw 0x02d7aca0a71a8000 0x80b5eb2829c6a000 0x20e58c30379c0000 0x0839630c0de70000

def z1325 : W := mkw 0x40df800e0f528228 0x1037e00383d4a08a 0xfaff800e0fffc03f 0x3ebfe00383fff00f

def z1326 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x051803f000003fc0 0xc14600fc00000ff0

def z1327 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0xa8e58c00079f0002 0x2a39630001e7c000

def z1328 : W := mkw 0x02df38000b50c001 0x00b7ce0002d43000 0x12fa30000ffcc002 0x04be8c0003ff3000

def z1329 : W := mkw 0x22dffc004f7bc007 0x88b7ff0013def001 0xfafffc08cfffc00e 0x3ebfff0233fff003

def z1330 : W := mkw 0x22dffc404f7bd107 0x88b7ff1013def441 0xfffffec8cffff03f 0x7fffffb233fffc0f

def z1331 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xec05cd36347f0ff2 0x3b01734d8d1fc3fc

def z1332 : W := mkw 0x02d7ac0ca71a8000 0x80b5eb0329c6a000 0x20e58c06379c0000 0x083963018de70000

def z1333 : W := mkw 0x4020c70e04ab2a2a 0xd00831c3812aca8a 0xec05cf0e047f3e3f 0x7b0173c3811fcf8f

def z1334 : W := mkw 0x819c00500ad43d80 0x6067001402b50f60 0x16f800000ffc3fc2 0x05be000003ff0ff0

def z1335 : W := mkw 0x10004411102d04d2 0x84001104440b4134 0xec05cd37347c0fc3 0xfb01734dcd1f03f0

def z1336 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfafffc000fffc1c2 0x3ebfff0003fff070

def z1337 : W := mkw 0x81bc03fcaad43d80 0x606f00ff2ab50f60 0x7ffc03f8cffc3fc2 0xdfff00fe33ff0ff0

def z1338 : W := mkw 0x209c00414a501154 0x0827001052940455 0x7ffc02c9cffc31ff 0xdfff00b273ff0c7f

def z1339 : W := mkw 0x004bd4000d6bc003 0x8012f500035af000 0xfafffc000fffc002 0x3ebfff0003fff000

def z1340 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x73fc03f00ffc3fc0 0x9cff00fc03ff0ff0

def z1341 : W := mkw 0x7028535f58e57fff 0x5c0a14d7d6395fff 0xdf1a73fff863ffff 0xf7c69cfffe18ffff

def z1342 : W := mkw 0x029cfc000e7b4003 0x80a73f00039ed000 0xfafdfc000fff0002 0x3ebf7f0003ffc000

def z1343 : W := mkw 0x02d7ec00073b8002 0x80b5fb0001cee000 0xfae7cc000fffc002 0x3eb9f30003fff000

def z1344 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbee381060f83fe3e 0x2fb8e04183e0ff8f

def z1345 : W := mkw 0x0063030c00802800 0x4018c0c300200a00 0xbee3830e0f83fe3f 0x6fb8e0c383e0ff8f

def z1346 : W := mkw 0x0000001000040480 0x0000000400010120 0x7ee401300ffc0fc2 0xdfb9004c03ff03f0

def z1347 : W := mkw 0x12d7ac02171a8220 0x84b5eb0085c6a088 0x20e58c06379c0000 0x083963018de70000

def z1348 : W := mkw 0x02d72c0003188000 0x80b5cb0000c62000 0x00e40c00039c0000 0x0039030000e70000

def z1349 : W := mkw 0x0094000002100000 0x0025000000840000 0x3ae400000f9c0002 0x0eb9000003e70000

def z1350 : W := mkw 0x22dffc414f7bd157 0x88b7ff1053def455 0xfefffe080ffff1ff 0x7fbfff8203fffc7f

def z1351 : W := mkw 0x024bd4000f7bc003 0x8092f50003def000 0xfafbf0000fffc002 0x3ebefc0003fff000

def z1352 : W := mkw 0x02d7aca0a71a8000 0x80b5eb2829c6a000 0x61fdfcf1f79c0000 0x987f7f3c7de70000

def z1353 : W := mkw 0x406383aea582aa28 0x5018e0eba960aa8a 0xbfe383cecf83fe3f 0x6ff8e0f3b3e0ff8f

def z1354 : W := mkw 0x22dffc0def7bc057 0x88b7ff037bdef015 0xfafffc0fffffc03f 0x3ebfff03fffff00f

def z1355 : W := mkw 0x00df280caa500000 0x0037ca032a940000 0xfafffc0ffffc0003 0x3ebfff03ffff0000

def z1356 : W := mkw 0x00f72baca0000000 0x003dcaeb28000000 0xfdfffffff06001c3 0xff7ffffffc180070

def z1357 : W := mkw 0x3000d413542f46f7 0x8c003504d50bd1bd 0xfe07ff3ffc7fffff 0xff81ffcfff1fffff

def z1358 : W := mkw 0x00bc03b00a540480 0x002f00ec02950120 0x7ffc03f00ffc0fc2 0xdfff00fc03ff03f0

def z1359 : W := mkw 0x00df80400f529100 0x0037e01003d4a440 0xffff82c80ffff1ff 0xffffe0b203fffc7f

def z1360 : W := mkw 0x812803f008c43d80 0x604a00fc02310f60 0x451803f000603fc0 0xd14600fc00180ff0

def z1361 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x67fc01f00ffc3fc2 0x99ff007c03ff0ff0

def z1362 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x3ee183060f83fe3e 0x4fb860c183e0ff8f

def z1363 : W := mkw 0x22df7c414b79d157 0x88b7df1052de7455 0x53fe7ec9cbfcf1cc 0x94ff9fb272ff3c73

def z1364 : W := mkw 0x02d7ac00071a8000 0x80b5eb0001c6a000 0x3ae58c000f9c0002 0x0eb9630003e70000

def z1365 : W := mkw 0x12d7ec03173b8272 0x84b5fb00c5cee09c 0xa0e5cc07379f0031 0x28397301cde7c00c

def z1366 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfd1dcff7347f0ff3 0xff4773fdcd1fc3fc

def z1367 : W := mkw 0x009c80000f528000 0x0027200003d4a000 0x7afc00000fffc002 0x1ebf000003fff000

def z1368 : W := mkw 0x22dfbc404f5ad105 0x88b7ef1013d6b441 0x33ffbec8cf9cf00c 0x0cffefb233e73c03

def z1369 : W := mkw 0x812083f204863fa0 0x604820fc81218fe8 0xad0183f604033ff3 0xeb4060fd8100cffc

def z1370 : W := mkw 0x029c7c000a794003 0x80a71f00029e5000 0x52fc7c000bfc0000 0x14bf1f0002ff0000

def z1371 : W := mkw 0x02dffc020f7bc223 0x80b7ff0083def088 0xfeffff0e0ffffe3f 0x7fbfffc383ffff8f

def z1372 : W := mkw 0x22d7fc01473bc057 0x88b5ff0051cef015 0xa0e7fc09c79fc03d 0x2839ff0271e7f00f

def z1373 : W := mkw 0x1000c413142f06f2 0x84003104c50bc1bc 0xfe07cd373c7fcff3 0xff81f34dcf1ff3fc

def z1374 : W := mkw 0xc12803fe08c43fa8 0x704a00ff82310fea 0xdf1a03fe0863ffff 0xf7c680ff8218ffff

def z1375 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffdcff00ffc3fc2 0xffff73fc03ff0ff0

def z1376 : W := mkw 0x81bc2bf0aad43d80 0x606f0afc2ab50f60 0x7ffc33f0cffc3fc2 0xdfff0cfc33ff0ff0

def z1377 : W := mkw 0x224bd4414f7bd157 0x8892f51053def455 0xfffbf2c9cffff1ff 0xfffefcb273fffc7f

def z1378 : W := mkw 0x02948400071a8000 0x80a5210001c6a000 0x20e40000079c0000 0x0839000001e70000

def z1379 : W := mkw 0x00d7ec00052b8002 0x8035fb00014ae000 0xfafffc000fffc002 0x3ebfff0003fff000

def z1380 : W := mkw 0x50f7afbeb58eaea8 0xd43debefad63abaa 0x20e58d36379c0e00 0x0839634d8de70380

def z1381 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfefffc000ffff03e 0x3fbfff0003fffc0f

def z1382 : W := mkw 0x02d7fc00073bc003 0x80b5ff0001cef000 0xf8fffc00079fc000 0x3e3fff0001e7f000

def z1383 : W := mkw 0x22dffc014f7bc057 0x88b7ff0053def015 0xfafffc000fffc03e 0x3ebfff0003fff00f

def z1384 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfbfffec00fffc002 0xfeffffb003fff000

def z1385 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0xbfe383cfcf83fe3f 0xeff8e0f3f3e0ff8f

def z1386 : W := mkw 0x912003f310843ff0 0x644800fcc4210ffc 0x050003f000003ff0 0xc14000fc00000ffc

def z1387 : W := mkw 0x2008504148615157 0x0802141052185455 0x9f1a32c8c863f1ff 0x67c68cb23218fc7f

def z1388 : W := mkw 0x5063c71f15afaefa 0xd418f1c7c56bebbe 0x8403cf3f3003fffd 0xe100f3cfcc00ffff

def z1389 : W := mkw 0x819c00f00ad43d80 0x6067003c02b50f60 0x7ffc00f00ffc3fc2 0x9fff003c03ff0ff0

def z1390 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0x92fbfc000fffc002 0x24beff0003fff000

def z1391 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xe0fffc0007ffc000 0x383fff0001fff000

def z1392 : W := mkw 0xc12003f200843fa8 0x704800fc80210fea 0x050003f000003ffc 0xc14000fc00000fff

def z1393 : W := mkw 0x22df78414b71d157 0x08b7de1052dc7455 0xfffe72c9cffff1ff 0xffff9cb273fffc7f

def z1394 : W := mkw 0x912003ffb0843ff0 0x644800ffec210ffc 0x050003fff0003ff1 0xc14000fffc000ffc

def z1395 : W := mkw 0xa1ff3becead07905 0x687fcefb3ab41e41 0x13fa32c8cb80f00c 0x04fe8cb232e03c03

def z1396 : W := mkw 0x00b403a000000000 0x002d00e800000000 0xf9fffffff0000001 0xfe7ffffffc000000

def z1397 : W := mkw 0x02dffc400f7bd103 0x80b7ff1003def440 0xfbfffcc00fffc1c2 0xbeffff3003fff070

def z1398 : W := mkw 0xc12003fea0843fa8 0x704800ffa8210fea 0x050003fff0003ffd 0xc14000fffc000fff

def z1399 : W := mkw 0xc1bc03fc0ad43d88 0x706f00ff02b50f62 0x7ffc03f80ffc3fce 0xdfff00fe03ff0ff3

def z1400 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffc43f10ffc3fc3 0xffff10fc43ff0ff0

def z1401 : W := mkw 0xa1bc03f04ad43d84 0x686f00fc12b50f61 0x7ffc03f8cffc3fce 0xdfff00fe33ff0ff3

def z1402 : W := mkw 0x0020030000802800 0x400800c000200a00 0x3ee003000f83fe3e 0x4fb800c003e0ff8f

def z1403 : W := mkw 0x02dfbc000f5ac001 0x80b7ef0003d6b000 0x20fdbc00079c0000 0x083f6f0001e70000

def z1404 : W := mkw 0x0243fc00052bc003 0x8090ff00014af000 0xfae7fc000fffc002 0x3eb9ff0003fff000

def z1405 : W := mkw 0x029cd4000f7bc003 0x80a7350003def000 0x22e400000fffc002 0x08b9000003fff000

def z1406 : W := mkw 0x02dffc0caf7bc003 0x80b7ff032bdef000 0xfbfffecfffffc003 0xfeffffb3fffff000

def z1407 : W := mkw 0x00df00000a500000 0x0037c00002940000 0xfaff80000ffc0002 0x3ebfe00003ff0000

def z1408 : W := mkw 0x00d728aca0000000 0x0035ca2b28000000 0xd91ffefff0000001 0xf647ffbffc000000

def z1409 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x3ee203080f83fe3e 0x4fb880c203e0ff8f

def z1410 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0xfffe73f9cfffffff 0xffff9cfe73ffffff

def z1411 : W := mkw 0xa12003f140843dd4 0x684800fc50210f75 0x050003f000003ffc 0xc14000fc00000fff

def z1412 : W := mkw 0x5000c413152f86fa 0x94003104c54be1be 0xec05cd37347fcfff 0xfb01734dcd1ff3ff

def z1413 : W := mkw 0x02dffc000f7bc003 0x80b7ff0003def000 0xfafffc080fffc03f 0x3ebfff0203fff00f

def z1414 : W := mkw 0x009c80020e520220 0x0027200083948088 0xfefd81060fff0e33 0x7fbf604183ffc38c

def z1415 : W := mkw 0xe12853ff48e57fff 0x784a14ffd2395fff 0xdf1a73ffc863ffff 0xf7c69cfff218ffff

def z1416 : W := mkw 0x2008504148615157 0x0802141052185455 0xff1a73c9cc63ffff 0xffc69cf27318ffff

def z1417 : W := mkw 0x4063830e0582aa28 0x5018e0c38160aa8a 0x16e2030e0f83fe3f 0x45b880c383e0ff8f

def z1418 : W := mkw 0x81bc03f00ad43d80 0x606f00fc02b50f60 0x7ffc73f1cffc3fc2 0xdfff1cfc73ff0ff0

def z1419 : W := mkw 0xa12053f140a57dd7 0x684814fc50295f75 0x850273f9c003fffd 0xe1409cfe7000ffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z9,z6]),(0,[z10,z0,z2,z4,z5,z11,z6])],[(0,[z12,z1,z2,z4,z5,z13,z6]),(0,[z14,z0,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z5,z6]),(0,[z0,z17,z2,z4,z5,z18,z6]),(0,[z19,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z20,z4,z5,z21,z6]),(0,[z0,z1,z22,z2,z4,z23,z6])],[(0,[z0,z1,z24,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z25]),(0,[z0,z15,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z26,z6]),(0,[z27,z0,z2,z4,z5,z18,z6])],[(0,[z0,z1,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z29,z6]),(1,[z30,z0,z1,z2,z4,z5]),(0,[z0,z2,z4,z5,z18,z6,z31]),(0,[z32,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z33])],[(0,[z0,z1,z2,z4,z5,z34,z35]),(0,[z0,z1,z20,z4,z5,z11,z6]),(0,[z0,z1,z2,z36,z5,z35,z6])],[(1,[z37,z38,z2,z4,z5,z6]),(0,[z0,z1,z39,z2,z4,z5,z6]),(0,[z40,z0,z15,z2,z4,z5,z6]),(0,[z0,z1,z41,z2,z4,z5,z6]),(0,[z0,z42,z2,z4,z43,z5,z6])],[(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z0,z45,z1,z2,z4,z5,z6]),(0,[z0,z2,z46,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z6]),(0,[z0,z1,z2,z4,z5,z49,z6]),(0,[z0,z1,z2,z4,z5,z50,z6])]],
   [[(1,[z0,z1,z51,z4,z5,z6]),(0,[z0,z2,z52,z4,z5,z53,z6]),(0,[z0,z1,z2,z4,z54,z5,z6]),(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z56,z2,z57,z4,z5,z6]),(0,[z0,z1,z58,z2,z4,z5,z6])],[(1,[z0,z1,z2,z59,z5,z6]),(0,[z0,z1,z2,z4,z60,z5,z6]),(1,[z1,z2,z4,z5,z61,z6])],[(0,[z0,z15,z28,z2,z4,z5,z6]),(0,[z62,z0,z1,z2,z4,z5,z6]),(0,[z63,z64,z0,z2,z4,z5,z6]),(0,[z19,z0,z2,z4,z47,z5,z6]),(0,[z0,z17,z2,z4,z47,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z67,z6]),(0,[z68,z0,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z69,z5,z6])],[(0,[z0,z1,z2,z4,z70,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z0,z72,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z4,z73,z5,z6])],[(0,[z63,z74,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z75,z4,z5,z6]),(0,[z76,z0,z1,z2,z4,z5,z6]),(0,[z1,z77,z2,z78,z4,z5,z6]),(1,[z0,z2,z4,z79,z5,z6]),(0,[z80,z0,z2,z52,z4,z5,z6]),(0,[z81,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z15,z2,z4,z5,z6]),(0,[z82,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z83]),(0,[z0,z1,z2,z4,z84,z5,z6]),(0,[z85,z0,z2,z4,z47,z5,z6]),(0,[z86,z63,z0,z2,z4,z5,z6]),(1,[z63,z0,z2,z4,z5,z87]),(0,[z0,z1,z2,z88,z5,z89,z6]),(0,[z90,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z91,z6]),(0,[z92,z0,z1,z2,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z94,z4,z5,z6]),(0,[z0,z1,z2,z4,z95,z5,z6]),(0,[z0,z1,z2,z4,z96,z5,z6]),(0,[z0,z1,z2,z4,z97,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6])],[(0,[z37,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z28,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z59,z5,z6]),(0,[z100,z0,z2,z4,z47,z5,z6]),(0,[z101,z63,z0,z2,z4,z5,z6]),(1,[z0,z1,z20,z102,z5,z6]),(0,[z0,z1,z2,z4,z103,z6,z104])],[(0,[z0,z1,z2,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z88,z13,z6]),(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z0,z15,z72,z2,z4,z5,z6]),(0,[z107,z0,z2,z4,z5,z18,z6]),(1,[z108,z0,z1,z109,z5,z6])],[(0,[z110,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z111]),(0,[z0,z1,z112,z2,z4,z5,z6]),(0,[z0,z1,z113,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z114,z5,z6])],[(0,[z0,z115,z1,z2,z4,z5,z6]),(0,[z0,z72,z1,z52,z4,z5,z6]),(0,[z0,z116,z2,z4,z47,z5,z6]),(0,[z63,z0,z15,z2,z4,z5,z6])],[(0,[z99,z1,z2,z78,z4,z5,z6]),(0,[z0,z1,z2,z4,z117,z5,z6]),(0,[z80,z0,z1,z118,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z119,z6]),(0,[z32,z0,z1,z2,z4,z5,z120]),(0,[z121,z0,z2,z4,z5,z6,z104])],[(0,[z38,z1,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z6]),(0,[z0,z15,z2,z4,z96,z5,z6]),(1,[z123,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z35])],[(0,[z0,z1,z2,z4,z124,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z125]),(1,[z0,z126,z2,z4,z5,z6])]],
   [[(0,[z37,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z128,z6]),(0,[z12,z1,z2,z78,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z72,z1,z2,z4,z5,z6]),(0,[z130,z0,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z5,z89,z6])],[(0,[z63,z0,z72,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z131,z5,z6]),(1,[z0,z15,z2,z132,z5,z6]),(0,[z63,z0,z2,z4,z73,z5,z6]),(1,[z0,z17,z2,z4,z5,z18]),(0,[z108,z0,z1,z4,z109,z5,z6]),(0,[z133,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z103,z6])],[(0,[z37,z0,z1,z2,z4,z5,z134]),(0,[z0,z1,z2,z4,z135,z5,z6])],[(0,[z0,z1,z2,z4,z136,z5,z6]),(0,[z0,z1,z2,z137,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z138])],[(0,[z99,z0,z1,z77,z4,z5,z6]),(1,[z0,z139,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z140,z6])],[(0,[z40,z12,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z89,z6]),(0,[z0,z1,z2,z4,z5,z6,z141])],[(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z142,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z143,z1,z2,z4,z5,z6]),(0,[z0,z17,z1,z56,z2,z4,z5]),(0,[z0,z139,z56,z2,z4,z5,z6])],[(0,[z0,z72,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z125,z31])]],
   [[(0,[z144,z0,z1,z2,z4,z5,z6]),(0,[z145,z63,z0,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z102,z5,z6])],[(0,[z37,z0,z1,z2,z4,z146,z6]),(0,[z147,z0,z2,z4,z5,z18,z6])],[(0,[z0,z148,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z78,z5,z6]),(0,[z0,z1,z2,z149,z4,z5,z6]),(0,[z19,z0,z150,z2,z4,z5,z6])],[(0,[z0,z15,z2,z52,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z89,z6])],[(0,[z0,z2,z4,z151,z5,z18,z6]),(0,[z0,z1,z2,z152,z4,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z153]),(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z0,z1,z2,z4,z156,z5,z6]),(0,[z0,z1,z2,z4,z5,z103,z35])],[(0,[z74,z0,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z18,z6]),(1,[z0,z1,z157,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z18,z6]),(0,[z158,z63,z0,z2,z4,z5,z6]),(0,[z159,z0,z1,z2,z4,z5,z6]),(0,[z160,z0,z2,z4,z5,z6,z31])],[(1,[z161,z1,z2,z4,z5,z6]),(0,[z32,z161,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z162,z6]),(0,[z0,z1,z2,z4,z5,z163,z6]),(0,[z0,z1,z2,z164,z4,z5,z6]),(0,[z0,z1,z165,z2,z4,z5,z6]),(0,[z1,z2,z4,z166,z5,z13,z6]),(0,[z0,z1,z2,z4,z5,z6,z167]),(0,[z0,z1,z2,z4,z5,z168,z6])]],
   [[(0,[z0,z1,z20,z46,z4,z5,z6]),(0,[z0,z1,z2,z169,z4,z5,z6]),(0,[z170,z0,z2,z4,z47,z5,z6]),(0,[z0,z15,z1,z2,z47,z5,z6]),(0,[z171,z0,z1,z2,z4,z5,z6]),(1,[z63,z0,z2,z4,z5,z18]),(0,[z19,z63,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z23,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z172]),(0,[z0,z1,z2,z4,z5,z173,z6])],[(0,[z99,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z174,z5,z6]),(0,[z175,z0,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z176,z47,z5,z6]),(0,[z177,z0,z1,z2,z4,z5,z6])],[(1,[z100,z1,z77,z4,z5,z6]),(0,[z63,z0,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z176,z5,z6]),(0,[z0,z1,z2,z4,z5,z178,z6]),(1,[z68,z63,z0,z2,z4,z5]),(0,[z32,z63,z0,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z89,z6]),(0,[z108,z0,z1,z2,z109,z5,z6]),(0,[z179,z0,z1,z2,z4,z5,z6]),(0,[z0,z180,z2,z36,z4,z5,z6]),(1,[z181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z182,z6])],[(0,[z183,z0,z1,z2,z4,z5,z6]),(1,[z170,z1,z2,z4,z13,z6]),(0,[z184,z0,z2,z4,z47,z5,z6]),(0,[z0,z20,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z185,z4,z5,z6]),(0,[z0,z2,z4,z5,z186,z18,z6])],[(0,[z175,z0,z1,z2,z4,z5,z125]),(0,[z187,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z56,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z188,z5,z6]),(0,[z0,z1,z2,z4,z5,z189,z6])],[(0,[z190,z0,z1,z2,z4,z5,z6]),(0,[z191,z63,z0,z2,z4,z5,z6]),(0,[z0,z1,z192,z2,z4,z5,z6])],[(0,[z0,z1,z2,z193,z4,z5,z6]),(0,[z194,z0,z1,z2,z4,z5,z6]),(0,[z68,z0,z1,z20,z4,z5,z6])]],
   [[(0,[z99,z0,z1,z2,z4,z5,z163]),(0,[z0,z1,z2,z4,z13,z89,z6]),(0,[z40,z0,z1,z2,z4,z166,z6]),(0,[z80,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z118,z2,z4,z5,z6]),(0,[z68,z0,z1,z2,z4,z5,z21]),(0,[z0,z1,z2,z4,z195,z5,z6])],[(0,[z99,z40,z1,z2,z4,z5,z6]),(0,[z100,z0,z1,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z196]),(0,[z63,z0,z1,z2,z4,z5,z87]),(0,[z0,z1,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z198])],[(0,[z0,z1,z2,z4,z199,z5,z6]),(0,[z0,z15,z56,z2,z4,z5,z6]),(0,[z0,z1,z200,z2,z4,z5,z6]),(0,[z108,z0,z201,z2,z4,z5,z6]),(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z203,z0,z1,z2,z4,z5,z6])],[(0,[z68,z100,z0,z1,z4,z5,z6]),(0,[z63,z0,z116,z2,z4,z5,z6]),(1,[z0,z204,z2,z4,z5,z6]),(0,[z0,z1,z205,z2,z4,z5,z6])],[(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z38,z72,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z13,z6,z125]),(0,[z108,z0,z2,z4,z47,z5,z6]),(0,[z0,z1,z207,z2,z4,z5,z6]),(0,[z208,z0,z1,z2,z4,z53,z6])],[(0,[z68,z0,z1,z2,z4,z5,z31])],[(0,[z0,z1,z2,z4,z209,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z34]),(0,[z210,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z118,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z109,z5,z6]),(0,[z0,z2,z36,z4,z5,z18,z6])],[(1,[z0,z211,z2,z4,z5,z6]),(0,[z30,z0,z1,z2,z52,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z212]),(0,[z0,z116,z1,z2,z4,z213,z6]),(0,[z68,z0,z1,z4,z5,z6,z31]),(1,[z0,z2,z4,z5,z6,z214])]],
   [[(0,[z0,z38,z2,z4,z213,z5,z6]),(0,[z0,z1,z2,z4,z5,z215,z6]),(0,[z63,z0,z2,z185,z4,z5,z6]),(1,[z160,z0,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z216]),(0,[z0,z1,z2,z151,z109,z5,z6]),(0,[z101,z0,z1,z2,z132,z5,z6]),(0,[z63,z0,z56,z2,z4,z5,z6])],[(1,[z217,z0,z2,z4,z5,z6]),(1,[z0,z15,z2,z47,z5,z6]),(1,[z218,z0,z2,z4,z5,z6]),(0,[z219,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z67,z6]),(0,[z0,z2,z132,z4,z47,z5,z6]),(0,[z0,z192,z2,z4,z5,z18,z6])],[(0,[z0,z1,z2,z4,z5,z220,z6]),(0,[z221,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z222,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z86,z0,z15,z2,z4,z5,z6]),(0,[z224,z63,z0,z2,z4,z5,z6])],[(0,[z175,z40,z1,z2,z4,z5,z6]),(0,[z63,z0,z118,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z103,z6]),(0,[z225,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z226,z31]),(1,[z227,z1,z2,z4,z5,z6])],[(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z229,z4,z5,z6]),(0,[z230,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z231,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z232,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z233,z5,z6]),(0,[z0,z234,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z235,z5,z6])]],
   [[(0,[z64,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z236]),(0,[z0,z72,z1,z118,z4,z5,z6]),(0,[z32,z0,z1,z2,z237,z5,z6])],[(0,[z40,z0,z1,z2,z4,z13,z6]),(0,[z0,z2,z4,z47,z5,z238,z6]),(1,[z0,z239,z2,z4,z5,z6]),(1,[z0,z1,z58,z4,z5,z6])],[(0,[z0,z2,z46,z4,z5,z18,z6]),(0,[z85,z0,z1,z2,z4,z5,z240]),(0,[z241,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z87])],[(0,[z0,z1,z2,z4,z5,z242,z6])],[(0,[z243,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z244,z5,z6]),(1,[z82,z0,z1,z4,z11,z6])],[(0,[z0,z1,z2,z4,z5,z245,z6]),(0,[z40,z0,z143,z2,z4,z5,z6]),(0,[z82,z0,z2,z4,z47,z5,z6]),(0,[z81,z0,z2,z4,z47,z5,z6]),(0,[z0,z246,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z213,z5,z18,z6]),(0,[z247,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z248]),(0,[z0,z249,z1,z2,z4,z5,z6]),(1,[z0,z1,z250,z4,z5,z6]),(0,[z32,z0,z1,z250,z4,z5,z6])],[(1,[z0,z1,z2,z4,z122,z6]),(0,[z0,z2,z4,z47,z5,z6,z104]),(0,[z68,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z251,z4,z5,z6])],[(0,[z147,z63,z0,z2,z4,z5,z6]),(0,[z68,z147,z0,z1,z2,z4,z5]),(0,[z252,z0,z1,z2,z4,z5,z6]),(0,[z147,z181,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z253,z4,z5,z6]),(0,[z0,z1,z2,z4,z254,z5,z6]),(0,[z64,z0,z2,z4,z47,z5,z6]),(0,[z255,z0,z1,z2,z4,z5,z6]),(1,[z68,z0,z1,z4,z5,z31])],[(0,[z37,z0,z2,z4,z47,z5,z6]),(0,[z256,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z257]),(0,[z85,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z258,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z259]),(0,[z0,z2,z4,z5,z6,z214,z104]),(0,[z0,z1,z2,z260,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z261]),(0,[z0,z1,z2,z262,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z263]),(0,[z32,z0,z1,z2,z4,z5,z263]),(0,[z0,z264,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z265,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z266,z6]),(0,[z0,z72,z118,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z21,z6]),(0,[z63,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z4,z23,z5,z11,z6])],[(0,[z100,z0,z2,z4,z5,z18,z6]),(0,[z85,z0,z1,z2,z151,z5,z6]),(0,[z1,z2,z4,z151,z5,z13,z6]),(0,[z0,z2,z78,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z21]),(0,[z0,z267,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z4,z89,z6])],[(0,[z269,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z46,z4,z109,z5,z6]),(0,[z85,z0,z1,z51,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z270]),(0,[z0,z1,z56,z2,z4,z5,z271]),(0,[z0,z1,z2,z237,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z89,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z122,z6]),(0,[z100,z0,z1,z4,z5,z21,z6]),(0,[z40,z1,z2,z4,z151,z5,z6]),(0,[z0,z2,z4,z47,z5,z11,z6]),(1,[z0,z1,z22,z4,z23,z6]),(0,[z32,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z272,z5,z6]),(0,[z273,z0,z1,z2,z4,z5,z6])],[(0,[z274,z0,z1,z2,z4,z5,z6]),(0,[z85,z1,z77,z2,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z67,z6]),(0,[z0,z246,z15,z2,z4,z5,z6]),(0,[z0,z116,z2,z4,z5,z18,z6]),(0,[z0,z161,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z77,z2,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z0,z2,z4,z47,z5,z35,z6]),(0,[z0,z1,z2,z4,z276,z5,z6]),(1,[z252,z1,z2,z4,z5,z6]),(0,[z179,z0,z1,z2,z4,z6,z271])],[(0,[z0,z1,z2,z4,z59,z5,z6]),(0,[z0,z277,z1,z2,z4,z5,z6]),(0,[z0,z77,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z216]),(0,[z278,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z153,z6]),(0,[z0,z1,z2,z4,z5,z34,z31])],[(0,[z100,z1,z77,z2,z4,z5,z6]),(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z280]),(0,[z0,z1,z2,z102,z4,z5,z281])],[(0,[z0,z1,z282,z2,z4,z5,z6]),(0,[z0,z15,z2,z237,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z283]),(0,[z0,z1,z2,z4,z284,z5,z6]),(0,[z0,z181,z1,z2,z4,z5,z6])],[(1,[z0,z24,z2,z4,z5,z6]),(0,[z85,z0,z1,z2,z4,z285,z6]),(0,[z175,z1,z2,z4,z5,z34,z6]),(1,[z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z2,z4,z5,z286,z6]),(0,[z68,z0,z1,z2,z4,z43,z5]),(0,[z0,z1,z2,z287,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z271,z104]),(0,[z0,z42,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z215,z6,z125]),(0,[z0,z1,z2,z288,z4,z5,z6]),(0,[z0,z1,z2,z137,z52,z4,z5]),(0,[z218,z0,z1,z2,z4,z5,z6]),(0,[z208,z0,z2,z4,z5,z53,z6]),(0,[z0,z2,z4,z5,z289,z11,z6])],[(0,[z74,z0,z2,z4,z47,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z6]),(0,[z290,z0,z1,z2,z4,z5,z6]),(0,[z170,z1,z2,z4,z5,z13,z6]),(0,[z0,z1,z2,z291,z4,z5,z6]),(0,[z0,z1,z2,z292,z4,z5,z6]),(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z0,z1,z2,z4,z5,z294,z6]),(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z296,z6])],[(1,[z0,z1,z2,z4,z5,z134]),(0,[z297,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z0,z1,z2,z57,z4,z5,z6])]],
   [[(0,[z99,z1,z2,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z299]),(1,[z0,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z23,z5,z6]),(0,[z32,z0,z15,z2,z4,z5,z6]),(0,[z108,z0,z1,z20,z4,z5,z6]),(0,[z0,z1,z2,z4,z300,z5,z6])],[(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z301,z5,z6]),(0,[z274,z0,z15,z2,z4,z5,z6]),(0,[z302,z0,z1,z2,z4,z5,z6]),(1,[z10,z0,z2,z4,z5,z6]),(0,[z303,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z304])],[(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z17,z1,z2,z4,z5,z34]),(1,[z80,z0,z52,z4,z5,z6]),(0,[z101,z0,z1,z2,z47,z5,z6]),(0,[z63,z0,z2,z237,z4,z5,z6]),(0,[z160,z0,z1,z2,z4,z5,z6]),(0,[z147,z227,z1,z2,z4,z5,z6])],[],[(0,[z37,z74,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z166,z88,z6]),(0,[z0,z1,z2,z4,z5,z306,z6]),(0,[z0,z1,z2,z4,z5,z307,z6])],[(0,[z0,z1,z2,z4,z146,z5,z6]),(1,[z40,z1,z2,z4,z166,z6]),(1,[z0,z2,z4,z73,z5,z6]),(0,[z0,z2,z4,z88,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z308,z6]),(1,[z0,z1,z4,z195,z5,z6])],[(1,[z0,z1,z2,z4,z146,z6]),(0,[z37,z0,z38,z2,z4,z5,z6]),(0,[z0,z1,z2,z309,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z310,z6]),(0,[z0,z2,z4,z47,z311,z5,z6]),(0,[z0,z1,z20,z102,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z312,z6]),(0,[z0,z1,z313,z2,z4,z5,z6])]],
   [[(0,[z99,z0,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z314,z5,z6]),(0,[z0,z315,z1,z2,z4,z5,z6]),(0,[z0,z1,z316,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z317,z6]),(0,[z0,z2,z4,z47,z5,z34,z6]),(0,[z208,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z318,z18,z6]),(0,[z0,z1,z2,z4,z319,z5,z6]),(1,[z0,z320,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z1,z2,z4,z5,z322,z6]),(0,[z0,z1,z2,z323,z4,z5,z6])],[(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z324,z2,z4,z5,z6]),(0,[z325,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z263])],[(0,[z0,z1,z2,z4,z5,z83,z6]),(0,[z326,z0,z1,z2,z4,z5,z6]),(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z12,z0,z15,z2,z4,z5,z6]),(0,[z170,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z13,z6]),(0,[z227,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z328,z5,z6]),(0,[z0,z2,z4,z47,z43,z5,z6]),(0,[z0,z56,z2,z4,z5,z18,z6]),(1,[z0,z2,z4,z114,z5,z6])],[(0,[z329,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z330,z47,z5,z6]),(0,[z10,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z331]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z332,z1,z2,z4,z5,z6]),(0,[z333,z0,z1,z2,z4,z5,z6]),(0,[z0,z20,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z334]),(0,[z0,z335,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z336]),(0,[z0,z1,z2,z4,z5,z6,z337])],[(0,[z194,z0,z2,z4,z47,z5,z6]),(0,[z0,z2,z4,z47,z5,z338,z6]),(0,[z0,z1,z2,z4,z5,z6,z339])]],
   [[(0,[z0,z38,z1,z2,z4,z5,z6]),(0,[z74,z1,z28,z2,z4,z5,z6]),(0,[z208,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z151,z5,z6]),(0,[z80,z0,z2,z4,z47,z5,z6]),(0,[z340,z0,z1,z2,z4,z5,z6]),(0,[z0,z341,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z342,z4,z5,z6]),(0,[z0,z1,z2,z4,z343,z5,z6]),(0,[z0,z15,z2,z4,z5,z13,z6]),(0,[z0,z1,z2,z4,z166,z23,z6]),(0,[z344,z0,z2,z4,z5,z18,z6]),(0,[z0,z345,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z346])],[(0,[z0,z1,z2,z4,z5,z6,z347]),(0,[z85,z0,z1,z157,z4,z5,z6]),(0,[z0,z1,z2,z4,z348,z5,z6]),(0,[z0,z1,z2,z4,z349,z5,z6]),(0,[z0,z180,z1,z2,z4,z5,z6])],[(0,[z74,z0,z38,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z163]),(0,[z0,z1,z2,z4,z5,z350,z6]),(0,[z0,z211,z1,z2,z4,z5,z6]),(0,[z208,z0,z15,z2,z4,z5,z6]),(0,[z351,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z352])],[(1,[z0,z1,z2,z4,z220,z6]),(0,[z0,z2,z4,z5,z18,z6,z125]),(0,[z0,z56,z2,z4,z47,z5,z6]),(0,[z68,z63,z0,z2,z4,z5,z6]),(0,[z353,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z186,z6]),(0,[z354,z0,z1,z2,z4,z5,z6])],[(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z356,z6]),(1,[z0,z1,z2,z237,z88,z6])],[(0,[z0,z1,z2,z4,z5,z6,z134]),(1,[z0,z357,z2,z4,z5,z6]),(0,[z85,z63,z0,z2,z4,z5,z6]),(0,[z358,z0,z15,z2,z4,z5,z6]),(0,[z63,z0,z324,z2,z4,z5,z6]),(0,[z108,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z359,z6])]],
   [[(0,[z0,z1,z2,z360,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z361,z6]),(0,[z63,z0,z2,z4,z5,z13,z6]),(0,[z40,z1,z2,z4,z166,z5,z6]),(0,[z0,z1,z2,z4,z362,z5,z6]),(0,[z0,z1,z2,z363,z4,z5,z6]),(0,[z0,z1,z2,z364,z4,z5,z6]),(0,[z0,z2,z237,z4,z349,z5,z6])],[(0,[z0,z1,z365,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z366,z6]),(0,[z0,z1,z367,z2,z4,z5,z6]),(0,[z123,z1,z2,z4,z109,z5,z6])],[(0,[z0,z38,z15,z2,z4,z5,z6]),(0,[z0,z368,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z226]),(0,[z0,z2,z4,z5,z238,z35,z6])],[(0,[z369,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z370,z6]),(0,[z0,z1,z2,z4,z5,z6,z125]),(0,[z371,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z372]),(0,[z63,z0,z2,z4,z5,z6,z6])],[(0,[z373,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z4,z47,z5,z6]),(0,[z0,z2,z4,z47,z374,z5,z6]),(0,[z375,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z376,z2,z4,z5,z6])],[(0,[z86,z0,z1,z2,z4,z5,z6]),(0,[z377,z0,z1,z2,z4,z5,z6]),(0,[z175,z0,z282,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z378,z6]),(0,[z147,z0,z15,z2,z4,z5,z6]),(0,[z379,z63,z0,z2,z4,z5,z6]),(0,[z0,z2,z102,z4,z276,z5,z6]),(0,[z0,z1,z2,z4,z5,z61,z6]),(0,[z0,z1,z2,z4,z380,z5,z6])],[(0,[z0,z1,z77,z2,z4,z5,z6]),(0,[z85,z99,z1,z2,z4,z5,z6]),(0,[z381,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z153]),(0,[z0,z1,z2,z4,z5,z382,z6]),(0,[z0,z2,z132,z4,z5,z18,z6]),(0,[z0,z2,z4,z5,z53,z18,z6]),(1,[z63,z0,z56,z2,z4,z5]),(0,[z0,z2,z237,z4,z5,z18,z6]),(0,[z0,z1,z201,z2,z4,z5,z6])],[(0,[z40,z0,z2,z4,z47,z5,z6]),(0,[z383,z0,z1,z2,z4,z5,z6]),(0,[z384,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z385]),(0,[z386,z0,z1,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z125]),(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z47,z5,z6]),(0,[z0,z2,z4,z5,z11,z18,z6]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z388,z6]),(0,[z0,z1,z2,z4,z5,z6,z389])],[(0,[z0,z1,z2,z78,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z6,z125]),(0,[z0,z1,z2,z4,z43,z5,z125]),(0,[z390,z63,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z240,z6]),(0,[z0,z1,z2,z4,z43,z5,z34]),(0,[z0,z1,z2,z4,z5,z391,z6]),(0,[z0,z2,z4,z5,z286,z18,z6]),(0,[z0,z1,z2,z4,z5,z248,z6])],[(0,[z0,z1,z2,z392,z4,z5,z6]),(0,[z0,z1,z2,z132,z4,z5,z6]),(0,[z0,z2,z4,z393,z47,z5,z6]),(0,[z394,z63,z0,z2,z4,z5,z6])],[(0,[z0,z15,z77,z2,z4,z5,z6]),(0,[z0,z1,z2,z395,z4,z5,z6]),(0,[z80,z208,z0,z2,z4,z5,z6])],[(0,[z396,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z31]),(0,[z397,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z398,z6]),(0,[z147,z0,z1,z2,z4,z5,z103])],[(0,[z85,z0,z1,z2,z4,z5,z216]),(0,[z0,z1,z2,z4,z399,z5,z6]),(0,[z40,z0,z223,z2,z4,z5,z6]),(0,[z0,z15,z2,z4,z47,z5,z6]),(0,[z0,z2,z237,z4,z47,z5,z6])],[(0,[z400,z0,z1,z2,z4,z5,z6]),(0,[z0,z401,z1,z2,z4,z5,z6]),(0,[z0,z15,z2,z78,z4,z5,z6]),(0,[z402,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z403,z6]),(0,[z0,z1,z404,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z405])]],
   [[(0,[z99,z0,z1,z2,z4,z5,z385]),(0,[z63,z0,z2,z4,z5,z6,z125]),(0,[z406,z0,z1,z4,z5,z6,z125]),(0,[z0,z1,z407,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z408]),(0,[z409,z0,z1,z2,z4,z5,z6]),(0,[z82,z0,z2,z4,z5,z18,z6]),(0,[z0,z2,z4,z5,z18,z6,z271]),(0,[z19,z0,z1,z2,z5,z6,z271])],[(0,[z0,z118,z2,z52,z4,z5,z6]),(0,[z0,z410,z1,z2,z4,z5,z6]),(0,[z0,z15,z2,z132,z4,z5,z6]),(0,[z0,z22,z2,z4,z5,z18,z6]),(0,[z0,z411,z1,z2,z4,z5,z6]),(0,[z121,z0,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z213,z5,z6]),(0,[z412,z0,z1,z2,z4,z5,z6]),(0,[z101,z0,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z88,z5,z6]),(0,[z0,z2,z4,z47,z213,z5,z6]),(0,[z0,z1,z2,z4,z5,z413,z6])],[(0,[z63,z0,z77,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z414,z5,z6]),(0,[z415,z63,z0,z2,z4,z5,z6])],[(0,[z37,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z22,z2,z4,z5,z6])],[(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z417,z0,z1,z2,z4,z5,z6]),(0,[z85,z0,z1,z2,z4,z418,z6]),(0,[z217,z0,z1,z2,z4,z5,z6]),(1,[z0,z72,z118,z4,z5,z6]),(0,[z63,z0,z2,z4,z47,z5,z6]),(0,[z0,z2,z4,z5,z18,z6,z259]),(0,[z0,z419,z2,z102,z4,z5,z6]),(0,[z82,z0,z1,z4,z5,z11,z6]),(0,[z0,z1,z2,z420,z4,z5,z6]),(0,[z303,z1,z2,z4,z23,z5,z6]),(0,[z0,z421,z1,z2,z4,z5,z6]),(0,[z0,z1,z56,z2,z4,z5,z35]),(0,[z422,z0,z2,z4,z5,z6,z271]),(0,[z0,z423,z1,z2,z4,z5,z6])],[(0,[z424,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z2,z78,z4,z5,z6]),(0,[z64,z1,z2,z4,z5,z6,z125]),(0,[z0,z15,z2,z4,z5,z6,z408])],[(0,[z0,z2,z78,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z425,z6]),(1,[z175,z1,z2,z4,z5,z34]),(0,[z0,z2,z52,z4,z5,z18,z6]),(0,[z145,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z426,z6]),(0,[z0,z1,z2,z4,z5,z6,z271])]],
   [[(0,[z0,z38,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z427]),(0,[z63,z0,z2,z132,z4,z5,z6]),(0,[z0,z1,z2,z4,z428,z5,z6]),(0,[z82,z0,z1,z2,z4,z11,z6])],[(1,[z99,z1,z46,z4,z5,z6]),(0,[z12,z0,z1,z2,z78,z5,z6]),(0,[z170,z63,z0,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z215,z6]),(1,[z406,z0,z1,z4,z5,z6]),(0,[z0,z22,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z429,z5,z6])],[(0,[z0,z430,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z431,z5,z6]),(0,[z0,z15,z22,z2,z4,z5,z6]),(0,[z208,z0,z116,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z238,z18,z6]),(1,[z1,z2,z4,z432,z5,z6])],[(0,[z0,z1,z2,z433,z4,z5,z6]),(0,[z0,z1,z2,z4,z434,z5,z6]),(0,[z82,z0,z1,z2,z4,z23,z6]),(0,[z0,z1,z2,z4,z5,z6,z435]),(1,[z0,z42,z2,z4,z5,z6])],[(0,[z0,z77,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z238,z6]),(0,[z158,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z436,z6])],[(1,[z0,z223,z2,z4,z5,z6]),(0,[z0,z1,z437,z2,z4,z5,z6]),(0,[z218,z0,z2,z4,z47,z5,z6]),(0,[z0,z15,z2,z4,z5,z6,z271]),(0,[z0,z1,z2,z4,z5,z6,z87]),(0,[z0,z1,z20,z2,z4,z5,z6])],[(0,[z0,z1,z438,z2,z4,z5,z6]),(1,[z0,z1,z323,z4,z5,z6]),(0,[z32,z0,z1,z323,z4,z5,z6])],[(0,[z439,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z52,z4,z47,z5,z6]),(0,[z0,z17,z1,z2,z4,z5,z6]),(0,[z82,z0,z1,z22,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z440,z2,z4,z5,z6]),(0,[z0,z1,z441,z2,z4,z5,z6]),(0,[z442,z0,z1,z2,z4,z5,z6]),(0,[z443,z0,z1,z2,z4,z5,z6]),(0,[z0,z444,z2,z4,z47,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z0,z419,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z445]),(0,[z0,z1,z150,z2,z4,z5,z6]),(1,[z121,z0,z2,z4,z5,z6])],[(0,[z74,z0,z2,z4,z5,z18,z6]),(0,[z14,z63,z0,z2,z4,z5,z6]),(0,[z63,z0,z22,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z289,z6]),(0,[z0,z1,z2,z4,z5,z6,z104])],[(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z447,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z448,z6])],[(0,[z0,z1,z77,z4,z109,z5,z6]),(0,[z0,z72,z2,z4,z47,z5,z6]),(0,[z0,z15,z20,z2,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z6,z87]),(0,[z32,z252,z1,z2,z4,z5,z6])],[(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z208,z0,z118,z2,z4,z5,z6]),(0,[z0,z15,z438,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z6,z271]),(0,[z63,z0,z17,z2,z4,z5,z6]),(0,[z0,z320,z1,z2,z4,z5,z6])],[(0,[z63,z100,z0,z2,z4,z5,z6]),(0,[z208,z0,z1,z2,z4,z166,z6]),(0,[z191,z0,z1,z2,z4,z5,z6]),(0,[z108,z63,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z450,z6])],[(0,[z0,z1,z2,z4,z5,z6,z451]),(0,[z0,z1,z20,z77,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z452,z0,z1,z2,z4,z5,z6]),(0,[z14,z0,z2,z4,z5,z35,z6]),(0,[z147,z0,z1,z2,z4,z5,z104]),(0,[z453,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z454,z4,z5,z6])],[(1,[z0,z143,z2,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z6,z104]),(0,[z0,z1,z2,z4,z5,z6,z455]),(0,[z0,z2,z4,z5,z6,z389,z271])]],
   [[(0,[z0,z1,z2,z4,z5,z456,z6]),(0,[z0,z1,z2,z4,z166,z103,z6]),(0,[z64,z0,z1,z2,z4,z5,z34]),(1,[z101,z0,z2,z47,z5,z6]),(0,[z457,z0,z1,z2,z4,z5,z6]),(0,[z68,z0,z1,z56,z4,z5,z6])],[(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z459,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z460,z5,z6]),(0,[z0,z1,z2,z461,z4,z5,z6]),(0,[z0,z118,z2,z4,z47,z5,z6]),(0,[z19,z0,z15,z2,z4,z5,z6]),(0,[z0,z17,z15,z2,z4,z5,z6]),(0,[z63,z0,z1,z56,z2,z4,z5])],[(0,[z63,z0,z38,z2,z4,z5,z6]),(0,[z0,z1,z462,z2,z4,z5,z6]),(0,[z175,z0,z2,z4,z47,z5,z6]),(0,[z68,z0,z15,z2,z4,z5,z6]),(0,[z63,z0,z20,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z6,z87]),(1,[z0,z2,z4,z5,z6,z259]),(0,[z0,z463,z1,z2,z4,z5,z6])],[(0,[z1,z2,z78,z4,z151,z5,z6]),(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z465,z5,z6]),(0,[z0,z1,z2,z4,z5,z35,z6])],[(1,[z85,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z466]),(0,[z0,z17,z1,z2,z4,z5,z125]),(0,[z0,z15,z2,z4,z4,z5,z6])],[(0,[z85,z0,z15,z2,z4,z5,z6]),(0,[z467,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z102,z4,z47,z5,z6]),(0,[z0,z468,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z469,z6]),(0,[z0,z1,z470,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z471])],[(0,[z63,z0,z2,z4,z5,z6,z104]),(0,[z108,z0,z204,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z472,z6])],[(0,[z0,z1,z473,z2,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z100,z0,z1,z77,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z166,z6]),(0,[z0,z1,z2,z474,z4,z5,z6]),(0,[z394,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z475,z6]),(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z477])]],
   [[(1,[z74,z28,z2,z4,z5,z6]),(0,[z100,z0,z15,z2,z4,z5,z6]),(0,[z63,z12,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z166,z5,z6]),(0,[z0,z15,z2,z4,z5,z298,z6]),(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z479,z0,z1,z2,z4,z5,z6])],[(0,[z0,z480,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z34,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z111]),(0,[z0,z15,z2,z4,z5,z35,z6]),(0,[z0,z1,z2,z4,z5,z6,z481]),(0,[z0,z1,z22,z4,z109,z5,z6]),(0,[z0,z1,z2,z482,z4,z5,z6]),(1,[z0,z2,z4,z276,z5,z6]),(1,[z0,z1,z2,z4,z5,z248]),(0,[z0,z1,z56,z4,z5,z21,z6]),(0,[z147,z0,z1,z2,z237,z4,z6])],[(0,[z0,z1,z2,z483,z4,z5,z6]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z450,z6]),(0,[z0,z2,z4,z5,z18,z6,z334]),(0,[z0,z2,z4,z5,z18,z6,z6]),(0,[z0,z1,z2,z4,z5,z50,z11]),(0,[z0,z1,z2,z4,z5,z6,z485])],[(0,[z224,z0,z1,z2,z4,z5,z6]),(1,[z64,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z5,z21,z125]),(0,[z0,z1,z2,z4,z5,z6,z486]),(0,[z80,z0,z2,z4,z5,z18,z6]),(0,[z0,z116,z15,z2,z4,z5,z6]),(0,[z63,z63,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z487,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z488])],[(0,[z489,z0,z1,z2,z4,z5,z6]),(1,[z0,z282,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z490,z6]),(0,[z0,z1,z2,z4,z491,z5,z6]),(0,[z0,z1,z58,z36,z4,z5,z6])],[(0,[z492,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z493]),(0,[z0,z494,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z23,z5,z61,z6]),(0,[z0,z1,z2,z4,z5,z120,z6])],[(0,[z208,z0,z1,z2,z4,z13,z6]),(0,[z0,z1,z2,z4,z5,z6,z495]),(0,[z0,z2,z4,z47,z5,z53,z6]),(0,[z82,z63,z0,z2,z4,z5,z6]),(0,[z32,z147,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z496,z4,z5,z6])],[(0,[z0,z1,z497,z2,z4,z5,z6]),(0,[z0,z1,z2,z78,z109,z5,z6]),(0,[z498,z0,z15,z2,z4,z5,z6]),(0,[z0,z1,z499,z2,z4,z5,z6]),(0,[z0,z1,z500,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z35,z125]),(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z0,z116,z72,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z298,z6]),(0,[z63,z0,z2,z4,z5,z35,z6]),(1,[z0,z2,z57,z4,z5,z6])],[(0,[z501,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z166,z11,z6]),(0,[z502,z0,z1,z2,z4,z5,z6]),(0,[z0,z503,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z103,z271])],[(0,[z37,z63,z0,z2,z4,z5,z6]),(0,[z175,z64,z1,z2,z4,z5,z6]),(0,[z504,z0,z1,z2,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z505])],[(0,[z0,z1,z2,z4,z5,z6,z506]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z368,z1,z2,z4,z5,z6]),(0,[z508,z0,z1,z2,z4,z5,z6]),(0,[z0,z509,z1,z2,z4,z5,z6]),(1,[z0,z510,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z511,z5,z6]),(0,[z512,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z6]),(0,[z0,z116,z2,z4,z213,z5,z6]),(0,[z0,z2,z4,z5,z18,z18,z6])],[(0,[z86,z0,z2,z4,z47,z5,z6]),(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z36,z4,z195,z5,z6])],[(1,[z0,z1,z2,z4,z5,z281]),(0,[z515,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z516,z5,z6]),(1,[z0,z503,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z6])],[(0,[z517,z0,z1,z2,z4,z5,z6]),(0,[z0,z116,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z43,z5,z6])]],
   [[(0,[z147,z0,z1,z2,z4,z13,z6]),(0,[z184,z0,z1,z2,z4,z5,z6]),(1,[z208,z0,z2,z4,z53,z6]),(0,[z0,z1,z2,z518,z4,z5,z6]),(0,[z0,z1,z4,z5,z21,z6,z31]),(0,[z519,z0,z1,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z271])],[(0,[z40,z0,z1,z2,z4,z5,z520]),(0,[z0,z1,z20,z2,z102,z5,z6]),(0,[z68,z0,z1,z2,z4,z5,z271]),(0,[z521,z0,z1,z2,z4,z5,z6])],[(0,[z40,z0,z2,z4,z5,z18,z6]),(0,[z0,z15,z2,z4,z5,z34,z6]),(1,[z63,z0,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z5,z338,z6]),(0,[z522,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z523,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z524,z6]),(0,[z0,z1,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z525]),(0,[z0,z204,z1,z2,z4,z5,z6]),(1,[z0,z1,z56,z4,z5,z21])],[(0,[z85,z12,z1,z2,z4,z5,z6]),(0,[z85,z0,z357,z2,z4,z5,z6]),(0,[z406,z0,z1,z2,z4,z5,z6])],[(0,[z40,z1,z2,z4,z5,z6,z125]),(0,[z175,z0,z1,z2,z4,z526,z6]),(0,[z0,z15,z2,z4,z43,z5,z6])],[(0,[z0,z17,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z527,z5,z6]),(1,[z0,z419,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z528]),(0,[z0,z1,z2,z4,z5,z6,z529])],[(0,[z0,z1,z2,z530,z4,z5,z6]),(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z170,z0,z15,z2,z4,z5,z6]),(0,[z400,z0,z2,z4,z47,z5,z6]),(0,[z532,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z4,z103,z6]),(0,[z19,z0,z1,z2,z36,z5,z6])]],
   [[(0,[z40,z1,z77,z2,z4,z5,z6]),(0,[z217,z0,z2,z4,z5,z6,z125]),(0,[z0,z1,z2,z4,z5,z533,z6]),(0,[z0,z1,z2,z4,z5,z534,z6])],[(0,[z0,z1,z2,z4,z535,z5,z6]),(0,[z0,z2,z4,z5,z13,z18,z6]),(0,[z63,z0,z2,z4,z5,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z536]),(0,[z0,z1,z2,z4,z5,z6,z537]),(0,[z0,z15,z2,z4,z5,z524,z6]),(0,[z0,z15,z2,z4,z5,z18,z6]),(0,[z68,z0,z17,z1,z2,z4,z5]),(0,[z538,z0,z1,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z539,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z540,z6]),(1,[z0,z1,z2,z4,z5,z240]),(0,[z0,z1,z2,z541,z4,z5,z6]),(0,[z542,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z543,z5,z6])],[(0,[z544,z0,z1,z2,z4,z5,z6]),(0,[z0,z545,z1,z2,z4,z5,z6]),(0,[z0,z1,z546,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z547]),(1,[z0,z2,z4,z349,z5,z6])],[(0,[z548,z0,z1,z2,z4,z5,z6]),(0,[z0,z549,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z5,z6]),(0,[z0,z2,z4,z166,z5,z18,z6]),(0,[z550,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z43,z5,z6])],[(0,[z0,z1,z2,z4,z551,z5,z6]),(0,[z80,z0,z2,z4,z213,z5,z6]),(0,[z82,z0,z239,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z6]),(1,[z422,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z552,z5,z6]),(0,[z0,z2,z4,z5,z89,z18,z6]),(0,[z0,z1,z2,z237,z4,z88,z6])],[(0,[z37,z38,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z553,z4,z5,z6]),(0,[z0,z1,z2,z554,z4,z5,z6]),(0,[z0,z1,z2,z4,z374,z5,z6]),(0,[z32,z0,z1,z2,z4,z88,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z520]),(0,[z63,z0,z2,z4,z5,z18,z6])],[(0,[z0,z1,z555,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z556,z6]),(0,[z0,z1,z2,z4,z5,z6,z557]),(0,[z0,z1,z2,z4,z43,z5,z103])],[(1,[z0,z365,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z540,z6]),(0,[z0,z15,z2,z46,z4,z5,z6])],[(0,[z85,z0,z1,z2,z78,z5,z6]),(1,[z14,z0,z2,z4,z5,z6]),(0,[z0,z558,z15,z2,z4,z5,z6]),(0,[z108,z0,z15,z2,z4,z5,z6]),(0,[z0,z15,z2,z36,z4,z5,z6]),(0,[z0,z1,z22,z4,z23,z5,z6]),(1,[z0,z2,z4,z5,z6,z226])],[(0,[z0,z15,z1,z2,z132,z5,z6]),(0,[z0,z2,z4,z5,z18,z103,z6]),(0,[z0,z1,z2,z4,z109,z5,z6]),(0,[z0,z1,z2,z4,z559,z5,z6]),(1,[z32,z0,z1,z2,z89,z6])],[(0,[z0,z1,z560,z2,z4,z5,z6]),(0,[z0,z1,z561,z2,z4,z5,z6]),(0,[z562,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z432,z109,z5,z6])],[(0,[z0,z1,z2,z563,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z564,z6]),(0,[z0,z2,z4,z213,z5,z53,z6]),(0,[z0,z1,z2,z4,z5,z6,z281]),(0,[z0,z1,z2,z4,z5,z35,z104])],[(0,[z0,z1,z2,z565,z4,z5,z6]),(0,[z0,z1,z2,z4,z566,z5,z6]),(0,[z0,z1,z567,z2,z4,z5,z6]),(0,[z0,z2,z4,z109,z5,z18,z6]),(1,[z0,z201,z2,z4,z5,z6]),(0,[z568,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z88,z5,z6])]],
   [[(0,[z175,z1,z2,z4,z5,z13,z6]),(0,[z0,z1,z2,z569,z4,z5,z6]),(0,[z68,z63,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z31])],[(0,[z99,z0,z2,z4,z5,z18,z6]),(0,[z63,z0,z2,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z151,z5,z6]),(0,[z80,z63,z0,z2,z4,z5,z6]),(1,[z0,z2,z4,z47,z5,z6]),(0,[z32,z0,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z570,z6]),(0,[z0,z2,z4,z5,z18,z6,z87]),(1,[z0,z2,z4,z5,z6,z389])],[(0,[z571,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z572,z6]),(0,[z99,z0,z365,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z573,z6]),(0,[z0,z15,z2,z4,z109,z5,z6]),(0,[z63,z0,z2,z36,z4,z5,z6]),(0,[z574,z0,z1,z2,z4,z5,z6]),(1,[z19,z0,z1,z2,z5,z271])],[(0,[z99,z0,z1,z4,z5,z21,z6]),(0,[z170,z40,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z575,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z103,z6]),(0,[z0,z1,z2,z4,z5,z6,z576])],[(0,[z0,z1,z2,z4,z5,z6,z577]),(1,[z0,z1,z2,z4,z285,z6]),(0,[z12,z0,z2,z4,z5,z18,z6]),(0,[z578,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z495,z125]),(0,[z0,z1,z2,z4,z5,z6,z579]),(0,[z0,z1,z56,z2,z4,z5,z21]),(0,[z580,z0,z1,z2,z4,z5,z6])],[(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z418,z6]),(0,[z0,z1,z2,z4,z5,z582,z6]),(0,[z0,z116,z1,z2,z4,z166,z6]),(0,[z64,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z271]),(0,[z0,z1,z2,z4,z213,z5,z6]),(0,[z0,z2,z4,z5,z18,z6,z104]),(0,[z0,z1,z2,z4,z88,z5,z6]),(1,[z0,z1,z2,z4,z6,z471])],[(0,[z0,z1,z2,z4,z285,z5,z6]),(0,[z0,z1,z2,z583,z4,z5,z6]),(0,[z0,z72,z2,z4,z5,z18,z6]),(0,[z0,z15,z2,z4,z5,z6,z31]),(0,[z584,z0,z1,z2,z4,z5,z6]),(0,[z585,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z586,z6])],[(0,[z12,z0,z1,z2,z151,z5,z6]),(0,[z0,z15,z2,z4,z151,z5,z6]),(0,[z0,z2,z4,z587,z5,z18,z6]),(0,[z384,z0,z1,z2,z4,z5,z11]),(1,[z303,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z36,z5,z35])]],
   [[(0,[z588,z0,z1,z2,z4,z5,z6]),(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z17,z1,z2,z4,z5,z18]),(0,[z0,z590,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z591,z6]),(0,[z0,z1,z2,z4,z5,z592,z6]),(0,[z0,z1,z2,z4,z6,z471,z271]),(0,[z147,z0,z1,z2,z4,z43,z6])],[(0,[z37,z0,z1,z2,z4,z5,z83]),(0,[z99,z0,z2,z4,z47,z5,z6]),(0,[z0,z15,z2,z4,z5,z103,z6]),(0,[z63,z0,z2,z4,z109,z5,z6]),(0,[z0,z1,z56,z2,z4,z5,z31]),(0,[z0,z1,z2,z4,z593,z5,z6]),(1,[z147,z0,z1,z2,z4,z104])],[(0,[z0,z28,z2,z52,z4,z5,z6]),(0,[z594,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z89,z6]),(1,[z0,z116,z2,z4,z213,z6]),(0,[z0,z2,z4,z5,z18,z21,z6]),(0,[z595,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z120]),(0,[z0,z1,z2,z4,z5,z6,z596])],[(0,[z0,z2,z78,z4,z79,z5,z6]),(0,[z0,z1,z2,z4,z5,z597,z6]),(1,[z0,z1,z4,z5,z6,z495]),(0,[z0,z15,z2,z4,z88,z5,z6]),(0,[z0,z15,z2,z4,z213,z5,z6]),(0,[z68,z0,z1,z2,z4,z5,z6])],[(1,[z0,z45,z2,z4,z5,z6]),(0,[z12,z0,z2,z4,z47,z5,z6]),(0,[z598,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z318,z6]),(0,[z0,z118,z2,z4,z5,z18,z6]),(0,[z82,z0,z15,z2,z4,z5,z6]),(0,[z208,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z599,z6])],[(0,[z0,z2,z4,z47,z5,z13,z6]),(0,[z0,z1,z2,z600,z4,z5,z6]),(0,[z175,z0,z2,z4,z5,z18,z6]),(0,[z63,z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z601,z2,z4,z5,z6]),(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z63,z0,z2,z569,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z6,z31]),(0,[z0,z1,z2,z4,z5,z603,z6])],[(0,[z0,z468,z1,z2,z4,z5,z6]),(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z85,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z151,z5,z6]),(0,[z0,z1,z2,z4,z605,z5,z6]),(0,[z606,z0,z1,z2,z4,z5,z6])],[(0,[z64,z0,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z35,z6]),(1,[z384,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z607,z6])]],
   [[(0,[z37,z0,z15,z2,z4,z5,z6]),(0,[z0,z357,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z608,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z520]),(0,[z40,z63,z0,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z103,z6]),(0,[z0,z2,z102,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z609]),(0,[z0,z1,z2,z5,z35,z6,z271])],[(0,[z100,z0,z1,z2,z4,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z34,z6,z125]),(0,[z0,z1,z2,z4,z5,z6,z611]),(0,[z0,z2,z4,z5,z18,z6,z612]),(0,[z0,z2,z433,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z21,z6]),(0,[z613,z0,z1,z2,z4,z5,z6]),(0,[z0,z510,z1,z2,z4,z5,z6]),(0,[z0,z2,z36,z4,z114,z5,z6])],[(0,[z64,z0,z1,z2,z4,z5,z125]),(0,[z63,z0,z2,z4,z213,z5,z6]),(0,[z63,z0,z2,z4,z88,z5,z6]),(0,[z0,z2,z4,z43,z5,z18,z6]),(0,[z0,z1,z2,z4,z43,z5,z104])],[(0,[z0,z38,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z614,z5,z6]),(0,[z0,z2,z4,z47,z343,z5,z6]),(0,[z0,z1,z2,z615,z4,z5,z6]),(0,[z340,z0,z2,z4,z5,z18,z6])],[(0,[z379,z0,z1,z2,z4,z5,z6]),(0,[z99,z0,z45,z2,z4,z5,z6]),(0,[z85,z0,z24,z2,z4,z5,z6]),(0,[z0,z1,z616,z2,z4,z5,z6]),(0,[z208,z0,z2,z4,z47,z5,z6]),(0,[z0,z116,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z11,z6])],[(1,[z0,z2,z4,z5,z238,z6]),(0,[z0,z1,z2,z4,z5,z617,z6]),(0,[z82,z0,z320,z2,z4,z5,z6])],[(0,[z618,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z75,z5,z6]),(0,[z0,z116,z1,z2,z4,z13,z6]),(0,[z0,z1,z2,z4,z13,z103,z6]),(0,[z0,z1,z2,z4,z5,z125,z271]),(0,[z0,z1,z2,z619,z4,z5,z6]),(0,[z620,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z621]),(0,[z622,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z271]),(0,[z147,z0,z1,z2,z4,z6,z104])],[(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z21,z6]),(0,[z0,z1,z2,z4,z5,z624,z6]),(0,[z0,z1,z2,z4,z5,z625,z6])]],
   [[(0,[z390,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z393,z5,z6]),(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z612]),(0,[z0,z1,z22,z20,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z627]),(0,[z170,z0,z1,z2,z4,z166,z6]),(0,[z0,z1,z2,z4,z5,z6,z628]),(0,[z0,z1,z2,z629,z4,z5,z6]),(0,[z0,z1,z2,z4,z630,z5,z6]),(0,[z0,z1,z2,z4,z631,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z632]),(1,[z0,z150,z2,z4,z5,z6])],[(0,[z0,z1,z2,z633,z4,z5,z6]),(0,[z0,z1,z2,z4,z634,z5,z6]),(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z0,z1,z2,z4,z330,z5,z6]),(0,[z0,z15,z2,z4,z5,z11,z6]),(1,[z0,z2,z4,z5,z289,z6])],[(0,[z0,z38,z2,z4,z47,z5,z6]),(0,[z0,z2,z4,z131,z47,z5,z6]),(0,[z0,z1,z102,z4,z109,z5,z6]),(1,[z0,z2,z4,z5,z448,z6])],[(0,[z0,z1,z2,z4,z5,z636,z6]),(1,[z0,z1,z2,z4,z526,z6])],[(0,[z74,z0,z15,z2,z4,z5,z6]),(0,[z85,z1,z2,z4,z151,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z125]),(0,[z0,z1,z2,z637,z4,z5,z6]),(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z639,z6])],[(0,[z99,z0,z1,z2,z75,z5,z6]),(0,[z0,z1,z2,z4,z5,z640,z6]),(0,[z147,z0,z2,z4,z47,z5,z6]),(0,[z0,z1,z641,z2,z4,z5,z6]),(0,[z0,z642,z1,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z21,z6]),(0,[z0,z643,z1,z2,z4,z5,z6]),(0,[z644,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z23,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z214])],[(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z646,z2,z4,z5,z6]),(0,[z0,z211,z2,z78,z4,z5,z6]),(1,[z63,z0,z2,z4,z5,z6]),(0,[z0,z1,z4,z109,z5,z21,z6])]],
   [[(0,[z0,z1,z2,z4,z23,z13,z6]),(0,[z175,z0,z126,z2,z4,z5,z6]),(0,[z86,z0,z2,z4,z5,z18,z6]),(0,[z19,z0,z1,z2,z4,z5,z35])],[(0,[z0,z2,z4,z151,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z647,z6]),(0,[z80,z0,z1,z52,z4,z5,z6]),(0,[z0,z1,z2,z648,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z11,z6]),(1,[z0,z1,z2,z4,z5,z50]),(0,[z68,z0,z1,z2,z4,z5,z35]),(0,[z0,z1,z649,z2,z4,z5,z6])],[(0,[z0,z1,z2,z650,z4,z5,z6]),(0,[z0,z1,z2,z4,z166,z89,z6]),(0,[z175,z0,z1,z2,z4,z5,z34]),(0,[z0,z2,z4,z47,z47,z5,z6]),(0,[z415,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z109,z5,z11,z6])],[(0,[z0,z1,z2,z4,z5,z651,z6]),(0,[z0,z1,z2,z4,z166,z5,z6]),(0,[z0,z1,z2,z652,z4,z5,z6]),(0,[z653,z0,z1,z2,z4,z5,z6]),(0,[z101,z0,z2,z4,z5,z18,z6]),(0,[z0,z1,z654,z2,z4,z5,z6])],[(0,[z37,z0,z1,z2,z4,z220,z6]),(0,[z0,z1,z2,z655,z4,z5,z6]),(0,[z0,z1,z2,z4,z311,z5,z6]),(0,[z0,z15,z2,z4,z23,z5,z6]),(0,[z656,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z587,z5,z6]),(0,[z19,z0,z510,z2,z4,z5,z6])],[(0,[z0,z1,z657,z2,z4,z5,z6]),(0,[z0,z126,z1,z2,z4,z5,z6]),(0,[z0,z1,z658,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z659,z6]),(0,[z0,z1,z2,z4,z5,z660,z6])],[(0,[z99,z68,z0,z1,z4,z5,z6]),(0,[z0,z118,z2,z4,z213,z5,z6]),(0,[z63,z0,z2,z4,z631,z5,z6]),(1,[z0,z470,z2,z4,z5,z6]),(0,[z32,z0,z470,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z661,z5,z6])],[(0,[z0,z1,z2,z4,z540,z5,z6]),(0,[z99,z63,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z13,z11,z6]),(0,[z0,z1,z2,z4,z662,z5,z6]),(0,[z0,z1,z2,z4,z5,z663,z6]),(0,[z0,z1,z2,z4,z5,z664,z6]),(0,[z0,z139,z1,z2,z4,z5,z6])]],
   [[(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z666,z2,z4,z5,z6]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z667,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z668,z4,z5,z6]),(0,[z397,z0,z2,z4,z5,z18,z6]),(0,[z68,z0,z1,z4,z109,z5,z6]),(0,[z0,z1,z239,z2,z4,z5,z6]),(0,[z0,z1,z56,z2,z4,z43,z5]),(1,[z179,z0,z1,z2,z4,z6])],[(0,[z208,z0,z38,z2,z4,z5,z6]),(0,[z99,z0,z1,z46,z4,z5,z6]),(0,[z0,z15,z2,z4,z166,z5,z6]),(0,[z0,z1,z669,z2,z4,z5,z6]),(0,[z670,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z671,z0,z1,z2,z4,z5,z6]),(0,[z672,z0,z1,z2,z4,z5,z6]),(0,[z673,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z674,z6]),(0,[z675,z0,z1,z2,z4,z5,z6]),(0,[z170,z0,z1,z2,z4,z13,z6]),(0,[z0,z1,z2,z102,z4,z5,z6])],[(0,[z0,z1,z2,z4,z676,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z678,z6]),(0,[z101,z0,z2,z4,z47,z5,z6]),(0,[z0,z15,z658,z2,z4,z5,z6]),(0,[z0,z1,z2,z679,z4,z5,z6]),(0,[z63,z0,z2,z4,z23,z5,z6]),(0,[z680,z0,z1,z2,z4,z5,z6]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z682,z2,z4,z5,z6]),(0,[z0,z1,z2,z683,z4,z5,z6])],[(0,[z0,z684,z1,z2,z4,z5,z6]),(0,[z0,z1,z685,z2,z4,z5,z6]),(1,[z63,z0,z2,z4,z5,z125]),(0,[z686,z0,z1,z2,z4,z5,z6]),(0,[z687,z0,z1,z2,z4,z5,z6])],[(0,[z688,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z689,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z690]),(0,[z0,z1,z2,z4,z5,z6,z691]),(0,[z0,z1,z2,z4,z692,z5,z6]),(0,[z344,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z432,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z693]),(0,[z0,z694,z1,z2,z4,z5,z6])],[(0,[z1,z77,z2,z4,z5,z13,z6]),(0,[z80,z0,z15,z2,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z53,z6]),(0,[z0,z2,z4,z5,z18,z6,z695])]],
   [[(0,[z0,z1,z2,z157,z4,z5,z6]),(0,[z63,z0,z2,z4,z166,z5,z6]),(0,[z0,z15,z2,z102,z4,z5,z6]),(0,[z14,z0,z1,z2,z4,z5,z6]),(1,[z0,z463,z2,z4,z5,z6]),(0,[z32,z0,z463,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z526,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z271]),(0,[z0,z1,z2,z696,z4,z5,z6]),(0,[z0,z1,z2,z4,z697,z5,z6]),(0,[z0,z503,z2,z237,z4,z5,z6])],[(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z0,z1,z698,z2,z4,z5,z6]),(0,[z208,z63,z0,z2,z4,z5,z6]),(0,[z147,z0,z1,z56,z2,z4,z5])],[(0,[z699,z0,z1,z2,z4,z5,z6]),(0,[z175,z63,z0,z2,z4,z5,z6]),(0,[z0,z2,z36,z4,z47,z5,z6]),(0,[z670,z0,z15,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z103,z6]),(0,[z422,z0,z1,z2,z4,z5,z6]),(1,[z0,z180,z2,z4,z5,z6])],[(0,[z80,z0,z72,z2,z4,z5,z6]),(0,[z0,z116,z2,z52,z4,z5,z6]),(0,[z0,z558,z1,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z700,z4,z5,z6]),(0,[z0,z2,z4,z43,z5,z448,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z51,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z418,z6]),(0,[z701,z0,z1,z2,z4,z5,z6]),(0,[z30,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z702,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z703,z6]),(0,[z63,z0,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z0,z1,z20,z2,z109,z5,z6]),(0,[z0,z1,z250,z2,z4,z5,z6])],[(0,[z0,z1,z704,z2,z4,z5,z6]),(0,[z99,z1,z2,z4,z5,z13,z6]),(0,[z0,z15,z2,z696,z4,z5,z6]),(0,[z208,z0,z1,z2,z4,z213,z6]),(0,[z63,z0,z643,z2,z4,z5,z6]),(0,[z63,z0,z2,z102,z4,z5,z6]),(0,[z0,z1,z22,z2,z4,z11,z6]),(0,[z0,z1,z2,z705,z4,z5,z6]),(0,[z0,z1,z706,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z4,z5,z707,z6]),(0,[z0,z708,z2,z4,z5,z6]),(0,[z0,z2,z648,z47,z5,z6]),(0,[z0,z2,z4,z47,z5,z248])],[(0,[z709,z0,z2,z4,z5,z6]),(0,[z175,z1,z2,z4,z526,z34]),(0,[z63,z0,z58,z4,z5,z6])],[(0,[z710,z0,z2,z4,z5,z6]),(0,[z0,z711,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z712,z6]),(0,[z0,z1,z2,z4,z5,z713]),(0,[z0,z2,z4,z5,z6,z714]),(0,[z0,z2,z4,z47,z5,z715]),(0,[z716,z0,z2,z4,z5,z6]),(0,[z717,z0,z2,z4,z5,z6]),(0,[z718,z0,z2,z4,z5,z6])],[(0,[z719,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z238,z6]),(0,[z123,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z720])],[(0,[z1,z2,z4,z5,z13,z385]),(0,[z0,z2,z4,z5,z18,z413]),(0,[z394,z0,z324,z4,z5,z6]),(0,[z63,z0,z250,z4,z5,z6]),(0,[z123,z68,z1,z4,z5,z6]),(0,[z721,z0,z2,z4,z5,z6])],[(0,[z384,z0,z1,z2,z4,z166]),(0,[z0,z17,z2,z4,z5,z215])],[(0,[z0,z1,z2,z4,z5,z722])],[(0,[z85,z1,z2,z59,z5,z6]),(0,[z0,z150,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z723,z125]),(0,[z724,z0,z2,z4,z5,z6]),(0,[z161,z1,z2,z4,z89,z6])],[(0,[z0,z1,z2,z59,z5,z163]),(0,[z0,z1,z2,z4,z5,z725]),(0,[z0,z2,z4,z5,z448,z6]),(0,[z147,z0,z2,z4,z18,z104])],[(0,[z40,z1,z2,z59,z5,z6]),(0,[z0,z1,z2,z4,z526,z6]),(0,[z303,z726,z2,z4,z5,z6]),(0,[z0,z2,z36,z114,z5,z35])],[(0,[z550,z38,z2,z4,z5,z6])],[(0,[z406,z0,z1,z4,z5,z21])],[(0,[z63,z0,z2,z4,z5,z6]),(0,[z100,z1,z77,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z727]),(0,[z0,z1,z2,z4,z5,z728]),(0,[z181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z729,z4,z5]),(0,[z68,z63,z0,z2,z4,z5]),(0,[z63,z0,z2,z4,z5,z334])],[(0,[z0,z24,z157,z4,z5,z6]),(0,[z402,z0,z1,z2,z89,z6]),(0,[z0,z72,z324,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z730])]],
   [[(0,[z0,z684,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z220,z83]),(0,[z731,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z461,z5,z35]),(0,[z0,z15,z2,z348,z5,z6])],[(0,[z0,z2,z4,z5,z732,z6]),(0,[z0,z733,z2,z4,z5,z6]),(0,[z0,z1,z2,z734,z5,z6]),(0,[z0,z1,z735,z4,z5,z6]),(0,[z0,z2,z4,z5,z736,z6])],[(0,[z0,z2,z4,z5,z18,z385]),(0,[z1,z737,z46,z4,z5,z6]),(0,[z63,z2,z4,z5,z34,z125]),(0,[z406,z0,z17,z1,z4,z5]),(0,[z0,z2,z5,z35,z6,z259]),(0,[z19,z0,z2,z5,z18,z271])],[(0,[z0,z1,z738,z4,z5,z6]),(0,[z0,z15,z157,z4,z5,z6]),(0,[z32,z161,z1,z2,z89,z6])],[(0,[z0,z1,z2,z4,z5,z739]),(0,[z0,z1,z4,z5,z21,z385]),(0,[z0,z740,z2,z4,z5,z6]),(0,[z0,z4,z47,z195,z5,z6]),(0,[z161,z15,z2,z4,z5,z6])],[(0,[z63,z0,z2,z4,z5,z215]),(0,[z0,z180,z58,z4,z5,z6])],[(0,[z63,z643,z2,z4,z5,z34]),(0,[z218,z0,z2,z4,z5,z111])],[(0,[z63,z0,z2,z4,z5,z134]),(0,[z191,z0,z2,z4,z631,z6])],[(0,[z0,z741,z2,z4,z5,z6]),(0,[z0,z1,z742,z4,z5,z6])],[(0,[z0,z2,z4,z47,z5,z240]),(0,[z170,z15,z2,z4,z13,z6]),(0,[z743,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z744,z5,z6])],[(0,[z179,z0,z1,z56,z2,z4])],[(0,[z63,z0,z2,z4,z5,z372])],[(0,[z0,z1,z2,z4,z5,z745]),(0,[z160,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z573]),(0,[z746,z1,z2,z4,z5,z6]),(0,[z0,z463,z323,z4,z5,z6])],[(0,[z0,z2,z4,z747,z5,z6]),(0,[z0,z1,z2,z4,z5,z748])],[(0,[z0,z282,z2,z4,z526,z6]),(0,[z218,z0,z2,z4,z5,z6]),(0,[z108,z0,z15,z109,z5,z6]),(0,[z63,z0,z2,z4,z5,z248]),(0,[z749,z1,z2,z4,z5,z6])],[(0,[z0,z750,z2,z4,z5,z6]),(0,[z224,z643,z2,z4,z5,z6]),(0,[z0,z2,z4,z751,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z752,z6]),(0,[z0,z2,z4,z5,z6,z753])],[(0,[z227,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z754]),(0,[z0,z755,z2,z4,z5,z6])],[(0,[z0,z2,z756,z4,z5,z6]),(0,[z0,z180,z2,z4,z5,z6]),(0,[z0,z15,z2,z757,z5,z6]),(0,[z68,z63,z0,z324,z4,z5])],[(0,[z467,z38,z2,z4,z5,z6]),(0,[z0,z24,z2,z4,z5,z216]),(0,[z227,z1,z2,z4,z13,z6]),(0,[z758,z1,z2,z4,z5,z6])],[(0,[z99,z365,z46,z4,z5,z6]),(0,[z0,z45,z2,z4,z540,z6]),(0,[z99,z63,z46,z4,z5,z6]),(0,[z0,z2,z4,z5,z759,z153]),(0,[z0,z118,z4,z5,z6,z612]),(0,[z0,z2,z73,z109,z5,z6]),(0,[z0,z17,z2,z4,z5,z760]),(0,[z0,z1,z20,z4,z5,z248])],[(0,[z0,z239,z2,z4,z5,z6]),(0,[z761,z0,z1,z2,z4,z5]),(0,[z762,z15,z2,z4,z5,z6])],[(0,[z0,z1,z555,z4,z23,z6]),(0,[z0,z1,z2,z4,z763,z6]),(0,[z0,z2,z4,z5,z18,z49]),(0,[z0,z764,z2,z4,z5,z6])],[(0,[z0,z2,z4,z146,z18,z6]),(0,[z0,z15,z2,z4,z5,z216]),(0,[z147,z0,z1,z2,z4,z25]),(0,[z179,z422,z0,z2,z4,z6])],[(0,[z0,z1,z2,z59,z122,z6]),(0,[z63,z0,z2,z4,z5,z408]),(0,[z82,z63,z0,z4,z11,z6]),(0,[z108,z1,z432,z109,z5,z6]),(0,[z1,z2,z4,z5,z6,z765])],[(0,[z0,z1,z2,z4,z6,z766]),(0,[z0,z15,z2,z4,z67,z6]),(0,[z179,z0,z2,z4,z18,z6]),(0,[z0,z1,z2,z4,z767,z6])],[(0,[z0,z2,z4,z5,z768,z6]),(0,[z0,z769,z2,z4,z5,z6]),(0,[z0,z770,z2,z4,z5,z6]),(0,[z0,z24,z2,z4,z418,z6]),(0,[z0,z357,z157,z4,z5,z6]),(0,[z123,z1,z2,z78,z5,z6]),(0,[z0,z2,z4,z5,z6,z771])],[(0,[z0,z772,z2,z4,z5,z6])],[(0,[z0,z2,z4,z773,z5,z6]),(0,[z1,z774,z2,z4,z5,z6]),(0,[z775,z0,z2,z4,z47,z6]),(0,[z68,z63,z0,z4,z5,z31]),(0,[z68,z0,z1,z4,z5,z31])],[(0,[z776,z0,z2,z4,z5,z6])],[(0,[z63,z0,z2,z237,z88,z6]),(0,[z0,z1,z2,z4,z777,z6]),(0,[z0,z2,z4,z5,z6,z778])],[(0,[z0,z15,z58,z4,z5,z6]),(0,[z0,z58,z4,z114,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z779,z6]),(0,[z0,z2,z235,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z780]),(0,[z252,z1,z2,z4,z5,z263])],[(0,[z99,z421,z1,z4,z5,z6]),(0,[z406,z0,z1,z4,z43,z5]),(0,[z82,z0,z1,z4,z50,z11]),(0,[z179,z0,z2,z4,z6,z389])],[(0,[z416,z0,z52,z4,z5,z6]),(0,[z0,z781,z2,z4,z5,z6]),(0,[z15,z774,z2,z4,z5,z6]),(0,[z208,z0,z2,z4,z782,z6]),(0,[z68,z63,z0,z20,z4,z5])],[(0,[z1,z2,z4,z151,z418,z6]),(0,[z0,z2,z4,z5,z6,z783]),(0,[z784,z0,z1,z2,z4,z5]),(0,[z0,z15,z2,z785,z4,z5]),(0,[z0,z15,z250,z4,z5,z6]),(0,[z63,z0,z2,z4,z697,z5]),(0,[z0,z1,z4,z786,z5,z6])],[(0,[z0,z2,z4,z79,z5,z6]),(0,[z0,z1,z787,z4,z5,z6]),(0,[z175,z126,z2,z4,z5,z34]),(0,[z0,z2,z4,z5,z788,z6]),(0,[z0,z789,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z83]),(0,[z85,z2,z151,z5,z18,z6]),(0,[z0,z1,z2,z4,z790,z6]),(0,[z63,z0,z2,z4,z5,z87]),(0,[z0,z1,z56,z4,z5,z607])],[(0,[z0,z365,z2,z75,z5,z6])],[(0,[z85,z63,z2,z151,z5,z6]),(0,[z0,z2,z4,z587,z53,z6])],[(0,[z0,z148,z2,z4,z213,z6]),(0,[z63,z0,z2,z4,z5,z385]),(0,[z0,z15,z2,z4,z791,z6]),(0,[z0,z15,z2,z4,z5,z263]),(0,[z208,z0,z2,z4,z450,z6]),(0,[z63,z0,z2,z4,z5,z663]),(0,[z0,z1,z20,z102,z5,z6])],[(0,[z0,z1,z157,z78,z5,z6]),(0,[z0,z2,z4,z5,z792,z6])],[(0,[z85,z1,z51,z151,z5,z6]),(0,[z0,z15,z2,z4,z5,z793])],[(0,[z0,z2,z237,z73,z5,z6])],[(0,[z0,z15,z2,z4,z5,z6]),(0,[z0,z794,z2,z4,z5,z6]),(0,[z0,z1,z56,z4,z5,z795])],[(0,[z37,z38,z2,z4,z146,z6]),(0,[z85,z2,z151,z47,z5,z6]),(0,[z0,z2,z4,z5,z796,z6])],[(0,[z63,z0,z2,z4,z5,z451]),(0,[z0,z357,z2,z4,z5,z216]),(0,[z12,z0,z2,z73,z5,z6]),(0,[z80,z0,z52,z4,z5,z6]),(0,[z390,z0,z185,z4,z5,z6]),(0,[z0,z2,z73,z5,z35,z6]),(0,[z303,z797,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z119])],[(0,[z0,z1,z2,z4,z5,z798]),(0,[z522,z1,z2,z4,z166,z6])]],
   [[(0,[z0,z15,z2,z615,z5,z6]),(0,[z63,z252,z2,z4,z5,z6]),(0,[z68,z160,z0,z2,z4,z5]),(0,[z0,z799,z2,z4,z5,z6])],[],[(0,[z0,z800,z2,z4,z5,z6]),(0,[z0,z15,z2,z137,z4,z5]),(0,[z179,z0,z1,z2,z4,z104]),(0,[z147,z227,z1,z2,z4,z104])],[(0,[z170,z1,z2,z4,z801,z6]),(0,[z0,z2,z4,z47,z526,z6]),(0,[z80,z0,z149,z4,z5,z6])],[(0,[z0,z2,z650,z47,z5,z6]),(0,[z802,z0,z2,z4,z5,z6])],[(0,[z0,z15,z2,z4,z5,z134]),(0,[z0,z357,z2,z4,z418,z6]),(0,[z218,z0,z2,z4,z5,z87]),(0,[z803,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z804,z4,z5]),(0,[z0,z2,z4,z5,z6,z760])],[(0,[z194,z0,z52,z4,z5,z6]),(0,[z0,z2,z4,z805,z5,z6])],[(0,[z0,z1,z2,z4,z5,z806]),(0,[z0,z807,z2,z4,z5,z6]),(0,[z808,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z102,z5,z248]),(0,[z32,z0,z463,z2,z89,z6])],[(0,[z37,z2,z4,z5,z6,z334]),(0,[z0,z1,z2,z4,z809,z6]),(0,[z0,z2,z4,z5,z810,z520]),(0,[z64,z1,z4,z5,z495,z125]),(0,[z63,z0,z2,z4,z5,z481])],[(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z2,z4,z5,z812]),(0,[z129,z0,z1,z2,z5,z271]),(0,[z0,z15,z2,z491,z5,z6]),(0,[z63,z0,z2,z4,z813,z6]),(0,[z161,z1,z323,z4,z5,z6])],[(0,[z0,z2,z59,z814,z5,z6]),(0,[z0,z815,z2,z4,z5,z6]),(0,[z99,z68,z63,z0,z4,z5]),(0,[z40,z15,z2,z4,z166,z6]),(0,[z14,z803,z2,z4,z5,z6]),(0,[z0,z15,z4,z195,z5,z6])],[(0,[z80,z0,z185,z4,z5,z6])],[(0,[z0,z20,z102,z276,z5,z6]),(0,[z816,z0,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z235,z6])],[(0,[z0,z1,z817,z4,z5,z6]),(0,[z0,z2,z4,z73,z5,z125]),(0,[z68,z63,z0,z185,z4,z5]),(0,[z0,z1,z2,z4,z818,z6]),(0,[z68,z0,z1,z185,z4,z5]),(0,[z0,z2,z237,z88,z18,z6]),(0,[z0,z2,z819,z4,z5,z6]),(0,[z820,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z163]),(0,[z1,z77,z737,z4,z5,z6]),(0,[z0,z72,z316,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z18]),(0,[z63,z2,z4,z432,z5,z6]),(0,[z0,z2,z4,z5,z821,z6]),(0,[z0,z822,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z823,z6]),(0,[z63,z0,z4,z5,z6,z495]),(0,[z379,z158,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z760]),(0,[z0,z2,z4,z5,z6,z824]),(0,[z19,z0,z1,z2,z471,z271]),(0,[z147,z0,z2,z4,z214,z104])],[],[(0,[z825,z0,z2,z4,z5,z6]),(0,[z64,z1,z2,z4,z5,z725]),(0,[z123,z1,z2,z4,z5,z826])],[(0,[z0,z357,z2,z4,z5,z6]),(0,[z68,z63,z100,z0,z4,z5]),(0,[z0,z2,z132,z757,z5,z6])],[(0,[z0,z2,z4,z5,z18,z240]),(0,[z396,z1,z2,z4,z13,z6])],[(0,[z0,z2,z4,z285,z18,z6]),(0,[z0,z2,z229,z47,z5,z6]),(0,[z0,z2,z4,z5,z625,z18]),(0,[z0,z1,z102,z827,z5,z6]),(0,[z0,z2,z4,z5,z6,z828])],[(0,[z829,z0,z1,z4,z5,z6]),(0,[z0,z56,z2,z4,z73,z5]),(0,[z0,z2,z4,z5,z6,z830])],[(0,[z63,z0,z4,z5,z495,z125])],[(0,[z0,z831,z2,z4,z5,z6]),(0,[z0,z1,z51,z4,z5,z240])],[(0,[z0,z1,z2,z4,z832,z6]),(0,[z0,z1,z2,z4,z833,z6]),(0,[z834,z0,z2,z4,z5,z6]),(0,[z0,z2,z705,z47,z5,z6]),(0,[z0,z15,z2,z4,z5,z835])],[(0,[z0,z15,z2,z4,z220,z6]),(0,[z0,z1,z2,z4,z5,z153]),(0,[z836,z0,z2,z4,z5,z6])],[(0,[z63,z0,z2,z75,z5,z6]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z0,z838,z2,z4,z5,z6])],[(0,[z0,z839,z2,z4,z5,z6]),(0,[z0,z15,z2,z237,z88,z6]),(0,[z0,z2,z4,z840,z5,z6]),(0,[z841,z384,z0,z2,z4,z5])],[(0,[z0,z1,z2,z4,z842,z6]),(0,[z0,z2,z4,z5,z843,z6])],[(0,[z68,z160,z0,z4,z5,z31]),(0,[z0,z1,z2,z5,z844,z271])],[(0,[z0,z2,z75,z5,z18,z6]),(0,[z218,z0,z2,z4,z5,z18]),(0,[z626,z63,z0,z2,z4,z5])]],
   [[(0,[z63,z0,z2,z845,z5,z6]),(0,[z846,z0,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z847,z6]),(0,[z384,z0,z2,z4,z5,z289]),(0,[z0,z463,z2,z4,z5,z120])],[(0,[z0,z1,z2,z4,z848,z6]),(0,[z0,z15,z2,z47,z5,z6]),(0,[z0,z2,z4,z5,z289,z50])],[(0,[z303,z1,z2,z4,z540,z6]),(0,[z849,z0,z15,z2,z4,z5]),(0,[z0,z1,z2,z4,z850,z6]),(0,[z0,z851,z2,z4,z5,z6]),(0,[z852,z0,z1,z2,z4,z5])],[(0,[z68,z0,z4,z5,z18,z31])],[(0,[z0,z1,z2,z4,z853,z6]),(0,[z0,z1,z2,z4,z854,z6]),(0,[z0,z855,z2,z4,z5,z6]),(0,[z0,z2,z66,z47,z5,z6])],[(0,[z0,z2,z4,z5,z856,z6]),(0,[z0,z72,z857,z4,z5,z6]),(0,[z0,z1,z858,z4,z5,z6])],[(0,[z0,z15,z2,z4,z5,z385]),(0,[z859,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z860,z5,z6]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z862,z2,z4,z5,z6]),(0,[z0,z1,z20,z827,z5,z6]),(0,[z68,z0,z4,z5,z226,z31])],[(0,[z0,z2,z75,z47,z5,z6]),(0,[z82,z0,z4,z47,z11,z6])],[(0,[z0,z1,z2,z4,z801,z6]),(0,[z0,z2,z4,z47,z5,z780]),(0,[z68,z63,z0,z4,z109,z5]),(0,[z32,z0,z2,z89,z18,z6]),(0,[z0,z863,z2,z4,z5,z6]),(0,[z0,z864,z2,z4,z5,z6])],[(1,[z1,z2,z4,z801,z6]),(0,[z40,z1,z2,z4,z166,z153])],[(0,[z0,z1,z865,z4,z5,z6]),(0,[z0,z1,z2,z866,z5,z6])],[(0,[z68,z0,z4,z47,z5,z31]),(0,[z68,z14,z0,z2,z4,z5]),(0,[z82,z0,z1,z4,z11,z6]),(0,[z0,z1,z4,z5,z867,z6]),(0,[z868,z1,z2,z4,z5,z6])],[(0,[z406,z0,z4,z5,z215,z6]),(0,[z0,z2,z4,z5,z869,z6]),(0,[z0,z2,z4,z5,z870,z120])],[(0,[z0,z2,z4,z47,z5,z83]),(0,[z0,z1,z2,z4,z122,z6]),(0,[z406,z63,z0,z4,z5,z6]),(0,[z123,z1,z2,z4,z5,z871]),(0,[z0,z872,z2,z4,z5,z6])],[(0,[z0,z157,z4,z47,z5,z6]),(0,[z0,z1,z873,z4,z5,z6]),(0,[z453,z1,z2,z4,z5,z125]),(0,[z63,z0,z2,z4,z5,z322]),(0,[z63,z181,z2,z4,z5,z6]),(0,[z252,z1,z250,z4,z5,z6]),(0,[z0,z1,z323,z4,z5,z263])],[(0,[z0,z1,z874,z4,z5,z6]),(0,[z875,z63,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z32,z0,z1,z2,z89,z120])]],
   [[(0,[z123,z1,z2,z151,z5,z6]),(0,[z877,z0,z2,z4,z5,z281]),(0,[z32,z0,z1,z250,z89,z6])],[(0,[z10,z0,z2,z4,z166,z6]),(0,[z0,z2,z4,z47,z878,z6])],[(0,[z0,z1,z2,z879,z4,z5]),(0,[z0,z1,z323,z4,z5,z6])],[(0,[z0,z45,z2,z59,z5,z6]),(0,[z0,z880,z2,z4,z5,z6]),(0,[z1,z77,z4,z5,z647,z6]),(0,[z0,z2,z4,z213,z782,z6]),(0,[z63,z0,z56,z4,z5,z21]),(0,[z82,z0,z4,z11,z18,z6])],[(0,[z30,z0,z28,z2,z4,z5]),(0,[z881,z1,z2,z4,z5,z6])],[(0,[z64,z217,z2,z4,z5,z125]),(0,[z175,z15,z2,z4,z5,z34]),(0,[z0,z1,z22,z4,z23,z6])],[(0,[z622,z1,z2,z4,z13,z6]),(0,[z0,z1,z2,z4,z882,z6]),(0,[z63,z0,z2,z4,z5,z760]),(0,[z19,z0,z150,z2,z5,z271]),(0,[z0,z1,z2,z4,z883,z104])],[(0,[z38,z884,z2,z4,z5,z6]),(0,[z99,z15,z46,z4,z5,z6]),(0,[z252,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z885,z6])],[(0,[z175,z1,z2,z4,z5,z725]),(0,[z0,z323,z4,z5,z18,z6]),(0,[z147,z121,z0,z2,z4,z104])],[(0,[z0,z886,z2,z4,z5,z6]),(0,[z0,z2,z4,z887,z5,z6]),(0,[z0,z15,z2,z4,z888,z6]),(0,[z247,z0,z1,z4,z11,z6])],[(0,[z40,z1,z2,z4,z5,z385]),(0,[z889,z0,z1,z2,z4,z5]),(0,[z0,z890,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z240]),(0,[z340,z63,z0,z2,z4,z5]),(0,[z0,z2,z4,z176,z5,z238]),(0,[z0,z1,z2,z891,z5,z6])],[(0,[z0,z143,z2,z4,z5,z6]),(0,[z0,z24,z2,z4,z5,z6]),(0,[z63,z892,z2,z4,z5,z6])],[(0,[z893,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z0,z42,z2,z4,z5,z125]),(0,[z218,z0,z2,z4,z5,z238]),(0,[z147,z218,z0,z2,z4,z5]),(0,[z0,z2,z4,z5,z830,z281])],[(0,[z0,z143,z2,z4,z13,z6]),(0,[z0,z2,z4,z5,z50,z18])],[(0,[z0,z2,z4,z5,z895,z6]),(0,[z896,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z897,z5,z6]),(0,[z0,z15,z2,z4,z898,z6]),(0,[z32,z0,z1,z323,z89,z6])],[(0,[z0,z1,z157,z151,z5,z6]),(0,[z68,z0,z1,z4,z5,z138])]],
   [[(0,[z158,z38,z2,z4,z5,z6]),(0,[z0,z323,z4,z47,z5,z6])],[(0,[z0,z2,z4,z5,z899,z6]),(0,[z0,z2,z4,z5,z6,z900]),(0,[z181,z2,z4,z5,z18,z6])],[(0,[z0,z2,z137,z57,z4,z5]),(0,[z0,z901,z2,z4,z5,z6]),(0,[z0,z2,z4,z902,z5,z6])],[(0,[z903,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z904]),(0,[z0,z905,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z146,z6]),(0,[z63,z0,z51,z4,z5,z6]),(0,[z0,z2,z4,z276,z5,z6]),(0,[z0,z368,z438,z4,z5,z6]),(0,[z906,z0,z2,z4,z5,z6])],[(0,[z85,z24,z2,z151,z5,z6]),(0,[z63,z2,z4,z5,z13,z125]),(0,[z0,z1,z2,z4,z907,z5])],[(1,[z884,z2,z4,z5,z6]),(0,[z0,z1,z157,z4,z285,z6]),(0,[z64,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z5,z908]),(0,[z909,z1,z2,z4,z5,z6]),(0,[z0,z910,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z911])],[(0,[z912,z0,z2,z4,z5,z6]),(0,[z0,z51,z4,z47,z5,z6]),(0,[z0,z1,z4,z5,z6,z913]),(0,[z0,z914,z2,z4,z5,z6]),(0,[z0,z118,z857,z4,z5,z6]),(0,[z181,z2,z4,z47,z5,z6]),(0,[z0,z2,z915,z4,z5,z6])],[(0,[z99,z1,z46,z4,z5,z163]),(0,[z0,z1,z4,z5,z21,z257]),(0,[z85,z15,z2,z151,z5,z6]),(0,[z40,z143,z2,z4,z166,z6]),(0,[z0,z4,z47,z5,z6,z495]),(0,[z30,z0,z2,z4,z5,z18]),(0,[z0,z916,z2,z4,z5,z6]),(0,[z0,z2,z4,z917,z5,z6]),(0,[z0,z726,z2,z4,z5,z6])],[(0,[z0,z2,z4,z114,z5,z6]),(0,[z0,z1,z2,z4,z5,z918])],[(0,[z0,z28,z2,z4,z146,z6]),(0,[z0,z919,z2,z4,z5,z6]),(0,[z0,z1,z827,z109,z5,z6])],[(0,[z0,z22,z4,z23,z18,z6]),(0,[z0,z1,z20,z705,z5,z6]),(0,[z82,z10,z0,z4,z11,z6]),(0,[z0,z920,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z146,z134]),(0,[z644,z1,z77,z4,z5,z6]),(0,[z123,z1,z157,z4,z5,z6]),(0,[z406,z0,z1,z4,z5,z271]),(1,[z0,z2,z757,z5,z6]),(0,[z161,z1,z2,z4,z5,z120])],[(0,[z921,z0,z1,z2,z5,z6]),(0,[z0,z2,z4,z922,z5,z6]),(0,[z0,z15,z2,z4,z5,z248]),(0,[z415,z0,z2,z4,z450,z6])]],
   [[(0,[z40,z2,z4,z166,z18,z6]),(0,[z175,z2,z4,z5,z34,z18]),(0,[z0,z2,z4,z923,z5,z6])],[(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z126,z2,z4,z526,z6]),(0,[z0,z925,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z926]),(0,[z63,z0,z601,z2,z4,z5]),(0,[z0,z927,z2,z4,z5,z6]),(0,[z1,z2,z4,z928,z5,z6])],[(0,[z19,z0,z15,z2,z5,z271]),(0,[z0,z2,z4,z5,z929,z6])],[(0,[z208,z0,z2,z4,z53,z6]),(0,[z227,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z237,z930,z6])],[(0,[z0,z1,z2,z4,z5,z931]),(0,[z0,z2,z4,z5,z932,z6]),(0,[z0,z2,z4,z276,z5,z248])],[(0,[z758,z2,z4,z5,z18,z6]),(0,[z0,z2,z4,z5,z933,z6])],[(0,[z0,z1,z2,z4,z122,z385]),(0,[z406,z0,z1,z4,z5,z385])],[(0,[z93,z1,z2,z4,z13,z6])],[(0,[z0,z2,z59,z5,z18,z6]),(0,[z0,z223,z2,z4,z5,z153]),(0,[z0,z2,z4,z5,z934,z6]),(0,[z935,z0,z2,z4,z5,z6])],[(0,[z0,z419,z2,z4,z5,z6])],[(0,[z0,z1,z59,z5,z21,z6]),(0,[z63,z0,z646,z2,z4,z5]),(0,[z0,z1,z2,z4,z285,z216]),(0,[z936,z1,z2,z4,z5,z6])],[(0,[z884,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z59,z540,z6]),(0,[z0,z2,z5,z238,z6,z259]),(0,[z227,z2,z4,z47,z5,z6]),(0,[z0,z937,z2,z4,z5,z6]),(0,[z0,z1,z938,z4,z5,z6]),(0,[z939,z1,z2,z4,z5,z6])],[(0,[z0,z940,z2,z4,z5,z6]),(0,[z0,z2,z4,z941,z5,z6]),(0,[z0,z942,z2,z4,z5,z6])],[(0,[z0,z365,z2,z4,z122,z6]),(0,[z0,z943,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z13,z153]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z179,z0,z1,z2,z4,z34]),(0,[z945,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z946,z2,z4,z5,z6]),(0,[z0,z2,z4,z176,z5,z18]),(0,[z384,z0,z2,z4,z5,z18]),(0,[z0,z590,z1,z109,z5,z6])],[(0,[z0,z1,z2,z4,z947,z6]),(0,[z0,z2,z59,z47,z5,z6]),(0,[z85,z357,z2,z151,z5,z6]),(0,[z0,z15,z56,z4,z5,z21]),(0,[z0,z2,z4,z948,z5,z6])],[(0,[z0,z949,z2,z4,z5,z6]),(0,[z0,z2,z4,z950,z5,z6]),(0,[z0,z1,z2,z4,z5,z951]),(0,[z0,z2,z4,z952,z5,z6]),(0,[z0,z953,z2,z4,z5,z6]),(0,[z68,z0,z42,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z954]),(0,[z184,z2,z4,z343,z5,z6])],[(0,[z0,z955,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z520]),(0,[z406,z0,z4,z5,z18,z6]),(0,[z0,z956,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z526,z6]),(0,[z957,z0,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z388]),(0,[z32,z0,z1,z2,z89,z263])],[(0,[z0,z2,z4,z47,z122,z6]),(0,[z63,z0,z2,z4,z5,z236]),(0,[z0,z2,z4,z131,z374,z6]),(0,[z958,z1,z2,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z959]),(0,[z0,z2,z4,z5,z6,z960]),(0,[z397,z0,z2,z5,z6,z259])],[(0,[z1,z2,z78,z60,z5,z6]),(0,[z0,z961,z2,z4,z5,z6]),(0,[z68,z0,z2,z4,z73,z5]),(0,[z962,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z18,z83]),(0,[z99,z1,z46,z4,z122,z6]),(0,[z0,z15,z2,z4,z5,z240]),(0,[z0,z15,z2,z16,z5,z6]),(0,[z963,z0,z2,z4,z5,z6]),(0,[z32,z63,z0,z2,z89,z6])],[(0,[z0,z964,z2,z4,z5,z6]),(0,[z100,z1,z737,z4,z5,z6]),(0,[z0,z157,z4,z5,z18,z6])],[(0,[z965,z0,z2,z4,z5,z520]),(0,[z208,z0,z2,z4,z48,z6]),(0,[z0,z419,z2,z4,z5,z248])],[(0,[z0,z1,z2,z4,z5,z966]),(0,[z406,z147,z0,z1,z4,z5]),(0,[z967,z0,z1,z2,z4,z6])],[(0,[z406,z0,z4,z47,z5,z6]),(0,[z154,z0,z2,z47,z5,z6]),(0,[z14,z0,z2,z4,z5,z298]),(0,[z63,z968,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z844])],[],[(0,[z63,z0,z2,z4,z5,z257]),(1,[z406,z63,z0,z4,z5]),(0,[z422,z0,z2,z4,z5,z125]),(0,[z1,z2,z4,z5,z969,z6])],[(0,[z0,z1,z970,z4,z5,z6]),(0,[z598,z0,z1,z4,z11,z6]),(0,[z252,z2,z4,z47,z5,z6])]],
   [[(0,[z208,z0,z2,z4,z572,z6]),(0,[z406,z0,z1,z4,z5,z6]),(0,[z85,z1,z2,z971,z5,z6]),(0,[z0,z2,z4,z972,z5,z6]),(0,[z973,z0,z2,z4,z5,z6])],[(0,[z1,z2,z4,z432,z5,z6]),(0,[z12,z2,z78,z47,z5,z6]),(0,[z63,z0,z2,z4,z5,z29]),(0,[z0,z15,z2,z193,z5,z6]),(0,[z0,z116,z2,z4,z414,z6]),(0,[z0,z2,z4,z5,z974,z6]),(0,[z975,z0,z2,z4,z5,z6])],[(0,[z208,z0,z2,z4,z91,z6]),(0,[z976,z0,z2,z4,z5,z6]),(0,[z0,z977,z2,z4,z5,z6]),(0,[z63,z803,z2,z4,z5,z6]),(0,[z978,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z883])],[(0,[z40,z1,z2,z4,z166,z520]),(0,[z0,z15,z2,z258,z5,z6]),(0,[z0,z1,z20,z229,z5,z6]),(0,[z846,z0,z2,z4,z5,z248])],[(0,[z0,z979,z2,z4,z5,z6]),(0,[z14,z0,z2,z4,z5,z125]),(0,[z63,z0,z698,z2,z4,z5]),(0,[z161,z463,z2,z4,z5,z6])],[(0,[z123,z1,z2,z59,z5,z6]),(0,[z0,z980,z2,z4,z5,z6]),(0,[z147,z63,z0,z2,z4,z104]),(0,[z147,z0,z1,z2,z4,z104])],[(0,[z1,z2,z4,z526,z13,z6])],[(0,[z0,z1,z2,z5,z6,z981]),(0,[z227,z1,z2,z4,z526,z6]),(0,[z15,z2,z4,z432,z5,z6])],[(0,[z0,z45,z2,z4,z5,z6]),(0,[z0,z1,z157,z4,z418,z6]),(0,[z0,z982,z2,z4,z5,z6]),(0,[z983,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z984,z6]),(0,[z512,z0,z1,z109,z5,z6]),(0,[z985,z0,z2,z4,z5,z6]),(0,[z30,z0,z2,z4,z5,z53])],[(0,[z0,z1,z2,z75,z122,z6]),(0,[z0,z986,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z987,z6]),(0,[z0,z988,z2,z4,z5,z6])],[(0,[z158,z1,z2,z4,z5,z34]),(0,[z384,z63,z0,z2,z4,z5]),(0,[z0,z1,z2,z251,z5,z271])],[(0,[z63,z0,z2,z4,z5,z651]),(0,[z0,z989,z2,z4,z5,z6])],[(0,[z0,z2,z4,z47,z146,z6]),(0,[z0,z990,z2,z4,z5,z6]),(0,[z0,z797,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z725,z6]),(0,[z0,z1,z2,z4,z991,z6]),(0,[z0,z2,z4,z47,z907,z5]),(0,[z0,z1,z2,z4,z5,z992])],[(0,[z0,z357,z2,z4,z5,z240]),(0,[z63,z0,z2,z4,z763,z6]),(0,[z0,z1,z2,z5,z6,z844])]],
   [[(0,[z123,z1,z77,z4,z5,z6]),(0,[z0,z2,z4,z993,z5,z6]),(0,[z994,z1,z2,z4,z5,z6])],[(0,[z0,z15,z2,z136,z5,z6]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z0,z15,z4,z5,z6,z495]),(0,[z0,z2,z4,z5,z6,z259]),(0,[z0,z17,z2,z4,z5,z298]),(0,[z0,z1,z58,z4,z5,z35])],[(0,[z0,z2,z4,z5,z18,z163]),(0,[z64,z2,z4,z5,z215,z125]),(0,[z996,z0,z1,z2,z4,z5]),(1,[z0,z1,z4,z5,z795])],[(0,[z37,z2,z4,z393,z5,z6]),(0,[z0,z365,z2,z4,z5,z163]),(0,[z0,z2,z4,z526,z18,z6]),(0,[z997,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z930,z89,z6])],[(0,[z0,z51,z4,z5,z18,z6]),(0,[z0,z2,z4,z5,z782,z6])],[(0,[z0,z1,z998,z4,z5,z6])],[(0,[z0,z2,z4,z5,z289,z6]),(0,[z400,z2,z4,z393,z5,z6])],[(0,[z147,z0,z1,z2,z4,z883])],[(0,[z175,z1,z2,z4,z5,z153]),(0,[z0,z2,z4,z5,z999,z6])],[(0,[z0,z884,z2,z4,z5,z6])],[(0,[z225,z28,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z163]),(0,[z0,z2,z4,z1000,z5,z6]),(0,[z0,z1,z1001,z4,z5,z6]),(0,[z19,z0,z2,z5,z6,z259]),(0,[z0,z2,z4,z5,z987,z248])],[(0,[z0,z2,z4,z5,z1002,z6])],[(0,[z0,z15,z2,z75,z5,z6]),(0,[z0,z1,z2,z4,z418,z216]),(1,[z0,z857,z4,z5,z6]),(0,[z875,z14,z2,z4,z5,z6]),(0,[z0,z116,z2,z4,z782,z6])],[(0,[z0,z2,z4,z5,z18,z153]),(0,[z123,z1,z2,z4,z1003,z6]),(0,[z0,z1,z2,z4,z5,z826]),(0,[z0,z1,z2,z4,z5,z50])],[(0,[z63,z0,z2,z4,z5,z83]),(0,[z63,z0,z2,z4,z790,z6]),(0,[z63,z2,z4,z5,z61,z6])],[(0,[z63,z0,z2,z4,z5,z347]),(0,[z1,z2,z59,z5,z13,z6]),(0,[z0,z1004,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1005]),(0,[z0,z1006,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z298]),(0,[z179,z0,z1,z2,z4,z263])],[(0,[z63,z0,z20,z102,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1007]),(0,[z0,z2,z4,z67,z18,z6]),(0,[z0,z15,z2,z4,z526,z6]),(0,[z123,z108,z1,z109,z5,z6])],[(0,[z0,z1008,z2,z4,z5,z6]),(0,[z194,z0,z4,z311,z5,z6]),(0,[z1009,z0,z2,z4,z5,z6]),(0,[z0,z463,z250,z4,z5,z6])],[(0,[z0,z2,z4,z220,z18,z6]),(0,[z0,z2,z4,z5,z6,z1010]),(0,[z0,z2,z137,z4,z5,z18]),(0,[z179,z63,z0,z2,z4,z6]),(0,[z252,z470,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z5,z844])],[(0,[z0,z2,z4,z47,z5,z153]),(0,[z0,z1,z2,z4,z526,z125]),(0,[z0,z503,z2,z4,z5,z6]),(0,[z0,z1,z1011,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z281])],[(0,[z0,z1,z4,z1012,z5,z6])],[(0,[z0,z2,z4,z5,z810,z6]),(0,[z0,z1,z2,z4,z1013,z6]),(0,[z68,z63,z0,z56,z4,z5])],[(0,[z884,z1,z2,z4,z5,z6]),(0,[z0,z1014,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1015,z6]),(0,[z63,z0,z2,z4,z5,z125]),(0,[z0,z2,z4,z18,z6,z471]),(0,[z10,z0,z2,z4,z5,z50]),(0,[z0,z2,z4,z1016,z5,z6]),(0,[z0,z463,z2,z4,z5,z263]),(0,[z0,z1,z2,z237,z6,z596])],[(0,[z0,z1017,z2,z4,z5,z6]),(0,[z0,z2,z4,z1018,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1019]),(0,[z0,z1,z2,z4,z5,z1020]),(0,[z1021,z0,z2,z4,z5,z6])],[(0,[z76,z0,z1,z109,z5,z6]),(0,[z0,z2,z4,z5,z1022,z216])],[(0,[z0,z1,z1023,z4,z5,z6]),(0,[z1,z2,z4,z166,z801,z6]),(0,[z0,z463,z2,z4,z5,z6]),(0,[z0,z2,z1024,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1025])],[(0,[z0,z1,z2,z1026,z5,z6]),(0,[z0,z2,z4,z1027,z5,z6]),(0,[z0,z56,z2,z1028,z4,z5])],[],[(0,[z0,z1,z2,z4,z1029,z6]),(0,[z0,z1,z2,z75,z5,z163])]],
   [[(0,[z0,z15,z2,z4,z1030,z6]),(0,[z19,z0,z510,z2,z5,z271])],[(0,[z0,z1,z2,z4,z540,z6]),(0,[z0,z2,z4,z5,z1031,z6]),(0,[z0,z1032,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1033,z6]),(0,[z0,z2,z4,z5,z6,z1034])],[(0,[z0,z45,z2,z4,z5,z385]),(0,[z0,z1,z2,z4,z5,z1035]),(0,[z0,z1036,z2,z4,z5,z6]),(0,[z0,z2,z4,z1037,z5,z6]),(0,[z0,z2,z4,z213,z6,z695])],[(0,[z0,z1,z2,z4,z1038,z6]),(0,[z0,z1,z2,z4,z5,z1039]),(0,[z0,z223,z2,z4,z5,z520]),(0,[z0,z1,z2,z4,z5,z1040]),(0,[z63,z0,z2,z4,z5,z490])],[(0,[z0,z1,z2,z4,z1041,z6]),(0,[z147,z1,z2,z4,z13,z125]),(0,[z68,z218,z0,z2,z4,z5]),(0,[z0,z246,z2,z4,z96,z6])],[(0,[z0,z1,z2,z4,z1042,z6]),(0,[z0,z2,z433,z47,z5,z6]),(0,[z0,z1,z2,z4,z930,z6])],[(0,[z63,z100,z77,z4,z5,z6]),(0,[z40,z1,z2,z4,z526,z6]),(0,[z108,z0,z201,z109,z5,z6]),(0,[z1043,z1,z2,z4,z5,z6]),(0,[z0,z1044,z2,z4,z5,z6]),(0,[z179,z0,z1,z2,z4,z103])],[(0,[z0,z24,z2,z4,z5,z240]),(0,[z458,z1,z2,z4,z13,z6]),(0,[z63,z0,z2,z4,z818,z6]),(0,[z1045,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1046,z6])],[(0,[z63,z0,z2,z4,z5,z163]),(0,[z218,z0,z2,z4,z5,z125]),(0,[z0,z2,z4,z1047,z5,z6]),(0,[z30,z0,z1,z2,z4,z5]),(0,[z0,z2,z4,z782,z53,z6]),(0,[z0,z2,z4,z5,z870,z6]),(0,[z0,z1,z2,z4,z5,z871]),(0,[z0,z2,z4,z5,z1048,z263])],[(0,[z82,z0,z1,z4,z867,z6]),(0,[z82,z384,z0,z1,z4,z11]),(0,[z0,z1,z58,z36,z5,z35])],[(0,[z0,z1,z2,z4,z5,z1049]),(0,[z252,z2,z4,z5,z18,z6]),(0,[z1050,z1,z2,z4,z5,z6])],[(0,[z227,z1,z2,z4,z5,z125]),(0,[z32,z0,z1,z2,z89,z6])],[(0,[z0,z839,z2,z75,z5,z6]),(0,[z99,z1,z157,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1051]),(0,[z0,z1052,z2,z4,z5,z6]),(0,[z232,z1,z2,z4,z5,z125]),(0,[z0,z2,z4,z131,z213,z6]),(0,[z0,z2,z4,z5,z1048,z6])],[(0,[z0,z1,z2,z1053,z5,z6]),(0,[z1,z2,z4,z5,z61,z6]),(0,[z422,z0,z56,z2,z4,z5])],[(0,[z1,z77,z4,z328,z5,z6]),(0,[z0,z1,z1054,z4,z5,z6])],[(0,[z0,z2,z4,z1055,z18,z6]),(0,[z0,z2,z4,z6,z389,z471]),(0,[z0,z1,z2,z4,z1056,z6])]],
   [[(0,[z0,z1,z250,z4,z5,z120])],[(0,[z37,z884,z2,z4,z5,z6]),(0,[z1057,z1,z2,z4,z5,z6]),(0,[z1058,z0,z2,z4,z5,z6])],[(0,[z0,z24,z51,z4,z5,z6]),(0,[z1,z2,z4,z5,z1059,z6]),(0,[z0,z2,z4,z5,z6,z1060])],[(0,[z99,z45,z46,z4,z5,z6]),(0,[z0,z1061,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z285,z6]),(0,[z63,z0,z2,z4,z5,z153]),(0,[z0,z2,z461,z47,z5,z6]),(0,[z14,z0,z56,z2,z4,z5]),(0,[z15,z2,z4,z5,z61,z6]),(0,[z0,z1,z2,z4,z1062,z6])],[(0,[z0,z1,z2,z4,z5,z1063]),(0,[z0,z1,z157,z4,z5,z216]),(0,[z406,z63,z0,z2,z4,z5]),(0,[z1064,z1,z2,z4,z5,z6]),(0,[z0,z56,z57,z4,z5,z21]),(0,[z0,z1,z2,z4,z6,z471]),(0,[z0,z1,z2,z4,z5,z1065]),(0,[z0,z1,z2,z5,z35,z844])],[(0,[z0,z1,z2,z4,z5,z1066]),(0,[z0,z1067,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z270]),(0,[z0,z2,z47,z559,z5,z6]),(0,[z0,z2,z4,z5,z1068,z6]),(0,[z147,z161,z1,z2,z4,z6]),(0,[z0,z503,z2,z237,z88,z6])],[(0,[z0,z1,z77,z59,z5,z6]),(0,[z303,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1069,z6]),(0,[z0,z15,z51,z4,z5,z6]),(0,[z538,z1,z2,z4,z13,z6]),(0,[z108,z63,z0,z109,z5,z6]),(0,[z0,z1,z2,z36,z5,z35])],[(0,[z0,z1,z1070,z4,z5,z6]),(0,[z0,z1071,z2,z4,z5,z6]),(0,[z1072,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z1073,z5,z6])],[(0,[z303,z1,z2,z4,z13,z6]),(0,[z0,z1,z22,z4,z319,z6]),(0,[z273,z0,z1,z2,z5,z271])],[(0,[z0,z2,z4,z5,z1074,z6]),(0,[z0,z1,z2,z4,z5,z120])],[(0,[z123,z1,z2,z4,z5,z6]),(0,[z0,z4,z5,z215,z6,z495]),(0,[z1075,z1,z2,z4,z5,z6])],[(0,[z0,z1076,z2,z4,z5,z6])],[(0,[z0,z15,z2,z4,z5,z83]),(0,[z0,z2,z4,z5,z759,z6]),(0,[z0,z1,z2,z4,z5,z1077]),(0,[z63,z0,z2,z4,z5,z455]),(1,[z0,z1,z4,z867,z6])],[(0,[z0,z1078,z2,z4,z5,z6]),(0,[z0,z1079,z2,z4,z5,z6])],[(0,[z85,z1,z2,z151,z285,z6]),(0,[z0,z2,z4,z5,z1080,z6]),(0,[z384,z0,z1,z2,z4,z5]),(0,[z1081,z0,z2,z4,z5,z6]),(0,[z0,z42,z56,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1082,z6]),(0,[z1083,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z1084,z5,z6]),(0,[z0,z15,z20,z102,z5,z6]),(0,[z63,z0,z2,z861,z5,z6])]],
   [[],[(0,[z0,z2,z4,z1085,z5,z6]),(0,[z161,z1,z250,z4,z5,z6]),(0,[z19,z422,z0,z2,z5,z271])],[(0,[z12,z1,z2,z4,z418,z6]),(0,[z64,z2,z4,z47,z5,z125])],[(0,[z1086,z0,z2,z4,z5,z6]),(0,[z63,z0,z2,z866,z5,z6]),(0,[z82,z0,z239,z4,z11,z6]),(0,[z0,z1,z1087,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1088,z6]),(0,[z0,z1,z36,z195,z5,z35])],[(0,[z0,z2,z4,z1089,z5,z6]),(0,[z875,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z1090,z5,z6])],[(0,[z63,z0,z2,z4,z122,z6]),(0,[z1091,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z1092,z5,z6]),(0,[z161,z1,z2,z4,z5,z263]),(0,[z0,z2,z4,z5,z1093,z6])],[(0,[z99,z1,z2,z4,z418,z6]),(0,[z0,z2,z668,z47,z5,z6]),(0,[z574,z63,z0,z2,z4,z5]),(0,[z0,z2,z4,z5,z6,z1094]),(0,[z68,z0,z1,z4,z5,z488]),(0,[z19,z0,z1,z2,z5,z844])],[(0,[z37,z38,z2,z4,z220,z6]),(0,[z0,z126,z2,z4,z5,z125])],[(0,[z0,z1,z157,z4,z5,z6]),(0,[z0,z4,z114,z195,z5,z6])],[(0,[z161,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1095]),(0,[z0,z2,z237,z349,z88,z6]),(0,[z0,z2,z4,z5,z1096,z6])],[(0,[z0,z1,z2,z4,z540,z385]),(0,[z0,z1,z1097,z4,z5,z6]),(0,[z406,z63,z0,z1,z4,z5]),(0,[z63,z0,z323,z4,z5,z6])],[(0,[z0,z2,z4,z73,z5,z34]),(0,[z0,z1,z2,z1098,z5,z6]),(0,[z803,z15,z2,z4,z5,z6]),(0,[z0,z1,z1099,z4,z5,z6])],[(0,[z0,z357,z51,z4,z5,z6]),(0,[z584,z0,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z1100,z6]),(0,[z0,z2,z4,z47,z5,z281]),(0,[z0,z2,z4,z1101,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1102]),(0,[z63,z0,z22,z4,z23,z6])],[(0,[z63,z0,z2,z4,z5,z186]),(0,[z1103,z0,z2,z4,z5,z163]),(0,[z1,z2,z4,z5,z801,z6])]],
   [[(0,[z0,z1,z2,z1104,z5,z6]),(0,[z101,z0,z2,z73,z5,z6]),(1,[z0,z2,z4,z5,z760]),(0,[z877,z0,z2,z4,z5,z6]),(0,[z0,z1,z1105,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1106,z6]),(0,[z0,z2,z4,z5,z1107,z6]),(0,[z0,z4,z5,z18,z6,z495]),(0,[z0,z1108,z2,z4,z5,z6]),(0,[z1109,z1,z2,z4,z5,z6])],[(0,[z227,z1,z2,z4,z166,z6]),(0,[z406,z0,z1,z4,z5,z31]),(0,[z0,z1,z601,z4,z5,z21]),(1,[z0,z1,z827,z5,z6]),(0,[z0,z470,z323,z4,z5,z6])],[(0,[z1110,z0,z2,z4,z5,z216]),(0,[z0,z1111,z2,z4,z5,z6]),(0,[z0,z1112,z2,z4,z5,z6]),(0,[z0,z1113,z2,z4,z5,z6])],[(0,[z74,z884,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1114,z6]),(0,[z32,z0,z2,z47,z89,z6])],[(0,[z0,z56,z4,z47,z5,z21]),(0,[z0,z1115,z2,z4,z5,z6]),(0,[z0,z2,z4,z1116,z5,z6])],[(0,[z0,z192,z4,z5,z318,z6]),(0,[z0,z1117,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1118,z5,z6]),(0,[z0,z204,z2,z4,z5,z6]),(0,[z80,z30,z0,z2,z4,z5]),(0,[z63,z0,z2,z897,z5,z6]),(0,[z351,z63,z0,z2,z4,z5]),(0,[z0,z1,z2,z1119,z5,z6]),(0,[z179,z0,z1,z2,z4,z6])],[(0,[z100,z15,z77,z4,z5,z6]),(0,[z0,z1,z2,z757,z5,z6]),(0,[z0,z2,z237,z47,z88,z6]),(0,[z181,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1120])],[(0,[z63,z0,z2,z4,z5,z674]),(0,[z0,z2,z4,z47,z540,z6]),(0,[z99,z46,z4,z47,z5,z6]),(0,[z63,z0,z2,z4,z5,z723]),(0,[z0,z1,z2,z4,z6,z1121]),(1,[z0,z2,z4,z782,z6])],[(0,[z80,z0,z696,z4,z5,z6]),(0,[z0,z2,z4,z213,z678,z6])],[(0,[z0,z1,z2,z4,z1055,z6]),(0,[z0,z1122,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z214])],[(0,[z0,z1,z1123,z4,z5,z6]),(0,[z99,z1,z46,z4,z540,z6]),(0,[z0,z1,z2,z88,z930,z6])],[(0,[z0,z1,z2,z4,z5,z216]),(0,[z0,z72,z438,z4,z5,z6]),(0,[z32,z252,z1,z2,z89,z6])],[(0,[z63,z0,z2,z4,z146,z6]),(0,[z1124,z0,z2,z4,z5,z6])],[(0,[z0,z560,z2,z47,z5,z6]),(0,[z0,z1,z2,z1125,z5,z6]),(0,[z1126,z0,z2,z4,z5,z6]),(0,[z0,z2,z1127,z4,z5,z6]),(0,[z0,z2,z1128,z4,z5,z6]),(0,[z1,z2,z971,z151,z5,z6]),(0,[z0,z2,z4,z47,z5,z520]),(0,[z0,z116,z2,z4,z631,z6])]],
   [[(0,[z384,z10,z0,z2,z4,z5]),(0,[z0,z1129,z2,z4,z5,z6]),(0,[z422,z0,z2,z4,z6,z471])],[(0,[z0,z1,z1130,z4,z5,z6])],[(0,[z384,z0,z1,z20,z4,z5]),(0,[z0,z1131,z2,z4,z5,z6]),(0,[z179,z1075,z1,z2,z4,z6])],[(0,[z295,z1,z2,z4,z5,z125]),(0,[z2,z4,z47,z432,z5,z6]),(0,[z0,z1,z2,z4,z5,z1132])],[(0,[z0,z1,z2,z4,z418,z6]),(0,[z1133,z0,z2,z4,z5,z6]),(0,[z1134,z0,z2,z4,z5,z6])],[(0,[z0,z1135,z2,z4,z5,z6]),(0,[z1136,z0,z2,z4,z5,z6]),(0,[z0,z1137,z2,z4,z5,z6]),(0,[z0,z1,z250,z4,z5,z263])],[(0,[z0,z1138,z2,z4,z5,z6])],[(0,[z0,z2,z4,z122,z18,z6]),(0,[z0,z2,z4,z5,z18,z493]),(0,[z0,z1,z2,z4,z5,z1139]),(0,[z0,z1140,z2,z4,z5,z50]),(0,[z0,z1141,z2,z4,z5,z6])],[(0,[z0,z15,z2,z633,z5,z6]),(0,[z0,z1,z2,z4,z5,z1142]),(0,[z0,z1,z2,z554,z88,z6]),(0,[z0,z2,z4,z5,z298,z35]),(0,[z0,z2,z4,z5,z1143,z6]),(0,[z14,z0,z2,z36,z5,z35]),(0,[z147,z0,z1,z2,z4,z557])],[(0,[z0,z1144,z2,z4,z5,z6]),(0,[z160,z0,z2,z4,z5,z125]),(0,[z0,z1,z1145,z4,z5,z6]),(0,[z784,z0,z2,z4,z47,z5]),(0,[z0,z1,z2,z785,z4,z5]),(0,[z0,z1,z2,z1146,z5,z6]),(0,[z0,z2,z1147,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1148]),(0,[z0,z1149,z2,z4,z5,z6])],[(0,[z1150,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z285,z6]),(0,[z227,z15,z2,z4,z5,z6]),(0,[z63,z0,z421,z2,z4,z5])],[(0,[z1151,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z6,z471]),(0,[z1152,z1,z2,z4,z5,z6]),(0,[z1153,z0,z2,z4,z5,z6])],[(0,[z37,z38,z2,z4,z5,z6]),(0,[z123,z1154,z2,z4,z5,z6]),(0,[z0,z2,z4,z1155,z5,z6])],[(0,[z0,z1,z2,z75,z540,z6]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z303,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z263])],[(0,[z0,z1,z2,z4,z1156,z6]),(0,[z406,z40,z1,z4,z5,z6]),(0,[z158,z63,z2,z4,z5,z34])]],
   [[(0,[z0,z1,z2,z59,z5,z6]),(0,[z63,z0,z2,z4,z5,z427]),(0,[z1157,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1158,z6])],[(0,[z63,z0,z2,z4,z5,z577]),(0,[z1,z77,z78,z109,z5,z6]),(0,[z0,z2,z4,z47,z5,z120])],[(0,[z1159,z0,z1,z4,z5,z6]),(0,[z123,z2,z4,z47,z5,z6]),(0,[z0,z1160,z2,z4,z5,z6]),(0,[z0,z1,z4,z1161,z5,z6]),(0,[z0,z2,z4,z5,z1162,z6]),(0,[z0,z2,z4,z5,z6,z1163]),(0,[z0,z1,z2,z4,z1164,z6])],[(0,[z0,z2,z4,z5,z1022,z6]),(0,[z0,z118,z4,z5,z664,z6]),(0,[z0,z2,z4,z1165,z5,z6])],[(0,[z0,z15,z2,z4,z122,z6]),(0,[z0,z1166,z2,z4,z5,z6]),(0,[z219,z1,z2,z4,z5,z34]),(0,[z0,z2,z47,z5,z26,z6]),(0,[z14,z0,z2,z569,z5,z6]),(0,[z0,z2,z4,z5,z1167,z6]),(0,[z0,z1,z2,z1168,z5,z6])],[],[(0,[z62,z0,z2,z47,z5,z6]),(0,[z37,z38,z2,z4,z5,z134]),(0,[z0,z1169,z2,z4,z5,z6]),(0,[z0,z1,z1170,z4,z5,z6]),(0,[z775,z0,z1,z2,z4,z6]),(0,[z63,z161,z2,z4,z5,z6])],[(0,[z0,z1171,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z378]),(0,[z0,z2,z47,z5,z6,z259]),(0,[z0,z1,z2,z4,z5,z1172]),(0,[z1173,z0,z1,z2,z4,z6])],[(0,[z85,z0,z2,z73,z5,z6]),(0,[z0,z1,z2,z137,z4,z5]),(0,[z0,z1174,z2,z4,z5,z6])],[(0,[z402,z0,z2,z47,z5,z6]),(0,[z0,z15,z2,z275,z5,z6]),(0,[z108,z0,z1,z109,z5,z6])],[(0,[z63,z1157,z2,z4,z5,z6]),(0,[z0,z1,z56,z4,z5,z336])],[(0,[z1175,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1176]),(0,[z0,z2,z4,z5,z1177,z6]),(0,[z0,z15,z22,z4,z23,z6]),(0,[z0,z2,z433,z5,z238,z6]),(0,[z0,z1178,z2,z4,z5,z6])],[(0,[z1,z2,z737,z4,z5,z6]),(0,[z64,z2,z4,z5,z18,z125]),(0,[z10,z0,z2,z4,z5,z6]),(0,[z101,z0,z2,z757,z5,z6])],[(0,[z0,z1179,z2,z4,z5,z6]),(0,[z0,z1180,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1181,z6]),(0,[z252,z15,z2,z4,z5,z6]),(0,[z0,z2,z1182,z4,z5,z6])],[(0,[z0,z2,z4,z5,z723,z6]),(0,[z0,z1183,z2,z4,z5,z6])]],
   [[],[(0,[z40,z1,z2,z4,z166,z6]),(0,[z0,z2,z4,z73,z5,z6]),(0,[z0,z1,z4,z195,z5,z6])],[(0,[z63,z0,z2,z4,z43,z103]),(0,[z1184,z1,z2,z4,z5,z6])],[(0,[z40,z1,z2,z4,z801,z6]),(0,[z0,z139,z2,z4,z5,z6])],[(0,[z63,z0,z2,z4,z5,z162]),(0,[z0,z1,z4,z867,z11,z6]),(0,[z0,z1185,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z146,z83]),(0,[z0,z1,z2,z4,z1186,z6]),(0,[z0,z320,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1187,z6])],[(0,[z0,z1,z58,z4,z5,z271])],[(0,[z0,z1,z2,z4,z122,z163]),(0,[z0,z1188,z2,z4,z5,z6]),(0,[z63,z0,z2,z1028,z4,z5]),(0,[z671,z0,z1,z109,z5,z6]),(0,[z0,z1,z2,z705,z5,z35])],[(0,[z0,z45,z2,z75,z5,z6]),(0,[z0,z1,z2,z4,z5,z1189]),(0,[z384,z0,z1,z2,z4,z13]),(0,[z0,z2,z4,z47,z5,z50]),(0,[z274,z658,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z281]),(0,[z0,z1,z2,z4,z1003,z6])],[(0,[z227,z1,z2,z4,z5,z153]),(0,[z1109,z2,z4,z47,z5,z6])],[(0,[z63,z0,z2,z4,z5,z403]),(0,[z0,z1,z2,z4,z1190,z6])],[(0,[z0,z2,z757,z47,z5,z6]),(0,[z0,z22,z4,z47,z23,z6]),(0,[z0,z2,z4,z5,z6,z1191]),(0,[z0,z1192,z2,z4,z5,z6])],[(0,[z0,z15,z2,z4,z146,z6])],[(0,[z0,z1193,z2,z4,z5,z6]),(0,[z1194,z0,z2,z4,z5,z6])],[(0,[z1195,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1196]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1197,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z220,z6]),(0,[z82,z0,z15,z4,z11,z6]),(0,[z0,z56,z4,z5,z18,z21]),(0,[z303,z1,z2,z4,z5,z1198])],[(0,[z0,z1,z2,z1199,z5,z6]),(0,[z0,z2,z4,z1200,z5,z6]),(0,[z0,z58,z4,z47,z5,z6]),(0,[z0,z2,z4,z47,z6,z1121]),(0,[z1201,z0,z2,z4,z5,z263])],[(0,[z123,z1,z46,z4,z5,z6]),(0,[z170,z1,z2,z4,z13,z6])],[],[(0,[z0,z15,z2,z655,z5,z6]),(0,[z99,z46,z4,z5,z18,z6]),(0,[z68,z0,z15,z4,z5,z31])],[(0,[z0,z365,z2,z4,z540,z6]),(0,[z0,z1202,z2,z4,z5,z6]),(0,[z1150,z0,z2,z4,z5,z385]),(0,[z0,z2,z47,z5,z155,z6]),(0,[z1203,z0,z2,z4,z5,z6]),(0,[z1201,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1204,z5,z6]),(0,[z0,z2,z4,z1205,z5,z6]),(0,[z0,z1,z857,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1206]),(0,[z208,z0,z2,z4,z524,z6]),(0,[z1,z2,z4,z5,z6,z1207]),(0,[z0,z470,z2,z4,z5,z120])],[(0,[z85,z1,z157,z151,z5,z6]),(0,[z0,z2,z4,z587,z286,z6])],[(0,[z0,z1,z2,z4,z5,z1208]),(0,[z402,z1,z2,z151,z5,z6]),(0,[z175,z1,z2,z4,z67,z34]),(0,[z0,z2,z1209,z4,z5,z6]),(0,[z63,z227,z2,z4,z5,z6]),(0,[z384,z0,z1,z4,z109,z5]),(0,[z0,z1210,z2,z4,z5,z6]),(0,[z147,z181,z1,z2,z4,z104])],[(0,[z0,z1,z2,z4,z220,z134]),(0,[z0,z15,z2,z4,z5,z163]),(0,[z0,z1211,z2,z4,z5,z6]),(0,[z892,z1,z2,z4,z5,z6]),(0,[z0,z1212,z2,z4,z5,z6]),(0,[z1213,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1214])],[(0,[z0,z1,z2,z59,z5,z385]),(0,[z0,z2,z4,z5,z1215,z6]),(0,[z0,z2,z4,z5,z18,z520]),(0,[z63,z0,z56,z2,z4,z5]),(0,[z108,z0,z109,z5,z18,z6])],[(0,[z841,z0,z2,z4,z5,z6]),(0,[z1216,z0,z1,z2,z4,z5])],[(0,[z0,z2,z4,z47,z418,z6]),(0,[z0,z2,z4,z1217,z5,z6]),(0,[z0,z2,z4,z5,z1218,z6]),(0,[z32,z0,z1,z2,z930,z6])],[(0,[z1219,z0,z1,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z690]),(0,[z108,z0,z1,z827,z5,z6]),(0,[z0,z419,z20,z102,z5,z6])],[(0,[z0,z211,z2,z4,z5,z6]),(0,[z762,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z1039]),(0,[z0,z1,z2,z4,z5,z1220])],[(0,[z0,z1,z2,z4,z285,z240]),(0,[z0,z192,z52,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z47,z1042,z6]),(0,[z14,z0,z2,z73,z5,z6]),(0,[z968,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z1221,z5,z6]),(0,[z0,z2,z4,z5,z1222,z6])],[(0,[z217,z0,z2,z4,z5,z6])],[(0,[z0,z1,z1223,z4,z5,z6]),(0,[z0,z1,z2,z4,z67,z6]),(0,[z0,z1224,z2,z4,z5,z6]),(0,[z0,z1225,z2,z4,z5,z6])],[(0,[z517,z1,z2,z4,z5,z125]),(0,[z241,z0,z2,z4,z53,z6]),(0,[z63,z0,z1001,z4,z5,z6])],[(0,[z0,z15,z2,z4,z5,z153]),(0,[z0,z15,z2,z552,z5,z6]),(0,[z1226,z0,z2,z4,z5,z6]),(0,[z1057,z2,z4,z5,z18,z6])],[(0,[z1,z2,z4,z1227,z5,z6]),(0,[z1228,z1,z2,z4,z5,z6])],[(0,[z80,z0,z857,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z50]),(0,[z1229,z0,z2,z4,z5,z6])],[(0,[z0,z1230,z2,z4,z5,z6]),(0,[z0,z1,z4,z697,z5,z21]),(0,[z0,z1231,z2,z4,z5,z6])],[(0,[z0,z2,z4,z1232,z5,z6]),(0,[z0,z2,z4,z418,z18,z6]),(0,[z0,z1,z58,z4,z5,z6]),(0,[z160,z0,z56,z2,z4,z5])],[(0,[z63,z0,z2,z94,z4,z5]),(0,[z0,z72,z118,z4,z5,z6]),(0,[z303,z2,z4,z5,z18,z6])],[(0,[z0,z1,z2,z4,z5,z1233]),(0,[z0,z72,z657,z4,z5,z6]),(0,[z0,z1,z51,z4,z285,z6]),(0,[z218,z0,z56,z2,z4,z5]),(0,[z303,z63,z2,z4,z5,z6])],[(0,[z99,z1,z46,z59,z5,z6]),(0,[z0,z1234,z2,z4,z5,z6]),(0,[z0,z1235,z2,z4,z5,z6]),(0,[z85,z1,z2,z151,z5,z216]),(0,[z1110,z0,z2,z4,z5,z6]),(0,[z175,z1,z2,z4,z5,z34]),(0,[z0,z1,z1236,z4,z5,z6]),(0,[z2,z4,z5,z61,z18,z6])],[(0,[z422,z0,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z5,z1237]),(0,[z0,z2,z4,z5,z18,z120]),(0,[z0,z1,z250,z4,z5,z6]),(0,[z1238,z0,z2,z4,z5,z6])],[(0,[z74,z658,z2,z4,z5,z6]),(0,[z63,z183,z0,z2,z4,z5]),(0,[z63,z0,z2,z4,z5,z456]),(0,[z515,z1,z2,z4,z5,z125]),(0,[z123,z2,z4,z5,z18,z6]),(0,[z1,z2,z4,z5,z1239,z6]),(0,[z0,z1,z2,z5,z930,z6])],[(0,[z0,z2,z4,z5,z6,z1240]),(0,[z0,z2,z4,z757,z5,z6]),(0,[z0,z558,z2,z4,z5,z298]),(0,[z123,z63,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z281]),(0,[z0,z1,z2,z4,z867,z6])],[(0,[z1086,z0,z2,z4,z5,z240]),(0,[z0,z1,z4,z5,z6,z1241]),(0,[z123,z1,z4,z5,z21,z6])]],
   [[(0,[z1242,z0,z2,z4,z5,z6]),(0,[z0,z2,z36,z47,z5,z35]),(0,[z0,z2,z4,z848,z18,z6]),(0,[z0,z2,z4,z1243,z5,z6]),(0,[z1244,z1,z2,z4,z5,z6]),(0,[z68,z179,z0,z1,z2,z4])],[(0,[z0,z1,z2,z4,z1245,z6]),(0,[z0,z1246,z2,z4,z5,z6])],[(0,[z74,z643,z2,z4,z5,z6]),(0,[z85,z1,z2,z151,z418,z6]),(0,[z0,z2,z4,z1247,z5,z6]),(0,[z14,z0,z2,z4,z5,z34]),(0,[z0,z857,z52,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z793]),(0,[z63,z0,z205,z2,z4,z5])],[(0,[z0,z2,z4,z5,z1248,z6]),(0,[z0,z2,z4,z5,z1249,z6]),(0,[z1250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z898,z6]),(0,[z252,z1,z323,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1251]),(0,[z0,z1,z157,z4,z5,z240]),(0,[z0,z282,z2,z4,z67,z6]),(0,[z0,z1252,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1253,z6])],[(0,[z0,z1,z2,z1254,z5,z6]),(0,[z99,z1,z737,z4,z5,z6]),(0,[z0,z1,z4,z1255,z5,z6]),(0,[z80,z0,z137,z52,z4,z5]),(0,[z0,z1,z1256,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1257]),(0,[z1258,z0,z2,z4,z5,z120])],[(0,[z218,z0,z2,z4,z5,z35]),(0,[z0,z1,z56,z291,z4,z5]),(0,[z0,z1,z2,z4,z5,z795])],[],[(0,[z0,z1,z4,z5,z6,z795])],[(0,[z63,z0,z2,z4,z540,z6]),(0,[z406,z63,z0,z4,z5,z125])],[(0,[z0,z1259,z2,z4,z5,z6]),(0,[z965,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1260]),(0,[z161,z1,z2,z4,z88,z6])],[(0,[z101,z0,z2,z47,z5,z6]),(0,[z0,z15,z323,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1261])],[(0,[z0,z1262,z2,z4,z5,z6]),(0,[z0,z42,z2,z4,z5,z34]),(0,[z0,z2,z4,z47,z1187,z6]),(0,[z849,z0,z1,z2,z4,z5]),(0,[z145,z0,z2,z73,z5,z6]),(0,[z161,z2,z4,z5,z18,z6])],[(0,[z0,z1,z2,z4,z5,z134]),(0,[z0,z1,z685,z102,z5,z6]),(0,[z175,z282,z2,z4,z5,z34]),(0,[z498,z468,z2,z4,z5,z6]),(0,[z123,z1263,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1264]),(0,[z0,z2,z4,z1265,z5,z6])]],
   [[(0,[z85,z1,z2,z151,z5,z6]),(0,[z0,z2,z4,z5,z1114,z240]),(0,[z40,z223,z2,z4,z166,z6]),(0,[z63,z0,z2,z4,z5,z520]),(0,[z0,z15,z2,z4,z882,z6])],[(0,[z184,z28,z2,z4,z5,z6]),(0,[z834,z0,z2,z4,z5,z153]),(0,[z0,z1266,z2,z4,z5,z6]),(0,[z585,z0,z2,z4,z5,z18])],[(0,[z0,z38,z2,z4,z5,z83]),(0,[z10,z0,z2,z4,z13,z6]),(0,[z0,z250,z4,z5,z18,z6])],[(0,[z0,z1,z2,z4,z1267,z6])],[(0,[z0,z1268,z2,z4,z5,z6]),(0,[z0,z116,z2,z4,z96,z6])],[(0,[z0,z1,z2,z4,z5,z1269]),(0,[z68,z0,z1,z59,z5,z6]),(0,[z0,z1,z2,z1270,z5,z6]),(0,[z383,z0,z2,z47,z5,z6]),(0,[z161,z2,z4,z47,z5,z6]),(0,[z81,z0,z2,z4,z338,z6]),(0,[z108,z0,z204,z109,z5,z6]),(0,[z0,z1,z2,z4,z5,z248]),(0,[z82,z0,z320,z4,z11,z6]),(0,[z303,z1,z2,z4,z5,z720])],[(0,[z0,z1,z2,z1271,z5,z6]),(0,[z0,z1272,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z263])],[(0,[z0,z2,z4,z5,z1273,z6]),(0,[z0,z1,z2,z4,z1274,z6]),(0,[z30,z0,z116,z2,z4,z5])],[(0,[z0,z282,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z715]),(0,[z0,z1,z46,z59,z5,z6]),(0,[z0,z2,z4,z5,z1275,z6])],[(0,[z0,z1,z2,z4,z1276,z6])],[(0,[z0,z1,z2,z1277,z5,z6]),(0,[z0,z1,z2,z4,z5,z1278]),(0,[z170,z2,z4,z47,z13,z6]),(0,[z0,z250,z4,z47,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1279]),(0,[z1280,z1,z2,z4,z5,z6]),(0,[z1281,z0,z2,z4,z5,z6]),(0,[z0,z1282,z2,z4,z5,z6])],[(0,[z1283,z0,z1,z2,z4,z5]),(0,[z63,z0,z2,z4,z285,z6]),(0,[z0,z2,z57,z4,z5,z6]),(0,[z409,z0,z2,z47,z5,z6]),(0,[z63,z0,z192,z2,z4,z5]),(0,[z0,z58,z4,z5,z18,z6]),(0,[z68,z0,z1,z4,z5,z172]),(0,[z0,z1140,z2,z4,z5,z6])],[(0,[z358,z0,z696,z4,z5,z6]),(0,[z19,z0,z2,z73,z5,z6]),(0,[z63,z0,z2,z4,z6,z471])],[(0,[z0,z1,z2,z1284,z5,z6]),(0,[z0,z1,z2,z4,z166,z153]),(0,[z40,z63,z2,z4,z5,z125]),(0,[z63,z64,z2,z4,z5,z125]),(0,[z0,z1,z1285,z4,z5,z6]),(0,[z0,z1,z1286,z4,z5,z6])],[(0,[z0,z510,z2,z4,z5,z6]),(0,[z63,z0,z2,z36,z5,z35])]],
   [[(0,[z0,z1,z2,z4,z418,z240]),(0,[z0,z2,z4,z5,z18,z216]),(0,[z0,z1287,z2,z4,z5,z6])],[(0,[z64,z15,z2,z4,z5,z125]),(0,[z0,z2,z4,z5,z1288,z6]),(0,[z0,z2,z4,z5,z760,z87]),(0,[z32,z0,z470,z2,z89,z6])],[(0,[z100,z77,z4,z47,z5,z6]),(0,[z0,z1289,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1290]),(0,[z63,z0,z2,z4,z5,z120]),(0,[z1,z22,z4,z23,z61,z6])],[(0,[z0,z1,z737,z4,z5,z6]),(0,[z0,z1,z2,z4,z526,z34]),(0,[z0,z2,z4,z1291,z5,z6]),(0,[z0,z1,z287,z109,z5,z6]),(0,[z82,z0,z4,z289,z11,z6])],[(1,[z1,z737,z4,z5,z6]),(0,[z0,z2,z429,z47,z5,z6]),(0,[z0,z1292,z2,z4,z5,z6])],[(0,[z498,z38,z2,z4,z5,z6]),(0,[z406,z0,z15,z4,z5,z6]),(0,[z27,z2,z4,z5,z186,z6]),(0,[z0,z1,z2,z237,z88,z6]),(0,[z0,z2,z4,z5,z6,z1293])],[],[(0,[z1294,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z47,z5,z216]),(0,[z63,z958,z2,z4,z5,z6]),(0,[z0,z1,z20,z102,z5,z281]),(0,[z1295,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z844])],[(0,[z0,z1,z2,z4,z1296,z6])],[(0,[z0,z2,z4,z814,z5,z6]),(0,[z0,z2,z4,z47,z67,z6]),(0,[z0,z2,z1028,z4,z5,z6]),(0,[z340,z0,z4,z5,z6,z612])],[(0,[z0,z1,z2,z4,z6,z1297])],[(0,[z0,z2,z4,z1298,z5,z6]),(0,[z0,z1,z2,z4,z1299,z6]),(0,[z0,z15,z2,z4,z5,z281])],[(0,[z0,z1300,z2,z59,z5,z6]),(0,[z1,z77,z2,z4,z418,z6]),(0,[z0,z1301,z2,z4,z5,z6]),(0,[z1302,z0,z2,z4,z5,z6])],[(0,[z0,z1,z1303,z4,z5,z6]),(0,[z0,z1304,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1305]),(0,[z63,z0,z2,z4,z5,z691]),(0,[z0,z15,z2,z4,z1013,z6]),(0,[z1306,z1,z2,z4,z5,z6])],[(0,[z206,z0,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z385]),(0,[z0,z2,z4,z349,z5,z6])]],
   [[(0,[z63,z30,z0,z2,z4,z5]),(0,[z63,z0,z2,z700,z4,z5])],[(0,[z1307,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z1308,z6]),(0,[z422,z0,z2,z4,z5,z6]),(0,[z967,z0,z2,z4,z47,z6]),(0,[z208,z0,z2,z4,z703,z6]),(0,[z0,z2,z4,z5,z18,z263])],[(0,[z63,z0,z157,z4,z5,z6]),(0,[z0,z1,z1309,z4,z5,z6]),(0,[z2,z4,z47,z5,z61,z6]),(0,[z0,z2,z4,z1310,z5,z6])],[(0,[z1311,z0,z2,z4,z5,z6]),(0,[z0,z143,z2,z4,z5,z153]),(0,[z217,z0,z4,z5,z6,z495]),(0,[z0,z1,z2,z4,z782,z6]),(0,[z0,z180,z2,z36,z5,z35])],[(0,[z0,z365,z2,z59,z5,z6]),(0,[z68,z422,z0,z2,z4,z5])],[(0,[z0,z2,z4,z5,z186,z83]),(0,[z957,z384,z0,z2,z4,z5]),(0,[z19,z179,z0,z1,z2,z271])],[(0,[z0,z2,z132,z5,z6,z259]),(0,[z0,z2,z4,z5,z1312,z6])],[(0,[z0,z1,z2,z4,z5,z1313]),(0,[z1,z2,z4,z5,z1314,z6]),(0,[z0,z2,z4,z5,z6,z226]),(0,[z14,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z1315])],[(0,[z0,z15,z2,z4,z540,z6]),(0,[z0,z1,z20,z392,z5,z6]),(0,[z0,z1154,z2,z4,z5,z6]),(0,[z0,z139,z56,z4,z5,z21])],[(0,[z63,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z47,z5,z263]),(0,[z0,z1,z4,z5,z21,z795]),(0,[z0,z2,z4,z5,z1316,z6])],[(0,[z161,z470,z2,z4,z5,z6]),(0,[z0,z1317,z2,z4,z5,z6])],[(0,[z0,z201,z2,z4,z5,z6]),(0,[z147,z0,z2,z4,z47,z104]),(0,[z0,z17,z2,z57,z4,z5]),(0,[z0,z2,z36,z5,z18,z35]),(0,[z0,z1318,z2,z4,z5,z6])],[(0,[z0,z1319,z2,z4,z5,z6]),(0,[z1,z2,z4,z540,z13,z6]),(0,[z0,z2,z4,z5,z50,z934])],[(0,[z0,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z1320,z5,z6]),(0,[z0,z1321,z2,z4,z5,z6]),(0,[z0,z444,z4,z330,z5,z6]),(0,[z0,z2,z4,z5,z298,z271]),(0,[z0,z2,z4,z5,z6,z1322]),(0,[z0,z1,z2,z4,z380,z103])],[(0,[z0,z1,z1323,z4,z5,z6]),(0,[z0,z1324,z2,z4,z5,z6]),(0,[z0,z15,z2,z4,z5,z520]),(0,[z19,z63,z0,z2,z5,z271]),(0,[z0,z2,z4,z5,z1325,z6]),(0,[z68,z0,z1,z4,z5,z261]),(0,[z0,z2,z4,z5,z1326,z6]),(0,[z19,z0,z1,z2,z5,z271])],[(0,[z0,z143,z2,z4,z166,z6]),(0,[z0,z2,z288,z47,z5,z6]),(0,[z0,z1327,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z215,z6]),(0,[z99,z1,z46,z4,z5,z6]),(0,[z0,z45,z2,z4,z122,z6]),(0,[z550,z1,z2,z4,z166,z6]),(0,[z0,z1328,z2,z4,z5,z6]),(0,[z340,z30,z0,z2,z4,z5]),(0,[z0,z20,z102,z5,z18,z6]),(0,[z0,z2,z4,z1329,z5,z6]),(0,[z0,z2,z4,z1330,z5,z6])],[(0,[z0,z2,z4,z5,z1273,z385]),(0,[z63,z0,z1011,z4,z5,z6]),(0,[z0,z1,z2,z4,z813,z6])],[(0,[z0,z1,z2,z4,z888,z6]),(0,[z0,z42,z2,z4,z5,z6]),(0,[z344,z0,z2,z4,z6,z695])],[(0,[z0,z1,z1331,z4,z5,z6]),(0,[z0,z1332,z2,z4,z5,z6]),(0,[z0,z2,z4,z1333,z5,z6]),(0,[z0,z2,z4,z5,z18,z196])],[(0,[z0,z223,z2,z4,z5,z6]),(0,[z1,z2,z4,z971,z5,z6]),(0,[z0,z1,z2,z4,z5,z1334]),(0,[z2,z4,z432,z5,z18,z6]),(0,[z0,z4,z195,z5,z18,z6])],[(0,[z40,z63,z2,z4,z166,z6]),(0,[z0,z1,z1335,z4,z5,z6]),(0,[z0,z2,z47,z566,z5,z6]),(0,[z68,z0,z1,z683,z4,z5])],[(0,[z0,z2,z4,z47,z5,z134]),(0,[z63,z0,z2,z4,z5,z216]),(0,[z0,z2,z4,z1336,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1337]),(0,[z0,z1,z4,z5,z6,z495]),(0,[z121,z0,z2,z4,z5,z6]),(0,[z161,z1,z2,z4,z103,z6])],[(0,[z0,z20,z102,z47,z5,z6]),(0,[z996,z0,z2,z4,z47,z5]),(0,[z0,z2,z4,z1338,z5,z6])],[(0,[z0,z2,z4,z5,z215,z134]),(0,[z0,z2,z4,z540,z18,z6]),(0,[z0,z2,z4,z5,z18,z212])],[(0,[z99,z1,z563,z4,z5,z6]),(0,[z0,z15,z2,z4,z285,z6]),(0,[z1339,z0,z2,z4,z5,z6])],[(0,[z371,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z540,z163]),(0,[z0,z2,z4,z5,z1031,z163]),(0,[z0,z15,z2,z4,z6,z471])],[(0,[z40,z1,z2,z4,z540,z6]),(0,[z40,z2,z4,z47,z166,z6]),(0,[z0,z1,z2,z4,z5,z1340]),(0,[z0,z1,z4,z5,z795,z31]),(0,[z0,z1,z2,z260,z5,z35])],[(0,[z63,z0,z2,z4,z418,z6]),(0,[z0,z2,z857,z4,z5,z6]),(0,[z303,z15,z2,z4,z5,z6]),(0,[z0,z15,z2,z36,z5,z35])],[(0,[z63,z0,z2,z4,z5,z304]),(0,[z0,z2,z4,z5,z1341,z6]),(0,[z0,z1342,z2,z4,z5,z6])],[]],
   [[(0,[z0,z15,z2,z4,z5,z120]),(0,[z0,z2,z73,z5,z89,z6]),(0,[z0,z1343,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1344,z6]),(0,[z1345,z0,z1,z2,z4,z6]),(0,[z14,z0,z2,z4,z5,z408]),(0,[z1346,z0,z1,z2,z4,z5]),(0,[z0,z2,z1347,z4,z5,z6])],[(0,[z0,z1,z2,z75,z5,z6]),(0,[z0,z1348,z2,z4,z5,z6]),(0,[z63,z0,z2,z1146,z5,z6])],[(0,[z40,z1,z2,z4,z399,z6]),(0,[z1349,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z1350,z5,z6]),(0,[z81,z0,z2,z4,z53,z6])],[(0,[z1,z77,z157,z4,z5,z6]),(0,[z0,z1351,z2,z4,z5,z6]),(0,[z0,z1352,z2,z4,z5,z6]),(0,[z179,z881,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1353,z6]),(0,[z0,z2,z4,z1354,z5,z6]),(0,[z170,z63,z2,z4,z13,z6]),(0,[z1355,z0,z2,z4,z5,z6]),(0,[z406,z0,z1,z4,z5,z35]),(0,[z0,z126,z2,z4,z5,z34]),(0,[z1356,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z1357,z5,z6])],[(0,[z74,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z845,z5,z6]),(0,[z442,z63,z0,z2,z4,z5]),(0,[z0,z2,z47,z5,z6,z611]),(0,[z63,z0,z2,z4,z5,z263]),(0,[z0,z1,z2,z827,z5,z6]),(0,[z0,z2,z36,z5,z238,z35])],[(1,[z1,z2,z4,z5,z725])],[(0,[z63,z0,z2,z59,z5,z6]),(0,[z108,z0,z47,z109,z5,z6]),(0,[z0,z15,z2,z569,z5,z6]),(0,[z0,z470,z250,z4,z5,z6])],[(0,[z1358,z0,z1,z2,z4,z5]),(0,[z80,z30,z0,z52,z4,z5]),(0,[z179,z0,z2,z4,z47,z6]),(0,[z1359,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z47,z220,z6]),(0,[z1,z2,z4,z5,z725,z125]),(0,[z0,z15,z2,z474,z5,z6]),(0,[z0,z2,z4,z5,z1360,z6])],[(0,[z0,z1,z2,z4,z5,z1361]),(0,[z0,z1,z2,z4,z1362,z6]),(0,[z0,z2,z4,z1363,z5,z6]),(0,[z68,z0,z1,z4,z5,z795])],[(0,[z100,z77,z4,z5,z18,z6]),(0,[z30,z0,z15,z2,z4,z5]),(0,[z0,z1364,z2,z4,z5,z6])],[(0,[z0,z2,z1365,z4,z5,z6]),(0,[z0,z470,z2,z4,z5,z263])],[(0,[z0,z1,z1366,z4,z5,z6]),(0,[z0,z2,z4,z5,z298,z6]),(0,[z0,z1,z2,z4,z5,z1198])]],
   [[(0,[z0,z2,z244,z47,z5,z6]),(0,[z0,z365,z2,z4,z5,z385]),(0,[z0,z2,z47,z5,z635,z6]),(0,[z32,z0,z15,z2,z89,z6])],[(0,[z0,z357,z2,z4,z285,z6]),(0,[z1367,z0,z2,z4,z5,z6]),(0,[z63,z0,z2,z137,z4,z5]),(0,[z0,z2,z4,z1368,z5,z6]),(0,[z0,z2,z4,z5,z1369,z6]),(0,[z0,z1370,z2,z4,z5,z6]),(1,[z0,z1,z2,z930,z6])],[(0,[z0,z38,z2,z4,z146,z6]),(0,[z1,z2,z4,z117,z13,z6]),(0,[z0,z470,z2,z4,z5,z6]),(0,[z0,z1371,z2,z4,z5,z6])],[],[(0,[z0,z116,z2,z4,z535,z6]),(0,[z0,z2,z47,z5,z6,z486])],[(0,[z0,z45,z2,z4,z5,z163]),(0,[z0,z2,z4,z1372,z5,z6])],[(0,[z170,z2,z4,z13,z18,z6]),(0,[z1,z2,z4,z5,z153,z125]),(0,[z0,z1,z1373,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1374]),(0,[z0,z1,z2,z4,z1030,z6])],[(0,[z0,z2,z4,z47,z5,z385]),(0,[z0,z1,z51,z4,z5,z216]),(0,[z2,z4,z47,z1227,z5,z6]),(0,[z19,z0,z2,z47,z5,z271]),(0,[z0,z15,z2,z4,z5,z50])],[(0,[z0,z1,z2,z4,z5,z1375]),(0,[z0,z1,z2,z971,z5,z6])],[(0,[z532,z1,z2,z4,z13,z6]),(0,[z63,z0,z2,z4,z5,z34])],[(0,[z99,z1,z46,z4,z5,z385]),(0,[z0,z1,z2,z4,z5,z1376]),(0,[z100,z1,z4,z5,z6,z693]),(0,[z0,z2,z4,z1377,z5,z6]),(0,[z0,z1378,z2,z4,z5,z6]),(0,[z63,z0,z4,z195,z5,z6]),(0,[z0,z1,z56,z4,z5,z21])],[(0,[z1379,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z103,z263])],[(0,[z0,z15,z2,z676,z5,z6]),(0,[z0,z1,z2,z5,z1380,z6]),(0,[z0,z1381,z2,z4,z5,z6]),(0,[z0,z1382,z2,z4,z5,z6])],[(0,[z0,z2,z4,z1383,z5,z6]),(0,[z147,z0,z1,z2,z4,z537]),(0,[z147,z0,z15,z2,z4,z104]),(0,[z0,z1,z2,z4,z5,z760])],[(0,[z0,z1,z51,z4,z418,z6]),(0,[z30,z0,z2,z4,z47,z5]),(0,[z252,z463,z2,z4,z5,z6])],[(0,[z0,z2,z75,z1232,z5,z6]),(0,[z0,z1384,z2,z4,z5,z6]),(0,[z406,z1,z4,z5,z13,z6]),(0,[z175,z63,z2,z4,z5,z34])]],
   [[(0,[z0,z1,z2,z4,z1385,z6]),(0,[z0,z2,z4,z5,z6,z1386]),(0,[z0,z2,z102,z73,z5,z6])],[(0,[z0,z1,z2,z1387,z5,z6]),(0,[z0,z1,z2,z4,z5,z240]),(0,[z179,z0,z1,z2,z4,z125]),(0,[z0,z2,z4,z5,z1388,z6])],[(0,[z0,z1,z2,z4,z5,z1389]),(0,[z30,z0,z38,z2,z4,z5]),(0,[z0,z1300,z2,z4,z5,z6]),(0,[z0,z1390,z2,z4,z5,z6]),(0,[z218,z0,z2,z4,z43,z5]),(0,[z63,z0,z2,z4,z5,z178])],[(0,[z0,z118,z4,z330,z5,z6]),(0,[z384,z0,z15,z2,z4,z5])],[(0,[z107,z2,z4,z5,z6,z334]),(0,[z0,z1391,z2,z4,z5,z6]),(0,[z227,z1174,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1392]),(0,[z0,z2,z137,z4,z47,z5]),(0,[z0,z1,z4,z109,z5,z248]),(0,[z0,z2,z4,z276,z5,z281])],[(0,[z588,z0,z1,z109,z5,z6]),(0,[z175,z2,z4,z47,z5,z34])],[(0,[z208,z0,z2,z4,z9,z6]),(0,[z303,z1,z2,z4,z166,z6]),(0,[z406,z217,z0,z4,z5,z6]),(0,[z160,z0,z2,z4,z5,z34]),(0,[z123,z1,z2,z4,z850,z6])],[(0,[z0,z2,z4,z5,z18,z6]),(0,[z0,z126,z2,z4,z67,z6]),(0,[z0,z2,z4,z1393,z5,z6]),(0,[z227,z1178,z2,z4,z5,z6])],[(0,[z0,z365,z2,z4,z5,z6]),(0,[z27,z28,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z220,z6]),(0,[z0,z2,z4,z5,z6,z1394]),(0,[z0,z1,z4,z5,z6,z1395]),(0,[z218,z0,z2,z4,z5,z34])],[(0,[z63,z0,z2,z1199,z5,z6])],[(0,[z0,z15,z2,z4,z418,z6]),(0,[z594,z1,z2,z4,z13,z6])],[(0,[z0,z1,z51,z4,z5,z6]),(0,[z0,z1,z2,z75,z5,z385]),(0,[z85,z1,z2,z151,z5,z240]),(0,[z227,z1,z2,z4,z5,z34]),(0,[z1396,z1,z2,z4,z5,z6])],[(0,[z37,z38,z2,z4,z5,z83]),(0,[z0,z143,z2,z4,z5,z520]),(0,[z406,z64,z1,z4,z5,z125]),(0,[z0,z1397,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1398]),(0,[z0,z1,z2,z4,z5,z1399]),(0,[z0,z180,z4,z195,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1400]),(0,[z1,z2,z78,z59,z5,z6]),(0,[z0,z1,z2,z4,z5,z1401])]],
   [[(0,[z1402,z0,z1,z2,z4,z6]),(0,[z0,z2,z4,z5,z6,z389]),(0,[z0,z1,z22,z4,z867,z6]),(0,[z0,z1,z4,z23,z867,z6])],[(0,[z0,z2,z4,z5,z18,z134]),(0,[z0,z1403,z2,z4,z5,z6]),(0,[z0,z1404,z2,z4,z5,z6]),(0,[z0,z1405,z2,z4,z5,z6])],[(0,[z1103,z0,z2,z4,z5,z6]),(0,[z1258,z0,z2,z4,z5,z6]),(0,[z0,z1406,z2,z4,z5,z6])],[(0,[z1,z2,z4,z209,z13,z6]),(0,[z670,z0,z2,z4,z524,z6]),(0,[z19,z0,z2,z5,z389,z271])],[(0,[z68,z0,z1,z4,z5,z385]),(0,[z1407,z0,z2,z4,z5,z6]),(0,[z384,z0,z2,z4,z47,z5])],[(0,[z325,z1,z2,z4,z5,z34]),(0,[z0,z15,z2,z73,z5,z6])],[(0,[z0,z1,z2,z4,z878,z6]),(0,[z303,z1,z22,z4,z23,z6]),(0,[z0,z1,z323,z4,z5,z120])],[(0,[z0,z15,z2,z59,z5,z6])],[(0,[z30,z0,z118,z2,z4,z5]),(0,[z0,z2,z4,z5,z18,z248]),(0,[z1408,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z83]),(0,[z0,z1,z2,z4,z1409,z6]),(0,[z0,z24,z2,z4,z285,z6]),(0,[z0,z1,z2,z4,z5,z1410]),(0,[z0,z15,z2,z679,z5,z6]),(0,[z0,z116,z2,z4,z213,z6]),(0,[z0,z1,z4,z827,z5,z6]),(0,[z0,z1263,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1411]),(0,[z0,z1,z4,z5,z1412,z6]),(0,[z63,z0,z2,z4,z5,z280]),(0,[z0,z419,z2,z4,z5,z281]),(0,[z0,z1413,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z883])],[(0,[z0,z126,z2,z4,z5,z6]),(0,[z63,z0,z2,z4,z67,z6]),(0,[z875,z1,z2,z4,z5,z6]),(0,[z1414,z0,z2,z4,z5,z6]),(0,[z252,z1,z2,z4,z5,z120]),(0,[z0,z2,z4,z5,z6,z1415])],[(0,[z1,z2,z4,z5,z34,z725]),(0,[z218,z0,z2,z4,z5,z271]),(0,[z179,z0,z15,z2,z4,z6]),(0,[z0,z1,z2,z1416,z5,z6])],[(0,[z0,z1,z2,z4,z1417,z6]),(0,[z99,z1,z46,z75,z5,z6]),(0,[z0,z1,z2,z4,z5,z1418]),(0,[z0,z15,z2,z132,z5,z6]),(0,[z0,z2,z4,z5,z6,z1419]),(0,[z0,z17,z2,z4,z5,z18]),(0,[z63,z0,z2,z57,z4,z5])],[(0,[z1,z2,z4,z801,z13,z6])],[]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 495) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 495).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 996).take 444) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1440)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [495, 501, 444] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 145).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 297).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 440).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [145, 152, 143, 72] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37287

theorem PEqualNP.Outside.L_meta_37287 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4206946496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4206946496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37287.solve